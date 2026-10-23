#!/usr/bin/env python3
"""Trillium Rocq -> Lean correspondence checker.

Parses every `.v` file of the Trillium Rocq development, collects the declared
names, and classifies each one against the Lean side's porting annotations
(dumped by `lake exe dumpPortingData`):

  * ported   -- some Lean declaration carries `@[rocq_alias <name>]`
  * ignored  -- `#rocq_ignore <name> "reason"` or `#rocq_ignore_file <dir> "<file>" "reason"`
  * missing  -- neither

It also flags *stale* annotations (pointing to names that do not exist in Rocq) and
ported declarations whose Lean proof depends on `sorryAx`.

Naming convention (mirrors iris-lean's `scripts/check_porting.py`):

  Rocq root     Lean alias prefix        `#rocq_ignore_file` directory argument
  trillium/     trillium.                trillium.<subdir>      (e.g. trillium.prelude)
  heap_lang/    trillium.heap_lang.      trillium.heap_lang
  fairness/     trillium.fairness.       trillium.fairness
  fairis/       trillium.fairis.         trillium.fairis, trillium.fairis.examples

Rocq `Module M` qualifies names (`M.foo`); `Section`s do not. If the same prefixed
name is declared in several files, every occurrence is further qualified by the
file stem, e.g. `trillium.fairness.fairness.foo` vs `trillium.fairis.fairness.foo`
are distinct anyway, but two `foo`s in `fairness/a.v` and `fairness/b.v` become
`trillium.fairness.a.foo` and `trillium.fairness.b.foo`.

Usage:
  python3 scripts/check_correspondence.py [--rocq DIR] [--no-build] [-o CORRESPONDENCE.md] [--strict]

The Rocq checkout (default: $TRILLIUM_ROCQ_DIR, else ../../trillium relative to this
project) must be at the commit in scripts/TRILLIUM_ROCQ_REVISION
(https://github.com/logsem/trillium).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_ROCQ = Path(os.environ.get("TRILLIUM_ROCQ_DIR", ROOT.parent.parent / "trillium"))
ROCQ_REVISION = (ROOT / "scripts" / "TRILLIUM_ROCQ_REVISION").read_text().strip()
ROOTS = ["trillium", "heap_lang", "fairness", "fairis"]

# ---------------------------------------------------------------------------
# Rocq parsing (adapted from iris-lean scripts/check_porting.py; adds
# CoInductive/Axiom/Let which Trillium uses)
# ---------------------------------------------------------------------------

_DEF_KEYWORDS = (
    r"Definition|Lemma|Theorem|Instance|Class|Record|Structure|"
    r"Inductive|CoInductive|Fixpoint|CoFixpoint|Variant|Corollary|Proposition|"
    r"Fact|Remark|Example|Axiom|Canonical\s+Structure"
)
_DEF_RE = re.compile(
    rf"^\s*(?P<modifiers>(?:(?:Global|Local|Program|#\[(?:export|global|local)\])\s+)*)"
    rf"(?:{_DEF_KEYWORDS})\s+(?P<identifier>\w[\w']*)",
    re.MULTILINE,
)
_WITH_DEF_RE = re.compile(r"^with\s+(\w[\w']*)\s*(?=[({:])")
_MODULE_START_RE = re.compile(r"^\s*Module\s+(?:Export\s+|Import\s+)?(\w+)")
_MODULE_TYPE_RE = re.compile(r"^\s*Module\s+Type\b")
_MODULE_ALIAS_RE = re.compile(r"^\s*Module\s+(?:Export\s+|Import\s+)?\w+\s*:=")
_SECTION_START_RE = re.compile(r"^\s*Section\s+(\w+)")
_END_RE = re.compile(r"^\s*End\s+(\w+)\s*\.")
_SKIP_RE = re.compile(
    r"^\s*(?:Notation|Ltac|Ltac2|Tactic\s+Notation|Hint|Arguments|"
    r"Typeclasses\s+(?:Opaque|Transparent)|Existing\s+Instance|Params|"
    r"(?:Declare|Delimit|Bind|Open|Close)\s+Scope|"
    r"Coercion|Import|Export|Require|From|Set|Unset)\b"
)


def strip_comments(text: str) -> str:
    out, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i:i + 2] == "*)" and depth > 0:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def parse_rocq_file(text: str) -> list[str]:
    text = strip_comments(text)
    text = re.sub(r"^with[ \t]*\n[ \t]*", "with ", text, flags=re.MULTILINE)
    names: list[str] = []
    modules: list[str] = []
    sections: list[str] = []
    for line in text.split("\n"):
        if (m := _MODULE_START_RE.match(line)) and not _MODULE_TYPE_RE.match(line):
            if not _MODULE_ALIAS_RE.match(line):
                modules.append(m.group(1))
            continue
        if m := _SECTION_START_RE.match(line):
            sections.append(m.group(1))
            continue
        if m := _END_RE.match(line):
            n = m.group(1)
            if sections and sections[-1] == n:
                sections.pop()
            elif modules and modules[-1] == n:
                modules.pop()
            continue
        if _SKIP_RE.match(line):
            continue
        m = _DEF_RE.match(line) or _WITH_DEF_RE.match(line)
        if m:
            ident = m.group("identifier") if m.re is _DEF_RE else m.group(1)
            q = ".".join([*modules, ident])
            if q not in names:
                names.append(q)
    return names


# ---------------------------------------------------------------------------
# Packages and qualification
# ---------------------------------------------------------------------------

def prefix_of(rel: str) -> str:
    root = rel.split("/", 1)[0]
    return "trillium." if root == "trillium" else f"trillium.{root}."


def folder_args(rel: str) -> list[tuple[str, str]]:
    """All (directory argument, relative file) pairs that may name `rel` in
    `#rocq_ignore_file`."""
    parts = rel.split("/")
    root, rest = parts[0], parts[1:]
    base = "trillium" if root == "trillium" else f"trillium.{root}"
    out = [(base, "/".join(rest))]
    for i in range(1, len(rest)):
        out.append((base + "." + ".".join(rest[:i]), "/".join(rest[i:])))
    return out


def collect_rocq(rocq_dir: Path) -> dict[str, list[str]]:
    files = sorted(
        str(p.relative_to(rocq_dir))
        for r in ROOTS for p in (rocq_dir / r).rglob("*.v"))
    parsed = {f: parse_rocq_file((rocq_dir / f).read_text()) for f in files}
    base = {f: [prefix_of(f) + n for n in ns] for f, ns in parsed.items()}
    where: dict[str, set[str]] = defaultdict(set)
    for f, ns in base.items():
        for n in ns:
            where[n].add(f)
    out = {}
    for f, ns in parsed.items():
        stem = Path(f).stem
        out[f] = [prefix_of(f) + (f"{stem}.{n}" if len(where[prefix_of(f) + n]) > 1 else n)
                  for n in ns]
    return out


# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------

@dataclass
class Entry:
    rocq: str
    status: str  # ported / ignored / missing
    detail: str = ""
    sorry: bool = False
    modules: tuple[str, ...] = ()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rocq", type=Path, default=DEFAULT_ROCQ)
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--json", default=str(ROOT / ".lake/porting_data.json"))
    ap.add_argument("-o", "--output", default=str(ROOT / "CORRESPONDENCE.md"))
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 if anything is missing, stale, or sorry-dependent")
    args = ap.parse_args()

    if not args.no_build:
        subprocess.run(["lake", "build"], cwd=ROOT, check=True)
        subprocess.run(["lake", "exe", "dumpPortingData", args.json], cwd=ROOT, check=True)
    data = json.loads(Path(args.json).read_text())

    rocq = collect_rocq(args.rocq)
    all_names = {n for ns in rocq.values() for n in ns}

    aliases: dict[str, list[dict]] = defaultdict(list)
    for a in data["aliases"]:
        aliases[a["rocq"]].append(a)
    ignores = {i["rocq"]: i["reason"] for i in data["ignores"]}
    ignored_files = {(i["folder"], i["file"]): i["reason"] for i in data["ignored_files"]}

    report: dict[str, list[Entry]] = {}
    file_reason: dict[str, str] = {}
    lean_modules: dict[str, set[str]] = defaultdict(set)
    for f, names in rocq.items():
        freason = next((ignored_files[k] for k in folder_args(f) if k in ignored_files), None)
        if freason:
            file_reason[f] = freason
        entries = []
        for n in names:
            if n in aliases:
                al = sorted(aliases[n], key=lambda a: a["lean"])
                mods = tuple(sorted({a["module"] for a in al}))
                lean_modules[f].update(mods)
                entries.append(Entry(n, "ported", ", ".join(f"`{a['lean']}`" for a in al),
                                     any(a["sorry"] for a in al), mods))
            elif n in ignores:
                entries.append(Entry(n, "ignored", ignores[n]))
            elif freason:
                entries.append(Entry(n, "ignored", "(whole file) " + freason))
            else:
                entries.append(Entry(n, "missing"))
        report[f] = entries

    stale_alias = sorted(n for n in aliases if n not in all_names)
    stale_ignore = sorted(n for n in ignores if n not in all_names)
    known_dirs = {k for f in rocq for k in folder_args(f)}
    stale_files = sorted(k for k in ignored_files if k not in known_dirs)

    tot = defaultdict(int)
    for es in report.values():
        for e in es:
            tot[e.status] += 1
            tot["sorry"] += e.sorry
    total = sum(len(es) for es in report.values())

    L = []
    L.append("# Trillium → Lean correspondence\n")
    L.append("Generated by `scripts/check_correspondence.py` from the Rocq sources of "
             f"Trillium ([logsem/trillium@{ROCQ_REVISION[:7]}]"
             f"(https://github.com/logsem/trillium/tree/{ROCQ_REVISION})) and the "
             "`@[rocq_alias]` / `#rocq_ignore` / "
             "`#rocq_ignore_file` annotations in `Trillium/`. **Do not edit by hand**; "
             "regenerate with `python3 scripts/check_correspondence.py`.\n")
    L.append("Every named Rocq declaration (`Definition`, `Lemma`, `Instance`, `Inductive`, "
             "`CoInductive`, `Record`, `Class`, `Fixpoint`, …; notations and anonymous "
             "instances are not tracked) is classified as **ported** (a Lean declaration "
             "carries `@[rocq_alias <name>]`), **ignored** (deliberately not ported, with "
             "the recorded reason), or **missing**. `sorry` marks ported declarations whose "
             "Lean proof still depends on `sorryAx`.\n")
    L.append("## Summary\n")
    L.append(f"- Rocq files: **{len(report)}**, declarations: **{total}**")
    L.append(f"- ported: **{tot['ported']}**, ignored: **{tot['ignored']}**, "
             f"missing: **{tot['missing']}**, ported-but-sorry: **{tot['sorry']}**")
    L.append(f"- stale aliases: **{len(stale_alias)}**, stale ignores: "
             f"**{len(stale_ignore)}**, stale ignored files: **{len(stale_files)}**\n")
    L.append("| Rocq file | Lean module(s) | decls | ported | ignored | missing | sorry |")
    L.append("|---|---|---:|---:|---:|---:|---:|")
    for f, es in report.items():
        c = defaultdict(int)
        for e in es:
            c[e.status] += 1
            c["sorry"] += e.sorry
        mods = ", ".join(f"`{m}`" for m in sorted(lean_modules[f])) or (
            "*(file ignored)*" if f in file_reason else "—")
        L.append(f"| `{f}` | {mods} | {len(es)} | {c['ported']} | {c['ignored']} | "
                 f"{c['missing']} | {c['sorry']} |")
    L.append("")
    if stale_alias or stale_ignore or stale_files:
        L.append("## Stale annotations\n")
        for n in stale_alias:
            L.append(f"- alias `{n}` → " + ", ".join(f"`{a['lean']}`" for a in aliases[n]))
        for n in stale_ignore:
            L.append(f"- ignore `{n}`")
        for d, fl in stale_files:
            L.append(f"- ignored file `{d}` `{fl}`")
        L.append("")
    L.append("## Per-file details\n")
    for f, es in report.items():
        L.append(f"### `{f}`\n")
        if f in file_reason:
            L.append(f"*Whole file ignored:* {file_reason[f]}\n")
        if not es:
            L.append("*(no named declarations)*\n")
            continue
        L.append("| Rocq | status | Lean / reason |")
        L.append("|---|---|---|")
        for e in es:
            st = {"ported": "✅ ported", "ignored": "➖ ignored", "missing": "❌ **missing**"}[e.status]
            if e.sorry:
                st += " ⚠️ sorry"
            detail = e.detail.replace("|", "\\|")
            L.append(f"| `{e.rocq}` | {st} | {detail} |")
        L.append("")
    Path(args.output).write_text("\n".join(L) + "\n")
    print(f"{total} decls: {tot['ported']} ported, {tot['ignored']} ignored, "
          f"{tot['missing']} missing, {tot['sorry']} sorry; stale: {len(stale_alias)} "
          f"aliases, {len(stale_ignore)} ignores, {len(stale_files)} files -> {args.output}")
    bad = tot["missing"] or tot["sorry"] or stale_alias or stale_ignore or stale_files
    return 1 if (args.strict and bad) else 0


if __name__ == "__main__":
    sys.exit(main())
