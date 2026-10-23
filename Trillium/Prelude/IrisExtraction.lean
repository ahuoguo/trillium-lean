/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Instances.UPred.Instance
import Trillium.Prelude.Quantifiers

/-!
# Extracting meta-level facts from valid `uPred`s

Port of `trillium/prelude/iris_extraction.v`.

Each lemma relates validity `⊢ P` of a proposition of the `UPred M` model to a meta-level
statement. Notably, `extract_exists` commutes `⊢` with an existential over a type smaller than
`ℕ` (using `forall_exists_swap` and `nat_regular`).

iris-lean's `UPred M` is defined over unital *ordered* resource algebras (`UORA M`) rather than
`ucmra`s. `⊢ P` (i.e. `emp ⊢ P`) holds iff `P` holds of the unit at every step index
(`valid_iff_holds_unit`). Lemmas that need resources to be monotone under composition
(`extract_sep`, i.e. affinity of the logic, automatic in Rocq's `uPred`) assume `[IncOrd M]`,
which holds for `IProp GF`'s resources (`IResUR GF`). In `extract_own`, Rocq's `x ≼{n} ε`
becomes the ORA order `x ≼ₒ{n} unit`. `extract_persistently` is about `□` (Rocq's `□`, the
intuitionistic modality). iris-lean's OFEs are Leibniz, so in `extract_internal_eq` Rocq's
`x ≡ y` is `x = y`.
-/

namespace Trillium

open Iris Iris.BI ORA OFE

section extraction

variable {M : Type _} [UORA M]

/-- `⊢ P` holds iff `P` holds of the unit at every step index. (Helper, not in Rocq.) -/
theorem valid_iff_holds_unit (P : UPred M) : (⊢ P) ↔ ∀ n, P n ⟨unit, unit_validN⟩ :=
  ⟨fun H n => H n ⟨unit, unit_validN⟩ (ordN_refl unit),
   fun H n _ Hx => P.mono (H n) Hx (Nat.le_refl n)⟩

@[rocq_alias trillium.extract_forall]
theorem extract_forall {A : Type _} (Φ : A → UPred M) : (⊢ ∀ x, Φ x) ↔ ∀ x, ⊢ Φ x :=
  ⟨fun HP x => HP.trans (forall_elim x), fun HP => forall_intro HP⟩

@[rocq_alias trillium.extract_exists]
theorem extract_exists {A : Type _} (Φ : A → UPred M) (Hcard : SmallerCard A ℕ) :
    (⊢ ∃ x, Φ x) ↔ ∃ x, ⊢ Φ x := by
  constructor
  · intro HP
    have HP' : ∀ n, ∃ x, Φ x n ⟨unit, unit_validN⟩ := fun n => by
      obtain ⟨_, ⟨x, rfl⟩, Hx⟩ := (valid_iff_holds_unit _).mp HP n
      exact ⟨x, Hx⟩
    obtain ⟨x, Hx⟩ := forall_exists_swap (R := (· ≤ · : ℕ → ℕ → Prop))
      (P := fun n x => Φ x n ⟨unit, unit_validN⟩) Nat.le_total (fun _ _ _ => Nat.le_trans)
      (fun _ _ _ Hle H => (Φ _).mono H (ordN_refl _) Hle) Nat.le_refl nat_regular Hcard HP'
    exact ⟨x, (valid_iff_holds_unit _).mpr Hx⟩
  · rintro ⟨x, Hx⟩
    exact Hx.trans (exists_intro x)

@[rocq_alias trillium.extract_exists_alt]
theorem extract_exists_alt {A : Type _} (P : A → Prop) (Φ : A → UPred M)
    (Hcard : SmallerCard {x // P x} ℕ) :
    (⊢ ∃ x, ⌜P x⌝ ∧ Φ x) ↔ ∃ x, ⊢ ⌜P x⌝ ∧ Φ x := by
  constructor
  · intro HP
    have HP' : ⊢ ∃ x : {x // P x}, Φ x.1 :=
      HP.trans (exists_elim fun x => pure_elim_left fun HPx => exists_intro_trans (Ψ := fun x : {x // P x} => Φ x.1) ⟨x, HPx⟩ .rfl)
    obtain ⟨⟨x, HPx⟩, HΦ⟩ := (extract_exists _ Hcard).mp HP'
    exact ⟨x, and_intro (pure_intro HPx) HΦ⟩
  · rintro ⟨x, Hx⟩
    exact exists_intro_trans x Hx

@[rocq_alias trillium.extract_exists_alt2]
theorem extract_exists_alt2 {A B : Type _} (P : A → B → Prop) (Φ : A → B → UPred M)
    (Hcard : SmallerCard {p : A × B // P p.1 p.2} ℕ) :
    (⊢ ∃ x y, ⌜P x y⌝ ∧ Φ x y) ↔ ∃ x y, ⊢ ⌜P x y⌝ ∧ Φ x y := by
  constructor
  · intro HP
    have HP' : ⊢ ∃ x : {p : A × B // P p.1 p.2}, Φ x.1.1 x.1.2 :=
      HP.trans (exists_elim fun x => exists_elim fun y =>
        pure_elim_left fun HPxy => exists_intro_trans (Ψ := fun x : {p : A × B // P p.1 p.2} => Φ x.1.1 x.1.2) ⟨(x, y), HPxy⟩ .rfl)
    obtain ⟨⟨⟨x, y⟩, HPxy⟩, HΦ⟩ := (extract_exists _ Hcard).mp HP'
    exact ⟨x, y, and_intro (pure_intro HPxy) HΦ⟩
  · rintro ⟨x, y, Hxy⟩
    exact exists_intro_trans x (exists_intro_trans y Hxy)

@[rocq_alias trillium.extract_and]
theorem extract_and (P Q : UPred M) : (⊢ P ∧ Q) ↔ (⊢ P) ∧ (⊢ Q) :=
  ⟨fun HPQ => ⟨HPQ.trans and_elim_l, HPQ.trans and_elim_r⟩, fun ⟨HP, HQ⟩ => and_intro HP HQ⟩

/-- `Bool` is smaller than `ℕ`. -/
private theorem smaller_card_bool_nat : SmallerCard Bool ℕ := by
  intro f Hf
  have h01 := Hf.ne (show (0 : ℕ) ≠ 1 by decide)
  have h02 := Hf.ne (show (0 : ℕ) ≠ 2 by decide)
  have h12 := Hf.ne (show (1 : ℕ) ≠ 2 by decide)
  revert h01 h02 h12
  cases f 0 <;> cases f 1 <;> cases f 2 <;> decide

@[rocq_alias trillium.extract_or]
theorem extract_or (P Q : UPred M) : (⊢ P ∨ Q) ↔ (⊢ P) ∨ (⊢ Q) := by
  constructor
  · intro HPQ
    have HPQ' : ⊢ ∃ b : Bool, if b then P else Q :=
      HPQ.trans (or_elim (exists_intro_trans (Ψ := fun b : Bool => if b then P else Q) true .rfl)
        (exists_intro_trans (Ψ := fun b : Bool => if b then P else Q) false .rfl))
    obtain ⟨b, Hb⟩ := (extract_exists _ smaller_card_bool_nat).mp HPQ'
    cases b
    · exact .inr Hb
    · exact .inl Hb
  · rintro (HP | HQ)
    · exact HP.trans or_intro_l
    · exact HQ.trans or_intro_r

@[rocq_alias trillium.extract_pure]
theorem extract_pure (φ : Prop) : (⊢ (⌜φ⌝ : UPred M)) ↔ φ :=
  ⟨UPred.pure_soundness, fun Hφ => pure_intro Hφ⟩

@[rocq_alias trillium.extract_True]
theorem extract_True : (⊢ (True : UPred M)) ↔ True := extract_pure True

@[rocq_alias trillium.extract_False]
theorem extract_False : (⊢ (False : UPred M)) ↔ False := extract_pure False

@[rocq_alias trillium.extract_impl]
theorem extract_impl (P Q : UPred M) : (⊢ P → Q) → (⊢ P) → ⊢ Q :=
  fun HPQ HP => (and_intro HPQ HP).trans imp_elim_left

@[rocq_alias trillium.extract_sep]
theorem extract_sep [IncOrd M] (P Q : UPred M) : (⊢ P ∗ Q) ↔ (⊢ P) ∧ (⊢ Q) :=
  ⟨fun HPQ => ⟨HPQ.trans sep_elim_left, HPQ.trans sep_elim_right⟩,
   fun ⟨HP, HQ⟩ => emp_sep.2.trans (sep_mono HP HQ)⟩

@[rocq_alias trillium.extract_wand]
theorem extract_wand (P Q : UPred M) : (⊢ P -∗ Q) → (⊢ P) → ⊢ Q :=
  fun HPQ HP => emp_sep.2.trans ((sep_mono HPQ HP).trans wand_elim_left)

@[rocq_alias trillium.extract_later]
theorem extract_later (P : UPred M) : (⊢ ▷ P) ↔ ⊢ P :=
  ⟨UPred.later_soundness, fun HP => HP.trans later_intro⟩

@[rocq_alias trillium.extract_except_0]
theorem extract_except_0 (P : UPred M) : (⊢ ◇ P) ↔ ⊢ P :=
  ⟨fun HP => UPred.later_soundness (HP.trans except0_into_later),
   fun HP => HP.trans except0_intro⟩

@[rocq_alias trillium.extract_bupd]
theorem extract_bupd (P : UPred M) [Plain P] : (⊢ |==> P) ↔ ⊢ P :=
  ⟨UPred.bupd_soundness, fun HP => HP.trans bupd_intro⟩

@[rocq_alias trillium.extract_internal_eq]
theorem extract_internal_eq {A : Type _} [OFE A] (x y : A) : (⊢ (iprop(x ≡ y) : UPred M)) ↔ x = y := by
  constructor
  · intro Hxy
    exact OFE.eq_dist.mpr fun n => (valid_iff_holds_unit _).mp Hxy n
  · intro Hxy
    exact (valid_iff_holds_unit _).mpr fun n => OFE.eq_dist.mp Hxy n

@[rocq_alias trillium.extract_plainly]
theorem extract_plainly (P : UPred M) : (⊢ ■ P) ↔ ⊢ P := by
  rw [valid_iff_holds_unit, valid_iff_holds_unit]
  rfl

@[rocq_alias trillium.extract_persistently]
theorem extract_persistently (P : UPred M) : (⊢ □ P) ↔ ⊢ P :=
  ⟨fun HP => HP.trans intuitionistically_elim,
   fun HP => intuitionistically_emp.2.trans (intuitionistically_mono HP)⟩

@[rocq_alias trillium.extract_own]
theorem extract_own (x : M) : (⊢ UPred.ownM x) ↔ ∀ n, x ≼ₒ{n} (unit : M) :=
  valid_iff_holds_unit _

@[rocq_alias trillium.extract_valid]
theorem extract_valid {A : Type _} [ORA A] (x : A) : (⊢ (✓ x : UPred M)) ↔ ✓ x := by
  rw [valid_iff_holds_unit, valid_validN]
  rfl

end extraction

end Trillium
