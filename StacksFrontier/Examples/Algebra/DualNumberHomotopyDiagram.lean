module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.RingTheory.DualNumber
public import StacksCore.Tactic.StacksAttribute

/-!
# A diagram of complexes over the dual numbers commuting up to homotopy

Over the dual numbers `R = k[ε]`, consider the degreewise split short exact sequence of
two-term cochain complexes whose columns are `0 → R`, `R → R` (differential multiplication by
`ε`) and `R → 0`, concentrated in degrees zero and one. Multiplication by `1 + ε` on the left
column, together with the identity on the other two, is an endomorphism of the sequence whose
squares commute in the homotopy category — the left square only up to homotopy. This diagram is
the input to the failure of additivity of traces.

## Main definitions

* `Stacks.Examples.dualNumberTwoTermComplex`: a cochain complex supported in degrees zero and
  one, with a prescribed differential.
* `Stacks.Examples.dualNumberLeftComplex`, `Stacks.Examples.dualNumberMiddleComplex`,
  `Stacks.Examples.dualNumberRightComplex`: the three columns of the displayed sequence.

## Main results

* `Stacks.Examples.dualNumber_diagram_commutes_up_to_homotopy`: the displayed diagram commutes
  in the homotopy category, with its maps specified degreewise.

## Implementation notes

The two squares are represented by the single equation in the homotopy category; the right
square already commutes as a square of complexes. The existentially quantified maps are pinned
down by their components in every degree, so no choice of representatives is hidden.

## References

* [Stacks Project, Tag 087K](https://stacks.math.columbia.edu/tag/087K)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Examples

universe u

variable (k : Type u) [Field k]

/-- The ring of dual numbers over `k`. -/
public abbrev dualNumberRing := DualNumber k

/-- Modules over the dual numbers. -/
public abbrev DualNumberModuleCat := ModuleCat (dualNumberRing k)

/-- The zero module over the dual numbers. -/
public abbrev dualNumberZeroModule : DualNumberModuleCat k :=
  ModuleCat.of (dualNumberRing k) (Fin 0 → dualNumberRing k)

/-- A complex concentrated in degrees zero and one, with a prescribed differential. -/
public def dualNumberTwoTermComplex (P Q : DualNumberModuleCat k) (d : P ⟶ Q) :
    CochainComplex (DualNumberModuleCat k) ℤ :=
  CochainComplex.of
    (fun n => if n = 0 then P else if n = 1 then Q else dualNumberZeroModule k)
    (fun n => if h : n = 0 then
      eqToHom (by subst n; simp) ≫ d ≫ eqToHom (by subst n; simp)
      else 0)
    (fun n => by
      by_cases h : n = 0
      · subst n
        simp
      · simp [h])

/-- The left column of the displayed diagram, namely `0 → R`. -/
public abbrev dualNumberLeftComplex : CochainComplex (DualNumberModuleCat k) ℤ :=
  dualNumberTwoTermComplex k (dualNumberZeroModule k)
    (ModuleCat.of (dualNumberRing k) (dualNumberRing k)) 0

/-- The middle column of the displayed diagram, namely `R → R` by `ε`. -/
public abbrev dualNumberMiddleComplex : CochainComplex (DualNumberModuleCat k) ℤ :=
  dualNumberTwoTermComplex k (ModuleCat.of (dualNumberRing k) (dualNumberRing k))
    (ModuleCat.of (dualNumberRing k) (dualNumberRing k))
    (ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing k)
      (DualNumber.eps : dualNumberRing k)))

/-- The right column of the displayed diagram, namely `R → 0`. -/
public abbrev dualNumberRightComplex : CochainComplex (DualNumberModuleCat k) ℤ :=
  dualNumberTwoTermComplex k (ModuleCat.of (dualNumberRing k) (dualNumberRing k))
    (dualNumberZeroModule k) 0

/-- The prescribed endomorphism of the left column and the identity endomorphisms of the middle
and right columns make the two squares commute in the homotopy category. -/
@[stacks 087K]
public theorem dualNumber_diagram_commutes_up_to_homotopy :
    ∃ (i : dualNumberLeftComplex k ⟶ dualNumberMiddleComplex k)
      (p : dualNumberMiddleComplex k ⟶ dualNumberRightComplex k)
      (a : dualNumberLeftComplex k ⟶ dualNumberLeftComplex k),
      (i.f 1 = 𝟙 _) ∧
      (∀ n : ℤ, n ≠ 1 → i.f n = 0) ∧
      (p.f 0 = 𝟙 _) ∧
      (∀ n : ℤ, n ≠ 0 → p.f n = 0) ∧
      (a.f 1 = ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing k)
        (1 + (DualNumber.eps : dualNumberRing k)))) ∧
      (∀ n : ℤ, n ≠ 1 → a.f n = 0) ∧
      ((HomotopyCategory.quotient (DualNumberModuleCat k) (ComplexShape.up ℤ)).map a ≫
          (HomotopyCategory.quotient (DualNumberModuleCat k) (ComplexShape.up ℤ)).map i =
        (HomotopyCategory.quotient (DualNumberModuleCat k) (ComplexShape.up ℤ)).map i) ∧
      (i ≫ p = 0) := by
  classical
  let i : dualNumberLeftComplex k ⟶ dualNumberMiddleComplex k := {
    f := fun n => if h : n = 1 then (by subst n; exact 𝟙 _) else 0
    comm' := by
      intro n m hm
      by_cases hn : n = 0
      · subst n
        change (0 : ℤ) + 1 = m at hm
        subst m
        simp only [dualNumberLeftComplex, dualNumberTwoTermComplex, add_eq_right, ↓dreduceIte,
          dualNumberMiddleComplex, Int.reduceAdd, one_ne_zero, zero_ne_one, ↓reduceDIte,
          CochainComplex.of.d, zero_add, eqToHom_refl, Category.comp_id, Category.id_comp,
          Limits.comp_zero]
        exact CategoryTheory.Limits.zero_comp
      · simp [dualNumberLeftComplex, dualNumberMiddleComplex, dualNumberTwoTermComplex,
          CochainComplex.of.d, hn]
  }
  let p : dualNumberMiddleComplex k ⟶ dualNumberRightComplex k := {
    f := fun n => if h : n = 0 then (by subst n; exact 𝟙 _) else 0
    comm' := by
      intro n m hm
      by_cases hn : n = 0
      · subst n
        change (0 : ℤ) + 1 = m at hm
        subst m
        simp only [dualNumberMiddleComplex, dualNumberTwoTermComplex, add_eq_right, ↓dreduceIte,
          dualNumberRightComplex, Int.reduceAdd, one_ne_zero, ↓reduceDIte, CochainComplex.of.d,
          zero_add, eqToHom_refl, Category.comp_id, Limits.comp_zero, Category.id_comp]
        exact (CategoryTheory.Limits.comp_zero).symm
      · simp only [dualNumberMiddleComplex, dualNumberTwoTermComplex, add_eq_right, hn,
          dualNumberRightComplex, ↓reduceDIte, CochainComplex.of.d, Limits.zero_comp,
          dite_eq_ite, ite_self, ↓dreduceIte]
        exact CategoryTheory.Limits.zero_comp
  }
  let a : dualNumberLeftComplex k ⟶ dualNumberLeftComplex k := {
    f := fun n => if h : n = 1 then
      (by
        subst n
        exact 𝟙 _ + ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing k)
          (DualNumber.eps : dualNumberRing k))) else 0
    comm' := by
      intro n m hm
      by_cases hn : n = 0
      · subst n
        simp only [dualNumberLeftComplex, dualNumberTwoTermComplex, add_eq_right, ↓dreduceIte,
          zero_ne_one, ↓reduceDIte, CochainComplex.of.d, zero_add, Int.reduceAdd, one_ne_zero,
          eqToHom_refl, Category.comp_id, Limits.comp_zero, Limits.zero_comp, dite_eq_ite,
          ite_self]
        exact CategoryTheory.Limits.zero_comp
      · simp [dualNumberLeftComplex, dualNumberTwoTermComplex, CochainComplex.of.d, hn]
  }
  refine ⟨i, p, a, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; simp [i, hn]
  · intro n hn; simp [p, hn]
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    dsimp [dualNumberLeftComplex, dualNumberTwoTermComplex, dualNumberRing,
      DualNumberModuleCat] at x
    show x + (DualNumber.eps : dualNumberRing k) * x =
      (1 + (DualNumber.eps : dualNumberRing k)) * x
    rw [add_mul, one_mul]
  · intro n hn; simp [a, hn]
  · let hfun : ∀ n m, (dualNumberLeftComplex k).X n ⟶ (dualNumberMiddleComplex k).X m :=
      fun n m => if h : n = 1 ∧ m = 0 then (by
        rcases h with ⟨rfl, rfl⟩
        exact 𝟙 _) else 0
    have hfun10 : hfun 1 0 = 𝟙 _ := by dsimp [hfun]
    let h : Homotopy (a ≫ i) i := {
      hom := hfun
      zero := by
        intro n m hnm
        dsimp [hfun]
        split_ifs with h
        · rcases h with ⟨rfl, rfl⟩
          exact (hnm (ComplexShape.up_mk 0 1 (by norm_num))).elim
        · rfl
      comm := by
        intro n
        have hdiff : (dualNumberLeftComplex k).d n ((ComplexShape.up ℤ).next n) = 0 := by
          simp [dualNumberLeftComplex, dualNumberTwoTermComplex, CochainComplex.of.d]
          all_goals rfl
        show (a ≫ i).f n =
          (dualNumberLeftComplex k).d n ((ComplexShape.up ℤ).next n) ≫
              hfun ((ComplexShape.up ℤ).next n) n +
            hfun n ((ComplexShape.up ℤ).prev n) ≫
              (dualNumberMiddleComplex k).d ((ComplexShape.up ℤ).prev n) n +
            i.f n
        rw [hdiff, Limits.zero_comp, zero_add]
        by_cases hn : n = 1
        · subst n
          have hp : (ComplexShape.up ℤ).prev 1 = 0 :=
            (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk 0 1 (by norm_num))
          have ha : (a ≫ i).f 1 =
              𝟙 (ModuleCat.of (dualNumberRing k) (dualNumberRing k)) +
                ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing k)
                  (DualNumber.eps : dualNumberRing k)) := by
            show
              (𝟙 (ModuleCat.of (dualNumberRing k) (dualNumberRing k)) +
                ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing k)
                  (DualNumber.eps : dualNumberRing k))) ≫
                  𝟙 (ModuleCat.of (dualNumberRing k) (dualNumberRing k)) =
                𝟙 (ModuleCat.of (dualNumberRing k) (dualNumberRing k)) +
                  ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing k)
                    (DualNumber.eps : dualNumberRing k))
            simp
          have hprev : (dualNumberMiddleComplex k).d 0 1 =
              ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing k)
                (DualNumber.eps : dualNumberRing k)) := by
            simp [dualNumberMiddleComplex, dualNumberTwoTermComplex, CochainComplex.of.d]
          have hi : i.f 1 = 𝟙 (ModuleCat.of (dualNumberRing k) (dualNumberRing k)) := by rfl
          rw [hp, ha, hfun10, hprev, hi]
          exact add_comm _ _
        · have hleft : (a ≫ i).f n = 0 := by simp [a, i, hn]
          have hcomp : hfun n ((ComplexShape.up ℤ).prev n) = 0 := by simp [hfun, hn]
          have hi : i.f n = 0 := by simp [i, hn]
          rw [hleft, hcomp, hi]
          simp only [Limits.zero_comp, zero_add]
    }
    exact HomotopyCategory.eq_of_homotopy _ _ h
  · apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0 <;> simp [i, p, hn]

end Stacks.Examples

end
