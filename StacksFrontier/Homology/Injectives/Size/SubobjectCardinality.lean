module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.SetTheory.Cardinal.Order
import StacksCore.Tactic.StacksAttribute

/-!
# Cardinality of subobjects and of chains of subobjects

Let `C` be an abelian category with a separator `U`. Tag 0E8N bounds, in terms of `U`, how
many subobjects an object of `C` can have: a subobject `P` of `X` is determined by the set of
morphisms `U ⟶ X` that factor through it, so there are at most `2 ^ #(U ⟶ X)` subobjects of
`X`; and a strictly monotone or strictly antitone chain of subobjects of `X` indexed by a
well-ordered type `ι` satisfies `#ι ≤ #(U ⟶ X)`.

## Main definitions

* `Stacks.Injectives.leastGreater`: the least index strictly above a given one in a well-ordered
  type.
* `Stacks.Injectives.monoGapMap`, `Stacks.Injectives.antiGapMap`: a morphism out of `U`
  witnessing a step of a strictly increasing, respectively strictly decreasing, chain of
  subobjects.

## Main results

* `Stacks.Injectives.mk_subobject_le_two_pow_mk_hom`: the type of subobjects of `X` has
  cardinality at most `2 ^ #(U ⟶ X)`.
* `Stacks.Injectives.exists_morphism_between_subobjects`: for subobjects `P < Q` of `X` there is
  a morphism `U ⟶ X` factoring through `Q` but not through `P`.
* `Stacks.Injectives.cardinality_le_hom_of_strictMono_subobject` and
  `Stacks.Injectives.cardinality_le_hom_of_strictAnti_subobject`: a strictly increasing,
  respectively strictly decreasing, chain of subobjects of `X` indexed by a well-ordered type
  has cardinality at most `#(U ⟶ X)`.

## Implementation notes

The power set of the source is written as cardinal exponentiation by `2`, and the cardinality
of the morphism type is lifted into the universe of the type of subobjects.

For the chain bounds, the two directions of monotonicity are stated separately. Instead of
choosing a type to represent a cardinal, each result bounds the cardinality of an arbitrary
well-ordered index type directly; this is equivalent to the nonexistence formulation of the
source.

## References

* [Stacks Project, Tag 0E8N](https://stacks.math.columbia.edu/tag/0E8N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The collection of subobjects of an object has cardinality at most the cardinality of the
power set of the morphisms to it from a separator. -/
@[stacks 0E8N "subobject cardinality"]
theorem mk_subobject_le_two_pow_mk_hom {U X : C} (hU : IsSeparator U) :
    Cardinal.mk (Subobject X) ≤
      (2 : Cardinal.{max u v}) ^ Cardinal.lift.{u} (Cardinal.mk (U ⟶ X)) := by
  let Φ : Subobject X → Set (ULift.{u} (U ⟶ X)) :=
    fun P ↦ { f | P.Factors f.down }
  have hle (P Q : Subobject X) (hPQ : Φ P ⊆ Φ Q) : P ≤ Q := by
    apply Subobject.le_of_factors
    have hf : P.arrow ≫ cokernel.π Q.arrow = 0 :=
      (Preadditive.isSeparator_iff U).1 hU _ fun h ↦ by
      rw [← Category.assoc, ← Q.factorThru_arrow (h ≫ P.arrow)
        (hPQ (show ULift.up (h ≫ P.arrow) ∈ Φ P from P.factors_comp_arrow h)),
        Category.assoc, cokernel.condition, comp_zero]
    let _ : Mono Q.arrow := Subobject.arrow_mono Q
    exact (Q.factors_iff P.arrow).2 ⟨Abelian.monoLift Q.arrow P.arrow hf,
      Abelian.monoLift_comp Q.arrow P.arrow hf⟩
  have hΦ : Function.Injective Φ := fun P Q hPQ ↦
    le_antisymm (hle P Q (by simpa only [hPQ] using (Set.Subset.rfl : Φ Q ⊆ Φ Q)))
      (hle Q P (by simpa only [← hPQ] using (Set.Subset.rfl : Φ P ⊆ Φ P)))
  simpa using Cardinal.mk_le_of_injective hΦ

/-- For subobjects `P < Q` of `X` there is a morphism from a separator `U` to `X` which
factors through `Q` but not through `P`. -/
theorem exists_morphism_between_subobjects {U X : C} (hU : IsSeparator U)
    (P Q : Subobject X) (hPQ : P < Q) :
    ∃ φ : U ⟶ X, Q.Factors φ ∧ ¬ P.Factors φ := by
  let g : (Q : C) ⟶ cokernel P.arrow := Q.arrow ≫ cokernel.π P.arrow
  have hne : g ≠ 0 := fun hg => hPQ.2 (Subobject.le_of_factors ((P.factors_iff Q.arrow).2
    ⟨Abelian.monoLift P.arrow Q.arrow hg, Abelian.monoLift_comp P.arrow Q.arrow hg⟩))
  have hex : ∃ h : U ⟶ (Q : C), h ≫ g ≠ 0 := by
    by_contra! h
    exact hne ((Preadditive.isSeparator_iff U).1 hU _ h)
  obtain ⟨h, hh⟩ := hex
  refine ⟨h ≫ Q.arrow, Q.factors_comp_arrow h, ?_⟩
  intro hp
  have hzero : (h ≫ Q.arrow) ≫ cokernel.π P.arrow = 0 := by
    calc
      (h ≫ Q.arrow) ≫ cokernel.π P.arrow =
          (P.factorThru (h ≫ Q.arrow) hp ≫ P.arrow) ≫ cokernel.π P.arrow :=
        congrArg (fun k => k ≫ cokernel.π P.arrow)
          (P.factorThru_arrow (h ≫ Q.arrow) hp).symm
      _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
  apply hh
  change h ≫ (Q.arrow ≫ cokernel.π P.arrow) = 0
  simpa only [Category.assoc] using hzero

/-- The least index strictly above `i` in a well-ordered type, given that one exists. -/
noncomputable def leastGreater {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    (i : ι) (hi : ∃ j, i < j) : ι :=
  WellFoundedLT.min {j | i < j} ⟨Classical.choose hi, Classical.choose_spec hi⟩

/-- `leastGreater i hi` is strictly greater than `i`. -/
theorem lt_leastGreater {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    (i : ι) (hi : ∃ j, i < j) : i < leastGreater i hi :=
  WellFounded.min_mem wellFounded_lt {j | i < j}
    ⟨Classical.choose hi, Classical.choose_spec hi⟩

/-- `leastGreater i hi` is at most every index strictly greater than `i`. -/
theorem leastGreater_le {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    (i j : ι) (hi : ∃ k, i < k) (hij : i < j) : leastGreater i hi ≤ j :=
  WellFoundedLT.min_le hij

/-- A morphism from the separator `U` witnessing the step of a strictly increasing chain of
subobjects from `i` to the least index above it. -/
noncomputable def monoGapMap {U X : C} (hU : IsSeparator U)
    {ι : Type w} [LinearOrder ι] [WellFoundedLT ι] (f : ι → Subobject X)
    (hf : StrictMono f) (i : ι) (hi : ∃ j, i < j) : U ⟶ X :=
  Classical.choose (exists_morphism_between_subobjects hU (f i)
    (f (leastGreater i hi)) (hf (lt_leastGreater i hi)))

/-- `monoGapMap hU f hf i hi` factors through `f (leastGreater i hi)` but not through `f i`. -/
theorem monoGapMap_spec {U X : C} (hU : IsSeparator U)
    {ι : Type w} [LinearOrder ι] [WellFoundedLT ι] (f : ι → Subobject X)
    (hf : StrictMono f) (i : ι) (hi : ∃ j, i < j) :
    (f (leastGreater i hi)).Factors (monoGapMap hU f hf i hi) ∧
      ¬ (f i).Factors (monoGapMap hU f hf i hi) :=
  Classical.choose_spec (exists_morphism_between_subobjects hU (f i)
    (f (leastGreater i hi)) (hf (lt_leastGreater i hi)))

/-- A morphism from the separator `U` witnessing the step of a strictly decreasing chain of
subobjects from `i` to the least index above it. -/
noncomputable def antiGapMap {U X : C} (hU : IsSeparator U)
    {ι : Type w} [LinearOrder ι] [WellFoundedLT ι] (f : ι → Subobject X)
    (hf : StrictAnti f) (i : ι) (hi : ∃ j, i < j) : U ⟶ X :=
  Classical.choose (exists_morphism_between_subobjects hU
    (f (leastGreater i hi)) (f i) (hf (lt_leastGreater i hi)))

/-- `antiGapMap hU f hf i hi` factors through `f i` but not through `f (leastGreater i hi)`. -/
theorem antiGapMap_spec {U X : C} (hU : IsSeparator U)
    {ι : Type w} [LinearOrder ι] [WellFoundedLT ι] (f : ι → Subobject X)
    (hf : StrictAnti f) (i : ι) (hi : ∃ j, i < j) :
    (f i).Factors (antiGapMap hU f hf i hi) ∧
      ¬ (f (leastGreater i hi)).Factors (antiGapMap hU f hf i hi) :=
  Classical.choose_spec (exists_morphism_between_subobjects hU
    (f (leastGreater i hi)) (f i) (hf (lt_leastGreater i hi)))

omit [Abelian C] in
/-- If `ι` injects into the morphisms `U ⟶ X`, then the cardinality of `ι` is at most that of
`U ⟶ X`. -/
theorem cardinal_le_hom_of_embedding {U X : C} {ι : Type w}
    (g : ι → (U ⟶ X)) (hg : Function.Injective g) :
    Cardinal.lift.{v} (Cardinal.mk ι) ≤ Cardinal.lift.{w} (Cardinal.mk (U ⟶ X)) :=
  (Cardinal.lift_mk_le'.{w, v}).2 ⟨⟨g, hg⟩⟩

/-- If `g i` is nonzero and the `g i` for distinct `i` are distinct, where `g i` is only defined
for `i` with a larger index, then `ι` has cardinality at most that of `U ⟶ X`. -/
private theorem cardinal_le_hom_of_gap_map {U X : C} {ι : Type w} [LinearOrder ι]
    (g : ∀ i : ι, (∃ j, i < j) → (U ⟶ X)) (h0 : ∀ i hi, g i hi ≠ 0)
    (hlt : ∀ i j hi hj, i < j → g i hi ≠ g j hj) :
    Cardinal.lift.{v} (Cardinal.mk ι) ≤ Cardinal.lift.{w} (Cardinal.mk (U ⟶ X)) := by
  classical
  apply cardinal_le_hom_of_embedding (fun i => if hi : ∃ j, i < j then g i hi else 0)
  intro i j hij
  by_cases hi : ∃ k, i < k <;> by_cases hj : ∃ k, j < k
  · simp only [dite_eq_left hi, dite_eq_left hj] at hij
    rcases lt_trichotomy i j with h | h | h
    · exact (hlt i j hi hj h hij).elim
    · exact h
    · exact (hlt j i hj hi h hij.symm).elim
  · simp only [dite_eq_left hi, dite_eq_right hj] at hij
    exact (h0 i hi hij).elim
  · simp only [dite_eq_right hi, dite_eq_left hj] at hij
    exact (h0 j hj hij.symm).elim
  · exact le_antisymm (le_of_not_gt (fun h => hj ⟨i, h⟩)) (le_of_not_gt (fun h => hi ⟨j, h⟩))

/-- A strictly increasing chain of subobjects has cardinality at most the cardinality of the
set of morphisms from a separator to the ambient object. -/
@[stacks 0E8N "chain bound"]
theorem cardinality_le_hom_of_strictMono_subobject {U X : C} (hU : IsSeparator U)
    {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    (f : ι → Subobject X) (hf : StrictMono f) :
    Cardinal.lift.{v} (Cardinal.mk ι) ≤ Cardinal.lift.{w} (Cardinal.mk (U ⟶ X)) := by
  refine cardinal_le_hom_of_gap_map (monoGapMap hU f hf) (fun i hi hz => ?_)
    (fun i j hi hj hlt heq => ?_)
  · exact (monoGapMap_spec hU f hf i hi).2 (hz ▸ Subobject.factors_zero)
  · refine (monoGapMap_spec hU f hf j hj).2 ?_
    rw [← heq]
    exact Subobject.factors_of_le _ (hf.monotone (leastGreater_le i j hi hlt))
      (monoGapMap_spec hU f hf i hi).1

/-- A strictly decreasing chain of subobjects has cardinality at most the cardinality of the
set of morphisms from a separator to the ambient object. -/
@[stacks 0E8N "chain bound"]
theorem cardinality_le_hom_of_strictAnti_subobject {U X : C} (hU : IsSeparator U)
    {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    (f : ι → Subobject X) (hf : StrictAnti f) :
    Cardinal.lift.{v} (Cardinal.mk ι) ≤ Cardinal.lift.{w} (Cardinal.mk (U ⟶ X)) := by
  refine cardinal_le_hom_of_gap_map (antiGapMap hU f hf) (fun i hi hz => ?_)
    (fun i j hi hj hlt heq => ?_)
  · exact (antiGapMap_spec hU f hf i hi).2 (hz ▸ Subobject.factors_zero)
  · refine (antiGapMap_spec hU f hf i hi).2 ?_
    rw [heq]
    exact Subobject.factors_of_le _ (hf.antitone (leastGreater_le i j hi hlt))
      (antiGapMap_spec hU f hf j hj).1

end Stacks.Injectives
