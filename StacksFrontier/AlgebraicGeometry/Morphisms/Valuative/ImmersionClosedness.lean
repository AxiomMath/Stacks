module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# When an immersion is a closed immersion: the valuative criterion

A locally closed immersion of schemes is a *closed* immersion exactly when its range is closed,
hence exactly when it is universally closed, hence — if it is quasi-compact — exactly when it
satisfies the existence part of the valuative criterion.

If `j : Z ⟶ S` is a quasi-compact immersion through which exactly the base changes `g : T ⟶ S`
satisfying some condition `P` factor, then `j` is a closed immersion exactly when `P` *lifts along
valuation rings*: for every valuation ring `A` with fraction field `K` and every `a : Spec A ⟶ S`,
if `P` holds for the restriction of `a` to `Spec K` then `P` holds for `a`.

## Main definitions

* `AlgebraicGeometry.ValuativeLifting` is the lifting condition on a predicate on base changes: a
  predicate true of `a : Spec A ⟶ S` whenever it is true of the composite `Spec K ⟶ Spec A ⟶ S`
  with the fraction field of a valuation ring `A`.

## Main results

* `AlgebraicGeometry.isClosedImmersion_iff_isClosed_range`: an immersion is a closed immersion
  exactly when its range is closed.
* `AlgebraicGeometry.isClosedImmersion_iff_universallyClosed`: an immersion is a closed immersion
  exactly when it is universally closed.
* `AlgebraicGeometry.isClosedImmersion_iff_valuativeCriterion`: a quasi-compact immersion is a
  closed immersion exactly when it satisfies the existence part of the valuative criterion.
* `AlgebraicGeometry.isClosedImmersion_iff_valuativeLifting`: a quasi-compact immersion through
  which exactly the base changes satisfying `P` factor is a closed immersion exactly when `P` lifts
  along valuation rings.
* `AlgebraicGeometry.isClosedImmersion_of_valuativeLifting` is the direction of that equivalence
  which concludes closedness.
* `AlgebraicGeometry.isClosedImmersion_hom_iff_valuativeLifting_of_representableBy` is the same
  equivalence for a functor on the slice category over the base and a representing object.

## Implementation notes

The first equivalence is `AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion` together with the
fact that an immersion is a preimmersion; the second adds that a universally closed morphism is a
closed map, so that its range — the image of the whole space — is closed. The third is Mathlib's
`AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`.

Passing between the valuative criterion and `ValuativeLifting` uses that an immersion is a
monomorphism: the criterion demands a lift making *both* triangles commute, whereas the
factorization condition supplies only the triangle over the base. The remaining triangle is then
forced, since both of its sides become equal after composition with `j`.

## References

* [Stacks Project, Tag 01IQ](https://stacks.math.columbia.edu/tag/01IQ)
* [Stacks Project, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0)
* [Stacks Project, Tag 01KF](https://stacks.math.columbia.edu/tag/01KF)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry

variable {Z S : Scheme.{u}} (j : Z ⟶ S)

/-- An immersion is a closed immersion exactly when its range is closed. -/
theorem isClosedImmersion_iff_isClosed_range [IsImmersion j] :
    IsClosedImmersion j ↔ IsClosed (Set.range j.base) :=
  ⟨fun _ ↦ j.isClosedEmbedding.isClosed_range, fun h ↦ .of_isPreimmersion j h⟩

/-- An immersion is a closed immersion exactly when it is universally closed. -/
theorem isClosedImmersion_iff_universallyClosed [IsImmersion j] :
    IsClosedImmersion j ↔ UniversallyClosed j := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ .of_isPreimmersion j ?_⟩
  simpa using j.isClosedMap _ isClosed_univ

/-- The valuative criterion for an immersion to be a closed immersion: a quasi-compact immersion is
a closed immersion exactly when every valuative commutative square over it has a lift. -/
theorem isClosedImmersion_iff_valuativeCriterion [IsImmersion j] [QuasiCompact j] :
    IsClosedImmersion j ↔ ValuativeCriterion.Existence j := by
  rw [isClosedImmersion_iff_universallyClosed]
  exact ⟨fun h ↦ (UniversallyClosed.eq_valuativeCriterion ▸ h).1,
    fun h ↦ UniversallyClosed.of_valuativeCriterion j h⟩

/-- A predicate on the morphisms into a scheme `S` *lifts along valuation rings* if, for every
valuation ring `A` with fraction field `K` and every `a : Spec A ⟶ S`, the predicate holds for `a`
as soon as it holds for the restriction of `a` to the generic point `Spec K`. -/
def ValuativeLifting {S : Scheme.{u}} (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ S) → Prop) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] (a : Spec (.of A) ⟶ S),
    P (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ a) → P a

/-- A quasi-compact immersion `j : Z ⟶ S` through which exactly the morphisms satisfying a
predicate `P` factor is a closed immersion if and only if `P` lifts along valuation rings. -/
theorem isClosedImmersion_iff_valuativeLifting [IsImmersion j] [QuasiCompact j]
    (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ S) → Prop)
    (hP : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S), P g ↔ ∃ h : T ⟶ Z, h ≫ j = g) :
    IsClosedImmersion j ↔ ValuativeLifting P := by
  rw [isClosedImmersion_iff_valuativeCriterion]
  refine ⟨fun H A _ _ _ K _ _ _ a ha ↦ ?_, fun H sq ↦ ?_⟩
  · obtain ⟨g, hg⟩ := (hP _).mp ha
    obtain ⟨l, _, hl⟩ := (H { R := A, K := K, i₁ := g, i₂ := a, commSq := ⟨hg⟩ }).exists_lift
    exact (hP a).mpr ⟨l, hl⟩
  · obtain ⟨l, hl⟩ := (hP sq.i₂).mp (H sq.R sq.K sq.i₂ ((hP _).mpr ⟨sq.i₁, sq.commSq.w⟩))
    exact ⟨⟨⟨l, (cancel_mono j).mp (by rw [Category.assoc, hl, ← sq.commSq.w]), hl⟩⟩⟩

/-- A quasi-compact immersion through which exactly the morphisms satisfying `P` factor is a closed
immersion once `P` lifts along valuation rings. -/
theorem isClosedImmersion_of_valuativeLifting [IsImmersion j] [QuasiCompact j]
    (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ S) → Prop)
    (hP : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S), P g ↔ ∃ h : T ⟶ Z, h ≫ j = g)
    (H : ValuativeLifting P) : IsClosedImmersion j :=
  (isClosedImmersion_iff_valuativeLifting j P hP).mpr H

/-- The same criterion for a functor on the slice category over `S`: if the structure morphism of a
representing object is a quasi-compact immersion, it is a closed immersion exactly when having a
section over `T` lifts along valuation rings. -/
theorem isClosedImmersion_hom_iff_valuativeLifting_of_representableBy
    {G : (Over S)ᵒᵖ ⥤ Type v} {W : Over S} (e : G.RepresentableBy W)
    [IsImmersion W.hom] [QuasiCompact W.hom] :
    IsClosedImmersion W.hom ↔
      ValuativeLifting fun ⦃T : Scheme.{u}⦄ (g : T ⟶ S) ↦ Nonempty (G.obj (.op (Over.mk g))) := by
  refine isClosedImmersion_iff_valuativeLifting W.hom _ fun {T} g ↦ ?_
  refine ⟨fun h ↦ ⟨(e.homEquiv.symm h.some).left, Over.w _⟩, ?_⟩
  rintro ⟨h, hh⟩
  exact ⟨e.homEquiv (Over.homMk h hh)⟩

end AlgebraicGeometry

add_to_stacks 01IQ AlgebraicGeometry.isClosedImmersion_iff_isClosed_range

end
