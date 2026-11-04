module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackWhole
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence

/-!
# Restriction of the intersection product to an open subvariety

Restriction of cycles along an open immersion is flat pullback in relative dimension zero
(Tag 02RB), and flat pullback is compatible with the intersection product (Tag 0B0Z). So the
intersection product of two cycles meeting properly restricts to the product of the restrictions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

/-- **The intersection product restricts along an open immersion.** -/
theorem cycleComap_torFormulaCycleIntersectionProduct_of_isOpenImmersion (K : Type u) [Field K]
    [IsAlgClosed K] {X U : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sU] (hX : AlgebraicGeometry.IsRegular X)
    (hU : AlgebraicGeometry.IsRegular U) (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    (dX r s n : ℕ) (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hdU : topologicalKrullDim U = topologicalKrullDim X) (hrs : r + s = dX + n)
    (α : CycleGroup (fieldChowSituation K) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sX (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian sU
    cycleComap j j.isOpenEmbedding.injective
        (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX (n : ℤ) α.1 β.1) =
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sU hU (n : ℤ)
        (cycleComap j j.isOpenEmbedding.injective α.1)
        (cycleComap j j.isOpenEmbedding.injective β.1) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian sU
  have he : topologicalKrullDim U = topologicalKrullDim X + ((0 : ℕ) : WithBot ℕ∞) := by
    rw [hdU]; simp
  obtain ⟨-, h⟩ :=
    Stacks.Intersection.CycleFlatPullback.flatPullback_torFormulaCycleIntersectionProduct_eq
      K sU sX hU hX j hj 0 dX r s n hdX he hrs α β hαβ
  have hr := Stacks.Chow.relativeDimension_of_isOpenImmersion j
  rw [← cycleGroupRestrict_eq_flatPullback (fieldChowSituation K) sX sU j hj hr,
    ← cycleGroupRestrict_eq_flatPullback (fieldChowSituation K) sX sU j hj hr,
    ← cycleGroupRestrict_eq_flatPullback (fieldChowSituation K) sX sU j hj hr] at h
  simp only [Nat.cast_zero, add_zero] at h
  exact h

end Stacks.Intersection.RationalEquivalenceProduct

end
