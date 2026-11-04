module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.RingTheory.Nagata.Japanese
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduced closure of a point as a scheme

A closed subscheme of a locally Noetherian scheme is again locally Noetherian, and the reduced
closed subscheme supported on the closure of a single point is integral, with that point as its
generic point.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isLocallyNoetherian_subscheme`: a closed subscheme of
  a locally Noetherian scheme is locally Noetherian.
* `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure`: the
  reduced closed subscheme supported on the closure of a point is integral.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure`: the
  closed immersion of that subscheme carries its generic point to the point.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A closed subscheme of a locally Noetherian scheme is locally Noetherian. -/
theorem Scheme.IdealSheafData.isLocallyNoetherian_subscheme {X : Scheme.{u}}
    [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsLocallyNoetherian I.subscheme := by
  let C := I.subschemeCover.openCover
  have : ∀ i, IsAffine (C.X i) := fun i ↦
    inferInstanceAs (IsAffine (Spec (I.subschemeCover.X i)))
  rw [isLocallyNoetherian_iff_of_affine_openCover C]
  intro i
  have : IsNoetherianRing Γ(X, (i : X.affineOpens).1) :=
    IsLocallyNoetherian.component_noetherian ⟨_, (i : X.affineOpens).2⟩
  have : IsNoetherianRing (I.subschemeCover.X i) :=
    Ideal.Quotient.isNoetherianRing (I.ideal (i : X.affineOpens))
  exact isNoetherianRing_of_ringEquiv (I.subschemeCover.X i)
    (Scheme.ΓSpecIso (I.subschemeCover.X i)).commRingCatIsoToRingEquiv.symm

/-- The reduced closed subscheme supported on the closure of a point is integral. -/
@[sga "6 X 1.1.2" "integrality of Z(x)"]
theorem Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure
    {X : Scheme.{u}} (x : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme := by
  have hirr : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact isIrreducible_singleton.closure)
  have hred : IsReduced (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The closed immersion of the reduced closed subscheme supported on `closure {x}` carries the
generic point of that subscheme to `x`. -/
theorem Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure
    {X : Scheme.{u}} (x : X) :
    let _ : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme :=
      Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι
        (genericPoint
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme) =
      x := by
  have := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hclosure :
      closure ({I.subschemeι (genericPoint I.subscheme)} : Set X) = closure ({x} : Set X) := by
    rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, I.range_subschemeι, hI,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  exact isGenericPoint_closure.eq (hclosure ▸ isGenericPoint_closure)

end AlgebraicGeometry
