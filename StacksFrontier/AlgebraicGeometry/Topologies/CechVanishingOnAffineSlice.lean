module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechAmitsurComparisonOnTheSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceAlgebraAdjunction

/-!
# Čech vanishing on the slice of all schemes over `S` at an affine object

This file assembles [Stacks, Tag 03FJ] into the form the Čech-vanishing criterion for sheaf
cohomology consumes: a statement about the Čech cohomology of an **abelian** presheaf on
`Over S`, for a one-member covering of an object `U` of `Over S` with affine total space by an
affine object.

Four things have to be composed, and each is elsewhere:

* the adjunction `(CommAlgCat (ULift Γ(U.left, 𝒪)))ᵒᵖ ⥤ Over U` of
  `StacksFrontier/AlgebraicGeometry/Topologies/AffineSliceAlgebraAdjunction.lean`, which is what
  makes Tag 03FJ available over `Over S` rather than only over `Scheme` with `U = Spec R`, and
  which discharges the termwise identification outright;
* the slice-coefficient form of the comparison, from
  `StacksFrontier/AlgebraicGeometry/Descent/Module/CechAmitsurComparisonOnTheSlice.lean`, because
  the `R`-module structure on the coefficients exists only on the slice at `U`;
* the transport from `ModuleCat R` coefficients to `AddCommGrpCat` coefficients, and
* the transport from the slice at `U` back to `Over S`,

the last two from
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/ComplexAlongACoefficientFunctor.lean`.

## Main definitions

No definitions are introduced.

## Main results

* `AlgebraicGeometry.isZero_cechCohomology_singleton_succ_overAffine`: **the assembled
  statement.**  For `A` faithfully flat over `R = Γ(U.left, 𝒪)` and an abelian presheaf on
  `Over S` whose restriction to the slice at `U` underlies a presheaf of `R`-modules agreeing
  with the base change `Γ(-, 𝒪) ⊗_R M` on the fibre powers, the Čech cohomology of the
  one-member covering vanishes in every positive degree.

## Implementation notes

The coefficient data comes in three pieces, and the split is exactly where the mathematics
puts it.  `H` is the presheaf of `R`-modules on the slice; `e` identifies the abelian presheaf
with its underlying abelian groups; and `hpow` is the base-change comparison, demanded only at
the fibre powers `V ×_U ⋯ ×_U V`.  Only `hpow` is a mathematical hypothesis — it is
quasi-coherence of the module, and it is discharged by
`Stacks.Sites.isIso_tensorToSectionsApp`, those powers being affine.  Asking it on the whole
slice would be asking for something false; see
`Stacks.Descent.cechCosimplicialObjectIsoAmitsurOfPowerSections`.

No hypothesis about the fibre powers themselves is carried: the adjunction supplies the
termwise identification through
`Stacks.CechSite.isColimitPowerSectionsCoconeOfAdjunction`, so neither `hcolim` nor `hiso`
appears.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open Stacks.CechSite Stacks.Descent

universe u m

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left] (A : Type u) (M : Type m) [CommRing A]
  [Algebra (Γ(U.left, ⊤) : Type u) A] [AddCommGroup M] [Module (Γ(U.left, ⊤) : Type u) M]

/-- **Stacks 03FJ for a one-member covering of an affine object of `Over S` by an affine
object, with abelian-group coefficients.** -/
public theorem isZero_cechCohomology_singleton_succ_overAffine
    [Module.FaithfullyFlat (Γ(U.left, ⊤) : Type u) A]
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u m})
    (H : (Over U)ᵒᵖ ⥤ ModuleCat.{max u m} (Γ(U.left, ⊤) : Type u))
    (e : (Over.forget U).op ⋙ F ≅
      H ⋙ forget₂ (ModuleCat.{max u m} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{max u m})
    (a : CommAlgCat.{u} (ULift.{u} (Γ(U.left, ⊤) : Type u)))
    (hpow : powerSections ((overAffineAlgSpec U).obj (op a)) H ≅
      powerSections ((overAffineAlgSpec U).obj (op a)) (overAffineAlgΓ U).leftOp ⋙
        amitsurCoefficients.{u, u, m} (Γ(U.left, ⊤) : Type u) M)
    (harrow : sectionsTerminalArrow ((overAffineAlgSpec U).obj (op a))
        (overAffineAlgΓ U).leftOp ≅
      algebraMapArrow (Γ(U.left, ⊤) : Type u) A)
    (p : ℕ) :
    IsZero (cechCohomology
      (PreZeroHypercover.singleton.{max u m} ((overAffineAlgSpec U).obj (op a)).hom) F
        (p + 1)) :=
  isZero_cechCohomology_of_isZero_sliceModule _ (Γ(U.left, ⊤) : Type u) F H e (p + 1)
    (isZero_sliceCechCohomology_singleton_succ_of_adjunction_of_powerSections H
      (overAffineAlgAdjunction U) a hpow harrow p)

end AlgebraicGeometry

end
