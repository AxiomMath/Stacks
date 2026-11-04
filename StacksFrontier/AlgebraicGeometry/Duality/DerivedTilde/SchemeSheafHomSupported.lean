module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedPerfectFactorizationStandard
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPerfectHomQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionPerfectSupport
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSheafPerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.RestrictionOfPerfectObjects

/-!
# The derived internal Hom into a complex with support

Let `X` be a scheme, `T ⊆ X` a closed subset and `E` an object of `D(𝒪_X)` whose cohomology is
supported on `T`. Then so is the cohomology of `R𝓗om_{𝒪_X}(P, E)`, for every object `P`: the
complexes supported on a closed subset form an ideal for the derived internal Hom in its target
variable.

## Main results

* `AlgebraicGeometry.cohomologySupportedOn_derivedSheafHom`: if the cohomology of `E` is
  supported on a closed subset `T`, then so is the cohomology of `R𝓗om_{𝒪_X}(P, E)`.

## References

* [Stacks Project, Tag 0A9C](https://stacks.math.columbia.edu/tag/0A9C)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules (ringedSite)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- An additive functor carries a zero object to a zero object. -/
private theorem isZero_obj_of_additive {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) (hF : F.Additive) {Z : C} (hZ : IsZero Z) : IsZero (F.obj Z) :=
  have := hF
  Functor.map_isZero F hZ

/-- For `X` a scheme, `T ⊆ X` closed and `E` an object of `D(𝒪_X)` with cohomology supported on
`T`, the cohomology of `R𝓗om_{𝒪_X}(P, E)` is supported on `T` for every `P`. -/
theorem cohomologySupportedOn_derivedSheafHom (X : Scheme.{u}) {T : Set X} (hT : IsClosed T)
    (P E : (ringedSite X.sheaf).DerivedModules)
    (hE : CohomologySupportedOn X.ringCatSheaf T E) :
    CohomologySupportedOn X.ringCatSheaf T
      (((ringedSite X.sheaf).derivedSheafHomBifunctor.obj (op P)).obj E) := by
  let U : X.Opens := Stacks.Duality.Supported.complementOpenOfIsClosed hT
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := X.ringCatSheaf) U
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := X.ringCatSheaf) U
  have h := Stacks.DerivedQCoh.cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict U _
    (IsZero.of_iso (isZero_obj_of_additive _ (RingedSite.additive_derivedSheafHom_obj _ _)
      (Stacks.DerivedQCoh.isZero_derivedRestrict_of_cohomologySupportedOn_of_subset_compl T U
        subset_rfl E hE)) (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso U P E))
  rwa [show ((U : Set X))ᶜ = T from compl_compl T] at h

end AlgebraicGeometry

end
