module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StructureSheafCompactObject
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedCompactObject
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportModelComparison
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.CategoryTheory.Triangulated.CompactGeneratorFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring a map from the structure sheaf through a perfect complex with support

Let `X` be a quasi-compact quasi-separated scheme and `T ⊆ X` a closed subset with quasi-compact
complement. Every morphism `𝒪_X[0] ⟶ K` of `D_QCoh(𝒪_X)` whose target has cohomology supported
on `T` factors through a perfect object supported on `T`.

## Main definitions

* `Stacks.Duality.Supported.perfectSupported`: the objects of `D(𝒪_X)` that are perfect and have
  cohomology supported on `T`.
* `Stacks.Duality.Supported.complementOpenOfIsClosed`: the open complement `X ∖ T` of a closed
  subset.

## Main results

* `Stacks.Duality.Supported.hasCoproducts_derivedQuasiCoherentFullSubcategory`: `D_QCoh(𝒪_X)` has
  the direct sums indexed by `Type u`.
* `Stacks.Duality.Supported.exists_fac_perfectSupported`: the factorization.

## Implementation notes

The derived category is taken at the locally small model: it is the model at which
`D_{QCoh,T}(𝒪_X)` has a perfect generator and at which `𝒪_X[0]` is a compact object of
`D_QCoh(𝒪_X)`, the morphisms of the standard model lying in `Type (u + 1)` while the direct sums
are indexed by `Type u`.

## References

* [Stacks Project, Tag 0A9C](https://stacks.math.columbia.edu/tag/0A9C)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Duality.Supported

variable (X : Scheme.{u}) (T : Set X)

/-! ### The perfect complexes supported on `T`, as a property of `D_QCoh(𝒪_X)` -/

/-- Perfectness, as a property of the objects of `D(𝒪_X)` at the spelling the supported
derived category is built from. -/
abbrev isPerfectProp : ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  fun L ↦ IsPerfect (X := X.toRingedSpace) L

/-- Perfectness of objects of `D(𝒪_X)` is invariant under isomorphism. -/
instance isPerfectProp_isClosedUnderIsomorphisms :
    (isPerfectProp X).IsClosedUnderIsomorphisms :=
  Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect

/-- The perfect objects of `D(𝒪_X)` form a triangulated subcategory. -/
instance isPerfectProp_isTriangulated : (isPerfectProp X).IsTriangulated :=
  Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X.toRingedSpace

/-- A direct summand of a perfect object of `D(𝒪_X)` is perfect. -/
instance isPerfectProp_isStableUnderRetracts : (isPerfectProp X).IsStableUnderRetracts :=
  isStableUnderRetracts_isPerfect X

/-- The objects of `D(𝒪_X)` that are perfect and have cohomology supported on `T`. -/
def perfectSupported : ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  isPerfectProp X ⊓ derivedSupported X.ringCatSheaf T

/-- Being perfect and supported on `T` is invariant under isomorphism. -/
instance perfectSupported_isClosedUnderIsomorphisms :
    (perfectSupported X T).IsClosedUnderIsomorphisms := by
  unfold perfectSupported
  infer_instance

/-- The perfect objects of `D(𝒪_X)` supported on `T` form a triangulated subcategory. -/
instance perfectSupported_isTriangulated : (perfectSupported X T).IsTriangulated := by
  unfold perfectSupported
  infer_instance

/-- A direct summand of a perfect object of `D(𝒪_X)` supported on `T` is perfect and supported on
`T`. -/
instance perfectSupported_isStableUnderRetracts :
    (perfectSupported X T).IsStableUnderRetracts :=
  ⟨fun ret hL ↦ ⟨(isPerfectProp_isStableUnderRetracts X).of_retract ret hL.1,
    ObjectProperty.prop_of_retract _ ret hL.2⟩⟩

/-- The perfect complexes supported on `T`, as a property of the objects of `D_QCoh(𝒪_X)`. -/
abbrev perfectSupportedQCoh :
    ObjectProperty (derivedQuasiCoherent X).FullSubcategory :=
  (perfectSupported X T).inverseImage (derivedQuasiCoherent X).ι

/-- A direct summand in `D_QCoh(𝒪_X)` of a perfect complex supported on `T` is perfect and
supported on `T`. -/
instance : (perfectSupportedQCoh X T).IsStableUnderRetracts :=
  ⟨fun ret hL ↦ (perfectSupported X T).prop_of_retract
    (ret.map (derivedQuasiCoherent X).ι) hL⟩

/-! ### The inclusion of `D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)` is exact -/

/-- The inclusion `D_{QCoh,T}(𝒪_X) ⥤ D_QCoh(𝒪_X)` commutes with the shift. -/
noncomputable instance commShift_toQuasiCoherent : (toQuasiCoherent X T).CommShift ℤ :=
  ObjectProperty.commShift_ιOfLE (P := quasiCoherentSupported X T)
    (Q := derivedQuasiCoherent X) (fun _ hK ↦ hK.1)

/-- The inclusion `D_{QCoh,T}(𝒪_X) ⥤ D_QCoh(𝒪_X)` is a triangulated functor. -/
instance isTriangulated_toQuasiCoherent : (toQuasiCoherent X T).IsTriangulated :=
  ObjectProperty.isTriangulated_ιOfLE (P := quasiCoherentSupported X T)
    (Q := derivedQuasiCoherent X) (fun _ hK ↦ hK.1)

/-! ### The factorization -/

section Main

/-- **`D_QCoh(𝒪_X)` has the direct sums indexed by the Grothendieck universe**, at the
`SheafOfModules X.ringCatSheaf` spelling that the supported derived category is built over. -/
theorem hasCoproducts_derivedQuasiCoherentFullSubcategory :
    HasCoproducts.{u} (derivedQuasiCoherent X).FullSubcategory := fun J ↦
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    (SheafOfModules.{u} X.ringCatSheaf) J
  have := derivedQuasiCoherent_isClosedUnderCoproducts X J
  inferInstance

/-- `U = X ∖ T`, the open complement of a closed subset, as an open subscheme of `X`. -/
def complementOpenOfIsClosed {X : Scheme.{u}} {T : Set X} (hT : IsClosed T) : X.Opens :=
  ⟨Tᶜ, hT.isOpen_compl⟩

/-! ### The comparison with the standard model -/

/-- The comparison equivalence from the standard model of `D(𝒪_X)` to the locally small model. -/
abbrev standardToLocallySmall :
    @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules) ≌
      DerivedCategory X.Modules :=
  StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard X.Modules) _

/-- **`𝒪_X[0]` at the standard model is carried to `𝒪_X[0]` at the locally small model** by the
comparison `standardToLocallySmall`. -/
abbrev standardToLocallySmallStructureSheafIso :
    (standardToLocallySmall X).functor.obj
        ((@DerivedCategory.singleFunctor X.Modules _ _
          (HasDerivedCategory.standard X.Modules) 0).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (DerivedPushforward.derivedStructureSheaf X).obj :=
  (StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard X.Modules) _ 0).app
    (SheafOfModules.unit X.ringCatSheaf)

/-- **Perfectness at the locally small model is invariant under isomorphism**: if `Q ≅ Q'` in
`D(𝒪_X)` and `Q` is perfect, then `Q'` is perfect. -/
theorem isPerfect_of_iso_locallySmall {Q Q' : DerivedCategory X.Modules} (e : Q ≅ Q')
    (hQ : IsPerfect (X := X.toRingedSpace) Q) : IsPerfect (X := X.toRingedSpace) Q' :=
  Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.of_iso e hQ

/-- **Cohomological support at the locally small model is invariant under isomorphism**: if
`Q ≅ Q'` in `D(𝒪_X)` and `Q` has cohomology supported on `T`, then so does `Q'`. -/
theorem cohomologySupportedOn_of_iso_locallySmall {Q Q' : DerivedCategory X.Modules} (e : Q ≅ Q')
    (hQ : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T Q) :
    Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T Q' :=
  Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso X.ringCatSheaf T e hQ

/-- **`𝒪_X[0]` is a perfect object of `D(𝒪_X)`**, at the locally small model. -/
theorem isPerfect_structureSheaf_locallySmall :
    IsPerfect (X := X.toRingedSpace) (DerivedPushforward.derivedStructureSheaf X).obj :=
  AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree X _
    (AlgebraicGeometry.isFiniteLocallyFree_unit X)

variable {X T}

/-- **A map from the structure sheaf to a complex with support factors through a perfect complex
with support.** Let `X` be a quasi-compact quasi-separated scheme and `T ⊆ X` closed with
quasi-compact complement, and let `K` be an object of `D(𝒪_X)` with quasi-coherent cohomology
supported on `T`. Then every morphism `𝒪_X[0] ⟶ K` factors as `𝒪_X[0] ⟶ Q ⟶ K` with `Q` perfect
and supported on `T`. -/
theorem exists_fac_perfectSupported [CompactSpace X] [QuasiSeparatedSpace X] (hT : IsClosed T)
    (hTc : IsCompact Tᶜ) (K : DerivedCategory X.Modules)
    (hKqc : derivedQuasiCoherent X K)
    (hKT : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T K)
    (ζ : (DerivedPushforward.derivedStructureSheaf X).obj ⟶ K) :
    ∃ (Q : DerivedCategory X.Modules)
      (a : (DerivedPushforward.derivedStructureSheaf X).obj ⟶ Q) (b : Q ⟶ K),
      IsPerfect (X := X.toRingedSpace) Q ∧
        Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T Q ∧
          a ≫ b = ζ := by
  obtain ⟨G, hGperf, hGgen⟩ :=
    Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported X T hT hTc
  have hcopT := hasCoproducts_quasiCoherentSupportedDerivedCategory X T
  have hcop := hasCoproducts_derivedQuasiCoherentFullSubcategory X
  have hGc : IsCompactObject.{u} G := isCompactObject_of_isPerfect X T G hGperf
  have hGc' : IsCompactObject.{u} ((toQuasiCoherent X T).obj G) :=
    _root_.AlgebraicGeometry.isCompactObject_of_isPerfect X _ hGperf
  have hA : IsCompactObject.{u} (DerivedPushforward.derivedStructureSheaf X :
      (derivedQuasiCoherent X).FullSubcategory) :=
    DerivedPushforward.isCompactObject_derivedStructureSheaf X
  let Ksup : QuasiCoherentSupportedDerivedCategory X T :=
    ⟨K, hKqc, Stacks.Rouquier.derivedSupported_of_cohomologySupportedOn _ _ _ hKT⟩
  let ζ' : (DerivedPushforward.derivedStructureSheaf X : (derivedQuasiCoherent X).FullSubcategory)
      ⟶ (toQuasiCoherent X T).obj Ksup :=
    (ObjectProperty.fullyFaithfulι (derivedQuasiCoherent X)).preimage ζ
  have hpre : (derivedQuasiCoherent X).ι.map ζ' = ζ :=
    (ObjectProperty.fullyFaithfulι (derivedQuasiCoherent X)).map_preimage
      (X := DerivedPushforward.derivedStructureSheaf X)
      (Y := (toQuasiCoherent X T).obj Ksup) ζ
  obtain ⟨Q, a, b, hQ, hab⟩ :=
    exists_fac_of_isWeakTriangulatedGenerator (toQuasiCoherent X T) G hGc hGc' hGgen hA
      (perfectSupportedQCoh X T) ⟨hGperf, G.property.2⟩ Ksup ζ'
  exact ⟨Q.obj, (derivedQuasiCoherent X).ι.map a, (derivedQuasiCoherent X).ι.map b, hQ.1,
    Stacks.Rouquier.cohomologySupportedOn_of_derivedSupported _ _ _ hQ.2,
    ((derivedQuasiCoherent X).ι.map_comp a b).symm.trans
      ((congrArg (derivedQuasiCoherent X).ι.map hab).trans hpre)⟩

end Main

end Stacks.Duality.Supported

end
