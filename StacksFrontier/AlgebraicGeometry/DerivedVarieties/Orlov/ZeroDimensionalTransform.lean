module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.SupportedPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorInstance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The integral transform by a module supported over an affine open is right t-exact

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes with `S` affine, and let `𝓕` be a
quasi-coherent `𝒪_X`-module supported on a closed subset `Z` of an affine open `U ⊆ X` — for
instance a coherent module supported at a closed point. The transform
`N ↦ R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 N)` (`AlgebraicGeometry.fibreTransform`) is right t-exact on objects of
`D(𝒪_{X ×_S Y})` with quasi-coherent cohomology: if `H^j(N) = 0` for `j > a` then the same holds
for the transform.

The derived tensor product is right t-exact in both variables
(`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor`), its cohomology is
quasi-coherent ([Stacks, Tag 08DX]) and supported over `Z`, and over the affine open `U` the
second projection is affine, so its derived direct image preserves the vanishing
(`Stacks.AlgebraicGeometry.SupportedPushforwardReflect.isZero_homology_derivedPushforward_pullback_snd`).

This is the bound on the transforms of the "error" terms in the construction of
[Stacks, Section 0G07]: a kernel concentrated in degrees `≤ a` has its transform concentrated in
degrees `≤ a`.

## Main results

* `AlgebraicGeometry.isZero_homology_fibreTransform_of_isLE`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **Right t-exactness of the transform by a module supported over an affine open.** -/
theorem isZero_homology_fibreTransform_of_isLE [IsAffine S] {U : X.Opens} (hU : IsAffineOpen U)
    {Z : Set X} (hZ : IsClosed Z) (hZU : Z ⊆ U) (𝓕 : X.Modules) (h𝓕 : SheafOfModules.supp 𝓕 ⊆ Z)
    (h𝓕qc : 𝓕.IsQuasicoherent) (N : DerivedCategory (pullback f g).Modules)
    (hN : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (pullback f g).Modules j).obj
      N).IsQuasicoherent) (a : ℤ) (ha : N.IsLE a) (i : ℤ) (hi : a < i) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj (fibreTransform f g N 𝓕)) := by
  let M := (Scheme.Modules.pullback (pullback.fst f g)).obj 𝓕
  let A := (DerivedCategory.singleFunctor (pullback f g).Modules 0).obj M
  have hA : A.IsLE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor (pullback f g).Modules 0).obj M).IsLE 0)
  have hE : (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (pullback f g).toRingedSpace.sheaf).obj A).obj N).IsLE (0 + a) :=
    @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor _ _ _
      (pullback f g).toRingedSpace.sheaf _ _ _ _ _ _ _ _ 0 a hA ha
  rw [zero_add] at hE
  open Stacks.AlgebraicGeometry.SupportedPushforwardReflect in
  exact isZero_homology_derivedPushforward_pullback_snd
    f g hU hZ hZU _
    (TorFormula.isQuasicoherent_homology_derivedTensor (pullback f g) A N
      (isQuasicoherent_homology_singleFunctor_obj (pullback f g) M
        (Stacks.Modules.isQuasicoherent_pullback _ 𝓕 h𝓕qc)) hN)
    (cohomologySupportedOn_fourierMukaiTensor_singleFunctor_pullback f g N 𝓕 Z h𝓕)
    (@DerivedCategory.isZero_of_isLE _ _ _ _ _ a i hi hE)

end AlgebraicGeometry
