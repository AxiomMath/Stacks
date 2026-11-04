module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.CoherentAutoequivalence
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExactAlongAnIsomorphism
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor `M ↦ f^*M ⊗^𝐋 ℒ` for an automorphism `f` and an invertible module `ℒ`

Let `f : Y ⟶ X` be an isomorphism of schemes and `ℒ` an invertible `𝒪_Y`-module. The functor
`F'(M) = Lf^*M ⊗^𝐋 ℒ` of [Stacks, Tag 0G27] is
`AlgebraicGeometry.dpull f ⋙ AlgebraicGeometry.dtenR`; this file identifies it with the derived
functor of the exact functor `𝓕 ↦ f^*𝓕 ⊗ ℒ` of modules, so that on modules placed in degree zero it
is `𝓕 ↦ (f^*𝓕 ⊗ ℒ)[0]`, naturally.

* An invertible module is flat: tensoring by it is an equivalence of categories
  (`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible`), hence exact.
* `- ⊗^𝐋 ℒ[0]` is the derived functor of `- ⊗ ℒ` for flat `ℒ`: `ℒ[0]` is K-flat, so the
  derived tensor product is computed by the total tensor complex, which is `- ⊗ ℒ` applied
  degreewise.
* `Lf^*` is the derived functor of `f^*` because `f`, an isomorphism, is flat.

## Main definitions

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.pullbackDerivedTensor`: `M ↦ Lf^*M ⊗^𝐋 ℒ[0]`.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.perfectPullbackDerivedTensor`: the same functor
  on `D_perf`.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.pullbackDerivedTensorIso`: its identification
  with the derived functor of `𝓕 ↦ f^*𝓕 ⊗ ℒ`.

## References

* [Stacks Project, Tag 0G27](https://stacks.math.columbia.edu/tag/0G27)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)
open AlgebraicGeometry.CoherentModuleFunctors RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}}

/-! ### Exactness -/

/-- **Tensoring by an invertible module is exact**: it is an equivalence of categories. -/
theorem isFlat_of_isInvertible (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L := by
  have := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible
    (O := Y.presheaf) (hO := Y.ringCatSheaf.2) L (hL := hL)
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- **Inverse image along an isomorphism of schemes preserves finite limits.** -/
theorem preservesFiniteLimits_pullback_of_isIso (f : Y ⟶ X) [IsIso f] :
    PreservesFiniteLimits (Scheme.Modules.pullback f) :=
  preservesFiniteLimits_modulesPullback_of_flat f

/-! ### Tensoring by a flat module placed in degree zero -/

section Tensor

variable (Y)

/-- **For a K-flat right factor, the canonical map `𝓕[0] ⊗^𝐋 ℒ[0] ⟶ Tot(𝓕[0] ⊗ ℒ[0])` is an
isomorphism**, `ℒ` flat. -/
theorem isIso_toTensorSingleNatTrans_app_of_isFlat (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L) (A : Y.Modules) :
    IsIso ((Stacks.DerivedTensor.RingedSite.toTensorSingleNatTrans Y.toRingedSpace.sheaf
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) L).app A) := by
  have hK := Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.toRingedSpace.sheaf L
    hL 0
  dsimp only [Stacks.DerivedTensor.RingedSite.toTensorSingleNatTrans]
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Y.toRingedSpace.sheaf).toTensor_eq_comparisonRight
    ((CochainComplex.singleFunctor _ 0).obj A) ((CochainComplex.singleFunctor _ 0).obj L) hK]
  infer_instance

/-- **`𝓕[0] ⊗^𝐋 ℒ[0] ≅ (𝓕 ⊗ ℒ)[0]` naturally in `𝓕`, for a flat `ℒ`**: the canonical map
`Stacks.DerivedTensor.RingedSite.tensorSingleNatTrans` is invertible, `ℒ[0]` being K-flat. -/
def singleDerivedTensorIso (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L) :
    DerivedCategory.singleFunctor Y.Modules 0 ⋙
        dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).flip.obj L ⋙
        DerivedCategory.singleFunctor Y.Modules 0 :=
  have hiso : IsIso (Stacks.DerivedTensor.RingedSite.toTensorSingleNatTrans
      Y.toRingedSpace.sheaf (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) L) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun A =>
      isIso_toTensorSingleNatTrans_app_of_isFlat Y L hL A
  (Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0) _ ≪≫
      Functor.isoWhiskerLeft _ ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        Y.toRingedSpace.sheaf).tensor.flip.mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L))) ≪≫
    @asIso _ _ _ _ (Stacks.DerivedTensor.RingedSite.toTensorSingleNatTrans Y.toRingedSpace.sheaf
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) L) hiso ≪≫
    Stacks.DerivedTensor.RingedSite.totSingleIso Y.toRingedSpace.sheaf L

end Tensor

/-! ### The functor `M ↦ Lf^*M ⊗^𝐋 ℒ` -/

/-- **The functor `M ↦ Lf^*M ⊗^𝐋 ℒ` of [Stacks, Tag 0G27]**, for `f : Y ⟶ X` and an
`𝒪_Y`-module `ℒ` (placed in degree zero). -/
abbrev pullbackDerivedTensor (f : Y ⟶ X) (L : Y.Modules) :
    DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  dpull f ⋙ dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L)

/-- **On modules placed in degree zero, `M ↦ Lf^*M ⊗^𝐋 ℒ` is `𝓕 ↦ (f^*𝓕 ⊗ ℒ)[0]`**, naturally,
for `f` an isomorphism and `ℒ` flat. -/
def singlePullbackDerivedTensorIso (f : Y ⟶ X) [IsIso f] (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L) :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ pullbackDerivedTensor f L ≅
      pullbackTensor f L ⋙ DerivedCategory.singleFunctor Y.Modules 0 :=
  let e₁ : DerivedCategory.singleFunctor X.Modules 0 ⋙ dpull f ≅
      Scheme.Modules.pullback f ⋙ DerivedCategory.singleFunctor Y.Modules 0 :=
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor X.Modules 0)
        (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategoryOfIsIso
          f.toLRSHom.toShHom) ≪≫
      (modulePullback f.toLRSHom.toShHom).mapDerivedCategorySingleFunctor 0
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e₁ (dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f) (singleDerivedTensorIso Y L hL) ≪≫
    (Functor.associator _ _ _).symm

/-- `M ↦ Lf^*M ⊗^𝐋 ℒ` commutes with the shift: derived pullback does ([Stacks, Tag 06YJ]), and so
does the derived tensor product in its first variable ([Stacks, Tag 06YU]). -/
instance commShift_pullbackDerivedTensor (f : Y ⟶ X) (L : Y.Modules) :
    (pullbackDerivedTensor f L).CommShift ℤ :=
  letI : (dpull f).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift (f := f.toLRSHom.toShHom)
  letI : (dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L)).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Y.toRingedSpace.sheaf).commShift_left _
  Functor.CommShift.comp (F := dpull f) (G := dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L))

/-- **`M ↦ Lf^*M ⊗^𝐋 ℒ` is exact**: derived pullback is ([Stacks, Tag 06YJ]), and so is the derived
tensor product in its first variable ([Stacks, Tag 06YU]). -/
instance isTriangulated_pullbackDerivedTensor (f : Y ⟶ X) (L : Y.Modules) :
    (pullbackDerivedTensor f L).IsTriangulated :=
  letI : (dpull f).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift (f := f.toLRSHom.toShHom)
  letI : (dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L)).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Y.toRingedSpace.sheaf).commShift_left _
  haveI : (dpull f).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated (f := f.toLRSHom.toShHom)
  haveI : (dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L)).IsTriangulated :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Y.toRingedSpace.sheaf).exact_left _
  Functor.IsTriangulated.instComp (F := dpull f)
    (G := dtenR Y ((DerivedCategory.singleFunctor _ 0).obj L))

/-- **The functor `M ↦ Lf^*M ⊗^𝐋 ℒ` on perfect complexes**, for `ℒ` perfect in degree zero:
derived pullback and derived tensor product preserve perfectness ([Stacks, Tag 09J5]). -/
@[sga "6 IV 2.6" "special case"]
abbrev perfectPullbackDerivedTensor (f : Y ⟶ X) (L : Y.Modules)
    (hL : IsPerfect (X := Y.toRingedSpace) ((DerivedCategory.singleFunctor Y.Modules 0).obj L)) :
    PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ pullbackDerivedTensor f L) fun E =>
    isPerfect_dtenR _ _ (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E.obj
      E.property) hL

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
