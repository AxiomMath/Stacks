module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleAssociatedModulePicard
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerChowWitness
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Basic

/-!
# Twisted cohomology on a represented algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`.  Write
`Φ = (−)ᵃ` for the passage from `𝒪_T`-modules to modules on the small étale site of the
algebraic space `yoneda.obj U`: the associated module on the small étale site of `T`
(`AlgebraicGeometry.SmallEtale.associatedModule`) followed by the identification of that site
with the small étale site of `yoneda.obj U`
(`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`).  On quasi-coherent modules
`Φ` is the equivalence of Stacks 03DX,
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.

This file shows that `Φ` is compatible with twisting by integer tensor powers of invertible
modules, and concludes that the cohomology of a twist on a represented space proper over a field
`k` has the dimension of the Zariski cohomology of the corresponding twist on the scheme.

## Main results

* `isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule`, in the
  namespace `AlgebraicGeometry.Space`: `Φ` carries invertible modules to invertible modules, by
      Stacks 03EL at the two comparisons and
  `Stacks.SheafOfModules.Picard.isInvertible_map_obj`.
* `AlgebraicGeometry.Space.isInvertible_of_isInvertible_representedAssociatedModule`: conversely,
  a quasi-coherent `𝒪_T`-module whose image is invertible is invertible.  A tensor inverse on the
  space is quasi-coherent, so comes from `T`, and the isomorphism `𝓜 ⊗ 𝓝 ≅ 𝒪_T` is reflected by
  the full faithfulness of Stacks 03DX on quasi-coherent modules.
* `AlgebraicGeometry.Space.representedAssociatedModuleTensorPowerIso`:
  `Φ(𝓛^{⊗ m}) ≅ (Φ𝓛)^{⊗ m}` for every integer `m` (Stacks 01CU), by
  `Stacks.SheafOfModules.TensorPower.mapTensorPowerIso`.
* `AlgebraicGeometry.Space.representedAssociatedModuleTwistedSheafIso`: **`Φ` carries the twist
  `𝓕 ⊗ 𝓛₁^{⊗ n₁} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` on `T` to the twist of `Φ𝓕` by any family isomorphic to
  the `Φ𝓛_j`.**
* `AlgebraicGeometry.Space.representedTwistedCohomologyComparison`: **the hypothesis
  `AlgebraicGeometry.Space.RepresentedTwistedCohomologyComparison` holds**: every invertible module
  on a represented space proper over `k` comes from an invertible module on the scheme, and the
  cohomology of the twists on the two sides have the same dimension in every degree, by
  `AlgebraicGeometry.Space.finrank_representedCohomology_eq_finrank_cohomologyOverField`.

## Implementation notes

On the side of the algebraic space the tensor products and powers are stated at the spelling of
`AlgebraicGeometry.Space.twistStep`, whose category and topology are the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`; the comparisons of Stacks 03EL are stated at the
topology `AlgebraicGeometry.Space.SmallEtale.topology`.  The two are definitionally equal, but
instance search does not see it, so the equivalence instances for tensoring with an invertible
module are passed explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **`Φ` carries the structure sheaf to the structure sheaf**, in the packaging of
`Stacks.SheafOfModules.Picard.UnitIso`: the associated module of `𝒪_T` is the structure sheaf of
the small étale site of `T`, which the identification of sites carries to the structure sheaf of
`yoneda.obj U` on the nose. -/
def representedAssociatedModuleUnitIso :
    Stacks.SheafOfModules.Picard.UnitIso.{u, u, u, u + 1, u}
      (J₂ := SmallEtale.topology B S hS (yoneda.obj U))
          ((BigFppfOver.toScheme B S hS).obj U).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _)
      (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor) :=
  (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
    (_root_.AlgebraicGeometry.SmallEtale.associatedModulePicardUnitIso (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ≪≫ Iso.refl _

/-- **`Φ` carries the tensor product sheaf to the tensor product sheaf**, in the packaging of
`Stacks.SheafOfModules.Picard.TensorIso`: Stacks 03EL for the associated module
(`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso'`) followed by its compatibility with the
identification of sites (`AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso`). -/
def representedAssociatedModuleTensorIso :
    Stacks.SheafOfModules.Picard.TensorIso.{u, u, u, u + 1, u}
      (J₂ := SmallEtale.topology B S hS (yoneda.obj U))
          ((BigFppfOver.toScheme B S hS).obj U).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _)
      (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor) := fun L N =>
  (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleTensorIso' (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property L N) ≪≫
    representedSmallEtaleModuleTensorIso B S hS U _ _

/-- **The module on `yoneda.obj U` associated with an invertible `𝒪_T`-module is invertible.** -/
theorem isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj U).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _) L) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property
      ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj L)) :=
  Stacks.SheafOfModules.Picard.isInvertible_map_obj _ _ _ _ _
    (representedAssociatedModuleUnitIso B S hS U) (representedAssociatedModuleTensorIso B S hS U)
    L hL

/-- **`Φ` commutes with integer tensor powers of an invertible module** (Stacks 01CU):
`Φ(𝓛^{⊗ m}) ≅ (Φ𝓛)^{⊗ m}` for every `m : ℤ`, the power on the space being the one the twists
`AlgebraicGeometry.Space.twistStep` use. -/
def representedAssociatedModuleTensorPowerIso (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [hL : SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj U).presheaf
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 L] (n : ℤ) :
    haveI := isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
      B S hS U L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL)
    (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
            (Stacks.SheafOfModules.Invertible.tensorPower
              ((BigFppfOver.toScheme B S hS).obj U).presheaf
              ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 L n)) ≅
      invertibleTensorPower B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj L)) n := by
  haveI hLs := isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
      B S hS U L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL)
  letI hLa : SheafOfModules.IsInvertible (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property
      ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj L)) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hLs
  haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (J := SmallEtale.topology B S hS (yoneda.obj U))
      ⟨structurePresheaf B S hS (yoneda.obj U), Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ CommRingCat RingCat) (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)).O).property⟩).flip.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj L)).IsEquivalence :=
    @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible.{u, u + 1, u}
    (SmallEtale B S hS (yoneda.obj U)) _ (SmallEtale.topology B S hS (yoneda.obj U))
    (structurePresheaf B S hS (yoneda.obj U))
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property _ _
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj L) hLa
  exact @Stacks.SheafOfModules.TensorPower.mapTensorPowerIso.{u, u, u, u + 1, u}
      _ _ (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj U))
      ((BigFppfOver.toScheme B S hS).obj U).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _) _ _
      _ _ (SmallEtale.topology B S hS (yoneda.obj U))
      (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property _ _
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor) L inferInstance this
      (fun M => representedAssociatedModuleTensorIso B S hS U M L)
      (representedAssociatedModuleUnitIso B S hS U) n

/-- The integer tensor powers of an invertible module on an algebraic space depend only on its
isomorphism class: `L ≅ L'` induces `L^{⊗ m} ≅ L'^{⊗ m}`. -/
def invertibleTensorPowerCongr (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    {L L' : Modules.{u, u} B S hS F hF}
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        F hF).O).property L]
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        F hF).O).property L']
    (e : L ≅ L') (m : ℤ) :
    invertibleTensorPower B S hS F hF L m ≅
      invertibleTensorPower B S hS F hF L' m :=
  @Stacks.SheafOfModules.TensorPower.tensorPowerCongr.{u, u + 1, u}
    (smallEtaleRingedSite B S hS F hF).C _
    (smallEtaleRingedSite B S hS F hF).J
    (structurePresheaf B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        F hF).O).property _ _ L L'
    (@Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _
      (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        F hF).O).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL))
    (@Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _
      (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        F hF).O).property _ _ L'
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L' hL'))
    e m

/-- **`Φ` commutes with one twisting step**: `Φ(𝓜 ⊗ 𝓛^{⊗ m}) ≅ Φ𝓜 ⊗ L'^{⊗ m}` for an invertible
`𝓛` on `T` and a module `L'` on the space with `Φ𝓛 ≅ L'`. -/
def representedAssociatedModuleTwistStepIso (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [hL : SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj U).presheaf
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 L]
    (L' : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property L']
    (e : (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj L ≅ L') (m : ℤ) (M :
              ((BigFppfOver.toScheme B S hS).obj U).Modules) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj
              (((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨((BigFppfOver.toScheme B S hS).obj U).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj U).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2⟩).obj
          M).obj (Stacks.SheafOfModules.Invertible.tensorPower
            ((BigFppfOver.toScheme B S hS).obj U).presheaf
            ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 L m)) ≅
      twistStep B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) L' m
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj M) :=
  haveI hΦ := isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
      B S hS U L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL)
  representedAssociatedModuleTensorIso B S hS U M _ ≪≫
    @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).C _
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).J
      (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property _ _ _ _ _ _ (Iso.refl _)
      (representedAssociatedModuleTensorPowerIso B S hS U L m ≪≫
        invertibleTensorPowerCongr B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          (hL := hΦ) e m)

/-- **`Φ` commutes with twisting**: for invertible `𝓛₁, …, 𝓛_r` on `T` and modules `L'_j` on the
space with `Φ𝓛_j ≅ L'_j`, the image of the twist `𝓜 ⊗ 𝓛₁^{⊗ n₁} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` is the twist
of `Φ𝓜` by the `L'_j`. -/
def representedAssociatedModuleTwistedSheafIso {r : ℕ}
    (L : Fin r → ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [∀ j, SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj U).presheaf
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 (L j)]
    (L' : Fin r → Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property (L' j)]
    (e : ∀ j, (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj (L j) ≅ L' j)
              (n : Fin r → ℤ)
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj (twistedSheaf M L n) ≅
      twistedModule B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj M) L' n := by
  suffices h : ∀ (l : List (Fin r)) (M : ((BigFppfOver.toScheme B S hS).obj U).Modules),
      Nonempty ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj (l.foldl (fun N j =>
              ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((BigFppfOver.toScheme B S hS).obj U).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj U).presheaf
            (forget₂ CommRingCat RingCat)
              ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2⟩).obj N).obj
          (Stacks.SheafOfModules.Invertible.tensorPower
            ((BigFppfOver.toScheme B S hS).obj U).presheaf
            ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 (L j) (n j))) M) ≅
        l.foldl (fun N j => twistStep B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          (L' j) (n j) N) ((_root_.AlgebraicGeometry.SmallEtale.associatedModule
              (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj M)) from
    (h (List.finRange r) M).some
  intro l
  induction l with
  | nil => exact fun M => ⟨Iso.refl _⟩
  | cons j t ih =>
    exact fun M => ⟨(ih _).some ≪≫
      foldlTwistStepIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) L' n t
        (representedAssociatedModuleTwistStepIso B S hS U (L j) (L' j) (e j) (n j) M)⟩

/-- An invertible module on the represented space is the image under `Φ` of a quasi-coherent
`𝒪_T`-module (Stacks 0B8Q, 03DL and 03DX). -/
private theorem exists_isQuasicoherent_associatedModule_iso_of_isInvertible
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property N) :
    ∃ N' : ((BigFppfOver.toScheme B S hS).obj U).Modules,
      SheafOfModules.IsQuasicoherent N' ∧ Nonempty
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj N' ≅ N) := by
  have hNq : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ N
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ N hN)
  let Q := representedQuasicoherentSchemeEquivalence B S hS U
  exact ⟨(Q.inverse.obj ⟨N, hNq⟩).obj, (Q.inverse.obj ⟨N, hNq⟩).property,
    ⟨(ObjectProperty.ι _).mapIso (Q.counitIso.app ⟨N, hNq⟩)⟩⟩

/-- **A quasi-coherent `𝒪_T`-module whose associated module on `yoneda.obj U` is invertible is
invertible.**  By Stacks 0B8K, `Φ𝓜 ⊗ 𝓝 ≅ 𝒪` for some `𝓝`, which is invertible, hence
quasi-coherent (Stacks 0B8Q and 03DL), hence `Φ𝓝'` for a quasi-coherent `𝓝'` on `T` (Stacks 03DX).
Then `Φ(𝓜 ⊗ 𝓝') ≅ Φ𝒪_T`, and the full faithfulness of Stacks 03DX on quasi-coherent modules gives
`𝓜 ⊗ 𝓝' ≅ 𝒪_T`. -/
theorem isInvertible_of_isInvertible_representedAssociatedModule
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hM : SheafOfModules.IsQuasicoherent M)
    (h : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj M)) :
    Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj U).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _) M := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (L := (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj M)).1 h
  have hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property N :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit (L := N)).2
      ⟨(_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj M,
              ⟨Stacks.SheafOfModules.tensorSheafBraiding _ _ N _ ≪≫ e⟩⟩
  obtain ⟨N', hN', ⟨eN⟩⟩ :=
    exists_isQuasicoherent_associatedModule_iso_of_isInvertible B S hS U N hN
  let Q := representedQuasicoherentSchemeEquivalence B S hS U
  have hMN : SheafOfModules.IsQuasicoherent (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((BigFppfOver.toScheme B S hS).obj U).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj U).presheaf
          (forget₂ CommRingCat RingCat)
              ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2⟩).obj M).obj N') :=
    _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_tensorSheaf_of_isQuasicoherent _ _ _ hM
      hN'
  let e' : (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj
              (((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨((BigFppfOver.toScheme B S hS).obj U).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj U).presheaf
          (forget₂ CommRingCat RingCat)
              ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2⟩).obj M).obj N') ≅
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS U).functor).obj (SheafOfModules.unit
              ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) :=
    representedAssociatedModuleTensorIso B S hS U M N' ≪≫
      @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
        (SmallEtale B S hS (yoneda.obj U)) _ (SmallEtale.topology B S hS (yoneda.obj U))
        (structurePresheaf B S hS (yoneda.obj U))
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O).property _ _ _ _ _ _ (Iso.refl _)
        eN ≪≫ e ≪≫ (representedAssociatedModuleUnitIso B S hS U).symm
  let e'' : (⟨((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((BigFppfOver.toScheme B S hS).obj U).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj U).presheaf
          (forget₂ CommRingCat RingCat)
              ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2⟩).obj M).obj N', hMN⟩ :
        (SheafOfModules.isQuasicoherent
            ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) ≅
      ⟨SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _⟩ :=
    Q.fullyFaithfulFunctor.preimageIso ((ObjectProperty.fullyFaithfulι _).preimageIso e')
  exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit (L := M)).2
    ⟨N', ⟨(ObjectProperty.ι _).mapIso e''⟩⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-- **The twists of a quasi-coherent module by integer tensor powers of invertible modules are
quasi-coherent**: each step is a tensor product of two quasi-coherent modules. -/
theorem isQuasicoherent_twistedSheaf {X : Scheme.{u}} {r : ℕ} (F : X.Modules)
    (hF : SheafOfModules.IsQuasicoherent F) (L : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] (n : Fin r → ℤ) :
    SheafOfModules.IsQuasicoherent (twistedSheaf F L n) := by
  suffices h : ∀ (l : List (Fin r)) (M : X.Modules), SheafOfModules.IsQuasicoherent M →
      SheafOfModules.IsQuasicoherent (l.foldl (fun N j => ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.2⟩).obj N).obj
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 (L j) (n j))) M)
    from h (List.finRange r) F hF
  intro l
  induction l with
  | nil => exact fun _ hM => hM
  | cons j t ih =>
    exact fun M hM => ih _ (SmallEtale.isQuasicoherent_tensorSheaf_of_isQuasicoherent _ _ _ hM
      (@Scheme.Modules.isQuasicoherent_tensorPower_of_isInvertible X (L j) inferInstance (n j)))

namespace Space

attribute [local instance] hasInjectiveResolutions_modules in
/-- **The twisted cohomology of a quasi-coherent module on a represented algebraic space proper
over `k` is the Zariski cohomology of the corresponding twist on the scheme**, as the dimensions
of `k`-vector spaces in every degree:
`AlgebraicGeometry.Space.RepresentedTwistedCohomologyComparison` holds unconditionally. -/
theorem representedTwistedCohomologyComparison (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) : RepresentedTwistedCohomologyComparison k B hk := by
  intro U w _ F hF r L' hL'
  choose L'' hq he using fun j =>
    exists_isQuasicoherent_associatedModule_iso_of_isInvertible B (Spec (.of k)) hk U (L' j)
      (hL' j)
  let e := fun j => (he j).some
  have hL'' : ∀ j, SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).presheaf
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).ringCatSheaf.2 (L'' j) := fun j =>
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (isInvertible_of_isInvertible_representedAssociatedModule B (Spec (.of k)) hk U _
        (hq j)
        (@Stacks.SheafOfModules.isInvertible_of_iso.{u, u + 1, u}
          (SmallEtale B (Spec (.of k)) hk (yoneda.obj U)) _
          (SmallEtale.topology B (Spec (.of k)) hk (yoneda.obj U))
          (structurePresheaf B (Spec (.of k)) hk (yoneda.obj U))
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk
            (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U)).O).property _ _ _ _
          (e j).symm (hL' j)))
  refine ⟨fun j => L'' j, hL'', fun n i => ?_⟩
  have hG := @isQuasicoherent_twistedSheaf _ _ F hF (fun j => L'' j) hL'' n
  have h1 := finrank_representedCohomology_eq_finrank_cohomologyOverField B k hk U _ hG i
  have h2 := congrArg (fun g => Module.finrank k (cohomologyOverField k g
      (@twistedSheaf _ _ F (fun j => L'' j) hL'' n) i))
    (toScheme_map_eq_representedStructureMorphism k B hk U w)
  refine Eq.trans ?_ (h1.trans h2.symm)
  exact ((ModuleCat.restrictScalars (baseRingHom k B hk (yoneda.obj U)
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U))).mapIso
    (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (representedStructureRingSheaf B (Spec (.of k)) hk U)).rightDerived i).mapIso
        (@representedAssociatedModuleTwistedSheafIso B (Spec (.of k)) hk U r
          (fun j => L'' j) hL'' L' hL' e n F).symm)).toLinearEquiv.finrank_eq

end Space

end AlgebraicGeometry
