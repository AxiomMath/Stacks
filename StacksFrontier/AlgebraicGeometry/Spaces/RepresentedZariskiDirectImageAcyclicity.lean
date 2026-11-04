module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardInjectiveAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiEpsilonSquare
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion

/-!
# The direct image to the Zariski site of a represented algebraic space, and its acyclic objects

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let
`h_U = yoneda.obj U` be the algebraic space it represents. Restricting a module on the small
étale site of `h_U` to the Zariski opens of `T` is a functor

`ε_* : Mod(𝒪_{h_U}) ⥤ Mod(𝒪_T)`,

the direct image along the morphism of ringed sites `ε : (h_U)_étale ⟶ T_Zar` of Stacks 08H7
read through the identification of the small étale site of `h_U` with that of `T`. This file
records which modules are acyclic for `ε_*`:

* a quasi-coherent module (Stacks 03DW and 01XB on the affine opens of `T`, in the form
  `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`);
* the direct image of an injective module along any morphism of algebraic spaces into `h_U`
  (Stacks 072Z, `AlgebraicGeometry.Space.isTotallyAcyclic_modulePushforward_of_injective`).

Both come from one criterion (Stacks 072W in the form
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`):
`R ᵖ ε_* M` vanishes as soon as the cohomology of `M` over the étale chart of every affine open of
`T` vanishes in degree `p`, the affine opens forming a basis of `T`.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiDirectImageSchemeModules`: the functor `ε_*`.

## Main results

* `Stacks.Cohomology.isZero_rightDerived_evaluation_of_isTotallyAcyclic`: a sheaf of modules
  whose underlying abelian sheaf is totally acyclic has no higher cohomology over any object, on
  a site whose objects need not be small.
* `Space.isZero_rightDerived_representedZariskiDirectImage_of_isQuasicoherentOnSite`, in the
  namespace `AlgebraicGeometry`: `R ᵖ ε_* M = 0` for `p > 0` and `M` quasi-coherent.
* `AlgebraicGeometry.Space.isZero_rightDerived_representedZariskiDirectImage_modulePushforward`:
  `R ᵖ ε_* (f_* I) = 0` for `p > 0`, `I` injective.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtale
  AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtaleRingedSite
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtaleRingedSite

namespace Stacks.Cohomology

universe u u'

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{max u' u} (Sheaf J AddCommGrpCat.{u})] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (_root_.SheafOfModules.{u} R)] [HasExt.{max u' u} (_root_.SheafOfModules.{u} R)]
  [HasWeakSheafify J (Type u)]

/-- **A totally acyclic sheaf of modules has no higher cohomology over any object.** If the
abelian sheaf underlying `M` is totally acyclic (Stacks 072Y), then the higher right derived
functors of the sections over every object `W` vanish at `M`: the cohomology over `W` is the
cohomology over the sheaf of sets represented by `W`, the free abelian sheaf on `yoneda.obj W`
being that on its sheafification. -/
theorem isZero_rightDerived_evaluation_of_isTotallyAcyclic (M : _root_.SheafOfModules.{u} R)
    (hM : IsTotallyAcyclic.{max u' u} J ((_root_.SheafOfModules.toSheaf R).obj M)) (W : C)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((_root_.SheafOfModules.evaluation R (op W)).rightDerived p).obj M) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have := Presheaf.isIso_freeAbelianSheaf_map_of_W J (toSheafify J (yoneda.obj W))
    (J.W_toSheafify (yoneda.obj W))
  have h : Subsingleton (Abelian.Ext.{max u' u} ((Presheaf.freeAbelianSheaf J).obj
      (yoneda.obj W)) ((_root_.SheafOfModules.toSheaf R).obj M) (n + 1)) :=
    subsingleton_ext_of_iso (asIso ((Presheaf.freeAbelianSheaf J).map
      (toSheafify J (yoneda.obj W)))) (n + 1)
      (hM ((presheafToSheaf J (Type u)).obj (yoneda.obj W)) (n + 1) (by omega))
  exact ModuleCat.isZero_iff_subsingleton.2
    (ObjectSections.subsingleton_rightDerived_evaluation J R M W n
      (@AddCommGrpCat.isZero_of_subsingleton _ h))

end Stacks.Cohomology

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The direct image to the Zariski site of a represented algebraic space.** A module on the
small étale site of `h_U` is transported to the small étale site of the scheme `T` underlying `U`
and then restricted to the Zariski opens of `T`; this is the direct image `ε_*` of Stacks 08H7. It
is, definitionally, the direct image along the continuous functor taking an open of `T` to its
étale chart of `h_U`. -/
abbrev representedZariskiDirectImageSchemeModules :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  representedModuleRestriction B S hS U ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property

/-- The direct image `ε_*` to the Zariski site is additive. -/
instance additive_representedZariskiDirectImageSchemeModules :
    (representedZariskiDirectImageSchemeModules B S hS U).Additive :=
  inferInstanceAs ((representedModuleRestriction B S hS U ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).Additive)

/-- The étale chart of `h_U` attached to an open of the scheme underlying `U`. -/
abbrev representedOpenToChart :
    ((BigFppfOver.toScheme B S hS).obj U).Opens ⥤ SmallEtale B S hS (yoneda.obj U) :=
  _root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleEquivalence B S hS U).inverse

/-- The étale chart of an affine open is an affine chart. -/
theorem isAffineChart_representedOpenToChart {W : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (hW : IsAffineOpen W) :
    IsAffineChart B S hS (yoneda.obj U) ((representedOpenToChart B S hS U).obj W) :=
  hW

/-- **The criterion for `ε_*`-acyclicity.** If the cohomology of `M` in degree `p` vanishes over
the étale chart of every affine open of the scheme underlying `U`, then `R ᵖ ε_* M = 0`. -/
theorem isZero_rightDerived_representedZariskiDirectImage_of_affine
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (∀ W : ((BigFppfOver.toScheme B S hS).obj U).Opens, IsAffineOpen W →
      IsZero (((SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O))
        (op ((representedOpenToChart B S hS U).obj W))).rightDerived p).obj M)) →
    IsZero (((representedZariskiDirectImageSchemeModules B S hS U).rightDerived p).obj M) := by
  intro _ h
  have : EnoughInjectives (SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U))) :=
    enoughInjectives_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  have : (representedOpenToChart B S hS U).IsContinuous (Opens.grothendieckTopology _)
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
    Functor.isContinuous_comp _ _ _ (_root_.AlgebraicGeometry.SmallEtale.topology
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property) _
  let φ : ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⟶
      ((representedOpenToChart B S hS U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology _) (SmallEtale.topology B S hS (yoneda.obj U))).obj
        (ringStructureSheaf B S hS (yoneda.obj U)) :=
    _root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ≫
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).sheafPushforwardContinuous
          RingCat.{u} _ _).map (representedStructureMapInverse B S hS U)
  have : (SheafOfModules.pushforward.{u} (F := representedOpenToChart B S hS U)
      (K := SmallEtale.topology B S hS (yoneda.obj U)) φ).Additive :=
    { map_add := rfl }
  have : HasSheafify (SmallEtale.topology B S hS (yoneda.obj U)) AddCommGrpCat.{u} :=
    SmallEtale.instHasSheafify B S hS (yoneda.obj U) AddCommGrpCat.{u}
  have : (SmallEtale.topology B S hS (yoneda.obj U)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS (yoneda.obj U) AddCommGrpCat.{u}
  have key :=
    Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
      (representedOpenToChart B S hS U)
      (ringStructureSheaf B S hS (yoneda.obj U)) ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf
      φ p M (fun V ↦ ⟨_, generate_affineOpensPresieve_mem _ V, fun W _ hW ↦ h W hW⟩)
  have e := SheafOfModules.pushforwardComp.{u}
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedStructureMapInverse B S hS U)
  have : (SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U) ⋙
      SheafOfModules.pushforward.{u} (_root_.AlgebraicGeometry.SmallEtale.structureMap
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property)).Additive :=
    additive_representedZariskiDirectImageSchemeModules B S hS U
  exact IsZero.of_iso key ((Functor.rightDerivedIsoOfNatIso e p).app M)

/-- **A quasi-coherent module is `ε_*`-acyclic.** Over the étale chart of an affine open of the
scheme underlying `U` a quasi-coherent module has no higher cohomology (Stacks 03DW with 01XB,
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`). -/
theorem isZero_rightDerived_representedZariskiDirectImage_of_isQuasicoherentOnSite
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    have := hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    IsZero (((representedZariskiDirectImageSchemeModules B S hS U).rightDerived p).obj M) :=
  isZero_rightDerived_representedZariskiDirectImage_of_affine B S hS U M p fun _ hW ↦
    isZero_rightDerived_evaluation_of_isAffineChart B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) M hM _ (isAffineChart_representedOpenToChart B S hS U hW)
      p hp

/-- **The direct image of an injective module into a represented algebraic space is
`ε_*`-acyclic.** Its underlying abelian sheaf is totally acyclic (Stacks 072Z), so it has no higher
cohomology over any étale chart. -/
theorem isZero_rightDerived_representedZariskiDirectImage_modulePushforward
    {X : AlgebraicSpaces B S hS}
    (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (I : Modules.{u, u} B S hS X.1 X.2) (hI : Injective I) (p : ℕ) (hp : 0 < p) :
    have := hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    IsZero (((representedZariskiDirectImageSchemeModules B S hS U).rightDerived p).obj
      ((modulePushforward B S hS f).obj I)) := by
  have : HasWeakSheafify (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).J (Type u) :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS (yoneda.obj U)) (Type u))
  have := enoughInjectives_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  have : HasExt.{u + 1} (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :=
    HasExt.standard _
  exact isZero_rightDerived_representedZariskiDirectImage_of_affine B S hS U _ p fun W _ ↦
    Stacks.Cohomology.isZero_rightDerived_evaluation_of_isTotallyAcyclic.{u, u + 1}
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).J _ _
      (isTotallyAcyclic_modulePushforward_of_injective (hZ := hI) B S hS f I) _ p hp

end AlgebraicGeometry.Space

end
