module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FullyFaithfulSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSectionsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel

/-!
# Derived sections along a cocontinuous morphism of ringed sites

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the functor `u : D ⥤ C`,
and suppose that `u` is also cocontinuous, so that the direct image `f_*` of sheaves of modules
is exact (`Stacks.Cohomology.FullyFaithfulSubsite.preservesFiniteColimits_pushforwardTopos`).
Write `ε : (C_τ, O_C) ⟶ (C_{τ'}, O_C)` and `ε : (D_τ, O_D) ⟶ (D_{τ'}, O_D)` for the comparison
morphisms with the chaotic topologies, so that `Rε_*` sends a complex of sheaves of modules to
the presheaf of modules `V ↦ RΓ(V, -)`.

This file proves that derived sections commute with `f_*`:

`Rε_*(f_* L) ≅ f_*^{ch}(Rε_* L)` naturally in `L ∈ D(O_C)`,

where `f_*^{ch}` is the chaotic direct image: precomposition with `u.op` (the derived inverse
image `dInverseImage` of presheaves of modules along `u`) followed by restriction of scalars along
`f^♯ : O_D ⟶ u⁻¹ O_C`. On sections over an object `V` of `D` this is
`RΓ(V, f_* L) ≅ RΓ(u V, L)`, naturally in `L` and compatibly with the restriction maps.

It also transports the adjunction `Lf^* ⊣ f_*` of
`Stacks.Cohomology.FullyFaithfulSubsite.derivedPullbackAdjunction`, and the invertibility of its
unit for a fully faithful `u` with invertible `f^♯`, from the standard models of the derived
categories — in which the derived pullback of Tag 06YY is constructed — to the locally small
models of Tag 079Q, in which the chaotic comparison `Rε_*` of Tag 0GZS is constructed.

## Main results

* `isIso_derivedEpsilonPushforwardUnit_app_pushforwardTopos`: the direct image of a
  K-injective complex computes `Rε_*`; this needs no cocontinuity.
* `Stacks.Cohomology.FullyFaithfulSubsite.derivedEpsilonPushforwardIso`:
  `Rε_* ∘ f_* ≅ f_*^{ch} ∘ Rε_*`, with its defining compatibility
  `derivedEpsilonPushforwardIso_fac`.
* `Stacks.Cohomology.FullyFaithfulSubsite.derivedEpsilonPushforwardInverseImageIso`: the same,
  with `f_*^{ch}` split as `dInverseImage` followed by restriction of scalars along `f^♯`.
* `Stacks.Cohomology.FullyFaithfulSubsite.smallDerivedPullbackAdjunction` and
  `isIso_smallDerivedPullbackAdjunction_unit`: `Lf^* ⊣ f_*` in the locally small models, with
  invertible unit when `u` is fully faithful and `f^♯` is invertible.

## Implementation notes

The proof of `derivedEpsilonPushforwardIso` is that of
`Stacks.ModulesOnACategory.ChaoticComparison.derivedRestrictionPushforwardIso` (Stacks 0D6G for
`ε`): both sides are right derived functors of the one functor `ε_* ∘ f_* = f_*^{ch} ∘ ε_*`. The
difference is the input making `Rε_* ∘ f_*` a right derived functor. For a slice, restriction
preserves K-injective complexes (Stacks 08FI); for a general cocontinuous `u` it need not, the
left adjoint `f^*` not being exact. Instead, the comparison `ε_*(f_* I) ⟶ Rε_*(f_* I)` is checked
on sections over each object `V` of `D`, where a K-injective resolution of `f_* I` becomes a
quasi-isomorphism by the argument of Stacks 0D6H — sections over `V` are corepresented by
`j_{V!} O_V`, whose derived pullback is `j_{u V!} O_{u V}` because it is flat, and the derived
adjunction of Tag 07A6 moves the question to `I`, which is K-injective
(`Stacks.Cohomology.LerayUnbounded.quasiIso_sectionsOverObject_map`).

Restriction of scalars along `f^♯` is named `fSharpRestrictScalars` rather than written out: the
target of `f^♯` is spelled with the structure sheaf of the ringed topos underlying `X`, the
derived inverse image with that of `X` itself, and instance search does not identify the two
spellings, so that Mathlib's instances for restriction of scalars are not found at the second.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent (dInverseImage)
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (derivedPullback pullbackOnHomotopy)
open Stacks.Cohomology.LerayUnbounded
  (isIso_derivedPullbackComparison_app_single_extensionByZeroUnit quasiIso_sectionsOverObject_map)
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.FullyFaithfulSubsite

universe u

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of scalars of presheaves of modules along the structure map
`f^♯ : O_D ⟶ u⁻¹ O_C` of a morphism of ringed sites. -/
def fSharpRestrictScalars :
    PresheafOfModules.{u} (f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ⥤
      PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj :=
  PresheafOfModules.restrictScalars.{u} f.toRingedToposSiteHom.fSharpPresheaf

/-- Restriction of scalars along `f^♯` is additive. -/
instance fSharpRestrictScalars_additive : (fSharpRestrictScalars f).Additive where
  map_add := rfl

/-- Restriction of scalars along `f^♯` is exact: it does not change the underlying presheaf of
abelian groups, and exactness of presheaves of modules is tested there. -/
instance fSharpRestrictScalars_preservesHomology : (fSharpRestrictScalars f).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun _ hS ↦
    (PresheafOfModules.toPresheaf.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj).reflects_exact_of_faithful _
      (hS.map (PresheafOfModules.toPresheaf.{u}
        (f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)))

/-- Restriction of scalars along `f^♯` preserves finite limits. -/
instance fSharpRestrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (fSharpRestrictScalars f) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- Restriction of scalars along `f^♯` preserves finite colimits. -/
instance fSharpRestrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (fSharpRestrictScalars f) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- **Restriction of presheaves of modules along `f`**: the direct image of modules on the
chaotic sites, precomposition with `u.op` followed by restriction of scalars along `f^♯`. It is
the chaotic counterpart of `f_*`: `ε_* ∘ f_* = (this) ∘ ε_*` on the nose
(`pushforwardTopos_comp_epsilonPushforward`). -/
abbrev chaoticPushforward :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⥤
      PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj :=
  PresheafOfModules.pushforward₀.{u} f.u (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙
    fSharpRestrictScalars f

/-- The chaotic restriction preserves finite limits. -/
instance chaoticPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (chaoticPushforward f) :=
  comp_preservesFiniteLimits _ _

/-- The chaotic restriction preserves finite colimits. -/
instance chaoticPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (chaoticPushforward f) :=
  comp_preservesFiniteColimits _ _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`ε_* ∘ f_* = f_*^{ch} ∘ ε_*`**: the presheaf of modules underlying the direct image of a
sheaf of modules is the chaotic direct image of its underlying presheaf of modules. This holds
on the nose. -/
theorem pushforwardTopos_comp_epsilonPushforward :
    f.toRingedToposSiteHom.pushforwardTopos ⋙
        epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) =
      epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ chaoticPushforward f :=
  rfl

/-- A quasi-isomorphism of complexes becomes invertible in the derived category. -/
private theorem isIso_Qh_map_quotient_map {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (s : K ⟶ L) [QuasiIso s] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s)) := by
  rwa [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]

/-- **The derived pushforward of the chaotic comparison is computed at the direct image of a
K-injective complex.** For a K-injective complex `I` of `O_C`-modules, the comparison
`ε_*(f_* I) ⟶ Rε_*(f_* I)` is invertible. Indeed, on sections over an object `V` of the target, a
K-injective resolution `f_* I ⟶ J` becomes a quasi-isomorphism: both sides compute
`RΓ(V, Rf_* I) = RΓ(u V, I)` (Stacks 0D6H, through the corepresentability of sections by
`j_{V!} O_V` and the derived adjunction of Tag 07A6). No cocontinuity is needed here. -/
theorem isIso_derivedEpsilonPushforwardUnit_app_pushforwardTopos
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [hI : I.IsKInjective] :
    IsIso ((derivedEpsilonPushforwardUnit.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).app
      ((f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy.{u} f.toRingedToposSiteHom
    f.isMorphismOfSites_toRingedToposSiteHom
  obtain ⟨J, s, hJ, hs⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have hq : QuasiIso (((epsilonPushforward.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s) := by
    refine PresheafOfModules.quasiIso_of_forall_quasiIso_evaluation _ fun V ↦ ?_
    have := isIso_derivedPullbackComparison_app_single_extensionByZeroUnit f V.unop
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V))
        AddCommGrpCat.{u})).1
      (quasiIso_sectionsOverObject_map f V.unop I hI s hJ hs)
  refine Stacks.Cohomology.LerayUnbounded.isIso_of_comp_sq
    ((derivedEpsilonPushforwardUnit.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) ?_ ?_ ?_
  · exact @isIso_Qh_map_quotient_map _ _ _ _ _ _ _ hq
  · exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ J
  · have := isIso_Qh_map_quotient_map s
    exact Functor.map_isIso
      (derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _

section Derived

variable [f.u.IsCocontinuous Y.J X.J]

/-- The comparison exhibiting `Rε_* ∘ f_*` as a right derived functor of `ε_* ∘ f_*`. -/
abbrev restrictedEpsilonUnit :
    f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ (f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory ⋙
        derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Functor.whiskerLeft (f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory
      (ComplexShape.up ℤ))
      (derivedEpsilonPushforwardUnit.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
    Functor.whiskerRight f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategoryFactorsh.inv
      (derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The comparison exhibiting `f_*^{ch} ∘ Rε_*` as a right derived functor of `f_*^{ch} ∘ ε_*`. -/
abbrev epsilonRestrictedUnit :
    (epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        ((chaoticPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙
        (derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          (chaoticPushforward f).mapDerivedCategory) :=
  Functor.whiskerLeft
      ((epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ)) (chaoticPushforward f).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight
      (derivedEpsilonPushforwardUnit.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (chaoticPushforward f).mapDerivedCategory

/-- `Rε_* ∘ f_*` is a right derived functor of `ε_* ∘ f_*`: the comparison of `f_*` is
invertible, `f_*` being exact, and that of `Rε_*` is invertible at the direct image of a
K-injective complex by `isIso_derivedEpsilonPushforwardUnit_app_pushforwardTopos`. -/
instance isRightDerivedFunctor_restrictedEpsilon :
    (f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory ⋙
        derivedEpsilonPushforward.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).IsRightDerivedFunctor
      (restrictedEpsilonUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
    f.toRingedToposSiteHom.pushforwardTopos
    (epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _ _ _ _
    (fun _ _ ↦ NatIso.isIso_app_of_isIso
      f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategoryFactorsh.symm.hom _)
    (fun I _ ↦ isIso_derivedEpsilonPushforwardUnit_app_pushforwardTopos f I)

/-- `f_*^{ch} ∘ Rε_*` is a right derived functor of `f_*^{ch} ∘ ε_*`: the comparison of `Rε_*`
is invertible on a K-injective complex, and that of the exact chaotic restriction everywhere. -/
instance isRightDerivedFunctor_epsilonRestricted :
    (derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (chaoticPushforward f).mapDerivedCategory).IsRightDerivedFunctor
      (epsilonRestrictedUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
    (epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (chaoticPushforward f) _ _ _ _
    (fun I _ ↦ Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I)
    (fun _ _ ↦ NatIso.isIso_app_of_isIso
      (chaoticPushforward f).mapDerivedCategoryFactorsh.symm.hom _)

/-- The two underived composites `ε_* ∘ f_*` and `f_*^{ch} ∘ ε_*` are one functor, so the
sources of `restrictedEpsilonUnit` and `epsilonRestrictedUnit` are isomorphic, by an isomorphism
with identity components. -/
def restrictedEpsilonComparison :
    f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ≅
      (epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        ((chaoticPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (f.toRingedToposSiteHom.pushforwardTopos ⋙
          epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (epsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          chaoticPushforward f))
        (ComplexShape.up ℤ)).symm) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- **Derived sections of the direct image along a cocontinuous morphism of ringed sites.**
`Rε_*(f_* L) ≅ f_*^{ch}(Rε_* L)` naturally in `L ∈ D(O_C)`: the derived pushforward to the
chaotic site of the direct image of `L` is the chaotic restriction of the derived pushforward of
`L`. On sections over an object `V` of the target this reads `RΓ(V, f_* L) = RΓ(u V, L)`,
compatibly with the restriction maps. Both sides are right derived functors of the one functor
`ε_* ∘ f_* = f_*^{ch} ∘ ε_*`, so this is one application of the uniqueness of right derived
functors. -/
def derivedEpsilonPushforwardIso :
    f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory ⋙
        derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (chaoticPushforward f).mapDerivedCategory :=
  Functor.rightDerivedNatIso _ _ (restrictedEpsilonUnit f) (epsilonRestrictedUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (restrictedEpsilonComparison f)

/-- **The defining compatibility of `derivedEpsilonPushforwardIso`**: it carries the one
comparison into the other. -/
theorem derivedEpsilonPushforwardIso_fac
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (restrictedEpsilonUnit f).app K ≫
        (derivedEpsilonPushforwardIso f).hom.app (DerivedCategory.Qh.obj K) =
      (restrictedEpsilonComparison f).hom.app K ≫ (epsilonRestrictedUnit f).app K :=
  Functor.rightDerivedNatTrans_app _ _ (restrictedEpsilonUnit f) (epsilonRestrictedUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (restrictedEpsilonComparison f).hom K

/-- **`Rε_*(f_* L) ≅ (F⁻¹ Rε_* L)` with scalars restricted along `f^♯`**: the form of
`derivedEpsilonPushforwardIso` in which the chaotic restriction is split into the derived inverse
image `dInverseImage` of presheaves of modules along `u` and restriction of scalars along
`f^♯ : O_D ⟶ u⁻¹ O_C`. -/
def derivedEpsilonPushforwardInverseImageIso :
    f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory ⋙
        derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        dInverseImage.{u, u, u, u, u} f.u (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙
        (fSharpRestrictScalars f).mapDerivedCategory :=
  derivedEpsilonPushforwardIso f ≪≫ Functor.isoWhiskerLeft _
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (PresheafOfModules.pushforward₀.{u} f.u (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (fSharpRestrictScalars f))

/-! ### The derived pullback in the locally small model -/

section SmallModel

open Stacks.Injectives (grothendieckModelEquiv)

/-- The direct image read on the *standard* models of the two derived categories, the models in
which the derived pullback `Lf^*` and the adjunction `derivedPullbackAdjunction` are stated. -/
abbrev standardDerivedPushforward :
    @DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _ _
        (HasDerivedCategory.standard _) ⥤
      @DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _ _
        (HasDerivedCategory.standard _) :=
  @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
    (HasDerivedCategory.standard _) f.toRingedToposSiteHom.pushforwardTopos _ _ _

/-- Transporting the standard-model direct image along the two model comparisons gives a lift of
the degreewise direct image along the localization functor of the locally small model. -/
def standardDerivedPushforwardLiftingIso :
    DerivedCategory.Q ⋙ ((grothendieckModelEquiv.{u} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inverse ⋙
        standardDerivedPushforward f ⋙
        (grothendieckModelEquiv.{u} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).functor) ≅
      f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator _ _ _) ≪≫
        Functor.isoWhiskerLeft
          (@DerivedCategory.Q (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _ _
            (HasDerivedCategory.standard _))
          (grothendieckModelEquiv.{u} (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).unitIso.symm ≪≫
        Functor.rightUnitor _) _ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) f.toRingedToposSiteHom.pushforwardTopos _ _ _)
      (grothendieckModelEquiv.{u} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).functor ≪≫
    Functor.associator _ _ _

/-- **The direct image on derived categories does not depend on the model**: transported along
the comparison equivalences between the standard and the locally small models, the standard-model
functor induced by `f_*` is the locally-small-model one. -/
def standardDerivedPushforwardModelIso :
    (grothendieckModelEquiv.{u} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inverse ⋙
        standardDerivedPushforward f ⋙
        (grothendieckModelEquiv.{u} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).functor ≅
      f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ))
      (f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      ((grothendieckModelEquiv.{u} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inverse ⋙
        standardDerivedPushforward f ⋙
        (grothendieckModelEquiv.{u} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).functor) :=
    ⟨standardDerivedPushforwardLiftingIso f⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    (f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q) _ _ (Iso.refl _)

/-- **The derived pullback `Lf^*` read on the locally small models** of the two derived
categories: the standard-model `Lf^*` of Tag 06YY conjugated by the comparison equivalences,
which are the identity on objects. The models of the derived pullback are those of the
comparison equivalences and of `hasLeftDerivedFunctor_pullbackOnHomotopy`, which supplies its
existence. -/
abbrev smallDerivedPullback :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (grothendieckModelEquiv.{u} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inverse ⋙
    @derivedPullback.{u} _ _ _ _ _ _ f.toRingedToposSiteHom (_) (_)
      (hasLeftDerivedFunctor_pullbackOnHomotopy f.toRingedToposSiteHom
        f.isMorphismOfSites_toRingedToposSiteHom) ⋙
    (grothendieckModelEquiv.{u} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).functor

/-- **`Lf^* ⊣ f_*` in the locally small model**, for a morphism of ringed sites whose functor is
cocontinuous: `derivedPullbackAdjunction` transported along the comparison equivalences of the
two models. This is the adjunction compatible with `derivedEpsilonPushforwardIso`, both being
stated in the model in which the chaotic comparison `Rε_*` lives. -/
def smallDerivedPullbackAdjunction :
    smallDerivedPullback f ⊣ f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f.toRingedToposSiteHom
    f.isMorphismOfSites_toRingedToposSiteHom
  (((grothendieckModelEquiv.{u} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).symm.toAdjunction.comp
      (derivedPullbackAdjunction f)).comp
    (grothendieckModelEquiv.{u} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).toAdjunction).ofNatIsoRight
    (standardDerivedPushforwardModelIso f)

/-- **The unit of `smallDerivedPullbackAdjunction` is an isomorphism**, for a morphism of
ringed sites whose functor is continuous, cocontinuous and fully faithful and whose structure map
is invertible: `Lf^*` is fully faithful in the locally small model as well. -/
instance isIso_smallDerivedPullbackAdjunction_unit [f.u.Full] [f.u.Faithful] [IsIso f.fsharp] :
    IsIso (smallDerivedPullbackAdjunction f).unit := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f.toRingedToposSiteHom
    f.isMorphismOfSites_toRingedToposSiteHom
  have := (derivedPullbackAdjunction f).fullyFaithfulLOfIsIsoUnit.full
  have := (derivedPullbackAdjunction f).fullyFaithfulLOfIsIsoUnit.faithful
  infer_instance

end SmallModel

end Derived

end Stacks.Cohomology.FullyFaithfulSubsite

end
