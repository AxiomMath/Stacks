module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact

/-!
# The derived direct image on complexes with quasi-coherent cohomology

Let `f : Y ⟶ W` be a morphism of quasi-compact and quasi-separated algebraic spaces over a scheme
`S`.  This file proves that the unbounded derived direct image `Rf_*` carries `D_QCoh(𝒪_Y)` into
`D_QCoh(𝒪_W)` and has finite cohomological dimension there: there is an integer `N` with
`Rf_*E` living in degrees `≤ c + N` whenever `E` lives in degrees `≤ c`.  These are parts (1)
and (2) of [Stacks, Tag 08FA] for such morphisms.

## Main definitions

* `AlgebraicGeometry.Space.DerivedPushforwardQuasicoherentBounded`: every right derived functor
  of the direct image carries `D_QCoh` into `D_QCoh` and raises upper bounds by at most `N`.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryB_obj_of_isAffineHom`: along an affine morphism the
  derived direct image preserves quasi-coherent cohomology on the whole unbounded derived
  category; with `AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom` this is
  `AlgebraicGeometry.Space.derivedPushforwardQuasicoherentBounded_of_isAffineHom`, with `N = 0`.
* `AlgebraicGeometry.Space.nonempty_derivedPushforward_comp_obj_iso`: `Rg_* ∘ Rj_* ≅ R(j ≫ g)_*`
  on objects when `j` is étale.
* `Space.derivedPushforwardQuasicoherentBounded_of_elementaryDistinguishedSquare`: the bound
  propagates across an elementary distinguished square, by the Mayer–Vietoris triangle of
  Stacks 08GW.
* `AlgebraicGeometry.Space.exists_derivedPushforwardQuasicoherentBounded_of_isAffineSpace`: the
  bound for a morphism from a quasi-compact quasi-separated space to an affine one, by the
  induction principle of Stacks 08GP on the source.
* `AlgebraicGeometry.Space.exists_derivedPushforwardQuasicoherentBounded`: the bound for a morphism
  between quasi-compact quasi-separated spaces, by restriction to a surjective affine étale chart
  of the target (Stacks 08GE).
* `AlgebraicGeometry.Space.exists_isZero_homology_derivedPushforward_of_isQuasiCompact`: part (2)
  of Stacks 08FA, the cohomology sheaves of `Rf_*E` vanish in degrees `≥ N`.
* `Space.derivedCategoryB_derivedPushforward_obj_of_isQuasiCompact_of_isQuasiSeparated`: part (1)
  of Stacks 08FA, `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.

## Implementation notes

The source deduces the bound from the uniform vanishing of Stacks 073G and the spectral sequence
of Stacks 015J.  Neither is used here.  The induction runs over the *source*: for an affine étale
object of the source the composite to the affine target is an affine morphism, where the bound is
`N = 0`; and across an elementary distinguished square `(U ⊆ W, V ⟶ W)` the Mayer–Vietoris
triangle `E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{U ×_W V,*}E|_{U ×_W V}` pushed forward along
`W ⟶ Z` raises the bound by one.  The general target is reduced to an affine one by restricting
to a surjective affine étale chart: quasi-coherence and vanishing descend along it.

The derived categories are the standard models `HasDerivedCategory.standard`, in which the
Mayer–Vietoris triangle of Stacks 08GW and the base change of Stacks 08GE are stated.  The
statements quantify over every right derived functor of the direct image.

## References

* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.SheafOfModules.Tensor (ringSheaf)
open CategoryTheory.PushforwardMayerVietoris

attribute [local instance 5000] SheafOfModules.instAbelian

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `D_QCoh(𝒪_X)` is a triangulated subcategory -/

/-- Quasi-coherence of modules on the small étale site of an algebraic space is a weak Serre
subcategory, in the five-term form of `WeakSerre.IsWeakSerre`. -/
theorem isWeakSerre_isQuasicoherentOnSite_of_isAlgebraicSpace
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    WeakSerre.IsWeakSerre (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)) := by
  let := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS F hF
  refine ⟨inferInstance, (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).exists_prop_of_isWeakSerreClass,
    fun E h₀ h₁ h₃ h₄ => ?_⟩
  exact ObjectProperty.prop_mid_of_exact₄ ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).prop_obj₂_of_exact)
    E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`, at any model of the derived
category. -/
instance isTriangulated_derivedCategoryB_isQuasicoherentOnSite
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS F hF)] :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O))).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (isWeakSerre_isQuasicoherentOnSite_of_isAlgebraicSpace B S hS F hF)

/-- `D_QCoh(𝒪_X)` is closed under isomorphisms in `D(𝒪_X)`, at any model of the derived
category. -/
instance isClosedUnderIsomorphisms_derivedCategoryB_isQuasicoherentOnSite
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS F hF)] :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (isWeakSerre_isQuasicoherentOnSite_of_isAlgebraicSpace B S hS F hF)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-! ### Affine morphisms -/

section Affine

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
  (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

include hf α in
/-- Along an affine morphism, the derived direct image of a quasi-coherent module placed in a
single degree has quasi-coherent cohomology. -/
theorem derivedCategoryB_obj_singleFunctor_of_isAffineHom
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (n : ℤ) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      (Rf.obj ((DerivedCategory.singleFunctor _ n).obj M)) := by
  let K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj M
  have hK : ∀ m, (K.X m).IsQuasicoherentOnSite := by
    intro m
    by_cases hm : m = n
    · subst hm
      exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).prop_of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m M).symm hM
    · exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).prop_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n M m hm)
  have hiso := isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite B S hS f hf Rf α K hK
  have hfK : ∀ m, ((((modulePushforward B S hS f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).X m).IsQuasicoherentOnSite :=
    fun m => pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf _ (hK m)
  have e : Rf.obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      DerivedCategory.Q.obj (((modulePushforward B S hS f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    Rf.mapIso (((DerivedCategory.singleFunctorIsoCompQ _ n).app M) ≪≫
        ((DerivedCategory.quotientCompQhIso _).app K).symm) ≪≫
      (@asIso _ _ _ _ _ hiso).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  exact (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).prop_of_iso e.symm
    (isQuasicoherentOnSite_derived_homology B S hS _ hfK)

include hf α in
/-- **The derived direct image along an affine morphism of algebraic spaces preserves
quasi-coherent cohomology**, on the whole unbounded derived category. -/
theorem derivedCategoryB_obj_of_isAffineHom (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) (Rf.obj E) := by
  let := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : Rf.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS f) Rf α
  refine Stacks.SmallDerivedCategory.derivedCategoryB_obj_of_isLE_bound Rf
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) inferInstance inferInstance
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (isWeakSerre_isQuasicoherentOnSite_of_isAlgebraicSpace B S hS Y.1 Y.2)
    (fun M hM n => derivedCategoryB_obj_singleFunctor_of_isAffineHom B S hS f hf Rf α M hM n)
    (fun K c hK => Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS f) Rf α
      (fun I hI => isIso_app_of_isKInjective_modulePushforward B S hS f _ Rf α I hI) K c hK)
    0 (fun K hK c hc => ?_) E hE
  simpa using isLE_derivedModulePushforward_obj_of_isAffineHom B S hS f hf Rf α K hK c hc

end Affine

/-! ### Derived direct image along a composite with an étale morphism -/

section Composite

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The derived direct image along `f` computed on a K-injective complex. -/
def derivedPushforwardObjIsoOfIsKInjective (f : X ⟶ Y)
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj (((modulePushforward B S hS f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) ≅ Rf.obj (DerivedCategory.Q.obj I) :=
  rightDerivedObjIsoOfKInjective (exists_quasiIso_isKInjective_modules B S hS X.1 X.2)
    (modulePushforward B S hS f) inferInstance Rf α inferInstance I hI

/-- **Derived direct image along a composite whose first factor is étale**: for `j : X ⟶ Y`
étale and any `g : Y ⟶ Z`, `Rg_*(Rj_* E) ≅ R(j ≫ g)_* E`. -/
theorem nonempty_derivedPushforward_comp_obj_iso (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)
    (g : Y ⟶ Z)
    (Rj : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (αj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (Rjg : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αjg : (modulePushforward B S hS (j ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rjg)
    [Rjg.IsRightDerivedFunctor αjg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    Nonempty (Rg.obj (Rj.obj E) ≅ Rjg.obj E) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) E
  have hjI : CochainComplex.IsKInjective (((modulePushforward B S hS j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) :=
    have := hI
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_adjunction (modulePushforward B S hS j)
      (etaleModulePullback.{u, u} B S hS j hj) (etaleModulePullbackAdjunction B S hS j hj) I
  refine ⟨Rg.mapIso (Rj.mapIso e.symm) ≪≫ Rg.mapIso
      (derivedPushforwardObjIsoOfIsKInjective B S hS j Rj αj I hI).symm ≪≫
    (derivedPushforwardObjIsoOfIsKInjective B S hS g Rg αg _ hjI).symm ≪≫
    DerivedCategory.Q.mapIso (((NatIso.mapHomologicalComplex
      (modulePushforwardCompIso B S hS j g) (ComplexShape.up ℤ))).app I) ≪≫
    derivedPushforwardObjIsoOfIsKInjective B S hS (j ≫ g) Rjg αjg I hI ≪≫ Rjg.mapIso e⟩

/-- The restriction to `X` of the K-injective complex `I` along an étale `j : X ⟶ Y` is
K-injective, `j_!` being exact. -/
theorem isKInjective_etaleModulePullback_mapHomologicalComplex (j : X ⟶ Y)
    (hj : IsEtale B S hS j.hom) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) :=
  isKInjective_etaleModulePullback B S hS j hj (etaleModuleLowerShriekAdjunction B S hS j hj) I hI

/-- The total right derived functor of the direct image along `f`. -/
private abbrev totalDerivedPushforward (f : X ⟶ Y) :=
  ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

/-- The unit of `totalDerivedPushforward`. -/
private abbrev totalDerivedPushforwardUnit (f : X ⟶ Y) :=
  ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

attribute [local instance] hasRightDerivedFunctor_modulePushforward in
/-- **Derived direct image after `R(j_*((-)|_X))`.**  For `j : X ⟶ Y` étale, any right derived
functor `R` of `F ↦ j_*(F|_X)` and any `g : Y ⟶ Z`, `Rg_*(R E) ≅ R(j ≫ g)_*(E|_X)`. -/
theorem nonempty_derivedPushforward_restrictPush_obj_iso (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)
    (g : Y ⟶ Z)
    (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (αR : (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (Rjg : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αjg : (modulePushforward B S hS (j ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rjg)
    [Rjg.IsRightDerivedFunctor αjg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    Nonempty (Rg.obj (R.obj E) ≅
      Rjg.obj ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2) E
  have hjI := isKInjective_etaleModulePullback_mapHomologicalComplex B S hS j hj I hI
  let Rj := totalDerivedPushforward B S hS j
  let αj := totalDerivedPushforwardUnit B S hS j
  obtain ⟨e₂⟩ := nonempty_derivedPushforward_comp_obj_iso B S hS j hj g Rj αj Rg αg Rjg αjg
    (DerivedCategory.Q.obj (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I))
  let K := ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have e₁ : R.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((modulePushforward B S hS j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    (rightDerivedObjIsoOfKInjective
      (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)
      (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) inferInstance
      R αR inferInstance I hI).symm
  have e₃ : DerivedCategory.Q.obj (((modulePushforward B S hS j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≅ Rj.obj (DerivedCategory.Q.obj K) :=
    derivedPushforwardObjIsoOfIsKInjective B S hS j Rj αj K hjI
  have e₄ : DerivedCategory.Q.obj K ≅
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E :=
    ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryFactors.app I).symm ≪≫
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.mapIso e
  exact ⟨Rg.mapIso (R.mapIso e.symm) ≪≫ Rg.mapIso e₁ ≪≫ Rg.mapIso e₃ ≪≫ e₂ ≪≫ Rjg.mapIso e₄⟩

end Composite

/-! ### Bounded derived direct images -/

section Bounded

/-- In a distinguished triangle of `D(A)` whose second and third vertices live in degrees
`≤ m`, the first vertex lives in degrees `≤ m + 1`. -/
theorem isLE_obj₁_of_distinguished {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A)) (m : ℤ)
    (h₂ : T.obj₂.IsLE m) (h₃ : T.obj₃.IsLE m) : T.obj₁.IsLE (m + 1) := by
  have h₃' : DerivedCategory.TStructure.t.IsLE
      ((shiftFunctor (DerivedCategory A) (-1 : ℤ)).obj T.obj₃) (m + 1) :=
    DerivedCategory.TStructure.t.isLE_shift T.obj₃ m (-1) (m + 1) (by omega)
  have h₂' : DerivedCategory.TStructure.t.IsLE T.obj₂ (m + 1) :=
    DerivedCategory.TStructure.t.isLE_of_le T.obj₂ m (m + 1) (by omega)
  exact DerivedCategory.TStructure.t.isLE₂ T.invRotate (inv_rot_of_distTriang T hT) (m + 1)
    h₃' h₂'

/-- Membership in an isomorphism-closed property and an upper bound both transfer along an
isomorphism. -/
private theorem prop_and_isLE_of_iso {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty (DerivedCategory A)) [P.IsClosedUnderIsomorphisms]
    {X Y : DerivedCategory A} (e : X ≅ Y) {N : ℤ} {Q : ℤ → Prop} (h₁ : P Y)
    (h₂ : ∀ c, Q c → Y.IsLE (c + N)) : P X ∧ ∀ c, Q c → X.IsLE (c + N) :=
  ⟨P.prop_of_iso e.symm h₁, fun c hc =>
    have := h₂ c hc
    DerivedCategory.TStructure.t.isLE_of_iso e.symm (c + N)⟩

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **`Rg_*` carries `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_Z)` and raises upper bounds by at most `N`**,
for every right derived functor `Rg_*` of the direct image. -/
def DerivedPushforwardQuasicoherentBounded (g : Y ⟶ Z) (N : ℤ) : Prop :=
  ∀ (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg),
    Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
    ∀ E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) E →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)) (Rg.obj E) ∧
        ∀ c : ℤ, E.IsLE c → (Rg.obj E).IsLE (c + N)

/-- A bound may be enlarged. -/
theorem DerivedPushforwardQuasicoherentBounded.mono {g : Y ⟶ Z} {N N' : ℤ}
    (h : DerivedPushforwardQuasicoherentBounded B S hS g N) (hN : N ≤ N') :
    DerivedPushforwardQuasicoherentBounded B S hS g N' := by
  intro Rg αg hRg E hE
  refine ⟨(h Rg αg hRg E hE).1, fun c hc => ?_⟩
  have := (h Rg αg hRg E hE).2 c hc
  exact DerivedCategory.TStructure.t.isLE_of_le _ (c + N) (c + N') (by omega)

/-- The bound depends on the morphism only. -/
theorem DerivedPushforwardQuasicoherentBounded.of_eq {g g' : Y ⟶ Z} (hg : g = g') {N : ℤ}
    (h : DerivedPushforwardQuasicoherentBounded B S hS g N) :
    DerivedPushforwardQuasicoherentBounded B S hS g' N := hg ▸ h

/-- **An affine morphism has a bounded derived direct image**, with `N = 0`. -/
theorem derivedPushforwardQuasicoherentBounded_of_isAffineHom (g : Y ⟶ Z)
    (hg : IsAffineHom B S hS g.hom) : DerivedPushforwardQuasicoherentBounded B S hS g 0 := by
  intro Rg αg hRg E hE
  refine ⟨derivedCategoryB_obj_of_isAffineHom B S hS g hg Rg αg E hE, fun c hc => ?_⟩
  simpa using isLE_derivedModulePushforward_obj_of_isAffineHom B S hS g hg Rg αg E hE c hc

end Bounded

section Square

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  hasRightDerivedFunctor_mapHomotopyCategory_modules hasRightDerivedFunctor_modulePushforward

variable {W Z : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- One term of the Mayer–Vietoris triangle of Stacks 08GW, pushed forward along `g`: if
`R(j_Y ≫ g)_*` is bounded on `D_QCoh(𝒪_Y)`, then `Rg_*(Rj_{Y,*}(E|_Y))` lies in `D_QCoh(𝒪_Z)`
with the same bound, for `E` in `D_QCoh(𝒪_W)`. -/
theorem derivedCategoryB_and_isLE_restrictPush {Y : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (hj : IsEtale B S hS j.hom) (g : W ⟶ Z) {N : ℤ}
    (hY : DerivedPushforwardQuasicoherentBounded B S hS (j ≫ g) N)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αR : (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (Rg : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)) (Rg.obj (R.obj E)) ∧
      ∀ c : ℤ, E.IsLE c → (Rg.obj (R.obj E)).IsLE (c + N) := by
  obtain ⟨e⟩ := nonempty_derivedPushforward_restrictPush_obj_iso B S hS j hj g R αR Rg αg
    (totalDerivedPushforward B S hS (j ≫ g)) (totalDerivedPushforwardUnit B S hS (j ≫ g)) E
  have hEY := derivedQuasicoherent_etaleModulePullback B S hS j hj E hE
  obtain ⟨h₁, h₂⟩ := hY _ (totalDerivedPushforwardUnit B S hS (j ≫ g)) inferInstance _ hEY
  exact prop_and_isLE_of_iso _ e h₁ fun c hc =>
    have := hc
    h₂ c (Stacks.Homology.isLE_mapDerivedCategory_obj _ E c)

/-- **The inductive step**: across an elementary distinguished square `(U ⊆ W, V ⟶ W)`, the
derived direct image along `g : W ⟶ Z` is bounded on `D_QCoh(𝒪_W)` as soon as it is along the
three composites `U ⟶ Z`, `V ⟶ Z`, `U ×_W V ⟶ Z`. -/
theorem derivedPushforwardQuasicoherentBounded_of_elementaryDistinguishedSquare (g : W ⟶ Z)
    {NU NV NP : ℤ}
    (hU : DerivedPushforwardQuasicoherentBounded B S hS (edsOpenHom B S hS hsq ≫ g) NU)
    (hV : DerivedPushforwardQuasicoherentBounded B S hS (edsEtaleHom B S hS hsq ≫ g) NV)
    (hP : DerivedPushforwardQuasicoherentBounded B S hS (edsInterHom B S hS hsq ≫ g) NP) :
    DerivedPushforwardQuasicoherentBounded B S hS g (max NU (max NV NP) + 1) := by
  intro Rg αg hRg E hE
  let := Functor.IsRightDerivedFunctor.commShift Rg αg
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : Rg.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS g) Rg αg
  have : Rg.Additive := inferInstance
  have : PreservesBinaryBiproducts Rg := preservesBinaryBiproducts_of_preservesBiproducts Rg
  obtain ⟨δ, hT⟩ :=
    exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek B S hS hsq E
  have hT' := Rg.map_distinguished _ hT
  obtain ⟨qU, bU⟩ := derivedCategoryB_and_isLE_restrictPush B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) g hU (edsDerivedRestrictPushOpen B S hS hsq)
    (edsTotalRightDerivedUnitOpen B S hS hsq) Rg αg E hE
  obtain ⟨qV, bV⟩ := derivedCategoryB_and_isLE_restrictPush B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) g hV (edsDerivedRestrictPushEtale B S hS hsq)
    (edsTotalRightDerivedUnitEtale B S hS hsq) Rg αg E hE
  obtain ⟨qP, bP⟩ := derivedCategoryB_and_isLE_restrictPush B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) g hP (edsDerivedRestrictPushInter B S hS hsq)
    (edsTotalRightDerivedUnitInter B S hS hsq) Rg αg E hE
  let QZ := DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))
  let eb := Rg.mapBiprod ((edsDerivedRestrictPushOpen B S hS hsq).obj E)
    ((edsDerivedRestrictPushEtale B S hS hsq).obj E)
  have qUV : QZ (Rg.obj ((edsDerivedRestrictPushOpen B S hS hsq).obj E ⊞
      (edsDerivedRestrictPushEtale B S hS hsq).obj E)) :=
    QZ.prop_of_iso eb.symm (QZ.ext_of_isTriangulatedClosed₂ _
      (binaryBiproductTriangle_distinguished _ _) qU qV)
  refine ⟨QZ.ext_of_isTriangulatedClosed₁ _ hT' qUV qP, fun c hc => ?_⟩
  have le : ∀ {K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)} {n : ℤ},
      K.IsLE (c + n) → n ≤ max NU (max NV NP) → K.IsLE (c + max NU (max NV NP)) :=
    fun {K n} _ hn => DerivedCategory.TStructure.t.isLE_of_le K (c + n) _ (by omega)
  have hUle := le (bU c hc) (by omega)
  have hVle := le (bV c hc) (by omega)
  have hPle := le (bP c hc) (by omega)
  have hUVle : (Rg.obj ((edsDerivedRestrictPushOpen B S hS hsq).obj E ⊞
      (edsDerivedRestrictPushEtale B S hS hsq).obj E)).IsLE (c + max NU (max NV NP)) := by
    have : DerivedCategory.TStructure.t.IsLE
        (Rg.obj ((edsDerivedRestrictPushOpen B S hS hsq).obj E) ⊞
          Rg.obj ((edsDerivedRestrictPushEtale B S hS hsq).obj E)) (c + max NU (max NV NP)) :=
      DerivedCategory.TStructure.t.isLE₂ _ (binaryBiproductTriangle_distinguished _ _)
        (c + max NU (max NV NP)) hUle hVle
    exact DerivedCategory.TStructure.t.isLE_of_iso eb.symm _
  simpa [add_assoc] using isLE_obj₁_of_distinguished _ hT' _ hUVle hPle

end Square

/-! ### Bounded derived direct images to an affine algebraic space -/

/-- **The derived direct image from a quasi-compact quasi-separated algebraic space to an affine
algebraic space is bounded on `D_QCoh`.** -/
theorem exists_derivedPushforwardQuasicoherentBounded_of_isAffineSpace
    (hZ : B.Contains (⊤_ Scheme.{u})) {Y Z : AlgebraicSpaces B S hS}
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hZaff : IsAffineSpace B S hS Z.1) (g : Y ⟶ Z) :
    ∃ N : ℤ, DerivedPushforwardQuasicoherentBounded B S hS g N := by
  have key := qcqs_induction_on_self B S hS hZ Y hYqc hYqs
    (fun T j => ∀ hT : IsAlgebraicSpace B S hS T, ∃ N : ℤ,
      DerivedPushforwardQuasicoherentBounded B S hS
        ((ObjectProperty.homMk j : (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ Y) ≫ g) N)
    (fun V hV hT => ⟨0, derivedPushforwardQuasicoherentBounded_of_isAffineHom B S hS _
      (isAffineHom_of_isAffineSpace B S hS (V.1.hom.hom ≫ g.hom) hV hZaff)⟩)
    (fun W V U f hf hsq _ _ _ _ hU hV hP hT => ?_)
  · obtain ⟨N, hN⟩ := key Y.2
    exact ⟨N, hN.of_eq B S hS rfl⟩
  · let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hT⟩
    let gW : W' ⟶ Z := (ObjectProperty.homMk W.1.hom.hom : W' ⟶ Y) ≫ g
    have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 U f := hsq
    obtain ⟨NU, hNU⟩ := hU hsq'.isOpenSubspace.1
    obtain ⟨NV, hNV⟩ := hV hsq'.isAlgebraicSpace
    obtain ⟨NP, hNP⟩ := hP (edsInter B S hS hsq').2
    refine ⟨max NU (max NV NP) + 1,
      derivedPushforwardQuasicoherentBounded_of_elementaryDistinguishedSquare B S hS hsq' gW
        (hNU.of_eq B S hS rfl) (hNV.of_eq B S hS ?_) (hNP.of_eq B S hS rfl)⟩
    rw [← hf]
    rfl

/-! ### Arbitrary quasi-compact quasi-separated targets -/

/-- **A module whose restriction to a surjective étale chart vanishes is zero.** -/
theorem isZero_of_isZero_etaleModulePullback_chartToSpace_of_isSurjective
    (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1) (hA : IsSurjective B S hS A.1.hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : IsZero ((etaleModulePullback B S hS (chartToSpace B S hS X A)
      (isEtale_chartToSpace B S hS X A)).obj M)) : IsZero M := by
  rw [isZero_etaleModulePullback_chartToSpace_iff] at h
  refine Stacks.SheafOfModules.isZero_of_coversTop
    (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 A hA) M (fun _ => ?_)
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  ext U s
  exact (h U.unop.left U.unop.hom).elim _ _

/-- A quasi-compact algebraic space has a surjective étale chart whose scheme is affine. -/
theorem exists_affine_surjective_smallEtale_chart (X : AlgebraicSpaces B S hS)
    (hX : IsQuasiCompactSpace B S hS X.1) :
    ∃ A : SmallEtale B S hS X.1, IsSurjective B S hS A.1.hom ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) := by
  obtain ⟨V, φ, hV, hφs, hφe⟩ :=
    exists_affine_isSurjective_isEtale_of_isQuasiCompactSpace B S hS X hX
  exact ⟨⟨CostructuredArrow.mk φ, (isEtale_iff_presheaf_of_yoneda B S hS φ).1 hφe⟩, hφs, hV⟩

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_derivedPushforwardQuasicoherent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

attribute [local instance] hasRightDerivedFunctor_modulePushforward in
/-- **The derived direct image along a quasi-compact quasi-separated morphism, restricted to an
affine étale chart of the target, is bounded on `D_QCoh`.** -/
theorem exists_bounded_etaleModulePullback_chartToSpace_derivedPushforward
    {Y W : AlgebraicSpaces B S hS} (g : Y ⟶ W) (hgqc : IsQuasiCompact B S hS g.hom)
    (hgqs : IsQuasiSeparated B S hS g.hom) (A : SmallEtale B S hS W.1)
    (hAa : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj A))) :
    ∃ N : ℤ, ∀ (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
      (αg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg),
      Rg.IsRightDerivedFunctor αg
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
      ∀ E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
        DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) E →
        DerivedQuasicoherentPullback B S hS (chartToSpace B S hS W A)
            (isEtale_chartToSpace B S hS W A) (Rg.obj E) ∧
          ∀ c : ℤ, E.IsLE c → ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS W A)
            (isEtale_chartToSpace B S hS W A)).mapDerivedCategory.obj (Rg.obj E)).IsLE (c + N) := by
  let C := chartSpace B S hS W A
  let φ : C ⟶ W := chartToSpace B S hS W A
  have hφ : IsEtale B S hS φ.hom := isEtale_chartToSpace B S hS W A
  let Y' := AlgebraicSpaces.fiberProduct B S hS g φ
  let i : Y' ⟶ Y := ObjectProperty.homMk (pullback.fst g.hom φ.hom)
  let g' : Y' ⟶ C := ObjectProperty.homMk (pullback.snd g.hom φ.hom)
  have sq : IsPullback i g' g φ := AlgebraicSpaces.isPullback_fiberProduct B S hS g φ
  have sq₀ : IsPullback (pullback.fst g.hom φ.hom) (pullback.snd g.hom φ.hom) g.hom φ.hom :=
    IsPullback.of_hasPullback _ _
  have hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS g' i φ g sq.flip hφ
  have hCa : IsAffineSpace B S hS C.1 := isAffineSpace_yoneda B S hS _ hAa
  have hY'qc : IsQuasiCompactSpace B S hS Y'.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS g'.hom hCa
      (isQuasiCompact_of_isPullback B S hS sq₀ hgqc)
  have hY'qs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y'.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS B.contains_terminal
      g'.hom Y'.2 hCa (isQuasiSeparated_of_isPullback B S hS sq₀ hgqs)
  obtain ⟨N, hN⟩ := exists_derivedPushforwardQuasicoherentBounded_of_isAffineSpace B S hS
    B.contains_terminal hY'qc hY'qs hCa g'
  refine ⟨N, fun Rg αg hRg E hE => ?_⟩
  let Rg' := totalDerivedPushforward B S hS g'
  let αg' := totalDerivedPushforwardUnit B S hS g'
  have := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategoryFactorsh
  have := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
    (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory
    (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategoryFactorsh
  let e := (derivedModulePushforwardEtaleRestrictIso B S hS sq hφ
    (etaleModuleLowerShriekAdjunction B S hS i hi) Rg Rg'
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory
    (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory αg αg'
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategoryFactorsh.inv
    (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategoryFactorsh.inv).app E
  obtain ⟨h₁, h₂⟩ := hN Rg' αg' inferInstance _
    (derivedQuasicoherent_etaleModulePullback B S hS i hi E hE)
  exact prop_and_isLE_of_iso _ e h₁ fun c hc =>
    have := hc
    h₂ c (Stacks.Homology.isLE_mapDerivedCategory_obj _ E c)

/-- **The derived direct image along a quasi-compact quasi-separated morphism to a quasi-compact
algebraic space is bounded on `D_QCoh`**: there is `N` such that `Rg_*` carries `D_QCoh(𝒪_Y)`
into `D_QCoh(𝒪_W)` and objects living in degrees `≤ c` to objects living in degrees `≤ c + N`.
-/
theorem exists_derivedPushforwardQuasicoherentBounded_of_isQuasiCompact
    {Y W : AlgebraicSpaces B S hS} (g : Y ⟶ W) (hgqc : IsQuasiCompact B S hS g.hom)
    (hgqs : IsQuasiSeparated B S hS g.hom) (hWqc : IsQuasiCompactSpace B S hS W.1) :
    ∃ N : ℤ, DerivedPushforwardQuasicoherentBounded B S hS g N := by
  obtain ⟨A, hAs, hAa⟩ := exists_affine_surjective_smallEtale_chart B S hS W hWqc
  obtain ⟨N, hN⟩ := exists_bounded_etaleModulePullback_chartToSpace_derivedPushforward B S hS g
    hgqc hgqs A hAa
  refine ⟨N, fun Rg αg hRg E hE => ?_⟩
  obtain ⟨h₁, h₂⟩ := hN Rg αg hRg E hE
  have h14 := (derivedQuasicoherent_tfae B S hS (Rg.obj E)).out 1 4
  refine ⟨h14.2 ⟨A, hAs, h₁⟩, fun c hc => ?_⟩
  have h₃ := h₂ c hc
  rw [DerivedCategory.isLE_iff]
  intro n hn
  refine isZero_of_isZero_etaleModulePullback_chartToSpace_of_isSurjective B S hS W A hAs _ ?_
  exact IsZero.of_iso (DerivedCategory.isZero_of_isLE _ (c + N) n hn)
    (((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS W A)
      (isEtale_chartToSpace B S hS W A)).mapDerivedCategoryHomologyIso n).app (Rg.obj E)).symm

/-- **The derived direct image between quasi-compact quasi-separated algebraic spaces is bounded
on `D_QCoh`.** -/
theorem exists_derivedPushforwardQuasicoherentBounded (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y W : AlgebraicSpaces B S hS}
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hWqc : IsQuasiCompactSpace B S hS W.1) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (g : Y ⟶ W) : ∃ N : ℤ, DerivedPushforwardQuasicoherentBounded B S hS g N :=
  exists_derivedPushforwardQuasicoherentBounded_of_isQuasiCompact B S hS g
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hYqc g.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y.2 hYqs g.hom) hWqc

/-- **Bounded derived direct image** (part (2) of [Stacks, Tag 08FA]).  Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of algebraic spaces over `S` with `Y` quasi-compact.
There is an integer `N` such that for every right derived functor `Rf_*` of the direct image and
every `E` in `D_QCoh(𝒪_X)` with `H^m(E) = 0` for `m > 0`, the cohomology sheaves `H^m(Rf_*E)`
vanish for `m ≥ N`. -/
theorem exists_isZero_homology_derivedPushforward_of_isQuasiCompact
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hYqc : IsQuasiCompactSpace B S hS Y.1) :
    ∃ N : ℤ, ∀ (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf),
      Rf.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) →
      ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
        DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E →
        (∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor _ m).obj E)) →
        ∀ m : ℤ, N ≤ m → IsZero ((DerivedCategory.homologyFunctor _ m).obj (Rf.obj E)) := by
  obtain ⟨N, hN⟩ := exists_derivedPushforwardQuasicoherentBounded_of_isQuasiCompact B S hS f hfqc
    hfqs hYqc
  refine ⟨N + 1, fun Rf α hRf E hE hE0 m hm => ?_⟩
  have hle : E.IsLE 0 := (DerivedCategory.isLE_iff E 0).2 hE0
  have := (hN Rf α hRf E hE).2 0 hle
  exact DerivedCategory.isZero_of_isLE _ (0 + N) m (by omega)

/-- **The derived direct image preserves `D_QCoh`** (part (1) of [Stacks, Tag 08FA]).  Let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`.  Then
the derived direct image `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`, for every right
derived functor `Rf_*` of the direct image. -/
theorem derivedCategoryB_derivedPushforward_obj_of_isQuasiCompact_of_isQuasiSeparated
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) (Rf.obj E) := by
  refine ((derivedQuasicoherent_tfae B S hS (Rf.obj E)).out 1 2).2 fun A hAa => ?_
  obtain ⟨N, hN⟩ := exists_bounded_etaleModulePullback_chartToSpace_derivedPushforward B S hS f
    hfqc hfqs A hAa
  exact (hN Rf α inferInstance E hE).1

end AlgebraicGeometry.Space

end
