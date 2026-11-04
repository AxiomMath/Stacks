module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineDerivedCoheratorEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms

/-!
# The derived coherator on a derived direct image from an affine étale chart

Let `j : V ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, with `V` affine, whose direct image preserves quasi-coherence, and let `Rj_*` be a
right derived functor of the direct image which is computed by `j_*` on K-injective complexes of
quasi-coherent modules (the square of [Stacks, Tag 09TG] commutes,
`AlgebraicGeometry.Space.derivedPushforwardSquareCommutes_iff`).  This file proves the step of the
proof of 09TG that uses that square:

* for every object `F` of `D_QCoh(𝒪_V)`, the object `Rj_* F` lies in `D_QCoh(𝒪_X)` and the
  counit `i_X(RQ_X(Rj_* F)) ⟶ Rj_* F` of the derived coherator adjunction is invertible.

Write `F = i_V(I)` with `I` a K-injective complex of quasi-coherent `𝒪_V`-modules (the affine
case, `AlgebraicGeometry.Space.isIso_spaceDerivedInclusionAdjunction_counit_app_of_isAffineSpace`).
By the square `Rj_* F = i_X(j_* I)`.  The comparison of `RQ_X` is invertible at `j_* I`, by
`Stacks.DerivedCoherator.isIso_comparison_pushforward_of_kInjective`: the right derived functors
`Rj_* ⋙ RQ_X` and `RQ_V ⋙ Φ` of `Q_X ∘ j_* = j_* ∘ Q_V` agree, and at `I` the second has
invertible comparison because `V` is affine.  So the unit of the derived coherator adjunction is
invertible at `j_* I`, hence its counit at `i_X(j_* I)`.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentEtalePullback` — restriction `j^* : QCoh(𝒪_X) ⥤ QCoh(𝒪_V)`
  along an étale morphism, with its adjunction to the direct image
  `AlgebraicGeometry.Space.quasicoherentEtalePullbackAdjunction`.

## Main results

* `AlgebraicGeometry.Space.isIso_spaceDerivedCoheratorUnit_app_quasicoherentPushforward` — the
  comparison of `RQ_X` is invertible at `j_* I`.
* `AlgebraicGeometry.Space.derivedQuasicoherentProperty_and_isIso_counit_derivedPushforward` —
  `Rj_* F` has quasi-coherent cohomology and the counit is invertible at it.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X V : AlgebraicSpaces B S hS} (j : V ⟶ X) (hj : IsEtale B S hS j.hom)

/-- Restriction of quasi-coherent modules along an étale morphism `j : V ⟶ X`: the étale
pullback of modules preserves quasi-coherence. -/
def quasicoherentEtalePullback :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS V.1 V.2 :=
  ObjectProperty.lift _ (quasicoherentSheavesι B S hS X ⋙ etaleModulePullback.{u, u} B S hS j hj)
    fun M => isQuasicoherentOnSite_etaleModulePullback B S hS j hj M.obj M.property

/-- The restriction to quasi-coherent modules is left adjoint to the direct image on
quasi-coherent modules: the adjunction `j^* ⊣ j_*` of all modules restricts. -/
def quasicoherentEtalePullbackAdjunction (hpush : PushforwardPreservesQuasicoherence B S hS j) :
    quasicoherentEtalePullback B S hS j hj ⊣ quasicoherentPushforward B S hS j hpush :=
  (etaleModulePullbackAdjunction B S hS j hj).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

variable (hV : IsAffineSpace B S hS V.1) (hpush : PushforwardPreservesQuasicoherence B S hS j)
  (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
  (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
  [Rj.IsRightDerivedFunctor βj
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ))]
  (H : DerivedPushforwardComputedOnKInjectives B S hS j Rj βj)

include hj hV H in
/-- **The comparison of the derived coherator `RQ_X` is invertible at `j_* I`**, for `I` a
K-injective complex of quasi-coherent `𝒪_V`-modules. -/
theorem isIso_spaceDerivedCoheratorUnit_app_quasicoherentPushforward
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ℤ) [I.IsKInjective] :
    IsIso ((spaceDerivedCoheratorUnit B S hS X).app
      ((quasicoherentSheavesι B S hS X).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj
        ((quasicoherentPushforward B S hS j hpush).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) :=
  Stacks.DerivedCoherator.isIso_comparison_pushforward_of_kInjective.{u, u, u}
    (quasicoherentSheavesι B S hS X) (quasicoherentSheavesι B S hS V)
    (spaceCoheratorAdjunction B S hS X) (spaceCoheratorAdjunction B S hS V)
    (spaceDerivedCoherator B S hS X) (spaceDerivedCoheratorUnit B S hS X)
    (spaceDerivedCoherator B S hS V) (spaceDerivedCoheratorUnit B S hS V)
    (etaleModulePullbackAdjunction B S hS j hj)
    (quasicoherentEtalePullbackAdjunction B S hS j hj hpush)
    (ObjectProperty.liftCompιIso _ _ _).symm (quasicoherentPushforwardCompιIso B S hS j hpush)
    Rj βj (isIso_spaceDerivedCoheratorUnit_app_of_isAffineSpace B S hS V hV) H I

include hj hV hpush H in
/-- **`Rj_* F` has quasi-coherent cohomology and the counit of the derived coherator adjunction
is invertible at it**, for every object `F` of `D_QCoh(𝒪_V)`. -/
theorem derivedQuasicoherentProperty_and_isIso_counit_derivedPushforward
    (F : DerivedCategory (Modules.{u, u} B S hS V.1 V.2))
    (hF : derivedQuasicoherentProperty B S hS V F) :
    derivedQuasicoherentProperty B S hS X (Rj.obj F) ∧
      IsIso ((spaceDerivedInclusionAdjunction B S hS X).counit.app (Rj.obj F)) := by
  -- `F` is `i_V` of a K-injective complex of quasi-coherent modules
  have hcV := isIso_spaceDerivedInclusionAdjunction_counit_app_of_isAffineSpace B S hS V hV F hF
  obtain ⟨I, s, hI, hs⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    (C := QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
    (DerivedCategory.Q.objPreimage ((spaceDerivedCoherator B S hS V).obj F))
  have : IsIso (DerivedCategory.Q.map s) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) s hs
  let eI : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅
      (spaceDerivedCoherator B S hS V).obj F :=
    (DerivedCategory.quotientCompQhIso _).app I ≪≫ (asIso (DerivedCategory.Q.map s)).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso _
  let eF : (quasicoherentSheavesι B S hS V).mapDerivedCategory.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≅ F :=
    (quasicoherentSheavesι B S hS V).mapDerivedCategory.mapIso eI ≪≫
      asIso ((spaceDerivedInclusionAdjunction B S hS V).counit.app F)
  -- by the square, `Rj_* F` is `i_X` of `j_* I`
  let Z := (HomotopyCategory.quotient (QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
    (ComplexShape.up ℤ)).obj I
  have hβ : IsIso (βj.app ((quasicoherentSheavesι B S hS V).mapHomotopyCategory
      (ComplexShape.up ℤ) |>.obj Z)) := H I hI
  let eR : Rj.obj F ≅ (quasicoherentSheavesι B S hS X).mapDerivedCategory.obj
      (DerivedCategory.Qh.obj ((quasicoherentPushforward B S hS j hpush).mapHomotopyCategory
        (ComplexShape.up ℤ) |>.obj Z)) :=
    Rj.mapIso eF.symm ≪≫
      Rj.mapIso ((quasicoherentSheavesι B S hS V).mapDerivedCategoryFactorsh.app Z) ≪≫
      (asIso (βj.app ((quasicoherentSheavesι B S hS V).mapHomotopyCategory
        (ComplexShape.up ℤ) |>.obj Z))).symm ≪≫
      DerivedCategory.Qh.mapIso ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (quasicoherentSheavesι B S hS V ⋙ modulePushforward B S hS j))
          (ComplexShape.up ℤ)).app Z ≪≫
        (Functor.mapHomotopyCategoryCompIso (quasicoherentPushforwardCompιIso B S hS j hpush)
          (ComplexShape.up ℤ)).symm.app Z) ≪≫
      ((quasicoherentSheavesι B S hS X).mapDerivedCategoryFactorsh.app
        ((quasicoherentPushforward B S hS j hpush).mapHomotopyCategory
          (ComplexShape.up ℤ) |>.obj Z)).symm
  refine ⟨derivedCategoryB_quasicoherent_of_iso B S hS X eR.symm
    (derivedCategoryB_mapDerivedCategory_obj B S hS X.1 X.2 _), ?_⟩
  -- the unit, hence the counit, of the derived coherator adjunction is invertible there
  have hunit := (Stacks.DerivedCoherator.isIso_inclusionDerivedAdjunction_unit_app_iff
    (quasicoherentSheavesι B S hS X) (spaceCoheratorAdjunction B S hS X)
    (spaceDerivedCoherator B S hS X) (spaceDerivedCoheratorUnit B S hS X) _).2
    (isIso_spaceDerivedCoheratorUnit_app_quasicoherentPushforward B S hS j hj hV hpush Rj βj H I)
  have := CategoryTheory.Adjunction.isIso_counit_app_obj_of_isIso_unit_app
    (spaceDerivedInclusionAdjunction B S hS X) _ hunit
  exact (NatTrans.isIso_app_iff_of_iso _ eR).2 this

end AlgebraicGeometry.Space

end
