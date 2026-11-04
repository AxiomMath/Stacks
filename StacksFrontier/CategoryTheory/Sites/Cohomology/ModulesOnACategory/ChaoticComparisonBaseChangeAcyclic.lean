module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveTruncationTower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonUnitSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalMorphismOfSitesEquivalence

/-!
# Hypothesis (2) of Stacks 0GZS from the acyclicity of base changes

Let `C` carry a Grothendieck topology `τ`, let `τ'` be the chaotic topology and let `O` be a
`τ`-sheaf of rings with commutative sections, with comparison morphism
`ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')`.  Hypothesis (2) of Stacks 0GZS asks that for every object `U`
and every K-flat complex `M^•` of `O(U)`-modules the canonical map
`M^• ⟶ RΓ((C/U)_τ, (M^• ⊗_{O(U)} O_U)^#)` be a quasi-isomorphism.

This file reduces that hypothesis to a statement about single modules: it holds as soon as, for
every `U` and every `O(U)`-module `N`, the presheaf `N ⊗_{O(U)} O_U` on `C/U` is already a
`τ`-sheaf with vanishing higher cohomology over every object of `C/U`.  This is how the source
proves hypothesis (2) in the case of Stacks 0H0J, where `C` is the associated affine site of a
category fibred in groupoids: "the total cohomology of the complex of modules associated to
`M^•` is quasi-isomorphic to `M^•`".

## Main results

* `Stacks.ModulesOnACategory.ChaoticComparison.isIso_derivedEpsilonAdjunction_unit_app_of_tower`:
  the `ε`-unit is invertible at a complex of presheaves of modules whose terms are sheaves and
  whose sheafification has a K-injective resolution carried by `ε_*` to a quasi-isomorphism.
* `Stacks.ModulesOnACategory.ChaoticComparison.rightAcyclic_forget_of_isZero_rightDerived`: a
  sheaf of modules whose module-valued cohomology over every object vanishes in positive degrees
  is acyclic for the forgetful functor to presheaves of modules.
* `Stacks.ModulesOnACategory.ChaoticComparison`
  `.isIso_derivedEpsilonAdjunction_unit_app_Lpullback_of_baseChange`: on a slice whose base changes
  `N ⊗_{O(U)} O_U` are acyclic sheaves, the `ε_U`-unit is invertible at every derived base change
  `P ⊗^L_{O(U)} O_U`.
* `Stacks.ModulesOnACategory.ChaoticComparison.isLocallyKFlatAcyclic_of_baseChange`: **hypothesis
  (2) of Stacks 0GZS** from the sheaf property and the acyclicity of the base changes
  `N ⊗_{O(U)} O_U`.

## Implementation notes

The complex `M^•` is unbounded, and no bound on cohomological dimension is available, so the
passage from single modules to complexes is the argument of
`StacksFrontier/Algebra/Homology/DerivedCategory/KInjectiveTruncationTower.lean`: the canonical
truncations `τ_{≥ n}` of the complex of sheaves `M^• ⊗ O_U` have terms of the form `N ⊗ O_U`,
because base change followed by sheafification preserves cokernels, so they are `ε_*`-acyclic;
the tower of injective resolutions of those truncations then gives a K-injective resolution which
`ε_*` carries to a quasi-isomorphism, the countable products of presheaves of modules being
exact.  Hence the comparison map of `Rε_*` is invertible at `M^• ⊗ O_U`, and the factorization
of the derived unit through the underived one (`Stacks.DerivedFunctor.derivedAdjunction_unit_app`)
gives the invertibility of the unit of `Lε^* ⊣ Rε_*` there.

The derived base change `M^• ⊗^L_{O(U)} O_U` is the derived pullback of
`Stacks.ModulesOnACategory.TerminalMorphismOfSites.Lpullback`, which is computed degreewise on a
K-flat complex (`CochainComplex.KFlatAdjunction.isIso_app_of_kFlat`); every object of `D(O(U))`
is represented by a K-flat complex (Stacks 06Y4).

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

namespace Stacks.ModulesOnACategory.ChaoticComparison

universe w u v r

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- **The `ε`-unit at a complex whose sheafification is resolved compatibly with `ε_*`.** Let
`Z` be a complex of presheaves of `O`-modules all of whose terms are `τ`-sheaves, and suppose its
sheafification `ε^*Z` admits a quasi-isomorphism `f` to a K-injective complex which `ε_*`
carries to a quasi-isomorphism.  Then the unit `Z ⟶ Rε_*(ε^*Z)` of the derived adjunction
`Lε^* ⊣ Rε_*` is an isomorphism.

The unit factors as the image of the degreewise unit, which is invertible because the terms of
`Z` are sheaves, followed by the comparison map of `Rε_*` at `ε^*Z`, which is invertible because
`f` computes `Rε_*`. -/
theorem isIso_derivedEpsilonAdjunction_unit_app_of_tower
    (Z : CochainComplex (PresheafOfModules.{max u v r w} R.obj) ℤ)
    (hZ : ∀ n, IsIso ((epsilonAdjunction.{w} R).unit.app (Z.X n)))
    {I : CochainComplex (SheafOfModules.{max u v r w} R) ℤ}
    (f : ((epsilonPullback.{w} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶ I)
    (hI : I.IsKInjective) [QuasiIso f]
    [QuasiIso (((epsilonPushforward.{w} R).mapHomologicalComplex (ComplexShape.up ℤ)).map f)] :
    IsIso ((derivedEpsilonAdjunction.{w} R).unit.app (DerivedCategory.Q.obj Z)) := by
  refine (NatTrans.isIso_app_iff_of_iso (derivedEpsilonAdjunction.{w} R).unit
    ((DerivedCategory.quotientCompQhIso _).app Z)).1 ?_
  have hfac := Stacks.DerivedFunctor.derivedAdjunction_unit_app (epsilonAdjunction.{w} R)
    (derivedEpsilonPushforward.{w} R) (derivedEpsilonPushforwardUnit.{w} R)
    (exists_quasiIso_isKInjective.{w} R)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Z)
  have hunit : IsIso ((Adjunction.mapHomotopyCategoryAdjunction (epsilonAdjunction.{w} R)
      (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Z)) := by
    rw [Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient]
    have : ∀ n, IsIso (((Adjunction.mapHomologicalComplexAdjunction (epsilonAdjunction.{w} R)
        (ComplexShape.up ℤ)).unit.app Z).f n) := hZ
    have : IsIso ((Adjunction.mapHomologicalComplexAdjunction (epsilonAdjunction.{w} R)
        (ComplexShape.up ℤ)).unit.app Z) :=
      HomologicalComplex.Hom.isIso_of_components _
    exact Functor.map_isIso _ _
  have hβ : IsIso ((derivedEpsilonPushforwardUnit.{w} R).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((epsilonPullback.{w} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))) :=
    Stacks.TruncationTower.isIso_derivedUnit_of_quasiIso_map (epsilonPushforward.{w} R)
      (exists_quasiIso_isKInjective.{w} R) (derivedEpsilonPushforward.{w} R)
      (derivedEpsilonPushforwardUnit.{w} R) f hI
  have hrhs : IsIso (DerivedCategory.Qh.map ((Adjunction.mapHomotopyCategoryAdjunction
        (epsilonAdjunction.{w} R) (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Z)) ≫
      (derivedEpsilonPushforwardUnit.{w} R).app
        (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Z))) := by
    have : IsIso ((derivedEpsilonPushforwardUnit.{w} R).app
        (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Z))) := hβ
    infer_instance
  rw [← hfac] at hrhs
  have : IsIso ((derivedEpsilonPushforward.{w} R).map
      ((epsilonPullback.{w} R).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Z))) := inferInstance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ this hrhs

/-- **A sheaf of modules with vanishing higher cohomology over every object is acyclic for the
forgetful functor to presheaves of modules.** The right derived functors of the forgetful functor
are computed sectionwise, evaluation of presheaves of modules being exact, and over an object
they are the module-valued cohomology over that object. -/
theorem rightAcyclic_forget_of_isZero_rightDerived
    [HasDerivedCategory (SheafOfModules.{max u v r w} R)]
    [HasDerivedCategory (PresheafOfModules.{max u v r w} R.obj)]
    (F : SheafOfModules.{max u v r w} R)
    (hF : ∀ (V : C) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op V)).rightDerived p).obj F)) :
    (SheafOfModules.forget R).rightAcyclic F := by
  rw [Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro V
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (SheafOfModules.forget R) (PresheafOfModules.evaluation R.obj V) p F
  have hz : IsZero (((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj V).rightDerived
      p).obj F) := hF V.unop p hp
  exact (hz.of_iso e).eq_of_src _ _

end Unit

section HypothesisTwo

open Stacks.TerminalBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000]
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v r w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

/-- **The `ε`-unit on the slice at a derived base change.** Let `U` be an object of `C` such that
for every `O(U)`-module `N` the presheaf `N ⊗_{O(U)} O_U` on `(C/U, τ)` is a `τ`-sheaf (`hsheaf`)
whose module-valued cohomology over every object of `C/U` vanishes in positive degrees
(`hacyc`).  Then for every object `P` of `D(O(U))` the unit
`P ⊗^L_{O(U)} O_U ⟶ Rε_{U*}(ε_U^*(P ⊗^L_{O(U)} O_U))` of the derived adjunction on the localized
site is an isomorphism.

Represent `P` by a K-flat complex `M^•`; the derived base change is then `M^• ⊗_{O(U)} O_U`
degreewise, a complex of sheaves, and the canonical truncations of its sheafification have terms
`N ⊗_{O(U)} O_U`, acyclic for `ε_{U*}`; the tower of injective resolutions of those truncations
computes `Rε_{U*}`. -/
theorem isIso_derivedEpsilonAdjunction_unit_app_Lpullback_of_baseChange (U : C)
    (hsheaf : ∀ (N : ModuleCat.{max u v r w}
        ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U))))),
      letI := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
        (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
      Presheaf.IsSheaf (J.over U) ((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
        (Over.mkIdTerminal (X := U))).obj N).presheaf)
    (hacyc : ∀ (N : ModuleCat.{max u v r w}
        ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U))))) (V : Over U) (p : ℕ), 0 < p →
      letI := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
        (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
      IsZero (((SheafOfModules.evaluation (overRingSheaf R U) (op V)).rightDerived p).obj
        ⟨(baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
          (Over.mkIdTerminal (X := U))).obj N, hsheaf N⟩))
    (P : DerivedCategory (ModuleCat.{max u v r w}
      ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U)))))) :
    IsIso ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
      ((morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
        (Over.mkIdTerminal (X := U))).Lpullback.obj P)) := by
  let := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
    (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
  -- a K-flat complex `M` representing `P`
  obtain ⟨M, g, hM, -, hg, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{r, max u v w}
      (DerivedCategory.Q.objPreimage P)
  have eP : DerivedCategory.Q.obj M ≅ P :=
    @asIso _ _ _ _ (DerivedCategory.Q.map g)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (φ := g)).2 hg) ≪≫
      DerivedCategory.Q.objObjPreimageIso P
  -- the derived base change of `M` is the degreewise one, `M` being K-flat
  have hLM : IsIso ((Stacks.ModulesOnACategory.TerminalMorphismOfSites.LpullbackComparison.{w}
      (overRingPresheaf R.obj U) (Over.mkIdTerminal (X := U))).app M) :=
    CochainComplex.KFlatAdjunction.isIso_app_of_kFlat
      (baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U) (Over.mkIdTerminal (X := U)))
      (Stacks.ModulesOnACategory.TerminalMorphismOfSites.quasiIso_baseChangePresheaf_map.{w}
        (overRingPresheaf R.obj U) (Over.mkIdTerminal (X := U)))
      _ _ M hM
  have eZ : (morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
        (Over.mkIdTerminal (X := U))).Lpullback.obj P ≅
      DerivedCategory.Q.obj
        (((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
          (Over.mkIdTerminal (X := U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
    ((morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
        (Over.mkIdTerminal (X := U))).Lpullback.mapIso eP).symm ≪≫
      @asIso _ _ _ _ _ hLM
  refine (NatTrans.isIso_app_iff_of_iso
    (derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit eZ).2 ?_
  -- the base changes `N ⊗ O_U` are sheaves
  have hunit : ∀ N, IsIso ((epsilonAdjunction.{w} (overRingSheaf R U)).unit.app
      ((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
        (Over.mkIdTerminal (X := U))).obj N)) := fun N =>
    ((epsilonAdjunction.{w} (overRingSheaf R U)).isIso_unit_app_iff_mem_essImage).2
      ⟨⟨_, hsheaf N⟩, ⟨Iso.refl _⟩⟩
  -- their sheafifications are acyclic for the forgetful functor
  have hLacyc : ∀ N, (SheafOfModules.forget (overRingSheaf R U)).rightAcyclic
      ((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
        (Over.mkIdTerminal (X := U)) ⋙ sliceEpsilonPullback.{w} R U).obj N) :=
    fun N => by
      let e : (epsilonPullback.{w} (overRingSheaf R U)).obj
          ((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
            (Over.mkIdTerminal (X := U))).obj N) ≅ ⟨_, hsheaf N⟩ :=
        (epsilonPushforward.{w} (overRingSheaf R U)).preimageIso
          ((@asIso _ _ _ _ _ (hunit N)).symm ≪≫ Iso.refl _)
      exact (SheafOfModules.forget (overRingSheaf R U)).rightAcyclic.prop_of_iso e.symm
        (rightAcyclic_forget_of_isZero_rightDerived.{w} (overRingSheaf R U) _
          (fun V p hp => hacyc N V p hp))
  -- the tower of injective resolutions of the truncations
  have : HasExactLimitsOfShape (Discrete ℕ)
      (PresheafOfModules.{max u v r w} (overRingSheaf R U).obj) :=
    Stacks.TruncationTower.presheafModules_hasExactCountableProducts _
  have : PreservesLimitsOfSize.{0, 0} (SheafOfModules.forget.{max u v r w} (overRingSheaf R U)) :=
    ⟨fun {_} _ ↦ inferInstance⟩
  have : (baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
      (Over.mkIdTerminal (X := U))).Additive := inferInstance
  have : (baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
      (Over.mkIdTerminal (X := U)) ⋙ sliceEpsilonPullback.{w} R U).Additive := inferInstance
  have : PreservesColimitsOfShape WalkingParallelPair
      (baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
        (Over.mkIdTerminal (X := U)) ⋙ sliceEpsilonPullback.{w} R U) :=
    ((baseChangeAdj.{max u v w} (overRingPresheaf R.obj U) (Over.mkIdTerminal (X := U))).comp
      (epsilonAdjunction.{w} (overRingSheaf R U))).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  obtain ⟨I, f, hI, hf, hFf⟩ :=
    Stacks.TruncationTower.exists_quasiIso_isKInjective_map_quasiIso
      (SheafOfModules.forget.{max u v r w} (overRingSheaf R U))
      (fun f hf => Stacks.TruncationTower.quasiIso_of_forget_map_quasiIso _ f hf)
      (((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
        (Over.mkIdTerminal (X := U)) ⋙ sliceEpsilonPullback.{w} R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)
      (Stacks.TruncationTower.property_truncGE_map
        (baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
          (Over.mkIdTerminal (X := U)) ⋙ sliceEpsilonPullback.{w} R U) _ hLacyc M)
  have : QuasiIso f := hf
  have : QuasiIso (((epsilonPushforward.{w} (overRingSheaf R U)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := hFf
  exact isIso_derivedEpsilonAdjunction_unit_app_of_tower.{w} (overRingSheaf R U) _
    (fun n => hunit _) f hI


/-- **Hypothesis (2) of Stacks 0GZS from the acyclicity of base changes.** Suppose that for
every object `U` of `C` and every `O(U)`-module `N` the presheaf `N ⊗_{O(U)} O_U` on the
localized site `(C/U, τ)` is a `τ`-sheaf (`hsheaf`) whose module-valued cohomology over every
object of `C/U` vanishes in positive degrees (`hacyc`).  Then for every `U` and every K-flat
complex `M^•` of `O(U)`-modules the canonical map
`M^• ⟶ RΓ((C/U)_τ, (M^• ⊗_{O(U)} O_U)^#)` is a quasi-isomorphism, which is hypothesis (2) of
Stacks 0GZS, `IsLocallyKFlatAcyclic`. -/
theorem isLocallyKFlatAcyclic_of_baseChange
    (hsheaf : ∀ (U : C) (N : ModuleCat.{max u v r w}
        ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U))))),
      letI := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
        (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
      Presheaf.IsSheaf (J.over U) ((baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
        (Over.mkIdTerminal (X := U))).obj N).presheaf)
    (hacyc : ∀ (U : C) (N : ModuleCat.{max u v r w}
        ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U))))) (V : Over U) (p : ℕ), 0 < p →
      letI := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
        (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
      IsZero (((SheafOfModules.evaluation (overRingSheaf R U) (op V)).rightDerived p).obj
        ⟨(baseChangePresheaf.{max u v w} (overRingPresheaf R.obj U)
          (Over.mkIdTerminal (X := U))).obj N, hsheaf U N⟩)) :
    IsLocallyKFlatAcyclic.{w} R hO := by
  intro U P
  let := Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
    (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
  have hunitP : IsIso ((morphismOfSites (overRingPresheaf R.obj U)
      (comm_overRingPresheaf R.obj U hO) (Over.mkIdTerminal (X := U))).adj.unit.app P) :=
    main_unit_isIso.{w} _ _ P
  exact IsIso.comp_isIso' hunitP (@Functor.map_isIso _ _ _ _ _ _ _ _
    (isIso_derivedEpsilonAdjunction_unit_app_Lpullback_of_baseChange.{w} R hO U (hsheaf U)
      (hacyc U) P))

end HypothesisTwo

end Stacks.ModulesOnACategory.ChaoticComparison

end
