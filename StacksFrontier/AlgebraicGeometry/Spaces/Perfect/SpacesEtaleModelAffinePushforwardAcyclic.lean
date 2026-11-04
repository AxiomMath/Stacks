module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleCollapseViaPlus
public import StacksFrontier.Algebra.Homology.RightDerivedExactPrecompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineDerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProductsBaseChange

/-!
# Direct image along an affine morphism on the spaces-étale model: acyclicity

Let `g : X ⟶ Y` be an affine morphism of algebraic spaces and `N` a sheaf of modules on the
spaces-étale model of `X` whose image among the `𝒪_X`-modules is quasi-coherent. This file shows
that `N` is right acyclic for the direct image `g_*` on the models, so that
`Rg_*(N[0]) ≅ (g_*N)[0]` (Stacks 073H on the models).

The cohomology of `N` over an object of the model of the form `V`, `V` an affine étale scheme
chart of `X`, is that of the corresponding `𝒪_X`-module over `V`, which vanishes in positive
degrees (`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`): the two
section functors agree through the equivalence of module categories, which is exact and
preserves injectives. Every object of the model of `Y` is covered by affine étale scheme charts,
whose base changes along `g` are affine étale scheme charts of `X`; the covering criterion
`Stacks.Cohomology.ModuleDirectImageOnACover.rightAcyclic_pushforward_of_presieve` concludes.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_spacesEtaleModel_of_isAffineChart`.
* `AlgebraicGeometry.Space.rightAcyclic_spacesEtaleModelHom_pushforwardTopos_of_isAffineHom`.
* `AlgebraicGeometry.Space.singleDerivedPushforwardIsoOfRightAcyclic` and
  `AlgebraicGeometry.Space.singleDerivedPushforwardPullbackToBaseRingIso`.

## References

* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sections

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- Sections over an object of a sheaf of modules, as an abelian group. -/
abbrev abSections (W : C) : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W)

/-- Sections over isomorphic objects agree. -/
def abSectionsIsoOfIso {W W' : C} (i : W ≅ W') : abSections R W ≅ abSections R W' :=
  Functor.isoWhiskerLeft (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)
    ((evaluation Cᵒᵖ AddCommGrpCat.{u}).mapIso i.symm.op)

/-- Sections as modules, followed by the underlying abelian group, are sections as abelian
groups. -/
def evaluationForgetIso (W : C) :
    SheafOfModules.evaluation.{u} R (op W) ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op W))) AddCommGrpCat.{u} ≅
      abSections R W :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Sections of a restricted module over `V` are the sections of the module over `v(V)`. -/
def abSectionsModuleRestrictionIso {D : Type*} [Category* D] (K : GrothendieckTopology D)
    (v : D ⥤ C) [v.IsDenseSubsite K J] (V : D) :
    Stacks.DenseSubsiteModules.moduleRestriction.{u} K J v R ⋙
        abSections (Stacks.DenseSubsiteModules.ringRestriction K J v R) V ≅
      abSections R (v.obj V) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Restriction of scalars does not change sections. -/
def abSectionsRestrictScalarsIso {R' : Sheaf J RingCat.{u}} (α : R ⟶ R') (V : C) :
    SheafOfModules.restrictScalars.{u} α ⋙ abSections R V ≅ abSections R' V :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **Images of enough objects of a dense subsite cover.** If every object of `(C, J)` is
covered by objects with property `P` and `G : (C, J) ⥤ (D, K)` is a dense subsite, then every
object `V` of `D` is covered by the arrows out of objects isomorphic to some `G(U)` with `P U`. -/
theorem generate_mem_of_hasEnoughObjects_of_isDenseSubsite {D : Type*} [Category* D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsDenseSubsite J K] (P : ObjectProperty C)
    (hP : J.HasEnoughObjects P) (V : D) :
    Sieve.generate (fun W (_ : W ⟶ V) => ∃ U, P U ∧ Nonempty (W ≅ G.obj U)) ∈ K V := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  refine K.transitive (G.is_cover_of_isCoverDense K V) _ ?_
  rintro Z f ⟨⟨Y, h, k, rfl⟩⟩
  rw [Sieve.pullback_comp]
  refine K.pullback_stable h ?_
  obtain ⟨I, Ui, fi, hcov, hPi⟩ := hP Y
  refine K.superset_covering ?_ ((Functor.functorPushforward_mem_iff J K G).2 hcov)
  rintro W g ⟨Z', a, b, ⟨Y', g', _, ⟨i⟩, rfl⟩, rfl⟩
  exact ⟨G.obj (Ui i), b ≫ G.map g', G.map (fi i) ≫ k, ⟨Ui i, hPi i, ⟨Iso.refl _⟩⟩, by simp⟩

end Sections

variable {X : AlgebraicSpaces B S hS}

variable (X) in
/-- The `𝒪_X`-modules at the universe of the structure rings have enough injectives
(`AlgebraicGeometry.Space.enoughInjectives_modules`, as a local instance). -/
local instance (priority := 5000) enoughInjectives_modules_smallEtale :
    EnoughInjectives (Modules.{u, u} B S hS X.1 X.2) :=
  enoughInjectives_modules B S hS X.1 X.2

/-- **Sections of a module on the spaces-étale model over an étale scheme chart are the sections
of the corresponding `𝒪_X`-module.** -/
def abSectionsSpacesEtaleModelIso (U : SmallEtale B S hS X.1) :
    abSections (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O)
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
          ((comparisonFunctor B S hS X).obj U)) ≅
      (spacesEtaleModelModulesEquiv B S hS X).functor ⋙ abSections _ U :=
  let ex := smallEtaleModelEquiv B S hS X
  let D := smallEtaleModelModulesEquiv B S hS X
  let F₁ := Stacks.DenseSubsiteModules.moduleRestriction.{u} (smallEtaleModelTopology B S hS X.1)
    (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
    (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))
  let F₂ := SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).inv
  abSectionsIsoOfIso _ ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.mapIso
      ((comparisonFunctor B S hS X).mapIso (ex.unitIso.app U))) ≪≫
    (abSectionsModuleRestrictionIso
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))
      (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X)
      (ex.functor.obj U)).symm ≪≫
    Functor.isoWhiskerLeft F₁ (abSectionsRestrictScalarsIso _
      (spacesEtaleModelRingRestrictionIso B S hS X).inv (ex.functor.obj U)).symm ≪≫
    (Functor.associator F₁ F₂ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (F₁ ⋙ F₂) D.counitIso).symm _ ≪≫
    Functor.associator (F₁ ⋙ F₂) (D.inverse ⋙ D.functor) _ ≪≫
    Functor.isoWhiskerLeft (F₁ ⋙ F₂) (Functor.associator D.inverse D.functor _) ≪≫
    (Functor.associator (F₁ ⋙ F₂) D.inverse _).symm ≪≫
    Functor.isoWhiskerLeft (spacesEtaleModelModulesEquiv B S hS X).functor
      (abSectionsModuleRestrictionIso (structureRingSheaf B S hS X)
        (smallEtaleModelTopology B S hS X.1) ex.inverse (ex.functor.obj U) ≪≫
        abSectionsIsoOfIso _ (ex.unitIso.app U).symm)

variable (X) in
/-- Modules on the spaces-étale model form a Grothendieck abelian category at universe `u`. -/
local instance isGrothendieckAbelian_spacesEtaleModelModules :
    IsGrothendieckAbelian.{u} (spacesEtaleModelRingedTopos B S hS X).Modules :=
  SheafOfModules.isGrothendieckAbelianU _

variable (X) in
/-- Modules on the spaces-étale model have enough injectives. -/
local instance (priority := 5000) enoughInjectives_spacesEtaleModelModules :
    EnoughInjectives (spacesEtaleModelRingedTopos B S hS X).Modules :=
  SheafOfModules.enoughInjectivesU.{u, u, u} _

/-- **Cohomology on the spaces-étale model over an affine étale scheme chart vanishes in positive
degrees** for a module whose corresponding `𝒪_X`-module is quasi-coherent: the section functors
over the chart agree through the exact equivalence of module categories, which preserves
injectives, and on the `𝒪_X`-modules the vanishing is
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`. -/
theorem isZero_rightDerived_evaluation_spacesEtaleModel_of_isAffineChart
    (N : (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hN : ((spacesEtaleModelModulesEquiv B S hS X).functor.obj N).IsQuasicoherentOnSite)
    (W : SmallModel.{u} (SpacesEtale B S hS X)) (U : SmallEtale B S hS X.1)
    (hU : IsAffineChart B S hS X.1 U)
    (i : W ≅ (equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
      ((comparisonFunctor B S hS X).obj U)) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O)
      (op W)).rightDerived p).obj N) := by
  let Rm := Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O
  let e := spacesEtaleModelModulesEquiv B S hS X
  let M := e.functor.obj N
  let Rs := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  have h₁ : IsZero (((abSections Rs U).rightDerived p).obj M) :=
    IsZero.of_iso ((forget₂ (ModuleCat.{u} (Rs.obj.obj (op U))) AddCommGrpCat.{u}).map_isZero
        (isZero_rightDerived_evaluation_of_isAffineChart B S hS X.1 X.2 M hN U hU p hp))
      ((Functor.rightDerivedIsoOfNatIso (evaluationForgetIso Rs U).symm p).app M ≪≫
        (Functor.rightDerivedCompIso (SheafOfModules.evaluation.{u} Rs (op U))
          (forget₂ (ModuleCat.{u} (Rs.obj.obj (op U))) AddCommGrpCat.{u}) p).app M)
  let ε := Stacks.Cohomology.RightDerivedEdgeIso.rightDerivedIsoOfExactOfIso e.functor
    (abSections Rs U) (abSections Rm ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.obj
      ((comparisonFunctor B S hS X).obj U))) (𝟭 _)
    ((abSectionsSpacesEtaleModelIso B S hS U).symm ≪≫ (Functor.rightUnitor _).symm) p
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1
    (IsZero.of_iso h₁
      (((Functor.rightDerivedCompIso (SheafOfModules.evaluation.{u} Rm (op W))
        (forget₂ (ModuleCat.{u} (Rm.obj.obj (op W))) AddCommGrpCat.{u}) p).app N).symm ≪≫
        (Functor.rightDerivedIsoOfNatIso (evaluationForgetIso Rm W) p).app N ≪≫
        (Functor.rightDerivedIsoOfNatIso (abSectionsIsoOfIso Rm i) p).app N ≪≫ (ε.app N).symm)))

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory

variable (X) in
/-- The spaces-étale model is essentially small at universe `u`. -/
local instance essentiallySmall_spacesEtaleModel :
    EssentiallySmall.{u} (spacesEtaleModelRingedTopos B S hS X).C :=
  essentiallySmallSelf.{u, u, u} _

variable (X) in
/-- Abelian presheaves on the spaces-étale model are sheafifiable. -/
local instance hasSheafify_spacesEtaleModel :
    HasSheafify (spacesEtaleModelRingedTopos B S hS X).J AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u, u + 1, u} _ _

variable (X) in
/-- On the spaces-étale model sheafification inverts exactly the locally bijective maps. -/
local instance wEqualsLocallyBijective_spacesEtaleModel :
    (spacesEtaleModelRingedTopos B S hS X).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u} _

/-- **Modules quasi-coherent on the `𝒪_X`-side are right acyclic for the direct image along an
affine morphism, on the spaces-étale models** (Stacks 073H on the models). Every object of the
model of `Y` is covered by affine étale scheme charts, their base changes along `g` are affine
étale scheme charts of `X`, and over those the cohomology of `N` vanishes in positive degrees
(`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_spacesEtaleModel_of_isAffineChart`). -/
theorem rightAcyclic_spacesEtaleModelHom_pushforwardTopos_of_isAffineHom
    {Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) (hg : IsAffineHom B S hS g.hom)
    (N : (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hN : ((spacesEtaleModelModulesEquiv B S hS X).functor.obj N).IsQuasicoherentOnSite) :
    (spacesEtaleModelHom B S hS g).pushforwardTopos.rightAcyclic N := by
  have hr := relativelyRepresentable_of_isAffineHom B S hS g hg
  let Ey := equivSmallModel.{u} (SpacesEtale B S hS Y)
  let c' := comparisonFunctor B S hS Y ⋙ Ey.functor
  have : c'.IsDenseSubsite (SmallEtale.topology B S hS Y.1) (smallModelTopology B S hS Y) :=
    Functor.isDenseSubsite_comp _ (SpacesEtale.topology B S hS Y) _ _ _
  have key : ∀ p : ℕ, 0 < p → ∀ V : SmallModel.{u} (SpacesEtale B S hS Y), ∃ R : Presieve V,
      Sieve.generate R ∈ smallModelTopology B S hS Y V ∧ ∀ ⦃W⦄ (k : W ⟶ V), R k →
        IsZero (((SheafOfModules.evaluation.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O)
          (op ((spacesEtaleModelHom B S hS g).u.obj W))).rightDerived p).obj N) := by
    intro p hp V
    refine ⟨_, generate_mem_of_hasEnoughObjects_of_isDenseSubsite
      (smallModelTopology B S hS Y) c' (IsAffineChart B S hS Y.1)
      (hasEnoughObjects_isAffineChart B S hS Y.1) V, ?_⟩
    rintro W k ⟨U, hU, ⟨iW⟩⟩
    exact isZero_rightDerived_evaluation_spacesEtaleModel_of_isAffineChart B S hS N hN _
      ((smallBaseChange B S hS g hr).obj U)
      (isAffineChart_smallBaseChange_of_isAffineHom B S hS g hg hr U hU)
      ((smallModelBaseChange B S hS g).mapIso iW ≪≫
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor.mapIso
          ((spacesBaseChange B S hS g).functor.mapIso
            (Ey.unitIso.app ((comparisonFunctor B S hS Y).obj U)).symm ≪≫
          (smallBaseChangeComparisonIso B S hS g hr U).symm)) p hp
  have : (SheafOfModules.pushforward.{u} (spacesEtaleModelHom B S hS g).fSharpRing).Additive :=
    (spacesEtaleModelHom B S hS g).pushforwardTopos_additive
  exact Stacks.Cohomology.ModuleDirectImageOnACover.rightAcyclic_pushforward_of_presieve
    (spacesEtaleModelHom B S hS g).u _ _ (spacesEtaleModelHom B S hS g).fSharpRing N key

/-- **`Rg_*(N[0]) ≅ (g_*N)[0]` on a family of right acyclic modules, naturally.** For a functor
`τ` into the modules on the spaces-étale model of `X` whose values are right acyclic for `g_*`,
the unit of the derived direct image at the complexes `τ(c)[0]` is invertible. -/
def singleDerivedPushforwardIsoOfRightAcyclic {Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    {𝒞 : Type*} [Category* 𝒞] (τ : 𝒞 ⥤ (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hτ : ∀ c, (spacesEtaleModelHom B S hS g).pushforwardTopos.rightAcyclic (τ.obj c)) :
    τ ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
          (spacesEtaleModelHom B S hS g) ≅
      τ ⋙ (spacesEtaleModelHom B S hS g).pushforwardTopos ⋙ DerivedCategory.singleFunctor _ 0 :=
  let f := spacesEtaleModelHom B S hS g
  let α := Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit f
  let RF := Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u} f
  let ν := Stacks.DerivedFunctor.singleUnit f.pushforwardTopos RF α
  haveI : ∀ c, IsIso ((Functor.whiskerLeft τ ν).app c) := fun c => by
    have := Functor.isIso_app_single_of_rightAcyclic f.pushforwardTopos RF α
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective
        (spacesEtaleModelRingedTopos B S hS X))
      (τ.obj c) (hτ c)
    simp only [Functor.whiskerLeft_app, ν, Stacks.DerivedFunctor.singleUnit, NatTrans.comp_app]
    infer_instance
  haveI : IsIso (Functor.whiskerLeft τ ν) := NatIso.isIso_of_isIso_app _
  (asIso (Functor.whiskerLeft τ ν)).symm

/-- **Stacks 073H on the spaces-étale models, in the form `Rg_*(τ(-)[0]) ≅ (g_*τ(-))[0]`**, for an
affine `g` and a functor `τ` whose values are quasi-coherent on the `𝒪_X`-side. -/
def singleDerivedPushforwardIsoOfIsAffineHom {Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (hg : IsAffineHom B S hS g.hom)
    {𝒞 : Type*} [Category* 𝒞] (τ : 𝒞 ⥤ (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hτ : ∀ c, ((spacesEtaleModelModulesEquiv B S hS X).functor.obj
      (τ.obj c)).IsQuasicoherentOnSite) :
    τ ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
          (spacesEtaleModelHom B S hS g) ≅
      τ ⋙ (spacesEtaleModelHom B S hS g).pushforwardTopos ⋙ DerivedCategory.singleFunctor _ 0 :=
  singleDerivedPushforwardIsoOfRightAcyclic B S hS g τ fun c =>
    rightAcyclic_spacesEtaleModelHom_pushforwardTopos_of_isAffineHom B S hS g hg _ (hτ c)

/-- **`Rg_*((f^*M)[0]) ≅ (g_*f^*M)[0]`, naturally in the `Γ(T)`-module `M`**, for `f : X ⟶ T` and
an affine `g : X ⟶ Y`: the modules `f^*M` on the spaces-étale model are `𝒪_X ⊗_{Γ(T)} M` on the
`𝒪_X`-side (`AlgebraicGeometry.Space.pullbackToBaseRingIso`), which is quasi-coherent. -/
def singleDerivedPushforwardPullbackToBaseRingIso {T : BigFppfOver B S hS}
    {Y : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (g : X ⟶ Y)
    (hg : IsAffineHom B S hS g.hom) :
    ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        DerivedCategory.singleFunctor _ 0 ⋙
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
          (spacesEtaleModelHom B S hS g) ≅
      ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos ⋙ DerivedCategory.singleFunctor _ 0 :=
  singleDerivedPushforwardIsoOfIsAffineHom B S hS g hg _ fun M =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((pullbackToBaseRingIso B S hS X (baseRingHomOfMap f)).app M).symm
      (isQuasicoherentOnSite_baseRingTensorModule B S hS X _ M)

end AlgebraicGeometry.Space

end
