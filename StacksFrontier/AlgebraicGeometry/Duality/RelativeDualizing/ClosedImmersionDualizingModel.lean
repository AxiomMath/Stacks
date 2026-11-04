module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DimensionFunctionScheme
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportRestrictDerivedIso
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing

/-!
# `R𝓗om(𝒪_Y, -)` of a dualizing model along a closed immersion

Let `i : Y ⟶ X` be a closed immersion into a locally Noetherian scheme and let `U ⊆ X` be an
affine open with `A = Γ(X, U)` and `B = Γ(Y, i⁻¹U)`. If `K ∈ D(𝒪_X)` restricts on `U` to the
sheaf associated to a dualizing complex `ω` over `A`, then `R𝓗om(𝒪_Y, K)` restricts on `i⁻¹U`
to the sheaf associated to `R Hom_A(B, ω)`, which is a dualizing complex over `B`
([Stacks, Tag 0AX0]). Consequently `R𝓗om(𝒪_Y, -)` carries dualizing complexes on `X` to
dualizing complexes on `Y` ([Stacks, Tag 0A86]).

Everything is stated at the locally small model of the derived categories,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the one at which the right adjoints of
[Stacks, Tag 0A9E] exist.

## Main definitions

* `Stacks.Injectives.mapDerivedCategoryGrothendieckModelsIso`: the derived functor of an exact
  functor between Grothendieck abelian categories does not depend on the models of its source and
  target derived categories.
* `Stacks.Duality.LocallySmall.derivedSheafHomExactSupportModelIso`: the same for
  `R𝓗om(𝒪_Z, -)` of a closed quotient morphism of ringed spaces.
* `Stacks.Duality.LocallySmall.affineDerivedSheafHomExactSupportTildeIso`: [Stacks, Tag 0A78],
  part (2), at the locally small model: `R𝓗om(𝒪_{Spec B}, L^~) ≅ (R Hom_A(B, L))^~` for `L`
  bounded below.
* `Stacks.Duality.LocallySmall.derivedSheafHomExactSupportRestrictIsoOfIso`: `R𝓗om(𝒪_Y, -)`
  transported along isomorphisms of the source and target of the closed immersion.

## Main results

* `Stacks.Duality.isDualizingModelOn_derivedSheafHomExactSupport`: if `ω` is a dualizing model
  of `K` on `U`, then `R Hom_A(B, ω)` is one of `R𝓗om(𝒪_Y, K)` on `i⁻¹U`.
* `Stacks.Duality.hasDualizingModelOn_derivedSheafHomExactSupport`: the same with the models
  left existential.
* `Stacks.Duality.isDualizingComplex_derivedSheafHomExactSupport`: `R𝓗om(𝒪_Y, K)` is a
  dualizing complex on `Y` whenever `K` is one on `X` ([Stacks, Tag 0A86]).

## References

* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe w u u₁ v₁ u₂ v₂

namespace Stacks.Injectives

section BothModels

variable (C₁ : Type u₁) [Category.{v₁} C₁] [Abelian C₁] [IsGrothendieckAbelian.{w} C₁]
  (C₂ : Type u₂) [Category.{v₂} C₂] [Abelian C₂] [IsGrothendieckAbelian.{w} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The derived functor of an exact functor read at the two models of source and target.**
Computed at the standard models and transported by the comparison of `D(C₂)`, it is the derived
functor at the locally small models precomposed with the comparison of `D(C₁)`. -/
def mapDerivedCategoryGrothendieckModelsIso :
    @Functor.mapDerivedCategory C₁ _ _ (HasDerivedCategory.standard C₁) C₂ _ _
          (HasDerivedCategory.standard C₂) F _ _ _ ⋙
        (grothendieckModelEquiv.{w} C₂).functor ≅
      (grothendieckModelEquiv.{w} C₁).functor ⋙
        @Functor.mapDerivedCategory C₁ _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C₁)
          C₂ _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C₂) F _ _ _ :=
  Functor.isoWhiskerRight
      (mapDerivedCategoryModelIso.{w} C₁ (hd₂ := HasDerivedCategory.standard C₂) F)
      (grothendieckModelEquiv.{w} C₂).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (grothendieckModelEquiv.{w} C₁).functor
      (mapDerivedCategoryTargetModelIso
        (hd₁ := hasDerivedCategory_of_isGrothendieckAbelian.{w} C₁) C₂ F)

end BothModels

end Stacks.Injectives

namespace Stacks.Duality.LocallySmall

/-- **`R ℰom(𝒪_Z, -)` read at the two models.** For a closed quotient morphism of ringed spaces,
the right derived functor of sheaf Hom with exact support at the standard models, followed by the
comparison of `D(𝒪_Z)`, is the one at the locally small models preceded by the comparison of
`D(𝒪_X)`. -/
def derivedSheafHomExactSupportModelIso (S : ClosedQuotientMorphismOfRingedSpaces.{u}) :
    S.derivedSheafHomExactSupport ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u}
          (SheafOfModules.{u} (structureSheafRing S.Z))).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u}
          (SheafOfModules.{u} (structureSheafRing S.X))).functor ⋙
        Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{u} S :=
  StacksDraft.DerivedModel.rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))
    S.derivedSheafHomExactSupportComparison
    (Stacks.Duality.AnyModel.derivedSheafHomExactSupportComparison.{u} S)
    (StacksDraft.DerivedModel.shrinkComparisonQhIso
      (SheafOfModules.{u} (structureSheafRing S.X))).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.shrinkComparisonQhIso
        (SheafOfModules.{u} (structureSheafRing S.Z))).symm)

/-- **[Stacks, Tag 0A78], part (2), at the locally small model.** For a ring map `φ : A ⟶ B`
whose spectrum is a closed immersion into a locally Noetherian scheme and a bounded-below `L` in
`D(A)`, `R ℰom(𝒪_{Spec B}, L^~) ≅ (R Hom_A(B, L))^~`. Boundedness below of `L` is read at the
standard model. -/
def affineDerivedSheafHomExactSupportTildeIso (A B : CommRingCat.{u}) (φ : A ⟶ B)
    [IsClosedImmersion (Spec.map φ)] [IsLocallyNoetherian (Spec A)]
    (L : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (hL : @DerivedCategoryB.IsBoundedBelow (ModuleCat.{u} A) _ _
      (HasDerivedCategory.standard _) L) :
    (derivedSheafHomExactSupport (Spec.map φ)).obj ((tilde.functor A).mapDerivedCategory.obj L) ≅
      (tilde.functor B).mapDerivedCategory.obj ((Dualizing.derivedHom.{u, u, u} φ.hom).obj L) :=
  haveI := isIso_affineDerivedSheafHomComparison_app_of_noetherian A B φ L hL
  (derivedSheafHomExactSupport (Spec.map φ)).mapIso
      ((Stacks.Injectives.mapDerivedCategoryGrothendieckModelsIso (ModuleCat.{u} A) (Spec A).Modules
        (tilde.functor A)).app L).symm ≪≫
    ((derivedSheafHomExactSupportModelIso (closedQuotient (Spec.map φ))).app _).symm ≪≫
    (Stacks.Injectives.grothendieckModelEquiv.{u} (Spec B).Modules).functor.mapIso
      (asIso ((affineDerivedSheafHomComparison A B φ).app L)).symm ≪≫
    (Stacks.Injectives.mapDerivedCategoryGrothendieckModelsIso (ModuleCat.{u} B) (Spec B).Modules
        (tilde.functor B)).app _

section Transport

variable {Y X Y' X' : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (i' : Y' ⟶ X')
  [IsClosedImmersion i'] (a : Y' ≅ Y) (b : X' ≅ X)

/-- Restriction along the inverse of an isomorphism of schemes is left adjoint to restriction
along the isomorphism. -/
def restrictInvRestrictAdjunction :
    Scheme.Modules.restrictFunctor a.inv ⊣ Scheme.Modules.restrictFunctor a.hom :=
  (Scheme.Modules.restrictAdjunction a.inv).ofNatIsoRight
    (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv a).symm

/-- For closed immersions `i`, `i'` and isomorphisms `a`, `b` with `a ≫ i = i' ≫ b`, restricting
along `a.inv` and pushing forward along `i` is pushing forward along `i'` and restricting along
`b.inv`. -/
def restrictInvPushforwardIso (h : a.hom ≫ i = i' ≫ b.hom) :
    Scheme.Modules.restrictFunctor a.inv ⋙ Scheme.Modules.pushforward i ≅
      Scheme.Modules.pushforward i' ⋙ Scheme.Modules.restrictFunctor b.inv :=
  Functor.isoWhiskerRight
      (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv a.symm) _ ≪≫
    Scheme.Modules.pushforwardComp a.hom i ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    (Scheme.Modules.pushforwardComp i' b.hom).symm ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv b.symm).symm

/-- `restrictInvPushforwardIso` on unbounded derived categories, all four functors being
exact. -/
def restrictInvPushforwardDerivedIso (h : a.hom ≫ i = i' ≫ b.hom) :
    (Scheme.Modules.restrictFunctor a.inv).mapDerivedCategory ⋙
        (Scheme.Modules.pushforward i).mapDerivedCategory ≅
      (Scheme.Modules.pushforward i').mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor b.inv).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr (restrictInvPushforwardIso i i' a b h) ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl _)).symm

/-- **`R ℰom(𝒪_Y, -)` transported along isomorphisms of schemes.** For closed immersions
`i : Y ⟶ X` and `i' : Y' ⟶ X'` and isomorphisms `a : Y' ≅ Y`, `b : X' ≅ X` with
`a ≫ i = i' ≫ b`, restricting `R ℰom(𝒪_Y, K)` along `a` is `R ℰom(𝒪_{Y'}, -)` of the
restriction of `K` along `b`, at the locally small derived categories. -/
def derivedSheafHomExactSupportRestrictIsoOfIso (h : a.hom ≫ i = i' ≫ b.hom) :
    derivedSheafHomExactSupport i ⋙ (Scheme.Modules.restrictFunctor a.hom).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor b.hom).mapDerivedCategory ⋙
        derivedSheafHomExactSupport i' :=
  let adja := Adjunction.mapDerivedCategory (restrictInvRestrictAdjunction a)
  let adjb := Adjunction.mapDerivedCategory (restrictInvRestrictAdjunction b)
  (adja.comp (derivedModulePushforwardSheafHomExactSupportAdjunction i)).rightAdjointUniq
    (((derivedModulePushforwardSheafHomExactSupportAdjunction i').comp adjb).ofNatIsoLeft
      (restrictInvPushforwardDerivedIso i i' a b h).symm)

end Transport

end Stacks.Duality.LocallySmall

namespace Stacks.Duality

open LocallySmall

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] (i : Y ⟶ X) [IsClosedImmersion i]

omit [IsLocallyNoetherian X] in
/-- The comparison `i⁻¹U ≅ Spec Γ(Y, i⁻¹U)` and `U ≅ Spec Γ(X, U)` intertwine the restriction
`i ∣_ U` with the spectrum of `i^♯ : Γ(X, U) ⟶ Γ(Y, i⁻¹U)`. -/
theorem isoSpec_inv_morphismRestrict {U : X.Opens} (hU : IsAffineOpen U) :
    (hU.preimage i).isoSpec.inv ≫ i ∣_ U = Spec.map (i.app U) ≫ hU.isoSpec.inv := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec i hU (hU.preimage i) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, Category.assoc, IsAffineOpen.isoSpec_inv_ι, h]

/-- **`R𝓗om(𝒪_Y, -)` carries a dualizing model to a dualizing model.** Let `i : Y ⟶ X` be a
closed immersion into a locally Noetherian scheme, `U ⊆ X` an affine open and `K ∈ D(𝒪_X)`
(locally small model) with `K|_U` the sheaf associated to a dualizing complex `ω` over
`A = Γ(X, U)`. Then `R𝓗om(𝒪_Y, K)|_{i⁻¹U}` is the sheaf associated to `R Hom_A(B, ω)`,
`B = Γ(Y, i⁻¹U)`, which is a dualizing complex over `B`. -/
theorem isDualizingModelOn_derivedSheafHomExactSupport (K : DerivedCategory X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(X, U)) _ _ (HasDerivedCategory.standard _))
    (hω : IsDualizingModelOn K hU ω) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
    IsDualizingModelOn ((derivedSheafHomExactSupport i).obj K) (hU.preimage i)
      ((Dualizing.derivedHom.{u, u, u} (i.app U).hom).obj ω) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing Γ(Y, i ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨i ⁻¹ᵁ U, hU.preimage i⟩
  have : IsClosedImmersion (Spec.map (i.app U)) :=
    IsClosedImmersion.spec_of_surjective _ (i.app_surjective U hU)
  obtain ⟨hωd, ⟨e⟩⟩ := hω
  refine ⟨Dualizing.isDualizingComplex_derivedHom_of_finite.{u, u} (i.app U).hom
    (RingHom.Finite.of_surjective _ (i.app_surjective U hU)) ω hωd, ⟨?_⟩⟩
  let eK : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω :=
    ((Stacks.Injectives.mapDerivedCategoryTargetModelIso U.toScheme.Modules
        (Scheme.Modules.restrictFunctor U.ι)).app K).symm ≪≫
      (Stacks.Injectives.grothendieckModelEquiv.{u} U.toScheme.Modules).functor.mapIso e ≪≫
      (Stacks.Injectives.mapDerivedCategoryGrothendieckModelsIso (ModuleCat.{u} Γ(X, U))
        U.toScheme.Modules
        (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app ω
  let eCancel : (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.obj
      ((tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) ≅
      (tilde.functor Γ(X, U)).mapDerivedCategory.obj ω :=
    (Functor.mapDerivedCategoryCompIso (Iso.refl ((tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.inv)) ≪≫
      Functor.mapDerivedCategoryCongr (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ hU.restrictIsoSpecCompIso ≪≫ Functor.rightUnitor _)).app ω
  let eUnit : (Scheme.Modules.restrictFunctor (hU.preimage i).isoSpec.inv).mapDerivedCategory ⋙
      (Scheme.Modules.restrictFunctor (hU.preimage i).isoSpec.hom).mapDerivedCategory ≅
      𝟭 (DerivedCategory (i ⁻¹ᵁ U).toScheme.Modules) :=
    Functor.mapDerivedCategoryCompIso (hU.preimage i).restrictIsoSpecInvCompIso ≪≫
      Functor.mapDerivedCategoryId _
  let E := ((Stacks.Injectives.mapDerivedCategoryTargetModelIso (i ⁻¹ᵁ U).toScheme.Modules
        (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U).ι)).app _) ≪≫
      (nonempty_restrict_derivedSheafHomExactSupport_iso i U K).some ≪≫
      (eUnit.app _).symm ≪≫
      (Scheme.Modules.restrictFunctor (hU.preimage i).isoSpec.hom).mapDerivedCategory.mapIso
        ((derivedSheafHomExactSupportRestrictIsoOfIso (i ∣_ U) (Spec.map (i.app U))
            (hU.preimage i).isoSpec.symm hU.isoSpec.symm
            (isoSpec_inv_morphismRestrict i hU)).app _ ≪≫
          (derivedSheafHomExactSupport (Spec.map (i.app U))).mapIso
            ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.mapIso eK ≪≫
              eCancel) ≪≫
          affineDerivedSheafHomExactSupportTildeIso _ _ (i.app U) ω
            (Dualizing.isBoundedBelow_of_bounded.{u, u} ω hωd.bounded)) ≪≫
      (Functor.mapDerivedCategoryCompIso (Iso.refl _)).app _ ≪≫
      ((Stacks.Injectives.mapDerivedCategoryGrothendieckModelsIso (ModuleCat.{u} Γ(Y, i ⁻¹ᵁ U))
        (i ⁻¹ᵁ U).toScheme.Modules (tilde.functor Γ(Y, i ⁻¹ᵁ U) ⋙
          Scheme.Modules.restrictFunctor (hU.preimage i).isoSpec.hom)).app _).symm
  exact (Stacks.Injectives.grothendieckModelEquiv.{u}
    (i ⁻¹ᵁ U).toScheme.Modules).fullyFaithfulFunctor.preimageIso E

/-- **`R𝓗om(𝒪_Y, -)` preserves carrying a dualizing model over an affine open.** For a closed
immersion `i : Y ⟶ X` into a locally Noetherian scheme and an affine open `U ⊆ X` over which
`K ∈ D(𝒪_X)` carries a dualizing model, `R𝓗om(𝒪_Y, K)` carries one over `i⁻¹U`: if `ω` models
`K` on `U`, then `R Hom_{Γ(X, U)}(Γ(Y, i⁻¹U), ω)` models `R𝓗om(𝒪_Y, K)` on `i⁻¹U`. -/
theorem hasDualizingModelOn_derivedSheafHomExactSupport (K : DerivedCategory X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) (h : HasDualizingModelOn K U hU) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
    HasDualizingModelOn ((derivedSheafHomExactSupport i).obj K) (i ⁻¹ᵁ U) (hU.preimage i) :=
  let ⟨ω, hω⟩ := h
  ⟨_, isDualizingModelOn_derivedSheafHomExactSupport i K hU ω hω⟩

/-- **`R𝓗om(𝒪_Y, -)` along a closed immersion carries dualizing complexes to dualizing
complexes.** For a closed immersion `i : Y ⟶ X` into a locally Noetherian scheme and a dualizing
complex `K` on `X` ([Stacks, Tag 0A87]), `R𝓗om(𝒪_Y, K)` is a dualizing complex on `Y`. -/
theorem isDualizingComplex_derivedSheafHomExactSupport (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
    IsDualizingComplex ((derivedSheafHomExactSupport i).obj K) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
  refine isDualizingComplex_of_hasDualizingModelOn_cover (fun U : X.affineOpens => i ⁻¹ᵁ U.1)
    (fun U => U.2.preimage i) ?_
    (fun U => hasDualizingModelOn_derivedSheafHomExactSupport i K U.1 U.2 (hK U.1 U.2))
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

end Stacks.Duality

end
