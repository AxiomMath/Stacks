module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaSurjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusFactorization07N5

/-!
# Arrow 1 of [Stacks, Tag 07N5] is an isomorphism, from its finite-level inputs

Let `T` be a Frobenius crystal situation over `A = Γ(S, 𝒪_S)` and `E` an `F`-crystal. Arrow 1 of
the proof of [Stacks, Tag 07N5] is the base change map

`f : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})`,

`...SmallSite.baseChangeArrow07QC`. The source shows that it is an isomorphism by reducing modulo
`p^N`. This file carries out that reduction, given the finite-level inputs as hypotheses.

The finite-level data: global crystalline situations `S_N` (for `X`) and `S'_N` (for `X^{(1)}`),
morphisms of divided power bases `ι : S_N ⟶ S`, `ι' : S'_N ⟶ S` and `σ_N : S'_N ⟶ S_N` with
`ι' ≫ Spec(σ) = σ_N ≫ ι`, and maps of schemes `g : X_N ⟶ X`, `g' : X'_N ⟶ X^{(1)}`,
`g_σ : X'_N ⟶ X_N` with `g' ≫ (X^{(1)} ⟶ X) = g_σ ≫ g`, each square compatible with the closed
fibres. The ring map `A ⟶ A'_N = Γ(S'_N, 𝒪)` is surjective with kernel in the Jacobson radical (for
`A'_N = A/p^N` and `A` `p`-adically complete).

The inputs:

* (P1) `RΓ(Cris(X/S), E)` and `RΓ(Cris(X^{(1)}/S), E^{(1)})` are pseudo-coherent;
* (P2) the base change maps `RΓ(CRIS(X/S), E) ⊗^L_A A_N ⟶ RΓ(CRIS(X_N/S_N), E_N)` and
  `RΓ(CRIS(X^{(1)}/S), E^{(1)}) ⊗^L_A A'_N ⟶ RΓ(CRIS(X'_N/S'_N), E^{(1)}_N)` are isomorphisms;
* (P3) the level-`N` base change map along `σ_N`,
  `RΓ(CRIS(X_N/S_N), E_N) ⊗^L_{A_N, σ_N} A'_N ⟶ RΓ(CRIS(X'_N/S'_N), E_N^{(1)})`, is an
  isomorphism.

The two ways of pasting the squares `S'_N ⟶ S^{(1)} ⟶ S` and `S'_N ⟶ S_N ⟶ S` give the same derived
comparison (`CategoryTheory.Functor.derivedSquareMap_comp`); transposing, `f ⊗^L_A A'_N` is
identified with (P3) composed with `σ_N`-base change of (P2) up to the isomorphism (P2) for
`X^{(1)}`, so `f ⊗^L_A A'_N` is an isomorphism, and the derived Nakayama lemma
(`IsPseudoCoherentIn.isIso_of_isIso_totalDerivedExtensionScalars_map_of_surjective` in the
namespace `StacksDraft.PseudoCoherence`) concludes, by (P1).

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.isIso_baseChangeArrow07QC_of_levels`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wB wA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

/-! ### Adjoint transposes -/

section Transposes

variable {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]

/-- The transpose along a composite adjunction, twisted by `ofNatIsoRight iso`, of
`(g ≫ G₁(h)) ≫ iso.hom` is `F₂` of the transpose of `g` followed by the transpose of `h`. -/
private theorem ofNatIsoRight_comp_homEquiv_symm_comp' {F₁ : 𝒞 ⥤ 𝒟} {G₁ : 𝒟 ⥤ 𝒞} {F₂ : 𝒟 ⥤ ℰ}
    {G₂ : ℰ ⥤ 𝒟} {G : ℰ ⥤ 𝒞} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (iso : G₂ ⋙ G₁ ≅ G) {X : 𝒞}
    {Y : 𝒟} {Z : ℰ} (g : X ⟶ G₁.obj Y) (h : Y ⟶ G₂.obj Z) :
    (((adj₁.comp adj₂).ofNatIsoRight iso).homEquiv X Z).symm ((g ≫ G₁.map h) ≫ iso.hom.app Z) =
      F₂.map ((adj₁.homEquiv X Y).symm g) ≫ (adj₂.homEquiv Y Z).symm h := by
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply]
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm]

/-- Two left adjoints of one functor have the same transposes, up to the comparison
isomorphism `leftAdjointUniq`. -/
private theorem leftAdjointUniq_hom_app_comp_homEquiv_symm' {L₁ L₂ : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞}
    (A : L₁ ⊣ R) (B : L₂ ⊣ R) {K : 𝒞} {Z : 𝒟} (x : K ⟶ R.obj Z) :
    (Adjunction.leftAdjointUniq A B).hom.app K ≫ (B.homEquiv K Z).symm x =
      (A.homEquiv K Z).symm x := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← Category.assoc,
    ← (Adjunction.leftAdjointUniq A B).hom.naturality x, Category.assoc,
    Adjunction.leftAdjointUniq_hom_app_counit]

/-- **Comparing transposes along two left adjoints of one functor**: if `z₂ = z₁ ≫ R(k)` with
`k` an isomorphism and the transpose of `z₂` along `B` is an isomorphism, so is the transpose of
`z₁` along `A`. -/
private theorem isIso_homEquiv_symm_of_comp' {L₁ L₂ : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (A : L₁ ⊣ R)
    (B : L₂ ⊣ R) {K : 𝒞} {Z₁ Z₂ : 𝒟} (z₁ : K ⟶ R.obj Z₁) (z₂ : K ⟶ R.obj Z₂) (k : Z₁ ⟶ Z₂)
    [IsIso k] (hz : z₂ = z₁ ≫ R.map k) (h : IsIso ((B.homEquiv K Z₂).symm z₂)) :
    IsIso ((A.homEquiv K Z₁).symm z₁) := by
  rw [hz, Adjunction.homEquiv_naturality_right_symm] at h
  have : IsIso ((B.homEquiv K Z₁).symm z₁) := IsIso.of_isIso_comp_right _ k
  rw [← leftAdjointUniq_hom_app_comp_homEquiv_symm' A B]
  infer_instance

end Transposes

/-! ### Two factorizations of one change of base -/

section CompComp

variable {S₂ S₁ S₀ S₁' : GlobalCrystallineSituation.{u}}
  {f₁ : S₂.S ⟶ S₁.S} {g₁ : S₂.X ⟶ S₁.X}
  (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁ = g₁ ≫ S₁.toClosedFiber)
  {f₂ : S₁.S ⟶ S₀.S} {g₂ : S₁.X ⟶ S₀.X}
  (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂ = g₂ ≫ S₀.toClosedFiber)
  {f₁' : S₂.S ⟶ S₁'.S} {g₁' : S₂.X ⟶ S₁'.X}
  (h₁' : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁' = g₁' ≫ S₁'.toClosedFiber)
  {f₂' : S₁'.S ⟶ S₀.S} {g₂' : S₁'.X ⟶ S₀.X}
  (h₂' : S₁'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂' = g₂' ≫ S₀.toClosedFiber)
  (hf : f₁ ≫ f₂ = f₁' ≫ f₂') (hg : g₁ ≫ g₂ = g₁' ≫ g₂')

/-- **Two factorizations of one change of divided power base agree**: if `f₁ ≫ f₂ = f₁' ≫ f₂'`
and `g₁ ≫ g₂ = g₁' ≫ g₂'`, rebasing along `(f₁, g₁)` then `(f₂, g₂)` is rebasing along
`(f₁', g₁')` then `(f₂', g₂')`. Every component is the identity of the underlying thickening. -/
def changeBaseCompCompIso :
    changeBase S₂ S₁ f₁ g₁ h₁ ⋙ changeBase S₁ S₀ f₂ g₂ h₂ ≅
      changeBase S₂ S₁' f₁' g₁' h₁' ⋙ changeBase S₁' S₀ f₂' g₂' h₂' :=
  NatIso.ofComponents
    (fun A ↦
      { hom :=
          { sourceHom := 𝟙 _
            targetHom := 𝟙 _
            immersion_naturality := by simp
            base_naturality := by simp [hf]
            toX_naturality := by simp [hg] }
        inv :=
          { sourceHom := 𝟙 _
            targetHom := 𝟙 _
            immersion_naturality := by simp
            base_naturality := by simp [hf]
            toX_naturality := by simp [hg] }
        hom_inv_id := by apply Thickening.Hom.ext <;> simp
        inv_hom_id := by apply Thickening.Hom.ext <;> simp })
    (fun k ↦ by apply Thickening.Hom.ext <;> simp)

end CompComp

namespace SmallSite

/-- The ring map of a composite of morphisms of divided power bases is the composite of the ring
maps. -/
theorem baseChangeRingHom_comp {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}} (f₁ : S₂.S ⟶ S₁.S)
    (f₂ : S₁.S ⟶ S₀.S) :
    baseChangeRingHom (S := S₂) (S' := S₀) (f₁ ≫ f₂) =
      (baseChangeRingHom (S := S₂) (S' := S₁) f₁).comp
        (baseChangeRingHom (S := S₁) (S' := S₀) f₂) := by
  ext a
  simp [baseChangeRingHom, DividedPowerScheme.Hom.comp_hom]
  rfl

/-- **The pullbacks along two factorizations of one change of base agree**: the composite of
the pullbacks along `(f₂, g₂)` and `(f₁, g₁)` is the composite of the pullbacks along `(f₂', g₂')`
and `(f₁', g₁')` when `f₁ ≫ f₂ = f₁' ≫ f₂'` and `g₁ ≫ g₂ = g₁' ≫ g₂'`. -/
def changeBaseBigModulePullbackCompCompIso {S₂ S₁ S₀ S₁' : GlobalCrystallineSituation.{u}}
    {f₁ : S₂.S ⟶ S₁.S} {g₁ : S₂.X ⟶ S₁.X}
    (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁ = g₁ ≫ S₁.toClosedFiber)
    {f₂ : S₁.S ⟶ S₀.S} {g₂ : S₁.X ⟶ S₀.X}
    (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂ = g₂ ≫ S₀.toClosedFiber)
    {f₁' : S₂.S ⟶ S₁'.S} {g₁' : S₂.X ⟶ S₁'.X}
    (h₁' : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁' = g₁' ≫ S₁'.toClosedFiber)
    {f₂' : S₁'.S ⟶ S₀.S} {g₂' : S₁'.X ⟶ S₀.X}
    (h₂' : S₁'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂' = g₂' ≫ S₀.toClosedFiber)
    (hf : f₁ ≫ f₂ = f₁' ≫ f₂') (hg : g₁ ≫ g₂ = g₁' ≫ g₂') :
    changeBaseBigModulePullback S₁ S₀ f₂ g₂ h₂ ⋙ changeBaseBigModulePullback S₂ S₁ f₁ g₁ h₁ ≅
      changeBaseBigModulePullback S₁' S₀ f₂' g₂' h₂' ⋙
        changeBaseBigModulePullback S₂ S₁' f₁' g₁' h₁' :=
  haveI : (changeBase S₂ S₁ f₁ g₁ h₁ ⋙ changeBase S₁ S₀ f₂ g₂ h₂).IsContinuous (topology S₂)
      (topology S₀) := Functor.isContinuous_comp _ _ _ (topology S₁) _
  haveI : (changeBase S₂ S₁' f₁' g₁' h₁' ⋙ changeBase S₁' S₀ f₂' g₂' h₂').IsContinuous
      (topology S₂) (topology S₀) := Functor.isContinuous_comp _ _ _ (topology S₁') _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (changeBaseCompCompIso h₁ h₂ h₁' h₂' hf hg).symm
      (ψ := (changeBaseStructureHom S₂ S₁' f₁' g₁' h₁' ≫
        ((changeBase S₂ S₁' f₁' g₁' h₁').sheafPushforwardContinuous RingCat.{u} (topology S₂)
          (topology S₁')).map (changeBaseStructureHom S₁' S₀ f₂' g₂' h₂') :
        crystallineStructureSheaf S₂ ⟶
          ((changeBase S₂ S₁' f₁' g₁' h₁' ⋙
            changeBase S₁' S₀ f₂' g₂' h₂').sheafPushforwardContinuous
              RingCat.{u} (topology S₂) (topology S₀)).obj (crystallineStructureSheaf S₀)))
      (by ext; rfl) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Reduction

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  {SN SN' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wB} (BigModuleSheaf SN)] [HasDerivedCategory.{wB} (BigModuleSheaf SN')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(SN.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(SN'.S.scheme, ⊤))]

/-- Restriction of scalars along `σ : A ⟶ A`, from the base of `X^{(1)}/S`. -/
abbrev twistSigmaRestrictScalars :
    ModuleCat.{u + 1} Γ((T.frobeniusTwistSituation).S.scheme, ⊤) ⥤
      ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤) :=
  ModuleCat.restrictScalars.{u + 1}
    (baseChangeRingHom (S := T.frobeniusTwistSituation) (S' := T.global) T.specSigma)

/-- **The pasted underived comparison** along `S'_N ⟶ S^{(1)} ⟶ S`: restricting a global section
along `(Spec(σ), X^{(1)} ⟶ X)` and then along `(ι', g')`. -/
def twistPasteTrans (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S)
    (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber) :
    bigBaseModuleGlobalSections T.global ⟶
      (changeBaseBigModulePullback T.frobeniusTwistSituation T.global T.specSigma
          T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma ⋙
        changeBaseBigModulePullback SN' T.frobeniusTwistSituation ι' g' h')
        ⋙ bigBaseModuleGlobalSections SN' ⋙
          (ModuleCat.restrictScalars.{u + 1}
              (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ⋙
            twistSigmaRestrictScalars T) :=
  changeBaseBigBaseGlobalSectionsTrans (S := T.frobeniusTwistSituation) (S' := T.global)
      T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma ≫
    Functor.whiskerLeft (changeBaseBigModulePullback T.frobeniusTwistSituation T.global
      T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma)
      (Functor.whiskerRight (changeBaseBigBaseGlobalSectionsTrans ι' g' h')
        (twistSigmaRestrictScalars T))

/-- The composite of two pullbacks along changes of divided power base is additive. -/
instance additive_changeBaseBigModulePullback_comp {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
    (f₁ : S₂.S ⟶ S₁.S) (g₁ : S₂.X ⟶ S₁.X)
    (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁ = g₁ ≫ S₁.toClosedFiber)
    (f₂ : S₁.S ⟶ S₀.S) (g₂ : S₁.X ⟶ S₀.X)
    (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂ = g₂ ≫ S₀.toClosedFiber) :
    (changeBaseBigModulePullback S₁ S₀ f₂ g₂ h₂ ⋙
      changeBaseBigModulePullback S₂ S₁ f₁ g₁ h₁).Additive where
  map_add := by intros; rfl

/-- The composite of two pullbacks along changes of divided power base preserves finite
limits. -/
instance preservesFiniteLimits_changeBaseBigModulePullback_comp
    {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
    (f₁ : S₂.S ⟶ S₁.S) (g₁ : S₂.X ⟶ S₁.X)
    (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁ = g₁ ≫ S₁.toClosedFiber)
    (f₂ : S₁.S ⟶ S₀.S) (g₂ : S₁.X ⟶ S₀.X)
    (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂ = g₂ ≫ S₀.toClosedFiber) :
    PreservesFiniteLimits (changeBaseBigModulePullback S₁ S₀ f₂ g₂ h₂ ⋙
      changeBaseBigModulePullback S₂ S₁ f₁ g₁ h₁) :=
  comp_preservesFiniteLimits _ _

/-- The composite of two pullbacks along changes of divided power base preserves finite
colimits. -/
instance preservesFiniteColimits_changeBaseBigModulePullback_comp
    {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
    (f₁ : S₂.S ⟶ S₁.S) (g₁ : S₂.X ⟶ S₁.X)
    (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁ = g₁ ≫ S₁.toClosedFiber)
    (f₂ : S₁.S ⟶ S₀.S) (g₂ : S₁.X ⟶ S₀.X)
    (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂ = g₂ ≫ S₀.toClosedFiber) :
    PreservesFiniteColimits (changeBaseBigModulePullback S₁ S₀ f₂ g₂ h₂ ⋙
      changeBaseBigModulePullback S₂ S₁ f₁ g₁ h₁) :=
  comp_preservesFiniteColimits _ _

/-- The pasted pullback along `S'_N ⟶ S^{(1)} ⟶ S` is additive. -/
instance additive_twistPastePullback (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S)
    (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber) :
    (changeBaseBigModulePullback T.frobeniusTwistSituation T.global T.specSigma
        T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma ⋙
      changeBaseBigModulePullback SN' T.frobeniusTwistSituation ι' g' h').Additive where
  map_add := by intros; rfl

/-- The pasted pullback along `S'_N ⟶ S^{(1)} ⟶ S` preserves finite limits. -/
instance preservesFiniteLimits_twistPastePullback (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S)
    (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber) :
    PreservesFiniteLimits (changeBaseBigModulePullback T.frobeniusTwistSituation T.global
        T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma ⋙
      changeBaseBigModulePullback SN' T.frobeniusTwistSituation ι' g' h') :=
  comp_preservesFiniteLimits _ _

/-- The pasted pullback along `S'_N ⟶ S^{(1)} ⟶ S` preserves finite colimits. -/
instance preservesFiniteColimits_twistPastePullback (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S)
    (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber) :
    PreservesFiniteColimits (changeBaseBigModulePullback T.frobeniusTwistSituation T.global
        T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma ⋙
      changeBaseBigModulePullback SN' T.frobeniusTwistSituation ι' g' h') :=
  comp_preservesFiniteColimits _ _

/-- **The derived comparisons along `S'_N ⟶ S^{(1)} ⟶ S` paste**: the comparison along
`(Spec(σ), X^{(1)} ⟶ X)` followed by `σ_*` of the comparison along `(ι', g')` is the derived
comparison of the pasted underived comparison `twistPasteTrans`. -/
theorem derivedChangeBaseBigGlobalSectionsMap_paste_twist
    (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S) (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber) (N : BigModuleSheaf T.global) :
    derivedChangeBaseBigGlobalSectionsMap (S := T.frobeniusTwistSituation) (S' := T.global)
        T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma N ≫
      (twistSigmaRestrictScalars T).mapDerivedCategoryPlus.map
        (derivedChangeBaseBigGlobalSectionsMap (S := SN') (S' := T.frobeniusTwistSituation) ι' g' h'
          ((sigmaBigModulePullback T).obj N)) ≫
      (Functor.mapDerivedCategoryPlusCompIsoh (Iso.refl (ModuleCat.restrictScalars.{u + 1}
          (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ⋙
            twistSigmaRestrictScalars T))).hom.app _ =
      Functor.derivedSquareMap (twistPasteTrans T ι' g' h') N := by
  rw [derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap (S := SN')]
  refine (congrArg (· ≫ _) (derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap
    (S := T.frobeniusTwistSituation) (S' := T.global) T.specSigma T.twistProjection
    T.twistToClosedFiber_comp_closedFiberMap_specSigma N)).trans ?_
  refine (Functor.derivedSquareMap_comp _ _ (twistPasteTrans T ι' g' h') (𝟙 _)
    (Iso.refl _).hom _ (Functor.mapDerivedCategoryPlusCompIsoh_compatible _) ?_ N).trans ?_
  · intro X
    exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans rfl
  · simp

/-- **The restrictions of scalars along the two factorizations of `A ⟶ A'_N` agree**:
restricting along `σ_N : A_N ⟶ A'_N` and then along `ι : A ⟶ A_N` is restricting along
`ι' : A ⟶ A'_N` and then along `σ : A ⟶ A`, since `ι' ≫ Spec(σ) = σ_N ≫ ι`. -/
def levelRestrictScalarsIso (ι : SN.S ⟶ T.global.S) (σN : SN'.S ⟶ SN.S)
    (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S) (hf : σN ≫ ι = ι' ≫ T.specSigma) :
    ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom (S := SN') (S' := SN) σN) ⋙
        ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom (S := SN) (S' := T.global) ι) ≅
      ModuleCat.restrictScalars.{u + 1}
          (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ⋙
        twistSigmaRestrictScalars T :=
  (ModuleCat.restrictScalarsComp' (baseChangeRingHom (S := SN) (S' := T.global) ι)
      (baseChangeRingHom (S := SN') (S' := SN) σN)
      (baseChangeRingHom (S := SN') (S' := T.global) (σN ≫ ι))
      (baseChangeRingHom_comp σN ι)).symm ≪≫
    ModuleCat.restrictScalarsComp'
      (baseChangeRingHom (S := T.frobeniusTwistSituation) (S' := T.global) T.specSigma)
      (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι')
      (baseChangeRingHom (S := SN') (S' := T.global) (σN ≫ ι))
      (by rw [hf]; exact baseChangeRingHom_comp (S₁ := T.frobeniusTwistSituation) ι' T.specSigma)

/-- **The pullbacks along the two factorizations of `X'_N ⟶ X` agree.** -/
def levelPullbackIso (ι : SN.S ⟶ T.global.S) (g : SN.X ⟶ T.global.X)
    (h : SN.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι = g ≫ T.global.toClosedFiber)
    (σN : SN'.S ⟶ SN.S) (gσ : SN'.X ⟶ SN.X)
    (hσ : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap σN = gσ ≫ SN.toClosedFiber)
    (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S) (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber)
    (hf : σN ≫ ι = ι' ≫ T.specSigma) (hg : gσ ≫ g = g' ≫ T.twistProjection) :
    changeBaseBigModulePullback SN T.global ι g h ⋙
        changeBaseBigModulePullback SN' SN σN gσ hσ ≅
      changeBaseBigModulePullback T.frobeniusTwistSituation T.global T.specSigma
          T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma ⋙
        changeBaseBigModulePullback SN' T.frobeniusTwistSituation ι' g' h' :=
  changeBaseBigModulePullbackCompCompIso hσ h h'
    T.twistToClosedFiber_comp_closedFiberMap_specSigma hf hg

omit [HasDerivedCategory (BigModuleSheaf T.frobeniusTwistSituation)] in
/-- **The two pastings of the level-`N` square agree**: the derived comparison along `(ι, g)`
followed by `ι_*` of the comparison along `(σ_N, g_σ)` is the comparison of the pasting along
`S'_N ⟶ S^{(1)} ⟶ S`, read through the identifications of the pullbacks and of the restrictions
of scalars along the two factorizations. -/
theorem derivedChangeBaseBigGlobalSectionsMap_paste_level (ι : SN.S ⟶ T.global.S)
    (g : SN.X ⟶ T.global.X)
    (h : SN.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι = g ≫ T.global.toClosedFiber)
    (σN : SN'.S ⟶ SN.S) (gσ : SN'.X ⟶ SN.X)
    (hσ : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap σN = gσ ≫ SN.toClosedFiber)
    (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S) (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber)
    (hf : σN ≫ ι = ι' ≫ T.specSigma) (hg : gσ ≫ g = g' ≫ T.twistProjection)
    (N : BigModuleSheaf T.global) :
    derivedChangeBaseBigGlobalSectionsMap (S := SN) (S' := T.global) ι g h N ≫
      (ModuleCat.restrictScalars.{u + 1}
          (baseChangeRingHom (S := SN) (S' := T.global) ι)).mapDerivedCategoryPlus.map
        (derivedChangeBaseBigGlobalSectionsMap (S := SN') (S' := SN) σN gσ hσ
          ((changeBaseBigModulePullback SN T.global ι g h).obj N)) ≫
      (Functor.mapDerivedCategoryPlusCompIsoh (levelRestrictScalarsIso T ι σN ι' hf)).hom.app _ =
      Functor.derivedSquareMap (twistPasteTrans T ι' g' h') N ≫
        (ModuleCat.restrictScalars.{u + 1}
            (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ⋙
          twistSigmaRestrictScalars T).mapDerivedCategoryPlus.map
          ((bigBaseModuleGlobalSections SN').rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (BigModuleSheaf SN') 0).map
              ((levelPullbackIso T ι g h σN gσ hσ ι' g' h' hf hg).inv.app N))) := by
  rw [derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap,
    derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  refine Functor.derivedSquareMap_comp _ _ (twistPasteTrans T ι' g' h')
    (levelPullbackIso T ι g h σN gσ hσ ι' g' h' hf hg).inv
    (levelRestrictScalarsIso T ι σN ι' hf).hom _
    (Functor.mapDerivedCategoryPlusCompIsoh_compatible _) ?_ N
  intro M
  ext x
  exact Subtype.ext <| funext fun A ↦ (x.2 ((changeBaseCompCompIso hσ h h'
    T.twistToClosedFiber_comp_closedFiberMap_specSigma hf hg).hom.app A.unop).op).symm

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]

/-- **Arrow 1 of the proof of [Stacks, Tag 07N5] is an isomorphism, given its finite-level
inputs.** Let `S_N`, `S'_N` be global crystalline situations with morphisms of divided power bases
`ι : S_N ⟶ S`, `ι' : S'_N ⟶ S` (the base of `X^{(1)}/S` being that of `X/S`) and
`σ_N : S'_N ⟶ S_N`, and maps `g : X_N ⟶ X`, `g' : X'_N ⟶ X^{(1)}`, `g_σ : X'_N ⟶ X_N`, each
square compatible with the closed fibres, such that `σ_N ≫ ι = ι' ≫ Spec(σ)` and
`g_σ ≫ g = g' ≫ (X^{(1)} ⟶ X)`. Suppose:

* the ring map `A ⟶ A'_N` of `ι'` is surjective with kernel in the Jacobson radical of `A`
  (`hsurj`, `hker`; for `A'_N = A/p^N` with `N ≠ 0` and `A` `p`-adically complete see
  `isIso_baseChangeArrow07QC_of_levels_of_isAdicComplete`);
* (P1) `RΓ(Cris(X/S), E)` and `RΓ(Cris(X^{(1)}/S), E^{(1)})` are pseudo-coherent (`hK`, `hL`);
* (P2) the base change maps along `ι` and `ι'`,
  `RΓ(CRIS(X/S), E) ⊗^L_A A_N ⟶ RΓ(CRIS(X_N/S_N), E_N)` and
  `RΓ(CRIS(X^{(1)}/S), E^{(1)}) ⊗^L_A A'_N ⟶ RΓ(CRIS(X'_N/S'_N), E^{(1)}_N)`, the transposes of
  `...SmallSite.derivedChangeBaseBigGlobalSectionsMap`, are isomorphisms (`hX`, `hX1`);
* (P3) the base change map along `σ_N`,
  `RΓ(CRIS(X_N/S_N), E_N) ⊗^L_{A_N} A'_N ⟶ RΓ(CRIS(X'_N/S'_N), E_N^{(1)})`, is an isomorphism
  (`hσN`).

Then `baseChangeArrow07QC T E` is an isomorphism. -/
theorem isIso_baseChangeArrow07QC_of_levels (E : Crystalline.FCrystal T)
    (ι : SN.S ⟶ T.global.S) (g : SN.X ⟶ T.global.X)
    (h : SN.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι = g ≫ T.global.toClosedFiber)
    (σN : SN'.S ⟶ SN.S) (gσ : SN'.X ⟶ SN.X)
    (hσ : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap σN = gσ ≫ SN.toClosedFiber)
    (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S) (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber)
    (hf : σN ≫ ι = ι' ≫ T.specSigma) (hg : gσ ≫ g = g' ≫ T.twistProjection)
    (hsurj : Function.Surjective
      (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι'))
    (hker : RingHom.ker (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ≤
      Ideal.jacobson ⊥)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global (toSmallFCrystal E))))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj (twistDerivedGlobalSectionsPlus T E.crystal)))
    (hX : IsIso (((derivedBaseChangeTensorAdjunction (S := SN) (S' := T.global) ι).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (S := SN) (S' := T.global) ι g h ((bigModuleULift T.global).obj E.crystal)))))
    (hX1 : IsIso (((derivedBaseChangeTensorAdjunction (S := SN')
      (S' := T.frobeniusTwistSituation) ι').homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (S := SN') (S' := T.frobeniusTwistSituation) ι' g' h'
        ((sigmaBigModulePullback T).obj ((bigModuleULift T.global).obj E.crystal))))))
    (hσN : IsIso (((derivedBaseChangeTensorAdjunction (S := SN') (S' := SN) σN).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (S := SN') (S' := SN) σN gσ hσ ((changeBaseBigModulePullback SN T.global ι g h).obj
          ((bigModuleULift T.global).obj E.crystal)))))) :
    IsIso (baseChangeArrow07QC T E) := by
  let Eb := (bigModuleULift T.global).obj E.crystal
  -- the four derived comparisons, read in the unbounded derived categories
  let a := DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
    (S := T.frobeniusTwistSituation) (S' := T.global) T.specSigma T.twistProjection
    T.twistToClosedFiber_comp_closedFiberMap_specSigma Eb)
  let b' := DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
    (S := SN') (S' := T.frobeniusTwistSituation) ι' g' h' ((sigmaBigModulePullback T).obj Eb))
  let b := DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
    (S := SN) (S' := T.global) ι g h Eb)
  let c := DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
    (S := SN') (S' := SN) σN gσ hσ ((changeBaseBigModulePullback SN T.global ι g h).obj Eb))
  let adjσ := frobeniusDerivedBaseChangeAdjunction T
  let adjq' := derivedBaseChangeTensorAdjunction (S := SN') (S' := T.frobeniusTwistSituation) ι'
  let adjq := derivedBaseChangeTensorAdjunction (S := SN) (S' := T.global) ι
  let adjσN := derivedBaseChangeTensorAdjunction (S := SN') (S' := SN) σN
  let eA := Functor.mapDerivedCategoryCompIsoh (Iso.refl (ModuleCat.restrictScalars.{u + 1}
    (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ⋙
      twistSigmaRestrictScalars T))
  let eB := Functor.mapDerivedCategoryCompIsoh (levelRestrictScalarsIso T ι σN ι' hf)
  -- the two pastings
  have hA := congrArg DerivedCategory.Plus.ι.map
    (derivedChangeBaseBigGlobalSectionsMap_paste_twist T ι' g' h' Eb)
  have hB := congrArg DerivedCategory.Plus.ι.map
    (derivedChangeBaseBigGlobalSectionsMap_paste_level T ι g h σN gσ hσ ι' g' h' hf hg Eb)
  simp only [Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusCompIsoh_hom_app] at hA hB
  let z₁ := DerivedCategory.Plus.ι.map
    (Functor.derivedSquareMap (twistPasteTrans T ι' g' h') Eb)
  let k := DerivedCategory.Plus.ι.map
    ((bigBaseModuleGlobalSections SN').rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor (BigModuleSheaf SN') 0).map
        ((levelPullbackIso T ι g h σN gσ hσ ι' g' h' hf hg).inv.app Eb)))
  have hk : IsIso k := by dsimp only [k]; infer_instance
  -- the transpose of the `S_N` pasting is an isomorphism
  have hB' : z₁ ≫ (ModuleCat.restrictScalars.{u + 1}
      (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ⋙
        twistSigmaRestrictScalars T).mapDerivedCategory.map k =
      (b ≫ (ModuleCat.restrictScalars.{u + 1}
        (baseChangeRingHom (S := SN) (S' := T.global) ι)).mapDerivedCategory.map c) ≫
        eB.hom.app _ :=
    hB.symm.trans (Category.assoc _ _ _).symm
  have hBiso : IsIso ((((adjq.comp adjσN).ofNatIsoRight eB).homEquiv _ _).symm
      (z₁ ≫ (ModuleCat.restrictScalars.{u + 1}
        (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') ⋙
          twistSigmaRestrictScalars T).mapDerivedCategory.map k)) := by
    have := hX
    have := hσN
    refine (congrArg IsIso ((congrArg _ hB').trans
      (ofNatIsoRight_comp_homEquiv_symm_comp' adjq adjσN eB b c))).mpr ?_
    infer_instance
  have hAiso := isIso_homEquiv_symm_of_comp' ((adjσ.comp adjq').ofNatIsoRight eA)
    ((adjq.comp adjσN).ofNatIsoRight eB) z₁ _ k rfl hBiso
  have hA' : z₁ = (a ≫ (twistSigmaRestrictScalars T).mapDerivedCategory.map b') ≫
      eA.hom.app _ :=
    hA.symm.trans (Category.assoc _ _ _).symm
  have hAeq : ((((adjσ.comp adjq').ofNatIsoRight eA)).homEquiv _ _).symm z₁ =
      (derivedBaseChangeTensor (S := SN') (S' := T.frobeniusTwistSituation) ι').map
        ((adjσ.homEquiv _ _).symm a) ≫ (adjq'.homEquiv _ _).symm b' :=
    (congrArg _ hA').trans (ofNatIsoRight_comp_homEquiv_symm_comp' adjσ adjq' eA a b')
  have hcomp : IsIso ((derivedBaseChangeTensor (S := SN') (S' := T.frobeniusTwistSituation) ι').map
      ((adjσ.homEquiv _ _).symm a) ≫ (adjq'.homEquiv _ _).symm b') :=
    (congrArg IsIso hAeq).mp hAiso
  have hmid : IsIso ((derivedBaseChangeTensor (S := SN') (S' := T.frobeniusTwistSituation) ι').map
      ((adjσ.homEquiv _ _).symm a)) := by
    have := hX1
    exact IsIso.of_isIso_comp_right _ ((adjq'.homEquiv _ _).symm b')
  -- arrow 1 is the transpose of `a`, up to the crossings between the small and the big site
  have hf_eq : baseChangeArrow07QC T E =
      (frobeniusDerivedBaseChangeTensor T).map (DerivedCategory.Plus.ι.map
        (derivedRestrictModuleGlobalSectionsULiftIso T.global E.crystal).inv) ≫
        (adjσ.homEquiv _ _).symm a ≫ DerivedCategory.Plus.ι.map
          (derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
            (T.sigmaModulePullback.obj E.crystal)).hom :=
    (congrArg (adjσ.homEquiv _ _).symm
      ((DerivedCategory.Plus.ι.map_comp _ _).trans
        (congrArg (_ ≫ ·) (DerivedCategory.Plus.ι.map_comp _ _)))).trans
      ((adjσ.homEquiv_naturality_left_symm _ _).trans
        (congrArg (_ ≫ ·) (adjσ.homEquiv_naturality_right_symm _ _)))
  have hDq : IsIso ((derivedBaseChangeTensor (S := SN') (S' := T.frobeniusTwistSituation) ι').map
      (baseChangeArrow07QC T E)) := by
    rw [hf_eq]
    let Dq' := derivedBaseChangeTensor (S := SN') (S' := T.frobeniusTwistSituation) ι'
    exact (congrArg IsIso ((Dq'.map_comp _ _).trans
        (congrArg (_ ≫ ·) (Dq'.map_comp _ _)))).mpr
      (IsIso.comp_isIso'
        (Iso.isIso_hom ((derivedBaseChangeTensor (S := SN') (S' := T.frobeniusTwistSituation)
          ι').mapIso ((frobeniusDerivedBaseChangeTensor T).mapIso (DerivedCategory.Plus.ι.mapIso
            (derivedRestrictModuleGlobalSectionsULiftIso T.global E.crystal).symm))))
        (IsIso.comp_isIso' hmid
          (Iso.isIso_hom ((derivedBaseChangeTensor (S := SN') (S' := T.frobeniusTwistSituation)
            ι').mapIso (DerivedCategory.Plus.ι.mapIso
              (derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
                (T.sigmaModulePullback.obj E.crystal)))))))
  have hK' := StacksDraft.PseudoCoherence.IsPseudoCoherentIn.totalDerivedExtensionScalars_obj
    (derivedBaseChangeTensorBundle (S := T.global) (S' := T.global) T.specSigma) hK
  exact hK'.isIso_of_isIso_totalDerivedExtensionScalars_map_of_surjective hsurj hker
    (derivedBaseChangeTensorBundle (S := SN') (S' := T.frobeniusTwistSituation) ι') hL
    (baseChangeArrow07QC T E) hDq

/-- `isIso_baseChangeArrow07QC_of_levels` for `A'_N = A/p^N`: the ring map `A ⟶ A'_N` of `ι'` is
surjective with kernel `(p^N)` for some `N ≠ 0`, and `A` is `p`-adically complete, so that the
kernel lies in the Jacobson radical. -/
theorem isIso_baseChangeArrow07QC_of_levels_of_isAdicComplete (E : Crystalline.FCrystal T)
    (ι : SN.S ⟶ T.global.S) (g : SN.X ⟶ T.global.X)
    (h : SN.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι = g ≫ T.global.toClosedFiber)
    (σN : SN'.S ⟶ SN.S) (gσ : SN'.X ⟶ SN.X)
    (hσ : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap σN = gσ ≫ SN.toClosedFiber)
    (ι' : SN'.S ⟶ T.frobeniusTwistSituation.S) (g' : SN'.X ⟶ T.frobeniusTwistSituation.X)
    (h' : SN'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap ι' =
      g' ≫ T.frobeniusTwistSituation.toClosedFiber)
    (hf : σN ≫ ι = ι' ≫ T.specSigma) (hg : gσ ≫ g = g' ≫ T.twistProjection)
    (hsurj : Function.Surjective
      (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι'))
    (N : ℕ) (hN : N ≠ 0)
    (hcomplete : IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
      Γ(T.global.S.scheme, ⊤))
    (hker : RingHom.ker (baseChangeRingHom (S := SN') (S' := T.frobeniusTwistSituation) ι') =
      Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤)) ^ N})
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global (toSmallFCrystal E))))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj (twistDerivedGlobalSectionsPlus T E.crystal)))
    (hX : IsIso (((derivedBaseChangeTensorAdjunction (S := SN) (S' := T.global) ι).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (S := SN) (S' := T.global) ι g h ((bigModuleULift T.global).obj E.crystal)))))
    (hX1 : IsIso (((derivedBaseChangeTensorAdjunction (S := SN')
      (S' := T.frobeniusTwistSituation) ι').homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (S := SN') (S' := T.frobeniusTwistSituation) ι' g' h'
        ((sigmaBigModulePullback T).obj ((bigModuleULift T.global).obj E.crystal))))))
    (hσN : IsIso (((derivedBaseChangeTensorAdjunction (S := SN') (S' := SN) σN).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (S := SN') (S' := SN) σN gσ hσ ((changeBaseBigModulePullback SN T.global ι g h).obj
          ((bigModuleULift T.global).obj E.crystal)))))) :
    IsIso (baseChangeArrow07QC T E) := by
  have := hcomplete
  exact isIso_baseChangeArrow07QC_of_levels T E ι g h σN gσ hσ ι' g' h' hf hg hsurj
    (hker.trans_le (StacksDraft.PseudoCoherence.span_singleton_pow_le_jacobson_bot_of_isAdicComplete
      hN)) hK hL hX hX1 hσN

end Reduction

end SmallSite

end Crystalline.GlobalCrystallineSituation
