module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualEvaluation

/-!
# A `DualSituation` on the blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. `BitUniformityIII/BlowupDualEvaluation.lean` built the evaluation dictionary `ev` of
[Stacks, Remark 0GAB] on the blowup and its field `ev_secM`, and reduced the remaining field
`ev_Htr` to one compatibility: that the canonical map `I^r/I^{r+n} ⟶ H⁰(X, 𝒪_{Yₙ}(r))`
intertwines the algebraic twisting-down map `powQuotLe` with the geometric one. This file proves
that compatibility and assembles the `DualSituation`.

The proof has the three steps the earlier file listed:

* the twisting-down map `𝒪_{Yₙ}(r) ⟶ 𝒪_{Yₙ}(r')`, `thickeningTwistDown`, which is
  `Stacks.Blowup.twistDownMap` whiskered into `𝒪_{Yₙ}`, and its compatibility with the canonical
  maps `𝒪_X(r) ⟶ 𝒪_{Yₙ}(r)` (`thickeningTwistProj_comp_thickeningTwistDown`, monoidal coherence);
* the naturality of `twistedPullbackQuotientIsoThickeningTwist` against it
  (`twistDownFactorMap_app_comp_quotientIso`), checked on local pure tensors;
* `Γ(twistDownMap)(ambientSections r x) = ambientSections r' x`
  (`blowupΓMap_twistDownMap_ambientSections`), the one-step case iterated.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.thickeningTwistDown`: `𝒪_{Yₙ}(r) ⟶ 𝒪_{Yₙ}(r')`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualSituationOf`: **the `DualSituation` on the
  blowup**, at any `q₀` with the defining property of `q(S)`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.cdivInv_blowupHtr_cdiv`: the compatibility that `ev_Htr`
  needed.
* `Stacks.LocalCohomology.UniformityIII.nonempty_dualSituation`: `DualSituation` is inhabited for
  every Noetherian ring, every ideal and every `c ≤ n`.

## References

* [Stacks Project, Remark 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The twisting-down map `𝒪_X(r) ⟶ 𝒪_X(r')` on the canonical sections**: the section of
`𝒪_X(r)` attached to `x ∈ Iʳ` is carried to the section of `𝒪_X(r')` attached to the same `x`,
viewed in `I^{r'} ⊇ Iʳ`. This is the one-step case
`app_top_ambientTwistMap_ambientSections` iterated along `Stacks.Blowup.twistDownMap_comp`. -/
theorem blowupΓMap_twistDownMap_ambientSections {r' r : ℕ} (h : r' ≤ r)
    (hz : (r' : ℤ) ≤ (r : ℤ)) (x : (I ^ r : Ideal A)) :
    blowupΓMap I (Stacks.Blowup.twistDownMap I (r : ℤ) (r' : ℤ) hz) (ambientSections I r x) =
      ambientSections I r' ⟨(x : A), Ideal.pow_le_pow_right h x.2⟩ := by
  induction r, h using Nat.le_induction with
  | base =>
    rw [Stacks.Blowup.twistDownMap_self]
    rfl
  | succ r hr ih =>
    have hz' : (r' : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    have hstep : ((r : ℤ)) ≤ ((r + 1 : ℕ) : ℤ) := by omega
    have h1 : Stacks.Blowup.twistDownMap I ((r + 1 : ℕ) : ℤ) (r : ℤ) hstep = ambientTwistMap I r :=
      Stacks.Blowup.twistDownMap_succ I (r : ℤ) hstep
    rw [← Stacks.Blowup.twistDownMap_comp I ((r + 1 : ℕ) : ℤ) (r : ℤ) (r' : ℤ) hz' hstep hz, h1]
    exact (congrArg (blowupΓMap I (Stacks.Blowup.twistDownMap I (r : ℤ) (r' : ℤ) hz'))
      (blowupΓMap_ambientTwistMap_ambientSections I r x)).trans (ih hz' _)

section Comm

open Stacks.SheafOfModules.TensorStalkRingedSpace in
/-- The symmetry of the sheafified tensor product on a local pure tensor. -/
theorem tensorSheafCommIso_hom_tmul (Y : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing Y)) (U : (TopologicalSpace.Opens Y.carrier)ᵒᵖ)
    (a : F.val.obj U) (b : G.val.obj U) :
    (((RingedSpaceThickening.tensorSheafCommIso Y F G).hom.val.app U).hom
      (toTensorSheafSection Y F G U (a ⊗ₜ b))) = toTensorSheafSection Y G F U (b ⊗ₜ a) :=
  congrArg (fun φ => (φ.app U).hom (a ⊗ₜ b))
    ((PresheafOfModules.sheafificationAdjunction (R := structureSheafRing Y)
      (𝟙 (structureSheafRing Y).obj)).unit.naturality
        (RingedSpaceThickening.presheafTensorCommHom F.val G.val)).symm

end Comm

section QuotientIso

/-- **The twisting-down map `𝒪_{Yₙ}(r) ⟶ 𝒪_{Yₙ}(r')`**: `Stacks.Blowup.twistDownMap` whiskered
into `𝒪_{Yₙ}`. -/
def thickeningTwistDown (n : ℕ) {r' r : ℕ} (hz : (r' : ℤ) ≤ (r : ℤ)) :
    thickeningTwist I n r ⟶ thickeningTwist I n r' :=
  thickeningSheaf I n ◁ (Stacks.Blowup.twistDownMap I (r : ℤ) (r' : ℤ) hz :
    blowupTwist I r ⟶ blowupTwist I r')

/-- The canonical maps `𝒪_X(r) ⟶ 𝒪_{Yₙ}(r)` commute with twisting down. -/
theorem thickeningTwistProj_comp_thickeningTwistDown (n : ℕ) {r' r : ℕ}
    (hz : (r' : ℤ) ≤ (r : ℤ)) :
    thickeningTwistProj I n r ≫ thickeningTwistDown I n hz =
      (Stacks.Blowup.twistDownMap I (r : ℤ) (r' : ℤ) hz : blowupTwist I r ⟶ blowupTwist I r') ≫
        thickeningTwistProj I n r' := by
  let f : blowupTwist I r ⟶ blowupTwist I r' := Stacks.Blowup.twistDownMap I (r : ℤ) (r' : ℤ) hz
  let p := thickeningProj I n
  change ((λ_ (blowupTwist I r)).inv ≫ (p ▷ blowupTwist I r)) ≫ (thickeningSheaf I n ◁ f) =
    f ≫ ((λ_ (blowupTwist I r')).inv ≫ (p ▷ blowupTwist I r'))
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ (whisker_exchange p f).symm).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (eq_whisker (leftUnitor_inv_naturality f).symm _).trans (Category.assoc _ _ _)

/-- **The identification `𝒪_X(r) ⊗ p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}(r)` commutes with twisting down.** -/
theorem twistDownFactorMap_app_comp_quotientIso (n : ℕ) {r' r : ℕ}
    (hz : (r' : ℤ) ≤ (r : ℤ)) :
    (Stacks.Blowup.twistDownFactorMap I (r : ℤ) (r' : ℤ) hz).app (ModuleCat.of A (A ⧸ I ^ n)) ≫
        (twistedPullbackQuotientIsoThickeningTwist I n r').hom =
      (twistedPullbackQuotientIsoThickeningTwist I n r).hom ≫ thickeningTwistDown I n hz := by
  let f : blowupTwist I r ⟶ blowupTwist I r' := Stacks.Blowup.twistDownMap I (r : ℤ) (r' : ℤ) hz
  let P := (AlgebraicGeometry.TopDegreeBaseChange.pullbackFactor A (Stacks.Blowup.blowUpOver I)).obj
    ((AlgebraicGeometry.TopDegreeBaseChange.tildeFactor A).obj (ModuleCat.of A (A ⧸ I ^ n)))
  have hL : (Stacks.Blowup.twistDownFactorMap I (r : ℤ) (r' : ℤ) hz).app
      (ModuleCat.of A (A ⧸ I ^ n)) = f ▷ P := by
    refine (Stacks.AlgebraicGeometry.ProjTwistLeftSlot.tensorFactorMap_app_eq_tensorSheafMap A
      (Stacks.Blowup.blowUpOver I) f P).trans ?_
    refine (Stacks.SheafOfModules.OnSpace.monoidal_tensorHom
      (blowupScheme I).toRingedSpace f (𝟙 P)).symm.trans ?_
    change 𝟙 _ ≫ (f ⊗ₘ 𝟙 P) ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
    exact tensorHom_id f P
  let X := (blowupScheme I).toRingedSpace
  let ψ := (pullbackTildeQuotientIsoThickeningSheaf I n).hom
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext X (fun U a b => ?_)
  rw [hL]
  have e1 := Stacks.SheafOfModules.OnSpace.whiskerRight_tmul X f P U a b
  have e2 := tensorSheafCommIso_hom_tmul X (blowupTwist I r') P U ((f.val.app U).hom a) b
  have e3 := Stacks.SheafOfModules.OnSpace.whiskerRight_tmul X ψ (blowupTwist I r') U b
    ((f.val.app U).hom a)
  have e4 := tensorSheafCommIso_hom_tmul X (blowupTwist I r) P U a b
  have e5 := Stacks.SheafOfModules.OnSpace.whiskerRight_tmul X ψ (blowupTwist I r) U b a
  have e6 := Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul X (thickeningSheaf I n) f U
    ((ψ.val.app U).hom b) a
  refine (congrArg ((twistedPullbackQuotientIsoThickeningTwist I n r').hom.val.app U).hom
    e1).trans ?_
  refine ((congrArg ((ψ ▷ blowupTwist I r').val.app U).hom e2).trans e3).trans ?_
  refine Eq.trans ?_ (congrArg ((thickeningTwistDown I n hz).val.app U).hom
    ((congrArg ((ψ ▷ blowupTwist I r).val.app U).hom e4).trans e5)).symm
  exact e6.symm

/-- **The twisting-down map on `Hⁱ(X, 𝒪_X(r) ⊗ p^*((A/Iⁿ)~))`, read on `Hⁱ(X, 𝒪_{Yₙ}(r))`**, is
`Hⁱ` of `thickeningTwistDown`: `twistDownFactorMap_app_comp_quotientIso` pushed through the
derived functor. -/
theorem blowupHmodTwistedPullbackQuotientEquiv_blowupHtr (n i : ℕ) {r' r : ℕ}
    (hz : (r' : ℤ) ≤ (r : ℤ))
    (y : blowupHmodTwistedPullback I (ModuleCat.of A (A ⧸ I ^ n)) i (r : ℤ)) :
    blowupHmodTwistedPullbackQuotientEquiv I n i r'
        (blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) i (r : ℤ) (r' : ℤ) hz y) =
      blowupHmodMap I i (thickeningTwistDown I n hz)
        (blowupHmodTwistedPullbackQuotientEquiv I n i r y) := by
  let F := (blowupΓmod I).rightDerived i
  have h := (F.map_comp _ _).symm.trans
    ((congrArg F.map (twistDownFactorMap_app_comp_quotientIso I n hz)).trans (F.map_comp _ _))
  exact ConcreteCategory.congr_hom h y

variable [IsNoetherianRing A]

/-- **The canonical map `I^r/I^{r+n} ⟶ H⁰(X, 𝒪_{Yₙ}(r))` commutes with twisting down**: on the
algebraic side twisting down is `powQuotLe`, on the geometric side it is `thickeningTwistDown`. -/
theorem blowupHmodMap_thickeningTwistDown_cdiv (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n : ℕ)
    {r' r : ℕ} (hrr : r' ≤ r) (hz : (r' : ℤ) ≤ (r : ℤ)) (u : powQuot I r n) :
    blowupHmodMap I 0 (thickeningTwistDown I n hz) ((blowupSituationOf I q₀ h).cdiv n r u) =
      (blowupSituationOf I q₀ h).cdiv n r' (powQuotLe I hrr u) := by
  rcases n with _ | m
  · exact @Subsingleton.elim _ (subsingleton_blowupHmod_thickeningTwist_zero I 0 r') _ _
  induction u using Submodule.Quotient.induction_on with
  | H x =>
    have hx : powQuotLe I hrr (Submodule.Quotient.mk x : powQuot I r (m + 1)) =
        Submodule.Quotient.mk ⟨(x : A), Ideal.pow_le_pow_right hrr x.2⟩ := rfl
    have hsec : blowupΓMap I (thickeningTwistDown I (m + 1) hz)
        (thickeningSections I (m + 1) r x) =
        thickeningSections I (m + 1) r' ⟨(x : A), Ideal.pow_le_pow_right hrr x.2⟩ := by
      have hsq := congrArg (fun φ => blowupΓMap I φ (ambientSections I r x))
        (thickeningTwistProj_comp_thickeningTwistDown I (m + 1) hz)
      exact ((blowupΓMap_comp I (thickeningTwistProj I (m + 1) r)
          (thickeningTwistDown I (m + 1) hz) (ambientSections I r x)).symm.trans hsq).trans
        ((blowupΓMap_comp I _ (thickeningTwistProj I (m + 1) r') (ambientSections I r x)).trans
          (congrArg (blowupΓMap I (thickeningTwistProj I (m + 1) r'))
            (blowupΓMap_twistDownMap_ambientSections I hrr hz x)))
    rw [hx, blowupSituationOf_cdiv_mk, blowupSituationOf_cdiv_mk]
    exact (blowupΓmodToH0_naturality I (thickeningTwistDown I (m + 1) hz) _).symm.trans
      (congrArg (blowupΓmodToH0 I (thickeningTwist I (m + 1) r')) hsec)

/-- **The compatibility `ev_Htr` was waiting for**: the canonical map
`I^r/I^{r+n} ⟶ H⁰(X, 𝒪_X(r) ⊗ p^*((A/Iⁿ)~))` intertwines `powQuotLe` with `blowupHtr`. This is
exactly the hypothesis of `blowupEv_blowupHtr_of_cdiv_twistDown`. -/
theorem cdivInv_blowupHtr_cdiv (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n : ℕ) (r r' : ℕ)
    (_hr : q₀ ≤ r) (hr' : q₀ ≤ r') (hrr : r' ≤ r) (hrr' : (r' : ℤ) ≤ (r : ℤ))
    (u : powQuot I r n) :
    cdivInv I q₀ h n hr'
        ((blowupHmodTwistedPullbackQuotientEquiv I n 0 r')
          (blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (r : ℤ) (r' : ℤ) hrr'
            ((blowupHmodTwistedPullbackQuotientEquiv I n 0 r).symm
              ((blowupSituationOf I q₀ h).cdiv n r u)))) =
      powQuotLe I hrr u := by
  rw [blowupHmodTwistedPullbackQuotientEquiv_blowupHtr]
  refine Eq.trans ?_ (cdivInv_cdiv I q₀ h n hr' (powQuotLe I hrr u))
  refine congrArg (cdivInv I q₀ h n hr') ?_
  refine Eq.trans ?_ (blowupHmodMap_thickeningTwistDown_cdiv I q₀ h n hrr hrr' u)
  exact congrArg (blowupHmodMap I 0 (thickeningTwistDown I n hrr')).hom
    ((blowupHmodTwistedPullbackQuotientEquiv I n 0 r).apply_symm_apply _)

end QuotientIso

/-! ### The `DualSituation` -/

variable [IsNoetherianRing A]

/-- **A `DualSituation` on the blowup**, at any `q₀` with the defining property of `q(S)`: the
`TwistedModuleSituation` `blowupTwistedModuleSituationOf` together with the evaluation dictionary
`blowupEv` of [Stacks, Remark 0GAB]. Its three fields are `blowupEv`, `ev_Htr` from
`blowupEv_blowupHtr_of_cdiv_twistDown` and `cdivInv_blowupHtr_cdiv`, and
`blowupEv_twistedPullbackSecM`. -/
def blowupDualSituationOf (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    DualSituation A I n c where
  toTwistedModuleSituation := blowupTwistedModuleSituationOf I q₀ h n c hcn
  ev M q hq := blowupEv I q₀ h n c hcn M q hq
  ev_Htr M q q' hq hq' hle hle' x := LinearMap.ext fun z =>
    blowupEv_blowupHtr_of_cdiv_twistDown I q₀ h n c hcn
      (cdivInv_blowupHtr_cdiv I q₀ h n) M q q' hq hq' hle hle' x z
  ev_secM M q hq x lam := blowupEv_twistedPullbackSecM I q₀ h n c hcn M q hq x lam

/-- **`DualSituation` is inhabited** for every Noetherian ring, every ideal and every `c ≤ n`. -/
theorem nonempty_dualSituation (n c : ℕ) (hcn : c ≤ n) : Nonempty (DualSituation A I n c) :=
  ⟨blowupDualSituationOf I (qS I) (isBaseThreshold_qS I) n c hcn⟩

end Stacks.LocalCohomology.UniformityIII

end
