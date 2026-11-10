module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionChartAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport

/-!
# The formal pullback is cartesian on affine charts

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale site which is cartesian on affine charts, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a morphism of inverse systems whose levelwise
kernels and cokernels are annihilated by one power `𝓘 ^ t`.  This file proves that the formal
pullback `P = G ×_{lim G / 𝓘 ⁿ⁺¹ G} lim E` of
`AlgebraicGeometry.Space.formalPullback` is **cartesian on the Noetherian affine charts**: for a
morphism `f : W ⟶ U` of Noetherian affine étale charts, with rings `R = 𝒪_F(U)` and
`R' = 𝒪_F(W)`, the base change comparison `R' ⊗_R P(U) ⟶ P(W)` is bijective.

This is the step of Stacks 08BB that replaces the étale descent of the source: the formal pullback
is a single global object, and what has to be checked is that its sections over the affine charts
glue like those of a quasi-coherent module.  The completion functor does not commute with étale
base change, so the comparison cannot be read off the completed modules; it is proved instead
from three properties of the sections of `P` over a Noetherian affine chart, established in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionChartAlgebraization`:

* the projection of `P(U)` onto the sections of `E_n` is the reduction modulo `𝓘(U) ⁿ⁺¹`;
* the kernel of the projection `P(U) ⟶ G(U)` is annihilated by `𝓘(U) ^ t`;
* `𝓘(U) ^ t` times a section of `G` lifts to `P(U)`.

Write `β : R' ⊗_R P(U) ⟶ P(W)` for the comparison.  The terms `E_n` and `G` are cartesian, so `β`
is an isomorphism modulo every power of `𝓘(W)`.  An element of the kernel of `β` therefore lies in
every `𝓘(W) ⁿ R' ⊗_R P(U)`, and by Krull's intersection theorem it is fixed by an element of
`𝓘(W)`; it also lies in the kernel of the base change of `P(U) ⟶ G(U)`, which by flatness of `R'`
over `R` is annihilated by `𝓘(W) ^ t`, so it vanishes.  For surjectivity, `𝓘(W) ^ (2 t) P(W)`
lies in the image of `β` by the two annihilation properties, and the image of `β` together with
`𝓘(W) ^ (2 t) P(W)` is everything.

## Main results

* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_formalPullback` — **the base change
  comparison of the formal pullback along a morphism of Noetherian affine charts is bijective.**
* `AlgebraicGeometry.Space.isNoetherianAffineChart_of_isAffine` — on a locally Noetherian
  algebraic space every affine étale chart is a Noetherian affine chart.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_formalPullback` — on a locally Noetherian
  algebraic space **the formal pullback is cartesian on affine charts**.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 00IP](https://stacks.math.columbia.edu/tag/00IP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (G : Modules.{u, u} B S hS F hF) (hG : IsCoherent B S hS F hF G)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G)

include hIcart hE hG in
/-- **The base change comparison of the formal pullback along a morphism of Noetherian affine
charts is bijective**, when the levelwise kernels and cokernels of `α` are annihilated by a power
of `𝓘`. -/
theorem bijective_sectionsBaseChange_formalPullback
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α)
    {U W : SmallEtale B S hS F} (hU : IsNoetherianAffineChart B S hS F U)
    (hW : IsNoetherianAffineChart B S hS F W) (f : W ⟶ U) :
    Function.Bijective (sectionsBaseChange (formalPullback B S hS F hF 𝓘 G α) f) := by
  obtain ⟨t, -, htk⟩ := id hα
  have htker := fun k => (htk k).1
  have htcok := fun k => (htk k).2
  let := chartAlgebra (hF := hF) f
  have : Module.Flat (chartRing B S hS F hF U) (chartRing B S hS F hF W) :=
    moduleFlat_chartRing_of_isAffine f hU.1 hW.1
  have : IsNoetherianRing (chartRing B S hS F hF W) := hW.2
  have : Module.Finite (chartRing B S hS F hF U)
      ((formalPullback B S hS F hF 𝓘 G α).val.obj (op U)) :=
    moduleFinite_formalPullback_sections B S hS F hF 𝓘 hIcart hE G hG α hU hα
  have hIt : chartSectionIdeal B S hS F hF 𝓘 W ^ t ≤
      Ideal.map (chartRestrict (hF := hF) f) (chartSectionIdeal B S hS F hF 𝓘 U ^ t) := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (chartIdeal_le_map_chartRestrict B S hS F hF 𝓘 f
      (hIcart U W hU.1 hW.1 f).2) t
  have hbcE : ∀ n : ℕ, Function.Bijective (sectionsBaseChange (E.obj (op n)) f) := fun n =>
    isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 hE n U W hU.1 hW.1 f
  have hbcG : Function.Bijective (sectionsBaseChange G f) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG.toIsQuasicoherentOnSite
      U W hU.1 hW.1 f
  have hlev := fun n => app_sectionsBaseChange (formalPullbackLevel B S hS F hF 𝓘 G α n) f
  have hmapβ := app_sectionsBaseChange (formalPullbackMap B S hS F hF 𝓘 G α) f
  have hlevU := fun n =>
    formalPullbackLevel_app_surjective_ker B S hS F hF 𝓘 hIcart hE G hG α hU hα n
  have hlevW := fun n =>
    formalPullbackLevel_app_surjective_ker B S hS F hF 𝓘 hIcart hE G hG α hW hα n
  have hlt : ∀ {M N : Type u} [AddCommGroup M] [Module (chartRing B S hS F hF U) M]
      [AddCommGroup N] [Module (chartRing B S hS F hF U) N]
      (φ : M →ₗ[chartRing B S hS F hF U] N) (s : chartRing B S hS F hF W)
      (z : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF W) M),
      LinearMap.lTensor (chartRing B S hS F hF W) φ (s • z) =
        s • LinearMap.lTensor (chartRing B S hS F hF W) φ z :=
    fun φ s z => (φ.baseChange (chartRing B S hS F hF W)).map_smul s z
  -- the action of `R` on the first factor of `R' ⊗_R M` through the restriction map
  have hres : ∀ (a : chartRing B S hS F hF U) {M : Type u} [AddCommGroup M]
      [Module (chartRing B S hS F hF U) M] (b : chartRing B S hS F hF W) (x : M),
      chartRestrict (hF := hF) f a • (b ⊗ₜ[chartRing B S hS F hF U] x) = b ⊗ₜ (a • x) :=
    fun a _ _ _ b x => by
      rw [show chartRestrict (hF := hF) f a =
          algebraMap (chartRing B S hS F hF U) (chartRing B S hS F hF W) a from rfl,
        algebraMap_smul, ← TensorProduct.tmul_smul]
  -- it suffices to check that `𝓘(U) ^ t` moves elements into a submodule
  have hext : ∀ {Q : Type u} [AddCommGroup Q] [Module (chartRing B S hS F hF W) Q]
      (N : Submodule (chartRing B S hS F hF W) Q),
      (∀ a ∈ chartSectionIdeal B S hS F hF 𝓘 U ^ t, ∀ w : Q, chartRestrict (hF := hF) f a • w ∈ N) →
      ∀ s ∈ chartSectionIdeal B S hS F hF 𝓘 W ^ t, ∀ w : Q, s • w ∈ N := by
    intro Q _ _ N h s hs w
    have hsJ : s ∈ N.colon Set.univ := by
      refine (Ideal.map_le_iff_le_comap.2 (fun a ha => ?_)) (hIt hs)
      rw [Ideal.mem_comap, Submodule.mem_colon]
      exact fun w _ => h a ha w
    exact Submodule.mem_colon.1 hsJ w (Set.mem_univ w)
  -- the reduction of `R' ⊗ P(U)` modulo `𝓘(W) ⁿ⁺¹`
  have hred : ∀ (n : ℕ) (z : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF W)
      ((formalPullback B S hS F hF 𝓘 G α).val.obj (op U))),
      LinearMap.lTensor (chartRing B S hS F hF W)
          ((formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op U)).hom z = 0 →
        z ∈ chartSectionIdeal B S hS F hF 𝓘 W ^ (n + 1) •
          (⊤ : Submodule (chartRing B S hS F hF W) (TensorProduct (chartRing B S hS F hF U)
            (chartRing B S hS F hF W) ((formalPullback B S hS F hF 𝓘 G α).val.obj (op U)))) := by
    intro n z hz
    have hex : Function.Exact (chartSectionIdeal B S hS F hF 𝓘 U ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF U)
          ((formalPullback B S hS F hF 𝓘 G α).val.obj (op U)))).subtype
        ((formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op U)).hom := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, (hlevU n).2]
    obtain ⟨w, rfl⟩ := ((_root_.lTensor_exact (chartRing B S hS F hF W) hex
      (hlevU n).1) z).mp hz
    clear hz
    induction w using TensorProduct.inductionOn with
    | tmul b k =>
      rw [LinearMap.lTensor_tmul]
      obtain ⟨k, hk⟩ := k
      change b ⊗ₜ k ∈ _
      refine Submodule.smul_induction_on hk (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
      · rw [TensorProduct.tmul_smul, ← algebraMap_smul (chartRing B S hS F hF W) a]
        exact Submodule.smul_mem_smul
          (chartRestrict_mem_chartIdeal_pow B S hS F hF 𝓘 f (n + 1) ha) Submodule.mem_top
      · rw [TensorProduct.tmul_add]
        exact add_mem hy hy'
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  -- the kernel of the base change of `P(U) ⟶ G(U)` is annihilated by `𝓘(W) ^ t`
  have hkert : ∀ z : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF W)
      ((formalPullback B S hS F hF 𝓘 G α).val.obj (op U)),
      LinearMap.lTensor (chartRing B S hS F hF W)
          ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op U)).hom z = 0 →
        ∀ s ∈ chartSectionIdeal B S hS F hF 𝓘 W ^ t, s • z = 0 := by
    intro z hz s hs
    have hex := LinearMap.exact_subtype_ker_map
      ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op U)).hom
    obtain ⟨w, rfl⟩ := ((Module.Flat.lTensor_exact (chartRing B S hS F hF W) hex) z).mp hz
    have hsw : s • w = 0 := by
      refine hext ⊥ (fun a ha x => ?_) s hs w
      rw [Submodule.mem_bot]
      induction x using TensorProduct.inductionOn with
      | tmul b k =>
        rw [hres]
        have hk : a • k = 0 := by
          refine Subtype.ext ?_
          exact smul_eq_zero_of_formalPullbackMap_eq_zero B S hS F hF 𝓘 G α htker U a ha k.1
            (LinearMap.mem_ker.mp k.2)
        rw [hk, TensorProduct.tmul_zero]
      | add x y hx hy => rw [smul_add, hx, hy, add_zero]
    rw [← hlt, hsw, map_zero]
  -- injectivity
  have hinj : Function.Injective (sectionsBaseChange (formalPullback B S hS F hF 𝓘 G α) f) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hψ : LinearMap.lTensor (chartRing B S hS F hF W)
        ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op U)).hom z = 0 := by
      apply hbcG.1
      rw [map_zero, ← hmapβ z, hz, map_zero]
    have hall : z ∈ ⨅ i : ℕ, chartSectionIdeal B S hS F hF 𝓘 W ^ i •
        (⊤ : Submodule (chartRing B S hS F hF W) (TensorProduct (chartRing B S hS F hF U)
          (chartRing B S hS F hF W) ((formalPullback B S hS F hF 𝓘 G α).val.obj (op U)))) := by
      rw [Submodule.mem_iInf]
      rintro (_ | n)
      · rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        exact Submodule.mem_top
      apply hred n z
      apply (hbcE n).1
      rw [map_zero, ← hlev n z, hz, map_zero]
    obtain ⟨⟨r, hr⟩, hrz⟩ :=
      (Ideal.mem_iInf_smul_pow_eq_bot_iff (chartSectionIdeal B S hS F hF 𝓘 W) z).1 hall
    have hpow : ∀ k : ℕ, r ^ k • z = z := by
      intro k
      induction k with
      | zero => rw [pow_zero, one_smul]
      | succ k ih => rw [pow_succ, mul_smul, hrz, ih]
    rw [← hpow t]
    exact hkert z hψ _ (Ideal.pow_mem_pow hr t)
  -- surjectivity modulo every power of `𝓘(W)`
  have hsurj_mod : ∀ (n : ℕ) (y : (formalPullback B S hS F hF 𝓘 G α).val.obj (op W)),
      ∃ z, y - sectionsBaseChange (formalPullback B S hS F hF 𝓘 G α) f z ∈
        chartSectionIdeal B S hS F hF 𝓘 W ^ (n + 1) •
          (⊤ : Submodule (chartRing B S hS F hF W)
            ((formalPullback B S hS F hF 𝓘 G α).val.obj (op W))) := by
    intro n y
    obtain ⟨w, hw⟩ := (hbcE n).2 ((formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op W) y)
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective (chartRing B S hS F hF W) (hlevU n).1 w
    refine ⟨z, ?_⟩
    have e1 : ((formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op W)).hom
        (sectionsBaseChange (formalPullback B S hS F hF 𝓘 G α) f z) =
        ((formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op W)).hom y :=
      (hlev n z).trans hw
    rw [← (hlevW n).2, LinearMap.mem_ker, map_sub, e1, sub_self]
  -- `𝓘(W) ^ t` times a section of `G(W)` comes from `R' ⊗ P(U)`
  have hcolon : ∀ a ∈ chartSectionIdeal B S hS F hF 𝓘 U ^ t,
      ∀ w : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF W) (G.val.obj (op U)),
      chartRestrict (hF := hF) f a • w ∈ LinearMap.range (LinearMap.baseChange
        (chartRing B S hS F hF W) ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op U)).hom) := by
    intro a ha w
    induction w using TensorProduct.inductionOn with
    | tmul b g =>
      obtain ⟨p, hp⟩ := exists_formalPullbackMap_eq_smul B S hS F hF 𝓘 hIcart hE G hG α hU
        htcok a ha g
      refine ⟨b ⊗ₜ p, ?_⟩
      rw [LinearMap.baseChange_tmul, hres]
      exact congrArg (TensorProduct.tmul _ b) hp
    | add x y hx hy => rw [smul_add]; exact add_mem hx hy
  have hcolon' := hext _ hcolon
  have hβt : ∀ s ∈ chartSectionIdeal B S hS F hF 𝓘 W ^ t,
      ∀ y : (formalPullback B S hS F hF 𝓘 G α).val.obj (op W), ∃ v,
        ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op W)).hom
          (s • y - sectionsBaseChange (formalPullback B S hS F hF 𝓘 G α) f v) = 0 := by
    intro s hs y
    obtain ⟨w, hw⟩ := hbcG.2 ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op W) y)
    obtain ⟨v, hv⟩ := hcolon' s hs w
    refine ⟨v, ?_⟩
    have h := hmapβ v
    rw [show LinearMap.lTensor (chartRing B S hS F hF W)
        ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op U)).hom v = s • w from hv,
      map_smul, hw] at h
    rw [map_sub, map_smul, ← h, sub_self]
  have hrange : chartSectionIdeal B S hS F hF 𝓘 W ^ (t + t) •
      (⊤ : Submodule (chartRing B S hS F hF W)
        ((formalPullback B S hS F hF 𝓘 G α).val.obj (op W))) ≤
      LinearMap.range (sectionsBaseChange (formalPullback B S hS F hF 𝓘 G α) f) := by
    rw [pow_add, Submodule.mul_smul]
    refine Submodule.smul_le.2 fun s' hs' x hx => ?_
    refine Submodule.smul_induction_on hx (fun s hs y _ => ?_) (fun x x' hx hx' => ?_)
    · obtain ⟨v, hv⟩ := hβt s hs y
      have h0 := smul_eq_zero_of_formalPullbackMap_eq_zero B S hS F hF 𝓘 G α htker W s' hs' _ hv
      rw [smul_sub, sub_eq_zero] at h0
      exact ⟨s' • v, by rw [map_smul, h0]⟩
    · rw [smul_add]
      exact add_mem hx hx'
  refine ⟨hinj, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hsurj_mod (t + t) y
  obtain ⟨v, hv⟩ := hrange
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ _)) hz)
  exact ⟨v + z, by rw [map_add, hv, sub_add_cancel]⟩

include hF in
/-- **On a locally Noetherian algebraic space every affine étale chart is a Noetherian affine
chart**: its scheme is locally Noetherian and affine, so its ring of global sections is
Noetherian. -/
theorem isNoetherianAffineChart_of_isAffine
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    IsNoetherianAffineChart B S hS F U := by
  refine ⟨hU, ?_⟩
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) :=
    (exists_atlas_iff_forall_etale B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T)
      hF).1 Fact.out U.1.left U.1.hom U.2
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) := hU
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

include hIcart hE hG in
/-- **On a locally Noetherian algebraic space the formal pullback is cartesian on affine
charts**, when the levelwise kernels and cokernels of `α` are annihilated by a power of `𝓘`. -/
theorem isCartesianOnAffineCharts_formalPullback
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α) :
    IsCartesianOnAffineCharts (formalPullback B S hS F hF 𝓘 G α) :=
  fun _ _ hU hW f => bijective_sectionsBaseChange_formalPullback B S hS F hF 𝓘 hIcart hE G hG α
    hα (isNoetherianAffineChart_of_isAffine B S hS F hF hU)
    (isNoetherianAffineChart_of_isAffine B S hS F hF hW) f

end AlgebraicGeometry.Space

end
