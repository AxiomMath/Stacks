module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalRetractPairs07L5
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothPresentationCohomology07LH

/-!
# [Stacks, Lemma 60.21.4, Tag 07LH] for the pair of [Stacks, Lemma 60.17.5, Tag 07L5]

[Stacks, Lemma 60.21.4, Tag 07LH] speaks of "`(M', ∇')` the pair over `D'` corresponding to `ℱ`,
see Lemma 60.17.5": the image of `ℱ` under the functor of [Stacks, Tag 07L5] towards the pairs
over `D'`, `...SmallSite.crystalRetractPairFunctor`.  This module states the lemma for exactly
that pair, `...SmallSite.crystalRetractPair_computesCohomology`, and deduces it from
`...SmallSite.smoothPresentationPair_computesCohomologyOfTower`.

Both pairs are base changes along `a : D → D'` of the pair `(M, ∇)` of [Stacks, Tag 07JG], so
they have the same module `D' ⊗̂_D M`.  They differ in the spelling of the one-forms:
[Stacks, Tag 07LH] uses the completion `Ω̂¹_{E'/A,δ}` of the one-forms of the envelope `E'` of
`P' → C`, [Stacks, Tag 07L5] the completed one-forms `Ω̂¹_{D'/A,γ̂}` of `D' = Ê'`, identified by
`...SmallSite.retractTargetFormsEquiv`.  The two connections agree after this identification
(`...SmallSite.crystalRetractConnModule_nabla`): a connection on a completed base change is
determined by its values on `1 ⊗ m` (`Crystalline.CompletedConnection.eq_of_baseChangeInclusion`),
where both are the base changes of `∇ m`, and the two comparisons of one-forms along `a` agree
because both are `a`-semilinear and carry `d x` to `d (a x)`
(`...SmallSite.crystalRetractFormsHom_psi_crystalPairFormsEquiv`).

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers Simplicial

universe u

namespace Crystalline

/-- **Semilinear additive maps out of the completed divided power differentials are determined
by their values on the differentials `d b`**, when the target is a `p`-adic completion: the
`d b` span `Ω_{B/A,δ}` over `B`, and the image of `Ω_{B/A,δ}` is dense. -/
theorem adicCompletion_differentials_addMonoidHom_ext {A : Type u} [CommRing A] {B : Type u}
    [CommRing B] [Algebra A B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ) {S₀ : Type u}
    [CommRing S₀] {Y : Type u} [AddCommGroup Y] [Module S₀ Y] {S : Type u} [CommRing S]
    [Module S (AdicCompletion (pAdicIdeal (A := S₀) p) Y)] (τ : B →+* S)
    {F G : AdicCompletion (pAdicIdeal (A := B) p) (dividedPowerDifferentials (A := A) δ) →+
      AdicCompletion (pAdicIdeal (A := S₀) p) Y}
    (hF : ∀ (c : B) z, F (c • z) = τ c • F z) (hG : ∀ (c : B) z, G (c • z) = τ c • G z)
    (h : ∀ b : B, F (AdicCompletion.of _ _ (dividedPowerDifferential (A := A) δ b)) =
      G (AdicCompletion.of _ _ (dividedPowerDifferential (A := A) δ b))) : F = G := by
  refine adicCompletion_addMonoidHom_ext_of_of p fun w ↦ ?_
  have hw : w ∈ (⊤ : Submodule B (dividedPowerDifferentials (A := A) δ)) := Submodule.mem_top
  rw [← dividedPowerDifferentials_span (A := A) δ] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h b
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hF, hG, hx]

/-- **A completed connection on a completed base change is determined by its values on the
inclusion `m ↦ 1 ⊗ m`**: the difference of two connections is `D'`-linear, the Leibniz
corrections cancelling. -/
theorem CompletedConnection.eq_of_baseChangeInclusion (p : ℕ) {D D' : Type u} [CommRing D]
    [CommRing D'] [Algebra D D'] {M : Type u} [AddCommGroup M] [Module D M] {Ω' : Type u}
    [AddCommGroup Ω'] [Module D' Ω'] {d' : D' → Ω'}
    {nabla₁ nabla₂ : CompletedConnection p D' Ω' d'
      (CompletedConnection.baseChangeCarrier p D D' M)}
    (h : ∀ m : M, nabla₁ (CompletedConnection.baseChangeInclusion p D D' M m) =
      nabla₂ (CompletedConnection.baseChangeInclusion p D D' M m)) : nabla₁ = nabla₂ := by
  let ψ : CompletedConnection.baseChangeCarrier p D D' M →+
      CompletedTensor p D' Ω' (CompletedConnection.baseChangeCarrier p D D' M) :=
    { toFun := fun x ↦ nabla₁ x - nabla₂ x
      map_zero' := by
        have h₁ : nabla₁ 0 = 0 := by simpa using nabla₁.map_add 0 0
        have h₂ : nabla₂ 0 = 0 := by simpa using nabla₂.map_add 0 0
        change nabla₁ 0 - nabla₂ 0 = 0
        rw [h₁, h₂, sub_zero]
      map_add' := fun x y ↦ by rw [nabla₁.map_add, nabla₂.map_add]; abel }
  have hN : IsHausdorff (pAdicIdeal (A := D') p)
      (CompletedTensor p D' Ω' (CompletedConnection.baseChangeCarrier p D D' M)) :=
    (AdicCompletion.isAdicComplete (CompletedConnection.pAdicIdeal_fg p D')).toIsHausdorff
  have key := CompletedConnection.baseChangeCarrier_ext p D D' M (RingHom.id D') hN (ψ := ψ)
    (ψ' := 0) (fun c x ↦ by
      change nabla₁ (c • x) - nabla₂ (c • x) = c • (nabla₁ x - nabla₂ x)
      rw [nabla₁.leibniz, nabla₂.leibniz, smul_sub]
      abel)
    (fun c x ↦ by simp) (fun m ↦ by
      change nabla₁ _ - nabla₂ _ = 0
      rw [h, sub_self])
  refine CompletedConnection.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun key x
  exact sub_eq_zero.mp hx

/-- **Base change of the values of a connection commutes with changes of the one-forms**: if
`ψ₁ ∘ e₁ = t ∘ ψ₂ ∘ e₂` on `Ω₀`, then the same holds for the induced maps on `M ⊗̂_D Ω₀`. -/
theorem CompletedConnection.baseChangeValues_completedTensorFormsMap_comm (p : ℕ) {D D' : Type u}
    [CommRing D] [CommRing D'] [Algebra D D'] {M : Type u} [AddCommGroup M] [hM : Module D M]
    {Ω₀ Ω₁ Ω₂ : Type u} [AddCommGroup Ω₀] [h₀ : Module D Ω₀] [AddCommGroup Ω₁] [Module D Ω₁]
    [AddCommGroup Ω₂] [h₂ : Module D Ω₂] {Ω₁' Ω₂' : Type u} [AddCommGroup Ω₁'] [Module D' Ω₁']
    [AddCommGroup Ω₂'] [Module D' Ω₂'] (e₁ : Ω₀ →ₗ[D] Ω₁) (e₂ : Ω₀ →ₗ[D] Ω₂)
    (ψ₁ : Ω₁ →ₛₗ[algebraMap D D'] Ω₁') (ψ₂ : Ω₂ →ₛₗ[algebraMap D D'] Ω₂') (t : Ω₂' →ₗ[D'] Ω₁')
    (h : ∀ ω, ψ₁ (e₁ ω) = t (ψ₂ (e₂ ω))) (x : CompletedTensor p D Ω₀ M) :
    CompletedConnection.baseChangeValues p D D' M Ω₁ Ω₁' ψ₁
        (CompletedConnection.completedTensorFormsMap e₁ x) =
      AdicCompletion.map (pAdicIdeal (A := D') p)
        (LinearMap.lTensor (CompletedConnection.baseChangeCarrier p D D' M) t)
        (CompletedConnection.baseChangeValues p D D' M Ω₂ Ω₂' ψ₂
          (CompletedConnection.completedTensorFormsMap e₂ x)) := by
  let F : CompletedTensor p D Ω₀ M →+
      CompletedTensor p D' Ω₁' (CompletedConnection.baseChangeCarrier p D D' M) :=
    (CompletedConnection.baseChangeValues p D D' M Ω₁ Ω₁' ψ₁).toAddMonoidHom.comp
      (CompletedConnection.completedTensorFormsMap (M := M) e₁).toAddMonoidHom
  let G : CompletedTensor p D Ω₀ M →+
      CompletedTensor p D' Ω₁' (CompletedConnection.baseChangeCarrier p D D' M) :=
    (AdicCompletion.map (pAdicIdeal (A := D') p)
        (LinearMap.lTensor (CompletedConnection.baseChangeCarrier p D D' M) t)).toAddMonoidHom.comp
      ((CompletedConnection.baseChangeValues p D D' M Ω₂ Ω₂' ψ₂).toAddMonoidHom.comp
        (CompletedConnection.completedTensorFormsMap (M := M) e₂).toAddMonoidHom)
  have hFG : F = G := adicCompletion_addMonoidHom_ext_of_of p fun y ↦ by
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [_root_.map_add, _root_.map_add, _root_.map_add, hy, hy']
    | tmul m ω =>
      simp only [F, G, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearMap.restrictScalars_apply, AdicCompletion.map_of, LinearMap.lTensor_tmul]
      rw [CompletedConnection.baseChangeValues_of_tmul,
        CompletedConnection.baseChangeValues_of_tmul, AdicCompletion.map_of,
        LinearMap.lTensor_tmul, h]
  exact DFunLike.congr_fun hFG x

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]
  [Fintype (wholeSpaceIndex S hp)] [DecidableEq (wholeSpaceIndex S hp)]
  (Fc : QuasiCoherentCrystal S)
  {P' : Type u} [CommRing P'] [Algebra ((affineSituation S hp).A : Type u) P']
  (f' : P' →ₐ[(affineSituation S hp).A] (affineSituation S hp).C) (hf' : Function.Surjective f')
  (a : DPMorphism (systemEnvelopeCompletion hp).dividedPowers
    (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers)
  (ha : ∀ c : ((affineSituation S hp).A : Type u),
    a (algebraMap ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp) c) =
      algebraMap ((affineSituation S hp).A : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u) c)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

/-- The divided power map `a : D → D'` of [Stacks, Tag 07L5] as an `A`-algebra map of the
completed envelopes, for the algebra structures of [Stacks, Tag 07LH]. -/
def crystalRetractAlgHom :
    AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object) (affineSituation S hp).p)
      (tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp) 0).object
      →ₐ[(affineSituation S hp).A]
    AdicCompletion (pAdicIdeal (A := (presentationEnvelope (affineSituation S hp) f').object)
        (affineSituation S hp).p) (presentationEnvelope (affineSituation S hp) f').object where
  toRingHom := a.toRingHom
  commutes' := ha

omit [IsAffine S.X] [IsAffine S.S.scheme] [Fintype (wholeSpaceIndex S hp)]
  [DecidableEq (wholeSpaceIndex S hp)] in
/-- `...SmallSite.crystalRetractAlgHom` is a divided power morphism of the completed envelopes. -/
theorem isDPMorphism_crystalRetractAlgHom :
    IsDPMorphism (completionDividedPowers (affineSituation S hp).p
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object.dividedPowers
      (tensorPowerEnvelope_prime_nilpotent (affineSituation S hp) _
        (wholeSpacePresentation_surjective S hp) 0))
    (completionDividedPowers (affineSituation S hp).p
      (presentationEnvelope (affineSituation S hp) f').object.dividedPowers
      (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf'))
    (crystalRetractAlgHom hp f' hf' a ha).toRingHom :=
  a.isDPMorphism

/-- **The pair over `D'` of [Stacks, Tag 07L5], read in the completed forms of the envelope of
`P' → C`**: the module with connection whose de Rham complex [Stacks, Tag 07LH] is about. -/
abbrev crystalRetractConnModule :
    FormsData.ConnModule (presentationFormsData (affineSituation S hp) f') :=
  smoothPresentationPair hp Fc f' hf' (crystalRetractAlgHom hp f' hf' a ha)
    (isDPMorphism_crystalRetractAlgHom hp f' hf' a ha)

variable (b : DPMorphism
    (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
    (systemEnvelopeCompletion hp).dividedPowers)
  (hb : ∀ c : ((affineSituation S hp).A : Type u),
    b (algebraMap ((affineSituation S hp).A : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u) c) =
      algebraMap ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp) c)
  (hab : ∀ x, a (b x) = x)
  (hρ : ∀ y, b (a y) - y ∈ (systemEnvelopeCompletion hp).ideal)

/-- The module of `...SmallSite.crystalRetractConnModule` is the module `D' ⊗̂_D M` of the pair
over `D'` of [Stacks, Tag 07L5]. -/
theorem crystalRetractConnModule_carrier :
    (crystalRetractConnModule hp Fc f' hf' a ha).carrier =
      ((crystalRetractPairFunctor hp _ a b ha hb hab hρ).obj Fc).carrier :=
  rfl

/-- **The two spellings of the one-forms of `D'`**: the completed one-forms `Ω̂¹_{D'/A,γ̂}` of
the completed ring `D'` itself, where the connections of the pairs over `D'` of
[Stacks, Tag 07L5] take their values, and the completion `Ω̂¹_{E'/A,δ}` of the one-forms of the
envelope `E'` of `P' → C`, where the de Rham complex of [Stacks, Tag 07LH] lives. -/
def retractTargetFormsEquiv :
    completedDividedPowerForms (affineSituation S hp).p ((affineSituation S hp).A : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers 1 ≃ₗ[
        AdicCompletion (pAdicIdeal (A := (presentationEnvelope (affineSituation S hp) f').object)
          (affineSituation S hp).p) (presentationEnvelope (affineSituation S hp) f').object]
      (presentationFormsData (affineSituation S hp) f').Om 1 :=
  (completedDividedPowerFormsAlgebraCongr (affineSituation S hp).p
      ((affineSituation S hp).A : Type u)
      (B := AdicCompletion
        (pAdicIdeal (A := (presentationEnvelope (affineSituation S hp) f').object)
          (affineSituation S hp).p) (presentationEnvelope (affineSituation S hp) f').object)
      (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers 1
      inferInstance (algebraCompletedEnvelopeOfPresentation (affineSituation S hp) f' hf')
      (Algebra.algebra_ext _ _ fun _ ↦ rfl)).symm.trans
    (completedFormsOfCompletionEquiv (affineSituation S hp).p ((affineSituation S hp).A : Type u)
      (presentationEnvelope (affineSituation S hp) f').object.dividedPowers
      (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf') 1).symm

omit [IsAffine S.X] [IsAffine S.S.scheme] [WholeSpacePresentation S hp]
  [Fintype (wholeSpaceIndex S hp)] [DecidableEq (wholeSpaceIndex S hp)] in
/-- `Crystalline.GlobalCrystallineSituation.SmallSite.retractTargetFormsEquiv` carries the
universal differential of `D'` to the universal differential of `Ω̂¹_{E'/A,δ}`. -/
theorem retractTargetFormsEquiv_differential
    (y : completedEnvelopeOfPresentation (affineSituation S hp) f' hf') :
    retractTargetFormsEquiv hp f' hf' (completedDividedPowerDifferentialOnRing
        (affineSituation S hp).p ((affineSituation S hp).A : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers y) =
      (presentationFormsData (affineSituation S hp) f').diff y := by
  have h1 := completedFormsOfCompletionEquiv_completedFormsDifferential (affineSituation S hp).p
    ((affineSituation S hp).A : Type u)
    (presentationEnvelope (affineSituation S hp) f').object.dividedPowers
    (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf') y
  have h2 := completedDividedPowerFormsAlgebraCongr_differentialOnRing (affineSituation S hp).p
    ((affineSituation S hp).A : Type u)
    (B := AdicCompletion (pAdicIdeal (A := (presentationEnvelope (affineSituation S hp) f').object)
      (affineSituation S hp).p) (presentationEnvelope (affineSituation S hp) f').object)
    (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
    inferInstance (algebraCompletedEnvelopeOfPresentation (affineSituation S hp) f' hf')
    (Algebra.algebra_ext _ _ fun _ ↦ rfl) y
  refine (congrArg (retractTargetFormsEquiv hp f' hf')
    (h2.symm.trans (congrArg (completedDividedPowerFormsAlgebraCongr _ _ _ _ _ _ _) h1.symm))).trans
    ?_
  simp only [retractTargetFormsEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The morphism of rings with forms `D → D'` of [Stacks, Tag 07LH] induced by `a`. -/
abbrev crystalRetractFormsHom :
    FormsData.Hom (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0)
      (presentationFormsData (affineSituation S hp) f') :=
  FormsData.Hom.ofCompletion (affineSituation S hp).p (affineSituation S hp).A _
    (presTowerPrime_nilpotent (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0) _
    (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf')
    (crystalRetractAlgHom hp f' hf' a ha) (isDPMorphism_crystalRetractAlgHom hp f' hf' a ha)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The two comparisons of one-forms along `a` agree**: from `Ω̂_{E/A,δ}`, the comparison of
[Stacks, Tag 07LH] after `Ω̂_{E/A,δ} ≃ Ω̂¹_{E/A,δ}` is the comparison of completed one-forms of the
completed rings of [Stacks, Tag 07L5] after `Ω̂_{E/A,δ} ≃ Ω̂¹_{D/A,γ̂}`, read back in
`Ω̂¹_{E'/A,δ}`.  Both are `a`-semilinear and carry `d x` to `d (a x)`. -/
theorem crystalRetractFormsHom_psi_crystalPairFormsEquiv (ω : pairForms hp) :
    (crystalRetractFormsHom hp f' hf' a ha).psi 1 (crystalPairFormsEquiv hp ω) =
      retractTargetFormsEquiv hp f' hf' (completedMapDifferentialForms (affineSituation S hp).p
        ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp).dividedPowers
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
        (dpMorphismAlgHom a ha) a.isDPMorphism 1
        (tensorPowerOneFormsEquiv (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) ω)) := by
  let T₀ := tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp) 0
  let F₁ : pairForms hp →+ (presentationFormsData (affineSituation S hp) f').Om 1 :=
    ((crystalRetractFormsHom hp f' hf' a ha).psi 1).toAddMonoidHom.comp
      (crystalPairFormsEquiv hp).toLinearMap.toAddMonoidHom
  let F₂ : pairForms hp →+ (presentationFormsData (affineSituation S hp) f').Om 1 :=
    (retractTargetFormsEquiv hp f' hf').toLinearMap.toAddMonoidHom.comp
      ((completedMapDifferentialForms (affineSituation S hp).p
        ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp).dividedPowers
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
        (dpMorphismAlgHom a ha) a.isDPMorphism 1).toAddMonoidHom.comp
        (tensorPowerOneFormsEquiv (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp)).toLinearMap.toAddMonoidHom)
  have hF₁ : ∀ (c : pairRing hp) (z : pairForms hp), F₁ (c • z) = a c • F₁ z := fun c z ↦
    (congrArg ((crystalRetractFormsHom hp f' hf' a ha).psi 1)
      ((crystalPairFormsEquiv hp).map_smul c z)).trans
      (LinearMap.map_smulₛₗ ((crystalRetractFormsHom hp f' hf' a ha).psi 1)
        (show (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring
          from c) _)
  have hF₂ : ∀ (c : pairRing hp) (z : pairForms hp), F₂ (c • z) = a c • F₂ z := fun c z ↦
    (congrArg (fun t ↦ retractTargetFormsEquiv hp f' hf' (completedMapDifferentialForms
        (affineSituation S hp).p ((affineSituation S hp).A : Type u)
        (systemEnvelopeCompletion hp).dividedPowers
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
        (dpMorphismAlgHom a ha) a.isDPMorphism 1 t))
      ((tensorPowerOneFormsEquiv (affineSituation S hp) (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp)).map_smul c z)).trans
    ((congrArg (retractTargetFormsEquiv hp f' hf') (LinearMap.map_smulₛₗ
      (completedMapDifferentialForms (affineSituation S hp).p ((affineSituation S hp).A : Type u)
        (systemEnvelopeCompletion hp).dividedPowers
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
        (dpMorphismAlgHom a ha) a.isDPMorphism 1)
      (show (systemEnvelopeCompletion hp : Type u) from c) _)).trans
      ((retractTargetFormsEquiv hp f' hf').map_smul _ _))
  have hd : ∀ y : pairRing hp, F₁ (pairDerivation hp y) = F₂ (pairDerivation hp y) := fun y ↦
    ((congrArg ((crystalRetractFormsHom hp f' hf' a ha).psi 1)
      (crystalPairFormsEquiv_pairDerivation hp y)).trans
      ((crystalRetractFormsHom hp f' hf' a ha).psi_diff y)).trans
    ((congrArg (fun t ↦ retractTargetFormsEquiv hp f' hf' (completedMapDifferentialForms
        (affineSituation S hp).p ((affineSituation S hp).A : Type u)
        (systemEnvelopeCompletion hp).dividedPowers
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
        (dpMorphismAlgHom a ha) a.isDPMorphism 1 t))
      (tensorPowerOneFormsEquiv_derivation (affineSituation S hp) (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) y)).trans
    ((congrArg (retractTargetFormsEquiv hp f' hf')
      (completedMapDifferentialForms_differentialOnRing _ _ _ _ _ _ y)).trans
      (retractTargetFormsEquiv_differential hp f' hf' (a y)))).symm
  have hd' : ∀ e : T₀.object, F₁ (AdicCompletion.of _ _
      (dividedPowerDifferential (A := ((affineSituation S hp).A : Type u)) T₀.object.dividedPowers
        e)) = F₂ (AdicCompletion.of _ _
      (dividedPowerDifferential (A := ((affineSituation S hp).A : Type u)) T₀.object.dividedPowers
        e)) := fun e ↦ by
    have he := tensorPowerDerivation_of (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0 e
    rw [← he]
    exact hd _
  have h : F₁ = F₂ := adicCompletion_differentials_addMonoidHom_ext
    (A := ((affineSituation S hp).A : Type u))
    T₀.object.dividedPowers (affineSituation S hp).p
    (a.toRingHom.comp (algebraMap T₀.object (pairRing hp)))
    (fun c z ↦ (congrArg F₁ (algebraMap_smul (pairRing hp) c z).symm).trans (hF₁ _ z))
    (fun c z ↦ (congrArg F₂ (algebraMap_smul (pairRing hp) c z).symm).trans (hF₂ _ z)) hd'
  exact DFunLike.congr_fun h ω

/-- **The two base changes of the values of a connection along `a` agree**, after the
identifications of the one-forms: `ψ_*` of [Stacks, Tag 07LH] after `Ω̂_{E/A,δ} ≃ Ω̂¹_{E/A,δ}`, and
`ψ_*` of [Stacks, Tag 07L5] after `Ω̂_{E/A,δ} ≃ Ω̂¹_{D/A,γ̂}`, read back in `Ω̂¹_{E'/A,δ}`. -/
theorem crystalRetractValues_comm
    (ω : CompletedTensor (affineSituation S hp).p (pairRing hp) (pairForms hp)
      (crystalPair hp Fc).carrier) :
    letI : Algebra (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring
        (presentationFormsData (affineSituation S hp) f').ring :=
      (crystalRetractFormsHom hp f' hf' a ha).toRingHom.toAlgebra
    letI : Algebra (systemEnvelopeCompletion hp : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u) :=
      a.toRingHom.toAlgebra
    CompletedConnection.baseChangeValues (affineSituation S hp).p
        (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring
        (presentationFormsData (affineSituation S hp) f').ring (crystalPairConnModule hp Fc).carrier
        ((presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).Om 1)
        ((presentationFormsData (affineSituation S hp) f').Om 1)
        ((crystalRetractFormsHom hp f' hf' a ha).psi 1)
        (CompletedConnection.completedTensorFormsMap (M := (crystalPair hp Fc).carrier)
          (crystalPairFormsEquiv hp).toLinearMap ω) =
      AdicCompletion.map (pAdicIdeal (A := (presentationFormsData (affineSituation S hp) f').ring)
          (affineSituation S hp).p)
        (LinearMap.lTensor (crystalRetractConnModule hp Fc f' hf' a ha).carrier
          (retractTargetFormsEquiv hp f' hf').toLinearMap)
        (CompletedConnection.baseChangeValues (affineSituation S hp).p
          (systemEnvelopeCompletion hp : Type u)
          (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u)
          ((pairCatToTensorPowerPairs hp).obj (crystalPair hp Fc)).carrier
          (systemEnvelopeCoordinates hp).forms
          (completedDividedPowerForms (affineSituation S hp).p ((affineSituation S hp).A : Type u)
            (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers 1)
          (completedMapDifferentialForms (affineSituation S hp).p
            ((affineSituation S hp).A : Type u) (systemEnvelopeCompletion hp).dividedPowers
            (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers
            (dpMorphismAlgHom a ha) a.isDPMorphism 1)
          (AdicCompletion.map (pAdicIdeal (A := (systemEnvelopeCompletion hp : Type u))
              (affineSituation S hp).p)
            (LinearMap.lTensor ((pairCatToTensorPowerPairs hp).obj (crystalPair hp Fc)).carrier
              (tensorPowerOneFormsEquiv (affineSituation S hp) (wholeSpacePresentation S hp)
                (wholeSpacePresentation_surjective S hp)).toLinearMap) ω)) := by
  let : Algebra (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring
      (presentationFormsData (affineSituation S hp) f').ring :=
    (crystalRetractFormsHom hp f' hf' a ha).toRingHom.toAlgebra
  exact CompletedConnection.baseChangeValues_completedTensorFormsMap_comm (affineSituation S hp).p
    (D := (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring)
    (D' := (presentationFormsData (affineSituation S hp) f').ring)
    (M := (crystalPairConnModule hp Fc).carrier) (hM := (crystalPairConnModule hp Fc).module)
    (h₀ := (inferInstance : Module (pairRing hp) (pairForms hp)))
    (h₂ := (systemEnvelopeCoordinates hp).module 1)
    _ _ _ _ _ (crystalRetractFormsHom_psi_crystalPairFormsEquiv hp f' hf' a ha) ω

/-- **The connection of `...SmallSite.crystalRetractConnModule` is the connection of the pair
over `D'` of [Stacks, Tag 07L5]**, read in `Ω̂¹_{E'/A,δ}` by
`...SmallSite.retractTargetFormsEquiv`: both are base changes along `a` of the connection of the
pair of [Stacks, Tag 07JG], and the two comparisons of one-forms along `a` agree
(`...SmallSite.crystalRetractFormsHom_psi_crystalPairFormsEquiv`). -/
theorem crystalRetractConnModule_nabla (x : (crystalRetractConnModule hp Fc f' hf' a ha).carrier) :
    (crystalRetractConnModule hp Fc f' hf' a ha).nabla x =
      AdicCompletion.map (pAdicIdeal (A := (presentationFormsData (affineSituation S hp) f').ring)
          (affineSituation S hp).p)
        (LinearMap.lTensor (crystalRetractConnModule hp Fc f' hf' a ha).carrier
          (retractTargetFormsEquiv hp f' hf').toLinearMap)
        (((crystalRetractPairFunctor hp _ a b ha hb hab hρ).obj Fc).nabla x) := by
  let nabla' : CompletedConnection (affineSituation S hp).p
      (presentationFormsData (affineSituation S hp) f').ring
      (completedDividedPowerForms (affineSituation S hp).p ((affineSituation S hp).A : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers 1)
      (completedDividedPowerDifferentialOnRing (affineSituation S hp).p
        ((affineSituation S hp).A : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf').dividedPowers)
      (crystalRetractConnModule hp Fc f' hf' a ha).carrier :=
    ((crystalRetractPairFunctor hp _ a b ha hb hab hρ).obj Fc).nabla
  let : Algebra (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) 0).ring
      (presentationFormsData (affineSituation S hp) f').ring :=
    (crystalRetractFormsHom hp f' hf' a ha).toRingHom.toAlgebra
  have key : (crystalRetractConnModule hp Fc f' hf' a ha).nabla =
      nabla'.transportForms (affineSituation S hp).p (retractTargetFormsEquiv hp f' hf')
        (retractTargetFormsEquiv_differential hp f' hf') := by
    refine CompletedConnection.eq_of_baseChangeInclusion (affineSituation S hp).p
      (M := (crystalPairConnModule hp Fc).carrier) fun m ↦ ?_
    refine (CompletedConnection.baseChange_inclusion _ _ _ _ _ _ _ _ _ _ _ _ m).trans ?_
    let : Algebra (systemEnvelopeCompletion hp : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u) :=
      a.toRingHom.toAlgebra
    refine Eq.trans ?_ (congrArg (AdicCompletion.map _ _)
      (CompletedConnection.baseChange_inclusion (affineSituation S hp).p
        (systemEnvelopeCompletion hp : Type u)
        (completedEnvelopeOfPresentation (affineSituation S hp) f' hf' : Type u)
        ((pairCatToTensorPowerPairs hp).obj (crystalPair hp Fc)).carrier _ _ _ _ _ _ _ _ m)).symm
    exact crystalRetractValues_comm hp Fc f' hf' a ha (pairConnection hp Fc m)
  exact (congrArg (fun n ↦ n x) key).trans
    (CompletedConnection.transportForms_apply _ _ _ nabla' x)

/-- **[Stacks, Lemma 60.21.4, Tag 07LH], for the pair of [Stacks, Lemma 60.17.5, Tag 07L5]**:
in the situation of [Stacks, Proposition 60.21.3, Tag 07LG] (`X` and `S` affine, `p` nilpotent on
`X`), let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules, `A → P' → C` ring maps with
`A → P'` smooth and `P' → C` surjective, `D'` the `p`-adic completion of `D_{P', γ}(J')`,
`P = A[x_i] → P' → C` the data of [Stacks, Tag 07L5] (`q : P ↠ P'`, the composite being the
presentation of the system), `a : D → D'`, `b : D' → D` a retract of [Stacks, Tag 07L5] compatible
with the augmentations, and
`(M', ∇') = (crystalRetractPairFunctor hp D' a b ha hb hab hρ).obj ℱ` the pair over `D'`
corresponding to `ℱ` (the base change along `a` of the pair of [Stacks, Tag 07JG]).  Then the
complex `M' ⊗^∧_{D'} Ω^*_{D'}` computes `RΓ(Cris(X/S), ℱ)`: the module with connection
`...SmallSite.crystalRetractConnModule` has module `M'`
(`...SmallSite.crystalRetractConnModule_carrier`) and connection `∇'` read in the completed
one-forms `Ω̂¹_{E'/A,δ}` (`...SmallSite.crystalRetractConnModule_nabla`), and the cohomology of its
de Rham complex in every degree `j` is `H^j(Cris(X/S), ℱ)`.  Here `D` is the completed envelope of
the presentation of the system (`...SmallSite.WholeSpacePresentation S hp`), as in
`...SmallSite.exists_presentation_retract_crystalPairEquivalence`. -/
@[stacks 07LH "in 07L5's reading: for A -> P' smooth and P' -> C surjective, D' the p-adically \
completed divided power envelope, the data A[x_i] ->> P' -> C of 07L5 presenting the system, \
a retract a : D -> D', b : D' -> D of 07L5 compatible with the \
augmentations, and (M', nabla') the pair over D' of 07L5 corresponding to F \
(crystalRetractPairFunctor), the complex M' ⊗^∧_{D'} Ω*_{D'} (crystalRetractConnModule: module M', \
connection nabla' read in the completed one-forms of the envelope of P') computes \
RΓ(Cris(X/S), F): its cohomology in every degree j is H^j(Cris(X/S), F)"]
theorem crystalRetractPair_computesCohomology
    [Algebra.Smooth ((affineSituation S hp).A : Type u) P']
    (q : MvPolynomial (wholeSpaceIndex S hp) (affineSituation S hp).A →ₐ[(affineSituation S hp).A]
      P') (hq : Function.Surjective q) (hgq : f'.comp q = wholeSpacePresentation S hp)
    (haug : (completedEnvelopeAugmentation (affineSituation S hp) f' hf').comp a.toRingHom =
      completedEnvelopeAugmentation (affineSituation S hp)
        (tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0)
        (tensorPowerPresentation_surjective (affineSituation S hp) _
          (wholeSpacePresentation_surjective S hp) 0)) :
    ((crystalRetractConnModule hp Fc f' hf' a ha).carrier =
        ((crystalRetractPairFunctor hp _ a b ha hb hab hρ).obj Fc).carrier) ∧
      (∀ x : (crystalRetractConnModule hp Fc f' hf' a ha).carrier,
        (crystalRetractConnModule hp Fc f' hf' a ha).nabla x =
          AdicCompletion.map (pAdicIdeal (A := (presentationFormsData (affineSituation S hp)
              f').ring) (affineSituation S hp).p)
            (LinearMap.lTensor (crystalRetractConnModule hp Fc f' hf' a ha).carrier
              (retractTargetFormsEquiv hp f' hf').toLinearMap)
            (((crystalRetractPairFunctor hp _ a b ha hb hab hρ).obj Fc).nabla x)) ∧
      ∀ j : ℕ, Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          ((crystalRetractConnModule hp Fc f' hf' a ha).complex.homology j) ≅
        (cohomologyFunctor S j).obj (abelianSheaf Fc.obj)) :=
  ⟨rfl, crystalRetractConnModule_nabla hp Fc f' hf' a ha b hb hab hρ,
    smoothPresentationPair_computesCohomologyOfTower hp Fc f' hf' _ _
      ⟨0, q.comp (MvPolynomial.rename Prod.snd),
        hq.comp (MvPolynomial.rename_surjective _ Prod.snd_surjective), by
          rw [← AlgHom.comp_assoc, hgq]
          rfl⟩ haug⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
