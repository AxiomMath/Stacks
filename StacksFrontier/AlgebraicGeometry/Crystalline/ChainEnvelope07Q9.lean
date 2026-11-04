module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamZigzag07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeAlphaPExtension07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechFunctorialRing07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerOpenData07Q9
public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# The envelope of the chain presentation of an iterated `α_p`-extension

Let `C = R_0 ⟶ R_1 ⟶ ⋯ ⟶ R_n` be a chain of `α_p`-extensions `R_{i+1} = R_i[z]/(z^p - c_i)`, and
let `P → C` be a surjective polynomial presentation with `p`-adically completed divided power
envelope `D`.  The presentation `P[z_1, …, z_n] → R_n` sending `z_i` to the `i`-th root has as
completed envelope `D'` the iterate of the construction of [Stacks, Tag 07N1]: applying the
identification of the completed envelope of one `α_p`-extension
(`Crystalline.alphaPCompletedEnvelopeEquiv`) once per stage of the chain.  This file draws the
consequence the proof of [Stacks, Tag 07QA] needs: **`D → D'` has a `D`-linear retraction**
sending `1` to `1`, the composite of the retractions of the stages, each the completion of the
coordinate of `z^0 ξ^[0] = 1` in the free `D`-module `⨁_{i < p, n ≥ 0} z^i ξ^[n] D`.

## Main definitions

* `Crystalline.completedPrimeRetraction07Q9` — the retraction
  `(B[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧ → B` of one stage, for a `p`-adically complete `B`.
* `Crystalline.variableEnvelopeMap07Q9` — the map of envelopes induced by a map of the variables
  across a morphism of affine crystalline situations.
* `Crystalline.GlobalCrystallineSituation.SmallSite.chainEnvelopeRetraction07Q9` — the retraction
  `D'(0) → D(0)` of the map `envelopeRingMap07Q9` of degree zero for the chain presentation of
  `Γ(f⁻¹(W))`.

## Main results

* `Crystalline.exists_chainRetraction07Q9` — the retraction for an arbitrary chain, an arbitrary
  presentation of its first ring and any presentation of its last ring on the old variables and
  the roots.
* `chainEnvelopeRetraction07Q9_mul_left`, `chainEnvelopeRetraction07Q9_one` — it is linear over
  `D(0)` and sends `1` to `1`.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.26.1, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
-/

@[expose] public section

noncomputable section

open DividedPowers CategoryTheory

universe u v w

namespace Crystalline

open PthRootExtension MvPolynomial

/-! ### The retraction of one stage -/

section StepRetraction

variable (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)
  [IsAdicComplete (pAdicIdeal (A := (B : Type u)) p) (B : Type u)]

open Classical in
/-- **The retraction `(B[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧ → B` of one stage**, for a `p`-adically complete
`B`: the completion of the coordinate `Crystalline.PthRootExtension.primeRetraction` of the basis
vector `z^0 ξ^[0] = 1` of the free `B`-module `⨁_{i < p, n ≥ 0} z^i ξ^[n] B`, read back in `B`
through its completeness.  (Over the zero ring it is zero.) -/
def completedPrimeRetraction07Q9 :
    AdicCompletion (pAdicIdeal (A := primeRing B p lam) p) (primeRing B p lam) →+ (B : Type u) :=
  if h : Nontrivial (B : Type u) then
    haveI := h
    haveI := nontrivial_xiAlg B
    ((AdicCompletion.ofLinearEquiv (pAdicIdeal (A := (B : Type u)) p)
        (B : Type u)).symm.toLinearMap.toAddMonoidHom).comp
      (PAdicCompletion.mapAddHom p (primeRing B p lam) (B : Type u)
        (primeRetraction B p lam hp).toAddMonoidHom)
  else 0

/-- The retraction of one stage is linear over `B`. -/
theorem completedPrimeRetraction07Q9_mul_left (b : (B : Type u))
    (y : AdicCompletion (pAdicIdeal (A := primeRing B p lam) p) (primeRing B p lam)) :
    completedPrimeRetraction07Q9 B p lam hp
        (AdicCompletion.of _ _ (algebraMap (B : Type u) (primeRing B p lam) b) * y) =
      b * completedPrimeRetraction07Q9 B p lam hp y := by
  unfold completedPrimeRetraction07Q9
  split_ifs with h
  · have := h
    have := nontrivial_xiAlg B
    set f := (primeRetraction B p lam hp).toAddMonoidHom
    have key : PAdicCompletion.mapAddHom p (primeRing B p lam) (B : Type u) f
          (AdicCompletion.of _ _ (algebraMap (B : Type u) (primeRing B p lam) b) * y) =
        b • PAdicCompletion.mapAddHom p (primeRing B p lam) (B : Type u) f y := by
      refine AdicCompletion.ext fun n => ?_
      obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective
        (pAdicIdeal (A := primeRing B p lam) p ^ n • ⊤ : Submodule _ (primeRing B p lam))
        (y.val n)
      have h1 : (AdicCompletion.of _ _ (algebraMap (B : Type u) (primeRing B p lam) b) * y).val n =
          Submodule.Quotient.mk (algebraMap (B : Type u) (primeRing B p lam) b * y') := by
        rw [AdicCompletion.val_mul, ← hy']
        rfl
      rw [PAdicCompletion.mapAddHom_val, h1, PAdicCompletion.levelMap_mk,
        AdicCompletion.val_smul_apply, PAdicCompletion.mapAddHom_val, ← hy',
        PAdicCompletion.levelMap_mk, ← Submodule.Quotient.mk_smul]
      congr 1
      show primeRetraction B p lam hp (algebraMap (B : Type u) (primeRing B p lam) b * y') =
        b • primeRetraction B p lam hp y'
      rw [← Algebra.smul_def, LinearMap.map_smul]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, key]
    exact (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := (B : Type u)) p)
      (B : Type u)).symm.map_smul b _
  · have : Subsingleton (B : Type u) := not_nontrivial_iff_subsingleton.mp h
    exact Subsingleton.elim _ _

/-- The retraction of one stage sends `1` to `1`. -/
theorem completedPrimeRetraction07Q9_one : completedPrimeRetraction07Q9 B p lam hp 1 = 1 := by
  unfold completedPrimeRetraction07Q9
  split_ifs with h
  · have := h
    have := nontrivial_xiAlg B
    have h1 : (1 : AdicCompletion (pAdicIdeal (A := primeRing B p lam) p) (primeRing B p lam)) =
        AdicCompletion.of _ _ (algebraMap (B : Type u) (primeRing B p lam) 1) := by
      rw [map_one]
      rfl
    have h2 : primeRetraction B p lam hp (algebraMap (B : Type u) (primeRing B p lam) 1) = 1 :=
      LinearMap.congr_fun (primeRetraction_comp B p lam hp) 1
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [h1, PAdicCompletion.mapAddHom_of]
    show (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := (B : Type u)) p) (B : Type u)).symm
      (AdicCompletion.of _ _ (primeRetraction B p lam hp _)) = 1
    rw [h2, AdicCompletion.ofLinearEquiv_symm_of]
  · have : Subsingleton (B : Type u) := not_nontrivial_iff_subsingleton.mp h
    exact Subsingleton.elim _ _

end StepRetraction

/-! ### The map of envelopes induced by a map of the variables -/

section VariableMap

variable {s t : AffineCrystallineSituation.{u, v}} (σ : AffineCrystallineSituation.Hom s t)
  {κ κ' : Type w} (g : MvPolynomial κ s.A →ₐ[s.A] s.C) (g' : MvPolynomial κ' t.A →ₐ[t.A] t.C)
  (j : κ → κ')

/-- The ring map `P → P'` of polynomial algebras sending the variable `x_k` to `x_{j(k)}`, over the
morphism of the bases of `σ`. -/
def variableMapRingHom07Q9 : MvPolynomial κ s.A →+* MvPolynomial κ' t.A :=
  eval₂Hom (C.comp σ.base.toRingHom) fun k => X (j k)

/-- The ring map of polynomial algebras is over the morphism of the bases. -/
theorem variableMapRingHom07Q9_C (b : s.A) :
    variableMapRingHom07Q9 σ j (C b) = C (σ.base.toRingHom b) :=
  eval₂Hom_C _ _ _

/-- The ring map of polynomial algebras on the variables. -/
theorem variableMapRingHom07Q9_X (k : κ) : variableMapRingHom07Q9 σ j (X k) = X (j k) :=
  eval₂Hom_X' _ _ _

variable {g g' j} (hj : ∀ k, g' (X (j k)) = σ.target (g (X k)))

include hj in
/-- The ring map of polynomial algebras commutes with the two presentations and `σ`. -/
theorem variableMapRingHom07Q9_comp :
    g'.toRingHom.comp (variableMapRingHom07Q9 σ j) = σ.target.comp g.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro b
    rw [RingHom.comp_apply, RingHom.comp_apply, variableMapRingHom07Q9_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [MvPolynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap, AlgHom.commutes,
      AlgHom.commutes]
    exact (RingHom.congr_fun σ.commutes b).symm
  · intro k
    simp only [RingHom.comp_apply, variableMapRingHom07Q9_X, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hj]

variable (g g') in
/-- **The divided power morphism of envelopes induced by a map of the variables** across a
morphism of affine crystalline situations: `Crystalline.polynomialEnvelopeMapOver` for
`Crystalline.variableMapRingHom07Q9`. -/
def variableEnvelopeMap07Q9 :
    DPMorphism (polynomialDividedPowerEnvelope s g).object.dividedPowers
      (polynomialDividedPowerEnvelope t g').object.dividedPowers :=
  (polynomialEnvelopeMapOver σ g g' (variableMapRingHom07Q9 σ j) (variableMapRingHom07Q9_C σ j)
    (variableMapRingHom07Q9_comp σ hj)).1

/-- The induced map of envelopes extends the map of polynomial algebras. -/
theorem variableEnvelopeMap07Q9_algebraMap (x : MvPolynomial κ s.A) :
    variableEnvelopeMap07Q9 σ g g' hj
        ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x) =
      (polynomialDividedPowerEnvelope t g').algebraMap.toRingHom (variableMapRingHom07Q9 σ j x) :=
  polynomialEnvelopeMapOver_polynomial _ _ _ _ _ _ x

/-- The ring map `D → D'` of the `q`-adic completions of the envelopes, induced by a map of the
variables. -/
abbrev completedVariableEnvelopeMap07Q9 (q : ℕ) :
    AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope s g).object) q)
        (polynomialDividedPowerEnvelope s g).object →+*
      AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope t g').object) q)
        (polynomialDividedPowerEnvelope t g').object :=
  adicCompletionRingMap (variableEnvelopeMap07Q9 σ g g' hj).toRingHom (map_pAdicIdeal_le _ _)

end VariableMap

/-! ### The `α_p`-algebra along a ring isomorphism -/

/-- The ring isomorphism `C[z]/(z^q - ψ⁻¹ c) ≃ R[z]/(z^p - c)` induced by a ring isomorphism
`ψ : C ≃ R` and `q = p`. -/
def alphaPAlgebraEquiv07Q9 {C R : Type*} [CommRing C] [CommRing R] {q p : ℕ} (hp : q = p)
    (ψ : C ≃+* R) (c : R) :
    AlgebraicGeometry.alphaPAlgebra q C (ψ.symm c) ≃+* AlgebraicGeometry.alphaPAlgebra p R c :=
  Ideal.quotientEquiv _ _ (Polynomial.mapEquiv ψ) (by
    subst hp
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp)

/-- The isomorphism of `α_p`-algebras extends `ψ`. -/
theorem alphaPAlgebraEquiv07Q9_algebraMap {C R : Type*} [CommRing C] [CommRing R] {q p : ℕ}
    (hp : q = p) (ψ : C ≃+* R) (c : R) (y : C) :
    alphaPAlgebraEquiv07Q9 hp ψ c (algebraMap C _ y) = algebraMap R _ (ψ y) := by
  show Ideal.quotientEquiv _ _ (Polynomial.mapEquiv ψ) _ (Ideal.Quotient.mk _ (Polynomial.C y)) =
    Ideal.Quotient.mk _ (Polynomial.C (ψ y))
  rw [Ideal.quotientEquiv_mk]
  simp

/-- The isomorphism of `α_p`-algebras sends `z` to `z`. -/
theorem alphaPAlgebraEquiv07Q9_root {C R : Type*} [CommRing C] [CommRing R] {q p : ℕ}
    (hp : q = p) (ψ : C ≃+* R) (c : R) :
    alphaPAlgebraEquiv07Q9 hp ψ c (Ideal.Quotient.mk _ Polynomial.X) =
      Ideal.Quotient.mk _ Polynomial.X := by
  rw [alphaPAlgebraEquiv07Q9, Ideal.quotientEquiv_mk]
  simp

/-! ### The retraction along a chain -/

/-- The variables `Option κ ⊕ Fin n` of the chain presentation after the first stage are those
`κ ⊕ Fin (n + 1)` of the whole chain: the new variable of the first stage is the first root. -/
def optionSumFinEquiv07Q9 (κ : Type w) (n : ℕ) : Option κ ⊕ Fin n ≃ κ ⊕ Fin (n + 1) where
  toFun v := Sum.elim (fun o => o.elim (Sum.inr 0) Sum.inl) (fun i => Sum.inr i.succ) v
  invFun v := Sum.elim (fun k => Sum.inl (some k)) (fun i => Fin.cases (Sum.inl none) Sum.inr i) v
  left_inv v := by
    rcases v with (_ | k) | i <;> simp
  right_inv v := by
    rcases v with k | i
    · rfl
    · cases i using Fin.cases <;> simp

section Step

variable {s t : AffineCrystallineSituation.{u, v}} (σ : AffineCrystallineSituation.Hom s t)
  (c : s.C) (T₁ : (alphaPSituation s c).C →+* t.C)
  (hT : ∀ y, T₁ (algebraMap s.C (alphaPSituation s c).C y) = σ.target y)

/-- The morphism of situations `(A, C[z]/(z^p - c)) ⟶ t` extending `σ` by a ring map
`C[z]/(z^p - c) → t.C` compatible with `σ` on `C`. -/
def alphaPStepHom07Q9 : AffineCrystallineSituation.Hom (alphaPSituation s c) t where
  base := σ.base
  target := T₁
  commutes := by
    refine RingHom.ext fun a => ?_
    change T₁ (algebraMap s.A (alphaPSituation s c).C a) = algebraMap t.A t.C (σ.base a)
    rw [IsScalarTower.algebraMap_apply s.A s.C (alphaPSituation s c).C a, hT]
    exact RingHom.congr_fun σ.commutes a

variable {κ κ' : Type w} {g : MvPolynomial κ s.A →ₐ[s.A] s.C}
  {g' : MvPolynomial κ' t.A →ₐ[t.A] t.C} {j : κ → κ'}
  (hj : ∀ k, g' (X (j k)) = σ.target (g (X k))) {j₁ : Option κ → κ'}
  (hj₁ : ∀ o, g' (X (j₁ o)) =
    (alphaPStepHom07Q9 σ c T₁ hT).target (alphaPPresentation s c g (X o)))
  (hjj : ∀ k, j₁ (some k) = j k)

/-- The `α_p`-extension condition on the old variables, in the form of
`Crystalline.alphaPEnvelopeMap`. -/
theorem alphaPStep_hsome07Q9 (k : κ) :
    alphaPPresentation s c g (X ((Equiv.refl (Option κ)) (some k))) =
      algebraMap s.C (alphaPSituation s c).C (g (X k)) :=
  alphaPPresentation_X_some s c g k

include hjj in
/-- **The map of envelopes `D → D'` factors through the envelope of the first stage.** -/
theorem variableEnvelopeMap07Q9_eq_comp_alphaPEnvelopeMap :
    variableEnvelopeMap07Q9 σ g g' hj =
      (variableEnvelopeMap07Q9 (alphaPStepHom07Q9 σ c T₁ hT) (alphaPPresentation s c g) g'
        hj₁).comp (alphaPEnvelopeMap (alphaPStep_hsome07Q9 c)) := by
  refine (polynomialDividedPowerEnvelope s g).dpMorphism_ext _ _ fun x => ?_
  show _ = variableEnvelopeMap07Q9 (alphaPStepHom07Q9 σ c T₁ hT) (alphaPPresentation s c g) g'
    hj₁ (alphaPEnvelopeMap (alphaPStep_hsome07Q9 c)
      ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x))
  rw [alphaPEnvelopeMap_algebraMap, variableEnvelopeMap07Q9_algebraMap,
    variableEnvelopeMap07Q9_algebraMap]
  refine congrArg _ ?_
  have hr : variableMapRingHom07Q9 σ j =
      (variableMapRingHom07Q9 (alphaPStepHom07Q9 σ c T₁ hT) j₁).comp
        (rename (⇑(Equiv.refl (Option κ)) ∘ some)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro b
      rw [RingHom.comp_apply, variableMapRingHom07Q9_C]
      show _ = variableMapRingHom07Q9 (alphaPStepHom07Q9 σ c T₁ hT) j₁ (rename _ (C b))
      rw [rename_C, variableMapRingHom07Q9_C]
      rfl
    · intro k
      rw [RingHom.comp_apply, variableMapRingHom07Q9_X]
      show _ = variableMapRingHom07Q9 (alphaPStepHom07Q9 σ c T₁ hT) j₁ (rename _ (X k))
      rw [rename_X, variableMapRingHom07Q9_X]
      exact congrArg X (hjj k).symm
  exact RingHom.congr_fun hr x

include hjj in
/-- The completed form of `Crystalline.variableEnvelopeMap07Q9_eq_comp_alphaPEnvelopeMap`. -/
theorem completedVariableEnvelopeMap07Q9_eq_comp (a : envelopeCompletedDPRing s g) :
    completedVariableEnvelopeMap07Q9 σ hj s.p a =
      completedVariableEnvelopeMap07Q9 (alphaPStepHom07Q9 σ c T₁ hT) hj₁ s.p
        (alphaPCompletedEnvelopeMap (alphaPStep_hsome07Q9 c) a) :=
  (congrArg (fun q : DPMorphism _ _ =>
    adicCompletionRingMap q.toRingHom (map_pAdicIdeal_le s.p q.toRingHom) a)
      (variableEnvelopeMap07Q9_eq_comp_alphaPEnvelopeMap σ c T₁ hT hj hj₁ hjj)).trans
    (RingHom.congr_fun (adicCompletionRingMap_comp s.p _ _) a)

include hjj in
/-- **The inductive step of `Crystalline.exists_chainRetraction07Q9`**: a retraction of the map
of completed envelopes out of the envelope of the first stage gives one out of `D`, composed
with the identification of the first stage (`Crystalline.alphaPCompletedEnvelopeEquiv`) and the
retraction of one stage (`Crystalline.completedPrimeRetraction07Q9`). -/
theorem exists_chainRetraction07Q9_step (hg : Function.Surjective g)
    (h : ∃ ρ₁ : AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope t g').object) s.p)
        (polynomialDividedPowerEnvelope t g').object →+
      envelopeCompletedDPRing (alphaPSituation s c) (alphaPPresentation s c g),
      (∀ a x, ρ₁ (completedVariableEnvelopeMap07Q9 (alphaPStepHom07Q9 σ c T₁ hT) hj₁ s.p a * x) =
        a * ρ₁ x) ∧ ρ₁ 1 = 1) :
    ∃ ρ : AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope t g').object) s.p)
        (polynomialDividedPowerEnvelope t g').object →+ envelopeCompletedDPRing s g,
      (∀ a x, ρ (completedVariableEnvelopeMap07Q9 σ hj s.p a * x) = a * ρ x) ∧ ρ 1 = 1 := by
  obtain ⟨ρ₁, hρ₁, hρ₁1⟩ := h
  obtain ⟨ct, hct⟩ := hg c
  obtain ⟨lam, hlam⟩ : ∃ lam : envelopeCompletedDPRing s g, lam - AdicCompletion.of _ _
      ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct) ∈
        (envelopeCompletedDPRing s g).ideal := by
    refine ⟨AdicCompletion.of _ _ ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom ct),
      ?_⟩
    rw [sub_self]
    exact zero_mem _
  have hnone : alphaPPresentation s c g (X ((Equiv.refl (Option κ)) none)) = alphaPRoot s c :=
    alphaPPresentation_X_none s c g
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : envelopeCompletedDPRing (alphaPSituation s c) (alphaPPresentation s c g)
      ≃+* alphaPCompletedPrimeDPRing s g lam, ∀ d,
      Φ (alphaPCompletedEnvelopeMap (alphaPStep_hsome07Q9 c) d) =
        AdicCompletion.of _ _ (algebraMap (envelopeCompletedDPRing s g)
          (primeRing (envelopeCompletedDPRing s g) s.p lam) d) :=
    ⟨_, alphaPCompletedEnvelopeEquiv_envelopeMap hg hnone (alphaPStep_hsome07Q9 c) hct hlam⟩
  obtain ⟨π, hπ, hπ1⟩ : ∃ π : alphaPCompletedPrimeDPRing s g lam →+ envelopeCompletedDPRing s g,
      (∀ b y, π (AdicCompletion.of _ _ (algebraMap (envelopeCompletedDPRing s g)
          (primeRing (envelopeCompletedDPRing s g) s.p lam) b) * y) = b * π y) ∧ π 1 = 1 :=
    ⟨completedPrimeRetraction07Q9 (envelopeCompletedDPRing s g) s.p lam s.p_ne_zero,
      completedPrimeRetraction07Q9_mul_left _ s.p lam s.p_ne_zero,
      completedPrimeRetraction07Q9_one _ s.p lam s.p_ne_zero⟩
  refine ⟨π.comp (Φ.toRingHom.toAddMonoidHom.comp ρ₁), fun a x => ?_, ?_⟩
  · have step1 : ρ₁ (completedVariableEnvelopeMap07Q9 σ hj s.p a * x) =
        alphaPCompletedEnvelopeMap (alphaPStep_hsome07Q9 c) a * ρ₁ x :=
      (congrArg (fun y => ρ₁ (y * x))
        (completedVariableEnvelopeMap07Q9_eq_comp σ c T₁ hT hj hj₁ hjj a)).trans (hρ₁ _ _)
    have step2 : Φ (alphaPCompletedEnvelopeMap (alphaPStep_hsome07Q9 c) a * ρ₁ x) =
        AdicCompletion.of _ _ (algebraMap (envelopeCompletedDPRing s g)
            (primeRing (envelopeCompletedDPRing s g) s.p lam) a) * Φ (ρ₁ x) :=
      (Φ.map_mul _ _).trans (congrArg (· * Φ (ρ₁ x)) (hΦ a))
    exact (congrArg (fun y => π (Φ y)) step1).trans ((congrArg π step2).trans (hπ a _))
  · exact (congrArg (fun y => π (Φ y)) hρ₁1).trans ((congrArg π Φ.map_one).trans hπ1)

end Step

section Nil

variable {s t : AffineCrystallineSituation.{u, v}} (σ : AffineCrystallineSituation.Hom s t)
  (τb : DPMorphism t.A.dividedPowers s.A.dividedPowers) (h₁ : ∀ a, τb (σ.base a) = a)
  (h₂ : ∀ a, σ.base (τb a) = a) {R : Type v} [CommRing R] (ψ : s.C ≃+* R) (ε : t.C ≃+* R)
  (hε : ∀ x, ε (σ.target x) = ψ x)

/-- The inverse morphism of situations, when the bases are isomorphic and `σ` is an isomorphism
on the targets. -/
def inverseHom07Q9 : AffineCrystallineSituation.Hom t s where
  base := τb
  target := ψ.symm.toRingHom.comp ε.toRingHom
  commutes := by
    refine RingHom.ext fun a => ?_
    have h := RingHom.congr_fun σ.commutes (τb a)
    rw [RingHom.comp_apply, RingHom.comp_apply] at h
    change ψ.symm (ε (algebraMap t.A t.C a)) = algebraMap s.A s.C (τb a)
    have h' : algebraMap t.A t.C a = σ.target (algebraMap s.A s.C (τb a)) := by
      rw [h]
      exact congrArg _ (h₂ a).symm
    rw [h', hε, RingEquiv.symm_apply_apply]

variable {κ κ' : Type w} {g : MvPolynomial κ s.A →ₐ[s.A] s.C}
  {g' : MvPolynomial κ' t.A →ₐ[t.A] t.C} (e : κ ≃ κ')
  (hvar : ∀ k, g' (X (e k)) = σ.target (g (X k)))

include hvar in
/-- The variable condition for the inverse morphism. -/
theorem inverseHom07Q9_var (v : κ') :
    g (X (e.symm v)) = (inverseHom07Q9 σ τb h₂ ψ ε hε).target (g' (X v)) := by
  obtain ⟨k, rfl⟩ := e.surjective v
  show _ = ψ.symm (ε (g' (X (e k))))
  rw [Equiv.symm_apply_apply, hvar, hε, RingEquiv.symm_apply_apply]

include h₁ h₂ hε in
/-- **The base case of `Crystalline.exists_chainRetraction07Q9`**: when `σ` is an isomorphism, the
inverse map of completed envelopes is a ring retraction. -/
theorem exists_chainRetraction07Q9_nil :
    ∃ ρ : AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope t g').object) s.p)
        (polynomialDividedPowerEnvelope t g').object →+
      AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope s g).object) s.p)
        (polynomialDividedPowerEnvelope s g).object,
      (∀ a x, ρ (completedVariableEnvelopeMap07Q9 σ (j := e) hvar s.p a * x) = a * ρ x) ∧
        ρ 1 = 1 := by
  set τ := inverseHom07Q9 σ τb h₂ ψ ε hε
  have hj' := inverseHom07Q9_var σ τb h₂ ψ ε hε e hvar
  have hU : (variableEnvelopeMap07Q9 τ g' g hj').comp (variableEnvelopeMap07Q9 σ g g' hvar) =
      DPMorphism.id _ := by
    refine (polynomialDividedPowerEnvelope s g).dpMorphism_ext _ _ fun x => ?_
    show variableEnvelopeMap07Q9 τ g' g hj' (variableEnvelopeMap07Q9 σ g g' hvar
      ((polynomialDividedPowerEnvelope s g).algebraMap.toRingHom x)) = _
    rw [variableEnvelopeMap07Q9_algebraMap, variableEnvelopeMap07Q9_algebraMap]
    refine congrArg _ ?_
    have hr : (variableMapRingHom07Q9 τ e.symm).comp (variableMapRingHom07Q9 σ e) =
        RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro b
        rw [RingHom.comp_apply, variableMapRingHom07Q9_C, variableMapRingHom07Q9_C]
        exact congrArg C (h₁ b)
      · intro k
        rw [RingHom.comp_apply, variableMapRingHom07Q9_X, variableMapRingHom07Q9_X,
          Equiv.symm_apply_apply]
        rfl
    exact RingHom.congr_fun hr x
  refine ⟨(completedVariableEnvelopeMap07Q9 τ hj' s.p).toAddMonoidHom, fun a x => ?_,
    (completedVariableEnvelopeMap07Q9 τ hj' s.p).map_one⟩
  show completedVariableEnvelopeMap07Q9 τ hj' s.p
      (completedVariableEnvelopeMap07Q9 σ hvar s.p a * x) = _
  rw [map_mul]
  refine congrArg (· * _) ?_
  have hc := RingHom.congr_fun (adicCompletionRingMap_comp s.p
    (variableEnvelopeMap07Q9 σ g g' hvar).toRingHom
    (variableEnvelopeMap07Q9 τ g' g hj').toRingHom) a
  have hi := congrArg (fun q : DPMorphism _ _ =>
    adicCompletionRingMap q.toRingHom (map_pAdicIdeal_le s.p q.toRingHom) a) hU
  exact hc.symm.trans (hi.trans (RingHom.congr_fun (adicCompletionRingMap_id s.p) a))

end Nil

section Chain

open AlgebraicGeometry

/-- **The retraction along a chain of `α_p`-extensions.**  Let `ch` be a chain
`R = R_0 ⟶ R_1 ⟶ ⋯ ⟶ R_n` of `α_p`-extensions, `g : P → C` a surjective presentation of a ring
`C ≅ R` in an affine crystalline situation `s` with prime `p`, and `g' : P' → C'` a presentation
in a situation `t` over an isomorphic base, with `C' ≅ R_n`, whose variables are those of `P` and
`n` more, the old ones going to the images of their values under `C → C'` and the new ones to the
roots of the chain.  Then the map `D → D'` of the `p`-adically completed divided power envelopes
has a `D`-linear retraction sending `1` to `1`.

The proof is by induction on the chain.  For the empty chain `D → D'` is an isomorphism of
rings, and its inverse is the retraction (`Crystalline.exists_chainRetraction07Q9_nil`).  For a
chain whose first stage adjoins a `p`-th root of `c`, the envelope `D_1` of the extension of
`P → C` by one variable is the completion of `D[z]⟨ξ⟩/(ξ - (z^p - λ))`
(`Crystalline.alphaPCompletedEnvelopeEquiv`), whose retraction onto `D` is
`Crystalline.completedPrimeRetraction07Q9`; it is composed with the retraction of `D_1 → D'` for
the rest of the chain (`Crystalline.exists_chainRetraction07Q9_step`). -/
theorem exists_chainRetraction07Q9 {p : ℕ} : ∀ {R : CommRingCat.{v}} {n : ℕ}
    (ch : AlphaPChain p R n)
    (s : AffineCrystallineSituation.{u, v}) (_hp : s.p = p) (ψ : s.C ≃+* R) {κ : Type w}
    (g : MvPolynomial κ s.A →ₐ[s.A] s.C) (_hg : Function.Surjective g)
    (t : AffineCrystallineSituation.{u, v}) (σ : AffineCrystallineSituation.Hom s t)
    (τb : DPMorphism t.A.dividedPowers s.A.dividedPowers) (_h₁ : ∀ a, τb (σ.base a) = a)
    (_h₂ : ∀ a, σ.base (τb a) = a) (ε : t.C ≃+* ch.top)
    (_hε : ∀ x, ε (σ.target x) = ch.toTop.hom (ψ x)) {κ' : Type w}
    (g' : MvPolynomial κ' t.A →ₐ[t.A] t.C) (e : κ ⊕ Fin n ≃ κ')
    (hvar : ∀ k, g' (X (e (Sum.inl k))) = σ.target (g (X k)))
    (_hroot : ∀ i, g' (X (e (Sum.inr i))) = ε.symm (ch.roots i)),
    ∃ ρ : AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope t g').object) s.p)
        (polynomialDividedPowerEnvelope t g').object →+
      AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope s g).object) s.p)
        (polynomialDividedPowerEnvelope s g).object,
      (∀ a x, ρ (completedVariableEnvelopeMap07Q9 σ (j := e ∘ Sum.inl) hvar s.p a * x) =
        a * ρ x) ∧ ρ 1 = 1 := by
  intro R n ch
  induction ch with
  | nil R =>
    intro s hp ψ κ g hg t σ τb h₁ h₂ ε hε κ' g' e hvar hroot
    exact exists_chainRetraction07Q9_nil σ τb h₁ h₂ ψ ε hε ((Equiv.sumEmpty κ (Fin 0)).symm.trans e)
      hvar
  | @cons R n c rest ih =>
    intro s hp ψ κ g hg t σ τb h₁ h₂ ε hε κ' g' e hvar hroot
    let T₁ : (alphaPSituation s (ψ.symm c)).C →+* t.C :=
      ε.symm.toRingHom.comp (rest.toTop.hom.comp (alphaPAlgebraEquiv07Q9 hp ψ c).toRingHom)
    have hT : ∀ y, T₁ (algebraMap s.C (alphaPSituation s (ψ.symm c)).C y) = σ.target y := by
      intro y
      show ε.symm (rest.toTop.hom (alphaPAlgebraEquiv07Q9 hp ψ c (algebraMap s.C _ y))) = _
      rw [alphaPAlgebraEquiv07Q9_algebraMap]
      show ε.symm ((AlphaPChain.cons c rest).toTop.hom (ψ y)) = _
      rw [← hε, RingEquiv.symm_apply_apply]
    have hj₁ : ∀ o, g' (X (((optionSumFinEquiv07Q9 κ n).trans e) (Sum.inl o))) =
        (alphaPStepHom07Q9 σ (ψ.symm c) T₁ hT).target
          (alphaPPresentation s (ψ.symm c) g (X o)) := by
      intro o
      cases o with
      | none =>
        rw [alphaPPresentation_X_none]
        show g' (X (e (Sum.inr 0))) = ε.symm (rest.toTop.hom (alphaPAlgebraEquiv07Q9 hp ψ c
          (Ideal.Quotient.mk _ Polynomial.X)))
        rw [hroot, alphaPAlgebraEquiv07Q9_root]
        rfl
      | some k =>
        rw [alphaPPresentation_X_some]
        exact (hvar k).trans (hT _).symm
    exact exists_chainRetraction07Q9_step σ (ψ.symm c) T₁ hT hvar hj₁ (fun _ => rfl) hg
      (ih (alphaPSituation s (ψ.symm c)) hp (alphaPAlgebraEquiv07Q9 hp ψ c)
        (alphaPPresentation s (ψ.symm c) g) (alphaPPresentation_surjective s _ g hg) t
        (alphaPStepHom07Q9 σ (ψ.symm c) T₁ hT) τb h₁ h₂ ε
        (fun x => RingEquiv.apply_symm_apply ε _) g' ((optionSumFinEquiv07Q9 κ n).trans e)
        hj₁ (fun i => hroot i.succ))

end Chain

/-! ### Degree zero of the tensor power presentations -/

section DegreeZero

variable {s t : AffineCrystallineSituation.{u, u}} (σ : AffineCrystallineSituation.Hom s t)
  {ι κ : Type u} (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (g₂ : MvPolynomial κ t.A →ₐ[t.A] t.C)
  (j : ι → κ) (hj : ∀ i, g₂ (X (j i)) = σ.target (g (X i)))

/-- The variables of degree zero: `x_i(0) ↦ x_{j(i)}(0)`. -/
def degreeZeroVariableMap07Q9 : Fin 1 × ι → Fin 1 × κ := fun v => (v.1, j v.2)

include hj in
/-- The variable condition of degree zero. -/
theorem degreeZeroVariableMap07Q9_spec (v : Fin 1 × ι) :
    tensorPowerPresentation t g₂ 0 (X (degreeZeroVariableMap07Q9 j v)) =
      σ.target (tensorPowerPresentation s g 0 (X v)) := by
  show g₂ (rename Prod.snd (X (v.1, j v.2))) = σ.target (g (rename Prod.snd (X v)))
  rw [rename_X, rename_X]
  exact hj v.2

/-- **The map of envelopes of degree zero induced by a renaming of the variables** is the map
`Crystalline.tensorPowerEnvelopeMapOver` of degree zero for the renaming. -/
theorem tensorPowerEnvelopeMapOver_zero_eq07Q9
    (hrC : ∀ b : s.A, variableMapRingHom07Q9 σ j (C b) = C (σ.base.toRingHom b))
    (hr : g₂.toRingHom.comp (variableMapRingHom07Q9 σ j) = σ.target.comp g.toRingHom) :
    tensorPowerEnvelopeMapOver σ g g₂ (variableMapRingHom07Q9 σ j) hrC hr 0 =
      variableEnvelopeMap07Q9 σ (tensorPowerPresentation s g 0) (tensorPowerPresentation t g₂ 0)
        (j := degreeZeroVariableMap07Q9 j) (degreeZeroVariableMap07Q9_spec σ g g₂ j hj) := by
  refine (polynomialDividedPowerEnvelope s (tensorPowerPresentation s g 0)).dpMorphism_ext _ _
    fun x => ?_
  rw [tensorPowerEnvelopeMapOver_polynomial, variableEnvelopeMap07Q9_algebraMap]
  refine congrArg _ ?_
  have h : tensorPowerRingHom σ (variableMapRingHom07Q9 σ j) 0 =
      variableMapRingHom07Q9 σ (degreeZeroVariableMap07Q9 j) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      rw [tensorPowerRingHom_C, variableMapRingHom07Q9_C]
    · rintro ⟨i, k⟩
      rw [variableMapRingHom07Q9_X]
      simp only [tensorPowerRingHom, eval₂Hom_X', variableMapRingHom07Q9_X,
        mvPolynomialCoprojection, rename_X]
      rfl
  exact RingHom.congr_fun h x

end DegreeZero

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline AlgebraicGeometry MvPolynomial

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {X' : Scheme.{u}} (f : X' ⟶ S.X)
  (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {p n : ℕ} (ch : AlphaPChain p Γ(S.X, W) n)
  (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)

/-- The chain presentation is `Crystalline.variableMapRingHom07Q9` of the inclusion of the old
variables, over the identity of `Γ(V)`. -/
theorem chainPresentationRename07Q9_eq :
    chainPresentationRename07Q9 S hW hVW f hW₂ (n := n) =
      variableMapRingHom07Q9 (openAffineSituationHom07Q9 S hW hVW f hW₂) Sum.inl := by
  apply MvPolynomial.ringHom_ext
  · intro b
    rw [chainPresentationRename07Q9_C, variableMapRingHom07Q9_C]
    rfl
  · intro c
    rw [variableMapRingHom07Q9_X]
    exact MvPolynomial.rename_X _ _

/-- The variables `(Fin 1 × C) ⊕ Fin n ≃ Fin 1 × (C ⊕ Fin n)` of degree zero of the chain
presentation: the old variables, and the roots placed in the only tensor factor. -/
def chainDegreeZeroVariables07Q9 (C : Type u) (n : ℕ) : (Fin 1 × C) ⊕ Fin n ≃ Fin 1 × (C ⊕ Fin n)
    where
  toFun v := Sum.elim (fun q => (q.1, Sum.inl q.2)) (fun i => (0, Sum.inr i)) v
  invFun q := Sum.elim (fun c => Sum.inl (q.1, c)) Sum.inr q.2
  left_inv v := by
    rcases v with ⟨j, c⟩ | i <;> rfl
  right_inv q := by
    obtain ⟨j, c | i⟩ := q
    · rfl
    · exact Prod.ext (Subsingleton.elim _ _) rfl

variable (he : f.app W ≫ e.hom = ch.toTop)

include he in
/-- The chain normal form identifies `f^♯` with the structure map of the chain. -/
theorem chainSectionsIso07Q9_restrictMap :
    (restrictMap07Q9 S hVW f).appTop ≫ (chainSectionsIso07Q9 S f ch e).hom =
      W.topIso.hom ≫ ch.toTop := by
  have h1 : (f ∣_ W).appTop = W.topIso.hom ≫ f.app W ≫ (f ⁻¹ᵁ W).topIso.inv := by
    rw [app_comp_topIso_inv, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  show (f ∣_ W).appTop ≫ (f ⁻¹ᵁ W).topIso.hom ≫ e.hom = _
  rw [h1, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, he]

/-- The old variables of the chain presentation go to the images under `f^♯` of the values of
the canonical presentation. -/
theorem chainPresentation07Q9_var (c : (openAffineSituation07Q9 S hW hVW).C) :
    chainPresentation07Q9 S hW hVW f hW₂ ch e (MvPolynomial.X (Sum.inl c)) =
      (openAffineSituationHom07Q9 S hW hVW f hW₂).target
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW) (MvPolynomial.X c)) := by
  rw [chainPresentation07Q9_X_inl, canonicalPresentation, aeval_X]
  rfl

/-- The old variables of degree zero of the chain presentation. -/
theorem chainDegreeZero07Q9_var (k : Fin 1 × (openAffineSituation07Q9 S hW hVW).C) :
    tensorPowerPresentation _ (chainPresentation07Q9 S hW hVW f hW₂ ch e) 0
        (MvPolynomial.X (chainDegreeZeroVariables07Q9 _ n (Sum.inl k))) =
      (openAffineSituationHom07Q9 S hW hVW f hW₂).target (tensorPowerPresentation _
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW)) 0 (MvPolynomial.X k)) :=
  degreeZeroVariableMap07Q9_spec _ _ _ Sum.inl (chainPresentation07Q9_var S hW hVW f hW₂ ch e) k

/-- The roots of degree zero of the chain presentation. -/
theorem chainDegreeZero07Q9_root (i : Fin n) :
    tensorPowerPresentation _ (chainPresentation07Q9 S hW hVW f hW₂ ch e) 0
        (MvPolynomial.X (chainDegreeZeroVariables07Q9 _ n (Sum.inr i))) =
      (chainSectionsIso07Q9 S f ch e).commRingCatIsoToRingEquiv.symm (ch.roots i) := by
  show chainPresentation07Q9 S hW hVW f hW₂ ch e
    (rename Prod.snd (MvPolynomial.X (0, Sum.inr i))) = _
  rw [rename_X, chainPresentation07Q9_X_inr]
  rfl

/-- **The map `envelopeMap07Q9` of degree zero for the chain presentation is the map of envelopes
of the renaming of the variables** `Crystalline.variableEnvelopeMap07Q9`, for the variables of
degree zero `chainDegreeZeroVariables07Q9`. -/
theorem envelopeMap07Q9_chain_eq :
    envelopeMap07Q9 S hW hVW f hW₂
      (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
      (chainPresentation07Q9 S hW hVW f hW₂ ch e) (chainPresentationRename07Q9 S hW hVW f hW₂)
      (chainPresentationRename07Q9_C S hW hVW f hW₂)
      (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0 =
      variableEnvelopeMap07Q9 (openAffineSituationHom07Q9 S hW hVW f hW₂) _ _
        (j := chainDegreeZeroVariables07Q9 _ n ∘ Sum.inl)
        (chainDegreeZero07Q9_var S hW hVW f hW₂ ch e) := by
  have h1 := tensorPowerEnvelopeMapOver_zero_eq07Q9 (openAffineSituationHom07Q9 S hW hVW f hW₂)
    (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
    (chainPresentation07Q9 S hW hVW f hW₂ ch e) Sum.inl
    (chainPresentation07Q9_var S hW hVW f hW₂ ch e)
    ((chainPresentationRename07Q9_eq S hW hVW f hW₂) ▸
      chainPresentationRename07Q9_C S hW hVW f hW₂)
    ((chainPresentationRename07Q9_eq S hW hVW f hW₂) ▸
      chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e)
  refine Eq.trans ?_ h1
  unfold envelopeMap07Q9
  congr 1
  exact chainPresentationRename07Q9_eq S hW hVW f hW₂

/-- The completion of `envelopeMap07Q9` of degree zero for the chain presentation is the
completed map of envelopes of the renaming of the variables. -/
theorem adicCompletionRingMap_envelopeMap07Q9_chain
    (a : AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope
      (openAffineSituation07Q9 S hW hVW) (tensorPowerPresentation _
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW)) 0)).object) S.p)
      (polynomialDividedPowerEnvelope (openAffineSituation07Q9 S hW hVW)
        (tensorPowerPresentation _ (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
          0)).object) :
    adicCompletionRingMap (envelopeMap07Q9 S hW hVW f hW₂
      (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
      (chainPresentation07Q9 S hW hVW f hW₂ ch e) (chainPresentationRename07Q9 S hW hVW f hW₂)
      (chainPresentationRename07Q9_C S hW hVW f hW₂)
      (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0).toRingHom
      (map_pAdicIdeal_le _ _) a =
      completedVariableEnvelopeMap07Q9 (openAffineSituationHom07Q9 S hW hVW f hW₂)
        (chainDegreeZero07Q9_var S hW hVW f hW₂ ch e) S.p a := by
  rw [envelopeMap07Q9_chain_eq]

include he in
/-- **The retraction of `D(0) → D'(0)` exists**, on the completed envelopes. -/
theorem exists_chainEnvelopeRetraction07Q9 (hp : S.p = p) :
    ∃ ρ : AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope
          (openAffineSituation₂07Q9 S hVW f hW₂) (tensorPowerPresentation _
            (chainPresentation07Q9 S hW hVW f hW₂ ch e) 0)).object) S.p)
        (polynomialDividedPowerEnvelope (openAffineSituation₂07Q9 S hVW f hW₂)
          (tensorPowerPresentation _ (chainPresentation07Q9 S hW hVW f hW₂ ch e) 0)).object →+
      AdicCompletion (pAdicIdeal (A := (polynomialDividedPowerEnvelope
          (openAffineSituation07Q9 S hW hVW) (tensorPowerPresentation _
            (canonicalPresentation (openAffineSituation07Q9 S hW hVW)) 0)).object) S.p)
        (polynomialDividedPowerEnvelope (openAffineSituation07Q9 S hW hVW)
          (tensorPowerPresentation _ (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
            0)).object,
      (∀ a x, ρ (adicCompletionRingMap (envelopeMap07Q9 S hW hVW f hW₂
          (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
          (chainPresentation07Q9 S hW hVW f hW₂ ch e) (chainPresentationRename07Q9 S hW hVW f hW₂)
          (chainPresentationRename07Q9_C S hW hVW f hW₂)
          (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0).toRingHom
          (map_pAdicIdeal_le _ _) a * x) = a * ρ x) ∧ ρ 1 = 1 := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_chainRetraction07Q9 ch (openAffineSituation07Q9 S hW hVW) hp
    W.topIso.commRingCatIsoToRingEquiv _
    (tensorPowerPresentation_surjective _ _ (canonicalPresentation_surjective _) 0)
    (openAffineSituation₂07Q9 S hVW f hW₂) (openAffineSituationHom07Q9 S hW hVW f hW₂)
    (DPMorphism.id _) (fun _ => rfl) (fun _ => rfl)
    (chainSectionsIso07Q9 S f ch e).commRingCatIsoToRingEquiv
    (fun x => congrArg (fun k => k.hom x) (chainSectionsIso07Q9_restrictMap S hVW f ch e he))
    _ (chainDegreeZeroVariables07Q9 _ n) (chainDegreeZero07Q9_var S hW hVW f hW₂ ch e)
    (chainDegreeZero07Q9_root S hW hVW f hW₂ ch e)
  refine ⟨ρ, fun a x => ?_, hρ1⟩
  rw [adicCompletionRingMap_envelopeMap07Q9_chain]
  exact hρ a x

/-- Conjugating by ring isomorphisms keeps an additive retraction linear over a ring map. -/
private theorem retraction_conj_mul_left07Q9 {R₁ R₂ T₁ T₂ : Type*} [Semiring R₁] [Semiring R₂]
    [Semiring T₁] [Semiring T₂] (E₁ : R₁ ≃+* T₁) (E₂ : R₂ ≃+* T₂) (ρ : T₂ →+ T₁) (φ : R₁ →+* R₂)
    (Φ : T₁ →+* T₂) (hΦ : ∀ a, E₂ (φ a) = Φ (E₁ a)) (hρ : ∀ a x, ρ (Φ a * x) = a * ρ x)
    (a : R₁) (x : R₂) : E₁.symm (ρ (E₂ (φ a * x))) = a * E₁.symm (ρ (E₂ x)) := by
  rw [map_mul E₂, hΦ, hρ, map_mul, RingEquiv.symm_apply_apply]

/-- **The retraction `D'(0) → D(0)` of the map of degree zero of the envelopes**, for the chain
presentation of `Γ(f⁻¹(W))`: an additive map, linear over `D(0)` acting on `D'(0)` through
`envelopeRingMap07Q9` (`chainEnvelopeRetraction07Q9_mul_left`), sending `1` to `1`
(`chainEnvelopeRetraction07Q9_one`).  It is the composite of the retractions of the stages of the
chain, `Crystalline.exists_chainRetraction07Q9`, read on the rings of the objects
`Crystalline.tensorPowerEnvelopeThickening` of degree zero. -/
def chainEnvelopeRetraction07Q9 (hp : S.p = p) :
    (tensorPowerEnvelopeThickening (openAffineSituation₂07Q9 S hVW f hW₂)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0).thickening.ring →+
      (tensorPowerEnvelopeThickening (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _) 0).thickening.ring :=
  ((tensorPowerEnvelopeThickeningRingEquiv _ _ (canonicalPresentation_surjective _)
      0).symm.toRingHom.toAddMonoidHom.comp
    (exists_chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp).choose).comp
    (tensorPowerEnvelopeThickeningRingEquiv _ _
      (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0).toRingHom.toAddMonoidHom

/-- **The retraction is linear over `D(0)`**, which acts on `D'(0)` through the map
`envelopeRingMap07Q9` of degree zero of the morphism of Čech systems of the chain. -/
theorem chainEnvelopeRetraction07Q9_mul_left (hp : S.p = p)
    (a : (tensorPowerEnvelopeThickening (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _) 0).thickening.ring)
    (x : (tensorPowerEnvelopeThickening (openAffineSituation₂07Q9 S hVW f hW₂)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0).thickening.ring) :
    chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp
        (envelopeRingMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
          (canonicalPresentation_surjective _) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
          (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
          (chainPresentationRename07Q9 S hW hVW f hW₂)
          (chainPresentationRename07Q9_C S hW hVW f hW₂)
          (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0 a * x) =
      a * chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp x := by
  exact retraction_conj_mul_left07Q9 _ _ _ _ _
    (ringEquiv_envelopeRingMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
      (canonicalPresentation_surjective _) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
      (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
      (chainPresentationRename07Q9 S hW hVW f hW₂) (chainPresentationRename07Q9_C S hW hVW f hW₂)
      (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) 0)
    (exists_chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp).choose_spec.1 a x

/-- **The retraction sends `1` to `1`.** -/
theorem chainEnvelopeRetraction07Q9_one (hp : S.p = p) :
    chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp 1 = 1 := by
  have hspec := (exists_chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp).choose_spec.2
  show (tensorPowerEnvelopeThickeningRingEquiv _ _ (canonicalPresentation_surjective _) 0).symm
    ((exists_chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp).choose
      ((tensorPowerEnvelopeThickeningRingEquiv _ _
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0) 1)) = 1
  exact (congrArg (fun y => (tensorPowerEnvelopeThickeningRingEquiv _ _
      (canonicalPresentation_surjective (openAffineSituation07Q9 S hW hVW)) 0).symm
      ((exists_chainEnvelopeRetraction07Q9 S hW hVW f hW₂ ch e he hp).choose y))
    (map_one (tensorPowerEnvelopeThickeningRingEquiv _ _
      (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) 0))).trans
    ((congrArg (tensorPowerEnvelopeThickeningRingEquiv _ _
      (canonicalPresentation_surjective (openAffineSituation07Q9 S hW hVW)) 0).symm hspec).trans
      (map_one _))

/-! ### The morphism of cosimplicial divided power algebras -/

section CosimplicialHom

variable {ι κ : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A
    →ₐ[(openAffineSituation07Q9 S hW hVW).A] (openAffineSituation07Q9 S hW hVW).C)
  (g₂ : MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A
    →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A] (openAffineSituation₂07Q9 S hVW f hW₂).C)
  (r : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →+*
    MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A)
  (hrC : ∀ b, r (MvPolynomial.C b) = MvPolynomial.C b)
  (hr : g₂.toRingHom.comp r = (restrictMap07Q9 S hVW f).appTop.hom.comp g.toRingHom)

/-- **The morphism of cosimplicial divided power algebras `D(•) ⟶ D'(•)`** of a morphism of
presentations over `f^♯`: in degree `b` the map `envelopeMap07Q9 b` of the uncompleted envelopes
of the `(b + 1)`-fold tensor power presentations, which is a map over `Γ(V)` and commutes with
the reindexings of the variables (`Crystalline.tensorPowerEnvelopeMapOver_comp_envelopeReindex`).
-/
def envelopeDPAlgebraHom07Q9 :
    (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW) g).Hom
      (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂) where
  app b :=
    letI : Algebra (openAffineSituation07Q9 S hW hVW).A
        ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).carrier b) :=
      (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).algebra b
    { __ := (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr b).toRingHom
      commutes' := fun a => congrArg (fun q : DPMorphism _ _ => q a)
        (tensorPowerEnvelopeMapOver_structureMap (openAffineSituationHom07Q9 S hW hVW f hW₂)
          g g₂ r hrC hr b) }
  isDPMorphism b := (envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr b).isDPMorphism
  naturality {m n} φ := by
    let : Algebra (openAffineSituation07Q9 S hW hVW).A
        ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).carrier n.len) :=
      (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).algebra n.len
    exact AlgHom.coe_ringHom_injective (RingHom.ext fun x => congrArg
      (fun q : DPMorphism _ _ => q x) (tensorPowerEnvelopeMapOver_comp_envelopeReindex
        (openAffineSituationHom07Q9 S hW hVW f hW₂) g g₂ r hrC hr φ))

/-- The component of degree `b` is the map `envelopeMap07Q9 b` of the uncompleted envelopes. -/
theorem envelopeDPAlgebraHom07Q9_app (b : ℕ)
    (x : (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW) g).carrier b) :
    (envelopeDPAlgebraHom07Q9 S hW hVW f hW₂ g g₂ r hrC hr).app b x =
      envelopeMap07Q9 S hW hVW f hW₂ g g₂ r hrC hr b x :=
  rfl

/-- **The completion of the morphism of cosimplicial divided power algebras is the map
`envelopeRingMap07Q9` of the Čech systems**, read through the identifications
`Crystalline.tensorPowerEnvelopeThickeningRingEquiv` of the rings of the objects `D(b)` and
`D'(b)` with the completed envelopes. -/
theorem ringEquiv_envelopeRingMap07Q9_eq_completedRingMap
    (hg : Function.Surjective g) (hg₂ : Function.Surjective g₂) (b : ℕ)
    (x : (tensorPowerEnvelopeThickening (openAffineSituation07Q9 S hW hVW) g hg
      b).thickening.ring) :
    tensorPowerEnvelopeThickeningRingEquiv _ g₂ hg₂ b
        (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr b x) =
      (envelopeDPAlgebraHom07Q9 S hW hVW f hW₂ g g₂ r hrC hr).completedRingMap S.p b
        (tensorPowerEnvelopeThickeningRingEquiv _ g hg b x) :=
  ringEquiv_envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr b x

variable (he : f.app W ≫ e.hom = ch.toTop)

/-- **The morphism of cosimplicial divided power algebras of a chain normal form**: from the
cosimplicial envelope of the canonical presentation of `Γ(W)` to that of the chain presentation
of `Γ(f⁻¹(W))`, induced by the renaming `chainPresentationRename07Q9` of the variables. -/
def chainEnvelopeHom07Q9 :
    (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))).Hom
      (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)) :=
  envelopeDPAlgebraHom07Q9 S hW hVW f hW₂ _ _ (chainPresentationRename07Q9 S hW hVW f hW₂)
    (chainPresentationRename07Q9_C S hW hVW f hW₂)
    (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e)

/-- **The completion of `chainEnvelopeHom07Q9` is `envelopeRingMap07Q9`** for the chain normal
form, read through `Crystalline.tensorPowerEnvelopeThickeningRingEquiv`: this is the ring map of
the morphism of Čech systems `chainCechSystemHom07Q9`. -/
theorem ringEquiv_envelopeRingMap07Q9_chain (b : ℕ)
    (x : (tensorPowerEnvelopeThickening (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
      (canonicalPresentation_surjective _) b).thickening.ring) :
    tensorPowerEnvelopeThickeningRingEquiv _ _
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) b
        (envelopeRingMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
          (canonicalPresentation_surjective _) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
          (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
          (chainPresentationRename07Q9 S hW hVW f hW₂)
          (chainPresentationRename07Q9_C S hW hVW f hW₂)
          (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) b x) =
      (chainEnvelopeHom07Q9 S hW hVW f hW₂ ch e).completedRingMap S.p b
        (tensorPowerEnvelopeThickeningRingEquiv _ _ (canonicalPresentation_surjective _) b x) :=
  ringEquiv_envelopeRingMap07Q9 S hW hVW f hW₂ _ _ _ _ _ _ _ b x

end CosimplicialHom

end Crystalline.GlobalCrystallineSituation.SmallSite
