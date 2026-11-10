module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.IntegralClosureCompletion
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization

/-!
# The completion of the normalization stalk of a one-dimensional scheme

Let `X` be a reduced Nagata scheme, `ν : X^ν ⟶ X` its normalization and `x` a point whose local
ring `A = 𝒪_{X,x}` has dimension one.  The stalk `A' = (ν_* 𝒪_{X^ν})_x` is finite over `A`, so
its completion along the extension `𝔪 A'` of the maximal ideal of `A` is the base change
`A' ⊗_A Â`.  This file computes that completion in two ways:

* it is a finite product of complete discrete valuation rings, one for each prime of `A'` above
  `𝔪`;
* it is the integral closure of `Â` in the total ring of fractions of `Â`.

## Main results

* `IsLocalRing.exists_pi_isDiscreteValuationRing_adicCompletion_map_maximalIdeal`: the
  ring-theoretic product decomposition, for an arbitrary normal finite extension.
* `AlgebraicGeometry.exists_pi_isDiscreteValuationRing_adicCompletion_normalizationStalk`:
  its specialisation to the normalization stalk.
* `IsLocalRing.exists_injective_range_eq_integralClosure_adicCompletion_fractionRing`: the
  ring-theoretic identification of the completion with the integral closure of `Â`.
* `AlgebraicGeometry.exists_injective_range_eq_integralClosure_adicCompletion_normalizationStalk`:
  its specialisation to the normalization stalk.

## Implementation notes

Both ring-theoretic statements are proved for an abstract finite `A`-algebra and then
transported to the normalization stalk along
`Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationStalkAlgEquivIntegralClosureSelf`,
which identifies that stalk with `integralClosure A (Frac A)`.  The comparison between the
`𝔪`-adic completion of `A'` as an `A`-module and its `𝔪 A'`-adic completion as a ring is
`ofTensorProductAlgEquiv`; the product decomposition over the primes above `𝔪` is
`AdicCompletion.nonempty_algEquiv_pi_primesOver` (Tag 07N9).

A prime `q` of `A'` above `𝔪` has height one: it is at most the dimension of `A'`, which equals
that of `A` because `A'` is integral over `A`, and at least one because a chosen nonzerodivisor
of `𝔪` lies in `q` and stays a nonzerodivisor in `A'`.  Normality of `A'` then makes `A'_q` a
one-dimensional normal Noetherian local domain, hence a discrete valuation ring, and so is its
completion.

The product decomposition does not need the point to be closed, nor the dimension of `X`: the
dimension hypothesis is used only through the dimension of the local ring at `x`.  The
identification of the completion with an integral closure is stated for `ringKrullDim A ≤ 1`, so
that it also covers the points whose local ring is a field; there `Â = A` and the integral
closure is everything.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
* [Stacks Project, Tag 07N9](https://stacks.math.columbia.edu/tag/07N9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

/-- The localization of a one-dimensional normal Noetherian ring at a prime containing a
nonzerodivisor is a discrete valuation ring. -/
private theorem exists_isDiscreteValuationRing_localization_of_mem_nonZeroDivisors
    {S : Type*} [CommRing S] [IsNoetherianRing S] (hdimS : ringKrullDim S = 1)
    (hnormalS : IsNormalRing S) (q : Ideal S) [q.IsPrime] {s : S} (hsq : s ∈ q)
    (hs : s ∈ nonZeroDivisors S) :
    ∃ _ : IsDomain (Localization.AtPrime q),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ ‹IsNoetherianRing S›
  have hqheight : q.height = 1 := by
    have hge : 1 ≤ q.height :=
      (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hs).trans
        (Ideal.height_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsq)))
    have hle : q.height ≤ 1 := by
      have hh := Ideal.height_le_ringKrullDim_of_isPrime (I := q)
      rw [hdimS] at hh
      exact_mod_cast hh
    simpa using le_antisymm hle hge
  have hdimL : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
    exact_mod_cast hqheight
  obtain ⟨hdomQ, hclosedQ⟩ := hnormalS q
  have : IsDomain (Localization.AtPrime q) := hdomQ
  have hitem : IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalRing (Localization.AtPrime q) ∧
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) ∧
      ringKrullDim (Localization.AtPrime q) = 1 :=
    ⟨inferInstance, inferInstance, hdomQ, hclosedQ, hdimL⟩
  exact (isDiscreteValuationRing_tfae (Localization.AtPrime q)).out 5 1 |>.mp hitem

namespace IsLocalRing

/-- **Stacks Project, Tag 0C1R.** The completion of a normal finite extension `S` of a reduced
one-dimensional Noetherian local ring `A`, along the ideal generated by the maximal ideal of
`A`, is a nonempty finite product of complete discrete valuation rings.

The factors are the completions of the local rings of `S` at the primes above the maximal
ideal of `A`. -/
public theorem exists_pi_isDiscreteValuationRing_adicCompletion_map_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A = 1)
    (S : Type u) [CommRing S] [Algebra A S] [Module.Finite A S]
    (hnormalS : IsNormalRing S) (hinj : Function.Injective (algebraMap A S))
    {f : A} (hfm : f ∈ maximalIdeal A) (hSf : algebraMap A S f ∈ nonZeroDivisors S) :
    ∃ (n : ℕ) (D : Fin n → Type u) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, IsDomain (D i))
        (_ : ∀ i, IsDiscreteValuationRing (D i)),
      0 < n ∧ (∀ i, IsAdicComplete (maximalIdeal (D i)) (D i)) ∧
        Nonempty (AdicCompletion ((maximalIdeal A).map (algebraMap A S)) S ≃+* ∀ i, D i) := by
  classical
  have : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  have hdimS : ringKrullDim S = 1 := by rw [← Algebra.IsIntegral.ringKrullDim_eq A S, hdim]
  have : IsLocalization.AtPrime A (maximalIdeal A) :=
    IsLocalization.of_le_isUnit fun a ha => (notMem_maximalIdeal (R := A)).mp ha
  let Q := (maximalIdeal A).primesOver S
  have : Finite Q := Algebra.QuasiFinite.finite_primesOver (S := S) (maximalIdeal A)
  let : Fintype Q := Fintype.ofFinite Q
  let L (q : Q) := Localization.AtPrime q.1
  -- Each `S_q` is a one-dimensional normal Noetherian local domain, hence a discrete
  -- valuation ring; so is its completion, which is moreover complete.
  have hlocal (q : Q) : ∃ _ : IsDomain (L q), IsDiscreteValuationRing (L q) := by
    have : q.1.IsPrime := q.2.1
    have hqOver : q.1.comap (algebraMap A S) = maximalIdeal A := by
      simpa [Ideal.under_def] using q.2.2.over.symm
    exact exists_isDiscreteValuationRing_localization_of_mem_nonZeroDivisors hdimS hnormalS q.1
      (by rwa [← Ideal.mem_comap, hqOver]) hSf
  let D₀ (q : Q) := AdicCompletion (maximalIdeal (L q)) (L q)
  have hcomplete (q : Q) : IsAdicComplete (maximalIdeal (D₀ q)) (D₀ q) := by
    obtain ⟨_, _⟩ := hlocal q
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact AdicCompletion.isAdicComplete_self _ (maximalIdeal (L q)).fg_of_isNoetherianRing
  have hdvr (q : Q) : ∃ _ : IsDomain (D₀ q), IsDiscreteValuationRing (D₀ q) := by
    obtain ⟨_, _⟩ := hlocal q
    exact (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal
      (A := L q)).mp ⟨inferInstance, inferInstance⟩
  -- Assemble: the completion of `S` is the base change `Â ⊗_A S`, which is the product.
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (R := A) (S := S)
    (maximalIdeal A) A L
  let eBase : AdicCompletion ((maximalIdeal A).map (algebraMap A S)) S ≃+* ∀ q : Q, D₀ q :=
    ((ofTensorProductAlgEquiv (maximalIdeal A) S).symm.trans
      (Algebra.TensorProduct.comm A (AdicCompletion (maximalIdeal A) A) S)).toRingEquiv.trans
      e.toRingEquiv
  let eFin : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  refine ⟨Fintype.card Q, fun i => D₀ (eFin i), fun _ => inferInstance,
    fun i => (hdvr (eFin i)).choose, fun i => ?_, Fintype.card_pos_iff.mpr inferInstance,
    fun i => hcomplete (eFin i), ⟨eBase.trans (RingEquiv.piCongrLeft D₀ eFin).symm⟩⟩
  have : IsDomain (D₀ (eFin i)) := (hdvr (eFin i)).choose
  exact (hdvr (eFin i)).choose_spec

/-- The `n`-th stage of `adicCompletionMap` is the induced map on the `n`-th infinitesimal
neighbourhoods. -/
private theorem evalₐ_adicCompletionMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B) (hf : I.map f ≤ J) (n : ℕ)
    (y : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (adicCompletionMap f I J hf y) =
      Ideal.quotientMap (J ^ n) f
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]; exact Ideal.pow_right_mono hf n))
        (AdicCompletion.evalₐ I n y) := by
  unfold adicCompletionMap
  exact AdicCompletion.evalₐ_liftRingHom _ _ _ _ _

/-- Over a field `K`, the structure map to `Frac K` precomposed with a surjection has range the
integral closure of `K`. -/
private theorem range_algebraMap_comp_eq_integralClosure {K C : Type*} [CommRing K] [CommRing C]
    (hK : IsField K) (e : C →+* K) (he : Function.Surjective e) :
    ((algebraMap K (FractionRing K)).comp e).range =
      (integralClosure K (FractionRing K)).toSubring := by
  have := hK.isDomain
  have hSurj : Function.Surjective (algebraMap K (FractionRing K)) :=
    IsFractionRing.surjective_iff_isField.mpr hK
  have : Module.Finite K (FractionRing K) :=
    Module.Finite.of_surjective (Algebra.linearMap K (FractionRing K)) hSurj
  have htop : integralClosure K (FractionRing K) = ⊤ :=
    integralClosure_eq_top_iff.mpr inferInstance
  refine Subring.ext fun z => ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [htop]
    trivial
  · obtain ⟨a, ha⟩ := hSurj z
    obtain ⟨c, hc⟩ := he a
    exact ⟨c, by simp [hc, ha]⟩

/-- On the left factor, the comparison `ofTensorProductAlgEquiv` is the map induced on adic
completions by the structure map of the algebra. -/
private theorem ofTensorProductAlgEquiv_includeLeft
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] (y : AdicCompletion I A) :
    ofTensorProductAlgEquiv I B
        (Algebra.TensorProduct.includeLeft (R := A) (S := AdicCompletion I A)
          (A := AdicCompletion I A) (B := B) y) =
      adicCompletionMap (algebraMap A B) I (I.map (algebraMap A B)) le_rfl y := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  change AdicCompletion.evalₐ _ n (ofTensorProductLinearEquiv I B (y ⊗ₜ[A] (1 : B))) = _
  rw [ofTensorProductLinearEquiv_tmul_eval, evalₐ_adicCompletionMap]
  simp

/-- On the right factor, the comparison `ofTensorProductAlgEquiv` is the structure map of the
adic completion of the algebra. -/
private theorem ofTensorProductAlgEquiv_includeRight
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] (b : B) :
    ofTensorProductAlgEquiv I B
        (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A) (B := B) b) =
      algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) b := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  change AdicCompletion.evalₐ _ n
    (ofTensorProductLinearEquiv I B ((1 : AdicCompletion I A) ⊗ₜ[A] b)) = _
  rw [ofTensorProductLinearEquiv_tmul_eval]
  simp

/-- The normalization of a one-dimensional reduced Nagata local ring commutes with completion,
in the form needed for the normalization stalk: for a finite `A`-algebra `B` identified with the
integral closure of `A` in `Frac A`, the completion of `B` along `𝔪 B` is the integral closure
of `Â` in `Frac Â`, compatibly with the maps from `Â` and from `B`. -/
@[ega "IV 7.6.1" "special case"]
private theorem exists_injective_range_eq_integralClosure_adicCompletion_of_dim_one
    {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsReduced A]
    [CommRing B] [Algebra A B] (hA : IsNagataRing A) (hdim : ringKrullDim A = 1)
    (f : B →ₐ[A] FractionRing A) (hf : Function.Injective f)
    (hrange : f.range = integralClosure A (FractionRing A)) :
    let Ac := AdicCompletion (maximalIdeal A) A
    let J := (maximalIdeal A).map (algebraMap A B)
    let C := AdicCompletion J B
    let k : Ac →+* C := adicCompletionMap (algebraMap A B) (maximalIdeal A) J le_rfl
    ∃ q : FractionRing A →+* FractionRing Ac,
      (∀ a : A, q (algebraMap A (FractionRing A) a) =
        algebraMap Ac (FractionRing Ac) (algebraMap A Ac a)) ∧
      ∃ g : C →+* FractionRing Ac,
        Function.Injective g ∧
        g.range = (integralClosure Ac (FractionRing Ac)).toSubring ∧
        (∀ y : Ac, g (k y) = algebraMap Ac (FractionRing Ac) y) ∧
        (∀ b : B, g (algebraMap B C b) = q (f b)) := by
  intro Ac J C k
  let D := integralClosure A (FractionRing A)
  have : Module.Finite A D := module_finite_integralClosure_fractionRing hA
  let eNorm : B ≃ₐ[A] D := (AlgEquiv.ofInjective f hf).trans (Subalgebra.equivOfEq _ _ hrange)
  have : Module.Finite A B :=
    Module.Finite.of_surjective eNorm.symm.toLinearMap eNorm.symm.surjective
  obtain ⟨q₀, g₀, hg₀i, hg₀r, hleft, hright⟩ :=
    exists_fractionRing_map_and_tensorProduct_range_eq_integralClosure_completion hA hdim
  let E : D ⊗[A] Ac ≃ₐ[A] C :=
    ((Algebra.TensorProduct.comm A D Ac).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : Ac ≃ₐ[A] Ac)
        eNorm.symm).restrictScalars A)).trans (ofTensorProductAlgEquiv (maximalIdeal A) B)
  let g₁ : D ⊗[A] Ac →ₐ[A] FractionRing Ac := g₀
  let g₂ : C →ₐ[A] FractionRing Ac := g₁.comp E.symm.toAlgHom
  have hg₂ (d : D ⊗[A] Ac) : g₂ (E d) = g₁ d := by simp [g₂, g₁]
  refine ⟨q₀.toRingHom, fun a => ?_, g₂.toRingHom, hg₀i.comp E.symm.injective, ?_, ?_, ?_⟩
  · rw [← IsScalarTower.algebraMap_apply A Ac (FractionRing Ac) a]
    exact q₀.commutes a
  · refine Subring.ext fun z => Iff.trans ?_ (SetLike.ext_iff.mp hg₀r z)
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨E.symm c, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨E d, hg₂ d⟩
  · intro y
    have hE : E (Algebra.TensorProduct.includeRight y) = k y := by
      simp only [E, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        AlgEquiv.refl_toAlgHom, AlgHom.id_apply, map_one]
      exact ofTensorProductAlgEquiv_includeLeft (maximalIdeal A) B y
    rw [← hE]
    refine (hg₂ _).trans ?_
    exact DFunLike.congr_fun hright y
  · intro b
    have hE : E (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := D) (B := Ac)
        (eNorm b)) = algebraMap B C b := by
      simp only [E, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply (R := A) (S := A) (A := D) (B := Ac),
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply]
      change ofTensorProductAlgEquiv (maximalIdeal A) B
        (Algebra.TensorProduct.includeRight (eNorm.symm (eNorm b))) = _
      rw [AlgEquiv.symm_apply_apply eNorm b]
      exact ofTensorProductAlgEquiv_includeRight (maximalIdeal A) B b
    rw [← hE]
    refine (hg₂ _).trans ?_
    exact DFunLike.congr_fun hleft (eNorm b)

/-- The same identification over a field, where every ring in sight is that field: the maximal
ideal is zero, so both completions are trivial and the integral closure is everything. -/
private theorem exists_injective_range_eq_integralClosure_adicCompletion_of_isField
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (hfield : IsField A) (f : B →ₐ[A] FractionRing A) (hf : Function.Injective f)
    (hrange : f.range = integralClosure A (FractionRing A)) :
    let Ac := AdicCompletion (maximalIdeal A) A
    let J := (maximalIdeal A).map (algebraMap A B)
    let C := AdicCompletion J B
    let k : Ac →+* C := adicCompletionMap (algebraMap A B) (maximalIdeal A) J le_rfl
    ∃ q : FractionRing A →+* FractionRing Ac,
      (∀ a : A, q (algebraMap A (FractionRing A) a) =
        algebraMap Ac (FractionRing Ac) (algebraMap A Ac a)) ∧
      ∃ g : C →+* FractionRing Ac,
        Function.Injective g ∧
        g.range = (integralClosure Ac (FractionRing Ac)).toSubring ∧
        (∀ y : Ac, g (k y) = algebraMap Ac (FractionRing Ac) y) ∧
        (∀ b : B, g (algebraMap B C b) = q (f b)) := by
  intro Ac J C k
  let : Field A := hfield.toField
  let eAK : A ≃ₐ[A] FractionRing A :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom A A (FractionRing A))
      ⟨IsFractionRing.injective A (FractionRing A),
        IsFractionRing.surjective_iff_isField.mpr hfield⟩
  have : Module.Finite A (FractionRing A) := .of_surjective eAK.toLinearMap eAK.surjective
  have hRangeTop : f.range = ⊤ := hrange.trans (integralClosure_eq_top_iff.mpr inferInstance)
  let eBA : B ≃ₐ[A] A :=
    AlgEquiv.ofBijective (eAK.symm.toAlgHom.comp f)
      ⟨fun z w h => hf (eAK.symm.injective h), fun a => by
        obtain ⟨b, hb⟩ := (AlgHom.mem_range f).mp (show eAK a ∈ f.range by simp [hRangeTop])
        exact ⟨b, by
          dsimp
          rw [hb, eAK.symm_apply_apply]⟩⟩
  have hI : maximalIdeal A = ⊥ := maximalIdeal_eq_bot
  have hJ : J = ⊥ := by simp [J, hI]
  have : IsAdicComplete (maximalIdeal A) A :=
    hI.symm ▸ (inferInstance : IsAdicComplete (⊥ : Ideal A) A)
  have : IsAdicComplete J B := hJ.symm ▸ (inferInstance : IsAdicComplete (⊥ : Ideal B) B)
  let eAhat : A ≃ₐ[A] Ac := AdicCompletion.ofAlgEquiv (maximalIdeal A)
  let eBhat : B ≃ₐ[A] C := (AdicCompletion.ofAlgEquiv J).restrictScalars A
  let eCA : C ≃ₐ[A] Ac := eBhat.symm.trans (eBA.trans eAhat)
  let : Field Ac := (eAhat.toRingEquiv.symm.isField (Field.toIsField A)).toField
  let qEq : FractionRing A ≃+* FractionRing Ac :=
    IsFractionRing.ringEquivOfRingEquiv eAhat.toRingEquiv
  let gAlg : C →ₐ[A] FractionRing Ac :=
    (IsScalarTower.toAlgHom A Ac (FractionRing Ac)).comp eCA.toAlgHom
  -- The two completions are trivial, so `k` is `eCA.symm` composed with nothing.
  have hk (a : A) : k (algebraMap A Ac a) = algebraMap B C (algebraMap A B a) :=
    RingHom.congr_fun
      (adicCompletionMap_comp_algebraMap (algebraMap A B) (maximalIdeal A) J le_rfl) a
  have heCA (y : Ac) : eCA (k y) = y := by
    obtain ⟨a, rfl⟩ := eAhat.surjective y
    have hae : eAhat a = algebraMap A Ac a := eAhat.commutes a
    rw [hae, hk a]
    have hB : eBhat.symm (algebraMap B C (algebraMap A B a)) = algebraMap A B a :=
      (AdicCompletion.ofAlgEquiv J).symm_apply_eq.mpr
        ((AdicCompletion.ofAlgEquiv J).commutes _).symm
    change eAhat (eBA (eBhat.symm (algebraMap B C (algebraMap A B a)))) = _
    rw [hB, show eBA (algebraMap A B a) = a by simp [eBA], hae]
  refine ⟨qEq.toRingHom, fun a => ?_, gAlg.toRingHom, ?_, ?_, fun y => ?_, fun b => ?_⟩
  · rw [← eAhat.commutes a]
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap eAhat.toRingEquiv a
  · exact fun z w h =>
      eCA.injective (IsFractionRing.injective Ac (FractionRing Ac) (by simpa [gAlg] using h))
  · exact range_algebraMap_comp_eq_integralClosure (Field.toIsField Ac) eCA.toRingHom
      eCA.surjective
  · simpa [gAlg] using congrArg (algebraMap Ac (FractionRing Ac)) (heCA y)
  · rw [show f b = algebraMap A (FractionRing A) (eBA b) from (eAK.apply_symm_apply (f b)).symm]
    change algebraMap Ac (FractionRing Ac) (eCA (algebraMap B C b)) = _
    rw [show eCA (algebraMap B C b) = eAhat (eBA b) by
      simp [eCA, eBhat, AdicCompletion.ofAlgEquiv]]
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap eAhat.toRingEquiv (eBA b)).symm

/-- **Stacks Project, Tag 0C1R.** Normalization commutes with completion for a reduced Nagata
local ring of dimension at most one: if `B` is identified with the integral closure of `A` in
the total ring of fractions of `A` by an injective `A`-algebra map `f`, then the completion of
`B` along the ideal generated by the maximal ideal of `A` is the integral closure of `Â` in the
total ring of fractions of `Â`, compatibly with the maps from `Â` and from `B`.

The dimension-zero case is covered: there `A` is a field, both completions are trivial, and the
integral closure is everything. -/
@[ega "IV 7.6.1" "special case", ega "IV 7.8.3" "(vii), special case"]
public theorem exists_injective_range_eq_integralClosure_adicCompletion_fractionRing
    {A B : Type u} [CommRing A] [IsLocalRing A] [_root_.IsReduced A]
    [CommRing B] [Algebra A B] (hA : IsNagataRing A) (hdim : ringKrullDim A ≤ 1)
    (f : B →ₐ[A] FractionRing A) (hf : Function.Injective f)
    (hrange : f.range = integralClosure A (FractionRing A)) :
    let Ac := AdicCompletion (maximalIdeal A) A
    let J := (maximalIdeal A).map (algebraMap A B)
    let C := AdicCompletion J B
    let k : Ac →+* C := adicCompletionMap (algebraMap A B) (maximalIdeal A) J le_rfl
    ∃ q : FractionRing A →+* FractionRing Ac,
      (∀ a : A, q (algebraMap A (FractionRing A) a) =
        algebraMap Ac (FractionRing Ac) (algebraMap A Ac a)) ∧
      ∃ g : C →+* FractionRing Ac,
        Function.Injective g ∧
        g.range = (integralClosure Ac (FractionRing Ac)).toSubring ∧
        (∀ y : Ac, g (k y) = algebraMap Ac (FractionRing Ac) y) ∧
        (∀ b : B, g (algebraMap B C b) = q (f b)) := by
  have : IsNoetherianRing A := hA.1
  by_cases hfield : IsField A
  · exact exists_injective_range_eq_integralClosure_adicCompletion_of_isField hfield f hf hrange
  · have hdimA : ringKrullDim A = 1 := by
      refine le_antisymm hdim ?_
      have hpos : ¬ ringKrullDim A ≤ 0 := fun hzero => by
        have : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr hzero
        exact hfield Ring.KrullDimLE.isField_of_isReduced
      cases h : ringKrullDim A with
      | bot => exact absurd (by simp [h] : ringKrullDim A ≤ 0) hpos
      | coe d =>
        refine WithBot.coe_le_coe.mpr (Order.one_le_iff_ne_zero.mpr fun hd => ?_)
        exact hpos (by simp [h, hd])
    exact exists_injective_range_eq_integralClosure_adicCompletion_of_dim_one hA hdimA f hf hrange

end IsLocalRing

namespace AlgebraicGeometry

open Stacks.NormalizationStalkAmbient
open Stacks.AlgebraicGeometry.NormalizationQuotient

/-- **Stacks Project, Tag 0C1R.** At a point of a reduced Nagata scheme whose local ring has
dimension one, the completion of the stalk of the pushforward of the structure sheaf of the
normalization, along the ideal generated by the maximal ideal of the local ring, is a nonempty
finite product of complete discrete valuation rings.

Neither the dimension of `X` nor the closedness of the point is needed: the dimension
hypothesis of the source enters only through the dimension of the local ring at `x`. -/
@[stacks 0C1R "complete_dvr_product"]
public theorem exists_pi_isDiscreteValuationRing_adicCompletion_normalizationStalk
    (X : Scheme.{u}) [IsReduced X] (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (hxdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    ∃ (n : ℕ) (D : Fin n → Type u) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, IsDomain (D i))
        (_ : ∀ i, IsDiscreteValuationRing (D i)),
      0 < n ∧ (∀ i, IsAdicComplete (maximalIdeal (D i)) (D i)) ∧
        Nonempty (AdicCompletion
          ((maximalIdeal (X.presheaf.stalk x)).map
            (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x)))
          (normalizationPushforwardStalk X hX x) ≃+* ∀ i, D i) := by
  have : _root_.IsReduced (X.presheaf.stalk x) :=
    AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  let A := X.presheaf.stalk x
  let : Algebra A (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let A' := normalizationPushforwardStalk X hX x
  have hA : IsNagataRing A := stalk_isNagataRing X hNagata x
  have : IsNoetherianRing A := hA.1
  let C := integralClosure A (FractionRing A)
  let e : A' ≃ₐ[A] C := normalizationStalkAlgEquivIntegralClosureSelf X hX x
  have : Module.Finite A C := module_finite_integralClosure_fractionRing hA
  have : Module.Finite A A' := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  -- A nonzerodivisor of the maximal ideal whose powers realize the total ring of fractions.
  obtain ⟨f, hfm, hLA, -⟩ :=
    exists_common_fractionRing_localization_and_injective_tensorProduct.{u, u} hA hxdim
  have hA'f : algebraMap A A' f ∈ nonZeroDivisors A' := by
    rw [← e.symm.commutes f, ← MulEquivClass.map_nonZeroDivisors e.symm]
    exact Submonoid.mem_map_of_mem _ (nonZeroDivisor_integralClosure_of_powerLocalization hLA)
  exact exists_pi_isDiscreteValuationRing_adicCompletion_map_maximalIdeal hxdim A'
    (IsNormalRing.congr e.symm.toRingEquiv (isNormalRing_integralClosure_fractionRing (A := A)))
    (normalizationPushforwardStalk_map_injective X hX x) hfm hA'f

/-- **Stacks Project, Tag 0C1R.** Completing the stalk of the pushforward of the structure sheaf
of the normalization of a reduced one-dimensional Nagata scheme, along the ideal generated by
the maximal ideal of the local ring at the point, gives the integral closure of the completed
local ring in its own total ring of fractions.

The two compatibility equations say that the resulting embedding extends the structure map of
the completed local ring and the given embedding `f₀` of the normalization stalk; the embedding
`f₀` exists and is unique by
`existsUnique_algHom_normalizationPushforwardStalk_fractionRing`.

Closedness of the point is not needed.  The points whose local ring is zero-dimensional are
covered: there the local ring is a field and both completions are trivial. -/
/- Distinct from `existsUnique_linearEquiv_quotient_adicCompletion_normalizationPushforwardStalk`
in `StacksFrontier/AlgebraicGeometry/NormalizationQuotient/Completion.lean`, which runs on the same
hypotheses and concludes the uniqueness of an `A`-linear isomorphism of the two quotients
`A'/A ≅ A'^∧/A^∧`, identifying neither completion on its own. The statement below identifies
`A'^∧` itself with the integral closure of `A^∧` in `Frac(A^∧)`, by a ring injection with that
range, and takes an embedding `f₀ : A' →ₐ[A] Frac A` as a further input. -/
@[stacks 0C1R "normalization_after_completion", ega "IV 7.6.1" "special case"]
public theorem exists_injective_range_eq_integralClosure_adicCompletion_normalizationStalk
    (X : Scheme.{u}) [IsReduced X] (hNagata : IsNagataScheme X)
    (hdim : topologicalKrullDim X = 1)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    let A := X.presheaf.stalk x
    let A' := normalizationPushforwardStalk X hX x
    let Ac := AdicCompletion (maximalIdeal A) A
    let J := (maximalIdeal A).map (algebraMap A A')
    let C := AdicCompletion J A'
    let k : Ac →+* C := adicCompletionMap (algebraMap A A') (maximalIdeal A) J le_rfl
    ∀ f₀ : A' →ₐ[A] FractionRing A, Function.Injective f₀ →
      f₀.range = integralClosure A (FractionRing A) →
      ∃ q : FractionRing A →+* FractionRing Ac,
        (∀ a : A, q (algebraMap A (FractionRing A) a) =
          algebraMap Ac (FractionRing Ac) (algebraMap A Ac a)) ∧
        ∃ g : C →+* FractionRing Ac,
          Function.Injective g ∧
          g.range = (integralClosure Ac (FractionRing Ac)).toSubring ∧
          (∀ y : Ac, g (k y) = algebraMap Ac (FractionRing Ac) y) ∧
          (∀ a' : A', g (algebraMap A' C a') = q (f₀ a')) := by
  have : _root_.IsReduced (X.presheaf.stalk x) :=
    AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  intro A A' Ac J C k f₀ hf₀ hrange
  exact IsLocalRing.exists_injective_range_eq_integralClosure_adicCompletion_fractionRing
    (stalk_isNagataRing X hNagata x)
    ((ringKrullDim_stalk_le_topologicalKrullDim X x).trans hdim.le) f₀ hf₀ hrange

end AlgebraicGeometry

end
