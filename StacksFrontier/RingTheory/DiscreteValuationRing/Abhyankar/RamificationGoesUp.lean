module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.UnramifiedBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unramified and tame ramification go up

A finite separable extension stays a finite product of fields after scalar extension along an
extension of discrete valuation rings, and unramifiedness and tame ramification pass to every
factor.

## Main results

* `IsDiscreteValuationRing.exists_algEquiv_pi_field_and_ramification_goes_up`: a finite separable
  extension stays a finite product of fields after scalar extension, and unramifiedness and tame
  ramification pass to every factor.

## References

* [The Stacks Project, Tag 0EXY](https://stacks.math.columbia.edu/tag/0EXY)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y

open scoped TensorProduct

/-- A finite étale base change stays étale on every normalized generic factor.

More precisely, suppose the generic tensor product `L ⊗[K] K'` is presented as a product of
fields `E i`.  If the normalization of `A` in `K'` is étale over `A`, then for every factor the
normalization of `B` in `E i` is étale over `B`.  Thus `integralClosure B (E i)` is the normalized
upper DVR in the base-change square and its vertical map from `B` has ramification index one.

The proof is the integral-closure form of étale base change: smooth base change identifies the
normalization of the tensor product (`TensorProduct.toIntegralClosure_bijective_of_smooth`), and
projection to a product factor preserves formal unramifiedness. -/
@[ega "IV 18.10.13" "(iii), special case"]
theorem algebraEtale_integralClosure_factor_of_etale_baseChange
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K' : Type y)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K']
    [Algebra A B] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Module.Finite K K'] [Algebra.IsSeparable K K']
    {I : Type*} (E : I → Type*) [∀ i, Field (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, Module.Finite L (E i)]
    [∀ i, Algebra.IsSeparable L (E i)]
    (e : (L ⊗[K] K') ≃ₐ[L] ∀ i, E i)
    (hA' : Algebra.Etale A (integralClosure A K')) (i : I) :
    Algebra.Etale B (integralClosure B (E i)) := by
  let _ : Algebra.Etale A (integralClosure A K') := hA'
  apply (isUnramifiedWithRespectTo_iff_etale B L (E i)).mp
  exact isUnramifiedWithRespectTo_pi_of_baseChange A B K L K' E e
    ((isUnramifiedWithRespectTo_iff_etale A K K').mpr hA') i

/-- A finite separable field extension is étale. -/
private theorem etale_of_finite_separable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] : Algebra.Etale K L :=
  ⟨Algebra.FormallyEtale.of_isSeparable K L,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- An étale algebra over a field surjects onto a finite separable field extension. -/
private theorem exists_surjective_algHom_field_of_etale
    (K : Type u) (R : Type v) [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
    [Algebra.Etale K R] :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra K M) (_ : Module.Finite K M)
      (_ : Algebra.IsSeparable K M) (p : R →ₐ[K] M), Function.Surjective p := by
  have : Algebra.Etale K (ULift.{w} R) := Algebra.Etale.of_equiv ULift.algEquiv.symm
  obtain ⟨n, H, hfield, halg, hfin, hsep, hn, ⟨d⟩⟩ :=
    exists_algEquiv_pi_field_of_etale K (ULift.{w} R)
  let i : Fin n := ⟨0, hn⟩
  let up : R ≃ₐ[K] ULift.{w} R := ULift.algEquiv.symm
  exact ⟨H i, inferInstance, inferInstance, inferInstance, inferInstance,
    (Pi.evalAlgHom K H i).comp (d.toAlgHom.comp up.toAlgHom),
    (Function.surjective_eval i).comp (d.surjective.comp up.surjective)⟩

/-- An `L`-algebra map out of `L ⊗[K] K'` is determined by its values on `1 ⊗ₜ a`. -/
private theorem algHom_tmul_eq_mul
    {K L K' E : Type*} [CommRing K] [CommRing L] [CommRing K'] [CommRing E]
    [Algebra K L] [Algebra K K'] [Algebra L E] (q : (L ⊗[K] K') →ₐ[L] E) (l : L) (a : K') :
    q (l ⊗ₜ[K] a) = algebraMap L E l * q (1 ⊗ₜ[K] a) := by
  rw [← q.commutes l, ← map_mul]
  congr 1
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- The Kummer root `y = π ^ (1 / n)` satisfies `y ^ n = π`. -/
private theorem piRoot_pow_eq_algebraMap
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (π : A) (n : ℕ)
    [Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π n))] :
    Stacks.KummerExtension.piRoot K π n ^ n =
      algebraMap A (Stacks.KummerExtension.K1 K π n) π := by
  have h := Stacks.KummerExtension.kummerPolyA_eval_piRoot K π n
  simpa only [Stacks.KummerExtension.kummerPolyA, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] using h

private theorem exists_algEquiv_pi_field_and_unramified_goes_up
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K' : Type y)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K']
    [Algebra A B] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Module.Finite K K'] [Algebra.IsSeparable K K'] :
    ∃ (n : ℕ) (E : Fin n → Type (max u v w x y))
        (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra L (E i))
        (_ : ∀ i, Algebra B (E i)) (_ : ∀ i, IsScalarTower B L (E i))
        (_ : ∀ i, Module.Finite L (E i)) (_ : ∀ i, Algebra.IsSeparable L (E i)),
      0 < n ∧ Nonempty ((L ⊗[K] K') ≃ₐ[L] ∀ i, E i) ∧
        (IsUnramifiedWithRespectTo A K K' →
          ∀ i, IsUnramifiedWithRespectTo B L (E i)) := by
  have : Algebra.Etale K K' := etale_of_finite_separable K K'
  let T := ULift.{max u v w} (L ⊗[K] K')
  have : Algebra.Etale L T := Algebra.Etale.of_equiv ULift.algEquiv.symm
  obtain ⟨n, E, hfield, halg, hfin, hsep, hn, ⟨e⟩⟩ :=
    exists_algEquiv_pi_field_of_etale L T
  let (i : Fin n) : Algebra B (E i) :=
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  have (i : Fin n) : IsScalarTower B L (E i) := .of_algebraMap_eq fun _ => rfl
  let e' := ULift.algEquiv.symm.trans e
  exact ⟨n, E, hfield, halg, inferInstance, inferInstance, hfin, hsep, hn, ⟨e'⟩,
    fun h i => isUnramifiedWithRespectTo_pi_of_baseChange A B K L K' E e' h i⟩

private theorem etale_adjoinRoot_of_isUnit_derivative
    {R : Type u} [CommRing R] {f : Polynomial R} (hf : f.Monic)
    (hu : IsUnit (AdjoinRoot.mk f f.derivative)) : Algebra.Etale R (AdjoinRoot f) := by
  let P : StandardEtalePair R := ⟨f, hf, f.derivative, ⟨1, 0, 1, by simp⟩⟩
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot f)
      (Localization.Away (AdjoinRoot.mk f f.derivative)) _ hu).restrictScalars R).symm)

private theorem etale_adjoinRoot_X_pow_sub_C_of_isUnit
    {R : Type u} [CommRing R] (n : ℕ) (hn : n ≠ 0)
    (u : R) (hu : IsUnit u) (hnu : IsUnit (n : R)) :
    Algebra.Etale R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C u)) := by
  let f := Polynomial.X ^ n - Polynomial.C u
  let S := AdjoinRoot f
  let x : S := AdjoinRoot.root f
  have hx : x ^ n = algebraMap R S u := by
    have h : Polynomial.aeval x f = 0 := (AdjoinRoot.aeval_eq f).trans AdjoinRoot.mk_self
    change Polynomial.aeval x (Polynomial.X ^ n - Polynomial.C u) = 0 at h
    simpa only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using h
  have hxunit : IsUnit x := (isUnit_pow_iff hn).mp (hx ▸ hu.map (algebraMap R S))
  apply etale_adjoinRoot_of_isUnit_derivative (Polynomial.monic_X_pow_sub_C u hn)
  have hder : AdjoinRoot.mk f f.derivative =
      algebraMap R S (n : R) * x ^ (n - 1) := by
    simp [f, Polynomial.derivative_X_pow, x, S]
  rw [hder]
  exact (hnu.map (algebraMap R S)).mul (hxunit.pow (n - 1))

private theorem exists_algHom_of_pi
    (R : Type u) [CommRing R] {I : Type v} [Finite I] (E : I → Type w)
    [∀ i, Field (E i)] [∀ i, Algebra R (E i)]
    (F : Type x) [Field F] [Algebra R F]
    (f : (∀ i, E i) →ₐ[R] F) :
    ∃ (i : I) (g : E i →ₐ[R] F), g.comp (Pi.evalAlgHom R E i) = f := by
  classical
  let _ := Fintype.ofFinite I
  have hsum : ∑ i : I, Pi.single i (1 : E i) = 1 := by
    ext i
    simp
  obtain ⟨i, hi⟩ : ∃ i : I, f (Pi.single i (1 : E i)) ≠ 0 := by
    by_contra! h
    have heq := congrArg f hsum
    simp only [map_sum, h, Finset.sum_const_zero, map_one] at heq
    exact zero_ne_one heq
  let π := Pi.evalAlgHom R E i
  have hπ : Function.Surjective π := Function.surjective_eval i
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker f.toRingHom := by
    intro z hz
    show f z = 0
    have hz' : z i = 0 := hz
    have hmul : z * Pi.single i (1 : E i) = 0 := by
      ext j
      by_cases hji : j = i
      · subst j; simp [hz']
      · simp [Pi.single_eq_of_ne hji]
    have heq := congrArg f hmul
    rw [map_mul, map_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_right hi
  let g := π.liftOfSurjective hπ f hker
  exact ⟨i, g, π.liftOfSurjective_comp hπ f hker⟩

private theorem formallyUnramified_integralClosure_of_etale_model
    (R : Type u) (K : Type v) (S : Type w) (E : Type x)
    [CommRing R] [Field K] [CommRing S] [Field E]
    [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R]
    [Algebra R S] [Algebra.Etale R S] [Module.Finite R S]
    [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    (f : (K ⊗[R] S) →ₐ[K] E) (hf : Function.Surjective f) :
    Algebra.FormallyUnramified R (integralClosure R E) := by
  obtain ⟨I, hI, F, hfield, halg, e, hF⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K (K ⊗[R] S)).mp inferInstance
  let (i : I) : Algebra R (F i) :=
    ((algebraMap K (F i)).comp (algebraMap R K)).toAlgebra
  have (i : I) : IsScalarTower R K (F i) := .of_algebraMap_eq fun _ => rfl
  obtain ⟨i, g, -⟩ := exists_algEquiv_of_surjective_pi K F E
    (f.comp e.symm.toAlgHom) (hf.comp e.symm.surjective)
  have : Algebra.FormallyUnramified R (integralClosure R (F i)) :=
    formallyUnramified_integralClosure_pi_of_etale R K S F
      ((Algebra.TensorProduct.comm R S K).trans (e.restrictScalars R)) i
  exact Algebra.FormallyUnramified.of_equiv (g.restrictScalars R).mapIntegralClosure

private theorem isUnramifiedWithRespectTo_of_adjoin_eq_top_of_pow_isUnit
    (A : Type u) (K : Type v) (E : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Algebra A E] [IsScalarTower A K E]
    (n : ℕ) (hn : n ≠ 0) (a : A) (ha : IsUnit a) (hna : IsUnit (n : A))
    (x : E) (hx : x ^ n = algebraMap A E a)
    (hgen : Algebra.adjoin K {x} = ⊤) :
    IsUnramifiedWithRespectTo A K E := by
  let p := Polynomial.X ^ n - Polynomial.C a
  let S := AdjoinRoot p
  have : Algebra.Etale A S := etale_adjoinRoot_X_pow_sub_C_of_isUnit n hn a ha hna
  have : Module.Finite A S := (AdjoinRoot.powerBasis'
    (Polynomial.monic_X_pow_sub_C a hn)).finite
  have hp : Polynomial.eval₂ (algebraMap A E) x p = 0 := by
    simp [p, hx]
  let g : S →ₐ[A] E := AdjoinRoot.liftAlgHom p (Algebra.ofId A E) x hp
  let f : (K ⊗[A] S) →ₐ[K] E :=
    Algebra.TensorProduct.lift (Algebra.ofId K E) g fun _ _ => .all _ _
  have hf : Function.Surjective f := by
    apply f.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le_iff.mpr
    apply Set.singleton_subset_iff.mpr
    refine ⟨1 ⊗ₜ[A] AdjoinRoot.root p, ?_⟩
    show (Algebra.ofId K E) 1 * g (AdjoinRoot.root p) = x
    rw [map_one, one_mul]
    exact AdjoinRoot.liftAlgHom_root p (Algebra.ofId A E) x hp
  have : Algebra.FormallyUnramified A (integralClosure A E) :=
    formallyUnramified_integralClosure_of_etale_model A K S E f hf
  exact isUnramifiedWithRespectTo_of_formallyUnramified_integralClosure A K E

private theorem adjoin_eq_top_of_surjective_tensorProduct
    (K : Type u) (L : Type v) (E : Type w) (F : Type x)
    [CommRing K] [CommRing L] [CommRing E] [CommRing F]
    [Algebra K L] [Algebra K E] [Algebra L F]
    (x : E) (hx : Algebra.adjoin K {x} = ⊤)
    (f : (L ⊗[K] E) →ₐ[L] F) (hf : Function.Surjective f) :
    Algebra.adjoin L {f (1 ⊗ₜ[K] x)} = ⊤ := by
  have h := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := L) {x} hx
  have heq := Algebra.adjoin_image L f ((fun x : E => (1 : L) ⊗ₜ[K] x) '' {x})
  rw [h, Algebra.map_top, f.range_eq_top.mpr hf] at heq
  simpa only [Set.image_singleton] using heq

private theorem adjoin_div_algebraMap_eq
    (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E]
    (x : E) (c : K) (hc : c ≠ 0) :
    Algebra.adjoin K {x / algebraMap K E c} = Algebra.adjoin K {x} := by
  apply le_antisymm
  · apply Algebra.adjoin_le_iff.mpr
    apply Set.singleton_subset_iff.mpr
    rw [div_eq_mul_inv, ← map_inv₀]
    exact (Algebra.adjoin K {x}).mul_mem (Algebra.subset_adjoin (Set.mem_singleton x))
      ((Algebra.adjoin K {x}).algebraMap_mem c⁻¹)
  · apply Algebra.adjoin_le_iff.mpr
    apply Set.singleton_subset_iff.mpr
    have hxc : x = x / algebraMap K E c * algebraMap K E c :=
      (div_mul_cancel₀ x (by simpa only [map_zero] using (algebraMap K E).injective.ne hc)).symm
    have hmem := (Algebra.adjoin K {x / algebraMap K E c}).mul_mem
      (Algebra.subset_adjoin (Set.mem_singleton _))
      ((Algebra.adjoin K {x / algebraMap K E c}).algebraMap_mem c)
    rwa [← hxc] at hmem

private theorem isTamelyRamifiedWithRespectTo_of_ringChar_eq_zero
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    (h : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0) :
    IsTamelyRamifiedWithRespectTo A K L := by
  let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have : CharZero (A ⧸ IsLocalRing.maximalIdeal A) :=
    (CharP.ringChar_zero_iff_CharZero _).mp h
  intro m hm hlo
  have := hm
  have := hlo
  let _ := Ideal.Quotient.field m
  have : Algebra.IsIntegral (A ⧸ IsLocalRing.maximalIdeal A)
      (integralClosure A L ⧸ m) := Algebra.IsIntegral.tower_top A
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField
    (K := A ⧸ IsLocalRing.maximalIdeal A) (L := integralClosure A L ⧸ m), Or.inl h⟩

private theorem isUnramifiedWithRespectTo_of_adjoin_eq_top_of_pow_eq_mul_pow
    (A : Type u) (K : Type v) (E : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Algebra A E] [IsScalarTower A K E]
    (n : ℕ) (hn : n ≠ 0) (a : A) (ha : IsUnit a) (hna : IsUnit (n : A))
    (x : E) (c : K) (hc : c ≠ 0)
    (hx : x ^ n = algebraMap A E a * (algebraMap K E c) ^ n)
    (hgen : Algebra.adjoin K {x} = ⊤) :
    IsUnramifiedWithRespectTo A K E := by
  apply isUnramifiedWithRespectTo_of_adjoin_eq_top_of_pow_isUnit A K E n hn a ha hna
    (x / algebraMap K E c)
  · rw [div_pow, hx, mul_div_cancel_right₀ _ (pow_ne_zero _
      (by simpa only [map_zero] using (algebraMap K E).injective.ne hc))]
  · rw [adjoin_div_algebraMap_eq K E x c hc, hgen]

private theorem isUnramifiedWithRespectTo_of_surjective_tensorProduct
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K' : Type y)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K']
    [Algebra A B] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Module.Finite K K'] [Algebra.IsSeparable K K']
    (E : Type*) [Field E] [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Module.Finite L E] [Algebra.IsSeparable L E]
    (q : (L ⊗[K] K') →ₐ[L] E) (hq : Function.Surjective q)
    (h : IsUnramifiedWithRespectTo A K K') :
    IsUnramifiedWithRespectTo B L E := by
  let A' := integralClosure A K'
  let C := B ⊗[A] A'
  have : Algebra.Etale A A' := (isUnramifiedWithRespectTo_iff_etale A K K').mp h
  have : Module.Finite A A' := IsIntegralClosure.finite A K K' A'
  have : IsLocalization (Algebra.algebraMapSubmonoid A' (nonZeroDivisors A)) K' :=
    IsIntegralClosure.isLocalization A K K' A'
  have : Algebra.IsPushout A A' K K' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors A) K A' K'
  have : Algebra.IsPushout A K A' K' := (Algebra.IsPushout.comm A A' K K').mp this
  let eK : (K ⊗[A] A') ≃ₐ[K] K' := Algebra.IsPushout.equiv A K A' K'
  let eL : (L ⊗[A] A') ≃ₐ[L] L ⊗[K] K' :=
    (Algebra.TensorProduct.cancelBaseChange A K L L A').symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := L) (A₁ := L)) eK)
  let eC : (L ⊗[B] C) ≃ₐ[L] L ⊗[K] K' :=
    (Algebra.TensorProduct.cancelBaseChange A B L L A').trans eL
  have : Algebra.FormallyUnramified B (integralClosure B E) :=
    formallyUnramified_integralClosure_of_etale_model B L C E
      (q.comp eC.toAlgHom) (hq.comp eC.surjective)
  exact isUnramifiedWithRespectTo_of_formallyUnramified_integralClosure B L E

private theorem lift_field_factor_through_finite_separable_extension
    (K : Type u) (L : Type v) (K' : Type w) (F : Type x) (E : Type y)
    [Field K] [Field L] [Field K'] [Field F] [Field E]
    [Algebra K L] [Algebra K K'] [Algebra K F] [Algebra K' F]
    [IsScalarTower K K' F] [Module.Finite K' F] [Algebra.IsSeparable K' F]
    [Algebra L E]
    (q : (L ⊗[K] K') →ₐ[L] E) (hq : Function.Surjective q) :
    ∃ (E' : Type (max u v w x y)) (_ : Field E')
      (_ : Algebra E E') (_ : Algebra L E') (_ : IsScalarTower L E E')
      (_ : Module.Finite E E') (_ : Algebra.IsSeparable E E')
      (q' : (L ⊗[K] F) →ₐ[L] E'),
      Function.Surjective q' ∧
        ∀ (l : L) (a : K'),
          q' (l ⊗ₜ[K] algebraMap K' F a) = algebraMap E E' (q (l ⊗ₜ[K] a)) := by
  classical
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L E := .of_algebraMap_eq fun _ => rfl
  let q₀ : K' →ₐ[K] E :=
    (q.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let : Algebra K' E := q₀.toAlgebra
  have : IsScalarTower K K' E := .of_algebraMap_eq fun a => (q₀.commutes a).symm
  let T := E ⊗[K'] F
  let g : (L ⊗[K] F) →ₐ[L] T :=
    Algebra.TensorProduct.lift (Algebra.ofId L T)
      (Algebra.TensorProduct.includeRight.restrictScalars K) fun _ _ => .all _ _
  have hg : Function.Surjective g := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero g⟩
    | add z z' hz hz' =>
      obtain ⟨a, rfl⟩ := hz
      obtain ⟨b, rfl⟩ := hz'
      exact ⟨a + b, map_add g a b⟩
    | tmul e f =>
      obtain ⟨a, rfl⟩ := hq e
      induction a using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add a b ha hb =>
        obtain ⟨a', ha'⟩ := ha
        obtain ⟨b', hb'⟩ := hb
        exact ⟨a' + b', by simp [ha', hb', TensorProduct.add_tmul]⟩
      | tmul l a =>
        refine ⟨l ⊗ₜ[K] (algebraMap K' F a * f), ?_⟩
        have hqla : q (l ⊗ₜ[K] a) = algebraMap L E l * algebraMap K' E a :=
          algHom_tmul_eq_mul q l a
        rw [hqla]
        show (algebraMap L E l ⊗ₜ[K'] (1 : F)) *
          (1 ⊗ₜ[K'] (algebraMap K' F a * f)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_comm (algebraMap K' E a)]
  have hcompat (l : L) (a : K') :
      g (l ⊗ₜ[K] algebraMap K' F a) = algebraMap E T (q (l ⊗ₜ[K] a)) := by
    show (algebraMap L E l ⊗ₜ[K'] (1 : F)) * (1 ⊗ₜ[K'] algebraMap K' F a) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← mul_one (algebraMap K' F a), ← Algebra.smul_def,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    show _ = q (l ⊗ₜ[K] a) ⊗ₜ[K'] (1 : F)
    congr 1
    show q (1 ⊗ₜ[K] a) * algebraMap L E l = _
    rw [algHom_tmul_eq_mul q l a, mul_comm]
  have : Algebra.Etale K' F := etale_of_finite_separable K' F
  obtain ⟨M, hfield, halg, hfinite, hsep, p, hp⟩ :=
    exists_surjective_algHom_field_of_etale.{_, _, max u v w} E T
  let : Algebra L M := ((algebraMap E M).comp (algebraMap L E)).toAlgebra
  have : IsScalarTower L E M := .of_algebraMap_eq fun _ => rfl
  let q' := (p.restrictScalars L).comp g
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, q', hp.comp hg, ?_⟩
  intro l a
  show p (g (l ⊗ₜ[K] algebraMap K' F a)) = _
  rw [hcompat, p.commutes]

private theorem monogenic_unit_uniformizer_root_is_tame
    (B : Type u) (L : Type v) (E : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field E] [Algebra B L] [IsFractionRing B L]
    [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Module.Finite L E] [Algebra.IsSeparable L E]
    (theta : B) (htheta : Irreducible theta)
    (unit : Bˣ) (e t : ℕ) (he : 0 < e) (heunit : IsUnit (e : B))
    (root : E)
    (hroot : root ^ e = algebraMap B E (unit : B) * (algebraMap B E theta) ^ t)
    (hgen : Algebra.adjoin L {root} = ⊤) :
    IsTamelyRamifiedWithRespectTo B L E := by
  classical
  have hthetaL : algebraMap B L theta ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective B L).ne htheta.ne_zero
  by_cases heone : e = 1
  · apply isTamelyRamifiedWithRespectTo_of_isUnramifiedWithRespectTo B L E
    apply isUnramifiedWithRespectTo_of_adjoin_eq_top_of_pow_eq_mul_pow B L E e
      (by omega) unit unit.isUnit heunit root ((algebraMap B L theta) ^ t)
      (pow_ne_zero _ hthetaL) _ hgen
    simpa only [heone, pow_one, map_pow, ← IsScalarTower.algebraMap_apply B L E] using hroot
  have he2 : 2 ≤ e := by omega
  have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly L theta e)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible L theta e he htheta⟩
  let F := Stacks.KummerExtension.K1 L theta e
  let D := Stacks.KummerExtension.A1 L theta e
  have hcop : ringChar (B ⧸ IsLocalRing.maximalIdeal B) = 0 ∨
      Nat.Coprime (ringChar (B ⧸ IsLocalRing.maximalIdeal B)) e := by
    by_cases hchar : ringChar (B ⧸ IsLocalRing.maximalIdeal B) = 0
    · exact Or.inl hchar
    · right
      have hne : (e : B ⧸ IsLocalRing.maximalIdeal B) ≠ 0 := by
        simpa only [map_natCast] using
          (heunit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))).ne_zero
      exact ((CharP.char_is_prime_or_zero (B ⧸ IsLocalRing.maximalIdeal B)
        (ringChar (B ⧸ IsLocalRing.maximalIdeal B))).resolve_right hchar).coprime_iff_not_dvd.mpr
        (fun h => hne ((CharP.cast_eq_zero_iff _ _ e).mpr h))
  have : Algebra.IsSeparable L F := Stacks.KummerExtension.isSeparable_K1 L theta e he2 htheta hcop
  have : IsDiscreteValuationRing D := Stacks.KummerExtension.isDiscreteValuationRing_A1 L theta e
    he2 htheta
  have : IsFractionRing D F := integralClosure.isFractionRing_of_finite_extension L F
  have : Algebra.Etale L E := etale_of_finite_separable L E
  obtain ⟨M, hfield, halg, hfinite, hsep, q, hq⟩ :=
    exists_surjective_algHom_field_of_etale.{_, _, u} F (F ⊗[L] E)
  let : Algebra L M := ((algebraMap F M).comp (algebraMap L F)).toAlgebra
  have : IsScalarTower L F M := .of_algebraMap_eq fun _ => rfl
  let : Algebra B M := ((algebraMap F M).comp (algebraMap B F)).toAlgebra
  have : IsScalarTower B F M := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B D M := .of_algebraMap_eq fun b => by
    show algebraMap F M (algebraMap B F b) =
      algebraMap F M (algebraMap D F (algebraMap B D b))
    rw [← IsScalarTower.algebraMap_apply B D F]
  let j : E →ₐ[L] M :=
    (q.restrictScalars L).comp Algebra.TensorProduct.includeRight
  have hjgen : Algebra.adjoin F {j root} = ⊤ :=
    adjoin_eq_top_of_surjective_tensorProduct L F E M root hgen q hq
  let y : F := Stacks.KummerExtension.piRoot L theta e
  have hy : y ^ e = algebraMap B F theta := piRoot_pow_eq_algebraMap L theta e
  have hyne : y ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hy
    exact hthetaL ((algebraMap L F).injective (by
      simpa only [map_zero, ← IsScalarTower.algebraMap_apply B L F] using hy.symm))
  have hjB (b : B) : j (algebraMap B E b) = algebraMap B M b := by
    rw [IsScalarTower.algebraMap_apply B L E, j.commutes]
    show algebraMap F M (algebraMap L F (algebraMap B L b)) = _
    rw [← IsScalarTower.algebraMap_apply B L F,
      ← IsScalarTower.algebraMap_apply B F M]
  have hjroot : (j root) ^ e = algebraMap D M (algebraMap B D unit) *
      (algebraMap F M (y ^ t)) ^ e := by
    have hpow : (algebraMap F M (y ^ t)) ^ e = (algebraMap B M theta) ^ t := by
      rw [← map_pow, ← pow_mul, Nat.mul_comm t e, pow_mul, hy, map_pow,
        ← IsScalarTower.algebraMap_apply B F M]
    rw [hpow, ← IsScalarTower.algebraMap_apply B D M, ← map_pow,
      hroot, map_mul, map_pow, hjB, hjB]
  have hM : IsUnramifiedWithRespectTo D F M :=
    isUnramifiedWithRespectTo_of_adjoin_eq_top_of_pow_eq_mul_pow D F M e
      (by omega) (algebraMap B D unit) (unit.isUnit.map (algebraMap B D))
      (by simpa only [map_natCast] using heunit.map (algebraMap B D))
      (j root) (y ^ t) (pow_ne_zero _ hyne) hjroot hjgen
  apply ((isTamelyRamifiedWithRespectTo_tfae_hasUnramifiedKummerOverfield
    B L E theta htheta).out 2 1).mp
  refine ⟨e, he, ?_, M, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨j⟩, hM⟩
  · simpa only [map_natCast] using heunit.map (IsLocalRing.residue B)
  · intro z
    rfl

private theorem isTamelyRamifiedWithRespectTo_of_unramified_baseChange_tower
    (B : Type*) (L : Type*) (T : Type*) (M : Type*)
    (A₀ : Type*) (K₀ : Type*) (F : Type*)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    [Field L] [Field T] [Field M] [Field K₀] [Field F]
    [Algebra B L] [IsFractionRing B L]
    [Algebra L T] [Algebra B T] [IsScalarTower B L T]
    [Algebra T M] [Algebra L M] [IsScalarTower L T M]
    [Algebra B M] [IsScalarTower B L M] [IsScalarTower B T M]
    [Module.Finite L T] [Algebra.IsSeparable L T]
    [Module.Finite T M] [Algebra.IsSeparable T M]
    [Algebra A₀ K₀] [IsFractionRing A₀ K₀]
    [Algebra K₀ T] [Algebra A₀ T] [IsScalarTower A₀ K₀ T]
    [Algebra K₀ F] [Algebra A₀ F] [IsScalarTower A₀ K₀ F]
    [Module.Finite K₀ F] [Algebra.IsSeparable K₀ F]
    (hint : ∀ a : A₀, IsIntegral B (algebraMap A₀ T a))
    (q : (T ⊗[K₀] F) →ₐ[T] M) (hq : Function.Surjective q)
    (hT : IsTamelyRamifiedWithRespectTo B L T)
    (hF : IsUnramifiedWithRespectTo A₀ K₀ F) :
    letI : Module.Finite L M := Module.Finite.trans T M
    letI : Algebra.IsSeparable L M := Algebra.IsSeparable.trans L T M
    IsTamelyRamifiedWithRespectTo B L M := by
  apply isTamelyRamified_tower B L T M hT
  intro m hm
  let C := integralClosure B T
  have : IsDedekindDomain C := integralClosure.isDedekindDomain B L T
  have : Module.Finite B C := IsIntegralClosure.finite B L T C
  have : m.IsMaximal := hm
  have : m.IsPrime := hm.isPrime
  have : IsFractionRing C T := integralClosure.isFractionRing_of_finite_extension L T
  let R := Localization.AtPrime m
  let : Algebra R T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ m.primeCompl
      (nonZeroDivisors C) m.primeCompl_le_nonZeroDivisors
  let : Algebra R M := ((algebraMap T M).comp (algebraMap R T)).toAlgebra
  have : IsScalarTower R T M := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C R T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
  have : IsFractionRing R T :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl R T
  have : m.LiesOver (IsLocalRing.maximalIdeal B) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under B m)).symm
  have : FaithfulSMul B T := (faithfulSMul_iff_algebraMap_injective B T).mpr <| by
    intro b c h
    apply IsFractionRing.injective B L
    apply (algebraMap L T).injective
    simpa only [IsScalarTower.algebraMap_apply B L T] using h
  have : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr <| by
    intro b c h
    exact FaithfulSMul.algebraMap_injective B T (congrArg Subtype.val h)
  have hmne : m ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field B) m
  have : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hmne R
  let f : A₀ →+* C := (algebraMap A₀ T).codRestrict C hint
  let : Algebra A₀ C := f.toAlgebra
  have : IsScalarTower A₀ C T := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₀ R T := .of_algebraMap_eq fun a => by
    show algebraMap A₀ T a = algebraMap R T (algebraMap C R (f a))
    rw [← IsScalarTower.algebraMap_apply C R T]
    rfl
  exact isTamelyRamifiedWithRespectTo_of_isUnramifiedWithRespectTo R T M
    (isUnramifiedWithRespectTo_of_surjective_tensorProduct A₀ R K₀ T F M q hq hF)

private theorem factor_tensorProduct_through_intermediate_field
    (K : Type u) (L : Type v) (K₀ : Type w) (F : Type x) (E : Type y)
    [Field K] [Field L] [Field K₀] [Field F] [Field E]
    [Algebra K L] [Algebra K K₀] [Algebra K F] [Algebra K₀ F]
    [IsScalarTower K K₀ F] [Module.Finite K K₀] [Algebra.IsSeparable K K₀]
    [Algebra L E]
    (q : (L ⊗[K] F) →ₐ[L] E) (hq : Function.Surjective q) :
    ∃ (T : Type (max v w)) (_ : Field T)
      (_ : Algebra L T) (_ : Algebra K T) (_ : IsScalarTower K L T)
      (_ : Algebra K₀ T) (_ : IsScalarTower K K₀ T)
      (_ : Algebra T E) (_ : IsScalarTower L T E)
      (_ : Module.Finite L T) (_ : Algebra.IsSeparable L T)
      (p : (L ⊗[K] K₀) →ₐ[L] T) (r : (T ⊗[K₀] F) →ₐ[T] E),
      Function.Surjective p ∧ Function.Surjective r ∧
      ∀ a : K₀, p (1 ⊗ₜ[K] a) = algebraMap K₀ T a := by
  classical
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L E := .of_algebraMap_eq fun _ => rfl
  let qF : F →ₐ[K] E := (q.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let fK₀ : K₀ →ₐ[K] E := qF.comp (IsScalarTower.toAlgHom K K₀ F)
  let f : (L ⊗[K] K₀) →ₐ[L] E :=
    Algebra.TensorProduct.lift (Algebra.ofId L E) fK₀ fun _ _ => .all _ _
  have : Algebra.Etale K K₀ := etale_of_finite_separable K K₀
  obtain ⟨n, H, hfield, halg, hfinite, hsep, hn, ⟨d⟩⟩ :=
    exists_algEquiv_pi_field_of_etale L (L ⊗[K] K₀)
  obtain ⟨i, g, hg⟩ := exists_algHom_of_pi L H E (f.comp d.symm.toAlgHom)
  let T := H i
  let p : (L ⊗[K] K₀) →ₐ[L] T := (Pi.evalAlgHom L H i).comp d.toAlgHom
  have hp : Function.Surjective p := (Function.surjective_eval i).comp d.surjective
  have hgp : g.comp p = f := by
    apply AlgHom.ext
    intro z
    have h := AlgHom.congr_fun hg (d z)
    simpa only [p, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h
  let : Algebra K T := ((algebraMap L T).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L T := .of_algebraMap_eq fun _ => rfl
  let p₀ : K₀ →ₐ[K] T := (p.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let : Algebra K₀ T := p₀.toAlgebra
  have : IsScalarTower K K₀ T := .of_algebraMap_eq fun a => (p₀.commutes a).symm
  let : Algebra T E := g.toAlgebra
  have : IsScalarTower L T E := .of_algebraMap_eq fun a => (g.commutes a).symm
  let : Algebra K₀ E := fK₀.toAlgebra
  have : IsScalarTower K₀ T E := .of_algebraMap_eq fun a => by
    show fK₀ a = g (p (1 ⊗ₜ[K] a))
    rw [← AlgHom.comp_apply, hgp]
    simp [f]
  let qF₀ : F →ₐ[K₀] E := { qF.toRingHom with commutes' := fun _ => rfl }
  let r : (T ⊗[K₀] F) →ₐ[T] E :=
    Algebra.TensorProduct.lift (Algebra.ofId T E) qF₀ fun _ _ => .all _ _
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨a, rfl⟩ := hq z
    induction a using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by simp [ha', hb']⟩
    | tmul l a =>
      refine ⟨algebraMap L T l ⊗ₜ[K₀] a, ?_⟩
      show g (algebraMap L T l) * q (1 ⊗ₜ[K] a) = q (l ⊗ₜ[K] a)
      rw [g.commutes, algHom_tmul_eq_mul q l a]
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    p, r, hp, hr, fun _ => rfl⟩

private theorem tame_field_factor_of_unramified_kummer
    (A : Type*) (B : Type*) (K : Type*) (L : Type*) (K₀ : Type*) (F : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₀] [Field F]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K₀] [Algebra A K₀] [IsScalarTower A K K₀]
    [Module.Finite K K₀] [Algebra.IsSeparable K K₀]
    [Algebra K F] [Algebra K₀ F] [IsScalarTower K K₀ F]
    [Module.Finite K₀ F] [Algebra.IsSeparable K₀ F]
    [IsDiscreteValuationRing (integralClosure A K₀)]
    [IsFractionRing (integralClosure A K₀) K₀]
    (π : A) (hπ : Irreducible π) (e : ℕ) (he : 0 < e) (heunit : IsUnit (e : A))
    (x : K₀) (hx : x ^ e = algebraMap A K₀ π)
    (hxgen : Algebra.adjoin K {x} = ⊤)
    (hF : IsUnramifiedWithRespectTo (integralClosure A K₀) K₀ F)
    (E : Type*) [Field E] [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Module.Finite L E] [Algebra.IsSeparable L E]
    (q : (L ⊗[K] F) →ₐ[L] E) (hq : Function.Surjective q) :
    IsTamelyRamifiedWithRespectTo B L E := by
  obtain ⟨T, hfield, halgL, halgK, htLK, halgK₀, htKK₀, halgE, htLTE,
    hfinite, hsep, p, r, hp, hr, hpK₀⟩ :=
    factor_tensorProduct_through_intermediate_field K L K₀ F E q hq
  let : Algebra B T := ((algebraMap L T).comp (algebraMap B L)).toAlgebra
  have : IsScalarTower B L T := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B T E := .of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B L E, IsScalarTower.algebraMap_apply L T E]
    rfl
  have : Module.Finite T E := Module.Finite.of_restrictScalars_finite L T E
  have : Algebra.IsSeparable T E := Algebra.isSeparable_tower_top_of_isSeparable L T E
  let : Algebra A T := ((algebraMap K T).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K T := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A L T := .of_algebraMap_eq fun a => by
    show algebraMap K T (algebraMap A K a) = algebraMap L T (algebraMap A L a)
    rw [IsScalarTower.algebraMap_apply K L T, ← IsScalarTower.algebraMap_apply A K L]
  have : IsScalarTower A B T := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A L T, IsScalarTower.algebraMap_apply A B L]
    rfl
  have : IsScalarTower A K₀ T := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K T, IsScalarTower.algebraMap_apply K K₀ T,
      ← IsScalarTower.algebraMap_apply A K K₀]
  let A₀ := integralClosure A K₀
  have : IsFractionRing A₀ K₀ := integralClosure.isFractionRing_of_finite_extension K K₀
  have hT : IsTamelyRamifiedWithRespectTo B L T := by
    obtain ⟨theta, htheta⟩ := IsDiscreteValuationRing.exists_irreducible B
    have hπB : algebraMap A B π ≠ 0 := by
      simpa only [map_zero] using (FaithfulSMul.algebraMap_injective A B).ne hπ.ne_zero
    obtain ⟨t, unit, hunit⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπB htheta
    apply monogenic_unit_uniformizer_root_is_tame B L T theta htheta unit e t he
      (by simpa only [map_natCast] using heunit.map (algebraMap A B))
      (algebraMap K₀ T x)
    · rw [← map_pow, hx, ← IsScalarTower.algebraMap_apply A K₀ T,
        IsScalarTower.algebraMap_apply A B T, hunit, map_mul, map_pow]
    · rw [← hpK₀ x]
      exact adjoin_eq_top_of_surjective_tensorProduct K L K₀ T x hxgen p hp
  have hint (a : A₀) : IsIntegral B (algebraMap A₀ T a) := by
    have ha : IsIntegral A (algebraMap A₀ T a) :=
      a.property.map (IsScalarTower.toAlgHom A K₀ T)
    exact ha.tower_top
  exact isTamelyRamifiedWithRespectTo_of_unramified_baseChange_tower B L T E A₀ K₀ F
    hint r hr hT hF

private theorem tame_field_factor_after_baseChange
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K' : Type y)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K']
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Module.Finite K K'] [Algebra.IsSeparable K K']
    (E : Type (max u v w x y)) [Field E]
    [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Module.Finite L E] [Algebra.IsSeparable L E]
    (q : (L ⊗[K] K') →ₐ[L] E) (hq : Function.Surjective q)
    (htame : IsTamelyRamifiedWithRespectTo A K K') :
    IsTamelyRamifiedWithRespectTo B L E := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, he, heunit, hcover⟩ :=
    ((isTamelyRamifiedWithRespectTo_tfae_hasUnramifiedKummerOverfield
      A K K' π hπ).out 1 2).mp htame
  have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π e)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K π e he hπ⟩
  let K₀ := Stacks.KummerExtension.K1 K π e
  let A₀ := Stacks.KummerExtension.A1 K π e
  obtain ⟨F, hfield, halgK₀, halgK, htKK₀, halgA, htAK₀, hfinite, hsep,
    hDVR, halgA₀, hcompat, ⟨j⟩, hF⟩ := hcover
  have halgA₀_eq : halgA₀ = A₀.toAlgebra (α := F) :=
    Algebra.algebra_ext _ _ hcompat
  subst halgA₀
  have heA : IsUnit (e : A) := (isUnit_map_iff (IsLocalRing.residue A) _).mp
    (by simpa only [map_natCast] using heunit)
  have hπK : algebraMap A K π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
  have : Algebra.Etale K K₀ :=
    etale_adjoinRoot_X_pow_sub_C_of_isUnit e (by omega) (algebraMap A K π)
      (isUnit_iff_ne_zero.mpr hπK) (by simpa only [map_natCast] using heA.map (algebraMap A K))
  have : Algebra.IsSeparable K K₀ := Algebra.FormallyUnramified.isSeparable K K₀
  have : Module.Finite K F := Module.Finite.trans K₀ F
  have : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K K₀ F
  have : IsFractionRing A₀ K₀ := integralClosure.isFractionRing_of_finite_extension K K₀
  let : Algebra K' F := j.toAlgebra
  have : IsScalarTower K K' F := .of_algebraMap_eq fun k => (j.commutes k).symm
  have : Module.Finite K' F := Module.Finite.of_restrictScalars_finite K K' F
  have : Algebra.IsSeparable K' F := Algebra.isSeparable_tower_top_of_isSeparable K K' F
  obtain ⟨E', hfield', halgE, halgL, htLE, hfinite', hsep', q', hq', _⟩ :=
    lift_field_factor_through_finite_separable_extension K L K' F E q hq
  let : Algebra B E' := ((algebraMap E E').comp (algebraMap B E)).toAlgebra
  have : IsScalarTower B E E' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B L E' := .of_algebraMap_eq fun b => by
    show algebraMap E E' (algebraMap B E b) = algebraMap L E' (algebraMap B L b)
    rw [IsScalarTower.algebraMap_apply B L E, ← IsScalarTower.algebraMap_apply L E E']
  have : Module.Finite L E' := Module.Finite.trans E E'
  have : Algebra.IsSeparable L E' := Algebra.IsSeparable.trans L E E'
  have hE' : IsTamelyRamifiedWithRespectTo B L E' := by
    apply tame_field_factor_of_unramified_kummer A B K L K₀ F π hπ e he heA
      (Stacks.KummerExtension.piRoot K π e) _ AdjoinRoot.adjoinRoot_eq_top hF E' q' hq'
    exact piRoot_pow_eq_algebraMap K π e
  exact isTamelyRamified_of_isTamelyRamified_tower B L E E' hE'

/-- **Stacks 0EXY.** A finite separable field extension remains a finite product of fields after
scalar extension along an extension of discrete valuation rings. If the original extension is
unramified, respectively tamely ramified, then every resulting field factor has the same
property over the larger discrete valuation ring. -/
@[stacks 0EXY,
  sga "1 XIII 2.0.3" "tame after DVR extension",
  sga "1 XIII 2.0.2" "⇒: tameness ascends"]
theorem exists_algEquiv_pi_field_and_ramification_goes_up
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K' : Type y)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K']
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Module.Finite K K'] [Algebra.IsSeparable K K'] :
    ∃ (n : ℕ) (E : Fin n → Type (max u v w x y))
        (_ : ∀ i, Field (E i))
        (_ : ∀ i, Algebra L (E i))
        (_ : ∀ i, Algebra B (E i))
        (_ : ∀ i, IsScalarTower B L (E i))
        (_ : ∀ i, Module.Finite L (E i))
        (_ : ∀ i, Algebra.IsSeparable L (E i)),
      0 < n ∧
        Nonempty ((L ⊗[K] K') ≃ₐ[L] ∀ i, E i) ∧
        (IsUnramifiedWithRespectTo A K K' →
          ∀ i, IsUnramifiedWithRespectTo B L (E i)) ∧
        (IsTamelyRamifiedWithRespectTo A K K' →
          ∀ i, IsTamelyRamifiedWithRespectTo B L (E i)) := by
  obtain ⟨n, E, hfield, halgL, halgB, htower, hfinite, hsep, hn, he, hu⟩ :=
    exists_algEquiv_pi_field_and_unramified_goes_up A B K L K'
  refine ⟨n, E, hfield, halgL, halgB, htower, hfinite, hsep, hn, he, hu, ?_⟩
  intro htame i
  obtain ⟨d⟩ := he
  let q : (L ⊗[K] K') →ₐ[L] E i := (Pi.evalAlgHom L E i).comp d.toAlgHom
  exact tame_field_factor_after_baseChange A B K L K' (E i) q
    ((Function.surjective_eval i).comp d.surjective) htame

end

end IsDiscreteValuationRing
