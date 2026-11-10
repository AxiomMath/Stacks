module

public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.FlatRelation
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.PresentationKernel

/-!
# Comparing the polynomial presentations of two divided power envelopes

Let `φ : (B, I, γ) → (B', I', γ')` be a morphism of divided power rings whose induced map
`B / I → B' / I'` is flat, and let `J ⊆ B` be an ideal containing `I`. Changing coefficients
along `φ` carries the divided power polynomial algebra on a set `T` over `B` to the one over
`B'`, and this file identifies the image of the presentation ideal of
`Crystalline.kernelPresentationIdeal` with the presentation ideal over `B'`.

That identification is the technical heart of the base-change theorem for divided power
envelopes: the two envelopes are the quotients of the two polynomial algebras by these ideals,
so matching the ideals matches the envelopes.

## Main definitions

* `Crystalline.polynomialCoefficientChange` is the coefficient-change homomorphism between the
  two divided power polynomial algebras.
* `Crystalline.dividedPowerEnvelopeBaseChangeMap` is the canonical divided power morphism
  between the two envelopes, obtained from the universal property.

## Main results

* `Crystalline.sourceKernel_map_le_targetKernel` and
  `Crystalline.targetKernel_le_sourceKernel_map` are the two inclusions which together say that
  the extension of the source presentation ideal is the target presentation ideal.
* `Crystalline.polynomialCoefficientChange_isDPMorphism` — coefficient change respects the
  divided powers.

## Implementation notes

Flatness enters only through `Ideal.flat_relation_decomposition`: a relation among the
images `φ (f t)` with constant term in `I'` is, modulo `I'`, a `B'`-combination of relations
among the `f t` with constant term in `I`. This is the equational criterion for flatness of
`B' / I'` over `B / I`,
and it is what lets a generator of the target presentation ideal be rewritten in terms of
generators coming from the source.

Coefficient change is identified with the unique divided power morphism out of the divided
power polynomial algebra determined by its values on coefficients and on variables; comparing
the two descriptions is what makes it a divided power morphism rather than merely a ring
homomorphism.

## References

* [Stacks Project, Tag 07HE](https://stacks.math.columbia.edu/tag/07HE)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Crystalline

open DividedPowers

private lemma dividedPowerPolynomial_embed_mem_ideal
    (B : DividedPowerRing.{u}) (T : Type u) (m : T →₀ B) :
    DividedPowerAlgebra.embed B (T →₀ B) m ∈
      dividedPowerPolynomialIdeal B.ideal T := by
  apply Ideal.mem_sup_right
  change (dividedPowerPolynomialAugmentation B T).toRingHom
    (DividedPowerAlgebra.embed B (T →₀ B) m) = 0
  simp [dividedPowerPolynomialAugmentation,
    DividedPowerAlgebra.lift_embed_apply]

private lemma dividedPowerPolynomial_embed_single
    (B : DividedPowerRing.{u}) (T : Type u) (t : T) (a : B) :
    DividedPowerAlgebra.embed B (T →₀ B) (Finsupp.single t a) =
      algebraMap B (DividedPowerAlgebra B (T →₀ B)) a * dividedPowerPolynomialVariable B t := by
  rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def]
  rfl

private lemma dividedPowers_dpow_finset_sum_mem
    {A : Type u} {ι : Type v} [CommRing A]
    (I K : Ideal A) (δ : DividedPowers I) (s : Finset ι) (x : ι → A)
    (hI : ∀ i ∈ s, x i ∈ I)
    (hK : ∀ i ∈ s, ∀ n : ℕ, n ≠ 0 → δ.dpow n (x i) ∈ K)
    {n : ℕ} (hn : n ≠ 0) : δ.dpow n (∑ i ∈ s, x i) ∈ K := by
  classical
  rw [δ.dpow_sum hI]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain ⟨i, hi, hn_i⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rwa [Finset.sum_count_of_mem_sym hk] : ∑ i ∈ s, Multiset.count i k ≠ 0)
  rw [← Finset.mul_prod_erase s
    (fun j => δ.dpow (Multiset.count j k) (x j)) hi]
  exact K.mul_mem_right _ (hK i hi _ hn_i)

private theorem setIndexedDividedPowerPolynomial_dpow_embed
    (B : DividedPowerRing.{u}) (T : Type u) (n : ℕ) (m : T →₀ B) :
    (setIndexedDividedPowerPolynomialDividedPowers
      B T).dpow n (DividedPowerAlgebra.embed B (T →₀ B) m) = DividedPowerAlgebra.dp B n m := by
  classical
  let δ := setIndexedDividedPowerPolynomialDividedPowers B T
  induction m using Finsupp.induction generalizing n with
  | zero =>
      cases n with
      | zero =>
          rw [δ.dpow_zero (dividedPowerPolynomial_embed_mem_ideal B T 0)]
          simp [DividedPowerAlgebra.dp_null]
      | succ n =>
          simpa [δ, DividedPowerAlgebra.embed, DividedPowerAlgebra.dp_null] using
            δ.dpow_mul (n := n + 1) (a := 0) (x := 0) (Ideal.zero_mem _)
  | @single_add i a m hi ha ih =>
      let x := dividedPowerPolynomialVariable B i
      have hx : x ∈ dividedPowerPolynomialIdeal B.ideal T := variable_mem_polynomialIdeal B i
      have hvar (j : ℕ) : δ.dpow j x =
          DividedPowerAlgebra.dp B j (Finsupp.single i 1) := by
        simpa [δ, x, dividedPowerPolynomialVariableMonomial] using
          setIndexedDividedPowerPolynomialDividedPowers_dpow_variable B i j
      calc
        δ.dpow n (DividedPowerAlgebra.embed B (T →₀ B) (Finsupp.single i a + m)) =
            (Finset.antidiagonal n).sum fun k =>
              δ.dpow k.1 (algebraMap B (DividedPowerAlgebra B (T →₀ B)) a * x) *
                δ.dpow k.2 (DividedPowerAlgebra.embed B (T →₀ B) m) := by
          rw [map_add, dividedPowerPolynomial_embed_single]
          exact δ.dpow_add (Ideal.mul_mem_left _ _ hx)
            (dividedPowerPolynomial_embed_mem_ideal B T m)
        _ = (Finset.antidiagonal n).sum fun k =>
              DividedPowerAlgebra.dp B k.1 (a • Finsupp.single i 1) *
                DividedPowerAlgebra.dp B k.2 m := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [δ.dpow_mul hx, ih k.2, hvar k.1, DividedPowerAlgebra.dp_smul]
          simp [Algebra.smul_def, map_pow]
        _ = DividedPowerAlgebra.dp B n (Finsupp.single i a + m) := by
          rw [Finsupp.smul_single_one, DividedPowerAlgebra.dp_add]

/-- Coefficient change along `φ`: the ring homomorphism from the divided power polynomial
algebra on `T` over `B` to the one over `B'`, applying `φ` to the coefficients and sending each
variable to the variable of the same index. -/
public noncomputable def polynomialCoefficientChange
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers) :
    DividedPowerAlgebra B (T →₀ B) →+* DividedPowerAlgebra B' (T →₀ B') := by
  let : Algebra B B' := φ.toRingHom.toAlgebra
  let : IsScalarTower B B' (DividedPowerAlgebra B' (T →₀ B')) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (DividedPowerAlgebra.map B'
    (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B'))).toRingHom

/-- Coefficient change along `φ` applies `φ` to constant coefficients. -/
private lemma polynomialCoefficientChange_algebraMap
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers) (b : B) :
    polynomialCoefficientChange (T := T) φ (algebraMap B (DividedPowerAlgebra B (T →₀ B)) b) =
      algebraMap B' (DividedPowerAlgebra B' (T →₀ B')) (φ.toRingHom b) := by
  let : Algebra B B' := φ.toRingHom.toAlgebra
  let : IsScalarTower B B' (DividedPowerAlgebra B' (T →₀ B')) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (DividedPowerAlgebra.map B'
    (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B')))
      (algebraMap B (DividedPowerAlgebra B (T →₀ B)) b) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_eq B B' (DividedPowerAlgebra B' (T →₀ B'))]
  rfl

/-- Coefficient change along `φ` sends each variable to the variable of the same index. -/
private lemma polynomialCoefficientChange_variable
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers) (t : T) :
    polynomialCoefficientChange (T := T) φ (dividedPowerPolynomialVariable B t) =
      dividedPowerPolynomialVariable B' t := by
  let : Algebra B B' := φ.toRingHom.toAlgebra
  let : IsScalarTower B B' (DividedPowerAlgebra B' (T →₀ B')) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change DividedPowerAlgebra.map B'
    (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B'))
      (DividedPowerAlgebra.dp B 1 (Finsupp.single t 1)) = _
  rw [DividedPowerAlgebra.map_apply_dp]
  congr 1
  ext s
  by_cases hs : s = t <;> simp [Finsupp.mapRange.linearMap_apply, hs]

/-- Coefficient change along `φ` carries the variable relation `X_t - b` to `X_t - φ b`. -/
private lemma polynomialCoefficientChange_variable_sub
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers) (b : B) (t : T) :
    polynomialCoefficientChange (T := T) φ (dividedPowerPolynomialVariable B t -
        algebraMap B (DividedPowerAlgebra B (T →₀ B)) b) =
      dividedPowerPolynomialVariable B' t -
        algebraMap B' (DividedPowerAlgebra B' (T →₀ B')) (φ.toRingHom b) := by
  rw [map_sub, polynomialCoefficientChange_variable, polynomialCoefficientChange_algebraMap]

/-- Coefficient change along `φ` is a morphism of divided power rings between the two divided
power polynomial algebras. -/
public theorem polynomialCoefficientChange_isDPMorphism
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers) :
    DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers B T)
      (setIndexedDividedPowerPolynomialDividedPowers B' T)
      (polynomialCoefficientChange (T := T) φ) := by
  classical
  let F := DividedPowerAlgebra B (T →₀ B)
  let F' := DividedPowerAlgebra B' (T →₀ B')
  let δB := setIndexedDividedPowerPolynomialDividedPowers B T
  let δB' := setIndexedDividedPowerPolynomialDividedPowers B' T
  let CB' := setIndexedDividedPowerPolynomialDividedPowerRing B' T
  let : Algebra B B' := φ.toRingHom.toAlgebra
  let : IsScalarTower B B' F' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let α : F →ₐ[B] F' := DividedPowerAlgebra.map B'
    (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B'))
  obtain ⟨q, hq, -⟩ := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial B T CB'
    ((setIndexedDividedPowerPolynomialCoefficientDPMorphism B' T).comp φ)
    fun t => ⟨dividedPowerPolynomialVariable B' t, variable_mem_polynomialIdeal B' t⟩
  let qAlg : F →ₐ[B] F' :=
    { toRingHom := q.toRingHom
      commutes' := fun b => congrArg (fun g => g b) hq.1 }
  have hαvar (t : T) : α (dividedPowerPolynomialVariable B t) =
      dividedPowerPolynomialVariable B' t :=
    polynomialCoefficientChange_variable φ t
  have hEmbed (m : T →₀ B) : qAlg (DividedPowerAlgebra.embed B (T →₀ B) m) =
      α (DividedPowerAlgebra.embed B (T →₀ B) m) := by
    induction m using Finsupp.induction with
    | zero => simp
    | @single_add t a m ht ha ih =>
        have hqAlgVar : qAlg (dividedPowerPolynomialVariable B t) =
            dividedPowerPolynomialVariable B' t := hq.2 t
        rw [map_add, map_add, ih, dividedPowerPolynomial_embed_single, map_add, map_mul, map_mul,
          hqAlgVar, hαvar t]
        congr 2
        exact (qAlg.commutes a).trans (α.commutes a).symm
  have hdp (n : ℕ) (m : T →₀ B) :
      qAlg (DividedPowerAlgebra.dp B n m) = α (DividedPowerAlgebra.dp B n m) := by
    rw [← setIndexedDividedPowerPolynomial_dpow_embed B T n m]
    change q.toRingHom (δB.dpow n (DividedPowerAlgebra.embed B (T →₀ B) m)) = _
    rw [← q.dpow_comp (n := n) (DividedPowerAlgebra.embed B (T →₀ B) m)
      (dividedPowerPolynomial_embed_mem_ideal B T m)]
    change δB'.dpow n (qAlg (DividedPowerAlgebra.embed B (T →₀ B) m)) =
      α (δB.dpow n (DividedPowerAlgebra.embed B (T →₀ B) m))
    rw [hEmbed, setIndexedDividedPowerPolynomial_dpow_embed B T n m]
    have hmapm : Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B') m =
        Finsupp.mapRange φ.toRingHom (map_zero φ.toRingHom) m := rfl
    rw [DividedPowerAlgebra.map_embed_apply, hmapm,
      setIndexedDividedPowerPolynomial_dpow_embed B' T n _, DividedPowerAlgebra.map_apply_dp]
    exact congrArg (DividedPowerAlgebra.dp B' n) hmapm.symm
  have hchange : polynomialCoefficientChange (T := T) φ = q.toRingHom :=
    (congrArg AlgHom.toRingHom (DividedPowerAlgebra.algHom_ext hdp)).symm
  rw [hchange]
  exact ⟨q.ideal_comp, fun x hx => q.dpow_comp x hx⟩

private lemma dividedPowerPolynomial_relation_mem_ideal
    (B : DividedPowerRing.{u}) (T : Type u) (f : T → B)
    (r : T →₀ B) (r₀ : B.ideal)
    (_hr : r.sum (fun t a => a * f t) = (r₀ : B)) :
    r.sum (fun t a => algebraMap B (DividedPowerAlgebra B (T →₀ B)) a *
      dividedPowerPolynomialVariable B t) -
        algebraMap B (DividedPowerAlgebra B (T →₀ B)) (r₀ : B) ∈
      dividedPowerPolynomialIdeal B.ideal T := by
  classical
  refine Ideal.sub_mem _ (Ideal.mem_sup_right ?_) (coefficient_mem_polynomialIdeal B r₀.property)
  exact Submodule.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ (variable_mem_positiveIdeal B t)

/-- The variable relation `X_t - f t` lies in the presentation ideal of `f`. -/
private lemma variable_sub_mem_kernelPresentationIdeal
    (B : DividedPowerRing.{u}) (T : Type u) (f : T → B) (t : T) :
    dividedPowerPolynomialVariable B t - algebraMap B (DividedPowerAlgebra B (T →₀ B)) (f t) ∈
      kernelPresentationIdeal B T f := by
  unfold kernelPresentationIdeal
  exact Ideal.subset_span (Or.inl ⟨t, rfl⟩)

/-- Every nonzero divided power of a linear relation among the `f t` with constant term in the
divided power ideal lies in the presentation ideal of `f`. -/
private lemma dpow_relation_mem_kernelPresentationIdeal
    (B : DividedPowerRing.{u}) (T : Type u) (f : T → B) {n : ℕ} (hn : n ≠ 0)
    (r : T →₀ B) (r₀ : B.ideal) (hr : r.sum (fun t a => a * f t) = (r₀ : B)) :
    (setIndexedDividedPowerPolynomialDividedPowers B T).dpow n
        (r.sum (fun t a => algebraMap B (DividedPowerAlgebra B (T →₀ B)) a *
          dividedPowerPolynomialVariable B t) -
          algebraMap B (DividedPowerAlgebra B (T →₀ B)) (r₀ : B)) ∈
      kernelPresentationIdeal B T f := by
  unfold kernelPresentationIdeal
  exact Ideal.subset_span (Or.inr ⟨n, r, r₀, by omega, hr, rfl⟩)

/-- A linear relation `∑ v_t X_t - ∑ v_t g t` is the combination `∑ v_t (X_t - g t)` of the
variable relations. -/
private lemma finsuppSum_sub_eq_sum_mul_variable_sub
    (B : DividedPowerRing.{u}) {T : Type u} (g : T → B) (v : T →₀ B) {S : Finset T}
    (hv : v.support ⊆ S) :
    v.sum (fun t a => algebraMap B (DividedPowerAlgebra B (T →₀ B)) a *
        dividedPowerPolynomialVariable B t) -
        algebraMap B (DividedPowerAlgebra B (T →₀ B)) (v.sum fun t a => a * g t) =
      ∑ t ∈ S, algebraMap B (DividedPowerAlgebra B (T →₀ B)) (v t) *
        (dividedPowerPolynomialVariable B t -
          algebraMap B (DividedPowerAlgebra B (T →₀ B)) (g t)) := by
  rw [Finsupp.sum_of_support_subset v hv, Finsupp.sum_of_support_subset v hv]
  · simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib]
  all_goals simp

/-- Coefficient change along `φ` carries a linear relation over `B` to the corresponding
combination of variable relations over `B'`. -/
private lemma polynomialCoefficientChange_relation
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers) (g : T → B) (v : T →₀ B)
    {S : Finset T} (hv : v.support ⊆ S) :
    polynomialCoefficientChange (T := T) φ
        (v.sum (fun t a => algebraMap B (DividedPowerAlgebra B (T →₀ B)) a *
          dividedPowerPolynomialVariable B t) -
          algebraMap B (DividedPowerAlgebra B (T →₀ B)) (v.sum fun t a => a * g t)) =
      ∑ t ∈ S, algebraMap B' (DividedPowerAlgebra B' (T →₀ B')) (φ.toRingHom (v t)) *
        (dividedPowerPolynomialVariable B' t -
          algebraMap B' (DividedPowerAlgebra B' (T →₀ B')) (φ.toRingHom (g t))) := by
  rw [finsuppSum_sub_eq_sum_mul_variable_sub B g v hv, map_sum]
  simp only [map_mul, polynomialCoefficientChange_variable_sub,
    polynomialCoefficientChange_algebraMap]

/-- Coefficient change along `φ` carries the presentation ideal of the divided power envelope
of `J` over `B` into the presentation ideal over `B'` of the images `φ j`, `j ∈ J`. The
flatness hypothesis is not needed for this inclusion. -/
public lemma sourceKernel_map_le_targetKernel
    {B B' : DividedPowerRing.{u}}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers)
    (J : Ideal B)
    (_hflat : RingHom.Flat (Ideal.quotientMap B'.ideal φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp))) :
    let f : J → B := fun j => j.1
    let f' : J → B' := fun j => φ.toRingHom j.1
    Ideal.map (polynomialCoefficientChange (T := J) φ)
        (kernelPresentationIdeal B J f) ≤
      kernelPresentationIdeal B' J f' := by
  intro f f'
  rw [Ideal.map_le_iff_le_comap]
  refine Ideal.span_le.2 ?_
  rintro z (⟨t, rfl⟩ | ⟨n, r, r₀, hn, hr, rfl⟩) <;> refine Ideal.mem_comap.2 ?_
  · rw [polynomialCoefficientChange_variable_sub]
    exact variable_sub_mem_kernelPresentationIdeal B' J f' t
  · let r' := Finsupp.mapRange φ.toRingHom (map_zero φ.toRingHom) r
    let r₀' : B'.ideal := ⟨φ.toRingHom r₀, φ.ideal_comp (Ideal.mem_map_of_mem _ r₀.property)⟩
    have hr' : r'.sum (fun t a => a * f' t) = r₀' := by
      rw [Finsupp.sum_mapRange_index]
      · change _ = φ.toRingHom r₀
        rw [← hr, map_finsuppSum]
        simp only [map_mul]
        rfl
      · simp
    rw [← (polynomialCoefficientChange_isDPMorphism (T := J) φ).dpow_comp _
        (dividedPowerPolynomial_relation_mem_ideal B J f r r₀ hr), ← hr,
      polynomialCoefficientChange_relation φ f r subset_rfl]
    convert dpow_relation_mem_kernelPresentationIdeal B' J f' (n := n) (by omega) r' r₀' hr'
      using 2
    rw [← hr']
    exact (finsuppSum_sub_eq_sum_mul_variable_sub B' f' r' Finsupp.support_mapRange).symm

/-- Coefficient change along `φ` carries each variable relation over `B` onto the variable
relation over `B'`, so the latter lies in the extension of the presentation ideal of `f`. -/
private lemma variable_sub_mem_map_kernelPresentationIdeal
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers) (f : T → B) (t : T) :
    dividedPowerPolynomialVariable B' t -
        algebraMap B' (DividedPowerAlgebra B' (T →₀ B')) (φ.toRingHom (f t)) ∈
      Ideal.map (polynomialCoefficientChange (T := T) φ) (kernelPresentationIdeal B T f) := by
  rw [← polynomialCoefficientChange_variable_sub φ (f t) t]
  exact Ideal.mem_map_of_mem _ (variable_sub_mem_kernelPresentationIdeal B T f t)

private lemma dividedPowers_dpow_add_mem {A : Type u} [CommRing A] {I K : Ideal A}
    (δ : DividedPowers I) {a c : A} (ha : a ∈ I) (hc : c ∈ I)
    (hKa : ∀ m : ℕ, m ≠ 0 → δ.dpow m a ∈ K) (hKc : ∀ m : ℕ, m ≠ 0 → δ.dpow m c ∈ K)
    {n : ℕ} (hn : n ≠ 0) : δ.dpow n (a + c) ∈ K := by
  simpa [Fintype.sum_bool, add_comm] using
    dividedPowers_dpow_finset_sum_mem I K δ Finset.univ (fun b : Bool => bif b then a else c)
      (by rintro (_ | _) _ <;> assumption) (by rintro (_ | _) _ <;> assumption) hn

private lemma sum_mul_eq_add_sum_mul_sum {R ι κ : Type*} [CommRing R] [Fintype κ]
    (S : Finset ι) (a b q : ι → R) (c : κ → R) (σ : κ → ι → R)
    (h : ∀ t, a t = b t + ∑ j, c j * σ j t) :
    ∑ t ∈ S, a t * q t = ∑ t ∈ S, b t * q t + ∑ j, c j * ∑ t ∈ S, σ j t * q t := by
  simp_rw [h, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-- If `B / I → B' / I'` is flat, every nonzero divided power of a linear relation among the
`φ (f t)` with constant term in `I'` lies in the extension along coefficient change of the
presentation ideal of `f`. -/
private lemma dpow_relation_mem_map_kernelPresentationIdeal
    {B B' : DividedPowerRing.{u}} {T : Type u}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers)
    (hflat : RingHom.Flat (Ideal.quotientMap B'.ideal φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp)))
    (f : T → B) (r' : T →₀ B') (r₀' : B'.ideal)
    (hr : r'.sum (fun t a => a * φ.toRingHom (f t)) = r₀') {n : ℕ} (hn : n ≠ 0) :
    (setIndexedDividedPowerPolynomialDividedPowers B' T).dpow n
        (r'.sum (fun t a => algebraMap B' (DividedPowerAlgebra B' (T →₀ B')) a *
          dividedPowerPolynomialVariable B' t) -
          algebraMap B' (DividedPowerAlgebra B' (T →₀ B')) (r₀' : B')) ∈
      Ideal.map (polynomialCoefficientChange (T := T) φ) (kernelPresentationIdeal B T f) := by
  classical
  obtain ⟨k, c, s, hsI, hsupp, hres⟩ := Ideal.flat_relation_decomposition
    B.ideal B'.ideal φ.toRingHom φ.ideal_comp hflat f r' (hr ▸ r₀'.property)
  let P' := DividedPowerAlgebra B' (T →₀ B')
  let α := polynomialCoefficientChange (T := T) φ
  let δ' := setIndexedDividedPowerPolynomialDividedPowers B' T
  let Ipoly' := dividedPowerPolynomialIdeal B'.ideal T
  let Kext := Ideal.map α (kernelPresentationIdeal B T f)
  let S := r'.support
  let i : T → B' := fun t => r' t - ∑ j, c j * φ.toRingHom (s j t)
  let Q (t : T) : P' := dividedPowerPolynomialVariable B' t - algebraMap B' P' (φ.toRingHom (f t))
  let R (j : Fin k) : DividedPowerAlgebra B (T →₀ B) :=
    (s j).sum (fun t a => algebraMap B (DividedPowerAlgebra B (T →₀ B)) a *
      dividedPowerPolynomialVariable B t) -
      algebraMap B (DividedPowerAlgebra B (T →₀ B)) ((s j).sum fun t a => a * f t)
  have hdp : DividedPowers.IsDPMorphism (setIndexedDividedPowerPolynomialDividedPowers B T) δ' α :=
    polynomialCoefficientChange_isDPMorphism (T := T) φ
  have hRmem (j : Fin k) : R j ∈ dividedPowerPolynomialIdeal B.ideal T :=
    dividedPowerPolynomial_relation_mem_ideal B T f (s j) ⟨_, hsI j⟩ rfl
  have hRI (j : Fin k) : α (R j) ∈ Ipoly' := hdp.ideal_comp (Ideal.mem_map_of_mem _ (hRmem j))
  have hiI (t : T) : algebraMap B' P' (i t) ∈ Ipoly' := coefficient_mem_polynomialIdeal B' (hres t)
  have hAI (t : T) (_ : t ∈ S) : algebraMap B' P' (i t) * Q t ∈ Ipoly' :=
    Ipoly'.mul_mem_right _ (hiI t)
  have hCI (j : Fin k) (_ : j ∈ Finset.univ) : algebraMap B' P' (c j) * α (R j) ∈ Ipoly' :=
    Ipoly'.mul_mem_left _ (hRI j)
  have hAK (t : T) (_ : t ∈ S) (m : ℕ) (hm : m ≠ 0) :
      δ'.dpow m (algebraMap B' P' (i t) * Q t) ∈ Kext := by
    rw [mul_comm (algebraMap B' P' (i t)), δ'.dpow_mul (hiI t)]
    exact Kext.mul_mem_right _ (Ideal.pow_mem_of_mem Kext
      (variable_sub_mem_map_kernelPresentationIdeal φ f t) m (Nat.pos_of_ne_zero hm))
  have hCK (j : Fin k) (_ : j ∈ Finset.univ) (m : ℕ) (hm : m ≠ 0) :
      δ'.dpow m (algebraMap B' P' (c j) * α (R j)) ∈ Kext := by
    rw [δ'.dpow_mul (hRI j), hdp.dpow_comp (n := m) _ (hRmem j)]
    exact Kext.mul_mem_left _ (Ideal.mem_map_of_mem α
      (dpow_relation_mem_kernelPresentationIdeal B T f hm (s j) ⟨_, hsI j⟩ rfl))
  have hdecomp : r'.sum (fun t a => algebraMap B' P' a * dividedPowerPolynomialVariable B' t) -
      algebraMap B' P' (r₀' : B') =
        ∑ t ∈ S, algebraMap B' P' (i t) * Q t + ∑ j, algebraMap B' P' (c j) * α (R j) := by
    have hRmap (j : Fin k) : α (R j) = ∑ t ∈ S, algebraMap B' P' (φ.toRingHom (s j t)) * Q t :=
      polynomialCoefficientChange_relation φ f (s j) (hsupp j)
    rw [← hr]
    refine (finsuppSum_sub_eq_sum_mul_variable_sub B' (fun t => φ.toRingHom (f t)) r'
      subset_rfl).trans ?_
    simp_rw [hRmap]
    exact sum_mul_eq_add_sum_mul_sum S (fun t => algebraMap B' P' (r' t))
      (fun t => algebraMap B' P' (i t)) Q (fun j => algebraMap B' P' (c j))
      (fun j t => algebraMap B' P' (φ.toRingHom (s j t))) fun t => by simp [i]
  rw [hdecomp]
  exact dividedPowers_dpow_add_mem δ' (Submodule.sum_mem _ hAI) (Submodule.sum_mem _ hCI)
    (fun m hm => dividedPowers_dpow_finset_sum_mem _ Kext δ' S _ hAI hAK hm)
    (fun m hm => dividedPowers_dpow_finset_sum_mem _ Kext δ' Finset.univ _ hCI hCK hm) hn

/-- If `B / I → B' / I'` is flat, the presentation ideal over `B'` of the images `φ j`,
`j ∈ J`, is contained in the extension along coefficient change of the presentation ideal of
the divided power envelope of `J` over `B`. -/
public lemma targetKernel_le_sourceKernel_map
    {B B' : DividedPowerRing.{u}}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers)
    (J : Ideal B)
    (hflat : RingHom.Flat (Ideal.quotientMap B'.ideal φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp))) :
    let f : J → B := fun j => j.1
    let f' : J → B' := fun j => φ.toRingHom j.1
    kernelPresentationIdeal B' J f' ≤
      Ideal.map (polynomialCoefficientChange (T := J) φ)
        (kernelPresentationIdeal B J f) := by
  intro f f'
  refine Ideal.span_le.2 ?_
  rintro z (⟨t, rfl⟩ | ⟨n, r', r₀', hn, hr, rfl⟩)
  · exact variable_sub_mem_map_kernelPresentationIdeal φ f t
  · exact dpow_relation_mem_map_kernelPresentationIdeal φ hflat f r' r₀' hr (n := n) (by omega)

/-- The canonical morphism of divided power envelopes induced by a morphism of
divided power rings and an inclusion of the extended ideal. -/
public noncomputable def dividedPowerEnvelopeBaseChangeMap
    {B B' : DividedPowerRing.{u}}
    (φ : DividedPowers.DPMorphism B.dividedPowers B'.dividedPowers)
    (J : Ideal B) (J' : Ideal B')
    (hJ : B.ideal.map (RingHom.id B) ≤ J)
    (hJ' : B'.ideal.map (RingHom.id B') ≤ J')
    (hmap : J.map φ.toRingHom ≤ J')
    (D : DividedPowerEnvelope B (RingHom.id B) J hJ)
    (D' : DividedPowerEnvelope B' (RingHom.id B') J' hJ') :
    DividedPowers.DPMorphism D.object.dividedPowers D'.object.dividedPowers := by
  let a : DividedPowers.DPMorphism B.dividedPowers D'.object.dividedPowers :=
    D'.structureMap.comp φ
  let p : IdealPair.Hom J D'.object.ideal :=
    IdealPair.Hom.comp D'.algebraMap (IdealPair.Hom.ofRingHom φ.toRingHom hmap)
  have hp : IdealPair.Hom.comp p (IdealPair.Hom.ofRingHom (RingHom.id B) hJ) =
      IdealPair.Hom.ofDPMorphism a := IdealPair.Hom.ext_toRingHom _ _ <| by
    ext x
    change D'.algebraMap.toRingHom (φ x) = D'.structureMap.toRingHom (φ x)
    rw [show D'.algebraMap.toRingHom = D'.structureMap.toRingHom by
      simpa using D'.algebraMap_comp]
  exact ((D.homEquiv D'.object a).symm ⟨p, hp⟩).1

end Crystalline
