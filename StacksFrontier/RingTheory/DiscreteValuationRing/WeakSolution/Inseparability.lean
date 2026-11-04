module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weak solutions and solutions after a base change of the fraction field

Let `A → B` be an extension of discrete valuation rings with fraction fields `K → L`. This
file collects three statements about the base-change package of a finite extension `K₁ / K`:
an example showing that inseparability of `K₁ / K` is *necessary* for a weak solution, the
stability of weak unramifiedness under a totally ramified separable base change, and the
Galois action on the rings of the base change.

For a perfect field `k` of positive characteristic `p` and the extension of power-series
rings `k[[x]] → k[[x ^ (1 / p)]]` sending the parameter `x` to the `p`-th power of the new
parameter, every weak solution of the induced extension of Laurent-series fields is
inseparable, and conversely every finite inseparable extension of `k((x))` is a solution.

If `A → B` is weakly unramified and `K₁ / K` is a finite separable extension that is totally
ramified with respect to `A`, then `L ⊗[K] K₁` is a field, the integral closure `A₁` of `A`
in `K₁` and the base change `B₁ = B ⊗[A] A₁` are discrete valuation rings, and `A₁ → B₁` is
again weakly unramified. The canonical image of `B₁` in `L ⊗[K] K₁` is the integral closure
of `B` there, so the same conclusions hold for that literal integral closure.

For a finite normal extension `K₁ / K`, the automorphism group of `K₁ / K` acts on the reduced
base change of `L` and on the integral closures of `A` and of `B`, compatibly with all the
structure maps, and its action on the maximal ideals of the latter integral closure is
transitive.

## Main results

* `IsDiscreteValuationRing.isWeaklyUnramified_iff_ramificationIdx_eq_one`: weak
  unramifiedness of an extension of discrete valuation rings, read as the
  length-theoretic ramification index of the maximal ideal upstairs being one.
* `IsDiscreteValuationRing.weakSolution_isInseparable_and_inseparable_isSolution`: for
  `k[[x]] → k[[x ^ (1 / p)]]` in positive characteristic `p`, every weak solution is
  inseparable, while every finite inseparable extension of `k((x))` is a solution.
* `IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified`:
  stability of weak unramifiedness under a finite separable totally ramified extension.
* `IsDiscreteValuationRing.normal_extension_acts_transitively_on_maximalSpectrum_integralClosure`:
  the compatible actions of `Aut(K₁ / K)` and transitivity on the maximal spectrum.

## Implementation notes

In the example the rings and their fraction fields are allowed to be abstract copies of the
power-series and Laurent-series rings. The algebra equivalences and their compatibility with
the fraction-field embeddings specify the copies canonically, while the equation on the
parameters expresses `k[[x]] → k[[x ^ (1 / p)]]` as the map `x ↦ x ^ p` after renaming the
target parameter. The abstract copies and the finite extension have independent universes; in
the existential base change `L₁` and `B₁` live in the universe of `L ⊗[K] K₁` and `A₁` in that
of `K₁`, and the formal-smoothness test-ring universe `v` is independent of all of these, being
the last universe argument of `IntegralClosureBaseChange.IsSolution`.

For the totally ramified base change, the tensor product is identified with the literal integral
closure through a `B`-algebra equivalence that agrees with the canonical embedding in the field.
Weak unramifiedness is expressed by equality of the extended maximal ideal with the maximal ideal
upstairs; injectivity of both canonical maps is included.

Actions on rings are represented by homomorphisms from the automorphism group to groups of
algebra automorphisms. The induced action on maximal ideals sends an ideal `q` along an
automorphism `g` to the inverse image of `q` under `g⁻¹`.

## References

* [Stacks Project, Tag 09EP](https://stacks.math.columbia.edu/tag/09EP)
* [Stacks Project, Tag 09ER](https://stacks.math.columbia.edu/tag/09ER)
* [Stacks Project, Tag 09EU](https://stacks.math.columbia.edu/tag/09EU)
-/

@[expose] public section

open scoped Pointwise TensorProduct

universe uk uA uB uK uL uK₁ uL₁ uA₁ uB₁ v u

namespace IsDiscreteValuationRing

/-! ### Two readings of the ramification index -/

/-- Weak unramifiedness of an extension of discrete valuation rings, stated with the
length-theoretic ramification index. -/
theorem isWeaklyUnramified_iff_ramificationIdx_eq_one (A B : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B] :
    IsWeaklyUnramified A B ↔ (IsLocalRing.maximalIdeal B).ramificationIdx A = 1 := by
  rw [IsWeaklyUnramified, ramificationIndex_eq_ramificationIdx]

/-! ### Inseparability is necessary for a weak solution -/

/- The parameter map is a Frobenius twist on power series. -/
private theorem powerSeries_pow_as_subst
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]
    (f : PowerSeries k) :
    PowerSeries.subst (PowerSeries.X ^ p)
      (PowerSeries.map (frobenius k p) f) = f ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← PowerSeries.expand_apply p hp, ← PowerSeries.map_expand]
  exact PowerSeries.map_frobenius_expand p hp

private theorem power_mem_base
    (p : ℕ) [Fact p.Prime] (k A B : Type*)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a))
    (b : B) : ∃ a : A, algebraMap A B a = b ^ p := by
  let f := PowerSeries.map (frobenius k p) (eB b)
  refine ⟨eA.symm f, eB.injective ?_⟩
  rw [hAB, eA.apply_symm_apply, powerSeries_pow_as_subst p k (eB b), map_pow]

private theorem fraction_power_mem_base
    (p : ℕ) (A B K L : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing B L]
    (hpow : ∀ b : B, ∃ a : A, algebraMap A B a = b ^ p)
    (l : L) : ∃ x : K, algebraMap K L x = l ^ p := by
  obtain ⟨b, c, _, hbc⟩ := IsFractionRing.div_surjective B l
  obtain ⟨a, ha⟩ := hpow b
  obtain ⟨d, hd⟩ := hpow c
  refine ⟨(algebraMap A K a) / (algebraMap A K d), ?_⟩
  calc
    algebraMap K L ((algebraMap A K a) / (algebraMap A K d)) =
        algebraMap A L a / algebraMap A L d := by
          rw [map_div₀, IsScalarTower.algebraMap_apply A K L,
            IsScalarTower.algebraMap_apply A K L]
    _ = algebraMap B L (algebraMap A B a) /
        algebraMap B L (algebraMap A B d) := by
          rw [IsScalarTower.algebraMap_apply A B L,
            IsScalarTower.algebraMap_apply A B L]
    _ = (algebraMap B L b) ^ p / (algebraMap B L c) ^ p := by
          rw [ha, hd, map_pow, map_pow]
    _ = l ^ p := by rw [← div_pow, hbc]

private theorem extension_purelyInseparable
    (p : ℕ) [Fact p.Prime]
    (k A B K L : Type*)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra k A] [Algebra k B] [Algebra k K]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing B L]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a)) :
    IsPurelyInseparable K L := by
  have : CharP K p := charP_of_injective_algebraMap
    (algebraMap k K).injective p
  rw [isPurelyInseparable_iff_pow_mem K p]
  intro l
  obtain ⟨x, hx⟩ := fraction_power_mem_base p A B K L
    (power_mem_base p k A B eA eB hAB) l
  exact ⟨1, x, by simpa using hx⟩

private theorem ring_extension_integral
    (p : ℕ) [Fact p.Prime] (k A B : Type*)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a)) :
    Algebra.IsIntegral A B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨a, ha⟩ := power_mem_base p k A B eA eB hAB b
  apply IsIntegral.of_pow (Fact.out : p.Prime).pos
  rw [← ha]
  exact isIntegral_algebraMap

private theorem ring_map_not_surjective
    (p : ℕ) [Fact p.Prime] (k A B : Type*)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a)) :
    ¬ Function.Surjective (algebraMap A B) := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (eB.symm PowerSeries.X)
  have hcoeff := congrArg (PowerSeries.coeff 1) (hAB a)
  rw [ha, eB.apply_symm_apply] at hcoeff
  simp [PowerSeries.coeff_subst_X_pow (Fact.out : p.Prime).ne_zero,
    (Fact.out : p.Prime).not_dvd_one] at hcoeff

private theorem field_extension_not_separable
    (p : ℕ) [Fact p.Prime] (k A B K L : Type*)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field K] [Field L]
    [Algebra k A] [Algebra k B] [Algebra k K]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a)) :
    ¬ Algebra.IsSeparable K L := by
  intro hsep
  have : IsPurelyInseparable K L := extension_purelyInseparable p k A B K L eA eB hAB
  refine ring_map_not_surjective p k A B eA eB hAB fun b ↦ ?_
  obtain ⟨x, hx⟩ :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L (algebraMap B L b)
  have hb : IsIntegral A (algebraMap B L b) := by
    have : Algebra.IsIntegral A B := ring_extension_integral p k A B eA eB hAB
    exact (Algebra.IsIntegral.isIntegral (R := A) b).map
      (IsScalarTower.toAlgHom A B L)
  have hxint : IsIntegral A x := IsIntegral.tower_bot (algebraMap K L).injective (hx ▸ hb)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxint
  refine ⟨a, IsFractionRing.injective B L ?_⟩
  calc
    algebraMap B L (algebraMap A B a) = algebraMap K L (algebraMap A K a) := by
      rw [← IsScalarTower.algebraMap_apply A B L,
        ← IsScalarTower.algebraMap_apply A K L]
    _ = algebraMap K L x := by rw [ha]
    _ = algebraMap B L b := hx

private theorem closure_tower_top
    (A B C E : Type*)
    [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A E] [Algebra B E] [Algebra C E]
    [IsScalarTower A B E] [IsIntegralClosure C A E]
    (hBA : Algebra.IsIntegral A B) : IsIntegralClosure C B E :=
  IsIntegralClosure.tower_top (R := A) (A := B) (B := E) (C := C)

private theorem tensor_eval_ker
    (F E M : Type*) [Field F] [Field E] [Field M]
    [Algebra F E] [Algebra F M] [IsPurelyInseparable F E]
    (f : E →ₐ[F] M) :
    RingHom.ker (Algebra.TensorProduct.lift f (AlgHom.id F M)
      (fun _ _ ↦ Commute.all _ _)) = nilradical (E ⊗[F] M) := by
  let g := Algebra.TensorProduct.lift f (AlgHom.id F M) (fun _ _ ↦ Commute.all _ _)
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦
    IsReduced.eq_zero _ (mem_nilradical.mp hx |>.map g)
  have hgx : g x = 0 := hx
  obtain ⟨n, hn, a, ha⟩ :=
    IsPurelyInseparable.exists_pow_mem_range_tensorProduct
      ((Algebra.TensorProduct.comm F E M) x)
  have hpow : x ^ n = Algebra.TensorProduct.includeRight a := by
    apply (Algebra.TensorProduct.comm F E M).injective
    simpa using ha.symm
  have ha0 : a = 0 := by simpa [g, hgx, hn.ne'] using (congrArg g hpow).symm
  exact mem_nilradical.mpr ⟨n, by simpa [ha0] using hpow⟩

private theorem formallySmoothNAdic_of_bijective.{w}
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Bijective φ) (n : Ideal S) :
    RingHom.FormallySmoothNAdic.{w} φ n := by
  let e := RingEquiv.ofBijective φ hφ
  intro T _ J _ f ψ hcomm _
  refine ⟨f.comp e.symm.toRingHom, ?_, ?_⟩
  · ext s
    have h := congrArg (fun h : R →+* T ⧸ J ↦ h (e.symm s)) hcomm
    change ψ (e (e.symm s)) = Ideal.Quotient.mk J (f (e.symm s)) at h
    simpa using h.symm
  · ext r
    change f (e.symm (e r)) = f r
    simp

private theorem tensor_eval_equiv
    (F E M : Type*) [Field F] [Field E] [Field M]
    [Algebra F E] [Algebra F M] [IsPurelyInseparable F E]
    (f : E →ₐ[F] M) :
    ∃ e : ((E ⊗[F] M) ⧸ nilradical (E ⊗[F] M)) ≃ₐ[F] M,
      (∀ x : E, e (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] M) x)) = f x) ∧
      (∀ x : M, e (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : M →ₐ[F] E ⊗[F] M) x)) = x) := by
  let g := Algebra.TensorProduct.lift f (AlgHom.id F M) (fun _ _ ↦ Commute.all _ _)
  have hg : Function.Surjective g := fun x ↦
    ⟨Algebra.TensorProduct.includeRight x, by simp [g]⟩
  let e := (Ideal.quotientEquivAlgOfEq F (tensor_eval_ker F E M f).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)
  exact ⟨e, fun x ↦ by simp [e, g], fun x ↦ by simp [e, g]⟩

private theorem localRingHom_bijective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f)
    (q : Ideal S) [q.IsPrime] :
    Function.Bijective (Localization.localRingHom (q.comap f) q f rfl) :=
  (Localization.localRingEquiv (q.comap f) q (RingEquiv.ofBijective f hf) rfl).bijective

private theorem exists_solution_of_algHom.{wA, wB, wK, wL, wM, wv}
    (A : Type wA) (B : Type wB) (K : Type wK) (L : Type wL) (M : Type wM)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field M]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K M] [Algebra A M]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K M]
    [Module.Finite K M] [IsPurelyInseparable K L] [Algebra.IsIntegral A B]
    (f : L →ₐ[K] M) :
    ∃ D : IntegralClosureBaseChange.{wA, wB, wK, wL, wM,
        max wL wM, wM, max wL wM} A B K L M,
      D.IsSolution.{wA, wB, wK, wL, wM, max wL wM, wM, max wL wM, wv} := by
  classical
  let T := L ⊗[K] M
  let R := T ⧸ nilradical T
  let C := integralClosure A M
  let S := integralClosure A R
  let : Algebra M T := Algebra.TensorProduct.rightAlgebra
  obtain ⟨e, hleft, hright⟩ := tensor_eval_equiv K L M f
  let eC : C ≃ₐ[A] S := (e.symm.restrictScalars A).mapIntegralClosure
  let : Algebra C S := eC.toAlgHom.toAlgebra
  let g : B →ₐ[A] S := IsIntegralClosure.lift A S R
  let : Algebra B S := g.toAlgebra
  have : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun a ↦ (g.commutes a).symm
  have : IsScalarTower A C S := IsScalarTower.of_algebraMap_eq fun a ↦ (eC.commutes a).symm
  have : IsScalarTower B S R := IsScalarTower.of_algebraMap_eq fun b ↦
    (IsIntegralClosure.algebraMap_lift A S R b).symm
  have : IsIntegralClosure S B R := IsIntegralClosure.tower_top (R := A)
  let D : IntegralClosureBaseChange.{wA, wB, wK, wL, wM,
      max wL wM, wM, max wL wM} A B K L M := {
    L₁ := R
    A₁ := C
    B₁ := S
    eL₁ := AlgEquiv.refl
    eL₁_left := fun x ↦ rfl
    eL₁_right := fun x ↦ rfl
    ringSquare := fun x ↦ by
      change e.symm (x : M) = Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : M →ₐ[K] T) (x : M))
      apply e.injective
      rw [e.apply_symm_apply, hright]
  }
  refine ⟨D, ?_⟩
  intro q hq
  have : q.IsPrime := hq.isPrime
  exact formallySmoothNAdic_of_bijective _
    (localRingHom_bijective (algebraMap C S) eC.bijective q) _

/-- If every `p`-th power in `E` comes from `F`, then `x ↦ x ^ p` lifts to a ring map `E → F`. -/
private theorem exists_ringHom_algebraMap_eq_pow
    (p : ℕ) (F E : Type*) [Field F] [Field E] [ExpChar E p] [Algebra F E]
    (hpow : ∀ x : E, ∃ a : F, algebraMap F E a = x ^ p) :
    ∃ g : E →+* F, ∀ x : E, algebraMap F E (g x) = x ^ p := by
  let i := (algebraMap F E).rangeRestrictFieldEquiv
  exact ⟨i.symm.toRingHom.comp ((frobenius E p).codRestrict (algebraMap F E).fieldRange hpow),
    fun x ↦ congrArg Subtype.val (i.apply_symm_apply _)⟩

private theorem nonempty_algHom_of_pow_mem
    (p : ℕ) (F E M : Type*)
    [Field F] [Field E] [Field M] [ExpChar F p]
    [Algebra F E] [Algebra F M]
    (hE : ∀ x : E, ∃ a : F, algebraMap F E a = x ^ p)
    (hM : ∀ a : F, ∃ x : M, x ^ p = algebraMap F M a) :
    Nonempty (E →ₐ[F] M) := by
  classical
  have : ExpChar E p := expChar_of_injective_algebraMap (algebraMap F E).injective p
  have : ExpChar M p := expChar_of_injective_algebraMap (algebraMap F M).injective p
  obtain ⟨g, hg⟩ := exists_ringHom_algebraMap_eq_pow p F E hE
  let j := (frobenius M p).rangeRestrictFieldEquiv
  let r : F →+* M := j.symm.toRingHom.comp
    ((algebraMap F M).codRestrict (frobenius M p).fieldRange hM)
  have hr (a : F) : r a ^ p = algebraMap F M a :=
    congrArg Subtype.val (j.apply_symm_apply _)
  refine ⟨{ r.comp g with commutes' := fun a ↦ ?_ }⟩
  apply (frobenius M p).injective
  change r (g (algebraMap F E a)) ^ p = (algebraMap F M a) ^ p
  rw [hr, ← map_pow]
  congr 1
  apply (algebraMap F E).injective
  rw [hg, map_pow]

private theorem sum_expand_mul_X_pow
    {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0) (f : PowerSeries R) :
    ∑ i ∈ Finset.range p,
      PowerSeries.expand p hp (PowerSeries.mk fun n ↦ PowerSeries.coeff (n * p + i) f) *
        PowerSeries.X ^ i = f := by
  ext n
  rw [map_sum]
  rw [Finset.sum_eq_single (n % p)]
  · rw [PowerSeries.coeff_mul_X_pow', ite_eq_left (Nat.mod_le n p)]
    have hd : p ∣ n - n % p := by
      have := Nat.mod_add_div n p
      exact ⟨n / p, by omega⟩
    rw [PowerSeries.coeff_expand, ite_eq_left hd, PowerSeries.coeff_mk]
    rw [Nat.div_mul_cancel hd, Nat.sub_add_cancel (Nat.mod_le n p)]
  · intro i hi hne
    rw [PowerSeries.coeff_mul_X_pow']
    split_ifs with hi'
    · rw [PowerSeries.coeff_expand]
      split_ifs with hd
      · exfalso
        apply hne
        have hn : n % p = i := by
          calc
            n % p = ((n - i) + i) % p := by rw [Nat.sub_add_cancel hi']
            _ = i := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd,
              zero_add, Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
              Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
        exact hn.symm
      · rfl
    · rfl
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.mod_lt n (Nat.pos_of_ne_zero hp)))).elim

private theorem linearCombination_surjective_of_subst_X_pow
    (p : ℕ) (hp : p ≠ 0) (k A B : Type*)
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a)) :
    Function.Surjective (Fintype.linearCombination A
      (fun i : Fin p ↦ eB.symm PowerSeries.X ^ (i : ℕ))) := by
  classical
  let v : Fin p → B := fun i ↦ eB.symm PowerSeries.X ^ (i : ℕ)
  change Function.Surjective (Fintype.linearCombination A v)
  intro b
  refine ⟨fun i ↦ eA.symm (PowerSeries.mk fun n ↦
    PowerSeries.coeff (n * p + (i : ℕ)) (eB b)), ?_⟩
  apply eB.injective
  change eB (∑ i : Fin p, _ • v i) = _
  simp only [map_sum, Algebra.smul_def, map_mul, hAB, eA.apply_symm_apply,
    v, map_pow, eB.apply_symm_apply]
  simpa only [PowerSeries.expand_apply] using
    (Fin.sum_univ_eq_sum_range (fun i ↦
      PowerSeries.expand p hp (PowerSeries.mk fun n ↦
        PowerSeries.coeff (n * p + i) (eB b)) * PowerSeries.X ^ i) p).trans
      (sum_expand_mul_X_pow p hp (eB b))

private theorem moduleFinite_of_subst_X_pow
    (p : ℕ) (hp : p ≠ 0) (k A B : Type*)
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a)) :
    Module.Finite A B :=
  Module.Finite.of_surjective _
    (linearCombination_surjective_of_subst_X_pow p hp k A B eA eB hAB)

private theorem powerSeries_frobenius_root
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [PerfectField k] [CharP k p]
    (f : PowerSeries k) :
    (PowerSeries.map ((frobeniusEquiv k p).symm : k →+* k) f) ^ p =
      PowerSeries.subst (PowerSeries.X ^ p) f := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← PowerSeries.map_frobenius_expand p hp
    (f := PowerSeries.map ((frobeniusEquiv k p).symm : k →+* k) f)]
  rw [PowerSeries.map_expand]
  have hmap : PowerSeries.map (frobenius k p)
      (PowerSeries.map ((frobeniusEquiv k p).symm : k →+* k) f) = f := by
    change PowerSeries.map ((frobenius k p).comp
      ((frobeniusEquiv k p).symm : k →+* k)) f = f
    rw [frobenius_comp_frobeniusEquiv_symm]
    rfl
  rw [hmap, PowerSeries.expand_apply]

private theorem exists_pow_eq_algebraMap
    (p : ℕ) [Fact p.Prime] (k A B : Type*)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a))
    (a : A) : ∃ b : B, b ^ p = algebraMap A B a := by
  refine ⟨eB.symm (PowerSeries.map ((frobeniusEquiv k p).symm : k →+* k) (eA a)), ?_⟩
  apply eB.injective
  rw [map_pow, eB.apply_symm_apply, powerSeries_frobenius_root, hAB]

private theorem fraction_exists_pow_eq_algebraMap
    (p : ℕ) (A B K L : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    (hroot : ∀ a : A, ∃ b : B, b ^ p = algebraMap A B a)
    (x : K) : ∃ y : L, y ^ p = algebraMap K L x := by
  obtain ⟨a, d, _, had⟩ := IsFractionRing.div_surjective A x
  obtain ⟨b, hb⟩ := hroot a
  obtain ⟨c, hc⟩ := hroot d
  refine ⟨algebraMap B L b / algebraMap B L c, ?_⟩
  rw [div_pow, ← map_pow, ← map_pow, hb, hc,
    ← IsScalarTower.algebraMap_apply A B L, ← IsScalarTower.algebraMap_apply A B L,
    IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L,
    ← map_div₀, had]

private theorem exists_root_of_isSeparable
    (p : ℕ) (F M R : Type*) [Field F] [Field M] [CommRing R]
    [ExpChar F p] [ExpChar R p] [Algebra F M] [Algebra F R] [Algebra M R]
    [IsScalarTower F M R] [Algebra.IsSeparable F M]
    (hroot : ∀ a : F, ∃ r : R, r ^ p = algebraMap F R a) :
    ∀ m : M, ∃ r : R, r ^ p = algebraMap M R m := by
  let S : Submodule F M := {
    carrier := {m | ∃ r : R, r ^ p = algebraMap M R m}
    zero_mem' := ⟨0, by rw [map_zero]; exact (frobenius R p).map_zero⟩
    add_mem' := by
      rintro x y ⟨r, hr⟩ ⟨s, hs⟩
      exact ⟨r + s, by rw [add_pow_expChar, hr, hs, map_add]⟩
    smul_mem' := by
      rintro a m ⟨r, hr⟩
      obtain ⟨s, hs⟩ := hroot a
      refine ⟨s * r, ?_⟩
      rw [mul_pow, hs, hr, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply F M R]
  }
  have hspan : Submodule.span F (Set.range fun m : M ↦ m ^ p) = ⊤ := by
    simpa using Field.span_map_pow_expChar_pow_eq_top_of_isSeparable
      (F := F) (E := M) (v := id) p 1 (by simp)
  have hle : Submodule.span F (Set.range fun m : M ↦ m ^ p) ≤ S :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun m ↦
      ⟨algebraMap M R m, (map_pow _ _ _).symm⟩
  intro m
  exact hle (hspan ▸ Submodule.mem_top)

private theorem tensor_pow_mem_base
    (p : ℕ) (F E M : Type*) [Field F] [Field E] [Field M]
    [ExpChar F p] [Algebra F E] [Algebra F M]
    (hpow : ∀ e : E, ∃ f : F, algebraMap F E f = e ^ p)
    (x : E ⊗[F] M) :
    ∃ m : M, (Algebra.TensorProduct.includeRight : M →ₐ[F] E ⊗[F] M) m = x ^ p := by
  have : ExpChar E p := expChar_of_injective_algebraMap (algebraMap F E).injective p
  have : ExpChar (E ⊗[F] M) p :=
    expChar_of_injective_algebraMap (algebraMap F (E ⊗[F] M)).injective p
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; exact (frobenius (E ⊗[F] M) p).map_zero.symm⟩
  | tmul e m =>
    obtain ⟨a, ha⟩ := hpow e
    refine ⟨algebraMap F M a * m ^ p, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← ha,
      Algebra.TensorProduct.includeRight_apply, ← Algebra.smul_def,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, add_pow_expChar]⟩

/-- An element of `E` whose `p`-th power is the image of an integral element is itself integral,
hence lies in any integral closure. -/
private theorem exists_algebraMap_eq_of_pow_eq
    (p : ℕ) (hp : 0 < p) (A R S F E : Type*) [CommRing A] [CommRing R] [CommRing S]
    [CommRing F] [CommRing E] [Algebra A F] [Algebra A E] [Algebra F E] [IsScalarTower A F E]
    [Algebra R F] [Algebra S E] [IsIntegralClosure R A F] [IsIntegralClosure S A E]
    (r : R) (x : E) (hx : x ^ p = algebraMap F E (algebraMap R F r)) :
    ∃ s : S, algebraMap S E s = x := by
  apply (IsIntegralClosure.isIntegral_iff (A := S) (R := A)).mp
  apply IsIntegral.of_pow hp
  rw [hx]
  exact ((IsIntegralClosure.isIntegral_iff (A := R)).mpr ⟨r, rfl⟩).map
    (IsScalarTower.toAlgHom A F E)

private theorem integralClosure_equiv_of_power
    (p : ℕ) (A R S F E : Type*) [CommRing A] [CommRing R] [CommRing S]
    [Field F] [CommRing E] [IsReduced E] [Nontrivial E] [ExpChar E p]
    [Algebra A F] [Algebra A E] [Algebra F E] [IsScalarTower A F E]
    [Algebra R F] [Algebra S E]
    [IsIntegralClosure R A F] [IsIntegralClosure S A E]
    (hp : p ≠ 0)
    (hpow : ∀ x : E, ∃ a : F, algebraMap F E a = x ^ p)
    (hroot : ∀ a : F, ∃ x : E, x ^ p = algebraMap F E a) :
    Nonempty (S ≃+* R) := by
  classical
  have hf := (algebraMap F E).injective
  have hR := IsIntegralClosure.algebraMap_injective R A F
  have hS := IsIntegralClosure.algebraMap_injective S A E
  have hex (s : S) : ∃ r : R,
      algebraMap F E (algebraMap R F r) = (algebraMap S E s) ^ p := by
    obtain ⟨a, ha⟩ := hpow (algebraMap S E s)
    have hi : IsIntegral A a := by
      apply IsIntegral.tower_bot hf
      rw [ha]
      exact ((IsIntegralClosure.isIntegral_iff (A := S)).mpr ⟨s, rfl⟩).pow p
    obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := R)).mp hi
    exact ⟨r, by rw [hr, ha]⟩
  choose f hf' using hex
  let g : S →+* R := {
    toFun := f
    map_one' := hR <| hf <| by
      rw [hf', map_one, map_one, map_one, one_pow]
    map_mul' := fun s t ↦ hR <| hf <| by
      rw [hf', map_mul, mul_pow, map_mul, map_mul, hf', hf']
    map_zero' := hR <| hf <| by
      rw [hf', map_zero, map_zero, map_zero, zero_pow hp]
    map_add' := fun s t ↦ hR <| hf <| by
      rw [hf', map_add, add_pow_expChar, map_add, map_add, hf', hf']
  }
  refine ⟨RingEquiv.ofBijective g ⟨?_, ?_⟩⟩
  · intro s t h
    apply hS
    apply sub_eq_zero.mp
    apply IsReduced.eq_zero _
    refine ⟨p, ?_⟩
    rw [sub_pow_expChar, ← hf', ← hf']
    exact sub_eq_zero.mpr (congrArg (fun r ↦ algebraMap F E (algebraMap R F r)) h)
  · intro r
    obtain ⟨x, hx⟩ := hroot (algebraMap R F r)
    obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_pow_eq p (Nat.pos_of_ne_zero hp) A R S F E r x hx
    refine ⟨s, hR <| hf ?_⟩
    change algebraMap F E (algebraMap R F (f s)) = _
    rw [hf', hs, hx]

private theorem ramificationIdx_ne_one_of_has_roots
    (p : ℕ) (R S : Type*) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [IsNoetherianRing S]
    (hp : 2 ≤ p) (hroot : ∀ r : R, ∃ s : S, s ^ p = algebraMap R S r)
    (q : Ideal S) [q.IsMaximal] (hq : q ≠ ⊥) : q.ramificationIdx R ≠ 1 := by
  intro he
  let T := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal T
  have hmap : (q.under R).map (algebraMap R S) ≤ q ^ 2 := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    obtain ⟨s, hs⟩ := hroot r
    have hsq : s ∈ q := (inferInstance : q.IsPrime).mem_of_pow_mem p (hs ▸ hr)
    have hsp : s ^ p ∈ q ^ p := Ideal.pow_mem_pow hsq p
    exact (Ideal.pow_le_pow_right hp) (hs ▸ hsp)
  have hlen : (q.under R).map (algebraMap R T) = m := by
    rwa [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff] at he
  have hm : m ≤ m * m := by
    rw [← pow_two]
    have hh := Ideal.map_mono (f := algebraMap S T) hmap
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S T, hlen, Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal] at hh
  have hm0 : m = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m m
    (IsNoetherian.noetherian _) hm (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
  refine hq (le_antisymm (fun s hs ↦ ?_) bot_le)
  apply (IsLocalization.injective T q.primeCompl_le_nonZeroDivisors)
  have hsm : algebraMap S T s ∈ m := by
    change algebraMap S (Localization.AtPrime q) s ∈ IsLocalRing.maximalIdeal _
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hs
  simpa [hm0] using hsm

private theorem not_weak_solution_of_isSeparable
    (p : ℕ) [Fact p.Prime]
    (A B K L M : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field M]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K M] [Algebra A M]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K M]
    [Module.Finite K M] [Algebra.IsSeparable K M] [Algebra.IsIntegral A B]
    [ExpChar K p]
    (hpow : ∀ l : L, ∃ a : K, algebraMap K L a = l ^ p)
    (hroot : ∀ a : K, ∃ l : L, l ^ p = algebraMap K L a)
    (D : IntegralClosureBaseChange A B K L M) : ¬ D.IsWeakSolution := by
  classical
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let := D.algebraBL₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.algebraAB₁
  let := D.algebraA₁B₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerKK₁L₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerAA₁K₁
  let := D.isScalarTowerBB₁L₁
  let := D.isScalarTowerABB₁
  let := D.isScalarTowerAA₁B₁
  let := D.isIntegralClosureA₁
  let := D.isIntegralClosureB₁
  let : Algebra A D.L₁ := ((algebraMap L D.L₁).comp (algebraMap A L)).toAlgebra
  have : IsScalarTower A B D.L₁ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap L D.L₁ (algebraMap A L a) = _
    rw [IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply B L D.L₁]
  have : IsScalarTower A K D.L₁ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap L D.L₁ (algebraMap A L a) = _
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply K L D.L₁]
  have : IsScalarTower A M D.L₁ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K D.L₁,
      IsScalarTower.algebraMap_apply K M D.L₁,
      ← IsScalarTower.algebraMap_apply A K M]
  have : IsScalarTower A D.B₁ D.L₁ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B D.L₁,
      IsScalarTower.algebraMap_apply B D.B₁ D.L₁,
      ← IsScalarTower.algebraMap_apply A B D.B₁]
  have : Nontrivial ((L ⊗[K] M) ⧸ nilradical (L ⊗[K] M)) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h ↦
      bot_ne_top ((Ideal.radical_eq_top (I := (⊥ : Ideal (L ⊗[K] M)))).mp h)
  have : IsReduced ((L ⊗[K] M) ⧸ nilradical (L ⊗[K] M)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have : Nontrivial D.L₁ := D.eL₁.toEquiv.nontrivial
  have : IsReduced D.L₁ := isReduced_of_injective D.eL₁ D.eL₁.injective
  have : ExpChar D.L₁ p := expChar_of_injective_algebraMap (algebraMap K D.L₁).injective p
  have hpow' (z : D.L₁) : ∃ m : M, algebraMap M D.L₁ m = z ^ p := by
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (D.eL₁ z)
    obtain ⟨m, hm⟩ := tensor_pow_mem_base p K L M hpow x
    refine ⟨m, D.eL₁.injective ?_⟩
    rw [D.eL₁_right, map_pow, ← hx, ← map_pow, ← hm]
  have hroot' : ∀ m : M, ∃ z : D.L₁, z ^ p = algebraMap M D.L₁ m := by
    refine exists_root_of_isSeparable p K M D.L₁ fun a ↦ ?_
    obtain ⟨l, hl⟩ := hroot a
    exact ⟨algebraMap L D.L₁ l, by rw [← map_pow, hl,
      ← IsScalarTower.algebraMap_apply K L D.L₁]⟩
  have : IsIntegralClosure D.B₁ A D.L₁ :=
    { algebraMap_injective := IsIntegralClosure.algebraMap_injective D.B₁ B D.L₁
      isIntegral_iff := fun {x} ↦
        ⟨fun hx ↦ (IsIntegralClosure.isIntegral_iff (A := D.B₁) (R := B)).mp hx.tower_top,
          fun hx ↦ isIntegral_trans (R := A) (A := B) x
            ((IsIntegralClosure.isIntegral_iff (A := D.B₁) (R := B)).mpr hx)⟩ }
  obtain ⟨e⟩ := integralClosure_equiv_of_power p A D.A₁ D.B₁ M D.L₁
    (Fact.out : p.Prime).ne_zero hpow' hroot'
  have : IsDomain D.A₁ := (IsIntegralClosure.algebraMap_injective D.A₁ A M).isDomain
    (algebraMap D.A₁ M)
  have : IsDomain D.B₁ := e.injective.isDomain e.toRingHom
  have : IsNoetherianRing D.A₁ := IsIntegralClosure.isNoetherianRing A K M D.A₁
  have : IsNoetherianRing D.B₁ := isNoetherianRing_of_ringEquiv D.A₁ e.symm
  have hroot'' (r : D.A₁) : ∃ s : D.B₁, s ^ p = algebraMap D.A₁ D.B₁ r := by
    obtain ⟨z, hz⟩ := hroot' (algebraMap D.A₁ M r)
    obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_pow_eq p (Fact.out : p.Prime).pos A D.A₁ D.B₁ M
      D.L₁ r z hz
    refine ⟨s, IsIntegralClosure.algebraMap_injective D.B₁ A D.L₁ ?_⟩
    rw [map_pow, hs, hz, D.ringSquare]
  have : Algebra.IsIntegral B D.B₁ := IsIntegralClosure.isIntegral_algebra B D.L₁
  have hinj : Function.Injective (algebraMap B D.B₁) := by
    apply Function.Injective.of_comp (f := algebraMap D.B₁ D.L₁)
    intro x y h
    apply IsFractionRing.injective B L
    apply (algebraMap L D.L₁).injective
    simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply] using h
  obtain ⟨q, hq⟩ := Ideal.exists_maximal D.B₁
  have hq0 : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hq fun h ↦
    IsDiscreteValuationRing.not_isField B (isField_of_isIntegral_of_isField hinj h)
  intro hw
  exact ramificationIdx_ne_one_of_has_roots p D.A₁ D.B₁ (Fact.out : p.Prime).two_le
    hroot'' q hq0 (hw q hq)

private theorem finrank_frobeniusFieldRange_eq
    (p : ℕ) (F M : Type*) [Field F] [Field M] [ExpChar F p] [ExpChar M p]
    [Algebra F M] [Module.Finite F M]
    [Module.Finite (frobenius F p).fieldRange F] :
    Module.finrank (frobenius M p).fieldRange M =
      Module.finrank (frobenius F p).fieldRange F := by
  let P := (frobenius F p).fieldRange
  let Q := (frobenius M p).fieldRange
  let f : P →+* Q := ((algebraMap F M).comp P.subtype).codRestrict Q (by
    rintro ⟨a, b, hb⟩
    refine ⟨algebraMap F M b, ?_⟩
    change (algebraMap F M b) ^ p = algebraMap F M a
    rw [← map_pow]
    exact congrArg (algebraMap F M) hb)
  let : Algebra P Q := f.toAlgebra
  have : IsScalarTower P F M := inferInstance
  have : IsScalarTower P Q M := ⟨fun a q m ↦ by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _⟩
  have hd : Module.finrank F M = Module.finrank P Q :=
    Algebra.finrank_eq_of_equiv_equiv (frobenius F p).rangeRestrictFieldEquiv
      (frobenius M p).rangeRestrictFieldEquiv (by
        ext x
        change algebraMap F M (x ^ p) = (algebraMap F M x) ^ p
        exact map_pow _ _ _)
  have : Module.Finite P Q := FiniteDimensional.of_finrank_pos (hd ▸ Module.finrank_pos)
  have : Module.Finite P M := Module.Finite.trans F M
  have : Module.Finite Q M := Module.Finite.of_restrictScalars_finite P Q M
  have h₁ := Module.finrank_mul_finrank P F M
  have h₂ := Module.finrank_mul_finrank P Q M
  rw [← hd] at h₂
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := F) (M := M))
  exact h₂.trans (h₁.symm.trans (mul_comm _ _))

private theorem isSeparable_of_span_pow_eq_top
    (p : ℕ) (F M : Type*) [Field F] [Field M] [ExpChar F p] [ExpChar M p]
    [Algebra F M] [Module.Finite F M]
    (hspan : Submodule.span F (Set.range fun m : M ↦ m ^ p) = ⊤) :
    Algebra.IsSeparable F M := by
  let S := separableClosure F M
  have : ExpChar S p := expChar_of_injective_algebraMap (algebraMap F S).injective p
  have hstep (n : ℕ) (hn : ∀ m : M, m ^ p ^ (n + 1) ∈ S) :
      ∀ m : M, m ^ p ^ n ∈ S := by
    let V : Submodule F M := {
      carrier := {m | m ^ p ^ n ∈ S}
      zero_mem' := by
        change iterateFrobenius M p n 0 ∈ S
        rw [map_zero]
        exact S.zero_mem
      add_mem' := by
        intro x y hx hy
        change iterateFrobenius M p n (x + y) ∈ S
        rw [map_add]
        exact S.add_mem hx hy
      smul_mem' := by
        intro a x hx
        change (a • x) ^ p ^ n ∈ S
        rw [Algebra.smul_def, mul_pow, ← map_pow]
        exact S.mul_mem (S.algebraMap_mem _) hx
    }
    have hle : Submodule.span F (Set.range fun m : M ↦ m ^ p) ≤ V := by
      apply Submodule.span_le.mpr
      rintro _ ⟨m, rfl⟩
      change (m ^ p) ^ p ^ n ∈ S
      rw [← pow_mul, ← pow_succ']
      exact hn m
    exact fun m ↦ hle (hspan ▸ Submodule.mem_top)
  have hdown (n : ℕ) (hn : ∀ m : M, m ^ p ^ n ∈ S) : ∀ m : M, m ∈ S := by
    induction n with
    | zero => simpa using hn
    | succ n ih => exact ih (hstep n hn)
  refine ⟨fun m ↦ hdown (IsPurelyInseparable.exponent S M) (fun x ↦ ?_) m⟩
  obtain ⟨s, hs⟩ := IsPurelyInseparable.exponent_def' S p x
  exact hs ▸ s.property

private theorem exists_root_of_not_isSeparable_of_frobeniusFieldRange_prime
    (p : ℕ) (F M : Type*) [Field F] [Field M] [ExpChar F p] [ExpChar M p]
    [Algebra F M] [Module.Finite F M]
    (hprime : (Module.finrank (frobenius M p).fieldRange M).Prime)
    (hsep : ¬ Algebra.IsSeparable F M) :
    ∀ a : F, ∃ m : M, m ^ p = algebraMap F M a := by
  classical
  let Q := (frobenius M p).fieldRange
  let J := IntermediateField.adjoin F (Set.range fun m : M ↦ m ^ p)
  let I : IntermediateField Q M := {
    J.toSubfield with
    algebraMap_mem' := by
      rintro ⟨m, r, hr⟩
      exact IntermediateField.subset_adjoin F _ ⟨r, hr⟩
  }
  have : IsSimpleOrder (IntermediateField Q M) :=
    IntermediateField.isSimpleOrder_of_finrank_prime Q M hprime
  rcases eq_bot_or_eq_top I with hI | hI
  · intro a
    have ha : algebraMap F M a ∈ I := J.algebraMap_mem a
    rw [hI, IntermediateField.mem_bot] at ha
    obtain ⟨q, hq⟩ := ha
    exact hq ▸ q.property
  · exfalso
    apply hsep
    apply isSeparable_of_span_pow_eq_top p F M
    have hJ : J = ⊤ := by
      apply top_unique
      intro m _
      change m ∈ I
      rw [hI]
      trivial
    have hspan : J.toSubalgebra.toSubmodule =
        Submodule.span F (Set.range fun m : M ↦ m ^ p) := by
      rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x), Algebra.adjoin_eq_span]
      congr 1
      exact congrArg (fun S : Submonoid M ↦ (S : Set M))
        (MonoidHom.mrange (powMonoidHom (α := M) p)).closure_eq
    rw [← hspan, hJ]
    rfl

private theorem exists_ringEquiv_of_pow_mem
    (p : ℕ) (F E : Type*) [Field F] [Field E] [ExpChar E p] [Algebra F E]
    (hpow : ∀ x : E, ∃ a : F, algebraMap F E a = x ^ p)
    (hroot : ∀ a : F, ∃ x : E, x ^ p = algebraMap F E a) :
    ∃ e : E ≃+* F, ∀ x : E, algebraMap F E (e x) = x ^ p := by
  obtain ⟨g, hg⟩ := exists_ringHom_algebraMap_eq_pow p F E hpow
  exact ⟨RingEquiv.ofBijective g ⟨g.injective, fun a ↦ (hroot a).elim fun x hx ↦
    ⟨x, (algebraMap F E).injective ((hg x).trans hx)⟩⟩, hg⟩

private theorem finrank_eq_prime_of_subst_X_pow
    (p : ℕ) [Fact p.Prime] (k A B K L : Type*)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra k A] [Algebra k B] [Algebra k K]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FaithfulSMul A B]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a)) :
    Module.finrank K L = p := by
  have hp : p.Prime := Fact.out
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have : Module.Finite A B := moduleFinite_of_subst_X_pow p hp.ne_zero k A B eA eB hAB
  have hdeg := IsFractionRing.finrank_eq A K B L
  have hpos : 0 < Module.finrank K L := hdeg ▸ Module.finrank_pos
  have : Module.Finite K L := FiniteDimensional.of_finrank_pos hpos
  have hle : Module.finrank K L ≤ p := by
    rw [hdeg]
    simpa using LinearMap.finrank_le_finrank_of_surjective
      (linearCombination_surjective_of_subst_X_pow p hp.ne_zero k A B eA eB hAB)
  have : IsPurelyInseparable K L := extension_purelyInseparable p k A B K L eA eB hAB
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K L p
  have hn0 : n ≠ 0 := by
    intro hn0
    rw [hn0, pow_zero] at hn
    have hs : Algebra.IsSeparable K L := by
      have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := K) (E := L)).mp hn
      refine ⟨fun x ↦ ?_⟩
      obtain ⟨a, rfl⟩ := hsurj.2 x
      exact isSeparable_algebraMap a
    exact field_extension_not_separable p k A B K L eA eB hAB hs
  apply le_antisymm hle
  rw [hn]
  exact le_self_pow₀ hp.one_lt.le hn0

private theorem finrank_frobeniusFieldRange_of_rootField
    (p : ℕ) (F E : Type*) [Field F] [Field E] [ExpChar F p] [ExpChar E p]
    [Algebra F E]
    (hpow : ∀ x : E, ∃ a : F, algebraMap F E a = x ^ p)
    (hroot : ∀ a : F, ∃ x : E, x ^ p = algebraMap F E a) :
    Module.finrank (frobenius F p).fieldRange F = Module.finrank F E := by
  obtain ⟨e, he⟩ := exists_ringEquiv_of_pow_mem p F E hpow hroot
  symm
  apply Algebra.finrank_eq_of_equiv_equiv (frobenius F p).rangeRestrictFieldEquiv e
  ext a
  change a ^ p = e (algebraMap F E a)
  apply (algebraMap F E).injective
  rw [he, map_pow]

/-- For `k[[x]] → k[[x^(1/p)]]` in positive characteristic `p`, every weak solution is
inseparable, while every finite inseparable extension of `k((x))` is a solution. -/
@[stacks 09EP]
theorem weakSolution_isInseparable_and_inseparable_isSolution
    (p : ℕ) [Fact p.Prime]
    (k : Type uk) (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [Field k] [PerfectField k] [CharP k p]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra k A] [Algebra k B] [Algebra k K] [Algebra k L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower k A B] [IsScalarTower k A K] [IsScalarTower k B L]
    [IsScalarTower k K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    (eA : A ≃ₐ[k] PowerSeries k) (eB : B ≃ₐ[k] PowerSeries k)
    (eK : K ≃ₐ[k] LaurentSeries k) (eL : L ≃ₐ[k] LaurentSeries k)
    (hAB : ∀ a : A, eB (algebraMap A B a) =
      PowerSeries.subst (PowerSeries.X ^ p) (eA a))
    (_hAK : ∀ a : A, eK (algebraMap A K a) = (eA a : LaurentSeries k))
    (_hBL : ∀ b : B, eL (algebraMap B L b) = (eB b : LaurentSeries k)) :
    (∀ (K₁ : Type uK₁) [Field K₁] [Algebra K K₁] [Algebra A K₁]
        [IsScalarTower A K K₁] [Module.Finite K K₁]
        (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
          A B K L K₁),
        D.IsWeakSolution → ¬ Algebra.IsSeparable K K₁) ∧
      ∀ (K₁ : Type uK₁) [Field K₁] [Algebra K K₁] [Algebra A K₁]
        [IsScalarTower A K K₁] [Module.Finite K K₁],
        ¬ Algebra.IsSeparable K K₁ →
          ∃ D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁,
              max uL uK₁, uK₁, max uL uK₁} A B K L K₁,
            D.IsSolution.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁, v} := by
  have hp : p.Prime := Fact.out
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  have : Algebra.IsIntegral A B := ring_extension_integral p k A B eA eB hAB
  have hpow := fraction_power_mem_base p A B K L
    (power_mem_base p k A B eA eB hAB)
  have hroot := fraction_exists_pow_eq_algebraMap p A B K L
    (exists_pow_eq_algebraMap p k A B eA eB hAB)
  refine ⟨fun K₁ _ _ _ _ _ D hw hs ↦ ?_, fun K₁ _ _ _ _ _ hsep ↦ ?_⟩
  · let := hs
    exact not_weak_solution_of_isSeparable p A B K L K₁ hpow hroot D hw
  have : ExpChar K₁ p := expChar_of_injective_algebraMap (algebraMap K K₁).injective p
  have hd : Module.finrank (frobenius K p).fieldRange K = p :=
    (finrank_frobeniusFieldRange_of_rootField p K L hpow hroot).trans
      (finrank_eq_prime_of_subst_X_pow p k A B K L eA eB hAB)
  have : Module.Finite (frobenius K p).fieldRange K :=
    FiniteDimensional.of_finrank_pos (by rw [hd]; exact hp.pos)
  have hprime : (Module.finrank (frobenius K₁ p).fieldRange K₁).Prime := by
    rwa [finrank_frobeniusFieldRange_eq p K K₁, hd]
  have hroot₁ := exists_root_of_not_isSeparable_of_frobeniusFieldRange_prime
    p K K₁ hprime hsep
  obtain ⟨f⟩ := nonempty_algHom_of_pow_mem p K L K₁ hpow hroot₁
  have : IsPurelyInseparable K L := extension_purelyInseparable p k A B K L eA eB hAB
  exact exists_solution_of_algHom A B K L K₁ f

end IsDiscreteValuationRing
