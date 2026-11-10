module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init

public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra

/-!
# The completed base change at a prime where the map is quasi-finite

Let `R` be a Noetherian ring, let `S` be an `R`-algebra of finite type, let `q ⊂ S` be a prime
lying over `p ⊂ R`, and assume `R → S` is quasi-finite at `q`. Write `Rₚ^∧` and `S_q^∧` for the
completions of the local rings at their maximal ideals. Then `S_q^∧` is a direct factor of the
base change `S ⊗[R] Rₚ^∧`: there is an idempotent `e` of `S ⊗[R] Rₚ^∧` such that, as
`S`-algebras, `S ⊗[R] Rₚ^∧ = S_q^∧ × (S ⊗[R] Rₚ^∧) ⧸ (e)`.

## Main results

* `AdicCompletion.factor_evalₐ`: the transition maps of the tower defining an adic completion are
  compatible with its projections `AdicCompletion.evalₐ`.
* `AdicCompletion.nonempty_algEquiv_of_algEquiv`: adic completions are transported along an
  isomorphism of the base rings matching the ideals.
* `AdicCompletion.exists_isIdempotentElem_nonempty_algEquiv_prod_quotient`: for `R` Noetherian and
  `S` of finite type over `R` and quasi-finite at a prime `q` lying over `p`, the base change of
  `S` along `Rₚ^∧` is, as an `S`-algebra, the product of `S_q^∧` with the factor cut out by an
  idempotent; `Stacks.AdicCompletion.QuasiFiniteFactor.solution` is the same statement.

## References

* [StackProject 07NC](https://stacks.math.columbia.edu/tag/07NC), Lemma 10.126.4.
* [StackProject 07N9](https://stacks.math.columbia.edu/tag/07N9), Lemma 10.97.7.
* [StackProject 00QB](https://stacks.math.columbia.edu/tag/00QB), Lemma 10.123.14.

## Tags

adic completion, quasi-finite, local ring, base change, idempotent, product decomposition
-/

@[expose] public section

/-- The transition maps of the tower defining an adic completion are compatible with its
projections `AdicCompletion.evalₐ`. -/
theorem AdicCompletion.factor_evalₐ {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ}
    (hmn : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨y, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq, ← neg_sub]
  have h := y.property hmn
  rw [SModEq.sub_mem] at h
  exact neg_mem (by simpa using h)

/-- Adic completions are transported along an isomorphism of the base rings matching the ideals. -/
theorem AdicCompletion.nonempty_algEquiv_of_algEquiv {A : Type*} [CommRing A]
    {R₁ : Type*} [CommRing R₁] [Algebra A R₁] {R₂ : Type*} [CommRing R₂] [Algebra A R₂]
    (e : R₁ ≃ₐ[A] R₂) (I₁ : Ideal R₁) (I₂ : Ideal R₂) (h : I₂ = Ideal.map (e : R₁ →+* R₂) I₁) :
    Nonempty (AdicCompletion I₁ R₁ ≃ₐ[A] AdicCompletion I₂ R₂) := by
  have hpow : ∀ n : ℕ, I₂ ^ n = Ideal.map (e : R₁ →+* R₂) (I₁ ^ n) := fun n => by
    rw [Ideal.map_pow, h]
  let E : (n : ℕ) → ((R₁ ⧸ I₁ ^ n) ≃ₐ[A] (R₂ ⧸ I₂ ^ n)) := fun n =>
    Ideal.quotientEquivAlg (I₁ ^ n) (I₂ ^ n) e (hpow n)
  have hEmk : ∀ (n : ℕ) (x : R₁),
      (E n) (Ideal.Quotient.mk (I₁ ^ n) x) = Ideal.Quotient.mk (I₂ ^ n) (e x) := fun n x => rfl
  have hE : ∀ (m n : ℕ) (hmn : m ≤ n) (y : R₁ ⧸ I₁ ^ n),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) ((E n) y) =
        (E m) (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) y) := by
    intro m n hmn y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hEmk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, hEmk]
  have hE' : ∀ (m n : ℕ) (hmn : m ≤ n) (y : R₂ ⧸ I₂ ^ n),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) ((E n).symm y) =
        (E m).symm (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) y) := by
    intro m n hmn y
    obtain ⟨z, rfl⟩ := (E n).surjective y
    rw [AlgEquiv.symm_apply_apply, hE m n hmn z, AlgEquiv.symm_apply_apply]
  refine ⟨AlgEquiv.ofAlgHom
    (AdicCompletion.liftAlgHom I₂ (fun n =>
        (E n).toAlgHom.comp ((AdicCompletion.evalₐ I₁ n).restrictScalars A))
      (fun {m n} hmn => AlgHom.ext fun x => by
        have h2 := hE m n hmn (AdicCompletion.evalₐ I₁ n x)
        rw [AdicCompletion.factor_evalₐ I₁ hmn] at h2
        simpa using h2))
    (AdicCompletion.liftAlgHom I₁ (fun n =>
        (E n).symm.toAlgHom.comp ((AdicCompletion.evalₐ I₂ n).restrictScalars A))
      (fun {m n} hmn => AlgHom.ext fun x => by
        have h2 := hE' m n hmn (AdicCompletion.evalₐ I₂ n x)
        rw [AdicCompletion.factor_evalₐ I₂ hmn] at h2
        simpa using h2))
    (AlgHom.ext fun x => AdicCompletion.ext_evalₐ fun n => by simp)
    (AlgHom.ext fun x => AdicCompletion.ext_evalₐ fun n => by simp)⟩

namespace Stacks.AdicCompletion.QuasiFiniteFactor

open TensorProduct IsLocalRing

/-- The two-factor decomposition of a commutative ring attached to an idempotent element, with the
factor complementary to `T ⧸ (e)` identified with a given algebra `A`. -/
private theorem nonempty_algEquiv_prod_quotient_of_nonempty_algEquiv_quotient {S : Type*}
    [CommRing S] {T : Type*} [CommRing T] [Algebra S T] {A : Type*} [CommRing A] [Algebra S A]
    {e : T} (he : IsIdempotentElem e)
    (h : Nonempty ((T ⧸ Ideal.span {1 - e}) ≃ₐ[S] A)) :
    Nonempty (T ≃ₐ[S] A × (T ⧸ Ideal.span {e})) :=
  h.elim fun h => ⟨(AlgEquiv.prodQuotientOfIsIdempotentElem S he.one_sub he (by ring)
    (by rw [sub_mul, one_mul, he, sub_self])).trans (h.prodCongr (AlgEquiv.refl))⟩

/-- A factor of a product of algebras is the quotient of the product by the idempotent
`1 - Pi.single j 1`. -/
private theorem nonempty_algEquiv_quotient_span_one_sub_single {ι : Type*} [DecidableEq ι]
    {B : Type*} [CommRing B] (X : ι → Type*) [∀ i, CommRing (X i)] [∀ i, Algebra B (X i)] (j : ι) :
    Nonempty ((((i : ι) → X i) ⧸ Ideal.span {1 - Pi.single j (1 : X j)}) ≃ₐ[B] X j) := by
  have hsurj : Function.Surjective (Pi.evalAlgHom B X j) := fun a => ⟨Pi.single j a, by simp⟩
  have hker : RingHom.ker (Pi.evalAlgHom B X j).toRingHom
      = Ideal.span {1 - Pi.single j (1 : X j)} := by
    apply le_antisymm
    · intro z hz
      rw [Ideal.mem_span_singleton']
      refine ⟨z, ?_⟩
      funext i
      by_cases h : i = j
      · subst h; simp [RingHom.mem_ker] at hz ⊢; simp [hz]
      · simp [h]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      simp [RingHom.mem_ker]
  exact ⟨(Ideal.quotientEquivAlgOfEq B hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)⟩

/-- For `S'` finite over the Noetherian ring `R` and
`q'` a prime of `S'` over `p`, the completion of the local ring `S'_{q'}` is the factor of
`S' ⊗[R] Rₚ^∧` cut out by an idempotent. -/
private theorem exists_isIdempotentElem_nonempty_algEquiv_quotient_of_finite {R S' : Type*}
    [CommRing R] [CommRing S'] [Algebra R S'] [IsNoetherianRing R] [Module.Finite R S']
    (p : Ideal R) [p.IsPrime] (q' : Ideal S') [q'.IsPrime] [q'.LiesOver p]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq' : Type*) [CommRing Sq'] [Algebra S' Sq'] [IsLocalization.AtPrime Sq' q']
    [IsLocalRing Sq'] :
    ∃ ε : S' ⊗[R] AdicCompletion (maximalIdeal Rp) Rp, IsIdempotentElem ε ∧
      Nonempty (((S' ⊗[R] AdicCompletion (maximalIdeal Rp) Rp) ⧸ Ideal.span {1 - ε}) ≃ₐ[S']
        AdicCompletion (maximalIdeal Sq') Sq') := by
  classical
  obtain ⟨Φ⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (S := S') p Rp
    (fun x => Localization.AtPrime x.1)
  set x₀ : p.primesOver S' := ⟨q', ‹q'.IsPrime›, ‹q'.LiesOver p›⟩ with hx₀
  set E : (∀ x : p.primesOver S', AdicCompletion (maximalIdeal (Localization.AtPrime x.1))
      (Localization.AtPrime x.1)) := Pi.single x₀ 1 with hE
  have hEid : IsIdempotentElem E := by
    change E * E = E
    funext i
    by_cases h : i = x₀
    · rw [h]; simp [hE]
    · simp [hE, h]
  refine ⟨Φ.symm E, hEid.map Φ.symm, ?_⟩
  · obtain ⟨Ψ⟩ := nonempty_algEquiv_quotient_span_one_sub_single (B := S')
      (fun x : p.primesOver S' => AdicCompletion (maximalIdeal (Localization.AtPrime x.1))
        (Localization.AtPrime x.1)) x₀
    obtain ⟨T⟩ := AdicCompletion.nonempty_algEquiv_of_algEquiv
      (IsLocalization.algEquiv q'.primeCompl (Localization.AtPrime q') Sq')
      (maximalIdeal (Localization.AtPrime q')) (maximalIdeal Sq')
      (IsLocalRing.map_ringEquiv_maximalIdeal
        (IsLocalization.algEquiv q'.primeCompl (Localization.AtPrime q') Sq').toRingEquiv).symm
    refine ⟨((Ideal.quotientEquivAlg _ _ Φ ?_).trans Ψ).trans T⟩
    rw [Ideal.map_span]
    simp [hE]

/-- Let `S' ⊆ S` be a subalgebra and `g ∈ S'` an element outside a prime `q`
of `S` such that every element of `S` lies in `S'` after multiplication by a power of `g`. Then the
local ring of `S` at `q` is also the local ring of `S'` at `q' = q ∩ S'`. -/
private theorem isLocalization_atPrime_comap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq q] (S' : Subalgebra R S) (g : S') (hg : (g : S) ∉ q)
    (hmem : ∀ y : S, ∃ n : ℕ, (g : S) ^ n * y ∈ S') :
    IsLocalization.AtPrime Sq (q.comap S'.val.toRingHom) := by
  have hqp : q.IsPrime := ‹_›
  have hmap : ∀ a : S', algebraMap S' Sq a = algebraMap S Sq (a : S) := fun a =>
    IsScalarTower.algebraMap_apply S' S Sq a
  have hgpow : ∀ n : ℕ, (g : S) ^ n ∉ q := fun n hn => hg (hqp.mem_of_pow_mem n hn)
  refine ⟨⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩⟩
  · rw [hmap]
    exact IsLocalization.map_units Sq (⟨(y : S), y.2⟩ : q.primeCompl)
  · obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj q.primeCompl z
    obtain ⟨n, hn⟩ := hmem y
    obtain ⟨m, hm⟩ := hmem (s : S)
    obtain ⟨a, ha⟩ : ∃ a : S', (a : S) = (g : S) ^ n * y := ⟨⟨_, hn⟩, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : S', (b : S) = (g : S) ^ m * (s : S) := ⟨⟨_, hm⟩, rfl⟩
    have hys' : z * algebraMap S Sq (s : S) = algebraMap S Sq y := hys
    have e1 : ((g ^ n * b : S') : S) = ((g : S) ^ n * (g : S) ^ m) * (s : S) := by
      push_cast [hb]; ring
    have e2 : ((g ^ m * a : S') : S) = ((g : S) ^ n * (g : S) ^ m) * y := by
      push_cast [ha]; ring
    refine ⟨⟨g ^ m * a, ⟨g ^ n * b, ?_⟩⟩, ?_⟩
    · intro hc
      have hc : ((g ^ n * b : S') : S) ∈ q := hc
      rw [e1] at hc
      exact (hqp.mem_or_mem hc).elim
        (fun hc' => (hqp.mem_or_mem hc').elim (hgpow n) (hgpow m)) s.2
    · have key : z * algebraMap S Sq ((g ^ n * b : S') : S)
          = algebraMap S Sq ((g ^ m * a : S') : S) := by
        rw [e1, e2, map_mul, map_mul, ← mul_assoc, mul_comm z, mul_assoc, hys', map_mul, map_mul]
      rwa [hmap, hmap]
  · rw [hmap, hmap] at h
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := q.primeCompl) h
    obtain ⟨n, hn⟩ := hmem (c : S)
    obtain ⟨d, hd⟩ : ∃ d : S', (d : S) = (g : S) ^ n * (c : S) := ⟨⟨_, hn⟩, rfl⟩
    refine ⟨⟨d, ?_⟩, ?_⟩
    · intro hcc
      have hcc : ((d : S)) ∈ q := hcc
      rw [hd] at hcc
      exact (hqp.mem_or_mem hcc).elim (hgpow n) c.2
    · apply Subtype.ext
      push_cast [hd]
      rw [mul_assoc, mul_assoc, hc]

/-- An element outside a prime `q` becomes a unit in the completion of the local ring at `q`. -/
private theorem isUnit_algebraMap_adicCompletion_of_notMem {S : Type*} [CommRing S]
    (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq q] [IsLocalRing Sq] {y : S} (hy : y ∉ q) :
    IsUnit (algebraMap S (AdicCompletion (maximalIdeal Sq) Sq) y) := by
  rw [IsScalarTower.algebraMap_apply S Sq (AdicCompletion (maximalIdeal Sq) Sq)]
  exact (IsLocalization.map_units Sq (⟨y, hy⟩ : q.primeCompl)).map _

/-- An element becomes `1` in its quotient by the ideal generated by `1 - e`. -/
private theorem mk_span_one_sub_self {T : Type*} [CommRing T] (e : T) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
  rw [Ideal.Quotient.mk_eq_one_iff_sub_mem, show e - 1 = -(1 - e) by ring]
  exact neg_mem (Ideal.mem_span_singleton_self _)

/-- A ring homomorphism sending `e` to `1` kills the ideal generated by `1 - e`. -/
private theorem map_eq_zero_of_mem_span_one_sub {T U F : Type*} [CommRing T] [Ring U]
    [FunLike F T U] [RingHomClass F T U] (f : F) {e z : T} (hf : f e = 1)
    (hz : z ∈ Ideal.span {1 - e}) : f z = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_mul, map_sub, map_one, hf, sub_self, mul_zero]

set_option maxHeartbeats 400000 in
-- The four algebra structures on `C = S_q^∧` (over `R`, `S`, `S'` and `Sq`) and the two tensor
-- products over `R` make the defeq checks in this single declaration cost about twice the default
-- budget; the argument itself is elementary.
/-- Let `S' ⊆ S` be a subalgebra and `g ∈ S'` an element
outside `q` such that every element of `S` lies in `S'` after multiplication by a power of `g`,
and let `ε` be an idempotent of `S' ⊗[R] Λ` cutting out the completion of `S'_{q'}`, where
`q' = q ∩ S'`. Then the image `e` of `ε` in `S ⊗[R] Λ` cuts out `S_q^∧`. -/
private theorem exists_isIdempotentElem_nonempty_algEquiv_quotient_of_exists_pow_smul_mem
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime]
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q] [IsLocalRing Sq]
    (Λ : Type*) [CommRing Λ] [Algebra R Λ] (S' : Subalgebra R S) (g : S') (hg : (g : S) ∉ q)
    (hmem : ∀ y : S, ∃ n : ℕ, (g : S) ^ n * y ∈ S')
    (ε : S' ⊗[R] Λ) (hε : IsIdempotentElem ε)
    (hA : Nonempty (((S' ⊗[R] Λ) ⧸ Ideal.span {1 - ε}) ≃ₐ[S']
      AdicCompletion (maximalIdeal Sq) Sq)) :
    ∃ e : S ⊗[R] Λ, IsIdempotentElem e ∧
      Nonempty (((S ⊗[R] Λ) ⧸ Ideal.span {1 - e}) ≃ₐ[S]
        AdicCompletion (maximalIdeal Sq) Sq) := by
  classical
  obtain ⟨Φ⟩ := hA
  let instR : Algebra R (AdicCompletion (maximalIdeal Sq) Sq) :=
    ((algebraMap S (AdicCompletion (maximalIdeal Sq) Sq)).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S (AdicCompletion (maximalIdeal Sq) Sq) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S' (AdicCompletion (maximalIdeal Sq) Sq) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  set C := AdicCompletion (maximalIdeal Sq) Sq with hCdef
  set ψ : (S' ⊗[R] Λ) →ₐ[R] (S ⊗[R] Λ) :=
    Algebra.TensorProduct.map S'.val (AlgHom.id R Λ) with hψdef
  have hψtmul : ∀ (a : S') (x : Λ), ψ (a ⊗ₜ[R] x) = (a : S) ⊗ₜ[R] x := fun a x ↦ by
    simp [hψdef]
  refine ⟨ψ ε, hε.map ψ, ?_⟩
  set I' : Ideal (S' ⊗[R] Λ) := Ideal.span {1 - ε} with hI'
  set I : Ideal (S ⊗[R] Λ) := Ideal.span {1 - ψ ε} with hI
  set f' : (S' ⊗[R] Λ) →ₐ[S'] C := Φ.toAlgHom.comp (Ideal.Quotient.mkₐ S' I') with hf'
  have hf'apply : ∀ z, f' z = Φ (Ideal.Quotient.mk I' z) := fun z => rfl
  set μ : Λ →ₐ[R] C := (f'.restrictScalars R).comp Algebra.TensorProduct.includeRight with hμ
  have hμapply : ∀ x : Λ, μ x = f' (1 ⊗ₜ[R] x) := fun x => rfl
  set f : (S ⊗[R] Λ) →ₐ[S] C :=
    Algebra.TensorProduct.lift (Algebra.ofId S C) μ (fun _ _ => Commute.all _ _) with hf
  have htmul_one : ∀ a : S', (a ⊗ₜ[R] (1 : Λ) : S' ⊗[R] Λ) = algebraMap S' (S' ⊗[R] Λ) a := by
    intro a
    rw [Algebra.TensorProduct.algebraMap_apply]; simp
  have hfψ : ∀ z, f (ψ z) = f' z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      rw [hψtmul, hf, Algebra.TensorProduct.lift_tmul, hμapply]
      have h1 : (a ⊗ₜ[R] x : S' ⊗[R] Λ) = algebraMap S' (S' ⊗[R] Λ) a * (1 ⊗ₜ[R] x) := by
        rw [← htmul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h1, map_mul, AlgHom.commutes]
      rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  have hfe : f (ψ ε) = 1 := by
    rw [hfψ, hf'apply, mk_span_one_sub_self, map_one]
  set F : ((S ⊗[R] Λ) ⧸ I) →ₐ[S] C := Ideal.Quotient.liftₐ I f
    (fun _ => map_eq_zero_of_mem_span_one_sub f hfe) with hF
  have hFmk : ∀ t, F (Ideal.Quotient.mk I t) = f t := fun t => rfl
  have hmkψε : Ideal.Quotient.mk I (ψ ε) = 1 := mk_span_one_sub_self _
  set α : ((S' ⊗[R] Λ) ⧸ I') →+* ((S ⊗[R] Λ) ⧸ I) :=
    Ideal.Quotient.lift I' ((Ideal.Quotient.mk I).comp ψ.toRingHom)
      (fun _ => map_eq_zero_of_mem_span_one_sub ((Ideal.Quotient.mk I).comp ψ.toRingHom)
        (by simpa using hmkψε)) with hα
  have hαmk : ∀ z, α (Ideal.Quotient.mk I' z) = Ideal.Quotient.mk I (ψ z) := fun z => rfl
  have hFα : ∀ a, F (α a) = Φ a := by
    intro a
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hαmk, hFmk, hfψ, hf'apply]
  have hgunitC : IsUnit (Φ (Ideal.Quotient.mk I' (g ⊗ₜ[R] (1 : Λ)))) := by
    have h1 : Φ (Ideal.Quotient.mk I' (g ⊗ₜ[R] (1 : Λ))) = algebraMap S C (g : S) := by
      rw [← hf'apply]
      rw [htmul_one, AlgHom.commutes]
      rfl
    rw [h1]
    exact isUnit_algebraMap_adicCompletion_of_notMem q Sq hg
  obtain ⟨v, hv⟩ : ∃ v, Ideal.Quotient.mk I' (g ⊗ₜ[R] (1 : Λ)) * v = 1 := by
    have h3 : IsUnit (Ideal.Quotient.mk I' (g ⊗ₜ[R] (1 : Λ))) := by
      have h4 := hgunitC.map Φ.symm
      rwa [Φ.symm_apply_apply] at h4
    exact h3.exists_right_inv
  have hwmk : α (Ideal.Quotient.mk I' (g ⊗ₜ[R] (1 : Λ)))
      = Ideal.Quotient.mk I ((g : S) ⊗ₜ[R] (1 : Λ)) := by
    rw [hαmk, hψtmul]
  have hw' : α (Ideal.Quotient.mk I' (g ⊗ₜ[R] (1 : Λ))) * α v = 1 :=
    (map_mul α _ v).symm.trans ((congrArg (⇑α) hv).trans (map_one α))
  have hw : Ideal.Quotient.mk I ((g : S) ⊗ₜ[R] (1 : Λ)) * α v = 1 := by
    rwa [← hwmk]
  have hαsurj : Function.Surjective α := by
    intro a
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction t using TensorProduct.inductionOn with
    | tmul y x =>
      obtain ⟨n, hn⟩ := hmem y
      refine ⟨v ^ n * Ideal.Quotient.mk I' ((⟨(g : S) ^ n * y, hn⟩ : S') ⊗ₜ[R] x), ?_⟩
      rw [map_mul, map_pow, hαmk, hψtmul]
      have h5' : (((g : S) ^ n * y) ⊗ₜ[R] x : S ⊗[R] Λ)
          = ((g : S) ⊗ₜ[R] (1 : Λ)) ^ n * (y ⊗ₜ[R] x) := by
        rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h5 : Ideal.Quotient.mk I ((((g : S) ^ n * y)) ⊗ₜ[R] x)
          = (Ideal.Quotient.mk I ((g : S) ⊗ₜ[R] (1 : Λ))) ^ n
            * Ideal.Quotient.mk I (y ⊗ₜ[R] x) := by
        rw [h5', map_mul (Ideal.Quotient.mk I), map_pow (Ideal.Quotient.mk I)]
      rw [show ((⟨(g : S) ^ n * y, hn⟩ : S') : S) = (g : S) ^ n * y from rfl, h5, ← mul_assoc,
        ← mul_pow, mul_comm (α v), hw, one_pow, one_mul]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨b₁, hb₁⟩ := h₁
      obtain ⟨b₂, hb₂⟩ := h₂
      exact ⟨b₁ + b₂, by rw [α.map_add, hb₁, hb₂, (Ideal.Quotient.mk I).map_add]⟩
  refine ⟨AlgEquiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro a₁ a₂ h
    obtain ⟨b₁, rfl⟩ := hαsurj a₁
    obtain ⟨b₂, rfl⟩ := hαsurj a₂
    rw [hFα, hFα] at h
    rw [Φ.injective h]
  · intro c
    exact ⟨α (Φ.symm c), by rw [hFα, Φ.apply_symm_apply]⟩

/-- The completion `S_q^∧` is cut out of the base change `S ⊗[R] Rₚ^∧` by an idempotent: there is
an idempotent `e` with `(S ⊗[R] Rₚ^∧) ⧸ (1 - e) = S_q^∧` as `S`-algebras. -/
private theorem exists_isIdempotentElem_nonempty_algEquiv_quotient_adicCompletion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q] [IsLocalRing Sq] :
    ∃ e : S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp, IsIdempotentElem e ∧
      Nonempty (((S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp) ⧸ Ideal.span {1 - e}) ≃ₐ[S]
        AdicCompletion (maximalIdeal Sq) Sq) := by
  obtain ⟨S', hFG, g, hg, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) q
  have : Module.Finite R S' := Module.Finite.iff_fg.2 hFG
  have hq'p : (q.comap S'.val.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have hcomp : (S'.val.toRingHom).comp (algebraMap R S') = algebraMap R S := by ext r; simp
  have : (q.comap S'.val.toRingHom).LiesOver p :=
    ⟨by rw [Ideal.under_def, Ideal.comap_comap, hcomp]; exact ‹q.LiesOver p›.over⟩
  have hmem : ∀ y : S, ∃ n : ℕ, (g : S) ^ n * y ∈ S' := by
    intro y
    obtain ⟨b, m, hb⟩ := Localization.awayMap_surjective_iff.1 hbij.2 y
    exact ⟨m, hb ▸ b.2⟩
  have := isLocalization_atPrime_comap q Sq S' g hg hmem
  obtain ⟨ε, hε, hA⟩ :=
    exists_isIdempotentElem_nonempty_algEquiv_quotient_of_finite (S' := S')
      p (q.comap S'.val.toRingHom) Rp Sq
  exact exists_isIdempotentElem_nonempty_algEquiv_quotient_of_exists_pow_smul_mem q Sq
    (AdicCompletion (maximalIdeal Rp) Rp) S' g hg hmem ε hε hA

/-- For `R` Noetherian and `S` of finite type over `R` and quasi-finite at a prime `q` lying over
`p`, the base change of `S` along `Rₚ^∧` is, as an `S`-algebra, the product of `S_q^∧` with the
quotient by an idempotent. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q] [IsLocalRing Sq] :
    ∃ e : S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp, IsIdempotentElem e ∧
      Nonempty (S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S]
        AdicCompletion (maximalIdeal Sq) Sq ×
          ((S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp) ⧸ Ideal.span {e})) := by
  obtain ⟨e, he, h⟩ :=
    exists_isIdempotentElem_nonempty_algEquiv_quotient_adicCompletion p q Rp Sq
  exact ⟨e, he, nonempty_algEquiv_prod_quotient_of_nonempty_algEquiv_quotient he h⟩

end Stacks.AdicCompletion.QuasiFiniteFactor

@[expose] public section

open TensorProduct IsLocalRing

/-- Let `R` be a Noetherian ring, let `S` be an `R`-algebra of finite type, and
let `q` be a prime of `S` lying over `p ⊂ R` at which `R → S` is quasi-finite. Let `Rₚ` and `S_q`
be the local rings of `R` at `p` and of `S` at `q`. Then the base change of `S` along the
completion `Rₚ^∧` of `Rₚ` at its maximal ideal is, as an `S`-algebra, the product of the
completion `S_q^∧` of `S_q` at its maximal ideal with a complementary factor cut out by an
idempotent: `Rₚ^∧ ⊗[R] S = S_q^∧ × B` for some `Rₚ^∧`-algebra `B`. -/
@[stacks 07NC "The source's `B` is named here as the explicit factor \
`(S ⊗[R] Rₚ^∧) ⧸ (e)` of an idempotent `e`, which is what makes it an `Rₚ^∧`-algebra. \
See the module docstring."]
public theorem AdicCompletion.exists_isIdempotentElem_nonempty_algEquiv_prod_quotient
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q] [IsLocalRing Sq] :
    ∃ e : S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp, IsIdempotentElem e ∧
      Nonempty (S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S]
        AdicCompletion (maximalIdeal Sq) Sq ×
          ((S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp) ⧸ Ideal.span {e})) :=
  Stacks.AdicCompletion.QuasiFiniteFactor.solution p q Rp Sq

end
