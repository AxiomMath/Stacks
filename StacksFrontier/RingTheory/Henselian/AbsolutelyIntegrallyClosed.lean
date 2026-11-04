module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.LinearCombination
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed
public import StacksFrontier.RingTheory.Idempotents.Lifting

/-!
# Henselian pairs over absolutely integrally closed rings

Let `A` be an absolutely integrally closed ring and `I ⊆ A` an ideal. The pair `(A, I)` is
henselian if and only if `I` is contained in the Jacobson radical of `A` and the reduction map
`A → A ⧸ I` induces a bijection on idempotents. In particular every localization of an
absolutely integrally closed ring at a prime ideal is strictly henselian.

## Main results

* `lifting_property_of_surjective_idemMap`: if `A` is absolutely integrally closed and
  `A → A ⧸ I` is surjective on idempotents, then coprime monic factorizations modulo `I` of monic
  polynomials lift to `A`.
* `henselianPair_iff_of_absolutelyIntegrallyClosed`: for `A` absolutely integrally closed,
  `(A, I)` is a henselian pair if and only if `I` is contained in the Jacobson radical of `A`
  and `A → A ⧸ I` induces a bijection on idempotents.
* `IsAbsolutelyIntegrallyClosed.isStrictlyHenselian_atPrime`: a localization of an absolutely
  integrally closed ring at a prime ideal is henselian with separably closed residue field.

## Implementation notes

The localization in `IsAbsolutelyIntegrallyClosed.isStrictlyHenselian_atPrime` is an arbitrary
algebra satisfying `IsLocalization.AtPrime`, rather than a chosen model, and strict henselianity
is phrased as `HenselianLocalRing` together with separable closedness of the residue field. The
local ring structure on the localization is not available to instance synthesis, so it is passed
as an `optParam` hypothesis defaulting to `IsLocalization.AtPrime.isLocalRing`, following
Mathlib's convention for statements about `IsLocalization.AtPrime`.

## References

* [Stacks Project, Tag 0DCT](https://stacks.math.columbia.edu/tag/0DCT)
* [Stacks Project, Tag 0DCS](https://stacks.math.columbia.edu/tag/0DCS)
-/

@[expose] public section

open Polynomial

/-- For an idempotent `e`, the linear polynomials `X - C e` and `X - C (1 - e)` are coprime. -/
theorem IsIdempotentElem.isCoprime_X_sub_C {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) :
    IsCoprime (X - C e : R[X]) (X - C (1 - e)) := by
  have he' : e * e = e := he
  have hsq : (e - (1 - e)) * (e - (1 - e)) = 1 := by linear_combination 4 * he'
  exact isCoprime_X_sub_C_of_isUnit_sub ⟨⟨_, _, hsq, hsq⟩, rfl⟩

/-- Mapping `X - C a` along a ring homomorphism gives `X - C (φ a)`. -/
private theorem map_X_sub_C_eq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    (X - C a : R[X]).map φ = X - C (φ a) := by
  simp

/-- A product of linear factors `X - C b` vanishes at each of the roots `b`. -/
private theorem eval_multiset_prod_X_sub_C_eq_zero {R : Type*} [CommRing R] {s : Multiset R}
    {a : R} (ha : a ∈ s) : ((s.map fun b => (X - C b : R[X])).prod).eval a = 0 := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp⟩)

/-- If coprime monic factorizations modulo `I` of monic polynomials lift to `A`, then the map
`idemMap I` from idempotents of `A` to idempotents of `A ⧸ I` is surjective. -/
theorem idemMap_surjective_of_lifting {A : Type*} [CommRing A] (I : Ideal A)
    (hp : ∀ f : A[X], f.Monic →
      ∀ g₀ h₀ : (A ⧸ I)[X], g₀.Monic → h₀.Monic →
        f.map (Ideal.Quotient.mk I) = g₀ * h₀ → IsCoprime g₀ h₀ →
          ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀) :
    Function.Surjective (idemMap I) := by
  rintro ⟨ebar, hebar⟩
  rcases subsingleton_or_nontrivial (A ⧸ I) with hsub | hnt
  · exact ⟨⟨0, IsIdempotentElem.zero⟩, Subtype.ext (Subsingleton.elim _ _)⟩
  set f : A[X] := X ^ 2 - X with hf
  have hfmonic : f.Monic := by rw [hf]; monicity!
  set g₀ : (A ⧸ I)[X] := X - C ebar with hg0
  set h₀ : (A ⧸ I)[X] := X - C (1 - ebar) with hh0
  have hg0m : g₀.Monic := monic_X_sub_C ebar
  have hh0m : h₀.Monic := monic_X_sub_C (1 - ebar)
  have hfmap : f.map (Ideal.Quotient.mk I) = g₀ * h₀ := by
    rw [hf, hg0, hh0]
    have heb : ebar * ebar = ebar := hebar
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X]
    have hCmul : C ebar * C (1 - ebar) = (0 : (A ⧸ I)[X]) := by
      rw [← C_mul, show ebar * (1 - ebar) = ebar - ebar * ebar by ring, heb, sub_self, C_0]
    have hCadd : C ebar + C (1 - ebar) = (1 : (A ⧸ I)[X]) := by
      rw [← C_add, show ebar + (1 - ebar) = 1 by ring, C_1]
    linear_combination (X : (A ⧸ I)[X]) * hCadd - hCmul
  have hcop : IsCoprime g₀ h₀ := hebar.isCoprime_X_sub_C
  obtain ⟨g, h, hgm, hhm, hgh, hgmap, hhmap⟩ := hp f hfmonic g₀ h₀ hg0m hh0m hfmap hcop
  have hlin : ∀ (p : A[X]) (c : A ⧸ I), p.Monic → p.map (Ideal.Quotient.mk I) = X - C c →
      ∃ a, p = X - C a := by
    intro p c hpm hpmap
    have h1 := hpm.natDegree_map (Ideal.Quotient.mk I)
    rw [hpmap, natDegree_X_sub_C] at h1
    refine ⟨- p.coeff 0, ?_⟩
    conv_lhs => rw [hpm.eq_X_add_C (by omega)]
    rw [map_neg, sub_neg_eq_add]
  obtain ⟨a, ha⟩ := hlin g _ hgm (hgmap.trans hg0)
  obtain ⟨b, hb⟩ := hlin h _ hhm (hhmap.trans hh0)
  have hprod : (X ^ 2 - X : A[X]) = (X - C a) * (X - C b) := by rw [← hf, hgh, ha, hb]
  obtain ⟨hsum, hmul⟩ : a + b = 1 ∧ a * b = 0 := by
    have e1 : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
      rw [C_add, C_mul]; ring
    rw [e1] at hprod
    have c1 : (X ^ 2 - X : A[X]).coeff 1 = (X ^ 2 - C (a + b) * X + C (a * b)).coeff 1 := by
      rw [hprod]
    have c0 : (X ^ 2 - X : A[X]).coeff 0 = (X ^ 2 - C (a + b) * X + C (a * b)).coeff 0 := by
      rw [hprod]
    refine ⟨?_, ?_⟩
    · simp [coeff_X_pow, coeff_C, coeff_X, mul_comm] at c1
      linear_combination c1
    · simp [coeff_X_pow, coeff_C, coeff_X] at c0
      linear_combination -c0
  have haidem : IsIdempotentElem a := by
    change a * a = a
    linear_combination a * hsum - hmul
  refine ⟨⟨a, haidem⟩, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk I a = ebar
  have hmap2 : g.map (Ideal.Quotient.mk I) = X - C (Ideal.Quotient.mk I a) := by
    rw [ha, map_X_sub_C_eq]
  rw [hgmap, hg0] at hmap2
  have hCeq : C ebar = C (Ideal.Quotient.mk I a) := by rwa [sub_right_inj] at hmap2
  exact (C_injective (R := A ⧸ I) hCeq).symm

/-- If `k₀ g₀ + l₀ h₀ = 1` in `R[X]`, then `1 - h₀(r) l₀(r) = g₀(r) k₀(r)` for every `r`. -/
theorem one_sub_eval_mul_eval_eq_of_bezout {R : Type*} [CommRing R]
    (g₀ h₀ k₀ l₀ : R[X]) (r : R) (hbez : k₀ * g₀ + l₀ * h₀ = 1) :
    1 - h₀.eval r * l₀.eval r = g₀.eval r * k₀.eval r := by
  have hb : k₀.eval r * g₀.eval r + l₀.eval r * h₀.eval r = 1 := by
    simpa using congrArg (Polynomial.eval r) hbez
  linear_combination -hb

/-- If `r` is a root of `g₀ h₀`, then `h₀(r) l₀(r) g₀(r) = 0` for every `l₀`. -/
theorem eval_mul_eval_mul_eval_eq_zero_of_bezout {R : Type*} [CommRing R]
    (g₀ h₀ l₀ : R[X]) (r : R) (hroot : (g₀ * h₀).IsRoot r) :
    h₀.eval r * l₀.eval r * g₀.eval r = 0 := by
  have hr : g₀.eval r * h₀.eval r = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_mul] using hroot
  linear_combination l₀.eval r * hr

/-- If `k₀ g₀ + l₀ h₀ = 1` in `R[X]` and `r` is a root of `g₀ h₀`, then
`(1 - h₀(r) l₀(r)) h₀(r) = 0`. -/
theorem one_sub_eval_mul_eval_mul_eval_eq_zero_of_bezout {R : Type*} [CommRing R]
    (g₀ h₀ k₀ l₀ : R[X]) (r : R) (hbez : k₀ * g₀ + l₀ * h₀ = 1)
    (hroot : (g₀ * h₀).IsRoot r) :
    (1 - h₀.eval r * l₀.eval r) * h₀.eval r = 0 := by
  have hr : g₀.eval r * h₀.eval r = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_mul] using hroot
  rw [one_sub_eval_mul_eval_eq_of_bezout g₀ h₀ k₀ l₀ r hbez]
  linear_combination k₀.eval r * hr

/-- If `k₀ g₀ + l₀ h₀ = 1` in `R[X]` and `r` is a root of `g₀ h₀`, then `h₀(r) l₀(r)` is
idempotent. -/
theorem isIdempotentElem_eval_mul_eval_of_bezout {R : Type*} [CommRing R]
    (g₀ h₀ k₀ l₀ : R[X]) (r : R) (hbez : k₀ * g₀ + l₀ * h₀ = 1)
    (hroot : (g₀ * h₀).IsRoot r) :
    IsIdempotentElem (h₀.eval r * l₀.eval r) := by
  have e2 := one_sub_eval_mul_eval_eq_of_bezout g₀ h₀ k₀ l₀ r hbez
  have e3 := eval_mul_eval_mul_eval_eq_zero_of_bezout g₀ h₀ l₀ r hroot
  change h₀.eval r * l₀.eval r * (h₀.eval r * l₀.eval r) = h₀.eval r * l₀.eval r
  linear_combination (-k₀.eval r) * e3 - (h₀.eval r * l₀.eval r) * e2

/-- If `g` is monic and `r` is a root of `g`, then `g = (X - C r) * g'` for some monic `g'`. -/
theorem Polynomial.Monic.exists_eq_X_sub_C_mul_of_isRoot {R : Type*} [CommRing R]
    {g : R[X]} (hg : g.Monic) {r : R} (hr : g.IsRoot r) :
    ∃ g' : R[X], g'.Monic ∧ g = (X - C r) * g' := by
  have key : (X - C r) * (g /ₘ (X - C r)) = g := mul_divByMonic_eq_iff_isRoot.mpr hr
  exact ⟨g /ₘ (X - C r), (monic_X_sub_C r).of_mul_monic_left (by rwa [key]), key.symm⟩

/-- Over an absolutely integrally closed ring `B`, if `g` is monic of positive degree and
`g * h = ∏_{a ∈ s} (X - C a)`, then `∏_{a ∈ s} g(a) = 0`. -/
theorem IsAbsolutelyIntegrallyClosed.prod_map_eval_eq_zero {B : Type*} [CommRing B]
    (hB : IsAbsolutelyIntegrallyClosed B) (g h : B[X]) (hg : g.Monic)
    (hdeg : 0 < g.natDegree)
    {s : Multiset B} (hs : g * h = (s.map (fun a => (X - C a : B[X]))).prod) :
    (s.map (fun a => g.eval a)).prod = 0 := by
  classical
  obtain ⟨t, ht⟩ := hB g hg
  have htne : t ≠ 0 := by
    rintro rfl
    simp [ht] at hdeg
  obtain ⟨b₀, hb₀⟩ := Multiset.exists_mem_of_ne_zero htne
  have hgsplit : g = (X - C b₀) * ((t.erase b₀).map (fun a => (X - C a : B[X]))).prod := by
    rw [ht]
    conv_lhs => rw [← Multiset.prod_map_erase (f := fun a => (X - C a : B[X])) hb₀]
  have hgb0 : g.eval b₀ = 0 := by rw [hgsplit]; simp
  have hfb0 : (s.map (fun a => b₀ - a)).prod = 0 := by
    have heq : (g * h).eval b₀ = (s.map (fun a => b₀ - a)).prod := by
      rw [hs, Polynomial.eval_multiset_prod, Multiset.map_map]
      congr 1; apply Multiset.map_congr rfl; intro a _; simp
    rw [← heq]; simp [hgb0]
  set g' := ((t.erase b₀).map (fun a => (X - C a : B[X]))).prod with hg'
  have hgeval : ∀ a, g.eval a = (a - b₀) * g'.eval a := by intro a; rw [hgsplit]; simp [hg']
  have hexp : (s.map (fun a => g.eval a)).prod
      = (s.map (fun a => a - b₀)).prod * (s.map (fun a => g'.eval a)).prod := by
    rw [← Multiset.prod_map_mul]; congr 1; apply Multiset.map_congr rfl; intro a _; rw [hgeval]
  rw [hexp]
  have hzero : (s.map (fun a => a - b₀)).prod = 0 := by
    have hneg : (s.map (fun a => a - b₀)).prod
        = (s.map (fun _ => (-1 : B))).prod * (s.map (fun a => b₀ - a)).prod := by
      rw [← Multiset.prod_map_mul]; congr 1; apply Multiset.map_congr rfl; intro a _; ring
    rw [hneg, hfb0, mul_zero]
  rw [hzero, zero_mul]

/-- If `e` is idempotent, then `p(e x + (1 - e) y) = e p(x) + (1 - e) p(y)` for every
polynomial `p`. -/
theorem IsIdempotentElem.eval_mul_add_one_sub_mul {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) (x y : R) (p : R[X]) :
    p.eval (e * x + (1 - e) * y) = e * p.eval x + (1 - e) * p.eval y := by
  have he' : e * e = e := he
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add, hp, hq]; ring
  | monomial n a =>
    simp only [eval_monomial]
    have key : (e * x + (1 - e) * y) ^ n = e * x ^ n + (1 - e) * y ^ n := by
      induction n with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih]
        linear_combination (x ^ k * x - x ^ k * y - x * y ^ k + y ^ k * y) * he'
    rw [key]; ring

/-- Let `L` be a nonempty list of roots of `f` and, for each `a ∈ L`, let `u a` be an idempotent
of `A` whose image in `A ⧸ I` annihilates `g₀(ā)`. Then `f` has a root `z` such that `g₀(z̄)` is
a multiple of the image of `∏_{a ∈ L} (1 - u a)` in `A ⧸ I`. -/
theorem exists_eval_eq_zero_and_prod_one_sub_dvd_eval {A : Type*} [CommRing A] (I : Ideal A)
    (f : A[X]) (g₀ : (A ⧸ I)[X]) (u : A → A) (L : List A) (hL : L ≠ [])
    (hf_root : ∀ a ∈ L, f.eval a = 0)
    (hu_idem : ∀ a ∈ L, IsIdempotentElem (u a))
    (hu_kill : ∀ a ∈ L, (Ideal.Quotient.mk I (u a)) * g₀.eval (Ideal.Quotient.mk I a) = 0) :
    ∃ z : A, f.eval z = 0 ∧
      Ideal.Quotient.mk I ((L.map (fun a => 1 - u a)).prod)
        ∣ g₀.eval (Ideal.Quotient.mk I z) := by
  induction L with
  | nil => exact absurd rfl hL
  | cons a L' ih =>
    by_cases hL' : L' = []
    · subst hL'
      refine ⟨a, hf_root a (by simp), ⟨g₀.eval (Ideal.Quotient.mk I a), ?_⟩⟩
      have hk := hu_kill a (by simp)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [map_sub, map_one]; linear_combination hk
    · have hmem : ∀ b ∈ L', b ∈ (a :: L') := fun b hb => List.mem_cons_of_mem a hb
      obtain ⟨z', hz'f, w', hz'g⟩ := ih hL'
        (fun b hb => hf_root b (hmem b hb)) (fun b hb => hu_idem b (hmem b hb))
        (fun b hb => hu_kill b (hmem b hb))
      set e := u a with he_def
      have he : IsIdempotentElem e := hu_idem a (by simp)
      refine ⟨e * a + (1 - e) * z', ?_, ?_⟩
      · rw [he.eval_mul_add_one_sub_mul a z' f, hf_root a (by simp), hz'f]; ring
      · have hmk : Ideal.Quotient.mk I (e * a + (1 - e) * z')
            = (Ideal.Quotient.mk I e) * (Ideal.Quotient.mk I a)
              + (1 - Ideal.Quotient.mk I e) * (Ideal.Quotient.mk I z') := by
          rw [map_add, map_mul, map_mul, map_sub, map_one]
        rw [hmk]
        have hei : IsIdempotentElem (Ideal.Quotient.mk I e) := he.map (Ideal.Quotient.mk I)
        rw [hei.eval_mul_add_one_sub_mul (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I z') g₀]
        have hk := hu_kill a (by simp)
        rw [he_def] at *
        rw [hk, hz'g]
        refine ⟨w', ?_⟩
        simp only [List.map_cons, List.prod_cons, map_mul, map_sub, map_one]; ring

/-- Let `A` be absolutely integrally closed with `A → A ⧸ I` surjective on idempotents, let
`f ∈ A[X]` be monic with `f̄ = g₀ h₀` for coprime monic `g₀, h₀ ∈ (A ⧸ I)[X]`, and suppose `g₀`
has positive degree. Then `f` has a root `a ∈ A` whose image in `A ⧸ I` is a root of `g₀`. -/
theorem IsAbsolutelyIntegrallyClosed.exists_isRoot_and_isRoot_map {A : Type*} [CommRing A]
    (hA : IsAbsolutelyIntegrallyClosed A) (I : Ideal A)
    (hsurj : Function.Surjective (idemMap I))
    (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hmap : f.map (Ideal.Quotient.mk I) = g₀ * h₀) (hcop : IsCoprime g₀ h₀)
    (hdeg : 0 < g₀.natDegree) :
    ∃ a : A, f.IsRoot a ∧ g₀.IsRoot (Ideal.Quotient.mk I a) := by
  classical
  have hB : IsAbsolutelyIntegrallyClosed (A ⧸ I) := isAbsolutelyIntegrallyClosed_quotient A I hA
  set mk := Ideal.Quotient.mk I with hmkdef
  obtain ⟨k₀, l₀, hbez⟩ := hcop
  obtain ⟨s, hs⟩ := hA f hf
  have hsB : g₀ * h₀ = ((s.map mk).map (fun b => (X - C b : (A⧸I)[X]))).prod := by
    rw [← hmap, hs, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => map_X_sub_C_eq _ _)
  set eps : A → (A ⧸ I) := fun a => h₀.eval (mk a) * l₀.eval (mk a)
  have hroot : ∀ a ∈ s, (g₀ * h₀).IsRoot (mk a) := by
    intro a ha
    rw [hsB]
    exact eval_multiset_prod_X_sub_C_eq_zero (Multiset.mem_map_of_mem _ ha)
  have hidem : ∀ a ∈ s, IsIdempotentElem (eps a) := fun a ha =>
    isIdempotentElem_eval_mul_eval_of_bezout g₀ h₀ k₀ l₀ (mk a) hbez (hroot a ha)
  have hkill : ∀ a ∈ s, eps a * g₀.eval (mk a) = 0 := fun a ha =>
    eval_mul_eval_mul_eval_eq_zero_of_bezout g₀ h₀ l₀ (mk a) (hroot a ha)
  have honeminus : ∀ a ∈ s, 1 - eps a = g₀.eval (mk a) * k₀.eval (mk a) := fun a _ =>
    one_sub_eval_mul_eval_eq_of_bezout g₀ h₀ k₀ l₀ (mk a) hbez
  set eps' : A → (A ⧸ I) :=
    fun a => if h : IsIdempotentElem (eps a) then eps a else 0 with heps'def
  have heps'idem : ∀ a, IsIdempotentElem (eps' a) := by
    intro a
    simp only [heps'def]
    split_ifs with h
    exacts [h, .zero]
  have heps'eq : ∀ a ∈ s, eps' a = eps a := by
    intro a ha; rw [heps'def]; simp [hidem a ha]
  have hlift : ∀ a : A, ∃ v : A, IsIdempotentElem v ∧ mk v = eps' a := by
    intro a
    obtain ⟨⟨v, hv⟩, hvmap⟩ := hsurj ⟨eps' a, heps'idem a⟩
    exact ⟨v, hv, by simpa [idemMap_val, hmkdef] using congrArg Subtype.val hvmap⟩
  choose u hu_idem hu_mk using hlift
  set L := s.toList with hLdef
  have hmemiff : ∀ a, a ∈ L ↔ a ∈ s := by intro a; rw [hLdef, Multiset.mem_toList]
  have hLne : L ≠ [] := by
    rw [hLdef]; intro hcon
    have hs0 : s = 0 := by rw [← Multiset.coe_toList s, hcon]; rfl
    rw [hs0] at hsB; simp only [Multiset.map_zero, Multiset.prod_zero] at hsB
    have hgh : (g₀ * h₀).natDegree = 0 := by rw [hsB]; simp
    have := hg₀.natDegree_mul hh₀
    omega
  have hf_root : ∀ a ∈ L, f.eval a = 0 := by
    intro a ha
    have has : a ∈ s := (hmemiff a).mp ha
    rw [hs]
    exact eval_multiset_prod_X_sub_C_eq_zero has
  have hu_idemL : ∀ a ∈ L, IsIdempotentElem (u a) := fun a _ => hu_idem a
  have hu_killL : ∀ a ∈ L, (mk (u a)) * g₀.eval (mk a) = 0 := by
    intro a ha
    have has : a ∈ s := (hmemiff a).mp ha
    rw [hu_mk a, heps'eq a has]; exact hkill a has
  obtain ⟨z, hzf, w, hzg⟩ :=
    exists_eval_eq_zero_and_prod_one_sub_dvd_eval I f g₀ u L hLne hf_root hu_idemL hu_killL
  refine ⟨z, hzf, ?_⟩
  have hfact : (s.map (fun a => g₀.eval (mk a))).prod = 0 := by
    have := hB.prod_map_eval_eq_zero g₀ h₀ hg₀ hdeg hsB
    rwa [Multiset.map_map] at this
  have hprodzero : mk ((L.map (fun a => 1 - u a)).prod) = 0 := by
    rw [map_list_prod, List.map_map]
    have hconv : (L.map (mk ∘ (fun a => 1 - u a))).prod
        = ((s.toList).map (fun a => 1 - eps' a)).prod := by
      rw [hLdef]; congr 1; apply List.map_congr_left; intro a _
      simp only [Function.comp_apply, map_sub, map_one, hu_mk a]
    rw [hconv, Multiset.prod_map_toList s (fun a => 1 - eps' a)]
    have step2 : (s.map (fun a => 1 - eps' a)).prod
        = (s.map (fun a => g₀.eval (mk a) * k₀.eval (mk a))).prod := by
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro a ha; rw [heps'eq a ha, honeminus a ha]
    rw [step2, Multiset.prod_map_mul, hfact, zero_mul]
  change g₀.eval (mk z) = 0
  rw [hzg, hprodzero, zero_mul]

/-- If `A` is absolutely integrally closed and `A → A ⧸ I` is surjective on idempotents,
then every factorization `f̄ = g₀ h₀` of a monic `f ∈ A[X]` into coprime monic polynomials over
`A ⧸ I` lifts to a factorization `f = g h` into monic polynomials with `ḡ = g₀` and `h̄ = h₀`. -/
theorem lifting_property_of_surjective_idemMap {A : Type*} [CommRing A]
    (hA : IsAbsolutelyIntegrallyClosed A) (I : Ideal A)
    (hsurj : Function.Surjective (idemMap I)) :
    ∀ f : A[X], f.Monic →
      ∀ g₀ h₀ : (A ⧸ I)[X], g₀.Monic → h₀.Monic →
        f.map (Ideal.Quotient.mk I) = g₀ * h₀ → IsCoprime g₀ h₀ →
          ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ := by
  intro f hf g₀ h₀ hg₀ hh₀ hmap hcop
  set n := g₀.natDegree with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing f g₀ h₀ with
  | _ n IH =>
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · have hg0eq : g₀ = 1 := hg₀.natDegree_eq_zero.mp (hn.symm.trans hz)
      refine ⟨1, f, monic_one, hf, ?_, ?_, ?_⟩
      · rw [one_mul]
      · rw [Polynomial.map_one, hg0eq]
      · rw [hmap, hg0eq, one_mul]
    · have hdeg : 0 < g₀.natDegree := by rwa [← hn]
      obtain ⟨a, hfa, hroot⟩ :=
        hA.exists_isRoot_and_isRoot_map I hsurj f hf g₀ h₀ hg₀ hh₀ hmap hcop hdeg
      obtain ⟨f', hf', hfeq⟩ := hf.exists_eq_X_sub_C_mul_of_isRoot hfa
      obtain ⟨g₀', hg₀', hg₀eq⟩ := hg₀.exists_eq_X_sub_C_mul_of_isRoot hroot
      have hcancel : f'.map (Ideal.Quotient.mk I) = g₀' * h₀ := by
        have hreg : IsRegular (X - C (Ideal.Quotient.mk I a) : (A ⧸ I)[X]) :=
          (monic_X_sub_C _).isRegular
        apply hreg.left
        change (X - C (Ideal.Quotient.mk I a)) * f'.map (Ideal.Quotient.mk I)
            = (X - C (Ideal.Quotient.mk I a)) * (g₀' * h₀)
        have e1 : (X - C (Ideal.Quotient.mk I a)) * f'.map (Ideal.Quotient.mk I)
            = f.map (Ideal.Quotient.mk I) := by
          rw [hfeq, Polynomial.map_mul, map_X_sub_C_eq]
        rw [e1, hmap, hg₀eq]
        ring
      have hcop' : IsCoprime g₀' h₀ :=
        hcop.of_isCoprime_of_dvd_left ⟨X - C (Ideal.Quotient.mk I a), by rw [hg₀eq]; ring⟩
      have hdeglt : g₀'.natDegree < n := by
        have hnt : Nontrivial (A ⧸ I) := by
          rcases subsingleton_or_nontrivial (A ⧸ I) with hs | hns
          · exfalso
            have hz0 : g₀.natDegree = 0 := by simp [Subsingleton.elim g₀ 0]
            omega
          · exact hns
        have hd : g₀.natDegree
            = (X - C (Ideal.Quotient.mk I a)).natDegree + g₀'.natDegree := by
          rw [hg₀eq]; exact Monic.natDegree_mul (monic_X_sub_C _) hg₀'
        rw [natDegree_X_sub_C, ← hn] at hd
        omega
      obtain ⟨g', h', hg'm, hh'm, hf'eq, hg'map, hh'map⟩ :=
        IH g₀'.natDegree hdeglt f' hf' g₀' h₀ hg₀' hh₀ hcancel hcop' rfl
      refine ⟨(X - C a) * g', h', (monic_X_sub_C a).mul hg'm, hh'm, ?_, ?_, hh'map⟩
      · rw [hfeq, hf'eq]; ring
      · rw [Polynomial.map_mul, hg'map, hg₀eq, map_X_sub_C_eq]

/-- **Stacks 0DCT**.
Let `A` be an absolutely integrally closed ring and `I ⊆ A` an ideal. Then `(A, I)` is a
henselian pair if and only if `I` is contained in the Jacobson radical of `A` and the map
`A → A ⧸ I` induces a bijection on idempotents. -/
@[stacks 0DCT]
theorem henselianPair_iff_of_absolutelyIntegrallyClosed
    {A : Type*} [CommRing A] (hA : IsAbsolutelyIntegrallyClosed A)
    (I : Ideal A) :
    HenselianPair A I ↔
      IsContainedInJacobson I ∧ InducesBijectionOnIdempotents I :=
  ⟨fun ⟨hjac, hlift⟩ => ⟨hjac, idemMap_injective I hjac, idemMap_surjective_of_lifting I hlift⟩,
    fun ⟨hjac, hbij⟩ => ⟨hjac, lifting_property_of_surjective_idemMap hA I hbij.surjective⟩⟩

/-- **Stacks 0DCS**.
The localization of an absolutely integrally closed ring at a prime ideal is strictly
henselian: it is a henselian local ring and its residue field is separably closed. -/
@[stacks 0DCS]
theorem IsAbsolutelyIntegrallyClosed.isStrictlyHenselian_atPrime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hA : IsAbsolutelyIntegrallyClosed A) (p : Ideal A) [p.IsPrime]
    [IsLocalization.AtPrime B p]
    (h : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B p) :
    HenselianLocalRing B ∧ IsSepClosed (IsLocalRing.ResidueField B) := by
  have hB : IsAbsolutelyIntegrallyClosed B :=
    isAbsolutelyIntegrallyClosed_localization A p.primeCompl B hA
  constructor
  · refine ((HenselianLocalRing.TFAE B).out 1 2).mpr ?_
    intro f hf a₀ hroot hderiv
    obtain ⟨s, hs⟩ := hB f hf
    rw [hs, aeval_def, eval₂_multiset_prod, Multiset.map_map] at hroot
    obtain ⟨a, ha_mem, ha_zero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hroot)
    refine ⟨a, ?_, ?_⟩
    · rw [hs]
      exact (show (X - C a).IsRoot a by simp).dvd
        (Multiset.dvd_prod (Multiset.mem_map.mpr ⟨a, ha_mem, rfl⟩))
    · exact (sub_eq_zero.mp (by simpa using ha_zero)).symm
  · exact IsSepClosed.of_exists_root _ fun f hf hirr _ =>
      (isAbsolutelyIntegrallyClosed_iff_exists_root _).mp
        (isAbsolutelyIntegrallyClosed_quotient B (IsLocalRing.maximalIdeal B) hB) f hf
        hirr.natDegree_pos
