module

public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples.BaseChange
import all StacksFrontier.RingTheory.UniversalHomeomorphism.Examples.PowerConditions
import all StacksFrontier.RingTheory.UniversalHomeomorphism.Examples.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal homeomorphisms: generation criteria

The three generation criteria for universal homeomorphisms of
`StacksFrontier.RingTheory.UniversalHomeomorphism.Examples`: `S` is generated over `R` by elements
`x` with a liftable power of `T - x`, or with `x ^ p ^ n` and `p ^ n • x` in the image of `φ`
for a prime `p`, or with `x ^ 2` and `x ^ 3` in the image, in each case with `ker φ` locally
nilpotent.

## Main results

* `PrimeSpectrum.isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_eq_top`,
  `PrimeSpectrum.isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_pow_eq_top`,
  `PrimeSpectrum.isHomeomorph_comap_and_residueFieldMap_bijective_of_adjoin_sq_cube_eq_top`:
  the three generation criteria.

## References

* [Stacks Project, Tag 09EF](https://stacks.math.columbia.edu/tag/09EF)
* [Stacks Project, Tag 0BRA](https://stacks.math.columbia.edu/tag/0BRA)
* [Stacks Project, Tag 0EUH](https://stacks.math.columbia.edu/tag/0EUH)
-/

@[expose] public section

universe u v u' v' w

/-- A ring map out of `S` sends all of `S` into any subsemiring of the target that contains the
image of a generating set of `S` over `R` and the image of `R`. -/
private theorem image_mem_of_adjoin_eq_top {R S S' : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] {G : Set S} (hgen : Algebra.adjoin R G = ⊤) (g : S →+* S')
    {T : Type*} [SetLike T S'] [SubsemiringClass T S'] (t : T) (hG : ∀ x ∈ G, g x ∈ t)
    (hR : ∀ r : R, g (algebraMap R S r) ∈ t) (s : S) : g s ∈ t := by
  have hs : s ∈ Algebra.adjoin R G := hgen ▸ Algebra.mem_top
  induction hs using Algebra.adjoin_induction with
  | mem x hx => exact hG x hx
  | algebraMap r => exact hR r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- If the image of `S` in a pushout `S'` of `S` over `R` lies in a subalgebra `B` over `R'`, then
`B` is everything, as `S'` is generated as an `R'`-module by that image. -/
private theorem eq_top_of_algebraMap_mem_of_isPushout {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S']
    [Algebra R' S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [hp : Algebra.IsPushout R S R' S'] (B : Subalgebra R' S') (h : ∀ m : S, algebraMap S S' m ∈ B) :
    B = ⊤ :=
  eq_top_iff.mpr fun z _ => hp.symm.out.inductionOn z (motive := fun w => w ∈ B) h
    (fun r' _ hn => B.smul_mem hn r') fun _ _ ha hb => add_mem ha hb

section

open Polynomial

/-- The set of hypothesis (2) of the source: the elements `x` of `S` such that `(T - x) ^ n`, for
some `n > 0`, is the image of a polynomial of `R[T]`. -/
private abbrev liftSet (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Set S :=
  {x : S | ∃ n > 0, ((X : S[X]) - C x) ^ n ∈ lifts (algebraMap R S)}

/-! ### Coefficients, integrality and functoriality of the generating condition -/

/-- The coefficient of `X ^ (n - 1)` of `(X - C x) ^ n` is `-(n • x)`; so if `(X - C x) ^ n` lifts
to `R[X]`, then `n • x` lies in the image of `R`. -/
private theorem nsmul_mem_range_of_mem_lifts {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (hn : 0 < n) {x : A} (h : ((X : A[X]) - C x) ^ n ∈ lifts (algebraMap R A)) :
    n • x ∈ (algebraMap R A).range := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hdeg : (((X : A[X]) - C x) ^ n).natDegree = n := by
    rw [(monic_X_sub_C x).natDegree_pow, natDegree_X_sub_C, mul_one]
  have h1 : (((X : A[X]) - C x) ^ n).nextCoeff = -(n • x) := by
    rw [(monic_X_sub_C x).nextCoeff_pow, nextCoeff_X_sub_C, smul_neg]
  have h2 : (((X : A[X]) - C x) ^ n).nextCoeff = (((X : A[X]) - C x) ^ n).coeff (n - 1) := by
    rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; exact hn), hdeg]
  obtain ⟨r, hr⟩ := (lifts_iff_coeff_lifts _).mp h (n - 1)
  exact ⟨-r, by rw [map_neg, hr, ← h2, h1, neg_neg]⟩

/-- An element `x` with `(X - C x) ^ n` liftable to `R[X]` is integral over `R`: a monic lift of
`(X - C x) ^ n` is a monic polynomial killing `x`. -/
private theorem isIntegral_of_mem_liftSet {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} (hx : x ∈ liftSet R S) : IsIntegral R x := by
  obtain ⟨n, hn, hlift⟩ := hx
  rcases subsingleton_or_nontrivial S with _ | _
  · exact ⟨X, monic_X, Subsingleton.elim _ _⟩
  · obtain ⟨P, hP, -, hPm⟩ := lifts_and_degree_eq_and_monic hlift ((monic_X_sub_C x).pow n)
    refine ⟨P, hPm, ?_⟩
    rw [← eval_map, hP]
    simp [zero_pow hn.ne']

/-- If `S` is generated as an `R`-algebra by elements with a liftable power of `T - x`, then
`R → S` is integral. -/
private theorem isIntegral_of_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hgen : Algebra.adjoin R (liftSet R S) = ⊤) : Algebra.IsIntegral R S :=
  ⟨fun _ => Algebra.adjoin_le (S := integralClosure R S)
    (fun _ hz => isIntegral_of_mem_liftSet hz) (hgen ▸ Algebra.mem_top)⟩

/-- The generating condition is functorial: in a commuting square of ring maps, the image of an
element with a liftable power of `T - x` again has one. -/
private theorem mem_liftSet_of_comp {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [Algebra R S] [Algebra R' S'] (g : S →+* S') (h : R →+* R')
    (hcomm : (algebraMap R' S').comp h = g.comp (algebraMap R S)) {x : S}
    (hx : x ∈ liftSet R S) : g x ∈ liftSet R' S' := by
  obtain ⟨n, hn, hlift⟩ := hx
  obtain ⟨P, hP⟩ := (mem_lifts _).mp hlift
  refine ⟨n, hn, (mem_lifts _).mpr ⟨P.map h, ?_⟩⟩
  rw [Polynomial.map_map, hcomm, ← Polynomial.map_map, hP, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- Hypothesis (2) is stable under base change: `S'` is generated as an `R'`-module by the image of
`S`, and the image of an element with a liftable power of `T - x` again has one. -/
private theorem adjoin_liftSet_eq_top_of_isPushout {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S']
    [Algebra R' S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [Algebra.IsPushout R S R' S'] (hgen : Algebra.adjoin R (liftSet R S) = ⊤) :
    Algebra.adjoin R' (liftSet R' S') = ⊤ := by
  have hcomm : (algebraMap R' S').comp (algebraMap R R') =
      (algebraMap S S').comp (algebraMap R S) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have himg : ∀ m : S, algebraMap S S' m ∈ Algebra.adjoin R' (liftSet R' S') :=
    image_mem_of_adjoin_eq_top hgen _ _
      (fun _ hw => Algebra.subset_adjoin (mem_liftSet_of_comp _ _ hcomm hw)) fun r => by
        rw [← RingHom.comp_apply, ← hcomm, RingHom.comp_apply]
        exact Subalgebra.algebraMap_mem _ _
  exact eq_top_of_algebraMap_mem_of_isPushout (R := R) _ himg

/-! ### The elements with a `q`-power in the base -/

/-- If `n` is invertible in the field `k` and `n • x` lies in the image of `k`, then so does `x`.
-/
private theorem mem_range_of_nsmul_mem_range {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : A} (h : n • x ∈ (algebraMap k A).range) :
    x ∈ (algebraMap k A).range := by
  obtain ⟨r, hr⟩ := h
  refine ⟨(n : k)⁻¹ * r, ?_⟩
  rw [map_mul, hr, nsmul_eq_mul, ← map_natCast (algebraMap k A) n, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hn, map_one, one_mul]

/-- Over a field `k` of exponential characteristic `q`, an element `x` with `(X - C x) ^ n`
liftable to `k[X]` has a `q`-power in the image of `k`.

For `q = 1` the coefficient `n • x` of `(X - C x) ^ n` and the invertibility of `n` give `x`
itself; for `q = p` prime, writing `n = p ^ e * m` with `m` prime to `p`, the polynomial
`(X ^ p ^ e - C (x ^ p ^ e)) ^ m` has its coefficients among those of `(X - C x) ^ n`, so it lifts
too, and its coefficient `m • x ^ p ^ e` gives `x ^ p ^ e`. -/
private theorem exists_pow_mem_range_of_mem_liftSet {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] (q : ℕ) [ExpChar k q] [ExpChar A q] {x : A} (hx : x ∈ liftSet k A) :
    ∃ N, x ^ q ^ N ∈ (algebraMap k A).range := by
  obtain ⟨n, hn, hlift⟩ := hx
  cases ‹ExpChar k q› with
  | zero =>
      refine ⟨0, ?_⟩
      rw [pow_zero, pow_one]
      exact mem_range_of_nsmul_mem_range (Nat.cast_ne_zero.mpr hn.ne')
        (nsmul_mem_range_of_mem_lifts hn hlift)
  | prime hp =>
      have hq0 : 0 < q := hp.pos
      have hcharA : CharP A q := by
        cases ‹ExpChar A q› with
        | zero => exact absurd hp Nat.not_prime_one
        | prime _ => assumption
      obtain ⟨e, m, hm, hn'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hp.ne_one
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hn'] at hn)
      have hexp : ((X : A[X]) - C x) ^ n
          = expand A (q ^ e) (((X : A[X]) - C (x ^ q ^ e)) ^ m) := by
        rw [map_pow, map_sub, expand_X, expand_C, hn', pow_mul, sub_pow_expChar_pow, map_pow]
      have hlift' : ((X : A[X]) - C (x ^ q ^ e)) ^ m ∈ lifts (algebraMap k A) := by
        rw [lifts_iff_coeff_lifts]
        intro i
        have hcoeff := (lifts_iff_coeff_lifts _).mp hlift (i * q ^ e)
        rwa [hexp, coeff_expand_mul (pow_pos hq0 e)] at hcoeff
      refine ⟨e, mem_range_of_nsmul_mem_range ?_ (nsmul_mem_range_of_mem_lifts hm0 hlift')⟩
      rwa [Ne, CharP.cast_eq_zero_iff k q]

/-- Over a field `k` of exponential characteristic `q`, a `k`-algebra generated by elements with a
liftable power of `T - x` lies in the perfect closure of `k`: each of its elements has a `q`-power
in the image of `k`. -/
private theorem mem_perfectClosure_of_adjoin_eq_top {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] (q : ℕ) [ExpChar k q] [ExpChar A q]
    (hgen : Algebra.adjoin k (liftSet k A) = ⊤) (x : A) : x ∈ Subalgebra.perfectClosure k A q :=
  Algebra.adjoin_le (fun _ hz => Subalgebra.mem_perfectClosure_iff.mpr
    (exists_pow_mem_range_of_mem_liftSet q hz)) (hgen ▸ Algebra.mem_top)

/-! ### The two fibrewise statements -/

/-- Over a field, an algebra generated by elements with a liftable power of `T - x` has at most one
prime ideal: an element of a prime has a `q`-power in the base, which must then be `0`, so the
element is nilpotent. -/
private theorem subsingleton_primeSpectrum_of_adjoin_eq_top {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] (hgen : Algebra.adjoin k (liftSet k A) = ⊤) : Subsingleton (PrimeSpectrum A) := by
  refine ⟨fun 𝔫₁ 𝔫₂ => ?_⟩
  have hnt : Nontrivial A :=
    nontrivial_of_ne 0 1 fun h =>
      𝔫₁.2.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ Submodule.zero_mem _))
  have : ExpChar k (ringExpChar k) := ringExpChar.expChar k
  have : ExpChar A (ringExpChar k) :=
    expChar_of_injective_algebraMap (algebraMap k A).injective (ringExpChar k)
  have key : ∀ 𝔫 : PrimeSpectrum A, 𝔫.asIdeal = nilradical A := by
    intro 𝔫
    refine le_antisymm (fun x hx => ?_) (nilradical_le_prime _)
    obtain ⟨N, c, hc⟩ := Subalgebra.mem_perfectClosure_iff.mp
      (mem_perfectClosure_of_adjoin_eq_top (ringExpChar k) hgen x)
    rcases eq_or_ne c 0 with rfl | hc0
    · exact ⟨ringExpChar k ^ N, by rw [← hc, map_zero]; exact Submodule.zero_mem _⟩
    · exact absurd (hc ▸ Ideal.pow_mem_of_mem _ hx _ (pow_pos (expChar_pos k (ringExpChar k)) N))
        (fun hmem => 𝔫.2.ne_top ((Ideal.eq_top_of_isUnit_mem _ hmem
          ((isUnit_iff_ne_zero.mpr hc0).map (algebraMap k A)))))
  exact PrimeSpectrum.ext ((key 𝔫₁).trans (key 𝔫₂).symm)

/-- The residue field extension of a prime is purely inseparable: `κ(𝔮)` is generated as a field by
the image of `S`, and every element of that image has a `q`-power in `κ(𝔭)`. -/
private theorem isPurelyInseparable_residueField_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hgen : Algebra.adjoin R (liftSet R S) = ⊤) (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S)) :
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).IsPurelyInseparable := by
  algebraize [Ideal.ResidueField.map p q (algebraMap R S) hpq]
  change IsPurelyInseparable p.ResidueField q.ResidueField
  have hcomm : (algebraMap p.ResidueField q.ResidueField).comp (algebraMap R p.ResidueField)
      = (algebraMap S q.ResidueField).comp (algebraMap R S) := by
    ext r
    exact Ideal.ResidueField.map_algebraMap p q (algebraMap R S) hpq r
  have : ExpChar p.ResidueField (ringExpChar p.ResidueField) := ringExpChar.expChar _
  have : ExpChar q.ResidueField (ringExpChar p.ResidueField) :=
    expChar_of_injective_algebraMap (algebraMap p.ResidueField q.ResidueField).injective _
  have himg : ∀ s : S, algebraMap S q.ResidueField s ∈
      perfectClosure p.ResidueField q.ResidueField :=
    image_mem_of_adjoin_eq_top hgen _ _
      (fun _ hw => mem_perfectClosure_iff.mpr
        (exists_pow_mem_range_of_mem_liftSet _ (mem_liftSet_of_comp _ _ hcomm hw))) fun r => by
        rw [← RingHom.comp_apply, ← hcomm, RingHom.comp_apply]
        exact IntermediateField.algebraMap_mem _ _
  rw [isPurelyInseparable_iff_pow_mem p.ResidueField (ringExpChar p.ResidueField)]
  intro ξ
  obtain ⟨y, z, -, rfl⟩ := Ideal.exists_div_algebraMap_residueField_eq q ξ
  exact mem_perfectClosure_iff.mp (div_mem (himg y) (himg z))

/-! ### Assembling -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `Spec(S) → Spec(R)` is injective: the fibre over a prime `𝔭` is the spectrum of the base change
`κ(𝔭) ⊗_R S`, which again satisfies hypothesis (2), so it is a single point. -/
private theorem injective_comap_of_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hgen : Algebra.adjoin R (liftSet R S) = ⊤) :
    Function.Injective (PrimeSpectrum.comap (algebraMap R S)) := by
  intro q₁ q₂ hq
  have hsub : Subsingleton
      (PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R S) q₁).asIdeal.Fiber S)) :=
    subsingleton_primeSpectrum_of_adjoin_eq_top
      (k := (PrimeSpectrum.comap (algebraMap R S) q₁).asIdeal.ResidueField)
      (adjoin_liftSet_eq_top_of_isPushout (R := R) (S := S) hgen)
  have h : (⟨q₁, rfl⟩ : (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        {PrimeSpectrum.comap (algebraMap R S) q₁} : Set (PrimeSpectrum S))) = ⟨q₂, hq.symm⟩ :=
    (PrimeSpectrum.preimageEquivFiber R S _).injective (Subsingleton.elim _ _)
  exact congrArg Subtype.val h

namespace PrimeSpectrum

open Polynomial in
/-- Let `φ : R → S` be a ring map whose kernel is locally nilpotent and such that `S` is generated
as an `R`-algebra by elements `x` for which there are an `n > 0` and a polynomial `P(T) ∈ R[T]`
whose image in `S[T]` is `(T - x) ^ n`. Then `Spec(S) → Spec(R)` is a homeomorphism, the induced
residue field extensions `κ(p) → κ(q)` are purely inseparable, and both hypotheses hold again for
every base change `R' → S'` of `R → S` along an arbitrary ring map `R → R'`, i.e. for every pushout
square of `R`-algebras completing `R`, `S` by `R'`, `S'`. -/
@[stacks 09EF]
public theorem isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_eq_top
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hker : RingHom.ker (algebraMap R S) ≤ nilradical R)
    (hgen : Algebra.adjoin R
      {x : S | ∃ n > 0, ((X : S[X]) - C x) ^ n ∈ lifts (algebraMap R S)} = ⊤) :
    IsHomeomorph (comap (algebraMap R S)) ∧
      (∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
        (hpq : p = q.comap (algebraMap R S)),
        (Ideal.ResidueField.map p q (algebraMap R S) hpq).IsPurelyInseparable) ∧
      ∀ (R' : Type u') (S' : Type v') [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S']
        [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
        [Algebra.IsPushout R S R' S'],
        RingHom.ker (algebraMap R' S') ≤ nilradical R' ∧
          Algebra.adjoin R'
            {x : S' | ∃ n > 0, ((X : S'[X]) - C x) ^ n ∈ lifts (algebraMap R' S')} = ⊤ := by
  have hgen' : Algebra.adjoin R (liftSet R S) = ⊤ := hgen
  have hint : Algebra.IsIntegral R S := isIntegral_of_adjoin_eq_top hgen'
  have hins : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
      (hpq : p = q.comap (algebraMap R S)),
      (Ideal.ResidueField.map p q (algebraMap R S) hpq).IsPurelyInseparable :=
    fun p _ q _ hpq => isPurelyInseparable_residueField_map hgen' p q hpq
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
    rintro ⟨p, hp⟩
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
      (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact hker.trans (nilradical_le_prime p))
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩
  obtain ⟨hhom, hbc⟩ :=
    PrimeSpectrum.isHomeomorph_comap_and_baseChange_of_bijective_comap_of_isPurelyInseparable
      ⟨injective_comap_of_adjoin_eq_top hgen', hsurj⟩ hins
  refine ⟨hhom, hins, fun R' S' _ _ _ _ _ _ _ _ _ => ⟨?_, adjoin_liftSet_eq_top_of_isPushout hgen'⟩⟩
  obtain ⟨-, hbij, -⟩ := hbc R' S'
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hbij.surjective.denseRange

end PrimeSpectrum

end

section

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The set `T` of the source's proof: the elements `x` of `S` for which there is an `n > 0` with
`x ^ p ^ n` and the `p ^ n`-fold sum `p ^ n • x` in the image of `R → S`. -/
private abbrev powNsmulSet (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) :
    Set S :=
  {x : S | ∃ n > 0, x ^ p ^ n ∈ (algebraMap R S).range ∧ p ^ n • x ∈ (algebraMap R S).range}

/-- A witness with an arbitrary, possibly zero, exponent suffices: if `x ^ p ^ a` and `p ^ a • x`
lie in the image of `R → S`, then so do `x ^ p ^ (a + 1)` and `p ^ (a + 1) • x`. -/
private theorem mem_powNsmulSet_of_pow (p : ℕ) {x : S} {a : ℕ}
    (h₁ : x ^ p ^ a ∈ (algebraMap R S).range) (h₂ : p ^ a • x ∈ (algebraMap R S).range) :
    x ∈ powNsmulSet R S p := by
  obtain ⟨r, hr⟩ := h₁
  obtain ⟨s, hs⟩ := h₂
  refine ⟨a + 1, Nat.succ_pos a, ⟨r ^ p, ?_⟩, ⟨p • s, ?_⟩⟩
  · rw [map_pow, hr, ← pow_mul, ← pow_succ]
  · rw [map_nsmul, hs, pow_succ, mul_comm (p ^ a) p, mul_smul]

/-- The image of `R → S` lies in `T`. -/
private theorem algebraMap_mem_powNsmulSet (p : ℕ) (r : R) : algebraMap R S r ∈ powNsmulSet R S p :=
  mem_powNsmulSet_of_pow p (a := 0) (by simp) (by simp)

/-- `T` is closed under multiplication: if `x` has exponent `n` and `y` has exponent `m`, then
`x * y` has exponent `n + m`. -/
private theorem mul_mem_powNsmulSet (p : ℕ) {x y : S} (hx : x ∈ powNsmulSet R S p)
    (hy : y ∈ powNsmulSet R S p) : x * y ∈ powNsmulSet R S p := by
  obtain ⟨n, hn, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
  obtain ⟨m, hm, ⟨c, hc⟩, ⟨d, hd⟩⟩ := hy
  refine ⟨n + m, by omega, ⟨a ^ p ^ m * c ^ p ^ n, ?_⟩, ⟨b * d, ?_⟩⟩
  · rw [map_mul, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      add_comm m n, mul_pow]
  · rw [map_mul, hb, hd, smul_mul_smul_comm, ← pow_add]

/-- A `ℤ`-algebra map `F : ℤ[x, y] → S` carries the subring
`ℤ[x ^ p ^ n, p ^ n x, y ^ p ^ m, p ^ m y]` of tag 0545 into the image of `R → S` as soon as it
carries the four generators there. -/
private theorem mem_range_of_mem_subringR {p n m : ℕ} (F : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] S)
    (hx₁ : F (MvPolynomial.X 0) ^ p ^ n ∈ (algebraMap R S).range)
    (hx₂ : p ^ n • F (MvPolynomial.X 0) ∈ (algebraMap R S).range)
    (hy₁ : F (MvPolynomial.X 1) ^ p ^ m ∈ (algebraMap R S).range)
    (hy₂ : p ^ m • F (MvPolynomial.X 1) ∈ (algebraMap R S).range) :
    ∀ z ∈ Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.subringR p n m, F z ∈ (algebraMap R
      S).range := by
  intro z hz
  rw [Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.subringR] at hz
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rcases hw with rfl | rfl | rfl | rfl
    · rwa [map_pow]
    · rwa [map_zsmul, ← Nat.cast_pow, natCast_zsmul]
    · rwa [map_pow]
    · rwa [map_zsmul, ← Nat.cast_pow, natCast_zsmul]
  | algebraMap i => exact ⟨(i : R), by simp⟩
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | mul u v _ _ hu hv => rw [map_mul]; exact mul_mem hu hv

/-- Tag 0545 for a pair of elements of an arbitrary `R`-algebra: if `p` is prime, `n, m > 0` and
the four elements `x ^ p ^ n`, `p ^ n x`, `y ^ p ^ m`, `p ^ m y` lie in the image of `R → S`, then
there is an `a` with `(x + y) ^ p ^ a` and `p ^ a (x + y)` in the image. It is the universal
computation `Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.exists_pow_mem` in `ℤ[x, y]`
  transported along the `ℤ`-algebra map sending the two
indeterminates to `x` and `y`. -/
private theorem exists_pow_add_mem_range {p : ℕ} (hp : p.Prime) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {x y : S} (hx₁ : x ^ p ^ n ∈ (algebraMap R S).range)
    (hx₂ : p ^ n • x ∈ (algebraMap R S).range) (hy₁ : y ^ p ^ m ∈ (algebraMap R S).range)
    (hy₂ : p ^ m • y ∈ (algebraMap R S).range) :
    ∃ a : ℕ, (x + y) ^ p ^ a ∈ (algebraMap R S).range ∧
      p ^ a • (x + y) ∈ (algebraMap R S).range := by
  obtain ⟨a, ha₁, ha₂⟩ := Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.exists_pow_mem p hp n
    m hn hm
  set F : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] S := MvPolynomial.aeval ![x, y] with hF
  have hFx : F (MvPolynomial.X 0) = x := by simp [hF]
  have hFy : F (MvPolynomial.X 1) = y := by simp [hF]
  have key := mem_range_of_mem_subringR (R := R) F (by rw [hFx]; exact hx₁) (by rw [hFx]; exact hx₂)
    (by rw [hFy]; exact hy₁) (by rw [hFy]; exact hy₂)
  refine ⟨a, ?_, ?_⟩
  · have := key _ ha₁
    rwa [map_pow, map_add, hFx, hFy] at this
  · have := key _ ha₂
    rwa [map_zsmul, map_add, hFx, hFy, ← Nat.cast_pow, natCast_zsmul] at this

/-- `T` is closed under addition, by tag 0545. This is the one step that uses the primality
of `p`. -/
private theorem add_mem_powNsmulSet {p : ℕ} (hp : p.Prime) {x y : S} (hx : x ∈ powNsmulSet R S p)
    (hy : y ∈ powNsmulSet R S p) : x + y ∈ powNsmulSet R S p := by
  obtain ⟨n, hn, hx₁, hx₂⟩ := hx
  obtain ⟨m, hm, hy₁, hy₂⟩ := hy
  obtain ⟨a, ha₁, ha₂⟩ := exists_pow_add_mem_range hp hn hm hx₁ hx₂ hy₁ hy₂
  exact mem_powNsmulSet_of_pow p ha₁ ha₂

/-- The claim of the source's proof: for `p` prime the set `T` is an `R`-subalgebra of `S`. -/
private def powNsmulSubalgebra (p : ℕ) (hp : p.Prime) : Subalgebra R S where
  carrier := powNsmulSet R S p
  mul_mem' := mul_mem_powNsmulSet p
  one_mem' := by simpa using algebraMap_mem_powNsmulSet (R := R) (S := S) p 1
  add_mem' := add_mem_powNsmulSet hp
  zero_mem' := by simpa using algebraMap_mem_powNsmulSet (R := R) (S := S) p 0
  algebraMap_mem' := algebraMap_mem_powNsmulSet p

/-- `T = S`: under hypothesis (a), every element of `S` admits an `n > 0` with `x ^ p ^ n` and
`p ^ n • x` in the image of `R → S`, because an `R`-subalgebra is its own `R`-algebra closure. -/
private theorem mem_powNsmulSet {p : ℕ} (hp : p.Prime)
    (hgen : Algebra.adjoin R (powNsmulSet R S p) = ⊤) (x : S) : x ∈ powNsmulSet R S p :=
  have h : (⊤ : Subalgebra R S) ≤ powNsmulSubalgebra p hp :=
    hgen ▸ Algebra.adjoin_le (S := powNsmulSubalgebra p hp) subset_rfl
  h Algebra.mem_top

/-- A ring map `g : S → S'` carrying the image of `R → S` into a set `T` carries a good element of
`S` to an element with a `p ^ n`-th power and a `p ^ n`-fold sum in `T`. Both the residue field
extension and the base change ask for this. -/
private theorem exists_pow_mem_of_mem_powNsmulSet {S' : Type*} [CommRing S'] {p : ℕ} (g : S →+* S')
    {T : Set S'} (hT : ∀ y ∈ (algebraMap R S).range, g y ∈ T) {x : S} (hx : x ∈ powNsmulSet R S p) :
    ∃ n > 0, g x ^ p ^ n ∈ T ∧ p ^ n • g x ∈ T := by
  obtain ⟨n, hn, h₁, h₂⟩ := hx
  exact ⟨n, hn, map_pow g x _ ▸ hT _ h₁, map_nsmul g _ x ▸ hT _ h₂⟩

/-- The residue field of a prime is generated, as a field, by the image of the ring. -/
private theorem closure_range_algebraMap_residueField {A : Type*} [CommRing A] (q : Ideal A)
    [q.IsPrime] : Subfield.closure (Set.range (algebraMap A q.ResidueField)) = ⊤ :=
  eq_top_iff.mpr fun ξ _ => by
    obtain ⟨y, z, -, rfl⟩ := Ideal.exists_div_algebraMap_residueField_eq q ξ
    exact div_mem (Subfield.subset_closure ⟨y, rfl⟩) (Subfield.subset_closure ⟨z, rfl⟩)

/-- A surjective ring map is purely inseparable: every element of the target is the image of an
element of the source, hence integral over it and in its image. -/
theorem RingHom.isPurelyInseparable_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) : f.IsPurelyInseparable := by
  let _ := f.toAlgebra
  have h : Function.Surjective (algebraMap A B) := by rwa [RingHom.algebraMap_toAlgebra]
  exact { isIntegral := ⟨fun x => by obtain ⟨y, rfl⟩ := h x; exact isIntegral_algebraMap⟩
          inseparable' := fun x _ => h x }

/-- Pure inseparability of a homomorphism of fields is unchanged by composing with isomorphisms on
either side. -/
theorem RingHom.isPurelyInseparable_congr {K K' L L' : Type*}
    [Field K] [Field K'] [Field L] [Field L']
    (e : K ≃+* K') (g : L ≃+* L') (f : K' →+* L') (hf : f.IsPurelyInseparable) :
    (g.symm.toRingHom.comp (f.comp e.toRingHom)).IsPurelyInseparable :=
  ((RingHom.isPurelyInseparable_of_surjective _ e.surjective).comp hf).comp
    (RingHom.isPurelyInseparable_of_surjective _ g.symm.surjective)

/-- If the image of a map of fields `f : K → L` is purely inseparable in `L`, then `f` is a purely
inseparable ring map: it is the composite of the surjection `K → f.fieldRange` with the inclusion
`f.fieldRange → L`. -/
private theorem isPurelyInseparable_of_fieldRange {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (h : IsPurelyInseparable f.fieldRange L) : f.IsPurelyInseparable := by
  rw [show f = f.fieldRange.subtype.comp f.rangeRestrictField from rfl]
  exact (RingHom.isPurelyInseparable_of_surjective _ f.rangeRestrictField_bijective.surjective).comp
    (RingHom.isPurelyInseparable_algebraMap_iff.mpr h)

/-- The residue field extension at a prime `𝔮` of `S` and its contraction `𝔭`, when every element
of `S` is good: the image `k` of `κ(𝔭)` satisfies the generating condition of tag 0BR9, because
`κ(𝔮)` is generated as a field by the residues of elements of `S` and each of those has a
`p ^ n`-th power and a `p ^ n`-fold sum in `k`. Hence the structural condition: the extension is
onto, or of characteristic `p` and purely inseparable. -/
private theorem surjective_or_isPurelyInseparable_residueFieldMap {p : ℕ} (hp : p.Prime)
    (hgood : ∀ x : S, x ∈ powNsmulSet R S p) (𝔭 : Ideal R) [𝔭.IsPrime] (𝔮 : Ideal S) [𝔮.IsPrime]
    (h : 𝔭 = 𝔮.comap (algebraMap R S)) :
    Function.Surjective (Ideal.ResidueField.map 𝔭 𝔮 (algebraMap R S) h) ∨
      ringChar 𝔮.ResidueField = p ∧
        (Ideal.ResidueField.map 𝔭 𝔮 (algebraMap R S) h).IsPurelyInseparable := by
  set f := Ideal.ResidueField.map 𝔭 𝔮 (algebraMap R S) h
  have hgc : Subfield.closure ((f.fieldRange : Set 𝔮.ResidueField) ∪
      f.fieldRange.powNsmulSet p) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← closure_range_algebraMap_residueField 𝔮]
    refine Subfield.closure_mono ?_
    rintro - ⟨x, rfl⟩
    exact Or.inr (exists_pow_mem_of_mem_powNsmulSet (algebraMap S 𝔮.ResidueField)
      (fun y hy => by
        obtain ⟨r, rfl⟩ := hy
        exact ⟨algebraMap R 𝔭.ResidueField r, Ideal.ResidueField.map_algebraMap 𝔭 𝔮 _ h r⟩)
      (hgood x))
  rcases (satisfiesGeneratingCondition_iff_structuralCondition f.fieldRange p hp).mp hgc with
    htop | ⟨hchar, hpi⟩
  · exact Or.inl (RingHom.fieldRange_eq_top_iff.mp htop)
  · exact Or.inr ⟨hchar, isPurelyInseparable_of_fieldRange f hpi⟩

section BaseChange

variable {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S']
  [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

/-- The image in `S'` of a good element of `S` is a good element of `S'`, for any commuting square
of algebra maps: the image of `R → S` lands in the image of `R' → S'`. -/
private theorem algebraMap_mem_powNsmulSet_of_mem {p : ℕ} {x : S} (hx : x ∈ powNsmulSet R S p) :
    algebraMap S S' x ∈ powNsmulSet R' S' p :=
  exists_pow_mem_of_mem_powNsmulSet (algebraMap S S')
    (fun y hy => by
      obtain ⟨r, rfl⟩ := hy
      exact ⟨algebraMap R R' r, by
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S S']⟩) hx

/-- Hypothesis (a) is inherited by a base change: `S'` is generated as an `R'`-module by the image
of `S`, whose elements are good. -/
private theorem adjoin_powNsmulSet_eq_top_of_isPushout {p : ℕ}
    [Algebra.IsPushout R S R' S'] (hgood : ∀ x : S, x ∈ powNsmulSet R S p) :
    Algebra.adjoin R' (powNsmulSet R' S' p) = ⊤ :=
  eq_top_of_algebraMap_mem_of_isPushout (R := R) _ fun m =>
    Algebra.subset_adjoin (algebraMap_mem_powNsmulSet_of_mem (hgood m))

end BaseChange

namespace PrimeSpectrum

/-- Let `p` be a prime number and let `φ : R → S` be a ring map whose kernel is locally nilpotent
and such that `S` is generated as an `R`-algebra by elements `x` for which there is an `n > 0` with
`x ^ p ^ n` and `p ^ n • x` in the image of `φ`. Then `Spec(S) → Spec(R)` is a homeomorphism, every
induced residue field extension `κ(𝔭) → κ(𝔮)` is either surjective or of characteristic `p` and
purely inseparable — the equivalent conditions of
`satisfiesGeneratingCondition_iff_structuralCondition` — and both hypotheses hold again for every
base change `R' → S'` of `R → S` along an arbitrary ring map `R → R'`, i.e. for every pushout
square of `R`-algebras completing `R`, `S` by `R'`, `S'`. -/
@[stacks 0BRA]
public theorem isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_pow_eq_top
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) (hp : p.Prime)
    (hker : RingHom.ker (algebraMap R S) ≤ nilradical R)
    (hgen : Algebra.adjoin R {x : S | ∃ n > 0, x ^ p ^ n ∈ (algebraMap R S).range ∧
      p ^ n • x ∈ (algebraMap R S).range} = ⊤) :
    IsHomeomorph (comap (algebraMap R S)) ∧
      (∀ (𝔭 : Ideal R) [𝔭.IsPrime] (𝔮 : Ideal S) [𝔮.IsPrime]
        (h : 𝔭 = 𝔮.comap (algebraMap R S)),
        Function.Surjective (Ideal.ResidueField.map 𝔭 𝔮 (algebraMap R S) h) ∨
          ringChar 𝔮.ResidueField = p ∧
            (Ideal.ResidueField.map 𝔭 𝔮 (algebraMap R S) h).IsPurelyInseparable) ∧
      ∀ (R' : Type u') (S' : Type v') [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S']
        [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
        [Algebra.IsPushout R S R' S'],
        RingHom.ker (algebraMap R' S') ≤ nilradical R' ∧
          Algebra.adjoin R' {x : S' | ∃ n > 0, x ^ p ^ n ∈ (algebraMap R' S').range ∧
            p ^ n • x ∈ (algebraMap R' S').range} = ⊤ := by
  have hgood : ∀ x : S, x ∈ powNsmulSet R S p := mem_powNsmulSet hp hgen
  have hhom : IsHomeomorph (PrimeSpectrum.comap (algebraMap R S)) := by
    refine PrimeSpectrum.isHomeomorph_comap _ (fun x => ?_) hker
    obtain ⟨n, -, h₁, -⟩ := hgood x
    exact ⟨p ^ n, pow_pos hp.pos n, h₁⟩
  refine ⟨hhom, ?_, ?_⟩
  · intro 𝔭 _ 𝔮 _ h
    exact surjective_or_isPurelyInseparable_residueFieldMap hp hgood 𝔭 𝔮 h
  · intro R' S' _ _ _ _ _ _ _ _ _
    exact ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp
        (surjective_comap_of_isPushout hhom.bijective.surjective).denseRange,
      adjoin_powNsmulSet_eq_top_of_isPushout hgood⟩

end PrimeSpectrum

end

section

open Polynomial

/-- In a domain an element is determined by its square and its cube. -/
private theorem eq_of_sq_eq_of_cube_eq {A : Type*} [CommRing A] [IsDomain A] {a b : A}
    (h2 : a ^ 2 = b ^ 2) (h3 : a ^ 3 = b ^ 3) : a = b := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ^ 2 = 0 := by simpa using h2.symm
    exact ((pow_eq_zero_iff two_ne_zero).mp hb).symm
  · have h : (a - b) * a ^ 2 = 0 := by
      have hba : b * a ^ 2 = b ^ 3 := by rw [h2]; ring
      rw [sub_mul, hba, ← h3]; ring
    rcases mul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) ha

/-- An element of a field whose square and cube lie in a subfield lies in that subfield. -/
theorem Subfield.mem_of_sq_mem_of_cube_mem {K : Type*} [Field K] (F : Subfield K) {a : K}
    (h2 : a ^ 2 ∈ F) (h3 : a ^ 3 ∈ F) : a ∈ F := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact F.zero_mem
  · have h : a ^ 3 / a ^ 2 = a := by field_simp
    exact h ▸ F.div_mem h3 h2

/-- An algebra generated by elements whose square lies in the base ring is integral. -/
private theorem isIntegral_of_adjoin_sq_cube_eq_top {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤) :
    Algebra.IsIntegral R S := by
  refine ⟨fun y => ?_⟩
  have hy : y ∈ Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} :=
    hgen ▸ Algebra.mem_top
  refine (Algebra.IsIntegral.adjoin (R := R) ?_).isIntegral ⟨y, hy⟩ |>.map (Subalgebra.val _)
  rintro x ⟨h2, -⟩
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp h2
  refine ⟨X ^ 2 - C a, monic_X_pow_sub_C a two_ne_zero, ?_⟩
  simp [ha]

/-- If `S` is generated as an `R`-algebra by elements whose square and cube lie in the image of
`R`, the residue field extension `κ(p) → κ(q)` at a prime `q` of `S` over `p` is surjective. -/
private theorem residueField_map_surjective {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S)) :
    Function.Surjective (Ideal.ResidueField.map p q (algebraMap R S) hpq) := by
  have key : ∀ y : S, algebraMap S q.ResidueField y ∈
      (Ideal.ResidueField.map p q (algebraMap R S) hpq).fieldRange :=
    image_mem_of_adjoin_eq_top hgen _ _
      (fun x hx => by
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx.1
        obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hx.2
        refine Subfield.mem_of_sq_mem_of_cube_mem _
          (RingHom.mem_fieldRange.mpr ⟨algebraMap R p.ResidueField a, ?_⟩)
          (RingHom.mem_fieldRange.mpr ⟨algebraMap R p.ResidueField b, ?_⟩)
        · rw [Ideal.ResidueField.map_algebraMap, ha, map_pow]
        · rw [Ideal.ResidueField.map_algebraMap, hb, map_pow])
      fun r => RingHom.mem_fieldRange.mpr
        ⟨algebraMap R p.ResidueField r, Ideal.ResidueField.map_algebraMap p q _ hpq r⟩
  intro x
  obtain ⟨y, z, -, rfl⟩ := Ideal.exists_div_algebraMap_residueField_eq q x
  exact RingHom.mem_fieldRange.mp (Subfield.div_mem _ (key y) (key z))

/-- If `S` is generated as an `R`-algebra by elements whose square and cube lie in the image of
`R`, the residue field extension `κ(p) → κ(q)` at a prime `q` of `S` over `p` is surjective. -/
private alias residueField_map_surjective_of_adjoin_eq_top := residueField_map_surjective

/-- Two ring maps from `S` to a domain which agree on the image of `R` are equal, if `S` is
generated as an `R`-algebra by elements whose square and cube lie in the image of `R`. -/
private theorem ringHom_eq_of_adjoin_sq_cube_eq_top {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤)
    {A : Type*} [CommRing A] [IsDomain A] (χ ψ : S →+* A)
    (h : ∀ r : R, χ (algebraMap R S r) = ψ (algebraMap R S r)) (y : S) : χ y = ψ y := by
  have hy : y ∈ Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} :=
    hgen ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx.1
    obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hx.2
    refine eq_of_sq_eq_of_cube_eq ?_ ?_
    · rw [← map_pow, ← map_pow, ← ha, h]
    · rw [← map_pow, ← map_pow, ← hb, h]
  | algebraMap r => exact h r
  | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy]

/-- The prime `q` of `S` is the kernel of a ring map `S → κ(p)` over `R`, where `p` is the prime
of `R` below `q`. -/
private theorem exists_ringHom_residueField {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap (algebraMap R S)) :
    ∃ χ : S →+* p.ResidueField,
      (∀ r : R, χ (algebraMap R S r) = algebraMap R p.ResidueField r) ∧
        ∀ y : S, χ y = 0 ↔ y ∈ q := by
  have hbij : Function.Bijective (Ideal.ResidueField.map p q (algebraMap R S) hpq) :=
    ⟨(Ideal.ResidueField.map p q (algebraMap R S) hpq).injective,
      residueField_map_surjective hgen p q hpq⟩
  set e := RingEquiv.ofBijective _ hbij
  have hcoe : ∀ x, e x = Ideal.ResidueField.map p q (algebraMap R S) hpq x := fun _ => rfl
  refine ⟨(e.symm : q.ResidueField →+* p.ResidueField).comp (algebraMap S q.ResidueField),
    fun r => ?_, fun y => ?_⟩
  · change e.symm (algebraMap S q.ResidueField (algebraMap R S r)) = algebraMap R p.ResidueField r
    rw [← Ideal.ResidueField.map_algebraMap p q (algebraMap R S) hpq r, ← hcoe,
      e.symm_apply_apply]
  · change e.symm (algebraMap S q.ResidueField y) = 0 ↔ y ∈ q
    rw [← Ideal.algebraMap_residueField_eq_zero (I := q) (x := y),
      EmbeddingLike.map_eq_zero_iff]

/-- If `S` is generated as an `R`-algebra by elements whose square and cube lie in the image of
`R` and `R → S` has locally nilpotent kernel, then `Spec S → Spec R` is surjective. -/
private theorem comap_surjective_of_ker_le_nilradical {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤)
    (hker : RingHom.ker (algebraMap R S) ≤ nilradical R) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
  have : Algebra.IsIntegral R S := isIntegral_of_adjoin_sq_cube_eq_top hgen
  intro p
  obtain ⟨q, -, hq, hq'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal ⊥
    (hker.trans (nilradical_le_prime p.asIdeal))
  exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hq'⟩

/-- If `S` is generated as an `R`-algebra by elements whose square and cube lie in the image of
`R`, then `Spec S → Spec R` is injective. -/
private theorem comap_injective_of_adjoin_sq_cube_eq_top {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤) :
    Function.Injective (PrimeSpectrum.comap (algebraMap R S)) := by
  intro q q' hqq'
  set p : Ideal R := q.asIdeal.comap (algebraMap R S) with hp
  have : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨χ, hχ, hχ'⟩ := exists_ringHom_residueField hgen p q.asIdeal hp
  obtain ⟨ψ, hψ, hψ'⟩ := exists_ringHom_residueField hgen p q'.asIdeal
    (hp.trans (congrArg PrimeSpectrum.asIdeal hqq'))
  have hχψ : ∀ y : S, χ y = ψ y :=
    ringHom_eq_of_adjoin_sq_cube_eq_top hgen χ ψ fun r => by rw [hχ, hψ]
  refine PrimeSpectrum.ext (Ideal.ext fun y => ?_)
  rw [← hχ' y, ← hψ' y, hχψ y]

/-- Generation by elements whose square and cube lie in the image of the base is stable under
pushout. -/
private theorem adjoin_sq_cube_eq_top_of_isPushout {R S R' S' : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
    [IsScalarTower R S S'] [IsScalarTower R R' S'] [Algebra.IsPushout R S R' S'] :
    Algebra.adjoin R'
      {x : S' | x ^ 2 ∈ (⊥ : Subalgebra R' S') ∧ x ^ 3 ∈ (⊥ : Subalgebra R' S')} = ⊤ := by
  have key : ∀ y : S, algebraMap S S' y ∈ Algebra.adjoin R'
      {x : S' | x ^ 2 ∈ (⊥ : Subalgebra R' S') ∧ x ^ 3 ∈ (⊥ : Subalgebra R' S')} :=
    image_mem_of_adjoin_eq_top hgen _ _
      (fun x hx => by
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx.1
        obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hx.2
        refine Algebra.subset_adjoin ⟨Algebra.mem_bot.mpr ⟨algebraMap R R' a, ?_⟩,
          Algebra.mem_bot.mpr ⟨algebraMap R R' b, ?_⟩⟩
        · rw [← IsScalarTower.algebraMap_apply R R' S', IsScalarTower.algebraMap_apply R S S',
            ha, map_pow]
        · rw [← IsScalarTower.algebraMap_apply R R' S', IsScalarTower.algebraMap_apply R S S',
            hb, map_pow])
      fun r => by
        rw [← IsScalarTower.algebraMap_apply R S S', IsScalarTower.algebraMap_apply R R' S']
        exact Subalgebra.algebraMap_mem _ _
  exact eq_top_of_algebraMap_mem_of_isPushout (R := R) _ key

/-- If `S` is generated as an `R`-algebra by elements whose square and cube lie in the image of
`R` and `Spec S → Spec R` is surjective, then any pushout `R' → S'` has locally nilpotent
kernel. -/
private theorem ker_le_nilradical_of_isPushout {R S R' S' : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
    [IsScalarTower R S S'] [IsScalarTower R R' S'] [Algebra.IsPushout R S R' S'] :
    RingHom.ker (algebraMap R' S') ≤ nilradical R' := by
  intro x' hx'
  rw [nilradical_eq_sInf]
  refine Ideal.mem_sInf.mpr fun {p'} hp' => ?_
  have : p'.IsPrime := hp'
  set p : Ideal R := p'.comap (algebraMap R R') with hp
  have : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨q, hq⟩ := hsurj ⟨p, ‹p.IsPrime›⟩
  obtain ⟨χ, hχ, -⟩ := exists_ringHom_residueField hgen p q.asIdeal
    (congrArg PrimeSpectrum.asIdeal hq).symm
  let f : S →ₐ[R] p'.ResidueField :=
    { (Ideal.ResidueField.map p p' (algebraMap R R') hp).comp χ with
      commutes' := fun r => by
        change (Ideal.ResidueField.map p p' (algebraMap R R') hp) (χ (algebraMap R S r)) = _
        rw [hχ r, Ideal.ResidueField.map_algebraMap p p' _ hp r,
          ← IsScalarTower.algebraMap_apply R R' p'.ResidueField] }
  let g : R' →ₐ[R] p'.ResidueField := IsScalarTower.toAlgHom R R' p'.ResidueField
  have hdesc := Algebra.pushoutDesc_right S' f g (fun x y => mul_comm _ _) x'
  rw [RingHom.mem_ker.mp hx', map_zero] at hdesc
  exact (Ideal.algebraMap_residueField_eq_zero (I := p')).mp hdesc.symm

namespace PrimeSpectrum

/-- Let `R → S` be a ring map with locally nilpotent kernel such that `S` is generated as an
`R`-algebra by elements whose square and cube lie in the image of `R`. Then `Spec S → Spec R` is a
homeomorphism, the induced residue field extensions `κ(𝔭) → κ(𝔮)` are isomorphisms, and both
hypotheses again hold for the base change `R' → S'` of `R → S` along any ring map `R → R'`. -/
@[stacks 0EUH]
public theorem isHomeomorph_comap_and_residueFieldMap_bijective_of_adjoin_sq_cube_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hgen : Algebra.adjoin R
      {x : S | x ^ 2 ∈ (⊥ : Subalgebra R S) ∧ x ^ 3 ∈ (⊥ : Subalgebra R S)} = ⊤)
    (hker : RingHom.ker (algebraMap R S) ≤ nilradical R) :
    IsHomeomorph (comap (algebraMap R S)) ∧
      (∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
        (hpq : p = q.comap (algebraMap R S)),
          Function.Bijective (Ideal.ResidueField.map p q (algebraMap R S) hpq)) ∧
      ∀ (R' : Type v) (S' : Type w) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R S']
        [Algebra S S'] [Algebra R' S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
        [Algebra.IsPushout R S R' S'],
          Algebra.adjoin R'
            {x : S' | x ^ 2 ∈ (⊥ : Subalgebra R' S') ∧ x ^ 3 ∈ (⊥ : Subalgebra R' S')} = ⊤ ∧
            RingHom.ker (algebraMap R' S') ≤ nilradical R' := by
  have hsurj := comap_surjective_of_ker_le_nilradical hgen hker
  refine ⟨isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨PrimeSpectrum.continuous_comap _, PrimeSpectrum.isClosedMap_comap_of_isIntegral _
      (isIntegral_of_adjoin_sq_cube_eq_top hgen).isIntegral,
      comap_injective_of_adjoin_sq_cube_eq_top hgen, hsurj⟩,
    fun p _ q _ hpq => ⟨(Ideal.ResidueField.map p q (algebraMap R S) hpq).injective,
      residueField_map_surjective hgen p q hpq⟩,
    fun R' S' _ _ _ _ _ _ _ _ _ => ⟨adjoin_sq_cube_eq_top_of_isPushout hgen,
      ker_le_nilradical_of_isPushout hgen hsurj⟩⟩

end PrimeSpectrum

end
