module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceGenericFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierIntegralComponents
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassSurjective
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksCore.Tactic.StacksAttribute

/-!
# The reduction of a sum of distinct integral divisors is their sum

Let `X` be an integral scheme and let `C₁, …, C_n` be pairwise distinct integral effective
Cartier divisors on `X`.  Then

`rad(Σ mᵢ Cᵢ) = Σ Cᵢ`  for positive multiplicities `mᵢ`,

written multiplicatively as `(∏ Cᵢ ^ mᵢ).radical = ∏ Cᵢ` for sheaves of ideals.  In particular
the reduction of the special fibre of a regular model is the sum of its irreducible components,
which is the identity carried as the hypothesis `hred` by the theorems built on the
decomposition `X_k = Σ mᵢ Cᵢ` of [Stacks, Tag 0C5Z] part (3).

## Main results

* `Stacks.Divisors.radical_prod_eq_prod_of_pairwise_ne` — the product of pairwise distinct
  integral effective Cartier divisors is already radical.
* `Stacks.Divisors.radical_prod_pow_eq_prod_of_pairwise_ne` — the general statement
  `(∏ Cᵢ ^ mᵢ).radical = ∏ Cᵢ`.
* `Stacks.Models.RegularModelSituation.radical_specialFiberIdeal_eq_prod_of_pairwise_ne` — the
  same at an arbitrary decomposition of the special fibre of a regular model.
* `Stacks.Models.RegularModelSituation.radical_specialFiberIdeal_eq_prod` — the canonical case,
  `rad(X_k) = Σ Cᵢ` over the irreducible components of `X_k`.

## The argument

Products and intersections of sheaves of ideals differ in general, so the identity is not formal;
what makes it true is that the divisors are locally principal and integral.  The proof is local
and elementary.

*Reduction to the squarefree case.* Raising a factor to a positive power does not change its
support, so `Σ mᵢ Cᵢ` and `Σ Cᵢ` have the same support; a radical sheaf of ideals is the
vanishing ideal of its support (`Scheme.IdealSheafData.vanishingIdeal_support`), so the two sums
have the same radical.  It therefore suffices to prove that `∏ Cᵢ` is radical.

*Locally.* Radicality is an inequality between sheaves of ideals, so it may be checked on an open
cover.  Around any point choose an affine open `Spec A ⊆ X` on which every `Cᵢ` is principal —
possible because each is an effective Cartier divisor and there are finitely many of them, and
principality passes to smaller affine opens by `Scheme.IdealSheafData.map_ideal`.  On such a
chart `A` is a domain, `Cᵢ` is cut out by a single `fᵢ ∈ A`, and `fᵢ` is either a unit (when `Cᵢ`
misses the chart) or a prime element: the ideal it generates is the vanishing ideal of the
irreducible closed set `supp Cᵢ`, which is prime on any chart it meets
(`Stacks.Divisors.isPrime_ideal_vanishingIdeal`).

*Distinctness becomes non-associateness.* Two distinct components have distinct supports, because
an integral closed subscheme is the reduced structure on its support, and a nonempty open piece of
an irreducible set is dense in it (`Stacks.Divisors.subset_closure_inter_of_isIrreducible`); so on
a chart that both meet they are cut out by non-associate primes.

*The ring-theoretic core.* In a domain, a product of pairwise non-associate primes generates a
radical ideal: if `fᵢ ∣ x ^ k` then `fᵢ ∣ x` by primality, and a common multiple of pairwise
non-associate primes is divisible by their product, because `f_{j+1}` is prime and divides no
`f₁ ⋯ f_j`.

## Implementation notes

The hypothesis of pairwise distinctness cannot be dropped.  With `ι = Fin 2` and
`C 0 = C 1 = C` a single integral effective Cartier divisor, `m = (1, 1)`, every other hypothesis
holds while `rad(C ^ 2) = C` and `∏ i, C i = C ^ 2`.

Distinctness is used only through the weaker-looking consequence that the generators on a chart
are non-associate; incomparability of the supports is *not* needed, because two distinct proper
principal primes of a domain are automatically incomparable.

## References

* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace Stacks.Divisors

/-! ### A product of pairwise non-associate primes -/

/-- **A product of pairwise non-associate prime elements divides every common multiple.**  The
induction step removes one factor `f i`: it is prime and divides no other factor, hence divides
no product of the others, so it divides the cofactor left by the inductive hypothesis. -/
theorem prod_dvd_of_forall_dvd_of_prime {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (s : Finset ι) (f : ι → R) (x : R) (hp : ∀ i ∈ s, Prime (f i))
    (hassoc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Associated (f i) (f j))
    (hdvd : ∀ i ∈ s, f i ∣ x) : (∏ i ∈ s, f i) ∣ x := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i t hit ih =>
      have hmem : ∀ j ∈ t, j ∈ Finset.cons i t hit := fun j hj => Finset.mem_cons_of_mem hj
      have hi : i ∈ Finset.cons i t hit := Finset.mem_cons_self ..
      obtain ⟨y, hy⟩ := ih (fun j hj => hp j (hmem j hj))
        (fun j hj l hl hjl => hassoc j (hmem j hj) l (hmem l hl) hjl)
        (fun j hj => hdvd j (hmem j hj))
      have hpi : Prime (f i) := hp i hi
      have hnot : ¬ f i ∣ ∏ j ∈ t, f j := by
        intro h
        obtain ⟨j, hj, hji⟩ := (hpi.dvd_finset_prod_iff f).mp h
        refine hassoc i hi j (hmem j hj) (fun hij => hit (hij ▸ hj)) ?_
        exact (hpi.dvd_prime_iff_associated (hp j (hmem j hj))).mp hji
      have hdy : f i ∣ y := by
        have hx : f i ∣ (∏ j ∈ t, f j) * y := hy ▸ hdvd i hi
        exact (hpi.dvd_or_dvd hx).resolve_left hnot
      obtain ⟨z, rfl⟩ := hdy
      exact ⟨z, by rw [Finset.prod_cons, hy]; ring⟩

/-- **A product of pairwise non-associate primes generates a radical ideal.**  Primality carries
each factor out of a power, and then the product divides the element. -/
theorem radical_span_singleton_prod_le {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (s : Finset ι) (f : ι → R) (hp : ∀ i ∈ s, Prime (f i))
    (hassoc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Associated (f i) (f j)) :
    (Ideal.span {∏ i ∈ s, f i}).radical ≤ Ideal.span {∏ i ∈ s, f i} := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  exact prod_dvd_of_forall_dvd_of_prime s f x hp hassoc fun i hi =>
    (hp i hi).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem f hi).trans hn)

/-! ### Finite products of sheaves of ideals -/

variable {X : Scheme.{u}}

/-- The support of a finite product of sheaves of ideals is the union of their supports. -/
theorem support_finsetProd {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData) :
    (∏ i ∈ s, C i).support = s.sup fun i => (C i).support := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [Scheme.IdealSheafData.one_eq_top]
  | cons i t hit ih =>
      rw [Finset.prod_cons, Scheme.IdealSheafData.support_mul, ih, Finset.sup_cons]

/-- The support of a finite product of positive powers of sheaves of ideals is the union of the
supports of the bases: a positive power has the same support as its base. -/
theorem support_finsetProd_pow {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData) (m : ι → ℕ)
    (hm : ∀ i ∈ s, m i ≠ 0) :
    (∏ i ∈ s, C i ^ m i).support = s.sup fun i => (C i).support := by
  rw [support_finsetProd]
  exact Finset.sup_congr rfl fun i hi => Scheme.IdealSheafData.support_pow _ _ (hm i hi)

/-- **Positive multiplicities do not change the reduction.**  A radical sheaf of ideals is the
vanishing ideal of its support, and raising the factors to positive powers leaves the support of
a product alone. -/
theorem radical_prod_pow_eq_radical_prod {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData)
    (m : ι → ℕ) (hm : ∀ i ∈ s, m i ≠ 0) :
    (∏ i ∈ s, C i ^ m i).radical = (∏ i ∈ s, C i).radical := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support (I := ∏ i ∈ s, C i ^ m i),
    ← Scheme.IdealSheafData.vanishingIdeal_support (I := ∏ i ∈ s, C i),
    support_finsetProd_pow s C m hm, support_finsetProd s C]

/-! ### Simultaneous local equations -/

/-- **Finitely many effective Cartier divisors are simultaneously principal near any point.**
Each is principal on some affine open neighbourhood; shrinking to a common affine open
neighbourhood keeps them principal, because the ideal cut out on a smaller affine open is the
image of the ideal cut out on the larger one. -/
theorem exists_affineOpen_forall_ideal_eq_span {ι : Type*} (s : Finset ι)
    (C : ι → X.IdealSheafData) (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i)) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U.1 : Set X) ∧
      ∃ f : ι → Γ(X, U.1), ∀ i ∈ s, (C i).ideal U = Ideal.span {f i} := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
      exact ⟨U, hxU, 0, by simp⟩
  | cons i t hit ih =>
      obtain ⟨W, hxW, g, hg⟩ := ih fun j hj => hC j (Finset.mem_cons_of_mem hj)
      obtain ⟨V, hV, hxV, b, -, hb⟩ :=
        exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor (C i)
          (hC i (Finset.mem_cons_self ..)) x
      obtain ⟨-, ⟨A, hA, rfl⟩, hxA, hsub⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ (W.1 : Set X) ∩ (V : Set X) from ⟨hxW, hxV⟩)
          ((W.1 : X.Opens).isOpen.inter V.isOpen)
      have hAW : (⟨A, hA⟩ : X.affineOpens) ≤ W := fun z hz => (hsub hz).1
      have hAV : (⟨A, hA⟩ : X.affineOpens) ≤ (⟨V, hV⟩ : X.affineOpens) :=
        fun z hz => (hsub hz).2
      refine ⟨⟨A, hA⟩, hxA, Function.update
        (fun j => (X.presheaf.map (homOfLE hAW).op).hom (g j)) i
        ((X.presheaf.map (homOfLE hAV).op).hom b), fun j hj => ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hjt
      · rw [Function.update_self, ← Scheme.IdealSheafData.map_ideal (C j) hAV, hb,
          Ideal.map_span, Set.image_singleton]
      · rw [Function.update_of_ne (fun h : j = i => hit (h ▸ hjt)),
          ← Scheme.IdealSheafData.map_ideal (C j) hAW, hg j hjt, Ideal.map_span,
          Set.image_singleton]

/-! ### The product of distinct integral divisors is radical -/

variable [IsIntegral X]

omit [IsIntegral X] in
/-- The support of a sheaf of ideals with integral closed subscheme is irreducible: it is the
range of the closed immersion of that subscheme. -/
theorem isIrreducible_support_of_isIntegral_subscheme (D : X.IdealSheafData)
    [AlgebraicGeometry.IsIntegral D.subscheme] :
    IsIrreducible ((D.support : Closeds X) : Set X) := by
  have h := (IrreducibleSpace.isIrreducible_univ D.subscheme).image D.subschemeι
    D.subschemeι.continuous.continuousOn
  rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h
  exact h

omit [IsIntegral X] in
/-- **Away from its support a sheaf of ideals is the unit ideal.**  The zero locus of the ideal
cut out on an affine open is the part of the support lying over that open. -/
theorem ideal_eq_top_of_support_inter_eq_empty (D : X.IdealSheafData) (U : X.affineOpens)
    (hempty : ((D.support : Closeds X) : Set X) ∩ (U.1 : Set X) = ∅) : D.ideal U = ⊤ := by
  have h1 : (U.2.fromSpec : _ → X) ⁻¹' D.supportSet = ∅ := by
    have h2 := fromSpec_image_preimage U D.supportSet
    rw [show D.supportSet = ((D.support : Closeds X) : Set X) from rfl, hempty] at h2
    exact Set.image_eq_empty.mp h2
  rw [preimage_fromSpec_supportSet] at h1
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h1

/-- **The product of pairwise distinct integral effective Cartier divisors is radical.**  On a
chart carrying simultaneous local equations the product is cut out by a product of pairwise
non-associate primes, which generates a radical ideal. -/
theorem radical_prod_eq_prod_of_pairwise_ne {ι : Type*} (s : Finset ι)
    (C : ι → X.IdealSheafData)
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hint : ∀ i ∈ s, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → C i ≠ C j) :
    (∏ i ∈ s, C i).radical = ∏ i ∈ s, C i := by
  classical
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
  -- the inequality is local, so it is enough to produce a good chart around every point
  have key : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U.1 : Set X) ∧
      ((∏ i ∈ s, C i).radical).ideal U ≤ (∏ i ∈ s, C i).ideal U := by
    intro x
    obtain ⟨U, hxU, f, hf⟩ := exists_affineOpen_forall_ideal_eq_span s C hC x
    refine ⟨U, hxU, ?_⟩
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    have : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
    -- each component is the reduced structure on its irreducible support
    have hvan : ∀ i ∈ s, C i = Scheme.IdealSheafData.vanishingIdeal (C i).support := by
      intro i hi
      have := hint i hi
      have : IsReduced (C i).subscheme := inferInstance
      exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme (C i) (C i).support rfl
    have hirr : ∀ i ∈ s, IsIrreducible (((C i).support : Closeds X) : Set X) := by
      intro i hi
      have := hint i hi
      exact isIrreducible_support_of_isIntegral_subscheme (C i)
    -- a proper ideal on the chart means the support meets the chart
    have hmeet : ∀ i ∈ s, (C i).ideal U ≠ ⊤ →
        ((((C i).support : Closeds X) : Set X) ∩ (U.1 : Set X)).Nonempty := by
      intro i _ hprop
      rcases Set.eq_empty_or_nonempty
        ((((C i).support : Closeds X) : Set X) ∩ (U.1 : Set X)) with hemp | h
      · exact absurd (ideal_eq_top_of_support_inter_eq_empty (C i) U hemp) hprop
      · exact h
    -- and then it is prime
    have hprime : ∀ i ∈ s, (C i).ideal U ≠ ⊤ → ((C i).ideal U).IsPrime := by
      intro i hi hprop
      rw [hvan i hi]
      exact isPrime_ideal_vanishingIdeal _ (hirr i hi).2 U (hmeet i hi hprop)
    -- distinct components have distinct ideals on a chart they both meet
    have hsupp : ∀ i ∈ s, ∀ j ∈ s, (C i).ideal U ≠ ⊤ → (C i).ideal U = (C j).ideal U →
        (((C i).support : Closeds X) : Set X) ⊆ (((C j).support : Closeds X) : Set X) := by
      intro i hi j hj hprop heq
      have hset : (((C i).support : Closeds X) : Set X) ∩ (U.1 : Set X) =
          (((C j).support : Closeds X) : Set X) ∩ (U.1 : Set X) := by
        rw [show (((C i).support : Closeds X) : Set X) = (C i).supportSet from rfl,
          show (((C j).support : Closeds X) : Set X) = (C j).supportSet from rfl,
          ← fromSpec_image_preimage U (C i).supportSet,
          ← fromSpec_image_preimage U (C j).supportSet,
          preimage_fromSpec_supportSet, preimage_fromSpec_supportSet, heq]
      have hdense := subset_closure_inter_of_isIrreducible (hirr i hi) (U.1).isOpen
        (hmeet i hi hprop)
      rw [hset] at hdense
      exact hdense.trans (closure_minimal Set.inter_subset_left
        (Scheme.IdealSheafData.isClosed_supportSet (C j)))
    have hidne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (C i).ideal U ≠ ⊤ → (C j).ideal U ≠ ⊤ →
        (C i).ideal U ≠ (C j).ideal U := by
      intro i hi j hj hij hti htj heq
      refine hne i hi j hj hij ?_
      have h1 : (((C i).support : Closeds X) : Set X) = (((C j).support : Closeds X) : Set X) :=
        le_antisymm (hsupp i hi j hj hti heq) (hsupp j hj i hi htj heq.symm)
      rw [hvan i hi, hvan j hj, TopologicalSpace.Closeds.ext h1]
    -- read the product off the chart, dropping the factors that miss it
    set t := s.filter (fun i => (C i).ideal U ≠ ⊤) with htdef
    have hts : t ⊆ s := Finset.filter_subset _ _
    have htmem : ∀ i ∈ t, (C i).ideal U ≠ ⊤ := fun i hi => (Finset.mem_filter.mp hi).2
    have hprodU : (∏ i ∈ s, C i).ideal U = Ideal.span {∏ i ∈ t, f i} := by
      rw [ideal_finsetProd]
      rw [← Finset.prod_subset hts (fun i hi hit => by
        have : (C i).ideal U = ⊤ := by
          by_contra hcon
          exact hit (Finset.mem_filter.mpr ⟨hi, hcon⟩)
        rw [this, Ideal.one_eq_top])]
      rw [← Ideal.prod_span_singleton]
      exact Finset.prod_congr rfl fun i hi => hf i (hts hi)
    rw [show ((∏ i ∈ s, C i).radical).ideal U = ((∏ i ∈ s, C i).ideal U).radical from rfl,
      hprodU]
    by_cases hz : ∃ i ∈ t, f i = 0
    · obtain ⟨i, hi, hfi⟩ := hz
      rw [Finset.prod_eq_zero hi hfi]
      intro y hy
      obtain ⟨n, hn⟩ := hy
      rw [Ideal.mem_span_singleton, zero_dvd_iff] at hn ⊢
      exact (pow_eq_zero_iff'.mp hn).1
    · have hz' : ∀ i ∈ t, f i ≠ 0 := fun i hi hfi => hz ⟨i, hi, hfi⟩
      refine radical_span_singleton_prod_le t f (fun i hi => ?_) (fun i hi j hj hij => ?_)
      · exact (Ideal.span_singleton_prime (hz' i hi)).mp
          (hf i (hts hi) ▸ hprime i (hts hi) (htmem i hi))
      · intro hass
        refine hidne i (hts hi) j (hts hj) hij (htmem i hi) (htmem j hj) ?_
        rw [hf i (hts hi), hf j (hts hj)]
        exact le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hass.symm.dvd)
          (Ideal.span_singleton_le_span_singleton.mpr hass.dvd)
  choose U hxU hle using key
  refine Scheme.IdealSheafData.le_of_iSup_eq_top U (le_antisymm le_top fun x _ => ?_) hle
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- **The reduction of a sum of pairwise distinct integral effective Cartier divisors.**  For
positive multiplicities `mᵢ` and pairwise distinct integral effective Cartier divisors `Cᵢ` on an
integral scheme,

`rad(Σ mᵢ Cᵢ) = Σ Cᵢ`.

Pairwise distinctness is necessary: with `C 0 = C 1` and `m = (1, 1)` the left-hand side is
`C 0` and the right-hand side `C 0 ^ 2`. -/
theorem radical_prod_pow_eq_prod_of_pairwise_ne {ι : Type*} (s : Finset ι)
    (C : ι → X.IdealSheafData) (m : ι → ℕ)
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hint : ∀ i ∈ s, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → C i ≠ C j)
    (hm : ∀ i ∈ s, m i ≠ 0) :
    (∏ i ∈ s, C i ^ m i).radical = ∏ i ∈ s, C i :=
  (radical_prod_pow_eq_radical_prod s C m hm).trans
    (radical_prod_eq_prod_of_pairwise_ne s C hC hint hne)

end Stacks.Divisors

namespace Stacks.Models

namespace RegularModelSituation

open Stacks.Divisors

variable (S : RegularModelSituation.{u})

/-- **The reduction of the special fibre at a decomposition into distinct components.**  If the
special fibre of a regular model is written `X_k = Σ mᵢ Cᵢ` with positive multiplicities and
pairwise distinct integral effective Cartier divisors `Cᵢ`, then its reduction is `Σ Cᵢ`.

This is the hypothesis called `hred` in the theorems built on such a decomposition; the content
is `Stacks.Divisors.radical_prod_pow_eq_prod_of_pairwise_ne`, applied on the total space of the
model, which is integral. -/
theorem radical_specialFiberIdeal_eq_prod_of_pairwise_ne {ι : Type*} (s : Finset ι)
    (C : ι → S.X.IdealSheafData) (m : ι → ℕ)
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hint : ∀ i ∈ s, AlgebraicGeometry.IsIntegral (C i).subscheme)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → C i ≠ C j)
    (hm : ∀ i ∈ s, 0 < m i)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    S.specialFiberIdeal.radical = ∏ i ∈ s, C i := by
  have : IsIntegral S.X := S.isIntegral_X
  rw [hdec]
  exact radical_prod_pow_eq_prod_of_pairwise_ne s C m hC hint hne fun i hi => (hm i hi).ne'

/-- **Distinct irreducible components of the special fibre cut out distinct sheaves of ideals**:
the support of the component ideal is the image of the component, and the special fibre is
embedded in the model. -/
theorem specialFiberComponentIdeal_ne {Z W : irreducibleComponents S.specialFiber}
    (h : Z ≠ W) : S.specialFiberComponentIdeal Z ≠ S.specialFiberComponentIdeal W := by
  intro heq
  refine h (Subtype.ext ?_)
  have h1 := S.coe_support_specialFiberComponentIdeal Z
  rw [heq] at h1
  exact Set.image_injective.mpr S.specialFiberι.isClosedEmbedding.injective
    (h1.symm.trans (S.coe_support_specialFiberComponentIdeal W))

/-- **The reduced special fibre is the sum of the irreducible components of the special fibre**,

`rad(X_k) = Σ_i Cᵢ`,

over the finitely many irreducible components `Cᵢ` of `X_k` taken with their reduced induced
structure.  Together with `X_k = Σ mᵢ Cᵢ`, part (3) of [Stacks, Tag 0C5Z], this is the
identification of the reduction of the special fibre used throughout the genus formula for a
regular model.

The components are integral effective Cartier divisors with positive multiplicities and they are
pairwise distinct, so this is
`Stacks.Divisors.radical_prod_pow_eq_prod_of_pairwise_ne` at the canonical family. -/
theorem radical_specialFiberIdeal_eq_prod :
    S.specialFiberIdeal.radical = ∏ Z, S.specialFiberComponentIdeal Z :=
  S.radical_specialFiberIdeal_eq_prod_of_pairwise_ne Finset.univ S.specialFiberComponentIdeal
    S.specialFiberMultiplicity
    (fun Z _ => S.isEffectiveCartierDivisor_specialFiberComponent Z)
    (fun _ _ => inferInstance)
    (fun _ _ _ _ hZW => S.specialFiberComponentIdeal_ne hZW)
    (fun Z _ => S.specialFiberMultiplicity_pos Z)
    S.specialFiberIdeal_eq_prod

end RegularModelSituation

end Stacks.Models

end
