module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Noether normalization at a point

Stacks tag 00OZ (Commutative Algebra, Lemma 10.115.5).

Let `k` be a field and `S` a finite type `k`-algebra, i.e. a commutative `k`-algebra
finitely generated as a `k`-algebra, and write `X = Spec(S)` for the prime spectrum of `S`.
For `g ∈ S` we write `S_g` for the localization of `S` away from `g`, that is the
localization at `{1, g, g², …}`, and identify `Spec(S_g)` with the standard open `D(g)`.
For a commutative ring `R`, `dim(R)` is its Krull dimension, the supremum of the lengths
`n` of chains of primes `p_0 ⊊ p_1 ⊊ ⋯ ⊊ p_n`, an element of
`{-∞} ∪ {0, 1, 2, …} ∪ {∞}`; in Lean this is `ringKrullDim R : WithBot ℕ∞`.

The Krull dimension of a topological space `T` at a point `x ∈ T` is
`dim_x(T) = min { dim(U) : x ∈ U ⊆ T open }`. For `X = Spec(S)` and `q` the prime of `S`
corresponding to `x`, the standard opens `D(g) = Spec(S_g)` with `g ∈ S \ q` form a basis
of open neighbourhoods of `x` and `dim(D(g)) = dim(S_g)`, so
`dim_x(X) = min { dim(S_g) : g ∈ S, g ∉ q }`, and the minimum is attained. This is the
form used here, taken as an infimum over `WithBot ℕ∞`; see `localDimAtPrime`. The equality
with the topological local dimension `topologicalKrullDimAt` of 0055 (4) is proved in
`StacksFrontier.RingTheory.NoetherNormalization.AtPoint` as
`topologicalKrullDimAt_eq_localDimAtPrime`, which also states 00OZ with `dim_x(X)` itself
(`noether_normalization_at_point_topologicalKrullDimAt`).

The main result is that there exist `g ∈ S` with `g ∉ q`, a natural number `d`, and a
`k`-algebra homomorphism `ψ : k[y_1, …, y_d] → S_g` such that `d = dim(S_g) = dim_x(X)`
and `ψ` is injective and finite, where finite means that `S_g` is a finitely generated
module over `k[y_1, …, y_d]` and injectivity says that the images of `y_1, …, y_d` are
algebraically independent over `k`. The polynomial ring `k[y_1, …, y_d]` is
`MvPolynomial (Fin d) k`, with `MvPolynomial (Fin 0) k ≃ k` when `d = 0`. Since `X`
contains `x` it is nonempty, so `S` and each `S_g` with `g ∉ q` are nonzero; hence `d` is
a genuine natural number and `dim_x(X)` is finite.
-/

@[expose] public section

open Algebra

/-- The Krull dimension of `X = Spec(S)` at the point corresponding to a prime ideal `q`:
the infimum over `WithBot ℕ∞` of the Krull dimensions `dim(S_g)` of the localizations of
`S` away from elements `g ∉ q`. Since the standard opens `D(g) = Spec(S_g)` for `g ∉ q`
form a neighbourhood basis of the point and `dim(D(g)) = dim(S_g)`, this agrees with the
topological local dimension `min { dim(U) : x ∈ U ⊆ X open }`; that equality is
`topologicalKrullDimAt_eq_localDimAtPrime` in
`StacksFrontier.RingTheory.NoetherNormalization.AtPoint`. -/
@[ega "IV 17.15.8", sga "1 II 5.9"]
noncomputable def localDimAtPrime (k : Type*) {S : Type*} [Field k] [CommRing S] [Algebra k S]
    (q : Ideal S) : WithBot ℕ∞ :=
  ⨅ g ∈ (qᶜ : Set S), ringKrullDim (Localization.Away g)

/-- Going up for chains: over an integral extension `R → T` whose map on spectra is
surjective, every chain of primes of `R` lifts to a chain of the same length in `T`. -/
theorem exists_ltSeries_lift_of_isIntegral {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [Algebra.IsIntegral R T]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R T)))
    (p : LTSeries (PrimeSpectrum R)) :
    ∃ q : LTSeries (PrimeSpectrum T),
      q.length = p.length ∧ PrimeSpectrum.comap (algebraMap R T) q.last = p.last := by
  obtain ⟨n, hn⟩ : ∃ n, p.length = n := ⟨_, rfl⟩
  induction n generalizing p with
  | zero =>
    obtain ⟨Q, hQ⟩ := hsurj p.last
    exact ⟨RelSeries.singleton _ Q, by simp [hn], hQ⟩
  | succ m ih =>
    have hlen0 : p.length ≠ 0 := by lia
    obtain ⟨q', hq'len, hq'last⟩ := ih p.eraseLast (by simp [hn])
    have hrel : p.eraseLast.last < p.last := p.eraseLast_last_rel_last hlen0
    have hle : Ideal.comap (algebraMap R T) q'.last.asIdeal ≤ p.last.asIdeal := by
      rw [← PrimeSpectrum.comap_asIdeal, hq'last]
      exact hrel.le
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal q'.last.asIdeal hle
    let Qp : PrimeSpectrum T := ⟨Q, hQprime⟩
    have hcomapQp : PrimeSpectrum.comap (algebraMap R T) Qp = p.last := PrimeSpectrum.ext hQcomap
    have hltQp : q'.last < Qp := by
      refine (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (lt_of_le_of_ne hQge fun heq => ?_)
      have hcc : PrimeSpectrum.comap (algebraMap R T) q'.last =
          PrimeSpectrum.comap (algebraMap R T) Qp :=
        PrimeSpectrum.ext (congrArg (Ideal.comap (algebraMap R T)) heq)
      rw [hq'last, hcomapQp] at hcc
      exact hrel.ne hcc
    exact ⟨q'.snoc Qp hltQp, by simp [hq'len, hn], by rwa [RelSeries.last_snoc]⟩

/-- An injective integral ring homomorphism `f : R →+* T` preserves Krull dimension:
`ringKrullDim R = ringKrullDim T`. -/
@[ega "0 16.1.5", ega "0 16.1.6" "Case where B is local", ega "IV 5.4.3" "more general"]
theorem ringKrullDim_eq_of_injective_isIntegral
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (hinj : Function.Injective f) (hint : f.IsIntegral) :
    ringKrullDim R = ringKrullDim T := by
  let := f.toAlgebra
  have : Algebra.IsIntegral R T := ⟨hint⟩
  refine le_antisymm (iSup_le fun p => ?_) ?_
  · obtain ⟨q, hqlen, _⟩ := exists_ltSeries_lift_of_isIntegral (hint.comap_surjective hinj) p
    rw [← hqlen]
    exact Order.LTSeries.length_le_krullDim q
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) fun x y hxy => ?_
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hxy ⊢
    have : x.asIdeal.IsPrime := x.isPrime
    exact Ideal.IsIntegral.under_lt_under hxy

/-- Global Noether normalization (Stacks tag 00OY): a nonzero finite type algebra `T` over
a field `k` admits `d : ℕ` and an injective finite `k`-algebra map
`ψ : k[y_1, …, y_d] → T` with `(d : WithBot ℕ∞) = ringKrullDim T`. -/
@[ega "IV 6.11.9" "special case"]
theorem noether_normalization_global
    {k T : Type*} [Field k] [CommRing T] [Algebra k T] [Algebra.FiniteType k T] [Nontrivial T] :
    ∃ (d : ℕ) (ψ : MvPolynomial (Fin d) k →ₐ[k] T),
      (d : WithBot ℕ∞) = ringKrullDim T ∧
      Function.Injective ψ ∧ ψ.toRingHom.Finite := by
  obtain ⟨ι, x, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial' (R := k) (S := T)).mp ‹_›
  let n := Fintype.card ι
  let renE := MvPolynomial.renameEquiv k (Fintype.equivFin ι)
  let F : MvPolynomial (Fin n) k →ₐ[k] T := f.comp renE.symm.toAlgHom
  have hF : Function.Surjective F := hf.comp renE.symm.surjective
  let I : Ideal (MvPolynomial (Fin n) k) := RingHom.ker F
  let e : (MvPolynomial (Fin n) k ⧸ I) ≃ₐ[k] T := Ideal.quotientKerAlgEquivOfSurjective hF
  have hI : I ≠ ⊤ := by
    intro h
    have : Subsingleton (MvPolynomial (Fin n) k ⧸ I) := by rw [h]; infer_instance
    exact (not_subsingleton T) (e.symm.injective.subsingleton)
  obtain ⟨s, hsn, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_quotient I hI
  let ψ : MvPolynomial (Fin s) k →ₐ[k] T := e.toAlgHom.comp g
  have hψinj : Function.Injective ψ := e.injective.comp hginj
  have hψint : ψ.toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans g.toRingHom e.toAlgHom.toRingHom hgint
      (RingHom.isIntegral_of_surjective _ e.surjective)
  refine ⟨s, ψ, ?_, hψinj, ?_⟩
  · rw [← ringKrullDim_eq_of_injective_isIntegral ψ.toRingHom hψinj hψint,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k]
    simp
  · let : Algebra (MvPolynomial (Fin s) k) T := ψ.toRingHom.toAlgebra
    have : IsScalarTower k (MvPolynomial (Fin s) k) T :=
      .of_algebraMap_eq fun r => (ψ.commutes r).symm
    have : Algebra.IsIntegral (MvPolynomial (Fin s) k) T := ⟨hψint⟩
    have : Algebra.FiniteType (MvPolynomial (Fin s) k) T :=
      Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin s) k) T
    change Module.Finite (MvPolynomial (Fin s) k) T
    exact Algebra.IsIntegral.finite

/-- The local dimension at a prime is attained: for a finite type `k`-algebra `S` and a
prime ideal `q` there exists `g ∉ q` with
`ringKrullDim (Localization.Away g) = localDimAtPrime k q`. -/
theorem localDimAtPrime_attained
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) [q.IsPrime] :
    ∃ g ∉ q, ringKrullDim (Localization.Away g) = localDimAtPrime k q := by
  have : Nonempty (qᶜ : Set S) := ⟨⟨1, q.one_notMem⟩⟩
  have heq : localDimAtPrime k q
      = sInf (Set.range (fun x : (qᶜ : Set S) => ringKrullDim (Localization.Away (x:S)))) := by
    rw [sInf_range]
    unfold localDimAtPrime
    rw [iInf_subtype']
  obtain ⟨x, hx⟩ := csInf_mem (Set.range_nonempty
    fun x : (qᶜ : Set S) => ringKrullDim (Localization.Away (x : S)))
  refine ⟨x, x.property, ?_⟩
  rw [heq, ← hx]

/-- Noether normalization at a point: for a field `k`, a finite type `k`-algebra `S`, and a
prime ideal `q` of `S` corresponding to a point `x` of `X = Spec(S)`, there exist an element
`g ∉ q`, a natural number `d`, and a `k`-algebra homomorphism `ψ : k[y_1, …, y_d] → S_g`, where
`k[y_1, …, y_d] = MvPolynomial (Fin d) k`, such that `d = dim(S_g) = localDimAtPrime k q` and
`ψ` is injective and finite. Here `localDimAtPrime k q` is the minimum of `dim(S_g)` over `g ∉ q`;
Stacks 00OZ itself, with the topological local dimension `dim_x(X)` of 0055 (4), is
`noether_normalization_at_point_topologicalKrullDimAt`, deduced from this one. -/
theorem noether_normalization_at_point
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) [q.IsPrime] :
    ∃ (g : S) (_ : g ∉ q) (d : ℕ)
      (ψ : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g),
      (d : WithBot ℕ∞) = ringKrullDim (Localization.Away g) ∧
      (d : WithBot ℕ∞) = localDimAtPrime k q ∧
      Function.Injective ψ ∧
      ψ.toRingHom.Finite := by
  obtain ⟨g, hg, hdim⟩ := localDimAtPrime_attained (k := k) q
  have : Nontrivial (Localization.Away g) :=
    (IsLocalization.Away.lift g (S := Localization.Away g)
      (IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q)
        ⟨g, hg⟩)).domain_nontrivial
  obtain ⟨d, ψ, hd, hinj, hfin⟩ :=
    noether_normalization_global (k := k) (T := Localization.Away g)
  exact ⟨g, hg, d, ψ, hd, hd.trans hdim, hinj, hfin⟩

/-!
# Separating a finite set of multi-indices by a dot product

Stacks tag 051M (Lemma 10.115.1). Fix `n : ℕ` and work with multi-indices, elements of
`ℕ^n` modelled as functions `Fin n → ℕ`, so that `ν = (ν_1, …, ν_n)`; the index
`i : Fin n` stands for the Stacks index `i + 1`. The dot product of exponent vectors
`e = (e_1, …, e_n)` and `ν = (ν_1, …, ν_n)` is `e · ν = ∑_{i=1}^{n} e_i ν_i ∈ ℕ`.

The result: for a finite set `N ⊆ ℕ^n` of multi-indices and all exponents with
`e_1 ≫ e_2 ≫ ⋯ ≫ e_{n-1} ≫ e_n` we have `e · ν = e · ν' ↔ ν = ν'` for all `ν, ν' ∈ N`.

The informal notation `e_1 ≫ e_2 ≫ ⋯ ≫ e_n` is a nested "for all sufficiently large"
quantifier: for all sufficiently large `e_n`, for all `e_{n-1}` sufficiently large in terms
of `e_n`, …, for all `e_1` sufficiently large in terms of `e_2, …, e_n`. This is the
predicate `EventuallyRapidlyDecreasing`, and the lemma is
`eventuallyRapidlyDecreasing_dotProduct_eq_iff`. In fact `e_n` may be any positive
integer (`eventuallyRapidlyDecreasing_snoc_dotProduct_eq_iff`); the bound on `e_{i-1}` is
`e_{i-1} > A_i e_i + ⋯ + A_n e_n` with `A_i` the largest `i`-th coordinate in `N`.
Finiteness of `N` is essential, since it is what bounds the `A_i`; nonemptiness is not
needed. All quantities are natural numbers.

The weaker statement that some single tuple `e` separates `N`, for instance
`e_i = M^{n-i}` with `M` larger than every coordinate, is
`exists_separating_exponents`.
-/

@[expose] public section

/-- Base-`M` digit vectors are determined by `∑ i, M ^ i * g i` when all digits are `< M`. -/
private theorem eq_of_sum_pow_mul_eq {M m : ℕ} {g h : Fin m → ℕ} (hg : ∀ i, g i < M)
    (hh : ∀ i, h i < M)
    (hsum : ∑ i : Fin m, M ^ (i : ℕ) * g i = ∑ i : Fin m, M ^ (i : ℕ) * h i) : g = h := by
  have := (finFunctionFinEquiv (m := M) (n := m)).injective
    (a₁ := fun i => ⟨g i, hg i⟩) (a₂ := fun i => ⟨h i, hh i⟩)
    (Fin.ext (by simpa [finFunctionFinEquiv_apply, mul_comm] using hsum))
  funext i
  simpa using congrArg (fun f => (f i : ℕ)) this

/-- `EventuallyRapidlyDecreasing n P` says that `P e` holds for all exponent vectors
`e = (e_1, …, e_n) : Fin n → ℕ` with `e_1 ≫ e_2 ≫ ⋯ ≫ e_n`, in the nested sense: for all
sufficiently large `e_n`, for all `e_{n-1}` sufficiently large in terms of `e_n`, …, for all
`e_1` sufficiently large in terms of `e_2, …, e_n`. Here `e 0` is `e_1` and `e (Fin.last _)`
is `e_n`; the last coordinate is quantified outermost. -/
def EventuallyRapidlyDecreasing : (n : ℕ) → ((Fin n → ℕ) → Prop) → Prop
  | 0, P => P Fin.elim0
  | n + 1, P => ∀ᶠ a in Filter.atTop, EventuallyRapidlyDecreasing n fun e => P (Fin.snoc e a)

/-- `EventuallyRapidlyDecreasing n` is monotone in the predicate. -/
theorem EventuallyRapidlyDecreasing.mono {n : ℕ} {P Q : (Fin n → ℕ) → Prop}
    (h : EventuallyRapidlyDecreasing n P) (hPQ : ∀ e, P e → Q e) :
    EventuallyRapidlyDecreasing n Q := by
  induction n with
  | zero => exact hPQ _ h
  | succ n ih =>
    rw [EventuallyRapidlyDecreasing] at h ⊢
    exact Filter.Eventually.mono h fun a ha => ih ha fun e => hPQ _

/-- A predicate holding for `e_1 ≫ ⋯ ≫ e_n` holds for some exponent vector. -/
theorem EventuallyRapidlyDecreasing.exists {n : ℕ} {P : (Fin n → ℕ) → Prop}
    (h : EventuallyRapidlyDecreasing n P) : ∃ e, P e := by
  induction n with
  | zero => exact ⟨_, h⟩
  | succ n ih =>
    rw [EventuallyRapidlyDecreasing] at h
    obtain ⟨a, ha⟩ := h.exists
    obtain ⟨e, he⟩ := ih ha
    exact ⟨_, he⟩

/-- Stacks 051M with an arbitrary positive last exponent: for a finite set `N` of
multi-indices in `ℕ^{n+1}` and any `c > 0`, for `e_1 ≫ ⋯ ≫ e_n ≫ e_{n+1} = c` the dot
product with `e = (e_1, …, e_n, c)` separates `N`. -/
@[stacks 051M "the last exponent `e_n` may be any positive integer; `N` need not be \
nonempty"]
theorem eventuallyRapidlyDecreasing_snoc_dotProduct_eq_iff {n : ℕ}
    (N : Finset (Fin (n + 1) → ℕ)) {c : ℕ} (hc : 0 < c) :
    EventuallyRapidlyDecreasing n fun e => ∀ ν ∈ N, ∀ ν' ∈ N,
      ((Fin.snoc e c : Fin (n + 1) → ℕ) ⬝ᵥ ν = (Fin.snoc e c : Fin (n + 1) → ℕ) ⬝ᵥ ν' ↔
        ν = ν') := by
  induction n generalizing c with
  | zero =>
    intro ν _ ν' _
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    simp only [dotProduct, Fin.sum_univ_castSucc, Finset.univ_eq_empty, Finset.sum_empty,
      Fin.snoc_last, zero_add] at h
    funext i
    obtain rfl : i = Fin.last 0 := Subsingleton.elim (α := Fin 1) _ _
    exact Nat.eq_of_mul_eq_mul_left hc h
  | succ n ih =>
    rw [EventuallyRapidlyDecreasing]
    filter_upwards [Filter.eventually_gt_atTop (c * N.sup fun ν => ν (Fin.last (n + 1)))]
      with a ha
    have hlt : ∀ ν ∈ N, c * ν (Fin.last (n + 1)) < a := fun ν hν =>
      (Nat.mul_le_mul_left c (Finset.le_sup (f := fun ν => ν (Fin.last (n + 1))) hν)).trans_lt
        ha
    let φ : (Fin (n + 2) → ℕ) → Fin (n + 1) → ℕ := fun ν =>
      Fin.snoc (Fin.init (Fin.init ν)) (a * Fin.init ν (Fin.last n) + c * ν (Fin.last (n + 1)))
    have hφ : ∀ (e : Fin n → ℕ) (ν : Fin (n + 2) → ℕ),
        (Fin.snoc (Fin.snoc e a : Fin (n + 1) → ℕ) c : Fin (n + 2) → ℕ) ⬝ᵥ ν =
          (Fin.snoc e 1 : Fin (n + 1) → ℕ) ⬝ᵥ φ ν := by
      intro e ν
      simp only [φ, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.init]
      ring
    have hinj : ∀ ν ∈ N, ∀ ν' ∈ N, φ ν = φ ν' → ν = ν' := by
      intro ν hν ν' hν' h
      have hinit : Fin.init (Fin.init ν) = Fin.init (Fin.init ν') := by
        simpa [φ] using congrArg Fin.init h
      have hlast : a * Fin.init ν (Fin.last n) + c * ν (Fin.last (n + 1)) =
          a * Fin.init ν' (Fin.last n) + c * ν' (Fin.last (n + 1)) := by
        simpa [φ] using congrFun h (Fin.last n)
      have ha0 : 0 < a := (Nat.zero_le _).trans_lt (hlt ν hν)
      have hdiv : ∀ x y : ℕ, y < a → (a * x + y) / a = x := fun x y hy => by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ ha0, Nat.div_eq_of_lt hy, zero_add]
      have hx : Fin.init ν (Fin.last n) = Fin.init ν' (Fin.last n) := by
        have := congrArg (· / a) hlast
        simpa only [hdiv _ _ (hlt ν hν), hdiv _ _ (hlt ν' hν')] using this
      rw [hx] at hlast
      have hy := Nat.eq_of_mul_eq_mul_left hc (Nat.add_left_cancel hlast)
      funext i
      induction i using Fin.lastCases with
      | last => exact hy
      | cast j =>
        induction j using Fin.lastCases with
        | last => exact hx
        | cast k => exact congrFun hinit k
    refine (ih (N.image φ) one_pos).mono fun e he ν hν ν' hν' => ?_
    rw [hφ, hφ]
    exact (he _ (Finset.mem_image_of_mem φ hν) _ (Finset.mem_image_of_mem φ hν')).trans
      ⟨hinj ν hν ν' hν', fun h => h ▸ rfl⟩

/-- Stacks 051M: for a finite set `N` of multi-indices in `ℕ^n`, for all exponent vectors
`e = (e_1, …, e_n)` with `e_1 ≫ e_2 ≫ ⋯ ≫ e_n` (in the nested sense of
`EventuallyRapidlyDecreasing`) we have `e · ν = e · ν' ↔ ν = ν'` for all `ν, ν' ∈ N`. -/
@[stacks 051M "nested quantifier `e_1 ≫ ⋯ ≫ e_n` as `EventuallyRapidlyDecreasing`; `N` \
need not be nonempty"]
theorem eventuallyRapidlyDecreasing_dotProduct_eq_iff {n : ℕ} (N : Finset (Fin n → ℕ)) :
    EventuallyRapidlyDecreasing n fun e => ∀ ν ∈ N, ∀ ν' ∈ N, (e ⬝ᵥ ν = e ⬝ᵥ ν' ↔ ν = ν') := by
  cases n with
  | zero =>
    intro ν _ ν' _
    exact ⟨fun _ => funext fun i => i.elim0, fun h => h ▸ rfl⟩
  | succ n =>
    rw [EventuallyRapidlyDecreasing]
    filter_upwards [Filter.eventually_gt_atTop 0] with c hc
    exact eventuallyRapidlyDecreasing_snoc_dotProduct_eq_iff N hc

/-- For a finite set `N ⊆ ℕ^n`, there is an exponent tuple `e ∈ ℕ^n` such that
`e · ν = e · ν' ↔ ν = ν'` for all `ν, ν' ∈ N`, for instance `e_i = M^i` with `M` larger than
every coordinate. This only asserts that one separating tuple exists; Stacks 051M asserts
that every tuple with `e_1 ≫ ⋯ ≫ e_n` separates `N`, which is
`eventuallyRapidlyDecreasing_dotProduct_eq_iff`. -/
theorem exists_separating_exponents {n : ℕ} (N : Finset (Fin n → ℕ)) :
    ∃ e : Fin n → ℕ, ∀ ν ∈ N, ∀ ν' ∈ N, (e ⬝ᵥ ν = e ⬝ᵥ ν' ↔ ν = ν') := by
  set M : ℕ := N.sup Finset.univ.sup + 1
  have hbound : ∀ ν ∈ N, ∀ i, ν i < M := fun ν hν i =>
    Nat.lt_succ_of_le <| (Finset.le_sup (Finset.mem_univ i)).trans <|
      Finset.le_sup (f := Finset.univ.sup) hν
  refine ⟨fun i => M ^ (i : ℕ), fun ν hν ν' hν' => ⟨fun h => ?_, fun h => h ▸ rfl⟩⟩
  exact eq_of_sum_pow_mul_eq (hbound ν hν) (hbound ν' hν') h

/-- Equivalent formulation: there exists `e ∈ ℕ^n` such that the map `ν ↦ e · ν` is
injective on `N`. -/
theorem exists_separating_exponents_injOn {n : ℕ} (N : Finset (Fin n → ℕ)) :
    ∃ e : Fin n → ℕ, Set.InjOn (e ⬝ᵥ ·) (N : Set (Fin n → ℕ)) :=
  let ⟨e, he⟩ := exists_separating_exponents N
  ⟨e, fun ν hν ν' hν' h => (he ν hν ν' hν').mp h⟩

/-!
# Tilting a nonconstant polynomial to have constant leading coefficient

Stacks tag 051N (Lemma 10.115.2).

Let `R` be a commutative ring and `n ≥ 1`. Working in the polynomial ring
`R[x_1, …, x_n]`, distinguish the variable `x_n`. Given a nonconstant polynomial
`g`, for all exponents `e_1 ≫ e_2 ≫ ⋯ ≫ e_{n-1} ≫ e_n = 1` the tilting
substitution `Φ_e : x_i ↦ x_i + x_n^(e_i)` for `i < n` and `x_n ↦ x_n` makes
`Φ_e(g)`, viewed as a polynomial in `x_n` over `S = R[x_1, …, x_{n-1}]`, have a
*constant* leading coefficient `a ∈ R`, one of the nonzero coefficients of `g`,
and positive degree. The nested quantifier `≫` is `EventuallyRapid`, and the
statement is `eventuallyRapid_subst_constant_leadingCoeff_of_nonconstant`.

## Indexing convention

The informal statement uses `n ≥ 1` variables `x_1, …, x_n` with `x_n`
distinguished. Here this is `MvPolynomial (Fin (n+1)) R` for `n : ℕ`, so that
the number of variables is `n + 1 ≥ 1`, and the variable of index `0` plays the
role of the distinguished variable `x_n`, while the remaining indices `1, …, n`
play the role of `x_{n-1}, …, x_1` (index `i` stands for `x_{n-i}`, so larger
indices carry the faster growing exponents).

This aligns with `MvPolynomial.finSuccEquiv`, the isomorphism
`R[X_0, X_1, …, X_n] ≃ (R[X_1, …, X_n])[X_0]`, which views a multivariate
polynomial as a univariate polynomial in `X 0` with coefficients in the
remaining variables. So `S = MvPolynomial (Fin n) R` plays the role of
`S = R[x_1, …, x_{n-1}]`, the distinguished variable `X 0` plays the role of
`x_n`, and `e 0 = 1` encodes `e_n = 1`.
-/

@[expose] public section

open MvPolynomial Polynomial

variable {R : Type*} [CommRing R]

/-- The substitution `Φ_e`.

The $R$-algebra endomorphism of `MvPolynomial (Fin (n+1)) R` determined by
fixing the distinguished variable `X 0` (the role of $x_n$) and sending every
other variable `X i` to `X i + (X 0)^(e i)` (the role of
$x_i \mapsto x_i + x_n^{e_i}$).

`e : Fin (n+1) → ℕ` collects the exponents; only the values `e i` for `i ≠ 0`
are used by the substitution, and we fix `e 0 = 1` in the statement to encode
`e_n = 1`. -/
noncomputable def subst (n : ℕ) (e : Fin (n + 1) → ℕ) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval (fun i => if i = 0 then (X 0 : MvPolynomial (Fin (n + 1)) R)
                  else X i + (X 0) ^ (e i))

/-- `subst` fixes the distinguished variable `X 0` (i.e. $\Phi_e(x_n) = x_n$). -/
theorem subst_X_zero (n : ℕ) (e : Fin (n + 1) → ℕ) :
    subst n e (X 0 : MvPolynomial (Fin (n + 1)) R) = X 0 := by
  simp [subst]

/-- `subst` sends every non-distinguished variable `X i` to `X i + (X 0)^(e i)`
(i.e. $\Phi_e(x_i) = x_i + x_n^{e_i}$ for $i < n$). -/
theorem subst_X_ne_zero (n : ℕ) (e : Fin (n + 1) → ℕ) (i : Fin (n + 1))
    (hi : i ≠ 0) :
    subst n e (X i : MvPolynomial (Fin (n + 1)) R) = X i + (X 0) ^ (e i) := by
  simp [subst, hi]

/-- Base-`M` representations are unique: if all coordinates of `g` and `h` are `< M` and
`∑ i, M ^ i * g i = ∑ i, M ^ i * h i`, then `g = h`. -/
theorem base_repr_injective (M : ℕ) :
    ∀ (m : ℕ) (g h : Fin m → ℕ),
      (∀ i, g i < M) → (∀ i, h i < M) →
      (∑ i : Fin m, M ^ (i : ℕ) * g i = ∑ i : Fin m, M ^ (i : ℕ) * h i) → g = h :=
  fun _ _ _ hg hh hsum => eq_of_sum_pow_mul_eq hg hh hsum

/-- An existential consequence of Stacks tag 051M (Lemma 10.115.1), normalized: for a finite
set `N` of multi-indices in `Fin (m+1) →₀ ℕ` there exist exponents `e i ≥ 1` with `e 0 = 1`
such that the linear form `ν ↦ ∑ i, e i * ν i` is injective on `N`. Only one such tuple is
asserted to exist (namely `e i = M ^ i`); the full Stacks statement, that every tuple with
`e_1 ≫ ⋯ ≫ e_n` works, is `eventuallyRapidlyDecreasing_dotProduct_eq_iff`. -/
theorem supporting_lemma_normalized (m : ℕ) (N : Finset (Fin (m + 1) →₀ ℕ)) :
    ∃ e : Fin (m + 1) → ℕ, e 0 = 1 ∧ (∀ i, 1 ≤ e i) ∧
      ∀ ν ∈ N, ∀ ν' ∈ N,
        (∑ i, e i * ν i = ∑ i, e i * ν' i) ↔ ν = ν' := by
  set M := (N.sup fun ν => ∑ i, ν i) + 1
  have hM1 : 1 ≤ M := Nat.le_add_left 1 _
  have hbound : ∀ ν ∈ N, ∀ i : Fin (m + 1), (ν i) < M := by
    intro ν hν i
    have h1 : ν i ≤ ∑ j, ν j :=
      Finset.single_le_sum (f := ν) (by intro j _; exact Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : (∑ j, ν j) ≤ N.sup fun ν => ∑ i, ν i :=
      Finset.le_sup (f := fun ν => ∑ i, ν i) hν
    lia
  refine ⟨fun i => M ^ (i : ℕ), by simp, fun i => Nat.one_le_pow _ _ (by lia), ?_⟩
  exact fun ν hν ν' hν' => ⟨fun hsum => Finsupp.ext <| congrFun <|
    base_repr_injective M (m + 1) ν ν' (hbound ν hν) (hbound ν' hν') hsum, fun h => h ▸ rfl⟩

/-!
### Ingredients

The notation used throughout is:

* `Ψ` is the composite algebra hom `(finSuccEquiv R n) ∘ (subst n e)`, from
  `MvPolynomial (Fin (n+1)) R` to `(MvPolynomial (Fin n) R)[X]`.
* `D ν = ∑ i, e i * ν i` is the tilted degree of a multi-index.
* `P ν = ∏ i, (Ψ (X i)) ^ (ν i)` is the image of the variable part of the
  monomial `X^ν`; it is monic of degree `D ν`.
-/

/-- The image of a monomial under an `R`-algebra hom
`Ψ : R[X_0, …, X_n] →ₐ[R] (R[X_1, …, X_n])[X]`:
`Ψ (monomial ν c) = C (C c) * ∏ i, (Ψ (X i))^(ν i)`. -/
theorem psi_monomial {n : ℕ}
    (Ψ : MvPolynomial (Fin (n + 1)) R →ₐ[R] Polynomial (MvPolynomial (Fin n) R))
    (ν : Fin (n + 1) →₀ ℕ) (c : R) :
    Ψ (MvPolynomial.monomial ν c)
      = Polynomial.C (MvPolynomial.C c) * ∏ i, (Ψ (X i)) ^ (ν i) := by
  have hC : Ψ (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
    simpa only [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply] using Ψ.commutes c
  rw [MvPolynomial.monomial_eq, map_mul, hC]
  congr 1
  rw [Finsupp.prod, map_prod]
  simp only [map_pow]
  rw [← Finsupp.prod_fintype (f := ν) (g := fun i e => Ψ (X i) ^ e)
      (fun i => by simp)]
  rfl

/-- The degree and leading coefficient of a sum dominated by a single term.

Let `s` be a finite set, `cν : ι → S` and `Q : ι → Polynomial S` with each
`Q i` monic of degree `δ i`.  If a distinguished index `i₀ ∈ s` strictly
dominates: `cν i₀ ≠ 0` and `∀ i ∈ s, i ≠ i₀ → δ i < δ i₀` (and lower terms have
`natDegree (C (cν i) * Q i) ≤ δ i < δ i₀`), then the sum
`∑ i ∈ s, C (cν i) * Q i` has `natDegree = δ i₀` and `leadingCoeff = cν i₀`. -/
theorem natDegree_leadingCoeff_dominant_sum {S : Type*} [CommRing S]
    {ι : Type*} (s : Finset ι) (cν : ι → S) (Q : ι → Polynomial S) (δ : ι → ℕ)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (hmonic : ∀ i, (Q i).Monic)
    (hdeg : ∀ i, (Q i).natDegree = δ i) (hc0 : cν i₀ ≠ 0)
    (hdom : ∀ i ∈ s, i ≠ i₀ → δ i < δ i₀) :
    (∑ i ∈ s, Polynomial.C (cν i) * Q i).natDegree = δ i₀ ∧
    (∑ i ∈ s, Polynomial.C (cν i) * Q i).leadingCoeff = cν i₀ := by
  classical
  set f : ι → Polynomial S := fun i => Polynomial.C (cν i) * Q i with hf
  rw [← Finset.add_sum_erase s f hi₀]
  set rest := ∑ i ∈ s.erase i₀, f i with hrest
  have hQ0 : (Q i₀).leadingCoeff = 1 := (hmonic i₀).leadingCoeff
  have hmulne : cν i₀ * (Q i₀).leadingCoeff ≠ 0 := by
    rwa [hQ0, mul_one]
  have hlcf0 : (f i₀).leadingCoeff = cν i₀ := by
    simp only [hf]
    exact (hmonic i₀).leadingCoeff_C_mul (cν i₀)
  have hf0ne : f i₀ ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hlcf0
    exact hc0 hlcf0.symm
  have hndegf0 : (f i₀).natDegree = δ i₀ := by
    simp only [hf]
    rw [Polynomial.natDegree_C_mul_of_mul_ne_zero hmulne, hdeg i₀]
  have hdegf0 : (f i₀).degree = (δ i₀ : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hf0ne, hndegf0]
  have hrestdeg : rest.degree < (δ i₀ : WithBot ℕ) := by
    rw [hrest]
    apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (δ i₀))]
    intro i hi
    have hlt : δ i < δ i₀ :=
      hdom i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
    have hdle : (f i).degree ≤ ((δ i : ℕ) : WithBot ℕ) := by
      have h1 : (f i).degree ≤ (Q i).degree := by
        simp only [hf]
        refine le_trans (Polynomial.degree_mul_le _ _) ?_
        have h2 : (Polynomial.C (cν i)).degree + (Q i).degree
            ≤ (0 : WithBot ℕ) + (Q i).degree := by
          gcongr
          exact Polynomial.degree_C_le
        rwa [zero_add] at h2
      refine le_trans h1 ?_
      rw [← hdeg i]
      exact Polynomial.degree_le_natDegree
    refine lt_of_le_of_lt hdle ?_
    exact_mod_cast hlt
  have hcmp : rest.degree < (f i₀).degree := by rwa [hdegf0]
  refine ⟨?_, ?_⟩
  · rw [add_comm, Polynomial.natDegree_add_eq_right_of_degree_lt hcmp, hndegf0]
  · rw [add_comm, Polynomial.leadingCoeff_add_of_degree_lt hcmp, hlcf0]

/-- Positivity of the tilted degree of a nonzero multi-index: if `e i ≥ 1` for
all `i` and `ν ≠ 0`, then `0 < ∑ i, e i * ν i`. -/
theorem tilted_degree_pos {n : ℕ} (e : Fin (n + 1) → ℕ) (ν : Fin (n + 1) →₀ ℕ)
    (he : ∀ i, 1 ≤ e i) (hν : ν ≠ 0) :
    0 < ∑ i, e i * ν i := by
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hν
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
  calc 0 < 1 := Nat.one_pos
    _ ≤ e j * ν j := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp (he j)) hj)
    _ ≤ ∑ i, e i * ν i :=
        Finset.single_le_sum (f := fun i => e i * ν i) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ j)

/-- The tilting computation for one admissible exponent vector. Let `g` be a nonconstant
polynomial in `MvPolynomial (Fin (n+1)) R` and let `e` be exponents with `e 0 = 1`, every
`e i ≥ 1`, and such that `ν ↦ ∑ i, e i * ν i` is injective on the support of `g`. Then
`finSuccEquiv R n (subst n e g)`, viewed as a polynomial in `X 0`, has positive degree `d`
and leading coefficient `MvPolynomial.C a` for a nonzero coefficient `a` of `g`. -/
theorem exists_natDegree_leadingCoeff_subst_of_injOn
    (n : ℕ) (g : MvPolynomial (Fin (n + 1)) R)
    (hg : ¬ ∃ r : R, g = MvPolynomial.C r) (e : Fin (n + 1) → ℕ) (he0 : e 0 = 1)
    (he1 : ∀ i, 1 ≤ e i)
    (hinj : ∀ ν ∈ g.support, ∀ ν' ∈ g.support,
      (∑ i, e i * ν i = ∑ i, e i * ν' i) ↔ ν = ν') :
    ∃ (d : ℕ) (a : R),
      (∃ ν ∈ g.support, a = g.coeff ν) ∧
      0 < d ∧
      (finSuccEquiv R n (subst n e g)).natDegree = d ∧
      (finSuccEquiv R n (subst n e g)).leadingCoeff = MvPolynomial.C a := by
  classical
  have hg0 : g ≠ 0 := by
    rintro rfl; exact hg ⟨0, by simp⟩
  have hntR : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hg ⟨0, Subsingleton.elim _ _⟩
  have hsupp : g.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hg0 (MvPolynomial.support_eq_empty.mp h)
  set D : (Fin (n + 1) →₀ ℕ) → ℕ := fun ν => ∑ i, e i * ν i with hD
  set Ψ : MvPolynomial (Fin (n + 1)) R →ₐ[R]
      Polynomial (MvPolynomial (Fin n) R) :=
    (finSuccEquiv R n).toAlgHom.comp (subst n e) with hΨ
  have hΨX0 : Ψ (X 0) = Polynomial.X := by
    change (finSuccEquiv R n) (subst n e (X 0 : MvPolynomial (Fin (n + 1)) R))
        = Polynomial.X
    rw [subst_X_zero]
    exact finSuccEquiv_X_zero
  have hΨXsucc : ∀ j : Fin n,
      Ψ (X j.succ) = Polynomial.C (MvPolynomial.X j) + Polynomial.X ^ (e j.succ) := by
    intro j
    have hne : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
    change (finSuccEquiv R n) (subst n e (X j.succ))
        = Polynomial.C (MvPolynomial.X j) + Polynomial.X ^ (e j.succ)
    rw [subst_X_ne_zero n e j.succ hne, map_add, map_pow,
      finSuccEquiv_X_succ, finSuccEquiv_X_zero]
  have hΨX_monic_deg : ∀ i : Fin (n + 1),
      (Ψ (X i)).Monic ∧ (Ψ (X i)).natDegree = e i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [hΨX0, he0]
      exact ⟨monic_X, natDegree_X⟩
    · intro j
      rw [hΨXsucc j]
      have hej : 1 ≤ e j.succ := he1 j.succ
      have hmonicXpow : (Polynomial.X ^ (e j.succ) :
          Polynomial (MvPolynomial (Fin n) R)).Monic := monic_X_pow _
      have hdegC : (Polynomial.C (MvPolynomial.X j) :
          Polynomial (MvPolynomial (Fin n) R)).degree <
          (Polynomial.X ^ (e j.succ) : Polynomial (MvPolynomial (Fin n) R)).degree := by
        refine lt_of_le_of_lt Polynomial.degree_C_le ?_
        rw [Polynomial.degree_X_pow]
        exact_mod_cast Nat.pos_of_ne_zero (by lia)
      have hmonic : (Polynomial.C (MvPolynomial.X j) +
          Polynomial.X ^ (e j.succ) : Polynomial (MvPolynomial (Fin n) R)).Monic := by
        rw [add_comm]; exact hmonicXpow.add_of_left hdegC
      refine ⟨hmonic, ?_⟩
      rw [add_comm, Polynomial.natDegree_add_eq_left_of_degree_lt hdegC, natDegree_X_pow]
  have hΨX_monic : ∀ i : Fin (n + 1), (Ψ (X i)).Monic := fun i => (hΨX_monic_deg i).left
  have hΨX_deg : ∀ i : Fin (n + 1), (Ψ (X i)).natDegree = e i :=
    fun i => (hΨX_monic_deg i).right
  set P : (Fin (n + 1) →₀ ℕ) → Polynomial (MvPolynomial (Fin n) R) :=
    fun ν => ∏ i, (Ψ (X i)) ^ (ν i) with hP
  have hP_monic : ∀ ν, (P ν).Monic := fun ν =>
    monic_prod_of_monic _ _ fun i _ => (hΨX_monic i).pow _
  have hP_deg : ∀ ν, (P ν).natDegree = D ν := by
    intro ν
    rw [hP]
    rw [natDegree_prod_of_monic _ _ fun i _ => (hΨX_monic i).pow _, hD]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hΨX_monic i).natDegree_pow, hΨX_deg i]; ring
  have hΨg : Ψ g = ∑ ν ∈ g.support,
      Polynomial.C (MvPolynomial.C (g.coeff ν)) * P ν := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [psi_monomial Ψ ν (g.coeff ν)]
  obtain ⟨νs, hνs_mem, hνs_max⟩ :=
    g.support.exists_max_image D hsupp
  have hdom : ∀ ν ∈ g.support, ν ≠ νs → D ν < D νs := fun ν hν hne =>
    (hνs_max ν hν).lt_of_ne fun h => hne ((hinj ν hν νs hνs_mem).mp h)
  set a : R := g.coeff νs with ha
  have ha0 : a ≠ 0 := MvPolynomial.mem_support_iff.mp hνs_mem
  set d : ℕ := D νs with hd
  have hmain : (Ψ g).natDegree = d ∧ (Ψ g).leadingCoeff = MvPolynomial.C a := by
    rw [hΨg]
    have hCne : (MvPolynomial.C a : MvPolynomial (Fin n) R) ≠ 0 := by
      simpa [MvPolynomial.C_eq_zero] using ha0
    have := natDegree_leadingCoeff_dominant_sum g.support
      (fun ν => MvPolynomial.C (g.coeff ν)) P D νs hνs_mem hP_monic hP_deg hCne hdom
    simpa [ha, hd] using this
  refine ⟨d, a, ⟨νs, hνs_mem, rfl⟩, ?_, ?_, ?_⟩
  · obtain ⟨ν₀, hν₀_mem, hν₀_ne⟩ : ∃ ν ∈ g.support, ν ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_ne_iff] at hcon
      apply hg
      refine ⟨g.coeff 0, ?_⟩
      ext ν
      rw [MvPolynomial.coeff_C]
      by_cases hν : ν = 0
      · simp [hν]
      · rw [ite_eq_right (Ne.symm hν)]
        by_contra hc
        exact hν (hcon ν (MvPolynomial.mem_support_iff.mpr hc))
    have hpos : 0 < D ν₀ := tilted_degree_pos e ν₀ he1 hν₀_ne
    have : D ν₀ ≤ D νs := hνs_max ν₀ hν₀_mem
    rw [hd]; lia
  · exact hmain.left
  · exact hmain.right

/-- Let `g` be a nonconstant polynomial in `MvPolynomial (Fin (n+1)) R`, that is one
not in the image of the constant inclusion `MvPolynomial.C : R → …`. Then there
exist exponents `e` with `e 0 = 1`, encoding `e_n = 1`, a positive integer `d`,
and an element `a ∈ R` such that:

1. `a` is one of the nonzero coefficients of `g`: there is a multi-index `ν` in
   the support of `g` with `a = g.coeff ν`, so in particular `a ≠ 0`.

2. Viewing `f = subst n e g` as a polynomial in the distinguished variable `X 0`
   via `finSuccEquiv R n`, its degree in that variable is `d` and its leading
   coefficient is the *constant* `MvPolynomial.C a`, the image of `a ∈ R` inside
   `S = MvPolynomial (Fin n) R`.

This is the existential consequence of Stacks 051N, which asserts the conclusion for all
sufficiently rapidly growing exponents; that full statement is
`eventuallyRapid_subst_constant_leadingCoeff_of_nonconstant`. -/
theorem exists_substitution_with_constant_leadingCoeff_of_nonconstant
    (n : ℕ) (g : MvPolynomial (Fin (n + 1)) R)
    (hg : ¬ ∃ r : R, g = MvPolynomial.C r) :
    ∃ (e : Fin (n + 1) → ℕ) (d : ℕ) (a : R),
      e 0 = 1 ∧
      (∃ ν ∈ g.support, a = g.coeff ν) ∧
      0 < d ∧
      (finSuccEquiv R n (subst n e g)).natDegree = d ∧
      (finSuccEquiv R n (subst n e g)).leadingCoeff = MvPolynomial.C a := by
  obtain ⟨e, he0, he1, hinj⟩ := supporting_lemma_normalized n g.support
  obtain ⟨d, a, h⟩ := exists_natDegree_leadingCoeff_subst_of_injOn n g hg e he0 he1 hinj
  exact ⟨e, d, a, he0, h⟩

/-- `EventuallyRapid k P` says that `P e` holds for all `e = (e_0, …, e_{k-1}) ∈ ℕ^k` with
`e_{k-1} ≫ e_{k-2} ≫ ⋯ ≫ e_0`, in the nested sense of the Stacks notation `≫`: for all
sufficiently large `e_0`, for all `e_1` sufficiently large depending on `e_0`, …, for all
`e_{k-1}` sufficiently large depending on `e_0, …, e_{k-2}`, the property `P e` holds.
Concretely `EventuallyRapid 0 P` is `P` of the empty tuple and `EventuallyRapid (k+1) P` is
`EventuallyRapid k (fun f => ∀ᶠ a in atTop, P (Fin.snoc f a))`. -/
def EventuallyRapid : (k : ℕ) → ((Fin k → ℕ) → Prop) → Prop
  | 0, P => P Fin.elim0
  | k + 1, P => EventuallyRapid k fun f => ∀ᶠ a in Filter.atTop, P (Fin.snoc f a : Fin (k + 1) → ℕ)

theorem EventuallyRapid.mono {k : ℕ} {P Q : (Fin k → ℕ) → Prop} (h : EventuallyRapid k P)
    (hPQ : ∀ f, P f → Q f) : EventuallyRapid k Q := by
  induction k with
  | zero => exact hPQ _ h
  | succ k ih => exact ih h fun f hf => hf.mono fun a ha => hPQ _ ha

theorem EventuallyRapid.and {k : ℕ} {P Q : (Fin k → ℕ) → Prop} (hP : EventuallyRapid k P)
    (hQ : EventuallyRapid k Q) : EventuallyRapid k fun f => P f ∧ Q f := by
  induction k with
  | zero => exact ⟨hP, hQ⟩
  | succ k ih => exact (ih hP hQ).mono fun f hf => hf.1.and hf.2

/-- A property holding for all sufficiently rapidly growing exponents holds for some. -/
theorem EventuallyRapid.exists {k : ℕ} {P : (Fin k → ℕ) → Prop} (h : EventuallyRapid k P) :
    ∃ f, P f := by
  induction k with
  | zero => exact ⟨_, h⟩
  | succ k ih =>
    obtain ⟨f, hf⟩ := ih h
    obtain ⟨a, ha⟩ := hf.exists
    exact ⟨_, ha⟩

/-- Stacks 051M in the nested form used by 051N: for a finite set `N ⊆ ℕ^{k+1}` and all
`e' ∈ ℕ^k` with `e'_{k-1} ≫ ⋯ ≫ e'_0 ≫ 1`, the exponents `e = (1, e'_0, …, e'_{k-1})` are
positive and `ν ↦ e · ν` is injective on `N`. -/
theorem eventuallyRapid_pos_injOn (k : ℕ) (N : Finset (Fin (k + 1) → ℕ)) :
    EventuallyRapid k fun e' => (∀ i, 1 ≤ e' i) ∧
      Set.InjOn (fun ν : Fin (k + 1) → ℕ => ∑ i, (Fin.cons 1 e' : Fin (k + 1) → ℕ) i * ν i)
        (N : Set (Fin (k + 1) → ℕ)) := by
  induction k with
  | zero =>
    refine ⟨fun i => i.elim0, fun ν _ ν' _ h => funext fun i => ?_⟩
    fin_cases i
    simpa using h
  | succ k ih =>
    refine (ih (N.image Fin.init)).mono fun e' ⟨hpos, hinj⟩ => ?_
    set w : Fin (k + 1) → ℕ := Fin.cons 1 e' with hw
    set S : (Fin (k + 2) → ℕ) → ℕ := fun ν => ∑ i, w i * Fin.init ν i with hS
    have hsplit : ∀ (a : ℕ) (ν : Fin (k + 2) → ℕ),
        ∑ i, (Fin.cons 1 (Fin.snoc e' a : Fin (k + 1) → ℕ) : Fin (k + 2) → ℕ) i * ν i
          = S ν + a * ν (Fin.last _) := by
      intro a ν
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.sum_univ_castSucc]
      simp [hS, hw, Fin.init]
    filter_upwards [Filter.eventually_ge_atTop (N.sup S + 1)] with a ha
    have ha1 : 0 < a := by lia
    refine ⟨fun i => ?_, fun ν hν ν' hν' h => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using Nat.succ_le_of_lt ha1
      · simpa using hpos j
    · simp only [hsplit] at h
      have hlt : ∀ μ ∈ N, S μ < a := fun μ hμ =>
        lt_of_le_of_lt (Finset.le_sup (f := S) hμ) (by lia)
      have hSν' := hlt ν' (Finset.mem_coe.mp hν')
      have hSν := hlt ν (Finset.mem_coe.mp hν)
      have hlast : ν (Fin.last _) = ν' (Fin.last _) := by
        have := congrArg (· / a) h
        simpa [Nat.add_mul_div_left _ _ ha1, Nat.div_eq_of_lt hSν, Nat.div_eq_of_lt hSν']
          using this
      have hS' : S ν = S ν' := by
        have := congrArg (· % a) h
        simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSν, Nat.mod_eq_of_lt hSν']
          using this
      have hinit : Fin.init ν = Fin.init ν' :=
        hinj (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hν)))
          (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hν'))) hS'
      funext i
      refine Fin.lastCases hlast (fun j => ?_) i
      exact congrFun hinit j

/-- **Stacks 051N.** Let `g ∈ R[x_1, …, x_N]` be nonconstant (here `N = n + 1`, the
variable `X 0` plays the role of the distinguished variable `x_N`, and `X i` for `1 ≤ i ≤ n`
plays the role of `x_{N-i}`). Then for all exponents `e_1 ≫ e_2 ≫ ⋯ ≫ e_{N-1} ≫ e_N = 1`,
in the nested sense of `EventuallyRapid` (the tuple `e' : Fin n → ℕ` lists
`e_{N-1}, …, e_1`, and the full exponent vector is `Fin.cons 1 e'`), the substituted
polynomial `g(x_1 + x_N^{e_1}, …, x_{N-1} + x_N^{e_{N-1}}, x_N)`, viewed via `finSuccEquiv`
as a polynomial in `x_N`, equals `a x_N^d + (lower order terms in x_N)` with `d > 0` and
`a ∈ R` one of the nonzero coefficients of `g`: its degree is `d` and its leading
coefficient is the constant `MvPolynomial.C a`. -/
@[stacks 051N "for all exponents e₁ ≫ ⋯ ≫ e_{N-1} ≫ e_N = 1 in the nested sense of \
`EventuallyRapid`; X 0 is the distinguished variable x_N"]
theorem eventuallyRapid_subst_constant_leadingCoeff_of_nonconstant
    (n : ℕ) (g : MvPolynomial (Fin (n + 1)) R)
    (hg : ¬ ∃ r : R, g = MvPolynomial.C r) :
    EventuallyRapid n fun e' => ∃ (d : ℕ) (a : R),
      (∃ ν ∈ g.support, a = g.coeff ν) ∧
      0 < d ∧
      (finSuccEquiv R n (subst n (Fin.cons 1 e') g)).natDegree = d ∧
      (finSuccEquiv R n (subst n (Fin.cons 1 e') g)).leadingCoeff = MvPolynomial.C a := by
  classical
  refine (eventuallyRapid_pos_injOn n (g.support.image (⇑))).mono fun e' ⟨hpos, hinj⟩ => ?_
  refine exists_natDegree_leadingCoeff_subst_of_injOn n g hg _ (Fin.cons_zero _ _)
    (fun i => ?_) (fun ν hν ν' hν' => ⟨fun h => ?_, fun h => h ▸ rfl⟩)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using hpos j
  · exact DFunLike.coe_injective
      (hinj (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hν))
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hν')) h)
