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
form used here, taken as an infimum over `WithBot ℕ∞`; see `localDimAtPrime`.

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
topological local dimension `min { dim(U) : x ∈ U ⊆ X open }`. -/
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
`k[y_1, …, y_d] = MvPolynomial (Fin d) k`, such that `d = dim(S_g) = dim_x(X)` and `ψ` is
injective and finite. -/
@[stacks 00OZ]
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
# Separating a finite set of multi-indices by a single dot product

Stacks tag 051M. Fix `n : ℕ` and work with multi-indices, elements of `ℕ^n` modelled as
functions `Fin n → ℕ`, so that `ν = (ν_1, …, ν_n)`. The dot product of exponent vectors
`e = (e_1, …, e_n)` and `ν = (ν_1, …, ν_n)` is `e · ν = ∑_{i=1}^{n} e_i ν_i ∈ ℕ`.

The result: for a finite set `N ⊆ ℕ^n` of multi-indices there is an exponent tuple
`e ∈ ℕ^n` with `e · ν = e · ν' ↔ ν = ν'` for all `ν, ν' ∈ N`; equivalently, `ν ↦ e · ν`
is injective on `N`.

The informal notation `e_1 ≫ e_2 ≫ ⋯ ≫ e_n` expresses that the conclusion holds once the
exponents decrease rapidly enough in magnitude. Concretely one may take `e_i = M^{n-i}`
for a base `M` larger than every coordinate appearing in any `ν ∈ N`, which separates
multi-indices by reading off their base-`M` digits; the content is the existence of a
single tuple `e` for which the dot product distinguishes the finitely many elements of `N`.
The implication `ν = ν' ⇒ e · ν = e · ν'` is trivial, so the substance is injectivity of
`ν ↦ e · ν` on `N`. Finiteness of `N` is essential, since it is what bounds `M`;
nonemptiness is not needed. All quantities are natural numbers.
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

/-- For a finite set `N ⊆ ℕ^n`, there is an exponent tuple `e ∈ ℕ^n` such that
`e · ν = e · ν' ↔ ν = ν'` for all `ν, ν' ∈ N`. -/
@[stacks 051M]
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
`g`, there is a tilting substitution `Φ_e : x_i ↦ x_i + x_n^(e_i)` for `i < n`
and `x_n ↦ x_n`, after which `Φ_e(g)`, viewed as a polynomial in `x_n` over
`S = R[x_1, …, x_{n-1}]`, has a *constant* leading coefficient `a ∈ R`, one of
the nonzero coefficients of `g`, and positive degree.

## Indexing convention

The informal statement uses `n ≥ 1` variables `x_1, …, x_n` with `x_n`
distinguished. Here this is `MvPolynomial (Fin (n+1)) R` for `n : ℕ`, so that
the number of variables is `n + 1 ≥ 1`, and the variable of index `0` plays the
role of the distinguished variable `x_n`, while the remaining indices `1, …, n`
play the role of `x_1, …, x_{n-1}`.

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

/-- Stacks tag 051M (Lemma 10.115.1), normalized: for a finite set `N` of multi-indices in
`Fin (m+1) →₀ ℕ` there are exponents `e i ≥ 1` with `e 0 = 1` such that the linear form
`ν ↦ ∑ i, e i * ν i` is injective on `N`. -/
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

/-- Let `g` be a nonconstant polynomial in `MvPolynomial (Fin (n+1)) R`, that is one
not in the image of the constant inclusion `MvPolynomial.C : R → …`. Then there
exist exponents `e` with `e 0 = 1`, encoding `e_n = 1`, a positive integer `d`,
and an element `a ∈ R` such that:

1. `a` is one of the nonzero coefficients of `g`: there is a multi-index `ν` in
   the support of `g` with `a = g.coeff ν`, so in particular `a ≠ 0`.

2. Viewing `f = subst n e g` as a polynomial in the distinguished variable `X 0`
   via `finSuccEquiv R n`, its degree in that variable is `d` and its leading
   coefficient is the *constant* `MvPolynomial.C a`, the image of `a ∈ R` inside
   `S = MvPolynomial (Fin n) R`. -/
@[stacks 051N]
theorem exists_substitution_with_constant_leadingCoeff_of_nonconstant
    (n : ℕ) (g : MvPolynomial (Fin (n + 1)) R)
    (hg : ¬ ∃ r : R, g = MvPolynomial.C r) :
    ∃ (e : Fin (n + 1) → ℕ) (d : ℕ) (a : R),
      e 0 = 1 ∧
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
  obtain ⟨e, he0, he1, hinj⟩ := supporting_lemma_normalized n g.support
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
  refine ⟨e, d, a, he0, ⟨νs, hνs_mem, rfl⟩, ?_, ?_, ?_⟩
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
