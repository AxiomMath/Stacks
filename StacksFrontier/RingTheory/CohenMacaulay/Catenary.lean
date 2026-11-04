module

public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.MvPolynomial
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.CohenMacaulay.Support

@[expose] public section

universe u v

/-!
# A ring with a Cohen–Macaulay module of full support is universally catenary

Let `R` be a Noetherian ring and let `M` be a finite Cohen–Macaulay `R`-module (Definition 0AAH)
with `Supp(M) = Spec(R)`. This file proves that `R` is universally catenary: every `R`-algebra of
finite type is catenary. The case `M = R` is Stacks 00NM's first sentence, a Noetherian
Cohen–Macaulay ring being universally catenary.

The argument is the source's. A finite-type `R`-algebra is a quotient of a polynomial algebra
`S = R[x_1, …, x_n]`, and catenarity passes to a quotient (Lemma 00NK), so it suffices to see that
`S` is catenary. Both hypotheses ascend to `S`: the base change `S ⊗_R M` is Cohen–Macaulay over
`S` by Lemma 0AAI, and its support is again everything. So everything rests on the catenarity of a
ring carrying such a module, and that is dimension theory in a localisation: a maximal chain of
primes ending at `𝔮` and starting at a minimal prime has length `height 𝔮`, because it becomes a
maximal chain of primes of `R_𝔮` under `Spec(R_𝔮) ≃ (-∞, 𝔮]`, where `M_𝔮` is a maximal
Cohen–Macaulay module of full support (Lemma 0AAE) and `dim(R_𝔮) = height 𝔮`. Prolonging a maximal
chain from `𝔭` to `𝔮` downwards by a maximal chain from a minimal prime to `𝔭` therefore gives
`length + height 𝔭 = height 𝔮`: the length of a maximal chain depends only on its two endpoints,
which is catenarity, and the common value is `height 𝔮 - height 𝔭`.

## Main results

* `Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ`: the statement of Stacks
  00NM.

## Implementation notes

*Maximal chains.* A maximal chain of primes with prescribed endpoints is a `RelSeries` for the
covering relation `⋖` on `PrimeSpectrum R`, as in Lemma 0AAE, while `Ring.IsCatenary` (Definition
00NI) phrases the same thing as an `LTSeries` all of whose steps are covering pairs. The two carry
the same data — `⟨t.length, t.toFun, htc⟩` is the repackaging, and it changes neither `length` nor
either end — so the passage between them is by `rfl`.

*Heights are read as natural numbers.* `Ideal.height` is valued in `ℕ∞`, but every prime of a
Noetherian ring has finite height (`Ideal.height_ne_top_of_isPrime`), so cutting both sides of
`length + height 𝔭 = height 𝔮` down by `ENat.toNat` loses nothing, and it leaves the arithmetic of
`length_add_height_head_eq_height_last` to `omega`.

*The existence of a maximal chain below a prime* is what makes the difference of two heights
available, and it comes from a chain of length `height 𝔭` ending at `𝔭`
(`Ideal.exists_ltSeries_length_eq_height`): along such a chain the height of the `i`-th term is `i`
(`Order.height_eq_index_of_length_eq_height_last`), so consecutive terms differ in height by one
and are therefore a covering pair, and the first term has height `0`, hence is a minimal prime.

*Three lemmas of the theory are proved here as private helpers*, none being in Mathlib nor in this
project's library. `Supp(R) = Spec(R)`, for want of a version of `Module.support_of_isTorsionFree`
that assumes neither a domain nor a nonzero module. `Supp(M_𝔮) = Spec(R_𝔮)` when
`Supp(M) = Spec(R)`: a prime `P` of `R_𝔮` contracts to a prime `𝔭` of `R`, an element of `R_𝔮`
outside `P` is `a/s` with `a ∉ 𝔭`, and a witness `m` for `𝔭 ∈ Supp(M)` gives one for
`P ∈ Supp(M_𝔮)`, since `t·a·m = 0` with `t ∉ 𝔮` would exhibit `t·a ∉ 𝔭` killing `m`. And
`Supp(S ⊗_R M) = Spec(S)` for `S = R[x_i]`: if `x·(1 ⊗ m) = 0` then each coefficient of `x` kills
`m`, by applying `coeff_i ⊗ id`, hence lies in the contraction of the prime, so `x` lies in the
prime by `MvPolynomial.mem_map_C_iff`. The last two are special cases of the base-change formula
`Supp_A(A ⊗_R M) = f^♯{}^{-1}(Supp M)` of tag 0BUR.

## References

* [StacksProject 00NM](https://stacks.math.columbia.edu/tag/00NM)
* [StacksProject 0AAE](https://stacks.math.columbia.edu/tag/0AAE)
* [StacksProject 0AAI](https://stacks.math.columbia.edu/tag/0AAI)
* [StacksProject 00NK](https://stacks.math.columbia.edu/tag/00NK)
-/

@[expose] public section

namespace Stacks.CohenMacaulay.UniversallyCatenary



/-- A maximal chain of primes: a series for the covering relation on the prime spectrum, the shape
Lemma 0AAE takes its chains in. -/
private abbrev CovSeries (R : Type*) [CommRing R] :=
  RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q}

/-- Every term of a series for the covering relation is at most its last term. -/
private theorem covSeries_le_last {α : Type*} [Preorder α]
    (s : RelSeries {(a, b) : α × α | a ⋖ b}) (i : Fin (s.length + 1)) : s i ≤ s.last :=
  LTSeries.monotone ⟨s.length, s.toFun, fun i => CovBy.lt (s.step i)⟩ (Fin.le_last i)

/-- Two elements whose heights are `n` and `n + 1` and which are comparable form a covering pair:
an element strictly between them would have height strictly between `n` and `n + 1`. -/
private theorem covBy_of_height_eq_of_height_eq {α : Type*} [Preorder α] {a b : α} {n : ℕ}
    (hab : a < b) (ha : Order.height a = n) (hb : Order.height b = (n : ℕ∞) + 1) : a ⋖ b := by
  refine ⟨hab, fun c hac hcb => ?_⟩
  have h1 : (n : ℕ∞) + 1 ≤ Order.height c := ha ▸ Order.height_add_one_le hac
  have h2 : Order.height c + 1 ≤ (n : ℕ∞) + 1 := hb ▸ Order.height_add_one_le hcb
  have h3 : ((n : ℕ∞) + 1) + 1 ≤ (n : ℕ∞) + 1 := le_trans (by gcongr) h2
  simp [ENat.add_one_le_iff] at h3

/-- **A maximal chain of primes ending at a given prime exists**, in a ring whose primes have
finite height: a chain of length `height 𝔭` ending at `𝔭` has `i`-th term of height `i`, so its
steps are covering pairs and its first term is a minimal prime. -/
private theorem exists_covSeries_isMin_head {R : Type*} [CommRing R] [IsNoetherianRing R]
    (q : PrimeSpectrum R) : ∃ s : CovSeries R, IsMin s.head ∧ s.last = q := by
  obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height q.asIdeal
  have hidx : ∀ i : Fin (l.length + 1), Order.height (l i) = ((i : ℕ) : ℕ∞) := fun i =>
    Order.height_eq_index_of_length_eq_height_last
      (by rw [hlast, ← PrimeSpectrum.height_eq_orderHeight, hlen]) i
  refine ⟨⟨l.length, l.toFun, fun i => covBy_of_height_eq_of_height_eq (n := (i : ℕ)) (l.step i)
    (by simpa using hidx i.castSucc) (by simpa using hidx i.succ)⟩, ?_, hlast⟩
  show IsMin (l.toFun 0)
  exact Order.height_eq_zero.mp (by simpa using hidx 0)

/-- **The chains of primes ending at `𝔮` are bounded in length by `height 𝔮`**, a natural number in
a Noetherian ring. This is the first, easy half of catenarity. -/
private theorem length_le_toNat_height {R : Type*} [CommRing R] [IsNoetherianRing R]
    {q : PrimeSpectrum R} (t : LTSeries (PrimeSpectrum R)) (htl : t.last = q) :
    t.length ≤ q.asIdeal.height.toNat := by
  have h1 : (t.length : ℕ∞) ≤ q.asIdeal.height := by
    rw [PrimeSpectrum.height_eq_orderHeight]; exact htl ▸ Order.length_le_height_last
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := q.asIdeal))
  rw [← hn] at h1 ⊢
  simpa using h1

/-- **The support of a localization at a prime is full when the support is.** If `Supp(M)` is all
of `Spec(R)` then `Supp(M_𝔮)` is all of `Spec(R_𝔮)`: a prime `P` of `R_𝔮` contracts to a prime `𝔭`
of `R`, and a witness `m` for `𝔭 ∈ Supp(M)` is a witness for `P ∈ Supp(M_𝔮)`, because an element
of `R_𝔮` outside `P` is `a/s` with `a ∉ 𝔭` and `t · a · m = 0` with `t ∉ 𝔮` would exhibit the
element `t · a` outside `𝔭` killing `m`. This is a special case of the base-change formula for
supports, tag 0BUR. -/
private theorem support_localizedModule_atPrime_eq_univ {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (q : Ideal R) [q.IsPrime]
    (h : Module.support R M = Set.univ) :
    Module.support (Localization.AtPrime q) (LocalizedModule q.primeCompl M) = Set.univ := by
  refine Set.eq_univ_of_forall fun P => Module.mem_support_iff'.mpr ?_
  set p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (Localization.AtPrime q)) P
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp (h ▸ Set.mem_univ p)
  refine ⟨LocalizedModule.mk m 1, fun x hxP hx => ?_⟩
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj q.primeCompl x
  have ha : a ∉ p.asIdeal := fun ha => hxP <| by
    rw [← Ideal.mul_unit_mem_iff_mem P.asIdeal (IsLocalization.map_units _ s), hs]
    exact Ideal.mem_comap.mp ha
  have hz : a • LocalizedModule.mk m (1 : q.primeCompl) = 0 := by
    rw [← algebraMap_smul (Localization.AtPrime q), ← hs, mul_comm, mul_smul, hx, smul_zero]
  rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk (1 : q.primeCompl),
    LocalizedModule.mk_eq] at hz
  obtain ⟨u, hu⟩ := hz
  refine hm ((u : R) * a) (fun hmem => (p.isPrime.mem_or_mem hmem).elim (fun h' => ?_) ha) ?_
  · exact P.asIdeal.notMem_of_isUnit (IsLocalization.map_units _ u) (Ideal.mem_comap.mp h')
  · rw [mul_smul]
    simp only [one_smul, smul_zero] at hu
    exact hu

/-- **A maximal chain of primes ending at `𝔮` and starting at a minimal prime has length
`height 𝔮`** when `R` carries a finite Cohen–Macaulay module `M` of full support. Under
`Spec(R_𝔮) ≃ (-∞, 𝔮]` the chain becomes a maximal chain of primes of `R_𝔮` from a minimal prime to
the maximal ideal, and `M_𝔮` is a maximal Cohen–Macaulay `R_𝔮`-module of full support, so Lemma
0AAE measures it by `dim(R_𝔮) = height 𝔮`. -/
private theorem length_eq_height_last {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.IsCohenMacaulay R M) (hsupp : Module.support R M = Set.univ) (s : CovSeries R)
    (hmin : IsMin s.head) : (s.length : ℕ∞) = s.last.asIdeal.height := by
  set q : PrimeSpectrum R := s.last
  set Rq := Localization.AtPrime q.asIdeal
  set Mq := LocalizedModule q.asIdeal.primeCompl M
  have hsupp' : Module.support Rq Mq = Set.univ :=
    support_localizedModule_atPrime_eq_univ q.asIdeal hsupp
  have hCM : Module.IsMaximalCohenMacaulay Rq Mq :=
    (hM q (hsupp ▸ Set.mem_univ q)).trans
      (Module.supportDim_eq_ringKrullDim_of_support_eq_univ hsupp')
  set e := IsLocalization.AtPrime.primeSpectrumOrderIso Rq q.asIdeal
  set s' : CovSeries Rq :=
    ⟨s.length, fun i => e.symm ⟨s i, covSeries_le_last s i⟩, fun i =>
      (apply_covBy_apply_iff e.symm).mpr
        (CovBy.of_image (OrderEmbedding.subtype (· ∈ Set.Iic q)) (s.step i))⟩
  have h := hCM.length_eq_ringKrullDim_of_support_eq_univ hsupp' s'
    ((OrderIso.isMin_apply e.symm).mpr fun c hc => hmin hc)
    ((OrderIso.isMax_apply e.symm).mpr fun c _ => c.2)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal Rq] at h
  exact_mod_cast h

/-- **The length of a maximal chain of primes is the difference of the heights of its two ends**:
`length + height(head) = height(last)`. Prolong the chain downwards by a maximal chain from a
minimal prime to its head; that chain and the prolonged one both start at a minimal prime, so
`length_eq_height_last` measures each by the height of its last term. This is the content of
catenarity: the length of a maximal chain is determined by the pair of its endpoints. -/
private theorem length_add_height_head_eq_height_last {R : Type u} [CommRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.IsCohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (t : LTSeries (PrimeSpectrum R)) (htc : ∀ i : Fin t.length, t i.castSucc ⋖ t i.succ) :
    t.length + t.head.asIdeal.height.toNat = t.last.asIdeal.height.toNat := by
  obtain ⟨u, humin, hulast⟩ := exists_covSeries_isMin_head t.head
  have hhead : (⟨t.length, t.toFun, htc⟩ : CovSeries R).head = t.head := rfl
  have hlast : (⟨t.length, t.toFun, htc⟩ : CovSeries R).last = t.last := rfl
  have hu : (u.length : ℕ∞) = t.head.asIdeal.height := by
    rw [← hulast]; exact length_eq_height_last hM hsupp u humin
  have hsm := length_eq_height_last hM hsupp
    (u.smash ⟨t.length, t.toFun, htc⟩ (hulast.trans hhead.symm))
    (by rw [RelSeries.head_smash]; exact humin)
  rw [RelSeries.smash_length, RelSeries.last_smash, hlast] at hsm
  have h1 : t.head.asIdeal.height.toNat = u.length := by rw [← hu]; simp
  have h2 : t.last.asIdeal.height.toNat = u.length + t.length := by
    rw [← hsm, ENat.toNat_natCast]
  omega

/-- **A Noetherian ring carrying a finite Cohen–Macaulay module of full support is catenary.** The
maximal chains from `𝔭` to `𝔮` all have length `height 𝔮 - height 𝔭`, and every chain from `𝔭` to
`𝔮` has length at most `height 𝔮`. -/
@[ega "0 16.5.12" "partial"]
private theorem isCatenary_of_isCohenMacaulay {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.IsCohenMacaulay R M) (hsupp : Module.support R M = Set.univ) :
    Ring.IsCatenary R := fun p q _ =>
  ⟨⟨q.asIdeal.height.toNat, fun t _ htl => length_le_toNat_height t htl⟩,
    q.asIdeal.height.toNat - p.asIdeal.height.toNat, fun t hth htl htc => by
      have h := length_add_height_head_eq_height_last hM hsupp t htc
      rw [hth, htl] at h
      omega⟩

/-- **The support of a polynomial base change is full when the support is.** If `Supp(M)` is all of
`Spec(R)` then `Supp(S ⊗_R M)` is all of `Spec(S)` for `S = R[x_i : i ∈ σ]`: if `x · (1 ⊗ m) = 0`
then applying `coeff_i ⊗ id` shows every coefficient of `x` kills `m`, hence lies in the
contraction of the given prime, so `x` lies in that prime by `MvPolynomial.mem_map_C_iff`. This is
a special case of the base-change formula for supports, tag 0BUR. -/
private theorem support_mvPolynomial_tensor_eq_univ {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (σ : Type*) (h : Module.support R M = Set.univ) :
    Module.support (MvPolynomial σ R) (TensorProduct R (MvPolynomial σ R) M) = Set.univ := by
  refine Set.eq_univ_of_forall fun Q => ?_
  set p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (MvPolynomial σ R)) Q
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp (h ▸ Set.mem_univ p)
  refine Module.mem_support_iff'.mpr ⟨TensorProduct.mk R (MvPolynomial σ R) M 1 m,
    fun x hxQ hx => hxQ ?_⟩
  have hx' : (TensorProduct.mk R (MvPolynomial σ R) M x) m = 0 := by
    rw [← hx]; simp [TensorProduct.smul_tmul']
  have hcoeff : ∀ i, MvPolynomial.coeff i x ∈ p.asIdeal := fun i => by
    by_contra hc
    refine hm _ hc ?_
    have := congrArg
      (fun z => (TensorProduct.lid R M) ((MvPolynomial.lcoeff R i).rTensor M z)) hx'
    simpa using this
  have hmap : x ∈ Ideal.map (algebraMap R (MvPolynomial σ R)) p.asIdeal := by
    rw [MvPolynomial.algebraMap_eq]
    exact MvPolynomial.mem_map_C_iff.mpr hcoeff
  exact Ideal.map_comap_le hmap

end Stacks.CohenMacaulay.UniversallyCatenary

end

/-!
# Cohen-Macaulay rings are universally catenary

Let `R` be a Noetherian ring carrying a finite Cohen–Macaulay module `M` whose support is all of
`Spec(R)`. Then `R` is universally catenary: every `R`-algebra of finite type is catenary. The
case `M = R` is the statement that a Noetherian Cohen–Macaulay ring is universally catenary.

Both hypotheses ascend along a polynomial extension — `M ⊗_R R[x_1, …, x_n]` is again
Cohen–Macaulay by Lemma 0AAI, and its support is again everything — and catenarity descends
along a surjection by Lemma 00NK, so, a finite-type `R`-algebra being a quotient of a polynomial
algebra, it suffices to see that a ring carrying such a module is catenary. That is dimension
theory in a pair of localisations: given primes `p ⊆ q`, a maximal chain of primes from `p` to `q`
of length `n`, prolonged downwards by a maximal chain from a minimal prime to `p` of length `m`,
becomes a maximal chain of primes of the local ring `R_q`, so `n + m = dim(R_q)` and
`m = dim(R_p)` by Lemma 0AAE applied to `M_q` and `M_p`. Hence `n = dim(R_q) - dim(R_p)` does not
depend on the chain, which is catenarity.

## Main results

* `Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ`: a Noetherian ring admitting
  a finite Cohen–Macaulay module of full support is universally catenary.

## Implementation notes

*One statement for both sentences of the source.* The second sentence is the general one and the
first is its case `M = R`: `Module.IsCohenMacaulay R R` is Definition 00NC, a Noetherian ring all
of whose local rings are Cohen–Macaulay, because
`Module.supportDim (Localization.AtPrime p) (Localization.AtPrime p)` is
`ringKrullDim (Localization.AtPrime p)` (`Module.supportDim_self_eq_ringKrullDim`, after the
`R_𝔭`-linear isomorphism `LocalizedModule p.primeCompl R ≃ Localization.AtPrime p`), and the
support hypothesis is then vacuous, since `Module.support R R = Set.univ` for every `R`. Hence no
separate declaration is owed for the first sentence.

*The hypothesis is the source's, by name.* "Cohen–Macaulay `R`-module" is Definition 0AAH, the
project's `Module.IsCohenMacaulay`, and "`Supp(M) = Spec(R)`" is `Module.support R M = Set.univ`,
the spelling the companion Tag 0AAE uses for the same clause. Neither is unfolded here: the localised
modules `M_𝔭` and the local rings `R_𝔭` that the condition speaks of live inside Definition 0AAH,
which pins them to the canonical models `Localization.AtPrime p` and
`LocalizedModule p.primeCompl M`, and measures depth along
`IsLocalRing.maximalIdeal (Localization.AtPrime p)`. Writing the conjunction out instead, as the
single condition `Module.IsMaximalCohenMacaulay (Localization.AtPrime p)
(LocalizedModule p.primeCompl M)` at every prime `p` of `R`, gives an equivalent hypothesis and so
an equally strong theorem — with full support, `Module.supportDim (R_𝔭) (M_𝔭)` collapses to
`ringKrullDim (R_𝔭)`, and conversely maximal Cohen–Macaulayness at `p` forces `M_𝔭 ≠ 0`, the zero
module having depth `⊤` where a Noetherian local ring has finite dimension — but it names neither
definition, so a reader holding Definition 0AAH could not apply the result, and it does not meet
Lemma 0AAI, which is stated on `Module.IsCohenMacaulay` and is what the source's proof of this
lemma invokes.

*The hypothesis quantifies no universe, and its localisations are the canonical ones.* For
`R : Type u` and `M : Type v` the objects the condition speaks of are `Localization.AtPrime 𝔭`,
of universe `u`, and `LocalizedModule 𝔭.primeCompl M`, of universe `max u v`; Definition 0AAH
names both, so the two universes here are independent and the hypothesis is an assumption about
the localisation of `M` itself. A hypothesis phrased over an abstract localisation `M_𝔭 : Type v`
instead would be weaker than it appears: it excludes `LocalizedModule 𝔭.primeCompl M` unless
`u ≤ v`, so it could not be applied to the canonical localisation and, absent any `M_𝔭` in
`Type v` satisfying `IsLocalizedModule 𝔭.primeCompl`, would be satisfiable vacuously. The
concrete form is also the one Tag 00ND uses for its own hypothesis at the localisations of `R`.

*Noetherian and finite are assumed here, not inside the definitions.* Definitions 00N3 and 0AAH
are made for a Noetherian ring and a finite module; the project's `Module.IsCohenMacaulay` states
the condition without them, so both are hypotheses of this lemma, as they are of Lemmas 0AAI and
0AAE.

*The catenary predicate.* `Ring.IsUniversallyCatenary` is Definition 00NL, formalized with Tag 00NK,
and carries no Noetherian hypothesis of its own; `R` is Noetherian here, so the conclusion is the
source's notion verbatim. Its finite-type algebras range over the universe of `R`, which is no
restriction: every finite-type `R`-algebra is a quotient of some `R[X_1, …, X_n]`, hence
isomorphic to one in that universe.

Faithfulness to [StackProject 00NM].

1. No dead hypothesis. `hM` and `hsupp` are the source's two conditions on `M`, and both are
   consumed: `hM` through Lemmas 0AAI and 0AAE, `hsupp` to know that a maximal chain of primes of
   `R_𝔮` has length `dim(R_𝔮)` rather than `dim Supp(M_𝔮)`, and to keep the support full after
   base change. `[IsNoetherianRing R]` is the source's and is what makes dimension theory
   available; `[Module.Finite R M]` is the finiteness the source keeps inside Definitions 00N3
   and 0AAH, without which `depth(M_𝔭) ≤ dim Supp(M_𝔭)` fails. Nothing else is assumed: no local
   hypothesis on `R`, no dimension named, no bound on the chains.
2. The scalars and base are the source's. Inside `hM` the depth and the dimension are those of the
   localisation — the depth of the `R_𝔭`-module `M_𝔭` along the maximal ideal of `R_𝔭`, and the
   dimension of `Supp(M_𝔭)` over `R_𝔭` — never the depth of `M` over `R` or along an ideal of
   `R`; `hsupp` is an equality of subsets of `Spec(R)`. In the conclusion the algebras are
   `R`-algebras of finite type and their catenarity is about chains of their own primes.
3. The objects the source names are pinned, not merely asserted to exist. `M_𝔭` and `R_𝔭` are the
   canonical `LocalizedModule p.primeCompl M` and `Localization.AtPrime p`, localised along the
   same `p.primeCompl` and so a localisation of the pair `(R, M)` at `p` rather than two unrelated
   objects; `Supp(M)` is `Module.support R M`, the set of primes with `M_𝔭 ≠ 0`; and
   `Ring.IsCatenary` pins the common length of the maximal chains from `p` to `q` by an `∃ n`
   inside the clause for that fixed pair, as the source does.
4. The instantiation is not degenerate. Take `R = k[x, y]` over a field and `M = R`: every
   localisation of `R` is a regular local ring, hence Cohen–Macaulay, so `hM` holds, `hsupp` holds
   for every ring, and `Spec(R)` carries chains of primes of length `2`, so the conclusion
   constrains lengths that are genuinely nonzero. The conclusion is not automatic either: Nagata's
   example is a Noetherian ring that is not universally catenary, so `hM` cannot be dropped. A
   witness with `M` not the ring itself: any Noetherian Cohen–Macaulay `R` with `M = R × R`.

## References

* [StackProject 00NM](https://stacks.math.columbia.edu/tag/00NM)

## Tags

Cohen-Macaulay ring, Cohen-Macaulay module, universally catenary, catenary, depth
-/



@[expose] public section

/-- **A Noetherian ring with a Cohen–Macaulay module of full support is universally catenary.**
If `R` is Noetherian and `M` is a finite Cohen–Macaulay `R`-module (Definition 0AAH) with
`Supp(M) = Spec(R)`, then every `R`-algebra of finite type is catenary. Taking `M = R`, where the
support condition is automatic, this says that a Noetherian Cohen–Macaulay ring is universally
catenary. The universes of `R` and `M` are independent: the localisations the hypothesis speaks
of are named inside Definition 0AAH, which puts `M_𝔭` in `Type (max u v)`. -/
@[stacks 00NM "The source's `M` Cohen-Macaulay with `Supp(M) = Spec(R)` is
`Module.IsCohenMacaulay R M` (Definition 0AAH) together with `Module.support R M = Set.univ`, the
spelling of the companion Tag 0AAE; the Noetherian and finiteness hypotheses, which the source keeps
inside Definitions 00N3 and 0AAH, are assumed explicitly; and the first sentence of the tag is the
case `M = R`, where the support condition holds for every ring. See the module docstring.",
  ega "0 16.5.12" "local CM ring case",
  ega "IV 6.3.7" "CM ring itself",
  ega "IV 7.2.7" "universally catenary", sga "6 X 1.5" "Affine ambient case"]
public theorem Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ {R : Type u}
    [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hM : Module.IsCohenMacaulay R M)
    (hsupp : Module.support R M = Set.univ) :
    Ring.IsUniversallyCatenary R := by
  intro C _ _ _
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R C›
  refine Ring.IsCatenary.of_surjective (f := (f : MvPolynomial (Fin n) R →+* C)) hf ?_
  exact Stacks.CohenMacaulay.UniversallyCatenary.isCatenary_of_isCohenMacaulay
    (M := TensorProduct R (MvPolynomial (Fin n) R) M)
    (hM.mvPolynomial_of_isBaseChange (TensorProduct.isBaseChange R M _))
    (Stacks.CohenMacaulay.UniversallyCatenary.support_mvPolynomial_tensor_eq_univ _ hsupp)

end
