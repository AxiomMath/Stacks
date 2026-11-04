module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Nagata.JapaneseCriteria
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness

/-!
# Tate's theorem: N-2 ascends along a complete principal quotient

Let `R` be a Noetherian integrally closed domain and let `x ∈ R` be such that `xR` is prime,
so that `R ⧸ xR` is again a domain. Tate's theorem says that if `R ⧸ xR` is N-2 (Japanese) and
`R` is complete for the `x`-adic topology, then `R` itself is N-2: the integral closure of `R`
in *every* finite extension `L` of `K = Frac(R)` is a finite `R`-module.

In characteristic zero, or more generally for a separable `L/K`, finiteness is a trace-form
argument needing only that `R` be Noetherian and integrally closed
(`IsIntegralClosure.finite`), and neither the quotient nor the completeness hypothesis is
involved. The content is therefore inseparable: for `L/K` purely inseparable of exponent `q = pⁿ`
one may adjoin a `q`-th root `y` of `x` to `L`, and then the integral closure `S` of `R` in `L`
has `yS` as its unique prime over `xR`, with `S ⧸ yS` sitting inside the integral closure of
`R ⧸ xR` in the residue field `κ(yS)` — a finite extension of `κ(xR)`, so the N-2 hypothesis on
`R ⧸ xR` bounds `S ⧸ yS`, hence `S ⧸ xS`, and `x`-adic completeness of `R` lifts that bound
to finiteness of `S` itself.

## Main results

* `IsJapaneseRing.of_quotient_span_singleton`: Tate's theorem, Tag 032P.

## Implementation notes

Normality of the domain `R` is `IsIntegrallyClosed R`, Mathlib's spelling of "integrally closed
in its field of fractions", rather than this development's `IsNormalRing` (Tag 037D), which
quantifies over the localizations of a ring not assumed to be a domain; for a domain the two
agree, and the hypothesis of the source is normality *of a domain*.

"`R ⧸ xR` is a domain" is spelled `(Ideal.span {x}).IsPrime`, a condition on `R` and `x`, which
is what supplies the `IsDomain (R ⧸ Ideal.span {x})` instance that the statement of
`IsJapaneseRing` for the quotient requires (`Ideal.Quotient.isDomain`). It also rules out `x`
being a unit, which the source's hypothesis rules out for the same reason.

Completeness is weakened from the source's `R ≅ lim R/xⁿR` to `IsPrecomplete (Ideal.span {x}) R`:
the Hausdorff half of `IsAdicComplete`, i.e. `⋂ xⁿR = 0`, is automatic for a Noetherian domain
and a proper ideal (`IsHausdorff.of_isDomain`, applicable since a prime ideal is not `⊤`), so
demanding it would be demanding something free. A ring carrying `IsAdicComplete (Ideal.span {x}) R`
satisfies the hypothesis by `IsAdicComplete.toIsPrecomplete`, so the usual instances apply
directly.

The proof runs the source's argument, with two departures from its wording.

* The reduction to purely inseparable extensions is Tag 032N
  (`isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable`), which also disposes of the
  characteristic-zero case: in characteristic zero the only finite purely inseparable extension
  of `K` is `K` itself, so nothing beyond normality is needed there and the source's appeal to
  Tag 032M is not separately required. The uniform exponent `q = pⁿ`, for which `a ^ q` lies in
  `K` for every `a : L`, is `IsPurelyInseparable.exponent`, available because `L/K` is finite,
  and the enlargement of `L` by a `q`-th root `y` of `x` is `L⟮y⟯` inside an algebraic closure of
  `L`. That `a ^ q` again lies in `K` for every `a : L⟮y⟯` follows from the same statement for `L`
  together with `y ^ q = x`, by the additivity of the `q`-th power map on a field of exponential
  characteristic `p`.

* Finiteness of the residue field extension `κ(yS)/κ(xR)` is proved directly, rather than through
  the source's route of localizing at `xR`, invoking Krull-Akizuki (Tag 00PG) to know that
  `S_{yS}` is Noetherian, and then citing Tag 031F. The direct argument is that elements of `S`
  whose classes mod `yS` are independent over `R ⧸ xR` are independent over `K`: a `K`-linear
  relation is cleared of denominators to an `R`-linear one and divided by the largest power of `x`
  dividing all of its coefficients — possible because `⋂ xⁿR = 0` — after which reducing modulo
  `yS` contradicts the assumed independence. So `[κ(yS) : κ(xR)] ≤ [L⟮y⟯ : K]`, which is all the
  source's chain of lemmas is used for, and neither the discrete valuation rings nor Krull-Akizuki
  are needed.

The passage from `S ⧸ yS` to `S ⧸ xS = S ⧸ y ^ q S` is the source's filtration of `S ⧸ yⁿS` by the
`yⁱS ⧸ yⁱ⁺¹S`, carried out as the statement that `S = V + yS` with `V` finitely generated implies
`S = V + yV + ⋯ + yⁿ⁻¹V + yⁿS`. Finiteness of `S` itself is then Tag 031D
(`Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top`), whose separatedness
hypothesis `⋂ xⁿS = 0` holds because an element of the intersection has its `q`-th power in
`⋂ xⁿR = 0`.

Faithfulness.
1. Every hypothesis is used by the conclusion, and none is decoration: `IsNoetherianRing R` and
   `IsIntegrallyClosed R` give the separable part of `L/K` (they alone are the
   characteristic-zero case), while `IsJapaneseRing (R ⧸ Ideal.span {x})` and
   `IsPrecomplete (Ideal.span {x}) R` are what handle the purely inseparable part; dropping
   either leaves a false statement, completeness being unrelated to the finiteness of a residual
   integral closure and conversely.
2. The scalars and base are the source's: N-2 for `R` asserts `Module.Finite R` of the integral
   closure of `R` in `L` — finiteness over `R`, not over `K` nor `L` — and N-2 for the quotient
   is over `R ⧸ xR`, not over `R`.
3. The maps the source names are pinned, not merely assumed to exist: the quotient is `R ⧸ xR`
   along `Ideal.Quotient.mk`, and completeness is with respect to the `x`-adic filtration
   `(Ideal.span {x})ⁿ` rather than an unspecified isomorphism `R ≅ lim R/xⁿR`.
4. The instantiation is not degenerate: `R = k[[t]]` for a field `k` and `x = t` satisfies every
   hypothesis — a Noetherian integrally closed domain, `span {t}` prime with quotient the field
   `k`, which is N-2, and `IsAdicComplete (Ideal.span {PowerSeries.X}) (PowerSeries k)` is an
   instance — and its conclusion, that `k[[t]]` is N-2, is a statement about infinitely many
   nontrivial extensions of `k((t))`.

## References

* [Grothendieck and Dieudonné, *Éléments de géométrie algébrique*][EGA], Theorem 23.1.3
* [Stacks Project, Tag 032P](https://stacks.math.columbia.edu/tag/032P)
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
  {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
  [IsScalarTower R (FractionRing R) M]

private theorem algebraMap_inj : Function.Injective (algebraMap R M) := by
  rw [IsScalarTower.algebraMap_eq R (FractionRing R) M]
  exact (FaithfulSMul.algebraMap_injective (FractionRing R) M).comp
    (IsFractionRing.injective R (FractionRing R))

/-- In a Noetherian domain, an element divisible by every power of a prime generator `x` is zero. -/
private theorem eq_zero_of_forall_pow_dvd [IsNoetherianRing R] {x : R}
    (hp : (Ideal.span {x}).IsPrime) {r : R} (h : ∀ n : ℕ, x ^ n ∣ r) : r = 0 :=
  (IsHausdorff.of_isDomain _ hp.ne_top).haus r fun n => SModEq.zero.mpr (by
    simpa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using h n)

/-- Cancel the largest possible power of `x` from a nonzero family: if some `a j ≠ 0`, then
`a i = x ^ N * c i` for all `i`, for some `N` and some family `c` not contained in `x R`. -/
private theorem exists_pow_mul_not_mem [IsNoetherianRing R] {x : R}
    (hp : (Ideal.span {x}).IsPrime) {ι : Type*} (a : ι → R) {j : ι} (hj : a j ≠ 0) :
    ∃ (N : ℕ) (c : ι → R), (∀ i, a i = x ^ N * c i) ∧ ∃ i, c i ∉ Ideal.span {x} := by
  classical
  have hex : ∃ n, ¬ ∀ i, x ^ n ∣ a i := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hj (eq_zero_of_forall_pow_dvd hp fun n => hall n j)
  have hspec : ¬ ∀ i, x ^ Nat.find hex ∣ a i := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    simp at hspec
  obtain ⟨N, hN⟩ : ∃ N, Nat.find hex = N + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hdvd : ∀ i, x ^ N ∣ a i := not_not.mp (Nat.find_min hex (by omega))
  choose c hc using hdvd
  refine ⟨N, c, hc, ?_⟩
  by_contra hall
  simp only [not_exists, not_not] at hall
  refine hspec fun i => ?_
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hall i)
  rw [hN, hc i, ← hd]
  exact ⟨d, by ring⟩

variable [IsIntegrallyClosed R]

private theorem exists_pow_eq {q : ℕ}
    (hMq : ∀ a : M, ∃ k : FractionRing R, a ^ q = algebraMap (FractionRing R) M k)
    (s : integralClosure R M) : ∃ r : R, (s : M) ^ q = algebraMap R M r := by
  obtain ⟨k, hk⟩ := hMq (s : M)
  have hint : IsIntegral R ((s : M) ^ q) := s.2.pow q
  rw [hk] at hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (IsIntegral.tower_bot (FaithfulSMul.algebraMap_injective _ _) hint)
  exact ⟨r, by rw [hk, ← hr, ← IsScalarTower.algebraMap_apply]⟩

/-- Membership in the ideal `y S` of `S = integralClosure R M` is detected by `q`-th powers:
`s ∈ y S` if and only if `s ^ q ∈ x R`. -/
private theorem mem_span_iff {q : ℕ} (hq : 0 < q)
    (hMq : ∀ a : M, ∃ k : FractionRing R, a ^ q = algebraMap (FractionRing R) M k)
    {x : R} {y : integralClosure R M} (hy : (y : M) ^ q = algebraMap R M x)
    (s : integralClosure R M) :
    s ∈ Ideal.span {y} ↔ ∃ r : R, (s : M) ^ q = algebraMap R M (x * r) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero] at hy
    have hy0 : (y : M) = 0 := pow_eq_zero_iff hq.ne' |>.mp hy
    constructor
    · rintro hs
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      exact ⟨0, by rw [Subalgebra.coe_mul, hy0, mul_zero, zero_pow hq.ne', zero_mul, map_zero]⟩
    · rintro ⟨r, hr⟩
      rw [zero_mul, map_zero] at hr
      have hs0 : s = 0 := Subtype.ext (by simpa using pow_eq_zero_iff hq.ne' |>.mp hr)
      exact hs0 ▸ Submodule.zero_mem _
  have hx0 : algebraMap R M x ≠ 0 := fun h => hx ((map_eq_zero_iff _ algebraMap_inj).mp h)
  have hy0 : (y : M) ≠ 0 := by
    intro h
    rw [h, zero_pow hq.ne'] at hy
    exact hx0 hy.symm
  constructor
  · rintro hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    obtain ⟨r, hr⟩ := exists_pow_eq hMq t
    refine ⟨r, ?_⟩
    rw [Subalgebra.coe_mul, mul_pow, hr, hy, map_mul]
    ring
  · rintro ⟨r, hr⟩
    have hupow : ((s : M) / (y : M)) ^ q = algebraMap R M r := by
      rw [div_pow, hr, hy, map_mul, mul_comm, mul_div_assoc, div_self hx0, mul_one]
    have huint : IsIntegral R ((s : M) / (y : M)) :=
      IsIntegral.of_pow hq (by rw [hupow]; exact isIntegral_algebraMap)
    refine Ideal.mem_span_singleton'.mpr ⟨⟨_, huint⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul]
    exact div_mul_cancel₀ _ hy0

section Prime

variable {q : ℕ} (hq : 0 < q)
  (hMq : ∀ a : M, ∃ k : FractionRing R, a ^ q = algebraMap (FractionRing R) M k)
  {x : R} (hp : (Ideal.span {x}).IsPrime)
  {y : integralClosure R M} (hy : (y : M) ^ q = algebraMap R M x)

include hq hMq hp hy

/-- The ideal `y S` is prime: its elements are the `s` with `s ^ q ∈ x R`, and `x R` is prime. -/
private theorem isPrime_span : (Ideal.span {y}).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
  · intro htop
    obtain ⟨r, hr⟩ := (mem_span_iff hq hMq hy 1).mp (htop ▸ Submodule.mem_top)
    rw [OneMemClass.coe_one, one_pow] at hr
    have h1 : (1 : R) = x * r :=
      algebraMap_inj (M := M) (show algebraMap R M 1 = algebraMap R M (x * r) by rw [map_one, hr])
    exact hp.ne_top (Ideal.span_singleton_eq_top.mpr (isUnit_iff_exists_inv.mpr ⟨r, h1.symm⟩))
  · intro a b hab
    obtain ⟨r, hr⟩ := (mem_span_iff hq hMq hy _).mp hab
    obtain ⟨ra, hra⟩ := exists_pow_eq hMq a
    obtain ⟨rb, hrb⟩ := exists_pow_eq hMq b
    have key : ra * rb = x * r := by
      apply algebraMap_inj (M := M)
      rw [map_mul, ← hra, ← hrb, ← mul_pow, ← Subalgebra.coe_mul, hr]
    have hmem : ra * rb ∈ Ideal.span {x} :=
      key ▸ Ideal.mem_span_singleton'.mpr ⟨r, mul_comm r x⟩
    rcases hp.mem_or_mem hmem with h | h
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
      exact Or.inl ((mem_span_iff hq hMq hy a).mpr ⟨c, by rw [hra, ← hc, mul_comm]⟩)
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
      exact Or.inr ((mem_span_iff hq hMq hy b).mpr ⟨c, by rw [hrb, ← hc, mul_comm]⟩)

/-- The prime `y S` of `S` lies over the prime `x R` of `R`. -/
private theorem comap_span :
    Ideal.comap (algebraMap R (integralClosure R M)) (Ideal.span {y}) = Ideal.span {x} := by
  have hcoe : ∀ r : R, ((algebraMap R (integralClosure R M) r : integralClosure R M) : M)
      = algebraMap R M r := fun r => rfl
  ext r
  rw [Ideal.mem_comap, mem_span_iff hq hMq hy]
  constructor
  · rintro ⟨c, hc⟩
    rw [hcoe, ← map_pow] at hc
    have h : r ^ q = x * c := algebraMap_inj hc
    exact hp.mem_of_pow_mem q (h ▸ Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c x⟩)
  · rintro hr
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    refine ⟨c ^ (m + 1) * x ^ m, ?_⟩
    rw [hcoe, ← map_pow, ← hc]
    exact congrArg (algebraMap R M) (by ring)

end Prime


section Quotient

variable [IsNoetherianRing R] {x : R} (hp : (Ideal.span {x}).IsPrime)
  {y : integralClosure R M} [(Ideal.span {y}).LiesOver (Ideal.span {x})]

include hp
omit [IsIntegrallyClosed R]

/-- Elements of `S = integralClosure R M` whose classes mod `y S` are linearly independent over
`R / x R` are themselves linearly independent over `K = Frac R`.

A `K`-linear relation is cleared of denominators to an `R`-linear one, then divided by the largest
power of `x` dividing all its coefficients; the resulting relation has a coefficient outside `x R`,
so reducing it modulo `y S` contradicts the assumed independence. -/
private theorem linearIndependent_of_quotient {ι : Type*} [Finite ι]
    (f : ι → integralClosure R M)
    (hLI : LinearIndependent (R ⧸ Ideal.span {x})
      fun i => Ideal.Quotient.mk (Ideal.span {y}) (f i)) :
    LinearIndependent (FractionRing R) fun i => ((f i : M)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg i₀
  by_contra hne
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ g
  choose a ha using fun i => hb i (Finset.mem_univ i)
  have hrel : ∀ i, algebraMap R (FractionRing R) (a i)
      = algebraMap R (FractionRing R) (b : R) * g i := fun i => by
    rw [ha i, Algebra.smul_def]
  have hb0 : algebraMap R (FractionRing R) (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have haj : a i₀ ≠ 0 := by
    intro h
    have h₀ := hrel i₀
    rw [h, map_zero] at h₀
    exact (mul_eq_zero.mp h₀.symm).elim hb0 hne
  have hsum : ∑ i, algebraMap R M (a i) * (f i : M) = 0 := by
    have : ∀ i, algebraMap R M (a i) * (f i : M)
        = algebraMap R M (b : R) * (g i • (f i : M)) := by
      intro i
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R (FractionRing R) M,
        IsScalarTower.algebraMap_apply R (FractionRing R) M (b : R), hrel i, map_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, hg, mul_zero]
  obtain ⟨N, c, hc, i₁, hi₁⟩ := exists_pow_mul_not_mem hp a haj
  have hxN : algebraMap R M (x ^ N) ≠ 0 := by
    intro h
    rw [map_eq_zero_iff _ algebraMap_inj] at h
    exact haj (by rw [hc i₀, h, zero_mul])
  have hsum' : ∑ i, algebraMap R M (c i) * (f i : M) = 0 := by
    have h0 : algebraMap R M (x ^ N) * ∑ i, algebraMap R M (c i) * (f i : M) = 0 := by
      rw [Finset.mul_sum, ← hsum]
      exact Finset.sum_congr rfl fun i _ => by rw [hc i, map_mul]; ring
    exact (mul_eq_zero.mp h0).resolve_left hxN
  have hsumS : ∑ i, algebraMap R (integralClosure R M) (c i) * f i = 0 := by
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum]
    simpa using hsum'
  have hQ : ∑ i, (Ideal.Quotient.mk (Ideal.span {x}) (c i)) •
      (Ideal.Quotient.mk (Ideal.span {y}) (f i)) = 0 := by
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {y})) hsumS
    rw [map_sum, map_zero] at h
    refine h ▸ Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_mk_of_liesOver, map_mul]
  exact hi₁ ((Ideal.Quotient.eq_zero_iff_mem).mp
    (Fintype.linearIndependent_iff.mp hLI _ hQ i₁))

end Quotient


/-- Let `A` be a Noetherian N-2 domain and let `C` be a domain containing `A` in which the `q`-th
power of every element lies in `A`. If every `A`-linearly independent family in `C` has at most `N`
members, then `C` is a finite `A`-module.

The bound makes `Frac C` a finite extension of `Frac A`, so N-2 for `A` bounds the integral closure
of `A` in `Frac C`, and `C` — every element of which is integral over `A`, being a `q`-th root of
an element of `A` — is contained in that integral closure. -/
private theorem module_finite_of_isJapaneseRing {A C : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing C] [IsDomain C] [Algebra A C]
    (hinj : Function.Injective (algebraMap A C)) (hA : IsJapaneseRing A) {q : ℕ} (hq : 0 < q)
    (hCq : ∀ t : C, ∃ a : A, t ^ q = algebraMap A C a) {N : ℕ}
    (hN : ∀ (n : ℕ) (v : Fin n → C), LinearIndependent A v → n ≤ N) :
    Module.Finite A C := by
  classical
  have hAinj : Function.Injective (algebraMap A (FractionRing C)) :=
    (IsFractionRing.injective C (FractionRing C)).comp hinj
  let : Algebra (FractionRing A) (FractionRing C) := (IsFractionRing.lift hAinj).toAlgebra
  have : IsScalarTower A (FractionRing A) (FractionRing C) :=
    IsScalarTower.of_algebraMap_eq fun a => (IsFractionRing.lift_algebraMap hAinj a).symm
  have hfd : FiniteDimensional (FractionRing A) (FractionRing C) := by
    have hrank : Module.rank (FractionRing A) (FractionRing C) ≤ (N : Cardinal) := by
      refine rank_le fun s hs => ?_
      obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors C) s id
      choose w hw using fun i : s => hb i.1 i.2
      have hb0 : algebraMap C (FractionRing C) (b : C) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
      have h1 : LinearIndependent (FractionRing A)
          fun i : s => algebraMap C (FractionRing C) (w i) := by
        have hker : (LinearMap.mulLeft (FractionRing A)
            (algebraMap C (FractionRing C) (b : C))).ker = ⊥ := by
          rw [LinearMap.ker_eq_bot]
          exact fun u v huv => mul_left_cancel₀ hb0 huv
        have heq : (fun i : s => algebraMap C (FractionRing C) (w i))
            = ⇑(LinearMap.mulLeft (FractionRing A)
                (algebraMap C (FractionRing C) (b : C))) ∘ fun i : s => (i : FractionRing C) := by
          funext i
          simp only [Function.comp_apply, LinearMap.mulLeft_apply]
          rw [hw i, Algebra.smul_def, id_eq]
        rw [heq]
        exact hs.map' _ hker
      have h2 : LinearIndependent A fun i : s => algebraMap C (FractionRing C) (w i) :=
        h1.restrict_scalars (by
          simpa [Algebra.smul_def] using IsFractionRing.injective A (FractionRing A))
      have h3 : LinearIndependent A fun i : s => w i :=
        LinearIndependent.of_comp
          ((Algebra.linearMap C (FractionRing C)).restrictScalars A) h2
      have e : Fin s.card ≃ (s : Type u) :=
        (finCongr (Fintype.card_coe s).symm).trans (Fintype.equivFin (s : Type u)).symm
      exact hN s.card (fun i => w (e i)) (h3.comp e e.injective)
    exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0))
  have hfin := hA.finite (FractionRing C)
  have : IsNoetherian A (integralClosure A (FractionRing C)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have hint : ∀ t : C, IsIntegral A (algebraMap C (FractionRing C) t) := by
    intro t
    obtain ⟨a, ha⟩ := hCq t
    refine IsIntegral.of_pow hq ?_
    rw [← map_pow, ha, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  refine Module.Finite.of_injective
    ({ toFun := fun t => ⟨algebraMap C (FractionRing C) t, hint t⟩
       map_add' := fun s t => Subtype.ext (by simp)
       map_smul' := fun a t => Subtype.ext (by
         simp only [RingHom.id_apply, SetLike.val_smul]
         rw [Algebra.smul_def, Algebra.smul_def, map_mul,
           IsScalarTower.algebraMap_apply A C (FractionRing C)]) } :
      C →ₗ[A] integralClosure A (FractionRing C))
    fun u v h => IsFractionRing.injective C (FractionRing C) (congrArg Subtype.val h)

section Residue

variable [IsNoetherianRing R] [FiniteDimensional (FractionRing R) M] {q : ℕ} (hq : 0 < q)
  (hMq : ∀ a : M, ∃ k : FractionRing R, a ^ q = algebraMap (FractionRing R) M k)
  {x : R} [(Ideal.span {x}).IsPrime] {y : integralClosure R M}
  [(Ideal.span {y}).IsPrime] [(Ideal.span {y}).LiesOver (Ideal.span {x})]

include hq hMq

/-- `S / y S` is a finite `R / x R`-module, where `S = integralClosure R M`: the `q`-th power of
every element of `S / y S` comes from `R / x R`, and a family in `S / y S` independent over
`R / x R` lifts to a `K`-independent family in `M`, so has at most `[M : K]` members. -/
private theorem module_finite_quotient (hJ : IsJapaneseRing (R ⧸ Ideal.span {x})) :
    Module.Finite (R ⧸ Ideal.span {x}) (integralClosure R M ⧸ Ideal.span {y}) := by
  classical
  refine module_finite_of_isJapaneseRing (FaithfulSMul.algebraMap_injective _ _) hJ hq
    (N := Module.finrank (FractionRing R) M) ?_ ?_
  · intro t
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨r, hr⟩ := exists_pow_eq hMq s
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, ← map_pow]
    exact congrArg (Ideal.Quotient.mk (Ideal.span {y})) (Subtype.ext (by simpa using hr))
  · intro n v hv
    choose g hg using fun i => Ideal.Quotient.mk_surjective (v i)
    have h4 : LinearIndependent (R ⧸ Ideal.span {x})
        fun i => Ideal.Quotient.mk (Ideal.span {y}) (g i) := by simpa only [hg] using hv
    simpa using (linearIndependent_of_quotient inferInstance g h4).fintype_card_le_finrank

end Residue

section Filtration

variable {R : Type u} [CommRing R] {M : Type u} [Field M] [Algebra R M]

/-- `x S = y ^ q S` inside `S = integralClosure R M`, as `R`-submodules. -/
private theorem smul_top_eq {n : ℕ} {x : R} {y : integralClosure R M}
    (hy : (y : M) ^ n = algebraMap R M x) :
    (Ideal.span {x}) • (⊤ : Submodule R (integralClosure R M))
      = (Ideal.span {y ^ n}).restrictScalars R := by
  have hxy : algebraMap R (integralClosure R M) x = y ^ n := Subtype.ext (by simpa using hy.symm)
  refine le_antisymm (Submodule.smul_le.mpr ?_) ?_
  · intro r hr s _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap R (integralClosure R M) c * s, ?_⟩
    rw [Algebra.smul_def, ← hc, map_mul, hxy]
    ring
  · intro s hs
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hs
    rw [← ht, ← hxy, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) Submodule.mem_top

/-- A quotient of `S` by a submodule complemented by a finitely generated one is a finite
`R`-module. -/
private theorem module_finite_quotient_of_fg_sup {N : Submodule R (integralClosure R M)}
    {V : Submodule R (integralClosure R M)} (hVfg : V.FG) (hV : V ⊔ N = ⊤) :
    Module.Finite R (integralClosure R M ⧸ N) := by
  have h1 : Submodule.map N.mkQ V ⊔ Submodule.map N.mkQ N = ⊤ := by
    rw [← Submodule.map_sup, hV, Submodule.map_top, Submodule.range_mkQ]
  have h2 : Submodule.map N.mkQ N = ⊥ :=
    eq_bot_iff.mpr (Submodule.map_le_iff_le_comap.mpr
      (by rw [Submodule.comap_bot, Submodule.ker_mkQ]))
  rw [h2, sup_bot_eq] at h1
  exact Module.finite_def.mpr (h1 ▸ hVfg.map _)

/-- The `y`-adic filtration: if `S = V + y S` with `V` finitely generated, then
`S = V + y V + ⋯ + y ^ (n-1) V + y ^ n S`, again with a finitely generated first part. -/
private theorem exists_fg_sup_pow (y : integralClosure R M)
    (h₁ : ∃ V : Submodule R (integralClosure R M), V.FG ∧
      V ⊔ (Ideal.span {y}).restrictScalars R = ⊤) (n : ℕ) :
    ∃ V : Submodule R (integralClosure R M), V.FG ∧
      V ⊔ (Ideal.span {y ^ n}).restrictScalars R = ⊤ := by
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
  | succ n ih =>
    obtain ⟨V, hVfg, hV⟩ := ih
    obtain ⟨V₁, hV₁fg, hV₁⟩ := h₁
    refine ⟨V₁ ⊔ Submodule.map (LinearMap.mulLeft R y) V, hV₁fg.sup (hVfg.map _),
      le_antisymm le_top fun s _ => ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hV₁ ▸ Submodule.mem_top (x := s))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb
    obtain ⟨a', ha', b', hb', hab'⟩ := Submodule.mem_sup.mp (hV ▸ Submodule.mem_top (x := c))
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hb'
    refine Submodule.mem_sup.mpr ⟨a + y * a', Submodule.add_mem _ (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨a', ha', rfl⟩)), d * y ^ (n + 1),
      Ideal.mem_span_singleton'.mpr ⟨d, rfl⟩, ?_⟩
    rw [← hab, ← hc, ← hab', ← hd]
    ring

end Filtration

section Main

variable [IsNoetherianRing R] [FiniteDimensional (FractionRing R) M] {q : ℕ} (hq : 0 < q)
  (hMq : ∀ a : M, ∃ k : FractionRing R, a ^ q = algebraMap (FractionRing R) M k)
  {x : R} [(Ideal.span {x}).IsPrime] [IsPrecomplete (Ideal.span {x}) R]
  {y : integralClosure R M} (hy : (y : M) ^ q = algebraMap R M x)

include hq hMq hy

/-- **Tate's argument.** If `x R` is prime with `R / x R` Japanese, `R` is `x`-adically
precomplete, and the `q`-th power of every element of `M` lies in `K` with `x` a `q`-th power in
`M`, then the integral closure of `R` in `M` is a finite `R`-module. -/
private theorem module_finite_integralClosure (hJ : IsJapaneseRing (R ⧸ Ideal.span {x})) :
    Module.Finite R (integralClosure R M) := by
  classical
  have : (Ideal.span {y}).IsPrime := isPrime_span hq hMq inferInstance hy
  have : (Ideal.span {y}).LiesOver (Ideal.span {x}) :=
    ⟨(comap_span hq hMq inferInstance hy).symm⟩
  -- `S / y S` is finite over `R / x R`, hence over `R`
  have hPfin : Module.Finite R (R ⧸ Ideal.span {x}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R (Ideal.span {x})).toLinearMap
      Ideal.Quotient.mk_surjective
  have h1 : Module.Finite (R ⧸ Ideal.span {x}) (integralClosure R M ⧸ Ideal.span {y}) :=
    module_finite_quotient hq hMq hJ
  have h2 : Module.Finite R (integralClosure R M ⧸ Ideal.span {y}) :=
    Module.Finite.trans (R ⧸ Ideal.span {x}) _
  -- hence `S = V + y S` with `V` finitely generated
  have h3 : ∃ V : Submodule R (integralClosure R M), V.FG ∧
      V ⊔ (Ideal.span {y}).restrictScalars R = ⊤ := by
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin
      (R := R) (M := integralClosure R M ⧸ Ideal.span {y})
    choose f hf using fun i => Ideal.Quotient.mk_surjective (g i)
    refine ⟨Submodule.span R (Set.range f), Submodule.fg_span (Set.finite_range f),
      le_antisymm le_top fun s _ => ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
      (hg ▸ Submodule.mem_top (x := Ideal.Quotient.mk (Ideal.span {y}) s))
    refine Submodule.mem_sup.mpr ⟨∑ i, c i • f i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), s - ∑ i, c i • f i, ?_, by ring⟩
    have : Ideal.Quotient.mk (Ideal.span {y}) (∑ i, c i • f i)
        = Ideal.Quotient.mk (Ideal.span {y}) s := by
      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hf i, Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl
    simpa [Ideal.Quotient.eq_zero_iff_mem] using
      (Submodule.Quotient.eq (Ideal.span {y})).mp this.symm
  -- so `S / x S = S / y ^ q S` is finite over `R`, hence over `R / x R`
  obtain ⟨V, hVfg, hV⟩ := exists_fg_sup_pow y h3 q
  have h4 : Module.Finite R (integralClosure R M ⧸
      (Ideal.span {x}) • (⊤ : Submodule R (integralClosure R M))) := by
    rw [smul_top_eq hy]
    exact module_finite_quotient_of_fg_sup hVfg hV
  have h5 : Module.Finite (R ⧸ Ideal.span {x}) (integralClosure R M ⧸
      (Ideal.span {x}) • (⊤ : Submodule R (integralClosure R M))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  -- the intersection of the `xⁿ S` is zero
  have hhaus : ⨅ n : ℕ, (Ideal.span {x}) ^ n • (⊤ : Submodule R (integralClosure R M)) = ⊥ := by
    refine eq_bot_iff.mpr fun f hf => ?_
    obtain ⟨rf, hrf⟩ := exists_pow_eq hMq f
    have hrf0 : rf = 0 := by
      refine eq_zero_of_forall_pow_dvd (x := x) inferInstance fun n => ?_
      have hfn : f ∈ (Ideal.span {x}) ^ n • (⊤ : Submodule R (integralClosure R M)) :=
        (Submodule.mem_iInf _).mp hf n
      rw [Ideal.span_singleton_pow, smul_top_eq (n := q * n) (x := x ^ n)
        (by rw [pow_mul, hy, map_pow])] at hfn
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hfn
      obtain ⟨rt, hrt⟩ := exists_pow_eq hMq t
      obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      have hyq : ((y : M) ^ (q * n)) ^ q = algebraMap R M ((x ^ n) ^ q) := by
        rw [pow_mul, map_pow, map_pow, ← hy]
      have hkey : rf = rt * (x ^ n) ^ q := by
        refine algebraMap_inj (M := M) ?_
        rw [map_mul, ← hrf, ← hyq, ← hrt, ← ht]
        push_cast
        ring
      exact ⟨rt * x ^ (n * m), by rw [hkey, hm]; ring⟩
    have : (f : M) ^ q = 0 := by rw [hrf, hrf0, map_zero]
    exact Subtype.ext (by simpa using pow_eq_zero_iff hq.ne' |>.mp this)
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    (Ideal.span {x}) hhaus h5

end Main

section Descent

/-- Tate's argument, applied inside a finite extension `F` of `L` in which `x` has a `q`-th root
and whose `q`-th powers all lie in `K`: the integral closure of `R` in `L` is then finite, being
carried injectively into the integral closure of `R` in `F`. -/
private theorem module_finite_of_intermediateField {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {x : R} [(Ideal.span {x}).IsPrime]
    [IsPrecomplete (Ideal.span {x}) R] (hJ : IsJapaneseRing (R ⧸ Ideal.span {x}))
    {L Ω : Type u} [Field L] [Algebra (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
    [Field Ω] [Algebra L Ω] [Algebra (FractionRing R) Ω] [Algebra R Ω]
    [IsScalarTower R (FractionRing R) Ω] [IsScalarTower (FractionRing R) L Ω]
    [IsScalarTower R L Ω] (F : IntermediateField L Ω) [FiniteDimensional L F] {q : ℕ}
    (hq : 0 < q)
    (hFq : ∀ a : F, ∃ k : FractionRing R, (a : Ω) ^ q = algebraMap (FractionRing R) Ω k)
    (y : F) (hy : (y : Ω) ^ q = algebraMap R Ω x) :
    Module.Finite R (integralClosure R L) := by
  have i4 : IsScalarTower R L ↥F := IntermediateField.isScalarTower F
  have i5 : IsScalarTower (FractionRing R) L ↥F := IntermediateField.isScalarTower F
  have i6 : FiniteDimensional (FractionRing R) ↥F := Module.Finite.trans L ↥F
  have c1 : ∀ r : R, ((algebraMap R ↥F r : ↥F) : Ω) = algebraMap R Ω r := fun _ => rfl
  have c2 : ∀ k : FractionRing R, ((algebraMap (FractionRing R) ↥F k : ↥F) : Ω)
      = algebraMap (FractionRing R) Ω k := fun _ => rfl
  have i3 : IsScalarTower R (FractionRing R) ↥F := IsScalarTower.of_algebraMap_eq fun r =>
    Subtype.ext (by rw [c1, c2, IsScalarTower.algebraMap_apply R (FractionRing R) Ω])
  have hFq' : ∀ a : ↥F, ∃ k : FractionRing R, a ^ q = algebraMap (FractionRing R) ↥F k := by
    intro a
    obtain ⟨k, hk⟩ := hFq a
    exact ⟨k, Subtype.ext (by rw [c2]; simpa using hk)⟩
  have hy' : y ^ q = algebraMap R ↥F x := Subtype.ext (by rw [c1]; simpa using hy)
  have hyint : IsIntegral R y := IsIntegral.of_pow hq (by rw [hy']; exact isIntegral_algebraMap)
  exact module_finite_integralClosure_of_injective (IsScalarTower.toAlgHom R L ↥F)
    (algebraMap L ↥F).injective
    (module_finite_integralClosure (M := ↥F) hq hFq' (y := ⟨y, hyint⟩) (by simpa using hy') hJ)

end Descent


/-- **Tate's theorem.** Let `R` be a Noetherian integrally closed (i.e. normal) domain and let
`x ∈ R` generate a prime ideal, so that `R ⧸ xR` is a domain. If `R ⧸ xR` is N-2 (Japanese) and
`R` is `x`-adically complete, then `R` is N-2.

Completeness is asked for as `IsPrecomplete (Ideal.span {x}) R`; the Hausdorff half of
`IsAdicComplete` is automatic here, see the module docstring. -/
@[stacks 032P, ega "0 23.1.3"]
public theorem IsJapaneseRing.of_quotient_span_singleton {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (x : R) [(Ideal.span {x}).IsPrime]
    [IsPrecomplete (Ideal.span {x}) R] (h : IsJapaneseRing (R ⧸ Ideal.span {x})) :
    IsJapaneseRing R := by
  rw [isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable]
  intro L _ _ _ _ _ _
  have hexp : ExpChar (FractionRing R) (ringExpChar (FractionRing R)) :=
    ringExpChar.expChar (FractionRing R)
  have t1 : IsScalarTower R (FractionRing R) (AlgebraicClosure L) :=
    IsScalarTower.to₁₂₄ R (FractionRing R) L (AlgebraicClosure L)
  have t2 : IsScalarTower R L (AlgebraicClosure L) :=
    IsScalarTower.to₁₃₄ R (FractionRing R) L (AlgebraicClosure L)
  have hexpΩ : ExpChar (AlgebraicClosure L) (ringExpChar (FractionRing R)) :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (FractionRing R) (AlgebraicClosure L)) _
  have hLq : ∀ a : L, ∃ k : FractionRing R,
      a ^ ringExpChar (FractionRing R) ^ IsPurelyInseparable.exponent (FractionRing R) L
        = algebraMap (FractionRing R) L k := by
    intro a
    obtain ⟨k, hk⟩ := IsPurelyInseparable.exponent_def (K := FractionRing R) a
    exact ⟨k, hk.symm⟩
  have hq : 0 < ringExpChar (FractionRing R) ^ IsPurelyInseparable.exponent (FractionRing R) L :=
    pow_pos (expChar_pos (FractionRing R) (ringExpChar (FractionRing R))) _
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap R (AlgebraicClosure L) x) hq
  have hyint : IsIntegral L y := IsIntegral.of_pow hq (by
    rw [hy, IsScalarTower.algebraMap_apply R L (AlgebraicClosure L)]
    exact isIntegral_algebraMap)
  have key : ∀ a ∈ IntermediateField.adjoin L ({y} : Set (AlgebraicClosure L)),
      ∃ k : FractionRing R,
        a ^ ringExpChar (FractionRing R) ^ IsPurelyInseparable.exponent (FractionRing R) L
          = algebraMap (FractionRing R) (AlgebraicClosure L) k := by
    intro a ha
    induction ha using IntermediateField.adjoin_induction with
    | mem z hz =>
      refine ⟨algebraMap R (FractionRing R) x, ?_⟩
      rw [Set.mem_singleton_iff.mp hz, hy,
        IsScalarTower.algebraMap_apply R (FractionRing R) (AlgebraicClosure L)]
    | algebraMap z =>
      obtain ⟨k, hk⟩ := hLq z
      exact ⟨k, by rw [← map_pow, hk, ← IsScalarTower.algebraMap_apply]⟩
    | add z w _ _ ihz ihw =>
      obtain ⟨k₁, h₁⟩ := ihz
      obtain ⟨k₂, h₂⟩ := ihw
      exact ⟨k₁ + k₂, by rw [add_pow_expChar_pow, h₁, h₂, map_add]⟩
    | inv z _ ihz =>
      obtain ⟨k, hk⟩ := ihz
      exact ⟨k⁻¹, by rw [inv_pow, hk, map_inv₀]⟩
    | mul z w _ _ ihz ihw =>
      obtain ⟨k₁, h₁⟩ := ihz
      obtain ⟨k₂, h₂⟩ := ihw
      exact ⟨k₁ * k₂, by rw [mul_pow, h₁, h₂, map_mul]⟩
  have : FiniteDimensional L (IntermediateField.adjoin L ({y} : Set (AlgebraicClosure L))) :=
    IntermediateField.adjoin.finiteDimensional hyint
  exact module_finite_of_intermediateField h
    (IntermediateField.adjoin L ({y} : Set (AlgebraicClosure L))) hq
    (fun a => key a a.2) ⟨y, IntermediateField.mem_adjoin_simple_self L y⟩ hy


end
