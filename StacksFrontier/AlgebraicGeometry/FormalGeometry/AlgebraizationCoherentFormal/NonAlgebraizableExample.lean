module

public import Mathlib.Algebra.MonoidAlgebra.Division
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Order
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationSituation

/-!
# The two-chart formal line modules on the punctured spectrum of `k[x,y][[t]]`

Let `k` be a field, `A = k[x,y][[t]]`, `I = (t)` and `𝔞 = (x,y,t)`, so that in the
algebraization situation attached to this data `Y = V(t)` is the closed fibre and
`U = Spec(A) \ V(x,y,t)` is the punctured spectrum. The intersection `U ∩ Y` is covered by the
two basic opens `D(x)` and `D(y)`, and on that two-chart cover one glues `A_x/t^nA_x` to
`A_y/t^nA_y` along the unit

`u = 1 + t/(xy) + ∑_{m ≥ 2} a_m t^m/(xy)^{φ(m)}`

of `A_{xy}/t^nA_{xy}`. This file sets up that data: the situation, the two-chart covering of
`U ∩ Y`, the chart rings and their reductions, the transition element together with its
invertibility and its compatibility down the tower, the module of compatible pairs, and — for
the degenerate choice `a_m = 0` — a nonzero compatible system of such pairs, namely the
function `x` on `D(x)` glued to `x + t/y` on `D(y)`.

Modulo `t²` the transition element is `1 + t/(xy)` for every choice of `a` and `φ`, and the
glued module of that order is already not free: a trivialization would write `1/(xy)` as the
difference of a function on `D(x)` and a function on `D(y)`, which the Laurent expansions of
the two charts forbid.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.situation` — the algebraization situation with
  `A = k[x,y][[t]]`, `I = (t)` and `𝔞 = (x,y,t)`.
* `Stacks.Algebraization.NonAlgebraizableExample.chartRing` — the quotient `A_r/t^nA_r` of a
  localization of `A` away from an element `r`.
* `Stacks.Algebraization.NonAlgebraizableExample.transitionElement` — the image in
  `A_{xy}/t^nA_{xy}` of the displayed power series `u`.
* `Stacks.Algebraization.NonAlgebraizableExample.gluedSections` — the `A`-module of pairs of
  chart elements matched by a prescribed transition element.
* `Stacks.Algebraization.NonAlgebraizableExample.coordinateSection` — the pair consisting of
  `x` on `D(x)` and `x + t/y` on `D(y)`.
* `Stacks.Algebraization.NonAlgebraizableExample.sectionsLimit` — the inverse limit
  `lim H⁰(U, L_n)` of the global sections, as the module of compatible systems of glued pairs.
* `Stacks.Algebraization.NonAlgebraizableExample.HasSeparatedExponents` — the condition on the
  exponents `φ` under which that limit vanishes, abstracted from the source's two prescriptions
  `φ(m) = 2^m` and `φ(m) = m²`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.coe_U_inter_zeroLocus_eq` — `U ∩ Y` is the
  union of `D(x) ∩ Y` and `D(y) ∩ Y`. Both pieces are affine, being basic opens of an affine
  scheme (`AlgebraicGeometry.IsAffineOpen.basicOpen`).
* `Stacks.Algebraization.NonAlgebraizableExample.compl_zeroLocus_map_idealXYT` — the punctured
  spectrum of `A/t^nA` is the union of the two basic opens `D(x)` and `D(y)`: the element `t` is
  nilpotent there, so `V(x,y,t)` and `V(x,y)` agree and no third chart is needed.
* `Stacks.Algebraization.NonAlgebraizableExample.isUnit_transitionElement` — the transition
  element is a unit, for every choice of coefficients and exponents.
* `Stacks.Algebraization.NonAlgebraizableExample.chartReduction_transitionElement` — the
  transition elements are compatible with reduction modulo `t^n`, so they form a tower.
* `Stacks.Algebraization.NonAlgebraizableExample.exists_ne_zero_compatible_mem_gluedSections` —
  when `a_m = 0` for `m ≥ 2` there is a nonzero compatible system of glued pairs.
* `Stacks.Algebraization.NonAlgebraizableExample.not_isUnit_of_mem_gluedSections_two` — modulo
  `t²` no pair of invertible chart functions is matched by the transition element, for any
  choice of coefficients and exponents.
* `Stacks.Algebraization.NonAlgebraizableExample.sectionsLimit_eq_bot` — when every `a_m` is
  `1` and `φ(m)` is `2^m` or `m²`, the limit `lim H⁰(U, L_n)` is zero; contrast
  `sectionsLimit_ne_bot` for the degenerate choice `a_m = 0`. It factors through
  `sectionsLimit_eq_bot_of_hasSeparatedExponents`, which asks only that the exponents separate
  degrees, and `hasSeparatedExponents_of_eq_two_pow_or_sq`, which checks that both prescriptions
  do.

## Implementation notes

The series `u` does not converge in `A_{xy}`, because the exponents `φ(m)` are unbounded; only
its truncations modulo `t^n` are meaningful, and `transitionElement` is defined by that finite
truncation. This is what the source means by "the image of any power series of the form `u`":
the terms with `m ≥ n` are divisible by `t^n` and so do not contribute.

All chart rings are instances of a single `chartRing k r n = A_r/t^nA_r`, with the two charts
and their overlap obtained by taking `r` to be `x`, `y` and `xy`; the reduction maps down the
tower are then one construction, `chartReduction`.

`gluedSections` is defined for an arbitrary transition element rather than only for a unit; the
invertibility of the transition element is the separate statement `isUnit_transitionElement`.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- The polynomial ring `k[x,y]`, with its two variables indexed by `Fin 2`. -/
public abbrev PlaneRing : Type u := MvPolynomial (Fin 2) k

/-- The ring `A = k[x,y][[t]]`. -/
public abbrev AmbientRing : Type u := PowerSeries (PlaneRing k)

/-- The first coordinate `x` of the plane, viewed in `A = k[x,y][[t]]`. -/
public def xVar : AmbientRing k := PowerSeries.C (MvPolynomial.X 0)

/-- The second coordinate `y` of the plane, viewed in `A = k[x,y][[t]]`. -/
public def yVar : AmbientRing k := PowerSeries.C (MvPolynomial.X 1)

/-- The power-series variable `t` of `A = k[x,y][[t]]`. -/
public def tVar : AmbientRing k := PowerSeries.X

/-- The ideal `I = (t)` of `A = k[x,y][[t]]`. -/
public def idealT : Ideal (AmbientRing k) := Ideal.span {tVar k}

/-- The ideal `𝔞 = (x,y,t)` of `A = k[x,y][[t]]`. -/
public def idealXYT : Ideal (AmbientRing k) := Ideal.span {xVar k, yVar k, tVar k}

/-- **Stacks Project, Tag 0EHE (the situation).** The algebraization situation with
`A = k[x,y][[t]]`, `I = (t)` and `𝔞 = (x,y,t)`. -/
@[stacks 0EHE "the situation A = k[x,y][[t]], I = (t), 𝔞 = (x,y,t)"]
public def situation : AlgebraizationSituation.{u} where
  A := AmbientRing k
  I := idealT k
  a := idealXYT k
  I_le_a := Ideal.span_mono (by simp)

/-- The ring of the situation is `A = k[x,y][[t]]`. -/
@[simp]
public lemma situation_A : (situation k).A = AmbientRing k := rfl

/-- The ideal `I` of the situation is `(t)`. -/
@[simp]
public lemma situation_I : (situation k).I = idealT k := rfl

/-- The ideal `𝔞` of the situation is `(x,y,t)`. -/
@[simp]
public lemma situation_a : (situation k).a = idealXYT k := rfl

/-- **Stacks Project, Tag 0EHE (the two-chart covering).** The punctured closed fibre
`U ∩ Y` of the situation is covered by the two basic opens `D(x)` and `D(y)`. Each of
`D(x) ∩ Y` and `D(y) ∩ Y` is affine, being a basic open of an affine scheme; see
`AlgebraicGeometry.IsAffineOpen.basicOpen`. -/
@[stacks 0EHE "the open covering of U ∩ Y by D(x) and D(y)"]
public theorem coe_U_inter_zeroLocus_eq :
    (situation k).U.carrier ∩
        PrimeSpectrum.zeroLocus ((idealT k : Ideal (AmbientRing k)) : Set (AmbientRing k)) =
      ((PrimeSpectrum.basicOpen (xVar k)).carrier ∪
          (PrimeSpectrum.basicOpen (yVar k)).carrier) ∩
        PrimeSpectrum.zeroLocus ((idealT k : Ideal (AmbientRing k)) : Set (AmbientRing k)) := by
  have hxmem : xVar k ∈ ({xVar k, yVar k, tVar k} : Set (AmbientRing k)) :=
    Set.mem_insert _ _
  have hymem : yVar k ∈ ({xVar k, yVar k, tVar k} : Set (AmbientRing k)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have htmem : tVar k ∈ ({xVar k, yVar k, tVar k} : Set (AmbientRing k)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  apply Set.eq_of_subset_of_subset
  · rintro p ⟨hU, hY⟩
    have htp : tVar k ∈ p.asIdeal := hY (Ideal.subset_span rfl)
    refine ⟨?_, hY⟩
    rcases Classical.em (xVar k ∈ p.asIdeal) with hx | hx
    · rcases Classical.em (yVar k ∈ p.asIdeal) with hy | hy
      · have hspan : Ideal.span ({xVar k, yVar k, tVar k} : Set (AmbientRing k)) ≤
            p.asIdeal :=
          Ideal.span_le.mpr (by
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl | rfl
            · exact hx
            · exact hy
            · exact htp)
        exact absurd hspan hU
      · exact Set.mem_union_right _ hy
    · exact Set.mem_union_left _ hx
  · rintro p ⟨h, hY⟩
    refine ⟨?_, hY⟩
    intro hmem
    rcases h with hx | hy
    · exact hx (hmem (Ideal.subset_span hxmem))
    · exact hy (hmem (Ideal.subset_span hymem))

/-- The level ring `A/t^nA` of the construction: the ring of the closed subscheme of `Spec(A)`
cut out by `I^n = (t^n)`, on whose punctured spectrum the module `L_n` lives. -/
public abbrev levelRing (n : ℕ) : Type u := AmbientRing k ⧸ (idealT k) ^ n

/-- The image of `t` in `A/t^nA` is nilpotent. -/
public lemma isNilpotent_mk_tVar (n : ℕ) :
    IsNilpotent (Ideal.Quotient.mk ((idealT k) ^ n) (tVar k)) :=
  ⟨n, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, idealT, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _⟩

/-- The image of `t` in `A/t^nA` lies in every prime ideal. -/
public lemma mk_tVar_mem_asIdeal (n : ℕ) (p : PrimeSpectrum (levelRing k n)) :
    Ideal.Quotient.mk ((idealT k) ^ n) (tVar k) ∈ p.asIdeal := by
  obtain ⟨m, hm⟩ := isNilpotent_mk_tVar k n
  exact p.isPrime.mem_of_pow_mem m (hm ▸ p.asIdeal.zero_mem)

/-- **Stacks Project, Tag 0EHE (the two charts cover the punctured spectrum of `A/t^n`).**
The element `t` is nilpotent in `A/t^nA`, hence lies in every prime, so the vanishing locus of
`𝔞 = (x,y,t)` in `Spec(A/t^nA)` is the vanishing locus of `(x,y)`. Its complement — the part of
`Spec(A/t^nA)` lying over `U` — is therefore the union of the two basic opens `D(x)` and `D(y)`,
and no third chart is needed to cover it. -/
@[stacks 0EHE "the two charts D(x), D(y) cover the punctured spectrum of A/t^n"]
public theorem compl_zeroLocus_map_idealXYT (n : ℕ) :
    (PrimeSpectrum.zeroLocus
        (((idealXYT k).map (Ideal.Quotient.mk ((idealT k) ^ n)) : Ideal (levelRing k n)) :
          Set (levelRing k n)))ᶜ =
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk ((idealT k) ^ n) (xVar k))).carrier ∪
        (PrimeSpectrum.basicOpen (Ideal.Quotient.mk ((idealT k) ^ n) (yVar k))).carrier := by
  have hmap : ((idealXYT k).map (Ideal.Quotient.mk ((idealT k) ^ n)) : Ideal (levelRing k n)) =
      Ideal.span {Ideal.Quotient.mk ((idealT k) ^ n) (xVar k),
        Ideal.Quotient.mk ((idealT k) ^ n) (yVar k),
        Ideal.Quotient.mk ((idealT k) ^ n) (tVar k)} := by
    rw [idealXYT, Ideal.map_span]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton]
  ext p
  simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.mem_union,
    TopologicalSpace.Opens.carrier_eq_coe, SetLike.coe_subset_coe,
    PrimeSpectrum.mem_basicOpen, hmap, Ideal.span_le, Set.insert_subset_iff,
    Set.singleton_subset_iff, SetLike.mem_coe]
  have := mk_tVar_mem_asIdeal k n p
  tauto

/-- The quotient `A_r/t^nA_r` of the localization of `A = k[x,y][[t]]` away from `r` by the
`n`-th power of `t`. Taking `r` to be `x`, `y` or `xy` gives the two charts of the cover of
`U ∩ Y` and their overlap. -/
public abbrev chartRing (r : AmbientRing k) (n : ℕ) : Type u :=
  Localization.Away r ⧸
    Ideal.span {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n}

/-- The reduction `A_r/t^{n+1}A_r → A_r/t^nA_r`. -/
public def chartReduction (r : AmbientRing k) (n : ℕ) :
    chartRing k r (n + 1) →ₐ[Localization.Away r] chartRing k r n :=
  Ideal.Quotient.factorₐ _ <| by
    simpa only [Ideal.span_singleton_pow] using
      Ideal.pow_le_pow_right
        (I := Ideal.span {algebraMap (AmbientRing k) (Localization.Away r) (tVar k)})
        (Nat.le_succ n)

/-- Reduction modulo `t^n` sends the class of `z` in `A_r/t^{n+1}A_r` to its class in
`A_r/t^nA_r`. -/
@[simp]
public lemma chartReduction_mk (r : AmbientRing k) (n : ℕ) (z : Localization.Away r) :
    chartReduction k r n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ z :=
  Ideal.Quotient.factorₐ_apply_mk _ _ _

/-- **Stacks Project, Tag 0EHE (the transition element).** The image in `A_{xy}/t^nA_{xy}` of
the power series `u = 1 + t/(xy) + ∑_{m ≥ 2} a_m t^m/(xy)^{φ(m)}`. Only the terms with `m < n`
survive modulo `t^n`, which is why the sum is taken over `Finset.Ico 2 n`. -/
public def transitionElement (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    chartRing k (xVar k * yVar k) n :=
  Ideal.Quotient.mk _ <|
    1 + algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) *
        IsLocalization.Away.invSelf (xVar k * yVar k) +
      ∑ m ∈ Finset.Ico 2 n,
        algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k))
            (PowerSeries.C (a m)) *
          algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) ^ m *
          IsLocalization.Away.invSelf (xVar k * yVar k) ^ φ m

/-- **Stacks Project, Tag 0EHE (invertibility of the transition element).** The transition
element is a unit of `A_{xy}/t^nA_{xy}`: it is `1` plus a nilpotent element, every term beyond
the leading `1` being divisible by `t`. -/
@[stacks 0EHE "the transition element is a unit of A_xy/t^n A_xy"]
public theorem isUnit_transitionElement (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    IsUnit (transitionElement k a φ n) := by
  set R := Localization.Away (xVar k * yVar k) with hR
  set τ : R := algebraMap (AmbientRing k) R (tVar k) with hτ
  set p : R := τ * IsLocalization.Away.invSelf (xVar k * yVar k) +
    ∑ m ∈ Finset.Ico 2 n,
      algebraMap (AmbientRing k) R (PowerSeries.C (a m)) * τ ^ m *
        IsLocalization.Away.invSelf (xVar k * yVar k) ^ φ m with hp
  have hmem : p ∈ Ideal.span {τ} := by
    rw [hp]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun m hm => ?_)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self τ)
    · have hm1 : 1 ≤ m := le_trans (by norm_num) (Finset.mem_Ico.mp hm).1
      have hpow : τ ^ m ∈ Ideal.span {τ} := by
        rw [← Nat.sub_add_cancel hm1, pow_succ']
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self τ)
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hpow)
  have hpow : p ^ n ∈ Ideal.span {τ ^ n} := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hmem n
  have hzero : Ideal.Quotient.mk (Ideal.span {τ ^ n}) (p ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hpow
  rw [map_pow] at hzero
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {τ ^ n}) p) :=
    ⟨n, hzero⟩
  simpa only [transitionElement, hp, map_add, map_one, add_assoc] using hnil.isUnit_one_add

/-- **Stacks Project, Tag 0EHE (the transition tower).** The transition elements are
compatible with reduction modulo `t^n`, so the glued modules form an inverse system. -/
@[stacks 0EHE "the transition elements are compatible with reduction mod t^n"]
public theorem chartReduction_transitionElement (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    chartReduction k (xVar k * yVar k) n (transitionElement k a φ (n + 1)) =
      transitionElement k a φ n := by
  rcases le_or_gt 2 n with hn | hn
  · have hz : Ideal.Quotient.mk (Ideal.span
        {(algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k)) ^ n})
        (algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k))
              (PowerSeries.C (a n)) *
            algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) ^ n *
            IsLocalization.Away.invSelf (xVar k * yVar k) ^ φ n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _
          (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    rw [transitionElement, transitionElement, chartReduction_mk, Finset.sum_Ico_succ_top hn,
      ← add_assoc, map_add, hz, add_zero]
  · have h₀ : Finset.Ico 2 n = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    have h₁ : Finset.Ico 2 (n + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp only [transitionElement, h₀, h₁, Finset.sum_empty, add_zero, chartReduction_mk]

/-- Restriction of localizations along a divisibility `r ∣ q`, that is, restriction of functions
from the basic open `D(r)` to the smaller basic open `D(q)`. -/
public def localizationRestrict (r q : AmbientRing k) (h : r ∣ q) :
    Localization.Away r →ₐ[AmbientRing k] Localization.Away q :=
  { IsLocalization.Away.lift r (IsLocalization.Away.isUnit_of_dvd (x := q) h) with
    commutes' := fun z => IsLocalization.Away.lift_eq _ _ z }

/-- Restriction from `D(r)` to `D(q)` sends the image of an element of `A` to its image. -/
@[simp]
public lemma localizationRestrict_algebraMap (r q : AmbientRing k) (h : r ∣ q)
    (z : AmbientRing k) :
    localizationRestrict k r q h (algebraMap (AmbientRing k) (Localization.Away r) z) =
      algebraMap (AmbientRing k) (Localization.Away q) z :=
  (localizationRestrict k r q h).commutes z

/-- Restriction `A_r/t^nA_r → A_q/t^nA_q` along a divisibility `r ∣ q`. -/
public def chartRestrict (r q : AmbientRing k) (h : r ∣ q) (n : ℕ) :
    chartRing k r n →ₐ[AmbientRing k] chartRing k q n :=
  Ideal.quotientMapₐ _ (localizationRestrict k r q h) <| by
    rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, localizationRestrict_algebraMap]
    exact Ideal.mem_span_singleton_self _

/-- Restriction between charts is computed on representatives. -/
public lemma chartRestrict_mk (r q : AmbientRing k) (hdvd : r ∣ q) (n : ℕ)
    (z : Localization.Away r) :
    chartRestrict k r q hdvd n (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (localizationRestrict k r q hdvd z) := rfl

/-- Restriction from the chart `D(x)` to the overlap `D(xy)`. -/
public abbrev xChartToOverlap (n : ℕ) :
    chartRing k (xVar k) n →ₐ[AmbientRing k] chartRing k (xVar k * yVar k) n :=
  chartRestrict k (xVar k) (xVar k * yVar k) (dvd_mul_right _ _) n

/-- Restriction from the chart `D(y)` to the overlap `D(xy)`. -/
public abbrev yChartToOverlap (n : ℕ) :
    chartRing k (yVar k) n →ₐ[AmbientRing k] chartRing k (xVar k * yVar k) n :=
  chartRestrict k (yVar k) (xVar k * yVar k) (dvd_mul_left _ _) n

/-- **Stacks Project, Tag 0EHE (the glued sections).** The `A`-module of pairs matched by a
prescribed transition element: a pair `(f, h)` with `f` a function on `D(x)` and `h` a function
on `D(y)`, both taken modulo `t^n`, lies in it exactly when `h = g · f` on the overlap `D(xy)`.
For `g` the transition element these are the sections of the glued module. -/
public def gluedSections (n : ℕ) (g : chartRing k (xVar k * yVar k) n) :
    Submodule (AmbientRing k) (chartRing k (xVar k) n × chartRing k (yVar k) n) where
  carrier := {s | yChartToOverlap k n s.2 = g * xChartToOverlap k n s.1}
  zero_mem' := by simp
  add_mem' := by
    intro s s' hs hs'
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, map_add] at hs hs' ⊢
    rw [hs, hs', mul_add]
  smul_mem' := by
    intro c s hs
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, map_smul] at hs ⊢
    rw [hs, mul_smul_comm]

/-- A pair `(s₁, s₂)` of chart elements is a glued section for `g` exactly when the restriction of
`s₂` to the overlap is `g` times the restriction of `s₁`. -/
public lemma mem_gluedSections_iff (n : ℕ) (g : chartRing k (xVar k * yVar k) n)
    (s : chartRing k (xVar k) n × chartRing k (yVar k) n) :
    s ∈ gluedSections k n g ↔
      yChartToOverlap k n s.2 = g * xChartToOverlap k n s.1 := Iff.rfl

/-- **Stacks Project, Tag 0EHE (the limit of global sections).** The inverse limit
`lim H⁰(U, L_n)`: systems of glued pairs, one at each order, compatible with reduction modulo
`t^n`. -/
public def sectionsLimit (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) :
    Submodule (AmbientRing k)
      ((n : ℕ) → chartRing k (xVar k) n × chartRing k (yVar k) n) where
  carrier := {s | (∀ n : ℕ, s n ∈ gluedSections k n (transitionElement k a φ n)) ∧
    ∀ n : ℕ, (chartReduction k (xVar k) n (s (n + 1)).1,
      chartReduction k (yVar k) n (s (n + 1)).2) = s n}
  zero_mem' := ⟨fun n => Submodule.zero_mem _, fun n => by simp⟩
  add_mem' := by
    intro s s' hs hs'
    refine ⟨fun n => Submodule.add_mem _ (hs.1 n) (hs'.1 n), fun n => ?_⟩
    have h := hs.2 n
    have h' := hs'.2 n
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add]
    rw [← h, ← h']
    rfl
  smul_mem' := by
    intro c s hs
    refine ⟨fun n => Submodule.smul_mem _ c (hs.1 n), fun n => ?_⟩
    have hsmul : ∀ (r : AmbientRing k) (m : ℕ) (z : chartRing k r (m + 1)),
        chartReduction k r m (c • z) = c • chartReduction k r m z := by
      intro r m z
      rw [← IsScalarTower.algebraMap_smul (Localization.Away r) c z, map_smul,
        IsScalarTower.algebraMap_smul]
    have h := hs.2 n
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, hsmul]
    rw [← h]
    rfl

/-- A system of pairs lies in `sectionsLimit` exactly when each term is a glued section for the
transition element of its order, and each term is the reduction modulo `t^n` of the next. -/
public lemma mem_sectionsLimit_iff (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (s : (n : ℕ) → chartRing k (xVar k) n × chartRing k (yVar k) n) :
    s ∈ sectionsLimit k a φ ↔
      (∀ n : ℕ, s n ∈ gluedSections k n (transitionElement k a φ n)) ∧
      ∀ n : ℕ, (chartReduction k (xVar k) n (s (n + 1)).1,
        chartReduction k (yVar k) n (s (n + 1)).2) = s n := Iff.rfl

/-- The image of `1/r` under restriction along `r * s = q` is `s/q`. -/
private lemma localizationRestrict_invSelf (r s q : AmbientRing k) (hq : r * s = q)
    (h : r ∣ q) :
    localizationRestrict k r q h (IsLocalization.Away.invSelf r) =
      algebraMap (AmbientRing k) (Localization.Away q) s *
        IsLocalization.Away.invSelf q := by
  have hur : IsUnit (algebraMap (AmbientRing k) (Localization.Away q) r) :=
    IsLocalization.Away.isUnit_of_dvd (x := q) h
  refine hur.mul_left_inj.mp ?_
  have h1 : localizationRestrict k r q h (IsLocalization.Away.invSelf r) *
      algebraMap (AmbientRing k) (Localization.Away q) r = 1 := by
    rw [← localizationRestrict_algebraMap k r q h r, ← map_mul,
      mul_comm (IsLocalization.Away.invSelf r), IsLocalization.Away.mul_invSelf, map_one]
  have h2 : algebraMap (AmbientRing k) (Localization.Away q) s *
      IsLocalization.Away.invSelf q *
      algebraMap (AmbientRing k) (Localization.Away q) r = 1 := by
    calc algebraMap (AmbientRing k) (Localization.Away q) s *
          IsLocalization.Away.invSelf q *
          algebraMap (AmbientRing k) (Localization.Away q) r
        = algebraMap (AmbientRing k) (Localization.Away q) r *
            algebraMap (AmbientRing k) (Localization.Away q) s *
            IsLocalization.Away.invSelf q := by ring
      _ = algebraMap (AmbientRing k) (Localization.Away q) q *
            IsLocalization.Away.invSelf q := by rw [← map_mul, hq]
      _ = 1 := IsLocalization.Away.mul_invSelf q
  rw [h1, h2]

/-- **Stacks Project, Tag 0EHE (the glued coordinate function).** The pair consisting of the
function `x` on `D(x)` and the function `x + t/y` on `D(y)`, taken modulo `t^n`. -/
public def coordinateSection (n : ℕ) :
    chartRing k (xVar k) n × chartRing k (yVar k) n :=
  (Ideal.Quotient.mk _ (algebraMap (AmbientRing k) (Localization.Away (xVar k)) (xVar k)),
   Ideal.Quotient.mk _ (algebraMap (AmbientRing k) (Localization.Away (yVar k)) (xVar k) +
     algebraMap (AmbientRing k) (Localization.Away (yVar k)) (tVar k) *
       IsLocalization.Away.invSelf (yVar k)))

/-- Modulo `t^n` the transition element with vanishing higher coefficients is `1 + t/(xy)`. -/
public lemma transitionElement_of_higher_eq_zero (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 0) (n : ℕ) :
    transitionElement k a φ n =
      Ideal.Quotient.mk _ (1 +
        algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) *
          IsLocalization.Away.invSelf (xVar k * yVar k)) := by
  rw [transitionElement,
    Finset.sum_eq_zero fun m hm => by
      simp [ha m (Finset.mem_Ico.mp hm).1], add_zero]

/-- **Stacks Project, Tag 0EHE (the `a_m = 0` case).** For vanishing higher coefficients the
function `x` on `D(x)` and the function `x + t/y` on `D(y)` are matched by the transition
element: on the overlap `(1 + t/(xy)) · x = x + t/y`. -/
public theorem coordinateSection_mem_gluedSections (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 0) (n : ℕ) :
    coordinateSection k n ∈ gluedSections k n (transitionElement k a φ n) := by
  have key :
      localizationRestrict k (yVar k) (xVar k * yVar k) (dvd_mul_left _ _)
          (algebraMap (AmbientRing k) (Localization.Away (yVar k)) (xVar k) +
            algebraMap (AmbientRing k) (Localization.Away (yVar k)) (tVar k) *
              IsLocalization.Away.invSelf (yVar k)) =
        (1 + algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) *
            IsLocalization.Away.invSelf (xVar k * yVar k)) *
          localizationRestrict k (xVar k) (xVar k * yVar k) (dvd_mul_right _ _)
            (algebraMap (AmbientRing k) (Localization.Away (xVar k)) (xVar k)) := by
    rw [map_add, map_mul,
      localizationRestrict_invSelf k (yVar k) (xVar k) (xVar k * yVar k) (mul_comm _ _)
        (dvd_mul_left _ _),
      localizationRestrict_algebraMap, localizationRestrict_algebraMap,
      localizationRestrict_algebraMap]
    ring
  rw [mem_gluedSections_iff, transitionElement_of_higher_eq_zero k a φ ha]
  exact (congrArg (Ideal.Quotient.mk _) key).trans (map_mul _ _ _)

/-- The glued coordinate functions are compatible with reduction modulo `t^n`. -/
public theorem chartReduction_coordinateSection (n : ℕ) :
    (chartReduction k (xVar k) n (coordinateSection k (n + 1)).1,
        chartReduction k (yVar k) n (coordinateSection k (n + 1)).2) =
      coordinateSection k n := by
  simp only [coordinateSection, chartReduction_mk]

private def residue : AmbientRing k →+* k :=
  (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : k) else 0)).comp
    PowerSeries.constantCoeff

private lemma residue_xVar : residue k (xVar k) = 1 := by simp [residue, xVar]

private lemma residue_tVar : residue k (tVar k) = 0 := by simp [residue, tVar]

private def localizedResidue : Localization.Away (xVar k) →+* k :=
  IsLocalization.Away.lift (xVar k) (g := residue k)
    (by rw [residue_xVar]; exact isUnit_one)

@[simp]
private lemma localizedResidue_algebraMap (z : AmbientRing k) :
    localizedResidue k (algebraMap (AmbientRing k) (Localization.Away (xVar k)) z) =
      residue k z :=
  IsLocalization.Away.lift_eq _ _ z

private def quotientResidue (n : ℕ) (hn : 0 < n) : chartRing k (xVar k) n →+* k :=
  Ideal.Quotient.lift _ (localizedResidue k) <| by
    intro z hz
    rw [Ideal.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    rw [map_mul, map_pow, localizedResidue_algebraMap, residue_tVar,
      zero_pow hn.ne', zero_mul]

/-- The glued coordinate function is nonzero at every positive order: its `x`-chart component
has residue `1` at the point `x = 1`, `y = 0`, `t = 0`. -/
public theorem coordinateSection_fst_ne_zero (n : ℕ) (hn : 0 < n) :
    (coordinateSection k n).1 ≠ 0 := by
  intro hz
  have h := congrArg (quotientResidue k n hn) hz
  rw [map_zero] at h
  rw [coordinateSection] at h
  simp only [quotientResidue, Ideal.Quotient.lift_mk, localizedResidue_algebraMap,
    residue_xVar] at h
  exact one_ne_zero h

/-- At every positive order the chart ring `A_x/tⁿA_x` is a nonzero ring: evaluation at the
point `x = 1`, `y = 0`, `t = 0` is a ring map from it to `k`. -/
public theorem nontrivial_chartRing_xVar (n : ℕ) (hn : 0 < n) :
    Nontrivial (chartRing k (xVar k) n) :=
  ⟨1, 0, fun h => one_ne_zero (α := k) (by simpa using congrArg (quotientResidue k n hn) h)⟩

/-- **Stacks Project, Tag 0EHE (nonzero limit of global sections for `a_m = 0`).** When the
higher coefficients `a_m` vanish, the function `x` on `D(x)` and the function `x + t/y` on
`D(y)` glue at every order to a system of glued sections which is compatible with the reductions
modulo `t^n` and is nonzero at every positive order. This is the source's reason that
`lim H⁰(U, L_n)` is nonzero for this choice of coefficients. -/
@[stacks 0EHE "for a_m = 0 the functions x and x + t/y glue to a nonzero compatible system"]
public theorem exists_ne_zero_compatible_mem_gluedSections (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 0) :
    ∃ s : (n : ℕ) → chartRing k (xVar k) n × chartRing k (yVar k) n,
      (∀ n : ℕ, s n ∈ gluedSections k n (transitionElement k a φ n)) ∧
      (∀ n : ℕ, (chartReduction k (xVar k) n (s (n + 1)).1,
        chartReduction k (yVar k) n (s (n + 1)).2) = s n) ∧
      ∀ n : ℕ, 0 < n → s n ≠ 0 :=
  ⟨coordinateSection k, coordinateSection_mem_gluedSections k a φ ha,
    chartReduction_coordinateSection k, fun n hn hz =>
      coordinateSection_fst_ne_zero k n hn (by rw [hz]; rfl)⟩

/-- For vanishing higher coefficients the limit of global sections is nonzero. -/
public theorem sectionsLimit_ne_bot (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 0) : sectionsLimit k a φ ≠ ⊥ := by
  obtain ⟨s, hmem, hcomp, hne⟩ := exists_ne_zero_compatible_mem_gluedSections k a φ ha
  intro hbot
  have hs : s ∈ sectionsLimit k a φ := ⟨hmem, hcomp⟩
  rw [hbot, Submodule.mem_bot] at hs
  exact hne 1 Nat.one_pos (by simp [hs])

/-! ### Laurent expansion of a chart element

A function on the chart `D(r)`, with `r` a monomial in `x` and `y`, is a power series in `t`
whose coefficients are Laurent polynomials in `x` and `y`; on `D(x)` the exponent of `y` stays
nonnegative and on `D(y)` the exponent of `x` does. Reading the gluing relation off in these
coordinates is what shows that the glued module at order two is not free.
-/

/-- The ring `k[x^{±1}, y^{±1}]` of Laurent polynomials in the two plane coordinates. -/
private abbrev LaurentRing : Type u := AddMonoidAlgebra k (ℤ × ℤ)

/-- The exponent pair of a monomial of `k[x,y]`, read in `ℤ × ℤ`. -/
private def exponentPair : (Fin 2 →₀ ℕ) →+ ℤ × ℤ where
  toFun d := ((d 0 : ℤ), (d 1 : ℤ))
  map_zero' := by simp
  map_add' := by intros; simp

/-- A monomial of `k[x,y]` is determined by its exponent pair. -/
private lemma exponentPair_injective : Function.Injective exponentPair := by
  intro d e h
  ext i
  fin_cases i
  · exact_mod_cast (show (d 0 : ℤ) = e 0 from congrArg Prod.fst h)
  · exact_mod_cast (show (d 1 : ℤ) = e 1 from congrArg Prod.snd h)

/-- The inclusion of `k[x,y]` into the Laurent polynomial ring `k[x^{±1}, y^{±1}]`. -/
private def planeToLaurent : PlaneRing k →+* LaurentRing k :=
  AddMonoidAlgebra.mapDomainRingHom k exponentPair

/-- A polynomial is determined by its Laurent expansion. -/
private lemma planeToLaurent_injective : Function.Injective (planeToLaurent k) :=
  AddMonoidAlgebra.mapDomain_injective exponentPair_injective

/-- The two plane coordinates go to the Laurent monomials `x` and `y`. -/
private lemma planeToLaurent_X (i : Fin 2) :
    planeToLaurent k (MvPolynomial.X i) =
      AddMonoidAlgebra.single (if i = 0 then (1, 0) else (0, 1)) 1 := by
  fin_cases i <;>
    simp [planeToLaurent, AddMonoidAlgebra.mapDomainRingHom, MvPolynomial.X,
      MvPolynomial.monomial, AddMonoidAlgebra.lsingle, exponentPair]

/-- A polynomial has no monomial with a negative exponent. -/
private lemma planeToLaurent_coeff_eq_zero (p : PlaneRing k) (z : ℤ × ℤ)
    (hz : z.1 < 0 ∨ z.2 < 0) : (planeToLaurent k p).coeff z = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨d, rfl⟩
  rcases hz with hz | hz <;> simp [exponentPair] at hz <;> omega

/-- Every Laurent monomial is invertible. -/
private lemma isUnit_single (z : ℤ × ℤ) : IsUnit (AddMonoidAlgebra.single z (1 : k)) :=
  IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-z) 1) <| by
    rw [AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def]
    congr 1
    exact add_neg_cancel z

/-- The expansion of a function on the chart `D(r)` as a power series in `t` with Laurent
polynomial coefficients, available once `r` is invertible in `k[x^{±1}, y^{±1}][[t]]`. -/
private def chartExpansion (r : AmbientRing k)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r)) :
    Localization.Away r →+* PowerSeries (LaurentRing k) :=
  IsLocalization.Away.lift r hr

/-- A function coming from `A` expands to its own coefficientwise image. -/
private lemma chartExpansion_algebraMap (r : AmbientRing k)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r)) (b : AmbientRing k) :
    chartExpansion k r hr (algebraMap (AmbientRing k) (Localization.Away r) b) =
      PowerSeries.map (planeToLaurent k) b :=
  IsLocalization.Away.lift_eq r hr b

/-- The `d`-th Laurent coefficient of the expansion of a function on the chart `D(r)`. -/
private def chartCoeff (r : AmbientRing k)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r)) (d : ℕ)
    (z : Localization.Away r) : LaurentRing k :=
  PowerSeries.coeff d (chartExpansion k r hr z)

/-- Functions on `D(r)` agreeing modulo `t^n` have the same expansion coefficients in the
degrees below `n`. -/
private lemma chartCoeff_congr (r : AmbientRing k)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r)) {n d : ℕ} (hd : d < n)
    {z w : Localization.Away r}
    (h : Ideal.Quotient.mk (Ideal.span
          {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n}) z =
        Ideal.Quotient.mk _ w) :
    chartCoeff k r hr d z = chartCoeff k r hr d w := by
  have hmem : z - w ∈ Ideal.span
      {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n} := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have hexp : chartExpansion k r hr (z - w) =
      PowerSeries.X ^ n * chartExpansion k r hr c := by
    rw [hc, map_mul, map_pow, chartExpansion_algebraMap]
    simp [tVar]
  have hzero : PowerSeries.coeff d (chartExpansion k r hr (z - w)) = 0 :=
    PowerSeries.X_pow_dvd_iff.mp ⟨_, hexp⟩ d hd
  rw [map_sub, map_sub, sub_eq_zero] at hzero
  exact hzero

/-- The expansion coefficients in degrees below `n` are stable along a tower of lifts of a
compatible system of classes modulo `t^n`. -/
private lemma chartCoeff_stable (r : AmbientRing k)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r)) (F : ℕ → Localization.Away r)
    (hred : ∀ n : ℕ, (Ideal.Quotient.mk _ (F (n + 1)) : chartRing k r n) =
      Ideal.Quotient.mk _ (F n)) (d n : ℕ) (hdn : d < n) :
    chartCoeff k r hr d (F n) = chartCoeff k r hr d (F (d + 1)) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge d m with h | h
    · exact (chartCoeff_congr k r hr h (hred m)).trans (ih h)
    · rw [show d = m by omega]

/-- Inverse classes modulo `t^n`, `0 < n`, have inverse constant expansion coefficients. -/
private lemma chartCoeff_zero_mul_eq_one (r : AmbientRing k)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r)) {n : ℕ} (hn : 0 < n)
    {F G : Localization.Away r}
    (h : (Ideal.Quotient.mk _ F : chartRing k r n) * Ideal.Quotient.mk _ G = 1) :
    chartCoeff k r hr 0 F * chartCoeff k r hr 0 G = 1 := by
  have h0 := chartCoeff_congr k r hr hn (z := F * G) (w := 1) (by rwa [map_mul, map_one])
  simpa [chartCoeff, PowerSeries.coeff_mul] using h0

/-- On the chart `D(r)` of a monomial `r` with a vanishing exponent, no expansion coefficient
involves a monomial that is negative in that variable. -/
private lemma chartCoeff_coeff_eq_zero (r : AmbientRing k) (v : ℤ × ℤ)
    (hr : PowerSeries.map (planeToLaurent k) r =
      PowerSeries.C (AddMonoidAlgebra.single v 1))
    (hu : IsUnit (PowerSeries.map (planeToLaurent k) r))
    (z : Localization.Away r) (d : ℕ) (w : ℤ × ℤ)
    (hw : (v.1 = 0 ∧ w.1 < 0) ∨ (v.2 = 0 ∧ w.2 < 0)) :
    (chartCoeff k r hu d z).coeff w = 0 := by
  obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj r z
  have he := congrArg (chartExpansion k r hu) hb
  rw [map_mul, map_pow, chartExpansion_algebraMap, chartExpansion_algebraMap, hr,
    ← map_pow, AddMonoidAlgebra.single_pow] at he
  have hc := congrArg (fun q => (PowerSeries.coeff d q).coeff (w + m • v)) he
  simp only [PowerSeries.coeff_mul_C, PowerSeries.coeff_map, one_pow,
    AddMonoidAlgebra.coeff_mul_single_add, mul_one] at hc
  rw [chartCoeff, hc]
  apply planeToLaurent_coeff_eq_zero
  rcases hw with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · left; simpa [hv] using hw
  · right; simpa [hv] using hw

/-- The coordinate `x` expands to the Laurent monomial `x`. -/
private lemma map_xVar : PowerSeries.map (planeToLaurent k) (xVar k) =
    PowerSeries.C (AddMonoidAlgebra.single (1, 0) 1) := by
  simp [xVar, planeToLaurent_X]

/-- The coordinate `y` expands to the Laurent monomial `y`. -/
private lemma map_yVar : PowerSeries.map (planeToLaurent k) (yVar k) =
    PowerSeries.C (AddMonoidAlgebra.single (0, 1) 1) := by
  simp [yVar, planeToLaurent_X]

/-- The product `xy` expands to the Laurent monomial `xy`. -/
private lemma map_xyVar : PowerSeries.map (planeToLaurent k) (xVar k * yVar k) =
    PowerSeries.C (AddMonoidAlgebra.single (1, 1) 1) := by
  rw [map_mul, map_xVar, map_yVar, ← map_mul]
  simp [AddMonoidAlgebra.single_mul_single]

/-- The coordinate `x` becomes invertible in `k[x^{±1}, y^{±1}][[t]]`. -/
private lemma isUnit_map_xVar : IsUnit (PowerSeries.map (planeToLaurent k) (xVar k)) := by
  rw [map_xVar]
  exact (isUnit_single k _).map PowerSeries.C

/-- The coordinate `y` becomes invertible in `k[x^{±1}, y^{±1}][[t]]`. -/
private lemma isUnit_map_yVar : IsUnit (PowerSeries.map (planeToLaurent k) (yVar k)) := by
  rw [map_yVar]
  exact (isUnit_single k _).map PowerSeries.C

/-- The product `xy` becomes invertible in `k[x^{±1}, y^{±1}][[t]]`. -/
private lemma isUnit_map_xyVar :
    IsUnit (PowerSeries.map (planeToLaurent k) (xVar k * yVar k)) := by
  rw [map_xyVar]
  exact (isUnit_single k _).map PowerSeries.C

/-- Restricting a function to a smaller chart does not change its expansion. -/
private lemma chartExpansion_localizationRestrict (r q : AmbientRing k) (hdvd : r ∣ q)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r))
    (hq : IsUnit (PowerSeries.map (planeToLaurent k) q))
    (z : Localization.Away r) :
    chartExpansion k q hq (localizationRestrict k r q hdvd z) =
      chartExpansion k r hr z := by
  have hcomp : (chartExpansion k q hq).comp
      (localizationRestrict k r q hdvd : Localization.Away r →+* Localization.Away q) =
      chartExpansion k r hr := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext b
    simp [chartExpansion_algebraMap]
  exact DFunLike.congr_fun hcomp z

/-- Restricting a function to a smaller chart does not change its expansion coefficients. -/
private lemma chartCoeff_localizationRestrict (r q : AmbientRing k) (hdvd : r ∣ q)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r))
    (hq : IsUnit (PowerSeries.map (planeToLaurent k) q)) (d : ℕ)
    (z : Localization.Away r) :
    chartCoeff k q hq d (localizationRestrict k r q hdvd z) = chartCoeff k r hr d z := by
  rw [chartCoeff, chartCoeff, chartExpansion_localizationRestrict]

/-- The `d`-th Laurent coefficient of a function on the chart `D(x)`. -/
private abbrev xCoeff (d : ℕ) (z : Localization.Away (xVar k)) : LaurentRing k :=
  chartCoeff k (xVar k) (isUnit_map_xVar k) d z

/-- The `d`-th Laurent coefficient of a function on the chart `D(y)`. -/
private abbrev yCoeff (d : ℕ) (z : Localization.Away (yVar k)) : LaurentRing k :=
  chartCoeff k (yVar k) (isUnit_map_yVar k) d z

/-- The `d`-th Laurent coefficient of a function on the overlap `D(xy)`. -/
private abbrev xyCoeff (d : ℕ) (z : Localization.Away (xVar k * yVar k)) : LaurentRing k :=
  chartCoeff k (xVar k * yVar k) (isUnit_map_xyVar k) d z

/-- On `D(x)` no expansion coefficient involves a negative power of `y`. -/
private lemma xCoeff_coeff_eq_zero (d : ℕ) (z : Localization.Away (xVar k)) (w : ℤ × ℤ)
    (hw : w.2 < 0) : (xCoeff k d z).coeff w = 0 :=
  chartCoeff_coeff_eq_zero k (xVar k) (1, 0) (map_xVar k) _ z d w (Or.inr ⟨rfl, hw⟩)

/-- On `D(y)` no expansion coefficient involves a negative power of `x`. -/
private lemma yCoeff_coeff_eq_zero (d : ℕ) (z : Localization.Away (yVar k)) (w : ℤ × ℤ)
    (hw : w.1 < 0) : (yCoeff k d z).coeff w = 0 :=
  chartCoeff_coeff_eq_zero k (yVar k) (0, 1) (map_yVar k) _ z d w (Or.inl ⟨rfl, hw⟩)

/-- Functions on `D(xy)` agreeing modulo `t²` have the same coefficients in degrees `0`
and `1`. -/
private lemma xyCoeff_congr {d : ℕ} (hd : d < 2)
    {z w : Localization.Away (xVar k * yVar k)}
    (h : (Ideal.Quotient.mk _ z : chartRing k (xVar k * yVar k) 2) =
      Ideal.Quotient.mk _ w) :
    xyCoeff k d z = xyCoeff k d w := chartCoeff_congr k _ _ hd h

/-- The expansion coefficients of a function on `D(x)` survive restriction to the overlap. -/
private lemma xyCoeff_xRestrict (d : ℕ) (z : Localization.Away (xVar k)) :
    xyCoeff k d
        (localizationRestrict k (xVar k) (xVar k * yVar k) (dvd_mul_right _ _) z) =
      xCoeff k d z :=
  chartCoeff_localizationRestrict k _ _ _ (isUnit_map_xVar k) (isUnit_map_xyVar k) d z

/-- The expansion coefficients of a function on `D(y)` survive restriction to the overlap. -/
private lemma xyCoeff_yRestrict (d : ℕ) (z : Localization.Away (yVar k)) :
    xyCoeff k d
        (localizationRestrict k (yVar k) (xVar k * yVar k) (dvd_mul_left _ _) z) =
      yCoeff k d z :=
  chartCoeff_localizationRestrict k _ _ _ (isUnit_map_yVar k) (isUnit_map_xyVar k) d z

/-- Representatives of a glued section for the class of `u` are matched by `u` on the overlap. -/
private lemma mk_restrict_eq_mul_of_mem_gluedSections {n : ℕ}
    (u : Localization.Away (xVar k * yVar k))
    {s : chartRing k (xVar k) n × chartRing k (yVar k) n}
    (hs : s ∈ gluedSections k n (Ideal.Quotient.mk _ u))
    {F : Localization.Away (xVar k)} {H : Localization.Away (yVar k)}
    (hF : Ideal.Quotient.mk _ F = s.1) (hH : Ideal.Quotient.mk _ H = s.2) :
    (Ideal.Quotient.mk _ (localizationRestrict k (yVar k) (xVar k * yVar k)
          (dvd_mul_left _ _) H) : chartRing k (xVar k * yVar k) n) =
      Ideal.Quotient.mk _ (u * localizationRestrict k (xVar k) (xVar k * yVar k)
        (dvd_mul_right _ _) F) := by
  rw [mem_gluedSections_iff, ← hF, ← hH] at hs
  simpa only [yChartToOverlap, xChartToOverlap, chartRestrict_mk, ← map_mul] using hs

/-- The function `1/(xy)` on the overlap expands to the Laurent monomial `x⁻¹y⁻¹`. -/
private lemma chartExpansion_invSelf :
    chartExpansion k (xVar k * yVar k) (isUnit_map_xyVar k)
        (IsLocalization.Away.invSelf (xVar k * yVar k)) =
      PowerSeries.C (AddMonoidAlgebra.single (-1, -1) 1) := by
  have hmono : AddMonoidAlgebra.single ((1 : ℤ), (1 : ℤ)) (1 : k) *
      AddMonoidAlgebra.single ((-1 : ℤ), (-1 : ℤ)) (1 : k) = 1 := by
    rw [AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def]
    congr 1
  have hinv : PowerSeries.C (AddMonoidAlgebra.single ((1 : ℤ), (1 : ℤ)) (1 : k)) *
      PowerSeries.C (AddMonoidAlgebra.single ((-1 : ℤ), (-1 : ℤ)) (1 : k)) = 1 := by
    rw [← map_mul, hmono, map_one]
  have hone : chartExpansion k (xVar k * yVar k) (isUnit_map_xyVar k)
      (algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (xVar k * yVar k) *
        IsLocalization.Away.invSelf (xVar k * yVar k)) = 1 := by
    rw [IsLocalization.Away.mul_invSelf, map_one]
  rw [map_mul, chartExpansion_algebraMap, map_xyVar] at hone
  exact (IsUnit.of_mul_eq_one _ hinv).mul_left_cancel (hone.trans hinv.symm)

/-- The lift `1 + t/(xy)` to the overlap of the order-two transition element. -/
private def overlapUnitTwo : Localization.Away (xVar k * yVar k) :=
  1 + algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) *
    IsLocalization.Away.invSelf (xVar k * yVar k)

/-- Modulo `t²` the transition element is `1 + t/(xy)`, whatever the higher coefficients are. -/
private lemma transitionElement_two (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) :
    transitionElement k a φ 2 = Ideal.Quotient.mk _ (overlapUnitTwo k) := by
  simp [transitionElement, overlapUnitTwo]

/-- The expansion of `1 + t/(xy)` is `1 + x⁻¹y⁻¹t`. -/
private lemma chartExpansion_overlapUnitTwo :
    chartExpansion k (xVar k * yVar k) (isUnit_map_xyVar k) (overlapUnitTwo k) =
      1 + PowerSeries.X * PowerSeries.C (AddMonoidAlgebra.single (-1, -1) (1 : k)) := by
  rw [overlapUnitTwo, map_add, map_one, map_mul, chartExpansion_algebraMap,
    chartExpansion_invSelf]
  simp [tVar]

/-- Multiplying by `1 + t/(xy)` leaves the constant coefficient of an expansion unchanged. -/
private lemma xyCoeff_overlapUnitTwo_mul_zero (w : Localization.Away (xVar k * yVar k)) :
    xyCoeff k 0 (overlapUnitTwo k * w) = xyCoeff k 0 w := by
  simp only [chartCoeff, map_mul, chartExpansion_overlapUnitTwo]
  simp [PowerSeries.coeff_mul]

/-- Multiplying by `1 + t/(xy)` adds `x⁻¹y⁻¹` times the constant coefficient to the linear
coefficient. -/
private lemma xyCoeff_overlapUnitTwo_mul_one (w : Localization.Away (xVar k * yVar k)) :
    xyCoeff k 1 (overlapUnitTwo k * w) =
      xyCoeff k 1 w +
        AddMonoidAlgebra.single (-1, -1) (1 : k) * xyCoeff k 0 w := by
  simp only [chartCoeff, map_mul, chartExpansion_overlapUnitTwo]
  simp [PowerSeries.coeff_mul, Finset.antidiagonal]

/-- Two Laurent polynomials with no negative exponents whose product is `1` both have a nonzero
constant term. -/
private lemma coeff_zero_ne_zero_of_mul_eq_one (p q : LaurentRing k)
    (hp : ∀ z : ℤ × ℤ, z.1 < 0 ∨ z.2 < 0 → p.coeff z = 0)
    (hq : ∀ z : ℤ × ℤ, z.1 < 0 ∨ z.2 < 0 → q.coeff z = 0)
    (hpq : p * q = 1) : p.coeff 0 ≠ 0 := by
  classical
  intro hp0
  have hz : (p * q).coeff 0 = 0 := by
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    apply Finset.sum_eq_zero
    intro z _
    change p.coeff z * q.coeff (-z + 0) = 0
    by_cases hneg : z.1 < 0 ∨ z.2 < 0
    · rw [hp z hneg, zero_mul]
    · by_cases hz0 : z = 0
      · rw [hz0, hp0, zero_mul]
      · have hpos : (-z + 0).1 < 0 ∨ (-z + 0).2 < 0 := by
          simp only [add_zero, Prod.fst_neg, Prod.snd_neg]
          have hne : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
            contrapose! hz0
            exact Prod.ext hz0.1 hz0.2
          omega
        rw [hq _ hpos, mul_zero]
  rw [hpq] at hz
  have hone : (1 : LaurentRing k).coeff 0 = 1 := by
    rw [AddMonoidAlgebra.one_def]
    exact Finsupp.single_eq_same
  rw [hone] at hz
  exact one_ne_zero hz

/-- **Stacks Project, Tag 0EHE (nontriviality of the glued module at order two).** The glued
module at order two is not free: no pair consisting of an invertible function on `D(x)` and an
invertible function on `D(y)`, both taken modulo `t²`, is matched by the transition element. The
obstruction is that `1/(xy)` is not a sum of a function on `D(x)` and a function on `D(y)`. -/
@[stacks 0EHE "modulo t^2 no pair of invertible chart functions is matched"]
public theorem not_isUnit_of_mem_gluedSections_two (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (s : chartRing k (xVar k) 2 × chartRing k (yVar k) 2)
    (hs : s ∈ gluedSections k 2 (transitionElement k a φ 2)) :
    ¬ (IsUnit s.1 ∧ IsUnit s.2) := by
  rintro ⟨hfst, hsnd⟩
  obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective s.1
  obtain ⟨H, hH⟩ := Ideal.Quotient.mk_surjective s.2
  obtain ⟨finv, hfinv⟩ := hfst.exists_right_inv
  obtain ⟨Finv, hFinv⟩ := Ideal.Quotient.mk_surjective finv
  obtain ⟨ginv, hginv⟩ := hsnd.exists_right_inv
  obtain ⟨Ginv, hGinv⟩ := Ideal.Quotient.mk_surjective ginv
  have hglue := mk_restrict_eq_mul_of_mem_gluedSections k (overlapUnitTwo k)
    (transitionElement_two k a φ ▸ hs) hF hH
  -- the constant coefficients of the two charts agree on the overlap
  have hconst : yCoeff k 0 H = xCoeff k 0 F := by
    have h := xyCoeff_congr k (d := 0) (by omega) hglue
    rwa [xyCoeff_yRestrict, xyCoeff_overlapUnitTwo_mul_zero, xyCoeff_xRestrict] at h
  -- the linear coefficients differ by `1/(xy)` times the constant one
  have hlin : yCoeff k 1 H =
      xCoeff k 1 F + AddMonoidAlgebra.single (-1, -1) (1 : k) * xCoeff k 0 F := by
    have h := xyCoeff_congr k (d := 1) (by omega) hglue
    rwa [xyCoeff_yRestrict, xyCoeff_overlapUnitTwo_mul_one, xyCoeff_xRestrict,
      xyCoeff_xRestrict] at h
  -- invertibility makes the common constant coefficient invertible on each chart
  have hFmul : xCoeff k 0 F * xCoeff k 0 Finv = 1 :=
    chartCoeff_zero_mul_eq_one k _ _ two_pos (by rw [hF, hFinv, hfinv])
  have hHmul : yCoeff k 0 H * yCoeff k 0 Ginv = 1 :=
    chartCoeff_zero_mul_eq_one k _ _ two_pos (by rw [hH, hGinv, hginv])
  have hHmul' : xCoeff k 0 F * yCoeff k 0 Ginv = 1 := by rw [← hconst]; exact hHmul
  have hinv : xCoeff k 0 Finv = yCoeff k 0 Ginv :=
    (IsUnit.of_mul_eq_one _ hFmul).mul_left_cancel (hFmul.trans hHmul'.symm)
  -- so it has no negative exponents, and neither has its inverse
  have hsupp : ∀ (F' : Localization.Away (xVar k)) (H' : Localization.Away (yVar k)),
      yCoeff k 0 H' = xCoeff k 0 F' → ∀ z : ℤ × ℤ, z.1 < 0 ∨ z.2 < 0 →
        (xCoeff k 0 F').coeff z = 0 := by
    intro F' H' h z hz
    rcases hz with hz | hz
    · rw [← h]
      exact yCoeff_coeff_eq_zero k 0 H' z hz
    · exact xCoeff_coeff_eq_zero k 0 F' z hz
  have hne : (xCoeff k 0 F).coeff 0 ≠ 0 :=
    coeff_zero_ne_zero_of_mul_eq_one k _ _ (hsupp F H hconst) (hsupp Finv Ginv hinv.symm) hFmul
  -- the linear relation at the monomial `x⁻¹y⁻¹` says the opposite
  apply hne
  have hy1 : (yCoeff k 1 H).coeff ((-1 : ℤ), (-1 : ℤ)) = 0 :=
    yCoeff_coeff_eq_zero k 1 H _ (by norm_num)
  have hx1 : (xCoeff k 1 F).coeff ((-1 : ℤ), (-1 : ℤ)) = 0 :=
    xCoeff_coeff_eq_zero k 1 F _ (by norm_num)
  have h : (yCoeff k 1 H).coeff ((-1 : ℤ), (-1 : ℤ)) =
      (xCoeff k 1 F).coeff ((-1 : ℤ), (-1 : ℤ)) +
        (AddMonoidAlgebra.single ((-1 : ℤ), (-1 : ℤ)) (1 : k) * xCoeff k 0 F).coeff
          ((-1 : ℤ), (-1 : ℤ)) := by
    rw [hlin]
    simp
  rw [hy1, hx1, zero_add, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
    neg_add_cancel] at h
  exact h.symm

/-! ### Vanishing of the limit of glued sections for growing exponents

Take every higher coefficient to be `1`. Reading the gluing relation in Laurent coordinates
turns it into a convolution: the `N`-th coefficient of the `D(y)`-chart component is the sum
over `j ≤ N` of `(xy)^{-ψ(j)}` times the `(N - j)`-th coefficient of the `D(x)`-chart
component, where `ψ` is the exponent sequence `0, 1, φ(2), φ(3), …` of the transition series.
Once the gaps of `ψ` exceed every bound — as they do for `φ(m) = 2^m` and for `φ(m) = m²` — a
single term of that convolution carries a monomial that no other term and no chart function can
match, and every coefficient is forced to vanish.
-/

/-- The exponent of `1/(xy)` carried by the `t^j` term of the transition series. The series
begins `1 + t/(xy)`, so the exponents at `j = 0` and `j = 1` are `0` and `1`. -/
private def transitionExponent (φ : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then 1 else φ j

/-- Past the first two terms the exponent sequence of the transition series is `φ` itself. -/
private lemma transitionExponent_of_two_le (φ : ℕ → ℕ) {j : ℕ} (hj : 2 ≤ j) :
    transitionExponent φ j = φ j := by
  simp [transitionExponent, show j ≠ 0 by omega, show j ≠ 1 by omega]

/-- **The parameter condition of [Stacks, Tag 0EHE] on the exponents.** The exponents `φ(m)` of
the transition series *separate degrees*: for every bound `p` there is an index `n ≥ 2` whose
exponent exceeds `p` and exceeds `p` plus every earlier exponent. This is what the vanishing of
`lim H⁰(U, 𝓛ₙ)` needs of `φ`, and it is satisfied by both of the source's prescriptions
`φ(m) = 2ᵐ` and `φ(m) = m²` (`hasSeparatedExponents_of_eq_two_pow_or_sq`).

The *first* proof of non-algebraizability — the one through `Pic(U)` and the nontriviality of
`𝓛₂` — uses no condition on the parameters at all; see
`not_isUnit_of_mem_gluedSections_two`. -/
public def HasSeparatedExponents (φ : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, ∃ n : ℕ, 2 ≤ n ∧ p < φ n ∧ ∀ j : ℕ, 2 ≤ j → j < n → p + φ j < φ n

/-- **Stacks Project, Tag 0EHE (both prescribed growth rates separate degrees).** The exponents
`φ(m) = 2ᵐ` and the exponents `φ(m) = m²` both satisfy `HasSeparatedExponents`: the index
`n = p + 3` works for either, since `p < 2^{p+2}` and `p < 2p + 5`. -/
@[stacks 0EHE "phi(m) = 2^m and phi(m) = m^2 separate degrees"]
public theorem hasSeparatedExponents_of_eq_two_pow_or_sq {φ : ℕ → ℕ}
    (hφ : (∀ m : ℕ, 2 ≤ m → φ m = 2 ^ m) ∨ (∀ m : ℕ, 2 ≤ m → φ m = m ^ 2)) :
    HasSeparatedExponents φ := by
  intro p
  refine ⟨p + 3, by omega, ?_, ?_⟩
  · rcases hφ with hexp | hquad
    · rw [hexp _ (by omega)]
      have h1 : p < 2 ^ p := Nat.lt_two_pow_self
      have h2 : 2 ^ p ≤ 2 ^ (p + 3) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      omega
    · rw [hquad _ (by omega)]
      nlinarith
  · intro j hj2 hjn
    rcases hφ with hexp | hquad
    · rw [hexp j hj2, hexp (p + 3) (by omega)]
      have h1 : (2 : ℕ) ^ j ≤ 2 ^ (p + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : p < 2 ^ p := Nat.lt_two_pow_self
      have h3 : (2 : ℕ) ^ p ≤ 2 ^ (p + 2) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      have h4 : (2 : ℕ) ^ (p + 3) = 2 ^ (p + 2) * 2 := by
        rw [show p + 3 = (p + 2) + 1 from by omega, Nat.pow_succ]
      omega
    · rw [hquad j hj2, hquad (p + 3) (by omega)]
      have h1 : j ^ 2 ≤ (p + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : (p + 3) ^ 2 = (p + 2) ^ 2 + (2 * p + 5) := by nlinarith
      omega

/-- The exponent sequence `0, 1, φ(2), φ(3), …` of the transition series separates degrees as
soon as `φ` does: for any two bounds there is an index whose exponent exceeds the first and
exceeds every earlier exponent shifted by the second. -/
private lemma transitionExponent_gap {φ : ℕ → ℕ} (hφ : HasSeparatedExponents φ) (p q : ℤ) :
    ∃ n : ℕ, p < transitionExponent φ n ∧
      ∀ j < n, q + transitionExponent φ j < transitionExponent φ n := by
  obtain ⟨n, hn2, hnp, hmono⟩ := hφ (max p.toNat q.toNat + 1)
  have hp : p ≤ (max p.toNat q.toNat : ℕ) := by omega
  have hq : q ≤ (max p.toNat q.toNat : ℕ) := by omega
  refine ⟨n, ?_, ?_⟩
  · rw [transitionExponent_of_two_le φ hn2]
    omega
  · intro j hj
    rw [transitionExponent_of_two_le φ (j := n) hn2]
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj01 : j = 0 ∨ j = 1 := by omega
      rcases hj01 with rfl | rfl
      · rw [show transitionExponent φ 0 = 0 from by simp [transitionExponent]]
        omega
      · rw [show transitionExponent φ 1 = 1 from by simp [transitionExponent]]
        omega
    · rw [transitionExponent_of_two_le φ hj2]
      have hb := hmono j hj2 hj
      omega

/-- A convolution recurrence in `k[x^{±1}, y^{±1}]` whose exponent sequence has unbounded gaps
has only the zero solution: if the `f`-terms carry no negative power of `y`, the `g`-terms no
negative power of `x`, and `g N = ∑_{j ≤ N} (xy)^{-ψ(j)} f(N - j)`, then every `f` vanishes. -/
private lemma laurent_recurrence_eq_zero (ψ : ℕ → ℕ)
    (hgap : ∀ p q : ℤ, ∃ n : ℕ, p < ψ n ∧ ∀ j < n, q + ψ j < ψ n)
    (f g : ℕ → LaurentRing k)
    (hf : ∀ (n : ℕ) (z : ℤ × ℤ), z.2 < 0 → (f n).coeff z = 0)
    (hg : ∀ (n : ℕ) (z : ℤ × ℤ), z.1 < 0 → (g n).coeff z = 0)
    (heq : ∀ N : ℕ, g N = ∑ j ∈ Finset.range (N + 1),
      AddMonoidAlgebra.single (-(ψ j : ℤ), -(ψ j : ℤ)) (1 : k) * f (N - j)) :
    ∀ d : ℕ, f d = 0 := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    apply AddMonoidAlgebra.ext
    ext z
    obtain ⟨n, hnx, hny⟩ := hgap z.1 z.2
    have hz : (g (n + d)).coeff (z.1 - ψ n, z.2 - ψ n) = 0 := hg _ _ (by dsimp; omega)
    rw [heq] at hz
    have hs : (∑ j ∈ Finset.range (n + d + 1),
        AddMonoidAlgebra.single (-(ψ j : ℤ), -(ψ j : ℤ)) (1 : k) * f (n + d - j)).coeff
          (z.1 - ψ n, z.2 - ψ n) = (f d).coeff z := by
      simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single n]
      · simp only [Nat.add_sub_cancel_left, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
        congr 1
        ext <;> simp
      · intro j hj hjn
        have hjle : j ≤ n + d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        by_cases hjn' : j < n
        · rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
          apply hf
          have := hny j hjn'
          dsimp
          omega
        · rw [ih (n + d - j) (by omega), mul_zero]
          rfl
      · intro hn
        exact False.elim (hn (by simp))
    rwa [hs] at hz

/-- Not every expansion coefficient below the order can vanish on a nonzero class: a chart
function all of whose Laurent coefficients in degrees `< n` vanish is divisible by `t^n`. -/
private lemma chartClass_eq_zero (r : AmbientRing k)
    (hr : IsUnit (PowerSeries.map (planeToLaurent k) r)) (n : ℕ) (z : Localization.Away r)
    (hz : ∀ d : ℕ, d < n → chartCoeff k r hr d z = 0) :
    (Ideal.Quotient.mk (Ideal.span
        {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n}) z :
      chartRing k r n) = 0 := by
  obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj r z
  have hdiv : PowerSeries.X ^ n ∣ chartExpansion k r hr z :=
    PowerSeries.X_pow_dvd_iff.mpr hz
  have hh := congrArg (chartExpansion k r hr) hb
  rw [map_mul, map_pow, chartExpansion_algebraMap, chartExpansion_algebraMap] at hh
  have hdivb : PowerSeries.X ^ n ∣ b := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun d hd => planeToLaurent_injective k ?_
    rw [map_zero, ← PowerSeries.coeff_map]
    exact PowerSeries.X_pow_dvd_iff.mp (hh ▸ dvd_mul_of_dvd_left hdiv _) d hd
  obtain ⟨b', hb'⟩ := hdivb
  have hzero : Ideal.Quotient.mk (Ideal.span
      {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n})
      (algebraMap (AmbientRing k) (Localization.Away r) b) = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ?_)
    rw [hb', map_mul, map_pow]
    exact dvd_mul_right _ _
  have hu := ((IsLocalization.Away.algebraMap_isUnit r).pow m).map
    (Ideal.Quotient.mk (Ideal.span
      {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n}))
  refine hu.mul_right_cancel ?_
  rwa [zero_mul, ← map_mul, hb]

/-- The lift to `A_{xy}` of the truncated transition series. -/
private def transitionLift (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    Localization.Away (xVar k * yVar k) :=
  1 + algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) *
      IsLocalization.Away.invSelf (xVar k * yVar k) +
    ∑ m ∈ Finset.Ico 2 n,
      algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k))
          (PowerSeries.C (a m)) *
        algebraMap (AmbientRing k) (Localization.Away (xVar k * yVar k)) (tVar k) ^ m *
        IsLocalization.Away.invSelf (xVar k * yVar k) ^ φ m

/-- The transition element is the class of its lift. -/
private lemma transitionElement_eq_mk (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    transitionElement k a φ n = Ideal.Quotient.mk _ (transitionLift k a φ n) := rfl

/-- With all higher coefficients equal to `1` the transition series expands as the truncated
sum `∑_{j < n} (xy)^{-ψ(j)} t^j`, with `ψ` the exponent sequence of the series. -/
private lemma chartExpansion_transitionLift (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 1) {n : ℕ} (hn : 2 ≤ n) :
    chartExpansion k (xVar k * yVar k) (isUnit_map_xyVar k) (transitionLift k a φ n) =
      ∑ j ∈ Finset.range n,
        PowerSeries.C (AddMonoidAlgebra.single
            (-(transitionExponent φ j : ℤ), -(transitionExponent φ j : ℤ)) (1 : k)) *
          PowerSeries.X ^ j := by
  have hsplit (h : ℕ → PowerSeries (LaurentRing k)) :
      ∑ j ∈ Finset.range n, h j = h 0 + h 1 + ∑ j ∈ Finset.Ico 2 n, h j := by
    rw [Finset.sum_Ico_eq_sub _ hn]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    abel
  rw [hsplit]
  simp only [transitionLift, map_add, map_one, map_mul, map_sum, map_pow,
    chartExpansion_algebraMap, chartExpansion_invSelf, tVar, PowerSeries.map_X]
  have h0 : (PowerSeries.C (AddMonoidAlgebra.single
      (-(transitionExponent φ 0 : ℤ), -(transitionExponent φ 0 : ℤ)) (1 : k)) *
        PowerSeries.X ^ 0) = 1 := by
    simp only [transitionExponent, ↓reduceIte, Nat.cast_zero, neg_zero, pow_zero, mul_one]
    change PowerSeries.C (1 : LaurentRing k) = 1
    simp
  rw [h0]
  congr 1
  · simp [transitionExponent, mul_comm]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj2 := (Finset.mem_Ico.mp hj).1
    rw [ha j hj2, PowerSeries.map_C, map_one, map_one, one_mul,
      transitionExponent_of_two_le φ hj2, ← map_pow, AddMonoidAlgebra.single_pow]
    simp [mul_comm]

/-- Below the truncation order, multiplying by a truncated polynomial in `t` is a convolution
of coefficients. -/
private lemma coeff_truncated_mul {A : Type u} [CommRing A] (h : ℕ → A) (q : PowerSeries A)
    {n d : ℕ} (hd : d < n) :
    PowerSeries.coeff d
        ((∑ j ∈ Finset.range n, PowerSeries.C (h j) * PowerSeries.X ^ j) * q) =
      ∑ j ∈ Finset.range (d + 1), h j * PowerSeries.coeff (d - j) q := by
  classical
  simp only [Finset.sum_mul, map_sum, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  symm
  trans ∑ j ∈ Finset.range (d + 1),
    h j * if j ≤ d then PowerSeries.coeff (d - j) q else 0
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp [hjd]
  · refine Finset.sum_subset (Finset.range_mono hd) fun j hj hnot => ?_
    have hdj : ¬ j ≤ d := by simpa using hnot
    simp [hdj]

/-- The gluing relation in Laurent coordinates: below the truncation order, the coefficients of
the transition series times a function on the overlap are a convolution. -/
private lemma xyCoeff_transitionLift_mul (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 1) {n d : ℕ} (hn : 2 ≤ n) (hd : d < n)
    (w : Localization.Away (xVar k * yVar k)) :
    xyCoeff k d (transitionLift k a φ n * w) =
      ∑ j ∈ Finset.range (d + 1),
        AddMonoidAlgebra.single
            (-(transitionExponent φ j : ℤ), -(transitionExponent φ j : ℤ)) (1 : k) *
          xyCoeff k (d - j) w := by
  simp only [chartCoeff, map_mul]
  rw [chartExpansion_transitionLift k a φ ha hn, coeff_truncated_mul _ _ hd]

/-- When every higher coefficient `a_m` is `1` and the exponents separate degrees, the only
compatible system of glued sections is the zero one. -/
public theorem eq_zero_of_compatible_mem_gluedSections (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 1) (hφ : HasSeparatedExponents φ)
    (s : (n : ℕ) → chartRing k (xVar k) n × chartRing k (yVar k) n)
    (hs : ∀ n : ℕ, s n ∈ gluedSections k n (transitionElement k a φ n))
    (hred : ∀ n : ℕ, (chartReduction k (xVar k) n (s (n + 1)).1,
      chartReduction k (yVar k) n (s (n + 1)).2) = s n) :
    ∀ n : ℕ, s n = 0 := by
  classical
  choose F hF using fun n : ℕ => Ideal.Quotient.mk_surjective (I :=
    Ideal.span {(algebraMap (AmbientRing k) (Localization.Away (xVar k)) (tVar k)) ^ n})
    (s n).1
  choose H hH using fun n : ℕ => Ideal.Quotient.mk_surjective (I :=
    Ideal.span {(algebraMap (AmbientRing k) (Localization.Away (yVar k)) (tVar k)) ^ n})
    (s n).2
  have hFstab : ∀ d n : ℕ, d < n → xCoeff k d (F n) = xCoeff k d (F (d + 1)) :=
    chartCoeff_stable k (xVar k) (isUnit_map_xVar k) F fun n => by
      have h := congrArg Prod.fst (hred n)
      rwa [← hF (n + 1), ← hF n, chartReduction_mk] at h
  have hHstab : ∀ d n : ℕ, d < n → yCoeff k d (H n) = yCoeff k d (H (d + 1)) :=
    chartCoeff_stable k (yVar k) (isUnit_map_yVar k) H fun n => by
      have h := congrArg Prod.snd (hred n)
      rwa [← hH (n + 1), ← hH n, chartReduction_mk] at h
  have hrec : ∀ N : ℕ, yCoeff k N (H (N + 1)) = ∑ j ∈ Finset.range (N + 1),
      AddMonoidAlgebra.single
          (-(transitionExponent φ j : ℤ), -(transitionExponent φ j : ℤ)) (1 : k) *
        xCoeff k (N - j) (F (N - j + 1)) := by
    intro N
    have h := chartCoeff_congr k (xVar k * yVar k) (isUnit_map_xyVar k)
      (show N < N + 2 by omega)
      (mk_restrict_eq_mul_of_mem_gluedSections k (transitionLift k a φ (N + 2)) (hs (N + 2))
        (hF (N + 2)) (hH (N + 2)))
    have hsum := xyCoeff_transitionLift_mul k a φ ha (show (2 : ℕ) ≤ N + 2 by omega)
      (show N < N + 2 by omega)
      (localizationRestrict k (xVar k) (xVar k * yVar k) (dvd_mul_right _ _) (F (N + 2)))
    refine (hHstab N (N + 2) (by omega)).symm.trans ?_
    refine (xyCoeff_yRestrict k N (H (N + 2))).symm.trans (h.trans (hsum.trans ?_))
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun w : LaurentRing k => AddMonoidAlgebra.single
        (-(transitionExponent φ j : ℤ), -(transitionExponent φ j : ℤ)) (1 : k) * w)
      ((xyCoeff_xRestrict k (N - j) (F (N + 2))).trans
        (hFstab (N - j) (N + 2) (by omega)))
  have hfzero : ∀ d : ℕ, xCoeff k d (F (d + 1)) = 0 :=
    laurent_recurrence_eq_zero k (transitionExponent φ) (transitionExponent_gap hφ)
      (fun d => xCoeff k d (F (d + 1))) (fun d => yCoeff k d (H (d + 1)))
      (fun d z hz => xCoeff_coeff_eq_zero k d (F (d + 1)) z hz)
      (fun d z hz => yCoeff_coeff_eq_zero k d (H (d + 1)) z hz) hrec
  have hgzero : ∀ d : ℕ, yCoeff k d (H (d + 1)) = 0 := by
    intro d
    rw [hrec d]
    simp [hfzero]
  intro n
  have h1 : (s n).1 = 0 := by
    rw [← hF n]
    exact chartClass_eq_zero k (xVar k) (isUnit_map_xVar k) n (F n) fun d hd =>
      (hFstab d n hd).trans (hfzero d)
  have h2 : (s n).2 = 0 := by
    rw [← hH n]
    exact chartClass_eq_zero k (yVar k) (isUnit_map_yVar k) n (H n) fun d hd =>
      (hHstab d n hd).trans (hgzero d)
  exact Prod.ext h1 h2

/-- When every higher coefficient `a_m` is `1` and the exponents separate degrees, the limit
`lim H⁰(U, L_n)` of the global sections of the glued modules is zero. This is the form of
`sectionsLimit_eq_bot` the source's two prescriptions `φ(m) = 2^m` and `φ(m) = m²` factor
through. -/
public theorem sectionsLimit_eq_bot_of_hasSeparatedExponents (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 1) (hφ : HasSeparatedExponents φ) :
    sectionsLimit k a φ = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun s hs => ?_
  funext n
  exact eq_zero_of_compatible_mem_gluedSections k a φ ha hφ s hs.1 hs.2 n

/-- **Stacks Project, Tag 0EHE (vanishing limit of global sections).** When every higher
coefficient `a_m` is `1` and the exponents are `φ(m) = 2^m` or `φ(m) = m²`, the limit
`lim H⁰(U, L_n)` of the global sections of the glued modules is zero. -/
@[stacks 0EHE "lim H^0(U, L_n) = 0 for a_m = 1 and φ(m) = 2^m or m^2"]
public theorem sectionsLimit_eq_bot (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 1)
    (hφ : (∀ m : ℕ, 2 ≤ m → φ m = 2 ^ m) ∨ (∀ m : ℕ, 2 ≤ m → φ m = m ^ 2)) :
    sectionsLimit k a φ = ⊥ :=
  sectionsLimit_eq_bot_of_hasSeparatedExponents k a φ ha
    (hasSeparatedExponents_of_eq_two_pow_or_sq hφ)

end Stacks.Algebraization.NonAlgebraizableExample

end
