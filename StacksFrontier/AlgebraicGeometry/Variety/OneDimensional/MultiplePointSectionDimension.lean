module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafSum
public import StacksFrontier.AlgebraicGeometry.Divisors.MultiplePointCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# The sections of a multiple of a closed point on a curve

Let `k` be a field, let `Y` be a proper curve over `k` which is locally Noetherian and integral,
and let `y` be a closed point of `Y` at which the local ring `𝒪_{Y,y}` is a discrete valuation
ring. Then `(N+1)·y` is an effective Cartier divisor, and for the inclusion `i` of its closed
subscheme

`dim_k H⁰(Y, i_* i^* 𝒪_Y((N+1)y)) ≥ N + 1`.

This is clause (2) of [Stacks, Tag 0AYT] in the shape the proof of [Stacks, Tag 0A27] consumes:
it is exactly the predicate `AlgebraicGeometry.MultiplePointSectionDimension` carried as a
hypothesis by `AlgebraicGeometry.isAffineOpen_compl_singleton_of_isCurve` and
`AlgebraicGeometry.isAffine_or_isProjectiveMorphism`, instantiated at the point the proof of
Tag 0A27 picks. Nothing is assumed: the statement below has no hypotheses beyond the geometry.

## The argument

The source computes `H⁰(Y, 𝒪_{n·y})` as `𝒪_{Y,y}/(π^n)` for `π` a uniformizer and reads the
bound off the `k`-linear independence of `1, π, …, π^{n-1}`. The proof here is that count done
through degrees, all three ingredients of which this library has:

* the module in the statement is the restriction of `𝒪_Y(D)` to the zero scheme of the canonical
  section `1_D`, and that zero scheme is `D` itself ([Stacks, Tag 01X0]), so
  `AlgebraicGeometry.invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme` —
  the identity underlying part (1) of [Stacks, Tag 0B40] — says that the dimension of its `H⁰`
  *is* the degree of `𝒪_Y(D)`, the cohomology on `D` and on `Y` agreeing because `i` is a closed
  immersion;
* the degree is additive in sums of divisors, since `𝒪_Y(D + D') ≅ 𝒪_Y(D) ⊗ 𝒪_Y(D')`
  ([Stacks, Tag 02OP]) and the degree is additive in tensor products ([Stacks, Tag 0AYX]);
  by induction `deg 𝒪_Y((N+1)y) = (N+1) · deg 𝒪_Y(y)`;
* `deg 𝒪_Y(y) ≥ 1`, because the canonical section of `𝒪_Y(y)` vanishes somewhere — its zero
  scheme is the reduced point `y`, which is nonempty — which is part (2) of
  [Stacks, Tag 0B40].

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `divisorInvertibleDegree`: the degree of `𝒪_X(D)` as a function of the ideal sheaf `D` alone.
* `finrank_cohomologyOverField_zero_eq_divisorInvertibleDegree`:
  `dim_k H⁰(X, i_* i^* 𝒪_X(D)) = deg 𝒪_X(D)` for an effective Cartier divisor `D` on a proper
  integral scheme of dimension at most one over `k`.
* `divisorInvertibleDegree_mul` and `divisorInvertibleDegree_pow_succ`: the degree is additive in
  sums of effective Cartier divisors, hence `deg 𝒪_X(n·D) = n · deg 𝒪_X(D)`.
* `one_le_divisorInvertibleDegree`: an effective Cartier divisor with a point has degree at
  least one.
* `succ_le_finrank_cohomologyOverField_multiplePoint`: **clause (2) of [Stacks, Tag 0AYT]** in
  the form displayed above.

## Implementation notes

**Why `divisorInvertibleDegree` exists.** `AlgebraicGeometry.invertibleCurveDegree` takes the
invertibility of its module as an instance argument, and the module here is
`Stacks.Divisors.modulesInvertibleSheaf D`, whose invertibility instance is derived from
`Stacks.Divisors.IsEffectiveCartierDivisor D`. Rewriting the divisor — which the induction on
`n` does, by `pow_succ` — therefore has to move an instance whose type mentions the term being
rewritten, and `rw` refuses the resulting motive. `divisorInvertibleDegree` is the body of
`AlgebraicGeometry.invertibleCurveDegree` at `𝒪_X(D)` with no instance argument at all, equal to
it by `rfl` (`invertibleCurveDegree_eq_divisorInvertibleDegree`), and `pow_succ` rewrites inside
it without incident.

**Two spellings of `𝒪_X(D)`.** `Stacks.Divisors.invertibleSheaf` is written over `X.sheaf.obj`
and `Stacks.Divisors.invertibleSheaf'` over `X.presheaf`; the two are equal by `rfl` but are not
interchangeable for `rw` or for instance search. `Stacks.Divisors.invertibleSheafSumIso` is
stated at the primed spelling and the statements below at the unprimed one, so the comparison
`𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')` is consumed by giving it a declared type rather than by
rewriting with it; the same is true of `Stacks.Divisors.sumSheaf` against the `tensorSheaf` that
[Stacks, Tag 0AYX] is stated with, and of the invertibility of `sumSheaf`, which is registered
only at the `X.sheaf.obj` index and has to be re-bound at the other.

**No `@[stacks]` attribute.** Clause (2) of [Stacks, Tag 0AYT] is the decomposition
`H⁰ = ⨁_{x ∈ Supp} ℱ_x`, which is proved at
`AlgebraicGeometry.cohomologyOverFieldZeroEquivDirectSumSuppStalk`; what is proved here is the
lower bound on the dimension that the proof of [Stacks, Tag 0A27] reads off it in one special
case, and it is neither that clause nor Tag 0A27.

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 02OP](https://stacks.math.columbia.edu/tag/02OP)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-! ### The degree of `𝒪_X(D)` as a function of `D` -/

/-- **The degree of `𝒪_X(D)` on a scheme over `k`**, as a function of the ideal sheaf `D` alone:
the alternating sum of the dimensions of `Hⁿ(X, 𝒪_X(D))` minus the same sum for the structure
sheaf. This is the body of `AlgebraicGeometry.invertibleCurveDegree` at
`Stacks.Divisors.modulesInvertibleSheaf D`, with the invertibility instance — which that
definition does not use — removed, so that the divisor can be rewritten inside it. -/
noncomputable def divisorInvertibleDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData) : ℤ :=
  (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k (cohomologyOverField k f (modulesInvertibleSheaf D) n) : ℤ)) -
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k
        (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ))

/-- `Stacks.Divisors.modulesInvertibleSheaf D` has `AlgebraicGeometry.divisorInvertibleDegree` as
its degree: the two definitions have the same body. -/
theorem invertibleCurveDegree_eq_divisorInvertibleDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (modulesInvertibleSheaf D)] :
    invertibleCurveDegree k f hdim (modulesInvertibleSheaf D) =
      divisorInvertibleDegree k f D := rfl

/-! ### The degree is the dimension of the sections of `𝒪_X(D)` along `D` -/

/-- **`dim_k H⁰(X, i_* i^* 𝒪_X(D)) = deg 𝒪_X(D)`** for an effective Cartier divisor `D` with
inclusion `i` on a proper integral scheme of dimension at most one over a field.

`AlgebraicGeometry.invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme` gives
this for the zero scheme of a nonzero global section; the section is the canonical section
`1_D`, which is nonzero because `X` is integral
(`AlgebraicGeometry.canonicalSections_eval_top_ne_zero`) and whose zero scheme is `D` itself
(`Stacks.Divisors.zeroScheme_canonicalSections`, [Stacks, Tag 01X0]). That statement measures the
cohomology on `D`, and
`AlgebraicGeometry.finrank_cohomologyOverField_pushforward_of_isClosedImmersion` moves it
to `X`. -/
theorem finrank_cohomologyOverField_zero_eq_divisorInvertibleDegree (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    (Module.finrank k (cohomologyOverField k f
        ((Scheme.Modules.pushforward D.subschemeι).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (modulesInvertibleSheaf D))) 0) : ℤ) =
      divisorInvertibleDegree k f D := by
  rw [← invertibleCurveDegree_eq_divisorInvertibleDegree k f hdim,
    invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k f hdim
      (modulesInvertibleSheaf D) (canonicalSections D)
      (canonicalSections_eval_top_ne_zero D ‹_›)
      (forall_finiteDimensional_cohomologyOverField_unit k f),
    zeroScheme_canonicalSections D,
    finrank_cohomologyOverField_pushforward_of_isClosedImmersion k D.subschemeι f]

/-! ### Additivity of the degree in the divisor -/

/-- **The degree of `𝒪_X(D)` is additive in sums of effective Cartier divisors**, on a proper
scheme of dimension at most one over a field: `deg 𝒪_X(D + D') = deg 𝒪_X(D) + deg 𝒪_X(D')`.

The sum of divisors is the product of their ideal sheaves, and
`Stacks.Divisors.invertibleSheafSumIso` ([Stacks, Tag 02OP]) identifies `𝒪_X(D + D')` with
`𝒪_X(D) ⊗ 𝒪_X(D')`; the degree is an isomorphism invariant
(`AlgebraicGeometry.invertibleCurveDegree_eq_of_iso`) and additive in tensor products of finite
locally free sheaves, which is
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`
([Stacks, Tag 0AYX]) at the two ranks equal to one. -/
theorem divisorInvertibleDegree_mul (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (D D' : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (hD' : IsEffectiveCartierDivisor D') :
    divisorInvertibleDegree k f (D * D') =
      divisorInvertibleDegree k f D + divisorInvertibleDegree k f D' := by
  have := hD
  have := hD'
  have : IsEffectiveCartierDivisor (D * D') := isEffectiveCartierDivisor_mul _ _ hD hD'
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (sumSheaf D D') :=
    isInvertible_sumSheaf D D'
  have hsum : invertibleCurveDegree k f hdim (sumSheaf D D') =
      invertibleCurveDegree k f hdim (modulesInvertibleSheaf (D * D')) :=
    invertibleCurveDegree_eq_of_iso k f hdim (invertibleSheafSumIso D D')
  rw [← invertibleCurveDegree_eq_divisorInvertibleDegree k f hdim,
    ← invertibleCurveDegree_eq_divisorInvertibleDegree k f hdim,
    ← invertibleCurveDegree_eq_divisorInvertibleDegree k f hdim, ← hsum,
    invertibleCurveDegree_eq_curveDegree, invertibleCurveDegree_eq_curveDegree,
    invertibleCurveDegree_eq_curveDegree]
  have h0 := curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim
    (modulesInvertibleSheaf D) (modulesInvertibleSheaf D') 1 1
  have h1 : curveDegree k f hdim (sumSheaf D D') 1 =
      ((1 : ℕ) : ℤ) * curveDegree k f hdim (modulesInvertibleSheaf D) 1 +
        ((1 : ℕ) : ℤ) * curveDegree k f hdim (modulesInvertibleSheaf D') 1 := h0
  simpa using h1

/-- **`deg 𝒪_X(n·D) = n · deg 𝒪_X(D)`** for an effective Cartier divisor `D` on a proper scheme
of dimension at most one over a field, at every positive multiple.

Induction on `n` from `D^1 = D`, each step being `AlgebraicGeometry.divisorInvertibleDegree_mul`
at `D^{n+1} · D`; the multiples are effective Cartier divisors by
`Stacks.Divisors.isEffectiveCartierDivisor_pow`, the remark following [Stacks, Tag 01WT]. The
statement is at `n + 1` rather than at `n` because at `n = 0` the divisor is empty and the
right-hand side is `0`, which is true but is not what the induction produces. -/
theorem divisorInvertibleDegree_pow_succ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (n : ℕ) :
    divisorInvertibleDegree k f (D ^ (n + 1)) =
      (n + 1 : ℤ) * divisorInvertibleDegree k f D := by
  induction n with
  | zero => rw [pow_one]; ring
  | succ m ih =>
      rw [pow_succ, divisorInvertibleDegree_mul k f hdim _ D
        (isEffectiveCartierDivisor_pow hD (m + 1)) hD, ih]
      push_cast
      ring

/-! ### An effective Cartier divisor with a point has positive degree -/

/-- **An effective Cartier divisor whose closed subscheme has a point has degree at least one**,
on a proper integral scheme of dimension at most one over a field.

This is part (2) of [Stacks, Tag 0B40],
`AlgebraicGeometry.invertibleCurveDegree_pos_of_nonempty_zeroScheme`, at the canonical section
`1_D`: that section is nonzero because `X` is integral and its zero scheme is `D`, so the
hypothesis of a nonempty zero scheme is the hypothesis that `D` has a point. -/
theorem one_le_divisorInvertibleDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (hne : Nonempty D.subscheme) :
    1 ≤ divisorInvertibleDegree k f D := by
  have := hD
  have hne' : Nonempty
      (zeroScheme X (modulesInvertibleSheaf D) ((canonicalSections D).eval (op ⊤))).subscheme := by
    rw [zeroScheme_canonicalSections D]
    exact hne
  have h := invertibleCurveDegree_pos_of_nonempty_zeroScheme k f hdim (modulesInvertibleSheaf D)
    (canonicalSections D) (canonicalSections_eval_top_ne_zero D hD) hne'
  have h' : 0 < divisorInvertibleDegree k f D := h
  omega

/-! ### Clause (2) of Stacks Tag 0AYT -/

/-- **Clause (2) of [Stacks, Tag 0AYT], in the shape the proof of [Stacks, Tag 0A27] consumes.**
Let `Y` be a proper curve over a field `k`, locally Noetherian and integral, and let `y` be a
closed point at which `𝒪_{Y,y}` is a discrete valuation ring. Then for every `N` the `k`-vector
space `H⁰(Y, i_* i^* 𝒪_Y((N+1)y))` has dimension at least `N + 1`, where `i` is the inclusion of
the effective Cartier divisor `(N+1)y`.

This is exactly `AlgebraicGeometry.MultiplePointSectionDimension k`, the hypothesis that
`AlgebraicGeometry.isAffineOpen_compl_singleton_of_isCurve` carries, with nothing assumed.

`(N+1)y` is an effective Cartier divisor by
`AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_pow`, items (4) and (5) of
[Stacks, Tag 0B8Y] followed by the remark after [Stacks, Tag 01WT]. Its dimension count is
`N + 1 = (N+1) · 1 ≤ (N+1) · deg 𝒪_Y(y) = deg 𝒪_Y((N+1)y) = dim_k H⁰(Y, i_* i^* 𝒪_Y((N+1)y))`,
the three steps being `AlgebraicGeometry.one_le_divisorInvertibleDegree`,
`AlgebraicGeometry.divisorInvertibleDegree_pow_succ` and
`AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_divisorInvertibleDegree`. The point `y`
lies in the support of its own reduced structure
(`AlgebraicGeometry.supportSet_vanishingIdeal_singleton`), which is the range of the inclusion of
that subscheme, so the divisor `y` has a point. -/
theorem succ_le_finrank_cohomologyOverField_multiplePoint (k : Type u) [Field k]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsIntegral Y]
    (hq : IsProper q) (hc : IsCurve k q) {y : Y} (hy : IsClosed ({y} : Set Y))
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] (N : ℕ) :
    N + 1 ≤ Module.finrank k (cohomologyOverField k q
      ((Scheme.Modules.pushforward (Scheme.IdealSheafData.vanishingIdeal
            (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y) ^ (N + 1)).subschemeι).obj
        ((Scheme.Modules.pullback (Scheme.IdealSheafData.vanishingIdeal
              (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y) ^ (N + 1)).subschemeι).obj
          (modulesInvertibleSheaf (Scheme.IdealSheafData.vanishingIdeal
            (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y) ^ (N + 1))))) 0) := by
  have := hq
  have hdim : topologicalKrullDim Y ≤ 1 := le_of_eq hc.topologicalKrullDim_eq_one
  have hD : IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) :=
    isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hy
  have hmem : y ∈ Set.range
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change y ∈ (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).supportSet
    rw [supportSet_vanishingIdeal_singleton hy]
    rfl
  obtain ⟨z, -⟩ := hmem
  have key := finrank_cohomologyOverField_zero_eq_divisorInvertibleDegree k q hdim
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ (N + 1))
  rw [divisorInvertibleDegree_pow_succ k q hdim _ hD N] at key
  have h1 := one_le_divisorInvertibleDegree k q hdim _ hD ⟨z⟩
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℤ) ≤ N + 1)
  rw [mul_one, ← key] at h2
  exact_mod_cast h2

end AlgebraicGeometry

end
