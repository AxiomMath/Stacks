module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.TwistDimensions
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Picard.CurveChowZero
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochMeromorphic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPoints

/-!
# Divisors in the image of `Pic(X) ⟶ CH_0(X)` on a curve

Let `k` be a field and let `X` be an integral proper curve over `k`. For an effective Cartier
divisor `D ⊆ X` the homomorphism `AlgebraicGeometry.curvePicardToChowZero` of
`StacksFrontier.AlgebraicGeometry.Picard.CurveChowZero` sends the Picard class of `𝒪_X(D)` to the
class of the zero-cycle `[D]_0`:

`c₁(𝒪_X(D)) ∩ [X]_1 = [D]_0`   in   `CH_0(X)`.

This is [Stacks, Tag 02SK] — `c₁(ℒ) ∩ [X] = [Z(s)]` for a nonzero global section `s` of an
invertible `ℒ` — applied to the canonical section `1_D` of `𝒪_X(D)`, whose zero scheme is `D`
itself by [Stacks, Tag 01X0].

Specialised to a `k`-rational point `x` of a smooth proper curve, where the reduced point is an
effective Cartier divisor, this says

`c₁(𝒪_X(x)) ∩ [X]_1 = [x]`,

the class `Stacks.WeilCohomology.rationalPointChowClass` of that point. Hence for two rational
points `x`, `x'` the difference `[x] - [x']` is the image under `curvePicardToChowZero` of the
Picard class of `𝒪_X(x) ⊗ 𝒪_X(x')^{-1}`, and that class has degree zero, since each of the two
point divisors has degree one.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `invertibleCurveChowZeroClass_invertibleSheaf` — `c₁(𝒪_X(D)) ∩ [X]_1 = [D]_0` for an effective
  Cartier divisor `D` on an integral proper curve.
* `curvePicardToChowZero_divisorPicardClass` — the same read through
  `Stacks.Divisors.picardClass`, so as a statement about the homomorphism out of `Pic(X)`.
* `cycleAssociatedToClosedSubscheme_vanishingIdeal_point` — the zero-cycle of the reduced point
  of a section is the zero-cycle of the section itself.
* `curvePicardToChowZero_divisorPicardClass_point` — `c₁(𝒪_X(x)) ∩ [X]_1` is
  `Stacks.WeilCohomology.rationalPointChowClass` at `x`.
* `invertibleCurveDegreeHom_divisorPicardClass_point` — the Picard class of a rational point has
  degree one.
* `exists_curvePicardToChowZero_eq_rationalPointChowClass_sub` — **the correspondence the
  degree-zero statement consumes**: `[x] - [x']` is the image of a Picard class of degree zero,
  namely `𝒪_X(x) ⊗ 𝒪_X(x')^{-1}`.

## Implementation notes

**Why `[X]_1` sits at the grading it does.** [Stacks, Tag 02SK] is stated at a delta-dimension
`n` of `X`, with the cap product landing in degree `n - 1` and the fundamental cycle in degree
`n - 1 + 1`. For an integral scheme of topological dimension one over a field the
delta-dimension is one —
`AlgebraicGeometry.schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one` — so the two
gradings are `0` and `1`, which is where
`AlgebraicGeometry.invertibleCurveChowZeroClass` takes them; the numerals are matched by
`norm_num` and no transport is used.

**The two cycles of a rational point.** A `k`-rational point `x` of `X`, that is a section of
the structure morphism, is a closed immersion, so it has a zero-cycle
`Stacks.WeilCohomology.rationalPointChowClass`. The divisor it cuts out is the *reduced* point
`Scheme.IdealSheafData.vanishingIdeal {x}`, a different closed subscheme of `X` with the same
ideal sheaf: `Spec k` is reduced, so the kernel ideal sheaf of `x` is the vanishing ideal of the
closure of its range, which is that point. Two closed immersions with the same kernel ideal sheaf
differ by an isomorphism of their sources over `X` (`IsClosedImmersion.isIso_lift`), and the
associated cycle of [Stacks, Tag 02QU] is invariant under such an isomorphism
(`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso`), so the two cycles are equal. No new
comparison is introduced.

**The hypothesis `h0`.** The geometric facts about a rational point on a smooth proper curve —
that it is closed, that the curve is integral of dimension one, and that the reduced point is an
effective Cartier divisor — are `AlgebraicGeometry.GenusOne.isClosed_point`,
`AlgebraicGeometry.GenusOne.isCurve` and `AlgebraicGeometry.GenusOne.isEffectiveCartierDivisor`,
which take `dim_k H⁰(X, 𝒪_X) = 1` as their hypothesis and no genus hypothesis at all. That is
the hypothesis carried here, and it holds for a geometrically irreducible curve. The degree of a
rational point is `AlgebraicGeometry.GenusOne.divisorInvertibleDegree_vanishingIdeal_point`,
which has the same hypotheses.

No tag is attached. [Stacks, Tag 02SK] is registered on the cap-product identity this file
applies, [Stacks, Tag 01X0] on the zero scheme of the canonical section, [Stacks, Tag 02QU] on
the associated cycle and [Stacks, Tag 01CX] on the Picard group; what is proved here is their
composite at a divisor and at a rational point.

## References

* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.Chow
open Stacks.RingedSpace (structureIsSheaf)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-! ### The zero-cycle class of `𝒪_X(D)` -/

/-- **`c₁(𝒪_X(D)) ∩ [X]_1 = [D]_0`** for an effective Cartier divisor `D` on an integral proper
curve over a field. This is [Stacks, Tag 02SK] at the canonical section `1_D` of `𝒪_X(D)`, which
is nonzero because `X` is integral and whose zero scheme is `D` by [Stacks, Tag 01X0]. -/
theorem invertibleCurveChowZeroClass_invertibleSheaf [IsIntegral X]
    (hone : topologicalKrullDim X = 1) (D : X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    invertibleCurveChowZeroClass k f (Stacks.Divisors.modulesInvertibleSheaf D) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f D.subschemeι 0) := by
  have hdelta : schemeDeltaDimension (fieldChowSituation k) f = ((1 : ℤ) : EInt) :=
    schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one k f hone
  have hs : Stacks.Divisors.canonicalSection D ≠ 0 := by
    rw [← Stacks.Divisors.canonicalSections_eval_top D]
    exact canonicalSections_eval_top_ne_zero D hD
  have h := Stacks.ChernCap42.firstChernClassCapOfInvertible_fundamentalCycle
    (fieldChowSituation k) f 1 hdelta
    (Stacks.Divisors.modulesInvertibleSheaf D) (Stacks.Divisors.canonicalSection D) hs
  have hz : Stacks.Divisors.zeroScheme X (Stacks.Divisors.modulesInvertibleSheaf D)
      (Stacks.Divisors.canonicalSection D) = D :=
    Stacks.Divisors.zeroScheme_canonicalSection' D
  rwa [hz] at h

/-- **The Picard class of an effective Cartier divisor goes to the class of its zero-cycle.**
`AlgebraicGeometry.curvePicardToChowZero` sends `Stacks.Divisors.picardClass D` to `[D]_0`. -/
theorem curvePicardToChowZero_divisorPicardClass [IsIntegral X]
    (hone : topologicalKrullDim X = 1) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    curvePicardToChowZero k f (Stacks.Divisors.picardClass D) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f D.subschemeι 0) := by
  refine Eq.trans ?_ (invertibleCurveChowZeroClass_invertibleSheaf k f hone D)
  exact curvePicardToChowZero_picardClass k f (Stacks.Divisors.invertibleSheaf' D)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)

/-! ### Rational points -/

/-- **The zero-cycle of the reduced point of a section is the zero-cycle of the section.** The
section `x : Spec k ⟶ X` is a closed immersion with reduced source, so its kernel ideal sheaf is
the vanishing ideal of its image; two closed immersions with the same kernel ideal sheaf differ
by an isomorphism of their sources over `X`, and the associated cycle of [Stacks, Tag 02QU] is
invariant under such an isomorphism. -/
theorem cycleAssociatedToClosedSubscheme_vanishingIdeal_point
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨{GenusOne.point x}, GenusOne.isClosed_point f x hx⟩ : Closeds X)).subschemeι 0 =
      letI : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id f x hx
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) f x 0 := by
  let : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id f x hx
  set D := Scheme.IdealSheafData.vanishingIdeal
    (⟨{GenusOne.point x}, GenusOne.isClosed_point f x hx⟩ : Closeds X) with hDdef
  have hrange : Set.range x = ({GenusOne.point x} : Set X) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_singleton_iff.2 (congrArg x (Subsingleton.elim _ _))
    · rintro rfl
      exact ⟨_, rfl⟩
  have hker : D.subschemeι.ker = x.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      hDdef]
    refine congrArg Scheme.IdealSheafData.vanishingIdeal ?_
    ext1
    rw [Closeds.coe_closure, hrange, (GenusOne.isClosed_point f x hx).closure_eq]
    rfl
  have : IsIso (IsClosedImmersion.lift D.subschemeι x hker.le) :=
    IsClosedImmersion.isIso_lift D.subschemeι x hker
  exact (cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) f x D.subschemeι
    (asIso (IsClosedImmersion.lift D.subschemeι x hker.le))
    (IsClosedImmersion.lift_fac D.subschemeι x hker.le) 0).symm

/-- **`c₁(𝒪_X(x)) ∩ [X]_1` is the class of the rational point `x`.** The reduced point of a
`k`-rational point of a smooth proper curve is an effective Cartier divisor, and its zero-cycle
is `Stacks.WeilCohomology.rationalPointChowClass`. -/
theorem curvePicardToChowZero_divisorPicardClass_point [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    haveI := GenusOne.isIntegral f h0
    haveI := GenusOne.isEffectiveCartierDivisor f h0 x hx
    curvePicardToChowZero k f (Stacks.Divisors.picardClass
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨{GenusOne.point x}, GenusOne.isClosed_point f x hx⟩ : Closeds X))) =
      Stacks.WeilCohomology.rationalPointChowClass k f x hx := by
  have := GenusOne.isIntegral f h0
  have := GenusOne.isEffectiveCartierDivisor f h0 x hx
  have := GenusOne.isCurve f h0
  rw [curvePicardToChowZero_divisorPicardClass k f (IsCurve.topologicalKrullDim_eq_one (f := f)) _,
    cycleAssociatedToClosedSubscheme_vanishingIdeal_point k f x hx]
  rfl

/-- **A `k`-rational point has degree one**: the Picard class of the reduced point of a section
has degree one, which is
`AlgebraicGeometry.GenusOne.divisorInvertibleDegree_vanishingIdeal_point`. -/
theorem invertibleCurveDegreeHom_divisorPicardClass_point [SmoothOfRelativeDimension 1 f]
    (hdim : topologicalKrullDim X ≤ 1)
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    haveI := GenusOne.isEffectiveCartierDivisor f h0 x hx
    invertibleCurveDegreeHom k f hdim (Stacks.Divisors.picardClass
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨{GenusOne.point x}, GenusOne.isClosed_point f x hx⟩ : Closeds X))) = 1 := by
  have := GenusOne.isEffectiveCartierDivisor f h0 x hx
  rw [invertibleCurveDegreeHom_picardClass k f hdim (Stacks.Divisors.invertibleSheaf' _)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard _)]
  exact GenusOne.divisorInvertibleDegree_vanishingIdeal_point f h0 x hx

/-- **`[x] - [x']` is the image of a Picard class of degree zero.** For two `k`-rational points
`x`, `x'` of a smooth proper curve over `k` the difference of their zero-cycle classes in
`CH_0(X)` is `AlgebraicGeometry.curvePicardToChowZero` applied to the Picard class of
`𝒪_X(x) ⊗ 𝒪_X(x')^{-1}`, and that class lies in the kernel of the degree homomorphism, both point
divisors having degree one.

This is the correspondence a divisibility statement about `Pic⁰(X)` consumes: a class `c` of
degree zero with `n • c' = c` for some `c'` produces `[x] - [x'] = n • (c' ↦ CH_0)`, by
additivity of `AlgebraicGeometry.curvePicardToChowZero`. -/
theorem exists_curvePicardToChowZero_eq_rationalPointChowClass_sub
    [SmoothOfRelativeDimension 1 f] (hdim : topologicalKrullDim X ≤ 1)
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (x x' : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ c : Stacks.Picard.ofScheme X,
      invertibleCurveDegreeHom k f hdim c = 0 ∧
        curvePicardToChowZero k f c =
          Stacks.WeilCohomology.rationalPointChowClass k f x hx -
            Stacks.WeilCohomology.rationalPointChowClass k f x' hx' := by
  have := GenusOne.isEffectiveCartierDivisor f h0 x hx
  have := GenusOne.isEffectiveCartierDivisor f h0 x' hx'
  refine ⟨Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point x}, GenusOne.isClosed_point f x hx⟩ : Closeds X)) -
    Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point x'}, GenusOne.isClosed_point f x' hx'⟩ : Closeds X)), ?_, ?_⟩
  · rw [map_sub, invertibleCurveDegreeHom_divisorPicardClass_point k f hdim h0 x hx,
      invertibleCurveDegreeHom_divisorPicardClass_point k f hdim h0 x' hx', sub_self]
  · rw [map_sub, curvePicardToChowZero_divisorPicardClass_point k f h0 x hx,
      curvePicardToChowZero_divisorPicardClass_point k f h0 x' hx']

end AlgebraicGeometry

end
