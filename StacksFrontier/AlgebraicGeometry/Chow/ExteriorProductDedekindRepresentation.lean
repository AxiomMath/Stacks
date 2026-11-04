module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.SecondVariable
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.ReductionToIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.ClosedPointCase
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.InverseMap

/-!
# The bivariant class attached to a Chow class over a Dedekind base acts by exterior product

Let `(S, δ)` be a base as in section 42.63 of the Stacks Project: locally the spectrum of a
Dedekind domain, with `δ(s) = 0` at the closed points and `δ(s) = 1` elsewhere, and with no
zero-dimensional component. Let `X` be locally of finite type over `S`. **Stacks 0FC5** identifies
`A^p(X → S)` with `CH_{1-p}(X)` by `c ↦ c ∩ [S]₁`, and its proof describes the inverse: the class
`c_α` attached to `α ∈ CH_{1-p}(X)` is the one whose cap product is the exterior product of
Stacks 0FC4,

  `c_α ∩ α' = α × α'`   in `CH_{n-p}(X ×_S U)`, for `α' ∈ CH_n(U)`.

This file proves that every `c ∈ A^p(X → S)` caps as the exterior product with `c ∩ [S]₁`, which
is that clause of Stacks 0FC5 together with the bijectivity proved in
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariant`.

The argument is the final paragraph of the source's proof. By Stacks 02UC both sides are
determined by their values on the fundamental classes `[T]` of integral schemes `T` over the base;
here this is done by hand for the exterior product, which is not known beforehand to be bivariant:
a cycle on `U` is the pushforward from the coproduct of the closures of the points of its support,
and the exterior product commutes with that pushforward and with restriction to the open and
closed pieces. If `T` dominates a component of the base it is flat over it (Stacks 0AUW) and
`[T] = (T → S)^*[S]₁`; otherwise `T` lies over a closed point `s`, which on an integral
neighbourhood `V` is the zero scheme `D` of a section of an invertible module with trivial
restriction to `D`, and `[T] = h^* i^*[V]₁` for the Gysin map `i^*` of `D` (Stacks 0B79) and a flat
`h : T ⟶ D`. Since `c` commutes with flat pullback and Gysin maps, `c ∩ [T]` is computed from
`c ∩ [S]₁`, and on cycles the result is the defining rule of the exterior product.

## Main results

* `Stacks.Chow.isExteriorProductOverBase_bivariantCapBaseFundamentalClass` — every
  `c ∈ A^p(X → S)` acts by exterior product with `c ∩ [S]₁`.
* `Stacks.Chow.exists_isExteriorProductOverBase` — **Stacks 0FC5**, the inverse map: every
  `α ∈ CH_{1-p}(X)` is `c_α ∩ [S]₁` for a class `c_α` with `c_α ∩ α' = α × α'`.
* `Stacks.Chow.cap_heq_exteriorProductDedekindCycles_of_forall_isIntegral` — the reduction to
  fundamental classes of integral schemes.
* `Stacks.Chow.cap_fundamentalCycle_heq_of_mem_genericPoints`,
  `Stacks.Chow.cap_fundamentalCycle_heq_of_notMem_genericPoints` — the two cases of an integral
  test scheme.
* `Stacks.Chow.cycleGroupRestrict_exteriorProductDedekindCycles`,
  `Stacks.Chow.properPushforward_exteriorProductDedekindCycles_of_isClosedImmersion`,
  `Stacks.Chow.properPushforward_exteriorProductDedekindCycles_sigmaDesc` — the exterior product
  over a Dedekind base commutes with restriction to an open subscheme and with pushforward along a
  closed immersion or from a coproduct of closed subschemes, in its second variable.
* `Stacks.Chow.exteriorProductDedekindCycles_fundamentalCycle_apply_of_dominates`,
  `Stacks.Chow.flatPullback_gysinCycleMap_apply` — the exterior product with the fundamental class
  of an integral scheme as a flat pullback, respectively a flat pullback of a Gysin map on cycles.

## Implementation notes

The statement is `Stacks.Chow.IsExteriorProductOverBase`, the hypothesis `hrep` of
`Stacks.Chow.exteriorProductDedekindChow_cap_comm` (Stacks 0FC7), at the class
`α = c ∩ [S]₁` of `Stacks.Chow.bivariantCapBaseFundamentalClass`. Bivariant classes are those of the
Gysin system `Stacks.Chow.gysinSystemOfInvertible`, as in Stacks 0FC5 here; the Gysin step uses that
its Gysin map is the Gysin map on cycles of Stacks 0B6Z for a divisor with trivial normal bundle.

The source writes `c_α = g_* ∘ ξ` for generators `ξ` and checks that it is bivariant. That is not
needed: Stacks 0FC5 already supplies a class with `c ∩ [S]₁ = α`, and what is proved is that every
class caps as the exterior product with its image, by the source's own comparison of `c` with
`c_α` on fundamental classes, with `α × -` in place of `c_α ∩ -`.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 0FC7](https://stacks.math.columbia.edu/tag/0FC7)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
-/
