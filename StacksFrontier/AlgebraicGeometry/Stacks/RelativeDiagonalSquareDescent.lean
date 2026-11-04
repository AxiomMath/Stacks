module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivityProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent

/-!
# Descending a relative property from a product projection to the diagonal

Let `S` be a scheme contained in a big fppf site `B` and let `x : 𝒯₁ ⟶ 𝒳`, `y : 𝒯₂ ⟶ 𝒳` be
1-morphisms of categories fibred in groupoids over the big fppf site of `S` with a common target.
The over-the-site form of Stacks 02XE, `AlgebraicGeometry.Stack.relativeDiagonalSquare`, exhibits

```text
  𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂
      |            |
      |            | x × y
      v            v
      𝒳     ⟶    𝒳 × 𝒳
            Δ
```

as a 2-fibre product, so the projection `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂` is a base change of the diagonal
of `𝒳` along `x × y`. The declaration
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_twoFibreProductProjection` reads that
square in the easy direction, transporting representability *down* from the diagonal to the
projection. This file reads it in the other direction: Stacks 045D descends a relative
property of Stacks 03YK *up* along `x × y`, so a property of the projection is a property of the
diagonal as soon as `x × y` is locally essentially surjective — and a product of locally
essentially surjective 1-morphisms is locally essentially surjective, which is
`AlgebraicGeometry.Stack.localEssSurj_productMap`.

The hypotheses are exactly those two and no more: `x` and `y` are arbitrary 1-morphisms, neither
assumed representable nor equal to one another, `𝒳` is an arbitrary category fibred in groupoids
rather than an algebraic stack, and the property `P` is arbitrary subject to the two standing
assumptions of Stacks 03YK — stability under base change and locality on the target for the fppf
precoverage.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_of_twoFibreProductProjection`: the
  diagonal of `𝒳` has the relative property `P` as soon as the projection `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂`
  does and `x × y` is locally essentially surjective.
* `AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_of_localEssSurj`: the same conclusion
  from local essential surjectivity of `x` and of `y` separately.

## Implementation notes

**Neither declaration carries a `@[stacks]` attribute, and the omission is deliberate.** What is
proved is Stacks 045D applied at the square of Stacks 02XE; both of those tags are already
carried, by `AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange` and — for the
representability half of 02XE over the site — by the declarations of
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare`, and an application of a lemma is
not a covering set for the lemma. The geometric statement this is the stack-level step of,
Stacks 06MB, additionally needs that the projection is unramified, resp. locally quasi-finite,
which is a statement about morphisms of algebraic spaces and is not proved here; so the 06MB
tag is not carried either.

The second declaration is stated at
`CatFiberedInGroupoids.{u, u, u + 1, u + 1}` and not at the general universe tuple of the first.
That is forced, not chosen: `AlgebraicGeometry.Stack.localEssSurj_productMap` is stated at that
tuple, and it is the only hypothesis of the first declaration which the product of two covers
discharges. The general form is therefore the one to cite whenever local essential surjectivity
of `x × y` is available by other means.

Each of the three occurrences of `AlgebraicGeometry.Stack.relativeDiagonalSquare`,
`AlgebraicGeometry.Stack.diagonalBasedFunctor` and `AlgebraicGeometry.Stack.diagonal` in the
second declaration carries its universes explicitly. Without them the object universe of the
2-fibre product apex is a metavariable constrained only by `max (max (u + 1) ?w) u = u + 1`,
which has no unique solution, and elaboration stops at an unsolved universe constraint rather
than at a type error.

## References

* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A relative property of the projection to a product is one of the diagonal.** Let `P` be a
property of morphisms of algebraic spaces over `S` which is stable under base change and local on
the target for the fppf precoverage, and let `x : 𝒯₁ ⟶ 𝒳` and `y : 𝒯₂ ⟶ 𝒳` be 1-morphisms of
categories fibred in groupoids over the big fppf site of `S` whose product `x × y` is locally
essentially surjective. If the diagonal of `𝒳` is representable by algebraic spaces and the
projection `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂` has the relative property `P` of Stacks 03YK, then so does the
diagonal of `𝒳`.

This is Stacks 045D applied at `AlgebraicGeometry.Stack.relativeDiagonalSquare`, the
over-the-site form of Stacks 02XE, which exhibits the projection as the base change of the
diagonal along `x × y`. -/
theorem hasRelativeProperty_diagonal_of_twoFibreProductProjection
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (𝒯₁ 𝒯₂ 𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳))
    (hxy : ∀ (U : BigFppfOver B S hS)
      (q : (CatFiberedInGroupoids.product 𝒳 𝒳).val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : (CatFiberedInGroupoids.product 𝒯₁ 𝒯₂).val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor
              (CatFiberedInGroupoids.productMap x y)).obj z ⟶ q.1,
              (CatFiberedInGroupoids.product 𝒳 𝒳).val.p.IsHomLift k φ)
    (hP : HasRelativeProperty B S hS P (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y).fst
      (isRepresentableByAlgebraicSpaces_twoFibreProductProjection.{u, v, w}
        B S hS 𝒯₁ 𝒯₂ 𝒳 x y hΔ)) :
    HasRelativeProperty B S hS P (diagonal B S hS 𝒳) hΔ :=
  hasRelativeProperty_of_baseChange.{u, v, w, t} B S hS 𝒳
    (CatFiberedInGroupoids.product 𝒳 𝒳) (CatFiberedInGroupoids.product 𝒯₁ 𝒯₂) P
    (diagonal B S hS 𝒳) (CatFiberedInGroupoids.productMap x y)
    (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y)
    (isTwoFibreProduct_relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y) hΔ hxy hP

/-- **A relative property of the projection to a product is one of the diagonal, for a pair of
locally essentially surjective 1-morphisms.** The hypothesis on the product `x × y` of
`AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_of_twoFibreProductProjection` is supplied
by `AlgebraicGeometry.Stack.localEssSurj_productMap` from local essential surjectivity of `x` and
of `y` separately. -/
theorem hasRelativeProperty_diagonal_of_localEssSurj
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (𝒯₁ 𝒯₂ 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (diagonalBasedFunctor.{u, u, u + 1} B S hS 𝒳))
    (hx : ∀ (U : BigFppfOver B S hS) (q : 𝒳.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒯₁.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor x).obj z ⟶ q.1,
            𝒳.val.p.IsHomLift k φ)
    (hy : ∀ (U : BigFppfOver B S hS) (q : 𝒳.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒯₂.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor y).obj z ⟶ q.1,
            𝒳.val.p.IsHomLift k φ)
    (hP : HasRelativeProperty B S hS P
      (relativeDiagonalSquare.{u, u, u} B S hS 𝒯₁ 𝒯₂ 𝒳 x y).fst
      (isRepresentableByAlgebraicSpaces_twoFibreProductProjection.{u, u, u}
        B S hS 𝒯₁ 𝒯₂ 𝒳 x y hΔ)) :
    HasRelativeProperty B S hS P (diagonal.{u, u, u + 1} B S hS 𝒳) hΔ :=
  hasRelativeProperty_diagonal_of_twoFibreProductProjection.{u, u, u, t} B S hS P 𝒯₁ 𝒯₂ 𝒳 x y hΔ
    (localEssSurj_productMap B S hS x y hx hy) hP

end AlgebraicGeometry.Stack

end
