module

public import StacksFrontier.RingTheory.Rig.Category.CompletedBaseChange
public import StacksFrontier.RingTheory.Rig.Category.PolynomialPresentation
public import StacksFrontier.RingTheory.Rig.Category.AdicAlgebraSystem

/-!
# The category of adically complete algebras of finite type modulo an ideal

Fix a commutative ring `A` and an ideal `I ⊆ A`. This file builds the category `𝒞` of
Stacks chapter 88: its objects are the `I`-adically complete `A`-algebras `B` whose
reduction `B / IB` is of finite type over `A / I`, and its morphisms are the `A`-algebra
maps. It also builds the second category `𝒞'` of the chapter, whose objects are the
inverse systems `… → B₃ → B₂ → B₁` of finite type `A / Iⁿ`-algebras in which each
transition exhibits its target as the reduction of its source, and the functor
`B ↦ (B / Iⁿ⁺¹B)ₙ` from the first category to the second.

The main constructions on these categories are completed base change along a ring map
`A₁ → A₂` carrying a power of `I₁` into a finitely generated `I₂`, which sends `B` to the
`I₂`-adic completion of `B ⊗[A₁] A₂`; the presentation of an arbitrary object as a quotient
of a completed polynomial algebra `A[x₁, …, xᵣ]^`; and the identification of completed base
change along a surjection `A → A / 𝔞` with the ordinary quotient functor.

## Main definitions

* `Rig.AdicFiniteTypeAlgebra` — the category `𝒞` of `I`-adically complete `A`-algebras of
  finite type modulo `I`, as a full subcategory of `CommAlgCat A`.
* `Rig.AdicAlgebraSystem` — the category `𝒞'` of inverse systems of finite type algebras
  over the quotients `A / Iⁿ`.
* `Rig.CompletedBaseChange` and `Rig.completedBaseChange` — the completed base-change
  functor, bundled with the identification of its values with the adic completions of the
  tensor products.
* `Rig.completedBaseChangeOfIsNoetherianRing` — the same functor over a Noetherian ring `A₂`,
  needing only that some positive power of `I₁` maps into `I₂`.
* `Rig.CompletedPolynomialPresentation` and `Rig.completedPolynomialPresentation` — a
  presentation of an object as a quotient of a completed polynomial algebra.
* `Rig.adicQuotientFunctor` — the functor `𝒞 ⥤ 𝒞'` sending `B` to `(B / Iⁿ⁺¹B)ₙ`.
* `Rig.completionMap` — the map of adic completions induced by a ring homomorphism
  carrying one ideal into another.
* `Rig.quotientPowMap` — the map `A₁ / I₁^(cn) → A₂ / I₂ⁿ` induced by a homomorphism
  carrying `I₁^c` into `I₂`.

## Main results

* `Rig.exists_adicCompletion_mvPolynomial_quotient_equiv` — every object is a quotient of
  a completed polynomial algebra in finitely many variables.
* `Rig.isNoetherianRing` — over a Noetherian base every object is a Noetherian ring, and
  `Rig.quotient_isAdicFiniteType` — every quotient of an object is again an object.
* `Rig.iAdicallyCompleteRing_adicCompletion_mvPolynomial` and
  `Rig.finiteType_quotient_adicCompletion_mvPolynomial` — the completed polynomial
  algebras are themselves objects of the category.
* `Rig.quotient_isAdicallyComplete`, `Rig.tensor_quotient_completion_bijective` and
  `Rig.quotientBaseChange` — base change along `A → A / 𝔞` is the quotient functor.

## Implementation notes

The displayed systems of `AdicAlgebraSystem` are indexed from zero: the Lean index `n`
stands for the source's `B_{n+1}`.

## References

* [Stacks Project, Tag 0AJN](https://stacks.math.columbia.edu/tag/0AJN)
* [Stacks Project, Tag 0AJP](https://stacks.math.columbia.edu/tag/0AJP)
* [Stacks Project, Tag 0AJQ](https://stacks.math.columbia.edu/tag/0AJQ)
* [Stacks Project, Tag 0AK0](https://stacks.math.columbia.edu/tag/0AK0)
* [Stacks Project, Tag 0AL3](https://stacks.math.columbia.edu/tag/0AL3)
* [Stacks Project, Tag 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
* [Stacks Project, Tag 0AL6](https://stacks.math.columbia.edu/tag/0AL6)
-/

