module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.FiniteCoverQuotientStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.EssImageAlongTargetEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtendFiberUnit

/-!
# Objects of the quotient stack presenting `FA_d` locally come from points of the object space

Let `S` be a scheme of a big fppf site, let `d` be a positive integer, and let `G` be a groupoid
in algebraic spaces over an algebraic space `B` over `S` whose pointwise groupoid presheaf is
isomorphic to the presheaf `FA_d` of free rank-`d` algebra structures — for the conjugation action
of the unit-fixing subgroup of `GL_d` on the scheme of structure constants this is the `[X/G]` of
Stacks 05YQ. Then every object of a fibre of `[U/R]` comes from a point of the object space over
each member of a covering of the test object **by opens of it**.

`AlgebraicGeometry.Stack.essImage_toQuotientStack` (Stacks 044X part (1)) says the same with an
fppf covering, and for a general groupoid in algebraic spaces that is all that is true: the
covering it produces comes from the three-stage construction of the stackification and has no
geometry in it. What makes the covering Zariski here is clause (b) of the proof of Stacks 05YQ: a
finite locally free algebra of rank `d` has, over a standard open cover of its base, a basis whose
first vector is the unit, and such a basis is exactly a lift of the object to a point of the
scheme of structure constants. That is
`AlgebraicGeometry.FiniteFreeAlgebra.exists_opens_essImage_specFiniteCover`, and this file
carries it across the identification of `ℋ_d` with the quotient stack.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_opens_essImage_toQuotientStack`: the statement
  above, the covering being a family of opens of the test object, one through each of its
  points.

## Implementation notes

The transport runs along the equivalence
`AlgebraicGeometry.FiniteFreeAlgebra.nonempty_isEquivalenceOver_finiteCover_quotientStack`, whose
functor is the extension of `Spec` across the stackification, in four steps, each of which keeps
the covering family it is given:

1. the covering family of clause (b) for the object of `ℋ_d` that the equivalence attaches to the
   given object of `[U/R]`, as
   `AlgebraicGeometry.FiniteFreeAlgebra.exists_opens_essImage_specFiniteCover`;
2. up to the raised morphism universe at which the stackification criterion reads everything,
   as `CategoryTheory.Functor.IsFibredOneMorphism.essImage_uliftHom_pullbackFiber`;
3. across the comparison of the pointwise groupoid fibration of `G` with that of `FA_d`, an
   equivalence over the site on the source, as
   `CategoryTheory.Functor.Stackification.essImage_comp_apply_of_isEquivalenceOver`; and across
   the 2-isomorphism of Stacks 0435 identifying the extension precomposed with the stackification
   map with `Spec`, as
   `CategoryTheory.Functor.Stackification.essImage_extend_comp_of_essImage`;
4. back across the equivalence itself, now on the target, as
   `CategoryTheory.Functor.Stackification.essImage_of_essImage_comp_of_isEquivalenceOver`.

Nothing is assumed: every input is an unconditional statement of the library, and in particular the
bootstrap theorem Stacks 04S6 does not appear.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0435](https://stacks.math.columbia.edu/tag/0435)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S} {d : ℕ} [NeZero d]
  {B : AlgebraicSpaces 𝒞 S hS} (G : GroupoidInAlgebraicSpaces 𝒞 S hS B)
  (η : ffaSitePresheaf 𝒞 S hS d ≅
    AlgebraicGeometry.Stack.evaluationGroupoidFunctor G.toGroupoidInFunctors)

include η in
/-- **Every object of a fibre of the quotient stack presenting `FA_d` comes from a point of the
object space over an open neighbourhood of each point of the test object.**

For the action groupoid of the conjugation action of the unit-fixing subgroup of `GL_d` on the
scheme of structure constants this is the statement about the `[X/G]` of Stacks 05YQ. The opens
are returned as a family indexed by the points of the test object, the member at a point being an
affine open neighbourhood over which the corresponding degree-`d` cover acquires a basis whose
first vector is the unit.

`AlgebraicGeometry.Stack.essImage_toQuotientStack` gives only an fppf covering, that being all the
stackification itself provides; the Zariski refinement is clause (b) of the proof of Stacks 05YQ,
transported along the identification of `ℋ_d` with the quotient stack. -/
theorem exists_opens_essImage_toQuotientStack
    (T : BigFppfOver 𝒞 S hS) (x : (AlgebraicGeometry.Stack.quotientStack G).p.Fiber T) :
    ∃ O : ↥T.left.obj → T.left.obj.Opens, (∀ t, t ∈ O t) ∧
      ∀ t, (Functor.fiberFunctorOfCompEq
          (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G).comp_eq
          (BigFppfOver.openSubObj 𝒞 S hS T (O t))).essImage
        (Functor.pullbackFiber (AlgebraicGeometry.Stack.quotientStack G).p x
          (BigFppfOver.openSubHom 𝒞 S hS T (O t))) := by
  classical
  obtain ⟨hΦeq⟩ := nonempty_isEquivalenceOver_finiteCover_quotientStack G η
  have hΦ := Functor.Stackification.extend_isFibredOneMorphism
    (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G)
    (isFibredOneMorphism_specQuotientPrestack G η)
    (AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack G)
    (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).isMorSheaf
    (AlgebraicGeometry.Stack.essImage_toQuotientStack G)
    (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).hasEffectiveDescent
  obtain ⟨y₀, hy₀⟩ := Functor.IsFibredOneMorphism.surjective_fiberFunctorOfCompEq_uliftHomUp_obj
    (AlgebraicGeometry.Stack.finiteCoverProjection (B := 𝒞) (S := S) (hS := hS) (d := d)) T
    ((Functor.fiberFunctorOfCompEq hΦ.comp_eq T).obj x)
  obtain ⟨O, hmem, hess⟩ := exists_opens_essImage_specFiniteCover T y₀
  refine ⟨O, hmem, fun t => ?_⟩
  refine Functor.Stackification.essImage_of_essImage_comp_of_isEquivalenceOver
    (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G) hΦ hΦeq
    (BigFppfOver.openSubHom 𝒞 S hS T (O t)) x ?_
  refine Functor.Stackification.essImage_extend_comp_of_essImage
    (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G)
    (isFibredOneMorphism_specQuotientPrestack G η)
    (AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack G)
    (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).isMorSheaf
    (AlgebraicGeometry.Stack.essImage_toQuotientStack G)
    (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).hasEffectiveDescent
    (BigFppfOver.openSubObj 𝒞 S hS T (O t)) ?_
  refine Functor.Stackification.essImage_comp_apply_of_isEquivalenceOver
    (isFibredOneMorphism_quotientPrestackToFfa G η)
    (isEquivalenceOver_quotientPrestackToFfa G η)
    (isFibredOneMorphism_specFiniteCoverLift 𝒞 S hS d) ?_
  rw [← hy₀]
  exact Functor.IsFibredOneMorphism.essImage_uliftHom_pullbackFiber
    (isFibredOneMorphism_specFiniteCover 𝒞 S hS d)
    (BigFppfOver.openSubHom 𝒞 S hS T (O t)) y₀ (hess t)

end AlgebraicGeometry.FiniteFreeAlgebra

end
