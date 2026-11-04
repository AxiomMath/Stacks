module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackUniqueness
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafOfGroupoidsIsoEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecFiniteCoverLift
public import StacksFrontier.CategoryTheory.Sites.Stackification.TransportAlongEquivalenceOver

/-!
# `ℋ_d` is the quotient stack of a groupoid presenting `FA_d`

Let `S` be a scheme of a big fppf site and let `d` be a positive integer. The category `ℋ_d` of
degree-`d` finite locally free covers over the big fppf site over `S` receives the 1-morphism
`Spec` out of the pointwise groupoid fibration of the presheaf `FA_d` of free rank-`d` algebra
structures, and that 1-morphism satisfies the two clauses of Stacks 02ZN: the induced maps of
morphism presheaves are locally bijective, and every object of a fibre of `ℋ_d` is locally in the
essential image. This file turns those facts into the identification Stacks 05YQ asserts.

Let `G` be **any** groupoid in algebraic spaces over an algebraic space `B` over `S` whose
pointwise groupoid presheaf is isomorphic to `FA_d` restricted to the site over `S`. Then `ℋ_d` is
equivalent, over the big fppf site over `S`, to the quotient stack `[U/R]` of `G`. For the action
groupoid of the conjugation action of the unit-fixing subgroup of `GL_d` on the scheme of structure
constants this is the statement of Stacks 05YQ, `[U/R]` being the `[X/G]` of the source.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.specQuotientPrestack`: the 1-morphism from the pointwise
  groupoid fibration of `G`, at the raised morphism universe, into `ℋ_d` at the raised morphism
  universe: the comparison with `FA_d` followed by `Spec`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.isFibredOneMorphism_specQuotientPrestack`: it is a
  1-morphism of fibred categories over the site.
* `AlgebraicGeometry.FiniteFreeAlgebra.isLocallyBijective_and_essImage_specQuotientPrestack`: the
  two clauses of Stacks 02ZN for it.
* `AlgebraicGeometry.FiniteFreeAlgebra.nonempty_isEquivalenceOver_finiteCover_quotientStack`:
  **`ℋ_d` is equivalent over the big fppf site to the quotient stack of `G`.**

## Implementation notes

Three universe adjustments stand between the inputs and the criterion
`AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_extend_toQuotientStack`, and all three are
already in the library.

The criterion reads its hypotheses on `AlgebraicGeometry.Stack.quotientPrestack`, the pointwise
groupoid fibration of `G` with its morphisms raised one universe, because the explicit
stackification of Stacks 02ZN needs objects and morphisms in a common universe. So `Spec` and its
two clauses are taken at the raised morphism universe, which is
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/FiniteFreeAlgebra/SpecFiniteCoverLift.lean`.

The source of `Spec` is the pointwise groupoid fibration of `FA_d`, and the criterion asks for one
out of the pointwise groupoid fibration of `G`. The two presheaves of groupoids are isomorphic, so
the comparison is `CategoryTheory.presheafOfGroupoidsMap`, which is an equivalence over the site by
`CategoryTheory.isEquivalenceOver_presheafOfGroupoidsMap` and stays one after the morphism-universe
lift; the two clauses then transport along it by
`Functor.Stackification.isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver` in
`CategoryTheory`.

`ℋ_d` is a stack at the raised morphism universe by
`AlgebraicGeometry.FiniteFreeAlgebra.isStack_uliftHomProj_finiteCoverProjection`, and is fibred
there by `CategoryTheory.Functor.isFibered_uliftHomProj_of_isFibered` applied to
`AlgebraicGeometry.FiniteFreeAlgebra.isFibered_finiteCoverProjection`, both instances.

Everything is stated for an arbitrary `G` and an arbitrary isomorphism, because nothing in the
argument is particular to the conjugation action: what the action contributes is the isomorphism
itself.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 02ZP](https://stacks.math.columbia.edu/tag/02ZP)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
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

/-! ### The comparison of the two presentations -/

/-- The comparison of the pointwise groupoid fibration of `G` with that of `FA_d`, at the raised
morphism universe: the morphism-universe lift of the functor induced by the inverse of the given
isomorphism of presheaves of groupoids. -/
noncomputable abbrev quotientPrestackToFfa :
    (AlgebraicGeometry.Stack.quotientPrestack G).obj ⥤
      ULiftHom.{u + 1} (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj :=
  Functor.uliftHomMap (presheafOfGroupoidsMap η.symm.hom)

/-- The comparison of the two presentations is a 1-morphism of fibred categories over the site. -/
theorem isFibredOneMorphism_quotientPrestackToFfa :
    (AlgebraicGeometry.Stack.quotientPrestack G).p.IsFibredOneMorphism
      (Functor.uliftHomProj (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p :
        ULiftHom.{u + 1} (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj ⥤
          BigFppfOver 𝒞 S hS)
      (quotientPrestackToFfa G η) :=
  (isFibredOneMorphism_presheafOfGroupoidsMap η.symm.hom).uliftHom

/-- The comparison of the two presentations is an equivalence over the site. -/
noncomputable def isEquivalenceOver_quotientPrestackToFfa :
    Functor.IsEquivalenceOver (AlgebraicGeometry.Stack.quotientPrestack G).p
      (Functor.uliftHomProj (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p :
        ULiftHom.{u + 1} (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj ⥤
          BigFppfOver 𝒞 S hS)
      (quotientPrestackToFfa G η) :=
  isEquivalenceOver_uliftHomMap_presheafOfGroupoidsMap η.symm

/-! ### `Spec` out of the pointwise groupoid fibration of `G` -/

/-- **The 1-morphism of the proof of Stacks 05YQ out of the pointwise groupoid fibration of `G`**,
at the raised morphism universe: the comparison with the pointwise groupoid fibration of `FA_d`
followed by the lift of `Spec`. -/
noncomputable abbrev specQuotientPrestack :
    (AlgebraicGeometry.Stack.quotientPrestack G).obj ⥤
      ULiftHom.{u + 1} (AlgebraicGeometry.Stack.FiniteCover 𝒞 S hS d) :=
  quotientPrestackToFfa G η ⋙ specFiniteCoverLift 𝒞 S hS d

/-- `AlgebraicGeometry.FiniteFreeAlgebra.specQuotientPrestack` is a 1-morphism of fibred categories
over the big fppf site over `S`. -/
theorem isFibredOneMorphism_specQuotientPrestack :
    (AlgebraicGeometry.Stack.quotientPrestack G).p.IsFibredOneMorphism
      (Functor.uliftHomProj (AlgebraicGeometry.Stack.finiteCoverProjection
        (B := 𝒞) (S := S) (hS := hS) (d := d)))
      (specQuotientPrestack G η) :=
  (isFibredOneMorphism_quotientPrestackToFfa G η).comp
    (isFibredOneMorphism_specFiniteCoverLift 𝒞 S hS d)

/-- **The two clauses of Stacks 02ZN for
`AlgebraicGeometry.FiniteFreeAlgebra.specQuotientPrestack`.** They hold for the lift of `Spec`, and
transport along the comparison of the two presentations, which is an equivalence over the site. -/
theorem isLocallyBijective_and_essImage_specQuotientPrestack :
    (∀ (U : BigFppfOver 𝒞 S hS) (a b : (AlgebraicGeometry.Stack.quotientPrestack G).p.Fiber U),
        CategoryTheory.Presheaf.IsLocallyInjective ((BigFppfOver.topology 𝒞 S hS).over U)
            ((isFibredOneMorphism_specQuotientPrestack G η).morPresheafMap a b) ∧
          CategoryTheory.Presheaf.IsLocallySurjective ((BigFppfOver.topology 𝒞 S hS).over U)
            ((isFibredOneMorphism_specQuotientPrestack G η).morPresheafMap a b)) ∧
      (∀ (U : BigFppfOver 𝒞 S hS)
          (x : (Functor.uliftHomProj (AlgebraicGeometry.Stack.finiteCoverProjection
            (B := 𝒞) (S := S) (hS := hS) (d := d))).Fiber U),
        ∃ R ∈ BigFppfOver.topology 𝒞 S hS U,
          ∀ ⦃V : BigFppfOver 𝒞 S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
            (Functor.fiberFunctorOfCompEq
                (isFibredOneMorphism_specQuotientPrestack G η).comp_eq V).essImage
              (Functor.pullbackFiber (Functor.uliftHomProj
                (AlgebraicGeometry.Stack.finiteCoverProjection
                  (B := 𝒞) (S := S) (hS := hS) (d := d))) x f)) :=
  Functor.Stackification.isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver
    (isFibredOneMorphism_quotientPrestackToFfa G η)
    (isEquivalenceOver_quotientPrestackToFfa G η)
    (isFibredOneMorphism_specFiniteCoverLift 𝒞 S hS d) (BigFppfOver.topology 𝒞 S hS)
    (isLocallyBijective_specFiniteCoverLift 𝒞 S hS d) (essImage_specFiniteCoverLift 𝒞 S hS d)

/-! ### The identification of `ℋ_d` with the quotient stack -/

/-- **Stacks 05YQ, the identification.** Let `G` be a groupoid in algebraic spaces over an
algebraic space `B` over `S` whose pointwise groupoid presheaf is isomorphic to the presheaf `FA_d`
of free rank-`d` algebra structures on the big fppf site over `S`. Then the category `ℋ_d` of
degree-`d` finite locally free covers is equivalent, over the big fppf site over `S`, to the
quotient stack `[U/R]` of `G`.

The equivalence is the extension of
`AlgebraicGeometry.FiniteFreeAlgebra.specQuotientPrestack` across the stackification
`AlgebraicGeometry.Stack.toQuotientStack`, and the statement is the determinacy clause of
Stacks 02ZN and 02ZP in the form
`AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_extend_toQuotientStack`: the four inputs it
asks for are that `ℋ_d` is a stack, that `Spec` is a 1-morphism over the site, and the two clauses
of Stacks 02ZN for it. -/
theorem nonempty_isEquivalenceOver_finiteCover_quotientStack :
    Nonempty (Functor.IsEquivalenceOver (AlgebraicGeometry.Stack.quotientStack G).p
      (Functor.uliftHomProj (AlgebraicGeometry.Stack.finiteCoverProjection
        (B := 𝒞) (S := S) (hS := hS) (d := d)))
      (Functor.Stackification.extend
        (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G)
        (isFibredOneMorphism_specQuotientPrestack G η)
        (AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack G)
        (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).isMorSheaf
        (AlgebraicGeometry.Stack.essImage_toQuotientStack G)
        (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).hasEffectiveDescent)) :=
  AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_extend_toQuotientStack G
    (isFibredOneMorphism_specQuotientPrestack G η)
    (isLocallyBijective_and_essImage_specQuotientPrestack G η).1
    (isLocallyBijective_and_essImage_specQuotientPrestack G η).2
    (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d)

end AlgebraicGeometry.FiniteFreeAlgebra

end
