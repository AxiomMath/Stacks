module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecEssImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecLocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomLocallyBijective

/-!
# The 1-morphism `Spec` of Stacks 05YQ at the raised morphism universe

The determinacy clause of Stacks 02ZN is consumed by the quotient-stack criterion
`AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_extend_toQuotientStack` at the morphism
universe the explicit stackification works in, which is one above the morphism universe of the big
fppf site. The 1-morphism `Spec` of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/FiniteFreeAlgebra/SpecFiniteCover.lean` and the two
clauses of Stacks 02ZN proved for it live one universe below. This file raises all three, and
records that `ℋ_d` is a stack in the sense of Stacks 026F at both universes.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.specFiniteCoverLift`: the morphism-universe lift of the
  1-morphism `Spec`.

## Main results

* `AlgebraicGeometry.Stack.isStack_finiteCoverProjection`: `ℋ_d` is a stack over the big fppf site
  in the sense of Stacks 026F.
* `AlgebraicGeometry.FiniteFreeAlgebra.isStack_uliftHomProj_finiteCoverProjection`: so is its
  morphism-universe lift.
* `AlgebraicGeometry.FiniteFreeAlgebra.isFibredOneMorphism_specFiniteCoverLift`: the lift of `Spec`
  is a 1-morphism of fibred categories over the site.
* `AlgebraicGeometry.FiniteFreeAlgebra.isLocallyBijective_specFiniteCoverLift` and
  `AlgebraicGeometry.FiniteFreeAlgebra.essImage_specFiniteCoverLift`: the two clauses of Stacks
  02ZN for the lift.

## Implementation notes

Nothing mathematical happens here. `ℋ_d` is a stack in groupoids in the sense of Stacks 02ZI by
`AlgebraicGeometry.Stack.isStackInGroupoids_finiteCoverProjection`, and the big fppf site over `S`
has fibre products, so Stacks 02ZI implies Stacks 026F by
`CategoryTheory.Functor.isStack_of_isStackInGroupoids` — at the index universe `max u₁ v₁` of the
site, which the source statement is polymorphic in. Everything else is the morphism-universe
transport of `StacksFrontier/CategoryTheory/Sites/Stack/Transport/UliftHomLocallyBijective.lean`
applied to the clauses already proved.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- **`ℋ_d` is a stack over the big fppf site of `S` in the sense of Stacks 026F.** It is a stack
in groupoids by `AlgebraicGeometry.Stack.isStackInGroupoids_finiteCoverProjection`, and the site
has fibre products, so the three conditions of Stacks 02ZI give the three of Stacks 026F. -/
theorem isStack_finiteCoverProjection :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsStack
      (BigFppfOver.topology B S hS) :=
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
    (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).isFibered
  Functor.isStack_of_isStackInGroupoids
    (isStackInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- The morphism-universe lift of the 1-morphism `Spec` of Stacks 05YQ: the same functor, read
between the morphism-universe lifts of the pointwise groupoid fibration of free rank-`d`
structures and of `ℋ_d`. -/
noncomputable abbrev specFiniteCoverLift :
    ULiftHom.{u + 1} (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj ⥤
      ULiftHom.{u + 1} (AlgebraicGeometry.Stack.FiniteCover 𝒞 S hS d) :=
  Functor.uliftHomMap (specFiniteCover 𝒞 S hS d)

omit [NeZero d] in
/-- **The morphism-universe lift of `ℋ_d` is a stack over the big fppf site.** -/
theorem isStack_uliftHomProj_finiteCoverProjection :
    (Functor.uliftHomProj (AlgebraicGeometry.Stack.finiteCoverProjection
        (B := 𝒞) (S := S) (hS := hS) (d := d)) :
      ULiftHom.{u + 1} (AlgebraicGeometry.Stack.FiniteCover 𝒞 S hS d) ⥤
        BigFppfOver 𝒞 S hS).IsStack (BigFppfOver.topology 𝒞 S hS) :=
  Functor.isStack_uliftHomProj _ _ AlgebraicGeometry.Stack.isStack_finiteCoverProjection

/-- **The lift of `Spec` is a 1-morphism of fibred categories over the big fppf site over `S`.** -/
theorem isFibredOneMorphism_specFiniteCoverLift :
    (Functor.uliftHomProj (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p :
        ULiftHom.{u + 1} (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj ⥤
          BigFppfOver 𝒞 S hS).IsFibredOneMorphism
      (Functor.uliftHomProj (AlgebraicGeometry.Stack.finiteCoverProjection
        (B := 𝒞) (S := S) (hS := hS) (d := d)))
      (specFiniteCoverLift 𝒞 S hS d) :=
  (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).uliftHom

/-- **Clause (1) of Stacks 02ZN for the lift of `Spec`.** -/
theorem isLocallyBijective_specFiniteCoverLift (U : BigFppfOver 𝒞 S hS)
    (a b : (Functor.uliftHomProj (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p :
      ULiftHom.{u + 1} (presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj ⥤
        BigFppfOver 𝒞 S hS).Fiber U) :
    CategoryTheory.Presheaf.IsLocallyInjective ((BigFppfOver.topology 𝒞 S hS).over U)
        ((isFibredOneMorphism_specFiniteCover 𝒞 S hS d).uliftHom.morPresheafMap a b) ∧
      CategoryTheory.Presheaf.IsLocallySurjective ((BigFppfOver.topology 𝒞 S hS).over U)
        ((isFibredOneMorphism_specFiniteCover 𝒞 S hS d).uliftHom.morPresheafMap a b) :=
  (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).isLocallyBijective_morPresheafMap_uliftHom
    (BigFppfOver.topology 𝒞 S hS) (isLocallyBijective_specFiniteCover) U a b

/-- **Clause (2) of Stacks 02ZN for the lift of `Spec`.** -/
theorem essImage_specFiniteCoverLift (U : BigFppfOver 𝒞 S hS)
    (x : (Functor.uliftHomProj (AlgebraicGeometry.Stack.finiteCoverProjection
      (B := 𝒞) (S := S) (hS := hS) (d := d)) :
        ULiftHom.{u + 1} (AlgebraicGeometry.Stack.FiniteCover 𝒞 S hS d) ⥤
          BigFppfOver 𝒞 S hS).Fiber U) :
    ∃ R ∈ BigFppfOver.topology 𝒞 S hS U,
      ∀ ⦃V : BigFppfOver 𝒞 S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).uliftHom.comp_eq V).essImage
          (Functor.pullbackFiber (Functor.uliftHomProj
            (AlgebraicGeometry.Stack.finiteCoverProjection
              (B := 𝒞) (S := S) (hS := hS) (d := d))) x f) :=
  (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).essImage_uliftHom
    (BigFppfOver.topology 𝒞 S hS) essImage_specFiniteCover U x

end AlgebraicGeometry.FiniteFreeAlgebra

end
