module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackSeparated
public import StacksFrontier.CategoryTheory.FiberedCategory.PullbackPseudofunctorBaseChange

/-!
# The agreement condition over the exceptional corner is h local

Fullness of the comparison functor of a cartesian square,
`AlgebraicGeometry.BigHOver.exists_fiberHom`, consumes a morphism `a` over the centre and a
morphism `c` over the modification together with the hypothesis that they *agree over the
exceptional corner*: that the square

```
  e^* a ≫ cmpIso.app y = cmpIso.app x ≫ d^* c
```

commutes in the fibre over the corner, `cmpIso` being the structural isomorphism of the comparison
functor.  When `a` and `c` are pulled back from one morphism over the base this is naturality of
`cmpIso`; in the application they are not, and the hypothesis has to be produced.

This file reduces it to a local statement: the square commutes as soon as it commutes after base
change along every member of an h covering family of the corner.  Two facts make the reduction
immediate.  Equality of morphisms of a fibre is h local — that is
`AlgebraicGeometry.BigHOver.eq_of_pullbackFiberHom_eq_of_covering`, conditions (1), (2) and (3) of
Stacks 0EX9 run together — and the comparison morphism of two cartesian structures is compatible
with base change, which is
`CategoryTheory.Functor.IsFibered.CartStruct.pullbackFiberHom_cmpMor`.

## Main results

* `AlgebraicGeometry.BigHOver.fiberPullback_map_comp_iso_eq_of_covering`: the agreement condition
  over the exceptional corner, from its base changes along an h covering family of the corner.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.IsFibered CategoryTheory.Functor.IsFibered.CartStruct

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]

/-- The cartesian structure of the composite `d ≫ b` around a cartesian square, read over the
other composite `e ≫ z`.  This is the second argument of the structural isomorphism of
`AlgebraicGeometry.BigHOver.twoFibreProductComparison`, named so that it can be spoken about. -/
public def cartCompOfSquare {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) {z : Z ⟶ X} (d : E ⟶ X')
    {e : E ⟶ Z} (hsq : IsPullback e d z b) :
    CartStruct p (e ≫ z) (fiberPullback (p := p) b ⋙ fiberPullback (p := p) d) :=
  hsq.w ▸ cartComp b d

/-- The structural isomorphism of the comparison functor of a cartesian square, at an object of
the fibre over the base, is the comparison morphism of the two cartesian structures around the
square. -/
public theorem twoFibreProductComparison_obj_iso_hom
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hsq : IsPullback e d z b) (w : p.Fiber X) :
    ((twoFibreProductComparison B S hS p b z d e hsq).obj w).iso.hom =
      cmpMor (cartComp z e) (cartCompOfSquare b d hsq) w := rfl

/-- **The agreement condition over the exceptional corner is h local.** For a category fibred in
groupoids satisfying conditions (1), (2) and (3) of Stacks 0EX9, a morphism `a` over the centre of
a cartesian square and a morphism `c` over its modification agree over the exceptional corner as
soon as their base changes along every member of an h covering family of the corner do.

This is the hypothesis of `AlgebraicGeometry.BigHOver.exists_fiberHom`, and the local form it is
reduced to is the same condition for the two cartesian structures composed with the chosen
cartesian structure of the covering morphism, by
`CategoryTheory.Functor.IsFibered.CartStruct.pullbackFiberHom_cmpMor`. -/
public theorem fiberPullback_map_comp_iso_eq_of_covering
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hsq : IsPullback e d z b) {x y : p.Fiber X}
    (a : (fiberPullback (p := p) z).obj x ⟶ (fiberPullback (p := p) z).obj y)
    (c : (fiberPullback (p := p) b).obj x ⟶ (fiberPullback (p := p) b).obj y)
    {I : Type (u + 1)} {V : I → BigHOver B S hS} (γ : ∀ i, V i ⟶ E)
    (hγ : Sieve.ofArrows V γ ∈ BigHOver.topology B S hS E)
    (hloc : ∀ i,
      Functor.pullbackFiberHom ((fiberPullback (p := p) e).map a) (γ i) ≫
          cmpMor (CartStruct.comp (cartComp z e) (cartPullback (γ i)))
            (CartStruct.comp (cartCompOfSquare b d hsq) (cartPullback (γ i))) y =
        cmpMor (CartStruct.comp (cartComp z e) (cartPullback (γ i)))
            (CartStruct.comp (cartCompOfSquare b d hsq) (cartPullback (γ i))) x ≫
          Functor.pullbackFiberHom ((fiberPullback (p := p) d).map c) (γ i)) :
    (fiberPullback (p := p) e).map a ≫
        ((twoFibreProductComparison B S hS p b z d e hsq).obj y).iso.hom =
      ((twoFibreProductComparison B S hS p b z d e hsq).obj x).iso.hom ≫
        (fiberPullback (p := p) d).map c := by
  have key : (fiberPullback (p := p) e).map a ≫
        cmpMor (cartComp z e) (cartCompOfSquare b d hsq) y =
      cmpMor (cartComp z e) (cartCompOfSquare b d hsq) x ≫ (fiberPullback (p := p) d).map c := by
    refine eq_of_pullbackFiberHom_eq_of_covering h1 h2 h3 h4 _ _ γ hγ fun i ↦ ?_
    rw [Functor.pullbackFiberHom_comp, Functor.pullbackFiberHom_comp,
      pullbackFiberHom_cmpMor, pullbackFiberHom_cmpMor]
    exact hloc i
  exact key

end BigHOver

end AlgebraicGeometry

end
