module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone

/-!
# A morphism of smooth lifts is étale on the ambient spaces, given 0CJC (Stacks 0CJS)

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S`, an algebraic space `W` over `S` and
a smooth 1-morphism `x : W ⟶ 𝒳`, and consider the category
`AlgebraicGeometry.Stack.EtaleSmoothLift` of smooth lifts of étale opens of `W` along `ι`
(**Stacks 0CJP**). Stacks 0CJS says that for a morphism `(f, f', γ)` of that category the
component `f'` between the ambient algebraic spaces is étale.

The source's proof has two steps. First, `f` is étale: it is a morphism of the spaces-étale site
of `W`, so it is a factor of one étale structure morphism through another and **Stacks 03FV**
applies. Second, the two objects of the category are cartesian squares over `ι` with smooth
right-hand legs, so `(f, f')` is a morphism of thickenings over the thickening `ι`, satisfying
the hypotheses of **Stacks 0CJC**: the ambient map of the target is locally of finite type and
that of the source is flat and locally of finite presentation, all three because they are
smooth. The étale clause of that lemma then carries étaleness from `f` to `f'`.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_base`: the component `f` of a morphism of
  smooth lifts is étale, which is **Stacks 03FV** on the spaces-étale site of `W`.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_ambient`: the component `f'` is étale, given
  the étale clause of Stacks 0CJC as the hypothesis `hCJC`. The unconditional statement of
  **Stacks 0CJS** is `AlgebraicGeometry.Stack.EtaleSmoothLift.Hom.isEtale_ambient`, in
  `StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleAmbient`, which carries the tag.

## Implementation notes

**The carried hypothesis `hCJC`, and what it is.** Stacks 0CJC is Lemma 106.5.2, an eleven-clause
list of properties of a 1-morphism of algebraic stacks invariant along a commutative diagram of
thickenings. Its clause (9), étaleness, is exactly what 0CJS invokes. When this file was written
that clause was not yet in the library; it now is, unconditionally, as
`AlgebraicGeometry.Stack.isEtale_ambient_of_isEtale` (registered as Stacks 0CJC "etale" through
`AlgebraicGeometry.Stack.isEtale_iff_isEtale_ambient`), proved by the separate chart reduction
through a surjective *étale* chart of `V' ×_{𝒴'} 𝒳'` that the source uses for clauses (8) and
(9). The hypothesis `hCJC` is therefore redundant: it is discharged in
`AlgebraicGeometry.Stack.isEtale_of_isTwoFibreProduct_of_isThickening`, and the unconditional
**Stacks 0CJS** is `AlgebraicGeometry.Stack.EtaleSmoothLift.Hom.isEtale_ambient`. The
declaration below is kept, untagged, as the conditional form.

The hypothesis `hCJC` below is that missing clause, written out for the base thickening `ι` in
the only shape in which 0CJS uses it: for two cartesian squares over `ι` whose right-hand legs
`x'` and `y'` are 1-morphisms from algebraic spaces, with the target's leg locally of finite type
and the source's leg flat and locally of finite presentation, and for a morphism `(f, f', γ)` of
those squares over `𝒳'` — the restriction equation `i ≫ f' = f ≫ j` together with the coherence
between the two fillers and `γ` — étaleness of `f` gives étaleness of `f'`. Nothing about the
category of smooth lifts enters the hypothesis, and the data it asks for is exactly the data of
a commutative diagram of thickenings as in 0CJC; it is *not* the conclusion being proved, which
is about an arbitrary morphism of `AlgebraicGeometry.Stack.EtaleSmoothLift`.

What is proved here is the rest of the source's argument: étaleness of `f` from the spaces-étale
site of `W`, and the verification that a morphism of smooth lifts supplies 0CJC with every
hypothesis it asks for — the two cartesian squares, the restriction equation, the comparison
2-morphism and its coherence, and the three finiteness and flatness conditions, which come from
smoothness of the two ambient maps by **Stacks 0DNP**, **Stacks 06Q5** and the flatness of a
smooth 1-morphism of algebraic stacks.

**Inherited caveat.** Thickenings of algebraic stacks are
`AlgebraicGeometry.Stack.IsThickening` (**Stacks 0BPP**, part (1)), which omits the
homeomorphism-of-underlying-spaces clause of the source for want of a library site for the point
topology of Stacks 04XL. That omission is inherited here, through
`AlgebraicGeometry.Stack.EtaleSmoothLift`.

## References

* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJS](https://stacks.math.columbia.edu/tag/0CJS)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- **The base component of a morphism of smooth lifts is étale.** A morphism of smooth lifts
lies over a morphism `f : U ⟶ V` of the spaces-étale site of `W`, so `f` is a factor of the
étale structure morphism `a : U ⟶ W` through the étale structure morphism `b : V ⟶ W` and
**Stacks 03FV** applies. -/
theorem isEtale_base (ξ η : EtaleSmoothLift B S hS ι hι W x hx) (m : ξ ⟶ η) :
    Space.IsEtale B S hS (Hom.base m).hom.left.hom := by
  refine MorphismProperty.of_postcomp (Space.etaleMorphisms B S hS)
    (W' := Space.etaleMorphisms B S hS) (Hom.base m).hom.left η.base.obj.hom η.base.property ?_
  rw [Over.w (Hom.base m).hom]
  exact ξ.base.property

/-- **Stacks 0CJS, given the étale clause of 0CJC as a hypothesis.** For a morphism `(f, f', γ)`
of smooth lifts of étale opens of `W` along the thickening `ι`, the component `f' : U' ⟶ V'`
between the ambient algebraic spaces is étale, given `hCJC`.

The unconditional statement, which carries the tag Stacks 0CJS, is
`AlgebraicGeometry.Stack.EtaleSmoothLift.Hom.isEtale_ambient`: `hCJC` holds, by
`AlgebraicGeometry.Stack.isEtale_of_isTwoFibreProduct_of_isThickening`.

The hypothesis `hCJC` is the étale clause, item (9), of **Stacks 0CJC** for the thickening `ι`,
written out for a morphism of two cartesian squares over `ι` whose right-hand legs come from
algebraic spaces: given that the target's leg `y'` is locally of finite type, that the source's
leg `x'` is flat and locally of finite presentation, that the two squares are 2-fibre products,
and that `(f, f', γ)` is a morphism of them over `𝒳'`, étaleness of `f` gives étaleness of `f'`.
See the implementation notes for where that clause is proved.

Everything 0CJC asks for is supplied here from the two smooth lifts and the morphism between
them: the squares are their `isTwoFibreProduct` fields, the restriction equation, the comparison
2-morphism and its coherence are the fields of the morphism, and the three conditions on `x'`
and `y'` follow from smoothness of the ambient maps — local finite presentation by
**Stacks 0DNP**, local finite type by **Stacks 06Q5** on top of it, and flatness by
monotonicity of the smooth-diagram criterion. Étaleness of `f` is `isEtale_base`. -/
theorem isEtale_ambient
    (hCJC : ∀ (U U' V V' : AlgebraicSpaces B S hS) (i : U ⟶ U') (j : V ⟶ V')
      (u : (algebraicSpaceStackFunctor B S hS).obj U ⟶ 𝒳)
      (v : (algebraicSpaceStackFunctor B S hS).obj V ⟶ 𝒳)
      (x' : (algebraicSpaceStackFunctor B S hS).obj U' ⟶ 𝒳')
      (y' : (algebraicSpaceStackFunctor B S hS).obj V' ⟶ 𝒳')
      (α : u ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x')
      (β : v ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map j ≫ y'),
      IsTwoFibreProduct
          (⟨(algebraicSpaceStackFunctor B S hS).obj U, u,
            (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x') →
        IsTwoFibreProduct
            (⟨(algebraicSpaceStackFunctor B S hS).obj V, v,
              (algebraicSpaceStackFunctor B S hS).map j, β⟩ : TwoCommSq ι y') →
          AlgebraicStacks.IsFlat B S hS x' →
            AlgebraicStacks.IsLocallyOfFinitePresentation B S hS x' →
              AlgebraicStacks.IsLocallyOfFiniteType B S hS y' →
                ∀ (f : U ⟶ V) (f' : U' ⟶ V')
                  (hL : u ≫ ι = (algebraicSpaceStackFunctor B S hS).map f ≫ (v ≫ ι)),
                  i ≫ f' = f ≫ j →
                    ∀ (γ : x' ⟶ (algebraicSpaceStackFunctor B S hS).map f' ≫ y')
                      (hR : (algebraicSpaceStackFunctor B S hS).map f ≫
                          ((algebraicSpaceStackFunctor B S hS).map j ≫ y') =
                        (algebraicSpaceStackFunctor B S hS).map i ≫
                          ((algebraicSpaceStackFunctor B S hS).map f' ≫ y')),
                      α.hom ≫ ((algebraicSpaceStackFunctor B S hS).map i ◁ γ) =
                          eqToHom hL ≫
                            ((algebraicSpaceStackFunctor B S hS).map f ◁ β.hom) ≫ eqToHom hR →
                        Space.IsEtale B S hS f.hom → Space.IsEtale B S hS f'.hom)
    (ξ η : EtaleSmoothLift B S hS ι hι W x hx) (m : ξ ⟶ η) :
    Space.IsEtale B S hS (Hom.ambient m).hom :=
  hCJC ξ.base.obj.left ξ.ambient η.base.obj.left η.ambient ξ.inclusion η.inclusion
    ((algebraicSpaceStackFunctor B S hS).map ξ.base.obj.hom ≫ x)
    ((algebraicSpaceStackFunctor B S hS).map η.base.obj.hom ≫ x)
    ξ.ambientMap η.ambientMap ξ.comm η.comm ξ.isTwoFibreProduct η.isTwoFibreProduct
    (AlgebraicStacks.isFlat_of_isSmooth B S hS _ ξ.isSmooth_ambientMap)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _
      ξ.isSmooth_ambientMap)
    (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _
        η.isSmooth_ambientMap))
    (Hom.base m).hom.left (Hom.ambient m) (left_leg ξ η (Hom.base m)) (Hom.inclusion_comp m)
    (Hom.comm m)
    (right_leg ξ η (Hom.base m) (Hom.ambient m) (Hom.inclusion_comp m))
    (Hom.coherence m) (isEtale_base ξ η m)

end EtaleSmoothLift

end AlgebraicGeometry.Stack

end
