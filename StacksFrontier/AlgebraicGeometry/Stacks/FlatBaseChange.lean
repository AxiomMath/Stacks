module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange

/-!
# Base change of flatness for 1-morphisms of algebraic stacks (Stacks 06PY)

**Stacks 06PY** says that a base change of a flat 1-morphism of algebraic stacks over `S` is flat.

The source proves it by combining the base-change remark **Stacks 06FQ** with the base-change
statement **Stacks 03MO** for morphisms of algebraic spaces, and that is the route taken here.
Stacks 06FQ turns a property of morphisms of algebraic spaces which is smooth local on the
source-and-target, and whose restriction to algebraic spaces is stable under base change, into a
property of 1-morphisms of algebraic stacks — through the *existential* smooth-diagram criterion
of **Stacks 06FM** — that is stable under base change along an arbitrary 2-fibre-product square.

Flatness of a 1-morphism of algebraic stacks is **Stacks 06PW**, which inlines that existential
criterion, so no round trip through the universal criterion is needed: the identification is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram`, an `Iff.rfl`.
This is the one respect in which the proof is shorter than its finiteness siblings
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_baseChange` (Stacks 06FU) and
`...isLocallyOfFinitePresentation_baseChange` (Stacks 06Q4), whose notions are defined over the
universal criterion of Stacks 06FS and Stacks 06Q2 part (1).

Flatness of morphisms of algebraic spaces is smooth local on the source-and-target by
**Stacks 06FC** at the flat case, and stable under base change by **Stacks 03MO**.

No comparison 1-morphism is built: both ingredients take a square that is merely *recognised* as a
2-fibre product, so there is nothing to transport along.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_baseChange`: **Stacks 06PY**.

## Implementation notes

The source lemma asserts one proposition, so the tag's covering set is one declaration.

The base-change stability of flatness is supplied as a `letI` rather than left to instance search,
because `AlgebraicGeometry.Stack.spaceProperty` wraps the property in an inverse image and the
library's `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` is stated at that wrapped
spelling; the composition sibling
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_comp` (Stacks 06PX) needs no such instance because
Stacks 06FP takes composition stability as an explicit hypothesis.

## References

* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A base change of a flat 1-morphism of algebraic stacks over `S` is flat: if `P` is a 2-fibre
product of the cospan `(g, f)` and `f` is flat, then the projection `P.fst` is flat. -/
@[stacks 06PY]
theorem isFlat_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsFlat B S hS f) :
    IsFlat B S hS P.fst :=
  let : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS P.fst).2
    (Stack.hasPropertyOnSomeSmoothDiagram_baseChange B S hS
      (fun _ _ h => Space.IsFlat B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f g P hP
      ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hf))

/-- **Flatness of a 1-morphism of algebraic stacks is unchanged by precomposition with an
equivalence.** If the functor underlying `k : 𝒵 ⟶ 𝒳` is an equivalence of categories and
`f : 𝒳 ⟶ 𝒴` is flat, then so is `k ≫ f`.

**Stacks 003Z**, part (2) turns the equivalence of underlying categories into a quasi-inverse
`e : 𝒳 ⟶ 𝒵` over the site with both 2-cells over identities, so `f` is 2-isomorphic to
`e ≫ (k ≫ f)` and the existential smooth-diagram criterion of **Stacks 06FM** moves along `e` by
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence`. -/
theorem isFlat_comp_of_isEquivalence {𝒵 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒵 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom))
    (hf : IsFlat B S hS f) :
    IsFlat B S hS (k ≫ f) := by
  obtain ⟨F, hF, η, ε, -, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒵.val.val.p 𝒳.val.val.p
      𝒵.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p k.hom) hk
  have he : Functor.IsEquivalence F :=
    (CategoryTheory.Equivalence.mk F (CatFiberedInGroupoids.homFunctor k.hom) ε.symm
      η).isEquivalence_functor
  have hiso : (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩ : 𝒳.val ⟶ 𝒵.val) ≫ k.hom ≅
      𝟙 𝒳.val :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
      (F := BasedFunctor.comp ⟨F, hF⟩ k.hom.hom) (G := BasedFunctor.id 𝒳.val.val) ε hε)
  refine (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (k ≫ f)).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS
      (fun _ _ h => Space.IsFlat B S hS h) (k ≫ f).hom f.hom
      (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩) he ?_
      ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hf))
  exact (Bicategory.leftUnitor f.hom).symm ≪≫ Bicategory.whiskerRightIso hiso.symm f.hom ≪≫
    Bicategory.associator
      (Bicategory.InducedBicategory.mkHom (⟨F, hF⟩ : 𝒳.val.val ⥤ᵇ 𝒵.val.val)) k.hom f.hom

end AlgebraicGeometry.Stack.AlgebraicStacks

end
