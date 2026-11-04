module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PastingFunctorial

/-!
# The property of Stacks 0CIG along an equivalence of sources

Let `P` be a property of morphisms of algebraic spaces over `S`. The universal étale-smooth
diagram test of condition (1) of **Stacks 0CIF** at `P`, and with it the property of
Deligne–Mumford 1-morphisms of algebraic stacks that **Stacks 0CIG** induces from `P`, only
depends on a 1-morphism up to precomposition with an equivalence and up to an invertible
2-morphism. Consequently such a property, once known for the base change of `f` along `g` read
off the *canonical* 2-fibre product square, holds for the base change read off *every* 2-fibre
product square of `(f, g)`.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_isEquivalence_comp`: the
  universal étale-smooth diagram test passes from `f₂` to `f₁` when `φ ≫ f₂ ≅ f₁` with `φ` an
  equivalence.
* `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_of_isEquivalence_comp`: the same for the
  property of Stacks 0CIG.
* `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_snd_of_isTwoFibreProduct`: from the
  canonical 2-fibre product square of `(f, g)` to an arbitrary one.

## Implementation notes

A diagram `(a, b, h, η)` over `f₁` is turned into the diagram `(a ≫ φ, b ≫ 𝟙, h, -)` over `f₂`
whose cone is the rectangle obtained by pasting the cone of the first diagram onto the square
`E` with apex the source of `f₁`, legs `f₁` and `φ`, over the cospan `(𝟙, f₂)`. Because `φ` is
an equivalence, `E` is a 2-fibre product: its comparison into the degenerate 2-fibre product
`CategoryTheory.Bicategory.TwoCommSq.idCospan` is `φ` itself
(`CategoryTheory.Bicategory.toIdCospan`). Pasting a 2-fibre product of `(b, f₁)` onto `E` then
gives a 2-fibre product of `(b ≫ 𝟙, f₂)`, and pasting carries the comparison 1-morphism into it
along unchanged, so the étale clause of the new diagram is the étale clause of the old one. The
right-hand vertical 1-morphism of the new diagram is `b ≫ 𝟙` rather than `b`, which is why it is
the pasted rectangle on the nose; its smoothness is that of `b`, through the right unitor.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The universal étale-smooth diagram test is invariant under precomposition with an
equivalence.** Let `f₁ : 𝒳₁ ⟶ 𝒴` and `f₂ : 𝒳₂ ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S`
and `φ : 𝒳₁ ⟶ 𝒳₂` a 1-morphism whose underlying functor is an equivalence, with an invertible
2-morphism `φ ≫ f₂ ≅ f₁`. If every étale-smooth diagram over `f₂` has top horizontal morphism
with `P`, then so does every étale-smooth diagram over `f₁`. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_of_isEquivalence_comp
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳₁ 𝒳₂ 𝒴 : AlgebraicStacks.{u, w} B S hS} (φ : 𝒳₁ ⟶ 𝒳₂) (f₁ : 𝒳₁ ⟶ 𝒴) (f₂ : 𝒳₂ ⟶ 𝒴)
    (θ : φ.hom ≫ f₂.hom ≅ f₁.hom) (hφ : φ.hom.hom.toFunctor.IsEquivalence)
    (hf₂ : HasPropertyOnEveryEtaleSmoothDiagram B S hS P f₂) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f₁ := by
  classical
  intro U V hU hV a b h η hb hk
  -- the square `E` over `(𝟙 𝒴, f₂)` with legs `f₁` and `φ`, a 2-fibre product since `φ` is an
  -- equivalence
  let E : Bicategory.TwoCommSq (𝟙 𝒴.val) f₂.hom :=
    { pt := 𝒳₁.val
      fst := f₁.hom
      snd := φ.hom
      iso := Bicategory.rightUnitor f₁.hom ≪≫ θ.symm }
  have hE : Bicategory.IsTwoFibreProduct E :=
    Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (Bicategory.isTwoFibreProduct_idCospan f₂.hom) (Bicategory.toIdCospan E) hφ
  -- one étale comparison out of the cone of the given diagram
  have hQ₁ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f₁.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom f₁.hom
  let k₁ := Quotient.out (hQ₁.from (diagramCone B S hS f₁.hom a.hom b.hom h η))
  have hb' : IsRelativelySmooth B S hS (Bicategory.InducedBicategory.mkHom
      (b.hom ≫ 𝟙 𝒴.val) : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴).hom :=
    isRelativelySmooth_congr_twoIso B S hS (Bicategory.rightUnitor b.hom).symm hb
  exact hf₂ U V hU hV (a ≫ φ) (Bicategory.InducedBicategory.mkHom (b.hom ≫ 𝟙 𝒴.val)) h
    (E.pasteFst (diagramCone B S hS f₁.hom a.hom b.hom h η)).iso hb'
    (isRelativelyEtale_preHom_of_one B S hS
      (Bicategory.isTwoFibreProduct_pasteFst E hE _ hQ₁)
      (Bicategory.TwoCommSq.PreHom.pasteFst E k₁) (hk _ hQ₁ k₁))

/-- **The property of Stacks 0CIG is invariant under precomposition with an equivalence.** With
`φ ≫ f₂ ≅ f₁` and `φ` an equivalence, `f₁` has the property Stacks 0CIG induces from `P` as soon
as `f₂` has it: the Deligne–Mumford condition transfers by
`AlgebraicGeometry.Stack.isDM_of_equivalence` and the diagram test by
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_isEquivalence_comp`. -/
theorem hasEtaleSmoothLocalProperty_of_isEquivalence_comp
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳₁ 𝒳₂ 𝒴 : AlgebraicStacks.{u, w} B S hS} (φ : 𝒳₁ ⟶ 𝒳₂) (f₁ : 𝒳₁ ⟶ 𝒴) (f₂ : 𝒳₂ ⟶ 𝒴)
    (θ : φ.hom ≫ f₂.hom ≅ f₁.hom) (hφ : φ.hom.hom.toFunctor.IsEquivalence)
    (hf₂ : HasEtaleSmoothLocalProperty B S hS P f₂) :
    HasEtaleSmoothLocalProperty B S hS P f₁ :=
  ⟨isDM_of_equivalence B S hS f₂ f₁ φ.hom.hom (twoIsoHomIso B S hS θ) hφ hf₂.1,
    hasPropertyOnEveryEtaleSmoothDiagram_of_isEquivalence_comp B S hS P φ f₁ f₂ θ hφ hf₂.2⟩

/-- **The property of Stacks 0CIG on a base change does not depend on the 2-fibre product.** If
the second projection of the canonical 2-fibre product square of `(f, g)` has the property
Stacks 0CIG induces from `P`, then so does the second projection of every 2-fibre product square
`R` of `(f, g)`: the comparison of `R` with the canonical square is an equivalence, through which
the two projections agree up to an invertible 2-morphism. -/
theorem hasEtaleSmoothLocalProperty_snd_of_isTwoFibreProduct
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hcan : HasEtaleSmoothLocalProperty B S hS P
      (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd) :
    HasEtaleSmoothLocalProperty B S hS P R.snd := by
  have hQ := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS f g
  let d : Bicategory.TwoCommSq.PreHom R (AlgebraicStacks.twoFibreProductSquare B S hS f g) :=
    _root_.Quotient.out (hQ.from R)
  exact hasEtaleSmoothLocalProperty_of_isEquivalence_comp B S hS P d.hom R.snd
    (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd
    (algStackHomIso B S hS d.isoSnd.symm)
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hR hQ d) hcan

end AlgebraicGeometry.Stack

end
