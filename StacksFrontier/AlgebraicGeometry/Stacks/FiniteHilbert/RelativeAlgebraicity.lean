module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FiniteHilbertEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.AbsoluteAlgebraicity
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Faithful
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductFibreEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangedFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationAlgebraicStack
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.TwoFibreProductSetoid
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase

/-!
# Algebraicity of the relative finite Hilbert stack (Stacks 06CI)

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a positive natural number. **Stacks 06CI** says that if `𝒳` is representable by an
algebraic space and `F` is representable by algebraic spaces, surjective, flat and locally of
finite presentation, then the relative finite Hilbert stack `ℋ_d(𝒳/𝒴)` is an algebraic stack.
This file proves it, establishing the three nontrivial clauses of
`AlgebraicGeometry.Stack.IsAlgebraicStack` from those hypotheses.

The stack condition is obtained by a route that avoids descending the cover (condition (3) of
**Stacks 05WB**, which rests on Tag 0245): the 1-morphism
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD is representable by algebraic spaces (**Stacks
05YH**), the product `ℋ_d(𝒳) × 𝒴` is a stack (**Stacks 026G**, from `ℋ_d(𝒳)` being an algebraic
stack by **Stacks 05YS** and from `𝒴` being a stack), and **Stacks 05UN** transports the stack
condition to the source of a 1-morphism representable by algebraic spaces.

Representability of the diagonal is **Stacks 05XW** applied to a flat presentation of
`ℋ_d(𝒳/𝒴)`: the base change along Equation 05WD of the product `g × F` of an atlas `g` of
`ℋ_d(𝒳)` with `F` is representable by an algebraic space (**Stacks 0300**, the product `𝒰 × 𝒳`
of an algebraic space with an algebraic space being one), and it is surjective, flat and locally
of finite presentation over `ℋ_d(𝒳/𝒴)` by **Stacks 045E** and **Stacks 045C**.

The atlas clause is the source's own argument. Writing `𝒰` for a scheme atlas of `ℋ_d(𝒳)` and
`𝒲 = ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳)} 𝒰`, the 1-morphism `𝒲 ⟶ ℋ_d(𝒳/𝒴)` is a base change of `𝒰 ⟶ ℋ_d(𝒳)`,
hence representable by algebraic spaces, surjective and smooth (**Stacks 0302** and **Stacks
045C**), so **Stacks 05UL** finishes the proof once `𝒲` is representable by an algebraic space.
That is the engine of **Stacks 04SZ**,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange`,
applied to `𝒲`: it is a stack in setoids because `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` is faithful (**Stacks
05XV**, and this is where positivity of `d` is used) and `𝒰` is representable by an algebraic
space (**Stacks 05UI**), and the flat presentation of `ℋ_d(𝒳/𝒴)` base changes along
`𝒲 ⟶ ℋ_d(𝒳/𝒴)` to one of `𝒲`, which also makes the fibres of `𝒲` essentially small.

## Main results

* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_targetCFG_of_flatPresentation`: Stacks 05XW
  read at `F`, the diagonal of the target `𝒴` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpacesForgetToProduct_of_flatPresentation`:
  Stacks 05YH read under the hypotheses of Stacks 06CI.
* `AlgebraicGeometry.Stack.isStack_absoluteHilbertTargetProduct`: the product `ℋ_d(𝒳) × 𝒴` is a
  stack for the fppf topology.
* `AlgebraicGeometry.Stack.isStack_finiteHilbertCategory`: **the stack condition for
  `ℋ_d(𝒳/𝒴)`**, the first nontrivial clause of Stacks 06CI.
* `AlgebraicGeometry.Stack.isStackInSetoids_twoFibreProduct_forgetRelativeStructure`: Stacks
  05UI read at the faithful 1-morphism of Stacks 05XV — the 2-fibre product
  `ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳)} 𝒰` with a category representable by an algebraic space is a stack in
  setoids.
* `AlgebraicGeometry.Stack.exists_flatPresentation_finiteHilbertFibered`: the presentation of
  `ℋ_d(𝒳/𝒴)` by an algebraic space, surjective, flat and locally of finite presentation.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_finiteHilbertFibered`: **the diagonal clause
  of Stacks 06CI**, the diagonal of `ℋ_d(𝒳/𝒴)` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.essentiallySmall_fiber_hilbertAtlasSquare`: the fibres of
  `𝒲 = ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳)} 𝒰` are essentially small.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_hilbertAtlasSquare`: `𝒲` is
  representable by an algebraic space.
* `AlgebraicGeometry.Stack.isAlgebraicStack_finiteHilbertFibered`: **Stacks 06CI**, the relative
  finite Hilbert stack is an algebraic stack.

## Inputs

The second assertion of **Stacks 05YQ**, that the category `ℋ_d` of degree-`d` finite locally
free covers is an algebraic stack, is
`AlgebraicGeometry.Stack.isAlgebraicStack_finiteCoverFibered`; it enters through Stacks 05YS
(`AlgebraicGeometry.Stack.isAlgebraicStack_absoluteHilbertCategory`).

The bootstrap theorem **Stacks 04S6** part (3), which Stacks 05XW, Stacks 05UL and Stacks 04SZ
use, is the theorem `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.

Stacks 05YF, that a restriction of scalars along a finite locally free cover is an algebraic
space, enters through Stacks 05YH and Stacks 05YJ in its case of a base which is a scheme,
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree`.

The hypothesis `h𝒴`, the stack condition on `𝒴`, is the source's own standing hypothesis that
`𝒴` is a stack, in the sieve-indexed rendering `CategoryTheory.Functor.IsStack` of Stacks 026F
rather than the family-indexed `CategoryTheory.Functor.IsStackInGroupoids` of Stacks 02ZI that
`CategoryTheory.StackInGroupoids` bundles. The two are the conditions (1) and (3) of Stacks 02ZJ
and either may be assumed; the sieve-indexed one is what Stacks 05XW, Stacks 05UL and Stacks 05XY
all take, and it is needed here because Stacks 05XW is applied to `F`.

## Implementation notes

Positivity of `d` is the hypothesis of Stacks 05XV as stated here
(`AlgebraicGeometry.Stack.forgetRelativeStructure_faithful`): the proof there needs the
degree-`d` cover `Z ⟶ U` to be an fppf covering of `U`, which it is exactly when `d` is positive,
the degree-zero cover being empty. It is inherited here through the stack-in-setoids property of
`𝒲`, which is what the source's reduction of the atlas clause rests on.

## References

* [Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045E](https://stacks.math.columbia.edu/tag/045E)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 05UI](https://stacks.math.columbia.edu/tag/05UI)
* [Stacks Project, Tag 05UL](https://stacks.math.columbia.edu/tag/05UL)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05XV](https://stacks.math.columbia.edu/tag/05XV)
* [Stacks Project, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 05YS](https://stacks.math.columbia.edu/tag/05YS)
* [Stacks Project, Tag 06CI](https://stacks.math.columbia.edu/tag/06CI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local instance] Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- Hypothesis (2) of Stacks 06CI other than representability, in the longhand of Stacks 03YK:
every algebraic space representing a base change of `F` along a scheme-valued point of `𝒴` has
surjective, flat and locally finitely presented structural morphism. -/
abbrev RelativeFlatPresentation : Prop :=
  ∀ (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.toBasedCategory.obj)
    (_hy : y ⋙ 𝒴.toBasedCategory.p = Over.map V.hom)
    (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
        F.toFunctor)
      (presheafOfCategories (G ⋙ typeToCat)).p) →
    (let g := (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom
     Space.IsSurjective B S hS g ∧ Space.IsFlat B S hS g ∧
       Space.IsLocallyOfFinitePresentation B S hS g)

/-- **Stacks 05XW read at `F`.** Under the hypotheses of Stacks 06CI the diagonal
`𝒴 ⟶ 𝒴 × 𝒴` of the target is representable by algebraic spaces: `F` is a flat presentation of
`𝒴` by an algebraic space. -/
theorem hasRepresentableDiagonal_targetCFG_of_flatPresentation
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    HasRepresentableDiagonal B S hS (targetCFG (𝒴 := 𝒴)) :=
  hasRepresentableDiagonal_of_flatPresentation.{u, u + 1, u + 1} B S hS
    (Bicategory.InducedBicategory.mkHom
      (X := targetCFG (𝒴 := 𝒳)) (Y := targetCFG (𝒴 := 𝒴)) F)
    h𝒴 h𝒳 hF
    (fun V y hy G hG h => (hFprops V y hy G hG h).1)
    (fun V y hy G hG h => (hFprops V y hy G hG h).2.1)
    (fun V y hy G hG h => (hFprops V y hy G hG h).2.2)

/-- **Stacks 05YH read under the hypotheses of Stacks 06CI.** The 1-morphism
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD is representable by algebraic spaces, the hypothesis
of Stacks 05YH on the diagonal of `𝒴` being supplied by Stacks 05XW. -/
theorem isRepresentableByAlgebraicSpacesForgetToProduct_of_flatPresentation
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    IsRepresentableByAlgebraicSpacesForgetToProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) :=
  have : 𝒴.toBasedCategory.p.IsFibered :=
    𝒴.isStackInGroupoids.isFiberedInGroupoids.isFibered
  isRepresentableByAlgebraicSpacesForgetToProduct_of_diagonal
    (hasRepresentableDiagonal_targetCFG_of_flatPresentation h𝒴 h𝒳 hF hFprops)

/-- **The product `ℋ_d(𝒳) × 𝒴` is a stack** for the fppf topology, by Stacks 026G: it is the
2-fibre product of `ℋ_d(𝒳)` and `𝒴` over the site, which is itself a stack because it is
representable by an algebraic space. -/
theorem isStack_absoluteHilbertTargetProduct
    (hHd : Functor.IsStack
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (BigFppfOver.topology B S hS))
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS)) :
    Functor.IsStack (absoluteHilbertTargetProductProjection
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴))
      (BigFppfOver.topology B S hS) :=
  TwoFibreProductOver.isStack_structureFunctor _ _ _ _ _ _ hHd h𝒴
    (isStack_of_isRepresentableByAlgebraicSpace B S hS (terminalCFG B S hS)
      (isRepresentableByAlgebraicSpace_terminalCFG B S hS))
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids Functor.isFiberedInGroupoids_id
      (Functor.comp_id _))
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids Functor.isFiberedInGroupoids_id
      (Functor.comp_id _))

/-- **The relative finite Hilbert category `ℋ_d(𝒳/𝒴)` is a stack** for the fppf topology: the
1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD is representable by algebraic spaces and
its target is a stack, so Stacks 05UN applies. This needs no descent datum for `ℋ_d(𝒳/𝒴)` to be
effective, unlike condition (3) of Stacks 05WB. -/
theorem isStack_finiteHilbertCategory
    (hHd : Functor.IsStack
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (BigFppfOver.topology B S hS))
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (hrep : IsRepresentableByAlgebraicSpacesForgetToProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)) :
    Functor.IsStack
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (BigFppfOver.topology B S hS) :=
  isStack_of_isRepresentableByAlgebraicSpaces B S hS
    (Bicategory.InducedBicategory.mkHom
      (X := finiteHilbertFibered B S hS d 𝒳 𝒴 F)
      (Y := CatFiberedInGroupoids.product.{u, u, u + 1} (absoluteHilbertFibered 𝒳 d)
      (targetCFG (𝒴 := 𝒴)))
      (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)))
    hrep (isStack_absoluteHilbertTargetProduct hHd h𝒴)

/-- **Stacks 05UI read at the faithful 1-morphism of Stacks 05XV.** For positive degree `d`, the
2-fibre product of `ℋ_d(𝒳/𝒴)` with a category representable by an algebraic space over
`ℋ_d(𝒳)` is a stack in setoids: the 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` is faithful by Stacks 05XV
and a category representable by an algebraic space is a stack in setoids by Stacks 04SZ. -/
theorem isStackInSetoids_twoFibreProduct_forgetRelativeStructure (hd : 0 < d)
    (hHd : Functor.IsStack
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (BigFppfOver.topology B S hS))
    (hℋ : Functor.IsStack
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (BigFppfOver.topology B S hS))
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (gCat : 𝒰 ⟶ absoluteHilbertFibered 𝒳 d)
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰) :
    (TwoFibreProductOver.structureFunctor
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      𝒰.val.p
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor
      gCat.hom.toFunctor).IsStackInSetoids (BigFppfOver.topology B S hS) := by
  have : (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F)).toFunctor.Faithful := forgetRelativeStructure_faithful hd
  exact Functor.isStackInSetoids_twoFibreProduct _ hℋ
    isFiberedInGroupoids_finiteHilbertProjection
    (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒰 h𝒰) hHd
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids
      isFiberedInGroupoids_absoluteHilbertProjection
      (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).w)
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids
      isFiberedInGroupoids_absoluteHilbertProjection gCat.hom.w)

/-- **A flat presentation of `ℋ_d(𝒳/𝒴)` by an algebraic space.** Let `𝒰` be representable by an
algebraic space, with a 1-morphism `gCat : 𝒰 ⟶ ℋ_d(𝒳)` representable by algebraic spaces,
surjective and smooth. Under the hypotheses of Stacks 06CI the base change along Equation 05WD of
the product `gCat × F` is a 1-morphism to `ℋ_d(𝒳/𝒴)` out of a category representable by an
algebraic space which is representable by algebraic spaces, surjective, flat and locally of
finite presentation.

The product `𝒰 × 𝒳` is representable by an algebraic space by Stacks 0300 and the product
1-morphism is representable, surjective, flat and locally of finite presentation by Stacks 045E;
all four properties pass to the base change by Stacks 0300, Stacks 0302 and Stacks 045C. -/
theorem exists_flatPresentation_finiteHilbertFibered
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F))
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (gCat : 𝒰 ⟶ absoluteHilbertFibered 𝒳 d)
    (hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom)
    (hgsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) gCat hgCat)
    (hgsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) gCat hgCat) :
    ∃ (𝒬 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (v : 𝒬 ⟶ finiteHilbertFibered B S hS d 𝒳 𝒴 F)
      (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom),
      IsRepresentableByAlgebraicSpace B S hS 𝒬 ∧
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (Space.surjectiveMorphismProperty B S hS) v hv ∧
        @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
          (Space.isFlat_isStableUnderBaseChange B S hS)
          ((Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
            (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS))
          𝒬 (finiteHilbertFibered B S hS d 𝒳 𝒴 F) v hv ∧
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
            Space.IsLocallyOfFinitePresentation B S hS k.hom) v hv := by
  classical
  have hflatloc : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hlfpcomp : MorphismProperty.IsStableUnderComposition
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) :=
    ⟨fun {X Y Z} f g hf hg => Space.isLocallyOfFinitePresentation_comp B S hS X.property
      Y.property Z.property f.hom g.hom hf hg⟩
  let F' := Bicategory.InducedBicategory.mkHom
    (X := targetCFG (𝒴 := 𝒳)) (Y := targetCFG (𝒴 := 𝒴)) F
  have hF' : IsRepresentableByAlgebraicSpaces B S hS F'.hom := hF
  -- the product `𝒰 × 𝒳` and the product 1-morphism `gCat × F`
  let m := CatFiberedInGroupoids.productMap.{u, u, u + 1} gCat F'
  have hm : IsRepresentableByAlgebraicSpaces B S hS m.hom :=
    isRepresentableByAlgebraicSpaces_productMap.{u, u, u + 1} B S hS gCat F' hgCat hF'
  have h𝒫 : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.product.{u, u, u + 1} 𝒰 (targetCFG (𝒴 := 𝒳))) :=
    isRepresentableByAlgebraicSpace_product B S hS 𝒰 (targetCFG (𝒴 := 𝒳)) h𝒰 h𝒳
  have hmsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) m hm :=
    hasRelativeProperty_productMap.{u, u, u + 1, u + 1} B S hS _ gCat F' hgCat hF' hgsurj
      (fun V y hy G hG h => (hFprops V y hy G hG h).1)
  have hmflat : @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.isFlat_isStableUnderBaseChange B S hS) hflatloc _ _ m hm :=
    hasRelativeProperty_productMap.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      gCat F' hgCat hF'
      (fun V y hy G hG h => Space.isFlat_of_isSmooth B S hS _ (hgsmooth V y hy G hG h))
      (fun V y hy G hG h => (hFprops V y hy G hG h).2.1)
  have hmlfp : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) m hm :=
    hasRelativeProperty_productMap.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom)
      gCat F' hgCat hF'
      (fun V y hy G hG h =>
        Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hgsmooth V y hy G hG h))
      (fun V y hy G hG h => (hFprops V y hy G hG h).2.2)
  -- the base change of `gCat × F` along the 1-morphism of Equation 05WD
  have hrep : IsRepresentableByAlgebraicSpacesForgetToProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) :=
    isRepresentableByAlgebraicSpacesForgetToProduct_of_flatPresentation h𝒴 h𝒳 hF hFprops
  let j := Bicategory.InducedBicategory.mkHom
    (X := finiteHilbertFibered B S hS d 𝒳 𝒴 F)
    (Y := CatFiberedInGroupoids.product.{u, u, u + 1} (absoluteHilbertFibered 𝒳 d)
      (targetCFG (𝒴 := 𝒴)))
    (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F))
  have hj : IsRepresentableByAlgebraicSpaces B S hS j.hom := hrep
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} m j
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} m j
  have hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ j m Q hQ hj h𝒫
  let R := Q.swap
  have hR : Bicategory.IsTwoFibreProduct R := Bicategory.isTwoFibreProduct_swap hQ
  have hv : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ m j R hR hm
  exact ⟨Q.pt, R.fst, hv, hQpt,
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ m j R hR hm hmsurj,
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ m j R hR hm hmflat,
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ m j R hR hm hmlfp⟩

/-- `ℋ_d(𝒳)` is a stack with a surjective smooth scheme atlas, for `𝒳` an algebraic space. -/
private theorem exists_smooth_atlas_absoluteHilbertFibered [NeZero d]
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳))) :
    Functor.IsStack
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (BigFppfOver.topology B S hS) ∧
    ∃ (U : BigFppfOver B S hS) (gCat : schemeFibredCategory B S hS U ⟶ absoluteHilbertFibered 𝒳 d)
      (hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom),
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
        (Space.surjectiveMorphismProperty B S hS) gCat hgCat ∧
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
        (Space.smoothMorphismProperty B S hS) gCat hgCat := by
  obtain ⟨_hfib, ⟨hHd, _hgrp⟩, _hdiag, U, g, hg, hgprop⟩ :=
    isAlgebraicStack_absoluteHilbertCategory.{u, w} 𝒳 d h𝒳
  exact ⟨hHd, U, Bicategory.InducedBicategory.mkHom g, hg,
    fun V y hy G hG h => (hgprop V y hy G hG h).1,
    fun V y hy G hG h => (hgprop V y hy G hG h).2⟩

/-- **The diagonal of `ℋ_d(𝒳/𝒴)` is representable by algebraic spaces**, the second nontrivial
clause of Stacks 06CI. The base change along Equation 05WD of the product of a scheme atlas of
`ℋ_d(𝒳)` with `F` is a presentation of `ℋ_d(𝒳/𝒴)` by an algebraic space which is surjective,
flat and locally of finite presentation, so Stacks 05XW applies. -/
theorem hasRepresentableDiagonal_finiteHilbertFibered
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) [NeZero d] :
    HasRepresentableDiagonal B S hS (finiteHilbertFibered B S hS d 𝒳 𝒴 F) := by
  classical
  obtain ⟨hHdstk, U, gCat, hgCat, hgsurj, hgsmooth⟩ :=
    exists_smooth_atlas_absoluteHilbertFibered (d := d) h𝒳
  obtain ⟨𝒬, v, hv, h𝒬, hvsurj, hvflat, hvlfp⟩ :=
    exists_flatPresentation_finiteHilbertFibered h𝒴 h𝒳 hF hFprops
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) gCat hgCat hgsurj hgsmooth
  exact hasRepresentableDiagonal_of_flatPresentation.{u, u + 1, u + 1} B S hS v
    (isStack_finiteHilbertCategory hHdstk h𝒴
      (isRepresentableByAlgebraicSpacesForgetToProduct_of_flatPresentation h𝒴 h𝒳 hF hFprops))
    h𝒬 hv hvsurj hvflat hvlfp

/-- The forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` of Equation 05WD, read in the 2-category of
categories fibred in groupoids over the big fppf site of `S`. -/
noncomputable abbrev forgetRelativeStructureFibered :
    finiteHilbertFibered B S hS d 𝒳 𝒴 F ⟶ absoluteHilbertFibered 𝒳 d :=
  Bicategory.InducedBicategory.mkHom
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F))

/-- The 2-cartesian square of the source's proof of Stacks 06CI: its apex is the 2-fibre product
`𝒲 = ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳), g} 𝒰` of the relative finite Hilbert category with a category `𝒰`
over `ℋ_d(𝒳)`, and its first projection is `𝒲 ⟶ ℋ_d(𝒳/𝒴)`. -/
noncomputable abbrev hilbertAtlasSquare
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (gCat : 𝒰 ⟶ absoluteHilbertFibered 𝒳 d) :
    Bicategory.TwoCommSq
      (forgetRelativeStructureFibered (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)) gCat :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} _ gCat

/-- **`𝒲 = ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳)} 𝒰` is a stack** for the fppf topology, by Stacks 026G: all three
corners of the defining square are, `𝒰` because it is representable by an algebraic space. -/
theorem isStack_hilbertAtlasSquare
    (hHd : Functor.IsStack
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (BigFppfOver.topology B S hS))
    (hℋ : Functor.IsStack
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (BigFppfOver.topology B S hS))
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (gCat : 𝒰 ⟶ absoluteHilbertFibered 𝒳 d) :
    Functor.IsStack (hilbertAtlasSquare (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F) gCat).pt.val.p (BigFppfOver.topology B S hS) :=
  TwoFibreProductOver.isStack_structureFunctor _ _ _ _ _ _ hℋ
    (isStack_of_isRepresentableByAlgebraicSpace B S hS 𝒰 h𝒰) hHd
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids
      isFiberedInGroupoids_absoluteHilbertProjection
      (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).w)
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids
      isFiberedInGroupoids_absoluteHilbertProjection gCat.hom.w)

/-- **The projection `𝒲 ⟶ ℋ_d(𝒳/𝒴)` is representable by algebraic spaces**, being a base change
of `𝒰 ⟶ ℋ_d(𝒳)` (Stacks 0302). -/
theorem isRepresentableByAlgebraicSpaces_hilbertAtlasSquare_fst
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (gCat : 𝒰 ⟶ absoluteHilbertFibered 𝒳 d)
    (hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom) :
    IsRepresentableByAlgebraicSpaces B S hS
      (hilbertAtlasSquare (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F) gCat).fst.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ gCat _ _
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ gCat)
    hgCat

/-- **The fibres of `𝒲 = ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳)} 𝒰` are essentially small**, which is the one
hypothesis of the engine of Stacks 04SZ that would need algebraicity of `ℋ_d(𝒳/𝒴)`.

The flat presentation of `ℋ_d(𝒳/𝒴)` of
`AlgebraicGeometry.Stack.exists_flatPresentation_finiteHilbertFibered` base changes along
`𝒲 ⟶ ℋ_d(𝒳/𝒴)` to a flat presentation of `𝒲` whose source is representable by an algebraic
space, and essential smallness of the fibres descends along it. -/
theorem essentiallySmall_fiber_hilbertAtlasSquare
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F))
    (hHd : Functor.IsStack
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (BigFppfOver.topology B S hS))
    (hℋ : Functor.IsStack
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (BigFppfOver.topology B S hS))
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (gCat : 𝒰 ⟶ absoluteHilbertFibered 𝒳 d)
    (hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom)
    (hgsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) gCat hgCat)
    (hgsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) gCat hgCat)
    (V : BigFppfOver B S hS) :
    EssentiallySmall.{u}
      ((hilbertAtlasSquare (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F) gCat).pt.val.p.Fiber V) := by
  obtain ⟨𝒬, v, hv, h𝒬, hvsurj, hvflat, hvlfp⟩ :=
    exists_flatPresentation_finiteHilbertFibered h𝒴 h𝒳 hF hFprops h𝒰 gCat hgCat
      hgsurj hgsmooth
  exact essentiallySmall_fiber_of_baseChangedFlatPresentation B S hS v _
    (isStack_hilbertAtlasSquare hHd hℋ h𝒰 gCat) h𝒬 hv hvsurj hvflat hvlfp
    (isRepresentableByAlgebraicSpaces_hilbertAtlasSquare_fst gCat hgCat) V

/-- **`𝒲 = ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳)} 𝒰` is representable by an algebraic space** for positive degree
`d`: it is a stack in setoids by Stacks 05UI, its fibres are essentially small, and the flat
presentation of `ℋ_d(𝒳/𝒴)` base changes to a flat presentation of it, so the engine of
Stacks 04SZ applies. -/
theorem isRepresentableByAlgebraicSpace_hilbertAtlasSquare (hd : 0 < d)
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F))
    (hHd : Functor.IsStack
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      (BigFppfOver.topology B S hS))
    (hℋ : Functor.IsStack
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (BigFppfOver.topology B S hS))
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (gCat : 𝒰 ⟶ absoluteHilbertFibered 𝒳 d)
    (hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom)
    (hgsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) gCat hgCat)
    (hgsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) gCat hgCat) :
    IsRepresentableByAlgebraicSpace B S hS
      (hilbertAtlasSquare (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F) gCat).pt := by
  obtain ⟨𝒬, v, hv, h𝒬, hvsurj, hvflat, hvlfp⟩ :=
    exists_flatPresentation_finiteHilbertFibered h𝒴 h𝒳 hF hFprops h𝒰 gCat hgCat
      hgsurj hgsmooth
  exact isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange B S hS v _
    (isStackInSetoids_twoFibreProduct_forgetRelativeStructure hd hHd hℋ gCat h𝒰) h𝒬 hv hvsurj
    hvflat hvlfp (isRepresentableByAlgebraicSpaces_hilbertAtlasSquare_fst gCat hgCat)

/-- **Stacks 06CI.** For positive degree `d`, the relative finite Hilbert stack `ℋ_d(𝒳/𝒴)` of a
1-morphism `F : 𝒳 ⟶ 𝒴` of stacks in groupoids over the big fppf site of `S` with `𝒳`
representable by an algebraic space and `F` representable by algebraic spaces, surjective, flat
and locally of finite presentation is an algebraic stack.

The hypothesis `hd : 0 < d` is the domain of the statement, not a restriction of it: the source
defines `ℋ_d(𝒳/𝒴)` only for `d ≥ 1` (Examples of Stacks, Section 05WA).

Writing `𝒰` for a scheme atlas of `ℋ_d(𝒳)` and `𝒲 = ℋ_d(𝒳/𝒴) ×_{ℋ_d(𝒳)} 𝒰`, the 1-morphism
`𝒲 ⟶ ℋ_d(𝒳/𝒴)` is a base change of `𝒰 ⟶ ℋ_d(𝒳)`, hence representable by algebraic spaces,
surjective and smooth (Stacks 0302 and Stacks 045C), and `𝒲` is representable by an algebraic
space, so Stacks 05UL applies to it. -/
@[stacks 06CI "for positive degree d, the domain on which the source defines the finite Hilbert \
stack"]
theorem isAlgebraicStack_finiteHilbertFibered (hd : 0 < d)
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    IsAlgebraicStack.{u, w} B S hS (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val := by
  classical
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨hHd, U, gCat, hgCat, hgsurj, hgsmooth⟩ :=
    exists_smooth_atlas_absoluteHilbertFibered (d := d) h𝒳
  have h𝒰 : IsRepresentableByAlgebraicSpace B S hS (schemeFibredCategory B S hS U) :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U
  have hℋ : Functor.IsStack
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (BigFppfOver.topology B S hS) :=
    isStack_finiteHilbertCategory hHd h𝒴
      (isRepresentableByAlgebraicSpacesForgetToProduct_of_flatPresentation h𝒴 h𝒳 hF hFprops)
  exact isAlgebraicStack_of_smoothPresentation.{u, w} B S hS
    (hilbertAtlasSquare (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) gCat).fst
    hℋ
    (isRepresentableByAlgebraicSpace_hilbertAtlasSquare hd h𝒴 h𝒳 hF hFprops hHd hℋ
      h𝒰 gCat hgCat hgsurj hgsmooth)
    (isRepresentableByAlgebraicSpaces_hilbertAtlasSquare_fst gCat hgCat)
    (hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ gCat _ _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ gCat)
      hgCat hgsurj)
    (hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ gCat _ _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ gCat)
      hgCat hgsmooth)

end AlgebraicGeometry.Stack

end
