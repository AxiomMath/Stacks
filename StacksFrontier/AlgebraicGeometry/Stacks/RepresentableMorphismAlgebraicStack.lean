module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductPasting
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The source of a morphism representable by algebraic spaces into an algebraic stack

Let `j : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S` which is representable by algebraic spaces. **Stacks 05UN** says that `𝒳` inherits
both of `𝒴`'s properties of being a stack in groupoids and of being an algebraic stack. The
first of the two is
`AlgebraicGeometry.Stack.isStack_of_isRepresentableByAlgebraicSpaces`; this file proves the
second.

A scheme atlas `S_U ⟶ 𝒴` of `𝒴`, which the presentation clause of **Stacks 026O** provides,
base changes along `j` to a 1-morphism `W ⟶ 𝒳` which is again representable by algebraic
spaces (**Stacks 0302**), surjective and smooth (**Stacks 045C**); and `W` is representable by
an algebraic space (**Stacks 0300**), because its projection to `S_U` is a base change of `j`.
So `W ⟶ 𝒳` is a smooth surjective presentation of `𝒳` by a category representable by an
algebraic space, and **Stacks 05UL** applies.

## Main results

* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpaces`: the
  source of a 1-morphism representable by algebraic spaces inherits a diagonal representable by
  algebraic spaces from its target.
* `AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 05UM**, which is also the algebraic-stack clause of **Stacks 05UN**.
* `AlgebraicGeometry.Stack.isStack_and_isAlgebraicStack_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 05UN**, both clauses.

## Implementation notes

The source's monomorphism hypothesis on `j` was dropped upstream in 2016 and is not assumed
here.

The source reduces the algebraic-stack clause of Stacks 05UN to its stack-in-groupoids clause by
Stacks 05UM, and the two statements coincide here, so they are one declaration. Its proof splits
the four clauses of Stacks 026O in two: the diagonal clause is obtained from the diagonal of `𝒴` by
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpaces`, and the
remaining three by
`AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothPresentation_of_hasRepresentableDiagonal`,
the form of Stacks 05UL that takes the diagonal clause as a hypothesis.

Neither statement assumes `𝒳` or `𝒴` to be a stack in groupoids, although the source of
Stacks 05UM does. For `𝒴` that is part of being an algebraic stack, and for `𝒳` it is a
consequence of the hypotheses by Stacks 05UN's own stack-in-groupoids clause,
`AlgebraicGeometry.Stack.isStack_of_isRepresentableByAlgebraicSpaces`.

The base change is taken as the leg exchange `(twoFibreSquare g j).swap` of the canonical
square of Stacks 003Q, so that one and the same apex carries both the projection to `𝒳` whose
properties descend from the atlas and the projection to `S_U` whose representability makes the
apex an algebraic space; `CategoryTheory.Bicategory.isTwoFibreProduct_swap` is Stacks 003Q for
the exchanged square.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 05UL](https://stacks.math.columbia.edu/tag/05UL)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **The source of a 1-morphism representable by algebraic spaces inherits a representable
diagonal.** If `j : 𝒳 ⟶ 𝒴` is a 1-morphism of categories fibred in groupoids over the big fppf
site of `S` which is representable by algebraic spaces and the diagonal of `𝒴` is representable
by algebraic spaces, then so is the diagonal of `𝒳`.

The criterion used is the equivalence of conditions (1) and (3) of Stacks 045G: a diagonal is
representable by algebraic spaces exactly when every 1-morphism from a category represented by a
scheme is. So let `x : 𝒜 ⟶ 𝒳` be such a 1-morphism and factor it through the 2-fibre product
`𝒜 ×_𝒴 𝒳` taken along `x ≫ j`. The projection `𝒜 ×_𝒴 𝒳 ⟶ 𝒳` is a base change of `x ≫ j`
(Stacks 0302), which is representable by algebraic spaces because the diagonal of `𝒴` is; and
`𝒜 ×_𝒴 𝒳` is representable by an algebraic space (Stacks 0300), hence an algebraic stack, so its
own diagonal is representable and the tautological section `𝒜 ⟶ 𝒜 ×_𝒴 𝒳` is representable by
algebraic spaces. Stacks 0301 composes the two legs. -/
theorem hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpaces (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (h𝒴 : HasRepresentableDiagonal B S hS 𝒴) :
    HasRepresentableDiagonal B S hS 𝒳 := by
  have hfromSchemes : ∀ (𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)),
      HasRepresentableDiagonal B S hS 𝒯 → IsRepresentableFromSchemes B S hS 𝒯 := fun 𝒯 h =>
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒯).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒯).mp h)
  apply (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mpr
  apply (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mpr
  intro U x
  let 𝒜 := schemeFibredCategory B S hS U
  let xa : 𝒜 ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom x
  let ya : 𝒜 ⟶ 𝒴 := xa ≫ j
  have hya : IsRepresentableByAlgebraicSpaces B S hS ya.hom := hfromSchemes 𝒴 h𝒴 U ya.hom
  -- the 2-fibre product `𝒜 ×_𝒴 𝒳`, with its legs exchanged so that Stacks 0302 speaks about
  -- the projection to `𝒳`
  let R : TwoCommSq j ya := (twoFibreSquare ya j).swap
  have hR : IsTwoFibreProduct R := isTwoFibreProduct_swap (isTwoFibreSquare ya j)
  have hRpt : IsRepresentableByAlgebraicSpace B S hS R.pt :=
    isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS j ya hj
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  have hπ : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒜 𝒴 𝒳 ya j R hR hya
  obtain ⟨_, _, hdiag, _⟩ :=
    isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, u} B S hS R.pt hRpt
  -- the tautological section of the 2-fibre product over `𝒜`
  let tautological : 𝒜 ⟶ R.pt := Bicategory.InducedBicategory.mkHom
    ⟨TwoFibreProductOver.lift 𝒜.val.p 𝒳.val.p 𝒴.val.p ya.hom.toFunctor j.hom.toFunctor 𝒜.val.p
      (𝟭 𝒜.val.obj) xa.hom.toFunctor (Functor.id_comp _) xa.hom.w (Iso.refl _)
      (fun q => IsHomLift.id (ya.hom.w_obj q)),
      TwoFibreProductOver.lift_comp_structureFunctor ..⟩
  exact isRepresentableByAlgebraicSpaces_comp B S hS tautological R.fst
    (hfromSchemes R.pt hdiag U tautological.hom) hπ

/-- **Stacks 05UM.** If a 1-morphism `j : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big
fppf site of `S` is representable by algebraic spaces and `𝒴` is an algebraic stack over `S`,
then `𝒳` is an algebraic stack over `S`.

The scheme atlas of `𝒴` base changes along `j` to a 1-morphism `W ⟶ 𝒳` which is again
representable by algebraic spaces (Stacks 0302), surjective and smooth (Stacks 045C), with `W`
representable by an algebraic space (Stacks 0300); the diagonal of `𝒳` is inherited from that of
`𝒴`, so the form of Stacks 05UL that takes the diagonal as a hypothesis applies.

The same statement is the algebraic-stack clause of **Stacks 05UN**, whose stack-in-groupoids
clause is `AlgebraicGeometry.Stack.isStack_of_isRepresentableByAlgebraicSpaces`; the two
clauses together are
`AlgebraicGeometry.Stack.isStack_and_isAlgebraicStack_of_isRepresentableByAlgebraicSpaces`. -/
@[stacks 05UM]
theorem isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  obtain ⟨_, ⟨h𝒴stk, _⟩, h𝒴diag, U, g, hg, hgprop⟩ := h𝒴
  have h𝒳stk : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS) :=
    isStack_of_isRepresentableByAlgebraicSpaces B S hS j hj h𝒴stk
  have h𝒳diag : HasRepresentableDiagonal B S hS 𝒳 :=
    hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpaces B S hS j hj h𝒴diag
  let gCat : schemeFibredCategory B S hS U ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom g
  have hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom := hg
  have hgsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) gCat hgCat :=
    fun V y hy F hF he => (hgprop V y hy F hF he).1
  have hgsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) gCat hgCat :=
    fun V y hy F hF he => (hgprop V y hy F hF he).2
  -- the atlas of `𝒴`, base changed along `j`
  let R : TwoCommSq j gCat := (twoFibreSquare gCat j).swap
  have hR : IsTwoFibreProduct R := isTwoFibreProduct_swap (isTwoFibreSquare gCat j)
  have hW : IsRepresentableByAlgebraicSpace B S hS R.pt :=
    isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS j gCat hj
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  have hv : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ gCat j R hR hgCat
  have hvsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) R.fst hv :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) _ _ _ gCat j R hR hgCat hgsurj
  have hvsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) R.fst hv :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) _ _ _ gCat j R hR hgCat hgsmooth
  exact isAlgebraicStack_of_smoothPresentation_of_hasRepresentableDiagonal.{u, w} B S hS R.fst
    h𝒳stk h𝒳diag hW hv hvsurj hvsmooth

/-- **Stacks 05UN.** Let `j : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the
big fppf site of `S` which is representable by algebraic spaces. If `𝒴` is a stack in groupoids
then so is `𝒳`, and if `𝒴` is an algebraic stack then so is `𝒳`.

The first clause is `AlgebraicGeometry.Stack.isStack_of_isRepresentableByAlgebraicSpaces`, the
second `AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces`. -/
@[stacks 05UN]
theorem isStack_and_isAlgebraicStack_of_isRepresentableByAlgebraicSpaces (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom) :
    (𝒴.val.p.IsStack (BigFppfOver.topology B S hS) →
        𝒳.val.p.IsStack (BigFppfOver.topology B S hS)) ∧
      (IsAlgebraicStack.{u, w} B S hS 𝒴.val → IsAlgebraicStack.{u, w} B S hS 𝒳.val) :=
  ⟨isStack_of_isRepresentableByAlgebraicSpaces B S hS j hj,
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS j hj⟩

end AlgebraicGeometry.Stack

end
