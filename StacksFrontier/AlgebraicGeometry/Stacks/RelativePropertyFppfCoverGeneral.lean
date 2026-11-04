module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Checking a relative property after an fppf cover by an algebraic stack (Stacks 0CPP)

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks representable by algebraic spaces, and let `g : 𝒵 ⟶ 𝒴` be surjective, flat and locally of
finite presentation — *not* assumed representable by algebraic spaces. Then `f` has the relative
property `P` of Stacks 03YK exactly when the first projection of a 2-fibre product of the cospan
`(g, f)` does.

## Main results

Both live in the namespace `AlgebraicGeometry.Stack`:

* `AlgebraicStacks.exists_isRepresentableByAlgebraicSpace_fppfCover`: an algebraic stack admits a
  surjective, flat, locally finitely presented 1-morphism from an algebraic stack representable by
  an algebraic space.
* `hasRelativeProperty_iff_of_fppfCoverStack`: **Stacks 0CPP**.

## Implementation notes

**Stacks 06TY** (`AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_fppfCover`) is this statement
with the cover additionally assumed representable by algebraic spaces, and the source's proof
removes that hypothesis by descending to a cover whose source is an algebraic space, where
representability is automatic. Concretely, a smooth presentation `𝒲 ⟶ 𝒵` by an algebraic space
(`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation`) is
surjective, flat and locally of finite presentation, hence so is its composite with `g`, and
Stacks 06TY applies twice with that cover: over `𝒴` to `f`, and over `𝒵` to the projection
`𝒵 ×_𝒴 𝒳 ⟶ 𝒵`. The two right-hand sides are the same, because `𝒲 ×_𝒵 (𝒵 ×_𝒴 𝒳)` is
`𝒲 ×_𝒴 𝒳`; that identification is
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_pasteFst_of_isTwoFibreProduct`, the
pasting of two 2-fibre product squares.

Both sides of the equivalence quantify over a representability witness for the projection, which
is a proposition, so the existential on the right is equivalent to the statement at the witness
the base-change result Stacks 0302 supplies, exactly as in Stacks 06TY.

## References

* [Stacks Project, Tag 06TY](https://stacks.math.columbia.edu/tag/06TY)
* [Stacks Project, Tag 0CPP](https://stacks.math.columbia.edu/tag/0CPP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **An algebraic stack over `S` admits a surjective, flat, locally finitely presented cover by
an algebraic stack representable by an algebraic space.** The cover is the smooth presentation of
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation`, read as
a 1-morphism of algebraic stacks: it is surjective because it is surjective on objects
(**Stacks 04XI**), flat by **Stacks 04TA** and locally of finite presentation by **Stacks 0DNP**.

Representability of the source by an algebraic space is recorded because it is what makes every
1-morphism out of the cover representable by algebraic spaces. -/
theorem exists_isRepresentableByAlgebraicSpace_fppfCover
    (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    ∃ (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS) (c : 𝒲 ⟶ 𝒵),
      Stack.IsRepresentableByAlgebraicSpace B S hS 𝒲.val ∧
      Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom ∧
      Stack.IsSurjective B S hS c ∧ IsFlat B S hS c ∧
      IsLocallyOfFinitePresentation B S hS c := by
  obtain ⟨W, hW, w, hwsm, hwsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒵.property
  obtain ⟨hwrep, hwprop⟩ := hwsm
  have hsmooth : Stack.HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) w :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) w W hW
      (StacksRepresentableCFG.EquivalenceOver.refl _) ⟨hwrep, hwprop⟩
      (Space.isSmooth_id B S hS hW)
  exact ⟨⟨Stack.fibredCategory B S hS W,
      Stack.isAlgebraicStack_fibredCategory.{u, w} B S hS W hW⟩,
    Bicategory.InducedBicategory.mkHom w,
    Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW, hwrep,
    Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS _ hwsu,
    isFlat_of_isSmooth B S hS _ hsmooth,
    isLocallyOfFinitePresentation_of_isSmooth B S hS _ hsmooth⟩

/-- **`𝒲 ×_𝒵 (𝒵 ×_𝒴 𝒳)` is `𝒲 ×_𝒴 𝒳`.** If `Q` is a 2-fibre product of a cospan `(g, f)` of
algebraic stacks over `S` and `R` is a 2-fibre product of `(c, Q.fst)` for a 1-morphism
`c : 𝒲 ⟶ 𝒵`, then the pasted rectangle is a 2-fibre product of `(c ≫ g, f)`.

This is `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst` in the 2-category of algebraic
stacks; it is the identification of the two base changes which makes a cover of `𝒵` usable as a
cover of `𝒴`. -/
noncomputable def isTwoFibreProduct_pasteFst_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {g : 𝒵 ⟶ 𝒴} {c : 𝒲 ⟶ 𝒵}
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (R : Bicategory.TwoCommSq c Q.fst) (hR : Bicategory.IsTwoFibreProduct R) :
    Bicategory.IsTwoFibreProduct (Q.pasteFst R) :=
  Bicategory.isTwoFibreProduct_pasteFst Q hQ R hR

end AlgebraicStacks

/-- **Stacks 0CPP.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
stable under base change and local on the target for the fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S` representable by algebraic spaces, and let `g : 𝒵 ⟶ 𝒴` be
surjective, flat and locally of finite presentation. Then `f` has the relative property `P` of
Stacks 03YK if and only if the projection to `𝒵` of a 2-fibre product of the cospan `(g, f)` has
it.

Unlike **Stacks 06TY** the cover `g` is not assumed representable by algebraic spaces. -/
@[stacks 0CPP]
theorem hasRelativeProperty_iff_of_fppfCoverStack
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hSurj : IsSurjective B S hS g)
    (hFlat : AlgebraicStacks.IsFlat B S hS g)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (Q : Bicategory.TwoCommSq g f)
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    HasRelativeProperty B S hS P f.hom hf ↔
      ∃ hfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom,
        HasRelativeProperty B S hS P Q.fst.hom hfst := by
  obtain ⟨𝒲, c, h𝒲rep, hcrep, hcSurj, hcFlat, hcLfp⟩ :=
    AlgebraicStacks.exists_isRepresentableByAlgebraicSpace_fppfCover.{u, w} B S hS 𝒵
  -- the projection `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is a base change of `f`, hence representable (Stacks 0302)
  have hQfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val 𝒴.val 𝒵.val
      f.hom g.hom (AlgebraicStacks.toCatFiberedInGroupoids B S hS Q)
      (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS Q hQ) hf
  -- `𝒲 ×_𝒵 (𝒵 ×_𝒴 𝒳)`
  have hR : Bicategory.IsTwoFibreProduct
      (AlgebraicStacks.twoFibreProductSquare B S hS c Q.fst) :=
    AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS c Q.fst
  -- the composite cover `𝒲 ⟶ 𝒵 ⟶ 𝒴` is representable because `𝒲` is an algebraic space
  have hbrep : IsRepresentableByAlgebraicSpaces B S hS (c ≫ g).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴.property h𝒲rep
      (c ≫ g).hom
  -- Stacks 06TY over `𝒴`, along the cover `𝒲 ⟶ 𝒴`
  have hB := hasRelativeProperty_iff_of_fppfCover.{u, w} B S hS P f (c ≫ g) hf hbrep
    (isSurjective_comp B S hS c g hcSurj hSurj)
    (AlgebraicStacks.isFlat_comp B S hS c g hcFlat hFlat)
    (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS c g hcLfp hLfp)
    (Q.pasteFst (AlgebraicStacks.twoFibreProductSquare B S hS c Q.fst))
    (AlgebraicStacks.isTwoFibreProduct_pasteFst_of_isTwoFibreProduct B S hS Q hQ _ hR)
  -- Stacks 06TY over `𝒵`, along the cover `𝒲 ⟶ 𝒵`
  have hA := hasRelativeProperty_iff_of_fppfCover.{u, w} B S hS P Q.fst c hQfst hcrep
    hcSurj hcFlat hcLfp (AlgebraicStacks.twoFibreProductSquare B S hS c Q.fst) hR
  exact hB.trans (hA.symm.trans ⟨fun h => ⟨hQfst, h⟩, fun ⟨_, h⟩ => h⟩)

end AlgebraicGeometry.Stack

end
