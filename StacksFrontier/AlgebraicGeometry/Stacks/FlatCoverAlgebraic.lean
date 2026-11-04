module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciHilbertTargetFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids

/-!
# Artin's theorem on representability of flat groupoids (Stacks 06DC)

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`.
If `𝒳` is representable by an algebraic space and `F` is representable by algebraic spaces,
surjective, flat and locally of finite presentation, then `𝒴` is an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover_stackInGroupoids`: the theorem for
  stacks in groupoids.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover`: **Stacks 06DC**, stated for categories
  fibred in groupoids with `𝒴` a stack; `𝒳` is a stack because it is representable by an
  algebraic space, so nothing is assumed of it beyond the source's clause (1).

## References

* [Stacks Project, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW)
* [Stacks Project, Tag 06D9](https://stacks.math.columbia.edu/tag/06D9)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Artin's theorem on flat groupoids, for stacks in groupoids.** Let `F : 𝒳 ⟶ 𝒴` be a
1-morphism of stacks in groupoids over the big fppf site of `S`. If `𝒳` is representable by an
algebraic space and `F` is representable by algebraic spaces, surjective, flat and locally of
finite presentation, then `𝒴` is an algebraic stack. -/
theorem isAlgebraicStack_of_flatCover_stackInGroupoids
    {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS)}
    {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.toBasedCategory := by
  have hflat := fun U y hy P hP he => (hFprops U y hy P hP he).2.1
  have hlfp := fun U y hy P hP he => (hFprops U y hy P hP he).2.2
  let I := ULift.{u} {n : ℕ // 0 < n}
  have h : ∀ i : I, (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F) (d := i.down.1)).p.IsFiberedInGroupoids := fun i =>
    isFiberedInGroupoids_lciFiniteHilbertCategory (FiniteHilbert.hasOpenLciLocus hF hflat hlfp)
  have hI : Cardinal.mk I < B.cutoff.ord.cof :=
    (Cardinal.mk_le_aleph0 (α := ULift.{u} {n : ℕ // 0 < n})).trans_lt B.aleph0_lt_cutoff_cof
  refine isAlgebraicStack_of_jointlySurjective_formallySmoothAtlas.{u, w} B S hS h𝒴
    (hasRepresentableDiagonal_targetCFG_of_flatPresentation h𝒴 h𝒳 hF hFprops) hI
    (fun i => lciFiniteHilbertFibered (h i)) (fun i => lciFiniteHilbertToTargetFibered (h i))
    (fun i => hasFormallySmoothAtlas_lciFiniteHilbertFibered i.down.2 h𝒴 h𝒳 hF hFprops (h i))
    (fun i => isLimitPreservingOnObjects_lciFiniteHilbertToTargetFibered hF hFprops (h i))
    (fun i => isFormallySmoothOnObjects_lciFiniteHilbertToTarget (d := i.down.1) hF hflat hlfp)
    ?_
  intro U hU y hy
  obtain ⟨d, hd⟩ := isJointlySurjectiveOnObjects_lciFiniteHilbertToTarget hF hFprops U hU y hy
  exact ⟨⟨d⟩, hd⟩

/-- **Artin's theorem on representability of flat groupoids.** Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism
of categories fibred in groupoids over the big fppf site of `S`, with `𝒴` a stack. If `𝒳` is
representable by an algebraic space and `F` is representable by algebraic spaces, surjective,
flat and locally of finite presentation, then `𝒴` is an algebraic stack.

The source asks `𝒳` and `𝒴` to be stacks in groupoids. `𝒳` is one because it is representable
by an algebraic space (`AlgebraicGeometry.Stack.isStack_of_isRepresentableByAlgebraicSpace`), and
`𝒴` is a stack in groupoids at every descent universe because it is a stack (Stacks 02ZJ). -/
@[stacks 06DC "stated for categories fibred in groupoids with the target a stack: the source's \
requirement that `𝒳` and `𝒴` be stacks in groupoids is implied, for `𝒳` by clause (1) and for \
`𝒴` by Stacks 02ZJ"]
theorem isAlgebraicStack_of_flatCover
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒳 ⟶ 𝒴)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳)
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hFprops : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor F))
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom
       Space.IsSurjective B S hS g ∧ Space.IsFlat B S hS g ∧
         Space.IsLocallyOfFinitePresentation B S hS g)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_flatCover_stackInGroupoids
    (𝒳 := ⟨𝒳.val, (isStack_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳).isStackInGroupoids
      𝒳.2⟩)
    (𝒴 := ⟨𝒴.val, hstack.isStackInGroupoids 𝒴.2⟩) (F := F.hom) hstack h𝒳 hF hFprops

end AlgebraicGeometry.Stack

end
