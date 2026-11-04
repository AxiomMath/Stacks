module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionClosedImmersion
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# A closed immersion of sources does not raise the relative dimension of Stacks 0DRG

Let `f : T ⟶ 𝒳` be a 1-morphism, locally of finite type, from an algebraic space to an algebraic
stack over `S`, and let `i : T' ⟶ T` be a closed immersion of algebraic spaces over `S`. For a
point `t' ∈ |T'|` with image `t ∈ |T|` the fibre `T'_x = T' ×_𝒳 Spec k` is a closed subspace of
`T_x = T ×_𝒳 Spec k`, being its base change along `i`, so the relative dimension of
**Stacks 0DRG** satisfies

`dim_{t'}(T'_x) ≤ dim_t(T_x)`.

## Main results

* `AlgebraicGeometry.Stack.relativeDimensionAt_le_of_isClosedImmersion`: the relative dimension
  of Stacks 0DRG of `i ≫ f` at `t'` is at most that of `f` at the image of `t'`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DS0](https://stacks.math.columbia.edu/tag/0DS0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative dimension of Stacks 0DRG does not rise along a closed immersion of sources.**
Let `f : T ⟶ 𝒳` be a 1-morphism, locally of finite type, from an algebraic space to an algebraic
stack over `S`, let `i : T' ⟶ T` be a closed immersion of the algebraic stacks of two algebraic
spaces, and let `t' ∈ |T'|` have image `t ∈ |T|`. Then

`dim_{t'}(T'_x) ≤ dim_t(T_x)`,

the two relative dimensions of Stacks 0DRG at `t'` for `i ≫ f` and at `t` for `f`. -/
theorem relativeDimensionAt_le_of_isClosedImmersion
    {T' T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT' : IsAlgebraicSpace B S hS T') (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (i : algebraicSpaceStack.{u, w} B S hS T' hT' ⟶ algebraicSpaceStack.{u, w} B S hS T hT)
    (hi : AlgebraicStacks.IsClosedImmersion B S hS i)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hif : AlgebraicStacks.IsLocallyOfFiniteType B S hS (i ≫ f))
    (t' : Space.points B S hS T') (t : Space.points B S hS T)
    (ht : pointsMap B S hS (fibredCategory B S hS T').val
        (fibredCategory B S hS T').property (fibredCategory B S hS T).property i.hom.hom
        (stackPointOfSpacePoint B S hS T' t') = stackPointOfSpacePoint B S hS T t) :
    relativeDimensionAt.{u, w} B S hS T' hT' 𝒳 (i ≫ f) hif t' ≤
      relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t := by
  classical
  have hT'rep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T' hT'
  have hTrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  set p := Quotient.out (pointsMap B S hS (fibredCategory B S hS T').val
    (fibredCategory B S hS T').property 𝒳.val.property (i ≫ f).hom.hom
    (stackPointOfSpacePoint B S hS T' t'))
  have hp' : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS (fibredCategory B S hS T').val
        (fibredCategory B S hS T').property 𝒳.val.property (i ≫ f).hom.hom
        (stackPointOfSpacePoint B S hS T' t') := Quotient.out_eq _
  have hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS (fibredCategory B S hS T).val
        (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
        (stackPointOfSpacePoint B S hS T t) := by
    rw [hp', ← ht]
    exact (pointsMap_comp B S hS (fibredCategory B S hS T').val
      (fibredCategory B S hS T').property (fibredCategory B S hS T).property 𝒳.val.property
      i.hom.hom f.hom.hom (stackPointOfSpacePoint B S hS T' t')).symm
  have hRrep := isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f.hom
    𝒳.property hTrep p
  obtain ⟨ζ, hζ⟩ := exists_point_fieldFibreSquare B S hS f.hom
    (stackPointOfSpacePoint B S hS T t) p hp
  set N := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (fieldFibreSquare B S hS f.hom p).fst i.hom
  have hN : Bicategory.IsTwoFibreProduct N :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hNrep : IsRepresentableByAlgebraicSpace B S hS N.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (algebraicSpaceStack.{u, w} B S hS T' hT').val
      (algebraicSpaceStack.{u, w} B S hS T hT).val
      (fieldFibreSquare B S hS f.hom p).pt i.hom (fieldFibreSquare B S hS f.hom p).fst N hN
      hi.1 hRrep
  have hPaste : Bicategory.IsTwoFibreProduct
      (((fieldFibreSquare B S hS f.hom p).swap.paste N).swap) :=
    Bicategory.isTwoFibreProduct_swap
      (Bicategory.isTwoFibreProduct_paste
        (Bicategory.isTwoFibreProduct_swap
          (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
            f.hom (fieldValuedPointMorphism B S hS 𝒳.val p))) hN)
  obtain ⟨y, hy₁, hy₂⟩ := exists_point_of_isTwoFibreProduct B S hS N hN ζ
    (stackPointOfSpacePoint B S hS T' t') (hζ.trans ht.symm)
  obtain ⟨q', hq'⟩ := exists_point_fieldFibreSquare B S hS (i ≫ f).hom
    (stackPointOfSpacePoint B S hS T' t') p hp'
  have hleft : relativeDimensionAt.{u, w} B S hS T' hT' 𝒳 (i ≫ f) hif t' =
      representedDimensionAtPoint B S hS N.pt hNrep y := by
    rw [relativeDimensionAt_eq_fieldFibreDimensionAt.{u, w} B S hS T' hT' 𝒳 (i ≫ f) hif t'
      p q' hp' hq']
    exact (representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst.{u, w} B S hS (i ≫ f)
      hT'rep hif p hPaste hNrep y q' (hy₂.trans hq'.symm)).symm
  have hright : relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t =
      representedDimensionAtPoint B S hS (fieldFibreSquare B S hS f.hom p).pt hRrep ζ :=
    relativeDimensionAt_eq_fieldFibreDimensionAt.{u, w} B S hS T hT 𝒳 f hf t p ζ hp hζ
  rw [hleft, hright]
  obtain ⟨E, hE, ⟨eE⟩⟩ := id hNrep
  obtain ⟨F, hF, ⟨eF⟩⟩ := id hRrep
  obtain ⟨w, hw⟩ := (bijective_spacePointMap_representing B S hS E N.pt eE).surjective y
  let φ := representingMap B S hS N.pt (fieldFibreSquare B S hS f.hom p).pt E F eE eF N.fst
  let : (Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isImmersion_isLocalAtTarget_fppf B S hS
  have himm : Space.IsImmersion B S hS φ :=
    prop_representingMap_of_hasRelativeProperty B S hS (Space.immersionProperty B S hS)
      i.hom hi.1
      ((isImmersion_iff_hasRelativeProperty B S hS i.hom hi.1).1
        (fun U' z hz G hG he =>
          Space.isImmersion_of_isClosedImmersion B S hS (hi.2 U' z hz G hG he)))
      (fieldFibreSquare B S hS f.hom p).pt (fieldFibreSquare B S hS f.hom p).fst N hN
      E F hE hF eE eF
  have hnat := spacePointMap_representing_naturality B S hS E F N.pt
    (fieldFibreSquare B S hS f.hom p).pt eE eF N.fst w
  rw [hw, hy₁] at hnat
  calc representedDimensionAtPoint B S hS N.pt hNrep y
      = Space.dimensionAtPoint B S hS E hE w := by
        rw [← hw]
        exact representedDimensionAtPoint_eq B S hS N.pt hNrep E hE eE w
    _ ≤ Space.dimensionAtPoint B S hS F hF (Space.pointsMap B S hS E φ w) :=
        Space.dimensionAtPoint_le_of_isImmersion B S hS hE hF φ himm w
    _ = representedDimensionAtPoint B S hS (fieldFibreSquare B S hS f.hom p).pt hRrep ζ := by
        rw [← hnat]
        exact (representedDimensionAtPoint_eq B S hS (fieldFibreSquare B S hS f.hom p).pt hRrep
          F hF eF _).symm

end AlgebraicGeometry.Stack

end
