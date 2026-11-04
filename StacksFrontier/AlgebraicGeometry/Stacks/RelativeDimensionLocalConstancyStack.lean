module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionLocalConstancy

/-!
# The fibre dimension of a smooth 1-morphism with algebraic stack target

Stacks 0DRQ says that the fibre dimension of a 1-morphism locally of finite type is upper
semi-continuous on the source, and is locally constant when the 1-morphism is smooth. For a
morphism of algebraic spaces the two assertions are
`AlgebraicGeometry.Stack.isOpen_setOf_relativeDimensionAt_le` and
`AlgebraicGeometry.Stack.isLocallyConstant_relativeDimensionAt_of_isSmooth`. Here the second one is
proved for a 1-morphism `f : T ⟶ 𝒳` from an algebraic space to an arbitrary algebraic stack,
the fibre dimension being the relative dimension of Stacks 0DRG. That is the case the dimension
theory of algebraic stacks uses.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeDimensionAt_representingMap_fst_of_relativeDimensionAt`:
  the relative dimension of Stacks 0DRG of a 1-morphism from an algebraic space, read off the
  representing morphism of the first projection of a 2-fibre product.
* `AlgebraicGeometry.Stack.isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack`:
  **Stacks 0DRQ, part (2)**, for a smooth 1-morphism from an algebraic space to an algebraic
  stack.

## Implementation notes

The source pulls the 1-morphism back along a smooth surjective chart of the target and compares
the relative dimension of the base change with the original one, which is Stacks 0DRN. Here the
chart of the target is the 1-morphism `f : T ⟶ 𝒳` itself: its self-2-fibre-product
`Q = T ×_𝒳 T` is representable by an algebraic space `P`, because `f` is representable by
algebraic spaces over the algebraic stack `𝒳` (Stacks 045G), both projections of `Q` are smooth
as base changes of `f` (Stacks 075W), and the comparison is
`AlgebraicGeometry.Stack.hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt`,
which identifies the relative dimension of Stacks 04NM of the representing morphism
`pr₁ : P ⟶ T` of the first projection at a point `z` with the relative dimension of Stacks 0DRG
of `f` at the image of `z` under the *second* projection. Because the cospan is `(f, f)`,
Stacks 04XH produces a diagonal point of `Q` above any given point of `|T|`, so neither a second
chart of `𝒳` nor surjectivity of one is needed anywhere.

The relative dimension of Stacks 04NM of `pr₁` is locally constant because `pr₁` is a smooth
morphism of algebraic *spaces*, and the second projection is open on points because it is smooth,
hence flat and locally of finite presentation (Stacks 06R7). Transporting the open set on which
`pr₁` has constant relative dimension forward along `pr₂` therefore gives an open set in `|T|` on
which the relative dimension of `f` is constant.

Uniqueness of the value of `AlgebraicGeometry.Space.HasRelativeDimensionAt` at a point, which
turns the predicate back into a function, is
`AlgebraicGeometry.Space.eq_of_hasRelativeDimensionAt`.

The comparison is stated at an arbitrary cospan `(c, a)` of 1-morphisms out of algebraic spaces,
not only at `(a, a)`, because that is what the semicontinuity of part (1) needs: there the first
leg is a smooth chart of the target and the second the 1-morphism itself.

The universe `u` is that of the base scheme and of its relative big fppf site, while `w` is the
descent universe at which algebraicity of `𝒳` is tested; the two are independent.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- **The relative dimension of Stacks 0DRG is read off the representing morphism of the first
projection of a 2-fibre product.** Let `c : V ⟶ 𝒳` and `a : T ⟶ 𝒳` be 1-morphisms from the
algebraic stacks of algebraic spaces to an algebraic stack, with `a` locally of finite type, let
`Q` be a 2-fibre product of that cospan whose apex is representable by the algebraic space `P`,
and let `pr` be the morphism `P ⟶ V` of algebraic spaces representing the first projection
of `Q`. If a point `z` of `P` has image `s` in `|T|` under the morphism representing the second
projection, then the relative dimension of Stacks 04NM of `pr` at `z` is the relative dimension
of Stacks 0DRG of `a` at `s`.

This is the base-change comparison
`AlgebraicGeometry.Stack.hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt`,
the field-valued point and the point of the fibre above `s` being the admissible choices of
`AlgebraicGeometry.Stack.exists_eq_fieldFibreDimensionAt`. -/
theorem hasRelativeDimensionAt_representingMap_fst_of_relativeDimensionAt
    (V T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (c : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳)
    (a : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
    {Q : Bicategory.TwoCommSq c.hom a.hom} (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (hftpr : Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS Q.pt (fibredCategory B S hS V) P V eP
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst))
    (z : Space.points B S hS P) (s : Space.points B S hS T)
    (hzs : Space.pointsMap B S hS P
        (representingMap B S hS Q.pt (fibredCategory B S hS T) P T eP
          (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd) z = s)
    (d : ℕ∞)
    (hd : relativeDimensionAt.{u, w} B S hS T hT 𝒳 a ha s = (d : WithBot ℕ∞)) :
    Space.HasRelativeDimensionAt d B S hS
      (representingMap B S hS Q.pt (fibredCategory B S hS V) P V eP
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst) z := by
  classical
  have hTrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  obtain ⟨p', q', -, hq', hval⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒳 a ha s
  -- the point of `Q` corresponding to `z`
  have hsnd : pointsMap B S hS Q.pt.val Q.pt.property (fibredCategory B S hS T).property
      Q.snd.hom
      (spacePointMap B S hS P Q.pt (representingEquivalence B S hS P Q.pt eP).functor z) =
      stackPointOfSpacePoint B S hS T s := by
    rw [← spacePointMap_representing_naturality B S hS P T Q.pt (fibredCategory B S hS T) eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd z, hzs]
    rfl
  refine hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt.{u, w} B S hS c a
    hTrep ha hQ hQpt V P hV hP (StacksRepresentableCFG.EquivalenceOver.refl _) eP hftpr rfl
    (spacePointMap B S hS P Q.pt (representingEquivalence B S hS P Q.pt eP).functor z) z rfl
    p' q' ?_ d ?_
  · rw [hq', hsnd]
  · rw [← hval, hd]

/-- **Stacks 0DRQ, part (2), for a 1-morphism with algebraic stack target.** For a smooth
1-morphism `f : T ⟶ 𝒳`, locally of finite type, from an algebraic space over `S` to an
algebraic stack over `S`, the fibre dimension `t ↦ dim_t(T_{f(t)})` of Stacks 0DRG is locally
constant on `|T|`.

The source proves part (2) of Stacks 0DRQ for a 1-morphism of algebraic stacks by pulling it back
along a smooth surjective chart of the target and invoking Stacks 0DRN; here the chart is `f`
itself, so the base change is the first projection of the self-2-fibre-product `T ×_𝒳 T`, which
is representable by an algebraic space because `f` is representable by algebraic spaces over the
algebraic stack `𝒳`, and smooth as a base change of `f`. For a *morphism of algebraic spaces* the
relative dimension of Stacks 04NM is locally constant
(`AlgebraicGeometry.Space.exists_isOpen_forall_hasRelativeDimensionAt_of_isSmooth`), and the
comparison with the relative dimension of `f` itself is
`AlgebraicGeometry.Stack.hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt`.
The second projection is smooth as well, hence flat and locally of finite presentation, hence
open on points by Stacks 06R7, so the open set on which the base change has constant relative
dimension has open image in `|T|`; that image contains the given point because the cospan is
`(f, f)` and so has a diagonal point above it. -/
@[ega "IV 17.10.2" "more general"]
theorem isLocallyConstant_relativeDimensionAt_of_isSmooth_of_stack
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    IsLocallyConstant (relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf) := by
  classical
  have hTrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  set Q := twoFibreProductSquareAlgebraicStacks B S hS f f
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f f
  have hQc : Bicategory.IsTwoFibreProduct Q.underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom f.hom
  have hQpt : IsRepresentableByAlgebraicSpace B S hS Q.underlying.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS T) 𝒳.val (fibredCategory B S hS T) f.hom f.hom _ hQc
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hTrep f.hom)
      hTrep
  obtain ⟨P, hP, ⟨eP⟩⟩ := id hQpt
  have hsmfst :=
    isSmooth_representingMap_of_isSmooth.{u, w} B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P T hP hT eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst
      (AlgebraicStacks.isSmooth_baseChange B S hS f f Q hQ hsm)
  have hsmsnd :=
    isSmooth_representingMap_of_isSmooth.{u, w} B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P T hP hT eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd
      (AlgebraicStacks.isSmooth_baseChange B S hS f f Q.swap
        (Bicategory.isTwoFibreProduct_swap hQ) hsm)
  -- the second projection is open on points
  have hopen := Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hP hT
    _ (Space.isFlat_of_isSmooth B S hS _ hsmsnd)
    (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsmsnd)
  rw [IsLocallyConstant.iff_exists_open]
  intro t₀
  -- the diagonal point of `Q` above `t₀`
  obtain ⟨ζ₀, -, hζ₀snd⟩ := exists_point_of_isTwoFibreProduct B S hS Q.underlying hQc
    (stackPointOfSpacePoint B S hS T t₀) (stackPointOfSpacePoint B S hS T t₀) rfl
  obtain ⟨z₀, hz₀⟩ :=
    (bijective_spacePointMap_representing B S hS P Q.underlying.pt eP).surjective ζ₀
  -- the diagonal point lies above `t₀` for the second projection
  have hz₀t : Space.pointsMap B S hS P
      (representingMap B S hS Q.underlying.pt (fibredCategory B S hS T) P T eP
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.underlying.snd) z₀ = t₀ := by
    refine (bijective_spacePointMap_representing B S hS T (fibredCategory B S hS T)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).injective ?_
    rw [spacePointMap_representing_naturality B S hS P T Q.underlying.pt
      (fibredCategory B S hS T) eP (StacksRepresentableCFG.EquivalenceOver.refl _)
      Q.underlying.snd z₀, hz₀, hζ₀snd]
    rfl
  obtain ⟨W, dW, hWopen, hz₀W, hWconst⟩ :=
    Space.exists_isOpen_forall_hasRelativeDimensionAt_of_isSmooth B S hS hP hT _ hsmfst z₀
  have hcast : ∀ n : ℕ, ((n : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) := fun n => rfl
  -- on `W`, the relative dimension of `f` at the image of `z` is `dW`
  have hconst : ∀ z ∈ W, relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf
      (Space.pointsMap B S hS P
        (representingMap B S hS Q.underlying.pt (fibredCategory B S hS T) P T eP
          (StacksRepresentableCFG.EquivalenceOver.refl _) Q.underlying.snd) z) =
      (dW : WithBot ℕ∞) := by
    intro z hzW
    obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast B S hS T hT 𝒳 f hf
      (Space.pointsMap B S hS P
        (representingMap B S hS Q.underlying.pt (fibredCategory B S hS T) P T eP
          (StacksRepresentableCFG.EquivalenceOver.refl _) Q.underlying.snd) z)
    have hz := hasRelativeDimensionAt_representingMap_fst_of_relativeDimensionAt.{u, w} B S hS T T
      hT hT 𝒳 f f hf hQc hQpt P hP eP
      (Space.isLocallyOfFiniteType_of_isSmooth B S hS hsmfst) z _ rfl (d : ℕ∞)
      (by rw [hd, hcast])
    rw [hd, ← hcast d, Space.eq_of_hasRelativeDimensionAt B S hS hP hT _ z hz (hWconst z hzW)]
  refine ⟨Space.pointsMap B S hS P
      (representingMap B S hS Q.underlying.pt (fibredCategory B S hS T) P T eP
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.underlying.snd) '' W,
    hopen W hWopen, ⟨z₀, hz₀W, hz₀t⟩, ?_⟩
  rintro s ⟨z, hzW, rfl⟩
  rw [← hz₀t]
  exact (hconst z hzW).trans (hconst z₀ hz₀W).symm

end AlgebraicGeometry.Stack

end
