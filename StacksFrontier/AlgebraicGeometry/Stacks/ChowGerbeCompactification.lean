module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCompositionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty

/-!
# Proper covers of a stack over an algebraic space by compactifiable spaces

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and let `V ⊆ Y` be
an open subspace. [Stacks, Tag 0CQ7] produces, when `f` is separated of finite type, `Y` and `V`
are quasi-compact and quasi-separated and `𝒳_V` is a gerbe over `V`, a commutative diagram
`Z̄ ⟵ Z ⟶ 𝒳` over `Y` with `Z ⟶ Z̄` an open immersion, `Z̄ ⟶ Y` and `Z ⟶ 𝒳` proper, and `|V|`
contained in the image of `|Z ⟶ Y|`. This file records that conclusion and the reduction the
source proof uses repeatedly ("the initial remark"): the conclusion descends along a proper
morphism of algebraic spaces covered by a proper morphism of stacks.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover`: the conclusion of
  [Stacks, Tag 0CQ7] for a pair `(f, V)`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_proper`: the initial
  remark of the proof of [Stacks, Tag 0CQ7].
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_baseChange`: the
  initial remark along a proper surjective morphism `g : Y' ⟶ Y`, with `𝒳' = 𝒳 ×_Y Y'` and
  `V' = g⁻¹V`, the form of the reduction to a scheme `Y` by Stacks 09YC.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_section`: the last
  step of that proof, for a separated `f` with a section (Stacks 050J).

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The conclusion of [Stacks, Tag 0CQ7]** for a 1-morphism `f : 𝒳 ⟶ Y` from an algebraic
stack to an algebraic space and a subfunctor `V` of `Y`: there are algebraic spaces `Z` and `Z̄`,
an open immersion `j : Z ⟶ Z̄`, a proper morphism `ḡ : Z̄ ⟶ Y` of algebraic spaces and a proper
1-morphism `h : Z ⟶ 𝒳` with `h ≫ f` 2-isomorphic to `g = j ≫ ḡ`, such that `|V|` is contained in
the image of `|g|`. -/
def HasProperCompactifiableCover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (V : Subfunctor Y) : Prop :=
  ∃ (Zbar Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Zbar)
    (hZ : IsAlgebraicSpace B S hS Z) (j : Z ⟶ Zbar) (gbar : Zbar ⟶ Y)
    (h : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳),
    Space.IsOpenImmersion B S hS j ∧ Space.IsProper B S hS gbar ∧ IsProper B S hS h ∧
      Nonempty (h ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hZ hY (j ≫ gbar)) ∧
      Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ⊆
        Set.range (Space.pointsMap B S hS Z (j ≫ gbar))

/-- **The initial remark of the proof of [Stacks, Tag 0CQ7].** Let `f : 𝒳 ⟶ Y` and
`f' : 𝒳' ⟶ Y'` be 1-morphisms from algebraic stacks to algebraic spaces, let `p : Y' ⟶ Y` be a
proper morphism of algebraic spaces and `a : 𝒳' ⟶ 𝒳` a proper 1-morphism with `a ≫ f`
2-isomorphic to `f' ≫ p`, and let `V ⊆ Y`, `V' ⊆ Y'` be subfunctors such that `|V'|` maps onto a
set containing `|V|`. If the conclusion of [Stacks, Tag 0CQ7] holds for `(f', V')`, it holds for
`(f, V)`: compose the cover with `a` and the compactification with `p`. -/
theorem HasProperCompactifiableCover.of_proper {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY')
    (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p) (a : 𝒳' ⟶ 𝒳) (ha : IsProper B S hS a)
    (e : a ≫ f ≅ f' ≫ algebraicSpaceStackMap.{u, w} B S hS hY' hY p)
    (V : Subfunctor Y) (V' : Subfunctor Y')
    (hVV' : Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ⊆
      Space.pointsMap B S hS Y' p '' Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι))
    (h' : HasProperCompactifiableCover.{u, w} B S hS hY' f' V') :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  obtain ⟨Zbar, Z, hZbar, hZ, j, gbar, h, hj, hgbar, hh, ⟨eh⟩, hcov⟩ := h'
  have hcomp : algebraicSpaceStackMap.{u, w} B S hS hZ hY ((j ≫ gbar) ≫ p) =
      algebraicSpaceStackMap.{u, w} B S hS hZ hY' (j ≫ gbar) ≫
        algebraicSpaceStackMap.{u, w} B S hS hY' hY p := by
    simp only [algebraicSpaceStackMap, associatedMap_comp]
    rfl
  refine ⟨Zbar, Z, hZbar, hZ, j, gbar ≫ p, h ≫ a, hj,
    Space.isProper_comp B S hS hZbar hY' hY gbar p hgbar hp, isProper_comp B S hS h a hh ha,
    ⟨Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso h e ≪≫
      (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso eh _ ≪≫
      eqToIso hcomp.symm ≪≫ eqToIso (by rw [Category.assoc])⟩, ?_⟩
  intro v hv
  obtain ⟨v', hv', rfl⟩ := hVV' hv
  obtain ⟨z, rfl⟩ := hcov hv'
  exact ⟨z, by rw [← Category.assoc, Space.pointsMap_comp_apply]⟩

/-- **The initial remark of the proof of [Stacks, Tag 0CQ7] along a base change.** Let
`g : Y' ⟶ Y` be a proper surjective morphism of algebraic spaces and `V ⊆ Y` a subfunctor. If
the conclusion of [Stacks, Tag 0CQ7] holds for the base change `𝒳 ×_Y Y' ⟶ Y'` and `g⁻¹V`, it
holds for `(f, V)`: the projection `𝒳 ×_Y Y' ⟶ 𝒳` is proper (Stacks 0CL6) and `|g⁻¹V|` maps
onto `|V|`. -/
theorem HasProperCompactifiableCover.of_baseChange {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (g : Y' ⟶ Y) (hg : Space.IsProper B S hS g) (hgs : Space.IsSurjective B S hS g)
    (V : Subfunctor Y)
    (h : HasProperCompactifiableCover.{u, w} B S hS hY'
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f).fst
      (V.preimage g)) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  have ha : IsProper B S hS Q.snd :=
    isProper_baseChange B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ)
      ((isProper_algebraicSpaceStackMap_iff.{u, w} B S hS hY' hY g).2 hg)
  refine of_proper B S hS hY hY' f Q.fst g hg Q.snd ha Q.iso.symm V (V.preimage g) ?_ h
  rintro v ⟨w, rfl⟩
  obtain ⟨y, hy⟩ := hgs (Space.pointsMap B S hS V.toFunctor V.ι w)
  refine ⟨y, ?_, hy⟩
  rw [Space.range_pointsMap_preimage_ι]
  exact ⟨w, hy.symm⟩

/-- **The last step of the proof of [Stacks, Tag 0CQ7].** If `f : 𝒳 ⟶ Y` is separated and has
a section `x : Y ⟶ 𝒳` (that is, `x ≫ f` is 2-isomorphic to the identity), then the conclusion of
[Stacks, Tag 0CQ7] holds for every `V ⊆ Y`, with `Z̄ = Z = Y` and `h = x`, which is proper by
Stacks 050J. -/
theorem HasProperCompactifiableCover.of_section {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (hf : IsSeparated B S hS f)
    (x : algebraicSpaceStack.{u, w} B S hS Y hY ⟶ 𝒳) (hx : Nonempty (x ≫ f ≅ 𝟙 _))
    (V : Subfunctor Y) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  obtain ⟨η⟩ := hx
  have hxp : IsProper B S hS x :=
    (isProper_iff_isProper_hom B S hS x
      (isRepresentableByAlgebraicSpaces_section B S hS f x ⟨η⟩)).mpr
      (isRelativelyProper_section B S hS f x ⟨η⟩ hf)
  obtain ⟨e₀⟩ := nonempty_twoIso_associatedMap_id B S hS Y
  let e : 𝟙 (algebraicSpaceStack.{u, w} B S hS Y hY) ≅
      algebraicSpaceStackMap.{u, w} B S hS hY hY (𝟙 Y ≫ 𝟙 Y) :=
    (Bicategory.InducedBicategory.isoMk e₀ :
        algebraicSpaceStackMap.{u, w} B S hS hY hY (𝟙 Y) ≅ _).symm ≪≫
      eqToIso (by rw [Category.comp_id])
  refine ⟨Y, Y, hY, hY, 𝟙 Y, 𝟙 Y, x, Space.isOpenImmersion_of_isIso B S hS (𝟙 Y),
    Space.isProper_of_isIso B S hS (𝟙 Y), hxp, ⟨η ≪≫ e⟩, fun v _ => ⟨v, ?_⟩⟩
  rw [Category.comp_id, Space.pointsMap_id, id_eq]

end AlgebraicGeometry.Stack.AlgebraicStacks

end
