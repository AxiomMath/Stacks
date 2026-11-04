module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactificationSection

/-!
# Section covers in the proof of Stacks 0CQ7

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space all of whose values
lie in an open subspace `W ⊆ Y`. The last step of the proof of [Stacks, Tag 0CQ7]
(`AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_section_preimage`)
needs a proper morphism `p : Y' ⟶ Y` of algebraic spaces and a 1-morphism `x : p⁻¹(W) ⟶ 𝒳`
over `Y`. Every reduction of that proof replaces `Y` by a space proper over it; this file records
the datum the proof carries through those replacements, relative to a proper `q₀ : Y₀ ⟶ Y`: a
proper `p : Y' ⟶ Y₀` and a 1-morphism `x : (p ≫ q₀)⁻¹(W) ⟶ 𝒳` over `Y` whose source covers a
given subfunctor `V₀ ⊆ Y₀` on points.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionAlong`: a 1-morphism `g⁻¹(W) ⟶ 𝒳` over `Y`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver`: the datum above.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver.trans`: a section cover over a
  proper `r ≫ q₀` whose points cover those of `V₀` is a section cover over `q₀`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver.hasProperCompactifiableCover`:
  over the identity of `Y`, the conclusion of Stacks 0CQ7 follows for a separated `f`.
* `AlgebraicGeometry.Stack.eq_of_iso_algebraicSpaceStack`: 2-isomorphic 1-morphisms into the
  stack of an algebraic space are equal.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A 1-morphism `x : g⁻¹(W) ⟶ 𝒳` whose composite with `f` is the inclusion of `g⁻¹(W)` followed
by `g`. -/
def HasSectionAlong {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (W : Subfunctor Y) (hW : Space.IsOpenSubspace B S hS W)
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y) :
    Prop :=
  ∃ x : algebraicSpaceStack.{u, w} B S hS (W.preimage g).toFunctor
      (Space.isOpenSubspace_preimage B S hS g W hY hY' hW).1 ⟶ 𝒳,
    x ≫ f = algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS g W hY hY' hW).1 hY ((W.preimage g).ι ≫ g)

/-- `HasSectionAlong` is invariant under replacing `g` by an equal morphism `g'`. -/
theorem HasSectionAlong.congr {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    {hW : Space.IsOpenSubspace B S hS W} {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY' : IsAlgebraicSpace B S hS Y'} {g g' : Y' ⟶ Y} (h : HasSectionAlong hY f W hW hY' g)
    (e : g = g') : HasSectionAlong hY f W hW hY' g' :=
  e ▸ h

/-- **A section cover over `q₀ : Y₀ ⟶ Y`** of a subfunctor `V₀ ⊆ Y₀`: a proper morphism
`p : Y' ⟶ Y₀` of algebraic spaces and a 1-morphism `(p ≫ q₀)⁻¹(W) ⟶ 𝒳` over `Y`, such that every
point of `V₀` is the image of a point of `(p ≫ q₀)⁻¹(W)`. -/
def HasSectionCoverOver {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (W : Subfunctor Y) (hW : Space.IsOpenSubspace B S hS W)
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hY₀ : IsAlgebraicSpace B S hS Y₀) (q₀ : Y₀ ⟶ Y)
    (V₀ : Subfunctor Y₀) : Prop :=
  ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY' : IsAlgebraicSpace B S hS Y') (p : Y' ⟶ Y₀),
    Space.IsProper B S hS p ∧ HasSectionAlong hY f W hW hY' (p ≫ q₀) ∧
      Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) ⊆
        Space.pointsMap B S hS Y' p '' (Space.pointsMap B S hS Y' (p ≫ q₀) ⁻¹'
          Set.range (Space.pointsMap B S hS W.toFunctor W.ι))

/-- **Composing section covers with a proper morphism.** A section cover over `r ≫ q₀` of `V₁`,
for a proper `r : Y₁ ⟶ Y₀` mapping the points of `V₁` onto a set containing those of `V₀`, is a
section cover over `q₀` of `V₀`. -/
theorem HasSectionCoverOver.trans {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    {hW : Space.IsOpenSubspace B S hS W} {Y₀ Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY₀ : IsAlgebraicSpace B S hS Y₀) (hY₁ : IsAlgebraicSpace B S hS Y₁) {q₀ : Y₀ ⟶ Y}
    (r : Y₁ ⟶ Y₀) (hr : Space.IsProper B S hS r) {V₀ : Subfunctor Y₀} {V₁ : Subfunctor Y₁}
    (h : HasSectionCoverOver hY f W hW hY₁ (r ≫ q₀) V₁)
    (hV : Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) ⊆
      Space.pointsMap B S hS Y₁ r '' Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι)) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ := by
  obtain ⟨Y', hY', p, hp, hx, hcov⟩ := h
  have e : p ≫ r ≫ q₀ = (p ≫ r) ≫ q₀ := (Category.assoc _ _ _).symm
  refine ⟨Y', hY', p ≫ r, Space.isProper_comp B S hS hY' hY₁ hY₀ p r hp hr, hx.congr e, ?_⟩
  rintro _ hv
  obtain ⟨v₁, hv₁, rfl⟩ := hV hv
  obtain ⟨z, hz, rfl⟩ := hcov hv₁
  refine ⟨z, ?_, by rw [Space.pointsMap_comp_apply]⟩
  rw [Set.mem_preimage, ← e, Space.pointsMap_comp_apply]
  rwa [Set.mem_preimage, Space.pointsMap_comp_apply] at hz

/-- **Section covers are monotone in the covered subfunctor.** -/
theorem HasSectionCoverOver.mono {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    {hW : Space.IsOpenSubspace B S hS W} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y} {V₀ V₀' : Subfunctor Y₀}
    (h : HasSectionCoverOver hY f W hW hY₀ q₀ V₀)
    (hV : Set.range (Space.pointsMap B S hS V₀'.toFunctor V₀'.ι) ⊆
      Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι)) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀' := by
  obtain ⟨Y', hY', p, hp, hx, hcov⟩ := h
  exact ⟨Y', hY', p, hp, hx, hV.trans hcov⟩

/-- **A section cover over the identity gives the conclusion of Stacks 0CQ7.** If `f` is
separated and all its values lie in `W`, a section cover over `𝟙 Y` of `V` is the datum of
`HasProperCompactifiableCover.of_section_preimage`. -/
theorem HasSectionCoverOver.hasProperCompactifiableCover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    {hW : Space.IsOpenSubspace B S hS W} {V : Subfunctor Y}
    (h : HasSectionCoverOver hY f W hW hY (𝟙 Y) V) (hf : IsSeparated B S hS f)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ))) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  obtain ⟨Y', hY', p, hp, hx, hcov⟩ := h
  obtain ⟨x, hx⟩ := hx.congr (Category.comp_id p)
  refine HasProperCompactifiableCover.of_section_preimage hY hY' f hf W hW hfW p hp x
    ⟨eqToIso hx⟩ V ?_
  intro v hv
  obtain ⟨z, hz, rfl⟩ := hcov hv
  rw [Category.comp_id] at hz
  rw [← Space.range_pointsMap_preimage_ι] at hz
  obtain ⟨z', rfl⟩ := hz
  exact ⟨z', by rw [Space.pointsMap_comp_apply]⟩

/-- **Two 2-isomorphic 1-morphisms into the algebraic stack of an algebraic space are equal**:
the category attached to a presheaf of sets has no non-identity vertical morphisms. -/
theorem _root_.AlgebraicGeometry.Stack.eq_of_iso_algebraicSpaceStack
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hT : IsAlgebraicSpace B S hS T}
    {a b : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS T hT} (e : a ≅ b) : a = b :=
  Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS e.hom.hom)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
