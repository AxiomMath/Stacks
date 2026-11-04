module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.IsomFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiCompactOperations

/-!
# Families of local sections in the proof of Stacks 0CQ7

From its fourth paragraph on, the proof of [Stacks, Tag 0CQ7] works with quasi-compact opens
`W₁, …, Wₙ` of the base and 1-morphisms `xᵢ : Wᵢ ⟶ 𝒳` with `f ∘ xᵢ = id`, whose union is the
image `W` of `f`. Each reduction replaces the base by a space proper over it; here the base is a
space `Y₀` with a proper `q₀ : Y₀ ⟶ Y`, the opens lie in `q₀⁻¹(W)` and cover it, and
`f ∘ xᵢ = q₀|_{Wᵢ}`. This file packages that datum and its restriction along a proper morphism.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily`: the datum above.
* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.left` and `.right`: the restrictions of
  `xᵢ` and `xⱼ` to `Wᵢ ∩ Wⱼ`, between which the proof constructs isomorphisms.
* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.restrict`: the restriction along a
  proper morphism `r : Y₁ ⟶ Y₀`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A family of local sections over a proper base.** Over `q₀ : Y₀ ⟶ Y`: quasi-compact open
subspaces `U i ⊆ q₀⁻¹(W)` covering `q₀⁻¹(W)` on points, and 1-morphisms `x i : U i ⟶ 𝒳` with
`x i ≫ f` the inclusion of `U i` followed by `q₀`. -/
structure SectionFamily {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (W : Subfunctor Y) {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (q₀ : Y₀ ⟶ Y) (ι : Type) where
  /-- The open subspaces. -/
  U : ι → Subfunctor Y₀
  isOpen : ∀ i, Space.IsOpenSubspace B S hS (U i)
  isQC : ∀ i, Space.IsQuasiCompactSpace B S hS (U i).toFunctor
  le : ∀ i, U i ≤ W.preimage q₀
  cover : Set.range (Space.pointsMap B S hS (W.preimage q₀).toFunctor (W.preimage q₀).ι) ⊆
    ⋃ i, Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι)
  /-- The local sections. -/
  x : ∀ i, algebraicSpaceStack.{u, w} B S hS (U i).toFunctor (isOpen i).1 ⟶ 𝒳
  hx : ∀ i, x i ≫ f = algebraicSpaceStackMap.{u, w} B S hS (isOpen i).1 hY ((U i).ι ≫ q₀)

namespace SectionFamily

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W : Subfunctor Y} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀}
  {q₀ : Y₀ ⟶ Y} {ι : Type}

/-- The intersection `U i ∩ U j` is an open subspace of `Y₀`. -/
theorem isOpen_inf (F : SectionFamily hY f W hY₀ q₀ ι) (i j : ι) :
    Space.IsOpenSubspace B S hS (F.U i ⊓ F.U j) :=
  Space.isOpenSubspace_inf B S hS hY₀ _ _ (F.isOpen i) (F.isOpen j)

/-- The restriction of `x i` to `U i ∩ U j`. -/
noncomputable def left (F : SectionFamily hY f W hY₀ q₀ ι) (i j : ι) :
    algebraicSpaceStack.{u, w} B S hS (F.U i ⊓ F.U j).toFunctor (F.isOpen_inf i j).1 ⟶ 𝒳 :=
  algebraicSpaceStackMap.{u, w} B S hS (F.isOpen_inf i j).1 (F.isOpen i).1
    (Subfunctor.homOfLe inf_le_left) ≫ F.x i

/-- The restriction of `x j` to `U i ∩ U j`. -/
noncomputable def right (F : SectionFamily hY f W hY₀ q₀ ι) (i j : ι) :
    algebraicSpaceStack.{u, w} B S hS (F.U i ⊓ F.U j).toFunctor (F.isOpen_inf i j).1 ⟶ 𝒳 :=
  algebraicSpaceStackMap.{u, w} B S hS (F.isOpen_inf i j).1 (F.isOpen j).1
    (Subfunctor.homOfLe inf_le_right) ≫ F.x j

/-- The restrictions of `x i` and `x j` to `U i ∩ U j` have the same composite with `f`. -/
theorem left_comp_eq_right_comp (F : SectionFamily hY f W hY₀ q₀ ι) (i j : ι) :
    F.left i j ≫ f = F.right i j ≫ f := by
  simp only [left, right, Category.assoc, F.hx]
  rw [← algebraicSpaceStackMap_comp, ← algebraicSpaceStackMap_comp]
  rfl

/-- **Natural isomorphisms between the restrictions of `x i` and `x j` to `U i ∩ U j`.** -/
abbrev Isos (F : SectionFamily hY f W hY₀ q₀ ι) (i j : ι) : Type _ :=
  IsomFamily B S hS (F.U i ⊓ F.U j).toFunctor (F.isOpen_inf i j).1 (F.left i j) (F.right i j)

/-- **The restriction of a family of local sections along a proper morphism** `r : Y₁ ⟶ Y₀`:
the opens are the inverse images `r⁻¹(U i)` and the sections are `x i ∘ r`. -/
noncomputable def restrict (F : SectionFamily hY f W hY₀ q₀ ι)
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁) (r : Y₁ ⟶ Y₀)
    (hr : Space.IsQuasiCompact B S hS r) : SectionFamily hY f W hY₁ (r ≫ q₀) ι where
  U i := (F.U i).preimage r
  isOpen i := Space.isOpenSubspace_preimage B S hS r (F.U i) hY₀ hY₁ (F.isOpen i)
  isQC i := Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₀ hY₁ r hr
    (F.isOpen i) (F.isQC i)
  le i := fun T y hy => F.le i T hy
  cover := by
    rintro _ ⟨y, rfl⟩
    have hy : Space.pointsMap B S hS Y₁ r
        (Space.pointsMap B S hS _ (W.preimage (r ≫ q₀)).ι y) ∈
        Set.range (Space.pointsMap B S hS (W.preimage q₀).toFunctor (W.preimage q₀).ι) := by
      rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, ← Space.pointsMap_comp_apply]
      have := Space.range_pointsMap_preimage_ι B S hS (r ≫ q₀) W
      exact this.le ⟨y, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (F.cover hy)
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rw [Space.range_pointsMap_preimage_ι]
    exact hi
  x i := algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS r (F.U i) hY₀ hY₁ (F.isOpen i)).1 (F.isOpen i).1
      ((F.U i).fromPreimage r) ≫ F.x i
  hx i := by
    rw [Category.assoc, F.hx, ← algebraicSpaceStackMap_comp]
    congr 1

end SectionFamily

end AlgebraicGeometry.Stack.AlgebraicStacks

end
