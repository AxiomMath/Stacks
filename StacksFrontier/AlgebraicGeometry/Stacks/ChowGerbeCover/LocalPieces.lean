module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable

/-!
# From Zariski local isomorphisms to compatible isomorphisms on pieces of `V`

The fifth paragraph of the proof of [Stacks, Tag 0CQ7], situation (e): the local sections `xᵢ`
and `xⱼ` are Zariski locally isomorphic over `V`. "Let `y ∈ V` be arbitrary. Suppose that we can
find a quasi-compact open neighbourhood `y ∈ V_y ⊂ V` such that the lemma is true for the pair
`(𝒳 → Y, V_y)` … Since `V` is quasi-compact, we can find `y₁, …, y_m` with
`V = V_{y₁} ∪ … ∪ V_{y_m}` … Given `y` by condition (e) we can choose a quasi-compact open
neighbourhood `y ∈ V_y ⊂ V` and isomorphisms `φᵢ : x₁|_{V_y} → xᵢ|_{V_y}`. Set
`φᵢⱼ = φⱼ ∘ φᵢ⁻¹`." This file proves exactly that reduction: section covers of the pieces
`V_y`, carrying the cocycle `φᵢⱼ`, glue (along unions of section covers) to one of `V`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.hasSectionCoverOver_of_localIsos`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace SectionFamily

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W : Subfunctor Y} {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₁ : IsAlgebraicSpace B S hS Y₁}
  {q₁ : Y₁ ⟶ Y}

/-- A subfunctor whose points have empty image has no points. -/
theorem isEmpty_points_of_range_eq_empty {G : Subfunctor Y₁}
    (h : Set.range (Space.pointsMap B S hS G.toFunctor G.ι) = ∅) :
    IsEmpty (Space.points B S hS G.toFunctor) :=
  ⟨fun p => by
    have := Set.mem_range_self (f := Space.pointsMap B S hS G.toFunctor G.ι) p
    rw [h] at this
    exact this⟩

/-- **Finite unions of section covers.** -/
theorem hasSectionCoverOver_openSubspaceOfPoints_biUnion (hW : Space.IsOpenSubspace B S hS W)
    (hunion : ∀ (V₁ V₂ V' : Subfunctor Y₁),
      HasSectionCoverOver hY f W hW hY₁ q₁ V₁ → HasSectionCoverOver hY f W hW hY₁ q₁ V₂ →
      Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι) ⊆
        Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) ∪
          Set.range (Space.pointsMap B S hS V₂.toFunctor V₂.ι) →
      HasSectionCoverOver hY f W hW hY₁ q₁ V')
    (hempty : ∀ V' : Subfunctor Y₁, IsEmpty (Space.points B S hS V'.toFunctor) →
      HasSectionCoverOver hY f W hW hY₁ q₁ V')
    {κ : Type*} (R : κ → Subfunctor Y₁)
    (hR : ∀ k, HasSectionCoverOver hY f W hW hY₁ q₁ (R k)) (s : Finset κ) :
    HasSectionCoverOver hY f W hW hY₁ q₁ (Space.openSubspaceOfPoints B S hS Y₁
      (⋃ k ∈ s, Set.range (Space.pointsMap B S hS (R k).toFunctor (R k).ι))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine hempty _ (isEmpty_points_of_range_eq_empty ?_)
    rw [Space.range_pointsMap_ι_openSubspaceOfPoints]
    simp
  | insert a s _ ih =>
    refine hunion _ _ _ ih (hR a) ?_
    rw [Space.range_pointsMap_ι_openSubspaceOfPoints, Space.range_pointsMap_ι_openSubspaceOfPoints,
      Finset.set_biUnion_insert, Set.union_comm]

/-- **Situation (e) of the proof of Stacks 0CQ7 reduces to situation (f) on pieces.** Let `F` be
a family of local sections indexed by `Fin (m + 1)` and `V₁` a quasi-compact open lying in every
open of `F`, such that around every point of `V₁` the first section is Zariski locally isomorphic
to every other (`hloc`). If every quasi-compact open `N ⊆ V₁` carrying isomorphisms
`φᵢⱼ : xᵢ|_N ≅ xⱼ|_N` with `φᵢⱼ ≫ φⱼₖ = φᵢₖ` has a section cover (`hpiece`), and section covers
glue along unions (`hunion`) and exist over subfunctors without points (`hempty`), then `V₁` has
a section cover. -/
theorem hasSectionCoverOver_of_localIsos (hW : Space.IsOpenSubspace B S hS W) {m : ℕ}
    (F : SectionFamily hY f W hY₁ q₁ (Fin (m + 1)))
    (hunion : ∀ (V₁ V₂ V' : Subfunctor Y₁),
      HasSectionCoverOver hY f W hW hY₁ q₁ V₁ → HasSectionCoverOver hY f W hW hY₁ q₁ V₂ →
      Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι) ⊆
        Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) ∪
          Set.range (Space.pointsMap B S hS V₂.toFunctor V₂.ι) →
      HasSectionCoverOver hY f W hW hY₁ q₁ V')
    (hempty : ∀ V' : Subfunctor Y₁, IsEmpty (Space.points B S hS V'.toFunctor) →
      HasSectionCoverOver hY f W hW hY₁ q₁ V')
    (V₁ : Subfunctor Y₁) (hV₁ : Space.IsOpenSubspace B S hS V₁)
    (hV₁qc : Space.IsQuasiCompactSpace B S hS V₁.toFunctor) (hVU : ∀ i, V₁ ≤ F.U i)
    (hloc : ∀ y ∈ Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι), ∀ j,
      ∃ (O : Subfunctor Y₁) (hO : Space.IsOpenSubspace B S hS O) (hOV : O ≤ V₁),
        y ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
        Nonempty (IsomFamily B S hS O.toFunctor hO.1
          (algebraicSpaceStackMap.{u, w} B S hS hO.1 (F.isOpen 0).1
            (Subfunctor.homOfLe (hOV.trans (hVU 0))) ≫ F.x 0)
          (algebraicSpaceStackMap.{u, w} B S hS hO.1 (F.isOpen j).1
            (Subfunctor.homOfLe (hOV.trans (hVU j))) ≫ F.x j)))
    (hpiece : ∀ (N : Subfunctor Y₁) (hN : Space.IsOpenSubspace B S hS N),
      Space.IsQuasiCompactSpace B S hS N.toFunctor → ∀ (hNU : ∀ i, N ≤ F.U i)
      (φ : ∀ i j, IsomFamily B S hS N.toFunctor hN.1
        (algebraicSpaceStackMap.{u, w} B S hS hN.1 (F.isOpen i).1 (Subfunctor.homOfLe (hNU i)) ≫
          F.x i)
        (algebraicSpaceStackMap.{u, w} B S hS hN.1 (F.isOpen j).1 (Subfunctor.homOfLe (hNU j)) ≫
          F.x j)),
      (∀ i j k T v, (φ i j).1 T v ≫ (φ j k).1 T v = (φ i k).1 T v) →
      HasSectionCoverOver hY f W hW hY₁ q₁ N) :
    HasSectionCoverOver hY f W hW hY₁ q₁ V₁ := by
  classical
  -- a piece around every point of `V₁`
  have hnbhd : ∀ y ∈ Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι),
      ∃ N : Subfunctor Y₁, Space.IsOpenSubspace B S hS N ∧
        y ∈ Set.range (Space.pointsMap B S hS N.toFunctor N.ι) ∧
        HasSectionCoverOver hY f W hW hY₁ q₁ N := by
    intro y hy
    choose O hO hOV hyO ψ using hloc y hy
    have hUopen : _root_.IsOpen (Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) ∩
        ⋂ j, Set.range (Space.pointsMap B S hS (O j).toFunctor (O j).ι)) :=
      (Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY₁ V₁ hV₁).inter
        (isOpen_iInter_of_finite fun j =>
          Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY₁ _ (hO j))
    obtain ⟨N, hN, hNqc, hyN, hNsub⟩ :=
      Space.exists_isQuasiCompactSpace_isOpenSubspace_range_subset B S hS hY₁ _ hUopen y
        ⟨hy, Set.mem_iInter.2 hyO⟩
    have hNV : N ≤ V₁ := Space.le_of_range_pointsMap_ι_subset B S hS hV₁
      (hNsub.trans Set.inter_subset_left)
    have hNO : ∀ j, N ≤ O j := fun j => Space.le_of_range_pointsMap_ι_subset B S hS (hO j)
      (hNsub.trans (Set.inter_subset_right.trans (Set.iInter_subset _ j)))
    have hNU : ∀ i, N ≤ F.U i := fun i => hNV.trans (hVU i)
    let ψ' : ∀ j, IsomFamily B S hS N.toFunctor hN.1
        (algebraicSpaceStackMap.{u, w} B S hS hN.1 (F.isOpen 0).1 (Subfunctor.homOfLe (hNU 0)) ≫
          F.x 0)
        (algebraicSpaceStackMap.{u, w} B S hS hN.1 (F.isOpen j).1 (Subfunctor.homOfLe (hNU j)) ≫
          F.x j) := fun j =>
      (ψ j).some.restrict hN.1 (Subfunctor.homOfLe (hNO j))
    refine ⟨N, hN, hyN, hpiece N hN hNqc hNU (fun i j => (ψ' i).symm.comp (ψ' j)) ?_⟩
    intro i j k T v
    have := isIso_fiberHom B S hS 𝒳 ((ψ' j).1 T v)
    simp only [IsomFamily.comp_apply, Category.assoc]
    change _ ≫ (ψ' j).1 T v ≫ CategoryTheory.inv ((ψ' j).1 T v) ≫ _ = _
    rw [IsIso.hom_inv_id_assoc]
  choose N hN hyN hNc using hnbhd
  -- finitely many pieces cover `V₁`
  have hcpt := isCompact_range_pointsMap_of_isQuasiCompactSpace hV₁.1 hV₁qc V₁.ι
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover
    (fun y : Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) =>
      Set.range (Space.pointsMap B S hS (N y.1 y.2).toFunctor (N y.1 y.2).ι))
    (fun y => Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY₁ _ (hN y.1 y.2))
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyN y hy⟩)
  have hfin := hasSectionCoverOver_openSubspaceOfPoints_biUnion hW hunion hempty
    (fun y : Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) => N y.1 y.2)
    (fun y => hNc y.1 y.2)
  refine (hfin t).mono ?_
  rw [Space.range_pointsMap_ι_openSubspaceOfPoints]
  exact ht

end SectionFamily

end AlgebraicGeometry.Stack.AlgebraicStacks

end
