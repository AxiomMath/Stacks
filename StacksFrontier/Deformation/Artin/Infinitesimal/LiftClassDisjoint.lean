module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.DisjointGluing
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftClassPresheaf

/-!
# Classes of lifts along a disjoint covering family (Stacks 0DNS)

Let `F` be the functor of isomorphism classes of lifts of Stacks 0DNS. For a family
`{W_j ⟶ W}` of `Over U'` whose underlying morphisms form a disjoint covering family of the big
fppf site (for instance `W = ∐ W_j`), restriction `F(W) ⟶ ∏ F(W_j)` is bijective: lifts and their
isomorphisms glue along such a family, because `𝒳` is a stack in groupoids and the overlaps of
two distinct members are void.

## Main results

* `Deformation.Artin.LiftClassSheaf.LiftClassPresheaf.existsUnique_of_isDisjointCover`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Deformation.Artin.LiftClassSheaf

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
  {U U' : BigAffineFppf B S hS} {i : U ⟶ U'} {x : 𝒳.val.val.obj}
  {hx : 𝒳.val.val.p.obj x = (BigAffineFppf.inclusion B S hS).obj U}

open InfinitesimalLift

/-- The square comparing two restrictions along a morphism of `Over U'` is cartesian. -/
theorem isPullback_baseMap {W₁ W₂ : Over U'} (r₁ : Restriction B S hS 𝒳 i x hx W₁)
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (g : W₂ ⟶ W₁) :
    IsPullback ((BigAffineFppf.inclusion B S hS).map (baseMap r₁ r₂ g))
      ((BigAffineFppf.inclusion B S hS).map r₂.toCover)
      ((BigAffineFppf.inclusion B S hS).map r₁.toCover)
      ((BigAffineFppf.inclusion B S hS).map g.left) := by
  refine IsPullback.of_right ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, baseMap_toCover])
    r₁.isPullback
  rw [← Functor.map_comp, ← Functor.map_comp, baseMap_toDef, Over.w g]
  exact r₂.isPullback

namespace LiftClassPresheaf

variable (P : LiftClassPresheaf B S hS 𝒳 i x hx)

/-- **Lift classes glue uniquely along a disjoint covering family**: restriction
`F(W) ⟶ ∏ F(W_j)` is bijective. -/
theorem existsUnique_of_isDisjointCover {E : Over U'} {I : Type w} (E' : I → Over U')
    (ε : ∀ j, E' j ⟶ E)
    (hdc : IsDisjointCover (BigFppfOver.topology B S hS)
      (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (E' j).left)
      (fun j ↦ (BigAffineFppf.inclusion B S hS).map (ε j).left))
    (s : ∀ j, P.presheaf.obj (op (E' j))) :
    ∃! t : P.presheaf.obj (op E), ∀ j, P.presheaf.map (ε j).op t = s j := by
  obtain ⟨_, ⟨_, hst⟩, _⟩ := 𝒳.property
  have hp := 𝒳.val.isFiberedInGroupoids
  let r := Classical.choice (P.nonempty_restriction E)
  let r' : ∀ j, Restriction B S hS 𝒳 i x hx (E' j) := fun j ↦
    Classical.choice (P.nonempty_restriction (E' j))
  have hdcT := hdc.of_isPullback ((BigAffineFppf.inclusion B S hS).map r.toCover)
    (fun j ↦ (BigAffineFppf.inclusion B S hS).map (baseMap r (r' j) (ε j)))
    (fun j ↦ (BigAffineFppf.inclusion B S hS).map (r' j).toCover)
    (fun j ↦ isPullback_baseMap r (r' j) (ε j))
  have hdisj := fun j j' (hjj' : j ≠ j') ↦ hdc.2.2 j j' hjj' _ _ pullback.condition
  have hrobj : 𝒳.val.val.p.obj r.obj = (BigAffineFppf.inclusion B S hS).obj r.base :=
    IsHomLift.domain_eq _ ((BigAffineFppf.inclusion B S hS).map r.toDef) r.hom
  refine existsUnique_of_exists_of_unique ?_ ?_
  · -- existence: glue the lifted objects, then the arrows from the restriction of `x`
    choose l hl using fun j ↦ P.cls_surjective (r' j) (s j)
    obtain ⟨z, hz, ζ, hζ⟩ := hst.exists_glue_obj hdc.1 hdc.2.1 hdisj (fun j ↦ (l j).obj)
      (fun j ↦ obj_proj (l j))
    have hh : ∀ j, 𝒳.val.val.p.IsHomLift
        ((BigAffineFppf.inclusion B S hS).map (baseMap r (r' j) (ε j)) ≫
          (BigAffineFppf.inclusion B S hS).map r.toCover) ((l j).hom ≫ ζ j) := fun j ↦ by
      have := hζ j
      have : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (r' j).toCover ≫
          (BigAffineFppf.inclusion B S hS).map (ε j).left) ((l j).hom ≫ ζ j) := inferInstance
      have e : (BigAffineFppf.inclusion B S hS).map (r' j).toCover ≫
          (BigAffineFppf.inclusion B S hS).map (ε j).left =
          (BigAffineFppf.inclusion B S hS).map (baseMap r (r' j) (ε j)) ≫
            (BigAffineFppf.inclusion B S hS).map r.toCover := by
        rw [← Functor.map_comp, ← Functor.map_comp, baseMap_toCover]
      exact isHomLift_of_eq' e ((l j).hom ≫ ζ j)
    obtain ⟨v, ⟨hvl, hvw⟩, -⟩ := hst.existsUnique_glue_hom_over hdcT hrobj hz
      ((BigAffineFppf.inclusion B S hS).map r.toCover) (fun j ↦ (r' j).obj)
      (fun j ↦ restrictionMap r (r' j) (ε j)) (fun j ↦ inferInstance)
      (fun j ↦ (l j).hom ≫ ζ j) hh
    have := hvl
    let L : InfinitesimalLift B S hS 𝒳 i x hx r :=
      { obj := z
        hom := v
        isCartesian := hp.isStronglyCartesian_homLift _ _ }
    refine ⟨P.cls r L, fun j ↦ ?_⟩
    rw [← hl j]
    have := hζ j
    exact P.cls_map (ε j) r (r' j) L (l j) ⟨baseMap r (r' j) (ε j), restrictionMap r (r' j) (ε j),
      ζ j, baseMap_toCover _ _ _, baseMap_toDef _ _ _, inferInstance, restrictionMap_hom _ _ _,
      hp.isStronglyCartesian_homLift _ _, (hvw j).symm⟩
  · -- uniqueness: glue the isomorphisms of the restricted lifts
    intro t₁ t₂ ht₁ ht₂
    obtain ⟨L₁, rfl⟩ := P.cls_surjective r t₁
    obtain ⟨L₂, rfl⟩ := P.cls_surjective r t₂
    have hcls : ∀ (L : InfinitesimalLift B S hS 𝒳 i x hx r) j,
        P.cls (r' j) (baseChange (r' j) (ε j) L) = P.presheaf.map (ε j).op (P.cls r L) :=
      fun L j ↦ (P.cls_map (ε j) r (r' j) L _ (isRestrictionAlong_baseChange _ _ _)).symm
    have hiso : ∀ j, Isomorphic B S hS 𝒳 i x hx (baseChange (r' j) (ε j) L₁)
        (baseChange (r' j) (ε j) L₂) := fun j ↦ by
      rw [← P.cls_eq_iff, hcls, hcls, ht₁, ht₂]
    choose θ hθI hθl hθw using hiso
    have hα : ∀ (L : InfinitesimalLift B S hS 𝒳 i x hx r) j,
        𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (ε j).left)
          (IsPreFibered.pullbackMap (obj_proj L)
            ((BigAffineFppf.inclusion B S hS).map (ε j).left)) := fun L j ↦ inferInstance
    obtain ⟨Θ, ⟨hΘl, hΘw⟩, -⟩ := hst.existsUnique_glue_hom hdc.1 hdc.2.1 hdisj (obj_proj L₁)
      (obj_proj L₂) (fun j ↦ (baseChange (r' j) (ε j) L₁).obj)
      (fun j ↦ (baseChange (r' j) (ε j) L₂).obj) _ _ (hα L₁) (hα L₂) θ hθl
    have := hΘl
    obtain ⟨_, -, huniq⟩ := hst.existsUnique_glue_hom_over hdcT hrobj (obj_proj L₂)
      ((BigAffineFppf.inclusion B S hS).map r.toCover) (fun j ↦ (r' j).obj)
      (fun j ↦ restrictionMap r (r' j) (ε j)) (fun j ↦ inferInstance)
      (fun j ↦ restrictionMap r (r' j) (ε j) ≫ L₂.hom) fun j ↦ inferInstance
    have hw : L₁.hom ≫ Θ = L₂.hom := by
      refine (huniq _ ⟨inferInstance, fun j ↦ ?_⟩).trans (huniq _ ⟨inferInstance, fun j ↦ rfl⟩).symm
      exact (((baseChange_hom_comp_assoc (r' j) (ε j) L₁ Θ).symm.trans
        (Category.assoc _ _ _)).trans
          (congrArg (fun t ↦ (baseChange (r' j) (ε j) L₁).hom ≫ t) (hΘw j))).trans
        ((reassoc_of% (hθw j)) _ |>.trans (baseChange_hom_comp _ _ _))
    have := hp.isStronglyCartesian_homLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj E.left)) Θ
    exact (P.cls_eq_iff r L₁ L₂).2
      ⟨Θ, IsStronglyCartesian.isIso_of_base_isIso (p := 𝒳.val.val.p)
        (f := 𝟙 ((BigAffineFppf.inclusion B S hS).obj E.left)) Θ, hΘl, hw⟩

end LiftClassPresheaf

end Deformation.Artin.LiftClassSheaf

end
