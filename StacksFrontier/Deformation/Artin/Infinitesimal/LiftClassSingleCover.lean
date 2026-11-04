module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartNerveClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.LiftCover
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftClassDisjoint

/-!
# The sheaf condition of Stacks 0DNS for one affine fppf covering

Let `F` be the functor of isomorphism classes of lifts of Stacks 0DNS, for an algebraic stack
`𝒳` whose spaces of arrows of charts are locally of finite presentation (which follows from
the inertia being locally of finite presentation) and a deformation situation `(i, x)`. For a
morphism `k : W' ⟶ W` of `Over U'` which is flat, surjective and locally of finite presentation,
restriction `F(W) ⟶ F(W')` is injective, and its image is the equalizer of the two restrictions
to `W' ×_W W'`.

These are the restatements in terms of `F` of
`AlgebraicGeometry.Stack.GroupoidLift.exists_hom_of_cover_of_arrSpace` and
`AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_cover_of_arrSpace`, for the deformation
situation `x|_{B' ⊗_{A'} A}` over `W = Spec B'`.

## Main results

* `Deformation.Artin.LiftClassSheaf.Restriction.isDeformationSituation_toCover`.
* `Deformation.Artin.LiftClassSheaf.LiftClassPresheaf.injective_map_of_fppf`.
* `Deformation.Artin.LiftClassSheaf.LiftClassPresheaf.exists_map_eq_of_fppf`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry.Stack AlgebraicGeometry.Stack.GroupoidLift

namespace Deformation.Artin.LiftClassSheaf

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
  {U U' : BigAffineFppf B S hS} {i : U ⟶ U'} {x : 𝒳.val.val.obj}
  {hx : 𝒳.val.val.p.obj x = (BigAffineFppf.inclusion B S hS).obj U}

open InfinitesimalLift

/-- **The restriction of a deformation situation is a deformation situation**: `B' → B' ⊗_{A'} A`
is a square-zero surjection along with `A' → A`. -/
theorem Restriction.isDeformationSituation_toCover
    (hi : IsDeformationSituation (ringMap B S hS i).hom) {W : Over U'}
    (r : Restriction B S hS 𝒳 i x hx W) :
    IsDeformationSituation (ringMap B S hS r.toCover).hom := by
  obtain ⟨hs, hk⟩ := CommRingCat.surjective_and_ker_of_isPushout r.isPushout.flip hi.1
  refine ⟨hs, ?_⟩
  rw [hk, ← Ideal.map_pow, hi.2, Ideal.map_bot]

/-- The restriction of `x` lies over the base of the restriction. -/
theorem Restriction.obj_proj {W : Over U'} (r : Restriction B S hS 𝒳 i x hx W) :
    𝒳.val.val.p.obj r.obj = (BigAffineFppf.inclusion B S hS).obj r.base :=
  IsHomLift.domain_eq _ ((BigAffineFppf.inclusion B S hS).map r.toDef) r.hom

/-- Two restrictions of `x` along composable comparisons compose. -/
theorem baseMap_comp {W₁ W₂ W₃ : Over U'} (r₁ : Restriction B S hS 𝒳 i x hx W₁)
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (r₃ : Restriction B S hS 𝒳 i x hx W₃) (g : W₂ ⟶ W₁)
    (g' : W₃ ⟶ W₂) : baseMap r₂ r₃ g' ≫ baseMap r₁ r₂ g = baseMap r₁ r₃ (g' ≫ g) :=
  r₁.hom_ext (by simp) (by simp)

namespace LiftClassPresheaf

variable (P : LiftClassPresheaf B S hS 𝒳 i x hx)

/-- **Restriction of lift classes along an affine fppf morphism is injective.** -/
theorem injective_map_of_fppf (harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳.val)
    (hi : IsDeformationSituation (ringMap B S hS i).hom) {W W' : Over U'} (k : W' ⟶ W)
    (hkf : Flat ((BigAffineFppf.toScheme B S hS).map k.left))
    (hks : Surjective ((BigAffineFppf.toScheme B S hS).map k.left))
    (hkp : LocallyOfFinitePresentation ((BigAffineFppf.toScheme B S hS).map k.left)) :
    Function.Injective (P.presheaf.map k.op) := by
  intro t₁ t₂ ht
  let r := Classical.choice (P.nonempty_restriction W)
  let r' := Classical.choice (P.nonempty_restriction W')
  obtain ⟨L₁, rfl⟩ := P.cls_surjective r t₁
  obtain ⟨L₂, rfl⟩ := P.cls_surjective r t₂
  have hiso : Isomorphic B S hS 𝒳 i x hx (baseChange r' k L₁) (baseChange r' k L₂) := by
    rw [← P.cls_eq_iff, ← P.cls_map k r r' L₁ _ (isRestrictionAlong_baseChange _ _ _),
      ← P.cls_map k r r' L₂ _ (isRestrictionAlong_baseChange _ _ _), ht]
  obtain ⟨θ, -, hθl, hθw⟩ := hiso
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj W.left)) := W.left.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj r.base)) := r.base.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj W'.left)) := W'.left.property
  have := hθl
  have :=
    isStronglyCartesian_pullbackMap (obj_proj L₁) ((BigAffineFppf.inclusion B S hS).map k.left)
  have :=
    isStronglyCartesian_pullbackMap (obj_proj L₂) ((BigAffineFppf.inclusion B S hS).map k.left)
  have hρ₁ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map k.left)
      (IsPreFibered.pullbackMap (obj_proj L₁) ((BigAffineFppf.inclusion B S hS).map k.left)) :=
    (isStronglyCartesian_pullbackMap (obj_proj L₁) _).toIsHomLift
  have hρ₂' : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map k.left)
      (IsPreFibered.pullbackMap (obj_proj L₂) ((BigAffineFppf.inclusion B S hS).map k.left)) :=
    (isStronglyCartesian_pullbackMap (obj_proj L₂) _).toIsHomLift
  have hρ₂ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map k.left)
      (θ ≫ IsPreFibered.pullbackMap (obj_proj L₂) ((BigAffineFppf.inclusion B S hS).map k.left)) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒳.val.val.p _ _ _ _ _ _ _ hρ₂' θ hθl
  obtain ⟨θ', hθ'l, hθ'w⟩ := exists_hom_of_cover_of_arrSpace 𝒳.property harr
    ((BigAffineFppf.inclusion B S hS).map r.toCover) (r.isDeformationSituation_toCover hi)
    ((BigAffineFppf.inclusion B S hS).map (baseMap r r' k))
    ((BigAffineFppf.inclusion B S hS).map r'.toCover) ((BigAffineFppf.inclusion B S hS).map k.left)
    (isPullback_baseMap r r' k) hkf hks hkp r.obj_proj (restrictionMap r r' k) inferInstance
    (baseChange r' k L₁).hom inferInstance L₁.hom inferInstance L₂.hom inferInstance
    _ hρ₁ _ hρ₂ (baseChange_hom_comp _ _ _)
    ((reassoc_of% hθw) _ |>.trans (baseChange_hom_comp _ _ _))
  have := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift
    (𝟙 ((BigAffineFppf.inclusion B S hS).obj W.left)) θ'
  exact (P.cls_eq_iff r L₁ L₂).2 ⟨θ', IsStronglyCartesian.isIso_of_base_isIso (p := 𝒳.val.val.p)
    (f := 𝟙 ((BigAffineFppf.inclusion B S hS).obj W.left)) θ', hθ'l, hθ'w⟩

/-- **A lift class over an affine fppf covering whose two restrictions to the double overlap
agree comes from the base.** -/
theorem exists_map_eq_of_fppf (harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳.val)
    (hi : IsDeformationSituation (ringMap B S hS i).hom) {W W' W'' : Over U'} (k : W' ⟶ W)
    (hkf : Flat ((BigAffineFppf.toScheme B S hS).map k.left))
    (hks : Surjective ((BigAffineFppf.toScheme B S hS).map k.left))
    (hkp : LocallyOfFinitePresentation ((BigAffineFppf.toScheme B S hS).map k.left))
    (p₁ p₂ : W'' ⟶ W') (hp : p₁ ≫ k = p₂ ≫ k)
    (hpb : IsPullback ((BigAffineFppf.inclusion B S hS).map p₁.left)
      ((BigAffineFppf.inclusion B S hS).map p₂.left) ((BigAffineFppf.inclusion B S hS).map k.left)
      ((BigAffineFppf.inclusion B S hS).map k.left))
    (t : P.presheaf.obj (op W')) (ht : P.presheaf.map p₁.op t = P.presheaf.map p₂.op t) :
    ∃ s, P.presheaf.map k.op s = t := by
  let r := Classical.choice (P.nonempty_restriction W)
  let r' := Classical.choice (P.nonempty_restriction W')
  let r'' := Classical.choice (P.nonempty_restriction W'')
  obtain ⟨m, rfl⟩ := P.cls_surjective r' t
  have hiso : Isomorphic B S hS 𝒳 i x hx (baseChange r'' p₁ m) (baseChange r'' p₂ m) := by
    rw [← P.cls_eq_iff, ← P.cls_map p₁ r' r'' m _ (isRestrictionAlong_baseChange _ _ _),
      ← P.cls_map p₂ r' r'' m _ (isRestrictionAlong_baseChange _ _ _), ht]
  obtain ⟨θ, -, hθl, hθw⟩ := hiso
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj W.left)) := W.left.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj r.base)) := r.base.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj r'.base)) := r'.base.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj W'.left)) := W'.left.property
  have := hθl
  have :=
    isStronglyCartesian_pullbackMap (obj_proj m) ((BigAffineFppf.inclusion B S hS).map p₁.left)
  have :=
    isStronglyCartesian_pullbackMap (obj_proj m) ((BigAffineFppf.inclusion B S hS).map p₂.left)
  have := (baseChange r'' p₁ m).isCartesian
  have hpb₃ : IsPullback ((BigAffineFppf.inclusion B S hS).map (baseMap r r'' (p₁ ≫ k)))
      ((BigAffineFppf.inclusion B S hS).map r''.toCover)
      ((BigAffineFppf.inclusion B S hS).map r.toCover)
      ((BigAffineFppf.inclusion B S hS).map p₁.left ≫
        (BigAffineFppf.inclusion B S hS).map k.left) := by
    rw [← Functor.map_comp, ← Over.comp_left]
    exact isPullback_baseMap r r'' (p₁ ≫ k)
  have hγ : restrictionMap r' r'' p₁ ≫ restrictionMap r r' k =
      restrictionMap r' r'' p₂ ≫ restrictionMap r r' k := by
    have e₁ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (baseMap r r'' (p₁ ≫ k)))
        (restrictionMap r' r'' p₁ ≫ restrictionMap r r' k) := by
      rw [← baseMap_comp r r' r'' k p₁, Functor.map_comp]
      infer_instance
    have e₂ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (baseMap r r'' (p₁ ≫ k)))
        (restrictionMap r' r'' p₂ ≫ restrictionMap r r' k) := by
      rw [hp, ← baseMap_comp r r' r'' k p₂, Functor.map_comp]
      infer_instance
    refine IsStronglyCartesian.ext 𝒳.val.val.p ((BigAffineFppf.inclusion B S hS).map r.toDef)
      r.hom ((BigAffineFppf.inclusion B S hS).map (baseMap r r'' (p₁ ≫ k))) ?_
    simp only [Category.assoc, restrictionMap_hom]
  have hσ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map p₁.left)
      (IsPreFibered.pullbackMap (obj_proj m) ((BigAffineFppf.inclusion B S hS).map p₁.left)) :=
    (isStronglyCartesian_pullbackMap (obj_proj m) _).toIsHomLift
  have hτ' : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map p₂.left)
      (IsPreFibered.pullbackMap (obj_proj m) ((BigAffineFppf.inclusion B S hS).map p₂.left)) :=
    (isStronglyCartesian_pullbackMap (obj_proj m) _).toIsHomLift
  have hτ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map p₂.left)
      (θ ≫ IsPreFibered.pullbackMap (obj_proj m) ((BigAffineFppf.inclusion B S hS).map p₂.left)) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒳.val.val.p _ _ _ _ _ _ _ hτ' θ hθl
  have hδ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map r''.toCover)
      (baseChange r'' p₁ m).hom := inferInstance
  obtain ⟨z, hz, φ, ρ, hφ, hρ, hw⟩ := exists_lift_of_cover_of_arrSpace 𝒳.property harr
    ((BigAffineFppf.inclusion B S hS).map r.toCover) (r.isDeformationSituation_toCover hi)
    ((BigAffineFppf.inclusion B S hS).map (baseMap r r' k))
    ((BigAffineFppf.inclusion B S hS).map r'.toCover) ((BigAffineFppf.inclusion B S hS).map k.left)
    (isPullback_baseMap r r' k) (r'.isDeformationSituation_toCover hi) hkf hks hkp
    ((BigAffineFppf.inclusion B S hS).map p₁.left) ((BigAffineFppf.inclusion B S hS).map p₂.left)
    hpb ((BigAffineFppf.inclusion B S hS).map (baseMap r r'' (p₁ ≫ k)))
    ((BigAffineFppf.inclusion B S hS).map r''.toCover) hpb₃
    ((BigAffineFppf.inclusion B S hS).map (baseMap r' r'' p₁))
    ((BigAffineFppf.inclusion B S hS).map (baseMap r' r'' p₂))
    (by rw [← Functor.map_comp, ← Functor.map_comp, baseMap_toCover])
    (by rw [← Functor.map_comp, ← Functor.map_comp, baseMap_toCover])
    (by rw [← Functor.map_comp, baseMap_comp])
    (by rw [← Functor.map_comp, baseMap_comp, hp])
    r.obj_proj (restrictionMap r r' k) inferInstance m.hom inferInstance
    (restrictionMap r' r'' p₁) (restrictionMap r' r'' p₂) inferInstance inferInstance hγ
    _ _ hσ hτ (baseChange r'' p₁ m).hom hδ
    (baseChange_hom_comp _ _ _) ((reassoc_of% hθw) _ |>.trans (baseChange_hom_comp _ _ _))
  have := hφ
  have := hρ
  let L : InfinitesimalLift B S hS 𝒳 i x hx r :=
    { obj := z
      hom := φ
      isCartesian := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _ }
  exact ⟨P.cls r L, P.cls_map k r r' L m ⟨baseMap r r' k, restrictionMap r r' k, ρ,
    baseMap_toCover _ _ _, baseMap_toDef _ _ _, inferInstance, restrictionMap_hom _ _ _,
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _, hw⟩⟩

end LiftClassPresheaf

end Deformation.Artin.LiftClassSheaf

end
