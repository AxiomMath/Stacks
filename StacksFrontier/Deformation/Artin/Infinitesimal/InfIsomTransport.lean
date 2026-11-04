module

public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# Vertical endomorphisms transported to the chosen pullbacks of `Mor(x, x)`

Let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids, `x` an object of the fibre over `V`, and
`Mor(x, x)` the presheaf of Stacks 02ZB on `𝒞/V`, whose sections over `W ⟶ V` are the vertical
endomorphisms of the *chosen* pullback of `x` along `W`.

An object `z` with an arrow `c : z ⟶ x` over `t : R ⟶ V` is another pullback of `x`; when `R` is
identified with `W` by an isomorphism `ι` compatible with the maps to `V`, the universal property
of the chosen pullback gives an isomorphism `z ⟶ W^* x` over `ι`
(`Deformation.Artin.cartesianCmp`). Conjugating by it carries a vertical endomorphism `θ` of `z`
to a section of `Mor(x, x)` over `W` (`Deformation.Artin.cartesianCmpEnd`), and this transport is
compatible with the restriction maps of `Mor(x, x)`: if `k : z₁ ⟶ z₂` is an arrow compatible with
the two arrows to `x` and `θ₁` is the restriction of `θ₂` along `k`, then the transport of `θ₁` is
the restriction of the transport of `θ₂` (`Deformation.Artin.morRestrict_cartesianCmpEnd`).

This is how the infinitesimal automorphisms of a trivial deformation, which are vertical
endomorphisms of *some* pullback of `x` along `Spec A[M] ⟶ Spec A`, are read as sections of the
automorphism space `Isom(x, x)` of `x`.

## Main definitions

* `Deformation.Artin.cartesianCmp`: the comparison arrow `z ⟶ W^* x`.
* `Deformation.Artin.cartesianCmpEnd`: the transport of a vertical endomorphism of `z`.

## Main results

* `Deformation.Artin.cartesianCmpEnd_spec`, `Deformation.Artin.eq_cartesianCmpEnd_iff`: the
  transport is the unique section conjugate to `θ`.
* `Deformation.Artin.morRestrict_cartesianCmpEnd`: transport commutes with restriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) [p.IsFibered] {V : 𝒞} (x : p.Fiber V)

section Transport

variable {z : 𝒳} {R : 𝒞} {t : R ⟶ V} (c : z ⟶ x.1) [p.IsHomLift t c]
  (W : Over V) (ι : R ⟶ W.left) (hι : ι ≫ W.hom = t)

/-- The comparison arrow from an object `z` with an arrow `c : z ⟶ x` over `t : R ⟶ V` to the
chosen pullback of `x` along `W ⟶ V`, lying over an arrow `ι : R ⟶ W` compatible with the maps
to `V`. -/
noncomputable def cartesianCmp : z ⟶ (pullbackFiber p x W.hom).1 :=
  IsStronglyCartesian.map p W.hom (IsPreFibered.pullbackMap x.2 W.hom) hι.symm c

/-- The comparison arrow `z ⟶ W^* x` lies over `ι`. -/
instance cartesianCmp_isHomLift : p.IsHomLift ι (cartesianCmp p x c W ι hι) := by
  unfold cartesianCmp; infer_instance

/-- The comparison arrow followed by the structure arrow `W^* x ⟶ x` of the chosen pullback is
`c`. -/
@[reassoc (attr := simp)]
theorem cartesianCmp_fac :
    cartesianCmp p x c W ι hι ≫ IsPreFibered.pullbackMap x.2 W.hom = c :=
  IsStronglyCartesian.fac p W.hom _ _ _

include hp in
/-- When `ι` is an isomorphism, so is the comparison arrow `z ⟶ W^* x`. -/
theorem isIso_cartesianCmp [IsIso ι] : IsIso (cartesianCmp p x c W ι hι) := by
  have := hp.isStronglyCartesian_homLift ι (cartesianCmp p x c W ι hι)
  exact IsStronglyCartesian.isIso_of_base_isIso p ι _

/-- A composite of three arrows lies over the composite of the arrows they lie over. -/
private theorem isHomLift_comp₃ (p : 𝒳 ⥤ 𝒞) {a b c d : 𝒳} {R₁ R₂ R₃ R₄ : 𝒞} {f₁ : R₁ ⟶ R₂}
    {f₂ : R₂ ⟶ R₃} {f₃ : R₃ ⟶ R₄} (φ₁ : a ⟶ b) (φ₂ : b ⟶ c) (φ₃ : c ⟶ d) [p.IsHomLift f₁ φ₁]
    [p.IsHomLift f₂ φ₂] [p.IsHomLift f₃ φ₃] {f : R₁ ⟶ R₄} (e : f₁ ≫ f₂ ≫ f₃ = f) :
    p.IsHomLift f (φ₁ ≫ φ₂ ≫ φ₃) :=
  e ▸ inferInstance

/-- The conjugate of a vertical endomorphism `θ` of `z` by the comparison arrow `z ≅ W^* x` is a
vertical endomorphism of the chosen pullback. -/
theorem isHomLift_cartesianCmp_conj [IsIso ι] (θ : z ⟶ z) [p.IsHomLift (𝟙 R) θ]
    [IsIso (cartesianCmp p x c W ι hι)] :
    p.IsHomLift (𝟙 W.left)
      (inv (cartesianCmp p x c W ι hι) ≫ θ ≫ cartesianCmp p x c W ι hι) := by
  exact isHomLift_comp₃ p (f₁ := inv ι) (f₂ := 𝟙 R) (f₃ := ι) _ _ _ (by simp)

/-- **The transport of a vertical endomorphism.** A vertical endomorphism `θ` of `z`, conjugated
by the comparison `z ≅ W^* x`, as a section of `Mor(x, x)` over `W`. -/
noncomputable def cartesianCmpEnd [IsIso ι] (θ : z ⟶ z) [p.IsHomLift (𝟙 R) θ] :
    pullbackFiber p x W.hom ⟶ pullbackFiber p x W.hom :=
  haveI := isIso_cartesianCmp p hp x c W ι hι
  ⟨inv (cartesianCmp p x c W ι hι) ≫ θ ≫ cartesianCmp p x c W ι hι,
    isHomLift_cartesianCmp_conj p x c W ι hι θ⟩

/-- The comparison arrow `z ≅ W^* x` intertwines `θ` with its transport. -/
theorem cartesianCmpEnd_spec [IsIso ι] (θ : z ⟶ z) [p.IsHomLift (𝟙 R) θ] :
    θ ≫ cartesianCmp p x c W ι hι =
      cartesianCmp p x c W ι hι ≫ Fiber.fiberInclusion.map (cartesianCmpEnd p hp x c W ι hι θ) := by
  have := isIso_cartesianCmp p hp x c W ι hι
  change _ = _ ≫ inv (cartesianCmp p x c W ι hι) ≫ θ ≫ cartesianCmp p x c W ι hι
  simp

/-- The transport of `θ` is the only section of `Mor(x, x)` over `W` conjugate to `θ` under the
comparison `z ≅ W^* x`. -/
theorem eq_cartesianCmpEnd_iff [IsIso ι] (θ : z ⟶ z) [p.IsHomLift (𝟙 R) θ]
    (g : pullbackFiber p x W.hom ⟶ pullbackFiber p x W.hom) :
    g = cartesianCmpEnd p hp x c W ι hι θ ↔
      θ ≫ cartesianCmp p x c W ι hι = cartesianCmp p x c W ι hι ≫ Fiber.fiberInclusion.map g := by
  have := isIso_cartesianCmp p hp x c W ι hι
  refine ⟨fun hg ↦ hg ▸ cartesianCmpEnd_spec p hp x c W ι hι θ, fun h ↦ Fiber.hom_ext ?_⟩
  change Fiber.fiberInclusion.map g = inv (cartesianCmp p x c W ι hι) ≫ θ ≫ _
  rw [h]
  simp

/-- The transport of the identity is the identity. -/
theorem cartesianCmpEnd_id [IsIso ι] :
    haveI : p.IsHomLift (𝟙 R) (𝟙 z) := IsHomLift.id (IsHomLift.domain_eq p t c)
    cartesianCmpEnd p hp x c W ι hι (𝟙 z) = 𝟙 _ := by
  have : p.IsHomLift (𝟙 R) (𝟙 z) := IsHomLift.id (IsHomLift.domain_eq p t c)
  symm
  rw [eq_cartesianCmpEnd_iff, CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Transport is injective. -/
theorem cartesianCmpEnd_injective [IsIso ι] (θ θ' : z ⟶ z) [p.IsHomLift (𝟙 R) θ]
    [p.IsHomLift (𝟙 R) θ']
    (h : cartesianCmpEnd p hp x c W ι hι θ = cartesianCmpEnd p hp x c W ι hι θ') : θ = θ' := by
  have := isIso_cartesianCmp p hp x c W ι hι
  have h₁ := cartesianCmpEnd_spec p hp x c W ι hι θ
  have h₂ := cartesianCmpEnd_spec p hp x c W ι hι θ'
  rw [h] at h₁
  rw [← h₂] at h₁
  exact (cancel_mono _).1 h₁

/-- The vertical endomorphism of `z` conjugate to a section `g` of `Mor(x, x)` over `W`. -/
noncomputable def cartesianCmpEndInv [IsIso ι]
    (g : pullbackFiber p x W.hom ⟶ pullbackFiber p x W.hom) : z ⟶ z :=
  haveI := isIso_cartesianCmp p hp x c W ι hι
  cartesianCmp p x c W ι hι ≫ Fiber.fiberInclusion.map g ≫ inv (cartesianCmp p x c W ι hι)

/-- The endomorphism of `z` conjugate to a section of `Mor(x, x)` over `W` is vertical. -/
theorem cartesianCmpEndInv_isHomLift [IsIso ι]
    (g : pullbackFiber p x W.hom ⟶ pullbackFiber p x W.hom) :
    p.IsHomLift (𝟙 R) (cartesianCmpEndInv p hp x c W ι hι g) := by
  have := isIso_cartesianCmp p hp x c W ι hι
  have : p.IsHomLift (𝟙 W.left) (Fiber.fiberInclusion.map g) := g.2
  unfold cartesianCmpEndInv
  exact isHomLift_comp₃ p (f₁ := ι) (f₂ := 𝟙 W.left) (f₃ := inv ι) _ _ _ (by simp)

/-- The transport of the endomorphism conjugate to a section `g` is `g` itself. -/
theorem cartesianCmpEnd_cartesianCmpEndInv [IsIso ι]
    (g : pullbackFiber p x W.hom ⟶ pullbackFiber p x W.hom) :
    haveI := cartesianCmpEndInv_isHomLift p hp x c W ι hι g
    cartesianCmpEnd p hp x c W ι hι (cartesianCmpEndInv p hp x c W ι hι g) = g := by
  have := cartesianCmpEndInv_isHomLift p hp x c W ι hι g
  have := isIso_cartesianCmp p hp x c W ι hι
  symm
  rw [eq_cartesianCmpEnd_iff]
  simp [cartesianCmpEndInv]

end Transport

section Naturality

variable {z₁ z₂ : 𝒳} {R₁ R₂ : 𝒞} {t₁ : R₁ ⟶ V} {t₂ : R₂ ⟶ V} (c₁ : z₁ ⟶ x.1) (c₂ : z₂ ⟶ x.1)
  [p.IsHomLift t₁ c₁] [p.IsHomLift t₂ c₂] {W₁ W₂ : Over V} (ι₁ : R₁ ⟶ W₁.left)
  (ι₂ : R₂ ⟶ W₂.left) [IsIso ι₁] [IsIso ι₂] (hι₁ : ι₁ ≫ W₁.hom = t₁) (hι₂ : ι₂ ≫ W₂.hom = t₂)
  {h : R₁ ⟶ R₂} (k : z₁ ⟶ z₂) [p.IsHomLift h k] (hk : k ≫ c₂ = c₁) (H : W₁ ⟶ W₂)
  (hH : ι₁ ≫ H.left = h ≫ ι₂)

omit [IsIso ι₂] in
include hk hH in
/-- The restriction map of the chosen pullbacks is the comparison of `z₁` with `z₂` read through
the two comparisons. -/
theorem pullbackFiberMap_eq_cartesianCmp :
    haveI := isIso_cartesianCmp p hp x c₁ W₁ ι₁ hι₁
    pullbackFiberMap p x H =
      inv (cartesianCmp p x c₁ W₁ ι₁ hι₁) ≫ k ≫ cartesianCmp p x c₂ W₂ ι₂ hι₂ := by
  have := isIso_cartesianCmp p hp x c₁ W₁ ι₁ hι₁
  have hl : p.IsHomLift H.left
      (inv (cartesianCmp p x c₁ W₁ ι₁ hι₁) ≫ k ≫ cartesianCmp p x c₂ W₂ ι₂ hι₂) :=
    isHomLift_comp₃ p (f₁ := inv ι₁) (f₃ := ι₂) _ _ _ (by rw [← hH, IsIso.inv_hom_id_assoc])
  refine IsStronglyCartesian.ext p W₂.hom (IsPreFibered.pullbackMap x.2 W₂.hom) H.left ?_
  rw [pullbackFiberMap_fac, Category.assoc, Category.assoc, cartesianCmp_fac, hk,
    IsIso.eq_inv_comp, cartesianCmp_fac]

include hk hH in
/-- **Transport commutes with restriction.** If `θ₁` is the restriction of `θ₂` along an arrow
`k : z₁ ⟶ z₂` compatible with the arrows to `x`, the transport of `θ₁` is the restriction of the
transport of `θ₂` in `Mor(x, x)`. -/
theorem morRestrict_cartesianCmpEnd (θ₁ : z₁ ⟶ z₁) (θ₂ : z₂ ⟶ z₂) [p.IsHomLift (𝟙 R₁) θ₁]
    [p.IsHomLift (𝟙 R₂) θ₂] (hθ : θ₁ ≫ k = k ≫ θ₂) :
    morRestrict p x x H (cartesianCmpEnd p hp x c₂ W₂ ι₂ hι₂ θ₂) =
      cartesianCmpEnd p hp x c₁ W₁ ι₁ hι₁ θ₁ := by
  have := isIso_cartesianCmp p hp x c₁ W₁ ι₁ hι₁
  have := isIso_cartesianCmp p hp x c₂ W₂ ι₂ hι₂
  symm
  refine morRestrict_uniq p x x H _ _ ?_
  rw [pullbackFiberMap_eq_cartesianCmp p hp x c₁ c₂ ι₁ ι₂ hι₁ hι₂ k hk H hH]
  change (inv (cartesianCmp p x c₁ W₁ ι₁ hι₁) ≫ θ₁ ≫ cartesianCmp p x c₁ W₁ ι₁ hι₁) ≫ _ =
    (inv (cartesianCmp p x c₁ W₁ ι₁ hι₁) ≫ k ≫ cartesianCmp p x c₂ W₂ ι₂ hι₂) ≫
      (inv (cartesianCmp p x c₂ W₂ ι₂ hι₂) ≫ θ₂ ≫ cartesianCmp p x c₂ W₂ ι₂ hι₂) ≫ _
  simp only [Category.assoc, cartesianCmp_fac, IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% hθ, hk]

end Naturality

end Deformation.Artin
