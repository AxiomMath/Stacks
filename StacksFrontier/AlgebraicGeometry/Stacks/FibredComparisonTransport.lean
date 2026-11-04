module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothFaithfulTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# Transporting limit preservation and lifts along comparisons of categories fibred in groupoids

Let `p : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, and let `E : 𝒳' ⥤ 𝒳` and `G : 𝒴 ⥤ 𝒴'` be functors which lie strictly over the site,
are fully faithful, and are essentially surjective through vertical isomorphisms. The categories
`𝒳'`, `𝒴'` may have their hom types in other universes than `𝒳`, `𝒴`: this is the situation of
the small model `CategoryTheory.BasedCategory.shrinkHoms` of a category whose morphisms are not
small, and of the category of elements of an algebraic space next to its category of test
schemes.

The composite `E ⋙ p ⋙ G` is a 1-morphism `𝒳' ⟶ 𝒴'`, and this file shows that it inherits
from `p`

* limit preservation on objects (Stacks 06CU), and
* the lifting property along first-order thickenings of affine objects which, over a target
  with faithful structure functor, is formal smoothness on objects
  (`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_faithful_of_exists_lift`).

## Main definitions

* `AlgebraicGeometry.Stack.FibredComparison`: a functor strictly over the site, fully faithful
  and essentially surjective through vertical isomorphisms.
* `AlgebraicGeometry.Stack.FibredComparison.conj`: the 1-morphism `E ⋙ p ⋙ G`.
* `AlgebraicGeometry.Stack.HasThickeningLifts`: the lifting property.

## Main results

* `AlgebraicGeometry.Stack.FibredComparison.isLimitPreservingOnObjects_conj`.
* `AlgebraicGeometry.Stack.FibredComparison.hasThickeningLifts_conj`.

## Implementation notes

In a category fibred in groupoids every morphism is strongly cartesian over its image
(`CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift`), so only the lifting
conditions have to be transported.

No declaration here carries a tag; these are inputs of the proof of Stacks 0DPJ.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v₁ w₁ v₂ w₂ v₃ w₃

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism lies over `f` along a functor which is strictly over the base exactly when its
image does. -/
theorem isHomLift_map_iff_of_comp_eq {𝒜 : Type*} {𝒜' : Type*} [Category 𝒜] [Category 𝒜']
    {𝒮 : Type*} [Category 𝒮] {G : 𝒜 ⥤ 𝒜'} {q : 𝒜' ⥤ 𝒮} {p : 𝒜 ⥤ 𝒮} (hG : G ⋙ q = p)
    {R T : 𝒮} (f : R ⟶ T) {a b : 𝒜} (φ : a ⟶ b) :
    q.IsHomLift f (G.map φ) ↔ p.IsHomLift f φ := by
  subst hG
  exact ⟨fun _ ↦ IsHomLift.of_fac' (G ⋙ q) f φ (IsHomLift.domain_eq q f (G.map φ))
      (IsHomLift.codomain_eq q f (G.map φ)) (IsHomLift.fac' q f (G.map φ)),
    fun _ ↦ IsHomLift.of_fac' q f (G.map φ) (IsHomLift.domain_eq (G ⋙ q) f φ)
      (IsHomLift.codomain_eq (G ⋙ q) f φ) (IsHomLift.fac' (G ⋙ q) f φ)⟩

section Generic

variable {𝒜 : Type*} [Category 𝒜] {𝒮 : Type*} [Category 𝒮] {p : 𝒜 ⥤ 𝒮}

/-- A morphism over `f` followed by one over an identity lies over `f`. -/
theorem isHomLift_comp_of_vertical_right {R T : 𝒮} (f : R ⟶ T) {a b c : 𝒜} (φ : a ⟶ b)
    (ψ : b ⟶ c) (h₁ : p.IsHomLift f φ) (h₂ : p.IsHomLift (𝟙 T) ψ) : p.IsHomLift f (φ ≫ ψ) := by
  have := h₁
  have := h₂
  infer_instance

/-- A morphism over an identity followed by one over `f` lies over `f`. -/
theorem isHomLift_comp_of_vertical_left {R T : 𝒮} (f : R ⟶ T) {a b c : 𝒜} (φ : a ⟶ b)
    (ψ : b ⟶ c) (h₁ : p.IsHomLift (𝟙 R) φ) (h₂ : p.IsHomLift f ψ) : p.IsHomLift f (φ ≫ ψ) := by
  have := h₁
  have := h₂
  infer_instance

/-- The inverse of a vertical isomorphism is vertical. -/
theorem isHomLift_inv_of_vertical (R : 𝒮) {a b : 𝒜} (φ : a ⟶ b) [IsIso φ]
    (h : p.IsHomLift (𝟙 R) φ) : p.IsHomLift (𝟙 R) (inv φ) := by
  have := h
  infer_instance

/-- Transport of a vertical lift along an equality of objects of the base. -/
theorem isHomLift_id_of_eq {R R' : 𝒮} (e : R = R') {a b : 𝒜} (φ : a ⟶ b)
    (h : p.IsHomLift (𝟙 R) φ) : p.IsHomLift (𝟙 R') φ := by
  subst e
  exact h

end Generic

/-- The equation closing the transport of limit preservation, over plain categories. -/
theorem conj_comm_eq {𝒜' 𝒜 ℬ ℬ' : Type*} [Category 𝒜'] [Category 𝒜] [Category ℬ]
    [Category ℬ'] (E : 𝒜' ⥤ 𝒜) [E.Full] [E.Faithful] (P : 𝒜 ⥤ ℬ) (G : ℬ ⥤ ℬ') [G.Full]
    [G.Faithful] {x' x₁' : 𝒜'} {xU x₁ : 𝒜} {y0 : ℬ} {y' : ℬ'} (β : xU ⟶ E.obj x') [IsIso β]
    (δ : xU ⟶ x₁) (η : E.obj x₁' ⟶ x₁) [IsIso η] (γ₁ : P.obj x₁ ⟶ y0) (ε : G.obj y0 ⟶ y')
    [IsIso ε] (γ' : G.obj (P.obj (E.obj x')) ⟶ y')
    (hcomm : P.map δ ≫ γ₁ = P.map β ≫ G.preimage (γ' ≫ inv ε)) :
    G.map (P.map (E.map (E.preimage (inv β ≫ δ ≫ inv η)))) ≫ G.map (P.map η ≫ γ₁) ≫ ε =
      G.map (P.map (E.map (𝟙 x'))) ≫ γ' := by
  rw [Functor.map_preimage, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc, ← G.map_comp]
  have hc : P.map (inv β ≫ δ ≫ inv η) ≫ P.map η ≫ γ₁ = G.preimage (γ' ≫ inv ε) := by
    rw [← Category.assoc, ← P.map_comp, Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, P.map_comp, Category.assoc, hcomm, ← Category.assoc, ← P.map_comp,
      IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hc, Functor.map_preimage, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **A comparison of categories fibred in groupoids**: a functor `𝒳' ⥤ 𝒳` lying strictly over
the site, fully faithful, and essentially surjective through vertical isomorphisms. -/
structure FibredComparison (𝒳' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS))
    (𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)) where
  /-- The functor. -/
  F : 𝒳'.val.obj ⥤ 𝒳.val.obj
  /-- It lies strictly over the site. -/
  w : F ⋙ 𝒳.val.p = 𝒳'.val.p
  /-- It is full. -/
  full : F.Full
  /-- It is faithful. -/
  faithful : F.Faithful
  /-- Every object is isomorphic, by a vertical isomorphism, to an object in its image. -/
  essSurj : ∀ x : 𝒳.val.obj, ∃ (x' : 𝒳'.val.obj) (η : F.obj x' ⟶ x),
    IsIso η ∧ 𝒳.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x)) η

namespace FibredComparison

variable {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}

/-- The image of an object lies over the same object of the site. -/
theorem w_obj (E : FibredComparison 𝒳' 𝒳) (x : 𝒳'.val.obj) :
    𝒳.val.p.obj (E.F.obj x) = 𝒳'.val.p.obj x :=
  Functor.congr_obj E.w x

/-- A morphism lies over `f` exactly when its image does. -/
theorem isHomLift_map_iff (E : FibredComparison 𝒳' 𝒳) {R T : BigFppfOver B S hS} (f : R ⟶ T)
    {a b : 𝒳'.val.obj} (φ : a ⟶ b) :
    𝒳.val.p.IsHomLift f (E.F.map φ) ↔ 𝒳'.val.p.IsHomLift f φ :=
  isHomLift_map_iff_of_comp_eq E.w f φ

/-- An object over `T` is isomorphic, by a vertical isomorphism, to the image of an object over
`T`. -/
private theorem exists_vertical_iso_of_obj_eq (E : FibredComparison 𝒳' 𝒳) {T : BigFppfOver B S hS}
    {x : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = T) :
    ∃ (x' : 𝒳'.val.obj) (η : E.F.obj x' ⟶ x), IsIso η ∧ 𝒳.val.p.IsHomLift (𝟙 T) η ∧
      𝒳'.val.p.obj x' = T := by
  subst hx
  obtain ⟨x', η, hη, hηl⟩ := E.essSurj x
  exact ⟨x', η, hη, hηl,
    (E.w_obj x').symm.trans (IsHomLift.domain_eq 𝒳.val.p (𝟙 (𝒳.val.p.obj x)) η)⟩

/-- A morphism over `f`, corrected by the inverse of a vertical isomorphism, descends to a
morphism over `f`. -/
private theorem isHomLift_preimage_comp_inv (E : FibredComparison 𝒳' 𝒳) [E.F.Full]
    {R T : BigFppfOver B S hS} (f : R ⟶ T) {a c : 𝒳'.val.obj} {b : 𝒳.val.obj}
    (ψ : E.F.obj a ⟶ b) (η : E.F.obj c ⟶ b) [IsIso η] (hψ : 𝒳.val.p.IsHomLift f ψ)
    (hη : 𝒳.val.p.IsHomLift (𝟙 T) η) : 𝒳'.val.p.IsHomLift f (E.F.preimage (ψ ≫ inv η)) := by
  refine (E.isHomLift_map_iff _ _).1 ?_
  rw [Functor.map_preimage]
  exact isHomLift_comp_of_vertical_right f ψ (inv η) hψ (isHomLift_inv_of_vertical T η hη)

/-- The lift condition for the composite `G (p η ≫ γ₁) ≫ ε` used to transport the lifts. -/
private theorem isHomLift_map_comp_comp (E : FibredComparison 𝒳' 𝒳) (p : 𝒳 ⟶ 𝒴)
    (G : FibredComparison 𝒴 𝒴') {R T : BigFppfOver B S hS} (f : R ⟶ T) {x' : 𝒳'.val.obj}
    {x₁ : 𝒳.val.obj} {y0 : 𝒴.val.obj} {y' : 𝒴'.val.obj} (η : E.F.obj x' ⟶ x₁)
    (γ₁ : (CatFiberedInGroupoids.homFunctor p).obj x₁ ⟶ y0) (ε : G.F.obj y0 ⟶ y')
    (hη : 𝒳.val.p.IsHomLift (𝟙 R) η) (hγ₁ : 𝒴.val.p.IsHomLift f γ₁)
    (hε : 𝒴'.val.p.IsHomLift (𝟙 T) ε) :
    𝒴'.val.p.IsHomLift f (G.F.map ((CatFiberedInGroupoids.homFunctor p).map η ≫ γ₁) ≫ ε) := by
  have h0 : 𝒴.val.p.IsHomLift (𝟙 R) ((CatFiberedInGroupoids.homFunctor p).map η) :=
    (isHomLift_map_iff_of_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p p) _ η).2 hη
  exact isHomLift_comp_of_vertical_right _ _ ε ((G.isHomLift_map_iff _ _).2
    (isHomLift_comp_of_vertical_left _ _ γ₁ h0 hγ₁)) hε

/-- **The 1-morphism `E ⋙ p ⋙ G`.** -/
def conj (E : FibredComparison 𝒳' 𝒳) (p : 𝒳 ⟶ 𝒴) (G : FibredComparison 𝒴 𝒴') : 𝒳' ⟶ 𝒴' :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := E.F ⋙ CatFiberedInGroupoids.homFunctor p ⋙ G.F
      w := by
        change E.F ⋙ CatFiberedInGroupoids.homFunctor p ⋙ G.F ⋙ 𝒴'.val.p = 𝒳'.val.p
        rw [G.w, CatFiberedInGroupoids.homFunctor_comp_p, E.w] }

/-- **Limit preservation on objects is inherited by `E ⋙ p ⋙ G`** (Stacks 06CU). -/
theorem isLimitPreservingOnObjects_conj (E : FibredComparison 𝒳' 𝒳) (p : 𝒳 ⟶ 𝒴)
    (G : FibredComparison 𝒴 𝒴')
    (hp : BigFppfOver.IsLimitPreservingOnObjects.{u, v₃, w₃} B S hS 𝒳 𝒴 p) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v₃, w₃} B S hS 𝒳' 𝒴' (E.conj p G) := by
  intro I _ _ D c hc i y' x' γ' hγ'
  let := E.full
  let := E.faithful
  let := G.full
  let := G.faithful
  let P := CatFiberedInGroupoids.homFunctor p
  let x : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt) :=
    ⟨E.F.obj x'.1, (E.w_obj x'.1).trans x'.2⟩
  obtain ⟨y0, ε, hεiso, hε', hy0⟩ := G.exists_vertical_iso_of_obj_eq y'.2
  have := hεiso
  let y : 𝒴.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)) := ⟨y0, hy0⟩
  let γ : P.obj x.1 ⟶ y.1 := G.F.preimage (γ' ≫ inv ε)
  have hγl : 𝒴.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) γ :=
    G.isHomLift_preimage_comp_inv _ γ' ε hγ'.toIsHomLift hε'
  have hγ := @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ _
    𝒴.isFiberedInGroupoids _ _ _ _ ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) γ hγl
  obtain ⟨i₁, j, x₁, xU, δ, β, γ₁, hδ, hβ, hβiso, hγ₁, hcomm⟩ := hp I D c hc i y x γ hγ
  obtain ⟨x₁', η, hηiso, hη', hx₁'⟩ := E.exists_vertical_iso_of_obj_eq x₁.2
  have := hβiso
  have := hηiso
  let δ' : x'.1 ⟶ x₁' := E.F.preimage (inv β ≫ δ ≫ inv η)
  have hδ'l : 𝒳'.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i₁)) δ' := by
    have := E.isHomLift_preimage_comp_inv _ (inv β ≫ δ) η
      (isHomLift_comp_of_vertical_left _ _ _ (isHomLift_inv_of_vertical _ β hβ) hδ.toIsHomLift)
      hη'
    rwa [Category.assoc] at this
  let γ₁' : (CatFiberedInGroupoids.homFunctor (E.conj p G)).obj x₁' ⟶ y'.1 :=
    G.F.map (P.map η ≫ γ₁) ≫ ε
  have hγ₁'l : 𝒴'.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (D.map j)) γ₁' :=
    E.isHomLift_map_comp_comp p G _ η γ₁ ε hη' hγ₁.toIsHomLift hε'
  refine ⟨i₁, j, ⟨x₁', hx₁'⟩, x', δ', 𝟙 _, γ₁',
    @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ _
      𝒳'.isFiberedInGroupoids _ _ _ _ _ δ' hδ'l,
    IsHomLift.id x'.2, inferInstance,
    @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ _
      𝒴'.isFiberedInGroupoids _ _ _ _ _ γ₁' hγ₁'l, ?_⟩
  exact conj_comm_eq E.F P G.F β δ η γ₁ ε γ' hcomm

end FibredComparison

/-- **The lifting property along first-order thickenings of affine objects** of a 1-morphism
`g : 𝒜 ⟶ ℬ`: for every first-order thickening `i : U ⟶ U'` of affine objects of the site, every
object `x` of `𝒜` over `U` and every morphism `ψ : g(x) ⟶ y'` of `ℬ` over `i`, there are an
object `x'` of `𝒜` over `U'`, a morphism `x ⟶ x'` over `i` and a morphism `g(x') ⟶ y'` over the
identity of `U'`. Over a target with faithful structure functor this is formal smoothness on
objects (`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_faithful_of_exists_lift`). -/
def HasThickeningLifts {𝒜 ℬ : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    (g : 𝒜 ⟶ ℬ) : Prop :=
  ∀ {U U' : BigFppfOver B S hS} (i : U ⟶ U'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
    Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
    ∀ {x : 𝒜.val.obj} (_ : 𝒜.val.p.obj x = U) {y' : ℬ.val.obj} (_ : ℬ.val.p.obj y' = U')
      (ψ : (CatFiberedInGroupoids.homFunctor g).obj x ⟶ y') [ℬ.val.p.IsHomLift i ψ],
      ∃ (x' : 𝒜.val.obj) (_ : 𝒜.val.p.obj x' = U') (β : x ⟶ x') (_ : 𝒜.val.p.IsHomLift i β)
        (γ' : (CatFiberedInGroupoids.homFunctor g).obj x' ⟶ y'),
        ℬ.val.p.IsHomLift (𝟙 U') γ'

namespace FibredComparison

variable {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}

/-- **The lifting property is inherited by `E ⋙ p ⋙ G`.** -/
theorem hasThickeningLifts_conj (E : FibredComparison 𝒳' 𝒳) (p : 𝒳 ⟶ 𝒴)
    (G : FibredComparison 𝒴 𝒴') (hp : HasThickeningLifts p) :
    HasThickeningLifts (E.conj p G) := by
  intro U U' i hU hU' hi x hx y' hy' ψ hψ
  let := E.full
  let := E.faithful
  let := G.full
  let := G.faithful
  let P := CatFiberedInGroupoids.homFunctor p
  obtain ⟨y0, ε, hεiso, hε', hy0⟩ := G.exists_vertical_iso_of_obj_eq hy'
  have := hεiso
  have := G.isHomLift_preimage_comp_inv i ψ ε hψ hε'
  obtain ⟨x₁, hx₁, β, hβ, γ₁, hγ₁⟩ := hp i hU hU' hi ((E.w_obj x).trans hx) hy0
    (G.F.preimage (ψ ≫ inv ε))
  obtain ⟨x₁', η, hηiso, hη', hx₁'⟩ := E.exists_vertical_iso_of_obj_eq hx₁
  have := hηiso
  exact ⟨x₁', hx₁', E.F.preimage (β ≫ inv η), E.isHomLift_preimage_comp_inv i β η hβ hη',
    G.F.map (P.map η ≫ γ₁) ≫ ε, E.isHomLift_map_comp_comp p G _ η γ₁ ε hη' hγ₁ hε'⟩

end FibredComparison

end AlgebraicGeometry.Stack

end
