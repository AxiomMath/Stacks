module

public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.Chart
public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveSingleArrow

/-!
# The descent datum on the chart of an object of a descent datum

Let `D` be a descent datum of a category fibred in groupoids `𝒳` over the big fppf site of `S`,
relative to a sieve `R` of `U`, and let `f : W ⟶ U` be an arrow of `R`, with `x = D f` the object
over `W`. For a 1-morphism `g : 𝒮/P ⥤ 𝒳` and a product `T = W × P`, a point of the presheaf of
pairs `(ψ : Z ⟶ T, m : x|_{ψ ≫ pr₁} ⟶ g (ψ ≫ pr₂))` can be moved along any `t : Z ⟶ T` agreeing
with `ψ` over `U × P`, by twisting `m` with the gluing isomorphism of `D`. This file defines that
action on a representing object `Q` of the presheaf, and proves that it lies over `t`, that it is
associative, and that it is natural in `Z`.

## Main definitions

* `AlgebraicGeometry.Stack.ChartAction.twist`: the twisted vertical morphism.
* `AlgebraicGeometry.Stack.ChartAction.act`: the action on points of `Q`.

## Main results

* `AlgebraicGeometry.Stack.ChartAction.act_comp_π`, `AlgebraicGeometry.Stack.ChartAction.act_act`
  and `AlgebraicGeometry.Stack.ChartAction.comp_act`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

/-- A composite of three morphisms lying over an identity lies over that identity. -/
lemma isHomLift_id_comp₃ {𝒮 𝒳₀ : Type*} [Category 𝒮] [Category 𝒳₀] {p : 𝒳₀ ⥤ 𝒮} {Z : 𝒮}
    {a b c d : 𝒳₀} (φ₁ : a ⟶ b) (φ₂ : b ⟶ c) (φ₃ : c ⟶ d) (h₁ : p.IsHomLift (𝟙 Z) φ₁)
    (h₂ : p.IsHomLift (𝟙 Z) φ₂) (h₃ : p.IsHomLift (𝟙 Z) φ₃) :
    p.IsHomLift (𝟙 Z) (φ₁ ≫ φ₂ ≫ φ₃) := by
  simpa using (inferInstance : p.IsHomLift (𝟙 Z ≫ 𝟙 Z ≫ 𝟙 Z) (φ₁ ≫ φ₂ ≫ φ₃))

/-- A diagram chase in an arbitrary category. -/
lemma comp_square_aux {𝒞 : Type*} [Category 𝒞] {a b c d e b' c' e' : 𝒞} (A : a ⟶ b) (r : b ⟶ c)
    (E : c ⟶ d) (Y₂ : d ⟶ e) (Y₂' : c ⟶ c') (E' : c' ⟶ e) (Y₁' : b ⟶ b') (m : b' ⟶ c')
    (Y₁ : a ⟶ e') (A' : e' ⟶ b') (hgm : E ≫ Y₂ = Y₂' ≫ E') (hfac : r ≫ Y₂' = Y₁' ≫ m)
    (hnat : A ≫ Y₁' = Y₁ ≫ A') : A ≫ (r ≫ E) ≫ Y₂ = Y₁ ≫ A' ≫ m ≫ E' := by
  rw [Category.assoc, hgm, ← Category.assoc r, hfac]
  simp only [Category.assoc]
  rw [← Category.assoc A, hnat]
  simp only [Category.assoc]

/-- The inverses of two composable isomorphisms compose to the inverse of their composite. -/
private theorem iso_inv_comp_inv_eq {𝒞 : Type*} [Category 𝒞] {X Y Z : 𝒞} {α : X ≅ Y} {β : Y ≅ Z}
    {γ : X ≅ Z} (h : α.hom ≫ β.hom = γ.hom) : β.inv ≫ α.inv = γ.inv :=
  congrArg Iso.inv (Iso.ext (α := α ≪≫ β) (β := γ) h)

namespace ChartAction

variable {𝒮 : Type*} [Category 𝒮] {𝒳₀ : Type*} [Category 𝒳₀] {p : 𝒳₀ ⥤ 𝒮} [p.IsFibered]
  {U W : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R) {f : W ⟶ U} (hf : R.arrows f)

/-- **The gluing isomorphisms of a descent datum are natural.** -/
lemma iso_inv_pullbackFiberMap {Z Z' : 𝒮} {a b : Z ⟶ W} (heq : a ≫ f = b ≫ f) (k : Z' ⟶ Z)
    {a' b' : Z' ⟶ W} (ha : k ≫ a = a') (hb : k ≫ b = b') :
    Fiber.fiberInclusion.map (D.iso hf hf a' b'
        (by rw [← ha, ← hb, Category.assoc, Category.assoc, heq])).inv ≫
      pullbackFiberMap p (D.obj f hf) (Over.homMk k ha : Over.mk a' ⟶ Over.mk a) =
    pullbackFiberMap p (D.obj f hf) (Over.homMk k hb : Over.mk b' ⟶ Over.mk b) ≫
      Fiber.fiberInclusion.map (D.iso hf hf a b heq).inv := by
  subst ha hb
  have hmap : ∀ c : Z ⟶ W, pullbackFiberMap p (D.obj f hf)
      (Over.homMk k rfl : Over.mk (k ≫ c) ⟶ Over.mk c) =
      Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj f hf) c k).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p (D.obj f hf) c).2 k := by
    intro c
    have : p.IsHomLift k (pullbackFiberMap p (D.obj f hf)
        (Over.homMk k rfl : Over.mk (k ≫ c) ⟶ Over.mk c)) :=
      pullbackFiberMap_isHomLift p (D.obj f hf)
        (Over.homMk k rfl : Over.mk (k ≫ c) ⟶ Over.mk c)
    refine IsStronglyCartesian.ext p c (IsPreFibered.pullbackMap (D.obj f hf).2 c) k ?_
    refine (pullbackFiberMap_fac p (D.obj f hf)
      (Over.homMk k rfl : Over.mk (k ≫ c) ⟶ Over.mk c)).trans ?_
    rw [Category.assoc, pullbackFiberCompIso, pullbackFiberCompIso'_inv_fac]
    rfl
  have hinv := iso_inv_comp_inv_eq
    (α := (pullbackFiberCompIso (D.obj f hf) a k).symm)
    (β := pullbackFiberIso (D.iso hf hf a b heq) k ≪≫ pullbackFiberCompIso (D.obj f hf) b k)
    (D.iso_pullback hf hf a b heq k)
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc] at hinv
  rw [hmap, hmap, ← hinv]
  simp only [Functor.map_comp, Category.assoc, pullbackFiberIso_inv]
  rw [← Category.assoc (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj f hf) a k).hom),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    pullbackFiberHom_fac]

section Action

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  [𝒳.val.p.IsFibered] {U W P T : BigFppfOver B S hS} {R : Sieve U}
  (D : SieveDescentDatum 𝒳.val.p R) {f : W ⟶ U} (hf : R.arrows f)
  {g : Over P ⥤ 𝒳.val.obj} (hg : g ⋙ 𝒳.val.p = Over.forget P) (pr₁ : T ⟶ W) (pr₂ : T ⟶ P)

/-- The slice point of the object of `D` at `f`, read on `𝒮/T` through `pr₁`. -/
noncomputable abbrev chartFst : Over T ⥤ 𝒳.val.obj :=
  Over.map pr₁ ⋙ pullbackSliceFunctor 𝒳.val.p (D.obj f hf)

/-- The presheaf the chart represents: pairs `(ψ : Z ⟶ T, m : D f|_{ψ ≫ pr₁} ⟶ g (ψ ≫ pr₂))`. -/
noncomputable abbrev chartPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  slicePairIsom 𝒳 T (overMap_comp_eq_forget 𝒳 (pullbackSliceFunctor_comp 𝒳.val.p (D.obj f hf)) pr₁)
    (overMap_comp_eq_forget 𝒳 hg pr₂)

/-- The vertical morphisms at `ψ` of the presheaf of the chart. -/
abbrev ChartVert {Z : BigFppfOver B S hS} (ψ : Z ⟶ T) : Type u :=
  VertHom 𝒳.val.p (Over.forget T) (chartFst 𝒳 D hf pr₁) (Over.map pr₂ ⋙ g) (Over.mk ψ)

include hg in
/-- **The twist of a vertical morphism by the gluing isomorphism of `D`.** -/
noncomputable def twist {Z : BigFppfOver B S hS} {ψ t : Z ⟶ T} (h₁ : ψ ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f)
    (h₂ : ψ ≫ pr₂ = t ≫ pr₂) (m : ChartVert 𝒳 D hf (g := g) pr₁ pr₂ ψ) :
    ChartVert 𝒳 D hf (g := g) pr₁ pr₂ t :=
  ⟨Fiber.fiberInclusion.map (D.iso hf hf (ψ ≫ pr₁) (t ≫ pr₁)
      (by simpa only [Category.assoc] using h₁)).inv ≫ m.1 ≫
      g.map (eqToHom (show (Over.map pr₂).obj (Over.mk ψ) = (Over.map pr₂).obj (Over.mk t) from
        congrArg Over.mk h₂)),
    isHomLift_id_comp₃ (Z := Z) _ _ _
      (inferInstance : 𝒳.val.p.IsHomLift (𝟙 Z) (Fiber.fiberInclusion.map (D.iso hf hf (ψ ≫ pr₁)
        (t ≫ pr₁) (by simpa only [Category.assoc] using h₁)).inv)) m.2
      (isHomLift_map_eqToHom 𝒳 hg (congrArg Over.mk h₂))⟩

/-- The underlying morphism of `twist` is the inverse of the gluing isomorphism of `D`, then `m`,
then `g` applied to the identification of `ψ ≫ pr₂` with `t ≫ pr₂`. -/
lemma twist_val {Z : BigFppfOver B S hS} {ψ t : Z ⟶ T} (h₁ : ψ ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f)
    (h₂ : ψ ≫ pr₂ = t ≫ pr₂) (m : ChartVert 𝒳 D hf (g := g) pr₁ pr₂ ψ) :
    (twist 𝒳 D hf hg pr₁ pr₂ h₁ h₂ m).1 =
      Fiber.fiberInclusion.map (D.iso hf hf (ψ ≫ pr₁) (t ≫ pr₁)
        (by simpa only [Category.assoc] using h₁)).inv ≫ m.1 ≫
        g.map (eqToHom (show (Over.map pr₂).obj (Over.mk ψ) = (Over.map pr₂).obj (Over.mk t) from
          congrArg Over.mk h₂)) :=
  rfl

/-- Twisting twice is twisting once. -/
lemma twist_twist {Z : BigFppfOver B S hS} {ψ t t' : Z ⟶ T} (h₁ : ψ ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f)
    (h₂ : ψ ≫ pr₂ = t ≫ pr₂) (h₁' : t ≫ pr₁ ≫ f = t' ≫ pr₁ ≫ f) (h₂' : t ≫ pr₂ = t' ≫ pr₂)
    (m : ChartVert 𝒳 D hf (g := g) pr₁ pr₂ ψ) :
    twist 𝒳 D hf hg pr₁ pr₂ h₁' h₂' (twist 𝒳 D hf hg pr₁ pr₂ h₁ h₂ m) =
      twist 𝒳 D hf hg pr₁ pr₂ (h₁.trans h₁') (h₂.trans h₂') m := by
  refine VertHom.ext ?_
  rw [twist_val, twist_val, twist_val]
  simp only [Category.assoc]
  have hc' := iso_inv_comp_inv_eq (D.cocycle hf hf hf (ψ ≫ pr₁) (t ≫ pr₁) (t' ≫ pr₁)
    (by simpa only [Category.assoc] using h₁) (by simpa only [Category.assoc] using h₁')
    (by simpa only [Category.assoc] using h₁.trans h₁'))
  rw [← Category.assoc (Fiber.fiberInclusion.map _), ← Functor.map_comp, hc']
  congr 1
  refine (Category.assoc _ _ _).trans (congrArg _ ((g.map_comp _ _).symm.trans ?_))
  rw [eqToHom_trans]

/-- Twisting along the identity does nothing. -/
lemma twist_self {Z : BigFppfOver B S hS} {ψ : Z ⟶ T} (h₁ : ψ ≫ pr₁ ≫ f = ψ ≫ pr₁ ≫ f)
    (h₂ : ψ ≫ pr₂ = ψ ≫ pr₂) (m : ChartVert 𝒳 D hf (g := g) pr₁ pr₂ ψ) :
    twist 𝒳 D hf hg pr₁ pr₂ h₁ h₂ m = m := by
  refine VertHom.ext ?_
  rw [twist_val]
  have hinv : (D.iso hf hf (ψ ≫ pr₁) (ψ ≫ pr₁) (by simp only [Category.assoc])).inv =
      𝟙 _ := Iso.inv_ext (by simp)
  rw [hinv, CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_refl,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- Twisting commutes with restriction. -/
lemma restrict_twist {Z Z' : BigFppfOver B S hS} (k : Z' ⟶ Z) {ψ t : Z ⟶ T}
    (h₁ : ψ ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : ψ ≫ pr₂ = t ≫ pr₂)
    (m : ChartVert 𝒳 D hf (g := g) pr₁ pr₂ ψ) :
    VertHom.restrict 𝒳.isFiberedInGroupoids
        (overMap_comp_eq_forget 𝒳 (pullbackSliceFunctor_comp 𝒳.val.p (D.obj f hf)) pr₁)
        (overMap_comp_eq_forget 𝒳 hg pr₂)
        (Over.homMk k rfl : Over.mk (k ≫ t) ⟶ Over.mk t) (twist 𝒳 D hf hg pr₁ pr₂ h₁ h₂ m) =
      twist 𝒳 D hf hg pr₁ pr₂ (ψ := k ≫ ψ) (t := k ≫ t)
        (by simp only [Category.assoc, h₁]) (by simp only [Category.assoc, h₂])
        (VertHom.restrict 𝒳.isFiberedInGroupoids
          (overMap_comp_eq_forget 𝒳 (pullbackSliceFunctor_comp 𝒳.val.p (D.obj f hf)) pr₁)
          (overMap_comp_eq_forget 𝒳 hg pr₂)
          (Over.homMk k rfl : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) m) := by
  refine (VertHom.restrict_uniq _ _ _ _ _ _ ?_).symm
  rw [twist_val, twist_val]
  have hgm : g.map (eqToHom (show (Over.map pr₂).obj (Over.mk (k ≫ ψ)) =
        (Over.map pr₂).obj (Over.mk (k ≫ t)) from congrArg Over.mk
          (show (k ≫ ψ) ≫ pr₂ = (k ≫ t) ≫ pr₂ by rw [Category.assoc, Category.assoc, h₂]))) ≫
      (Over.map pr₂ ⋙ g).map (Over.homMk k rfl : Over.mk (k ≫ t) ⟶ Over.mk t) =
      (Over.map pr₂ ⋙ g).map (Over.homMk k rfl : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) ≫
        g.map (eqToHom (show (Over.map pr₂).obj (Over.mk ψ) = (Over.map pr₂).obj (Over.mk t) from
          congrArg Over.mk h₂)) := by
    refine (g.map_comp _ _).symm.trans ((congrArg g.map ?_).trans (g.map_comp _ _))
    refine Over.OverMorphism.ext ?_
    simp
  have hfac := VertHom.restrict_fac 𝒳.isFiberedInGroupoids
    (overMap_comp_eq_forget 𝒳 (pullbackSliceFunctor_comp 𝒳.val.p (D.obj f hf)) pr₁)
    (overMap_comp_eq_forget 𝒳 hg pr₂) (Over.homMk k rfl : Over.mk (k ≫ ψ) ⟶ Over.mk ψ) m
  have hnat := iso_inv_pullbackFiberMap D hf (a := ψ ≫ pr₁) (b := t ≫ pr₁)
    (by simpa only [Category.assoc] using h₁) k (a' := (k ≫ ψ) ≫ pr₁) (b' := (k ≫ t) ≫ pr₁)
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  exact (Category.assoc _ _ _).trans (comp_square_aux _ _ _ _ _ _ _ _ _ _ hgm hfac hnat)

/-- A section of the chart presheaf moved along `t`. -/
noncomputable def moveSection {Z : BigFppfOver B S hS}
    (s : (chartPresheaf 𝒳 D hf hg pr₁ pr₂).obj (op Z)) (t : Z ⟶ T)
    (h₁ : s.1 ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : s.1 ≫ pr₂ = t ≫ pr₂) :
    (chartPresheaf 𝒳 D hf hg pr₁ pr₂).obj (op Z) :=
  ⟨t, twist 𝒳 D hf hg pr₁ pr₂ h₁ h₂ s.2⟩

/-- The section moved along `t` has first component `t`. -/
lemma moveSection_fst {Z : BigFppfOver B S hS}
    (s : (chartPresheaf 𝒳 D hf hg pr₁ pr₂).obj (op Z)) (t : Z ⟶ T)
    (h₁ : s.1 ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : s.1 ≫ pr₂ = t ≫ pr₂) :
    (moveSection 𝒳 D hf hg pr₁ pr₂ s t h₁ h₂).1 = t :=
  rfl

/-- Moving a section along `t` and then along `t'` is moving it along `t'`. -/
lemma moveSection_moveSection {Z : BigFppfOver B S hS}
    (s : (chartPresheaf 𝒳 D hf hg pr₁ pr₂).obj (op Z)) (t t' : Z ⟶ T)
    (h₁ : s.1 ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : s.1 ≫ pr₂ = t ≫ pr₂)
    (h₁' : t ≫ pr₁ ≫ f = t' ≫ pr₁ ≫ f) (h₂' : t ≫ pr₂ = t' ≫ pr₂) :
    moveSection 𝒳 D hf hg pr₁ pr₂ (moveSection 𝒳 D hf hg pr₁ pr₂ s t h₁ h₂) t' h₁' h₂' =
      moveSection 𝒳 D hf hg pr₁ pr₂ s t' (h₁.trans h₁') (h₂.trans h₂') :=
  Sigma.ext rfl (heq_of_eq (twist_twist 𝒳 D hf hg pr₁ pr₂ h₁ h₂ h₁' h₂' s.2))

/-- Restriction along `k` sends the section moved along `t` to the restricted section moved
along `k ≫ t`. -/
lemma map_moveSection {Z Z' : BigFppfOver B S hS} (k : Z' ⟶ Z)
    (s : (chartPresheaf 𝒳 D hf hg pr₁ pr₂).obj (op Z)) (t : Z ⟶ T)
    (h₁ : s.1 ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : s.1 ≫ pr₂ = t ≫ pr₂) :
    (chartPresheaf 𝒳 D hf hg pr₁ pr₂).map k.op (moveSection 𝒳 D hf hg pr₁ pr₂ s t h₁ h₂) =
      moveSection 𝒳 D hf hg pr₁ pr₂ ((chartPresheaf 𝒳 D hf hg pr₁ pr₂).map k.op s) (k ≫ t)
        (by simp only [OverShriek.presheaf_map_apply_fst, Quiver.Hom.unop_op, Category.assoc, h₁])
        (by simp only [OverShriek.presheaf_map_apply_fst, Quiver.Hom.unop_op, Category.assoc,
          h₂]) := by
  obtain ⟨ψ, m⟩ := s
  exact Sigma.ext rfl (heq_of_eq (restrict_twist 𝒳 D hf hg pr₁ pr₂ k h₁ h₂ m))

/-- Equal sections moved along the same `t` are equal. -/
lemma moveSection_congr {Z : BigFppfOver B S hS}
    {s s' : (chartPresheaf 𝒳 D hf hg pr₁ pr₂).obj (op Z)} (hs : s = s') (t : Z ⟶ T)
    (h₁ : s.1 ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : s.1 ≫ pr₂ = t ≫ pr₂)
    (h₁' : s'.1 ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂' : s'.1 ≫ pr₂ = t ≫ pr₂) :
    moveSection 𝒳 D hf hg pr₁ pr₂ s t h₁ h₂ = moveSection 𝒳 D hf hg pr₁ pr₂ s' t h₁' h₂' := by
  subst hs
  rfl

/-- Moving a section along its own first component does nothing. -/
lemma moveSection_self {Z : BigFppfOver B S hS}
    (s : (chartPresheaf 𝒳 D hf hg pr₁ pr₂).obj (op Z)) (t : Z ⟶ T) (ht : s.1 = t)
    (h₁ : s.1 ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : s.1 ≫ pr₂ = t ≫ pr₂) :
    moveSection 𝒳 D hf hg pr₁ pr₂ s t h₁ h₂ = s := by
  obtain ⟨ψ, m⟩ := s
  subst ht
  exact Sigma.ext rfl (heq_of_eq (twist_self 𝒳 D hf hg pr₁ pr₂ h₁ h₂ m))

section Chart

variable {Q : BigFppfOver B S hS} {π : Q ⟶ T}
  (e : yoneda.obj Q ≅ chartPresheaf 𝒳 D hf hg pr₁ pr₂)
  (he : e.hom ≫ OverShriek.presheafToYoneda _ = yoneda.map π)

include he in
/-- The section of the chart presheaf corresponding to `q : Z ⟶ Q` has first component
`q ≫ π`. -/
lemma fst_hom_app {Z : BigFppfOver B S hS} (q : Z ⟶ Q) : (e.hom.app (op Z) q).1 = q ≫ π := by
  have := congrArg (fun α => α.app (op Z) q) he
  simp only [yoneda_obj_obj, NatTrans.comp_app, comp_apply, yoneda_map_app, TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk] at this
  exact this

include he in
/-- **The action on the chart.** A point `q` of `Q` moved along `t : Z ⟶ T` agreeing with
`q ≫ π` over `U × P`. -/
noncomputable def act {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (t : Z ⟶ T)
    (h₁ : q ≫ π ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : q ≫ π ≫ pr₂ = t ≫ pr₂) : Z ⟶ Q :=
  e.inv.app (op Z) (moveSection 𝒳 D hf hg pr₁ pr₂ (e.hom.app (op Z) q) t
    (by rwa [fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he q, Category.assoc])
    (by rwa [fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he q, Category.assoc]))

/-- The section of the chart presheaf corresponding to `act q t` is the section corresponding
to `q` moved along `t`. -/
lemma hom_app_act {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (t : Z ⟶ T)
    (h₁ : q ≫ π ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : q ≫ π ≫ pr₂ = t ≫ pr₂) :
    e.hom.app (op Z) (act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂) =
      moveSection 𝒳 D hf hg pr₁ pr₂ (e.hom.app (op Z) q) t
        (by rw [fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he q, Category.assoc]; exact h₁)
        (by rw [fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he q, Category.assoc]; exact h₂) := by
  simp [act]

/-- The moved point lies over `t`. -/
lemma act_comp_π {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (t : Z ⟶ T)
    (h₁ : q ≫ π ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : q ≫ π ≫ pr₂ = t ≫ pr₂) :
    act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂ ≫ π = t := by
  rw [← fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he, hom_app_act]
  rfl

/-- Moving a point along its own image does nothing. -/
lemma act_self {Z : BigFppfOver B S hS} (q : Z ⟶ Q)
    (h₁ : q ≫ π ≫ pr₁ ≫ f = (q ≫ π) ≫ pr₁ ≫ f) (h₂ : q ≫ π ≫ pr₂ = (q ≫ π) ≫ pr₂) :
    act 𝒳 D hf hg pr₁ pr₂ e he q (q ≫ π) h₁ h₂ = q := by
  have hinj : Function.Injective (e.hom.app (op Z)) := fun a b hab => by
    simpa using congrArg (e.inv.app (op Z)) hab
  refine hinj ?_
  rw [hom_app_act]
  exact moveSection_self 𝒳 D hf hg pr₁ pr₂ _ _ (fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he q) _ _

/-- **The action is associative.** -/
lemma act_act {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (t t' : Z ⟶ T)
    (h₁ : q ≫ π ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : q ≫ π ≫ pr₂ = t ≫ pr₂)
    (h₁' : act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂ ≫ π ≫ pr₁ ≫ f = t' ≫ pr₁ ≫ f)
    (h₂' : act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂ ≫ π ≫ pr₂ = t' ≫ pr₂)
    (h₁'' : q ≫ π ≫ pr₁ ≫ f = t' ≫ pr₁ ≫ f) (h₂'' : q ≫ π ≫ pr₂ = t' ≫ pr₂) :
    act 𝒳 D hf hg pr₁ pr₂ e he (act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂) t' h₁' h₂' =
      act 𝒳 D hf hg pr₁ pr₂ e he q t' h₁'' h₂'' := by
  have hπ := act_comp_π 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂
  have k₁ : t ≫ pr₁ ≫ f = t' ≫ pr₁ ≫ f := by rwa [← hπ, Category.assoc]
  have k₂ : t ≫ pr₂ = t' ≫ pr₂ := by rwa [← hπ, Category.assoc]
  refine congrArg (e.inv.app (op Z)) ((moveSection_congr 𝒳 D hf hg pr₁ pr₂
    (hom_app_act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂) t' _ _ k₁ k₂).trans ?_)
  exact moveSection_moveSection 𝒳 D hf hg pr₁ pr₂ _ t t' _ _ k₁ k₂

/-- **The action is natural.** -/
lemma comp_act {Z Z' : BigFppfOver B S hS} (k : Z' ⟶ Z) (q : Z ⟶ Q) (t : Z ⟶ T)
    (h₁ : q ≫ π ≫ pr₁ ≫ f = t ≫ pr₁ ≫ f) (h₂ : q ≫ π ≫ pr₂ = t ≫ pr₂)
    (h₁' : (k ≫ q) ≫ π ≫ pr₁ ≫ f = (k ≫ t) ≫ pr₁ ≫ f)
    (h₂' : (k ≫ q) ≫ π ≫ pr₂ = (k ≫ t) ≫ pr₂) :
    k ≫ act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂ =
      act 𝒳 D hf hg pr₁ pr₂ e he (k ≫ q) (k ≫ t) h₁' h₂' := by
  have hnat : k ≫ act 𝒳 D hf hg pr₁ pr₂ e he q t h₁ h₂ =
      e.inv.app (op Z') ((chartPresheaf 𝒳 D hf hg pr₁ pr₂).map k.op
        (moveSection 𝒳 D hf hg pr₁ pr₂ (e.hom.app (op Z) q) t
          (by rwa [fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he q, Category.assoc])
          (by rwa [fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he q, Category.assoc]))) := by
    rw [NatTrans.naturality_apply]
    rfl
  rw [hnat, map_moveSection]
  refine congrArg (e.inv.app (op Z')) (moveSection_congr 𝒳 D hf hg pr₁ pr₂ ?_ _ _ _ _ _)
  rw [← NatTrans.naturality_apply]
  rfl

end Chart

end Action

end ChartAction

end AlgebraicGeometry.Stack

end
