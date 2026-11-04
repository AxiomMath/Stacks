module

public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Cancel
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Presentation

/-!
# Morphisms presented by morphisms of `𝒜`

With the notation of `StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Presentation`, a
morphism `u : ev e ⟶ ev e'` is *good* when, after padding both sides by objects `X`, `Y` of `𝒜`,
it coheres with an isomorphism `pad e ⊗ X ≅ pad e' ⊗ Y` and a morphism `base e ⊗ X ⟶ base e' ⊗ Y`.
Good morphisms contain the identities and the images of the morphisms of the free monoidal
category, the images under `Ψ` of the morphisms of `𝒜` and the braidings, and they are closed
under composition and whiskering.

## Main definitions

* `CategoryTheory.InvertingObject.Expr.Good`: good morphisms.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.InvertingObject.Expr

open MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [BraidedCategory 𝒜] {L : 𝒜}
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] [BraidedCategory 𝒟]
  {Ψ : 𝒜 ⥤ 𝒟} [Ψ.Monoidal] {𝕋 : 𝒟} {ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟}

omit [BraidedCategory 𝒜] in
/-- Coherence is preserved by replacing `u`, `φ` and `c` with equal morphisms. -/
theorem Coh.congr {e e' : Expr 𝒜} {u u' : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    {φ φ' : (pad L).obj e ≅ (pad L).obj e'} {c c' : (base).obj e ⟶ (base).obj e'}
    (h : Coh L Ψ 𝕋 ω u φ c) (hu : u = u') (hφ : φ = φ') (hc : c = c') :
    Coh L Ψ 𝕋 ω u' φ' c' := by
  subst hu hφ hc
  exact h

omit [BraidedCategory 𝒜] in
/-- The inverse of a cohering triple of isomorphisms coheres. -/
theorem Coh.inv {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ≅ (ev Ψ 𝕋).obj e'}
    {φ : (pad L).obj e ≅ (pad L).obj e'} {c : (base).obj e ≅ (base).obj e'}
    (h : Coh L Ψ 𝕋 ω u.hom φ c.hom) : Coh L Ψ 𝕋 ω u.inv φ.symm c.inv := by
  unfold Coh at *
  rw [← cancel_epi (u.hom ⊗ₘ Ψ.map φ.hom), ← Category.assoc, tensorHom_comp_tensorHom,
    Iso.symm_hom, ← Functor.map_comp, u.hom_inv_id, φ.hom_inv_id, Functor.map_id,
    tensorHom_id, id_whiskerRight, Category.id_comp, reassoc_of% h, ← Functor.map_comp,
    c.hom_inv_id, Functor.map_id, Category.comp_id]

omit [BraidedCategory 𝒜] in
/-- Paddings by isomorphic objects cohere. -/
theorem coh_pd {X Y : 𝒜} (ξ : X ≅ Y) :
    Coh L Ψ 𝕋 ω (e := pd X) (e' := pd Y) (𝟙 (𝟙_ 𝒟)) ξ ξ.hom := by
  unfold Coh presIso
  show (𝟙 (𝟙_ 𝒟) ⊗ₘ Ψ.map ξ.hom) ≫ (λ_ (Ψ.obj Y)).hom = (λ_ (Ψ.obj X)).hom ≫ Ψ.map ξ.hom
  rw [id_tensorHom, leftUnitor_naturality]

variable (L Ψ 𝕋 ω)

/-- The presentation of `e` with an extra padding `X`:
`ev e ⊗ Ψ(pad e ⊗ X) ≅ Ψ(base e ⊗ X)`. -/
def θ (e : Expr 𝒜) (X : 𝒜) :
    (ev Ψ 𝕋).obj e ⊗ Ψ.obj ((pad L).obj e ⊗ X) ≅ Ψ.obj ((base).obj e ⊗ X) :=
  whiskerLeftIso _ (μIso Ψ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso (presIso L Ψ 𝕋 ω e) _ ≪≫ μIso Ψ _ _

omit [BraidedCategory 𝒜] in
/-- The underlying morphism of `θ e X`, written out. -/
theorem θ_hom (e : Expr 𝒜) (X : 𝒜) : (θ L Ψ 𝕋 ω e X).hom =
    (ev Ψ 𝕋).obj e ◁ δ Ψ _ _ ≫ (α_ _ _ _).inv ≫ (presIso L Ψ 𝕋 ω e).hom ▷ Ψ.obj X ≫
      μ Ψ _ _ :=
  rfl

/-- `u : ev e ⟶ ev e'` is presented by `c : base e ⊗ X ⟶ base e' ⊗ Y` along the paddings `X`, `Y`
and `φ : pad e ⊗ X ≅ pad e' ⊗ Y`. -/
def RelX {e e' : Expr 𝒜} (u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e') (X Y : 𝒜)
    (φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y) (c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y) :
    Prop :=
  u ▷ Ψ.obj ((pad L).obj e ⊗ X) ≫ (ev Ψ 𝕋).obj e' ◁ Ψ.map φ.hom ≫ (θ L Ψ 𝕋 ω e' Y).hom =
    (θ L Ψ 𝕋 ω e X).hom ≫ Ψ.map c

variable {L Ψ 𝕋 ω}

omit [BraidedCategory 𝒜] in
/-- The identity of `ev e` is presented by the identity, with equal paddings. -/
theorem relX_id (e : Expr 𝒜) (X : 𝒜) :
    RelX L Ψ 𝕋 ω (𝟙 ((ev Ψ 𝕋).obj e)) X X (Iso.refl _) (𝟙 _) := by
  simp [RelX]

omit [BraidedCategory 𝒜] in
/-- Composites of presented morphisms are presented by the composites of the presenting data. -/
theorem RelX.comp {e e' e'' : Expr 𝒜} {f : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    {h : (ev Ψ 𝕋).obj e' ⟶ (ev Ψ 𝕋).obj e''} {X Y Z : 𝒜}
    {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y} {ψ : (pad L).obj e' ⊗ Y ≅ (pad L).obj e'' ⊗ Z}
    {c₁ : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y} {c₂ : (base).obj e' ⊗ Y ⟶ (base).obj e'' ⊗ Z}
    (hf : RelX L Ψ 𝕋 ω f X Y φ c₁) (hh : RelX L Ψ 𝕋 ω h Y Z ψ c₂) :
    RelX L Ψ 𝕋 ω (f ≫ h) X Z (φ ≪≫ ψ) (c₁ ≫ c₂) := by
  unfold RelX at *
  simp only [Iso.trans_hom, Functor.map_comp, whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  rw [← whisker_exchange_assoc, hh, reassoc_of% hf]

omit [BraidedCategory 𝒜] in
/-- Naturality of `θ` in the extra padding. -/
@[reassoc]
theorem θ_naturality (e : Expr 𝒜) {X X' : 𝒜} (τ : X ⟶ X') :
    (θ L Ψ 𝕋 ω e X).hom ≫ Ψ.map ((base).obj e ◁ τ) =
      (ev Ψ 𝕋).obj e ◁ Ψ.map ((pad L).obj e ◁ τ) ≫ (θ L Ψ 𝕋 ω e X').hom := by
  simp only [θ_hom, Category.assoc, ← μ_natural_right, ← whiskerLeft_comp_assoc,
    ← δ_natural_right]
  simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]

omit [BraidedCategory 𝒜] in
/-- Changing the target padding of a presented morphism along an isomorphism. -/
theorem RelX.changeRight {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'} {X Y Y' : 𝒜}
    {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y} {c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y}
    (h : RelX L Ψ 𝕋 ω u X Y φ c) (ψ : Y ≅ Y') :
    RelX L Ψ 𝕋 ω u X Y' (φ ≪≫ whiskerLeftIso _ ψ) (c ≫ (base).obj e' ◁ ψ.hom) := by
  unfold RelX at *
  rw [Functor.map_comp, ← reassoc_of% h, θ_naturality]
  simp

omit [BraidedCategory 𝒜] in
/-- Changing the target padding of a presented morphism along a morphism. -/
theorem RelX.changeRightHom {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'} {X Y Y' : 𝒜}
    {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y} {c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y}
    (h : RelX L Ψ 𝕋 ω u X Y φ c) (χ : Y ⟶ Y') (φ' : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y')
    (hφ : φ.hom ≫ (pad L).obj e' ◁ χ = φ'.hom) :
    RelX L Ψ 𝕋 ω u X Y' φ' (c ≫ (base).obj e' ◁ χ) := by
  unfold RelX at *
  rw [Functor.map_comp, ← reassoc_of% h, θ_naturality, ← hφ, Functor.map_comp, whiskerLeft_comp,
    Category.assoc]

omit [BraidedCategory 𝒜] in
/-- Two morphisms presented by the same data agree after whiskering by the image of the
padding. -/
theorem RelX.whiskerRight_eq {e e' : Expr 𝒜} {u u' : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    {X Y : 𝒜} {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y}
    {c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y} (h : RelX L Ψ 𝕋 ω u X Y φ c)
    (h' : RelX L Ψ 𝕋 ω u' X Y φ c) :
    u ▷ Ψ.obj ((pad L).obj e ⊗ X) = u' ▷ Ψ.obj ((pad L).obj e ⊗ X) :=
  (cancel_mono ((ev Ψ 𝕋).obj e' ◁ Ψ.map φ.hom ≫ (θ L Ψ 𝕋 ω e' Y).hom)).1 (h.trans h'.symm)

omit [BraidedCategory 𝒜] in
/-- Changing the source padding of a presented morphism along an isomorphism. -/
theorem RelX.changeLeft {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'} {X X' Y : 𝒜}
    {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y} {c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y}
    (h : RelX L Ψ 𝕋 ω u X Y φ c) (ψ : X' ≅ X) :
    RelX L Ψ 𝕋 ω u X' Y (whiskerLeftIso _ ψ ≪≫ φ) ((base).obj e ◁ ψ.hom ≫ c) := by
  unfold RelX at *
  rw [Functor.map_comp, θ_naturality_assoc, ← h]
  simp only [Iso.trans_hom, whiskerLeftIso_hom, Functor.map_comp, whiskerLeft_comp,
    Category.assoc]
  rw [whisker_exchange_assoc]

/-- Whiskering the second factor of a tensor by `u` and then `f ▷ B` is reassociated. -/
private theorem whiskerRight_whiskerLeft_whiskerRight_associator_inv {C : Type*} [Category C]
    [MonoidalCategory C] {P Q A A' : C} (u : P ⟶ Q) (f : A ⟶ A') (B : C) :
    u ▷ (A ⊗ B) ≫ Q ◁ f ▷ B ≫ (α_ Q A' B).inv = (α_ P A B).inv ≫ (u ▷ A ≫ Q ◁ f) ▷ B := by
  simp only [comp_whiskerRight]
  monoidal

omit [BraidedCategory 𝒜] in
/-- A cohering triple is presented, with any common padding. -/
theorem Coh.relX {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    {φ : (pad L).obj e ≅ (pad L).obj e'} {c : (base).obj e ⟶ (base).obj e'}
    (h : Coh L Ψ 𝕋 ω u φ c) (X : 𝒜) :
    RelX L Ψ 𝕋 ω u X X (whiskerRightIso φ X) (c ▷ X) := by
  unfold RelX
  simp only [θ_hom, whiskerRightIso_hom]
  rw [← whiskerLeft_comp_assoc, ← δ_natural_left, whiskerLeft_comp_assoc,
    ← whisker_exchange_assoc]
  have key := whiskerRight_whiskerLeft_whiskerRight_associator_inv u (Ψ.map φ.hom) (Ψ.obj X)
  rw [← tensorHom_def] at key
  have hX := congrArg (· ▷ Ψ.obj X) h
  simp only [comp_whiskerRight] at hX
  rw [reassoc_of% key, reassoc_of% hX, μ_natural_left]
  simp only [Category.assoc]

omit [BraidedCategory 𝒜] in
/-- `θ` with the padding `X ⊗ D` is `θ` with the padding `X`, tensored with `Ψ(D)`. -/
theorem θ_tensor_right (e : Expr 𝒜) (X D : 𝒜) :
    (θ L Ψ 𝕋 ω e (X ⊗ D)).hom =
      (ev Ψ 𝕋).obj e ◁ Ψ.map (α_ ((pad L).obj e) X D).inv ≫
        (ev Ψ 𝕋).obj e ◁ δ Ψ _ _ ≫ (α_ _ _ _).inv ≫ (θ L Ψ 𝕋 ω e X).hom ▷ Ψ.obj D ≫
          μ Ψ _ _ ≫ Ψ.map (α_ ((base).obj e) X D).hom := by
  have hδ : Ψ.map (α_ ((pad L).obj e) X D).inv ≫ δ Ψ ((pad L).obj e ⊗ X) D ≫
      δ Ψ ((pad L).obj e) X ▷ Ψ.obj D =
      δ Ψ ((pad L).obj e) (X ⊗ D) ≫ Ψ.obj ((pad L).obj e) ◁ δ Ψ X D ≫ (α_ _ _ _).inv := by
    rw [map_associator_inv]
    simp
  have hμ : μ Ψ ((base).obj e) X ▷ Ψ.obj D ≫ μ Ψ ((base).obj e ⊗ X) D ≫
      Ψ.map (α_ ((base).obj e) X D).hom =
      (α_ _ _ _).hom ≫ Ψ.obj ((base).obj e) ◁ μ Ψ X D ≫ μ Ψ ((base).obj e) (X ⊗ D) :=
    associativity Ψ _ _ _
  simp only [θ_hom, comp_whiskerRight, Category.assoc]
  rw [hμ, ← associator_inv_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp_assoc, Category.assoc, hδ]
  have hx : (presIso L Ψ 𝕋 ω e).hom ▷ Ψ.obj (X ⊗ D) =
      ((ev Ψ 𝕋).obj e ⊗ Ψ.obj ((pad L).obj e)) ◁ δ Ψ X D ≫
        (presIso L Ψ 𝕋 ω e).hom ▷ (Ψ.obj X ⊗ Ψ.obj D) ≫ Ψ.obj ((base).obj e) ◁ μ Ψ X D := by
    rw [whisker_exchange_assoc, ← whiskerLeft_comp, δ_μ, whiskerLeft_id, Category.comp_id]
  rw [hx]
  monoidal

omit [BraidedCategory 𝒜] in
/-- An extra padding `D` on both sides of a presented morphism. -/
theorem RelX.padRight {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'} {X Y : 𝒜}
    {φ : (Expr.pad L).obj e ⊗ X ≅ (Expr.pad L).obj e' ⊗ Y}
    {c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y}
    (h : RelX L Ψ 𝕋 ω u X Y φ c) (D : 𝒜) :
    RelX L Ψ 𝕋 ω u (X ⊗ D) (Y ⊗ D) ((α_ _ _ _).symm ≪≫ whiskerRightIso φ D ≪≫ α_ _ _ _)
      ((α_ _ _ _).inv ≫ c ▷ D ≫ (α_ _ _ _).hom) := by
  unfold RelX at *
  rw [θ_tensor_right, θ_tensor_right]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Functor.map_comp,
    whiskerLeft_comp, Category.assoc, Iso.map_hom_inv_id_assoc]
  have e₁ : (ev Ψ 𝕋).obj e' ◁ Ψ.map (α_ ((Expr.pad L).obj e') Y D).hom ≫
      (ev Ψ 𝕋).obj e' ◁ Ψ.map (α_ ((Expr.pad L).obj e') Y D).inv ≫
      (ev Ψ 𝕋).obj e' ◁ δ Ψ ((Expr.pad L).obj e' ⊗ Y) D =
      (ev Ψ 𝕋).obj e' ◁ δ Ψ ((Expr.pad L).obj e' ⊗ Y) D := by
    rw [← whiskerLeft_comp_assoc, Iso.map_hom_inv_id, whiskerLeft_id, Category.id_comp]
  have e₂ : (ev Ψ 𝕋).obj e' ◁ Ψ.map (φ.hom ▷ D) ≫
      (ev Ψ 𝕋).obj e' ◁ δ Ψ ((Expr.pad L).obj e' ⊗ Y) D =
      (ev Ψ 𝕋).obj e' ◁ δ Ψ ((Expr.pad L).obj e ⊗ X) D ≫
        (ev Ψ 𝕋).obj e' ◁ (Ψ.map φ.hom ▷ Ψ.obj D) := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, δ_natural_left]
  have key := whiskerRight_whiskerLeft_whiskerRight_associator_inv u (Ψ.map φ.hom) (Ψ.obj D)
  rw [reassoc_of% e₁, reassoc_of% e₂, ← whisker_exchange_assoc, ← whisker_exchange_assoc,
    reassoc_of% key,
    ← comp_whiskerRight_assoc, Category.assoc, h, comp_whiskerRight_assoc, μ_natural_left_assoc]

variable (L Ψ 𝕋 ω) in
/-- The presentation of `e ⊗ pd X`, with its source and target written out. -/
def presPad (e : Expr 𝒜) (X : 𝒜) :
    ((ev Ψ 𝕋).obj e ⊗ 𝟙_ 𝒟) ⊗ Ψ.obj ((Expr.pad L).obj e ⊗ X) ≅ Ψ.obj ((base).obj e ⊗ X) :=
  presIso L Ψ 𝕋 ω (e ⊗ pd X)

/-- `θ e X` is the presentation of `e ⊗ pd X`. -/
theorem θ_eq_presPad (e : Expr 𝒜) (X : 𝒜) :
    (θ L Ψ 𝕋 ω e X).hom =
      (ρ_ ((ev Ψ 𝕋).obj e)).inv ▷ Ψ.obj ((Expr.pad L).obj e ⊗ X) ≫
        (presPad L Ψ 𝕋 ω e X).hom := by
  rw [presPad, presIso_tensor_hom, θ_hom]
  show _ = _ ≫ (𝟙 _ ⊗ₘ (Ψ.map (𝟙 _) ≫ δ Ψ _ _)) ≫ tensorδ _ _ _ _ ≫
    ((presIso L Ψ 𝕋 ω e).hom ⊗ₘ (λ_ (Ψ.obj X)).hom) ≫ μ Ψ _ _ ≫ Ψ.map (𝟙 _)
  simp only [Functor.map_id, Category.id_comp, Category.comp_id, tensorHom_def,
    Category.assoc]
  have hstr : (ρ_ ((ev Ψ 𝕋).obj e)).inv ▷ (Ψ.obj ((Expr.pad L).obj e) ⊗ Ψ.obj X) ≫
      tensorδ ((ev Ψ 𝕋).obj e) (Ψ.obj ((Expr.pad L).obj e)) (𝟙_ 𝒟) (Ψ.obj X) ≫
      ((ev Ψ 𝕋).obj e ⊗ Ψ.obj ((Expr.pad L).obj e)) ◁ (λ_ (Ψ.obj X)).hom =
      (α_ _ _ _).inv := by
    simp only [tensorδ, braiding_inv_tensorUnit_right]
    monoidal
  rw [id_whiskerRight, Category.id_comp,
    ← whisker_exchange_assoc (presIso L Ψ 𝕋 ω e).hom (λ_ (Ψ.obj X)).hom,
    ← whisker_exchange_assoc, reassoc_of% hstr]

/-- A presented morphism is a cohering triple on the padded expressions. -/
theorem relX_iff_coh {e e' : Expr 𝒜} (u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e') (X Y : 𝒜)
    (φ : (Expr.pad L).obj e ⊗ X ≅ (Expr.pad L).obj e' ⊗ Y)
    (c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y) :
    RelX L Ψ 𝕋 ω u X Y φ c ↔
      Coh L Ψ 𝕋 ω (e := e ⊗ pd X) (e' := e' ⊗ pd Y) (u ▷ 𝟙_ 𝒟) φ c := by
  show _ ↔ ((u ▷ 𝟙_ 𝒟) ⊗ₘ Ψ.map φ.hom) ≫ (presPad L Ψ 𝕋 ω e' Y).hom =
    (presPad L Ψ 𝕋 ω e X).hom ≫ Ψ.map c
  unfold RelX
  rw [θ_eq_presPad, θ_eq_presPad, Category.assoc]
  have hn : u ▷ Ψ.obj ((Expr.pad L).obj e ⊗ X) ≫ (ev Ψ 𝕋).obj e' ◁ Ψ.map φ.hom ≫
      (ρ_ ((ev Ψ 𝕋).obj e')).inv ▷ Ψ.obj ((Expr.pad L).obj e' ⊗ Y) =
      (ρ_ ((ev Ψ 𝕋).obj e)).inv ▷ Ψ.obj ((Expr.pad L).obj e ⊗ X) ≫ ((u ▷ 𝟙_ 𝒟) ⊗ₘ Ψ.map φ.hom) := by
    rw [tensorHom_def, ← comp_whiskerRight_assoc, ← rightUnitor_inv_naturality,
      comp_whiskerRight_assoc, ← whisker_exchange]
  rw [reassoc_of% hn]
  constructor
  · intro h
    rwa [cancel_epi] at h
  · intro h
    rw [h]

/-- Good morphisms: morphisms presented along some paddings with invertible images. -/
def Good {e e' : Expr 𝒜} (u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e') : Prop :=
  ∃ (X Y : 𝒜) (φ : (Expr.pad L).obj e ⊗ X ≅ (Expr.pad L).obj e' ⊗ Y)
    (c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y), IsInvertible (Ψ.obj X) ∧
      IsInvertible (Ψ.obj Y) ∧ RelX L Ψ 𝕋 ω u X Y φ c

omit [BraidedCategory 𝒜] in
/-- Identities are good. -/
theorem good_id (e : Expr 𝒜) : Good (L := L) (ω := ω) (𝟙 ((ev Ψ 𝕋).obj e)) :=
  ⟨𝟙_ 𝒜, 𝟙_ 𝒜, _, _, isInvertible_map_tensorUnit Ψ, isInvertible_map_tensorUnit Ψ, relX_id e _⟩

omit [BraidedCategory 𝒜] in
/-- The first component of a cohering triple is good. -/
theorem Coh.good {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    {φ : (Expr.pad L).obj e ≅ (Expr.pad L).obj e'} {c : (base).obj e ⟶ (base).obj e'}
    (h : Coh L Ψ 𝕋 ω u φ c) : Good (L := L) (ω := ω) u :=
  ⟨𝟙_ 𝒜, 𝟙_ 𝒜, _, _, isInvertible_map_tensorUnit Ψ, isInvertible_map_tensorUnit Ψ, h.relX _⟩

/-- A composite of good morphisms is good. -/
theorem Good.comp {e e' e'' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    {u' : (ev Ψ 𝕋).obj e' ⟶ (ev Ψ 𝕋).obj e''} (h : Good (L := L) (ω := ω) u)
    (h' : Good (L := L) (ω := ω) u') : Good (L := L) (ω := ω) (u ≫ u') := by
  obtain ⟨X, Y, φ, c, hX, hY, h⟩ := h
  obtain ⟨Y', Z, φ', c', hY', hZ, h'⟩ := h'
  exact ⟨_, _, _, _, IsInvertible.map_tensor Ψ hX hY', IsInvertible.map_tensor Ψ hZ hY,
    ((h.padRight Y').changeRight (β_ Y Y')).comp (h'.padRight Y)⟩

/-- Whiskering a good morphism on the left keeps it good. -/
theorem Good.whiskerLeft (e₂ : Expr 𝒜) {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    (h : Good (L := L) (ω := ω) u) :
    Good (L := L) (ω := ω) (e := e₂ ⊗ e) (e' := e₂ ⊗ e')
      (δ (ev Ψ 𝕋) e₂ e ≫ (ev Ψ 𝕋).obj e₂ ◁ u ≫ μ (ev Ψ 𝕋) e₂ e') := by
  obtain ⟨X, Y, φ, c, hX, hY, h⟩ := h
  have h₁ := (((coh_map (L := L) (Ψ := Ψ) (𝕋 := 𝕋) (ω := ω) (α_ e₂ e (pd X)).hom).comp
    ((coh_id e₂).tensor ((relX_iff_coh u X Y φ c).1 h))).comp
    (coh_map (α_ e₂ e' (pd Y)).inv))
  refine ⟨X, Y, _, _, hX, hY, (relX_iff_coh _ X Y _ _).2 (h₁.congr ?_ rfl rfl)⟩
  rw [map_associator, map_associator_inv]
  simp only [Category.assoc, μ_δ_assoc]
  show 𝟙 _ ≫ δ (ev Ψ 𝕋) e₂ e ▷ 𝟙_ 𝒟 ≫ (α_ ((ev Ψ 𝕋).obj e₂) ((ev Ψ 𝕋).obj e) (𝟙_ 𝒟)).hom ≫
      (ev Ψ 𝕋).obj e₂ ◁ 𝟙 _ ≫ (𝟙 ((ev Ψ 𝕋).obj e₂) ⊗ₘ u ▷ 𝟙_ 𝒟) ≫ (ev Ψ 𝕋).obj e₂ ◁ 𝟙 _ ≫
        (α_ ((ev Ψ 𝕋).obj e₂) ((ev Ψ 𝕋).obj e') (𝟙_ 𝒟)).inv ≫ μ (ev Ψ 𝕋) e₂ e' ▷ 𝟙_ 𝒟 ≫ 𝟙 _ =
    (δ (ev Ψ 𝕋) e₂ e ≫ (ev Ψ 𝕋).obj e₂ ◁ u ≫ μ (ev Ψ 𝕋) e₂ e') ▷ 𝟙_ 𝒟
  rw [Category.id_comp, Category.comp_id, whiskerLeft_id, Category.id_comp, whiskerLeft_id,
    Category.id_comp, id_tensorHom, comp_whiskerRight, comp_whiskerRight, whisker_assoc]
  simp only [Category.assoc]

omit [BraidedCategory 𝒜] in
/-- A morphism equal to a good morphism is good. -/
theorem Good.congr {e e' : Expr 𝒜} {u u' : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    (h : Good (L := L) (ω := ω) u) (hu : u = u') : Good (L := L) (ω := ω) u' :=
  hu ▸ h

/-- The images of the morphisms of the free monoidal category are good. -/
theorem good_map {e e' : Expr 𝒜} (w : e ⟶ e') : Good (L := L) (ω := ω) ((ev Ψ 𝕋).map w) :=
  (coh_map w).good

/-- The images under `Ψ` of the morphisms of `𝒜` are good. -/
theorem good_atom {A B : 𝒜} (g : A ⟶ B) :
    Good (L := L) (ω := ω) (e := atom A) (e' := atom B) (Ψ.map g) :=
  (coh_atom g).good

/-- Whiskering on the left, with the structure maps of `ev` written as identities. -/
theorem Good.whiskerLeft' (e₂ : Expr 𝒜) {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    (h : Good (L := L) (ω := ω) u) :
    Good (L := L) (ω := ω) (e := e₂ ⊗ e) (e' := e₂ ⊗ e') ((ev Ψ 𝕋).obj e₂ ◁ u) :=
  (h.whiskerLeft e₂).congr (by
    show 𝟙 _ ≫ (ev Ψ 𝕋).obj e₂ ◁ u ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
    rfl)

/-- Conjugating a whiskering by the symmetry. -/
private theorem braiding_whiskerLeft_braiding {C : Type*} [Category C] [MonoidalCategory C]
    [SymmetricCategory C] {A B : C} (u : A ⟶ B) (D : C) :
    ((β_ A D).hom ≫ D ◁ u) ≫ (β_ D B).hom = u ▷ D := by
  rw [Category.assoc, BraidedCategory.braiding_naturality_right,
    SymmetricCategory.symmetry_assoc]

section Symmetric

variable {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] [SymmetricCategory 𝒟]
  {Ψ : 𝒜 ⥤ 𝒟} [Ψ.Braided] {𝕋 : 𝒟} {ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟}

/-- The braidings are good. -/
theorem good_braiding (e₁ e₂ : Expr 𝒜) :
    Good (L := L) (ω := ω) (e := e₁ ⊗ e₂) (e' := e₂ ⊗ e₁)
      (β_ ((ev Ψ 𝕋).obj e₁) ((ev Ψ 𝕋).obj e₂)).hom :=
  (coh_braiding e₁ e₂).good.congr (by
    show 𝟙 _ ≫ (β_ ((ev Ψ 𝕋).obj e₁) ((ev Ψ 𝕋).obj e₂)).hom ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id])

/-- Whiskering on the right keeps a morphism good. -/
theorem Good.whiskerRight {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    (h : Good (L := L) (ω := ω) u) (e₂ : Expr 𝒜) :
    Good (L := L) (ω := ω) (e := e ⊗ e₂) (e' := e' ⊗ e₂) (u ▷ (ev Ψ 𝕋).obj e₂) :=
  (((good_braiding e e₂).comp (h.whiskerLeft' e₂)).comp (good_braiding e₂ e')).congr
    (braiding_whiskerLeft_braiding u _)

end Symmetric

end CategoryTheory.InvertingObject.Expr
