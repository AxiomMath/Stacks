module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Free.Coherence
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import StacksFrontier.CategoryTheory.Monoidal.FreeMonoidalNatIso

/-!
# Formal tensor expressions and their presentations

Let `Ψ : 𝒜 ⥤ 𝒟` be a braided functor into a symmetric monoidal category, `L` an object of `𝒜`
and `𝕋` an object of `𝒟` with `ω : Ψ(L) ⊗ 𝕋 ≅ 𝟙`. A *formal expression* is an object of the
free monoidal category on the leaves `atom A` (`A ∈ 𝒜`), `inv` (an inverse of `L`) and `pd X`
(`X ∈ 𝒜`, a padding). It evaluates to `ev e ∈ 𝒟` by `atom A ↦ Ψ(A)`, `inv ↦ 𝕋`, `pd X ↦ 𝟙`; its
*padding* `pad e ∈ 𝒜` replaces `atom A ↦ 𝟙`, `inv ↦ L`, `pd X ↦ X`, and its *base* `base e ∈ 𝒜`
replaces `atom A ↦ A`, `inv ↦ 𝟙`, `pd X ↦ X`. Pairing each `inv` with its `L` gives the
*presentation*, a monoidal natural isomorphism

  `pres e : ev e ⊗ Ψ(pad e) ≅ Ψ(base e)`.

A morphism `u : ev e ⟶ ev e'` *coheres* with an isomorphism `φ : pad e ≅ pad e'` and a morphism
`c : base e ⟶ base e'` (`Coh`) when `(u ⊗ Ψ(φ)) ≫ pres e' = pres e ≫ Ψ(c)`. Cohering triples are
closed under composition and tensor product and contain the images of the morphisms of the free
monoidal category, the images under `Ψ` of the morphisms of `𝒜`, and the braidings.

## Main definitions

* `CategoryTheory.InvertingObject.Gen`, `CategoryTheory.InvertingObject.Expr`: formal tensor
  expressions.
* `CategoryTheory.InvertingObject.Expr.pres`: the presentation.
* `CategoryTheory.InvertingObject.Expr.Coh`: a morphism cohering with a morphism of `𝒜`.

## Main results

* `CategoryTheory.MonoidalCategory.tensorμ_comp_tensorHom_braiding`: in a symmetric monoidal
  category, the tensor product functor is braided.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MonoidalCategory BraidedCategory

/-- In a symmetric monoidal category the tensor product functor is braided: the middle-four
interchange followed by the two braidings is the braiding followed by the middle-four
interchange. -/
@[reassoc]
theorem MonoidalCategory.tensorμ_comp_tensorHom_braiding {C : Type*} [Category C]
    [MonoidalCategory C] [SymmetricCategory C] (A₁ B₁ A₂ B₂ : C) :
    tensorμ A₁ B₁ A₂ B₂ ≫ ((β_ A₁ A₂).hom ⊗ₘ (β_ B₁ B₂).hom) =
      (β_ (A₁ ⊗ B₁) (A₂ ⊗ B₂)).hom ≫ tensorμ A₂ B₂ A₁ B₁ := by
  have hs : (β_ A₁ B₂).hom ▷ B₁ ≫ (β_ B₂ A₁).hom ▷ B₁ = 𝟙 _ := by
    rw [← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight]
  calc tensorμ A₁ B₁ A₂ B₂ ≫ ((β_ A₁ A₂).hom ⊗ₘ (β_ B₁ B₂).hom)
      = 𝟙 _ ⊗≫ A₁ ◁ (β_ B₁ A₂).hom ▷ B₂ ⊗≫
          ((β_ A₁ A₂).hom ▷ (B₁ ⊗ B₂) ≫ (A₂ ⊗ A₁) ◁ (β_ B₁ B₂).hom) ⊗≫ 𝟙 _ := by
        simp only [tensorμ, tensorHom_def]
        monoidal
    _ = 𝟙 _ ⊗≫ A₁ ◁ (β_ B₁ A₂).hom ▷ B₂ ⊗≫ (β_ A₁ A₂).hom ▷ B₁ ▷ B₂ ⊗≫
          A₂ ◁ A₁ ◁ (β_ B₁ B₂).hom ⊗≫
          A₂ ◁ ((β_ A₁ B₂).hom ▷ B₁ ≫ (β_ B₂ A₁).hom ▷ B₁) ⊗≫ 𝟙 _ := by
        rw [hs]
        monoidal
    _ = (β_ (A₁ ⊗ B₁) (A₂ ⊗ B₂)).hom ≫ tensorμ A₂ B₂ A₁ B₁ := by
        simp only [tensorμ, braiding_tensor_left_hom, braiding_tensor_right_hom]
        monoidal

/-- `tensorδ` is natural. -/
@[reassoc]
theorem MonoidalCategory.tensorδ_natural {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : U₁ ⟶ V₁) (g₂ : U₂ ⟶ V₂) :
    ((f₁ ⊗ₘ g₁) ⊗ₘ f₂ ⊗ₘ g₂) ≫ tensorδ Y₁ Y₂ V₁ V₂ =
      tensorδ X₁ X₂ U₁ U₂ ≫ ((f₁ ⊗ₘ f₂) ⊗ₘ g₁ ⊗ₘ g₂) := by
  have : IsIso (tensorμ X₁ X₂ U₁ U₂) := ⟨⟨tensorδ _ _ _ _, by simp, by simp⟩⟩
  rw [← cancel_epi (tensorμ X₁ X₂ U₁ U₂), ← tensorμ_natural_assoc, tensorμ_tensorδ,
    tensorμ_tensorδ_assoc, Category.comp_id]

/-- The `tensorδ` form of `CategoryTheory.MonoidalCategory.tensorμ_comp_tensorHom_braiding`. -/
@[reassoc]
theorem MonoidalCategory.tensorHom_braiding_comp_tensorδ {C : Type*} [Category C]
    [MonoidalCategory C] [SymmetricCategory C] (A₁ B₁ A₂ B₂ : C) :
    ((β_ A₁ A₂).hom ⊗ₘ (β_ B₁ B₂).hom) ≫ tensorδ A₂ B₂ A₁ B₁ =
      tensorδ A₁ B₁ A₂ B₂ ≫ (β_ (A₁ ⊗ B₁) (A₂ ⊗ B₂)).hom := by
  have : IsIso (tensorμ A₁ B₁ A₂ B₂) := ⟨⟨tensorδ _ _ _ _, by simp, by simp⟩⟩
  rw [← cancel_epi (tensorμ A₁ B₁ A₂ B₂), tensorμ_comp_tensorHom_braiding_assoc,
    tensorμ_tensorδ_assoc]
  simp

namespace InvertingObject

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

/-- The leaves of formal tensor expressions over `𝒜`. -/
inductive Gen (𝒜 : Type u₁) : Type u₁
  /-- An object of `𝒜`. -/
  | atom (A : 𝒜) : Gen 𝒜
  /-- The symbol for an inverse of `L`. -/
  | inv : Gen 𝒜
  /-- A padding by an object of `𝒜`. -/
  | pd (X : 𝒜) : Gen 𝒜

/-- Formal tensor expressions: the free monoidal category on the leaves `Gen 𝒜`. -/
abbrev Expr (𝒜 : Type u₁) : Type u₁ := FreeMonoidalCategory (Gen 𝒜)

namespace Expr

section Functors

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] (L : 𝒜)

/-- The leaf `A`. -/
abbrev atom (A : 𝒜) : Expr 𝒜 := FreeMonoidalCategory.of (Gen.atom A)

/-- The leaf standing for an inverse. -/
abbrev inv : Expr 𝒜 := FreeMonoidalCategory.of Gen.inv

/-- The padding leaf. -/
abbrev pd (X : 𝒜) : Expr 𝒜 := FreeMonoidalCategory.of (Gen.pd X)

/-- The padding on the leaves. -/
def padLeaf : Gen 𝒜 → 𝒜
  | .atom _ => 𝟙_ 𝒜
  | .inv => L
  | .pd X => X

/-- The base on the leaves. -/
def baseLeaf : Gen 𝒜 → 𝒜
  | .atom A => A
  | .inv => 𝟙_ 𝒜
  | .pd X => X

/-- The padding: `atom A ↦ 𝟙`, `inv ↦ L`, `pd X ↦ X`. -/
abbrev pad : Expr 𝒜 ⥤ 𝒜 := FreeMonoidalCategory.project (padLeaf L)

/-- The base: `atom A ↦ A`, `inv ↦ 𝟙`, `pd X ↦ X`. -/
abbrev base : Expr 𝒜 ⥤ 𝒜 := FreeMonoidalCategory.project baseLeaf

variable {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] (Ψ : 𝒜 ⥤ 𝒟) (𝕋 : 𝒟)

/-- The evaluation on the leaves. -/
def evLeaf : Gen 𝒜 → 𝒟
  | .atom A => Ψ.obj A
  | .inv => 𝕋
  | .pd _ => 𝟙_ 𝒟

/-- The evaluation in `𝒟`: `atom A ↦ Ψ(A)`, `inv ↦ 𝕋`, `pd X ↦ 𝟙`. -/
abbrev ev : Expr 𝒜 ⥤ 𝒟 := FreeMonoidalCategory.project (evLeaf Ψ 𝕋)

end Functors

section Presentation

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [BraidedCategory 𝒜] (L : 𝒜)
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] [BraidedCategory 𝒟]
  (Ψ : 𝒜 ⥤ 𝒟) [Ψ.Monoidal] (𝕋 : 𝒟) (ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟)

/-- The functor `e ↦ ev e ⊗ Ψ(pad e)`. -/
abbrev padded : Expr 𝒜 ⥤ 𝒟 := ((ev Ψ 𝕋).prod' (pad L ⋙ Ψ)) ⋙ tensor 𝒟

omit [BraidedCategory 𝒜] in
/-- The comonoidal structure map of `padded` is the tensor product of those of `ev` and of
`pad ⋙ Ψ`, followed by the interchange `tensorδ`. -/
theorem padded_δ (e e' : Expr 𝒜) :
    δ (padded L Ψ 𝕋) e e' =
      ((ev Ψ 𝕋).obj e ⊗ (ev Ψ 𝕋).obj e') ◁ δ Ψ ((pad L).obj e) ((pad L).obj e') ≫
        tensorδ _ _ _ _ := by
  show ((δ ((ev Ψ 𝕋).prod' (pad L ⋙ Ψ)) e e').1 ⊗ₘ (δ ((ev Ψ 𝕋).prod' (pad L ⋙ Ψ)) e e').2) ≫
    tensorδ _ _ _ _ = _
  rw [Functor.prod'_δ_fst, Functor.prod'_δ_snd]
  simp

/-- The presentation on the leaves. -/
def presLeaf : ∀ g : Gen 𝒜,
    (padded L Ψ 𝕋).obj (FreeMonoidalCategory.of g) ≅ (base ⋙ Ψ).obj (FreeMonoidalCategory.of g)
  | .atom A => μIso Ψ A (𝟙_ 𝒜) ≪≫ Ψ.mapIso (ρ_ A)
  | .inv => β_ 𝕋 (Ψ.obj L) ≪≫ ω ≪≫ εIso Ψ
  | .pd X => λ_ (Ψ.obj X)

/-- **The presentation** `ev e ⊗ Ψ(pad e) ≅ Ψ(base e)`, the monoidal natural isomorphism
extending the pairing `ω` of each inverse leaf with its `L`. -/
def pres : padded L Ψ 𝕋 ≅ base ⋙ Ψ :=
  FreeMonoidalCategory.liftNatIso _ _ (presLeaf L Ψ 𝕋 ω)

/-- The presentation of a single expression, with its source and target written out. -/
def presIso (e : Expr 𝒜) :
    (ev Ψ 𝕋).obj e ⊗ Ψ.obj ((pad L).obj e) ≅ Ψ.obj ((base).obj e) :=
  (pres L Ψ 𝕋 ω).app e

omit [BraidedCategory 𝒜] in
/-- Naturality of `presIso` in the expression. -/
theorem presIso_naturality {e e' : Expr 𝒜} (w : e ⟶ e') :
    ((ev Ψ 𝕋).map w ⊗ₘ Ψ.map ((pad L).map w)) ≫ (presIso L Ψ 𝕋 ω e').hom =
      (presIso L Ψ 𝕋 ω e).hom ≫ Ψ.map ((base).map w) :=
  (pres L Ψ 𝕋 ω).hom.naturality w

omit [BraidedCategory 𝒜] in
/-- The presentation of `e ⊗ e'` in terms of the presentations of `e` and of `e'`. -/
theorem presIso_tensor_hom (e e' : Expr 𝒜) :
    (presIso L Ψ 𝕋 ω (e ⊗ e')).hom =
      (δ (ev Ψ 𝕋) e e' ⊗ₘ (Ψ.map (δ (pad L) e e') ≫ δ Ψ ((pad L).obj e) ((pad L).obj e'))) ≫
        tensorδ _ _ _ _ ≫ ((presIso L Ψ 𝕋 ω e).hom ⊗ₘ (presIso L Ψ 𝕋 ω e').hom) ≫
          μ Ψ ((base).obj e) ((base).obj e') ≫ Ψ.map (μ (base) e e') := by
  rw [presIso, pres, FreeMonoidalCategory.liftNatIso_app_tensor]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, tensorIso_hom,
    Functor.OplaxMonoidal.comp_δ, Functor.LaxMonoidal.comp_μ, tensor_δ, Category.assoc]
  congr 1
  show ((δ ((ev Ψ 𝕋).prod' (pad L ⋙ Ψ)) e e').1 ⊗ₘ
    (δ ((ev Ψ 𝕋).prod' (pad L ⋙ Ψ)) e e').2) = _
  rw [Functor.prod'_δ_fst, Functor.prod'_δ_snd, Functor.OplaxMonoidal.comp_δ]

/-- `u : ev e ⟶ ev e'` *coheres* with `φ : pad e ≅ pad e'` and `c : base e ⟶ base e'`. -/
def Coh {e e' : Expr 𝒜} (u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e')
    (φ : (pad L).obj e ≅ (pad L).obj e') (c : (base).obj e ⟶ (base).obj e') : Prop :=
  (u ⊗ₘ Ψ.map φ.hom) ≫ (presIso L Ψ 𝕋 ω e').hom = (presIso L Ψ 𝕋 ω e).hom ≫ Ψ.map c

variable {L Ψ 𝕋 ω}

omit [BraidedCategory 𝒜] in
/-- The identities cohere. -/
theorem coh_id (e : Expr 𝒜) : Coh L Ψ 𝕋 ω (𝟙 ((ev Ψ 𝕋).obj e)) (Iso.refl _) (𝟙 _) := by
  simp [Coh]

omit [BraidedCategory 𝒜] in
/-- Coherence is preserved by composition. -/
theorem Coh.comp {e e' e'' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'}
    {u' : (ev Ψ 𝕋).obj e' ⟶ (ev Ψ 𝕋).obj e''} {φ : (pad L).obj e ≅ (pad L).obj e'}
    {φ' : (pad L).obj e' ≅ (pad L).obj e''} {c : (base).obj e ⟶ (base).obj e'}
    {c' : (base).obj e' ⟶ (base).obj e''} (h : Coh L Ψ 𝕋 ω u φ c)
    (h' : Coh L Ψ 𝕋 ω u' φ' c') : Coh L Ψ 𝕋 ω (u ≫ u') (φ ≪≫ φ') (c ≫ c') := by
  unfold Coh at *
  rw [Iso.trans_hom, Functor.map_comp, ← tensorHom_comp_tensorHom, Category.assoc, h',
    reassoc_of% h, Functor.map_comp]

omit [BraidedCategory 𝒜] in
/-- Coherence is preserved by the tensor product. -/
theorem Coh.tensor {e₁ e₁' e₂ e₂' : Expr 𝒜} {u₁ : (ev Ψ 𝕋).obj e₁ ⟶ (ev Ψ 𝕋).obj e₁'}
    {u₂ : (ev Ψ 𝕋).obj e₂ ⟶ (ev Ψ 𝕋).obj e₂'} {φ₁ : (pad L).obj e₁ ≅ (pad L).obj e₁'}
    {φ₂ : (pad L).obj e₂ ≅ (pad L).obj e₂'} {c₁ : (base).obj e₁ ⟶ (base).obj e₁'}
    {c₂ : (base).obj e₂ ⟶ (base).obj e₂'} (h₁ : Coh L Ψ 𝕋 ω u₁ φ₁ c₁)
    (h₂ : Coh L Ψ 𝕋 ω u₂ φ₂ c₂) :
    Coh L Ψ 𝕋 ω (e := e₁ ⊗ e₂) (e' := e₁' ⊗ e₂')
      (δ (ev Ψ 𝕋) e₁ e₂ ≫ (u₁ ⊗ₘ u₂) ≫ μ (ev Ψ 𝕋) e₁' e₂')
      ((μIso (pad L) e₁ e₂).symm ≪≫ tensorIso φ₁ φ₂ ≪≫ μIso (pad L) e₁' e₂')
      (δ (base) e₁ e₂ ≫ (c₁ ⊗ₘ c₂) ≫ μ (base) e₁' e₂') := by
  unfold Coh at *
  simp only [presIso_tensor_hom, Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, tensorIso_hom,
    Functor.map_comp, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, μ_δ, Category.comp_id, Functor.Monoidal.map_μ_δ_assoc]
  rw [← δ_natural]
  have key : (δ (ev Ψ 𝕋) e₁ e₂ ≫ (u₁ ⊗ₘ u₂) ⊗ₘ Ψ.map (δ (pad L) e₁ e₂) ≫
      δ Ψ ((pad L).obj e₁) ((pad L).obj e₂) ≫ (Ψ.map φ₁.hom ⊗ₘ Ψ.map φ₂.hom)) =
      (δ (ev Ψ 𝕋) e₁ e₂ ⊗ₘ Ψ.map (δ (pad L) e₁ e₂) ≫ δ Ψ ((pad L).obj e₁) ((pad L).obj e₂)) ≫
        ((u₁ ⊗ₘ u₂) ⊗ₘ (Ψ.map φ₁.hom ⊗ₘ Ψ.map φ₂.hom)) := by
    rw [tensorHom_comp_tensorHom, Category.assoc]
  rw [key, Category.assoc, tensorδ_natural_assoc, tensorHom_comp_tensorHom_assoc, h₁, h₂,
    ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc]

omit [BraidedCategory 𝒜] in
/-- The images of the morphisms of the free monoidal category cohere. -/
theorem coh_map {e e' : Expr 𝒜} (w : e ⟶ e') :
    Coh L Ψ 𝕋 ω ((ev Ψ 𝕋).map w) (asIso ((pad L).map w)) ((base).map w) :=
  presIso_naturality L Ψ 𝕋 ω w

omit [BraidedCategory 𝒜] in
/-- The images under `Ψ` of the morphisms of `𝒜` cohere. -/
theorem coh_atom {A B : 𝒜} (g : A ⟶ B) :
    Coh L Ψ 𝕋 ω (e := atom A) (e' := atom B) (Ψ.map g) (Iso.refl _) g := by
  unfold Coh presIso
  show (Ψ.map g ⊗ₘ Ψ.map (𝟙 _)) ≫ (μ Ψ B (𝟙_ 𝒜) ≫ Ψ.map (ρ_ B).hom) =
    (μ Ψ A (𝟙_ 𝒜) ≫ Ψ.map (ρ_ A).hom) ≫ Ψ.map g
  rw [Functor.map_id, MonoidalCategory.tensorHom_id, μ_natural_left_assoc, ← Functor.map_comp,
    rightUnitor_naturality, Functor.map_comp, Category.assoc]

end Presentation

section Braided

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [BraidedCategory 𝒜] {L : 𝒜}
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] [SymmetricCategory 𝒟]
  {Ψ : 𝒜 ⥤ 𝒟} [Ψ.Braided] {𝕋 : 𝒟} {ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟}

/-- The braidings cohere. -/
theorem coh_braiding (e₁ e₂ : Expr 𝒜) :
    Coh L Ψ 𝕋 ω (e := e₁ ⊗ e₂) (e' := e₂ ⊗ e₁)
      (δ (ev Ψ 𝕋) e₁ e₂ ≫ (β_ ((ev Ψ 𝕋).obj e₁) ((ev Ψ 𝕋).obj e₂)).hom ≫ μ (ev Ψ 𝕋) e₂ e₁)
      ((μIso (pad L) e₁ e₂).symm ≪≫ β_ ((pad L).obj e₁) ((pad L).obj e₂) ≪≫ μIso (pad L) e₂ e₁)
      (δ (base) e₁ e₂ ≫ (β_ ((base).obj e₁) ((base).obj e₂)).hom ≫ μ (base) e₂ e₁) := by
  unfold Coh
  simp only [presIso_tensor_hom, Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom,
    Functor.map_comp, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, μ_δ, Category.comp_id, Functor.Monoidal.map_μ_δ_assoc]
  have hb : Ψ.map (β_ ((pad L).obj e₁) ((pad L).obj e₂)).hom ≫ δ Ψ ((pad L).obj e₂) ((pad L).obj e₁)
      = δ Ψ ((pad L).obj e₁) ((pad L).obj e₂) ≫
        (β_ (Ψ.obj ((pad L).obj e₁)) (Ψ.obj ((pad L).obj e₂))).hom := by
    rw [Functor.map_braiding]
    simp
  rw [hb, ← Category.assoc (Ψ.map (δ (pad L) e₁ e₂)), ← tensorHom_comp_tensorHom_assoc,
    tensorHom_braiding_comp_tensorδ_assoc, ← braiding_naturality_assoc,
    ← Functor.LaxBraided.braided_assoc]

end Braided

end Expr

end InvertingObject

end CategoryTheory
