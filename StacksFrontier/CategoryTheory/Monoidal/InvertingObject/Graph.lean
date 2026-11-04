module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Transport
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Good

/-!
# The symmetric monoidal category of good morphisms

With the notation of `StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Good`, the formal
expressions together with the good morphisms between their evaluations form a symmetric
monoidal category `Graph L Ψ 𝕋 ω`, with a faithful braided functor `Graph.incl` to `𝒟` given by
the evaluation.

## Main definitions

* `CategoryTheory.InvertingObject.Graph`: the category of formal expressions and good
  morphisms.
* `CategoryTheory.InvertingObject.Graph.incl`: its faithful braided functor to `𝒟`.
* `CategoryTheory.InvertingObject.Graph.ι`: the braided monoidal functor `A ↦ atom A` from `𝒜`.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.InvertingObject

open MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open Expr

/-- The category of formal expressions whose padding has an invertible image, with good
morphisms between their evaluations. -/
structure Graph {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] (L : 𝒜)
    {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] (Ψ : 𝒜 ⥤ 𝒟) (𝕋 : 𝒟)
    (ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟) : Type u₁ where
  /-- The object given by a formal expression. -/
  mk ::
  /-- The formal expression underlying an object. -/
  expr : Expr 𝒜
  /-- The image of the padding is invertible. -/
  isInvertible : IsInvertible (Ψ.obj ((pad L).obj expr))

section Atoms

/-- A coherence computation behind `Expr.coh_μ`. -/
@[reassoc]
theorem tensorδ_whiskerLeft_rightUnitor {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (A B Y : C) (e : Y ⟶ 𝟙_ C) :
    (𝟙 (A ⊗ B) ⊗ₘ (e ▷ Y ≫ (λ_ Y).hom)) ≫ (A ⊗ B) ◁ e ≫ (ρ_ (A ⊗ B)).hom =
      tensorδ A Y B Y ≫ ((A ◁ e ≫ (ρ_ A).hom) ⊗ₘ (B ◁ e ≫ (ρ_ B).hom)) := by
  have h₁ : tensorδ A Y B Y ≫ ((A ◁ e ≫ (ρ_ A).hom) ⊗ₘ (B ◁ e ≫ (ρ_ B).hom)) =
      ((𝟙 A ⊗ₘ 𝟙 B) ⊗ₘ (e ⊗ₘ e)) ≫ tensorδ A (𝟙_ C) B (𝟙_ C) ≫ ((ρ_ A).hom ⊗ₘ (ρ_ B).hom) := by
    rw [← tensorHom_comp_tensorHom, ← id_tensorHom, ← id_tensorHom, ← tensorδ_natural_assoc]
  have h₂ : e ▷ Y ≫ (λ_ Y).hom ≫ e = (e ⊗ₘ e) ≫ (λ_ (𝟙_ C)).hom := by
    rw [← leftUnitor_naturality, tensorHom_def_assoc]
  have h₃ : (A ⊗ B) ◁ (λ_ (𝟙_ C)).hom ≫ (ρ_ (A ⊗ B)).hom =
      tensorδ A (𝟙_ C) B (𝟙_ C) ≫ ((ρ_ A).hom ⊗ₘ (ρ_ B).hom) := by
    simp only [tensorδ, braiding_inv_tensorUnit_left, tensorHom_def]
    monoidal
  rw [h₁, id_tensorHom_id, id_tensorHom, ← whiskerLeft_comp_assoc, Category.assoc, h₂,
    whiskerLeft_comp_assoc, h₃, id_tensorHom]

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [BraidedCategory 𝒜] {L : 𝒜}
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] [BraidedCategory 𝒟]
  {Ψ : 𝒜 ⥤ 𝒟} [Ψ.Monoidal] {𝕋 : 𝒟} {ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟}

/-- The tensorator of `Ψ` coheres. -/
theorem Expr.coh_μ (A B : 𝒜) :
    Coh L Ψ 𝕋 ω (e := atom A ⊗ atom B) (e' := atom (A ⊗ B)) (μ Ψ A B) (λ_ (𝟙_ 𝒜)) (𝟙 _) := by
  unfold Coh
  rw [presIso_tensor_hom]
  show (μ Ψ A B ⊗ₘ Ψ.map (λ_ (𝟙_ 𝒜)).hom) ≫ (μ Ψ (A ⊗ B) (𝟙_ 𝒜) ≫ Ψ.map (ρ_ (A ⊗ B)).hom) =
    ((𝟙 _ ⊗ₘ (Ψ.map (𝟙 _) ≫ δ Ψ (𝟙_ 𝒜) (𝟙_ 𝒜))) ≫ tensorδ _ _ _ _ ≫
      ((μ Ψ A (𝟙_ 𝒜) ≫ Ψ.map (ρ_ A).hom) ⊗ₘ (μ Ψ B (𝟙_ 𝒜) ≫ Ψ.map (ρ_ B).hom)) ≫
        μ Ψ A B ≫ Ψ.map (𝟙 _)) ≫ Ψ.map (𝟙 _)
  simp only [Functor.map_id, Category.id_comp, Category.comp_id, map_rightUnitor,
    map_leftUnitor, μ_δ_assoc]
  have h : (μ Ψ A B ⊗ₘ (η Ψ ▷ Ψ.obj (𝟙_ 𝒜) ≫ (λ_ (Ψ.obj (𝟙_ 𝒜))).hom)) ≫
      Ψ.obj (A ⊗ B) ◁ η Ψ ≫ (ρ_ (Ψ.obj (A ⊗ B))).hom =
      (𝟙 _ ⊗ₘ (η Ψ ▷ Ψ.obj (𝟙_ 𝒜) ≫ (λ_ (Ψ.obj (𝟙_ 𝒜))).hom)) ≫
        (Ψ.obj A ⊗ Ψ.obj B) ◁ η Ψ ≫ (ρ_ (Ψ.obj A ⊗ Ψ.obj B)).hom ≫ μ Ψ A B := by
    rw [← rightUnitor_naturality, id_tensorHom, whisker_exchange_assoc, whisker_exchange_assoc,
      tensorHom_def, Category.assoc]
  rw [← Category.id_comp (μ Ψ A B), ← tensorHom_comp_tensorHom, Category.assoc, Category.id_comp,
    h]
  congr 1
  exact tensorδ_whiskerLeft_rightUnitor_assoc _ _ _ _ _

omit [BraidedCategory 𝒜] in
/-- The unit of `Ψ` coheres. -/
theorem Expr.coh_ε :
    Coh L Ψ 𝕋 ω (e := 𝟙_ (Expr 𝒜)) (e' := atom (𝟙_ 𝒜)) (ε Ψ) (Iso.refl _) (𝟙 _) := by
  unfold Coh presIso pres
  rw [FreeMonoidalCategory.liftNatIso_app, FreeMonoidalCategory.liftNatIso_app,
    FreeMonoidalCategory.liftNatIsoApp_unit]
  show (ε Ψ ⊗ₘ Ψ.map (𝟙 _)) ≫ (μ Ψ (𝟙_ 𝒜) (𝟙_ 𝒜) ≫ Ψ.map (ρ_ (𝟙_ 𝒜)).hom) = _
  simp only [Iso.trans_hom, Iso.symm_hom, εIso_inv, εIso_hom, Functor.OplaxMonoidal.comp_η,
    Functor.LaxMonoidal.comp_ε, tensor_η, tensor_map, Functor.prod'_η_fst, Functor.prod'_η_snd,
    FreeMonoidalCategory.project_η, FreeMonoidalCategory.project_ε, Functor.map_id,
    tensorHom_id, map_rightUnitor, μ_δ_assoc]
  show _ = (((𝟙 _ ⊗ₘ Ψ.map (𝟙 (𝟙_ 𝒜)) ≫ η Ψ) ≫ (λ_ (𝟙_ 𝒟)).hom) ≫ ε Ψ ≫ Ψ.map (𝟙 (𝟙_ 𝒜))) ≫
    Ψ.map (𝟙 (𝟙_ 𝒜))
  simp only [Functor.map_id, Category.id_comp, Category.comp_id, id_tensorHom, unitors_equal]
  rw [← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]

end Atoms

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [BraidedCategory 𝒜] (L : 𝒜)
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] [SymmetricCategory 𝒟]
  (Ψ : 𝒜 ⥤ 𝒟) [Ψ.Braided] (𝕋 : 𝒟) (ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟)

namespace Graph

variable {L Ψ 𝕋 ω}

/-- The morphisms `X ⟶ Y` of `Graph` are the good morphisms between the evaluations of `X` and
`Y`, with the composition of `𝒟`. -/
instance : Category.{v₂} (Graph L Ψ 𝕋 ω) where
  Hom X Y := {u : (ev Ψ 𝕋).obj X.expr ⟶ (ev Ψ 𝕋).obj Y.expr // Good (L := L) (ω := ω) u}
  id _ := ⟨𝟙 _, good_id _⟩
  comp f g := ⟨f.1 ≫ g.1, f.2.comp g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/-- Two morphisms of `Graph` are equal if their underlying morphisms of `𝒟` are equal. -/
@[ext]
theorem hom_ext {X Y : Graph L Ψ 𝕋 ω} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/-- The underlying morphism of an identity of `Graph` is the identity. -/
@[simp] theorem id_val (X : Graph L Ψ 𝕋 ω) : (𝟙 X : X ⟶ X).1 = 𝟙 _ := rfl

/-- The underlying morphism of a composite in `Graph` is the composite of underlying morphisms. -/
@[simp] theorem comp_val {X Y Z : Graph L Ψ 𝕋 ω} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

variable (L Ψ 𝕋 ω) in
/-- The evaluation, as a faithful functor to `𝒟`. -/
def incl : Graph L Ψ 𝕋 ω ⥤ 𝒟 where
  obj X := (ev Ψ 𝕋).obj X.expr
  map f := f.1

/-- `incl` sends an object to the evaluation of its formal expression. -/
@[simp] theorem incl_obj (X : Graph L Ψ 𝕋 ω) : (incl L Ψ 𝕋 ω).obj X = (ev Ψ 𝕋).obj X.expr :=
  rfl

/-- `incl` sends a morphism to its underlying morphism of `𝒟`. -/
@[simp] theorem incl_map {X Y : Graph L Ψ 𝕋 ω} (f : X ⟶ Y) : (incl L Ψ 𝕋 ω).map f = f.1 := rfl

/-- The functor `incl` is faithful. -/
instance : (incl L Ψ 𝕋 ω).Faithful where
  map_injective h := Subtype.ext h

/-- The isomorphism of `Graph` given by an isomorphism of formal expressions. -/
def freeIso {X Y : Graph L Ψ 𝕋 ω} (w : X.expr ≅ Y.expr) : X ≅ Y where
  hom := ⟨(ev Ψ 𝕋).map w.hom, good_map _⟩
  inv := ⟨(ev Ψ 𝕋).map w.inv, good_map _⟩
  hom_inv_id := hom_ext (((ev Ψ 𝕋).map_comp _ _).symm.trans (by
    rw [w.hom_inv_id, Functor.map_id]; rfl))
  inv_hom_id := hom_ext (((ev Ψ 𝕋).map_comp _ _).symm.trans (by
    rw [w.inv_hom_id, Functor.map_id]; rfl))

/-- The tensor product of `Graph` is that of formal expressions on objects and that of `𝒟` on
morphisms, with the structure isomorphisms of formal expressions. -/
instance : MonoidalCategoryStruct (Graph L Ψ 𝕋 ω) where
  tensorObj X Y := mk (X.expr ⊗ Y.expr) (X.isInvertible.map_tensor Ψ Y.isInvertible)
  whiskerLeft X _ _ f := ⟨(ev Ψ 𝕋).obj X.expr ◁ f.1, f.2.whiskerLeft' _⟩
  whiskerRight f Y := ⟨f.1 ▷ (ev Ψ 𝕋).obj Y.expr, f.2.whiskerRight _⟩
  tensorHom f g := ⟨f.1 ⊗ₘ g.1,
    ((f.2.whiskerRight _).comp (g.2.whiskerLeft' _)).congr (tensorHom_def _ _).symm⟩
  tensorUnit := mk (𝟙_ (Expr 𝒜)) (isInvertible_map_tensorUnit Ψ)
  associator X Y Z := freeIso (α_ X.expr Y.expr Z.expr)
  leftUnitor X := freeIso (λ_ X.expr)
  rightUnitor X := freeIso (ρ_ X.expr)

/-- Conjugating the associator by identity isomorphisms gives the associator. -/
theorem refl_associator {C : Type*} [Category C] [MonoidalCategory C] (A B D : C) :
    (((Iso.refl ((A ⊗ B) ⊗ D)).symm ≪≫ ((Iso.refl (A ⊗ B)).symm ⊗ᵢ Iso.refl D)) ≪≫
      α_ A B D ≪≫ ((Iso.refl A ⊗ᵢ Iso.refl (B ⊗ D)) ≪≫ Iso.refl (A ⊗ B ⊗ D))).hom =
      (α_ A B D).hom := by
  simp

/-- Conjugating the left unitor by identity isomorphisms gives the left unitor. -/
theorem refl_leftUnitor {C : Type*} [Category C] [MonoidalCategory C] (A : C) :
    (((Iso.refl (𝟙_ C ⊗ A)).symm ≪≫ ((Iso.refl (𝟙_ C)).symm ⊗ᵢ Iso.refl A)) ≪≫ λ_ A).hom =
      (λ_ A).hom := by
  simp

/-- Conjugating the right unitor by identity isomorphisms gives the right unitor. -/
theorem refl_rightUnitor {C : Type*} [Category C] [MonoidalCategory C] (A : C) :
    (((Iso.refl (A ⊗ 𝟙_ C)).symm ≪≫ (Iso.refl A ⊗ᵢ (Iso.refl (𝟙_ C)).symm)) ≪≫ ρ_ A).hom =
      (ρ_ A).hom := by
  simp

/-- A morphism is its own conjugate by identity isomorphisms. -/
theorem refl_conj {C : Type*} [Category C] {A B : C} (g : A ⟶ B) :
    g = (Iso.refl A).inv ≫ g ≫ (Iso.refl B).hom := by
  simp

/-- The data inducing the monoidal structure of `Graph` along `incl`. -/
def inducingData : Monoidal.InducingFunctorData (incl L Ψ 𝕋 ω) where
      μIso := fun _ _ => Iso.refl _
      whiskerLeft_eq := fun _ _ _ _ => refl_conj _
      whiskerRight_eq := fun _ _ => refl_conj _
      tensorHom_eq := fun _ _ => refl_conj _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ => (refl_associator _ _ _).symm
      leftUnitor_eq := fun _ => (refl_leftUnitor _).symm
      rightUnitor_eq := fun _ => (refl_rightUnitor _).symm

/-- The monoidal structure of `Graph` induced along `incl`. -/
instance : MonoidalCategory (Graph L Ψ 𝕋 ω) :=
  Monoidal.induced (incl L Ψ 𝕋 ω) inducingData

/-- The functor `incl` is monoidal, with identity tensorator and unit. -/
instance : (incl L Ψ 𝕋 ω).Monoidal :=
  Monoidal.fromInducedMonoidal (incl L Ψ 𝕋 ω) inducingData

/-- The tensorator of `incl` is the identity. -/
@[simp] theorem incl_μ (X Y : Graph L Ψ 𝕋 ω) : μ (incl L Ψ 𝕋 ω) X Y = 𝟙 _ := rfl

/-- The inverse tensorator of `incl` is the identity. -/
@[simp] theorem incl_δ (X Y : Graph L Ψ 𝕋 ω) : δ (incl L Ψ 𝕋 ω) X Y = 𝟙 _ := rfl

/-- The unit morphism of `incl` is the identity. -/
@[simp] theorem incl_ε : ε (incl L Ψ 𝕋 ω) = 𝟙 _ := rfl

/-- The counit morphism of `incl` is the identity. -/
@[simp] theorem incl_η : η (incl L Ψ 𝕋 ω) = 𝟙 _ := rfl

/-- The braiding of `Graph`. -/
def braiding (X Y : Graph L Ψ 𝕋 ω) : X ⊗ Y ≅ Y ⊗ X where
  hom := ⟨(β_ ((ev Ψ 𝕋).obj X.expr) ((ev Ψ 𝕋).obj Y.expr)).hom, good_braiding _ _⟩
  inv := ⟨(β_ ((ev Ψ 𝕋).obj X.expr) ((ev Ψ 𝕋).obj Y.expr)).inv,
    (good_braiding Y.expr X.expr).congr (SymmetricCategory.braiding_swap_eq_inv_braiding _ _)⟩
  hom_inv_id := hom_ext (Iso.hom_inv_id _)
  inv_hom_id := hom_ext (Iso.inv_hom_id _)

/-- `Graph` is braided by `Graph.braiding`. -/
instance : BraidedCategory (Graph L Ψ 𝕋 ω) :=
  BraidedCategory.ofFaithful (incl L Ψ 𝕋 ω) braiding (fun _ _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm)

/-- The functor `incl` is braided. -/
instance : (incl L Ψ 𝕋 ω).Braided where
  braided _ _ := (Category.id_comp _).trans (Category.comp_id _).symm

/-- The braided monoidal category `Graph` is symmetric. -/
instance : SymmetricCategory (Graph L Ψ 𝕋 ω) :=
  SymmetricCategory.ofFaithful (incl L Ψ 𝕋 ω)

variable (L Ψ 𝕋 ω)

/-- The functor `A ↦ atom A` from `𝒜`. -/
def ι : 𝒜 ⥤ Graph L Ψ 𝕋 ω where
  obj A := mk (atom A) (isInvertible_map_tensorUnit Ψ)
  map g := ⟨Ψ.map g, good_atom g⟩
  map_id A := hom_ext (Ψ.map_id A)
  map_comp f g := hom_ext (Ψ.map_comp f g)

/-- The underlying morphism of `(ι L Ψ 𝕋 ω).map g` is `Ψ.map g`. -/
@[simp] theorem ι_map_val {A B : 𝒜} (g : A ⟶ B) : ((ι L Ψ 𝕋 ω).map g).1 = Ψ.map g := rfl

/-- The monoidal structure of `ι`, given by that of `Ψ`. -/
def ιCoreMonoidal : (ι L Ψ 𝕋 ω).CoreMonoidal where
  εIso :=
    { hom := ⟨ε Ψ, coh_ε.good⟩
      inv := ⟨η Ψ, (Coh.inv (e := 𝟙_ (Expr 𝒜)) (e' := atom (𝟙_ 𝒜)) (u := εIso Ψ)
        (φ := Iso.refl _) (c := Iso.refl _) coh_ε).good⟩
      hom_inv_id := hom_ext (ε_η Ψ)
      inv_hom_id := hom_ext (η_ε Ψ) }
  μIso A B :=
    { hom := ⟨μ Ψ A B, (coh_μ A B).good⟩
      inv := ⟨δ Ψ A B, (Coh.inv (e := atom A ⊗ atom B) (e' := atom (A ⊗ B)) (u := μIso Ψ A B)
        (φ := λ_ (𝟙_ 𝒜)) (c := Iso.refl _)
        (coh_μ A B)).good⟩
      hom_inv_id := hom_ext (μ_δ Ψ A B)
      inv_hom_id := hom_ext (δ_μ Ψ A B) }
  μIso_hom_natural_left f X := hom_ext (μ_natural_left Ψ f X)
  μIso_hom_natural_right X f := hom_ext (μ_natural_right Ψ X f)
  associativity X Y Z := hom_ext (associativity Ψ X Y Z)
  left_unitality X := hom_ext (left_unitality Ψ X)
  right_unitality X := hom_ext (right_unitality Ψ X)

/-- The functor `ι` is monoidal, with the monoidal structure of `Ψ`. -/
instance : (ι L Ψ 𝕋 ω).Monoidal := (ιCoreMonoidal L Ψ 𝕋 ω).toMonoidal

/-- The functor `ι` is braided. -/
instance : (ι L Ψ 𝕋 ω).Braided where
  braided A B := hom_ext (Functor.LaxBraided.braided (F := Ψ) A B)

/-- The underlying morphism of the tensorator of `ι` is the tensorator of `Ψ`. -/
@[simp] theorem ι_μ_val (A B : 𝒜) : (μ (ι L Ψ 𝕋 ω) A B).1 = μ Ψ A B := rfl

/-- The underlying morphism of the unit morphism of `ι` is that of `Ψ`. -/
@[simp] theorem ι_ε_val : (ε (ι L Ψ 𝕋 ω)).1 = ε Ψ := rfl

end Graph

end CategoryTheory.InvertingObject
