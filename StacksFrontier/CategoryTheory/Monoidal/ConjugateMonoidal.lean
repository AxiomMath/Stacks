module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Conjugate natural transformations and monoidal structures

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be two adjunctions between monoidal categories in which the left
adjoints are oplax monoidal, the right adjoints lax monoidal, and the structures are compatible
with the adjunctions (`CategoryTheory.Adjunction.IsMonoidal`). A natural transformation
`τ : R₁ ⟶ R₂` and its conjugate `σ : L₂ ⟶ L₁` determine each other. This file proves that if `τ`
is monoidal then `σ` is compatible with the two oplax structures: `σ` commutes with the counit
morphisms `η` and with the comparison morphisms `δ`. When both left adjoints are strong monoidal
this says that `σ` is a monoidal natural transformation.

This is the form in which monoidality of a comparison of left adjoints is proved in practice: the
left adjoints are typically sheafified Kan extensions, about which nothing can be computed
directly, while the right adjoints are restrictions, for which the corresponding identity is a
computation with sections.

## Main results

* `CategoryTheory.Adjunction.conjugateEquiv_symm_app_unit_comp_η` and
  `CategoryTheory.Adjunction.conjugateEquiv_symm_app_tensor_comp_δ`: the conjugate of a monoidal
  transformation of lax right adjoints commutes with `η` and with `δ`.
* `CategoryTheory.NatTrans.isMonoidal_of_η_of_δ`: between strong monoidal functors, a natural
  transformation commuting with `η` and `δ` is monoidal; conversely
  `CategoryTheory.NatTrans.IsMonoidal.app_tensor_comp_δ` and
  `CategoryTheory.NatTrans.IsMonoidal.app_unit_comp_η`.
* `CategoryTheory.Adjunction.isMonoidal_conjugateEquiv_symm`: the conjugate of a monoidal
  transformation of lax right adjoints of strong monoidal functors is monoidal.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

namespace Adjunction

/-- Transposing `σ.app A ≫ f` along `adj₂` is transposing `f` along `adj₁` followed by the
conjugate of `σ`. -/
private theorem homEquiv_app_comp_conjugateEquiv {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (σ : L₂ ⟶ L₁) {A : C}
    {B : D} (f : L₁.obj A ⟶ B) :
    adj₂.homEquiv _ _ (σ.app A ≫ f) = adj₁.homEquiv _ _ f ≫ (conjugateEquiv adj₁ adj₂ σ).app B := by
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv adj₁ adj₂, Category.assoc, ← NatTrans.naturality, Category.assoc]

variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- The conjugate `σ : L₂ ⟶ L₁` of a transformation of lax right adjoints whose conjugate is
monoidal commutes with the counit morphisms `η` of the two oplax left adjoints. -/
theorem conjugateEquiv_symm_app_unit_comp_η (σ : L₂ ⟶ L₁)
    [NatTrans.IsMonoidal (conjugateEquiv adj₁ adj₂ σ)] :
    σ.app (𝟙_ C) ≫ η L₁ = η L₂ := by
  apply (adj₂.homEquiv _ _).injective
  rw [homEquiv_app_comp_conjugateEquiv adj₁ adj₂, homEquiv_unit, homEquiv_unit,
    adj₁.unit_app_unit_comp_map_η, NatTrans.IsMonoidal.unit, adj₂.unit_app_unit_comp_map_η]

/-- The conjugate `σ : L₂ ⟶ L₁` of a transformation of lax right adjoints whose conjugate is
monoidal commutes with the comparison morphisms `δ` of the two oplax left adjoints. -/
theorem conjugateEquiv_symm_app_tensor_comp_δ (σ : L₂ ⟶ L₁)
    [NatTrans.IsMonoidal (conjugateEquiv adj₁ adj₂ σ)] (X Y : C) :
    σ.app (X ⊗ Y) ≫ δ L₁ X Y = δ L₂ X Y ≫ (σ.app X ⊗ₘ σ.app Y) := by
  apply (adj₂.homEquiv _ _).injective
  rw [homEquiv_app_comp_conjugateEquiv adj₁ adj₂, homEquiv_unit, homEquiv_unit, Functor.map_comp,
    adj₁.unit_app_tensor_comp_map_δ, Category.assoc, NatTrans.IsMonoidal.tensor,
    tensorHom_comp_tensorHom_assoc, unit_conjugateEquiv, unit_conjugateEquiv,
    ← tensorHom_comp_tensorHom_assoc, μ_natural, adj₂.unit_app_tensor_comp_map_δ_assoc]

end Adjunction

namespace NatTrans

/-- Between strong monoidal functors, a natural transformation commuting with the counit
morphisms `η` and the comparison morphisms `δ` of the oplax structures is monoidal. -/
theorem isMonoidal_of_η_of_δ {F₁ F₂ : C ⥤ D} [F₁.Monoidal] [F₂.Monoidal] (σ : F₁ ⟶ F₂)
    (hη : σ.app (𝟙_ C) ≫ η F₂ = η F₁)
    (hδ : ∀ X Y : C, σ.app (X ⊗ Y) ≫ δ F₂ X Y = δ F₁ X Y ≫ (σ.app X ⊗ₘ σ.app Y)) :
    NatTrans.IsMonoidal σ where
  unit := by
    rw [← cancel_mono (η F₂), Category.assoc, hη, Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  tensor X Y := by
    rw [← cancel_mono (δ F₂ X Y), Category.assoc, hδ, Functor.Monoidal.μ_δ_assoc,
      Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- A monoidal natural transformation between strong monoidal functors commutes with the
comparison morphisms `δ`. -/
@[reassoc]
theorem IsMonoidal.app_tensor_comp_δ {F₁ F₂ : C ⥤ D} [F₁.Monoidal] [F₂.Monoidal] (σ : F₁ ⟶ F₂)
    [NatTrans.IsMonoidal σ] (X Y : C) :
    σ.app (X ⊗ Y) ≫ δ F₂ X Y = δ F₁ X Y ≫ (σ.app X ⊗ₘ σ.app Y) := by
  rw [← cancel_epi (μ F₁ X Y), NatTrans.IsMonoidal.tensor_assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, Functor.Monoidal.μ_δ_assoc]

/-- A monoidal natural transformation between strong monoidal functors commutes with the
counit morphisms `η`. -/
@[reassoc]
theorem IsMonoidal.app_unit_comp_η {F₁ F₂ : C ⥤ D} [F₁.Monoidal] [F₂.Monoidal] (σ : F₁ ⟶ F₂)
    [NatTrans.IsMonoidal σ] : σ.app (𝟙_ C) ≫ η F₂ = η F₁ := by
  rw [← cancel_epi (ε F₁), NatTrans.IsMonoidal.unit_assoc, Functor.Monoidal.ε_η,
    Functor.Monoidal.ε_η]

end NatTrans

namespace Adjunction

variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.Monoidal] [L₂.Monoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- **The conjugate of a monoidal transformation of lax right adjoints is monoidal**, when the two
left adjoints are strong monoidal and the adjunctions are compatible with the structures. -/
theorem isMonoidal_conjugateEquiv_symm (σ : L₂ ⟶ L₁)
    [NatTrans.IsMonoidal (conjugateEquiv adj₁ adj₂ σ)] :
    NatTrans.IsMonoidal σ :=
  NatTrans.isMonoidal_of_η_of_δ σ (conjugateEquiv_symm_app_unit_comp_η adj₁ adj₂ σ)
    (conjugateEquiv_symm_app_tensor_comp_δ adj₁ adj₂ σ)

end Adjunction

namespace Functor.LaxMonoidal

variable {F G : C ⥤ D} [F.LaxMonoidal] (e : F ≅ G)

/-- Transport of a lax monoidal structure along a natural isomorphism of functors: the unit
morphism and the tensorator are those of the source, conjugated by the isomorphism. This is the
lax counterpart of Mathlib's `CategoryTheory.Functor.Monoidal.transport`. -/
@[instance_reducible]
def transport : G.LaxMonoidal :=
  LaxMonoidal.ofTensorHom (ε F ≫ e.hom.app (𝟙_ C))
    (fun X Y => (e.inv.app X ⊗ₘ e.inv.app Y) ≫ μ F X Y ≫ e.hom.app (X ⊗ Y))
    (fun {X Y X' Y'} f g => by
      simp only [tensorHom_comp_tensorHom_assoc, NatTrans.naturality, Category.assoc]
      rw [← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, e.hom.naturality])
    (fun X Y Z => by
      simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp]
      rw [← e.hom.naturality]
      conv_lhs => rw [← Category.comp_id (e.inv.app Z), ← tensorHom_comp_tensorHom, tensorHom_id,
        Category.assoc, associativity_assoc, associator_naturality_assoc]
      conv_rhs => rw [← Category.comp_id (e.inv.app X), ← tensorHom_comp_tensorHom, id_tensorHom]
      simp only [Category.assoc])
    (fun X => by
      simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp]
      rw [← e.hom.naturality, ← tensorUnit_whiskerLeft_comp_leftUnitor_hom_assoc,
        leftUnitor_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id])
    (fun X => by
      simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
        Category.comp_id, Category.id_comp]
      rw [← e.hom.naturality, ← whiskerRight_tensorUnit_comp_rightUnitor_hom_assoc,
        rightUnitor_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id])

/-- The unit morphism of the transported lax monoidal structure on `G` is `ε F` followed by the
component of `e.hom` at the monoidal unit. -/
@[reassoc]
lemma transport_ε : letI := transport e
    ε G = ε F ≫ e.hom.app (𝟙_ C) :=
  rfl

/-- The tensorator of the transported lax monoidal structure on `G` at `X` and `Y` is the
tensorator of `F` conjugated by the components of `e`. -/
@[reassoc]
lemma transport_μ (X Y : C) : letI := transport e
    μ G X Y = (e.inv.app X ⊗ₘ e.inv.app Y) ≫ μ F X Y ≫ e.hom.app (X ⊗ Y) :=
  rfl

/-- The isomorphism along which a lax monoidal structure is transported is monoidal. -/
lemma isMonoidal_transport_hom : letI := transport e
    NatTrans.IsMonoidal e.hom := by
  let := transport e
  exact ⟨rfl, fun X Y => by
    rw [transport_μ, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
      tensorHom_id, id_whiskerRight, Category.id_comp]⟩

end Functor.LaxMonoidal

end CategoryTheory
