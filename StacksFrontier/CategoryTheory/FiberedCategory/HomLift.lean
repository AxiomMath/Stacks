module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-! # Lying over a morphism: composites and opposite categories

Lemmas about `CategoryTheory.Functor.IsHomLift`, which records that a morphism of the total
category lies over a given morphism of the base: lifts through a composite functor, and lifts
transported across `Opposite.op`.

## Main results

* `CategoryTheory.Functor.isHomLift_comp_iff`: `ψ` lies over `f` for `G ⋙ r` if and only if
  `G.map ψ` lies over `f` for `r`.
* `CategoryTheory.Functor.isHomLift_comp_functor`: a morphism lying over `f` for `p` lies over
  `u.map f` for `p ⋙ u`.
* `CategoryTheory.isHomLift_op`: a lift transported to the opposite categories.
* `CategoryTheory.isHomLift_unop`: a lift transported back from the opposite categories.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]

/-- Lying over a morphism of the base is detected through a composite: for `G : 𝒮 ⥤ 𝒯` and a
structure functor `r : 𝒯 ⥤ 𝒵`, a morphism `ψ` of `𝒮` lies over `f` for `G ⋙ r` if and only if
`G.map ψ` lies over `f` for `r`. -/
lemma Functor.isHomLift_comp_iff (G : 𝒮 ⥤ 𝒯) (r : 𝒯 ⥤ 𝒵) {R S : 𝒵} (f : R ⟶ S) {a b : 𝒮}
    (ψ : a ⟶ b) : (G ⋙ r).IsHomLift f ψ ↔ r.IsHomLift f (G.map ψ) :=
  ⟨fun _ => by
    subst_hom_lift (G ⋙ r) f ψ
    exact IsHomLift.map (p := r) (G.map ψ),
    fun _ => by
    subst_hom_lift r f (G.map ψ)
    exact IsHomLift.map (p := G ⋙ r) ψ⟩

/-- A morphism lying over `f` for `p` lies over `u.map f` for `p ⋙ u`. -/
public lemma Functor.isHomLift_comp_functor {p : 𝒮 ⥤ 𝒯} (u : 𝒯 ⥤ 𝒵) {R S : 𝒯} {x y : 𝒮}
    (f : R ⟶ S) (φ : x ⟶ y) (hf : p.IsHomLift f φ) : (p ⋙ u).IsHomLift (u.map f) φ := by
  subst_hom_lift p f φ
  exact IsHomLift.map (p := p ⋙ u) φ

/-- A morphism lying over an identity for `p` lies over an identity for `p ⋙ u`. -/
public lemma Functor.isHomLift_id_comp_functor {p : 𝒮 ⥤ 𝒯} (u : 𝒯 ⥤ 𝒵) {R : 𝒯} {x y : 𝒮}
    {φ : x ⟶ y} (hφ : p.IsHomLift (𝟙 R) φ) : (p ⋙ u).IsHomLift (𝟙 (u.obj R)) φ := by
  have h₀ := Functor.isHomLift_comp_functor u (𝟙 R) φ hφ
  rwa [u.map_id] at h₀

/-- A morphism lying over `f` lies over `f.op` after passing to opposite categories. -/
public lemma isHomLift_op (p : 𝒮 ⥤ 𝒯) {R S : 𝒯} {a b : 𝒮} (f : R ⟶ S) (φ : a ⟶ b)
    [inst : p.IsHomLift f φ] : p.op.IsHomLift f.op φ.op := by
  subst_hom_lift p f φ
  exact IsHomLift.map (p := p.op) φ.op

/-- A morphism of the opposite categories lying over `f` for `p.op` unops to a morphism
lying over `f.unop` for `p`. -/
public lemma isHomLift_unop (p : 𝒮 ⥤ 𝒯) {R S : 𝒯ᵒᵖ} {a b : 𝒮ᵒᵖ} (f : R ⟶ S) (φ : a ⟶ b)
    [inst : p.op.IsHomLift f φ] : p.IsHomLift f.unop φ.unop := by
  subst_hom_lift p.op f φ
  exact IsHomLift.map (p := p) φ.unop

end CategoryTheory
