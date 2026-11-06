module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheaf

/-!
# Morphisms out of the presheaf of components are compatible families of sections

For a functor `z : 𝒵 ⥤ 𝒳`, the presheaf of components `Ψ(z)` of
`Stacks.Sites.CoverDescent.componentPresheaf` is the left Kan extension along `z` of the final
presheaf. Concretely: a morphism `Ψ(z) ⟶ F` into a presheaf of sets `F` on `𝒳` is the same thing
as a compatible family of sections of `F` over the image of `z`, that is, a section of
`z.op ⋙ F`. This file records that bijection and its naturality in `F`.

## Main definitions

* `Stacks.Sites.CoverDescent.componentPresheafHomEquiv`:
  `(Ψ(z) ⟶ F) ≃ (z.op ⋙ F).sections`.

## Main results

* `Stacks.Sites.CoverDescent.componentPresheafHomEquiv_naturality`: the bijection is natural in
  `F`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂

namespace Stacks.Sites.CoverDescent

variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒵 : Type u₂} [Category.{v₂} 𝒵] (z : 𝒵 ⥤ 𝒳)

/-- The morphism `Ψ(z) ⟶ F` attached to a compatible family of sections of `F` over the image of
`z`: the class of `φ : y ⟶ z(ζ)` goes to the restriction along `φ` of the section at `ζ`. -/
def componentPresheafDesc (F : 𝒳ᵒᵖ ⥤ Type (max u₂ v₁)) (s : (z.op ⋙ F).sections) :
    componentPresheaf z ⟶ F where
  app y := ↾fun c => Quotient.lift (fun x : StructuredArrow y.unop z =>
      F.map x.hom.op (s.1 (op x.right)))
    (fun x x' (h : Zigzag x x') => by
      induction h with
      | refl => rfl
      | tail _ hzag ih =>
        rw [ih]
        rcases hzag with ⟨⟨m⟩⟩ | ⟨⟨m⟩⟩
        · rw [← StructuredArrow.w m, op_comp, Functor.map_comp_apply]
          congr 1
          exact (s.2 m.right.op).symm
        · rw [← StructuredArrow.w m, op_comp, Functor.map_comp_apply]
          congr 1
          exact s.2 m.right.op) c
  naturality {y y'} g := TypeCat.homEquiv.injective (funext fun c => by
    induction c using Quotient.inductionOn with
    | h x =>
      change F.map (g.unop ≫ x.hom).op (s.1 (op x.right)) =
        F.map g (F.map x.hom.op (s.1 (op x.right)))
      rw [op_comp, Functor.map_comp_apply]
      rfl)

/-- The morphism `componentPresheafDesc z F s` sends the class of `φ : y ⟶ z(ζ)` to the
restriction along `φ` of the section of `s` at `ζ`. -/
lemma componentPresheafDesc_app_mk (F : 𝒳ᵒᵖ ⥤ Type (max u₂ v₁)) (s : (z.op ⋙ F).sections)
    {y : 𝒳} {ζ : 𝒵} (φ : y ⟶ z.obj ζ) :
    (componentPresheafDesc z F s).app (op y) (componentMk z φ) = F.map φ.op (s.1 (op ζ)) :=
  rfl

/-- The compatible family of sections over the image of `z` attached to a morphism
`η : Ψ(z) ⟶ F`: its value at `ζ` is the image under `η` of the class of the identity of `z(ζ)`. -/
def componentPresheafSection (F : 𝒳ᵒᵖ ⥤ Type (max u₂ v₁)) (η : componentPresheaf z ⟶ F) :
    (z.op ⋙ F).sections :=
  ⟨fun ζ => η.app (op (z.obj ζ.unop)) (componentMk z (𝟙 _)), fun {ζ ζ'} m => by
    change F.map (z.map m.unop).op (η.app _ (componentMk z (𝟙 _))) =
      η.app _ (componentMk z (𝟙 _))
    rw [← NatTrans.naturality_apply η (z.map m.unop).op, componentPresheaf_map_mk,
      Category.comp_id]
    congr 1
    exact ((componentMk_eq_of_comp z (𝟙 _) m.unop).trans (by rw [Category.id_comp])).symm⟩

/-- **Morphisms out of the presheaf of components are compatible families of sections**:
`(Ψ(z) ⟶ F) ≃ (z.op ⋙ F).sections`, a morphism going to its values on the classes of the
identities of the objects `z(ζ)`. -/
def componentPresheafHomEquiv (F : 𝒳ᵒᵖ ⥤ Type (max u₂ v₁)) :
    (componentPresheaf z ⟶ F) ≃ (z.op ⋙ F).sections where
  toFun := componentPresheafSection z F
  invFun := componentPresheafDesc z F
  left_inv η := by
    refine NatTrans.ext (funext fun y => TypeCat.homEquiv.injective (funext fun c => ?_))
    obtain ⟨y⟩ := y
    obtain ⟨ζ, φ, rfl⟩ := componentMk_surjective z c
    refine (componentPresheafDesc_app_mk z F _ φ).trans ?_
    refine (NatTrans.naturality_apply η φ.op (componentMk z (𝟙 _))).symm.trans ?_
    rw [componentPresheaf_map_mk, Category.comp_id]
    rfl
  right_inv s := by
    refine Subtype.ext (funext fun ζ => ?_)
    refine (componentPresheafDesc_app_mk z F s (𝟙 _)).trans ?_
    rw [op_id, Functor.map_id_apply]

/-- **The bijection `componentPresheafHomEquiv` is natural in the presheaf**: composing with
`α : F ⟶ G` acts on the compatible family of sections sectionwise. -/
lemma componentPresheafHomEquiv_naturality {F G : 𝒳ᵒᵖ ⥤ Type (max u₂ v₁)}
    (η : componentPresheaf z ⟶ F) (α : F ⟶ G) (ζ : 𝒵ᵒᵖ) :
    (componentPresheafHomEquiv z G (η ≫ α)).1 ζ =
      α.app _ ((componentPresheafHomEquiv z F η).1 ζ) :=
  rfl

end Stacks.Sites.CoverDescent

end
