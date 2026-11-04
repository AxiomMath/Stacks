module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre

/-!
# Reindexing and comparing presheaves of vertical morphisms

Let `p : X ⥤ 𝒞` be fibred in groupoids and let `Y₁, Y₂ : 𝒯 ⥤ X` be two families of objects of
`X` indexed by a category `𝒯` over `𝒞`. The presheaf
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheaf` on `𝒯` has as its sections
over `a` the vertical morphisms `Y₁ a ⟶ Y₂ a`. This file records the three structural facts about
that presheaf which a fibre computation needs and which the file introducing it does not state.

* Reindexing along a functor `K : D ⥤ 𝒯` is the same as forming the presheaf of the reindexed
  families: the sections agree by definition, and the restriction maps agree because both are the
  unique vertical fill-in against one and the same cartesian morphism.
* Replacing `Y₁` and `Y₂` by families 2-isomorphic to them over `𝒞` changes the presheaf by an
  isomorphism: conjugate a vertical morphism by the components of the two 2-isomorphisms.
* Interchanging `Y₁` and `Y₂` changes the presheaf by an isomorphism: a vertical morphism of a
  category fibred in groupoids is invertible, and inverting commutes with restriction.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafIsoOfNatIso`: the comparison
  isomorphism for 2-isomorphic families.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafSymmIso`: the comparison
  isomorphism for the interchanged families.

## Main results

* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheaf_comp_op`: the presheaf of
  the reindexed families is the reindexing of the presheaf, on the nose.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.isIso_val`: a vertical morphism is
  invertible.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.restrict_inv`: inverting a vertical
  morphism commutes with restriction.

## What is and is not proved

Proved, in full, with no carried hypothesis: the three facts above, for abstract categories. No
tag is claimed; the file states no result of the Stacks project.

## Implementation notes

Every proof is an appeal to
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.restrict_uniq`: restriction is
characterised by one equation, so to identify two restrictions it is enough to check that
equation for one of them.

## References

* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Y₁ Y₂ : 𝒯 ⥤ X}

attribute [local implicit_reducible] presheaf VertHom

/-! ### Reindexing along a functor -/

/-- **The presheaf of vertical morphisms of a reindexed pair of families is the reindexing of the
presheaf of vertical morphisms.** The sections agree by definition — a vertical morphism between
the values of `Y₁` and `Y₂` at `K T` is the same thing as one between the values of `K ⋙ Y₁` and
`K ⋙ Y₂` at `T` — and the restriction maps agree because each is the unique vertical fill-in
against the image under `Y₂` of one and the same morphism. -/
theorem presheaf_comp_op {D : Type u₄} [Category.{v₄} D] (K : D ⥤ 𝒯)
    (hp : p.IsFiberedInGroupoids) (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯)
    (h₁' : (K ⋙ Y₁) ⋙ p = K ⋙ p𝒯) (h₂' : (K ⋙ Y₂) ⋙ p = K ⋙ p𝒯) :
    K.op ⋙ presheaf hp h₁ h₂ = presheaf hp h₁' h₂' := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro T T' f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  ext φ
  exact (restrict_uniq hp h₁' h₂' f.unop φ (restrict hp h₁ h₂ (K.map f.unop) φ)
    (restrict_fac hp h₁ h₂ (K.map f.unop) φ)).symm

/-! ### Comparing 2-isomorphic families -/

section Congr

variable {Y₁' Y₂' : 𝒯 ⥤ X} (hp : p.IsFiberedInGroupoids) (h₁ : Y₁ ⋙ p = p𝒯)
  (h₂ : Y₂ ⋙ p = p𝒯) (h₁' : Y₁' ⋙ p = p𝒯) (h₂' : Y₂' ⋙ p = p𝒯) (θ₁ : Y₁ ≅ Y₁') (θ₂ : Y₂ ≅ Y₂')
  (hθ₁ : ∀ a, p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₁.hom.app a))
  (hθ₂ : ∀ a, p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₂.hom.app a))

include hθ₁ hθ₂ in
/-- Conjugating a vertical morphism by the components of two vertical 2-isomorphisms gives a
vertical morphism. -/
theorem isHomLift_conj (a : 𝒯) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₁.inv.app a ≫ φ.1 ≫ θ₂.hom.app a) := by
  have h1 : p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₁.inv.app a) := by
    have h0 : p.IsHomLift (𝟙 (p𝒯.obj a)) (θ₁.app a).hom := hθ₁ a
    exact IsHomLift.lift_id_inv p (p𝒯.obj a) (θ₁.app a)
  have h2 := φ.2
  have h3 := hθ₂ a
  have hc : p.IsHomLift (𝟙 (p𝒯.obj a)) (φ.1 ≫ θ₂.hom.app a) :=
    IsHomLift.comp_lift_id_right p (𝟙 (p𝒯.obj a)) φ.1 (θ₂.hom.app a)
  exact IsHomLift.comp_lift_id_left p (𝟙 (p𝒯.obj a)) (φ.1 ≫ θ₂.hom.app a) (θ₁.inv.app a)

include hθ₁ hθ₂ in
/-- Conjugation by two vertical 2-isomorphisms commutes with restriction: both sides are the
unique vertical fill-in against the image of one morphism. -/
theorem restrict_conj {a' a : 𝒯} (h : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    restrict hp h₁' h₂' h ⟨θ₁.inv.app a ≫ φ.1 ≫ θ₂.hom.app a, isHomLift_conj θ₁ θ₂ hθ₁ hθ₂ a φ⟩ =
      ⟨θ₁.inv.app a' ≫ (restrict hp h₁ h₂ h φ).1 ≫ θ₂.hom.app a',
        isHomLift_conj θ₁ θ₂ hθ₁ hθ₂ a' (restrict hp h₁ h₂ h φ)⟩ := by
  refine (restrict_uniq hp h₁' h₂' h _ _ ?_).symm
  calc (θ₁.inv.app a' ≫ (restrict hp h₁ h₂ h φ).1 ≫ θ₂.hom.app a') ≫ Y₂'.map h
      = θ₁.inv.app a' ≫ (restrict hp h₁ h₂ h φ).1 ≫ Y₂.map h ≫ θ₂.hom.app a := by
        simp only [Category.assoc, ← θ₂.hom.naturality h]
    _ = θ₁.inv.app a' ≫ (Y₁.map h ≫ φ.1) ≫ θ₂.hom.app a := by
        rw [← Category.assoc (restrict hp h₁ h₂ h φ).1, restrict_fac hp h₁ h₂ h φ]
    _ = Y₁'.map h ≫ θ₁.inv.app a ≫ φ.1 ≫ θ₂.hom.app a := by
        simp only [Category.assoc]
        rw [← Category.assoc (θ₁.inv.app a'), ← θ₁.inv.naturality h, Category.assoc]

include hθ₁ hθ₂ in
/-- **The presheaves of vertical morphisms of two pairs of 2-isomorphic families are
isomorphic.** The components conjugate by the 2-isomorphisms, which is compatible with
restriction by
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.restrict_conj`. -/
noncomputable def presheafIsoOfNatIso :
    presheaf hp h₁ h₂ ≅ presheaf hp h₁' h₂' :=
  NatIso.ofComponents
    (fun a => Equiv.toIso
      { toFun := fun φ => ⟨θ₁.inv.app a.unop ≫ φ.1 ≫ θ₂.hom.app a.unop,
          isHomLift_conj θ₁ θ₂ hθ₁ hθ₂ a.unop φ⟩
        invFun := fun φ => ⟨θ₁.hom.app a.unop ≫ φ.1 ≫ θ₂.inv.app a.unop, by
          exact isHomLift_conj (p𝒯 := p𝒯) θ₁.symm θ₂.symm
            (fun b => by
              have h0 : p.IsHomLift (𝟙 (p𝒯.obj b)) (θ₁.app b).hom := hθ₁ b
              exact IsHomLift.lift_id_inv p (p𝒯.obj b) (θ₁.app b))
            (fun b => by
              have h0 : p.IsHomLift (𝟙 (p𝒯.obj b)) (θ₂.app b).hom := hθ₂ b
              exact IsHomLift.lift_id_inv p (p𝒯.obj b) (θ₂.app b)) a.unop φ⟩
        left_inv := fun φ => by
          apply Subtype.ext
          simp
        right_inv := fun φ => by
          apply Subtype.ext
          simp })
    (by
      intro a a' f
      ext φ
      exact (restrict_conj hp h₁ h₂ h₁' h₂' θ₁ θ₂ hθ₁ hθ₂ f.unop φ).symm)

end Congr

/-! ### Interchanging the two families -/

section Symm

variable (hp : p.IsFiberedInGroupoids) (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯)

include hp in
/-- **A vertical morphism of a category fibred in groupoids is invertible.** It lies over an
identity, hence is strongly cartesian over an isomorphism. -/
theorem isIso_val {a : 𝒯} (φ : VertHom p p𝒯 Y₁ Y₂ a) : IsIso φ.1 := by
  have hφ := φ.2
  have := hp.isStronglyCartesian_homLift (𝟙 (p𝒯.obj a)) φ.1
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p𝒯.obj a)) φ.1

include hp in
/-- The inverse of a vertical morphism is vertical. -/
theorem isHomLift_inv_val {a : 𝒯} (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    letI := isIso_val hp φ
    p.IsHomLift (𝟙 (p𝒯.obj a)) (CategoryTheory.inv φ.1) := by
  have := isIso_val hp φ
  have hφ := φ.2
  exact IsHomLift.lift_id_inv_isIso p (p𝒯.obj a) φ.1

/-- The inverse of a vertical morphism, as a vertical morphism the other way round. -/
noncomputable def symmVal {a : 𝒯} (φ : VertHom p p𝒯 Y₁ Y₂ a) : VertHom p p𝒯 Y₂ Y₁ a :=
  letI := isIso_val hp φ
  ⟨CategoryTheory.inv φ.1, isHomLift_inv_val hp φ⟩

/-- **Inverting a vertical morphism commutes with restriction.** The restriction of the inverse
satisfies the equation characterising the inverse of the restriction. -/
theorem restrict_symmVal {a' a : 𝒯} (h : a' ⟶ a) (φ : VertHom p p𝒯 Y₁ Y₂ a) :
    restrict hp h₂ h₁ h (symmVal hp φ) = symmVal hp (restrict hp h₁ h₂ h φ) := by
  have := isIso_val hp φ
  have := isIso_val hp (restrict hp h₁ h₂ h φ)
  refine (restrict_uniq hp h₂ h₁ h (symmVal hp φ) (symmVal hp (restrict hp h₁ h₂ h φ)) ?_).symm
  change CategoryTheory.inv (restrict hp h₁ h₂ h φ).1 ≫ Y₁.map h =
    Y₂.map h ≫ CategoryTheory.inv φ.1
  rw [← cancel_epi (restrict hp h₁ h₂ h φ).1, IsIso.hom_inv_id_assoc,
    ← Category.assoc, restrict_fac hp h₁ h₂ h φ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The presheaf of vertical morphisms is isomorphic to the one with the two families
interchanged.** The components invert, which is compatible with restriction by
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.restrict_symmVal`. -/
noncomputable def presheafSymmIso : presheaf hp h₁ h₂ ≅ presheaf hp h₂ h₁ :=
  NatIso.ofComponents
    (fun a => Equiv.toIso
      { toFun := symmVal hp
        invFun := symmVal hp
        left_inv := fun φ => by
          have := isIso_val hp φ
          apply Subtype.ext
          change CategoryTheory.inv (CategoryTheory.inv φ.1) = φ.1
          simp
        right_inv := fun φ => by
          have := isIso_val hp φ
          apply Subtype.ext
          change CategoryTheory.inv (CategoryTheory.inv φ.1) = φ.1
          simp })
    (by
      intro a a' f
      ext φ
      exact (restrict_symmVal hp h₁ h₂ f.unop φ).symm)

end Symm

end CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

end
