module

public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDescDense

/-!
# Naturality of morphisms out of a tensor product of sheaves of modules

A natural family of bilinear maps `β_U : F(U) × G(U) → H(U)` defines a morphism
`CategoryTheory.Sheaf.tensorDesc β : F ⊗ G ⟶ H` of sheaves of modules. Precomposing it with
`f ▷ G` for `f : F' ⟶ F` (resp. with `F ◁ g` for `g : G' ⟶ G`) gives the morphism of the
family `β_U ∘ (f_U × 1)` (resp. `β_U ∘ (1 × g_U)`)
(`CategoryTheory.Sheaf.whiskerRight_tensorDesc`, `CategoryTheory.Sheaf.whiskerLeft_tensorDesc`).
A natural family of bilinear maps on a site which restricts on a dense subsite to a given family
is the extension of that family (`CategoryTheory.Sheaf.denseExtensionBilinear_eq`).

These are the tools for the adjointness of morphisms of sheaves for a pairing defined on
sections, used for the intertwiners of a representation and of its contragredient for the
coefficient pairing of Poincaré duality in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `CategoryTheory.Sheaf.whiskerRight_tensorDesc`, `CategoryTheory.Sheaf.whiskerLeft_tensorDesc`.
* `CategoryTheory.Sheaf.denseExtensionBilinear_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe w v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Sheaf

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] {R : Type u} [CommRing R]

/-- **Precomposing a morphism out of the sectionwise tensor product with `f ▷ G`.** -/
theorem whiskerRight_presheafTensorDesc {F F' G H : Cᵒᵖ ⥤ ModuleCat.{max w u} R} (f : F' ⟶ F)
    (β : ∀ U, F.obj U →ₗ[R] G.obj U →ₗ[R] H.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (g : U ⟶ V) (a : F.obj U) (b : G.obj U),
      H.map g (β U a b) = β V (F.map g a) (G.map g b)) :
    f ▷ G ≫ presheafTensorDesc β hβ =
      presheafTensorDesc (fun U => (β U).comp (f.app U).hom) (fun {U V} g a b =>
        (hβ g ((f.app U).hom a) b).trans
          (congrArg (fun z => β V z (G.map g b))
            (ConcreteCategory.congr_hom (f.naturality g) a).symm)) := by
  ext U : 2
  exact ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

/-- **Precomposing a morphism out of the sectionwise tensor product with `F ◁ g`.** -/
theorem whiskerLeft_presheafTensorDesc {F G G' H : Cᵒᵖ ⥤ ModuleCat.{max w u} R} (g : G' ⟶ G)
    (β : ∀ U, F.obj U →ₗ[R] G.obj U →ₗ[R] H.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj U) (b : G.obj U),
      H.map f (β U a b) = β V (F.map f a) (G.map f b)) :
    F ◁ g ≫ presheafTensorDesc β hβ =
      presheafTensorDesc (fun U => (β U).compl₂ (g.app U).hom) (fun {U V} f a b =>
        (hβ f a ((g.app U).hom b)).trans
          (congrArg (fun z => β V (F.map f a) z)
            (ConcreteCategory.congr_hom (g.naturality f) b).symm)) := by
  ext U : 2
  exact ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

end Presheaf

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type u} [CommRing R]

attribute [local instance] monoidalCategory

variable [(J.W (A := ModuleCat.{max w u} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{max w u} R)]

/-- **Precomposing `tensorDesc β` with `f ▷ G`** gives `tensorDesc` of `β ∘ (f × 1)`. -/
theorem whiskerRight_tensorDesc {F F' G H : Sheaf J (ModuleCat.{max w u} R)} (f : F' ⟶ F)
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (g : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map g (β U a b) = β V (F.obj.map g a) (G.obj.map g b)) :
    f ▷ G ≫ tensorDesc β hβ =
      tensorDesc (fun U => (β U).comp (f.hom.app U).hom) (fun {U V} g a b =>
        (hβ g ((f.hom.app U).hom a) b).trans
          (congrArg (fun z => β V z (G.obj.map g b))
            (ConcreteCategory.congr_hom (f.hom.naturality g) a).symm)) := by
  let L := presheafToSheaf J (ModuleCat.{max w u} R)
  have hs : f ≫ (sheafificationIso F).hom = (sheafificationIso F').hom ≫ L.map f.hom :=
    (sheafificationNatIso J (ModuleCat.{max w u} R)).hom.naturality f
  have h₁ : f ▷ G ≫ (sheafificationIso F ⊗ᵢ sheafificationIso G).hom =
      (sheafificationIso F' ⊗ᵢ sheafificationIso G).hom ≫ L.map f.hom ▷ L.obj G.obj := by
    rw [tensorIso_hom, tensorIso_hom, ← tensorHom_id, tensorHom_comp_tensorHom, hs,
      Category.id_comp, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have h₂ : L.map f.hom ▷ L.obj G.obj ≫
      (Functor.Monoidal.μIso L F.obj G.obj).hom =
      (Functor.Monoidal.μIso L F'.obj G.obj).hom ≫ L.map (f.hom ▷ G.obj) :=
    Functor.LaxMonoidal.μ_natural_left L f.hom G.obj
  simp only [tensorDesc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Adjunction.homEquiv_naturality_left_symm,
    whiskerRight_presheafTensorDesc]

/-- **Precomposing `tensorDesc β` with `F ◁ g`** gives `tensorDesc` of `β ∘ (1 × g)`. -/
theorem whiskerLeft_tensorDesc {F G G' H : Sheaf J (ModuleCat.{max w u} R)} (g : G' ⟶ G)
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) :
    F ◁ g ≫ tensorDesc β hβ =
      tensorDesc (fun U => (β U).compl₂ (g.hom.app U).hom) (fun {U V} f a b =>
        (hβ f a ((g.hom.app U).hom b)).trans
          (congrArg (fun z => β V (F.obj.map f a) z)
            (ConcreteCategory.congr_hom (g.hom.naturality f) b).symm)) := by
  let L := presheafToSheaf J (ModuleCat.{max w u} R)
  have hs : g ≫ (sheafificationIso G).hom = (sheafificationIso G').hom ≫ L.map g.hom :=
    (sheafificationNatIso J (ModuleCat.{max w u} R)).hom.naturality g
  have h₁ : F ◁ g ≫ (sheafificationIso F ⊗ᵢ sheafificationIso G).hom =
      (sheafificationIso F ⊗ᵢ sheafificationIso G').hom ≫ L.obj F.obj ◁ L.map g.hom := by
    rw [tensorIso_hom, tensorIso_hom, ← id_tensorHom, tensorHom_comp_tensorHom, hs,
      Category.id_comp, ← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  have h₂ : L.obj F.obj ◁ L.map g.hom ≫
      (Functor.Monoidal.μIso L F.obj G.obj).hom =
      (Functor.Monoidal.μIso L F.obj G'.obj).hom ≫ L.map (F.obj ◁ g.hom) :=
    Functor.LaxMonoidal.μ_natural_right L F.obj g.hom
  simp only [tensorDesc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Adjunction.homEquiv_naturality_left_symm,
    whiskerLeft_presheafTensorDesc]

end Sheaf

section Dense

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  {K : GrothendieckTopology D} [G.IsCoverDense K] [G.IsLocallyFull K]
  {R : Type u} [CommRing R] {F₁ F₂ : Dᵒᵖ ⥤ ModuleCat.{max w u} R}
  {H : Sheaf K (ModuleCat.{max w u} R)}
  (β : ∀ U : Cᵒᵖ, F₁.obj (G.op.obj U) →ₗ[R] F₂.obj (G.op.obj U) →ₗ[R] H.obj.obj (G.op.obj U))
  (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F₁.obj (G.op.obj U)) (b : F₂.obj (G.op.obj U)),
    H.obj.map (G.op.map f) (β U a b) = β V (F₁.map (G.op.map f) a) (F₂.map (G.op.map f) b))

/-- **Uniqueness of the extension of bilinear maps from a dense subsite**: a natural family of
bilinear maps on `D` which is `β` on the image of `G` is `denseExtensionBilinear G β`. -/
theorem denseExtensionBilinear_eq
    (β' : ∀ V : Dᵒᵖ, F₁.obj V →ₗ[R] F₂.obj V →ₗ[R] H.obj.obj V)
    (hβ' : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (a : F₁.obj V) (b : F₂.obj V),
      H.obj.map f (β' V a b) = β' W (F₁.map f a) (F₂.map f b))
    (h : ∀ (U : Cᵒᵖ) (a : F₁.obj (G.op.obj U)) (b : F₂.obj (G.op.obj U)),
      β' (G.op.obj U) a b = β U a b) (V : Dᵒᵖ) :
    denseExtensionBilinear G β hβ V = β' V := by
  have h₂ : presheafTensorDesc (F := G.op ⋙ F₁) (G := G.op ⋙ F₂) (H := G.op ⋙ H.obj) β hβ =
      Functor.whiskerLeft G.op (presheafTensorDesc β' hβ') := by
    ext U : 2
    exact ModuleCat.hom_ext (TensorProduct.ext' fun a b => (h U a b).symm)
  have h₃ : denseExtensionTensorHom G β hβ = presheafTensorDesc β' hβ' := by
    change Functor.IsCoverDense.sheafHom (G := G) (K := K) (ℱ := F₁ ⊗ F₂) (ℱ' := H) _ = _
    rw [h₂]
    exact Functor.IsCoverDense.sheafHom_eq _ _
  ext a b
  rw [denseExtensionBilinear_apply', h₃]
  rfl

end Dense

end CategoryTheory.Sheaf
