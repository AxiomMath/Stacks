module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.InverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsComp
public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheafHomEvaluation

/-!
# Inverse image commutes with restriction of scalars, monoidally

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `f : X ⟶ Y` a morphism of schemes.
Restriction of scalars `res_ρ` of étale sheaves of modules is lax monoidal: the morphism
`res_ρ A ⊗_Λ res_ρ B ⟶ res_ρ (A ⊗_{Λ'} B)` sends `a ⊗ b` to `a ⊗ b`
(`Stacks.EtaleCohomology.etaleModuleRestrictScalarsTensorHom`). The comparison
`κ : f⁻¹ ∘ res_ρ ≅ res_ρ ∘ f⁻¹` (`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictScalars`)
is compatible with it and with the monoidal structures of the inverse images
(`Stacks.EtaleCohomology.etaleModuleInverseImageMonoidal`):
`μ ≫ f⁻¹(res_ρ A ⊗ res_ρ B ⟶ res_ρ(A ⊗ B)) ≫ κ =`
`(κ ⊗ κ) ≫ (res_ρ f⁻¹A ⊗ res_ρ f⁻¹B ⟶ res_ρ(f⁻¹A ⊗ f⁻¹B)) ≫ res_ρ μ`
(`Stacks.EtaleCohomology.μ_comp_map_restrictScalarsTensorHom_comp_inverseImageRestrictScalars`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleRestrictScalarsTensorHom`: the lax structure
  `res_ρ A ⊗_Λ res_ρ B ⟶ res_ρ (A ⊗_{Λ'} B)` of restriction of scalars.

## Main results

* `Stacks.EtaleCohomology.tensorHom_comp_etaleModuleRestrictScalarsTensorHom`: naturality.
* `Stacks.EtaleCohomology.μ_directImage_comp_map_restrictScalarsTensorHom`: compatibility with the
  lax structure of the direct image.
* `Stacks.EtaleCohomology.μ_comp_map_restrictScalarsTensorHom_comp_inverseImageRestrictScalars`:
  compatibility of `κ` with the monoidal structures of the inverse images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

namespace Stacks.EtaleCohomology

/-! ### Morphisms out of a tensor product of sheaves of modules, on pure tensors -/

section Bilinear

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]

attribute [local instance] Sheaf.monoidalCategory

variable [(J.W (A := ModuleCat.{u + 1} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{u + 1} R)]

/-- The bilinear components of `CategoryTheory.Sheaf.tensorDesc β` are `β`. -/
theorem sheafTensorBilinear_tensorDesc {F G H : Sheaf J (ModuleCat.{u + 1} R)}
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) (U : Cᵒᵖ)
    (a : F.obj.obj U) (c : G.obj.obj U) :
    Sheaf.tensorBilinear (Sheaf.tensorDesc.{u + 1, u, u + 1, 0} β hβ) U a c = β U a c := by
  rw [Sheaf.tensorBilinear_apply, Sheaf.tensorPresheafComponent_tensorDesc]
  rfl

/-- The bilinear components of a composite `b ≫ w` are those of `b` followed by `w`. -/
theorem sheafTensorBilinear_comp {F G H H' : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H)
    (w : H ⟶ H') (U : Cᵒᵖ) (a : F.obj.obj U) (c : G.obj.obj U) :
    Sheaf.tensorBilinear (b ≫ w) U a c = (w.hom.app U).hom (Sheaf.tensorBilinear b U a c) := by
  rw [Sheaf.tensorBilinear_apply, Sheaf.tensorBilinear_apply, Sheaf.tensorPresheafComponent_comp]
  rfl

/-- **Two morphisms out of a tensor product of sheaves of modules agree as soon as they agree on
pure tensors of sections.** -/
theorem sheafTensor_hom_ext {F G H : Sheaf J (ModuleCat.{u + 1} R)} {b b' : F ⊗ G ⟶ H}
    (h : ∀ U a c, Sheaf.tensorBilinear b U a c = Sheaf.tensorBilinear b' U a c) : b = b' := by
  rw [Sheaf.eq_tensorDesc b, Sheaf.eq_tensorDesc b']
  exact Sheaf.tensorDesc_congr _ _ h

/-- The bilinear components of `F ◁ g ≫ b` are those of `b` precomposed with `g`. -/
theorem sheafTensorBilinear_whiskerLeft_comp {F G G' H : Sheaf J (ModuleCat.{u + 1} R)}
    (g : G' ⟶ G) (b : F ⊗ G ⟶ H) (U : Cᵒᵖ) (a : F.obj.obj U) (c : G'.obj.obj U) :
    Sheaf.tensorBilinear (F ◁ g ≫ b) U a c =
      Sheaf.tensorBilinear b U a ((g.hom.app U).hom c) :=
  (congrArg (fun t ↦ Sheaf.tensorBilinear (F ◁ g ≫ t) U a c) (Sheaf.eq_tensorDesc b)).trans
    ((congrArg (fun t ↦ Sheaf.tensorBilinear t U a c) (Sheaf.whiskerLeft_tensorDesc g _ _)).trans
      (sheafTensorBilinear_tensorDesc _ _ U a c))

/-- The bilinear components of `f ▷ G ≫ b` are those of `b` precomposed with `f`. -/
theorem sheafTensorBilinear_whiskerRight_comp {F F' G H : Sheaf J (ModuleCat.{u + 1} R)}
    (f : F' ⟶ F) (b : F ⊗ G ⟶ H) (U : Cᵒᵖ) (a : F'.obj.obj U) (c : G.obj.obj U) :
    Sheaf.tensorBilinear (f ▷ G ≫ b) U a c =
      Sheaf.tensorBilinear b U ((f.hom.app U).hom a) c :=
  (congrArg (fun t ↦ Sheaf.tensorBilinear (f ▷ G ≫ t) U a c) (Sheaf.eq_tensorDesc b)).trans
    ((congrArg (fun t ↦ Sheaf.tensorBilinear t U a c) (Sheaf.whiskerRight_tensorDesc f _ _)).trans
      (sheafTensorBilinear_tensorDesc _ _ U a c))

/-- The bilinear components of `(f ⊗ g) ≫ b` are those of `b` precomposed with `f` and `g`. -/
theorem sheafTensorBilinear_tensorHom_comp {F F' G G' H : Sheaf J (ModuleCat.{u + 1} R)}
    (f : F' ⟶ F) (g : G' ⟶ G) (b : F ⊗ G ⟶ H) (U : Cᵒᵖ) (a : F'.obj.obj U)
    (c : G'.obj.obj U) :
    Sheaf.tensorBilinear ((f ⊗ₘ g) ≫ b) U a c =
      Sheaf.tensorBilinear b U ((f.hom.app U).hom a) ((g.hom.app U).hom c) :=
  (congrArg (fun t ↦ Sheaf.tensorBilinear t U a c)
    ((congrArg (· ≫ b) (MonoidalCategory.tensorHom_def f g)).trans (Category.assoc _ _ _))).trans
    ((sheafTensorBilinear_whiskerRight_comp f _ U a c).trans
      (sheafTensorBilinear_whiskerLeft_comp g b U _ c))

/-- The bilinear components of any morphism out of a tensor product are its values on the pure
tensors `Sheaf.tensorBilinear (𝟙 _)`. -/
theorem sheafTensorBilinear_eq_app {F G H : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H)
    (U : Cᵒᵖ) (a : F.obj.obj U) (c : G.obj.obj U) :
    Sheaf.tensorBilinear b U a c =
      (b.hom.app U).hom (Sheaf.tensorBilinear (𝟙 (F ⊗ G)) U a c) := by
  rw [← sheafTensorBilinear_comp, Category.id_comp]

/-- A morphism of tensor products on a pure tensor of sections. -/
theorem sheafTensorHom_app_tensorBilinear_id {F F' G G' : Sheaf J (ModuleCat.{u + 1} R)}
    (f : F ⟶ F') (g : G ⟶ G') (U : Cᵒᵖ) (a : F.obj.obj U) (c : G.obj.obj U) :
    ((f ⊗ₘ g).hom.app U).hom (Sheaf.tensorBilinear (𝟙 (F ⊗ G)) U a c) =
      Sheaf.tensorBilinear (𝟙 (F' ⊗ G')) U ((f.hom.app U).hom a) ((g.hom.app U).hom c) := by
  rw [← sheafTensorBilinear_comp, Category.id_comp, ← Category.comp_id (f ⊗ₘ g),
    sheafTensorBilinear_tensorHom_comp]

/-- The tensorator of the forgetful functor from sheaves to presheaves is the presheaf component
of the identity of the tensor product. -/
theorem μ_sheafToPresheaf_eq_tensorPresheafComponent (F G : Sheaf J (ModuleCat.{u + 1} R)) :
    letI := Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal J (ModuleCat.{u + 1} R)
    μ (sheafToPresheaf J (ModuleCat.{u + 1} R)) F G =
      Sheaf.tensorPresheafComponent (𝟙 (F ⊗ G)) := by
  let := Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal J (ModuleCat.{u + 1} R)
  have hP : ∀ P : Sheaf J (ModuleCat.{u + 1} R), (sheafificationIso P).hom ≫
      (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit.app P = 𝟙 P := fun P ↦
    Sheaf.hom_ext ((sheafificationAdjunction J (ModuleCat.{u + 1} R)).right_triangle_components P)
  have hiso : (Sheaf.tensorIsoSheafifyTensor F G).inv =
      (Stacks.SheafPushforwardMonoidal.sheafifyTensorIso J (ModuleCat.{u + 1} R) F G).hom := by
    rw [← cancel_epi (Sheaf.tensorIsoSheafifyTensor F G).hom, Iso.hom_inv_id]
    change 𝟙 _ = ((sheafificationIso F).hom ⊗ₘ (sheafificationIso G).hom) ≫
      (Functor.Monoidal.μIso (presheafToSheaf J (ModuleCat.{u + 1} R)) F.obj G.obj).hom ≫
        (Functor.Monoidal.μIso (presheafToSheaf J (ModuleCat.{u + 1} R)) F.obj G.obj).inv ≫
          ((sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit.app F ⊗ₘ
            (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit.app G)
    rw [Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom, hP, hP, id_tensorHom_id]
  rw [Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf, Sheaf.tensorPresheafComponent,
    Category.comp_id, hiso]
  rfl

/-- The tensorator of the forgetful functor on a pure tensor of sections. -/
theorem μ_sheafToPresheaf_app_tmul (F G : Sheaf J (ModuleCat.{u + 1} R)) (U : Cᵒᵖ)
    (a : F.obj.obj U) (c : G.obj.obj U) :
    letI := Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal J (ModuleCat.{u + 1} R)
    ((μ (sheafToPresheaf J (ModuleCat.{u + 1} R)) F G).app U).hom (a ⊗ₜ c) =
      Sheaf.tensorBilinear (𝟙 (F ⊗ G)) U a c := by
  rw [μ_sheafToPresheaf_eq_tensorPresheafComponent]
  rfl

end Bilinear

/-! ### Restriction of scalars is lax monoidal -/

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

section RestrictScalars

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}

/-- The pure tensors `a ⊗ b` of `A ⊗_{Λ'} B`, as a `Λ`-bilinear map of the restricted
sections. -/
def etaleModuleRestrictScalarsTensorBilinear (A B : EtaleModules.{u, 0} Λ' X) (U : X.Etaleᵒᵖ) :
    ((etaleModuleRestrictScalars ρ X).obj A).obj.obj U →ₗ[Λ]
      ((etaleModuleRestrictScalars ρ X).obj B).obj.obj U →ₗ[Λ]
        ((etaleModuleRestrictScalars ρ X).obj (A ⊗ B)).obj.obj U :=
  LinearMap.mk₂ Λ (fun a c ↦ Sheaf.tensorBilinear (𝟙 (A ⊗ B)) U a c)
    (fun a a' c ↦ (Sheaf.tensorBilinear (𝟙 (A ⊗ B)) U).map_add₂ a a' c)
    (fun r a c ↦ (Sheaf.tensorBilinear (𝟙 (A ⊗ B)) U).map_smul₂ (ρ r) a c)
    (fun a c c' ↦ (Sheaf.tensorBilinear (𝟙 (A ⊗ B)) U a).map_add c c')
    (fun r a c ↦ (Sheaf.tensorBilinear (𝟙 (A ⊗ B)) U a).map_smul (ρ r) c)

/-- **The lax structure of restriction of scalars**:
`res_ρ A ⊗_Λ res_ρ B ⟶ res_ρ (A ⊗_{Λ'} B)`, `a ⊗ b ↦ a ⊗ b`. -/
def etaleModuleRestrictScalarsTensorHom (A B : EtaleModules.{u, 0} Λ' X) :
    (etaleModuleRestrictScalars ρ X).obj A ⊗ (etaleModuleRestrictScalars ρ X).obj B ⟶
      (etaleModuleRestrictScalars ρ X).obj (A ⊗ B) :=
  Sheaf.tensorDesc.{u + 1, u, u + 1, 0} (etaleModuleRestrictScalarsTensorBilinear ρ A B)
    (fun f a c ↦ Sheaf.tensorBilinear_naturality (𝟙 (A ⊗ B)) f a c)

/-- The lax structure of restriction of scalars sends the pure tensor `a ⊗ b` to `a ⊗ b`. -/
theorem tensorBilinear_etaleModuleRestrictScalarsTensorHom (A B : EtaleModules.{u, 0} Λ' X)
    (U : X.Etaleᵒᵖ) (a : ((etaleModuleRestrictScalars ρ X).obj A).obj.obj U)
    (c : ((etaleModuleRestrictScalars ρ X).obj B).obj.obj U) :
    Sheaf.tensorBilinear (etaleModuleRestrictScalarsTensorHom ρ A B) U a c =
      Sheaf.tensorBilinear (𝟙 (A ⊗ B)) U a c :=
  sheafTensorBilinear_tensorDesc (etaleModuleRestrictScalarsTensorBilinear ρ A B)
    (fun f a c ↦ Sheaf.tensorBilinear_naturality (𝟙 (A ⊗ B)) f a c) U a c

/-- Postcomposing the lax structure of restriction of scalars with `res_ρ g` applies `g` to the
pure tensor `a ⊗ b`. -/
private theorem tensorBilinear_restrictScalarsTensorHom_comp_map {A B C : EtaleModules.{u, 0} Λ' X}
    (g : A ⊗ B ⟶ C) (U : X.Etaleᵒᵖ) (a : ((etaleModuleRestrictScalars ρ X).obj A).obj.obj U)
    (c : ((etaleModuleRestrictScalars ρ X).obj B).obj.obj U) :
    Sheaf.tensorBilinear (etaleModuleRestrictScalarsTensorHom ρ A B ≫
      (etaleModuleRestrictScalars ρ X).map g) U a c =
      (g.hom.app U).hom (Sheaf.tensorBilinear (𝟙 (A ⊗ B)) U a c) :=
  (sheafTensorBilinear_comp _ _ U a c).trans
    (congrArg (g.hom.app U).hom (tensorBilinear_etaleModuleRestrictScalarsTensorHom ρ A B U a c))

/-- **The lax structure of restriction of scalars is natural.** -/
theorem tensorHom_comp_etaleModuleRestrictScalarsTensorHom {A A' B B' : EtaleModules.{u, 0} Λ' X}
    (φ : A ⟶ A') (ψ : B ⟶ B') :
    ((etaleModuleRestrictScalars ρ X).map φ ⊗ₘ (etaleModuleRestrictScalars ρ X).map ψ) ≫
        etaleModuleRestrictScalarsTensorHom ρ A' B' =
      etaleModuleRestrictScalarsTensorHom ρ A B ≫
        (etaleModuleRestrictScalars ρ X).map (φ ⊗ₘ ψ) := by
  refine sheafTensor_hom_ext fun U a c ↦ ?_
  have h₁ : Sheaf.tensorBilinear (((etaleModuleRestrictScalars ρ X).map φ ⊗ₘ
      (etaleModuleRestrictScalars ρ X).map ψ) ≫ etaleModuleRestrictScalarsTensorHom ρ A' B') U a c =
      Sheaf.tensorBilinear (𝟙 (A' ⊗ B')) U ((φ.hom.app U).hom a) ((ψ.hom.app U).hom c) :=
    (sheafTensorBilinear_tensorHom_comp _ _ _ U a c).trans
      (tensorBilinear_etaleModuleRestrictScalarsTensorHom ρ A' B' U _ _)
  exact h₁.trans ((sheafTensorHom_app_tensorBilinear_id φ ψ U a c).symm.trans
    (tensorBilinear_restrictScalarsTensorHom_comp_map ρ (φ ⊗ₘ ψ) U a c).symm)

end RestrictScalars

/-! ### Compatibility with direct and inverse image -/

attribute [local instance] etaleModuleDirectImageLaxMonoidal etaleModuleInverseImageMonoidal

section Image

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The tensorator of the direct image on pure tensors: `a ⊗ b ↦ a ⊗ b`. -/
theorem tensorBilinear_μ_etaleModuleDirectImage {Λ : Type} [CommRing Λ]
    (A B : EtaleModules.{u, 0} Λ X) (U : Y.Etaleᵒᵖ)
    (a : ((etaleModuleDirectImage.{u, 0} Λ f).obj A).obj.obj U)
    (c : ((etaleModuleDirectImage.{u, 0} Λ f).obj B).obj.obj U) :
    Sheaf.tensorBilinear (μ (etaleModuleDirectImage.{u, 0} Λ f) A B) U a c =
      Sheaf.tensorBilinear (𝟙 (A ⊗ B)) ((smallEtaleBaseChange f).op.obj U) a c := by
  let := Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)
  let := Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)
  have h := Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf_comp_map_μ_pushforward
    Y.smallEtaleTopology X.smallEtaleTopology (ModuleCat.{u + 1} Λ) (smallEtaleBaseChange f) A B
  have h' := ConcreteCategory.congr_hom (NatTrans.congr_app h U) (a ⊗ₜ c)
  refine (sheafTensorBilinear_eq_app _ U a c).trans ?_
  refine (congrArg ((μ (etaleModuleDirectImage.{u, 0} Λ f) A B).hom.app U).hom
    (μ_sheafToPresheaf_app_tmul _ _ U a c).symm).trans ?_
  exact h'.trans (μ_sheafToPresheaf_app_tmul A B _ a c)

/-- **The lax structure of the direct image commutes with that of restriction of scalars.** -/
theorem μ_directImage_comp_map_restrictScalarsTensorHom (A B : EtaleModules.{u, 0} Λ' X) :
    μ (etaleModuleDirectImage.{u, 0} Λ f) ((etaleModuleRestrictScalars ρ X).obj A)
        ((etaleModuleRestrictScalars ρ X).obj B) ≫
      (etaleModuleDirectImage.{u, 0} Λ f).map (etaleModuleRestrictScalarsTensorHom ρ A B) =
    etaleModuleRestrictScalarsTensorHom ρ ((etaleModuleDirectImage.{u, 0} Λ' f).obj A)
        ((etaleModuleDirectImage.{u, 0} Λ' f).obj B) ≫
      (etaleModuleRestrictScalars ρ Y).map (μ (etaleModuleDirectImage.{u, 0} Λ' f) A B) := by
  refine sheafTensor_hom_ext fun U a c ↦ ?_
  refine (sheafTensorBilinear_comp _ _ U a c).trans ?_
  refine Eq.trans ?_ (sheafTensorBilinear_comp _ _ U a c).symm
  refine (congrArg ((etaleModuleRestrictScalarsTensorHom ρ A B).hom.app _).hom
    (tensorBilinear_μ_etaleModuleDirectImage f _ _ U a c)).trans ?_
  refine (sheafTensorBilinear_eq_app (etaleModuleRestrictScalarsTensorHom ρ A B)
    ((smallEtaleBaseChange f).op.obj U) a c).symm.trans ?_
  refine (tensorBilinear_etaleModuleRestrictScalarsTensorHom ρ A B _ a c).trans ?_
  refine Eq.trans ?_ (tensorBilinear_restrictScalarsTensorHom_comp_map ρ
    (μ (etaleModuleDirectImage.{u, 0} Λ' f) A B) U a c).symm
  refine Eq.trans ?_ (sheafTensorBilinear_eq_app (μ (etaleModuleDirectImage.{u, 0} Λ' f) A B) U a c)
  exact (tensorBilinear_μ_etaleModuleDirectImage f A B U a c).symm

/-- **The comparison `f⁻¹ ∘ res_ρ ≅ res_ρ ∘ f⁻¹` is monoidal**, in the oplax form:
`f⁻¹(res A ⊗ res B ⟶ res(A ⊗ B)) ≫ κ ≫ res δ =`
`δ ≫ (κ ⊗ κ) ≫ (res f⁻¹A ⊗ res f⁻¹B ⟶ res(f⁻¹A ⊗ f⁻¹B))`. -/
theorem map_restrictScalarsTensorHom_comp_inverseImageRestrictScalars_δ
    (A B : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleInverseImage.{u, 0} Λ f).map (etaleModuleRestrictScalarsTensorHom ρ A B) ≫
        (etaleModuleInverseImageRestrictScalars ρ f).hom.app (A ⊗ B) ≫
        (etaleModuleRestrictScalars ρ X).map (δ (etaleModuleInverseImage.{u, 0} Λ' f) A B) =
      δ (etaleModuleInverseImage.{u, 0} Λ f) ((etaleModuleRestrictScalars ρ Y).obj A)
          ((etaleModuleRestrictScalars ρ Y).obj B) ≫
        ((etaleModuleInverseImageRestrictScalars ρ f).hom.app A ⊗ₘ
          (etaleModuleInverseImageRestrictScalars ρ f).hom.app B) ≫
        etaleModuleRestrictScalarsTensorHom ρ ((etaleModuleInverseImage.{u, 0} Λ' f).obj A)
          ((etaleModuleInverseImage.{u, 0} Λ' f).obj B) := by
  let adj := etaleModuleInverseImageAdj.{u, 0} Λ f
  let adj' := etaleModuleInverseImageAdj.{u, 0} Λ' f
  let R' := etaleModuleRestrictScalars ρ Y
  have hu := fun G ↦ etaleModuleInverseImageRestrictScalars_unit ρ f G
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hL : adj.unit.app (R'.obj A ⊗ R'.obj B) ≫
      (etaleModuleDirectImage.{u, 0} Λ f).map
        ((etaleModuleInverseImage.{u, 0} Λ f).map (etaleModuleRestrictScalarsTensorHom ρ A B)) =
      etaleModuleRestrictScalarsTensorHom ρ A B ≫ adj.unit.app (R'.obj (A ⊗ B)) :=
    (adj.unit.naturality (etaleModuleRestrictScalarsTensorHom ρ A B)).symm
  rw [reassoc_of% hL, reassoc_of% (hu (A ⊗ B))]
  have hδ' := Adjunction.unit_app_tensor_comp_map_δ adj' A B
  have hδ := Adjunction.unit_app_tensor_comp_map_δ adj (R'.obj A) (R'.obj B)
  rw [reassoc_of% hδ]
  change etaleModuleRestrictScalarsTensorHom ρ A B ≫
      R'.map (adj'.unit.app (A ⊗ B) ≫
        (etaleModuleDirectImage.{u, 0} Λ' f).map (δ (etaleModuleInverseImage.{u, 0} Λ' f) A B)) = _
  rw [hδ', ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, hu A, hu B]
  simp only [Functor.comp_obj]
  rw [μ_directImage_comp_map_restrictScalarsTensorHom]
  exact (congrArg (etaleModuleRestrictScalarsTensorHom ρ A B ≫ ·)
    ((etaleModuleRestrictScalars ρ Y).map_comp _ _)).trans
    ((reassoc_of% (tensorHom_comp_etaleModuleRestrictScalarsTensorHom ρ
      (adj'.unit.app A) (adj'.unit.app B))) _).symm

/-- **The comparison `f⁻¹ ∘ res_ρ ≅ res_ρ ∘ f⁻¹` is monoidal**:
`μ ≫ f⁻¹(res A ⊗ res B ⟶ res(A ⊗ B)) ≫ κ =`
`(κ ⊗ κ) ≫ (res f⁻¹A ⊗ res f⁻¹B ⟶ res(f⁻¹A ⊗ f⁻¹B)) ≫ res μ`. -/
theorem μ_comp_map_restrictScalarsTensorHom_comp_inverseImageRestrictScalars
    (A B : EtaleModules.{u, 0} Λ' Y) :
    μ (etaleModuleInverseImage.{u, 0} Λ f) ((etaleModuleRestrictScalars ρ Y).obj A)
          ((etaleModuleRestrictScalars ρ Y).obj B) ≫
        (etaleModuleInverseImage.{u, 0} Λ f).map (etaleModuleRestrictScalarsTensorHom ρ A B) ≫
        (etaleModuleInverseImageRestrictScalars ρ f).hom.app (A ⊗ B) =
      ((etaleModuleInverseImageRestrictScalars ρ f).hom.app A ⊗ₘ
          (etaleModuleInverseImageRestrictScalars ρ f).hom.app B) ≫
        etaleModuleRestrictScalarsTensorHom ρ ((etaleModuleInverseImage.{u, 0} Λ' f).obj A)
          ((etaleModuleInverseImage.{u, 0} Λ' f).obj B) ≫
        (etaleModuleRestrictScalars ρ X).map (μ (etaleModuleInverseImage.{u, 0} Λ' f) A B) := by
  have h := congrArg (fun t ↦ μ (etaleModuleInverseImage.{u, 0} Λ f)
      ((etaleModuleRestrictScalars ρ Y).obj A) ((etaleModuleRestrictScalars ρ Y).obj B) ≫ t ≫
      (etaleModuleRestrictScalars ρ X).map (μ (etaleModuleInverseImage.{u, 0} Λ' f) A B))
    (map_restrictScalarsTensorHom_comp_inverseImageRestrictScalars_δ ρ f A B)
  simp only [Category.assoc, ← Functor.map_comp, Functor.Monoidal.δ_μ,
    Functor.Monoidal.μ_δ_assoc] at h
  exact h

end Image

end Stacks.EtaleCohomology

end
