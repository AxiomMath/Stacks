module

public import StacksFrontier.CategoryTheory.Sites.SheafPullbackMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ConjugateEquivMonoidal

/-!
# The direct image of sheaves is lax monoidal, read on presheaves

Let `G : C ⥤ D` be a continuous functor of sites for which the inverse image `G⁻¹` is monoidal
(`CategoryTheory.Functor.sheafPullbackMonoidal`). Its right adjoint, the direct image
`G_* : Sheaf K A ⥤ Sheaf J A`, is then lax monoidal
(`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`), and so is the inclusion of sheaves into
presheaves, right adjoint to the monoidal sheafification. On presheaves the direct image is
precomposition with `G.op`, which is strictly monoidal for the pointwise tensor products. This file
shows that the two lax structures on
`G_* ⋙ (sheaves ⊆ presheaves) = (sheaves ⊆ presheaves) ⋙ (G.op ⋙ -)` agree
(`CategoryTheory.Functor.sheafToPresheaf_μ_comp_map_sheafPushforwardContinuous_μ`): the
tensorator of `G_*`, read on presheaves, is the tensorator of the inclusion precomposed with
`G.op`. Morphisms out of a tensor product of sheaves are determined by their presheaf reading
(`CategoryTheory.Functor.sheafToPresheaf_μ_cancel`), so this describes the tensorator of `G_*`
completely.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open Limits MonoidalCategory Opposite LaxMonoidal OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension G.op P]
  [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).obj M)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).flip.obj M)]

attribute [local instance] Sheaf.monoidalCategory lanMonoidal sheafPullbackMonoidal

/-- The inclusion of sheaves into presheaves is lax monoidal, as the right adjoint of the
monoidal sheafification. -/
@[instance_reducible]
def sheafToPresheafLaxMonoidal (L : GrothendieckTopology C) [HasWeakSheafify L A]
    [(L.W (A := A)).IsMonoidal] : (sheafToPresheaf L A).LaxMonoidal :=
  (sheafificationAdjunction L A).rightAdjointLaxMonoidal

/-- The direct image of sheaves is lax monoidal, as the right adjoint of the monoidal inverse
image. -/
@[instance_reducible]
def sheafPushforwardContinuousLaxMonoidal : (G.sheafPushforwardContinuous A J K).LaxMonoidal :=
  (G.sheafAdjunctionContinuous A J K).rightAdjointLaxMonoidal

attribute [local instance] sheafToPresheafLaxMonoidal sheafPushforwardContinuousLaxMonoidal

/-- The monoidal adjunction `L.lan ⊣ (L ⋙ -)`, for the oplax structure on the left Kan
extension obtained from the strict structure on precomposition. -/
lemma lanAdjunction_isMonoidal :
    (G.op.lanAdjunction A).IsMonoidal := by
  let := (G.op.lanAdjunction A).leftAdjointOplaxMonoidal
  have h : (G.op.lanAdjunction A).IsMonoidal := inferInstance
  exact ⟨h.leftAdjoint_ε, h.leftAdjoint_μ⟩

attribute [local instance] lanAdjunction_isMonoidal

/-- The identity of `G_* ⋙ (sheaves ⊆ presheaves) = (sheaves ⊆ presheaves) ⋙ (G.op ⋙ -)` is a
monoidal transformation between the two composite lax structures: it is the conjugate of the
monoidal comparison `a_J ⋙ G⁻¹ ≅ G.op.lan ⋙ a_K` of the left adjoints. -/
theorem isMonoidal_sheafPushforwardContinuous_comp_sheafToPresheaf :
    @NatTrans.IsMonoidal _ _ _ _ _ _ (G.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A)
      (sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op)
      (𝟙 (G.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A)) _ _ := by
  let adj₁ := (sheafificationAdjunction J A).comp (G.sheafAdjunctionContinuous A J K)
  let adj₂ := (G.op.lanAdjunction A).comp (sheafificationAdjunction K A)
  let e := presheafToSheafCompSheafPullbackIso G A J K
  let : Localization.Lifting (presheafToSheaf J A) J.W (G.op.lan ⋙ presheafToSheaf K A)
      (G.sheafPullback A J K) := ⟨e⟩
  have he : NatTrans.IsMonoidal e.hom :=
    Localization.Monoidal.lifting_isMonoidal (presheafToSheaf J A) J.W
      (G.sheafPullback A J K) (G.op.lan ⋙ presheafToSheaf K A)
  have hconj : conjugateEquiv adj₁ adj₂ e.inv = 𝟙 _ := by
    apply NatTrans.ext
    funext X
    apply (adj₂.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, conjugateEquiv_counit]
    have h := Adjunction.leftAdjointUniq_hom_app_counit
      (adj₂.ofNatIsoRight (Iso.refl _)) adj₁ X
    simp only [Adjunction.ofNatIsoRight] at h
    simp only [NatTrans.id_app]
    refine h.trans ?_
    simp only [Functor.comp_obj, Iso.refl_inv, whiskerRight_id', Category.id_comp]
    exact (Category.id_comp _).symm.trans (congrArg (· ≫ adj₂.counit.app X)
      ((G.op.lan ⋙ presheafToSheaf K A).map_id _).symm)
  have hm := Adjunction.isMonoidal_conjugateEquiv adj₁ adj₂ e.inv
    (NatTrans.IsMonoidal.app_unit_comp_η e.inv)
    (NatTrans.IsMonoidal.app_tensor_comp_δ e.inv)
  rw [hconj] at hm
  exact hm

/-- **The tensorator of the direct image of sheaves, read on presheaves**: it is the tensorator
of the inclusion of sheaves into presheaves, precomposed with `G.op`. -/
theorem sheafToPresheaf_μ_comp_map_sheafPushforwardContinuous_μ (X Y : Sheaf K A) :
    μ (sheafToPresheaf J A) ((G.sheafPushforwardContinuous A J K).obj X)
        ((G.sheafPushforwardContinuous A J K).obj Y) ≫
      (sheafToPresheaf J A).map (μ (G.sheafPushforwardContinuous A J K) X Y) =
      Functor.whiskerLeft G.op (μ (sheafToPresheaf K A) X Y) := by
  have := (isMonoidal_sheafPushforwardContinuous_comp_sheafToPresheaf G A J K).tensor X Y
  have hres : μ ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op) X.obj Y.obj = 𝟙 _ := rfl
  simp only [comp_μ, NatTrans.id_app] at this
  refine (Category.comp_id _).symm.trans (this.trans ?_)
  exact (congrArg (· ≫ _) (MonoidalCategory.id_tensorHom_id _ _)).trans
    ((Category.id_comp _).trans ((congrArg (· ≫ _) hres).trans (Category.id_comp _)))

/-- **The unit of the direct image of sheaves, read on presheaves**: it is the unit of the
inclusion of sheaves into presheaves, precomposed with `G.op`. -/
theorem sheafToPresheaf_ε_comp_map_sheafPushforwardContinuous_ε :
    ε (sheafToPresheaf J A) ≫
      (sheafToPresheaf J A).map (ε (G.sheafPushforwardContinuous A J K)) =
      Functor.whiskerLeft G.op (ε (sheafToPresheaf K A)) := by
  have := (isMonoidal_sheafPushforwardContinuous_comp_sheafToPresheaf G A J K).unit
  have hres : ε ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op) = 𝟙 _ := rfl
  simp only [comp_ε, NatTrans.id_app] at this
  refine (Category.comp_id _).symm.trans (this.trans ?_)
  exact (congrArg (· ≫ _) hres).trans (Category.id_comp _)

section Cancel

variable {C : Type*} [Category* C] (L : GrothendieckTopology C) {A : Type*} [Category* A]
  [MonoidalCategory A] [HasWeakSheafify L A] [(L.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory sheafToPresheafLaxMonoidal

/-- Morphisms out of a tensor product of sheaves are determined by their reading on presheaves
through the tensorator of the inclusion of sheaves into presheaves. -/
theorem sheafToPresheaf_μ_cancel {X Y Z : Sheaf L A} {f g : X ⊗ Y ⟶ Z}
    (h : μ (sheafToPresheaf L A) X Y ≫ (sheafToPresheaf L A).map f =
      μ (sheafToPresheaf L A) X Y ≫ (sheafToPresheaf L A).map g) : f = g := by
  let adj := sheafificationAdjunction L A
  have hμ : ∀ k : X ⊗ Y ⟶ Z, μ (sheafToPresheaf L A) X Y ≫ (sheafToPresheaf L A).map k =
      adj.homEquiv _ _ (δ (presheafToSheaf L A) _ _ ≫
        (adj.counit.app X ⊗ₘ adj.counit.app Y) ≫ k) := fun k => by
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rfl
  rw [hμ, hμ] at h
  have h' := (adj.homEquiv _ _).injective h
  rwa [cancel_epi, cancel_epi] at h'

/-- Morphisms out of the tensor unit of sheaves are determined by their reading on presheaves
through the unit of the inclusion of sheaves into presheaves. -/
theorem sheafToPresheaf_ε_cancel {Z : Sheaf L A} {f g : 𝟙_ (Sheaf L A) ⟶ Z}
    (h : ε (sheafToPresheaf L A) ≫ (sheafToPresheaf L A).map f =
      ε (sheafToPresheaf L A) ≫ (sheafToPresheaf L A).map g) : f = g := by
  let adj := sheafificationAdjunction L A
  have hε : ∀ k : 𝟙_ (Sheaf L A) ⟶ Z, ε (sheafToPresheaf L A) ≫ (sheafToPresheaf L A).map k =
      adj.homEquiv _ _ (η (presheafToSheaf L A) ≫ k) := fun k => by
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  rw [hε, hε] at h
  have h' := (adj.homEquiv _ _).injective h
  rwa [cancel_epi] at h'

/-- A natural transformation of lax monoidal functors into sheaves is monoidal as soon as it is
monoidal after the inclusion of sheaves into presheaves. -/
theorem isMonoidal_of_whiskerRight_sheafToPresheaf {E : Type*} [Category* E] [MonoidalCategory E]
    {R₁ R₂ : E ⥤ Sheaf L A} [R₁.LaxMonoidal] [R₂.LaxMonoidal] (α : R₁ ⟶ R₂)
    [NatTrans.IsMonoidal (Functor.whiskerRight α (sheafToPresheaf L A))] :
    NatTrans.IsMonoidal α where
  unit := by
    apply sheafToPresheaf_ε_cancel L
    have := NatTrans.IsMonoidal.unit (τ := Functor.whiskerRight α (sheafToPresheaf L A))
    simp only [comp_ε, Functor.whiskerRight_app, Category.assoc] at this
    rw [Functor.map_comp, this]
  tensor X Y := by
    apply sheafToPresheaf_μ_cancel L
    have := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerRight α (sheafToPresheaf L A)) X Y
    simp only [comp_μ, Functor.whiskerRight_app, Category.assoc] at this
    rw [Functor.map_comp, this, Functor.map_comp, μ_natural_assoc]

end Cancel

section Reading

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*} [Category* A]
  [MonoidalCategory A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E)
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify L A] [(L.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory sheafToPresheafLaxMonoidal

/-- A lax monoidal structure on the direct image `G_*` **reads on presheaves as precomposition**
when its tensorator and unit, followed by the inclusion of sheaves into presheaves, are those of
the inclusion precomposed with `G.op`. -/
structure ReadsAsPrecomposition (G : C ⥤ D) [G.IsContinuous J K]
    [lax : (G.sheafPushforwardContinuous A J K).LaxMonoidal] : Prop where
  μ_eq (X Y : Sheaf K A) : μ (sheafToPresheaf J A) ((G.sheafPushforwardContinuous A J K).obj X)
      ((G.sheafPushforwardContinuous A J K).obj Y) ≫
    (sheafToPresheaf J A).map (μ (G.sheafPushforwardContinuous A J K) X Y) =
      Functor.whiskerLeft G.op (μ (sheafToPresheaf K A) X Y)
  ε_eq : ε (sheafToPresheaf J A) ≫
    (sheafToPresheaf J A).map (ε (G.sheafPushforwardContinuous A J K)) =
      Functor.whiskerLeft G.op (ε (sheafToPresheaf K A))

/-- Naturality of a morphism of presheaves `f` against the maps `S.map (ψ.app U)`, in terms of
whiskering along the two functors `H₁ H₂`. -/
private theorem whiskerLeft_comp_eq_comp_whiskerLeft {B : Type*} [Category* B]
    {S T : Eᵒᵖ ⥤ B} (f : S ⟶ T) {H₁ H₂ : Cᵒᵖ ⥤ Eᵒᵖ} (ψ : H₁ ⟶ H₂)
    (βS : H₁ ⋙ S ⟶ H₂ ⋙ S) (βT : H₁ ⋙ T ⟶ H₂ ⋙ T)
    (hS : ∀ U, βS.app U = S.map (ψ.app U)) (hT : ∀ U, βT.app U = T.map (ψ.app U)) :
    Functor.whiskerLeft H₁ f ≫ βT = βS ≫ Functor.whiskerLeft H₂ f :=
  NatTrans.ext (funext fun U => (congrArg (_ ≫ ·) (hT U)).trans
    ((f.naturality (ψ.app U)).symm.trans (congrArg (· ≫ _) (hS U).symm)))

/-- **A comparison of direct images induced by a transformation of site functors is monoidal**,
for lax structures that read on presheaves as precomposition. -/
theorem isMonoidal_of_readsAsPrecomposition {G₁ G₂ : C ⥤ D} [G₁.IsContinuous J K]
    [G₂.IsContinuous J K] [(G₁.sheafPushforwardContinuous A J K).LaxMonoidal]
    [(G₂.sheafPushforwardContinuous A J K).LaxMonoidal]
    (h₁ : ReadsAsPrecomposition (A := A) J K G₁) (h₂ : ReadsAsPrecomposition (A := A) J K G₂)
    (φ : G₂ ⟶ G₁)
    (α : G₁.sheafPushforwardContinuous A J K ⟶ G₂.sheafPushforwardContinuous A J K)
    (hα : ∀ M, (α.app M).hom = Functor.whiskerRight (NatTrans.op φ) M.obj) :
    NatTrans.IsMonoidal α := by
  have hu : Functor.whiskerLeft G₁.op (ε (sheafToPresheaf K A)) ≫
      (sheafToPresheaf J A).map (α.app (𝟙_ (Sheaf K A))) =
      Functor.whiskerLeft G₂.op (ε (sheafToPresheaf K A)) :=
    (whiskerLeft_comp_eq_comp_whiskerLeft _ (NatTrans.op φ) (𝟙 _) _ (fun _ => rfl)
      fun U => NatTrans.congr_app (hα _) U).trans (Category.id_comp _)
  have ht : ∀ X Y : Sheaf K A, Functor.whiskerLeft G₁.op (μ (sheafToPresheaf K A) X Y) ≫
      (sheafToPresheaf J A).map (α.app (X ⊗ Y)) =
      ((sheafToPresheaf J A).map (α.app X) ⊗ₘ (sheafToPresheaf J A).map (α.app Y)) ≫
        Functor.whiskerLeft G₂.op (μ (sheafToPresheaf K A) X Y) := fun X Y =>
    whiskerLeft_comp_eq_comp_whiskerLeft _ (NatTrans.op φ) _ _
      (fun U => congrArg₂ (· ⊗ₘ ·) (NatTrans.congr_app (hα X) U) (NatTrans.congr_app (hα Y) U))
      fun U => NatTrans.congr_app (hα _) U
  have : NatTrans.IsMonoidal (Functor.whiskerRight α (sheafToPresheaf J A)) := by
    constructor
    · simp only [comp_ε, Functor.whiskerRight_app, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁.ε_eq).trans
        (hu.trans h₂.ε_eq.symm))
    · intro X Y
      simp only [comp_μ, Functor.whiskerRight_app, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (h₁.μ_eq X Y)).trans
        ((ht X Y).trans (congrArg (_ ≫ ·) (h₂.μ_eq X Y).symm)))
  exact isMonoidal_of_whiskerRight_sheafToPresheaf J α

/-- **A transformation from the identity to a direct image, induced by a transformation of site
functors, is monoidal**, for a lax structure that reads on presheaves as precomposition. -/
theorem isMonoidal_of_readsAsPrecomposition_id {G : C ⥤ C} [G.IsContinuous J J]
    [(G.sheafPushforwardContinuous A J J).LaxMonoidal] (h : ReadsAsPrecomposition (A := A) J J G)
    (φ : G ⟶ 𝟭 C) (α : 𝟭 (Sheaf J A) ⟶ G.sheafPushforwardContinuous A J J)
    (hα : ∀ M U, (α.app M).hom.app U = M.obj.map (φ.app (Opposite.unop U)).op) :
    NatTrans.IsMonoidal α := by
  have hu : ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map (α.app (𝟙_ (Sheaf J A))) =
      Functor.whiskerLeft G.op (ε (sheafToPresheaf J A)) :=
    (whiskerLeft_comp_eq_comp_whiskerLeft (ε (sheafToPresheaf J A)) (NatTrans.op φ) (𝟙 _)
      ((sheafToPresheaf J A).map (α.app _)) (fun _ => rfl) fun U => hα _ U).trans
      (Category.id_comp _)
  have ht : ∀ X Y : Sheaf J A, μ (sheafToPresheaf J A) X Y ≫
      (sheafToPresheaf J A).map (α.app (X ⊗ Y)) =
      ((sheafToPresheaf J A).map (α.app X) ⊗ₘ (sheafToPresheaf J A).map (α.app Y)) ≫
        Functor.whiskerLeft G.op (μ (sheafToPresheaf J A) X Y) := fun X Y =>
    whiskerLeft_comp_eq_comp_whiskerLeft (μ (sheafToPresheaf J A) X Y) (NatTrans.op φ)
      ((sheafToPresheaf J A).map (α.app X) ⊗ₘ (sheafToPresheaf J A).map (α.app Y))
      ((sheafToPresheaf J A).map (α.app _))
      (fun U => congrArg₂ (· ⊗ₘ ·) (hα X U) (hα Y U)) fun U => hα _ U
  have : NatTrans.IsMonoidal (Functor.whiskerRight α (sheafToPresheaf J A)) := by
    constructor
    · change (ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map (𝟙 _)) ≫
          (sheafToPresheaf J A).map (α.app _) =
        ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map (ε (G.sheafPushforwardContinuous A J J))
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact hu.trans h.ε_eq.symm
    · intro X Y
      change (μ (sheafToPresheaf J A) X Y ≫ (sheafToPresheaf J A).map (𝟙 _)) ≫
          (sheafToPresheaf J A).map (α.app (X ⊗ Y)) =
        ((sheafToPresheaf J A).map (α.app X) ⊗ₘ (sheafToPresheaf J A).map (α.app Y)) ≫
          μ (sheafToPresheaf J A) _ _ ≫
            (sheafToPresheaf J A).map (μ (G.sheafPushforwardContinuous A J J) X Y)
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact (ht X Y).trans (congrArg (_ ≫ ·) (h.μ_eq X Y).symm)
  exact isMonoidal_of_whiskerRight_sheafToPresheaf J α

/-- **A comparison between a composite of direct images and a direct image, induced by a
transformation of site functors, is monoidal**, for lax structures that read on presheaves as
precomposition (the composite carrying the composite lax structure). -/
theorem isMonoidal_of_readsAsPrecomposition_comp {G₁ : C ⥤ D} {G₂ : D ⥤ E} {G₃ : C ⥤ E}
    [G₁.IsContinuous J K] [G₂.IsContinuous K L] [G₃.IsContinuous J L]
    [(G₁.sheafPushforwardContinuous A J K).LaxMonoidal]
    [(G₂.sheafPushforwardContinuous A K L).LaxMonoidal]
    [(G₃.sheafPushforwardContinuous A J L).LaxMonoidal]
    (h₁ : ReadsAsPrecomposition (A := A) J K G₁) (h₂ : ReadsAsPrecomposition (A := A) K L G₂)
    (h₃ : ReadsAsPrecomposition (A := A) J L G₃) (φ : G₃ ⟶ G₁ ⋙ G₂)
    (α : G₂.sheafPushforwardContinuous A K L ⋙ G₁.sheafPushforwardContinuous A J K ⟶
      G₃.sheafPushforwardContinuous A J L)
    (hα : ∀ M U, (α.app M).hom.app U = M.obj.map (φ.app (Opposite.unop U)).op) :
    NatTrans.IsMonoidal α := by
  let ι := sheafToPresheaf J A
  let P₁ := G₁.sheafPushforwardContinuous A J K
  let P₂ := G₂.sheafPushforwardContinuous A K L
  have hεc : ε ι ≫ ι.map (ε P₁ ≫ P₁.map (ε P₂)) =
      Functor.whiskerLeft G₁.op (Functor.whiskerLeft G₂.op (ε (sheafToPresheaf L A))) :=
    (congrArg (_ ≫ ·) (ι.map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h₁.ε_eq).trans ((Functor.whiskerLeft_comp _ _ _).symm.trans
        (congrArg (Functor.whiskerLeft G₁.op) h₂.ε_eq))))
  have hμc : ∀ X Y : Sheaf L A, μ ι (P₁.obj (P₂.obj X)) (P₁.obj (P₂.obj Y)) ≫
      ι.map (μ P₁ (P₂.obj X) (P₂.obj Y) ≫ P₁.map (μ P₂ X Y)) =
      Functor.whiskerLeft G₁.op (Functor.whiskerLeft G₂.op (μ (sheafToPresheaf L A) X Y)) :=
    fun X Y => (congrArg (_ ≫ ·) (ι.map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (h₁.μ_eq _ _)).trans ((Functor.whiskerLeft_comp _ _ _).symm.trans
        (congrArg (Functor.whiskerLeft G₁.op) (h₂.μ_eq X Y)))))
  have hu : Functor.whiskerLeft G₁.op (Functor.whiskerLeft G₂.op (ε (sheafToPresheaf L A))) ≫
      ι.map (α.app (𝟙_ (Sheaf L A))) =
      Functor.whiskerLeft G₃.op (ε (sheafToPresheaf L A)) :=
    (whiskerLeft_comp_eq_comp_whiskerLeft (ε (sheafToPresheaf L A)) (NatTrans.op φ) (𝟙 _)
      (ι.map (α.app _)) (fun _ => rfl) fun U => hα _ U).trans (Category.id_comp _)
  have ht : ∀ X Y : Sheaf L A,
      Functor.whiskerLeft G₁.op (Functor.whiskerLeft G₂.op (μ (sheafToPresheaf L A) X Y)) ≫
        ι.map (α.app (X ⊗ Y)) =
      (ι.map (α.app X) ⊗ₘ ι.map (α.app Y)) ≫
        Functor.whiskerLeft G₃.op (μ (sheafToPresheaf L A) X Y) := fun X Y =>
    whiskerLeft_comp_eq_comp_whiskerLeft (μ (sheafToPresheaf L A) X Y) (NatTrans.op φ)
      (ι.map (α.app X) ⊗ₘ ι.map (α.app Y)) (ι.map (α.app _))
      (fun U => congrArg₂ (· ⊗ₘ ·) (hα X U) (hα Y U)) fun U => hα _ U
  have : NatTrans.IsMonoidal (Functor.whiskerRight α (sheafToPresheaf J A)) := by
    constructor
    · change (ε ι ≫ ι.map (ε P₁ ≫ P₁.map (ε P₂))) ≫ ι.map (α.app _) =
        ε ι ≫ ι.map (ε (G₃.sheafPushforwardContinuous A J L))
      exact (congrArg (· ≫ _) hεc).trans (hu.trans h₃.ε_eq.symm)
    · intro X Y
      change (μ ι (P₁.obj (P₂.obj X)) (P₁.obj (P₂.obj Y)) ≫
          ι.map (μ P₁ (P₂.obj X) (P₂.obj Y) ≫ P₁.map (μ P₂ X Y))) ≫ ι.map (α.app (X ⊗ Y)) =
        (ι.map (α.app X) ⊗ₘ ι.map (α.app Y)) ≫ μ ι _ _ ≫
          ι.map (μ (G₃.sheafPushforwardContinuous A J L) X Y)
      exact (congrArg (· ≫ _) (hμc X Y)).trans ((ht X Y).trans
        (congrArg (_ ≫ ·) (h₃.μ_eq X Y).symm))
  exact isMonoidal_of_whiskerRight_sheafToPresheaf J α

end Reading

/-- The lax structure of the direct image, right adjoint to the monoidal inverse image, reads
on presheaves as precomposition. -/
theorem readsAsPrecomposition_sheafPushforwardContinuous :
    ReadsAsPrecomposition (A := A) J K G where
  μ_eq := sheafToPresheaf_μ_comp_map_sheafPushforwardContinuous_μ G A J K
  ε_eq := sheafToPresheaf_ε_comp_map_sheafPushforwardContinuous_ε G A J K


end CategoryTheory.Functor

end
