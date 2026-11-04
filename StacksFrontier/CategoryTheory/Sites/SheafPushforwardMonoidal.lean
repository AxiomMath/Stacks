module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksFrontier.CategoryTheory.Monoidal.ConjugateMonoidal
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensor
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensorUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushforward of sheaves is lax monoidal, and inverse image is monoidal

Let `G : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`, and let `A` be a
monoidal category for which sheafification on both sites is monoidal, so that `Sheaf J A` and
`Sheaf K A` carry the tensor product `CategoryTheory.Sheaf.monoidalCategory`: the sheafification
of the sectionwise tensor product. This file shows:

* the pushforward `G_* : Sheaf K A ⥤ Sheaf J A` is **lax monoidal**: its tensorator
  `G_*M ⊗ G_*N ⟶ G_*(M ⊗ N)` is the morphism out of the sheafification of the sectionwise tensor
  product `U ↦ M(G U) ⊗ N(G U)` induced by the sheafification unit of `M ⊗ N`;
* the comparison of pushforwards along a composite is a **monoidal** natural isomorphism;
* consequently every left adjoint `G⁻¹` of `G_*` is oplax monoidal
  (`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`), and its oplax structure is **strong**
  as soon as the left Kan extension along `G.op` commutes with the sectionwise tensor product and
  preserves the unit — which is the case when the comma categories computing it are filtered and
  the tensor product commutes with colimits over them.

## Main definitions

* `Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal`: the forgetful functor from
  sheaves to presheaves is lax monoidal, as the right adjoint of sheafification.
* `Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal`: the lax monoidal structure on the
  pushforward of sheaves along a continuous functor.

## Main results

* `Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf_comp_map_μ_pushforward`: the tensorator of
  the pushforward, read on underlying presheaves, is the restriction along `G.op` of the
  sheafification unit of `M ⊗ N`.
* `Stacks.SheafPushforwardMonoidal.isMonoidal_sheafPushforwardContinuousComp'_hom`: the
  comparison of pushforwards along a composite is monoidal.

## Implementation notes

The lax structure is transported, along the counit of sheafification, from the composite of
three lax monoidal functors: the forgetful functor to presheaves, restriction along `G.op`
(strict monoidal, the tensor product of presheaves being sectionwise) and sheafification. The
formula `μ_sheafToPresheaf_comp_map_μ_pushforward` characterizes it, because a morphism out of a
tensor product of sheaves is determined by its composite with the tensorator of the forgetful
functor (`hom_ext_tensor`), which is the sheafification unit up to isomorphism. Every later
statement is proved through that characterization.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.LaxMonoidal
  Functor.OplaxMonoidal

namespace Stacks.SheafPushforwardMonoidal

attribute [local instance] Sheaf.monoidalCategory

section Forget

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

/-- The forgetful functor from sheaves to presheaves is lax monoidal for
`CategoryTheory.Sheaf.monoidalCategory`: it is the right adjoint of sheafification, which is
monoidal. -/
@[instance_reducible]
noncomputable def sheafToPresheafLaxMonoidal : (sheafToPresheaf J A).LaxMonoidal :=
  (sheafificationAdjunction J A).rightAdjointLaxMonoidal

attribute [local instance] sheafToPresheafLaxMonoidal

/-- The morphism from the sheafification of the sectionwise tensor product of two sheaves to
their tensor product: the comparison of sheafification followed by the two counits. -/
noncomputable def sheafifyTensorIso (P Q : Sheaf J A) :
    (presheafToSheaf J A).obj ((sheafToPresheaf J A).obj P ⊗ (sheafToPresheaf J A).obj Q) ≅
      P ⊗ Q :=
  (Functor.Monoidal.μIso (presheafToSheaf J A) _ _).symm ≪≫
    tensorIso (asIso ((sheafificationAdjunction J A).counit.app P))
      (asIso ((sheafificationAdjunction J A).counit.app Q))

/-- The tensorator of the forgetful functor from sheaves to presheaves at `P` and `Q` is the
adjoint transpose of `sheafifyTensorIso J A P Q`. -/
lemma μ_sheafToPresheaf (P Q : Sheaf J A) :
    μ (sheafToPresheaf J A) P Q =
      (sheafificationAdjunction J A).homEquiv _ _ (sheafifyTensorIso J A P Q).hom :=
  rfl

/-- **A morphism out of a tensor product of sheaves is determined by its composite with the
tensorator of the forgetful functor**, that is, by its restriction to the sectionwise tensor
product. -/
lemma hom_ext_tensor {P Q S : Sheaf J A} {f g : P ⊗ Q ⟶ S}
    (h : μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map f =
      μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map g) : f = g := by
  rw [μ_sheafToPresheaf, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_right] at h
  simpa using (sheafificationAdjunction J A).homEquiv _ _ |>.injective h

/-- A morphism out of the unit sheaf is determined by its composite with the unit morphism of
the forgetful functor. -/
lemma hom_ext_unit {S : Sheaf J A} {f g : 𝟙_ (Sheaf J A) ⟶ S}
    (h : ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map f =
      ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map g) : f = g := by
  have hε : ε (sheafToPresheaf J A) =
      (sheafificationAdjunction J A).homEquiv _ _ (η (presheafToSheaf J A)) := rfl
  rw [hε, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_right] at h
  exact (cancel_epi _).1 ((sheafificationAdjunction J A).homEquiv _ _ |>.injective h)

/-- The morphism out of a tensor product of sheaves with a prescribed restriction to the
sectionwise tensor product. -/
noncomputable def tensorDesc {P Q S : Sheaf J A}
    (φ : (sheafToPresheaf J A).obj P ⊗ (sheafToPresheaf J A).obj Q ⟶
      (sheafToPresheaf J A).obj S) : P ⊗ Q ⟶ S :=
  (sheafifyTensorIso J A P Q).inv ≫ ((sheafificationAdjunction J A).homEquiv _ _).symm φ

/-- The restriction of `tensorDesc J A φ` to the sectionwise tensor product is `φ`. -/
@[reassoc (attr := simp)]
lemma μ_comp_map_tensorDesc {P Q S : Sheaf J A}
    (φ : (sheafToPresheaf J A).obj P ⊗ (sheafToPresheaf J A).obj Q ⟶
      (sheafToPresheaf J A).obj S) :
    μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map (tensorDesc J A φ) = φ := by
  rw [μ_sheafToPresheaf, tensorDesc, ← Adjunction.homEquiv_naturality_right,
    Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] in
/-- Sheafifying a morphism into the underlying presheaf of a sheaf and composing with the counit
is inverse to the adjunction bijection. -/
lemma homEquiv_map_comp_counit {Q : Cᵒᵖ ⥤ A} {S : Sheaf J A}
    (φ : Q ⟶ (sheafToPresheaf J A).obj S) :
    (sheafificationAdjunction J A).homEquiv _ _
      ((presheafToSheaf J A).map φ ≫ (sheafificationAdjunction J A).counit.app S) = φ := by
  rw [Adjunction.homEquiv_unit]
  simp

/-- The tensorator of the forgetful functor followed by the sheafification of a morphism of
presheaves, conjugated by the counits: the composite is that morphism. -/
lemma μ_comp_map_sheafify {S₁ S₂ S₃ : Sheaf J A} {Q : Cᵒᵖ ⥤ A}
    (φ₁ : (sheafToPresheaf J A).obj S₁ ⊗ (sheafToPresheaf J A).obj S₂ ⟶ Q)
    (φ₂ : Q ⟶ (sheafToPresheaf J A).obj S₃) :
    μ (sheafToPresheaf J A) S₁ S₂ ≫ (sheafToPresheaf J A).map
        ((inv ((sheafificationAdjunction J A).counit.app S₁) ⊗ₘ
            inv ((sheafificationAdjunction J A).counit.app S₂)) ≫
          ((μ (presheafToSheaf J A) _ _ ≫ (presheafToSheaf J A).map φ₁) ≫
            (presheafToSheaf J A).map φ₂) ≫
          (sheafificationAdjunction J A).counit.app S₃) = φ₁ ≫ φ₂ := by
  rw [μ_sheafToPresheaf, ← Adjunction.homEquiv_naturality_right]
  have : (sheafifyTensorIso J A S₁ S₂).hom ≫
      (inv ((sheafificationAdjunction J A).counit.app S₁) ⊗ₘ
          inv ((sheafificationAdjunction J A).counit.app S₂)) ≫
        ((μ (presheafToSheaf J A) _ _ ≫ (presheafToSheaf J A).map φ₁) ≫
          (presheafToSheaf J A).map φ₂) ≫
        (sheafificationAdjunction J A).counit.app S₃ =
      (presheafToSheaf J A).map (φ₁ ≫ φ₂) ≫ (sheafificationAdjunction J A).counit.app S₃ := by
    simp [sheafifyTensorIso, tensorHom_comp_tensorHom_assoc]
  rw [this, homEquiv_map_comp_counit]

/-- The unit morphism of the forgetful functor from sheaves to presheaves is the adjoint
transpose of the unit morphism of sheafification. -/
lemma ε_sheafToPresheaf :
    ε (sheafToPresheaf J A) =
      (sheafificationAdjunction J A).homEquiv _ _ (η (presheafToSheaf J A)) :=
  rfl

/-- The unit morphism of the forgetful functor followed by the sheafification of a morphism of
presheaves out of the unit, conjugated by the counit: the composite is that morphism. -/
lemma ε_comp_map_sheafify {S : Sheaf J A} {Q : Cᵒᵖ ⥤ A} (φ₁ : 𝟙_ (Cᵒᵖ ⥤ A) ⟶ Q)
    (φ₂ : Q ⟶ (sheafToPresheaf J A).obj S) :
    ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map
        (((ε (presheafToSheaf J A) ≫ (presheafToSheaf J A).map φ₁) ≫
            (presheafToSheaf J A).map φ₂) ≫
          (sheafificationAdjunction J A).counit.app S) = φ₁ ≫ φ₂ := by
  rw [ε_sheafToPresheaf, ← Adjunction.homEquiv_naturality_right]
  have : η (presheafToSheaf J A) ≫
      ((ε (presheafToSheaf J A) ≫ (presheafToSheaf J A).map φ₁) ≫
          (presheafToSheaf J A).map φ₂) ≫
        (sheafificationAdjunction J A).counit.app S =
      (presheafToSheaf J A).map (φ₁ ≫ φ₂) ≫ (sheafificationAdjunction J A).counit.app S := by
    simp
  rw [this, homEquiv_map_comp_counit]

end Forget

attribute [local instance] sheafToPresheafLaxMonoidal

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]
  [HasWeakSheafify K A] [(K.W (A := A)).IsMonoidal]
  (G : C ⥤ D) [G.IsContinuous J K]

/-- The pushforward along `G` is isomorphic to the composite of the forgetful functor to
presheaves, restriction along `G.op` and sheafification; the isomorphism is the counit of
sheafification. -/
noncomputable def pushforwardIso :
    sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
      G.sheafPushforwardContinuous A J K :=
  NatIso.ofComponents
    (fun M => @asIso _ _ _ _ ((sheafificationAdjunction J A).counit.app
        ((G.sheafPushforwardContinuous A J K).obj M)) (isIso_sheafificationAdjunction_counit _))
    (fun f => (sheafificationAdjunction J A).counit.naturality
      ((G.sheafPushforwardContinuous A J K).map f))

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
/-- The component of `pushforwardIso` at `M` is the sheafification counit at the pushforward of
`M`. -/
@[simp]
lemma pushforwardIso_hom_app (M : Sheaf K A) :
    (pushforwardIso J K A G).hom.app M =
      (sheafificationAdjunction J A).counit.app ((G.sheafPushforwardContinuous A J K).obj M) :=
  rfl

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
/-- The inverse of the component of `pushforwardIso` at `M` is the inverse of the sheafification
counit at the pushforward of `M`. -/
@[simp]
lemma pushforwardIso_inv_app (M : Sheaf K A) :
    (pushforwardIso J K A G).inv.app M =
      inv ((sheafificationAdjunction J A).counit.app
        ((G.sheafPushforwardContinuous A J K).obj M)) :=
  rfl

/-- **The pushforward of sheaves along a continuous functor is lax monoidal**, for the tensor
product `CategoryTheory.Sheaf.monoidalCategory` on both sides. -/
@[instance_reducible]
noncomputable def pushforwardLaxMonoidal : (G.sheafPushforwardContinuous A J K).LaxMonoidal :=
  Functor.LaxMonoidal.transport (pushforwardIso J K A G)

attribute [local instance] pushforwardLaxMonoidal

omit [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
/-- The underlying presheaf of the pushforward of a sheaf is its restriction along `G.op`. -/
lemma sheafToPresheaf_obj_pushforward_obj (M : Sheaf K A) :
    (sheafToPresheaf J A).obj ((G.sheafPushforwardContinuous A J K).obj M) =
      ((Functor.whiskeringLeft _ _ A).obj G.op).obj ((sheafToPresheaf K A).obj M) :=
  rfl

omit [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
/-- The underlying presheaf of the pushforward of a morphism is its restriction along `G.op`. -/
lemma sheafToPresheaf_map_pushforward_map {M N : Sheaf K A} (f : M ⟶ N) :
    (sheafToPresheaf J A).map ((G.sheafPushforwardContinuous A J K).map f) =
      ((Functor.whiskeringLeft _ _ A).obj G.op).map ((sheafToPresheaf K A).map f) :=
  rfl

/-- **The tensorator of the pushforward, on underlying presheaves**: precomposed with the
tensorator of the forgetful functor it is the restriction along `G.op` of the tensorator of the
forgetful functor at `M` and `N`, i.e. of the sheafification unit of the sectionwise tensor
product. This characterizes it, by `hom_ext_tensor`. -/
lemma μ_sheafToPresheaf_comp_map_μ_pushforward (M N : Sheaf K A) :
    μ (sheafToPresheaf J A) ((G.sheafPushforwardContinuous A J K).obj M)
        ((G.sheafPushforwardContinuous A J K).obj N) ≫
      (sheafToPresheaf J A).map (μ (G.sheafPushforwardContinuous A J K) M N) =
    ((Functor.whiskeringLeft _ _ A).obj G.op).map (μ (sheafToPresheaf K A) M N) := by
  have h := μ_comp_map_sheafify J A (S₁ := (G.sheafPushforwardContinuous A J K).obj M)
    (S₂ := (G.sheafPushforwardContinuous A J K).obj N)
    (S₃ := (G.sheafPushforwardContinuous A J K).obj (M ⊗ N))
    (μ ((Functor.whiskeringLeft _ _ A).obj G.op) ((sheafToPresheaf K A).obj M)
      ((sheafToPresheaf K A).obj N))
    (((Functor.whiskeringLeft _ _ A).obj G.op).map (μ (sheafToPresheaf K A) M N))
  exact h.trans (Category.id_comp _)

/-- The unit morphism of the pushforward, on underlying presheaves: it is the restriction along
`G.op` of the unit morphism of the forgetful functor. -/
lemma ε_sheafToPresheaf_comp_map_ε_pushforward :
    ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map (ε (G.sheafPushforwardContinuous A J K)) =
    ((Functor.whiskeringLeft _ _ A).obj G.op).map (ε (sheafToPresheaf K A)) := by
  have h := ε_comp_map_sheafify J A (S := (G.sheafPushforwardContinuous A J K).obj (𝟙_ _))
    (ε ((Functor.whiskeringLeft _ _ A).obj G.op))
    (((Functor.whiskeringLeft _ _ A).obj G.op).map (ε (sheafToPresheaf K A)))
  exact h.trans (Category.id_comp _)

end Pushforward

section Composition

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₄} [Category.{v₄} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]
  [HasWeakSheafify K A] [(K.W (A := A)).IsMonoidal]
  [HasWeakSheafify L A] [(L.W (A := A)).IsMonoidal]
  {G₁ : C ⥤ D} {G₂ : D ⥤ E} {G₁₂ : C ⥤ E} (e : G₁ ⋙ G₂ ≅ G₁₂)
  [G₁.IsContinuous J K] [G₂.IsContinuous K L] [G₁₂.IsContinuous J L]

attribute [local instance] pushforwardLaxMonoidal

omit [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [HasWeakSheafify L A] in
include e in
/-- The comparison of pushforwards along a composite, on underlying presheaves: it is the
action of the comparison of the composite functors. -/
lemma sheafToPresheaf_map_sheafPushforwardContinuousComp'_hom_app (S : Sheaf L A) :
    (sheafToPresheaf J A).map ((Functor.sheafPushforwardContinuousComp' e A J K L).hom.app S) =
      Functor.whiskerRight (NatTrans.op e.inv) ((sheafToPresheaf L A).obj S) := by
  ext U
  exact Category.id_comp _

/-- **The comparison of pushforwards along a composite is monoidal**: for an isomorphism
`G₁ ⋙ G₂ ≅ G₁₂` of continuous functors, the induced isomorphism `G₂_* ⋙ G₁_* ≅ G₁₂_*` is a
monoidal natural isomorphism, the composite carrying the composite lax monoidal structure. -/
instance isMonoidal_sheafPushforwardContinuousComp'_hom :
    NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousComp' e A J K L).hom where
  unit := by
    apply hom_ext_unit
    have h₁ := ε_sheafToPresheaf_comp_map_ε_pushforward J K A G₁
    have h₂ := ε_sheafToPresheaf_comp_map_ε_pushforward K L A G₂
    have h₁₂ := ε_sheafToPresheaf_comp_map_ε_pushforward J L A G₁₂
    rw [Functor.LaxMonoidal.comp_ε, Functor.map_comp, Functor.map_comp, ← Category.assoc,
      ← Category.assoc, h₁, h₁₂]
    change (((Functor.whiskeringLeft _ _ A).obj G₁.op).map (ε (sheafToPresheaf K A)) ≫
        ((Functor.whiskeringLeft _ _ A).obj G₁.op).map
          ((sheafToPresheaf K A).map (ε (G₂.sheafPushforwardContinuous A K L)))) ≫ _ = _
    rw [← Functor.map_comp, h₂, sheafToPresheaf_map_sheafPushforwardContinuousComp'_hom_app]
    ext U
    exact ((ε (sheafToPresheaf L A)).naturality _).symm.trans (Category.id_comp _)
  tensor M N := by
    apply hom_ext_tensor
    have h₁ := μ_sheafToPresheaf_comp_map_μ_pushforward J K A G₁
      ((G₂.sheafPushforwardContinuous A K L).obj M) ((G₂.sheafPushforwardContinuous A K L).obj N)
    have h₂ := μ_sheafToPresheaf_comp_map_μ_pushforward K L A G₂ M N
    have h₁₂ := μ_sheafToPresheaf_comp_map_μ_pushforward J L A G₁₂ M N
    rw [Functor.LaxMonoidal.comp_μ, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    dsimp only [Functor.comp_obj] at h₁ ⊢
    rw [← Category.assoc, ← Category.assoc, h₁, ← μ_natural_assoc, h₁₂]
    change (((Functor.whiskeringLeft _ _ A).obj G₁.op).map
        (μ (sheafToPresheaf K A) ((G₂.sheafPushforwardContinuous A K L).obj M)
          ((G₂.sheafPushforwardContinuous A K L).obj N)) ≫
        ((Functor.whiskeringLeft _ _ A).obj G₁.op).map
          ((sheafToPresheaf K A).map (μ (G₂.sheafPushforwardContinuous A K L) M N))) ≫ _ = _
    rw [← Functor.map_comp, h₂, sheafToPresheaf_map_sheafPushforwardContinuousComp'_hom_app,
      sheafToPresheaf_map_sheafPushforwardContinuousComp'_hom_app,
      sheafToPresheaf_map_sheafPushforwardContinuousComp'_hom_app]
    ext U
    exact ((μ (sheafToPresheaf L A) M N).naturality _).symm

end Composition

section Lan

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [∀ X : D, HasColimitsOfShape (CostructuredArrow G X) A]

/-- Left Kan extension along `G` is oplax monoidal for the pointwise tensor products, as the left
adjoint of restriction along `G`, which is strict monoidal. -/
@[instance_reducible]
noncomputable def lanOplaxMonoidal : (G.lan : (C ⥤ A) ⥤ (D ⥤ A)).OplaxMonoidal :=
  (G.lanAdjunction A).leftAdjointOplaxMonoidal

attribute [local instance] lanOplaxMonoidal

/-- The comparison morphism of the oplax structure of left Kan extension is
`Stacks.InverseImageTensor.lanDeltaUnconditional`, the morphism attached by the universal property
of the Kan extension to the tensor product of the two units. -/
lemma δ_lan (P Q : C ⥤ A) :
    δ (G.lan : (C ⥤ A) ⥤ (D ⥤ A)) P Q =
      Stacks.InverseImageTensor.lanDeltaUnconditional G A P Q := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (G.lanUnit.app (P ⊗ Q))
  ext X
  have h := congr_app ((G.lanAdjunction A).unit_app_tensor_comp_map_δ P Q) X
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app,
    Stacks.InverseImageTensor.lanUnit_app_comp_lanDelta_app_general]
  simpa using h

/-- Left Kan extension along `G` preserves the unit when the comma categories computing it are
connected: the left Kan extension of a constant functor is then constant. -/
instance isIso_η_lan [∀ X : D, IsConnected (CostructuredArrow G X)] :
    IsIso (η (G.lan : (C ⥤ A) ⥤ (D ⥤ A))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have hu := (G.lanAdjunction A).unit_app_unit_comp_map_η
  rw [Functor.lanAdjunction_unit] at hu
  have h : (η (G.lan : (C ⥤ A) ⥤ (D ⥤ A))).app X =
      (IsColimit.coconePointUniqueUpToIso
        (Stacks.InverseImageTensor.lanIsColimitUnconditional G A (𝟙_ (C ⥤ A)) X)
        (isColimitConstCocone _ (𝟙_ A))).hom := by
    refine (Stacks.InverseImageTensor.lanIsColimitUnconditional G A (𝟙_ (C ⥤ A)) X).hom_ext
      fun T => ?_
    refine Eq.trans ?_ (IsColimit.comp_coconePointUniqueUpToIso_hom
      (Stacks.InverseImageTensor.lanIsColimitUnconditional G A (𝟙_ (C ⥤ A)) X)
      (isColimitConstCocone _ (𝟙_ A)) T).symm
    have hT := congr_app hu T.left
    simp only [NatTrans.comp_app, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app] at hT
    simp only [Stacks.InverseImageTensor.lanCoconeUnconditional,
      Functor.LeftExtension.coconeAt_ι_app,
      Functor.LeftExtension.mk_hom, Functor.LeftExtension.mk_right, Category.assoc]
    rw [(η (G.lan : (C ⥤ A) ⥤ (D ⥤ A))).naturality T.hom, reassoc_of% hT]
    exact Category.comp_id _
  rw [h]
  exact Iso.isIso_hom _

variable [∀ X : D, IsFiltered (CostructuredArrow G X)]
  [∀ (X : D) (P Q : C ⥤ A), PreservesColimit₂ (CostructuredArrow.proj G X ⋙ P)
    (CostructuredArrow.proj G X ⋙ Q) (curriedTensor A)]

/-- Left Kan extension along `G` commutes with the pointwise tensor product when the comma
categories computing it are filtered and the tensor product commutes with colimits over them:
the comparison morphism is `Stacks.InverseImageTensor.lanDeltaUnconditional`. -/
instance isIso_δ_lan (P Q : C ⥤ A) : IsIso (δ (G.lan : (C ⥤ A) ⥤ (D ⥤ A)) P Q) := by
  rw [δ_lan]
  infer_instance

end Lan

section Pullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]
  [HasWeakSheafify K A] [(K.W (A := A)).IsMonoidal]
  (G : C ⥤ D) [G.IsContinuous J K]
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) A]

attribute [local instance] pushforwardLaxMonoidal lanOplaxMonoidal

/-- The sheafification adjunction is monoidal, for the monoidal structure of sheafification and
the lax monoidal structure `sheafToPresheafLaxMonoidal` of the forgetful functor. -/
instance isMonoidal_sheafificationAdjunction : (sheafificationAdjunction J A).IsMonoidal :=
  inferInstanceAs (letI := (sheafificationAdjunction J A).rightAdjointLaxMonoidal
    (sheafificationAdjunction J A).IsMonoidal)

/-- The pushforward followed by the forgetful functor is, on the nose, the forgetful functor
followed by restriction along `G.op`, and this identification is monoidal for the composite lax
structures. -/
instance isMonoidal_sheafPushforwardContinuousCompSheafToPresheafIso_hom :
    NatTrans.IsMonoidal (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).hom where
  unit := by
    rw [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.comp_ε,
      ε_sheafToPresheaf_comp_map_ε_pushforward J K A G]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  tensor M N := by
    rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ,
      μ_sheafToPresheaf_comp_map_μ_pushforward J K A G]
    refine (Category.comp_id _).trans ?_
    ext U
    dsimp only [Functor.sheafPushforwardContinuousCompSheafToPresheafIso, Iso.refl,
      Functor.sheafPushforwardContinuous, ObjectProperty.lift]
    simp only [ObjectProperty.ι_obj, Functor.whiskeringLeft_obj_obj, Functor.comp_obj,
      Functor.op_obj, Monoidal.tensorObj_obj, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app, Functor.comp_map, ObjectProperty.ι_map, NatTrans.id_app,
      tensorHom_id, id_whiskerRight, Category.id_comp, NatTrans.comp_app,
      Functor.Monoidal.whiskeringLeft_μ_app]
    exact (Category.id_comp ((μ (sheafToPresheaf K A) M N).app _)).symm

/-- If `a ≫ b ≫ c` is an isomorphism and `a`, `b` are, then so is `c`. -/
private theorem isIso_of_isIso_fac {C : Type*} [Category C] {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) {d : W ⟶ Z} [IsIso a] [IsIso b] [IsIso d] (h : a ≫ b ≫ c = d) : IsIso c := by
  subst h
  have := IsIso.of_isIso_comp_left a (b ≫ c)
  exact IsIso.of_isIso_comp_left b c

variable {F : Sheaf J A ⥤ Sheaf K A} (adj : F ⊣ G.sheafPushforwardContinuous A J K)

/-- The comparison of the two left adjoints of `G_* ⋙ forget = forget ⋙ (restriction along G.op)`:
sheafification followed by `F`, and left Kan extension followed by sheafification. -/
noncomputable def lanSheafifyIso :
    (G.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) ⋙ presheafToSheaf K A ≅ presheafToSheaf J A ⋙ F :=
  (conjugateIsoEquiv ((sheafificationAdjunction J A).comp adj)
    ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A))).symm
      (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K)

/-- The oplax monoidal structure on a left adjoint of the pushforward: the mate of the lax
monoidal structure of the pushforward, `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`. -/
@[instance_reducible]
noncomputable def pullbackOplaxMonoidal : F.OplaxMonoidal :=
  adj.leftAdjointOplaxMonoidal

/-- The conjugate of `lanSheafifyIso` is a monoidal natural transformation, being the
monoidal identification `G.sheafPushforwardContinuousCompSheafToPresheafIso A J K`. -/
instance isMonoidal_conjugateEquiv_lanSheafifyIso_hom :
    NatTrans.IsMonoidal (conjugateEquiv ((sheafificationAdjunction J A).comp adj)
      ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A))
      (lanSheafifyIso J K A G adj).hom) := by
  rw [lanSheafifyIso, conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  infer_instance

/-- The comparison `lanSheafifyIso` commutes with the comparison morphisms `δ` of the two oplax
monoidal functors `G.op.lan ⋙ sheafification` and `sheafification ⋙ F`. -/
lemma lanSheafifyIso_hom_app_tensor_comp_δ (Q₁ Q₂ : Cᵒᵖ ⥤ A) :
    letI := pullbackOplaxMonoidal J K A G adj
    (lanSheafifyIso J K A G adj).hom.app (Q₁ ⊗ Q₂) ≫ δ (presheafToSheaf J A ⋙ F) Q₁ Q₂ =
      δ ((G.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) ⋙ presheafToSheaf K A) Q₁ Q₂ ≫
        ((lanSheafifyIso J K A G adj).hom.app Q₁ ⊗ₘ (lanSheafifyIso J K A G adj).hom.app Q₂) :=
  let := pullbackOplaxMonoidal J K A G adj
  Adjunction.conjugateEquiv_symm_app_tensor_comp_δ ((sheafificationAdjunction J A).comp adj)
    ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)) _ Q₁ Q₂

/-- The comparison `lanSheafifyIso` commutes with the counit morphisms `η` of the two oplax
monoidal functors `G.op.lan ⋙ sheafification` and `sheafification ⋙ F`. -/
lemma lanSheafifyIso_hom_app_unit_comp_η :
    letI := pullbackOplaxMonoidal J K A G adj
    (lanSheafifyIso J K A G adj).hom.app (𝟙_ _) ≫ η (presheafToSheaf J A ⋙ F) =
      η ((G.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) ⋙ presheafToSheaf K A) :=
  let := pullbackOplaxMonoidal J K A G adj
  Adjunction.conjugateEquiv_symm_app_unit_comp_η ((sheafificationAdjunction J A).comp adj)
    ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)) _

section

attribute [local instance] IsFiltered.isConnected

variable [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]

/-- **The inverse image preserves the unit**: the counit morphism `η` of the oplax structure of a
left adjoint of the pushforward is an isomorphism, when the comma categories computing the left
Kan extension along `G.op` are filtered. -/
lemma isIso_η_pullback :
    letI := pullbackOplaxMonoidal J K A G adj
    IsIso (η F) := by
  let := pullbackOplaxMonoidal J K A G adj
  have h := lanSheafifyIso_hom_app_unit_comp_η J K A G adj
  rw [Functor.OplaxMonoidal.comp_η, Functor.OplaxMonoidal.comp_η] at h
  exact isIso_of_isIso_fac _ _ _ h

variable [∀ (X : Dᵒᵖ) (P Q : Cᵒᵖ ⥤ A), PreservesColimit₂ (CostructuredArrow.proj G.op X ⋙ P)
    (CostructuredArrow.proj G.op X ⋙ Q) (curriedTensor A)]

/-- **The inverse image commutes with the tensor product**: the comparison morphism `δ` of the
oplax structure of a left adjoint of the pushforward is an isomorphism, when the comma categories
computing the left Kan extension along `G.op` are filtered and the tensor product of `A` commutes
with colimits over them. -/
lemma isIso_δ_pullback (M N : Sheaf J A) :
    letI := pullbackOplaxMonoidal J K A G adj
    IsIso (δ F M N) := by
  let := pullbackOplaxMonoidal J K A G adj
  have hsh (Q₁ Q₂ : Cᵒᵖ ⥤ A) :
      IsIso (δ F ((presheafToSheaf J A).obj Q₁) ((presheafToSheaf J A).obj Q₂)) := by
    have h := lanSheafifyIso_hom_app_tensor_comp_δ J K A G adj Q₁ Q₂
    rw [Functor.OplaxMonoidal.comp_δ, Functor.OplaxMonoidal.comp_δ] at h
    exact isIso_of_isIso_fac _ _ _ h
  have h : F.map ((sheafificationAdjunction J A).counit.app M ⊗ₘ
      (sheafificationAdjunction J A).counit.app N) ≫ δ F M N =
      δ F _ _ ≫ (F.map ((sheafificationAdjunction J A).counit.app M) ⊗ₘ
        F.map ((sheafificationAdjunction J A).counit.app N)) :=
    (Functor.OplaxMonoidal.δ_natural F ((sheafificationAdjunction J A).counit.app M)
      ((sheafificationAdjunction J A).counit.app N)).symm
  have : IsIso (F.map ((sheafificationAdjunction J A).counit.app M ⊗ₘ
      (sheafificationAdjunction J A).counit.app N) ≫ δ F M N) := by
    rw [h]
    have : IsIso (δ F ((sheafToPresheaf J A ⋙ presheafToSheaf J A).obj M)
        ((sheafToPresheaf J A ⋙ presheafToSheaf J A).obj N)) := hsh _ _
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map ((sheafificationAdjunction J A).counit.app M ⊗ₘ
      (sheafificationAdjunction J A).counit.app N)) _

/-- **The inverse image of sheaves is a monoidal functor**: a left adjoint of the pushforward
along a continuous functor `G`, with the oplax structure `pullbackOplaxMonoidal` mated from the
lax structure of the pushforward, which is strong when the comma categories computing the left
Kan extension along `G.op` are filtered and the tensor product of `A` commutes with colimits
over them. -/
@[instance_reducible, ega "0 4.3.3" "special case", ega "IV 10.2.8" "more general"]
noncomputable def pullbackMonoidal : F.Monoidal :=
  letI := pullbackOplaxMonoidal J K A G adj
  haveI := isIso_η_pullback J K A G adj
  haveI := isIso_δ_pullback J K A G adj
  Functor.Monoidal.ofOplaxMonoidal F

/-- The comparison morphism `δ` of `pullbackMonoidal` is that of `pullbackOplaxMonoidal`. -/
lemma pullbackMonoidal_δ (M N : Sheaf J A) :
    letI := pullbackMonoidal J K A G adj
    δ F M N = (letI := pullbackOplaxMonoidal J K A G adj; δ F M N) :=
  rfl

/-- The counit morphism `η` of `pullbackMonoidal` is that of `pullbackOplaxMonoidal`. -/
lemma pullbackMonoidal_η :
    letI := pullbackMonoidal J K A G adj
    η F = (letI := pullbackOplaxMonoidal J K A G adj; η F) :=
  rfl

/-- The adjunction between the inverse image and the pushforward is compatible with the
monoidal structure `pullbackMonoidal` and the lax monoidal structure of the pushforward. -/
lemma isMonoidal_pullbackMonoidal :
    letI := pullbackMonoidal J K A G adj
    adj.IsMonoidal := by
  let := pullbackOplaxMonoidal J K A G adj
  exact ⟨Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj),
    Adjunction.IsMonoidal.leftAdjoint_μ (adj := adj)⟩

end

end Pullback

section CompositionPullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₄} [Category.{v₄} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]
  [HasWeakSheafify K A] [(K.W (A := A)).IsMonoidal]
  [HasWeakSheafify L A] [(L.W (A := A)).IsMonoidal]
  {G₁ : C ⥤ D} {G₂ : D ⥤ E} {G₁₂ : C ⥤ E} (e : G₁ ⋙ G₂ ≅ G₁₂)
  [G₁.IsContinuous J K] [G₂.IsContinuous K L] [G₁₂.IsContinuous J L]
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G₁.op X) A]
  [∀ X : Eᵒᵖ, HasColimitsOfShape (CostructuredArrow G₂.op X) A]
  [∀ X : Eᵒᵖ, HasColimitsOfShape (CostructuredArrow G₁₂.op X) A]
  [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G₁.op X)]
  [∀ X : Eᵒᵖ, IsFiltered (CostructuredArrow G₂.op X)]
  [∀ X : Eᵒᵖ, IsFiltered (CostructuredArrow G₁₂.op X)]
  [∀ (X : Dᵒᵖ) (P Q : Cᵒᵖ ⥤ A), PreservesColimit₂ (CostructuredArrow.proj G₁.op X ⋙ P)
    (CostructuredArrow.proj G₁.op X ⋙ Q) (curriedTensor A)]
  [∀ (X : Eᵒᵖ) (P Q : Dᵒᵖ ⥤ A), PreservesColimit₂ (CostructuredArrow.proj G₂.op X ⋙ P)
    (CostructuredArrow.proj G₂.op X ⋙ Q) (curriedTensor A)]
  [∀ (X : Eᵒᵖ) (P Q : Cᵒᵖ ⥤ A), PreservesColimit₂ (CostructuredArrow.proj G₁₂.op X ⋙ P)
    (CostructuredArrow.proj G₁₂.op X ⋙ Q) (curriedTensor A)]
  {F₁ : Sheaf J A ⥤ Sheaf K A} {F₂ : Sheaf K A ⥤ Sheaf L A} {F₁₂ : Sheaf J A ⥤ Sheaf L A}
  (adj₁ : F₁ ⊣ G₁.sheafPushforwardContinuous A J K)
  (adj₂ : F₂ ⊣ G₂.sheafPushforwardContinuous A K L)
  (adj₁₂ : F₁₂ ⊣ G₁₂.sheafPushforwardContinuous A J L)

attribute [local instance] pushforwardLaxMonoidal

/-- **The composition isomorphism of inverse images is monoidal**: for an isomorphism
`G₁ ⋙ G₂ ≅ G₁₂` of continuous functors, the isomorphism `F₁ ⋙ F₂ ≅ F₁₂` of left adjoints of the
pushforwards induced by the comparison of pushforwards along a composite is a monoidal natural
isomorphism, for the monoidal structures `pullbackMonoidal`. It is the conjugate of the monoidal
comparison of pushforwards, `isMonoidal_sheafPushforwardContinuousComp'_hom`. -/
lemma isMonoidal_leftAdjointCompIso_hom :
    letI := pullbackMonoidal J K A G₁ adj₁
    letI := pullbackMonoidal K L A G₂ adj₂
    letI := pullbackMonoidal J L A G₁₂ adj₁₂
    NatTrans.IsMonoidal (Adjunction.leftAdjointCompIso adj₁ adj₂ adj₁₂
      (Functor.sheafPushforwardContinuousComp' e A J K L)).hom := by
  let := pullbackMonoidal J K A G₁ adj₁
  let := pullbackMonoidal K L A G₂ adj₂
  let := pullbackMonoidal J L A G₁₂ adj₁₂
  have := isMonoidal_pullbackMonoidal J K A G₁ adj₁
  have := isMonoidal_pullbackMonoidal K L A G₂ adj₂
  have := isMonoidal_pullbackMonoidal J L A G₁₂ adj₁₂
  have : NatTrans.IsMonoidal (conjugateEquiv adj₁₂ (adj₁.comp adj₂)
      (Adjunction.leftAdjointCompIso adj₁ adj₂ adj₁₂
        (Functor.sheafPushforwardContinuousComp' e A J K L)).hom) := by
    rw [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
      Equiv.apply_symm_apply]
    infer_instance
  exact Adjunction.isMonoidal_conjugateEquiv_symm adj₁₂ (adj₁.comp adj₂) _

end CompositionPullback

end Stacks.SheafPushforwardMonoidal
