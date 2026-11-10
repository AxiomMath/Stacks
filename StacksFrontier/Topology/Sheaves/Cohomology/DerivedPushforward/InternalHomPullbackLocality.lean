module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTransportClauses
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.FullnessOfExtensionByZeroDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map of Tag 08I3 is local on the target

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  This file shows that the canonical
map of Tag 08I3,

`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)`,

is compatible with restriction to open subspaces of `Y`, which is the step "the question is local
on `Y`" of the proof of Tag 0GM7.

## Main results

* `Transpose.isIso_homComparison_of_isIso_projectionMap`: the comparison of a functor `P` with
  internal hom is invertible as soon as `P` has a left adjoint `L` for which the projection maps
  `L(W ⊗ P A) ⟶ L W ⊗ A` are invertible.
* `Transpose.isIso_projectionMap_of_isIso_unit`: for triangulated categories and a fully faithful
  left adjoint, the projection maps are invertible as soon as `P` kills `H(A, C)` whenever it kills
  `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

/-- A functor applied to two products of morphisms composes like the product of the composites. -/
private theorem map_mkHom_comp_map_mkHom {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂)
    (g' : Y₂ ⟶ Y₃) : T.map (f ×ₘ g) ≫ T.map (f' ×ₘ g') = T.map ((f ≫ f') ×ₘ (g ≫ g')) :=
  (T.map_comp _ _).symm

/-- Naturality of the inverse monoidality comparison in the first tensor factor. -/
private theorem map_mkHom_id_comp_inv_app {D₁ D₂ : Type*} [Category D₁] [Category D₂]
    (P : D₁ ⥤ D₂) (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂) (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)
    {X Y : D₁} (f : X ⟶ Y) (A : D₁) :
    T₂.map (P.map f ×ₘ 𝟙 (P.obj A)) ≫ m.inv.app (Y, A) =
      m.inv.app (X, A) ≫ P.map (T₁.map (f ×ₘ 𝟙 A)) := by
  have hn := m.inv.naturality (f ×ₘ 𝟙 A)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rwa [P.map_id] at hn

section Projection

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)
  {L : D₂ ⥤ D₁} (adj : L ⊣ P)

/-- **The projection map** `L(W ⊗ P A) ⟶ L W ⊗ A` of a functor `P` with a left adjoint `L`: the
transpose under the adjunction of `W ⊗ P A ⟶ P L W ⊗ P A ⟶ P(L W ⊗ A)`, the unit followed by the
monoidality comparison. -/
@[sga "4 IV 10.5" "more general"]
def projectionMap (W : D₂) (A : D₁) : L.obj (T₂.obj (W, P.obj A)) ⟶ T₁.obj (L.obj W, A) :=
  (adj.homEquiv _ _).symm (T₂.map (adj.unit.app W ×ₘ 𝟙 (P.obj A)) ≫ m.inv.app (L.obj W, A))

/-- The transpose of `g ≫ homComparison` is computed through the projection map. -/
theorem homEquiv_symm_e₂_comp_homComparison
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A B : D₁) (W : D₂) (g : W ⟶ P.obj ((H₁.obj (op A)).obj B)) :
    (adj.homEquiv _ _).symm
        (e₂ W (P.obj A) (P.obj B) (g ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B)) =
      projectionMap P T₁ T₂ m adj W A ≫ e₁ _ _ _ ((adj.homEquiv _ _).symm g) := by
  set g' := (adj.homEquiv _ _).symm g
  have hg : g = adj.unit.app W ≫ P.map g' :=
    ((adj.homEquiv _ _).apply_symm_apply g).symm.trans (adj.homEquiv_unit _ _ g')
  have hn := map_mkHom_id_comp_inv_app P T₁ T₂ m g' A
  have he : T₁.map (g' ×ₘ 𝟙 A) ≫ evaluation H₁ T₁ e₁ A B = e₁ _ _ _ g' := by
    rw [evaluation, ← hnat₁, Category.comp_id]
  rw [hnat₂, homComparison_adjoint, homComparisonDatum, hg]
  have hsplit : T₂.map ((adj.unit.app W ≫ P.map g') ×ₘ 𝟙 (P.obj A)) =
      T₂.map (adj.unit.app W ×ₘ 𝟙 (P.obj A)) ≫ T₂.map (P.map g' ×ₘ 𝟙 (P.obj A)) := by
    rw [map_mkHom_comp_map_mkHom, Category.id_comp]
  rw [hsplit, Category.assoc, reassoc_of% hn, ← P.map_comp, he, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- **A functor with a left adjoint whose projection maps are invertible commutes with internal
hom**: the comparison `P H(A, B) ⟶ H(P A, P B)` is invertible.  Precomposition with it is, under
the adjunction and the two tensor–hom bijections, precomposition with the projection map. -/
theorem isIso_homComparison_of_isIso_projectionMap
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A B : D₁) (hπ : ∀ W : D₂, IsIso (projectionMap P T₁ T₂ m adj W A)) :
    IsIso (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) := by
  apply isIso_of_yoneda_map_bijective
  intro W
  have hf : (fun g : W ⟶ P.obj ((H₁.obj (op A)).obj B) =>
      g ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) =
      (e₂ W (P.obj A) (P.obj B)).symm ∘ (adj.homEquiv _ _) ∘
        (fun k => projectionMap P T₁ T₂ m adj W A ≫ k) ∘ e₁ _ _ _ ∘ (adj.homEquiv _ _).symm := by
    funext g
    apply (e₂ W (P.obj A) (P.obj B)).injective
    apply (adj.homEquiv _ _).symm.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [homEquiv_symm_e₂_comp_homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m adj hnat₁ hnat₂ A B W g,
      Equiv.symm_apply_apply]
  rw [hf]
  have := hπ W
  refine (e₂ W (P.obj A) (P.obj B)).symm.bijective.comp
    ((adj.homEquiv _ _).bijective.comp ?_)
  refine Function.Bijective.comp ?_ ((e₁ _ _ _).bijective.comp (adj.homEquiv _ _).symm.bijective)
  exact ⟨fun k k' h => (cancel_epi _).1 h,
    fun k => ⟨inv (projectionMap P T₁ T₂ m adj W A) ≫ k, by simp⟩⟩

/-- The image of the projection map under `P` is the unit followed by the monoidality
comparison. -/
theorem unit_comp_map_projectionMap (W : D₂) (A : D₁) :
    adj.unit.app _ ≫ P.map (projectionMap P T₁ T₂ m adj W A) =
      T₂.map (adj.unit.app W ×ₘ 𝟙 (P.obj A)) ≫ m.inv.app (L.obj W, A) :=
  (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)

/-- If the unit of the adjunction is invertible, `P` carries the projection map to an
isomorphism. -/
theorem isIso_map_projectionMap (hunit : IsIso adj.unit) (W : D₂) (A : D₁) :
    IsIso (P.map (projectionMap P T₁ T₂ m adj W A)) := by
  have h := unit_comp_map_projectionMap P T₁ T₂ m adj W A
  have : IsIso (T₂.map (adj.unit.app W ×ₘ 𝟙 (P.obj A)) ≫ m.inv.app (L.obj W, A)) := by
    have : IsIso (adj.unit.app W ×ₘ 𝟙 (P.obj A)) := by
      rw [isIso_prod_iff]; exact ⟨inferInstance, inferInstance⟩
    infer_instance
  rw [← h] at this
  exact IsIso.of_isIso_comp_left (adj.unit.app _) _

variable [HasZeroObject D₁] [HasZeroObject D₂] [Preadditive D₁] [Preadditive D₂]
  [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [Pretriangulated D₁] [Pretriangulated D₂] [P.CommShift ℤ] [P.IsTriangulated]

include e₁ in
/-- **The projection maps of a fully faithful left adjoint are invertible** as soon as `P` kills
`H(A, C)` whenever it kills `C`.  The cone `C` of the projection map is killed by `P`, the unit
being invertible, so there are no morphisms into it from `L W ⊗ A` — they correspond to morphisms
`W ⟶ P H(A, C)` — nor from the shift of `L(W ⊗ P A)`; the long exact sequence then forces `C` to
vanish. -/
theorem isIso_projectionMap_of_isIso_unit (hunit : IsIso adj.unit)
    (hker : ∀ (A C : D₁), IsZero (P.obj C) → IsZero (P.obj ((H₁.obj (op A)).obj C)))
    (W : D₂) (A : D₁) : IsIso (projectionMap P T₁ T₂ m adj W A) := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle (projectionMap P T₁ T₂ m adj W A)
  have hPπ := isIso_map_projectionMap P T₁ T₂ m adj hunit W A
  have hPC : IsZero (P.obj C) :=
    Triangle.isZero₃_of_isIso₁ _ (P.map_distinguished _ hT) hPπ
  have hsub₂ : ∀ f f' : T₁.obj (L.obj W, A) ⟶ C, f = f' := by
    intro f f'
    have hz : IsZero (P.obj ((H₁.obj (op A)).obj C)) := hker A C hPC
    exact (e₁ _ _ _).symm.injective ((adj.homEquiv _ _).injective (hz.eq_of_tgt _ _))
  have hsub₁ : ∀ f f' : (L.obj (T₂.obj (W, P.obj A)))⟦(1 : ℤ)⟧ ⟶ C, f = f' := by
    intro f f'
    have hz : IsZero (P.obj (C⟦(-1 : ℤ)⟧)) :=
      (Functor.map_isZero (shiftFunctor D₂ (-1 : ℤ)) hPC).of_iso
        ((P.commShiftIso (-1 : ℤ)).app C)
    exact ((shiftEquiv D₁ (1 : ℤ)).toAdjunction.homEquiv _ _).injective
      ((adj.homEquiv _ _).injective (hz.eq_of_tgt _ _))
  have hC : IsZero C := by
    rw [IsZero.iff_id_eq_zero]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ hT (𝟙 C)
      ((Category.comp_id _).trans (hsub₂ _ _))
    rw [hk, hsub₁ k 0, comp_zero]
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hC

end Projection

section Composite

variable {D₁ D₂ D₃ : Type*} [Category D₁] [Category D₂] [Category D₃]
  (P : D₁ ⥤ D₂) (P' : D₂ ⥤ D₃)
  (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂) (H₃ : D₃ᵒᵖ ⥤ D₃ ⥤ D₃)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂) (T₃ : D₃ × D₃ ⥤ D₃)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (e₃ : ∀ A B C : D₃, (A ⟶ (H₃.obj (op B)).obj C) ≃ (T₃.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂) (m' : T₂ ⋙ P' ≅ P'.prod P' ⋙ T₃)

/-- The monoidality comparison of a composite: that of the first functor, carried by the second,
followed by that of the second. -/
def compTensorIso : T₁ ⋙ (P ⋙ P') ≅ (P ⋙ P').prod (P ⋙ P') ⋙ T₃ :=
  NatIso.ofComponents (fun X => P'.mapIso (m.app X) ≪≫ m'.app (P.obj X.1, P.obj X.2))
    (fun {X Y} f => by
      have h₁ := m.hom.naturality f
      have h₂ := m'.hom.naturality (P.map f.1 ×ₘ P.map f.2)
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at h₁ h₂ ⊢
      dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      rw [← Category.assoc, ← P'.map_comp, h₁, P'.map_comp, Category.assoc, h₂]
      exact (Category.assoc _ _ _).symm)

/-- The inverse of `compTensorIso` at `X` is the inverse comparison of the second functor
followed by the image under `P'` of the inverse comparison of the first. -/
theorem compTensorIso_inv_app (X : D₁ × D₁) :
    (compTensorIso P P' T₁ T₂ T₃ m m').inv.app X =
      m'.inv.app (P.obj X.1, P.obj X.2) ≫ P'.map (m.inv.app X) := rfl

/-- **The comparison of a composite functor with internal hom is the composite of the
comparisons**: `P'(P H(A, B)) ⟶ P' H(P A, P B) ⟶ H(P' P A, P' P B)`. -/
theorem homComparison_comp
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂) (hnat₃ : TensorHomEquivNaturalLeft H₃ T₃ e₃)
    (A B : D₁) :
    homComparison (P ⋙ P') H₁ H₃ T₁ T₃ e₁ e₃ (compTensorIso P P' T₁ T₂ T₃ m m') A B =
      P'.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) ≫
        homComparison P' H₂ H₃ T₂ T₃ e₂ e₃ m' (P.obj A) (P.obj B) := by
  apply (e₃ _ _ _).injective
  have hn := map_mkHom_id_comp_inv_app P' T₂ T₃ m' (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B)
    (P.obj A)
  have he : T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) ≫
      evaluation H₂ T₂ e₂ (P.obj A) (P.obj B) = homComparisonDatum P H₁ T₁ T₂ e₁ m A B := by
    rw [evaluation, ← hnat₂, Category.comp_id, homComparison_adjoint]
  have hR : e₃ _ _ _ (P'.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) ≫
        homComparison P' H₂ H₃ T₂ T₃ e₂ e₃ m' (P.obj A) (P.obj B)) =
      m'.inv.app (P.obj ((H₁.obj (op A)).obj B), P.obj A) ≫
        P'.map (m.inv.app ((H₁.obj (op A)).obj B, A)) ≫
          P'.map (P.map (evaluation H₁ T₁ e₁ A B)) := by
    rw [hnat₃, homComparison_adjoint, homComparisonDatum, reassoc_of% hn, ← P'.map_comp, he,
      homComparisonDatum, P'.map_comp]
  exact (homComparison_adjoint (P ⋙ P') H₁ H₃ T₁ T₃ e₁ e₃ _ A B).trans
    ((Category.assoc _ _ _).trans hR.symm)

end Composite

section Congr

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  {P P' : D₁ ⥤ D₂} (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂) (m' : T₁ ⋙ P' ≅ P'.prod P' ⋙ T₂) (c : P ≅ P')

/-- **The comparison with internal hom is invariant under an isomorphism of monoidal
functors.**  If `c : P ≅ P'` carries the monoidality comparison of `P` to that of `P'`, the
comparison of `P'` is that of `P` conjugated by `c`. -/
theorem homComparison_congr
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂) (hdin₂ : TensorHomEquivDinatural H₂ T₂ e₂)
    (htgt₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (hm : ∀ X : D₁ × D₁, m'.inv.app X =
      T₂.map (c.inv.app X.1 ×ₘ c.inv.app X.2) ≫ m.inv.app X ≫ c.hom.app (T₁.obj X))
    (A B : D₁) :
    homComparison P' H₁ H₂ T₁ T₂ e₁ e₂ m' A B =
      c.inv.app _ ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫
        (H₂.map (c.inv.app A).op).app (P.obj B) ≫ (H₂.obj (op (P'.obj A))).map (c.hom.app B) := by
  apply (e₂ _ _ _).injective
  have hT : T₂.map (𝟙 (P'.obj ((H₁.obj (op A)).obj B)) ×ₘ c.inv.app A) ≫
      T₂.map (c.inv.app ((H₁.obj (op A)).obj B) ×ₘ 𝟙 (P.obj A)) =
      T₂.map (c.inv.app ((H₁.obj (op A)).obj B) ×ₘ c.inv.app A) := by
    rw [map_mkHom_comp_map_mkHom, Category.id_comp, Category.comp_id]
  have hR : e₂ _ _ _ (c.inv.app _ ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫
        (H₂.map (c.inv.app A).op).app (P.obj B) ≫ (H₂.obj (op (P'.obj A))).map (c.hom.app B)) =
      T₂.map (c.inv.app ((H₁.obj (op A)).obj B) ×ₘ c.inv.app A) ≫
        m.inv.app ((H₁.obj (op A)).obj B, A) ≫ P.map (evaluation H₁ T₁ e₁ A B) ≫
          c.hom.app B := by
    have h₁ := htgt₂ _ _ _ _ (c.hom.app B) (c.inv.app ((H₁.obj (op A)).obj B) ≫
      homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫ (H₂.map (c.inv.app A).op).app (P.obj B))
    have h₂ := hdin₂ _ _ _ _ (c.inv.app A) (c.inv.app ((H₁.obj (op A)).obj B) ≫
      homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B)
    simp only [Category.assoc] at h₁ h₂
    rw [h₁, h₂, hnat₂, homComparison_adjoint, homComparisonDatum, reassoc_of% hT]
    simp only [Category.assoc]
  have hc := c.hom.naturality (evaluation H₁ T₁ e₁ A B)
  rw [hR, homComparison_adjoint, homComparisonDatum, hm]
  simp only [Category.assoc]
  rw [hc]

/-- `homComparison_congr` with the compatibility of the monoidality comparisons stated on the
forward maps: `c` is a monoidal natural isomorphism. -/
theorem homComparison_congr'
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂) (hdin₂ : TensorHomEquivDinatural H₂ T₂ e₂)
    (htgt₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (hm : ∀ X : D₁ × D₁, c.hom.app (T₁.obj X) ≫ m'.hom.app X =
      m.hom.app X ≫ T₂.map (c.hom.app X.1 ×ₘ c.hom.app X.2))
    (A B : D₁) :
    homComparison P' H₁ H₂ T₁ T₂ e₁ e₂ m' A B =
      c.inv.app _ ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫
        (H₂.map (c.inv.app A).op).app (P.obj B) ≫ (H₂.obj (op (P'.obj A))).map (c.hom.app B) := by
  refine homComparison_congr H₁ H₂ T₁ T₂ e₁ e₂ m m' c hnat₂ hdin₂ htgt₂ (fun X => ?_) A B
  have h := hm X
  have hcc : T₂.map (c.hom.app X.1 ×ₘ c.hom.app X.2) ≫ T₂.map (c.inv.app X.1 ×ₘ c.inv.app X.2) =
      𝟙 _ := by
    rw [map_mkHom_comp_map_mkHom, ← T₂.map_id]
    simp
  apply (cancel_epi (m'.hom.app X)).1
  rw [Iso.hom_inv_id_app]
  have h' : m'.hom.app X = c.inv.app (T₁.obj X) ≫ m.hom.app X ≫
      T₂.map (c.hom.app X.1 ×ₘ c.hom.app X.2) := by
    rw [← h, Iso.inv_hom_id_app_assoc]
  rw [h']
  simp only [Category.assoc]
  rw [reassoc_of% hcc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rfl

end Congr

section BridgedComposite

variable {CY CX CX' : Type*} [Category CY] [Category CX] [Category CX']
  (G : CY ⥤ CX) (F : CX ⥤ CX') (H : CY ⥤ CX') (c : G ⋙ F ≅ H)
  {pY qY : CY × CY ⥤ CY} {pX qX : CX × CX ⥤ CX} {pX' qX' : CX' × CX' ⥤ CX'}
  (bY : pY ≅ qY) (bX : pX ≅ qX) (bX' : pX' ≅ qX')
  (μg : pY ⋙ G ≅ G.prod G ⋙ pX) (μf : pX ⋙ F ≅ F.prod F ⋙ pX')
  (μh : pY ⋙ H ≅ H.prod H ⋙ pX')

/-- A monoidality comparison conjugated by isomorphisms of the tensor bifunctors on each
side. -/
abbrev bridgeTensorIso {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {p q : C × C ⥤ C} {p' q' : D × D ⥤ D} (b : p ≅ q) (b' : p' ≅ q')
    (μ : p ⋙ P ≅ P.prod P ⋙ p') : q ⋙ P ≅ P.prod P ⋙ q' :=
  Functor.isoWhiskerRight b.symm P ≪≫ μ ≪≫ Functor.isoWhiskerLeft (P.prod P) b'

/-- **A composition law for monoidality comparisons survives conjugation by isomorphisms of the
tensor bifunctors.** -/
theorem bridgeTensorIso_comp
    (hlaw : ∀ X : CY × CY, c.hom.app (pY.obj X) ≫ μh.hom.app X =
      F.map (μg.hom.app X) ≫ μf.hom.app (G.obj X.1, G.obj X.2) ≫
        pX'.map (c.hom.app X.1 ×ₘ c.hom.app X.2))
    (X : CY × CY) :
    c.hom.app (qY.obj X) ≫ (bridgeTensorIso H bY bX' μh).hom.app X =
      (compTensorIso G F qY qX qX' (bridgeTensorIso G bY bX μg)
          (bridgeTensorIso F bX bX' μf)).hom.app X ≫
        qX'.map (c.hom.app X.1 ×ₘ c.hom.app X.2) := by
  have hc := c.hom.naturality (bY.inv.app X)
  have hb := bX'.hom.naturality (c.hom.app X.1 ×ₘ c.hom.app X.2)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at hc hb
  dsimp only [compTensorIso, bridgeTensorIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.prod_obj]
  rw [← Category.assoc, ← hc, Category.assoc, reassoc_of% (hlaw X), hb]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc (bX.hom.app _), Iso.hom_inv_id_app, F.map_id, Category.id_comp]

end BridgedComposite

/-- A morphism conjugate to another by isomorphisms is carried by any functor to an isomorphism
exactly when the other is. -/
theorem isIso_map_iff_of_eq_conj {C E : Type*} [Category C] [Category E] (Φ : C ⥤ E)
    {A A' B B' : C} (φ : A ⟶ B) (ψ : A' ⟶ B') (a : A ⟶ A') (d : B' ⟶ B) [IsIso a] [IsIso d]
    (h : φ = a ≫ ψ ≫ d) : IsIso (Φ.map φ) ↔ IsIso (Φ.map ψ) := by
  subst h
  rw [Φ.map_comp, Φ.map_comp]
  constructor
  · intro h
    have : IsIso (Φ.map ψ ≫ Φ.map d) := IsIso.of_isIso_comp_left (Φ.map a) (Φ.map ψ ≫ Φ.map d)
    exact IsIso.of_isIso_comp_right (Φ.map ψ) (Φ.map d)
  · intro h
    infer_instance

/-- Two composites, the second factor of the first and the first factor of the second carried to
isomorphisms by `Φ`: if `Φ` inverts one composite exactly when it inverts the other, then it
inverts the first factor of the first exactly when it inverts the second factor of the second. -/
theorem isIso_map_iff_of_comp_iff {C E : Type*} [Category C] [Category E] (Φ : C ⥤ E)
    {A B D A' B' D' : C} {x : A ⟶ B} {y : B ⟶ D} {z : A' ⟶ B'} {w : B' ⟶ D'}
    (hy : IsIso (Φ.map y)) (hz : IsIso (Φ.map z))
    (h : IsIso (Φ.map (x ≫ y)) ↔ IsIso (Φ.map (z ≫ w))) :
    IsIso (Φ.map x) ↔ IsIso (Φ.map w) := by
  rw [Φ.map_comp, Φ.map_comp] at h
  exact ⟨fun _ => have := h.1 inferInstance; IsIso.of_isIso_comp_left (Φ.map z) (Φ.map w),
    fun _ => have := h.2 inferInstance; IsIso.of_isIso_comp_right (Φ.map x) (Φ.map y)⟩

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose

namespace Stacks.Cohomology.DerivedOpenImmersion

open _root_.Stacks.AlgebraicGeometry TopologicalSpace ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_jStar preservesFiniteColimits_jStar

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) (U : TopologicalSpace.Opens X.carrier)

/-- **Derived extension by zero is left adjoint to the derived pullback along the inclusion of an
open subspace.** -/
def jShriekDerivedPullbackAdjunction :
    (jShriek U (structureSheafRing X)).mapDerivedCategory ⊣
      (derivedPullback (X.ofRestrict U.isOpenEmbedding) :
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
          DerivedCategory (SheafOfModules.{u} (resRing U (structureSheafRing X)))) :=
  (Adjunction.mapDerivedCategory (jShriekAdjunction U (structureSheafRing X))).ofNatIsoRight
    (derivedPullbackOpenRestrictionIso X U).symm

/-- The unit of `jShriekDerivedPullbackAdjunction` is invertible: derived extension by zero is
fully faithful. -/
instance isIso_jShriekDerivedPullbackAdjunction_unit :
    IsIso (jShriekDerivedPullbackAdjunction X U).unit := by
  let := Stacks.DerivedGlueing.fullyFaithful_jShriek_mapDerivedCategory (structureSheafRing X) U
  have := (Stacks.DerivedGlueing.fullyFaithful_jShriek_mapDerivedCategory
    (structureSheafRing X) U).full
  have := (Stacks.DerivedGlueing.fullyFaithful_jShriek_mapDerivedCategory
    (structureSheafRing X) U).faithful
  exact Adjunction.unit_isIso_of_L_fully_faithful _

/-- An object of a derived category is zero exactly when its image under an exact functor
composed with any functor isomorphic to it is, degree by degree. -/
theorem isZero_obj_iff_of_iso_mapDerivedCategory {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : DerivedCategory C ⥤ DerivedCategory D) (θ : P ≅ F.mapDerivedCategory)
    (Z : DerivedCategory C) :
    IsZero (P.obj Z) ↔ ∀ n : ℤ, IsZero (F.obj ((DerivedCategory.homologyFunctor C n).obj Z)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ?_
  exact Iso.isZero_iff ((DerivedCategory.homologyFunctor D n).mapIso (θ.app Z) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app Z)

end Stacks.Cohomology.DerivedOpenImmersion

namespace Stacks.Cohomology.DerivedOpenImmersion

open _root_.Stacks.AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) (U : TopologicalSpace.Opens X.carrier)

/-- Pullback of a sheaf of modules along the inclusion of an open subspace vanishes exactly when
its restriction to the slice site over the open does. -/
theorem isZero_modulePullback_ofRestrict_iff (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsZero ((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj M) ↔
      IsZero ((SheafOfModules.overFunctor (structureSheafRing X) U).obj M) :=
  ((AlgebraicGeometry.SheafOfModules.overFunctorIsoPullback X U M).isZero_iff).symm.trans
    ⟨fun h => (Functor.map_isZero
        (U.sheafOfModulesEquivOver (structureSheafRing X)).inverse h).of_iso
        ((U.sheafOfModulesEquivOver (structureSheafRing X)).unitIso.app _),
      fun h => Functor.map_isZero (U.sheafOfModulesEquivOver (structureSheafRing X)).functor h⟩

/-- **The derived pullback along the inclusion of an open subspace vanishes exactly when the
derived restriction to the slice site over the open does.** -/
theorem isZero_derivedPullback_ofRestrict_iff
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsZero ((derivedPullback (X.ofRestrict U.isOpenEmbedding)).obj Z) ↔
      IsZero ((SheafOfModules.overFunctor (structureSheafRing X) U).mapDerivedCategory.obj Z) := by
  rw [isZero_obj_iff_of_iso_mapDerivedCategory _ _
      (derivedPullbackOpenImmersionIso (X.ofRestrict U.isOpenEmbedding)) Z,
    isZero_obj_iff_of_iso_mapDerivedCategory _ _ (Iso.refl _) Z]
  exact forall_congr' fun n => isZero_modulePullback_ofRestrict_iff X U _

-- `structureSheafRing` and `Stacks.SheafOfModules.Tensor.ringSheaf` are the same sheaf of rings
-- by `rfl`, and the statements below mix them.  `structureSheafRing` is `@[instance_reducible]`,
-- so it already unfolds both at `implicit` transparency and in instance search, and naming it
-- here would only take the latter away.  Its reduct stops at an explicit-constructor
-- projection, while `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`;
-- these two Mathlib definitions are the gap between them.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **The derived pullback to an open subspace kills `R𝓗om(A, C)` as soon as it kills `C`.**
Restriction to the slice site over the open commutes with the derived internal hom
(Tag 08JB), and the derived internal hom into a zero object is zero. -/
theorem isZero_derivedPullback_ofRestrict_derivedSheafHom
    (A C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hC : IsZero ((Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor
      (X.ofRestrict U.isOpenEmbedding)).obj C)) :
    IsZero ((Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor
      (X.ofRestrict U.isOpenEmbedding)).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op A)).obj C)) := by
  have hC' := (isZero_derivedPullback_ofRestrict_iff X U C).1 hC
  refine (isZero_derivedPullback_ofRestrict_iff X U _).2 ?_
  have := AlgebraicGeometry.RingedSite.additive_derivedSheafHom_obj
    ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)
    ((SheafOfModules.overFunctor (structureSheafRing X) U).mapDerivedCategory.obj A)
  exact (Functor.map_isZero ((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)).obj
        (op ((SheafOfModules.overFunctor (structureSheafRing X) U).mapDerivedCategory.obj A)))
      hC').of_iso
    ((AlgebraicGeometry.RingedSite.derivedHomRestriction
      (Stacks.SheafOfModules.ringedSite X.sheaf) U).iso A C)

/-- **Tag 08I3 along the inclusion of an open subspace is invertible**: for an open `U` of a
ringed space `X` and arbitrary `K, M ∈ D(𝒪_X)`, the canonical map

`R𝓗om(K, M)|_U ⟶ R𝓗om(K|_U, M|_U)`

is an isomorphism.  Derived extension by zero is a fully faithful left adjoint of the restriction,
and the restriction kills `R𝓗om(K, C)` whenever it kills `C`, so the projection maps of the
adjunction are invertible. -/
theorem isIso_derivedPullbackSheafHomMap_ofRestrict
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) :
    IsIso (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap
      (X.ofRestrict U.isOpenEmbedding) K M) := by
  let : (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor
      (X.ofRestrict U.isOpenEmbedding)).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift _
  have : (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor
      (X.ofRestrict U.isOpenEmbedding)).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated _
  let adj : (ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory ⊣
      Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor
        (X.ofRestrict U.isOpenEmbedding) := jShriekDerivedPullbackAdjunction X U
  have hunit : IsIso adj.unit := isIso_jShriekDerivedPullbackAdjunction_unit X U
  have hπ := fun W =>
    Stacks.Cohomology.DerivedInternalHomPullback.Transpose.isIso_projectionMap_of_isIso_unit
      (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor
        (X.ofRestrict U.isOpenEmbedding))
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf)
      (Stacks.Cohomology.DerivedInternalHomPullback.internalHomTensorUncurried X)
      (Stacks.Cohomology.DerivedInternalHomPullback.internalHomTensorUncurried
        (X.restrict U.isOpenEmbedding))
      (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite X.sheaf) A B C).toEquiv)
      (Stacks.Cohomology.DerivedInternalHomPullback.pullbackTensorIso
        (X.ofRestrict U.isOpenEmbedding)) adj hunit
      (fun A C hC => isZero_derivedPullback_ofRestrict_derivedSheafHom X U A C hC) W K
  exact DerivedInternalHomPullback.Transpose.isIso_homComparison_of_isIso_projectionMap
    (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor
      (X.ofRestrict U.isOpenEmbedding))
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom (X.restrict U.isOpenEmbedding).sheaf)
    (Stacks.Cohomology.DerivedInternalHomPullback.internalHomTensorUncurried X)
    (Stacks.Cohomology.DerivedInternalHomPullback.internalHomTensorUncurried
      (X.restrict U.isOpenEmbedding))
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X.sheaf) A B C).toEquiv)
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite (X.restrict U.isOpenEmbedding).sheaf) A B C).toEquiv)
    (Stacks.Cohomology.DerivedInternalHomPullback.pullbackTensorIso
      (X.ofRestrict U.isOpenEmbedding)) adj
    (Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace X)
    (Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace
      (X.restrict U.isOpenEmbedding)) K M hπ

end Stacks.Cohomology.DerivedOpenImmersion


namespace Stacks.Cohomology.DerivedInternalHomPullback

open _root_.Stacks.AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

-- As above: `structureSheafRing` is `@[instance_reducible]` and must stay so, since instance
-- search has to see through it to find the additive structure of a hom group of the derived
-- category; only the two Mathlib definitions bridging its reduct with
-- `Tensor.ringSheaf X.sheaf` need the local attribute.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

-- `Tensor.ringSheaf` is the third definition in that bridge, and it is seated one level lower,
-- at `instance_reducible`, because the three faults it answers for all live at `.instances`
-- transparency or below.  Per Lean core's reducibility attributes, `implicitReducible`
-- unfolds at `TransparencyMode.implicit`, *strictly above* `.instances`, while
-- `instanceReducible` unfolds at `.instances` and at every level above it; `.instances` is
-- where `rw` does its keyed matching and where instance search runs.  With `Tensor.ringSheaf`
-- left semireducible, `derivedPullbackSheafHomMap_comp`'s `rw` reported the pattern
-- `Transpose.homComparison (derivedPullbackFunctor g ⋙ derivedPullbackFunctor f) …` absent from
-- a target that displays as exactly that; `isIso_map_derivedPullbackSheafHomMap_comp_iff` could
-- not synthesize `IsIso` for a component of the composition isomorphism of Stacks 0D5S; and the
-- two statements of the `Cover` section below asked for `HasDerivedCategory` and for
-- `DerivedCategory.isIso_iff` at `SheafOfModules (structureSheafRing X)` and could not see that
-- that is the category their terms are written in.

section Composite

variable {X Y Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Stacks 079U along `g` then `f`, compared with Stacks 079U along `f ≫ g`, componentwise. -/
theorem derivedPullbackTensorIso_comp_app
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
          ((pullbackTensorUncurried Z).obj W) ≫
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso (f ≫ g)).hom.app W =
      (derivedPullbackFunctor f).map
          ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g).hom.app W) ≫
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app
          ((derivedPullbackFunctor g).obj W.1, (derivedPullbackFunctor g).obj W.2) ≫
        (pullbackTensorUncurried X).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app W.1 ×ₘ
            (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app W.2) :=
  NatTrans.congr_app (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp f g) W

/-- **Tag 08I3 along a composite.**  The canonical map along `f ≫ g` is the derived pullback
along `f` of the canonical map along `g`, followed by the canonical map along `f`, read through
the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S. -/
theorem derivedPullbackSheafHomMap_comp
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    derivedPullbackSheafHomMap (f ≫ g) K M =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).inv.app _ ≫
        ((derivedPullbackFunctor f).map (derivedPullbackSheafHomMap g K M) ≫
          derivedPullbackSheafHomMap f ((derivedPullbackFunctor g).obj K)
            ((derivedPullbackFunctor g).obj M)) ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            f g).inv.app K).op).app
            ((derivedPullbackFunctor g ⋙ derivedPullbackFunctor f).obj M) ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPullbackFunctor (f ≫ g)).obj K))).map
            ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
              f g).hom.app M) := by
  have h₁ := Transpose.homComparison_congr' (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Z)
    (internalHomTensorUncurried X) (tensorHomBijection Z) (tensorHomBijection X)
    (Transpose.compTensorIso (derivedPullbackFunctor g) (derivedPullbackFunctor f)
      (internalHomTensorUncurried Z) (internalHomTensorUncurried Y) (internalHomTensorUncurried X)
      (pullbackTensorIso g) (pullbackTensorIso f))
    (pullbackTensorIso (f ≫ g))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g)
    (tensorHomEquivNaturalLeft_ringedSpace X) (tensorHomEquivDinatural_ringedSpace X)
    (curriedTargetNatural_ringedSpace X)
    (Transpose.bridgeTensorIso_comp (derivedPullbackFunctor g) (derivedPullbackFunctor f)
      (derivedPullbackFunctor (f ≫ g))
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g)
      (tensorBridge Z) (tensorBridge Y) (tensorBridge X)
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g)
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f)
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso (f ≫ g))
      (derivedPullbackTensorIso_comp_app f g)) K M
  have h₂ := Transpose.homComparison_comp (derivedPullbackFunctor g) (derivedPullbackFunctor f)
    (Stacks.SheafOfModules.derivedSheafHom Z.sheaf) (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Z)
    (internalHomTensorUncurried Y) (internalHomTensorUncurried X) (tensorHomBijection Z)
    (tensorHomBijection Y) (tensorHomBijection X) (pullbackTensorIso g) (pullbackTensorIso f)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivNaturalLeft_ringedSpace X) K M
  refine h₁.trans ?_
  congr 2

/-- Tag 08I3 along a composite is invertible after any functor exactly when the derived pullback
along `f` of the map along `g`, followed by the map along `f`, is. -/
theorem isIso_map_derivedPullbackSheafHomMap_comp_iff {E : Type*} [Category E]
    (Φ : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ⥤ E)
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    IsIso (Φ.map (derivedPullbackSheafHomMap (f ≫ g) K M)) ↔
      IsIso (Φ.map ((derivedPullbackFunctor f).map (derivedPullbackSheafHomMap g K M) ≫
          derivedPullbackSheafHomMap f ((derivedPullbackFunctor g).obj K)
            ((derivedPullbackFunctor g).obj M))) :=
  @Transpose.isIso_map_iff_of_eq_conj _ _ _ _ Φ _ _ _ _ _ _ _ _
    (Iso.isIso_inv
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).app
        (((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op K)).obj M)))
    (Iso.isIso_hom
      ((((Stacks.SheafOfModules.derivedSheafHom X.sheaf).mapIso
              ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).app
                K).symm.op).app
            ((derivedPullbackFunctor g ⋙ derivedPullbackFunctor f).obj M)) ≪≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
            (op ((derivedPullbackFunctor (f ≫ g)).obj K))).mapIso
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).app M)))
    (derivedPullbackSheafHomMap_comp f g K M)

/-- Tag 08I3 along a composite is invertible exactly when the derived pullback along `f` of the
map along `g`, followed by the map along `f`, is. -/
theorem isIso_derivedPullbackSheafHomMap_comp_iff
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    IsIso (derivedPullbackSheafHomMap (f ≫ g) K M) ↔
      IsIso ((derivedPullbackFunctor f).map (derivedPullbackSheafHomMap g K M) ≫
          derivedPullbackSheafHomMap f ((derivedPullbackFunctor g).obj K)
            ((derivedPullbackFunctor g).obj M)) :=
  isIso_map_derivedPullbackSheafHomMap_comp_iff f g (𝟭 _) K M

end Composite

section Restriction

open Stacks.Cohomology.HigherDirectImage

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y) (V : TopologicalSpace.Opens Y)

/-- **Tag 08I3 is compatible with restriction to an open subspace of the target**, after any
functor.  For an open `V ⊆ Y`, the restriction to `h⁻¹(V)` of the canonical map along `h` is
carried by `Φ` to an isomorphism exactly when the canonical map along
`h|_{h⁻¹(V)} : h⁻¹(V) ⟶ V`, at the restrictions of `K` and `M`, is. -/
theorem isIso_map_map_derivedPullbackSheafHomMap_iff_restrict {E : Type*} [Category E]
    (Φ : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (restrictToOpen X (preimageOpen h V))) ⥤ E)
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso (Φ.map ((derivedPullbackFunctor (openSubspaceInclusion X (preimageOpen h V))).map
        (derivedPullbackSheafHomMap h K M))) ↔
      IsIso (Φ.map (derivedPullbackSheafHomMap (restrictedMorphism h V)
        ((derivedPullbackFunctor (openSubspaceInclusion Y V)).obj K)
        ((derivedPullbackFunctor (openSubspaceInclusion Y V)).obj M))) := by
  have h₁ := isIso_map_derivedPullbackSheafHomMap_comp_iff
    (openSubspaceInclusion X (preimageOpen h V)) h Φ K M
  have h₂ := isIso_map_derivedPullbackSheafHomMap_comp_iff (restrictedMorphism h V)
    (openSubspaceInclusion Y V) Φ K M
  rw [restrictedMorphism_comp_openSubspaceInclusion h V, h₂] at h₁
  have hW : IsIso (derivedPullbackSheafHomMap (openSubspaceInclusion X (preimageOpen h V))
      ((derivedPullbackFunctor h).obj K) ((derivedPullbackFunctor h).obj M)) :=
    Stacks.Cohomology.DerivedOpenImmersion.isIso_derivedPullbackSheafHomMap_ofRestrict X
      (preimageOpen h V) ((derivedPullbackFunctor h).obj K) ((derivedPullbackFunctor h).obj M)
  have hV : IsIso (derivedPullbackSheafHomMap (openSubspaceInclusion Y V) K M) :=
    Stacks.Cohomology.DerivedOpenImmersion.isIso_derivedPullbackSheafHomMap_ofRestrict Y V K M
  have hV' : IsIso ((derivedPullbackFunctor (restrictedMorphism h V)).map
      (derivedPullbackSheafHomMap (openSubspaceInclusion Y V) K M)) :=
    Iso.isIso_hom ((derivedPullbackFunctor (restrictedMorphism h V)).mapIso (@asIso _ _ _ _ _ hV))
  exact Transpose.isIso_map_iff_of_comp_iff Φ (Functor.map_isIso Φ _) (Functor.map_isIso Φ _)
    h₁.symm

/-- **Tag 08I3 is compatible with restriction to an open subspace of the target.**  For an open
`V ⊆ Y`, the restriction to `h⁻¹(V)` of the canonical map along `h` is invertible exactly when the
canonical map along `h|_{h⁻¹(V)} : h⁻¹(V) ⟶ V` is, at the restrictions of `K` and `M`. -/
theorem isIso_map_derivedPullbackSheafHomMap_iff_restrict
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso ((derivedPullbackFunctor (openSubspaceInclusion X (preimageOpen h V))).map
        (derivedPullbackSheafHomMap h K M)) ↔
      IsIso (derivedPullbackSheafHomMap (restrictedMorphism h V)
        ((derivedPullbackFunctor (openSubspaceInclusion Y V)).obj K)
        ((derivedPullbackFunctor (openSubspaceInclusion Y V)).obj M)) :=
  isIso_map_map_derivedPullbackSheafHomMap_iff_restrict h V (𝟭 _) K M

end Restriction

section Cover

open Stacks.Cohomology.HigherDirectImage

/-- Restriction to an open subspace commutes with cohomology: a cohomology map of the derived
restriction is invertible exactly when the restriction of the cohomology map is. -/
theorem isIso_homologyMap_derivedPullback_openSubspaceInclusion_iff
    {X : AlgebraicGeometry.RingedSpace.{u, u}} (W : TopologicalSpace.Opens X)
    {A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)}
    (f : A ⟶ B) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((derivedPullbackFunctor (openSubspaceInclusion X W)).map f)) ↔
      IsIso ((ExtensionByZeroModules.jStar W (structureSheafRing X)).map
        ((DerivedCategory.homologyFunctor
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) n).map f)) := by
  have : AlgebraicGeometry.SheafedSpace.IsOpenImmersion (openSubspaceInclusion X W) :=
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict X W.isOpenEmbedding
  have : (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion X W)).Additive :=
    RingedSpaceModuleAdjunction.modulePullback_additive _
  have : (RingedSpaceModuleAdjunction.modulePullback
      (openSubspaceInclusion X W)).PreservesHomology :=
    Stacks.Cohomology.DerivedOpenImmersion.modulePullbackOpenImmersion_preservesHomology _
  have : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion X W)) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion X W)) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let e : derivedPullbackFunctor (openSubspaceInclusion X W) ⋙ DerivedCategory.homologyFunctor
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X W)) n ≅
      DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) n ⋙
        ExtensionByZeroModules.jStar W (structureSheafRing X) :=
    Functor.isoWhiskerRight
        (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
          (openSubspaceInclusion X W)) _ ≪≫
      StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion X W)) n ≪≫
      Functor.isoWhiskerLeft _ (Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso X W)
  exact NatIso.isIso_map_iff e f

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **Tag 08I3 is local on the target, degree by degree.**  If every point `x` of `X` has an open
neighbourhood `V` of `h(x)` in `Y` such that the canonical map along `h|_{h⁻¹(V)} : h⁻¹(V) ⟶ V`, at
the restrictions of `K` and `M`, is invertible on degree-`n` cohomology, then so is the canonical
map along `h`. -/
theorem isIso_homologyMap_derivedPullbackSheafHomMap_of_local (n : ℤ)
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hloc : ∀ x : X.carrier, ∃ V : TopologicalSpace.Opens Y, h.hom.base x ∈ V ∧
      IsIso ((DerivedCategory.homologyFunctor _ n).map
        (derivedPullbackSheafHomMap (restrictedMorphism h V)
          ((derivedPullbackFunctor (openSubspaceInclusion Y V)).obj K)
          ((derivedPullbackFunctor (openSubspaceInclusion Y V)).obj M)))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map (derivedPullbackSheafHomMap h K M)) := by
  choose V hxV hV using hloc
  refine Stacks.Cohomology.isIso_of_isIso_jStar_map_of_iSup_eq_top (structureSheafRing X)
    (fun x => preimageOpen h (V x)) ?_ _ fun x => ?_
  · refine eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  · refine (isIso_homologyMap_derivedPullback_openSubspaceInclusion_iff (preimageOpen h (V x))
      _ n).1 ?_
    exact (isIso_map_map_derivedPullbackSheafHomMap_iff_restrict h (V x)
      (DerivedCategory.homologyFunctor _ n) K M).2 (hV x)

/-- **Tag 08I3 is local on the target.**  If the open subsets `V i` cover `Y` and the canonical
map along each restriction `h|_{h⁻¹(V i)} : h⁻¹(V i) ⟶ V i`, at the restrictions of `K` and `M`,
is invertible, then so is the canonical map along `h`. -/
theorem isIso_derivedPullbackSheafHomMap_of_cover {ι : Type*}
    (V : ι → TopologicalSpace.Opens Y) (hV : iSup V = ⊤)
    (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hloc : ∀ i, IsIso (derivedPullbackSheafHomMap (restrictedMorphism h (V i))
      ((derivedPullbackFunctor (openSubspaceInclusion Y (V i))).obj K)
      ((derivedPullbackFunctor (openSubspaceInclusion Y (V i))).obj M))) :
    IsIso (derivedPullbackSheafHomMap h K M) := by
  refine (DerivedCategory.isIso_iff
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) _).2 fun n => ?_
  refine isIso_homologyMap_derivedPullbackSheafHomMap_of_local h n K M fun x => ?_
  have hx : h.hom.base x ∈ iSup V := hV ▸ TopologicalSpace.Opens.mem_top _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨V i, hi, Functor.map_isIso _ _⟩

end Cover

end Stacks.Cohomology.DerivedInternalHomPullback

end
