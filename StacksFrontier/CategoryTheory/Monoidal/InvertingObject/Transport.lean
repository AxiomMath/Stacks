module

public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Good

/-!
# Transporting presentations along a braided functor

With the notation of `StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Presentation`, let
`H : 𝒟 ⥤ 𝒟'` be a braided functor, `Ψ' : 𝒜 ⥤ 𝒟'` a monoidal functor with a monoidal isomorphism
`κ : Ψ ⋙ H ≅ Ψ'`, and `τ : H(𝕋) ≅ 𝕋'` compatible with `ω` and `ω'`. The monoidal isomorphism
`N : ev ⋙ H ≅ ev'` given on the leaves by `κ`, `τ` and the unit of `H` carries the presentations
for `(Ψ, 𝕋, ω)` to those for `(Ψ', 𝕋', ω')` (`Expr.presIso_transport`), and hence carries a
morphism presented by `c` to a morphism presented by the same `c` (`Expr.RelX.transport`).

## Main definitions

* `CategoryTheory.InvertingObject.Expr.evTransport`: the isomorphism `N`.

## Main results

* `CategoryTheory.InvertingObject.Expr.presIso_transport`: `N` carries the presentations for
  `(Ψ, 𝕋, ω)` to those for `(Ψ', 𝕋', ω')`.
* `CategoryTheory.InvertingObject.Expr.RelX.transport`: a morphism presented by `c` is carried to
  a morphism presented by `c`.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

/-- A braided functor carries `tensorδ` to `tensorδ`. -/
@[reassoc]
theorem Functor.μ_map_tensorδ_δ {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D] (H : C ⥤ D) [H.Braided]
    (W X Y Z : C) :
    μ H (W ⊗ Y) (X ⊗ Z) ≫ H.map (tensorδ W X Y Z) ≫ δ H (W ⊗ X) (Y ⊗ Z) =
      (δ H W Y ⊗ₘ δ H X Z) ≫ tensorδ _ _ _ _ ≫ (μ H W X ⊗ₘ μ H Y Z) := by
  have : IsIso (tensorμ W X Y Z) := ⟨⟨tensorδ _ _ _ _, by simp, by simp⟩⟩
  rw [← cancel_mono (μ H (W ⊗ X) (Y ⊗ Z) ≫ H.map (tensorμ W X Y Z)), Category.assoc,
    Category.assoc, δ_μ_assoc, ← H.map_comp, tensorδ_tensorμ, H.map_id, Category.comp_id,
    Category.assoc, Category.assoc, ← tensorμ_comp_μ_tensorHom_μ_comp_μ, tensorδ_tensorμ_assoc,
    tensorHom_comp_tensorHom_assoc, δ_μ, δ_μ, id_tensorHom_id, Category.id_comp]

namespace InvertingObject.Expr

open FreeMonoidalCategory

/-- Induction on formal expressions, phrased with `⊗` and `𝟙_`. -/
private theorem induction' {C : Type*} {P : FreeMonoidalCategory C → Prop}
    (hof : ∀ x, P (of x)) (hunit : P (𝟙_ _)) (htensor : ∀ X Y, P X → P Y → P (X ⊗ Y)) :
    ∀ X, P X
  | .of x => hof x
  | .unit => hunit
  | .tensor X Y => htensor X Y (induction' hof hunit htensor X) (induction' hof hunit htensor Y)

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [BraidedCategory 𝒜] {L : 𝒜}
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [MonoidalCategory 𝒟] [BraidedCategory 𝒟]
  {Ψ : 𝒜 ⥤ 𝒟} [Ψ.Monoidal] {𝕋 : 𝒟} {ω : Ψ.obj L ⊗ 𝕋 ≅ 𝟙_ 𝒟}
  {𝒟' : Type u₃} [Category.{v₃} 𝒟'] [MonoidalCategory 𝒟'] [BraidedCategory 𝒟']
  {Ψ' : 𝒜 ⥤ 𝒟'} [Ψ'.Monoidal] {𝕋' : 𝒟'} {ω' : Ψ'.obj L ⊗ 𝕋' ≅ 𝟙_ 𝒟'}
  (H : 𝒟 ⥤ 𝒟') [H.Braided] (κ : Ψ ⋙ H ≅ Ψ') [NatTrans.IsMonoidal κ.hom] (τ : H.obj 𝕋 ≅ 𝕋')

/-- The components of `evTransport` at the generators: `κ` at an atom, `τ` at the inverse, and the
inverse of the unit isomorphism of `H` at a padding generator. -/
def evTransportLeaf : ∀ g : Gen 𝒜, (ev Ψ 𝕋 ⋙ H).obj (of g) ≅ (ev Ψ' 𝕋').obj (of g)
  | .atom A => κ.app A
  | .inv => τ
  | .pd _ => (εIso H).symm

/-- The monoidal isomorphism `ev ⋙ H ≅ ev'` given on the generators by `κ`, `τ` and the
unit of `H`. -/
def evTransport : ev Ψ 𝕋 ⋙ H ≅ ev Ψ' 𝕋' := liftNatIso _ _ (evTransportLeaf H κ τ)

/-- The isomorphism `evTransport` is monoidal. -/
instance : NatTrans.IsMonoidal (evTransport H κ τ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (liftNatIso _ _ (evTransportLeaf H κ τ)).hom)

omit [MonoidalCategory 𝒜] [BraidedCategory 𝒜] [Ψ.Monoidal] [Ψ'.Monoidal]
  [NatTrans.IsMonoidal κ.hom] in
/-- The component of `evTransport` at `e ⊗ e'` is the tensor product of the components at `e`
and `e'`, conjugated by the monoidal structure maps of `H`, `ev Ψ 𝕋` and `ev Ψ' 𝕋'`. -/
theorem evTransport_app_tensor (e e' : Expr 𝒜) :
    ((evTransport H κ τ).app (e ⊗ e')).hom =
      (H.map (δ (ev Ψ 𝕋) e e') ≫ δ H _ _) ≫
        (((evTransport H κ τ).app e).hom ⊗ₘ ((evTransport H κ τ).app e').hom) ≫
          μ (ev Ψ' 𝕋') e e' := by
  rw [evTransport, liftNatIso_app_tensor]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, tensorIso_hom,
    Functor.OplaxMonoidal.comp_δ]

omit [BraidedCategory 𝒜] in
/-- The monoidal isomorphism `κ` is compatible with the comonoidal structure maps `δ`. -/
@[reassoc]
theorem app_tensor_δ (A B : 𝒜) :
    κ.hom.app (A ⊗ B) ≫ δ Ψ' A B = H.map (δ Ψ A B) ≫ δ H _ _ ≫ (κ.hom.app A ⊗ₘ κ.hom.app B) := by
  have h := NatTrans.IsMonoidal.tensor (τ := κ.hom) A B
  rw [Functor.LaxMonoidal.comp_μ] at h
  rw [← cancel_epi (μ H (Ψ.obj A) (Ψ.obj B) ≫ H.map (μ Ψ A B))]
  simp only [Category.assoc] at h ⊢
  rw [reassoc_of% h, μ_δ, Category.comp_id, ← H.map_comp_assoc, μ_δ, H.map_id,
    Category.id_comp, μ_δ_assoc]

omit [BraidedCategory 𝒜] in
/-- The monoidal isomorphism `κ` is compatible with the unit maps `ε`. -/
@[reassoc]
theorem map_ε_app_unit : H.map (ε Ψ) ≫ κ.hom.app (𝟙_ 𝒜) = η H ≫ ε Ψ' := by
  have h := NatTrans.IsMonoidal.unit (τ := κ.hom)
  rw [Functor.LaxMonoidal.comp_ε, Category.assoc] at h
  rw [← h, η_ε_assoc]

omit [BraidedCategory 𝒜] in
/-- The monoidal isomorphism `κ` is compatible with the counit maps `η`. -/
@[reassoc]
theorem app_unit_η : κ.hom.app (𝟙_ 𝒜) ≫ η Ψ' = H.map (η Ψ) ≫ η H := by
  rw [← cancel_epi (H.map (ε Ψ)), map_ε_app_unit_assoc, ε_η, Category.comp_id,
    ← H.map_comp_assoc, ε_η, H.map_id, Category.id_comp]

omit [BraidedCategory 𝒜] in
/-- If `κ` carries `p₁` to `p₁'` along `t₁` and `p₂` to `p₂'` along `t₂`, then it carries the
tensor product of `p₁` and `p₂` to that of `p₁'` and `p₂'` along `t₁ ⊗ t₂`. -/
theorem presIso_transport_tensor_aux {X₁ X₂ : 𝒟} {X₁' X₂' : 𝒟'} {P₁ P₂ B₁ B₂ : 𝒜}
    (p₁ : X₁ ⊗ Ψ.obj P₁ ⟶ Ψ.obj B₁) (p₂ : X₂ ⊗ Ψ.obj P₂ ⟶ Ψ.obj B₂)
    (p₁' : X₁' ⊗ Ψ'.obj P₁ ⟶ Ψ'.obj B₁) (p₂' : X₂' ⊗ Ψ'.obj P₂ ⟶ Ψ'.obj B₂)
    (t₁ : H.obj X₁ ⟶ X₁') (t₂ : H.obj X₂ ⟶ X₂')
    (h₁ : μ H X₁ (Ψ.obj P₁) ≫ H.map p₁ ≫ κ.hom.app B₁ = (t₁ ⊗ₘ κ.hom.app P₁) ≫ p₁')
    (h₂ : μ H X₂ (Ψ.obj P₂) ≫ H.map p₂ ≫ κ.hom.app B₂ = (t₂ ⊗ₘ κ.hom.app P₂) ≫ p₂') :
    μ H (X₁ ⊗ X₂) (Ψ.obj (P₁ ⊗ P₂)) ≫
        H.map ((𝟙 (X₁ ⊗ X₂) ⊗ₘ (Ψ.map (𝟙 (P₁ ⊗ P₂)) ≫ δ Ψ P₁ P₂)) ≫ tensorδ _ _ _ _ ≫
          (p₁ ⊗ₘ p₂) ≫ μ Ψ B₁ B₂ ≫ Ψ.map (𝟙 (B₁ ⊗ B₂))) ≫ κ.hom.app (B₁ ⊗ B₂) =
      (((H.map (𝟙 (X₁ ⊗ X₂)) ≫ δ H X₁ X₂) ≫ (t₁ ⊗ₘ t₂) ≫ 𝟙 (X₁' ⊗ X₂')) ⊗ₘ
          κ.hom.app (P₁ ⊗ P₂)) ≫
        (𝟙 (X₁' ⊗ X₂') ⊗ₘ (Ψ'.map (𝟙 (P₁ ⊗ P₂)) ≫ δ Ψ' P₁ P₂)) ≫ tensorδ _ _ _ _ ≫
          (p₁' ⊗ₘ p₂') ≫ μ Ψ' B₁ B₂ ≫ Ψ'.map (𝟙 (B₁ ⊗ B₂)) := by
  have hκ : μ H (Ψ.obj B₁) (Ψ.obj B₂) ≫ H.map (μ Ψ B₁ B₂) ≫ κ.hom.app (B₁ ⊗ B₂) =
      (κ.hom.app B₁ ⊗ₘ κ.hom.app B₂) ≫ μ Ψ' B₁ B₂ := by
    have h := NatTrans.IsMonoidal.tensor (τ := κ.hom) B₁ B₂
    rwa [Functor.LaxMonoidal.comp_μ, Category.assoc] at h
  have ht : μ H (X₁ ⊗ X₂) (Ψ.obj P₁ ⊗ Ψ.obj P₂) ≫ H.map (tensorδ X₁ (Ψ.obj P₁) X₂ (Ψ.obj P₂)) =
      (δ H X₁ X₂ ⊗ₘ δ H _ _) ≫ tensorδ _ _ _ _ ≫ (μ H _ _ ⊗ₘ μ H _ _) ≫ μ H _ _ := by
    rw [← Functor.μ_map_tensorδ_δ_assoc, δ_μ, Category.comp_id]
  have key : H.obj (X₁ ⊗ X₂) ◁ H.map (δ Ψ P₁ P₂) ≫ (δ H X₁ X₂ ⊗ₘ δ H _ _) ≫
      ((t₁ ⊗ₘ t₂) ⊗ₘ (κ.hom.app P₁ ⊗ₘ κ.hom.app P₂)) =
      ((δ H X₁ X₂ ≫ (t₁ ⊗ₘ t₂)) ⊗ₘ κ.hom.app (P₁ ⊗ P₂)) ≫ (X₁' ⊗ X₂') ◁ δ Ψ' P₁ P₂ := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, app_tensor_δ, Category.id_comp, Category.comp_id]
  simp only [Functor.map_id, Category.id_comp, Category.comp_id, id_tensorHom, Functor.map_comp,
    Category.assoc]
  rw [map_whiskerLeft]
  simp only [Category.assoc, μ_δ_assoc]
  rw [reassoc_of% ht, map_tensor]
  simp only [Category.assoc, μ_δ_assoc]
  rw [hκ]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [h₁, h₂, ← tensorHom_comp_tensorHom, Category.assoc, ← tensorδ_natural_assoc,
    reassoc_of% key]

omit [MonoidalCategory 𝒜] [BraidedCategory 𝒜] [Ψ.Monoidal] [Ψ'.Monoidal]
  [NatTrans.IsMonoidal κ.hom] in
/-- The monoidal isomorphism `κ` carries the left unitor of `Ψ.obj X` to that of `Ψ'.obj X`,
along the counit `η H`. -/
theorem transport_leftUnitor (X : 𝒜) :
    μ H (𝟙_ 𝒟) (Ψ.obj X) ≫ H.map (λ_ (Ψ.obj X)).hom ≫ κ.hom.app X =
      (η H ⊗ₘ κ.hom.app X) ≫ (λ_ (Ψ'.obj X)).hom := by
  rw [map_leftUnitor, Category.assoc, Category.assoc, μ_δ_assoc, ← leftUnitor_naturality,
    tensorHom_def', Category.assoc, whisker_exchange_assoc]
  rfl

omit [BraidedCategory 𝒜] in
variable (L ω ω') in
/-- **Presentations are carried to presentations.** -/
theorem presIso_transport
    (hτ : μ H 𝕋 (Ψ.obj L) ≫ H.map (β_ 𝕋 (Ψ.obj L) ≪≫ ω ≪≫ εIso Ψ).hom ≫ κ.hom.app (𝟙_ 𝒜) =
      (τ.hom ⊗ₘ κ.hom.app L) ≫ (β_ 𝕋' (Ψ'.obj L) ≪≫ ω' ≪≫ εIso Ψ').hom) (e : Expr 𝒜) :
    μ H ((ev Ψ 𝕋).obj e) (Ψ.obj ((pad L).obj e)) ≫ H.map (presIso L Ψ 𝕋 ω e).hom ≫
        κ.hom.app ((base).obj e) =
      (((evTransport H κ τ).app e).hom ⊗ₘ κ.hom.app ((pad L).obj e)) ≫
        (presIso L Ψ' 𝕋' ω' e).hom := by
  induction e using induction' with
  | hof g =>
    cases g with
    | atom A =>
      change μ H (Ψ.obj A) (Ψ.obj (𝟙_ 𝒜)) ≫ H.map (μ Ψ A (𝟙_ 𝒜) ≫ Ψ.map (ρ_ A).hom) ≫
          κ.hom.app A = (κ.hom.app A ⊗ₘ κ.hom.app (𝟙_ 𝒜)) ≫ (μ Ψ' A (𝟙_ 𝒜) ≫ Ψ'.map (ρ_ A).hom)
      have h := NatTrans.IsMonoidal.tensor (τ := κ.hom) A (𝟙_ 𝒜)
      rw [Functor.LaxMonoidal.comp_μ, Category.assoc] at h
      rw [← reassoc_of% h, ← κ.hom.naturality, Functor.map_comp, Functor.comp_map,
        Category.assoc]
    | inv => exact hτ
    | pd X =>
      change μ H (𝟙_ 𝒟) (Ψ.obj X) ≫ H.map (λ_ (Ψ.obj X)).hom ≫ κ.hom.app X =
        (η H ⊗ₘ κ.hom.app X) ≫ (λ_ (Ψ'.obj X)).hom
      exact transport_leftUnitor H κ X
  | hunit =>
    simp only [presIso, pres, evTransport, liftNatIso_app, liftNatIsoApp_unit, Iso.trans_hom,
      Iso.symm_hom, εIso_inv, εIso_hom, Functor.OplaxMonoidal.comp_η, Functor.LaxMonoidal.comp_ε,
      tensor_η, tensor_map, Functor.prod'_η_fst, Functor.prod'_η_snd, project_η, project_ε]
    change μ H (𝟙_ 𝒟) (Ψ.obj (𝟙_ 𝒜)) ≫ H.map (((𝟙 (𝟙_ 𝒟) ⊗ₘ Ψ.map (𝟙 (𝟙_ 𝒜)) ≫ η Ψ) ≫
        (λ_ (𝟙_ 𝒟)).hom) ≫ ε Ψ ≫ Ψ.map (𝟙 (𝟙_ 𝒜))) ≫ κ.hom.app (𝟙_ 𝒜) =
      ((H.map (𝟙 (𝟙_ 𝒟)) ≫ η H) ≫ 𝟙 (𝟙_ 𝒟') ⊗ₘ κ.hom.app (𝟙_ 𝒜)) ≫
        ((𝟙 (𝟙_ 𝒟') ⊗ₘ Ψ'.map (𝟙 (𝟙_ 𝒜)) ≫ η Ψ') ≫ (λ_ (𝟙_ 𝒟')).hom) ≫ ε Ψ' ≫
          Ψ'.map (𝟙 (𝟙_ 𝒜))
    simp only [Functor.map_id, Category.id_comp, Category.comp_id, id_tensorHom,
      Category.assoc, leftUnitor_naturality_assoc, η_ε]
    exact transport_leftUnitor H κ (𝟙_ 𝒜)
  | htensor e e' ih ih' =>
    rw [presIso_tensor_hom, presIso_tensor_hom, evTransport_app_tensor]
    exact presIso_transport_tensor_aux H κ _ _ _ _ _ _ ih ih'

variable (hτ : μ H 𝕋 (Ψ.obj L) ≫ H.map (β_ 𝕋 (Ψ.obj L) ≪≫ ω ≪≫ εIso Ψ).hom ≫ κ.hom.app (𝟙_ 𝒜) =
      (τ.hom ⊗ₘ κ.hom.app L) ≫ (β_ 𝕋' (Ψ'.obj L) ≪≫ ω' ≪≫ εIso Ψ').hom)
include hτ

omit [BraidedCategory 𝒜] in
/-- `θ` is carried to `θ`. -/
theorem θ_transport (e : Expr 𝒜) (X : 𝒜) :
    μ H ((ev Ψ 𝕋).obj e) (Ψ.obj ((pad L).obj e ⊗ X)) ≫ H.map (θ L Ψ 𝕋 ω e X).hom ≫
        κ.hom.app ((base).obj e ⊗ X) =
      (((evTransport H κ τ).app e).hom ⊗ₘ κ.hom.app ((pad L).obj e ⊗ X)) ≫
        (θ L Ψ' 𝕋' ω' e X).hom := by
  have h := presIso_transport (H := H) (κ := κ) (τ := τ) (L := L) (ω := ω) (ω' := ω') hτ (e ⊗ pd X)
  rw [evTransport_app_tensor] at h
  change μ H _ _ ≫ H.map (presPad L Ψ 𝕋 ω e X).hom ≫ κ.hom.app _ =
    (((H.map (𝟙 _) ≫ δ H _ _) ≫ (((evTransport H κ τ).app e).hom ⊗ₘ η H) ≫ 𝟙 _) ⊗ₘ
      κ.hom.app _) ≫ (presPad L Ψ' 𝕋' ω' e X).hom at h
  have hr : H.map (ρ_ ((ev Ψ 𝕋).obj e)).inv ≫ ((H.map (𝟙 _) ≫ δ H _ _) ≫
      (((evTransport H κ τ).app e).hom ⊗ₘ η H) ≫ 𝟙 _) =
      ((evTransport H κ τ).app e).hom ≫ (ρ_ _).inv := by
    rw [H.map_id, Category.id_comp, Category.comp_id, map_rightUnitor_inv, tensorHom_def',
      Category.assoc, Category.assoc, μ_δ_assoc, ← whiskerLeft_comp_assoc, ε_η, whiskerLeft_id,
      Category.id_comp, rightUnitor_inv_naturality]
    rfl
  rw [θ_eq_presPad, θ_eq_presPad, Functor.map_comp, Category.assoc, ← μ_natural_left_assoc, h,
    ← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom, hr,
    Category.id_comp, ← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.comp_id]

omit [BraidedCategory 𝒜] in
/-- **A presented morphism is carried to a morphism presented by the same data.** -/
theorem RelX.transport {e e' : Expr 𝒜} {u : (ev Ψ 𝕋).obj e ⟶ (ev Ψ 𝕋).obj e'} {X Y : 𝒜}
    {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y} {c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y}
    (h : RelX L Ψ 𝕋 ω u X Y φ c) :
    RelX L Ψ' 𝕋' ω' (((evTransport H κ τ).app e).inv ≫ H.map u ≫
      ((evTransport H κ τ).app e').hom) X Y φ c := by
  unfold RelX at h ⊢
  have h₁ := θ_transport H κ τ hτ e X
  have h₂ := θ_transport H κ τ hτ e' Y
  have hl : (((evTransport H κ τ).app e).hom ⊗ₘ κ.hom.app ((pad L).obj e ⊗ X)) ≫
      (((evTransport H κ τ).app e).inv ≫ H.map u ≫ ((evTransport H κ τ).app e').hom) ▷
        Ψ'.obj ((pad L).obj e ⊗ X) ≫ (ev Ψ' 𝕋').obj e' ◁ Ψ'.map φ.hom =
      (H.map u ⊗ₘ H.map (Ψ.map φ.hom)) ≫
        (((evTransport H κ τ).app e').hom ⊗ₘ κ.hom.app ((pad L).obj e' ⊗ Y)) := by
    rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
      Iso.hom_inv_id_assoc, Category.comp_id, tensorHom_comp_tensorHom, Category.comp_id,
      ← κ.hom.naturality]
    rfl
  rw [← cancel_epi (((evTransport H κ τ).app e).hom ⊗ₘ κ.hom.app ((pad L).obj e ⊗ X)),
    reassoc_of% hl, ← h₂, ← reassoc_of% h₁, ← κ.hom.naturality c, Functor.comp_map,
    μ_natural_assoc, ← H.map_comp_assoc, ← H.map_comp_assoc, ← h, tensorHom_def,
    Category.assoc]

end InvertingObject.Expr

end CategoryTheory
