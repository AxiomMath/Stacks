module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom

/-!
# Transporting a tensor–internal-Hom adjunction along an equivalence

Let `T : C ⥤ C ⥤ C` and `H : Cᵒᵖ ⥤ C ⥤ C` be bifunctors tied together by a tensor–internal-Hom
adjunction (`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction`,
the bijection `Hom(A, H(B, M)) ≃ Hom(T(A, B), M)` of [Stacks, Tag 08J8] with its naturality in
all three objects), and let `e : D ≌ C` be an equivalence of categories. Then the bifunctors

`T_e(A, B) = e⁻¹ T(e A, e B)` and `H_e(B, M) = e⁻¹ H(e B, e M)`

on `D` are tied together by a tensor–internal-Hom adjunction as well: its bijection is the
composite of the adjunction `e ⊣ e⁻¹`, of the given bijection, and of the adjunction
`e⁻¹ ⊣ e`.

## Main definitions

* `TensorHomAdjunction.transportTensor`, `TensorHomAdjunction.transportHom`: the two
  transported bifunctors.
* `TensorHomAdjunction.transport`: the transported tensor–internal-Hom adjunction.
* `TensorHomAdjunction.transportCup`: a natural `R' A ⊗ R' B ⟶ R' (A ⊗ B)` transported along
  equivalences to the transported tensor bifunctors.
* `TensorHomAdjunction.transportTensorIso`: a comparison `F'(A ⊗ B) ≅ F'A ⊗ F'B` transported
  along equivalences to the transported tensor bifunctors.
* `TensorHomAdjunction.flipAdjunction`: tensoring with a fixed object is left adjoint to the
  internal Hom out of it.

## Main results

* `TensorHomAdjunction.transport_homEquiv`: the bijection of the transported adjunction is
  `TensorHomAdjunction.transportHomEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace TensorHomAdjunction

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (e : D ≌ C)

/-- The tensor bifunctor `T` on `C` read on `D` along the equivalence `e : D ≌ C`:
`(A, B) ↦ e⁻¹ T(e A, e B)`. -/
abbrev transportTensor (T : C ⥤ C ⥤ C) : D ⥤ D ⥤ D :=
  e.functor ⋙ T ⋙ (Functor.whiskeringLeft D C C).obj e.functor ⋙
    (Functor.whiskeringRight D C D).obj e.inverse

/-- The internal Hom bifunctor `H` on `C` read on `D` along the equivalence `e : D ≌ C`:
`(B, M) ↦ e⁻¹ H(e B, e M)`. -/
abbrev transportHom (H : Cᵒᵖ ⥤ C ⥤ C) : Dᵒᵖ ⥤ D ⥤ D :=
  e.functor.op ⋙ H ⋙ (Functor.whiskeringLeft D C C).obj e.functor ⋙
    (Functor.whiskeringRight D C D).obj e.inverse

/-- The value of `transportTensor e T` at `(A, B)` is `e⁻¹ T(e A, e B)`. -/
@[simp]
theorem transportTensor_obj_obj (T : C ⥤ C ⥤ C) (A B : D) :
    ((transportTensor e T).obj A).obj B = e.inverse.obj ((T.obj (e.functor.obj A)).obj
      (e.functor.obj B)) := rfl

/-- The action of `transportTensor e T` on a morphism `u : A ⟶ A'` in the first variable is
`e⁻¹ T(e u, e B)`. -/
@[simp]
theorem transportTensor_map_app (T : C ⥤ C ⥤ C) {A A' : D} (u : A ⟶ A') (B : D) :
    ((transportTensor e T).map u).app B =
      e.inverse.map ((T.map (e.functor.map u)).app (e.functor.obj B)) := rfl

/-- The action of `transportTensor e T` on a morphism `g : B ⟶ B'` in the second variable is
`e⁻¹ T(e A, e g)`. -/
@[simp]
theorem transportTensor_obj_map (T : C ⥤ C ⥤ C) (A : D) {B B' : D} (g : B ⟶ B') :
    ((transportTensor e T).obj A).map g =
      e.inverse.map ((T.obj (e.functor.obj A)).map (e.functor.map g)) := rfl

/-- The value of `transportHom e H` at `(B, M)` is `e⁻¹ H(e B, e M)`. -/
@[simp]
theorem transportHom_obj_obj (H : Cᵒᵖ ⥤ C ⥤ C) (B M : D) :
    ((transportHom e H).obj (op B)).obj M = e.inverse.obj ((H.obj (op (e.functor.obj B))).obj
      (e.functor.obj M)) := rfl

/-- The action of `transportHom e H` on a morphism `g : B' ⟶ B` in the first (contravariant)
variable is `e⁻¹ H(e g, e M)`. -/
@[simp]
theorem transportHom_map_app (H : Cᵒᵖ ⥤ C ⥤ C) {B B' : D} (g : B' ⟶ B) (M : D) :
    ((transportHom e H).map g.op).app M =
      e.inverse.map ((H.map (e.functor.map g).op).app (e.functor.obj M)) := rfl

/-- The action of `transportHom e H` on a morphism `m : M ⟶ M'` in the second variable is
`e⁻¹ H(e B, e m)`. -/
@[simp]
theorem transportHom_obj_map (H : Cᵒᵖ ⥤ C ⥤ C) (B : D) {M M' : D} (m : M ⟶ M') :
    ((transportHom e H).obj (op B)).map m =
      e.inverse.map ((H.obj (op (e.functor.obj B))).map (e.functor.map m)) := rfl

variable {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} (adj : TensorHomAdjunction T H)

/-- The bijection of the transported tensor–internal-Hom adjunction:
`Hom(A, e⁻¹H(eB, eM)) ≃ Hom(eA, H(eB, eM)) ≃ Hom(T(eA, eB), eM) ≃ Hom(e⁻¹T(eA, eB), M)`. -/
def transportHomEquiv (A B M : D) :
    (A ⟶ ((transportHom e H).obj (op B)).obj M) ≃ (((transportTensor e T).obj A).obj B ⟶ M) :=
  (e.toAdjunction.homEquiv A _).symm.trans
    ((adj.homEquiv (e.functor.obj A) (e.functor.obj B) (e.functor.obj M)).trans
      (e.symm.toAdjunction.homEquiv _ M).symm)

/-- `transportHomEquiv e adj` sends `h` to the composite of the inverse bijections of `e ⊣ e⁻¹`
and `e⁻¹ ⊣ e` with the bijection of `adj`, applied to `h`. -/
theorem transportHomEquiv_apply (A B M : D) (h : A ⟶ ((transportHom e H).obj (op B)).obj M) :
    transportHomEquiv e adj A B M h =
      (e.symm.toAdjunction.homEquiv _ M).symm
        (adj.homEquiv (e.functor.obj A) (e.functor.obj B) (e.functor.obj M)
          ((e.toAdjunction.homEquiv A _).symm h)) := rfl

/-- **A tensor–internal-Hom adjunction transported along an equivalence.** For
`e : D ≌ C` and a tensor–internal-Hom adjunction between `T` and `H` on `C`, the bifunctors
`e⁻¹ T(e -, e -)` and `e⁻¹ H(e -, e -)` on `D` are tied together by the composite of
`e ⊣ e⁻¹`, of the given bijection, and of `e⁻¹ ⊣ e`. -/
def transport : TensorHomAdjunction (transportTensor e T) (transportHom e H) where
  homEquiv := transportHomEquiv e adj
  homEquiv_naturality_source {A A' B M} u h := by
    rw [transportHomEquiv_apply, transportHomEquiv_apply,
      e.toAdjunction.homEquiv_naturality_left_symm, adj.homEquiv_naturality_source,
      e.symm.toAdjunction.homEquiv_naturality_left_symm]
    rfl
  homEquiv_naturality_middle {A B B' M} g h := by
    rw [transportHomEquiv_apply, transportHomEquiv_apply, transportHom_map_app,
      e.toAdjunction.homEquiv_naturality_right_symm, adj.homEquiv_naturality_middle,
      e.symm.toAdjunction.homEquiv_naturality_left_symm]
    rfl
  homEquiv_naturality_target {A B M M'} h m := by
    rw [transportHomEquiv_apply, transportHomEquiv_apply, transportHom_obj_map,
      e.toAdjunction.homEquiv_naturality_right_symm, adj.homEquiv_naturality_target]
    exact e.symm.toAdjunction.homEquiv_naturality_right_symm _ _

/-- The bijection of `transport e adj` is `transportHomEquiv e adj`. -/
theorem transport_homEquiv (A B M : D) :
    (transport e adj).homEquiv A B M = transportHomEquiv e adj A B M := rfl


/-! ### Transporting a lax structure on a functor -/

section Cup

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] {D₁ : Type*} [Category* D₁]
  {D₂ : Type*} [Category* D₂] (e₁ : D₁ ≌ C₁) (e₂ : D₂ ≌ C₂) {R : D₁ ⥤ D₂} {R' : C₁ ⥤ C₂}
  (c : R ⋙ e₂.functor ≅ e₁.functor ⋙ R') {T₁ : C₁ ⥤ C₁ ⥤ C₁} {T₂ : C₂ ⥤ C₂ ⥤ C₂}
  (cup : (R' ⋙ T₂) ⋙ (Functor.whiskeringLeft C₁ C₂ C₂).obj R' ⟶
    T₁ ⋙ (Functor.whiskeringRight C₁ C₁ C₂).obj R')

/-- The component of `transportCup`: `R A ⊗ R B ⟶ R (A ⊗ B)` for the transported tensor
products, read off the given one `R' A' ⊗ R' B' ⟶ R' (A' ⊗ B')` through `c : R e₂ ≅ e₁ R'`. -/
def transportCupApp (A B : D₁) :
    ((transportTensor e₂ T₂).obj (R.obj A)).obj (R.obj B) ⟶
      R.obj (((transportTensor e₁ T₁).obj A).obj B) :=
  e₂.inverse.map ((T₂.map (c.hom.app A)).app _ ≫ (T₂.obj _).map (c.hom.app B) ≫
      (cup.app (e₁.functor.obj A)).app (e₁.functor.obj B) ≫ R'.map (e₁.counitInv.app _) ≫
      c.inv.app _) ≫
    e₂.unitInv.app _

/-- Naturality of `transportCupApp` for a morphism `t` of `C₁` and a morphism `s` of `C₂` which are
compatible with `cup` and `c`. -/
private theorem transportCupApp_naturality_aux {A A' B B' : D₁}
    (s : (T₂.obj (e₂.functor.obj (R.obj A))).obj (e₂.functor.obj (R.obj B)) ⟶
      (T₂.obj (e₂.functor.obj (R.obj A'))).obj (e₂.functor.obj (R.obj B')))
    (t : (T₁.obj (e₁.functor.obj A)).obj (e₁.functor.obj B) ⟶
      (T₁.obj (e₁.functor.obj A')).obj (e₁.functor.obj B'))
    (h : s ≫ (T₂.map (c.hom.app A')).app _ ≫ (T₂.obj _).map (c.hom.app B') ≫
        (cup.app _).app _ =
      (T₂.map (c.hom.app A)).app _ ≫ (T₂.obj _).map (c.hom.app B) ≫ (cup.app _).app _ ≫
        R'.map t) :
    e₂.inverse.map s ≫ transportCupApp e₁ e₂ c cup A' B' =
      transportCupApp e₁ e₂ c cup A B ≫ R.map (e₁.inverse.map t) := by
  have hc' := c.inv.naturality (e₁.inverse.map t)
  have hcounit := e₁.counitInv.naturality t
  have hunit := e₂.unitInv.naturality (R.map (e₁.inverse.map t))
  dsimp at hc' hcounit hunit ⊢
  simp only [transportCupApp, Category.assoc]
  rw [← hunit, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  simp only [Category.assoc, Functor.comp_obj]
  rw [← hc', ← R'.map_comp_assoc, ← hcounit, R'.map_comp_assoc, ← reassoc_of% h]

/-- `transportCupApp e₁ e₂ c cup A B` is natural in `B`. -/
theorem transportCupApp_naturality_right (A : D₁) {B B' : D₁} (b : B ⟶ B') :
    ((transportTensor e₂ T₂).obj (R.obj A)).map (R.map b) ≫ transportCupApp e₁ e₂ c cup A B' =
      transportCupApp e₁ e₂ c cup A B ≫ R.map (((transportTensor e₁ T₁).obj A).map b) := by
  refine transportCupApp_naturality_aux e₁ e₂ c cup _ _ ?_
  have hc := c.hom.naturality b
  have hcup := (cup.app (e₁.functor.obj A)).naturality (e₁.functor.map b)
  dsimp at hc hcup ⊢
  rw [← hcup, ← (T₂.obj (R'.obj (e₁.functor.obj A))).map_comp_assoc, ← hc,
    (T₂.obj (R'.obj (e₁.functor.obj A))).map_comp_assoc, NatTrans.naturality_assoc]

/-- `transportCupApp e₁ e₂ c cup A B` is natural in `A`. -/
theorem transportCupApp_naturality_left {A A' : D₁} (a : A ⟶ A') (B : D₁) :
    ((transportTensor e₂ T₂).map (R.map a)).app (R.obj B) ≫ transportCupApp e₁ e₂ c cup A' B =
      transportCupApp e₁ e₂ c cup A B ≫ R.map (((transportTensor e₁ T₁).map a).app B) := by
  refine transportCupApp_naturality_aux e₁ e₂ c cup _ _ ?_
  have hc := c.hom.naturality a
  have hcup := congrArg (fun φ => NatTrans.app φ (e₁.functor.obj B))
    (cup.naturality (e₁.functor.map a))
  dsimp at hc hcup ⊢
  rw [← hcup, NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← T₂.map_comp, hc,
    T₂.map_comp, NatTrans.comp_app_assoc]

/-- **A lax structure transported along equivalences.** Given `c : R ⋙ e₂ ≅ e₁ ⋙ R'` and a
natural `R' A ⊗ R' B ⟶ R' (A ⊗ B)` for bifunctors `T₁`, `T₂`, the natural
`R A ⊗ R B ⟶ R (A ⊗ B)` for the transported bifunctors `transportTensor e₁ T₁` and
`transportTensor e₂ T₂`. -/
def transportCup :
    (R ⋙ transportTensor e₂ T₂) ⋙ (Functor.whiskeringLeft D₁ D₂ D₂).obj R ⟶
      transportTensor e₁ T₁ ⋙ (Functor.whiskeringRight D₁ D₁ D₂).obj R where
  app A :=
    { app := fun B => transportCupApp e₁ e₂ c cup A B
      naturality := fun _ _ b => transportCupApp_naturality_right e₁ e₂ c cup A b }
  naturality _ _ a := by
    ext B
    exact transportCupApp_naturality_left e₁ e₂ c cup a B

/-- The component of `transportCup e₁ e₂ c cup` at `(A, B)` is
`transportCupApp e₁ e₂ c cup A B`. -/
theorem transportCup_app_app (A B : D₁) :
    ((transportCup e₁ e₂ c cup).app A).app B = transportCupApp e₁ e₂ c cup A B := rfl

end Cup

/-! ### Transporting a comparison of tensor products along a functor -/

section Monoidal

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] {D₁ : Type*} [Category* D₁]
  {D₂ : Type*} [Category* D₂]

/-- The transported tensor bifunctor, uncurried, is `e⁻¹ ∘ T ∘ (e × e)`. -/
def uncurryTransportTensorIso (e : D₁ ≌ C₁) (T : C₁ ⥤ C₁ ⥤ C₁) :
    Functor.uncurry.obj (transportTensor e T) ≅
      e.functor.prod e.functor ⋙ Functor.uncurry.obj T ⋙ e.inverse :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Functor.uncurry_obj_map, transportTensor_obj_map, Iso.refl_hom, Category.comp_id,
      Category.id_comp, Functor.comp_map, Functor.prod_map, Functor.map_comp]
    rfl)

variable (e₁ : D₁ ≌ C₁) (e₂ : D₂ ≌ C₂) {F : D₂ ⥤ D₁} {F' : C₂ ⥤ C₁}
  (κ : e₂.functor ⋙ F' ≅ F ⋙ e₁.functor) {T₁ : C₁ ⥤ C₁ ⥤ C₁} {T₂ : C₂ ⥤ C₂ ⥤ C₂}
  (μ : Functor.uncurry.obj T₂ ⋙ F' ≅ F'.prod F' ⋙ Functor.uncurry.obj T₁)

/-- From `κ : e₂ ⋙ F' ≅ F ⋙ e₁`, the comparison `e₂⁻¹ ⋙ F ≅ F' ⋙ e₁⁻¹`. -/
def transportInverseIso : e₂.inverse ⋙ F ≅ F' ⋙ e₁.inverse :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft (e₂.inverse ⋙ F) e₁.unitIso ≪≫
    Functor.isoWhiskerLeft e₂.inverse (Functor.isoWhiskerRight κ.symm e₁.inverse) ≪≫
    Functor.isoWhiskerRight e₂.counitIso (F' ⋙ e₁.inverse) ≪≫ Functor.leftUnitor _

/-- **A comparison of tensor products transported along equivalences.** Given
`κ : e₂ ⋙ F' ≅ F ⋙ e₁` and `μ : F'(A ⊗ B) ≅ F'A ⊗ F'B`, the comparison
`F(A ⊗ B) ≅ FA ⊗ FB` for the transported bifunctors. -/
def transportTensorIso :
    Functor.uncurry.obj (transportTensor e₂ T₂) ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj (transportTensor e₁ T₁) :=
  Functor.isoWhiskerRight (uncurryTransportTensorIso e₂ T₂) F ≪≫
    Functor.isoWhiskerLeft (e₂.functor.prod e₂.functor ⋙ Functor.uncurry.obj T₂)
      (transportInverseIso e₁ e₂ κ) ≪≫
    Functor.isoWhiskerLeft (e₂.functor.prod e₂.functor) (Functor.isoWhiskerRight μ e₁.inverse) ≪≫
    Functor.isoWhiskerRight (NatIso.prod κ κ) (Functor.uncurry.obj T₁ ⋙ e₁.inverse) ≪≫
    Functor.isoWhiskerLeft (F.prod F) (uncurryTransportTensorIso e₁ T₁).symm

end Monoidal

/-! ### Tensoring with a fixed object is a left adjoint -/

section FlipAdjunction

variable {C : Type*} [Category* C] {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}

/-- **Tensoring with a fixed object `B` is left adjoint to the internal Hom out of `B`**, for a
tensor–internal-Hom adjunction. -/
def flipAdjunction (adj : TensorHomAdjunction T H) (B : C) : T.flip.obj B ⊣ H.obj (op B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A M => (adj.homEquiv A B M).symm
      homEquiv_naturality_left_symm := fun f g => adj.homEquiv_naturality_source f g
      homEquiv_naturality_right := fun f m =>
        (adj.homEquiv _ B _).injective (by
          rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_target, Equiv.apply_symm_apply]) }

end FlipAdjunction

end TensorHomAdjunction

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

end
