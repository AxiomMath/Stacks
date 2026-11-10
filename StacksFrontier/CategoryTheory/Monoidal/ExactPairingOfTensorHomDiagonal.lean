module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# A left dual from an invertible tensor–Hom diagonal

Let `C` be a monoidal category in which `- ⊗ E` has a right adjoint `H(E, -)` for each object
`E`, with counit `ε_K : H(E, K) ⊗ E ⟶ K`. Write `E^∨ = H(E, 𝟙)`. If the tensor–Hom diagonal
`t : E ⊗ E^∨ ⟶ H(E, E ⊗ 𝟙) ≅ H(E, E)` is invertible, then `E^∨` is a left dual of `E`: the
evaluation is `ε_𝟙 : E^∨ ⊗ E ⟶ 𝟙` and the coevaluation is `t⁻¹` applied to the section
`𝟙 ⟶ H(E, E)` adjoint to the left unitor of `E`.

## Main definitions

* `CategoryTheory.PullbackInternalHom.exactPairingOfIsIsoLeftTensorHomDiagonal`: the exact
  pairing of `E` with `H(E, 𝟙)` when the tensor–Hom diagonal is invertible.
* `CategoryTheory.PullbackInternalHom.exactPairingTensorHomMap`: for an exact pairing `(X, Y)`,
  the map `K ⊗ Y ⟶ H(X, K)`.

## Main results

* `CategoryTheory.PullbackInternalHom.whiskerRight_unitTensorHomDiagonal_comp_counit`: the
  diagonal followed by the counit is the evaluation of the second factor.
* `CategoryTheory.PullbackInternalHom.isIso_exactPairingTensorHomMap`: for an exact pairing
  `(X, Y)` the map `K ⊗ Y ⟶ H(X, K)` is invertible.
* `CategoryTheory.PullbackInternalHom.map_exactPairingTensorHomMap_comp_pullbackHomMap`: a
  monoidal functor carries the map `K ⊗ Y ⟶ H(X, K)` to the one of the image pairing, through
  the pullback map of internal Homs.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.PullbackInternalHom

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (H : Cᵒᵖ ⥤ C ⥤ C)
  (adj : ∀ P : C, (curriedTensor C).flip.obj P ⊣ H.obj (op P))

/-- The tensor–Hom diagonal `E ⊗ H(E, 𝟙) ⟶ H(E, E)` at the unit, followed by `H(E, ρ_E)`. -/
def unitTensorHomDiagonal (E : C) :
    E ⊗ (H.obj (op E)).obj (𝟙_ C) ⟶ (H.obj (op E)).obj E :=
  leftTensorHomDiagonal (curriedTensor C) H adj (fun A B D => α_ A B D) E E (𝟙_ C) ≫
    (H.obj (op E)).map (ρ_ E).hom

/-- The adjoint of `f : A ⊗ X ⟶ K`, whiskered by `X` and followed by the counit, is `f`. -/
private theorem whiskerRight_homEquiv_comp_counit {X K A : C} (f : A ⊗ X ⟶ K) :
    (adj X).homEquiv A K f ▷ X ≫ (adj X).counit.app K = f :=
  ((adj X).homEquiv_counit (g := (adj X).homEquiv A K f)).symm.trans (Equiv.symm_apply_apply _ _)

/-- **The diagonal followed by the counit is the evaluation of the second factor**:
`(t ▷ E) ≫ ε_E = α ≫ (E ◁ ε_𝟙) ≫ ρ_E`. -/
theorem whiskerRight_unitTensorHomDiagonal_comp_counit (E : C) :
    unitTensorHomDiagonal H adj E ▷ E ≫ (adj E).counit.app E =
      (α_ E ((H.obj (op E)).obj (𝟙_ C)) E).hom ≫ E ◁ (adj E).counit.app (𝟙_ C) ≫
        (ρ_ E).hom := by
  have h1 : leftTensorHomDiagonal (curriedTensor C) H adj (fun A B D => α_ A B D) E E (𝟙_ C) ▷ E ≫
      (adj E).counit.app (E ⊗ 𝟙_ C) = (α_ E ((H.obj (op E)).obj (𝟙_ C)) E).hom ≫
        E ◁ (adj E).counit.app (𝟙_ C) :=
    whiskerRight_homEquiv_comp_counit H adj _
  have h2 := (adj E).counit.naturality (ρ_ E).hom
  simp only [Functor.comp_map, Functor.id_map] at h2
  simp only [unitTensorHomDiagonal, MonoidalCategory.comp_whiskerRight, Category.assoc]
  change _ ≫ ((curriedTensor C).flip.obj E).map _ ≫ _ = _
  rw [h2]
  rw [← Category.assoc, h1, Category.assoc]

variable (E : C) [IsIso (leftTensorHomDiagonal (curriedTensor C) H adj (fun A B D => α_ A B D) E E
  (𝟙_ C))]

/-- The diagonal `E ⊗ H(E, 𝟙) ⟶ H(E, E)` is invertible. -/
instance : IsIso (unitTensorHomDiagonal H adj E) := by
  unfold unitTensorHomDiagonal; infer_instance

/-- The coevaluation `𝟙 ⟶ E ⊗ H(E, 𝟙)`: the section of `H(E, E)` adjoint to `λ_E`, followed by
the inverse of the diagonal. -/
def tensorHomDiagonalCoevaluation : 𝟙_ C ⟶ E ⊗ (H.obj (op E)).obj (𝟙_ C) :=
  (adj E).homEquiv _ _ (λ_ E).hom ≫ inv (unitTensorHomDiagonal H adj E)

/-- The first zigzag identity: `(η ▷ E) ≫ α ≫ (E ◁ ε_𝟙) = λ_E ≫ ρ_E⁻¹`, where `η` is
`tensorHomDiagonalCoevaluation`. -/
theorem tensorHomDiagonalCoevaluation_evaluation :
    tensorHomDiagonalCoevaluation H adj E ▷ E ≫ (α_ _ _ _).hom ≫
        E ◁ (adj E).counit.app (𝟙_ C) = (λ_ E).hom ≫ (ρ_ E).inv := by
  rw [← cancel_mono (ρ_ E).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← whiskerRight_unitTensorHomDiagonal_comp_counit,
    ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, tensorHomDiagonalCoevaluation,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact whiskerRight_homEquiv_comp_counit H adj _

/-- The interchange step: evaluating the outer pair first. -/
private theorem evaluation_interchange {D E' : C} (e : D ⊗ E' ⟶ 𝟙_ C) :
    (e ▷ D) ▷ E' ≫ (λ_ D).hom ▷ E' ≫ e =
      (α_ (D ⊗ E') D E').hom ≫ (D ⊗ E') ◁ e ≫ (ρ_ (D ⊗ E')).hom ≫ e := by
  rw [leftUnitor_whiskerRight]
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc, ← leftUnitor_naturality, ← whisker_exchange_assoc,
    unitors_equal, rightUnitor_naturality]

/-- The structural part of the second zigzag identity. -/
private theorem zigzag_structural {D E' : C} (c : 𝟙_ C ⟶ E' ⊗ D) (e : D ⊗ E' ⟶ 𝟙_ C) :
    (D ◁ c) ▷ E' ≫ (α_ D E' D).inv ▷ E' ≫ (α_ (D ⊗ E') D E').hom ≫ (D ⊗ E') ◁ e =
      (α_ D (𝟙_ C) E').hom ≫ D ◁ (c ▷ E' ≫ (α_ E' D E').hom ≫ E' ◁ e) ≫
        (α_ D E' (𝟙_ C)).inv := by
  monoidal

private theorem unitors_structural (D E' : C) :
    (α_ D (𝟙_ C) E').hom ≫ D ◁ ((λ_ E').hom ≫ (ρ_ E').inv) ≫ (α_ D E' (𝟙_ C)).inv ≫
        (ρ_ (D ⊗ E')).hom = (ρ_ D).hom ▷ E' := by
  monoidal

/-- The second zigzag identity: `(E^∨ ◁ η) ≫ α⁻¹ ≫ (ε_𝟙 ▷ E^∨) = ρ_{E^∨} ≫ λ_{E^∨}⁻¹`, where
`E^∨ = H(E, 𝟙)` and `η` is `tensorHomDiagonalCoevaluation`. -/
theorem tensorHomDiagonalEvaluation_coevaluation :
    (H.obj (op E)).obj (𝟙_ C) ◁ tensorHomDiagonalCoevaluation H adj E ≫ (α_ _ _ _).inv ≫
        (adj E).counit.app (𝟙_ C) ▷ (H.obj (op E)).obj (𝟙_ C) =
      (ρ_ ((H.obj (op E)).obj (𝟙_ C))).hom ≫ (λ_ ((H.obj (op E)).obj (𝟙_ C))).inv := by
  rw [← cancel_mono (λ_ ((H.obj (op E)).obj (𝟙_ C))).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ((adj E).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change (_ ▷ E) ≫ _ = (_ ▷ E) ≫ _
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [evaluation_interchange, reassoc_of% zigzag_structural,
    tensorHomDiagonalCoevaluation_evaluation]
  exact (reassoc_of% (unitors_structural ((H.obj (op E)).obj (𝟙_ C)) E)) _

/-- **A left dual from an invertible tensor–Hom diagonal**: if `E ⊗ H(E, 𝟙) ⟶ H(E, E ⊗ 𝟙)` is
invertible, then `H(E, 𝟙)` is a left dual of `E`, with evaluation the counit
`H(E, 𝟙) ⊗ E ⟶ 𝟙`. -/
@[instance_reducible]
def exactPairingOfIsIsoLeftTensorHomDiagonal : ExactPairing E ((H.obj (op E)).obj (𝟙_ C)) where
  coevaluation' := tensorHomDiagonalCoevaluation H adj E
  evaluation' := (adj E).counit.app (𝟙_ C)
  coevaluation_evaluation' := tensorHomDiagonalEvaluation_coevaluation H adj E
  evaluation_coevaluation' := tensorHomDiagonalCoevaluation_evaluation H adj E

/-- The evaluation of `exactPairingOfIsIsoLeftTensorHomDiagonal` is the counit at `𝟙`. -/
theorem exactPairingOfIsIsoLeftTensorHomDiagonal_evaluation :
    @ExactPairing.evaluation _ _ _ E _ (exactPairingOfIsIsoLeftTensorHomDiagonal H adj E) =
      (adj E).counit.app (𝟙_ C) :=
  rfl

/-- The coevaluation of `exactPairingOfIsIsoLeftTensorHomDiagonal`. -/
theorem exactPairingOfIsIsoLeftTensorHomDiagonal_coevaluation :
    @ExactPairing.coevaluation _ _ _ E _ (exactPairingOfIsIsoLeftTensorHomDiagonal H adj E) =
      tensorHomDiagonalCoevaluation H adj E :=
  rfl

section Pairing

variable {H adj}

/-- The map `K ⊗ Y ⟶ H(X, K)` of an exact pairing `(X, Y)`: the adjoint, for `- ⊗ X ⊣ H(X, -)`,
of `(K ⊗ Y) ⊗ X ≅ K ⊗ (Y ⊗ X) ⟶ K ⊗ 𝟙 ≅ K`. -/
def exactPairingTensorHomMap (X Y : C) [ExactPairing X Y] (K : C) :
    K ⊗ Y ⟶ (H.obj (op X)).obj K :=
  (adj X).homEquiv _ _ ((α_ K Y X).hom ≫ K ◁ ε_ X Y ≫ (ρ_ K).hom)

/-- **For an exact pairing `(X, Y)`, the map `K ⊗ Y ⟶ H(X, K)` is an isomorphism**: precomposed
with it, morphisms into `H(X, K)` are the morphisms `A ⊗ X ⟶ K`, which are the morphisms
`A ⟶ K ⊗ Y` by the pairing. -/
theorem isIso_exactPairingTensorHomMap (X Y : C) [ExactPairing X Y] (K : C) :
    IsIso (exactPairingTensorHomMap (H := H) (adj := adj) X Y K) := by
  refine isIso_of_yoneda_map_bijective _ fun A ↦ ?_
  have e : (fun g : A ⟶ K ⊗ Y ↦ g ≫ exactPairingTensorHomMap (H := H) (adj := adj) X Y K) =
      (adj X).homEquiv A K ∘ (tensorRightHomEquiv A X Y K).symm := by
    funext g
    exact ((adj X).homEquiv_naturality_left g _).symm
  rw [e]
  exact ((adj X).homEquiv A K).bijective.comp (tensorRightHomEquiv A X Y K).symm.bijective

/-- **The map `K ⊗ Y ⟶ H(X, K)` is natural in `K`.** -/
theorem exactPairingTensorHomMap_naturality (X Y : C) [ExactPairing X Y] {K K' : C}
    (φ : K ⟶ K') :
    φ ▷ Y ≫ exactPairingTensorHomMap (H := H) (adj := adj) X Y K' =
      exactPairingTensorHomMap (H := H) (adj := adj) X Y K ≫ (H.obj (op X)).map φ := by
  refine ((adj X).homEquiv_naturality_left _ _).symm.trans
    (Eq.trans ?_ ((adj X).homEquiv_naturality_right _ _))
  congr 1
  simp only [Functor.flip_obj_obj, curriedTensor_obj_obj, Functor.flip_obj_map,
    curriedTensor_map_app, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

end Pairing

section Functor

variable {D : Type*} [Category D] [MonoidalCategory D] {H adj}
  {HD : Dᵒᵖ ⥤ D ⥤ D} {adjD : ∀ P : D, (curriedTensor D).flip.obj P ⊣ HD.obj (op P)}
  (F : C ⥤ D) [F.Monoidal]
  (μ' : Functor.uncurry.obj (curriedTensor C) ⋙ F ≅
    F.prod F ⋙ Functor.uncurry.obj (curriedTensor D))
  (hμ' : ∀ A B : C, μ'.hom.app (A, B) = Functor.OplaxMonoidal.δ F A B)

include hμ' in
/-- **A monoidal functor carries the map `K ⊗ Y ⟶ H(X, K)` of an exact pairing `(X, Y)` to the one
of the image pairing `(F X, F Y)`**: `F(K ⊗ Y) ⟶ F H(X, K) ⟶ H(F X, F K)`, the second arrow the
pullback map of internal Homs, is `F(K ⊗ Y) ≅ F K ⊗ F Y ⟶ H(F X, F K)`. -/
theorem map_exactPairingTensorHomMap_comp_pullbackHomMap (X Y K : C) [ExactPairing X Y] :
    letI := ExactPairing.map F X Y
    F.map (exactPairingTensorHomMap (H := H) (adj := adj) X Y K) ≫
        pullbackHomMap (curriedTensor C) (curriedTensor D) μ' H HD adj adjD X K =
      Functor.OplaxMonoidal.δ F K Y ≫
        exactPairingTensorHomMap (H := HD) (adj := adjD) (F.obj X) (F.obj Y) (F.obj K) := by
  let := ExactPairing.map F X Y
  have hinv : ∀ A B : C, μ'.inv.app (A, B) = Functor.LaxMonoidal.μ F A B := fun A B => by
    rw [← cancel_epi (μ'.hom.app (A, B)), Iso.hom_inv_id_app, hμ']
    exact (Functor.Monoidal.δ_μ F A B).symm
  apply ((adjD (F.obj X)).homEquiv _ _).symm.injective
  simp only [pullbackHomMap, exactPairingTensorHomMap, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply, hinv]
  have ht := whiskerRight_homEquiv_comp_counit H adj
    ((α_ K Y X).hom ≫ K ◁ ε_ X Y ≫ (ρ_ K).hom)
  change F.map _ ▷ F.obj X ≫ _ = Functor.OplaxMonoidal.δ F K Y ▷ F.obj X ≫ _
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp]
  change Functor.LaxMonoidal.μ F _ X ≫ F.map ((((adj X).homEquiv _ _)
    ((α_ K Y X).hom ≫ K ◁ ε_ X Y ≫ (ρ_ K).hom)) ▷ X ≫ (adj X).counit.app K) = _
  rw [ht, ExactPairing.map_evaluation]
  simp only [Functor.map_comp, Functor.Monoidal.map_associator, Category.assoc,
    Functor.Monoidal.μ_δ_assoc, MonoidalCategory.whiskerLeft_comp, Functor.Monoidal.μ_δ_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc, Functor.Monoidal.map_rightUnitor F K,
    Functor.Monoidal.μ_δ_assoc]

end Functor

end CategoryTheory.PullbackInternalHom
