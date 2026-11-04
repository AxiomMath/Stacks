module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Left duals as tensor-compatible right adjoints

Let `C` be a monoidal category and let `X Y : C`. If `Y` is a left dual of `X`, i.e. if `X` and
`Y` form an exact pairing, then `Z ↦ Z ⊗ Y` is a right adjoint of `Z' ↦ Z' ⊗ X`; this is
`CategoryTheory.tensorRightAdjunction`.

Conversely, an arbitrary adjunction `tensorRight X ⊣ tensorRight Y` produces a candidate
coevaluation `η : 𝟙_ C ⟶ X ⊗ Y` and a candidate evaluation `ε : Y ⊗ X ⟶ 𝟙_ C`, but the two
triangle identities of an exact pairing need not hold: what the adjunction gives for free are only
the two weaker identities `Adjunction.unit_app_comp_tensorEvaluation_whiskerRight` and
`Adjunction.tensorCoevaluation_whiskerRight_comp_counit_app`, in which one of the two structure
maps is still an unspecialised component of the unit or of the counit.

The extra hypothesis that repairs this is that the adjunction be *compatible with the tensor
structure*: for every `W`, tensoring on the left by `W` commutes with the adjunction bijection
`Mor(Z' ⊗ X, Z) ≃ Mor(Z', Z ⊗ Y)`. This is `Adjunction.IsTensorCompatible`, and the two
directions

* `ExactPairing.isTensorCompatible_tensorRightAdjunction`
* `Adjunction.IsTensorCompatible.exactPairing`

say that being a tensor-compatible right adjoint of `tensorRight X` is an equivalent formulation
of being a left dual of `X`.

## Main declarations

* `Adjunction.IsTensorCompatible`: compatibility of an adjunction `tensorRight X ⊣ tensorRight Y`
  with the tensor structure.
* `Adjunction.tensorCoevaluation`, `Adjunction.tensorEvaluation`: the candidate coevaluation and
  evaluation extracted from such an adjunction.
* `ExactPairing.isTensorCompatible_tensorRightAdjunction`: the adjunction attached to an exact
  pairing is tensor compatible.
* `Adjunction.IsTensorCompatible.exactPairing`: a tensor-compatible adjunction
  `tensorRight X ⊣ tensorRight Y` exhibits `Y` as a left dual of `X`.
* `Adjunction.isIso_tensorEvaluation` and `ExactPairing.isIso_evaluation`: when `tensorRight X`
  is an equivalence the candidate evaluation of such an adjunction, and in particular the
  evaluation of an exact pairing on `X` and `Y`, is an isomorphism.

## References

* [Stacks, Tag 0FFR](https://stacks.math.columbia.edu/tag/0FFR)
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section HomEquiv

variable (X Y A B : C) [ExactPairing X Y]

/-- The hom-set bijection underlying `tensorRightAdjunction X Y` is `tensorRightHomEquiv`. -/
theorem tensorRightAdjunction_homEquiv :
    (tensorRightAdjunction X Y).homEquiv A B = tensorRightHomEquiv A X Y B := by
  have h := Adjunction.mkOfHomEquiv_homEquiv
    (F := tensorRight X) (G := tensorRight Y)
    { homEquiv := fun A Z => tensorRightHomEquiv A X Y Z
      homEquiv_naturality_left_symm := fun f g => tensorRightHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorRightHomEquiv_naturality f g }
  exact congrFun (congrFun h A) B

end HomEquiv

namespace Adjunction

variable {X Y : C}

/-- An adjunction `adj : tensorRight X ⊣ tensorRight Y`, i.e. a bijection
`Mor(Z' ⊗ X, Z) ≃ Mor(Z', Z ⊗ Y)` functorial in `Z` and `Z'`, is *compatible with the tensor
structure* if for all `W`, `Z`, `Z'` the square

```
  Mor(Z' ⊗ X, Z)         →  Mor(Z', Z ⊗ Y)
   | id_W ⊗ -                | id_W ⊗ -
   v                         v
  Mor(W ⊗ Z' ⊗ X, W ⊗ Z) →  Mor(W ⊗ Z', W ⊗ Z ⊗ Y)
```

commutes, the two vertical maps being `f ↦ 𝟙 W ⊗ f` read through the associators. -/
@[stacks 0FFR]
def IsTensorCompatible (adj : tensorRight X ⊣ tensorRight Y) : Prop :=
  ∀ (W Z Z' : C) (f : Z' ⊗ X ⟶ Z),
    adj.homEquiv (W ⊗ Z') (W ⊗ Z) ((α_ W Z' X).hom ≫ W ◁ f)
      = W ◁ adj.homEquiv Z' Z f ≫ (α_ W Z Y).inv

variable (adj : tensorRight X ⊣ tensorRight Y)

/-- The candidate coevaluation `η : 𝟙_ C ⟶ X ⊗ Y` attached to an adjunction
`tensorRight X ⊣ tensorRight Y`: the image of `(λ_ X).hom : 𝟙_ C ⊗ X ⟶ X` under the adjunction
bijection. It is the unit component at `𝟙_ C`, read through the coherence isomorphism. -/
def tensorCoevaluation : 𝟙_ C ⟶ X ⊗ Y := adj.homEquiv (𝟙_ C) X (λ_ X).hom

/-- The candidate evaluation `ε : Y ⊗ X ⟶ 𝟙_ C` attached to an adjunction
`tensorRight X ⊣ tensorRight Y`: the preimage of `(λ_ Y).inv : Y ⟶ 𝟙_ C ⊗ Y` under the adjunction
bijection. It is the counit component at `𝟙_ C`, read through the coherence isomorphism. -/
def tensorEvaluation : Y ⊗ X ⟶ 𝟙_ C := (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv

/-- Unfolding lemma for `Adjunction.tensorCoevaluation`. -/
theorem tensorCoevaluation_def :
    adj.tensorCoevaluation = adj.homEquiv (𝟙_ C) X (λ_ X).hom := rfl

/-- Unfolding lemma for `Adjunction.tensorEvaluation`. -/
theorem tensorEvaluation_def :
    adj.tensorEvaluation = (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv := rfl

/-- The unit component at `𝟙_ C` is the candidate coevaluation, read through the coherence
isomorphism `(𝟙_ C ⊗ X) ⊗ Y ≅ X ⊗ Y`. -/
theorem unit_app_unit_eq :
    adj.unit.app (𝟙_ C) = adj.tensorCoevaluation ≫ (λ_ X).inv ▷ Y := by
  rw [tensorCoevaluation_def, adj.homEquiv_unit, Functor.flip_obj_map, curriedTensor_map_app,
    Category.assoc, ← comp_whiskerRight]
  simp

/-- The counit component at `𝟙_ C` is the candidate evaluation, read through the coherence
isomorphism `Y ⊗ X ≅ (𝟙_ C ⊗ Y) ⊗ X`. -/
theorem counit_app_unit_eq :
    adj.counit.app (𝟙_ C) = (λ_ Y).hom ▷ X ≫ adj.tensorEvaluation := by
  rw [tensorEvaluation_def, adj.homEquiv_counit, Functor.flip_obj_map, curriedTensor_map_app,
    ← Category.assoc, ← comp_whiskerRight]
  simp

/-- **If `tensorRight X` is an equivalence, the candidate evaluation of any adjunction
`tensorRight X ⊣ tensorRight Y` is an isomorphism.** The counit of an adjunction whose left
adjoint is an equivalence is invertible, and by `Adjunction.counit_app_unit_eq` its component at
`𝟙_ C` is the candidate evaluation up to a coherence isomorphism. No compatibility with the
tensor structure is needed. -/
theorem isIso_tensorEvaluation [(tensorRight X).IsEquivalence] :
    IsIso adj.tensorEvaluation := by
  have h : IsIso ((λ_ Y).hom ▷ X ≫ adj.tensorEvaluation) := by
    rw [← adj.counit_app_unit_eq]
    infer_instance
  exact IsIso.of_isIso_comp_left ((λ_ Y).hom ▷ X) adj.tensorEvaluation

/-- The first identity that an adjunction `tensorRight X ⊣ tensorRight Y` supplies for free,
with no compatibility with the tensor structure assumed: `(ε ⊗ 1_Y) ∘ η_Y = 1_Y`, where `η_Y` is
the component of the unit at `Y`. -/
@[stacks 0FFR]
theorem unit_app_comp_tensorEvaluation_whiskerRight :
    adj.unit.app Y ≫ adj.tensorEvaluation ▷ Y = (λ_ Y).inv := by
  have key : adj.unit.app (𝟙_ C ⊗ Y) ≫ adj.counit.app (𝟙_ C) ▷ Y = 𝟙 (𝟙_ C ⊗ Y) :=
    adj.right_triangle_components (𝟙_ C)
  have hnat : adj.unit.app (𝟙_ C ⊗ Y) ≫ ((λ_ Y).hom ▷ X) ▷ Y = (λ_ Y).hom ≫ adj.unit.app Y :=
    (adj.unit.naturality (λ_ Y).hom).symm
  rw [adj.counit_app_unit_eq, comp_whiskerRight, ← Category.assoc, hnat, Category.assoc] at key
  exact (cancel_epi (λ_ Y).hom).mp (by rw [key, Iso.hom_inv_id])

/-- The second identity that an adjunction `tensorRight X ⊣ tensorRight Y` supplies for free,
with no compatibility with the tensor structure assumed: `ε_X ∘ (η ⊗ 1_X) = 1_X`, where `ε_X` is
the component of the counit at `X`. -/
@[stacks 0FFR]
theorem tensorCoevaluation_whiskerRight_comp_counit_app :
    adj.tensorCoevaluation ▷ X ≫ adj.counit.app X = (λ_ X).hom := by
  have key : adj.unit.app (𝟙_ C) ▷ X ≫ adj.counit.app (𝟙_ C ⊗ X) = 𝟙 (𝟙_ C ⊗ X) :=
    adj.left_triangle_components (𝟙_ C)
  have hnat : ((λ_ X).inv ▷ Y) ▷ X ≫ adj.counit.app (𝟙_ C ⊗ X)
      = adj.counit.app X ≫ (λ_ X).inv := adj.counit.naturality (λ_ X).inv
  rw [adj.unit_app_unit_eq, comp_whiskerRight, Category.assoc, hnat, ← Category.assoc] at key
  exact (cancel_mono (λ_ X).inv).mp (by rw [key, Iso.hom_inv_id])

end Adjunction

/-- The adjunction `tensorRight X ⊣ tensorRight Y` attached to an exact pairing is compatible
with the tensor structure. -/
@[stacks 0FFR]
theorem ExactPairing.isTensorCompatible_tensorRightAdjunction (X Y : C) [ExactPairing X Y] :
    (tensorRightAdjunction X Y).IsTensorCompatible := by
  intro W Z Z' f
  simp only [tensorRightAdjunction_homEquiv]
  refine (Equiv.eq_symm_apply _).mp ?_
  have h := tensorRightHomEquiv_tensor (X := Z') (X' := W) (Y := X) (Y' := Y) (Z := Z) (Z' := W)
    (tensorRightHomEquiv Z' X Y Z f) (𝟙 W)
  simp only [Equiv.symm_apply_apply, id_tensorHom] at h
  exact h.symm

/-- The candidate evaluation of the adjunction attached to an exact pairing is the evaluation of
that pairing. -/
theorem tensorRightAdjunction_tensorEvaluation (X Y : C) [ExactPairing X Y] :
    (tensorRightAdjunction X Y).tensorEvaluation = ε_ X Y := by
  have hcoh : (λ_ Y).inv ▷ X ≫ (α_ (𝟙_ C) Y X).hom ≫ (λ_ (Y ⊗ X)).hom = 𝟙 (Y ⊗ X) := by
    monoidal
  rw [Adjunction.tensorEvaluation_def, tensorRightAdjunction_homEquiv]
  show (λ_ Y).inv ▷ X ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ X Y ≫ (ρ_ (𝟙_ C)).hom = ε_ X Y
  rw [← unitors_equal, leftUnitor_naturality, reassoc_of% hcoh]

/-- **The evaluation of an exact pairing is an isomorphism as soon as tensoring on the right by
the first object is an equivalence.** For an invertible object `X` of a monoidal category this
identifies a left dual of `X` as a tensor inverse of `X`, the pairing being the trivializing
isomorphism. -/
theorem ExactPairing.isIso_evaluation (X Y : C) [ExactPairing X Y]
    [(tensorRight X).IsEquivalence] : IsIso (ε_ X Y) := by
  rw [← tensorRightAdjunction_tensorEvaluation X Y]
  exact (tensorRightAdjunction X Y).isIso_tensorEvaluation

namespace Adjunction.IsTensorCompatible

variable {X Y : C} {adj : tensorRight X ⊣ tensorRight Y}

/-- The inverse form of tensor compatibility: tensoring on the left by `W` also commutes with the
inverse of the adjunction bijection. -/
theorem homEquiv_symm (h : adj.IsTensorCompatible) (W Z Z' : C) (g : Z' ⟶ Z ⊗ Y) :
    (adj.homEquiv (W ⊗ Z') (W ⊗ Z)).symm (W ◁ g ≫ (α_ W Z Y).inv)
      = (α_ W Z' X).hom ≫ W ◁ (adj.homEquiv Z' Z).symm g := by
  have key := h W Z Z' ((adj.homEquiv Z' Z).symm g)
  rw [Equiv.apply_symm_apply] at key
  rw [← key, Equiv.symm_apply_apply]

/-- For a tensor-compatible adjunction, every component of the unit is determined by the
candidate coevaluation. -/
theorem unit_app (h : adj.IsTensorCompatible) (W : C) :
    adj.unit.app W = (ρ_ W).inv ≫ W ◁ adj.tensorCoevaluation ≫ (α_ W X Y).inv := by
  have key := h W X (𝟙_ C) (λ_ X).hom
  rw [adj.homEquiv_unit, Functor.flip_obj_map, curriedTensor_map_app,
    MonoidalCategory.triangle] at key
  have hnat : adj.unit.app (W ⊗ 𝟙_ C) ≫ ((ρ_ W).hom ▷ X) ▷ Y = (ρ_ W).hom ≫ adj.unit.app W :=
    (adj.unit.naturality (ρ_ W).hom).symm
  rw [hnat] at key
  rw [adj.tensorCoevaluation_def, ← key]
  simp

/-- For a tensor-compatible adjunction, every component of the counit is determined by the
candidate evaluation. -/
theorem counit_app (h : adj.IsTensorCompatible) (W : C) :
    adj.counit.app W = (α_ W Y X).hom ≫ W ◁ adj.tensorEvaluation ≫ (ρ_ W).hom := by
  have key := h.homEquiv_symm W (𝟙_ C) Y (λ_ Y).inv
  rw [adj.homEquiv_counit, Functor.flip_obj_map, curriedTensor_map_app] at key
  have hcoh : W ◁ (λ_ Y).inv ≫ (α_ W (𝟙_ C) Y).inv = (ρ_ W).inv ▷ Y := by monoidal
  rw [hcoh] at key
  have hnat : ((ρ_ W).inv ▷ Y) ▷ X ≫ adj.counit.app (W ⊗ 𝟙_ C)
      = adj.counit.app W ≫ (ρ_ W).inv := adj.counit.naturality (ρ_ W).inv
  rw [hnat] at key
  rw [adj.tensorEvaluation_def, ← Category.assoc, ← key]
  simp

/-- The `evaluation_coevaluation` triangle identity for the candidate coevaluation and evaluation
of a tensor-compatible adjunction. -/
theorem evaluation_coevaluation (h : adj.IsTensorCompatible) :
    adj.tensorCoevaluation ▷ X ≫ (α_ X Y X).hom ≫ X ◁ adj.tensorEvaluation
      = (λ_ X).hom ≫ (ρ_ X).inv := by
  have key : adj.unit.app (𝟙_ C) ▷ X ≫ adj.counit.app (𝟙_ C ⊗ X) = 𝟙 (𝟙_ C ⊗ X) :=
    adj.left_triangle_components (𝟙_ C)
  rw [h.unit_app, h.counit_app] at key
  rw [← Category.id_comp ((λ_ X).hom ≫ (ρ_ X).inv), ← key]
  monoidal

/-- The `coevaluation_evaluation` triangle identity for the candidate coevaluation and evaluation
of a tensor-compatible adjunction. -/
theorem coevaluation_evaluation (h : adj.IsTensorCompatible) :
    Y ◁ adj.tensorCoevaluation ≫ (α_ Y X Y).inv ≫ adj.tensorEvaluation ▷ Y
      = (ρ_ Y).hom ≫ (λ_ Y).inv := by
  have key : adj.unit.app (𝟙_ C ⊗ Y) ≫ adj.counit.app (𝟙_ C) ▷ Y = 𝟙 (𝟙_ C ⊗ Y) :=
    adj.right_triangle_components (𝟙_ C)
  rw [h.unit_app, h.counit_app] at key
  rw [← Category.comp_id ((ρ_ Y).hom ≫ (λ_ Y).inv), ← key]
  monoidal

/-- **The converse direction of Stacks 0FFR.** A tensor-compatible adjunction
`tensorRight X ⊣ tensorRight Y` exhibits `Y` as a left dual of `X`: its candidate coevaluation
and evaluation satisfy both triangle identities of an exact pairing. -/
@[instance_reducible, stacks 0FFR]
def exactPairing (h : adj.IsTensorCompatible) : ExactPairing X Y where
  coevaluation' := adj.tensorCoevaluation
  evaluation' := adj.tensorEvaluation
  coevaluation_evaluation' := h.coevaluation_evaluation
  evaluation_coevaluation' := h.evaluation_coevaluation

end Adjunction.IsTensorCompatible

end CategoryTheory

/- Stacks 0FFR, first assertion: since `Z ↦ Z ⊗ Y` is a right adjoint of `Z' ↦ Z' ⊗ X` when `Y`
is a left dual of `X`, uniqueness of adjoints makes a left dual unique up to unique isomorphism.
Mathlib records the resulting isomorphism between two left duals of a fixed object; substituting
`X₁ := Y₁`, `X₂ := Y₂`, `Y := X` in `leftDualIso` recovers the Stacks phrasing, in which `Y₁` and
`Y₂` are the two left duals of `X`. -/
add_to_stacks 0FFR CategoryTheory.leftDualIso
