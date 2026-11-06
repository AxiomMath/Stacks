module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective

/-!
# The invertible sheaf of a sum of effective Cartier divisors

Let `X` be an algebraic space over a scheme `S` and let `D₁, D₂ ⊆ X` be effective Cartier
divisors with sum `D = D₁ + D₂`.  Following Stacks 0842 there is a *unique* isomorphism
`𝒪_X(D₁) ⊗_{𝒪_X} 𝒪_X(D₂) ⟶ 𝒪_X(D)` carrying `1_{D₁} ⊗ 1_{D₂}` to `1_D`.

## Main definitions

* `AlgebraicGeometry.Space.tensorCanonicalSection` is the global section `1_{D₁} ⊗ 1_{D₂}` of
  `𝒪_X(D₁) ⊗_{𝒪_X} 𝒪_X(D₂)`.
* `AlgebraicGeometry.Space.sumInvertibleEvaluation` is the evaluation pairing
  `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ 𝓘_D ≅ 𝒪_X`, assembled from the two evaluation pairings
  `𝒪_X(Dᵢ) ⊗ 𝓘_{Dᵢ} ≅ 𝒪_X` of Stacks 0841 and the multiplication `𝓘_{D₁} ⊗ 𝓘_{D₂} ≅ 𝓘_D`.
* `AlgebraicGeometry.Space.mapTensorEvaluation` is the pairing against `𝓘_D` attached to a
  morphism `𝒪_X(D₁) ⊗ 𝒪_X(D₂) ⟶ 𝒪_X(D)`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_tensorInvertibleSheafIso` is **Stacks 0842**.
* `AlgebraicGeometry.Space.idealSumEvaluationAt_canonicalTensorAt`: `1_{D₁} ⊗ 1_{D₂}` pairs with
  a local section of `𝓘_D` to give that section — the normalisation which pins the isomorphism
  down.
* `AlgebraicGeometry.Space.tensorHomAt_tensorPairing_of_map_eq`: a morphism which becomes an
  endomorphism `g` of `𝒪_X` after tensoring by `𝓘_D` has its values against `𝓘_D` computed
  by `g`.
* `AlgebraicGeometry.Space.eq_id_of_app_ι_eq`: an endomorphism of `𝒪_X` acting as the identity
  on `𝓘_D` is the identity, because `1_D` is a regular section (Stacks 0847 (1)).

## Implementation notes

Both halves of the statement come from the same computation.  Tensoring by the invertible sheaf
`𝓘_D` is an equivalence, so a morphism `θ : 𝒪_X(D₁) ⊗ 𝒪_X(D₂) ⟶ 𝒪_X(D)` is the same thing as
an endomorphism `g` of `𝒪_X`, read off from the two evaluation pairings; and the value of `θ`
on `1_{D₁} ⊗ 1_{D₂}`, paired against a local section `t` of `𝓘_D`, is `g` applied to `t`.
Existence is the case `g = 𝟙`, and uniqueness is the statement that `g` is determined — which
is where regularity of `1_D` enters.

The isomorphism is produced by full faithfulness of tensoring by `𝓘_D` rather than by a
monoidal reassociation of `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ (𝓘_{D₁} ⊗ 𝓘_{D₂})`: the sheaf-level tensor
product of this library has no monoidal-category instance, while the *presheaf*-level one does,
so the only reassociation performed is `MonoidalCategory.tensorμ` on presheaves of modules, in
`AlgebraicGeometry.Space.tensorEvaluationPresheafPairing`, and the passage to sheaves is by the
universal property of sheafification throughout.

Morphisms out of a sheafified tensor product use the native curried
`Stacks.SheafOfModules.Tensor.sheafTensor`, and tensoring by `𝓘_D` on the right is its `flip`
at `𝓘_D`, an equivalence by `Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor`,
so its full faithfulness is used directly. Uniqueness follows by cancelling the evaluation
isomorphism.

## References

* [Stacks Project, Tag 0842](https://stacks.math.columbia.edu/tag/0842)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083V](https://stacks.math.columbia.edu/tag/083V)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open Stacks.PresheafOfModules.TensorInternalHom
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification (sheafify toSheafify sheafifyAdjunction)


namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)


/-! ### The evaluation pairing of the tensor product of the two invertible sheaves -/

section Evaluation

variable (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (hD₁ : IsEffectiveCartierDivisor B S hS X D₁)
    (hD₂ : IsEffectiveCartierDivisor B S hS X D₂)

/-- The presheaf-level pairing `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ (𝓘_{D₁} ⊗ 𝓘_{D₂}) ⟶ 𝒪_X`: interchange
the two middle factors and multiply the two evaluation pairings `𝒪_X(Dᵢ) ⊗ 𝓘_{Dᵢ} ≅ 𝒪_X`. -/
def tensorEvaluationPresheafPairing :
    (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
        modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)) ⊗
      (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁) ⊗
        modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)) ⟶
    modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  MonoidalCategory.tensorμ
      (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁))
      (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂))
      (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁))
      (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)) ≫
    (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (idealSheafOfModules B S hS X D₁) (associatedInvertibleSheaf B S hS X D₁ hD₁)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (associatedInvertibleSheafEvaluation B S hS X D₁ hD₁) ⊗ₘ
      tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (idealSheafOfModules B S hS X D₂) (associatedInvertibleSheaf B S hS X D₂ hD₂)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (associatedInvertibleSheafEvaluation B S hS X D₂ hD₂)) ≫
    (λ_ (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)))).hom

/-- The pairing of the tensor products takes a pure tensor to the product of the values of the
two evaluation pairings. -/
theorem tensorEvaluationPresheafPairing_tmul (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x₁ : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁)).obj W)
    (x₂ : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)).obj W)
    (t₁ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁)).obj W)
    (t₂ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)).obj W) :
    unitSectionOf B S hS X
        (tensorHomAt (structureCommRings B S hS X) _ _ _
          (tensorEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) W
          ((x₁ ⊗ₜ x₂) ⊗ₜ (t₁ ⊗ₜ t₂))) =
      unitSectionOf B S hS X
          (tensorHomAt (structureCommRings B S hS X) _ _ _
            (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
              (idealSheafOfModules B S hS X D₁) (associatedInvertibleSheaf B S hS X D₁ hD₁)
              (SheafOfModules.unit (structureRingSheaf B S hS X))
              (associatedInvertibleSheafEvaluation B S hS X D₁ hD₁)) W (x₁ ⊗ₜ t₁)) *
        unitSectionOf B S hS X
          (tensorHomAt (structureCommRings B S hS X) _ _ _
            (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
              (idealSheafOfModules B S hS X D₂) (associatedInvertibleSheaf B S hS X D₂ hD₂)
              (SheafOfModules.unit (structureRingSheaf B S hS X))
              (associatedInvertibleSheafEvaluation B S hS X D₂ hD₂)) W (x₂ ⊗ₜ t₂)) := by
  rfl

/-- Sheafification inverts the presheaf-level pairing of the tensor products: it is an
interchange isomorphism followed by the tensor product of the two evaluation pairings, each of
which is a unit of sheafification followed by an isomorphism, followed by a unit constraint. -/
theorem isIso_sheafify_map_tensorEvaluationPresheafPairing :
    IsIso ((sheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property).map
      (tensorEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)) := by
  have hpair : ∀ (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D),
      IsIso ((sheafify (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property).map
        (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (idealSheafOfModules B S hS X D) (associatedInvertibleSheaf B S hS X D hD)
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (associatedInvertibleSheafEvaluation B S hS X D hD))) := fun D hD =>
    Stacks.SheafOfModules.isIso_sheafify_map_comp _ _ _ _
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify _ _ _)
      (Stacks.SheafOfModules.isIso_sheafify_map_of_isIso _ _ _
        (Stacks.SheafOfModules.isIso_val_of_iso _))
  have htμ : IsIso (MonoidalCategory.tensorμ
      (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁))
      (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂))
      (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁))
      (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂))) :=
    ⟨MonoidalCategory.tensorδ _ _ _ _,
      MonoidalCategory.tensorμ_tensorδ _ _ _ _, MonoidalCategory.tensorδ_tensorμ _ _ _ _⟩
  refine Stacks.SheafOfModules.isIso_sheafify_map_comp _ _ _ _
    (Stacks.SheafOfModules.isIso_sheafify_map_of_isIso _ _ _ htμ) ?_
  refine Stacks.SheafOfModules.isIso_sheafify_map_comp _ _ _ _ ?_
    (Stacks.SheafOfModules.isIso_sheafify_map_of_isIso _ _ _ (Iso.isIso_hom _))
  rw [MonoidalCategory.tensorHom_def]
  refine Stacks.SheafOfModules.isIso_sheafify_map_comp _ _ _ _
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight _ _ _ _
      (hpair D₁ hD₁))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft _ _ _ _
      (hpair D₂ hD₂))

include hD₂ in
/-- Sheafification inverts the presheaf-level multiplication `𝓘_{D₁} ⊗ 𝓘_{D₂} ⟶ 𝓘_{D₁+D₂}`:
it is a unit of sheafification followed by the isomorphism of
`AlgebraicGeometry.Space.sumIdealIso`. -/
theorem isIso_sheafify_map_idealMulToSumPresheaf :
    IsIso ((sheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property).map
      (idealMulToSumPresheaf B S hS X D₁ D₂)) := by
  rw [← toSheafify_comp_sumIdealHom B S hS X D₁ D₂]
  have := isIso_sumIdealHom B S hS X D₁ D₂ hD₂
  exact Stacks.SheafOfModules.isIso_sheafify_map_comp _ _ _ _
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify _ _ _)
    (Stacks.SheafOfModules.isIso_sheafify_map_of_isIso _ _ _
      (Stacks.SheafOfModules.isIso_val_of_iso (asIso (sumIdealHom B S hS X D₁ D₂))))

/-- The pairing `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ 𝓘_{D₁+D₂} ⟶ 𝒪_X` obtained from
`AlgebraicGeometry.Space.tensorEvaluationPresheafPairing` by replacing `𝓘_{D₁} ⊗ 𝓘_{D₂}` with
`𝓘_{D₁+D₂}`. -/
def idealSumEvaluationPresheafPairing :
    (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
        modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)) ⊗
      modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)) ⟶
    modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  Stacks.SheafOfModules.liftAlongSheafifyIso (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property
    ((modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
        modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)) ◁
      idealMulToSumPresheaf B S hS X D₁ D₂)
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft _ _ _ _
      (isIso_sheafify_map_idealMulToSumPresheaf B S hS X D₁ D₂ hD₂))
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (tensorEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)

/-- The pairing against `𝓘_{D₁+D₂}` restricts along the multiplication of the two ideal sheaves
to the pairing against `𝓘_{D₁} ⊗ 𝓘_{D₂}`. -/
theorem whiskerLeft_comp_idealSumEvaluationPresheafPairing :
    ((modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)) ◁
        idealMulToSumPresheaf B S hS X D₁ D₂) ≫
      idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂ =
      tensorEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂ :=
  Stacks.SheafOfModules.comp_liftAlongSheafifyIso _ _ _ _ _ _

/-- Sheafification inverts the pairing against `𝓘_{D₁+D₂}`. -/
theorem isIso_sheafify_map_idealSumEvaluationPresheafPairing :
    IsIso ((sheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property).map
      (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)) :=
  Stacks.SheafOfModules.isIso_sheafify_map_liftAlongSheafifyIso _ _ _ _ _ _
    (isIso_sheafify_map_tensorEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)

/-- The evaluation pairing `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ 𝓘_{D₁+D₂} ⟶ 𝒪_X` on the *sheafified* tensor
product of the two invertible sheaves, extending
`AlgebraicGeometry.Space.idealSumEvaluationPresheafPairing` along the unit of
sheafification. -/
def sumInvertibleEvaluationPresheafPairing :
    modulePresheaf B S hS X
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
              ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
              ((structureRingSheaf B S hS X).property)⟩).obj
              ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
              ((associatedInvertibleSheaf B S hS X D₂ hD₂)))) ⊗
        modulePresheaf B S hS X
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)) ⟶
      modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  Stacks.SheafOfModules.liftAlongSheafifyIso (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property
    (toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)) ▷
      modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight _ _ _ _
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify _ _ _))
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)

/-- The pairing on the sheafified tensor product restricts, along the unit of sheafification, to
the pairing on the tensor product of presheaves. -/
theorem whiskerRight_comp_sumInvertibleEvaluationPresheafPairing :
    (toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)) ▷
      modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ≫
      sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂ =
      idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂ :=
  Stacks.SheafOfModules.comp_liftAlongSheafifyIso _ _ _ _ _ _

/-- Sheafification inverts the pairing on the sheafified tensor product. -/
theorem isIso_sheafify_map_sumInvertibleEvaluationPresheafPairing :
    IsIso ((sheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property).map
      (sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)) :=
  Stacks.SheafOfModules.isIso_sheafify_map_liftAlongSheafifyIso (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property
    (toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)) ▷
      modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight _ _ _ _
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify _ _ _))
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)
    (isIso_sheafify_map_idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)

/-- The evaluation pairing `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ 𝓘_{D₁+D₂} ⟶ 𝒪_X` as a morphism of sheaves of
`𝒪_X`-modules. -/
def sumInvertibleEvaluationHom :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂)))))).obj
        ((idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)))) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).homEquiv _
      (SheafOfModules.unit (structureRingSheaf B S hS X))).symm
      (sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)

/-- The evaluation pairing `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ 𝓘_{D₁+D₂} ⟶ 𝒪_X` is an isomorphism: each of
the two evaluation pairings `𝒪_X(Dᵢ) ⊗ 𝓘_{Dᵢ} ≅ 𝒪_X` is one and so is the multiplication
`𝓘_{D₁} ⊗ 𝓘_{D₂} ≅ 𝓘_{D₁+D₂}`. -/
theorem isIso_sumInvertibleEvaluationHom :
    IsIso (sumInvertibleEvaluationHom B S hS X D₁ D₂ hD₁ hD₂) :=
  Stacks.SheafOfModules.isIso_of_isIso_sheafify_map_homEquiv _ _ _
    (isIso_sheafify_map_sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)

/-- **The evaluation pairing `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ 𝓘_{D₁+D₂} ≅ 𝒪_X`.** -/
def sumInvertibleEvaluation :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂)))))).obj
        ((idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)))) ≅
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  @asIso _ _ _ _ (sumInvertibleEvaluationHom B S hS X D₁ D₂ hD₁ hD₂)
    (isIso_sumInvertibleEvaluationHom B S hS X D₁ D₂ hD₁ hD₂)

/-- The pairing of presheaves attached to the evaluation isomorphism
`AlgebraicGeometry.Space.sumInvertibleEvaluation` is the pairing it was built from. -/
theorem tensorPairing_sumInvertibleEvaluation :
    tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
            ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
            ((structureRingSheaf B S hS X).property)⟩).obj
            ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
            ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂) =
      sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂ :=
  ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).homEquiv _
      (SheafOfModules.unit (structureRingSheaf B S hS X))).apply_symm_apply
    (sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂)

/-- The restriction maps of `𝒪_X` as a module over itself are the restriction maps of the
structure sheaf. -/
theorem unitSectionOf_restrictₛₗ {U V : (SmallEtale B S hS X.1)ᵒᵖ} (f : U ⟶ V)
    (z : (modulePresheaf B S hS X
      (SheafOfModules.unit (structureRingSheaf B S hS X))).obj U) :
    unitSectionOf B S hS X
        ((modulePresheaf B S hS X
          (SheafOfModules.unit (structureRingSheaf B S hS X))).restrictₛₗ f z) =
      ((structureRingSheaf B S hS X).obj.map f).hom (unitSectionOf B S hS X z) :=
  rfl

/-- **The canonical section `1_{D₁} ⊗ 1_{D₂}`** of `𝒪_X(D₁) ⊗_{𝒪_X} 𝒪_X(D₂)`: the image under
the unit of sheafification of the pure tensor of the two canonical sections. -/
def tensorCanonicalSection :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂)))).sections :=
  PresheafOfModules.sectionsMk
    (M := modulePresheaf B S hS X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩).obj
          ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
          ((associatedInvertibleSheaf B S hS X D₂ hD₂)))))
    (fun U ↦ ((toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂))).app U).hom
      ((canonicalSection B S hS X D₁ hD₁).val U ⊗ₜ (canonicalSection B S hS X D₂ hD₂).val U))
    (fun {U V} f ↦ by
      refine Eq.trans (PresheafOfModules.naturality_apply
        (toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
            modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂))) f
        ((canonicalSection B S hS X D₁ hD₁).val U ⊗ₜ
          (canonicalSection B S hS X D₂ hD₂).val U)).symm ?_
      refine congrArg ((toSheafify (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂))).app V).hom ?_
      have h1 : (modulePresheaf B S hS X
            (associatedInvertibleSheaf B S hS X D₁ hD₁)).restrictₛₗ f
            ((canonicalSection B S hS X D₁ hD₁).val U) =
          (canonicalSection B S hS X D₁ hD₁).val V :=
        PresheafOfModules.sections_property (canonicalSection B S hS X D₁ hD₁) f
      have h2 : (modulePresheaf B S hS X
            (associatedInvertibleSheaf B S hS X D₂ hD₂)).restrictₛₗ f
            ((canonicalSection B S hS X D₂ hD₂).val U) =
          (canonicalSection B S hS X D₂ hD₂).val V :=
        PresheafOfModules.sections_property (canonicalSection B S hS X D₂ hD₂) f
      rw [← h1, ← h2]
      exact PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul f _ _)

/-- The pure tensor of the two canonical sections pairs with a product of local sections of the
two defining ideal sheaves to give that product. -/
theorem tensorHomAt_idealSumEvaluationPresheafPairing_mul (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t₁ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₁)).obj V)
    (t₂ : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D₂)).obj V) :
    unitSectionOf B S hS X
        (tensorHomAt (structureCommRings B S hS X) _ _ _
          (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) V
          (((canonicalSection B S hS X D₁ hD₁).val V ⊗ₜ
              (canonicalSection B S hS X D₂ hD₂).val V) ⊗ₜ
            ((idealMulToSumPresheaf B S hS X D₁ D₂).app V).hom (t₁ ⊗ₜ t₂))) =
      unitSectionOf B S hS X
          (((valPresheafMap (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X D₁).ι).app V).hom t₁) *
        unitSectionOf B S hS X
          (((valPresheafMap (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X D₂).ι).app V).hom t₂) := by
  have hstep : tensorHomAt (structureCommRings B S hS X) _ _ _
        (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) V
        (((canonicalSection B S hS X D₁ hD₁).val V ⊗ₜ
            (canonicalSection B S hS X D₂ hD₂).val V) ⊗ₜ
          ((idealMulToSumPresheaf B S hS X D₁ D₂).app V).hom (t₁ ⊗ₜ t₂)) =
      tensorHomAt (structureCommRings B S hS X) _ _ _
        (tensorEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) V
        (((canonicalSection B S hS X D₁ hD₁).val V ⊗ₜ
          (canonicalSection B S hS X D₂ hD₂).val V) ⊗ₜ (t₁ ⊗ₜ t₂)) := by
    rw [← whiskerLeft_comp_idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂]
    rfl
  have e1 := congrArg (unitSectionOf B S hS X)
    (tensorPairing_canonicalSection_tmul B S hS X D₁ hD₁ V t₁)
  have e2 := congrArg (unitSectionOf B S hS X)
    (tensorPairing_canonicalSection_tmul B S hS X D₂ hD₂ V t₂)
  refine Eq.trans (congrArg (unitSectionOf B S hS X) hstep)
    (Eq.trans (tensorEvaluationPresheafPairing_tmul B S hS X D₁ D₂ hD₁ hD₂ V
      ((canonicalSection B S hS X D₁ hD₁).val V)
      ((canonicalSection B S hS X D₂ hD₂).val V) t₁ t₂) ?_)
  rw [e1, e2]

/-- Pairing a fixed local section of `𝒪_X(D₁) ⊗ 𝒪_X(D₂)` against the local sections of
`𝓘_{D₁+D₂}`, as a linear map on the sections over an étale chart. -/
def idealSumEvaluationAt (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (w : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
      modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)).obj W) :
    (modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj W →ₗ[
      (structureCommRings B S hS X).obj W]
      (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))).obj W :=
  (tensorHomAt (structureCommRings B S hS X) _ _ _
    (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) W).comp
      (TensorProduct.mk _ _ _ w)

/-- The pairing against a fixed local section is the value of the pairing on the pure tensor. -/
theorem idealSumEvaluationAt_apply (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (w : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
      modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)).obj W)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj W) :
    idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ W w t =
      tensorHomAt (structureCommRings B S hS X) _ _ _
        (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) W (w ⊗ₜ t) :=
  rfl

/-- The canonical pure tensor `1_{D₁} ⊗ 1_{D₂}` of local sections over an étale chart. -/
def canonicalTensorAt (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
      modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)).obj W :=
  (canonicalSection B S hS X D₁ hD₁).val W ⊗ₜ (canonicalSection B S hS X D₂ hD₂).val W

include hD₁ hD₂ in
/-- **On an affine chart over the chart on which the sum is formed, `1_{D₁} ⊗ 1_{D₂}` pairs with
a local section of `𝓘_{D₁+D₂}` to give that section.** There the defining ideal of the sum is
the product of the two defining ideals, so such a section is a sum of products of local sections
of `𝓘_{D₁}` and `𝓘_{D₂}`. -/
theorem idealSumEvaluationAt_canonicalTensorAt_of_isAffine
    (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)))
    (mA : A ⟶ sumAtlasChart B S hS X)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj (op A)) :
    unitSectionOf B S hS X
        (idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ (op A)
          (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ (op A)) t) =
      unitSectionOf B S hS X
        (((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι).app (op A)).hom
            t) := by
  have hAff : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  have heq : definingIdealAt B S hS X (sumClosedSubspaces B S hS X D₁ D₂) (op A) =
      definingIdealAt B S hS X D₁ (op A) * definingIdealAt B S hS X D₂ (op A) :=
    definingIdealAt_sumClosedSubspaces_of_isAffine B S hS X D₁ D₂ A mA
  have key : ∀ (r : ToType ((structureRingSheaf B S hS X).obj.obj (op A)))
      (hr : r ∈ definingIdealAt B S hS X D₁ (op A) * definingIdealAt B S hS X D₂ (op A)),
      unitSectionOf B S hS X
          (idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ (op A)
            (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ (op A))
            (⟨r, heq.ge hr⟩ : (modulePresheaf B S hS X
              (idealSheafOfModules B S hS X
                (sumClosedSubspaces B S hS X D₁ D₂))).obj (op A))) = r := by
    intro r hr
    refine Submodule.mul_induction_on'
      (M := definingIdealAt B S hS X D₁ (op A)) (N := definingIdealAt B S hS X D₂ (op A))
      (C := fun r hr =>
        unitSectionOf B S hS X
          (idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ (op A)
            (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ (op A))
            (⟨r, heq.ge hr⟩ : (modulePresheaf B S hS X
              (idealSheafOfModules B S hS X
                (sumClosedSubspaces B S hS X D₁ D₂))).obj (op A))) = r) ?_ ?_ hr
    · intro a ha b hb
      exact tensorHomAt_idealSumEvaluationPresheafPairing_mul B S hS X D₁ D₂ hD₁ hD₂ (op A)
        ⟨a, ha⟩ ⟨b, hb⟩
    · intro y hy z hz ihy ihz
      refine Eq.trans (congrArg (unitSectionOf B S hS X)
        (map_add (idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ (op A)
          (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ (op A)))
          (⟨y, heq.ge hy⟩ : (modulePresheaf B S hS X
            (idealSheafOfModules B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂))).obj (op A))
          (⟨z, heq.ge hz⟩ : (modulePresheaf B S hS X
            (idealSheafOfModules B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂))).obj (op A)))) ?_
      refine Eq.trans (unitSectionOf_add B S hS X _ _) ?_
      exact congrArg₂ (· + ·) ihy ihz
  exact key t.1 (heq.le t.2)

/-- The pure tensor `1_{D₁} ⊗ 1_{D₂}` restricts to the pure tensor over a smaller chart. -/
theorem canonicalTensorAt_restrict {V W : (SmallEtale B S hS X.1)ᵒᵖ} (k : V ⟶ W) :
    (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)).restrictₛₗ k
        (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ V) =
      canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ W := by
  have h1 : (modulePresheaf B S hS X
        (associatedInvertibleSheaf B S hS X D₁ hD₁)).restrictₛₗ k
        ((canonicalSection B S hS X D₁ hD₁).val V) =
      (canonicalSection B S hS X D₁ hD₁).val W :=
    PresheafOfModules.sections_property (canonicalSection B S hS X D₁ hD₁) k
  have h2 : (modulePresheaf B S hS X
        (associatedInvertibleSheaf B S hS X D₂ hD₂)).restrictₛₗ k
        ((canonicalSection B S hS X D₂ hD₂).val V) =
      (canonicalSection B S hS X D₂ hD₂).val W :=
    PresheafOfModules.sections_property (canonicalSection B S hS X D₂ hD₂) k
  have e : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁) ⊗
          modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)).restrictₛₗ k
          (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ V) =
      (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₁ hD₁)).restrictₛₗ k
            ((canonicalSection B S hS X D₁ hD₁).val V) ⊗ₜ
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D₂ hD₂)).restrictₛₗ k
          ((canonicalSection B S hS X D₂ hD₂).val V) :=
    PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul k _ _
  rw [e, h1, h2]
  rfl

include hD₁ hD₂ in
/-- **`1_{D₁} ⊗ 1_{D₂}` pairs with every local section of `𝓘_{D₁+D₂}` to give that section.**
Both sides are sections of `𝒪_X`, so the identity is local, and it holds on the affine charts
over the chart on which the sum is formed. -/
theorem idealSumEvaluationAt_canonicalTensorAt (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V) :
    unitSectionOf B S hS X
        (idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ V
          (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ V) t) =
      unitSectionOf B S hS X
        (((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) := by
  refine structureSection_ext_of_forall_isAffine_hom B S hS X (sumAtlasChart B S hS X)
    (sumAtlasChart_isSurjective B S hS X) V _ _ fun A hA mA k => ?_
  have hL : ((structureRingSheaf B S hS X).obj.map k.op).hom
        (unitSectionOf B S hS X
          (idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ V
            (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ V) t)) =
      unitSectionOf B S hS X
        (idealSumEvaluationAt B S hS X D₁ D₂ hD₁ hD₂ (op A)
          (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ (op A))
          ((modulePresheaf B S hS X (idealSheafOfModules B S hS X
            (sumClosedSubspaces B S hS X D₁ D₂))).restrictₛₗ k.op t)) := by
    rw [← unitSectionOf_restrictₛₗ]
    refine congrArg (unitSectionOf B S hS X) ?_
    rw [idealSumEvaluationAt_apply, idealSumEvaluationAt_apply,
      ← canonicalTensorAt_restrict B S hS X D₁ D₂ hD₁ hD₂ k.op]
    exact (tensorHomAt_restrict (structureCommRings B S hS X) _ _ _
      (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) k.op
      (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ V) t).symm
  have hR : ((structureRingSheaf B S hS X).obj.map k.op).hom
        (unitSectionOf B S hS X
          (((valPresheafMap (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t)) =
      unitSectionOf B S hS X
        (((valPresheafMap (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X
            (sumClosedSubspaces B S hS X D₁ D₂)).ι).app (op A)).hom
          ((modulePresheaf B S hS X (idealSheafOfModules B S hS X
            (sumClosedSubspaces B S hS X D₁ D₂))).restrictₛₗ k.op t)) := by
    rw [← unitSectionOf_restrictₛₗ]
    exact congrArg (unitSectionOf B S hS X)
      (PresheafOfModules.naturality_apply (valPresheafMap (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι) k.op t).symm
  rw [hL, hR]
  exact idealSumEvaluationAt_canonicalTensorAt_of_isAffine B S hS X D₁ D₂ hD₁ hD₂ A hA mA _

end Evaluation

/-! ### The tensor product isomorphism -/

section TensorIso

variable (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (hD₁ : IsEffectiveCartierDivisor B S hS X D₁)
    (hD₂ : IsEffectiveCartierDivisor B S hS X D₂)
    (hD : IsEffectiveCartierDivisor B S hS X (sumClosedSubspaces B S hS X D₁ D₂))

/-- An endomorphism of `𝒪_X`, regarded as a module over itself, is multiplication by the image
of the unit section. -/
theorem unitEndo_app_apply
    (g : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X))
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))).obj V) :
    unitSectionOf B S hS X ((g.val.app V).hom y) =
      unitSectionOf B S hS X y *
        unitSectionOf B S hS X
          (((SheafOfModules.unit (structureRingSheaf B S hS X)).unitHomEquiv g).val V) := by
  conv_lhs =>
    rw [← (SheafOfModules.unit (structureRingSheaf B S hS X)).unitHomEquiv.symm_apply_apply g]
  rfl

/-- A local section of `𝒪_X`, regarded as a module over itself, read as a scalar acting on the
`𝒪_X`-modules. -/
def unitScalarOf {U : (SmallEtale B S hS X.1)ᵒᵖ}
    (z : (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))).obj U) :
    ToType ((Oforget (structureCommRings B S hS X)).obj U) := z

/-- Tensoring a morphism of sheaves of `𝒪_X`-modules on the right by `𝓘_{D₁+D₂}`, at the level
of presheaves of `𝒪_X`-modules. -/
def whiskerSumIdeal
    {N N' : SheafOfModules.{u} (structureRingSheaf B S hS X)} (θ : N ⟶ N') :
    modulePresheaf B S hS X N ⊗
        modulePresheaf B S hS X
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)) ⟶
      modulePresheaf B S hS X N' ⊗
        modulePresheaf B S hS X
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)) :=
  valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property θ ▷
    modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))

/-- Restricting the tensor product of a morphism with `𝓘_{D₁+D₂}` along the unit of
sheafification gives the tensor product of the morphism of underlying presheaves. -/
theorem toSheafify_comp_tensorSheafMapOnSite
    {N N' : SheafOfModules.{u} (structureRingSheaf B S hS X)} (θ : N ⟶ N') :
    toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (modulePresheaf B S hS X N ⊗
            modulePresheaf B S hS X
              (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ≫
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
            (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
            (structureRingSheaf B S hS X).property⟩).map θ).app
            (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)))).val =
      whiskerSumIdeal B S hS X D₁ D₂ θ ≫
        toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (modulePresheaf B S hS X N' ⊗
            modulePresheaf B S hS X
              (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) :=
  ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).unit.naturality
      (whiskerSumIdeal B S hS X D₁ D₂ θ)).symm

/-- A pairing against `𝓘_{D₁+D₂}` restricts along `θ ▷ 𝓘_{D₁+D₂}` to the pairing of `θ ▷ 𝓘_{D₁+D₂}`
followed by it. -/
private theorem whiskerSumIdeal_comp_toSheafify_comp
    {N N' H : SheafOfModules.{u} (structureRingSheaf B S hS X)} (θ : N ⟶ N')
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj N').obj
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ⟶ H)
    (φ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj N).obj
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ⟶ H)
    (h : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).map θ).app
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ≫ ψ = φ) :
    whiskerSumIdeal B S hS X D₁ D₂ θ ≫
        toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (modulePresheaf B S hS X N' ⊗
            modulePresheaf B S hS X
              (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ≫ ψ.val =
      toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (modulePresheaf B S hS X N ⊗
            modulePresheaf B S hS X
              (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ≫ φ.val := by
  subst h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ψ.val) (toSheafify_comp_tensorSheafMapOnSite B S hS X D₁ D₂ θ).symm).trans
      (Category.assoc _ _ _))

include hD₁ hD₂ in
/-- **`1_{D₁} ⊗ 1_{D₂}` pairs with a local section of `𝓘_{D₁+D₂}` to give that section**, for
the evaluation pairing of `AlgebraicGeometry.Space.sumInvertibleEvaluation`. -/
theorem tensorHomAt_sumInvertibleEvaluation_tensorCanonicalSection
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V) :
    tensorHomAt (structureCommRings B S hS X) _ _ _
        (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
              ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
              ((structureRingSheaf B S hS X).property)⟩).obj
              ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
              ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂)) V
        ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val V ⊗ₜ t) =
      ((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t := by
  have h1 : tensorHomAt (structureCommRings B S hS X) _ _ _
        (sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) V
        ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val V ⊗ₜ t) =
      tensorHomAt (structureCommRings B S hS X) _ _ _
        (idealSumEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂) V
        (canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ V ⊗ₜ t) := by
    rw [← whiskerRight_comp_sumInvertibleEvaluationPresheafPairing B S hS X D₁ D₂ hD₁ hD₂]
    rfl
  rw [tensorPairing_sumInvertibleEvaluation, h1]
  exact idealSumEvaluationAt_canonicalTensorAt B S hS X D₁ D₂ hD₁ hD₂ V t

/-- The pairing `(𝒪_X(D₁) ⊗ 𝒪_X(D₂)) ⊗ 𝓘_{D₁+D₂} ⟶ 𝒪_X` attached to a morphism
`θ : 𝒪_X(D₁) ⊗ 𝒪_X(D₂) ⟶ 𝒪_X(D₁+D₂)`: tensor `θ` by `𝓘_{D₁+D₂}` and follow it by the
evaluation pairing of `𝒪_X(D₁+D₂)`. -/
def mapTensorEvaluation
    (θ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂))) ⟶
      associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂)))))).obj
        ((idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)))) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
      (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
      (structureRingSheaf B S hS X).property⟩).map θ).app
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))) ≫
    (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD).hom

include hD₁ hD₂ in
/-- **The duality computation.** A morphism `θ : 𝒪_X(D₁) ⊗ 𝒪_X(D₂) ⟶ 𝒪_X(D₁+D₂)` which, after
tensoring by `𝓘_{D₁+D₂}` and composing with the two evaluation pairings, becomes an
endomorphism `g` of `𝒪_X`, has its values against `𝓘_{D₁+D₂}` computed by `g`. -/
theorem tensorHomAt_tensorPairing_of_map_eq
    (θ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂))) ⟶
      associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
        hD)
    (g : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X))
    (hg : mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD θ =
      (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom ≫ g)
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (modulePresheaf B S hS X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩).obj
          ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
          ((associatedInvertibleSheaf B S hS X D₂ hD₂))))).obj V)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V) :
    tensorHomAt (structureCommRings B S hS X) _ _ _
        (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
          (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD)
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD)) V
        ((θ.val.app V).hom x ⊗ₜ t) =
      (g.val.app V).hom
        (tensorHomAt (structureCommRings B S hS X) _ _ _
          (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
            (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
                ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
                ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
                ((structureRingSheaf B S hS X).property)⟩).obj
                ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
                ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
            (SheafOfModules.unit (structureRingSheaf B S hS X))
            (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂)) V (x ⊗ₜ t)) := by
  have key : whiskerSumIdeal B S hS X D₁ D₂ θ ≫
      tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
        (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD) =
      tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
              ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
              ((structureRingSheaf B S hS X).property)⟩).obj
              ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
              ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂) ≫ g.val := by
    exact (whiskerSumIdeal_comp_toSheafify_comp B S hS X D₁ D₂ θ _ _ hg).trans
      (Category.assoc _ _ _).symm
  exact congrArg (fun z => tensorHomAt (structureCommRings B S hS X) _ _ _ z V (x ⊗ₜ t)) key

/-- **The canonical section pairs by multiplication.** Multiplication by `1_{D₁+D₂}`, read
against `𝓘_{D₁+D₂}` through the evaluation pairing of `𝒪_X(D₁+D₂)`, is the multiplication of
`𝒪_X`: this is the content of Stacks 0847 (1) at the level of sections. -/
theorem tensorHomAt_tensorPairing_canonicalSectionHom
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X))).obj V)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V) :
    unitSectionOf B S hS X
        (tensorHomAt (structureCommRings B S hS X) _ _ _
          (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
            (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
            (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
              hD)
            (SheafOfModules.unit (structureRingSheaf B S hS X))
            (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
              hD)) V
          (((canonicalSectionHom B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD).val.app V).hom y ⊗ₜ t)) =
      unitSectionOf B S hS X y *
        unitSectionOf B S hS X
          (((valPresheafMap (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) := by
  have key : whiskerSumIdeal B S hS X D₁ D₂
        (canonicalSectionHom B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD) ≫
      tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
        (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD) =
      (λ_ (modulePresheaf B S hS X
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)))).hom ≫
        valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι := by
    refine (whiskerSumIdeal_comp_toSheafify_comp B S hS X D₁ D₂ _ _ _
      (map_canonicalSectionHom_comp_evaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
        hD)).trans ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun z => z ≫ valPresheafMap (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι)
      (toSheafify_comp_unitTensorHom B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
  refine Eq.trans (congrArg (fun z => unitSectionOf B S hS X
    (tensorHomAt (structureCommRings B S hS X) _ _ _ z V (y ⊗ₜ t))) key) ?_
  refine Eq.trans (congrArg (unitSectionOf B S hS X)
    (map_smul ((valPresheafMap (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom
      (unitScalarOf B S hS X y) t)) ?_
  rfl

/-- The coefficient of the section of `𝒪_X(D₁+D₂)` corresponding to `s` is the evaluation pairing
of any section `s'` equal to its restriction with `t`. -/
private theorem homSectionCoeff_associatedInvertibleSheafHomEquiv_eq (U : SmallEtale B S hS X.1)
    (s : (modulePresheaf B S hS X
      (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD)).obj (op U))
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (f : V.unop ⟶ U)
    (s' : (modulePresheaf B S hS X
      (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD)).obj V)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V)
    (h : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X
      (sumClosedSubspaces B S hS X D₁ D₂) hD)).restrictₛₗ f.op s = s') :
    homSectionCoeff (structureCommRings B S hS X) _ _ U
        (associatedInvertibleSheafHomEquiv B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD U s) V f t =
      tensorHomAt (structureCommRings B S hS X) _ _ _
        (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
          (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD)
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD)) V (s' ⊗ₜ t) := by
  subst h
  exact associatedInvertibleSheafHomEquiv_apply B S hS X _ hD U s V f t

include hD₁ hD₂ in
/-- **The coefficients of the morphism `θ` on `1_{D₁} ⊗ 1_{D₂}`.** Under the identification of
`𝒪_X(D₁+D₂)` with `SheafHom_{𝒪_X}(𝓘_{D₁+D₂}, 𝒪_X)`, the section `θ(1_{D₁} ⊗ 1_{D₂})`
corresponds to the inclusion `𝓘_{D₁+D₂} ⟶ 𝒪_X` followed by `g`. -/
theorem homSectionCoeff_map_tensorCanonicalSection
    (θ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂))) ⟶
      associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
        hD)
    (g : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X))
    (hg : mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD θ =
      (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom ≫ g)
    (U : SmallEtale B S hS X.1) (V : (SmallEtale B S hS X.1)ᵒᵖ) (f : V.unop ⟶ U)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V) :
    homSectionCoeff (structureCommRings B S hS X) _ _ U
        (associatedInvertibleSheafHomEquiv B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD U
          ((θ.val.app (op U)).hom
            ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val (op U)))) V f t =
      (g.val.app V).hom
        (((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) := by
  have h1 : (modulePresheaf B S hS X
          (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD)).restrictₛₗ f.op
        ((θ.val.app (op U)).hom
          ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val (op U))) =
      (θ.val.app V).hom ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val V) :=
    Eq.trans (PresheafOfModules.naturality_apply θ.val f.op _).symm
      (congrArg (θ.val.app V).hom
        (PresheafOfModules.sections_property
          (tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂) f.op))
  refine (homSectionCoeff_associatedInvertibleSheafHomEquiv_eq B S hS X D₁ D₂ hD U _ V f _ t
    h1).trans ?_
  refine Eq.trans (tensorHomAt_tensorPairing_of_map_eq B S hS X D₁ D₂ hD₁ hD₂ hD θ g hg V _ t) ?_
  exact congrArg (g.val.app V).hom
    (tensorHomAt_sumInvertibleEvaluation_tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂ V t)

include hD in
/-- **An endomorphism of `𝒪_X` which is the identity on `𝓘_{D₁+D₂}` is the identity.**  Composing
with multiplication by `1_{D₁+D₂}` and reading the result through the identification of
`𝒪_X(D₁+D₂)` with `SheafHom_{𝒪_X}(𝓘_{D₁+D₂}, 𝒪_X)` turns the hypothesis into an equality of two
multiples of `1_{D₁+D₂}`; that section is regular by Stacks 0847 (1). -/
theorem eq_id_of_app_ι_eq
    (g : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X))
    (hid : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (t : (modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V),
      (g.val.app V).hom
          (((valPresheafMap (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) =
        ((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) :
    g = 𝟙 (SheafOfModules.unit (structureRingSheaf B S hS X)) := by
  have hcsh : Mono (canonicalSectionHom B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
      hD) :=
    canonicalSection_isRegular B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
      hD
  refine (cancel_mono (canonicalSectionHom B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
    hD)).1 ?_
  refine (SheafOfModules.fullyFaithfulForget (structureRingSheaf B S hS X)).map_injective ?_
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  refine (associatedInvertibleSheafHomEquiv B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
    hD U.unop).injective ?_
  refine homSection_ext (structureCommRings B S hS X) _ _ U.unop _ _ fun V f t => ?_
  have hcoef : ∀ (p : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
        associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD),
      homSectionCoeff (structureCommRings B S hS X) _ _ U.unop
          (associatedInvertibleSheafHomEquiv B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD U.unop
            ((p.val.app U).hom y)) V f t =
        tensorHomAt (structureCommRings B S hS X) _ _ _
          (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
            (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
            (associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
              hD)
            (SheafOfModules.unit (structureRingSheaf B S hS X))
            (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
              hD)) V
          ((p.val.app V).hom
            ((modulePresheaf B S hS X
              (SheafOfModules.unit (structureRingSheaf B S hS X))).restrictₛₗ f.op y) ⊗ₜ t) := by
    intro p
    exact homSectionCoeff_associatedInvertibleSheafHomEquiv_eq B S hS X D₁ D₂ hD U.unop _ V f _ t
      (PresheafOfModules.naturality_apply p.val f.op y).symm
  refine Eq.trans (hcoef _) (Eq.trans ?_ (hcoef _).symm)
  refine Eq.trans (tensorHomAt_tensorPairing_canonicalSectionHom B S hS X D₁ D₂ hD V
      ((g.val.app V).hom ((modulePresheaf B S hS X
        (SheafOfModules.unit (structureRingSheaf B S hS X))).restrictₛₗ f.op y)) t)
    (Eq.trans ?_ (tensorHomAt_tensorPairing_canonicalSectionHom B S hS X D₁ D₂ hD V
      ((modulePresheaf B S hS X
        (SheafOfModules.unit (structureRingSheaf B S hS X))).restrictₛₗ f.op y) t).symm)
  have hu := unitEndo_app_apply B S hS X g V
    ((modulePresheaf B S hS X
      (SheafOfModules.unit (structureRingSheaf B S hS X))).restrictₛₗ f.op y)
  have hut := (unitEndo_app_apply B S hS X g V
      (((valPresheafMap (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X
          (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t)).symm.trans
    (congrArg (unitSectionOf B S hS X) (hid V t))
  rw [hu, mul_assoc, unitSection_mul_comm B S hS X
    (unitSectionOf B S hS X
      (((SheafOfModules.unit (structureRingSheaf B S hS X)).unitHomEquiv g).val V))
    (unitSectionOf B S hS X
      (((valPresheafMap (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X
          (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t)), hut]

include hD in
/-- **The coefficients of the canonical section `1_{D₁+D₂}`.** Under the identification of
`𝒪_X(D₁+D₂)` with `SheafHom_{𝒪_X}(𝓘_{D₁+D₂}, 𝒪_X)` the canonical section corresponds to the
inclusion `𝓘_{D₁+D₂} ⟶ 𝒪_X`. -/
theorem homSectionCoeff_canonicalSection :
    ∀ (U : SmallEtale B S hS X.1) (V : (SmallEtale B S hS X.1)ᵒᵖ) (f : V.unop ⟶ U)
    (t : (modulePresheaf B S hS X
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V),
    homSectionCoeff (structureCommRings B S hS X) _ _ U
        (associatedInvertibleSheafHomEquiv B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD U
          ((canonicalSection B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD).val (op U))) V f t =
      ((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X
          (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t := by
  intro U V f t
  exact (homSectionCoeff_associatedInvertibleSheafHomEquiv_eq B S hS X D₁ D₂ hD U _ V f _ t
    (PresheafOfModules.sections_property _ f.op)).trans
    (tensorPairing_canonicalSection_tmul B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
      hD V t)

include hD₁ hD₂ in
/-- **A morphism carries `1_{D₁} ⊗ 1_{D₂}` to `1_{D₁+D₂}`** as soon as the endomorphism of
`𝒪_X` attached to it by the duality acts as the identity on `𝓘_{D₁+D₂}`. -/
theorem map_tensorCanonicalSection_eq_canonicalSection :
    ∀ (θ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂))) ⟶
    associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
      hD)
    (g : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X)),
    (mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD θ =
      (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom ≫ g) →
    (∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (t : (modulePresheaf B S hS X
        (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V),
      (g.val.app V).hom
          (((valPresheafMap (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) =
        ((valPresheafMap (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X
            (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) →
    ∀ U : (SmallEtale B S hS X.1)ᵒᵖ,
      (θ.val.app U).hom ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val U) =
        (canonicalSection B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD).val U := by
  intro θ g hg hid U
  refine (associatedInvertibleSheafHomEquiv B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
    hD
    U.unop).injective ?_
  refine homSection_ext (structureCommRings B S hS X) _ _ U.unop _ _ fun V f t => ?_
  rw [homSectionCoeff_map_tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂ hD θ g hg U.unop V f t,
    homSectionCoeff_canonicalSection B S hS X D₁ D₂ hD U.unop V f t, hid V t]

include hD₁ hD₂ in
/-- The isomorphism `𝒪_X(D₁) ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁+D₂)` obtained from the two evaluation pairings
by full faithfulness of tensoring by `𝓘_{D₁+D₂}` has the expected image under that functor. -/
theorem map_preimageIso_sumInvertibleEvaluation
    (hfull : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).Full)
    (_hfaith : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).Faithful) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
              ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
              ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).preimageIso
            (X := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
                ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
                ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
                ((structureRingSheaf B S hS X).property)⟩).obj
                ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
                ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
            (Y := associatedInvertibleSheaf B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂) hD)
            (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂ ≪≫
              (associatedInvertibleSheafEvaluation B S hS X
                (sumClosedSubspaces B S hS X D₁ D₂) hD).symm)).hom =
        (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom ≫
          (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD).inv :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
      ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
      ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).map_preimage
      (X := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩).obj
          ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
          ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
      (Y := associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD)
      (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂ ≪≫
        (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD).symm).hom

include hD₁ hD₂ in
/-- The pairing attached to the comparison isomorphism is the evaluation pairing of
`𝒪_X(D₁) ⊗ 𝒪_X(D₂)`. -/
theorem mapTensorEvaluation_preimageIso
    (hfull : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).Full)
    (hfaith : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).Faithful) :
    mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
            ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
            ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).preimageIso
          (X := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
              ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
              ((structureRingSheaf B S hS X).property)⟩).obj
              ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
              ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
          (Y := associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD)
          (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂ ≪≫
            (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
              hD).symm)).hom =
      (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom := by
  have evaluationEquality := congrArg (fun morphism => morphism ≫
    (associatedInvertibleSheafEvaluation B S hS X
      (sumClosedSubspaces B S hS X D₁ D₂) hD).hom)
    (map_preimageIso_sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD hfull hfaith)
  exact evaluationEquality.trans
    ((Category.assoc _ _ _).trans ((congrArg
      (fun morphism => (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom ≫ morphism)
      (Iso.inv_hom_id (associatedInvertibleSheafEvaluation B S hS X
        (sumClosedSubspaces B S hS X D₁ D₂) hD))).trans (Category.comp_id _)))

include hD₁ hD₂ in
/-- **Stacks 0842**, with the effective Cartier-ness of the sum taken as a hypothesis.  For two
effective Cartier divisors `D₁, D₂` on an algebraic space `X` with sum `D = D₁ + D₂` there is a
*unique* isomorphism `𝒪_X(D₁) ⊗_{𝒪_X} 𝒪_X(D₂) ⟶ 𝒪_X(D)` carrying `1_{D₁} ⊗ 1_{D₂}` to
`1_D`. -/
theorem existsUnique_tensorInvertibleSheafIso_of_isEffectiveCartierDivisor :
    ∃! e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂))) ≅
        associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          hD,
      ∀ U : (SmallEtale B S hS X.1)ᵒᵖ,
        (e.hom.val.app U).hom
            ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val U) =
          (canonicalSection B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            hD).val U := by
  have hinv : Stacks.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂)) :=
    hD
  have heq : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
      ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
      ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))
  have hfull : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
      ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
      ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).Full := heq.full
  have hfaith : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
      ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
      ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X
        (sumClosedSubspaces B S hS X D₁ D₂))).Faithful := heq.faithful
  refine ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
      ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
      ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).preimageIso
    (X := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂))))
    (Y := associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂) hD)
    (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂ ≪≫
      (associatedInvertibleSheafEvaluation B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
        hD).symm), ?_, ?_⟩
  · refine map_tensorCanonicalSection_eq_canonicalSection B S hS X D₁ D₂ hD₁ hD₂ hD _
      (𝟙 (SheafOfModules.unit (structureRingSheaf B S hS X))) ?_ fun V t => rfl
    exact Eq.trans
      (mapTensorEvaluation_preimageIso B S hS X D₁ D₂ hD₁ hD₂ hD hfull hfaith)
      (Category.comp_id _).symm
  · intro e' he'
    have hg' : mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD e'.hom =
        (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom ≫
          ((sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).inv ≫
            mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD e'.hom) :=
      Eq.trans (Category.id_comp _).symm
        (Eq.trans (congrArg (fun z => z ≫ mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD e'.hom)
          (Iso.hom_inv_id (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂)).symm)
          (Category.assoc _ _ _))
    have hid : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
        (t : (modulePresheaf B S hS X
          (idealSheafOfModules B S hS X (sumClosedSubspaces B S hS X D₁ D₂))).obj V),
        (((sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).inv ≫
          mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD e'.hom).val.app V).hom
            (((valPresheafMap (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property
              (definingIdealSheaf B S hS X
                (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t) =
          ((valPresheafMap (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property
            (definingIdealSheaf B S hS X
              (sumClosedSubspaces B S hS X D₁ D₂)).ι).app V).hom t := by
      intro V t
      have h := homSectionCoeff_map_tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂ hD e'.hom _ hg'
        V.unop V (𝟙 V.unop) t
      rw [he' (op V.unop),
        homSectionCoeff_canonicalSection B S hS X D₁ D₂ hD V.unop V (𝟙 V.unop) t] at h
      exact h.symm
    have hgid := eq_id_of_app_ι_eq B S hS X D₁ D₂ hD _ hid
    have hcomp : mapTensorEvaluation B S hS X D₁ D₂ hD₁ hD₂ hD e'.hom =
        (sumInvertibleEvaluation B S hS X D₁ D₂ hD₁ hD₂).hom := by
      rw [hg', hgid]
      exact Category.comp_id _
    refine Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).flip.obj
      (idealSheafOfModules B S hS X
        (sumClosedSubspaces B S hS X D₁ D₂))).map_injective ?_)
    refine (Iso.cancel_iso_hom_right _ _ (associatedInvertibleSheafEvaluation B S hS X
      (sumClosedSubspaces B S hS X D₁ D₂) hD)).mp ?_
    exact hcomp.trans
      (mapTensorEvaluation_preimageIso B S hS X D₁ D₂ hD₁ hD₂ hD hfull hfaith).symm

include hD₁ hD₂ in
/-- **Stacks 0842.** For two effective Cartier divisors `D₁, D₂` on an algebraic space `X` with
sum `D = D₁ + D₂` there is a *unique* isomorphism
`𝒪_X(D₁) ⊗_{𝒪_X} 𝒪_X(D₂) ⟶ 𝒪_X(D)` carrying `1_{D₁} ⊗ 1_{D₂}` to `1_D`. -/
@[stacks 0842]
theorem existsUnique_tensorInvertibleSheafIso :
    ∃! e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
        ((associatedInvertibleSheaf B S hS X D₁ hD₁))).obj
        ((associatedInvertibleSheaf B S hS X D₂ hD₂))) ≅
        associatedInvertibleSheaf B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
          (isEffectiveCartierDivisor_sumClosedSubspaces B S hS X D₁ D₂ hD₁ hD₂),
      ∀ U : (SmallEtale B S hS X.1)ᵒᵖ,
        (e.hom.val.app U).hom
            ((tensorCanonicalSection B S hS X D₁ D₂ hD₁ hD₂).val U) =
          (canonicalSection B S hS X (sumClosedSubspaces B S hS X D₁ D₂)
            (isEffectiveCartierDivisor_sumClosedSubspaces B S hS X D₁ D₂ hD₁ hD₂)).val U :=
  existsUnique_tensorInvertibleSheafIso_of_isEffectiveCartierDivisor B S hS X D₁ D₂ hD₁ hD₂
    (isEffectiveCartierDivisor_sumClosedSubspaces B S hS X D₁ D₂ hD₁ hD₂)

end TensorIso

end AlgebraicGeometry.Space

end
