module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeExt

/-!
# A scalar acting by zero on the completed cotangent complex after base change

Let `(A₁, I₁) → (A₂, I₂)` be as in Stacks Remark 0AL5 with `A₁` and `A₂` Noetherian — a map of
Noetherian adic pairs carrying a positive power of `I₁` into `I₂` — let `B₁` be adically of
finite type over `(A₁, I₁)` and let `B₂` be its completed base change `(B₁ ⊗_{A₁} A₂)^∧_{I₂}`.
If multiplication by `f₁ ∈ B₁` on `NL^∧_{B₁/A₁}` is zero in `D(B₁)`, then multiplication by the
image `f₂ ∈ B₂` on `NL^∧_{B₂/A₂}` is zero in `D(B₂)`.

## Main results

* `Rig.smul_id_of_completedBaseChange`: the statement for any realization of the completed base
  change, the identification of `B₂` with `(B₁ ⊗_{A₁} A₂)^∧_{I₂}` taken as data.
* `Rig.smul_id_of_completedBaseChangeFunctor`: the statement for a `Rig.CompletedBaseChange`
  functor.

## Implementation notes

The hypotheses `hc` and `hmap` are the condition of Remark 0AL5 that a positive power of `I₁`
lands in `I₂`. They are not recoverable from a `Rig.CompletedBaseChange` alone.

## References

* [Stacks Project, Tag 0AK2](https://stacks.math.columbia.edu/tag/0AK2)
* [Stacks Project, Tag 0GAG](https://stacks.math.columbia.edu/tag/0GAG)
* [Stacks Project, Tag 0GAE](https://stacks.math.columbia.edu/tag/0GAE)
* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
* [The Stacks Project, Lemma 15.85.9 (0G9I)](https://stacks.math.columbia.edu/tag/0G9I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Rig

universe u₁ u₂ v w

open AdicFiniteTypeAlgebra CompletedPolynomialPresentation CompletedNaiveCotangentComplex

attribute [local instance] HasDerivedCategory.standard

section BaseChange

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂} {c : ℕ}
  {B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁} {B₂ : AdicFiniteTypeAlgebra.{u₂, w} A₂ I₂}
  [Algebra B₁.carrier B₂.carrier] [Algebra A₁ B₂.carrier]
  [IsScalarTower A₁ A₂ B₂.carrier] [IsScalarTower A₁ B₁.carrier B₂.carrier]

/-- Let `(A₁, I₁) → (A₂, I₂)` be as in Stacks Remark 0AL5, a map of Noetherian pairs carrying a
positive power of `I₁` into `I₂`, let `B₁` be adically of finite type over `(A₁, I₁)`, and let
`B₂` be identified by `e` with its completed base change `(B₁ ⊗_{A₁} A₂)^∧_{I₂}`. If `f₁ ∈ B₁`
acts by zero on `NL^∧_{B₁/A₁}` in `D(B₁)`, then its image in `B₂` acts by zero on
`NL^∧_{B₂/A₂}` in `D(B₂)`. -/
public theorem smul_id_of_completedBaseChange (hc : 0 < c)
    (hmap : (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂)
    (e : B₂.carrier ≃+* completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
    (heA : ∀ a : A₂, e (algebraMap A₂ B₂.carrier a) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedRight A₂ B₁ a))
    (heB : ∀ b : B₁.carrier, e (algebraMap B₁.carrier B₂.carrier b) =
      algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
        (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) (baseChangedLeft A₂ B₁ b))
    (P₁ : CompletedPolynomialPresentation I₁ B₁)
    (P₂ : CompletedPolynomialPresentation I₂ B₂) (f₁ : B₁.carrier)
    (h : f₁ • 𝟙 (derivedCompletedNaiveCotangentComplex B₁ P₁) = 0) :
    algebraMap B₁.carrier B₂.carrier f₁ •
      𝟙 (derivedCompletedNaiveCotangentComplex B₂ P₂) = 0 := by
  have hI₁ : I₁.FG := Ideal.fg_of_isNoetherianRing I₁
  have hI₂ : I₂.FG := Ideal.fg_of_isNoetherianRing I₂
  have hspan := le_span_range_sup_adicIdeal_of_completedBaseChange hI₂ e heA heB
  obtain ⟨r, g, hgen⟩ := exists_generating_family B₁
  have hsurj := completedAeval_surjective B₁ r g hI₁ hgen
  have hker : (baseChangePresentation (B₁ := B₁) hI₂ hc hmap hspan r g hgen).extension.ker ≤
      Ideal.map (baseChangeExtensionHom hI₁ hI₂ hc hmap hspan r g hgen).toRingHom
        (ofGenerators B₁ r g hI₁ hgen).extension.ker := by
    rw [ker_extension_baseChangePresentation hI₂ hc hmap hspan r g hgen,
      ker_extension_ofGenerators hI₁ r g hgen]
    exact ker_le_map_ker_of_completedBaseChange hI₂ hmap r g hsurj e heA heB
  exact smul_id_baseChange_presentation_of_ker_le hI₁ hI₂ hc hmap hspan r g hgen hker P₂ f₁
    (smul_id_congr_presentation B₁ P₁ (ofGenerators B₁ r g hI₁ hgen) f₁ h)

end BaseChange

section Functor

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂} {c : ℕ}

/-- With `(A₁, I₁) → (A₂, I₂)` as in Stacks Remark 0AL5, witnessed by `hc` and `hmap`, a scalar
`f₁ ∈ B₁` acting by zero on `NL^∧_{B₁/A₁}` in `D(B₁)` has its image
`Rig.CompletedBaseChange.scalar` in the base change `B₂ = C.functor.obj B₁` acting by zero on
`NL^∧_{B₂/A₂}` in `D(B₂)`, for any completed polynomial presentations of the two algebras. -/
@[stacks 0AK2]
public theorem smul_id_of_completedBaseChangeFunctor
    (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
    (hc : 0 < c) (hmap : (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂)
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
    (P₁ : CompletedPolynomialPresentation I₁ B₁)
    (P₂ : CompletedPolynomialPresentation I₂ (C.functor.obj B₁)) (f₁ : B₁.carrier)
    (h : f₁ • 𝟙 (derivedCompletedNaiveCotangentComplex B₁ P₁) = 0) :
    C.scalar B₁ f₁ •
      𝟙 (derivedCompletedNaiveCotangentComplex (C.functor.obj B₁) P₂) = 0 := by
  let instB : Algebra B₁.carrier (C.functor.obj B₁).carrier :=
    ((C.completedTensorProductEquiv B₁).symm.toRingHom.comp
      ((algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)).comp
        (baseChangedLeft A₂ B₁).toRingHom)).toAlgebra
  have halg : (algebraMap B₁.carrier (C.functor.obj B₁).carrier) =
      (C.completedTensorProductEquiv B₁).symm.toRingHom.comp
        ((algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
            (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)).comp
          (baseChangedLeft A₂ B₁).toRingHom) :=
    RingHom.algebraMap_toAlgebra _
  have hof : ∀ t : baseChangedAlgebra (A₂ := A₂) B₁,
      AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁)
          (baseChangedAlgebra (A₂ := A₂) B₁) t =
        algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁) t := fun t ↦ by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
  have halgb : ∀ b : B₁.carrier,
      algebraMap B₁.carrier (C.functor.obj B₁).carrier b =
        (C.completedTensorProductEquiv B₁).symm
          (algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
            (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
            (baseChangedLeft A₂ B₁ b)) := fun b ↦ by
    rw [halg]
    rfl
  have hscalar : ∀ b : B₁.carrier,
      algebraMap B₁.carrier (C.functor.obj B₁).carrier b = C.scalar B₁ b := fun b ↦ by
    rw [halgb b, ← hof]
  have heB : ∀ b : B₁.carrier,
      C.completedTensorProductEquiv B₁
          (algebraMap B₁.carrier (C.functor.obj B₁).carrier b) =
        algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
          (baseChangedLeft A₂ B₁ b) := fun b ↦ by
    rw [halgb b, RingEquiv.apply_symm_apply]
  have heA : ∀ a : A₂,
      C.completedTensorProductEquiv B₁
          (algebraMap A₂ (C.functor.obj B₁).carrier a) =
        algebraMap (baseChangedAlgebra (A₂ := A₂) B₁)
          (completedBaseChangedAlgebra (A₂ := A₂) (I₂ := I₂) B₁)
          (baseChangedRight A₂ B₁ a) := fun a ↦ by
    rw [C.algebraMap_completedTensorProductEquiv B₁ a, hof]
  let instA : Algebra A₁ (C.functor.obj B₁).carrier :=
    ((algebraMap A₂ (C.functor.obj B₁).carrier).comp (algebraMap A₁ A₂)).toAlgebra
  have hA₁ : (algebraMap A₁ (C.functor.obj B₁).carrier) =
      (algebraMap A₂ (C.functor.obj B₁).carrier).comp (algebraMap A₁ A₂) :=
    RingHom.algebraMap_toAlgebra _
  have towerA : IsScalarTower A₁ A₂ (C.functor.obj B₁).carrier :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by rw [hA₁]; rfl
  have towerB : IsScalarTower A₁ B₁.carrier (C.functor.obj B₁).carrier := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    have hleft : baseChangedLeft A₂ B₁ (algebraMap A₁ B₁.carrier x) =
        baseChangedRight A₂ B₁ (algebraMap A₁ A₂ x) := by
      simp only [baseChangedLeft, baseChangedRight, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one (R := A₁) (A := B₁.carrier),
        Algebra.algebraMap_eq_smul_one (R := A₁) (A := A₂), TensorProduct.smul_tmul]
    refine (C.completedTensorProductEquiv B₁).injective ?_
    rw [heB (algebraMap A₁ B₁.carrier x), hleft, ← heA (algebraMap A₁ A₂ x), hA₁]
    rfl
  rw [← hscalar f₁]
  exact smul_id_of_completedBaseChange hc hmap (C.completedTensorProductEquiv B₁)
    heA heB P₁ P₂ f₁ h

end Functor

end Rig

end
