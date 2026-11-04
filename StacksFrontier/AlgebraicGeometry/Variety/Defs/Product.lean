module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# Products of varieties

Over an algebraically closed field the fibre product of two varieties is again a variety, and its
dimension is the sum of the dimensions of the two factors. Over a field that is not algebraically
closed the first assertion fails: the spectrum of the Gaussian rational field is a variety over
`ℚ`, but its self-product over `Spec ℚ` is reducible, hence not a variety; in fact it is the
disjoint union of two copies of the original spectrum.

## Main definitions

* `AlgebraicGeometry.GaussianRationals`: the field `ℚ(i)` inside `ℂ`.
* `AlgebraicGeometry.gaussianRationalsToRat`: its structure morphism over `ℚ`.

## Main results

* `AlgebraicGeometry.isVariety_pullback`: over an algebraically closed field, a product of
  varieties is a variety.
* `AlgebraicGeometry.topologicalKrullDim_pullback_of_isVariety`: the dimension of a product of
  varieties is the sum of the dimensions of the factors.
* `AlgebraicGeometry.isVariety_and_topologicalKrullDim_pullback`: over an algebraically closed
  field, both assertions at once.
* `AlgebraicGeometry.gaussianRationals_isVariety`: each factor is a variety.
* `AlgebraicGeometry.gaussianRationals_product_reducible`: their product is reducible.
* `AlgebraicGeometry.gaussianRationals_product_not_isVariety`: their product is not a variety.
* `AlgebraicGeometry.gaussianRationals_product_iso_coprod`: its decomposition into two copies.

## Implementation notes

A variety over `k` carries its structure morphism to `Spec k`, and its product is the categorical
pullback of the two structure morphisms, with structure morphism the first projection followed by
the structure morphism of the first factor.

The dimension is the topological Krull dimension of the underlying space, valued in `WithBot ℕ∞`.
The dimension formula is read off from the general product formula for schemes locally of finite
type over a field, which a variety is; so, unlike the assertion that the product is a variety, it
is stated over an arbitrary field, algebraic closedness of the ground field playing no part in it.
The source fixes an algebraically closed ground field and asserts both at once, which is what
`isVariety_and_topologicalKrullDim_pullback` states; its first conjunct is the product-variety
result it cites.

In the counterexample the two factors are the same spectrum. Reducibility there is witnessed by
the idempotent decomposition of `ℚ(i) ⊗_ℚ ℚ(i)`, whose two factors are cut out by the evaluation
map and its conjugate. Reducibility, failure to be a variety, and the disjoint-union isomorphism
are stated separately.

## References

* [Stacks Project, Tag 020G](https://stacks.math.columbia.edu/tag/020G)
* [Stacks Project, Tag 05P3](https://stacks.math.columbia.edu/tag/05P3)
* [Stacks Project, Tag 0AZM](https://stacks.math.columbia.edu/tag/0AZM)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05P3.** The fibre product of two varieties over an
algebraically closed field is a variety. -/
@[stacks 05P3]
public instance isVariety_pullback (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsVariety k f] [IsVariety k g] :
    IsVariety k (pullback.fst f g ≫ f) := by
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  have : GeometricallyReduced f := geometricallyReduced_of_isReduced f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  constructor

/-- Let `X` and `Y` be varieties over a field `k`. The dimension of the product
`X ×_{Spec k} Y` is the sum of the dimensions of `X` and of `Y`. -/
public theorem topologicalKrullDim_pullback_of_isVariety (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsVariety k f] [IsVariety k g] :
    topologicalKrullDim ↑(pullback f g) = topologicalKrullDim X + topologicalKrullDim Y :=
  topologicalKrullDim_pullback k f g

/-- **Stacks Project, Tag 0AZM.** Let `X` and `Y` be varieties over an algebraically closed
field `k`. Then the product `X ×_{Spec k} Y` is a variety and its dimension is the sum of the
dimensions of `X` and of `Y`. -/
@[stacks 0AZM "the whole lemma, both of its conclusions: for `X` and `Y` varieties over an \
algebraically closed field `k` — the source's own hypothesis, and one the first conclusion \
needs, since over a field that is not algebraically closed a product of two varieties can be \
reducible (`AlgebraicGeometry.gaussianRationals_product_not_isVariety` below) — the product \
`X ×_{Spec k} Y`, with structure morphism the first projection followed by the structure \
morphism of `X`, is again a variety, AND its dimension is `dim X + dim Y`. A variety is \
`AlgebraicGeometry.IsVariety`: integral, separated, locally of finite type and quasi-compact \
over the field, so the first conclusion carries the integrality and separatedness of the \
product. Dimensions are `topologicalKrullDim`, valued in `WithBot ℕ∞`, and the formula is an \
equation there. The first conclusion is also Stacks 05P3, \
`AlgebraicGeometry.isVariety_pullback`; the second holds over an arbitrary field, \
`AlgebraicGeometry.topologicalKrullDim_pullback_of_isVariety`."]
public theorem isVariety_and_topologicalKrullDim_pullback (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsVariety k f] [IsVariety k g] :
    IsVariety k (pullback.fst f g ≫ f) ∧
      topologicalKrullDim ↑(pullback f g) = topologicalKrullDim X + topologicalKrullDim Y :=
  ⟨isVariety_pullback k f g, topologicalKrullDim_pullback_of_isVariety k f g⟩

private theorem gaussianImaginaryUnit_isIntegral : _root_.IsIntegral ℚ Complex.I := by
  show ∃ p : Polynomial ℚ, p.Monic ∧
    Polynomial.eval₂ (algebraMap ℚ ℂ) Complex.I p = 0
  refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · norm_num [Polynomial.Monic]
  · simp [Complex.I_sq]

/-- The Gaussian rational field `ℚ(i)`, realized inside `ℂ`. -/
public abbrev GaussianRationals : Type := IntermediateField.adjoin ℚ {Complex.I}

private noncomputable def gaussianComplexConjugation : ℂ →ₐ[ℚ] ℂ :=
  AlgEquiv.restrictScalars ℚ Complex.conjAe

private noncomputable def gaussianConjugation :
    GaussianRationals ≃ₐ[ℚ] GaussianRationals := by
  let c := gaussianComplexConjugation
  have hc : c Complex.I = -Complex.I := Complex.conj_I
  have hmap :
      IntermediateField.map c (IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ)) =
        IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ) := by
    have key (s : ℂ) : IntermediateField.adjoin ℚ ({-s} : Set ℂ) ≤
        IntermediateField.adjoin ℚ ({s} : Set ℂ) := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact IntermediateField.neg_mem _ (IntermediateField.subset_adjoin ℚ {s} (by simp))
    rw [IntermediateField.adjoin_map, Set.image_singleton, hc]
    exact le_antisymm (key _) (by simpa using key (-Complex.I))
  exact (IntermediateField.equivMap
      (IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ)) c).trans
    (IntermediateField.equivOfEq hmap)

private def gaussianImaginaryUnit : GaussianRationals :=
  ⟨Complex.I, IntermediateField.subset_adjoin ℚ ({Complex.I} : Set ℂ) (by simp)⟩

private theorem gaussianRationals_inv_two_add_inv_two :
    (2⁻¹ : GaussianRationals) + 2⁻¹ = 1 := by
  norm_num

private theorem gaussianConjugation_apply_gaussianImaginaryUnit :
    (gaussianConjugation gaussianImaginaryUnit).val = -Complex.I := by
  show gaussianComplexConjugation Complex.I = -Complex.I
  exact Complex.conj_I

private theorem gaussianConjugation_apply_gaussianImaginaryUnit' :
    gaussianConjugation gaussianImaginaryUnit = -gaussianImaginaryUnit := by
  apply Subtype.ext
  simpa [gaussianImaginaryUnit] using gaussianConjugation_apply_gaussianImaginaryUnit

private noncomputable def gaussianEvaluation :
    (GaussianRationals ⊗[ℚ] GaussianRationals) →ₐ[ℚ] GaussianRationals :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ GaussianRationals)
    (AlgHom.id ℚ GaussianRationals) (fun _ _ => Commute.all _ _)

private noncomputable def gaussianConjugateEvaluation :
    (GaussianRationals ⊗[ℚ] GaussianRationals) →ₐ[ℚ] GaussianRationals :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ GaussianRationals)
    gaussianConjugation.toAlgHom (fun _ _ => Commute.all _ _)

private theorem gaussianImaginaryUnit_mul_self :
    gaussianImaginaryUnit * gaussianImaginaryUnit = -1 := by
  apply Subtype.ext
  simp [gaussianImaginaryUnit]

private theorem orthogonal_idempotents_of_mul_self_eq_one {B : Type*} [CommRing B] {z c : B}
    (hz : z * z = 1) (hc : c + c = 1) :
    (1 - z) * c * ((1 - z) * c) = (1 - z) * c ∧ (1 + z) * c * ((1 + z) * c) = (1 + z) * c ∧
      (1 - z) * c * ((1 + z) * c) = 0 ∧ (1 - z) * c + (1 + z) * c = 1 ∧
      (1 - z) * c - (1 + z) * c = -z :=
  ⟨by linear_combination c ^ 2 * hz + (1 - z) * c * hc,
    by linear_combination c ^ 2 * hz + (1 + z) * c * hc, by linear_combination -c ^ 2 * hz,
    by linear_combination hc, by linear_combination -z * hc⟩

private noncomputable def algHomProdOfIdempotents {R A B : Type*} [CommSemiring R] [Semiring A]
    [CommRing B] [Algebra R A] [Algebra R B] (L : A →ₐ[R] B) (e₀ e₁ : B) (h₀ : e₀ * e₀ = e₀)
    (h₁ : e₁ * e₁ = e₁) (h₀₁ : e₀ * e₁ = 0) (hsum : e₀ + e₁ = 1) : A × A →ₐ[R] B where
  toFun a := L a.1 * e₀ + L a.2 * e₁
  map_zero' := by simp
  map_one' := by simp [hsum]
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    linear_combination -(L a.1 * L b.1) * h₀ - L a.2 * L b.2 * h₁ -
      (L a.1 * L b.2 + L a.2 * L b.1) * h₀₁
  commutes' r := by
    simp only [Prod.algebraMap_apply, AlgHom.commutes]
    rw [← mul_add, hsum, mul_one]

private noncomputable def gaussianTensorEvaluation :
    GaussianRationals ⊗[ℚ] GaussianRationals →ₐ[ℚ] GaussianRationals × GaussianRationals :=
  gaussianEvaluation.prod gaussianConjugateEvaluation

private theorem gaussianTensorEvaluation_tmul (a b : GaussianRationals) :
    gaussianTensorEvaluation (a ⊗ₜ b) = (a * b, a * gaussianConjugation b) := by
  simp [gaussianTensorEvaluation, gaussianEvaluation, gaussianConjugateEvaluation]

private noncomputable def gaussianIdempotent₀ : GaussianRationals ⊗[ℚ] GaussianRationals :=
  (1 - gaussianImaginaryUnit ⊗ₜ gaussianImaginaryUnit) * ((2⁻¹ : GaussianRationals) ⊗ₜ 1)

private noncomputable def gaussianIdempotent₁ : GaussianRationals ⊗[ℚ] GaussianRationals :=
  (1 + gaussianImaginaryUnit ⊗ₜ gaussianImaginaryUnit) * ((2⁻¹ : GaussianRationals) ⊗ₜ 1)

private theorem gaussianIdempotents :
    gaussianIdempotent₀ * gaussianIdempotent₀ = gaussianIdempotent₀ ∧
      gaussianIdempotent₁ * gaussianIdempotent₁ = gaussianIdempotent₁ ∧
      gaussianIdempotent₀ * gaussianIdempotent₁ = 0 ∧
      gaussianIdempotent₀ + gaussianIdempotent₁ = 1 ∧
      gaussianIdempotent₀ - gaussianIdempotent₁ =
        -(gaussianImaginaryUnit ⊗ₜ gaussianImaginaryUnit) :=
  orthogonal_idempotents_of_mul_self_eq_one
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, gaussianImaginaryUnit_mul_self,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg, Algebra.TensorProduct.one_def])
    (by rw [← TensorProduct.add_tmul, gaussianRationals_inv_two_add_inv_two,
      Algebra.TensorProduct.one_def])

private theorem gaussianTensorEvaluation_idempotent₀ :
    gaussianTensorEvaluation gaussianIdempotent₀ = (1, 0) := by
  rw [gaussianIdempotent₀, map_mul, map_sub, map_one, gaussianTensorEvaluation_tmul,
    gaussianTensorEvaluation_tmul, gaussianConjugation_apply_gaussianImaginaryUnit']
  ext <;> norm_num [gaussianImaginaryUnit_mul_self]

private theorem gaussianTensorEvaluation_idempotent₁ :
    gaussianTensorEvaluation gaussianIdempotent₁ = (0, 1) := by
  rw [gaussianIdempotent₁, map_mul, map_add, map_one, gaussianTensorEvaluation_tmul,
    gaussianTensorEvaluation_tmul, gaussianConjugation_apply_gaussianImaginaryUnit']
  ext <;> norm_num [gaussianImaginaryUnit_mul_self]

private noncomputable def gaussianTensorSection :
    GaussianRationals × GaussianRationals →ₐ[ℚ] GaussianRationals ⊗[ℚ] GaussianRationals :=
  algHomProdOfIdempotents (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ))
    gaussianIdempotent₀ gaussianIdempotent₁ gaussianIdempotents.1 gaussianIdempotents.2.1
    gaussianIdempotents.2.2.1 gaussianIdempotents.2.2.2.1

private theorem gaussianTensorEvaluation_comp_section :
    gaussianTensorEvaluation.comp gaussianTensorSection = AlgHom.id ℚ _ := by
  refine AlgHom.ext fun p => ?_
  show gaussianTensorEvaluation (p.1 ⊗ₜ 1 * gaussianIdempotent₀ +
    p.2 ⊗ₜ 1 * gaussianIdempotent₁) = p
  rw [map_add, map_mul, map_mul, gaussianTensorEvaluation_tmul, gaussianTensorEvaluation_tmul,
    gaussianTensorEvaluation_idempotent₀, gaussianTensorEvaluation_idempotent₁]
  ext <;> simp

private theorem gaussianTensorSection_comp_evaluation :
    gaussianTensorSection.comp gaussianTensorEvaluation = AlgHom.id ℚ _ := by
  apply Algebra.TensorProduct.ext
  · ext a
    show gaussianTensorSection (gaussianTensorEvaluation (a ⊗ₜ 1)) = a ⊗ₜ 1
    simp only [gaussianTensorEvaluation_tmul, map_one, mul_one]
    show a ⊗ₜ 1 * gaussianIdempotent₀ + a ⊗ₜ 1 * gaussianIdempotent₁ = _
    rw [← mul_add, gaussianIdempotents.2.2.2.1, mul_one]
  · apply IntermediateField.adjoin_algHom_ext (F := ℚ) (s := ({Complex.I} : Set ℂ))
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    show gaussianTensorSection (gaussianTensorEvaluation (1 ⊗ₜ gaussianImaginaryUnit)) =
      1 ⊗ₜ gaussianImaginaryUnit
    simp only [gaussianTensorEvaluation_tmul, one_mul,
      gaussianConjugation_apply_gaussianImaginaryUnit']
    show gaussianImaginaryUnit ⊗ₜ 1 * gaussianIdempotent₀ +
      (-gaussianImaginaryUnit) ⊗ₜ 1 * gaussianIdempotent₁ = _
    rw [TensorProduct.neg_tmul, neg_mul, ← sub_eq_add_neg, ← mul_sub, gaussianIdempotents.2.2.2.2,
      mul_neg, Algebra.TensorProduct.tmul_mul_tmul, gaussianImaginaryUnit_mul_self, one_mul,
      TensorProduct.neg_tmul, neg_neg]

/-- The canonical structure morphism `Spec ℚ(i) ⟶ Spec ℚ`. -/
public noncomputable abbrev gaussianRationalsToRat :
    Spec (.of GaussianRationals) ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ GaussianRationals))

/-- `Spec ℚ(i)` is a variety over `ℚ`. -/
@[stacks 020G "each factor is a variety"]
public theorem gaussianRationals_isVariety :
    IsVariety ℚ gaussianRationalsToRat := by
  have : FiniteDimensional ℚ GaussianRationals :=
    IntermediateField.adjoin.finiteDimensional gaussianImaginaryUnit_isIntegral
  have : Algebra.FiniteType ℚ GaussianRationals := Module.Finite.finiteType _
  have : LocallyOfFiniteType gaussianRationalsToRat := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    simpa [RingHom.finiteType_algebraMap]
  exact IsVariety.mk

/-- The product `Spec ℚ(i) ×_{Spec ℚ} Spec ℚ(i)` is reducible. -/
@[stacks 020G "the product is reducible"]
public theorem gaussianRationals_product_reducible :
    ¬ IrreducibleSpace
      (pullback gaussianRationalsToRat gaussianRationalsToRat : Scheme) := by
  intro hpullback
  let T := GaussianRationals ⊗[ℚ] GaussianRationals
  have : IrreducibleSpace (PrimeSpectrum T) :=
    (pullbackSpecIso ℚ GaussianRationals GaussianRationals).hom.homeomorph.irreducibleSpace_iff.mp
      hpullback
  have hne (f : T →ₐ[ℚ] GaussianRationals) (e : T) (he : f e = 1) :
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum T)).Nonempty := by
    have hmem : e ∉ (PrimeSpectrum.comap f.toRingHom ⊥).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal]
      show f e ≠ 0
      simp [he]
    exact ⟨PrimeSpectrum.comap f.toRingHom ⊥, hmem⟩
  obtain ⟨p, hp₀, hp₁⟩ := nonempty_preirreducible_inter (X := PrimeSpectrum T)
    PrimeSpectrum.isOpen_basicOpen PrimeSpectrum.isOpen_basicOpen
    (hne gaussianEvaluation _ (congrArg Prod.fst gaussianTensorEvaluation_idempotent₀))
    (hne gaussianConjugateEvaluation _ (congrArg Prod.snd gaussianTensorEvaluation_idempotent₁))
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp₀ hp₁
  have hmem : gaussianIdempotent₀ * gaussianIdempotent₁ ∈ p.asIdeal := by
    rw [gaussianIdempotents.2.2.1]
    exact zero_mem _
  exact (p.isPrime.mem_or_mem hmem).elim hp₀ hp₁

private noncomputable def gaussianTensorProductEquiv :
    (GaussianRationals ⊗[ℚ] GaussianRationals) ≃ₐ[ℚ]
      GaussianRationals × GaussianRationals :=
  AlgEquiv.ofAlgHom gaussianTensorEvaluation gaussianTensorSection
    gaussianTensorEvaluation_comp_section gaussianTensorSection_comp_evaluation

/-- The product of these two varieties is not a variety. -/
@[stacks 020G "the product is not a variety"]
public theorem gaussianRationals_product_not_isVariety :
    ¬ IsVariety ℚ
      (pullback.fst gaussianRationalsToRat gaussianRationalsToRat ≫
        gaussianRationalsToRat) := fun h => gaussianRationals_product_reducible
  ((AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced _).mp h.toIsIntegral).1

/-- The product is isomorphic to two disjoint copies of `Spec ℚ(i)`. -/
@[stacks 020G "the product is two copies of the factor"]
public theorem gaussianRationals_product_iso_coprod :
    Nonempty ((pullback gaussianRationalsToRat gaussianRationalsToRat) ≅
      (Spec (.of GaussianRationals) ⨿ Spec (.of GaussianRationals))) := by
  let e := gaussianTensorProductEquiv
  let pull := pullbackSpecIso ℚ GaussianRationals GaussianRationals
  let ringIso : Spec (.of (GaussianRationals ⊗[ℚ] GaussianRationals)) ≅
      Spec (.of (GaussianRationals × GaussianRationals)) :=
    Functor.mapIso Scheme.Spec e.symm.toCommRingCatIso.op
  let sumIso : (Spec (.of GaussianRationals) ⨿ Spec (.of GaussianRationals)) ≅
      Spec (.of (GaussianRationals × GaussianRationals)) :=
    asIso (coprodSpec GaussianRationals GaussianRationals)
  exact ⟨pull ≪≫ ringIso ≪≫ sumIso.symm⟩

end AlgebraicGeometry

end
