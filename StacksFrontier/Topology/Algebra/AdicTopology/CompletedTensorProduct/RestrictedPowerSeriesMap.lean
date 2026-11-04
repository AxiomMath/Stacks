module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeries

/-!
# The induced map on restricted power series rings

Let `A → B` be a homomorphism of commutative rings and let `I` be an ideal of `A`.  Reducing
coefficients along `A ⧸ Iⁿ → B ⧸ (I · B)ⁿ` at every level gives a ring homomorphism
`A{σ} → B{σ}` between the restricted power series rings for `I` and for its extension.  Under
the identification `B ⊗̂[A] A{σ} ≃+* B{σ}` this homomorphism is the canonical map from the right
factor into the completed tensor product, so it is the base change of `A{σ}` along `A → B`.

## Main definitions

* `TopologicalRing.restrictedPowerSeriesMap`: the induced map `A{σ} → B{σ}`.

## Main results

* `TopologicalRing.restrictedPowerSeriesMap_polynomialRingHom` and
  `TopologicalRing.restrictedPowerSeriesMap_coefficientRingHom`: the induced map is coefficient
  reduction on polynomials and the given map on constants, which pins it down on the image of
  the polynomial ring.
* `TopologicalRing.completedTensorProductRestrictedEquiv_tmul_one`: the induced map is the
  canonical map `A{σ} → B ⊗̂[A] A{σ}` followed by the identification of the completed tensor
  product with `B{σ}`.

## Implementation notes

The induced map is built from the compatible family of coefficient reductions rather than from
the completed tensor product, so that it is available without the tensor product topology and
its uniformity; the comparison with the completed tensor product is then a consequence of the
levelwise description of the identification `B ⊗̂[A] A{σ} ≃+* B{σ}`.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public section

namespace TopologicalRing

section

universe u v

open scoped TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The reductions of the coefficient map are compatible with the transition maps between the
coefficient quotients. -/
public theorem factorPow_comp_coefficientQuotientMap (I : Ideal A) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (I.map (algebraMap A B)) hmn).comp
        (coefficientQuotientMap (B := B) I n) =
      (coefficientQuotientMap (B := B) I m).comp (Ideal.Quotient.factorPow I hmn) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/-- The map `A{σ} → B{σ}` induced by `A → B`, reducing coefficients at every level. -/
public noncomputable def restrictedPowerSeriesMap (I : Ideal A) (σ : Type v) :
    RestrictedPowerSeries I σ →+* RestrictedPowerSeries (I.map (algebraMap A B)) σ where
  toFun x :=
    ⟨fun n => MvPolynomial.map (coefficientQuotientMap (B := B) I n)
        (RestrictedPowerSeries.coefficientProjection I σ n x), by
      intro m n hmn
      change RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
        (MvPolynomial.map (coefficientQuotientMap (B := B) I n)
          (RestrictedPowerSeries.coefficientProjection I σ n x)) = _
      rw [show RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn =
          MvPolynomial.map (Ideal.Quotient.factorPow (I.map (algebraMap A B)) hmn) from rfl,
        MvPolynomial.map_map, factorPow_comp_coefficientQuotientMap I hmn,
        ← MvPolynomial.map_map]
      exact congrArg (MvPolynomial.map (coefficientQuotientMap (B := B) I m)) (x.property hmn)⟩
  map_one' := Subtype.ext (funext fun n =>
    ((MvPolynomial.map (coefficientQuotientMap (B := B) I n)).comp
      (RestrictedPowerSeries.coefficientProjection I σ n)).map_one)
  map_mul' x y := Subtype.ext (funext fun n =>
    ((MvPolynomial.map (coefficientQuotientMap (B := B) I n)).comp
      (RestrictedPowerSeries.coefficientProjection I σ n)).map_mul x y)
  map_zero' := Subtype.ext (funext fun n =>
    ((MvPolynomial.map (coefficientQuotientMap (B := B) I n)).comp
      (RestrictedPowerSeries.coefficientProjection I σ n)).map_zero)
  map_add' x y := Subtype.ext (funext fun n =>
    ((MvPolynomial.map (coefficientQuotientMap (B := B) I n)).comp
      (RestrictedPowerSeries.coefficientProjection I σ n)).map_add x y)

/-- At every level the induced map is coefficientwise reduction of the level `n` coefficient
polynomial. -/
@[simp]
public theorem coefficientProjection_restrictedPowerSeriesMap (I : Ideal A) (σ : Type v)
    (n : ℕ) (x : RestrictedPowerSeries I σ) :
    RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n
        (restrictedPowerSeriesMap I σ x) =
      MvPolynomial.map (coefficientQuotientMap (B := B) I n)
        (RestrictedPowerSeries.coefficientProjection I σ n x) := rfl

/-- On a polynomial the induced map is coefficientwise extension of scalars. -/
@[simp]
public theorem restrictedPowerSeriesMap_polynomialRingHom (I : Ideal A) (σ : Type v)
    (p : MvPolynomial σ A) :
    restrictedPowerSeriesMap (B := B) I σ (RestrictedPowerSeries.polynomialRingHom I σ p) =
      RestrictedPowerSeries.polynomialRingHom (I.map (algebraMap A B)) σ
        (MvPolynomial.map (algebraMap A B) p) := by
  refine Subtype.ext (funext fun n => ?_)
  show MvPolynomial.map (coefficientQuotientMap (B := B) I n)
      (RestrictedPowerSeries.coefficientProjection I σ n
        (RestrictedPowerSeries.polynomialRingHom I σ p)) =
    RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n
      (RestrictedPowerSeries.polynomialRingHom (I.map (algebraMap A B)) σ
        (MvPolynomial.map (algebraMap A B) p))
  rw [RestrictedPowerSeries.coefficientProjection_polynomialRingHom,
    RestrictedPowerSeries.coefficientProjection_polynomialRingHom,
    MvPolynomial.map_map, MvPolynomial.map_map]
  rfl

/-- On a constant the induced map is the given map of coefficient rings. -/
@[simp]
public theorem restrictedPowerSeriesMap_coefficientRingHom (I : Ideal A) (σ : Type v) (a : A) :
    restrictedPowerSeriesMap (B := B) I σ (RestrictedPowerSeries.coefficientRingHom I σ a) =
      RestrictedPowerSeries.coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B a) := by
  refine Subtype.ext (funext fun n => ?_)
  show MvPolynomial.map (coefficientQuotientMap (B := B) I n)
      (RestrictedPowerSeries.coefficientProjection I σ n
        (algebraMap A (RestrictedPowerSeries I σ) a)) =
    RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A B)) σ n
      (algebraMap B (RestrictedPowerSeries (I.map (algebraMap A B)) σ) (algebraMap A B a))
  rw [RestrictedPowerSeries.coefficientProjection_algebraMap,
    RestrictedPowerSeries.coefficientProjection_algebraMap, MvPolynomial.map_C]
  rfl

section Topology

variable [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- **The induced map `A{σ} → B{σ}` is the base change of `A{σ}` along `A → B`.**  The
identification `B ⊗̂[A] A{σ} ≃+* B{σ}` carries the image of `1 ⊗ f` to the coefficientwise
reduction of `f`. -/
public theorem completedTensorProductRestrictedEquiv_tmul_one (I : Ideal A) (hI : I.FG)
    (σ : Type v) [IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ)]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (f : RestrictedPowerSeries I σ) :
    letI : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    letI : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
      tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
    completedTensorProductRestrictedEquiv I hI σ hJ
        (UniformSpace.Completion.coeRingHom ((1 : B) ⊗ₜ[A] f)) =
      restrictedPowerSeriesMap I σ f := by
  let _ : TopologicalSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductTopology (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let _ : UniformSpace (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProductUniformSpace (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  let _ : IsTopologicalRing (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isTopologicalRing (R := A) (A := B) (B := RestrictedPowerSeries I σ)
  let _ : IsUniformAddGroup (B ⊗[A] RestrictedPowerSeries I σ) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := RestrictedPowerSeries I σ)
  refine Subtype.ext (funext fun n => ?_)
  have h := coefficientProjection_completedTensorProductRestrictedEquiv I hI σ hJ n
    ((1 : B) ⊗ₜ[A] f)
  rwa [restrictedTensorProjection_tmul, map_one, one_mul] at h

end Topology

end

end TopologicalRing

end
