module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra
public import StacksFrontier.RingTheory.Kaehler.Basic

/-!
# Differentials of the standard affine chart of projective space

Grade `R[T₀, …, Tₙ]` by total degree and let `B = R[T]_{(Tᵢ)}` be the degree-zero homogeneous
localization at the variable `Tᵢ`, the coordinate ring of the standard chart `D₊(Tᵢ)` of
`Proj R[T] = P^n_R`. The chart is affine `n`-space over `R` on the affine coordinates
`T_j / T_i`, `j ≠ i`, so the module of Kähler differentials `Ω[B⁄R]` is free on their
differentials; the same basis survives any further localization of `B`, in particular the
localization at a prime.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPolyChart.chartAlgebra`: the chart ring as an algebra over the
  polynomial ring on the affine coordinates, along the chart comparison.
* `Stacks.AlgebraicGeometry.ProjPolyChart.kaehlerBasis`: the basis of `Ω[B⁄R]` consisting of the
  differentials `d(T_j / T_i)`, `j ≠ i`.
* `Stacks.AlgebraicGeometry.ProjPolyChart.localizationKaehlerBasis`: the corresponding basis of
  `Ω[Bₘ⁄R]` for `Bₘ` a localization of the chart ring.
* `Stacks.AlgebraicGeometry.ProjPolyChart.atPrimeKaehlerBasis`: the localization at a prime.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolyChart.free_kaehlerDifferential` and
  `Stacks.AlgebraicGeometry.ProjPolyChart.free_kaehlerDifferential_localization`: the modules of
  differentials of the chart ring and of any localization of it are free.
* `Stacks.AlgebraicGeometry.ProjPolyChart.span_range_D_chartCoord` and
  `Stacks.AlgebraicGeometry.ProjPolyChart.span_range_D_chartCoord_localization`: over any base
  through which the coefficient inclusion factors, not just over `R`, the differentials of the
  affine coordinates still generate.

## Implementation notes

The basis is transported from `KaehlerDifferential.mvPolynomialBasis` along the chart comparison
`R[Y_j : j ≠ i] ≃+* B` by `Module.Basis.ofIsLocalizedModule`, viewing a bijective ring map as the
localization at the trivial submonoid (`isLocalization_chart`).

`HomogeneousLocalization.instSMul` is deprioritised locally, so that the `R`-action on `B` found
by instance search is the one `Algebra.toSMul` reads off `HomogeneousLocalization.instAlgebra`;
the two agree definitionally but are different terms, and the scalar-tower hypotheses of
`KaehlerDifferential.map` are stated with the latter.

## References

* [Stacks Project, Tag 00RT](https://stacks.math.columbia.edu/tag/00RT)
* [Stacks Project, Tag 00RX](https://stacks.math.columbia.edu/tag/00RX)
* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.ProjPolyChart

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra SMulCommClass.of_commMonoid
attribute [local instance 0] HomogeneousLocalization.instSMul

variable (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))

/-- The structure map of the chart ring as an `R`-algebra is the coefficient inclusion
`R → R[T]_{(Tᵢ)}`. -/
public theorem algebraMap_eq_coeffToAway :
    algebraMap R (Away (polyGrading R n) (MvPolynomial.X i)) = coeffToAway R n i := rfl

/-- The chart ring as an algebra over the polynomial ring on the affine coordinates, along the
chart comparison `Y_j ↦ T_j / T_i`. -/
@[instance_reducible] public def chartAlgebra :
    Algebra (MvPolynomial {j : Fin (n + 1) // j ≠ i} R)
      (Away (polyGrading R n) (MvPolynomial.X i)) :=
  (chartHom R n i).toAlgebra

attribute [local instance] chartAlgebra

/-- The structure map of that algebra is the chart comparison. -/
public theorem algebraMap_chartAlgebra :
    algebraMap (MvPolynomial {j : Fin (n + 1) // j ≠ i} R)
      (Away (polyGrading R n) (MvPolynomial.X i)) = chartHom R n i := rfl

/-- `R → R[Y_j : j ≠ i] → R[T]_{(Tᵢ)}` is a tower of algebras. -/
public theorem isScalarTower_chart :
    IsScalarTower R (MvPolynomial {j : Fin (n + 1) // j ≠ i} R)
      (Away (polyGrading R n) (MvPolynomial.X i)) :=
  IsScalarTower.of_algebraMap_eq fun r => (chartHom_C R n i r).symm

attribute [local instance] isScalarTower_chart

/-- The chart ring is the localization of the polynomial ring on the affine coordinates at the
trivial submonoid. -/
public theorem isLocalization_chart :
    IsLocalization (⊥ : Submonoid (MvPolynomial {j : Fin (n + 1) // j ≠ i} R))
      (Away (polyGrading R n) (MvPolynomial.X i)) :=
  IsLocalization.of_le_isUnit_of_bijective
    (by
      rintro x ⟨y, hy, rfl⟩
      obtain rfl := Submonoid.mem_bot.mp hy
      simp)
    ⟨chartHom_injective R n i, chartHom_surjective R n i⟩

attribute [local instance] isLocalization_chart

/-- The basis of `Ω[R[T]_{(Tᵢ)}⁄R]` given by the differentials `d(T_j / T_i)`, `j ≠ i`, of the
affine coordinates of the standard chart. -/
public def kaehlerBasis :
    Module.Basis {j : Fin (n + 1) // j ≠ i} (Away (polyGrading R n) (MvPolynomial.X i))
      (Ω[Away (polyGrading R n) (MvPolynomial.X i)⁄R]) :=
  (KaehlerDifferential.mvPolynomialBasis R {j : Fin (n + 1) // j ≠ i}).ofIsLocalizedModule
    (Away (polyGrading R n) (MvPolynomial.X i)) ⊥
    (KaehlerDifferential.map R R (MvPolynomial {j : Fin (n + 1) // j ≠ i} R)
      (Away (polyGrading R n) (MvPolynomial.X i)))

/-- The basis element at `j` is the differential of the affine coordinate `T_j / T_i`. -/
@[simp] public theorem kaehlerBasis_apply (j : {j : Fin (n + 1) // j ≠ i}) :
    kaehlerBasis R n i j =
      KaehlerDifferential.D R (Away (polyGrading R n) (MvPolynomial.X i))
        (chartCoord R n i j) := by
  have h : kaehlerBasis R n i j =
      KaehlerDifferential.map R R (MvPolynomial {j : Fin (n + 1) // j ≠ i} R)
        (Away (polyGrading R n) (MvPolynomial.X i))
        (KaehlerDifferential.mvPolynomialBasis R {j : Fin (n + 1) // j ≠ i} j) :=
    Module.Basis.ofIsLocalizedModule_apply _ _ _ _ j
  rw [h, KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D,
    algebraMap_chartAlgebra, chartHom_X]

/-- The module of differentials of a chart ring is a free module over that ring. -/
public theorem free_kaehlerDifferential :
    Module.Free (Away (polyGrading R n) (MvPolynomial.X i))
      (Ω[Away (polyGrading R n) (MvPolynomial.X i)⁄R]) :=
  .of_basis (kaehlerBasis R n i)

/-- For `Bₘ` a localization of the chart ring, the basis of `Ω[Bₘ⁄R]` given by the differentials
of the images of the affine coordinates `T_j / T_i`, `j ≠ i`. -/
public def localizationKaehlerBasis
    (W : Submonoid (Away (polyGrading R n) (MvPolynomial.X i))) (Bₘ : Type v) [CommRing Bₘ]
    [Algebra (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ] [IsLocalization W Bₘ]
    [Algebra R Bₘ] [IsScalarTower R (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ] :
    Module.Basis {j : Fin (n + 1) // j ≠ i} Bₘ (Ω[Bₘ⁄R]) :=
  (kaehlerBasis R n i).ofIsLocalizedModule Bₘ W
    (KaehlerDifferential.map R R (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ)

/-- The basis element at `j` is the differential of the image of the affine coordinate
`T_j / T_i`. -/
@[simp] public theorem localizationKaehlerBasis_apply
    (W : Submonoid (Away (polyGrading R n) (MvPolynomial.X i))) (Bₘ : Type v) [CommRing Bₘ]
    [Algebra (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ] [IsLocalization W Bₘ]
    [Algebra R Bₘ] [IsScalarTower R (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ]
    (j : {j : Fin (n + 1) // j ≠ i}) :
    localizationKaehlerBasis R n i W Bₘ j =
      KaehlerDifferential.D R Bₘ
        (algebraMap (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ (chartCoord R n i j)) := by
  have h : localizationKaehlerBasis R n i W Bₘ j =
      KaehlerDifferential.map R R (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ
        (kaehlerBasis R n i j) :=
    Module.Basis.ofIsLocalizedModule_apply _ _ _ _ j
  rw [h, kaehlerBasis_apply, KaehlerDifferential.map_D]

/-- The module of differentials of a localization of a chart ring is a free module over that
localization. -/
public theorem free_kaehlerDifferential_localization
    (W : Submonoid (Away (polyGrading R n) (MvPolynomial.X i))) (Bₘ : Type v) [CommRing Bₘ]
    [Algebra (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ] [IsLocalization W Bₘ]
    [Algebra R Bₘ] [IsScalarTower R (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ] :
    Module.Free Bₘ (Ω[Bₘ⁄R]) :=
  .of_basis (localizationKaehlerBasis R n i W Bₘ)

/-- If the values of a function agree with a basis, then its range spans the module. -/
private theorem span_range_eq_top_of_basis_apply {ι A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (b : Module.Basis ι A M) {f : ι → M} (h : ∀ j, b j = f j) :
    Submodule.span A (Set.range f) = ⊤ := by
  rw [← funext h]
  exact b.span_eq

/-- For a base `R'` through which the coefficient inclusion of the chart ring factors,
`Ω[R[T]_{(Tᵢ)}⁄R']` is generated by the differentials `d(T_j / T_i)`, `j ≠ i`. -/
public theorem span_range_D_chartCoord (R' : Type v) [CommRing R'] [Algebra R R']
    [Algebra R' (Away (polyGrading R n) (MvPolynomial.X i))]
    [IsScalarTower R R' (Away (polyGrading R n) (MvPolynomial.X i))] :
    Submodule.span (Away (polyGrading R n) (MvPolynomial.X i))
        (Set.range fun j : {j : Fin (n + 1) // j ≠ i} =>
          KaehlerDifferential.D R' (Away (polyGrading R n) (MvPolynomial.X i))
            (chartCoord R n i j)) = ⊤ :=
  KaehlerDifferential.span_range_D_of_base R R'
    (Away (polyGrading R n) (MvPolynomial.X i)) (chartCoord R n i) <|
      span_range_eq_top_of_basis_apply (kaehlerBasis R n i) (kaehlerBasis_apply R n i)

/-- For `Bₘ` a localization of the chart ring and a base `R'` through which `R → Bₘ` factors,
`Ω[Bₘ⁄R']` is generated by the differentials of the images of `T_j / T_i`, `j ≠ i`. -/
public theorem span_range_D_chartCoord_localization
    (W : Submonoid (Away (polyGrading R n) (MvPolynomial.X i))) (Bₘ : Type v) [CommRing Bₘ]
    [Algebra (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ] [IsLocalization W Bₘ]
    [Algebra R Bₘ] [IsScalarTower R (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ]
    (R' : Type v) [CommRing R'] [Algebra R R'] [Algebra R' Bₘ] [IsScalarTower R R' Bₘ] :
    Submodule.span Bₘ
        (Set.range fun j : {j : Fin (n + 1) // j ≠ i} =>
          KaehlerDifferential.D R' Bₘ
            (algebraMap (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ
              (chartCoord R n i j))) = ⊤ :=
  KaehlerDifferential.span_range_D_of_base R R' Bₘ
    (fun j => algebraMap (Away (polyGrading R n) (MvPolynomial.X i)) Bₘ (chartCoord R n i j)) <|
      span_range_eq_top_of_basis_apply (localizationKaehlerBasis R n i W Bₘ)
        (localizationKaehlerBasis_apply R n i W Bₘ)

/-- For a prime `p` of the chart ring, the basis of `Ω[B_p⁄R]` given by the differentials of the
images of the affine coordinates `T_j / T_i`, `j ≠ i`. -/
public def atPrimeKaehlerBasis (p : Ideal (Away (polyGrading R n) (MvPolynomial.X i)))
    [p.IsPrime] :
    Module.Basis {j : Fin (n + 1) // j ≠ i} (Localization.AtPrime p)
      (Ω[Localization.AtPrime p⁄R]) :=
  localizationKaehlerBasis R n i p.primeCompl (Localization.AtPrime p)

/-- The basis element at `j` is the differential of the image of the affine coordinate
`T_j / T_i`. -/
@[simp] public theorem atPrimeKaehlerBasis_apply
    (p : Ideal (Away (polyGrading R n) (MvPolynomial.X i))) [p.IsPrime]
    (j : {j : Fin (n + 1) // j ≠ i}) :
    atPrimeKaehlerBasis R n i p j =
      KaehlerDifferential.D R (Localization.AtPrime p)
        (algebraMap (Away (polyGrading R n) (MvPolynomial.X i)) (Localization.AtPrime p)
          (chartCoord R n i j)) :=
  localizationKaehlerBasis_apply R n i p.primeCompl (Localization.AtPrime p) j

end Stacks.AlgebraicGeometry.ProjPolyChart

end
