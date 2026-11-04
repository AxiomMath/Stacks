module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Differentials on an affine chart of the blowup of affine space in a coordinate subspace

Let `R` be a commutative ring, let `σ` and `τ` be index types, and write
`A = R[x_k, y_j : k ∈ σ, j ∈ τ]` for `MvPolynomial (σ ⊕ τ) R`, the coordinate ring of
`𝐀^σ × 𝐀^τ` over `R`. Blowing up the coordinate subspace `y = 0` and passing to the chart where
the `i`-th ratio coordinate is invertible replaces `y_j` by `y_i t_j` for `j ≠ i`, and leaves
`y_i` and the `x_k` alone. The chart is again an affine space with coordinates
`x_k`, `y_i` and the ratios `t_j`, so its coordinate ring is another copy of `A`, and the chart
morphism is the `R`-algebra endomorphism `blowupChartHom` of `A` sending

* `X (.inl k) ↦ X (.inl k)`,
* `X (.inr i) ↦ X (.inr i)`,
* `X (.inr j) ↦ X (.inr i) * X (.inr j)` for `j ≠ i`.

On the chart the differential of the ratio coordinate `t_j = y_j / y_i` has a simple pole along
the exceptional divisor `y_i = 0`:
`d t_j = (d y_j - t_j * d y_i) / y_i`. This file records that computation, which appears in the
proof of [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G), in the form of
an explicit `A`-linear map

`blowupChartDifferentialRetraction : Ω[A⁄R] →ₗ[A] A ⊗[A] Ω[A⁄R]`

inverting `KaehlerDifferential.mapBaseChange R A A` up to the factor `y_i`, where the second copy
of `A` is an algebra over the first through `blowupChartHom`. On the differentials of the
coordinates it is given by `d x_k ↦ y_i ⊗ d x_k`, `d y_i ↦ y_i ⊗ d y_i`, and
`d t_j ↦ 1 ⊗ d y_j - t_j ⊗ d y_i`; the first two are divisible by `y_i` and the third is not,
which is exactly the simple pole.

## Main definitions

* `Stacks.Kaehler.blowupChartHom`: the chart morphism, as an `R`-algebra endomorphism of
  `MvPolynomial (σ ⊕ τ) R`.
* `Stacks.Kaehler.blowupChartAlgebra`: the algebra structure on `MvPolynomial (σ ⊕ τ) R` over
  itself given by `blowupChartHom`, together with `Stacks.Kaehler.blowupChartModule`,
  `Stacks.Kaehler.blowupChartTensor` and `Stacks.Kaehler.blowupChartTensorModule`, which pin down
  the module structures on `A` and on `A ⊗[A] Ω[A⁄R]` that it induces.
* `Stacks.Kaehler.blowupChartMapBaseChange`: `KaehlerDifferential.mapBaseChange R A A` for that
  algebra structure.
* `Stacks.Kaehler.blowupChartBaseChangeBasis`: the basis `1 ⊗ d x_v` of `A ⊗[A] Ω[A⁄R]`.
* `Stacks.Kaehler.blowupChartRetractionValue` and
  `Stacks.Kaehler.blowupChartDifferentialRetraction`: the values of the retraction on the
  differentials of the coordinates, and the retraction itself.

## Main results

* `Stacks.Kaehler.blowupChartDifferentialRetraction_D_X_inl`,
  `Stacks.Kaehler.blowupChartDifferentialRetraction_D_X_inr_self` and
  `Stacks.Kaehler.blowupChartDifferentialRetraction_D_X_inr_of_ne`: the retraction in the form
  displayed in Tag 0G5G, `d x_k ↦ y_i ⊗ d x_k`, `d y_i ↦ y_i ⊗ d y_i` and
  `d t_j ↦ 1 ⊗ d y_j - t_j ⊗ d y_i` — the first two divisible by `y_i`, the third not.
* `Stacks.Kaehler.mapBaseChange_comp_retraction` and
  `Stacks.Kaehler.retraction_comp_mapBaseChange`: the retraction is a two-sided inverse of
  `KaehlerDifferential.mapBaseChange R A A` up to the factor `y_i`.

## Implementation notes

Source and target of the chart morphism are the *same* type, so the two `A`-module structures on
`A` that the statement needs — the one along `blowupChartHom`, used for the left factor of
`A ⊗[A] Ω[A⁄R]`, and the tautological one, which is the module structure of the chart over itself
and makes `mapBaseChange` `A`-linear — cannot both be found by instance search. They are therefore
supplied explicitly: `blowupChartAlgebra` and `blowupChartModule` are not instances but
`@[instance_reducible]` definitions, in the idiom of
`Stacks.Smooth.algebraAppLE`, and appear as `letI`s in the statements below;
`blowupChartTensor` names the tensor product formed with the first of the two, and
`blowupChartTensorModule` the `TensorProduct.leftModule` structure on it formed with the second,
which is the one `KaehlerDifferential.mapBaseChange` is linear for.

For the same reason every tensor below is written `a ⊗ₜ ω` rather than `a • (1 ⊗ₜ ω)`: both
`A`-actions on `A ⊗[A] Ω[A⁄R]` are inhabited, and for a bare `•` instance search picks the one
through `blowupChartHom` (`TensorProduct.instSMul`) rather than the chart's own. The two forms
agree by `TensorProduct.tmul_eq_smul_one_tmul` once the action is fixed, so writing the tensor
out leaves no room for the ambiguity. In the statement of
`Stacks.Kaehler.retraction_comp_mapBaseChange` the factor `y_i` does appear as a `•`, and there
the action that instance search picks is again the one through `blowupChartHom`; that is harmless,
because `blowupChartHom` fixes `X (.inr i)`, so acting by `X (.inr i)` through `blowupChartHom` and
acting by it through the chart's own multiplication are the same additive map — they agree on the
tensors `a ⊗ₜ ω`, which generate.

No `IsScalarTower R A A` declaration is needed: with `blowupChartAlgebra` supplied explicitly the
scalar tower required by `KaehlerDifferential.mapBaseChange` is found by instance search, since
`A` acts on itself through an `R`-algebra map.

The retraction is built with `Module.Basis.constr` from
`KaehlerDifferential.mvPolynomialBasis R (σ ⊕ τ)`, and both composition identities are checked on
a basis — on `d x_v` for the one, on `1 ⊗ d x_v` for the other. Beyond the formulas themselves the
only input is the Leibniz rule for `d (y_i t_j)`.

A `DecidableEq τ` hypothesis is needed to single out the index `i` among the `y`-coordinates; it
is not used for anything else.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public section

suppress_compilation

open scoped TensorProduct
open KaehlerDifferential MvPolynomial

namespace Stacks.Kaehler

variable (R : Type*) [CommRing R] (σ τ : Type*) [DecidableEq τ] (i : τ)

/-! ### The chart morphism -/

/-- The chart morphism of the blowup of `𝐀^σ × 𝐀^τ` along the coordinate subspace `y = 0`, on the
chart where the `i`-th ratio coordinate is invertible: the `R`-algebra endomorphism of
`MvPolynomial (σ ⊕ τ) R` fixing the variables `X (.inl k)` and `X (.inr i)` and sending
`X (.inr j)` to `X (.inr i) * X (.inr j)` for `j ≠ i`. -/
def blowupChartHom : MvPolynomial (σ ⊕ τ) R →ₐ[R] MvPolynomial (σ ⊕ τ) R :=
  aeval (Sum.elim (fun k ↦ X (Sum.inl k))
    fun j ↦ if j = i then X (Sum.inr i) else X (Sum.inr i) * X (Sum.inr j))

/-- The chart morphism fixes the coordinates of the ambient factor `𝐀^σ`. -/
@[simp]
theorem blowupChartHom_X_inl (k : σ) :
    blowupChartHom R σ τ i (X (Sum.inl k)) = X (Sum.inl k) := by
  simp [blowupChartHom]

/-- The chart morphism fixes the equation `y_i` of the exceptional divisor. -/
@[simp]
theorem blowupChartHom_X_inr_self :
    blowupChartHom R σ τ i (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [blowupChartHom]

/-- The chart morphism sends `y_j` to `y_i t_j` for `j ≠ i`. -/
@[simp]
theorem blowupChartHom_X_inr_of_ne {j : τ} (hj : j ≠ i) :
    blowupChartHom R σ τ i (X (Sum.inr j)) = X (Sum.inr i) * X (Sum.inr j) := by
  simp [blowupChartHom, hj]

/-! ### The algebra and module structures along the chart morphism -/

/-- `MvPolynomial (σ ⊕ τ) R` as an algebra over itself through `blowupChartHom`: the chart of the
blowup as an algebra over the ambient affine space. This is not an instance, since the index `i`
cannot be recovered from the types; it is used through `letI`. -/
@[instance_reducible]
def blowupChartAlgebra : Algebra (MvPolynomial (σ ⊕ τ) R) (MvPolynomial (σ ⊕ τ) R) :=
  (blowupChartHom R σ τ i).toRingHom.toAlgebra

/-- The structure map of `blowupChartAlgebra` is `blowupChartHom`. -/
@[simp]
theorem algebraMap_blowupChartAlgebra (f : MvPolynomial (σ ⊕ τ) R) :
    @algebraMap (MvPolynomial (σ ⊕ τ) R) (MvPolynomial (σ ⊕ τ) R) _ _
      (blowupChartAlgebra R σ τ i) f = blowupChartHom R σ τ i f :=
  rfl

/-- The module structure on the chart over the ambient affine space underlying
`blowupChartAlgebra`, that is, `a • b = blowupChartHom a * b`. -/
@[instance_reducible]
def blowupChartModule : Module (MvPolynomial (σ ⊕ τ) R) (MvPolynomial (σ ⊕ τ) R) :=
  @Algebra.toModule _ _ _ _ (blowupChartAlgebra R σ τ i)

/-- The base change `A ⊗[A] Ω[A⁄R]` of the differentials of the ambient affine space to the
chart, the left factor carrying the module structure `blowupChartModule`. -/
@[reducible]
def blowupChartTensor : Type _ :=
  @TensorProduct (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial (σ ⊕ τ) R)
    Ω[MvPolynomial (σ ⊕ τ) R⁄R] _ _ (blowupChartModule R σ τ i) _

/-- The module structure of the chart on `A ⊗[A] Ω[A⁄R]`, acting on the left factor by
multiplication. This is the structure `KaehlerDifferential.mapBaseChange R A A` is linear for. -/
@[instance_reducible]
def blowupChartTensorModule :
    Module (MvPolynomial (σ ⊕ τ) R) (blowupChartTensor R σ τ i) :=
  @TensorProduct.leftModule (MvPolynomial (σ ⊕ τ) R) (MvPolynomial (σ ⊕ τ) R) _ _
    (MvPolynomial (σ ⊕ τ) R) Ω[MvPolynomial (σ ⊕ τ) R⁄R] _ _ _ (blowupChartModule R σ τ i) _
    (letI := blowupChartAlgebra R σ τ i; inferInstance)

/-- The canonical map `A ⊗[A] Ω[A⁄R] →ₗ[A] Ω[A⁄R]` on the chart, namely
`KaehlerDifferential.mapBaseChange R A A` for the algebra structure `blowupChartAlgebra`. -/
abbrev blowupChartMapBaseChange :=
  @mapBaseChange R _ (MvPolynomial (σ ⊕ τ) R) (MvPolynomial (σ ⊕ τ) R) _ _ _
    (blowupChartAlgebra R σ τ i) _ _

/-- The basis of `A ⊗[A] Ω[A⁄R]` over the chart obtained by base change from
`KaehlerDifferential.mvPolynomialBasis R (σ ⊕ τ)`. -/
def blowupChartBaseChangeBasis :
    letI := blowupChartTensorModule R σ τ i
    Module.Basis (σ ⊕ τ) (MvPolynomial (σ ⊕ τ) R) (blowupChartTensor R σ τ i) :=
  @Module.Basis.baseChange _ _ _ _ _ _ (MvPolynomial (σ ⊕ τ) R) _ (blowupChartAlgebra R σ τ i)
    (mvPolynomialBasis R (σ ⊕ τ))

/-- The `v`-th vector of `blowupChartBaseChangeBasis` is `1 ⊗ d x_v`. -/
@[simp]
theorem blowupChartBaseChangeBasis_apply (v : σ ⊕ τ) :
    letI := blowupChartModule R σ τ i
    blowupChartBaseChangeBasis R σ τ i v =
      (1 : MvPolynomial (σ ⊕ τ) R) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X v) := by
  simp only [blowupChartBaseChangeBasis, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]

/-! ### The retraction -/

/-- The value of `blowupChartDifferentialRetraction` on the differential of the `v`-th coordinate:
`y_i ⊗ d x_k` on the ambient coordinates, `y_i ⊗ d y_i` on the equation of the exceptional
divisor, and `1 ⊗ d y_j - t_j ⊗ d y_i` on the `j`-th ratio coordinate. -/
def blowupChartRetractionValue (v : σ ⊕ τ) : blowupChartTensor R σ τ i :=
  letI := blowupChartModule R σ τ i
  match v with
  | .inl k => X (Sum.inr i) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inl k))
  | .inr j =>
    if j = i then X (Sum.inr i) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i))
    else (1 : MvPolynomial (σ ⊕ τ) R) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr j)) -
      X (Sum.inr j) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i))

/-- On the ambient coordinate `x_k`, `blowupChartRetractionValue` is `y_i ⊗ d x_k`. -/
@[simp]
theorem blowupChartRetractionValue_inl (k : σ) :
    letI := blowupChartModule R σ τ i
    blowupChartRetractionValue R σ τ i (Sum.inl k) =
      X (Sum.inr i) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inl k)) :=
  rfl

/-- On the coordinate `y_i`, `blowupChartRetractionValue` is `y_i ⊗ d y_i`. -/
@[simp]
theorem blowupChartRetractionValue_inr_self :
    letI := blowupChartModule R σ τ i
    blowupChartRetractionValue R σ τ i (Sum.inr i) =
      X (Sum.inr i) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i)) := by
  simp [blowupChartRetractionValue]

/-- On the `j`-th ratio coordinate with `j ≠ i`, `blowupChartRetractionValue` is
`1 ⊗ d y_j - t_j ⊗ d y_i`. -/
@[simp]
theorem blowupChartRetractionValue_inr_of_ne {j : τ} (hj : j ≠ i) :
    letI := blowupChartModule R σ τ i
    blowupChartRetractionValue R σ τ i (Sum.inr j) =
      (1 : MvPolynomial (σ ⊕ τ) R) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr j)) -
        X (Sum.inr j) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i)) := by
  simp [blowupChartRetractionValue, hj]

/-- The retraction of `KaehlerDifferential.mapBaseChange R A A` on the chart: the `A`-linear map
`Ω[A⁄R] →ₗ[A] A ⊗[A] Ω[A⁄R]` taking the value `blowupChartRetractionValue` on the basis
`KaehlerDifferential.mvPolynomialBasis R (σ ⊕ τ)`. -/
def blowupChartDifferentialRetraction :
    letI := blowupChartTensorModule R σ τ i
    Ω[MvPolynomial (σ ⊕ τ) R⁄R] →ₗ[MvPolynomial (σ ⊕ τ) R] blowupChartTensor R σ τ i :=
  letI := blowupChartTensorModule R σ τ i
  (mvPolynomialBasis R (σ ⊕ τ)).constr (MvPolynomial (σ ⊕ τ) R)
    (blowupChartRetractionValue R σ τ i)

/-- The retraction takes the prescribed value on the differential of each coordinate. -/
@[simp]
theorem blowupChartDifferentialRetraction_apply_D_X (v : σ ⊕ τ) :
    letI := blowupChartTensorModule R σ τ i
    blowupChartDifferentialRetraction R σ τ i (D R (MvPolynomial (σ ⊕ τ) R) (X v)) =
      blowupChartRetractionValue R σ τ i v := by
  let := blowupChartTensorModule R σ τ i
  conv_lhs => rw [← mvPolynomialBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

/-! ### The retraction on the basis of differentials, and the two composition identities -/

/-- On the differential of an ambient coordinate the retraction is divisible by the equation `y_i`
of the exceptional divisor: `d x_k ↦ y_i ⊗ d x_k`, that is, `y_i` times `1 ⊗ d x_k`. -/
theorem blowupChartDifferentialRetraction_D_X_inl (k : σ) :
    letI := blowupChartModule R σ τ i
    letI := blowupChartTensorModule R σ τ i
    blowupChartDifferentialRetraction R σ τ i (D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inl k))) =
      X (Sum.inr i) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inl k)) := by
  rw [blowupChartDifferentialRetraction_apply_D_X, blowupChartRetractionValue_inl]

/-- On the differential of the equation of the exceptional divisor the retraction is divisible by
that equation: `d y_i ↦ y_i ⊗ d y_i`, that is, `y_i` times `1 ⊗ d y_i`. -/
theorem blowupChartDifferentialRetraction_D_X_inr_self :
    letI := blowupChartModule R σ τ i
    letI := blowupChartTensorModule R σ τ i
    blowupChartDifferentialRetraction R σ τ i (D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i))) =
      X (Sum.inr i) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i)) := by
  rw [blowupChartDifferentialRetraction_apply_D_X, blowupChartRetractionValue_inr_self]

/-- **The simple pole of `d t_j` along the exceptional divisor.** On the differential of a ratio
coordinate the retraction is *not* divisible by the equation `y_i` of the exceptional divisor:
`d t_j ↦ 1 ⊗ d y_j - t_j ⊗ d y_i`, whose two terms are `1` and `t_j` times the basis vectors
`1 ⊗ d y_j` and `1 ⊗ d y_i`. Together with `Stacks.Kaehler.mapBaseChange_comp_retraction` this is
the displayed identity `d t_j = (d y_j - t_j d y_i) / y_i` of [Stacks Project, Tag 0G5G]. -/
theorem blowupChartDifferentialRetraction_D_X_inr_of_ne {j : τ} (hj : j ≠ i) :
    letI := blowupChartModule R σ τ i
    letI := blowupChartTensorModule R σ τ i
    blowupChartDifferentialRetraction R σ τ i (D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr j))) =
      (1 : MvPolynomial (σ ⊕ τ) R) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr j)) -
        X (Sum.inr j) ⊗ₜ D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i)) := by
  rw [blowupChartDifferentialRetraction_apply_D_X,
    blowupChartRetractionValue_inr_of_ne _ _ _ _ hj]

/-- The retraction is a right inverse of `KaehlerDifferential.mapBaseChange R A A` up to the
equation `y_i` of the exceptional divisor. -/
theorem mapBaseChange_comp_retraction :
    blowupChartMapBaseChange R σ τ i ∘ₗ blowupChartDifferentialRetraction R σ τ i =
      (X (Sum.inr i) : MvPolynomial (σ ⊕ τ) R) • LinearMap.id := by
  refine (mvPolynomialBasis R (σ ⊕ τ)).ext fun v ↦ ?_
  rw [LinearMap.comp_apply, mvPolynomialBasis_apply,
    blowupChartDifferentialRetraction_apply_D_X]
  obtain k | j := v
  · simp [mapBaseChange_tmul, map_D]
  · by_cases hj : j = i <;> simp [hj, mapBaseChange_tmul, map_D, Derivation.leibniz]

/-- The retraction is a left inverse of `KaehlerDifferential.mapBaseChange R A A` up to the
equation `y_i` of the exceptional divisor. -/
theorem retraction_comp_mapBaseChange :
    letI := blowupChartTensorModule R σ τ i
    blowupChartDifferentialRetraction R σ τ i ∘ₗ blowupChartMapBaseChange R σ τ i =
      (X (Sum.inr i) : MvPolynomial (σ ⊕ τ) R) • LinearMap.id := by
  let := blowupChartModule R σ τ i
  let := blowupChartTensorModule R σ τ i
  let := @Algebra.to_smulCommClass _ _ _ _ (blowupChartAlgebra R σ τ i)
  refine (blowupChartBaseChangeBasis R σ τ i).ext fun v ↦ ?_
  rw [blowupChartBaseChangeBasis_apply, LinearMap.comp_apply, mapBaseChange_tmul, one_smul,
    map_D, algebraMap_blowupChartAlgebra]
  rcases v with k | j <;> [skip; rcases eq_or_ne j i with rfl | hj]
  on_goal 3 =>
    rw [blowupChartHom_X_inr_of_ne _ _ _ _ hj, Derivation.leibniz, map_add,
      LinearMap.map_smul, LinearMap.map_smul,
      blowupChartDifferentialRetraction_D_X_inr_self,
      blowupChartDifferentialRetraction_D_X_inr_of_ne _ _ _ _ hj,
      TensorProduct.tmul_eq_smul_one_tmul (X (Sum.inr j) : MvPolynomial (σ ⊕ τ) R),
      TensorProduct.tmul_eq_smul_one_tmul (X (Sum.inr i) : MvPolynomial (σ ⊕ τ) R)]
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    module
  all_goals
    simp only [blowupChartHom_X_inl, blowupChartHom_X_inr_self,
      blowupChartDifferentialRetraction_D_X_inl, blowupChartDifferentialRetraction_D_X_inr_self]
    exact TensorProduct.tmul_eq_smul_one_tmul _ _

end Stacks.Kaehler

end
