module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import Mathlib.AlgebraicGeometry.FunctionField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The meromorphic functions on an integral affine chart are its function field

Let `X` be an algebraic space over a scheme `S` satisfying the two standing hypotheses of
Stacks 0EN6, and let `V` be an *affine* étale chart of `X` whose scheme is integral. Then
`𝒦_X(V)` and the function field `R(V)` of that scheme are both total rings of fractions of the
same ring `𝒪_X(V) = Γ(V, 𝒪_V)`:

* `𝒦_X(V) = Q(𝒪_X(V))` is Stacks 0EN6, part (2),
  `AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj`; and
* `R(V) = Q(Γ(V, 𝒪_V))` is Mathlib's
  `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` at the open `⊤`.

So they are canonically isomorphic as `𝒪_X(V)`-algebras.

## Main results

* `AlgebraicGeometry.Space.chartFunctionFieldAlgebra`: the `𝒪_X(V)`-algebra structure on the
  function field of the chart scheme, by taking germs at the generic point.
* `AlgebraicGeometry.Space.isFractionRing_chartFunctionField`: the function field of an integral
  affine chart is the total ring of fractions of its regular functions.
* `AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv`: **the identification of `𝒦_X(V)`
  with the function field of the chart**, as an `𝒪_X(V)`-algebra isomorphism, with
  `AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv_algebraMap` for its action on a
  regular function.

## Implementation notes

The three algebra structures and the nonemptiness of the top open are `local` instances rather
than global ones, as `AlgebraicGeometry.Space.chartMeromorphicAlgebra` is: the ring of regular
functions on a chart has two spellings — the sections of
`AlgebraicGeometry.Space.structurePresheaf`, which is the one Stacks 0EN6, part (2) states its
localization at, and Mathlib's `Γ(chartScheme U, ⊤)` — and a *global* instance at either would be
found for the other only by unfolding `AlgebraicGeometry.Space.structurePresheaf`, which instance
search does not do.

The source of the isomorphism is spelled with `AlgebraicGeometry.Space.meromorphicFunctionSheaf`,
for the same reason, rather than with the definitionally equal
`AlgebraicGeometry.Space.meromorphicChartSheaf`.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The top open of an integral chart scheme is nonempty. -/
theorem nonempty_top_chartScheme (U : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme U)] :
    Nonempty (⊤ : (chartScheme U).Opens) :=
  ⟨⟨Nonempty.some inferInstance, trivial⟩⟩

attribute [local instance] nonempty_top_chartScheme

/-- The `𝒪_X(U)`-algebra structure on the meromorphic functions `𝒦_X(U)` over a chart, at the
spelling of the ring of regular functions that Stacks 0EN6, part (2) uses: restriction of scalars
along the component of `𝒪_X ⟶ 𝒦_X`. -/
abbrev chartMeromorphicFunctionAlgebra (U : SmallEtale B S hS X.1) :
    Algebra ((structurePresheaf B S hS X.1).obj (op U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
  ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra

/-- **The `𝒪_X(U)`-algebra structure on the function field of an integral chart**: a regular
function on the chart is sent to its germ at the generic point. -/
@[instance_reducible]
def chartFunctionFieldAlgebra (U : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme U)] :
    Algebra ((structurePresheaf B S hS X.1).obj (op U))
      ↥(chartScheme U).functionField :=
  ((chartScheme U).germToFunctionField ⊤).hom.toAlgebra

attribute [local instance] chartMeromorphicFunctionAlgebra chartFunctionFieldAlgebra

/-- The structure map of `AlgebraicGeometry.Space.chartFunctionFieldAlgebra` is the germ at the
generic point. -/
theorem chartFunctionFieldAlgebra_algebraMap (U : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme U)]
    (a : (structurePresheaf B S hS X.1).obj (op U)) :
    algebraMap ((structurePresheaf B S hS X.1).obj (op U))
        ↥(chartScheme U).functionField a =
      (chartScheme U).germToFunctionField ⊤ a := rfl

/-- **The function field of an integral affine chart is the total ring of fractions of its
regular functions.** -/
theorem isFractionRing_chartFunctionField (U : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme U)] (hU : IsAffine (chartScheme U)) :
    IsFractionRing ((structurePresheaf B S hS X.1).obj (op U))
      ↥(chartScheme U).functionField :=
  have := hU
  functionField_isFractionRing_of_isAffineOpen (chartScheme U) ⊤ (isAffineOpen_top _)

/-- **The meromorphic functions on an integral affine chart are its function field.** Both are
total rings of fractions of the regular functions on the chart — the first by Stacks 0EN6,
part (2), the second by Mathlib's
`AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` — so they agree. -/
@[ega "IV 20.1.13" "Algebraic clause only"]
def chartMeromorphicFunctionFieldEquiv
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme U)] (hU : IsAffine (chartScheme U)) :
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) ≃ₐ[
        (structurePresheaf B S hS X.1).obj (op U)] ↥(chartScheme U).functionField :=
  letI := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin U hU
  letI := isFractionRing_chartFunctionField B S hS X U hU
  IsLocalization.algEquiv ((structurePresheaf B S hS X.1).obj (op U))⁰ _ _

/-- The identification of `𝒦_X(U)` with the function field of the chart sends the meromorphic
function of a regular function to its germ at the generic point. -/
theorem chartMeromorphicFunctionFieldEquiv_algebraMap
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme U)] (hU : IsAffine (chartScheme U))
    (a : (structurePresheaf B S hS X.1).obj (op U)) :
    chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin U hU
        (algebraMap ((structurePresheaf B S hS X.1).obj (op U))
          ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) a) =
      (chartScheme U).germToFunctionField ⊤ a :=
  (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin U hU).commutes a

end AlgebraicGeometry.Space

end
