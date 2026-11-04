module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateFunctionals
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare

/-!
# The coordinate functionals of `Ω` of a `p`-adically completed divided power ring

[Stacks, Tag 07J9] defines the module of differentials of the `p`-adically completed divided power
envelope `D` as the inverse limit `Ω_D = lim_e Ω_{D_e/A, γ̄}`, every element of which is a
convergent series `∑ f_i d x_i`, with only finitely many `f_i` outside `p^e D` for each `e`. For an
infinite family of coordinates `Ω_D` is therefore not free on the `d x_i`.

This module constructs, for such a completed module, a family of `D`-linear coordinate functionals
`c_j : Ω → D` biorthogonal to the differentials (a `Crystalline.IsCoordinateDual`), with no
finiteness and no basis of the completion; this is the input of the proofs of items (07JD) and
(07JE) of [Stacks, Lemma 60.17.3, Tag 07JG].

## The construction

By `Crystalline.dividedPowerDifferentialsCompletionComparison` ([Stacks, Tag 07KK]), for `B` a
divided power ring in which `p` is nilpotent modulo the divided power ideal, the three inverse
limits

`lim_e Ω_{B_e}`,   `Ω_B^∧ = lim_e (Ω_B / p^e Ω_B)`,   `Ω_{B^∧}^∧`

are canonically identified; [Stacks, Tag 07J9] and [Stacks, Tag 07L0] define `Ω_D` and `Ω_{D(n)}`
as these limits. The middle one is Mathlib's `AdicCompletion` of the uncompleted module of
differentials, and this module works with it. For the envelope `B` of a polynomial presentation,
`Ω_B` is free on the `d x_i` (`Crystalline.dividedPowerDifferentialsBasis`), so its coordinates
`c_j^0 : Ω_B → B` exist, and their `p`-adic completions

`c_j = Ω_B^∧ ⟶ B^∧ = D`

are biorthogonal to the `d x_i`. They are `D`-linear because the completion `AdicCompletion.map`
of a linear map is linear over `AdicCompletion I R`.

The index family is arbitrary, and `Ω_B^∧` is not asserted to be free.

## Main definitions

* `Crystalline.adicDualFamily` — the completed coordinates
  `fun j ↦ AdicCompletion.map I (b.coord j)` of a basis `b` of `N`, as a family of functionals on
  `AdicCompletion I N` over `AdicCompletion I R`.

## Main results

* `Crystalline.adicCompletionOf_one` — the canonical map into an adic completion is unital.
* `Crystalline.adicDualFamily_of` — the completed coordinates on the image of an element.
* `Crystalline.isCoordinateDual_adicDualFamily` — the completed coordinates of a basis are a
  dual family for the images of the basis vectors in the completion, for an arbitrary index type.
* `Crystalline.isCoordinateDual_completedDividedPowerDifferentials` — the same at the divided
  power differentials of a divided power polynomial algebra `A⟨x_w : w ∈ W⟩`, where the basis is
  `Crystalline.dividedPowerDifferentialsBasis`.
* `Crystalline.eq_of_isCoordinateExpansion_adicCompletion`,
  `Crystalline.isIntegrable_of_isThetaMonomialFamily_adicCompletion` and
  `Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily_adicCompletion` —
  uniqueness of the coordinate operators and items (07JD) and (07JE) over a completed module of
  differentials, with no finiteness of the family of coordinates and no basis of the
  completion.

## Scope

No `@[stacks]` attribute is placed in this module. The two items of [Stacks, Tag 07JG] are proved
for an arbitrary family of coordinates, not for a crystal: the monomial family
`θ_K = ∏_i θ_i^{k_i}` that the source reads off `D(2)` and the `p`-adic convergence it reads off
`D(1)` are not treated here.

The identification of `AdicCompletion I Ω_B` with the limit `lim_e Ω_{B_e}` of [Stacks, Tag 07J9]
is `Crystalline.DifferentialsCompletionComparison.fromOriginalLimit`, an `AddEquiv` that is not
recorded as `D`-linear; the dual family is constructed on `AdicCompletion` and is not transported
across that equivalence.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Tag 07L0](https://stacks.math.columbia.edu/tag/07L0)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open scoped TensorProduct

universe u v uI w

namespace Crystalline

open DividedPowers

attribute [local instance low] setIndexedDividedPowerPolynomialCommRing
  coefficientDividedPowerRingAlgebra setIndexedDividedPowerPolynomialAlgebra'
  setIndexedDividedPowerPolynomialDividedPowerRingAlgebra

attribute [local implicit_reducible] coefficientDividedPowerRing
  DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing

/-! ### The completed coordinates of a basis -/

section AdicDual

variable {R : Type u} [CommRing R] (I : Ideal R) {N : Type v} [AddCommGroup N] [Module R N]
  {ι : Type uI}

/-- **The canonical map into an adic completion is unital.** -/
theorem adicCompletionOf_one : AdicCompletion.of I R (1 : R) = 1 :=
  map_one (algebraMap R (AdicCompletion I R))

/-- **The completed coordinates of a basis.** For a basis `b` of an `R`-module `N`, the `I`-adic
completion of its `j`-th coordinate `b.coord j : N → R`, as a map linear over
`AdicCompletion I R`. -/
noncomputable def adicDualFamily (b : Module.Basis ι R N) (j : ι) :
    AdicCompletion I N →ₗ[AdicCompletion I R] AdicCompletion I R :=
  AdicCompletion.map I (b.coord j)

/-- The completed `j`-th coordinate of the image of `x : N` in the completion is the image of the
`j`-th coordinate of `x`. -/
@[simp] theorem adicDualFamily_of (b : Module.Basis ι R N) (j : ι) (x : N) :
    adicDualFamily I b j (AdicCompletion.of I N x) =
      AdicCompletion.of I R (b.coord j x) :=
  AdicCompletion.map_of I (b.coord j) x

/-- **The completed coordinates of a basis are a dual family.**

If `d x_i` is the image in `AdicCompletion I N` of the `i`-th vector of a basis of `N`, then the
functionals `Crystalline.adicDualFamily` are biorthogonal to them. The index type is arbitrary. -/
theorem isCoordinateDual_adicDualFamily (b : Module.Basis ι R N)
    {dx : ι → AdicCompletion I N} (hdx : ∀ i, dx i = AdicCompletion.of I N (b i)) :
    IsCoordinateDual dx (adicDualFamily I b) where
  self i := by simp [hdx i, adicCompletionOf_one]
  of_ne {i j} hij := by simp [hdx i, Finsupp.single_eq_of_ne (Ne.symm hij)]

end AdicDual

/-! ### Uniqueness and the two items over a completed module of differentials -/

section Items

variable {R : Type u} [CommRing R] (I : Ideal R) {N : Type v} [AddCommGroup N] [Module R N]
  {ι : Type uI} (b : Module.Basis ι R N) {dx : ι → AdicCompletion I N}
  (hdx : ∀ i, dx i = AdicCompletion.of I N (b i))
  (p : ℕ) (M : Type w) [AddCommGroup M] [Module (AdicCompletion I R) M]
  {dd : AdicCompletion I R → AdicCompletion I N}
  {nabla : CompletedConnection p (AdicCompletion I R) (AdicCompletion I N) dd M}

include b hdx

/-- **The coordinate operators of a completed connection over a completed module of differentials
are unique.** For `dx` the images in `AdicCompletion I N` of a basis of `N`, indexed by an
arbitrary type, two families of coordinate operators of the connection coincide when `M` is
`p`-adically Hausdorff. -/
theorem eq_of_isCoordinateExpansion_adicCompletion {theta theta' : ι → (M → M)}
    (hco : IsCoordinateExpansion p (AdicCompletion I R) (AdicCompletion I N) dx nabla theta)
    (hco' : IsCoordinateExpansion p (AdicCompletion I R) (AdicCompletion I N) dx nabla theta')
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := AdicCompletion I R) p) M) :
    theta = theta' :=
  eq_of_isCoordinateExpansion_of_isCoordinateDual p (AdicCompletion I R) (AdicCompletion I N) M
    hco hco' (isCoordinateDual_adicDualFamily I b hdx) hM

variable {theta : ι → (M → M)} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- **Item (07JD) of [Stacks, Lemma 60.17.3, Tag 07JG] over a completed module of
differentials**: the connection is integrable, with no finiteness of the family of coordinates and
no basis of `Ω` itself. -/
theorem isIntegrable_of_isThetaMonomialFamily_adicCompletion
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hco : IsCoordinateExpansion p (AdicCompletion I R) (AdicCompletion I N) dx nabla theta)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := AdicCompletion I R) p) M) :
    IsIntegrable p (AdicCompletion I R) (AdicCompletion I N) dx nabla :=
  isIntegrable_of_isThetaMonomialFamily_of_isCoordinateDual p (AdicCompletion I R)
    (AdicCompletion I N) M hfamM hco (isCoordinateDual_adicDualFamily I b hdx) hM

/-- **Item (07JE) of [Stacks, Lemma 60.17.3, Tag 07JG] over a completed module of
differentials**: the connection is topologically quasi-nilpotent, with no finiteness of the family
of coordinates and no basis of `Ω` itself. -/
theorem isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily_adicCompletion
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hco : IsCoordinateExpansion p (AdicCompletion I R) (AdicCompletion I N) dx nabla theta)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := AdicCompletion I R) p) M)
    (hfin : ∀ m : M, {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p (AdicCompletion I R) M}.Finite) :
    IsTopologicallyQuasiNilpotent p (AdicCompletion I R) (AdicCompletion I N) dx nabla :=
  isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily_of_isCoordinateDual p
    (AdicCompletion I R) (AdicCompletion I N) M hfamM hco
    (isCoordinateDual_adicDualFamily I b hdx) hM hfin

end Items

/-! ### The divided power differentials of a divided power polynomial algebra, completed -/

section DividedPower

variable (A : Type u) [CommRing A] (W : Type w) (p : ℕ)

/-- **The completed divided power differentials of a divided power polynomial algebra have a dual
family of coordinate functionals on the `d x_w`.**

`Crystalline.dividedPowerDifferentialsBasis` is the basis of `Ω¹_{P/A,δ}` on the differentials of
the variables, for `P = A⟨x_w : w ∈ W⟩` and an arbitrary family `W`.  Its completed coordinates are
a dual family on the completion, over the completed ring `P^∧`; by [Stacks, Tag 07KK] this
completion is the `Ω` of the completed divided power ring, the module [Stacks, Tag 07J9] and
[Stacks, Tag 07L0] call `Ω_D` and `Ω_{D(n)}`. -/
theorem isCoordinateDual_completedDividedPowerDifferentials
    {dx : W → AdicCompletion
      (DividedPowers.pAdicIdeal (A := ↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)) p)
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers)}
    (hdx : ∀ i, dx i = AdicCompletion.of _ _
      (dividedPowerDifferential (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers
        (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i))) :
    IsCoordinateDual dx
      (adicDualFamily (DividedPowers.pAdicIdeal (A := ↑(
        setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W)) p)
        (dividedPowerDifferentialsBasis A W)) :=
  isCoordinateDual_adicDualFamily _ (dividedPowerDifferentialsBasis A W)
    fun i ↦ (hdx i).trans (by rw [dividedPowerDifferentialsBasis_apply])

end DividedPower

end Crystalline

end
