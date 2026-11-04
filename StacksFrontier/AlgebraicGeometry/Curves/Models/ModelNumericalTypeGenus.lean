module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaModel
import StacksCore.Tactic.StacksAttribute

/-!
# The numerical type of a regular proper model has the genus of the curve

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X` of `C`, `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and `gᵢ` the genus of
`Cᵢ`. [Stacks, Tag 0CA4] asserts that the data `n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ` form a numerical
type in the sense of [Stacks, Tag 0C6Z] whose genus, in the sense of [Stacks, Tag 0C72], is the
genus of `C`.

## Main results

* `Stacks.Models.RegularProperModelSituation.associatedNumericalType_spec_and_genus` —
  **[Stacks, Tag 0CA4]**: the numerical type associated to `X` has the data
  `n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ` of the model, and its genus is the genus of `C`.

## Implementation notes

The numerical type itself is
`Stacks.Models.RegularProperModelSituation.associatedNumericalType`, whose fields carry the
laws of a numerical type; that it has the model's data is
`Stacks.Models.RegularProperModelSituation.associatedNumericalType_spec`. The genus clause is the
genus formula of [Stacks, Tag 0CA3] read through
`Stacks.Models.RegularProperModelSituation.cast_genus_associatedNumericalType`, which writes the
genus of the numerical type as the right-hand side of that formula, as in the source's proof.

## References

* [Stacks Project, Tag 0CA4](https://stacks.math.columbia.edu/tag/0CA4)
* [Stacks Project, Tag 0CA3](https://stacks.math.columbia.edu/tag/0CA3)
* [Stacks Project, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z)
* [Stacks Project, Tag 0C72](https://stacks.math.columbia.edu/tag/0C72)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})
  [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **Stacks Project, Tag 0CA4.** In the situation of [Stacks, Tag 0C61], with `C₁, …, Cₙ` the
irreducible components of the special fibre enumerated by `e`, `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and `gᵢ`
the genus of `Cᵢ` over `κᵢ`, the data `n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ` form a numerical type —
the numerical type `Stacks.Models.RegularProperModelSituation.associatedNumericalType`, whose
fields carry the laws of [Stacks, Tag 0C6Z] — and its genus is the genus `g_C` of `C`. -/
@[stacks 0CA4 "the data n, m_i, (C_i . C_j), [kappa_i : k], g_i form a numerical type of \
genus the genus of C"]
public theorem associatedNumericalType_spec_and_genus (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    ((S.associatedNumericalType n e).componentCount = n ∧
      (∀ i, (S.associatedNumericalType n e).multiplicity i =
        (S.specialFiberMultiplicity (e i) : ℤ)) ∧
      (∀ i j, (S.associatedNumericalType n e).intersection i j =
        S.specialFiberIntersectionMatrix (e i) (e j)) ∧
      (∀ i, (S.associatedNumericalType n e).weight i =
        (S.specialFiberComponentWeight (e i) : ℤ)) ∧
      (∀ i, (S.associatedNumericalType n e).componentGenus i =
        (S.specialFiberComponentGenus (e i) : ℤ))) ∧
    (S.associatedNumericalType n e).genus = (genus S.C_to_K : ℤ) :=
  ⟨S.associatedNumericalType_spec n e, by
    exact_mod_cast (S.cast_genus_associatedNumericalType n e).trans
      S.cast_genus_eq_one_add_sum_specialFiberComponent.symm⟩

end RegularProperModelSituation

end Stacks.Models

end
