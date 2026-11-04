module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberIntersectionForm
import StacksCore.Tactic.StacksAttribute

/-!
# The numerical type associated to a regular proper model

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X ⟶ Spec(R)`, let `mᵢ` be their multiplicities,
`κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and `gᵢ` the genus of `Cᵢ` over `κᵢ`. [Stacks, Tag 0CA5] names the
numerical type of [Stacks, Tag 0CA4], with data `n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ`, *the numerical
type associated to `X`*.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.associatedNumericalType` — **[Stacks, Tag 0CA5]**,
  the numerical type associated to `X`, with every law of a numerical type proved.

## Main results

* `Stacks.Models.RegularProperModelSituation.associatedNumericalType_componentCount`,
  `..._multiplicity`, `..._intersection`, `..._weight`, `..._componentGenus` — the five families
  of the numerical type associated to `X`, which are what a consumer of Tag 0CA5 computes with.
* `Stacks.Models.RegularProperModelSituation.associatedNumericalType_spec` — the numerical type
  associated to `X` has the data `n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ` of the model. Together with its
  genus this is [Stacks, Tag 0CA4], carried by
  `Stacks.Models.RegularProperModelSituation.associatedNumericalType_spec_and_genus` in
  `StacksFrontier/AlgebraicGeometry/Curves/Models/ModelNumericalTypeGenus.lean`.
* `Stacks.Models.RegularProperModelSituation.cast_genus_associatedNumericalType` — the genus of
  the numerical type associated to `X` in the model's own terms.
* `Stacks.Models.RegularProperModelSituation.equivalent_associatedNumericalType` — **the
  numerical type associated to `X` is independent of the enumeration of the components**, up to
  the equivalence of [Stacks, Tag 0C70]. This is what licenses the definite article of
  [Stacks, Tag 0CA5].

## Implementation notes

The numerical type is
`Stacks.Models.RegularProperModelSituation.specialFiberNumericalType` at the multiplicities of
[Stacks, Tag 0C5Z], the intersection matrix
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix` and the component
genus `Stacks.Models.RegularProperModelSituation.specialFiberComponentGenus`, with each of its
hypotheses discharged: `hdec` and `hm` by part (3) of [Stacks, Tag 0C5Z]
(`Stacks.Models.RegularModelSituation.specialFiberIdeal_eq_prod`,
`Stacks.Models.RegularModelSituation.specialFiberMultiplicity_pos`), `hexpand` by
`Stacks.Models.RegularProperModelSituation.specialFiberDivisorDegree_eq_sum` ([Stacks, Tag 0AYX]),
`hsymm` by `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_comm`
([Stacks, Tag 0C64]), and `hoffDiag` and `hconnected` by parts (1) and (3) of [Stacks, Tag 0C66],
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff`
and `Stacks.Models.RegularProperModelSituation.not_forall_specialFiberIntersectionMatrix_eq_zero`.

The components of the special fibre carry no ordering, so an enumeration
`e : Fin n ≃ irreducibleComponents X_k` is an argument; nothing is chosen.

## References

* [Stacks Project, Tag 0CA5](https://stacks.math.columbia.edu/tag/0CA5)
* [Stacks Project, Tag 0CA4](https://stacks.math.columbia.edu/tag/0CA4)
* [Stacks Project, Tag 0C70](https://stacks.math.columbia.edu/tag/0C70)
* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **Stacks Project, Tag 0CA5: the numerical type associated to `X`**, in the situation of
[Stacks, Tag 0C61]: the numerical type described in [Stacks, Tag 0CA4], whose data are the number
`n` of irreducible components `C₁, …, Cₙ` of the special fibre (enumerated by `e`), their
multiplicities `mᵢ` (Tag 0C5Z), their intersection numbers `(Cᵢ · Cⱼ)`, their weights
`[κᵢ : k]` with `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})`, and their genera `gᵢ` over `κᵢ`. All the laws of a
numerical type are proved: the multiplicities are positive, the intersection matrix is the degree
matrix of the components, symmetric, nonnegative off the diagonal, connected and annihilates
`(mᵢ)`, and `[κᵢ : k]` divides every `(Cᵢ · Cⱼ)`. The enumeration is immaterial by
`Stacks.Models.RegularProperModelSituation.equivalent_associatedNumericalType`, which is what
licenses the definite article. -/
@[stacks 0CA5 "the numerical type associated to X: n, m_i, (C_i . C_j), [kappa_i : k], g_i of \
the components of the special fibre"]
public def associatedNumericalType (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    AlgebraicGeometry.NumericalType :=
  S.specialFiberNumericalType n e S.specialFiberMultiplicity S.specialFiberIntersectionMatrix
    S.specialFiberComponentGenus S.specialFiberIdeal_eq_prod S.specialFiberMultiplicity_pos
    (fun c Z => S.specialFiberDivisorDegree_eq_sum Z c) S.specialFiberIntersectionMatrix_comm
    (fun _ _ h => (S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff h).1)
    S.not_forall_specialFiberIntersectionMatrix_eq_zero

section AssociatedFields

variable (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)

/-- The numerical type associated to `X` has one component for each irreducible component of the
special fibre. -/
@[simp] public theorem associatedNumericalType_componentCount :
    (S.associatedNumericalType n e).componentCount = n := rfl

/-- The multiplicities of the numerical type associated to `X` are the multiplicities `mᵢ` of the
components of the special fibre. -/
@[simp] public theorem associatedNumericalType_multiplicity (i : Fin n) :
    (S.associatedNumericalType n e).multiplicity i = (S.specialFiberMultiplicity (e i) : ℤ) := rfl

/-- **The intersection matrix of the numerical type associated to `X` is `(Cᵢ · Cⱼ)`**, the
degree of `𝒪_X(Cⱼ)` on `Cᵢ`. -/
@[simp] public theorem associatedNumericalType_intersection (i j : Fin n) :
    (S.associatedNumericalType n e).intersection i j =
      S.specialFiberIntersectionMatrix (e i) (e j) := rfl

/-- The weights of the numerical type associated to `X` are the degrees `[κᵢ : k]`. -/
@[simp] public theorem associatedNumericalType_weight (i : Fin n) :
    (S.associatedNumericalType n e).weight i = (S.specialFiberComponentWeight (e i) : ℤ) := rfl

/-- The component genera of the numerical type associated to `X` are the genera `gᵢ` of the
components of the special fibre over their own fields of global functions. -/
@[simp] public theorem associatedNumericalType_componentGenus (i : Fin n) :
    (S.associatedNumericalType n e).componentGenus i =
      (S.specialFiberComponentGenus (e i) : ℤ) := rfl

/-- **The data of the numerical type associated to `X`.** In the situation of
[Stacks, Tag 0C61], with `C₁, …, Cₙ` the irreducible components of the special fibre enumerated
by `e`, `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and `gᵢ` the genus of `Cᵢ` over `κᵢ`, the data
`n, mᵢ, (Cᵢ · Cⱼ), [κᵢ : k], gᵢ` form a numerical type in the sense of [Stacks, Tag 0C6Z]: the
numerical type `Stacks.Models.RegularProperModelSituation.associatedNumericalType` has exactly
these data, all of its laws being proved. -/
public theorem associatedNumericalType_spec :
    (S.associatedNumericalType n e).componentCount = n ∧
    (∀ i, (S.associatedNumericalType n e).multiplicity i = (S.specialFiberMultiplicity (e i) : ℤ)) ∧
    (∀ i j, (S.associatedNumericalType n e).intersection i j =
      S.specialFiberIntersectionMatrix (e i) (e j)) ∧
    (∀ i, (S.associatedNumericalType n e).weight i =
      (S.specialFiberComponentWeight (e i) : ℤ)) ∧
    (∀ i, (S.associatedNumericalType n e).componentGenus i =
      (S.specialFiberComponentGenus (e i) : ℤ)) :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **The genus of the numerical type associated to `X`, in the model's own terms**:
`g = 1 + Σ_Z m_Z([κ_Z : k](g_Z - 1) - ½(C_Z · C_Z))`, the sum running over the irreducible
components of the special fibre rather than over their enumeration. This is the right-hand side
of the genus formula of [Stacks, Tag 0CA3], so the genus clause of [Stacks, Tag 0CA4] is that
formula read through this identity. -/
public theorem cast_genus_associatedNumericalType :
    ((S.associatedNumericalType n e).genus : ℚ) = 1 + ∑ Z, (S.specialFiberMultiplicity Z : ℚ) *
      ((S.specialFiberComponentWeight Z : ℚ) * ((S.specialFiberComponentGenus Z : ℚ) - 1) -
        (S.specialFiberIntersectionMatrix Z Z : ℚ) / 2) := by
  rw [AlgebraicGeometry.NumericalType.cast_genus]
  refine congrArg (fun x : ℚ => 1 + x) (Fintype.sum_equiv e _ _ fun i => ?_)
  simp only [associatedNumericalType_multiplicity, associatedNumericalType_weight,
    associatedNumericalType_componentGenus, associatedNumericalType_intersection]
  push_cast
  ring

end AssociatedFields

/-- **The numerical type associated to `X` does not depend on the enumeration of the components.**
Two enumerations of the irreducible components of the special fibre give equivalent numerical
types in the sense of [Stacks, Tag 0C70], the relabelling being the change of enumeration.

This is what licenses the definite article of [Stacks, Tag 0CA5]: the enumeration `e` is an
argument only because `AlgebraicGeometry.NumericalType` is indexed by `Fin n` while the
components of the special fibre carry no ordering, and the numerical type it produces is
independent of it. -/
public theorem equivalent_associatedNumericalType (n n' : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (e' : Fin n' ≃ irreducibleComponents S.specialFiber) :
    AlgebraicGeometry.NumericalType.Equivalent
      (S.associatedNumericalType n e)
      (S.associatedNumericalType n' e') :=
  by
  have h (i) : e i = e' ((e.trans e'.symm) i) := (e'.apply_symm_apply _).symm
  exact ⟨e.trans e'.symm, fun i => congrArg (Nat.cast ∘ S.specialFiberMultiplicity) (h i),
    fun i j => congrArg₂ S.specialFiberIntersectionMatrix (h i) (h j),
    fun i => congrArg (fun Z => (S.specialFiberComponentWeight Z : ℤ)) (h i),
    fun i => congrArg (fun Z => (S.specialFiberComponentGenus Z : ℤ)) (h i)⟩

end RegularProperModelSituation

end Stacks.Models

end
