module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentWeight
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Contraction

/-!
# Geometric and numerical contractions of a numerical type

Let `f : X ⟶ X'` contract an exceptional curve of the first kind `C_n` in the special fibre of a
regular proper model, and let `T`, `T'` be the numerical types associated to `X` and `X'`. This
file compares `T'` with the contraction of `T` of [Stacks, Tag 0C77], as in [Stacks, Tag 0CA9]:
they agree in every datum except the weights; the geometric weight `w'ᵢ` divides `wᵢ`, and divides
`wₙ` when `Cᵢ` meets `Cₙ`; the numerical weight is the largest divisor of `wᵢ` for which the genus
formula is an integer, hence is at least the geometric one; and the injectivity of the map of
Picard groups of [Stacks, Tag 0C7J] holds for every choice of smaller weights.

The source states that `w'ᵢ` divides `wₙ` for every `i`; for a component missing `Cₙ` the
contraction is an isomorphism near `Cᵢ`, so `w'ᵢ = wᵢ`, which need not divide `wₙ`. The
divisibility `w'ᵢ ∣ wₙ` is therefore stated for the components meeting `Cₙ`, where the maps
`κᵢ ← κ'ᵢ → κₙ` of [Stacks, Tag 0C6C] (2) exist (see `errata.md`).

## Main results

* `Stacks.Models.RegularProperModelSituation.associatedNumericalType_contraction_comparison` —
  [Stacks, Tag 0CA9].

## References

* [Stacks Project, Tag 0CA9](https://stacks.math.columbia.edu/tag/0CA9)
* [Stacks Project, Tag 0C77](https://stacks.math.columbia.edu/tag/0C77)
* [Stacks Project, Tag 0C7J](https://stacks.math.columbia.edu/tag/0C7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.NumericalType

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) {N : irreducibleComponents S.specialFiber}
  {X' : Scheme.{u}} {f : S.X ⟶ X'}

/-- **Stacks Project, Tag 0CA9.** Let `f : X ⟶ X'` contract a component `C_n` of the special
fibre of a regular proper model which is an exceptional curve of the first kind. Enumerate the
components of `X_k` by `e`, with `C_n` last, and those of `X'_k` by `e'`, compatibly with
`C'_i = f(C_i)`. Let `T` and `T'` be the numerical types associated to `X` and `X'`. Then
* `n` is a `(-1)`-index of `T`, and `T'` agrees with the contraction of `T` of Tag 0C77 except
  for the weights: `n' = n - 1`, `m'_i = m_i`, `a'_{ij} = a_{ij} - a_{in}a_{jn}/a_{nn}`, `g'_i` is
  the genus formula at `w'_i`, and `w'_i` is a positive integer dividing `w_i`;
* `w'_i` divides `w_n` when `a_{in} ≠ 0` (that is, when `C_i` meets `C_n`), and `w'_i = w_i`
  when `a_{in} = 0`;
* the numerical contraction `T''` of Tag 0C77 has the same `n'`, `m'_i` and `a'_{ij}` as `T'`, and
  its weight `w''_i` is the largest positive integer dividing `w_i` for which the genus formula is
  an integer; in particular `w'_i ≤ w''_i`;
* for every numerical type which is a contraction of `T` up to weight (so with any weights
  `w'_i ∣ w_i`, the geometric `T'` among them) the map `Pic(T) → Pic(T')` of Tag 0C7J is injective.

The source asserts `w'_i ∣ w_n` for every `i`; for a component missing `C_n` the weight is `w_i`,
which need not divide `w_n` (for the numerical datum, see
`AlgebraicGeometry.NumericalType.exists_intersection_eq_zero_not_weight_dvd`), so that
divisibility is stated for the components meeting `C_n`. -/
@[stacks 0CA9 "corrected: w'_i | w_n is stated for the components C_i meeting C_n, where 0C6C (2) \
gives the maps; a component missing C_n keeps w'_i = w_i, which need not divide w_n"]
public theorem associatedNumericalType_contraction_comparison
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    [DecidableEq (irreducibleComponents (S.contractedSituation hf).specialFiber)]
    (κ : Type u) [Field κ] {ε : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal N).subscheme}
    (hE : (S.specialFiberComponentIdeal N).IsExceptionalCurveOfFirstKind κ ε)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (e' : Fin (n - 1) ≃ irreducibleComponents (S.contractedSituation hf).specialFiber)
    (hN : e (lastIndex (S.associatedNumericalType n e)) = N)
    (he' : ∀ i, ((S.contractedComponentEquiv hf).symm (e' i)).1 =
      e (remainingIndex (S.associatedNumericalType n e) i)) :
    let T := S.associatedNumericalType n e
    let T' := (S.contractedSituation hf).associatedNumericalType (n - 1) e'
    ∃ h : IsMinusOneIndex T (lastIndex T), ∃ hT : IsContractionUpToWeight T T',
      -- the geometric weights
      (∀ i, T.intersection (remainingIndex T i) (lastIndex T) ≠ 0 →
          T'.weight (Fin.cast hT.componentCount_eq.symm i) ∣ T.weight (lastIndex T)) ∧
      (∀ i, T.intersection (remainingIndex T i) (lastIndex T) = 0 →
          T'.weight (Fin.cast hT.componentCount_eq.symm i) = T.weight (remainingIndex T i)) ∧
      -- comparison with the numerical contraction of Tag 0C77
      T'.componentCount = (contractLast T h).val.componentCount ∧
      (∀ i, T'.multiplicity (Fin.cast hT.componentCount_eq.symm i) =
          (contractLast T h).val.multiplicity
            (Fin.cast (contractLast T h).property.componentCount_eq.symm i)) ∧
      (∀ i j, T'.intersection (Fin.cast hT.componentCount_eq.symm i)
            (Fin.cast hT.componentCount_eq.symm j) =
          (contractLast T h).val.intersection
            (Fin.cast (contractLast T h).property.componentCount_eq.symm i)
            (Fin.cast (contractLast T h).property.componentCount_eq.symm j)) ∧
      (∀ i, T'.weight (Fin.cast hT.componentCount_eq.symm i) ≤
          (contractLast T h).val.weight
            (Fin.cast (contractLast T h).property.componentCount_eq.symm i)) ∧
      -- the numerical weight is the largest admissible one
      (∀ i, IsGreatest {d : ℤ | 0 < d ∧ d ∣ T.weight (remainingIndex T i) ∧
          ∃ G : ℤ, (G : ℚ) = (T.weight (remainingIndex T i) : ℚ) / d *
              ((T.componentGenus (remainingIndex T i) : ℚ) - 1) + 1 +
            ((T.intersection (remainingIndex T i) (lastIndex T) : ℚ) ^ 2 -
                T.weight (lastIndex T) * T.intersection (remainingIndex T i) (lastIndex T)) /
              (2 * d * T.weight (lastIndex T))}
        ((contractLast T h).val.weight
          (Fin.cast (contractLast T h).property.componentCount_eq.symm i))) ∧
      -- injectivity on Picard groups for smaller weights
      ∀ (T'' : NumericalType) (hT'' : IsContractionUpToWeight T T''),
        Function.Injective (hT''.picardMap h) := by
  intro T T'
  obtain ⟨h, hT, hdvd, heq⟩ :=
    S.isContractionUpToWeight_associatedNumericalType hf κ hE n e e' hN he'
  have hC := (contractLast T h).property
  refine ⟨h, hT, hdvd, heq, hT.componentCount_eq.trans hC.componentCount_eq.symm,
    fun i => (hT.multiplicity_eq i).trans (hC.multiplicity_eq i).symm,
    fun i j => by exact_mod_cast (hT.intersection_eq i j).trans (hC.intersection_eq i j).symm,
    fun i => (isGreatest_contractLast_weight T h i).2
      ⟨T'.weight_pos _, hT.weight_dvd i, T'.componentGenus _, hT.componentGenus_eq i⟩,
    isGreatest_contractLast_weight T h, fun _ hT'' => hT''.picardMap_injective h⟩

end RegularProperModelSituation

end Stacks.Models

end
