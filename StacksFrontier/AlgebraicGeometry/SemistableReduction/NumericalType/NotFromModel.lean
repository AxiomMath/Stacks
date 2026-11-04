module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Irreducible
public import Mathlib

/-!
# Numerical types that do not come from a model

Not every numerical type is the numerical type of a regular proper model, over a discrete
valuation ring, of a smooth projective geometrically irreducible curve over the fraction
field of that ring. The genus already obstructs this, since there are numerical types of
negative genus whereas the numerical type of such a model has the genus of the generic
curve. Positivity of the genus is not sufficient either: the one-component type of
multiplicity one, weight six and component genus one is minimal of genus one, and the
two-component type with both multiplicities one, both weights six, both component genera
one, self-intersections `-6` and mutual intersection `6` is minimal of genus seven. Neither
comes from a model, because the special fibre of such a model would live over a degree six
extension of the residue field and hence fail to be geometrically connected, contradicting
geometric connectedness of the generic fibre.

## Main results

* `AlgebraicGeometry.NumericalType.exists_genus_neg`: there is a numerical type of negative
  genus.
* `AlgebraicGeometry.NumericalType.exists_isMinimal_genus_one_weight_six` and
  `AlgebraicGeometry.NumericalType.exists_isMinimal_genus_seven_weight_six`: the two minimal
  numerical types of positive genus named by the source, all of whose weights are six.

## Implementation notes

Each existence statement pins down the whole of the data `n, mᵢ, aᵢⱼ, wᵢ, gᵢ`, so its witness
is the numerical type the source names and no other.

That no model realizes these numerical types is proved in
`StacksFrontier/AlgebraicGeometry/SemistableReduction/NumericalType/NotAssociated.lean`, from the
numerical type associated to a model (Tag 0CA5); the `@[stacks 0CA7]` attributes below name the
numerical half of each assertion.

## References

* [Stacks Project, Tag 0CA7](https://stacks.math.columbia.edu/tag/0CA7)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-! ### A numerical type of negative genus -/

/-- The one-component numerical type of multiplicity one, weight two and component genus
zero; its genus is `-1`. -/
private abbrev weightTwoGenusZeroType : NumericalType :=
  singletonNumericalType 1 2 0 one_pos (by norm_num) le_rfl

private lemma genus_weightTwoGenusZeroType : genus weightTwoGenusZeroType = -1 := by
  simpa using singletonNumericalType_genus 1 2 0 one_pos (by norm_num) le_rfl

/-- There is a numerical type whose genus is negative. The numerical type of a model has the
genus of the generic curve, which is nonnegative, so no such type comes from a model. -/
@[stacks 0CA7 "there exist numerical types whose genus is negative"]
public theorem exists_genus_neg : ∃ T : NumericalType, genus T < 0 :=
  ⟨weightTwoGenusZeroType, by rw [genus_weightTwoGenusZeroType]; norm_num⟩

/-! ### The one-component minimal type of genus one and weight six -/

/-- The one-component numerical type of multiplicity one, weight six and component genus
one. -/
private abbrev weightSixGenusOneType : NumericalType :=
  singletonNumericalType 1 6 1 one_pos (by norm_num) zero_le_one

private lemma genus_weightSixGenusOneType : genus weightSixGenusOneType = 1 := by
  simpa using singletonNumericalType_genus 1 6 1 one_pos (by norm_num) zero_le_one

private lemma isMinimal_weightSixGenusOneType : IsMinimal weightSixGenusOneType := by
  rintro ⟨i, hgenus, -⟩
  exact one_ne_zero hgenus

/-- The data `n = 1`, `m₁ = 1`, `a₁₁ = 0`, `w₁ = 6`, `g₁ = 1` is a minimal numerical type of
genus one. -/
@[stacks 0CA7 "n = 1, m₁ = 1, a₁₁ = 0, w₁ = 6, g₁ = 1 is a minimal numerical type of genus one"]
public theorem exists_isMinimal_genus_one_weight_six :
    ∃ T : NumericalType, T.componentCount = 1 ∧
      (∀ i, T.multiplicity i = 1) ∧
      (∀ i j, T.intersection i j = 0) ∧
      (∀ i, T.weight i = 6) ∧
      (∀ i, T.componentGenus i = 1) ∧
      IsMinimal T ∧ genus T = 1 :=
  ⟨weightSixGenusOneType, rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    isMinimal_weightSixGenusOneType, genus_weightSixGenusOneType⟩

/-! ### The two-component minimal type of genus seven and weight six -/

/-- The intersection matrix with `-6` on the diagonal and `6` off it. -/
private abbrev doubleSixIntersection : Fin 2 → Fin 2 → ℤ :=
  fun i j => if i = j then -6 else 6

/-- The two-component numerical type with both multiplicities one, both weights six, both
component genera one, self-intersections `-6` and mutual intersection `6`. -/
private abbrev doubleSixType : NumericalType :=
  { componentCount := 2
    componentCount_pos := by omega
    multiplicity := fun _ => 1
    intersection := doubleSixIntersection
    weight := fun _ => 6
    componentGenus := fun _ => 1
    multiplicity_pos := fun _ => one_pos
    weight_pos := fun _ => by norm_num
    componentGenus_nonneg := fun _ => zero_le_one
    intersection_symm := by
      intro i j
      by_cases h : i = j
      · subst h; rfl
      · simp [doubleSixIntersection, h, Ne.symm h]
    intersection_nonneg := by
      intro i j h
      simp [doubleSixIntersection, h]
    connected := by
      rintro ⟨I, ⟨i, hi⟩, hIuniv, hzero⟩
      obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
        by_contra hall
        exact hIuniv (Set.eq_univ_of_forall fun x => not_not.mp fun hx => hall ⟨x, hx⟩)
      have hne : i ≠ j := fun h => hj (h ▸ hi)
      have h0 := hzero i hi j hj
      simp [doubleSixIntersection, hne] at h0
    intersection_mul_multiplicity := by
      intro i
      fin_cases i <;> simp [Fin.sum_univ_two, doubleSixIntersection]
    weight_dvd_intersection := by
      intro i j
      by_cases h : i = j <;> simp [doubleSixIntersection, h] }

private lemma genus_doubleSixType : genus doubleSixType = 7 := by
  unfold genus
  norm_num [Fin.sum_univ_two, doubleSixIntersection]

private lemma isMinimal_doubleSixType : IsMinimal doubleSixType := by
  rintro ⟨i, hgenus, -⟩
  simp at hgenus

/-- The data `n = 2`, `m₁ = m₂ = 1`, `-a₁₁ = -a₂₂ = a₁₂ = a₂₁ = 6`, `w₁ = w₂ = 6`,
`g₁ = g₂ = 1` is a minimal numerical type of genus seven. -/
@[stacks 0CA7 "n = 2, m₁ = m₂ = 1, -a₁₁ = -a₂₂ = a₁₂ = a₂₁ = 6, w₁ = w₂ = 6, g₁ = g₂ = 1 \
  is a minimal numerical type of genus seven"]
public theorem exists_isMinimal_genus_seven_weight_six :
    ∃ T : NumericalType, T.componentCount = 2 ∧
      (∀ i, T.multiplicity i = 1) ∧
      (∀ i, T.intersection i i = -6) ∧
      (∀ i j, i ≠ j → T.intersection i j = 6) ∧
      (∀ i, T.weight i = 6) ∧
      (∀ i, T.componentGenus i = 1) ∧
      IsMinimal T ∧ genus T = 7 :=
  ⟨doubleSixType, rfl, fun _ => rfl, fun _ => by simp [doubleSixIntersection],
    fun _ _ h => by simp [doubleSixIntersection, h], fun _ => rfl, fun _ => rfl,
    isMinimal_doubleSixType, genus_doubleSixType⟩

end AlgebraicGeometry.NumericalType
