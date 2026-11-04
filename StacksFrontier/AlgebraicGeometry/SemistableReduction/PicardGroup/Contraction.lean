module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contraction
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Defs

/-!
# Picard groups under contraction of a minus-one component

Contracting a minus-one index gives an injection of the Picard group of the
numerical type into the Picard group of its contraction, and the image contains
twice every element of the target, so the cokernel is an elementary abelian
2-group.

## Main definitions

* `AlgebraicGeometry.NumericalType.contractPicardRepresentative`: the
  representative in `ℤ^n` of the image of a class.
* `AlgebraicGeometry.NumericalType.contractPicardMap`: the induced homomorphism
  of Picard groups.

## Main results

* `AlgebraicGeometry.NumericalType.contractPicardMap_mk` computes it on
  representatives.
* `AlgebraicGeometry.NumericalType.contractPicardMap_injective`.
* `AlgebraicGeometry.NumericalType.two_smul_mem_contractPicardMap_range`: the
  cokernel is an elementary abelian 2-group.

## References

* [Stacks Project, Tag 0C7J](https://stacks.math.columbia.edu/tag/0C7J)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The coordinate map `p` used to pass from the relation presentation of a
numerical type to that of its contraction. -/
public noncomputable def contractPicardRepresentative (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (x : Fin T.componentCount → ℤ) :
    Fin (contractLast T h).val.componentCount → ℤ := fun j ↦
  let i : Fin (T.componentCount - 1) :=
    Fin.cast (contractLast T h).property.componentCount_eq j
  x (lastIndex T) *
      (T.intersection (lastIndex T) (remainingIndex T i) /
        (contractLast T h).val.weight j) +
    x (remainingIndex T i) *
      (T.weight (remainingIndex T i) / (contractLast T h).val.weight j)

/-- The coordinate map `p` (`contractPicardRepresentative`) as a `ℤ`-linear map. -/
noncomputable def contractPicardLinearMap (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    (Fin T.componentCount → ℤ) →ₗ[ℤ]
      (Fin (contractLast T h).val.componentCount → ℤ) where
  toFun := contractPicardRepresentative T h
  map_add' x y := by
    funext j
    simp only [contractPicardRepresentative, Pi.add_apply]
    ring
  map_smul' a x := by
    funext j
    simp only [contractPicardRepresentative, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The projection `q : ℤ^n → ℤ^(n-1)` forgetting the coordinate at the contracted (last) index. -/
noncomputable def contractProjectionLinearMap (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    (Fin T.componentCount → ℤ) →ₗ[ℤ]
      (Fin (contractLast T h).val.componentCount → ℤ) where
  toFun x j :=
    x (remainingIndex T (Fin.cast (contractLast T h).property.componentCount_eq j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `contractPicardLinearMap` is `contractPicardRepresentative` on elements. -/
theorem contractPicardRepresentative_linearMap (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) (x : Fin T.componentCount → ℤ) :
    contractPicardLinearMap T h x = contractPicardRepresentative T h x := rfl

/-- The projection `q` kills the basis vector of the contracted (last) index. -/
theorem contractProjectionLinearMap_single_last (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    contractProjectionLinearMap T h (Pi.single (lastIndex T) 1) = 0 := by
  funext j
  change (Pi.single (lastIndex T) 1)
    (remainingIndex T (Fin.cast (contractLast T h).property.componentCount_eq j)) = 0
  simp [remainingIndex_ne_lastIndex T _]

/-- At a remaining index `i`, if `aᵢₙ / wₙ` is even and `aᵢₙ / wᵢ` is odd, then `wᵢ` is even. -/
theorem contraction_oldWeight_even_of_halving (T : NumericalType)
    (_h : IsMinusOneIndex T (lastIndex T)) (i : Fin (T.componentCount - 1))
    (hc : Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
      Odd (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (remainingIndex T i))) :
    Even (T.weight (remainingIndex T i)) :=
  halving_implies_even_weight _ _ _ (intersection_remaining_last_quotient T i)
    (intersection_remaining_own_weight_quotient T i) hc

/-- The weight at the second index divides the intersection number. -/
private theorem weight_dvd_intersection_right (T : NumericalType) (i j : Fin T.componentCount) :
    T.weight j ∣ T.intersection i j := by
  rw [T.intersection_symm]
  exact T.weight_dvd_intersection j i

/-- At a minus-one index the self-intersection divided by the weight is `-1`. -/
private theorem intersection_last_div_weight (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    T.intersection (lastIndex T) (lastIndex T) / T.weight (lastIndex T) = -1 := by
  rw [h.2, Int.neg_ediv_of_dvd (dvd_refl _), Int.ediv_self (T.weight_pos _).ne']

/-- Dividing `a` by `wi` and then `wi` by `wp` is dividing `a` by `wp`. -/
private theorem ediv_mul_ediv_of_dvd {a wi wp : ℤ} (hwi : wi ∣ a) (hwp : wp ∣ wi) :
    a / wi * (wi / wp) = a / wp := by
  rw [← Int.mul_ediv_assoc _ hwp, Int.ediv_mul_cancel_of_dvd hwi]

/-- The integer identity behind the compatibility of `p` with the relations at a remaining
index. -/
private theorem ediv_relation_remaining {a b c t wi wn wp : ℤ} (hwi : wi ∣ a) (hbn : wn ∣ b)
    (hcn : wn ∣ c) (hwpc : wp ∣ c) (hwpi : wp ∣ wi) (hwp0 : wp ≠ 0)
    (ht : t = a + b * (c / wn)) (htarget : wp ∣ t) :
    b / wn * (c / wp) + a / wi * (wi / wp) = t / wp := by
  apply mul_left_cancel₀ hwp0
  rw [Int.mul_ediv_cancel_of_dvd htarget, ht]
  linear_combination (b / wn) * Int.mul_ediv_cancel_of_dvd hwpc +
    (a / wi) * Int.mul_ediv_cancel_of_dvd hwpi + Int.mul_ediv_cancel_of_dvd hwi -
    (b / wn) * Int.mul_ediv_cancel_of_dvd hcn + (c / wn) * Int.mul_ediv_cancel_of_dvd hbn

/-- The coordinate at a remaining index of an element of the kernel of `p`. -/
private theorem coord_eq_of_ediv {xn xi a wi wp : ℤ} (hwpa : wp ∣ a) (hwpi : wp ∣ wi)
    (hwia : wi ∣ a) (hwi0 : wi ≠ 0) (hc : xn * (a / wp) + xi * (wi / wp) = 0) :
    xi = -(a / wi) * xn := by
  apply mul_left_cancel₀ hwi0
  linear_combination wp * hc - xn * Int.mul_ediv_cancel_of_dvd hwpa -
    xi * Int.mul_ediv_cancel_of_dvd hwpi + xn * Int.mul_ediv_cancel_of_dvd hwia

/-- An element whose remaining coordinates are determined by its last one is a relation. -/
private theorem mem_range_picardRelationMap_of_coord (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) (x : Fin T.componentCount → ℤ)
    (hcoord : ∀ i : Fin (T.componentCount - 1), x (remainingIndex T i) =
      -(T.intersection (lastIndex T) (remainingIndex T i) /
        T.weight (remainingIndex T i)) * x (lastIndex T)) :
    x ∈ LinearMap.range (picardRelationMap T) := by
  refine ⟨-x (lastIndex T) •
    Pi.single (M := fun _ : Fin T.componentCount => ℤ) (lastIndex T) (1 : ℤ), ?_⟩
  funext k
  rw [LinearMap.map_smul, picardRelationMap_single]
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases eq_lastIndex_or_eq_remainingIndex T k with hk | ⟨i, rfl⟩
  · subst hk
    rw [intersection_last_div_weight T h]
    ring
  · rw [hcoord i]
    ring

/-- The compatibility `p ∘ R = R' ∘ q` of linear maps out of `ℤ^n`, checked on the basis vectors of
the last and the remaining indices. -/
private theorem comp_eq_of_single (T : NumericalType) {m : ℕ}
    (R : (Fin T.componentCount → ℤ) →ₗ[ℤ] (Fin T.componentCount → ℤ))
    (R' : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℤ)) (p q : (Fin T.componentCount → ℤ) →ₗ[ℤ] (Fin m → ℤ))
    (hq : q (Pi.single (lastIndex T) 1) = 0) (hlast : p (R (Pi.single (lastIndex T) 1)) = 0)
    (hrem : ∀ i : Fin (T.componentCount - 1),
      p (R (Pi.single (remainingIndex T i) 1)) = R' (q (Pi.single (remainingIndex T i) 1))) :
    p.comp R = R'.comp q := by
  apply LinearMap.pi_ext (R := ℤ) (φ := fun _ : Fin T.componentCount => ℤ)
  intro k z
  change p (R (Pi.single k z)) = R' (q (Pi.single k z))
  have hsingle : Pi.single (M := fun _ : Fin T.componentCount => ℤ) k z =
      z • Pi.single (M := fun _ : Fin T.componentCount => ℤ) k 1 := by
    funext j
    simp [Pi.single_apply]
  rw [hsingle]
  simp only [LinearMap.map_smul]
  rcases eq_lastIndex_or_eq_remainingIndex T k with hk | ⟨i, rfl⟩
  · rw [hk, hlast, hq]
    simp
  · rw [hrem]

/-- A compatibility `p ∘ R = R' ∘ q` gives `range R ≤ (range R').comap p`. -/
private theorem range_le_comap_of_comp {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {R : M →ₗ[ℤ] M} {R' : N →ₗ[ℤ] N} {p q : M →ₗ[ℤ] N} (hcomp : p.comp R = R'.comp q) :
    LinearMap.range R ≤ (LinearMap.range R').comap p := by
  rintro _ ⟨x, rfl⟩
  exact ⟨q x, (LinearMap.congr_fun hcomp x).symm⟩

/-- Injectivity of the map of cokernels induced by `p`, when `p ∘ R = R' ∘ q`, `q` is surjective
and the kernel of `p` lies in the range of `R`. -/
private theorem mapQ_range_injective {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {R : M →ₗ[ℤ] M} {R' : N →ₗ[ℤ] N} {p q : M →ₗ[ℤ] N} (hcomp : p.comp R = R'.comp q)
    (hq : Function.Surjective q) (hker : ∀ x, p x = 0 → x ∈ LinearMap.range R)
    (hle : LinearMap.range R ≤ (LinearMap.range R').comap p) :
    Function.Injective ((LinearMap.range R).mapQ (LinearMap.range R') p hle) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range R) a
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range R) b
  have hab' : Submodule.Quotient.mk (p := LinearMap.range R') (p x) =
      Submodule.Quotient.mk (p := LinearMap.range R') (p y) := hab
  obtain ⟨t, ht⟩ := (Submodule.Quotient.eq _).1 hab'
  obtain ⟨z, hz⟩ := hq t
  have hker' : p (x - y - R z) = 0 := by
    rw [map_sub, map_sub, show p (R z) = R' (q z) from LinearMap.congr_fun hcomp z, hz, ht]
    simp
  have hxy : x - y ∈ LinearMap.range R := by
    simpa using (LinearMap.range R).add_mem (hker _ hker') ⟨z, rfl⟩
  exact (Submodule.Quotient.eq _).2 hxy

/-- The weight of the contraction at a remaining index divides the original weight there. -/
theorem contractPicardTargetWeight_dvd_old (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    (contractLast T h).val.weight
      (Fin.cast (contractLast T h).property.componentCount_eq.symm i) ∣
        T.weight (remainingIndex T i) :=
  (contractLast T h).property.isContractionUpToWeight.weight_dvd i

/-- The weight of the contraction at a remaining index `i` divides the intersection number
`aₙᵢ`. -/
theorem contractPicardTargetWeight_dvd_incidence (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    (contractLast T h).val.weight
      (Fin.cast (contractLast T h).property.componentCount_eq.symm i) ∣
        T.intersection (lastIndex T) (remainingIndex T i) :=
  (contractPicardTargetWeight_dvd_old T h i).trans (weight_dvd_intersection_right T _ _)

/-- The index of the contraction corresponding to a remaining index of `T`. -/
noncomputable def contractedIndex (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) (i : Fin (T.componentCount - 1)) :
    Fin (contractLast T h).val.componentCount :=
  Fin.cast (contractLast T h).property.componentCount_eq.symm i

/-- `contractedIndex` is injective. -/
theorem contractedIndex_injective (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    Function.Injective (contractedIndex T h) := fun _ _ hij =>
  Fin.ext (by simpa [contractedIndex] using congrArg Fin.val hij)

/-- `contractedIndex` is a left inverse of the cast from indices of the contraction to remaining
indices of `T`. -/
theorem contractedIndex_cast (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (j : Fin (contractLast T h).val.componentCount) :
    contractedIndex T h (Fin.cast (contractLast T h).property.componentCount_eq j) = j :=
  Fin.ext rfl

/-- The projection `q` sends the basis vector of a remaining index `i` to the basis vector of the
corresponding index of the contraction. -/
theorem contractProjectionLinearMap_single_remaining (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) (i : Fin (T.componentCount - 1)) :
    contractProjectionLinearMap T h (Pi.single (remainingIndex T i) 1) =
      Pi.single (contractedIndex T h i) 1 := by
  funext j
  have hidx : remainingIndex T
      (Fin.cast (contractLast T h).property.componentCount_eq j) = remainingIndex T i ↔
      j = contractedIndex T h i := by
    constructor <;> intro hij <;>
      exact Fin.ext (by simpa [remainingIndex, contractedIndex] using congrArg Fin.val hij)
  simp [contractProjectionLinearMap, Pi.single_apply, hidx]

/-- The value of `contractPicardRepresentative` at the index corresponding to a remaining index
`i`: `xₙ aₙᵢ / w'ᵢ + xᵢ wᵢ / w'ᵢ`. -/
theorem contractPicardRepresentative_at (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) (x : Fin T.componentCount → ℤ)
    (i : Fin (T.componentCount - 1)) :
    contractPicardRepresentative T h x (contractedIndex T h i) =
      x (lastIndex T) *
          (T.intersection (lastIndex T) (remainingIndex T i) /
            (contractLast T h).val.weight (contractedIndex T h i)) +
        x (remainingIndex T i) *
          (T.weight (remainingIndex T i) /
            (contractLast T h).val.weight (contractedIndex T h i)) := by
  simp [contractPicardRepresentative, contractedIndex]

/-- The intersection numbers of the contraction: `a'ᵢⱼ = aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)` at remaining indices
`i`, `j`. -/
theorem contractIntersection_eq_int (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i j : Fin (T.componentCount - 1)) :
    (contractLast T h).val.intersection (contractedIndex T h i)
        (contractedIndex T h j) =
      T.intersection (remainingIndex T i) (remainingIndex T j) +
        T.intersection (remainingIndex T i) (lastIndex T) *
          (T.intersection (remainingIndex T j) (lastIndex T) /
            T.weight (lastIndex T)) := by
  let a := T.intersection (remainingIndex T i) (remainingIndex T j)
  let b := T.intersection (remainingIndex T i) (lastIndex T)
  let c := T.intersection (remainingIndex T j) (lastIndex T)
  let w := T.weight (lastIndex T)
  have hdiv : w ∣ c := weight_dvd_intersection_right T _ _
  have hformula :
      ((contractLast T h).val.intersection (contractedIndex T h i)
        (contractedIndex T h j) : ℚ) =
        ((a + b * (c / w) : ℤ) : ℚ) := by
    dsimp [contractedIndex]
    rw [(contractLast T h).property.intersection_eq i j, h.2]
    push_cast
    rw [Int.cast_div_charZero hdiv]
    simp [div_neg]
    ring
  exact Int.cast_injective (α := ℚ) (by simpa [a, b, c, w] using hformula)

/-- The map `p` kills the relation of the contracted (last) index. -/
theorem contractPicardLinearMap_relation_last (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    contractPicardLinearMap T h
      (picardRelationMap T (Pi.single (lastIndex T) 1)) = 0 := by
  funext j
  let i := Fin.cast (contractLast T h).property.componentCount_eq j
  rw [← contractedIndex_cast T h j]
  change contractPicardRepresentative T h
    (picardRelationMap T (Pi.single (lastIndex T) 1)) (contractedIndex T h i) = 0
  rw [contractPicardRepresentative_at]
  simp only [picardRelationMap_single]
  have hnewWeightDiv : (contractLast T h).val.weight (contractedIndex T h i) ∣
      T.weight (remainingIndex T i) := by
    simpa [contractedIndex] using contractPicardTargetWeight_dvd_old T h i
  rw [intersection_last_div_weight T h,
    ediv_mul_ediv_of_dvd (weight_dvd_intersection_right T _ _) hnewWeightDiv]
  ring

/-- The map `p` sends the relation of a remaining index `i` to the relation of the corresponding
index of the contraction. -/
theorem contractPicardLinearMap_relation_remaining (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    contractPicardLinearMap T h
      (picardRelationMap T (Pi.single (remainingIndex T i) 1)) =
    picardRelationMap (contractLast T h).val
      (Pi.single (contractedIndex T h i) 1) := by
  funext j
  let k := Fin.cast (contractLast T h).property.componentCount_eq j
  rw [← contractedIndex_cast T h j]
  change contractPicardRepresentative T h
      (picardRelationMap T (Pi.single (remainingIndex T i) 1))
      (contractedIndex T h k) =
    picardRelationMap (contractLast T h).val
      (Pi.single (contractedIndex T h i) 1) (contractedIndex T h k)
  rw [contractPicardRepresentative_at, picardRelationMap_single T (remainingIndex T i),
    picardRelationMap_single (contractLast T h).val (contractedIndex T h i)]
  dsimp
  have hwpi : (contractLast T h).val.weight (contractedIndex T h k) ∣
      T.weight (remainingIndex T k) := by
    simpa [contractedIndex] using contractPicardTargetWeight_dvd_old T h k
  rw [T.intersection_symm (lastIndex T) (remainingIndex T k)]
  exact ediv_relation_remaining (weight_dvd_intersection_right T _ _)
    (weight_dvd_intersection_right T _ _) (weight_dvd_intersection_right T _ _)
    (hwpi.trans (T.weight_dvd_intersection _ _)) hwpi
    ((contractLast T h).val.weight_pos _).ne' (contractIntersection_eq_int T h i k)
    (weight_dvd_intersection_right _ _ _)

/-- The square `p ∘ (relations of T) = (relations of the contraction) ∘ q` commutes. -/
theorem contractPicardRelation_compatibility (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    (contractPicardLinearMap T h).comp (picardRelationMap T) =
      (picardRelationMap (contractLast T h).val).comp
        (contractProjectionLinearMap T h) := by
  refine comp_eq_of_single T _ _ _ _ (contractProjectionLinearMap_single_last T h)
    (contractPicardLinearMap_relation_last T h) fun i => ?_
  rw [contractPicardLinearMap_relation_remaining, contractProjectionLinearMap_single_remaining]

/-- The map `p` sends the relations of `T` into the relations of the contraction. -/
theorem contractPicardRelation_range_le_comap (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    LinearMap.range (picardRelationMap T) ≤
      (LinearMap.range (picardRelationMap (contractLast T h).val)).comap
        (contractPicardLinearMap T h) := by
  exact range_le_comap_of_comp (contractPicardRelation_compatibility T h)

/-- The projection `q` is surjective. -/
theorem contractProjectionLinearMap_surjective (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    Function.Surjective (contractProjectionLinearMap T h) := by
  intro y
  refine ⟨∑ i : Fin (T.componentCount - 1),
      y (contractedIndex T h i) • Pi.single (remainingIndex T i) 1, ?_⟩
  simp only [map_sum, map_smul, contractProjectionLinearMap_single_remaining]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  let i₀ := Fin.cast (contractLast T h).property.componentCount_eq j
  have hj₀ : contractedIndex T h i₀ = j := contractedIndex_cast T h j
  rw [Finset.sum_eq_single i₀]
  · simp [hj₀]
  · intro i hi hne
    have hji : j ≠ contractedIndex T h i := fun hji =>
      hne (contractedIndex_injective T h (hji.symm.trans hj₀.symm))
    simp [hji]
  · simp

/-- On the kernel of `p`, the coordinate at a remaining index `i` is `-(aₙᵢ / wᵢ) xₙ`. -/
theorem contractPicardLinearMap_kernel_coord (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (x : Fin T.componentCount → ℤ)
    (hx : contractPicardLinearMap T h x = 0)
    (i : Fin (T.componentCount - 1)) :
    x (remainingIndex T i) =
      -(T.intersection (lastIndex T) (remainingIndex T i) /
        T.weight (remainingIndex T i)) * x (lastIndex T) := by
  have hc := congrFun hx (contractedIndex T h i)
  change contractPicardRepresentative T h x (contractedIndex T h i) = 0 at hc
  rw [contractPicardRepresentative_at] at hc
  exact coord_eq_of_ediv (contractPicardTargetWeight_dvd_incidence T h i)
    (by simpa [contractedIndex] using contractPicardTargetWeight_dvd_old T h i)
    (weight_dvd_intersection_right T _ _) (T.weight_pos _).ne' hc

/-- The kernel of `p` lies in the relations of `T`. -/
theorem contractPicardLinearMap_ker_le_range (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (x : Fin T.componentCount → ℤ)
    (hx : contractPicardLinearMap T h x = 0) :
    x ∈ LinearMap.range (picardRelationMap T) := by
  exact mem_range_picardRelationMap_of_coord T h x (contractPicardLinearMap_kernel_coord T h x hx)

/-- The ratio `wᵢ / w'ᵢ` of the weights at a remaining index `i` is `1` or `2`. -/
theorem contractPicardWeightRatio_one_or_two (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    T.weight (remainingIndex T i) /
        (contractLast T h).val.weight (contractedIndex T h i) = 1 ∨
      T.weight (remainingIndex T i) /
        (contractLast T h).val.weight (contractedIndex T h i) = 2 := by
  let wi := T.weight (remainingIndex T i)
  let wp := (contractLast T h).val.weight (contractedIndex T h i)
  have hweight := (contractLast T h).property.weight_eq i
  by_cases hc : Even (T.intersection (remainingIndex T i) (lastIndex T) /
      T.weight (lastIndex T)) ∧
      Odd (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (remainingIndex T i))
  · have heven := contraction_oldWeight_even_of_halving T h i hc
    have hdiv : 2 ∣ wi := by simpa [wi] using even_iff_two_dvd.mp heven
    have hweight' : wp = wi / 2 := by
      simpa [wp, wi, contractedIndex] using (hweight.trans (ite_eq_left hc))
    have hpos : 0 < wi / 2 := hweight' ▸ (contractLast T h).val.weight_pos _
    right
    have hratio : wi / (wi / 2) = 2 := by
      calc
        wi / (wi / 2) = (wi / 2 * 2) / (wi / 2) := by rw [Int.ediv_mul_cancel_of_dvd hdiv]
        _ = 2 := Int.mul_ediv_cancel_left 2 hpos.ne'
    simpa [wi, wp, contractedIndex, hweight, hc] using hratio
  · left
    have hwi0 : wi ≠ 0 := (T.weight_pos _).ne'
    simpa [wi, wp, contractedIndex, hweight, hc] using Int.ediv_self hwi0

/-- The map `p` sends the basis vector of a remaining index `i` to `wᵢ / w'ᵢ` times the basis
vector of the corresponding index of the contraction. -/
theorem contractPicardLinearMap_single_remaining (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    contractPicardLinearMap T h (Pi.single (remainingIndex T i) 1) =
      fun j => if j = contractedIndex T h i then
        T.weight (remainingIndex T i) /
          (contractLast T h).val.weight j else 0 := by
  funext j
  let k := Fin.cast (contractLast T h).property.componentCount_eq j
  rw [← contractedIndex_cast T h j]
  change contractPicardRepresentative T h
      (Pi.single (remainingIndex T i) 1) (contractedIndex T h k) = _
  rw [contractPicardRepresentative_at]
  have hrem : remainingIndex T k = remainingIndex T i ↔ k = i :=
    (remainingIndex_injective T).eq_iff
  rw [contractedIndex_cast T h j]
  have hjcond : j = contractedIndex T h i ↔ k = i := by
    rw [← contractedIndex_cast T h j]
    exact (contractedIndex_injective T h).eq_iff
  simp [Pi.single_apply, remainingIndex_ne_lastIndex, hrem]
  by_cases hji : j = contractedIndex T h i
  · simp [hji, hjcond.mp hji]
  · have hki : k ≠ i := fun hk => hji (hjcond.mpr hk)
    simp [hji, hki]

/-- The Picard-group homomorphism induced by contracting the final minus-one
component. -/
@[stacks 0C7J "the induced homomorphism"]
public noncomputable def contractPicardMap (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    picardGroup T →+ picardGroup (contractLast T h).val := by
  let p := contractPicardLinearMap T h
  exact ((LinearMap.range (picardRelationMap T)).mapQ
    (LinearMap.range (picardRelationMap (contractLast T h).val)) p
    (by simpa [p] using contractPicardRelation_range_le_comap T h)).toAddMonoidHom

/-- On cokernel representatives, the contraction homomorphism is induced by the
coordinate map `p`. -/
@[stacks 0C7J "formula on representatives"]
public theorem contractPicardMap_mk (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (x : Fin T.componentCount → ℤ) :
    contractPicardMap T h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (contractPicardRepresentative T h x) := by
  simp [contractPicardMap, Submodule.mapQ_apply, contractPicardLinearMap]

/-- Contraction of a minus-one component induces an injection on Picard groups. -/
@[stacks 0C7J "injectivity"]
public theorem contractPicardMap_injective (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    Function.Injective (contractPicardMap T h) := by
  exact mapQ_range_injective (contractPicardRelation_compatibility T h)
    (contractProjectionLinearMap_surjective T h) (contractPicardLinearMap_ker_le_range T h)
    (contractPicardRelation_range_le_comap T h)

/-- At a remaining index `i`: `2` if the weight ratio `wᵢ / w'ᵢ` is `1`, and `1` otherwise. -/
noncomputable def contractPicardLiftScale (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) : ℤ :=
  if T.weight (remainingIndex T i) /
      (contractLast T h).val.weight (contractedIndex T h i) = 1 then 2 else 1

/-- `contractPicardLiftScale` times the weight ratio `wᵢ / w'ᵢ` is `2`. -/
theorem contractPicardLiftScale_mul_ratio (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    contractPicardLiftScale T h i *
        (T.weight (remainingIndex T i) /
          (contractLast T h).val.weight (contractedIndex T h i)) = 2 := by
  rcases contractPicardWeightRatio_one_or_two T h i with hratio | hratio <;>
    simp [contractPicardLiftScale, hratio]

/-- A preimage under `p` of `2 • y`, supported on the remaining indices. -/
noncomputable def contractPicardTwoPreimage (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (y : Fin (contractLast T h).val.componentCount → ℤ) :
    Fin T.componentCount → ℤ :=
  ∑ i : Fin (T.componentCount - 1),
    (contractPicardLiftScale T h i * y (contractedIndex T h i)) •
      Pi.single (remainingIndex T i) 1

/-- `contractPicardTwoPreimage T h y` is a preimage of `2 • y` under `p`. -/
theorem contractPicardLinearMap_two_preimage (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (y : Fin (contractLast T h).val.componentCount → ℤ) :
    contractPicardLinearMap T h (contractPicardTwoPreimage T h y) = 2 • y := by
  simp only [contractPicardTwoPreimage, map_sum, map_smul,
    contractPicardLinearMap_single_remaining]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let k := Fin.cast (contractLast T h).property.componentCount_eq j
  have hj : contractedIndex T h k = j := contractedIndex_cast T h j
  rw [Finset.sum_eq_single k]
  · rw [hj]
    simp only
    have hweight : (contractLast T h).val.weight j =
        (contractLast T h).val.weight (contractedIndex T h k) :=
      (congrArg (fun q => (contractLast T h).val.weight q) hj).symm
    rw [hweight]
    calc
      contractPicardLiftScale T h k * y j *
          (T.weight (remainingIndex T k) /
            (contractLast T h).val.weight (contractedIndex T h k)) =
        (contractPicardLiftScale T h k *
          (T.weight (remainingIndex T k) /
            (contractLast T h).val.weight (contractedIndex T h k))) * y j := by ring
      _ = 2 • y j := by
        rw [contractPicardLiftScale_mul_ratio]
        simp
  · intro i hi hne
    have hji : j ≠ contractedIndex T h i := fun hji =>
      hne (contractedIndex_injective T h (hji.symm.trans hj.symm))
    simp [hji]
  · simp

/-- The cokernel of the Picard-group map induced by contraction has exponent two. -/
@[stacks 0C7J "elementary abelian two-group cokernel"]
public theorem two_smul_mem_contractPicardMap_range (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (x : picardGroup (contractLast T h).val) :
    2 • x ∈ (contractPicardMap T h).range := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (picardRelationMap (contractLast T h).val)) x
  refine ⟨Submodule.Quotient.mk (contractPicardTwoPreimage T h y), ?_⟩
  rw [contractPicardMap_mk, ← contractPicardRepresentative_linearMap T h
    (contractPicardTwoPreimage T h y), contractPicardLinearMap_two_preimage]
  change Submodule.Quotient.mk (2 • y) = 2 • Submodule.Quotient.mk y
  exact map_smul (Submodule.mkQ
    (LinearMap.range (picardRelationMap (contractLast T h).val))) (2 : ℤ) y

/-! ### Contractions with smaller weights -/

namespace IsContractionUpToWeight

variable {T T' : NumericalType} (hT : IsContractionUpToWeight T T')

/-- The index of `T` that a component of a contraction up to weight comes from. -/
def oldIndex (j : Fin T'.componentCount) : Fin (T.componentCount - 1) :=
  Fin.cast hT.componentCount_eq j

/-- The component of a contraction up to weight that an index of `T` goes to. -/
def newIndex (i : Fin (T.componentCount - 1)) : Fin T'.componentCount :=
  Fin.cast hT.componentCount_eq.symm i

/-- `newIndex` is a left inverse of `oldIndex`. -/
theorem newIndex_oldIndex (j : Fin T'.componentCount) : hT.newIndex (hT.oldIndex j) = j :=
  Fin.ext rfl

/-- `newIndex` is injective. -/
theorem newIndex_injective : Function.Injective hT.newIndex := fun _ _ hij =>
  Fin.ext (by simpa [newIndex] using congrArg Fin.val hij)

/-- `oldIndex j = i` if and only if `j = newIndex i`. -/
theorem oldIndex_eq_iff (j : Fin T'.componentCount) (i : Fin (T.componentCount - 1)) :
    hT.oldIndex j = i ↔ j = hT.newIndex i := by
  constructor
  · rintro rfl
    exact (hT.newIndex_oldIndex j).symm
  · rintro rfl
    rfl

/-- The weight of `T'` at `newIndex i` divides the weight of `T` at the remaining index `i`. -/
theorem weight_newIndex_dvd (i : Fin (T.componentCount - 1)) :
    T'.weight (hT.newIndex i) ∣ T.weight (remainingIndex T i) :=
  hT.weight_dvd i

/-- The weight of `T'` at `newIndex i` divides the intersection number `aₙᵢ`. -/
theorem weight_dvd_incidence (i : Fin (T.componentCount - 1)) :
    T'.weight (hT.newIndex i) ∣ T.intersection (lastIndex T) (remainingIndex T i) :=
  (hT.weight_newIndex_dvd i).trans (weight_dvd_intersection_right T _ _)

/-- The coordinate map `p` of Tag 0C7J, at the weights of a contraction up to weight. -/
noncomputable def picardLinearMap :
    (Fin T.componentCount → ℤ) →ₗ[ℤ] (Fin T'.componentCount → ℤ) where
  toFun x j :=
    x (lastIndex T) *
        (T.intersection (lastIndex T) (remainingIndex T (hT.oldIndex j)) / T'.weight j) +
      x (remainingIndex T (hT.oldIndex j)) *
        (T.weight (remainingIndex T (hT.oldIndex j)) / T'.weight j)
  map_add' x y := by
    funext j
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The value of `picardLinearMap` at `newIndex i`: `xₙ aₙᵢ / w'ᵢ + xᵢ wᵢ / w'ᵢ`. -/
theorem picardLinearMap_apply (x : Fin T.componentCount → ℤ)
    (i : Fin (T.componentCount - 1)) :
    hT.picardLinearMap x (hT.newIndex i) =
      x (lastIndex T) *
          (T.intersection (lastIndex T) (remainingIndex T i) / T'.weight (hT.newIndex i)) +
        x (remainingIndex T i) *
          (T.weight (remainingIndex T i) / T'.weight (hT.newIndex i)) := rfl

/-- The projection `q` of Tag 0C7J, forgetting the last coordinate. -/
def projectionLinearMap :
    (Fin T.componentCount → ℤ) →ₗ[ℤ] (Fin T'.componentCount → ℤ) where
  toFun x j := x (remainingIndex T (hT.oldIndex j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection `q` kills the basis vector of the last index. -/
theorem projectionLinearMap_single_last :
    hT.projectionLinearMap (Pi.single (lastIndex T) 1) = 0 := by
  funext j
  change (Pi.single (lastIndex T) 1 : Fin T.componentCount → ℤ)
    (remainingIndex T (hT.oldIndex j)) = 0
  simp [remainingIndex_ne_lastIndex T (hT.oldIndex j)]

/-- The projection `q` sends the basis vector of a remaining index `i` to that of `newIndex i`. -/
theorem projectionLinearMap_single_remaining (i : Fin (T.componentCount - 1)) :
    hT.projectionLinearMap (Pi.single (remainingIndex T i) 1) =
      Pi.single (hT.newIndex i) 1 := by
  funext j
  rw [← hT.newIndex_oldIndex j]
  change (Pi.single (remainingIndex T i) 1 : Fin T.componentCount → ℤ)
    (remainingIndex T (hT.oldIndex j)) = _
  simp only [Pi.single_apply, (remainingIndex_injective T).eq_iff, hT.oldIndex_eq_iff,
    hT.newIndex_oldIndex]

/-- The projection `q` is surjective. -/
theorem projectionLinearMap_surjective : Function.Surjective hT.projectionLinearMap := by
  intro y
  refine ⟨fun k => if hk : k = lastIndex T then 0 else
    y (hT.newIndex ⟨k.val, by
      have := k.isLt
      have : k.val ≠ T.componentCount - 1 := fun hv => hk (Fin.ext hv)
      omega⟩), ?_⟩
  funext j
  change (if hk : remainingIndex T (hT.oldIndex j) = lastIndex T then 0 else _) = y j
  rw [dite_eq_right (remainingIndex_ne_lastIndex T _)]
  rfl

/-- The intersection numbers of `T'`: `a'ᵢⱼ = aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)` at remaining indices `i`,
`j`. -/
theorem intersection_newIndex (h : IsMinusOneIndex T (lastIndex T))
    (i j : Fin (T.componentCount - 1)) :
    T'.intersection (hT.newIndex i) (hT.newIndex j) =
      T.intersection (remainingIndex T i) (remainingIndex T j) +
        T.intersection (remainingIndex T i) (lastIndex T) *
          (T.intersection (remainingIndex T j) (lastIndex T) / T.weight (lastIndex T)) := by
  have hq := hT.intersection_eq i j
  rw [← contractedIntersection_cast T h i j] at hq
  exact_mod_cast hq

/-- The map `p` kills the relation of the last index. -/
theorem picardLinearMap_relation_last (h : IsMinusOneIndex T (lastIndex T)) :
    hT.picardLinearMap (picardRelationMap T (Pi.single (lastIndex T) 1)) = 0 := by
  funext j
  rw [← hT.newIndex_oldIndex j, picardLinearMap_apply]
  simp only [picardRelationMap_single]
  set i := hT.oldIndex j
  rw [intersection_last_div_weight T h,
    ediv_mul_ediv_of_dvd (weight_dvd_intersection_right T _ _) (hT.weight_newIndex_dvd i)]
  simp

/-- The map `p` sends the relation of a remaining index `i` to the relation of `newIndex i`. -/
theorem picardLinearMap_relation_remaining (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    hT.picardLinearMap (picardRelationMap T (Pi.single (remainingIndex T i) 1)) =
      picardRelationMap T' (Pi.single (hT.newIndex i) 1) := by
  funext j
  rw [← hT.newIndex_oldIndex j, picardLinearMap_apply, picardRelationMap_single T,
    picardRelationMap_single T']
  set k := hT.oldIndex j
  rw [T.intersection_symm (lastIndex T) (remainingIndex T k)]
  exact ediv_relation_remaining (weight_dvd_intersection_right T _ _)
    (weight_dvd_intersection_right T _ _) (weight_dvd_intersection_right T _ _)
    ((hT.weight_newIndex_dvd k).trans (T.weight_dvd_intersection _ _)) (hT.weight_newIndex_dvd k)
    (T'.weight_pos _).ne' (hT.intersection_newIndex h i k)
    (weight_dvd_intersection_right _ _ _)

/-- The square `p ∘ (relations of T) = (relations of T') ∘ q` commutes. -/
theorem picardRelation_compatibility (h : IsMinusOneIndex T (lastIndex T)) :
    hT.picardLinearMap.comp (picardRelationMap T) =
      (picardRelationMap T').comp hT.projectionLinearMap := by
  refine comp_eq_of_single T _ _ _ _ hT.projectionLinearMap_single_last
    (hT.picardLinearMap_relation_last h) fun i => ?_
  rw [hT.picardLinearMap_relation_remaining h, hT.projectionLinearMap_single_remaining]

/-- The kernel of `p` lies in the relations of `T`. -/
theorem picardLinearMap_ker_le_range (h : IsMinusOneIndex T (lastIndex T))
    (x : Fin T.componentCount → ℤ) (hx : hT.picardLinearMap x = 0) :
    x ∈ LinearMap.range (picardRelationMap T) := by
  refine mem_range_picardRelationMap_of_coord T h x fun i => ?_
  have hc := congrFun hx (hT.newIndex i)
  rw [picardLinearMap_apply] at hc
  exact coord_eq_of_ediv (hT.weight_dvd_incidence i) (hT.weight_newIndex_dvd i)
    (weight_dvd_intersection_right T _ _) (T.weight_pos _).ne' hc

/-- The homomorphism of Picard groups induced by a contraction up to weight along a minus-one
index, given on representatives by the map `p` of Tag 0C7J. -/
public noncomputable def picardMap (h : IsMinusOneIndex T (lastIndex T)) :
    picardGroup T →+ picardGroup T' :=
  ((LinearMap.range (picardRelationMap T)).mapQ (LinearMap.range (picardRelationMap T'))
    hT.picardLinearMap (by
      rintro _ ⟨x, rfl⟩
      refine ⟨hT.projectionLinearMap x, ?_⟩
      simpa [LinearMap.comp_apply] using
        (congrArg (fun f => f x) (hT.picardRelation_compatibility h)).symm)).toAddMonoidHom

/-- On representatives, the homomorphism of Picard groups induced by a contraction up to weight
sends `(lᵢ)` to `(lₙaₙᵢ/w'ᵢ + lᵢwᵢ/w'ᵢ)ᵢ`. -/
public theorem picardMap_mk (h : IsMinusOneIndex T (lastIndex T))
    (x : Fin T.componentCount → ℤ) (i : Fin (T.componentCount - 1)) :
    ∃ y : Fin T'.componentCount → ℤ, hT.picardMap h (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk y ∧
      y (Fin.cast hT.componentCount_eq.symm i) =
        x (lastIndex T) * (T.intersection (lastIndex T) (remainingIndex T i) /
            T'.weight (Fin.cast hT.componentCount_eq.symm i)) +
          x (remainingIndex T i) * (T.weight (remainingIndex T i) /
            T'.weight (Fin.cast hT.componentCount_eq.symm i)) :=
  ⟨hT.picardLinearMap x, rfl, rfl⟩

/-- **The injectivity of Tag 0C7J holds for smaller weights.** If `T'` is the contraction of a
minus-one index of `T` in every datum except that its weights `w'ᵢ` are only divisors of `wᵢ`,
the homomorphism `Pic(T) → Pic(T')` induced by `p` is still injective. -/
@[stacks 0CA9 "the injectivity of Pic(T) → Pic(T') of Tag 0C7J works as well for smaller w'_i"]
public theorem picardMap_injective (h : IsMinusOneIndex T (lastIndex T)) :
    Function.Injective (hT.picardMap h) := by
  exact mapQ_range_injective (hT.picardRelation_compatibility h) hT.projectionLinearMap_surjective
    (hT.picardLinearMap_ker_le_range h)
    (range_le_comap_of_comp (hT.picardRelation_compatibility h))

end IsContractionUpToWeight

end AlgebraicGeometry.NumericalType
