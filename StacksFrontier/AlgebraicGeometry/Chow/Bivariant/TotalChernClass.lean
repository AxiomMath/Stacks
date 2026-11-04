module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass

/-!
# The total Chern class of a finite locally free module

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let `ℰ`
be finite locally free of rank `r` on `Y`. Its *total Chern class* is the total Chow cohomology
class

  `c(ℰ) = 1 + c_1(ℰ) + ⋯ + c_r(ℰ)`,

whose degree-`j` component is the bivariant Chern class `c_j(ℰ) ∈ A^j(Y)` of [Stacks, Tag 0B7H]
for `j ≤ r` and zero above. On a test scheme `g : T ⟶ Y` its operation has index-`j` component
`c_j(g^*ℰ) ∩ -`, the cap product of [Stacks, Tag 02U6], and it is a unit of the ring of total
classes, its degree-`0` component being `c_0(ℰ) = 1`.

## Main definitions

* `Stacks.Chow.totalChern` — the total Chern class `c(ℰ)`.

## Main results

* `Stacks.Chow.op_totalChern_apply` — the operation of `c(ℰ)` on a test scheme `g : T ⟶ Y` has
  index-`j` component `c_j(g^*ℰ) ∩ -`.
* `Stacks.Chow.isUnit_totalChern` — `c(ℰ)` is a unit.

## References

* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (F : Y.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-- **The total Chern class** `c(ℰ) = 1 + c_1(ℰ) + ⋯ + c_r(ℰ)` of a finite locally free module of
rank `r`: the total Chow cohomology class whose degree-`j` component is the bivariant Chern class
`c_j(ℰ)` of Stacks 0B7H for `j ≤ r`, and zero for `j > r`. -/
def totalChern : TotalChowClass C sY := fun j ↦
  if h : j < r + 1 then GenuineChern.chernClass C sY F r ⟨j, h⟩ else 0

/-- The degree-`j` component of `c(ℰ)` is `c_j(ℰ)` for `j ≤ r`. -/
theorem totalChern_apply (j : Fin (r + 1)) :
    totalChern C sY F r j = GenuineChern.chernClass C sY F r j :=
  dif_pos j.isLt

/-- The degree-`j` component of `c(ℰ)` vanishes for `j > r`. -/
theorem totalChern_apply_of_lt {j : ℕ} (hj : r < j) : totalChern C sY F r j = 0 :=
  dif_neg (by omega)

/-- **The operation of the total Chern class.** On a test scheme `g : T ⟶ Y`, the index-`j`
component of the operation of `c(ℰ)` is `c_j(g^*ℰ) ∩ -`, for `j ≤ r`. -/
theorem op_totalChern_apply {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (j : Fin (r + 1)) (α : chowGroup C (g ≫ sY) k) :
    letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
    (totalChern C sY F r).op g k j α =
      GenuineChern.chernCap C r (g ≫ sY) ((Scheme.Modules.pullback g).obj F) k j α := by
  rw [TotalChowClass.op_apply, totalChern_apply]
  exact GenuineChern.idRule_chernClass C sY F r j g k α

/-- The index-`j` component of the operation of `c(ℰ)` vanishes for `j > r`. -/
theorem op_totalChern_of_lt {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    {j : ℕ} (hj : r < j) : (totalChern C sY F r).op g k j = 0 := by
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [TotalChowClass.op_apply, totalChern_apply_of_lt C sY F r hj, BivariantClass.idRule_zero]
  rfl

/-- **The total Chern class is a unit** of the ring of total classes: its operation on every test
scheme has index-`0` component `c_0(g^*ℰ) ∩ - = id`. -/
theorem isUnit_totalChern : IsUnit (totalChern C sY F r) := by
  refine TotalChowClass.isUnit_of_op_apply_zero fun g _ k ↦ AddMonoidHom.ext fun α ↦ ?_
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  rw [gradedCap_one_apply_zero]
  refine eq_of_heq ((heq_of_eq (op_totalChern_apply C sY F r g k 0 α)).trans
    ((chowGroupCast_heq C _ (show k - ((0 : Fin (r + 1)) : ℕ) = k by simp) _).symm.trans ?_))
  rw [GenuineChern.chernCap_zero_apply]
  exact (gradedDegreeCast_heq _ α).symm

end Stacks.Chow

end
