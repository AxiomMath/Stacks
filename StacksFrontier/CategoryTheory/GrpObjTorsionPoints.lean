module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The `n`-torsion of the group of points of a commutative group object

Let `G` be a commutative group object in a cartesian monoidal category `C`.  The points
`𝟙_ C ⟶ G` form a commutative group, written additively through `Additive`, and its `n`-torsion
subgroup consists of exactly those points carried to the unit `η[G]` by multiplication by `n`,
that is, by the `n`-th power `(𝟙 G) ^ n` of the identity in the group `G ⟶ G`.

For a group scheme `G` over a field `k` the object `𝟙_ (Over (Spec (.of k)))` is `Spec k` itself,
so `𝟙_ C ⟶ G` is the group of `k`-points of `G`, and the subtype appearing here is the set of
`k`-points of the kernel of multiplication by `n`: it is the fibre of `(𝟙 G) ^ n` over the unit
section.  This is the bridge between the `n`-torsion of the abstract group of points and the
geometry of multiplication by `n`.

## Main results

* `CategoryTheory.GrpObj.mem_torsionBy_additive_points_iff`: a point lies in the `n`-torsion of
  the group of points exactly when multiplication by `n` sends it to the unit section.
* `CategoryTheory.GrpObj.torsionByAdditivePointsEquiv`: the resulting bijection between the
  `n`-torsion subgroup of the group of points and the points killed by `(𝟙 G) ^ n`.
* `CategoryTheory.GrpObj.card_torsionBy_additive_points`: the two have the same cardinality.
-/

@[expose] public section

universe v u

namespace CategoryTheory.GrpObj

open scoped CategoryTheory.MonObj

open CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (G : C) [GrpObj G] [IsCommMonObj G]

/-- A point of a commutative group object lies in the `n`-torsion of the group of points exactly
when multiplication by `n` carries it to the unit section. -/
theorem mem_torsionBy_additive_points_iff (n : ℕ) (p : 𝟙_ C ⟶ G) :
    Additive.ofMul p ∈ Submodule.torsionBy ℤ (Additive (𝟙_ C ⟶ G)) (n : ℤ) ↔
      p ≫ (𝟙 G : G ⟶ G) ^ (n : ℤ) = η[G] := by
  have hone : (1 : 𝟙_ C ⟶ G) = η[G] := by
    simp [_root_.CategoryTheory.Hom.one_def]
  rw [Submodule.mem_torsionBy_iff, GrpObj.comp_zpow, Category.comp_id, zpow_natCast, ← hone,
    Nat.cast_smul_eq_nsmul ℤ n (Additive.ofMul p)]
  exact ⟨fun h => Additive.ofMul.injective h, fun h => congrArg Additive.ofMul h⟩

/-- The `n`-torsion subgroup of the group of points of a commutative group object is in bijection
with the points that multiplication by `n` carries to the unit section. -/
def torsionByAdditivePointsEquiv (n : ℕ) :
    Submodule.torsionBy ℤ (Additive (𝟙_ C ⟶ G)) (n : ℤ) ≃
      {p : 𝟙_ C ⟶ G // p ≫ (𝟙 G : G ⟶ G) ^ (n : ℤ) = η[G]} where
  toFun x := ⟨Additive.toMul x.1, (mem_torsionBy_additive_points_iff G n _).mp x.2⟩
  invFun p := ⟨Additive.ofMul p.1, (mem_torsionBy_additive_points_iff G n _).mpr p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `n`-torsion of the group of points has as many elements as the set of points that
multiplication by `n` carries to the unit section. -/
theorem card_torsionBy_additive_points (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (Additive (𝟙_ C ⟶ G)) (n : ℤ))
      = Nat.card {p : 𝟙_ C ⟶ G // p ≫ (𝟙 G : G ⟶ G) ^ (n : ℤ) = η[G]} :=
  Nat.card_congr (torsionByAdditivePointsEquiv G n)

end CategoryTheory.GrpObj
