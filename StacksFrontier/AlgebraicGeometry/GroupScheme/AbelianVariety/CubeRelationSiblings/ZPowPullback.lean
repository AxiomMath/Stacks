module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.FibreSubgroup

/-!
# The class of `[n]^*L` from the cube relation alone

The closed form of the class of `[n]^*L` in `Pic(A)`
(`Stacks.Groupoids.zpowIdPicardClass_eq`, the Picard-group form of
[Stacks, Tag 0BFF](https://stacks.math.columbia.edu/tag/0BFF)) is proved in
`StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianVariety/ZPowPullback.lean` from
`HasTheoremOfTheCube A`, which it uses only through the cube relation of
[Stacks, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE)
(`Stacks.Groupoids.pullbackPicardClass_cubeRelation`). This file states that relation as the
property `Stacks.Groupoids.HasCubeRelation A` — the cube class `D_L(f, g, t)` of
`StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianTorsion/Cube/FibreSubgroup.lean` vanishes for
every invertible `L` and every triple `f, g, t` — and derives the closed form from it.
`HasCubeRelation A` follows from `HasTheoremOfTheCube A`
(`Stacks.Groupoids.hasCubeRelation_of_hasTheoremOfTheCube`) and is proved for every abelian variety
over an algebraically closed field in `Cube/`.

## Main definitions

* `Stacks.Groupoids.HasCubeRelation`: the cube relation, for every invertible module on `A`.

## Main results

* `Stacks.Groupoids.hasCubeRelation_of_hasTheoremOfTheCube`.
* `Stacks.Groupoids.zpowIdPicardClass_rec_of_hasCubeRelation`: the cube relation at
  `([1], [1], [m])`.
* `Stacks.Groupoids.zpowIdPicardClass_eq_of_hasCubeRelation`: the closed form of the class of
  `[n]^*L`.

## Implementation notes

The recursion is derived once from the cube relation (`zpowIdPicardClass_rec_of_hasCubeRelation`);
the rest of the argument — the case `n = 2`, the three-term step and the two-sided induction — is
`Stacks.Groupoids.zpowIdPicardClass_eq_of_rec`, which takes the recursion as its input and so
contains no reference to the cube at all.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Stacks.SheafOfModules (picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **The cube relation of [Stacks, Tag 0BFE] for every invertible module on `A`**: the cube class
`D_L(f, g, t)` vanishes in `Pic(B)` for every invertible `L`, every `B` over `k` and every
`f, g, t : B ⟶ A`. -/
def HasCubeRelation : Prop :=
  ∀ (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    (B : Over (Spec (.of k))) (f g t : B ⟶ A), cubeClass L hL f g t = 0

variable {A}

/-- The cube relation as an equation between the classes of the two sides. -/
theorem pullbackPicardClass_cubeRelation_of_hasCubeRelation (hcr : HasCubeRelation A)
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    {B : Over (Spec (.of k))} (a b c : B ⟶ A) :
    pullbackPicardClass (a * b * c).left L hL + pullbackPicardClass a.left L hL +
          pullbackPicardClass b.left L hL + pullbackPicardClass c.left L hL =
      pullbackPicardClass (a * b).left L hL + pullbackPicardClass (a * c).left L hL +
        pullbackPicardClass (b * c).left L hL := by
  have h := hcr L hL B a b c
  rw [cubeClass_def] at h
  rw [← sub_eq_zero, ← h]
  abel

variable (A) in
/-- **The theorem of the cube gives the cube relation**, through
`Stacks.Groupoids.pullbackPicardClass_cubeRelation`. -/
theorem hasCubeRelation_of_hasTheoremOfTheCube [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) : HasCubeRelation A := by
  intro L hL B f g t
  rw [cubeClass_def, pullbackPicardClass_cubeRelation A hcube L hL f g t]
  abel

variable (A)
variable (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)

/-- **The cube relation at `a = b = [1]`, `c = [m]`**, from `HasCubeRelation A`. -/
theorem zpowIdPicardClass_rec_of_hasCubeRelation (hcr : HasCubeRelation A) (m : ℤ) :
    zpowIdPicardClass A L hL (m + 2) + zpowIdPicardClass A L hL 1 +
          zpowIdPicardClass A L hL 1 + zpowIdPicardClass A L hL m =
      zpowIdPicardClass A L hL 2 + zpowIdPicardClass A L hL (m + 1) +
        zpowIdPicardClass A L hL (m + 1) := by
  have h := pullbackPicardClass_cubeRelation_of_hasCubeRelation hcr L hL
    ((𝟙 A : A ⟶ A) ^ (1 : ℤ)) ((𝟙 A : A ⟶ A) ^ (1 : ℤ)) ((𝟙 A : A ⟶ A) ^ m)
  rw [← zpow_add (𝟙 A : A ⟶ A) 1 1, ← zpow_add (𝟙 A : A ⟶ A) (1 + 1) m,
    ← zpow_add (𝟙 A : A ⟶ A) 1 m, show ((1 : ℤ) + 1 + m) = m + 2 from by ring,
    show ((1 : ℤ) + 1) = 2 from by norm_num, show ((1 : ℤ) + m) = m + 1 from by ring] at h
  simp only [zpowIdPicardClass_def]
  exact h

/-- **The closed form of the class of `[n]^*L`, from its recursion.** If the classes of `[n]^*L`
satisfy the recursion `zpowIdPicardClass_rec_of_hasCubeRelation` for every `m`, then

`[n]^*L = n(n+1)/2 · L + n(n-1)/2 · [-1]^*L`

in `Pic(A)` for every integer `n`. The case `n = 2` is the recursion at `m = -1`, where `[0]`
contributes nothing; the three-term step is the recursion at `n - 1`; and the induction runs over
two consecutive values in both directions. -/
theorem zpowIdPicardClass_eq_of_rec
    (hrec : ∀ m : ℤ, zpowIdPicardClass A L hL (m + 2) + zpowIdPicardClass A L hL 1 +
          zpowIdPicardClass A L hL 1 + zpowIdPicardClass A L hL m =
      zpowIdPicardClass A L hL 2 + zpowIdPicardClass A L hL (m + 1) +
        zpowIdPicardClass A L hL (m + 1)) (n : ℤ) :
    zpowIdPicardClass A L hL n =
      triangularNumber n • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        triangularNumber (-n) • pullbackPicardClass (ι : A ⟶ A).left L hL := by
  have htwo : zpowIdPicardClass A L hL 2 = zpowIdPicardClass A L hL 1 +
      zpowIdPicardClass A L hL 1 + zpowIdPicardClass A L hL 1 +
        zpowIdPicardClass A L hL (-1) := by
    have h := hrec (-1)
    rw [show (-1 + 2 : ℤ) = 1 from by norm_num, show (-1 + 1 : ℤ) = 0 from by norm_num,
      zpowIdPicardClass_zero, add_zero, add_zero] at h
    exact h.symm
  have hstep : ∀ n : ℤ,
      zpowIdPicardClass A L hL (n + 1) + zpowIdPicardClass A L hL (n - 1) =
        picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
          pullbackPicardClass (ι : A ⟶ A).left L hL +
          zpowIdPicardClass A L hL n + zpowIdPicardClass A L hL n := by
    intro n
    have h := hrec (n - 1)
    rw [show (n - 1 + 2 : ℤ) = n + 1 from by ring, show (n - 1 + 1 : ℤ) = n from by ring,
      htwo, zpowIdPicardClass_one, zpowIdPicardClass_neg_one] at h
    refine add_right_cancel (b := picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
      picardClass A.left.presheaf A.left.ringCatIsSheaf L hL) ?_
    rw [show zpowIdPicardClass A L hL (n + 1) + zpowIdPicardClass A L hL (n - 1) +
          (picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
            picardClass A.left.presheaf A.left.ringCatIsSheaf L hL) =
        zpowIdPicardClass A L hL (n + 1) +
          picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
          picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
          zpowIdPicardClass A L hL (n - 1) from by abel, h]
    abel
  have key : ∀ m : ℤ, zpowIdPicardClass A L hL m = zpowIdPicardFormula A L hL m ∧
      zpowIdPicardClass A L hL (m + 1) = zpowIdPicardFormula A L hL (m + 1) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [zpowIdPicardClass_zero, zpowIdPicardFormula_zero]
        · rw [zero_add, zpowIdPicardClass_one, zpowIdPicardFormula_one]
    | succ i ih =>
        refine ⟨ih.2, ?_⟩
        have hs := hstep ((i : ℤ) + 1)
        have hf := zpowIdPicardFormula_step A L hL ((i : ℤ) + 1)
        rw [show ((i : ℤ) + 1 - 1) = (i : ℤ) from by ring] at hs hf
        rw [ih.1, ih.2, ← hf] at hs
        exact add_right_cancel hs
    | pred i ih =>
        have hs := hstep (-(i : ℤ))
        have hf := zpowIdPicardFormula_step A L hL (-(i : ℤ))
        rw [ih.1, ih.2, ← hf] at hs
        refine ⟨add_left_cancel hs, ?_⟩
        rw [show (-(i : ℤ) - 1 + 1) = -(i : ℤ) from by ring]
        exact ih.1
  rw [(key n).1, zpowIdPicardFormula_def]

/-- **The closed form of the class of `[n]^*L` in `Pic(A)`, from the cube relation**: the
sibling of `Stacks.Groupoids.zpowIdPicardClass_eq` under `HasCubeRelation A` in place of
`HasTheoremOfTheCube A`. -/
theorem zpowIdPicardClass_eq_of_hasCubeRelation (hcr : HasCubeRelation A) (n : ℤ) :
    zpowIdPicardClass A L hL n =
      triangularNumber n • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        triangularNumber (-n) • pullbackPicardClass (ι : A ⟶ A).left L hL :=
  zpowIdPicardClass_eq_of_rec A L hL (zpowIdPicardClass_rec_of_hasCubeRelation A L hL hcr) n

end Stacks.Groupoids

end
