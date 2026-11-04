module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of an invertible module along multiplication by an integer

Let `A` be an abelian variety over a field `k` and let `L` be an invertible `𝒪_A`-module. Write
`[n] : A → A` for multiplication by `n`, that is the `n`th power of the identity in the group
`A ⟶ A` of morphisms into the group object, and `[-1] = ι` for inversion. Assuming the theorem
of the cube for the triple self-product of `A` (`Stacks.Groupoids.HasTheoremOfTheCube A`), for
every integer `n`

`[n]^*L ≅ L^{⊗ n(n+1)/2} ⊗ ([-1]^*L)^{⊗ n(n-1)/2}`

as invertible modules on `A`.

## Main definitions

* `Stacks.Groupoids.triangularNumber`: the `n`th triangular number `n(n + 1)/2`, for `n` an
  arbitrary integer.
* `Stacks.Groupoids.zpowIdPicardClass`: the class of `[n]^*L` in `Pic(A)`.
* `Stacks.Groupoids.zpowIdPicardFormula`: the class of `L^{⊗ n(n+1)/2} ⊗ ([-1]^*L)^{⊗ n(n-1)/2}`
  in `Pic(A)`.

## Main results

* `Stacks.Groupoids.pullbackPicardClass_cubeRelation`: the cube relation pulled back along an
  arbitrary triple of morphisms `(a, b, c) : B → A × A × A`.
* `Stacks.Groupoids.zpowIdPicardClass_step`: the recursion
  `[[n+1]^*L] + [[n-1]^*L] = [L] + [[-1]^*L] + 2 [[n]^*L]` in `Pic(A)`.
* `Stacks.Groupoids.zpowIdPicardClass_eq`: the closed form of `[[n]^*L]` in `Pic(A)`.
* `Stacks.Groupoids.nonempty_zpowId_pullback_iso_two_mul`: the isomorphism, with the two exponents
  given by the division-free characterisations `2a = n(n+1)` and `2b = n(n-1)`.
* `Stacks.Groupoids.nonempty_zpowId_pullback_iso`: the isomorphism, with the exponents
  `n(n+1)/2` and `n(n-1)/2`.

## References

* [Stacks Project, Tag 0BFF](https://stacks.math.columbia.edu/tag/0BFF)
* [Stacks Project, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE)
* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.SheafOfModules (schemeTensor schemeTensorPower picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

/-! ### Triangular numbers -/

/-- The `n`th triangular number `n(n + 1)/2`, for `n` an arbitrary integer. -/
def triangularNumber (n : ℤ) : ℤ := n * (n + 1) / 2

/-- The product of two consecutive integers is even. -/
theorem two_dvd_mul_succ (n : ℤ) : (2 : ℤ) ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (n + 1), by rw [hm]; ring⟩
  · exact ⟨n * (m + 1), by rw [hm]; ring⟩

/-- Twice the `n`th triangular number is `n(n + 1)`. -/
theorem two_mul_triangularNumber (n : ℤ) : 2 * triangularNumber n = n * (n + 1) :=
  Int.mul_ediv_cancel' (two_dvd_mul_succ n)

/-- Twice `n(n - 1)/2` is `n(n - 1)`. -/
theorem two_mul_mul_pred_ediv_two (n : ℤ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  refine Int.mul_ediv_cancel' ?_
  have h := two_dvd_mul_succ (n - 1)
  rwa [show (n - 1) * ((n - 1) + 1) = n * (n - 1) from by ring] at h

/-- An integer whose double is `n(n + 1)` is the `n`th triangular number. -/
theorem triangularNumber_eq_of_two_mul {a n : ℤ} (h : 2 * a = n * (n + 1)) :
    a = triangularNumber n :=
  mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) (h.trans (two_mul_triangularNumber n).symm)

/-- The `0`th triangular number is `0`. -/
@[simp] theorem triangularNumber_zero : triangularNumber 0 = 0 := by
  norm_num [triangularNumber]

/-- The first triangular number is `1`. -/
@[simp] theorem triangularNumber_one : triangularNumber 1 = 1 := by
  norm_num [triangularNumber]

/-- The `(-1)`st triangular number is `0`. -/
@[simp] theorem triangularNumber_neg_one : triangularNumber (-1) = 0 := by
  norm_num [triangularNumber]

/-- The `n`th triangular number read backwards: `n(n - 1)/2` is the `(-n)`th. -/
theorem triangularNumber_neg (n : ℤ) : triangularNumber (-n) = n * (n - 1) / 2 := by
  rw [triangularNumber, show (-n) * ((-n) + 1) = n * (n - 1) from by ring]

/-- The three-term recursion satisfied by the triangular numbers. -/
theorem triangularNumber_rec (n : ℤ) :
    triangularNumber (n + 1) + triangularNumber (n - 1) = 2 * triangularNumber n + 1 := by
  refine mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) ?_
  rw [mul_add, mul_add, two_mul_triangularNumber, two_mul_triangularNumber,
    two_mul_triangularNumber, mul_one]
  ring

/-! ### The cube relation along a triple of morphisms -/

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- For morphisms `a, b, c : B ⟶ A` the classes in `Pic(B)` of the pullbacks of `L` along the
seven sums of `a`, `b`, `c` satisfy the alternating relation of the cube. -/
theorem pullbackPicardClass_cubeRelation [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A)
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    {B : Over (Spec (.of k))} (a b c : B ⟶ A) :
    pullbackPicardClass (a * b * c).left L hL + pullbackPicardClass a.left L hL +
          pullbackPicardClass b.left L hL + pullbackPicardClass c.left L hL =
      pullbackPicardClass (a * b).left L hL + pullbackPicardClass (a * c).left L hL +
        pullbackPicardClass (b * c).left L hL := by
  obtain ⟨e⟩ := nonempty_cubeRelation A hcube L hL
  have h1 : lift (lift a b) c ≫ cubeProj₁ A = a := by simp [cubeProj₁]
  have h2 : lift (lift a b) c ≫ cubeProj₂ A = b := by simp [cubeProj₂]
  have h3 : lift (lift a b) c ≫ cubeProj₃ A = c := by simp [cubeProj₃]
  have key := Stacks.SheafOfModules.pullbackPicardClass_congr (lift (lift a b) c).left _ _
    (Stacks.SheafOfModules.isInvertible_schemeTensor₄ (cubeObj A).left _ _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₃ A) L hL))
    (Stacks.SheafOfModules.isInvertible_schemeTensor₃ (cubeObj A).left _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL)) e
  rw [Stacks.SheafOfModules.pullbackPicardClass_schemeTensor₄ (lift (lift a b) c).left _ _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₃ A) L hL),
    Stacks.SheafOfModules.pullbackPicardClass_schemeTensor₃ (lift (lift a b) c).left _ _ _
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL)
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL)
      (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_comp (lift (lift a b) c).left
      (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A).left L hL
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_comp (lift (lift a b) c).left
      (cubeProj₁ A).left L hL (isInvertible_pullbackOver (cubeProj₁ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_comp (lift (lift a b) c).left
      (cubeProj₂ A).left L hL (isInvertible_pullbackOver (cubeProj₂ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_comp (lift (lift a b) c).left
      (cubeProj₃ A).left L hL (isInvertible_pullbackOver (cubeProj₃ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_comp (lift (lift a b) c).left
      (cubeProj₁ A * cubeProj₂ A).left L hL
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_comp (lift (lift a b) c).left
      (cubeProj₁ A * cubeProj₃ A).left L hL
      (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL),
    ← Stacks.SheafOfModules.pullbackPicardClass_comp (lift (lift a b) c).left
      (cubeProj₂ A * cubeProj₃ A).left L hL
      (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL)] at key
  simpa only [← Over.comp_left, MonObj.comp_mul, h1, h2, h3] using key

/-! ### The class of `[n]^*L` -/

/-- The class in `Pic(A)` of the pullback of `L` along multiplication by `n`. -/
noncomputable def zpowIdPicardClass
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L) (n : ℤ) :
    Stacks.SheafOfModules.PicardGroup A.left.presheaf A.left.ringCatIsSheaf :=
  pullbackPicardClass ((𝟙 A : A ⟶ A) ^ n).left L hL

/-- The class of `[n]^*L` is the Picard class of the pullback of `L` along `[n]`. -/
theorem zpowIdPicardClass_def
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L) (n : ℤ) :
    zpowIdPicardClass A L hL n = pullbackPicardClass ((𝟙 A : A ⟶ A) ^ n).left L hL := rfl

variable (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)

/-- The class of `[0]^*L` vanishes. -/
theorem zpowIdPicardClass_zero : zpowIdPicardClass A L hL 0 = 0 := by
  rw [zpowIdPicardClass_def, zpow_zero]
  exact pullbackPicardClass_one L hL

/-- The class of `[1]^*L` is the class of `L`. -/
theorem zpowIdPicardClass_one :
    zpowIdPicardClass A L hL 1 = picardClass A.left.presheaf A.left.ringCatIsSheaf L hL := by
  rw [zpowIdPicardClass_def, zpow_one, Over.id_left,
    Stacks.SheafOfModules.pullbackPicardClass_id]

/-- The class of `[-1]^*L` is the class of the pullback of `L` along inversion. -/
theorem zpowIdPicardClass_neg_one :
    zpowIdPicardClass A L hL (-1) = pullbackPicardClass (ι : A ⟶ A).left L hL := by
  rw [zpowIdPicardClass_def, zpow_neg, zpow_one, GrpObj.inv_eq_inv]

/-- The cube relation at `a = b = [1]` and `c = [m]`, in terms of the classes of `[n]^*L`. -/
theorem zpowIdPicardClass_rec [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (m : ℤ) :
    zpowIdPicardClass A L hL (m + 2) + zpowIdPicardClass A L hL 1 +
          zpowIdPicardClass A L hL 1 + zpowIdPicardClass A L hL m =
      zpowIdPicardClass A L hL 2 + zpowIdPicardClass A L hL (m + 1) +
        zpowIdPicardClass A L hL (m + 1) := by
  have h := pullbackPicardClass_cubeRelation A hcube L hL
    ((𝟙 A : A ⟶ A) ^ (1 : ℤ)) ((𝟙 A : A ⟶ A) ^ (1 : ℤ)) ((𝟙 A : A ⟶ A) ^ m)
  rw [← zpow_add (𝟙 A : A ⟶ A) 1 1, ← zpow_add (𝟙 A : A ⟶ A) (1 + 1) m,
    ← zpow_add (𝟙 A : A ⟶ A) 1 m, show ((1 : ℤ) + 1 + m) = m + 2 from by ring,
    show ((1 : ℤ) + 1) = 2 from by norm_num, show ((1 : ℤ) + m) = m + 1 from by ring] at h
  simpa only [zpowIdPicardClass_def] using h

/-- The class of `[2]^*L` is three times the class of `[1]^*L` plus the class of `[-1]^*L`. -/
theorem zpowIdPicardClass_two [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) :
    zpowIdPicardClass A L hL 2 = zpowIdPicardClass A L hL 1 + zpowIdPicardClass A L hL 1 +
      zpowIdPicardClass A L hL 1 + zpowIdPicardClass A L hL (-1) := by
  have h := zpowIdPicardClass_rec A L hL hcube (-1)
  rw [show (-1 + 2 : ℤ) = 1 from by norm_num, show (-1 + 1 : ℤ) = 0 from by norm_num,
    zpowIdPicardClass_zero, add_zero, add_zero] at h
  exact h.symm

/-- The classes of `[n + 1]^*L` and `[n - 1]^*L` add up to twice the class of `[n]^*L` together
with the classes of `L` and of `[-1]^*L`. -/
theorem zpowIdPicardClass_step [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (n : ℤ) :
    zpowIdPicardClass A L hL (n + 1) + zpowIdPicardClass A L hL (n - 1) =
      picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        pullbackPicardClass (ι : A ⟶ A).left L hL +
        zpowIdPicardClass A L hL n + zpowIdPicardClass A L hL n := by
  have h := zpowIdPicardClass_rec A L hL hcube (n - 1)
  rw [show (n - 1 + 2 : ℤ) = n + 1 from by ring, show (n - 1 + 1 : ℤ) = n from by ring,
    zpowIdPicardClass_two A L hL hcube, zpowIdPicardClass_one, zpowIdPicardClass_neg_one] at h
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

/-! ### The closed form -/

/-- The `n(n+1)/2`-fold multiple of the class of `L` plus the `n(n-1)/2`-fold multiple of the
class of `[-1]^*L`, in `Pic(A)`. -/
noncomputable def zpowIdPicardFormula (n : ℤ) :
    Stacks.SheafOfModules.PicardGroup A.left.presheaf A.left.ringCatIsSheaf :=
  triangularNumber n • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
    triangularNumber (-n) • pullbackPicardClass (ι : A ⟶ A).left L hL

/-- The defining formula of `zpowIdPicardFormula`. -/
theorem zpowIdPicardFormula_def (n : ℤ) :
    zpowIdPicardFormula A L hL n =
      triangularNumber n • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        triangularNumber (-n) • pullbackPicardClass (ι : A ⟶ A).left L hL := rfl

/-- `zpowIdPicardFormula` vanishes at `0`. -/
theorem zpowIdPicardFormula_zero : zpowIdPicardFormula A L hL 0 = 0 := by
  rw [zpowIdPicardFormula_def, neg_zero, triangularNumber_zero, zero_smul, zero_smul, add_zero]

/-- `zpowIdPicardFormula` at `1` is the class of `L`. -/
theorem zpowIdPicardFormula_one :
    zpowIdPicardFormula A L hL 1 = picardClass A.left.presheaf A.left.ringCatIsSheaf L hL := by
  rw [zpowIdPicardFormula_def, triangularNumber_one, one_smul, triangularNumber_neg_one,
    zero_smul, add_zero]

/-- `zpowIdPicardFormula` satisfies the same recursion as the classes of `[n]^*L`. -/
theorem zpowIdPicardFormula_step (n : ℤ) :
    zpowIdPicardFormula A L hL (n + 1) + zpowIdPicardFormula A L hL (n - 1) =
      picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        pullbackPicardClass (ι : A ⟶ A).left L hL +
        zpowIdPicardFormula A L hL n + zpowIdPicardFormula A L hL n := by
  simp only [zpowIdPicardFormula_def]
  rw [show (-(n + 1) : ℤ) = -n - 1 from by ring, show (-(n - 1) : ℤ) = -n + 1 from by ring,
    show triangularNumber (n + 1) =
        triangularNumber n + triangularNumber n + 1 - triangularNumber (n - 1) from by
      have h := triangularNumber_rec n; linarith,
    show triangularNumber (-n - 1) =
        triangularNumber (-n) + triangularNumber (-n) + 1 - triangularNumber (-n + 1) from by
      have h := triangularNumber_rec (-n); linarith,
    sub_smul, sub_smul, add_smul, add_smul, add_smul, add_smul, one_smul, one_smul]
  abel

/-- The class of `[n]^*L` in `Pic(A)` is `zpowIdPicardFormula`. -/
theorem zpowIdPicardClass_eq_formula [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (n : ℤ) :
    zpowIdPicardClass A L hL n = zpowIdPicardFormula A L hL n := by
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
        have hs := zpowIdPicardClass_step A L hL hcube ((i : ℤ) + 1)
        have hf := zpowIdPicardFormula_step A L hL ((i : ℤ) + 1)
        rw [show ((i : ℤ) + 1 - 1) = (i : ℤ) from by ring] at hs hf
        rw [ih.1, ih.2, ← hf] at hs
        exact add_right_cancel hs
    | pred i ih =>
        have hs := zpowIdPicardClass_step A L hL hcube (-(i : ℤ))
        have hf := zpowIdPicardFormula_step A L hL (-(i : ℤ))
        rw [ih.1, ih.2, ← hf] at hs
        refine ⟨add_left_cancel hs, ?_⟩
        rw [show (-(i : ℤ) - 1 + 1) = -(i : ℤ) from by ring]
        exact ih.1
  exact (key n).1

/-- The class of `[n]^*L` in `Pic(A)` is the `n(n+1)/2`-fold multiple of the class of `L` plus
the `n(n-1)/2`-fold multiple of the class of `[-1]^*L`. -/
theorem zpowIdPicardClass_eq [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (n : ℤ) :
    zpowIdPicardClass A L hL n =
      triangularNumber n • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        triangularNumber (-n) • pullbackPicardClass (ι : A ⟶ A).left L hL := by
  rw [zpowIdPicardClass_eq_formula A L hL hcube, zpowIdPicardFormula_def]

/-! ### The pullback along multiplication by an integer -/

/-- Let `k` be a field, `A` an abelian variety over `k` satisfying the theorem of the cube for
its triple self-product, and `L` an invertible `𝒪_A`-module. If `a` and `b` are integers with
`2a = n(n+1)` and `2b = n(n-1)` then

`[n]^*L ≅ L^{⊗ a} ⊗ ([-1]^*L)^{⊗ b}`

where `[n]` is the `n`th power of the identity in the group `A ⟶ A`, that is multiplication by
`n`, and `[-1] = ι` is inversion. -/
theorem nonempty_zpowId_pullback_iso_two_mul [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (n a b : ℤ) (ha : 2 * a = n * (n + 1))
    (hb : 2 * b = n * (n - 1)) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) L ≅
      schemeTensor A.left (schemeTensorPower A.left L hL a)
        (schemeTensorPower A.left (pullbackOver (ι : A ⟶ A) L)
          (isInvertible_pullbackOver (ι : A ⟶ A) L hL) b)) := by
  have ha' : a = triangularNumber n := triangularNumber_eq_of_two_mul ha
  have hb' : b = triangularNumber (-n) := by
    refine triangularNumber_eq_of_two_mul ?_
    rw [hb]; ring
  refine (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
    (isInvertible_pullbackOver ((𝟙 A : A ⟶ A) ^ n) L hL)
    (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left L hL a)
      (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left
        (pullbackOver (ι : A ⟶ A) L) (isInvertible_pullbackOver (ι : A ⟶ A) L hL) b))).mp ?_
  rw [Stacks.SheafOfModules.picardClass_schemeTensor A.left _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left L hL a)
      (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left
        (pullbackOver (ι : A ⟶ A) L) (isInvertible_pullbackOver (ι : A ⟶ A) L hL) b),
    Stacks.SheafOfModules.picardClass_schemeTensorPower A.left L hL a,
    Stacks.SheafOfModules.picardClass_schemeTensorPower A.left
      (pullbackOver (ι : A ⟶ A) L) (isInvertible_pullbackOver (ι : A ⟶ A) L hL) b,
    ha', hb']
  exact zpowIdPicardClass_eq A L hL hcube n

/-- Let `k` be a field, let `A` be an abelian variety over `k` satisfying the theorem of the
cube for its triple self-product, and let `L` be an invertible `𝒪_A`-module. Then

`[n]^*L ≅ L^{⊗ n(n+1)/2} ⊗ ([-1]^*L)^{⊗ n(n-1)/2}`

for every integer `n`, where `[n] : A → A` is multiplication by `n`, the `n`th power of the
identity in the group `A ⟶ A` of morphisms into the group object, and `[-1] = ι` is inversion. -/
@[stacks 0BFF "for every integer n, assuming the theorem of the cube (Tag 0BF4) for A"]
theorem nonempty_zpowId_pullback_iso [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) L ≅
      schemeTensor A.left (schemeTensorPower A.left L hL (n * (n + 1) / 2))
        (schemeTensorPower A.left (pullbackOver (ι : A ⟶ A) L)
          (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (n * (n - 1) / 2))) :=
  nonempty_zpowId_pullback_iso_two_mul A L hL hcube n _ _
    (two_mul_triangularNumber n) (two_mul_mul_pred_ediv_two n)

end Stacks.Groupoids

end
