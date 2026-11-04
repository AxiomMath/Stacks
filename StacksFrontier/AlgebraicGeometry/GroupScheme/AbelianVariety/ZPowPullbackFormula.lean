module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Cube.TheoremOfTheCube

/-!
# The pullback of an invertible module along multiplication by an integer

Let `A` be an abelian variety over a field `k` and let `L` be an invertible `𝒪_A`-module. Write
`[n] : A → A` for multiplication by `n`, the `n`th power of the identity in the group `A ⟶ A`,
and `[-1] = ι` for inversion. This file proves the formula

`[n]^*L ≅ L^{⊗ n(n+1)/2} ⊗ ([-1]^*L)^{⊗ n(n-1)/2}`

for every integer `n`, together with its consequences for symmetric and antisymmetric modules.

## Main results

* `Stacks.Groupoids.nonempty_zpowId_pullback_iso_of_isAbelianVariety`: the formula above, for
  every integer `n`.
* `Stacks.Groupoids.zpowIdPicardClass_eq_triangularNumber`: the same at the level of classes
  in `Pic(A)`.
* `Stacks.Groupoids.pullbackPicardClass_zpow_eq`: the class version for the powers `f^n` of an
  arbitrary morphism `f : B ⟶ A`.
* `Stacks.SheafOfModules.pullbackPicardClass_schemeTensorPower`: the pullback class of
  `L^{⊗ n}` is `n` times the pullback class of `L`.
* `Stacks.Groupoids.zpowIdPicardClass_comp`: `[m]^*[n]^*L ≅ [mn]^*L`, at the level of classes.
* `Stacks.Groupoids.zpowIdPicardClass_schemeTensor`: `[n]^*` is additive in `L`.
* `Stacks.Groupoids.nonempty_pullbackOver_inv_symmetrization`: the module `L ⊗ [-1]^*L` is
  symmetric, that is isomorphic to its pullback along `[-1]`; and
  `Stacks.Groupoids.nonempty_pullbackOver_inv_antisymmetrization`: the module
  `L ⊗ ([-1]^*L)^{⊗ -1}` is antisymmetric.
* `Stacks.Groupoids.nonempty_zpowId_pullback_symmetrization_iso`: `[n]^*𝒩 ≅ 𝒩^{⊗ n²}` for
  `𝒩 = L ⊗ [-1]^*L`.
* `Stacks.Groupoids.nonempty_zpowId_pullback_iso_of_antisymmetric`: for `L` antisymmetric,
  that is `[-1]^*L ≅ L^{⊗ -1}`, `[n]^*L ≅ L^{⊗ n}`.

## References

* [Stacks Project, Tag 0BFF](https://stacks.math.columbia.edu/tag/0BFF)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Stacks.SheafOfModules (schemeTensor schemeTensorPower picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.SheafOfModules

variable {X Y : Scheme.{u}}

/-- The pullback class of `L^{⊗ (m + 1)}` is the pullback class of `L^{⊗ m}` plus that of
`L`. -/
theorem pullbackPicardClass_schemeTensorPower_add_one (φ : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L) (m : ℤ) :
    pullbackPicardClass φ (schemeTensorPower Y L hL (m + 1))
        (isInvertible_schemeTensorPower Y L hL (m + 1)) =
      pullbackPicardClass φ (schemeTensorPower Y L hL m)
          (isInvertible_schemeTensorPower Y L hL m) +
        pullbackPicardClass φ L hL := by
  have := @TensorPower.isEquivalence_tensorRightFunctor _ _ _ Y.presheaf Y.ringCatIsSheaf _ _
    L hL
  rw [← pullbackPicardClass_schemeTensor φ _ L (isInvertible_schemeTensorPower Y L hL m) hL]
  exact pullbackPicardClass_congr φ _ _ _ _
    (TensorPower.tensorPowerSuccIso Y.presheaf Y.ringCatIsSheaf L m).symm

/-- **The pullback class of `L^{⊗ n}` is `n` times the pullback class of `L`.** -/
theorem pullbackPicardClass_schemeTensorPower (φ : X ⟶ Y)
    (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L) (n : ℤ) :
    pullbackPicardClass φ (schemeTensorPower Y L hL n)
        (isInvertible_schemeTensorPower Y L hL n) =
      n • pullbackPicardClass φ L hL := by
  induction n using Int.induction_on with
  | zero =>
      rw [zero_smul]
      exact pullbackPicardClass_unit φ (isInvertible_schemeTensorPower Y L hL 0)
  | succ i ih =>
      rw [pullbackPicardClass_schemeTensorPower_add_one, ih, add_smul, one_smul]
  | pred i ih =>
      have h := pullbackPicardClass_schemeTensorPower_add_one φ L hL (-(i : ℤ) - 1)
      rw [sub_add_cancel, ih] at h
      rw [sub_smul, one_smul, h, add_sub_cancel_right]

end Stacks.SheafOfModules

namespace Stacks.Groupoids

/-! ### Triangular numbers -/

/-- `n(n+1)/2 - n(n-1)/2 = n`. -/
theorem triangularNumber_sub_triangularNumber_neg (n : ℤ) :
    triangularNumber n - triangularNumber (-n) = n := by
  linarith [two_mul_triangularNumber n, two_mul_triangularNumber (-n)]

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)

/-! ### Functoriality of the classes of `[n]^*L` -/

/-- **`[m]^*[n]^*L ≅ [mn]^*L`**, at the level of classes in `Pic(A)`. -/
theorem zpowIdPicardClass_comp (m n : ℤ) :
    zpowIdPicardClass A (pullbackOver ((𝟙 A : A ⟶ A) ^ n) L)
        (isInvertible_pullbackOver ((𝟙 A : A ⟶ A) ^ n) L hL) m =
      zpowIdPicardClass A L hL (m * n) := by
  rw [zpowIdPicardClass_def, zpowIdPicardClass_def,
    ← Stacks.SheafOfModules.pullbackPicardClass_comp, ← Over.comp_left, GrpObj.comp_zpow,
    Category.comp_id, zpow_mul]

/-- The class of `[-1]^*[-1]^*L` is the class of `L`, because inversion is an involution. -/
theorem pullbackPicardClass_inv_pullbackOver_inv :
    pullbackPicardClass (ι : A ⟶ A).left (pullbackOver (ι : A ⟶ A) L)
        (isInvertible_pullbackOver (ι : A ⟶ A) L hL) =
      picardClass A.left.presheaf A.left.ringCatIsSheaf L hL := by
  rw [← Stacks.SheafOfModules.pullbackPicardClass_comp, ← Over.comp_left, GrpObj.inv_comp_inv,
    Over.id_left, Stacks.SheafOfModules.pullbackPicardClass_id]

/-- The class of `[n]^*L` only depends on the isomorphism class of `L`. -/
theorem zpowIdPicardClass_congr
    (M : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M)
    (e : L ≅ M) (n : ℤ) :
    zpowIdPicardClass A L hL n = zpowIdPicardClass A M hM n :=
  Stacks.SheafOfModules.pullbackPicardClass_congr _ L M hL hM e

/-- **`[n]^*(L ⊗ M) ≅ [n]^*L ⊗ [n]^*M`**, at the level of classes in `Pic(A)`. -/
theorem zpowIdPicardClass_schemeTensor
    (M : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M) (n : ℤ) :
    zpowIdPicardClass A (schemeTensor A.left L M)
        (Stacks.SheafOfModules.isInvertible_schemeTensor A.left L M hL hM) n =
      zpowIdPicardClass A L hL n + zpowIdPicardClass A M hM n :=
  Stacks.SheafOfModules.pullbackPicardClass_schemeTensor _ L M hL hM

/-! ### Symmetric and antisymmetric modules -/

/-- `[-1]^*(L ⊗ P) ≅ Q` as soon as the classes of `[-1]^*L + [-1]^*P` and `Q` in `Pic(A)` agree. -/
private theorem nonempty_pullbackOver_inv_schemeTensor_iso
    {P Q : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace)}
    (hP : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf P)
    (hQ : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf Q)
    (h : pullbackPicardClass (ι : A ⟶ A).left L hL + pullbackPicardClass (ι : A ⟶ A).left P hP =
      picardClass A.left.presheaf A.left.ringCatIsSheaf Q hQ) :
    Nonempty (pullbackOver (ι : A ⟶ A) (schemeTensor A.left L P) ≅ Q) := by
  refine (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
    (isInvertible_pullbackOver (ι : A ⟶ A) _
      (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL hP)) hQ).mp ?_
  rw [← Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL hP),
    Stacks.SheafOfModules.pullbackPicardClass_schemeTensor _ _ _ hL hP, h]

include hL in
/-- **The symmetrization `L ⊗ [-1]^*L` is symmetric**: it is isomorphic to its own pullback
along `[-1]`. -/
theorem nonempty_pullbackOver_inv_symmetrization :
    Nonempty (pullbackOver (ι : A ⟶ A) (schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L)) ≅
      schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L)) := by
  have hι := isInvertible_pullbackOver (ι : A ⟶ A) L hL
  refine nonempty_pullbackOver_inv_schemeTensor_iso A L hL hι
    (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL hι) ?_
  rw [pullbackPicardClass_inv_pullbackOver_inv A L hL,
    Stacks.SheafOfModules.picardClass_schemeTensor A.left _ _ hL hι,
    ← Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass _ _ hL hι, add_comm]

include hL in
/-- **The antisymmetrization `L ⊗ ([-1]^*L)^{⊗ -1}` is antisymmetric**: its pullback along `[-1]`
is isomorphic to its own tensor inverse. -/
theorem nonempty_pullbackOver_inv_antisymmetrization :
    Nonempty (pullbackOver (ι : A ⟶ A) (schemeTensor A.left L
        (schemeTensorPower A.left (pullbackOver (ι : A ⟶ A) L)
          (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (-1))) ≅
      schemeTensorPower A.left (schemeTensor A.left L
          (schemeTensorPower A.left (pullbackOver (ι : A ⟶ A) L)
            (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (-1)))
        (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL
          (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left _
            (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (-1))) (-1)) := by
  have hι := isInvertible_pullbackOver (ι : A ⟶ A) L hL
  have hι' := Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left _ hι (-1)
  refine nonempty_pullbackOver_inv_schemeTensor_iso A L hL hι'
    (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left _
      (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL hι') (-1)) ?_
  rw [Stacks.SheafOfModules.pullbackPicardClass_schemeTensorPower,
    pullbackPicardClass_inv_pullbackOver_inv A L hL,
    Stacks.SheafOfModules.picardClass_schemeTensorPower,
    Stacks.SheafOfModules.picardClass_schemeTensor A.left _ _ hL hι',
    Stacks.SheafOfModules.picardClass_schemeTensorPower,
    ← Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass _ _ hL hι]
  simp only [neg_smul, one_smul, smul_add, smul_neg, neg_neg]
  abel

/-! ### Tensor powers -/

/-- `[n]^*L ≅ L^{⊗ m}` as soon as the class of `[n]^*L` in `Pic(A)` is `m` times that of `L`. -/
theorem nonempty_zpowId_pullback_iso_tensorPower_of_zpowIdPicardClass_eq {n m : ℤ}
    (h : zpowIdPicardClass A L hL n =
      m • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) L ≅ schemeTensorPower A.left L hL m) := by
  refine (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
    (isInvertible_pullbackOver ((𝟙 A : A ⟶ A) ^ n) L hL)
    (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left L hL m)).mp ?_
  rw [Stacks.SheafOfModules.picardClass_schemeTensorPower, ← h]
  rfl

/-! ### The closed form, and its symmetric and antisymmetric cases -/

section Cube

variable [AlgebraicGeometry.IsAbelianVariety k A]

/-- **The class of `[n]^*L` in `Pic(A)`** is `n(n+1)/2` times the class of `L` plus `n(n-1)/2`
times the class of `[-1]^*L`. -/
theorem zpowIdPicardClass_eq_triangularNumber (n : ℤ) :
    zpowIdPicardClass A L hL n =
      triangularNumber n • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        triangularNumber (-n) • pullbackPicardClass (ι : A ⟶ A).left L hL :=
  zpowIdPicardClass_eq A L hL (hasTheoremOfTheCube k A) n

/-- **The class of `[n]^*L` for `L` antisymmetric**, that is with `[-1]^*L ≅ L^{⊗ -1}`, is `n`
times the class of `L`. -/
theorem zpowIdPicardClass_eq_of_antisymmetric
    (hanti : Nonempty (pullbackOver (ι : A ⟶ A) L ≅ schemeTensorPower A.left L hL (-1)))
    (n : ℤ) :
    zpowIdPicardClass A L hL n = n • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL := by
  have h : pullbackPicardClass (ι : A ⟶ A).left L hL =
      (-1 : ℤ) • picardClass A.left.presheaf A.left.ringCatIsSheaf L hL := by
    rw [← Stacks.SheafOfModules.picardClass_schemeTensorPower A.left L hL (-1)]
    exact (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
      (isInvertible_pullbackOver (ι : A ⟶ A) L hL)
      (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left L hL (-1))).mpr hanti
  rw [zpowIdPicardClass_eq_triangularNumber A L hL, h, smul_smul, mul_neg_one,
    neg_smul, ← sub_eq_add_neg, ← sub_smul, triangularNumber_sub_triangularNumber_neg]

/-- **`[n]^*L ≅ L^{⊗ n}` for `L` antisymmetric**, that is with `[-1]^*L ≅ L^{⊗ -1}`. -/
theorem nonempty_zpowId_pullback_iso_of_antisymmetric
    (hanti : Nonempty (pullbackOver (ι : A ⟶ A) L ≅ schemeTensorPower A.left L hL (-1)))
    (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) L ≅ schemeTensorPower A.left L hL n) :=
  nonempty_zpowId_pullback_iso_tensorPower_of_zpowIdPicardClass_eq A L hL
    (zpowIdPicardClass_eq_of_antisymmetric A L hL hanti n)

/-- **`[n]^*𝒩 ≅ 𝒩^{⊗ n²}` for the symmetrization `𝒩 = L ⊗ [-1]^*L`.** -/
theorem nonempty_zpowId_pullback_symmetrization_iso (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n)
        (schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L)) ≅
      schemeTensorPower A.left (schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L))
        (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL
          (isInvertible_pullbackOver (ι : A ⟶ A) L hL)) (n * n)) :=
  nonempty_zpowId_pullback_iso_of_symmetric A (hasTheoremOfTheCube k A) _ _
    (nonempty_pullbackOver_inv_symmetrization A L hL).some n

/-- **`[n]^*𝒜 ≅ 𝒜^{⊗ n}` for the antisymmetrization `𝒜 = L ⊗ ([-1]^*L)^{⊗ -1}`.** -/
theorem nonempty_zpowId_pullback_antisymmetrization_iso (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) (schemeTensor A.left L
        (schemeTensorPower A.left (pullbackOver (ι : A ⟶ A) L)
          (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (-1))) ≅
      schemeTensorPower A.left (schemeTensor A.left L
          (schemeTensorPower A.left (pullbackOver (ι : A ⟶ A) L)
            (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (-1)))
        (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL
          (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left _
            (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (-1))) n) :=
  nonempty_zpowId_pullback_iso_of_antisymmetric A _ _
    (nonempty_pullbackOver_inv_antisymmetrization A L hL) n

/-- For every morphism `f : B ⟶ A` of schemes over `k` and every integer `n`, the class of
`(f^n)^*L` in `Pic(B)` is `n(n+1)/2` times the class of `f^*L` plus `n(n-1)/2` times the class of
`(f⁻¹)^*L`. -/
theorem pullbackPicardClass_zpow_eq {B : Over (Spec (.of k))} (f : B ⟶ A) (n : ℤ) :
    pullbackPicardClass (f ^ n).left L hL =
      triangularNumber n • pullbackPicardClass f.left L hL +
        triangularNumber (-n) • pullbackPicardClass (f⁻¹).left L hL := by
  have hι := isInvertible_pullbackOver (ι : A ⟶ A) L hL
  obtain ⟨e⟩ := nonempty_zpowId_pullback_iso_two_mul A L hL (hasTheoremOfTheCube k A) n
    (triangularNumber n) (triangularNumber (-n)) (two_mul_triangularNumber n)
    (by rw [two_mul_triangularNumber]; ring)
  have hf : f ^ n = f ≫ (𝟙 A : A ⟶ A) ^ n := by rw [GrpObj.comp_zpow, Category.comp_id]
  have hf' : f⁻¹ = f ≫ (ι : A ⟶ A) := by rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
  rw [hf, hf', Over.comp_left, Over.comp_left,
    Stacks.SheafOfModules.pullbackPicardClass_comp _ _ L hL
      (isInvertible_pullbackOver _ L hL),
    Stacks.SheafOfModules.pullbackPicardClass_comp _ _ L hL hι,
    Stacks.SheafOfModules.pullbackPicardClass_congr _ _ _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _
        (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left L hL _)
        (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left _ hι _)) e,
    Stacks.SheafOfModules.pullbackPicardClass_schemeTensor _ _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left L hL _)
      (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left _ hι _),
    Stacks.SheafOfModules.pullbackPicardClass_schemeTensorPower,
    Stacks.SheafOfModules.pullbackPicardClass_schemeTensorPower]

/-- Let `k` be a field, let `A` be an abelian variety over `k` and let `L` be an invertible
`𝒪_A`-module. Then for every integer `n`

`[n]^*L ≅ L^{⊗ n(n+1)/2} ⊗ ([-1]^*L)^{⊗ n(n-1)/2}`

where `[n] : A → A` is multiplication by `n`, the `n`th power of the identity in the group
`A ⟶ A` of morphisms into the group object, and `[-1] = ι` is inversion. Both divisions are
exact (`Stacks.Groupoids.two_dvd_mul_succ`). -/
@[stacks 0BFF]
theorem nonempty_zpowId_pullback_iso_of_isAbelianVariety (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) L ≅
      schemeTensor A.left (schemeTensorPower A.left L hL (n * (n + 1) / 2))
        (schemeTensorPower A.left (pullbackOver (ι : A ⟶ A) L)
          (isInvertible_pullbackOver (ι : A ⟶ A) L hL) (n * (n - 1) / 2))) :=
  nonempty_zpowId_pullback_iso A L hL (hasTheoremOfTheCube k A) n

end Cube

end Stacks.Groupoids

end
