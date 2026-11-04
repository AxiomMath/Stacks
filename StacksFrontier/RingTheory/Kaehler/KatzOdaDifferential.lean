module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaTensor
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection

/-!
# The differentials of the graded pieces of `Ω^•_{B/R}`

Let `R → A → B` be ring maps and filter `⋀^• Ω_{B/R}` by the forms pulled back from `A`. The de
Rham differential preserves the filtration and is `A`-linear on its graded pieces
(`StacksFrontier.RingTheory.Kaehler.KatzOdaFunctorial`), so each graded piece
`gr^k = F^k / F^{k+1}` is a complex of `A`-modules. This file builds these differentials and
shows that the identification

`⋀ᵏ_A Ω_{A/R} ⊗_A gr^0_m ≅ gr^k_{k+m}`,  `a ⊗ [η] ↦ (-1)^{km} [a ∧ η]`

of `StacksFrontier.RingTheory.Kaehler.KatzOdaTensor`, twisted by the sign `(-1)^{km}`, commutes with
the differentials `1 ⊗ d` and `d`: by the Leibniz rule
`d(a ∧ η) = da ∧ η + (-1)^k a ∧ dη`, and `da ∧ η` lies in `F^{k+1}`. Equivalently the untwisted
map is wedging with `a` on the right, `[η ∧ a]`.

## Main definitions

* `KaehlerDifferential.zeroGradedD`: the differential of `gr^0`, `A`-linear.
* `KaehlerDifferential.gradedD`: the differential of `gr^k`, `A`-linear.
* `KaehlerDifferential.gradedMulSigned`: `a ⊗ [η] ↦ (-1)^{km} [a ∧ η]`.

## Main results

* `KaehlerDifferential.gradedD_gradedMulSigned`: the twisted map commutes with the differentials.

## References

* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace KaehlerDifferential

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

local notation "F" => exteriorPower.wedgeStep (mapBaseChange R A B)

/-- The zeroth step of the filtration is everything. -/
theorem wedgeStep_zero (n : ℕ) : F 0 n = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  have := exteriorPower.wedgeLeftMul_mem_wedgeStep (mapBaseChange R A B) (j := 0) (m := n)
    (Nat.zero_add n) le_rfl (exteriorPower.ιMulti B 0 Fin.elim0) y
  convert this using 1
  refine Subtype.ext ?_
  simp [exteriorPower.coe_wedgeLeftMul, ExteriorAlgebra.ιMulti_zero_apply]

/-- **The differential of `gr^0 = ⋀ᵐ Ω_{B/R} / F^1`**, `A`-linear. -/
noncomputable def zeroGradedD (m : ℕ) :
    exteriorPower.wedgeZeroGraded (mapBaseChange R A B) m →ₗ[A]
      exteriorPower.wedgeZeroGraded (mapBaseChange R A B) (m + 1) where
  toFun := (Submodule.Quotient.restrictScalarsEquiv R (F 1 (m + 1))).toLinearMap ∘
    (Submodule.mapQ ((F 1 m).restrictScalars R) ((F 1 (m + 1)).restrictScalars R)
      (deRhamDifferential (A := R) m) fun _ hx => (Submodule.restrictScalars_mem R _ _).2
        (deRhamDifferential_mem_wedgeStep R A B ((Submodule.restrictScalars_mem R _ _).1 hx))) ∘
    (Submodule.Quotient.restrictScalarsEquiv R (F 1 m)).symm
  map_add' x y := by simp only [Function.comp_apply, map_add]
  map_smul' a q := by
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      change (Submodule.Quotient.mk (deRhamDifferential (A := R) m (a • y)) :
          exteriorPower.wedgeZeroGraded (mapBaseChange R A B) (m + 1)) =
        a • (Submodule.Quotient.mk (deRhamDifferential (A := R) m y) :
          exteriorPower.wedgeZeroGraded (mapBaseChange R A B) (m + 1))
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← algebraMap_smul B a y,
        ← algebraMap_smul B a]
      exact deRhamDifferential_smul_sub_mem R A B (k := 0) a (by rw [wedgeStep_zero]; trivial)

/-- The differential of `gr^0` sends the class of `y` to the class of `d y`. -/
@[simp]
theorem zeroGradedD_mk (m : ℕ) (y : ⋀[B]^m (Ω[B⁄R])) :
    zeroGradedD R A B m (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (deRhamDifferential (A := R) m y) :=
  rfl

/-- The differential of `gr^0` squares to zero. -/
theorem zeroGradedD_zeroGradedD (m : ℕ)
    (q : exteriorPower.wedgeZeroGraded (mapBaseChange R A B) m) :
    zeroGradedD R A B (m + 1) (zeroGradedD R A B m q) = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | H y => rw [zeroGradedD_mk, zeroGradedD_mk, deRhamDifferential_comp_self]; rfl

/-- The de Rham differential restricted to the `k`-th step. -/
noncomputable def stepD (k n : ℕ) : F k n →ₗ[R] F k (n + 1) where
  toFun x := ⟨deRhamDifferential (A := R) n x, deRhamDifferential_mem_wedgeStep R A B x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul (deRhamDifferential (A := R) n) r (x : ⋀[B]^n (Ω[B⁄R])))

/-- **The differential of `gr^k = F^k / F^{k+1}`**, `A`-linear. -/
noncomputable def gradedD (k n : ℕ) :
    exteriorPower.wedgeGraded (mapBaseChange R A B) k n →ₗ[A]
      exteriorPower.wedgeGraded (mapBaseChange R A B) k (n + 1) where
  toFun := (Submodule.Quotient.restrictScalarsEquiv R _).toLinearMap ∘
    (Submodule.mapQ (((F (k + 1) n).comap (F k n).subtype).restrictScalars R)
      (((F (k + 1) (n + 1)).comap (F k (n + 1)).subtype).restrictScalars R) (stepD R A B k n)
      fun x hx => (Submodule.restrictScalars_mem R _ _).2
        (deRhamDifferential_mem_wedgeStep R A B ((Submodule.restrictScalars_mem R _ _).1 hx))) ∘
    (Submodule.Quotient.restrictScalarsEquiv R _).symm
  map_add' x y := by simp only [Function.comp_apply, map_add]
  map_smul' a q := by
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      change (Submodule.Quotient.mk (stepD R A B k n (a • y)) :
          exteriorPower.wedgeGraded (mapBaseChange R A B) k (n + 1)) =
        a • (Submodule.Quotient.mk (stepD R A B k n y) :
          exteriorPower.wedgeGraded (mapBaseChange R A B) k (n + 1))
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
      change deRhamDifferential (A := R) n ((a • y : F k n) : ⋀[B]^n (Ω[B⁄R])) -
        a • deRhamDifferential (A := R) n (y : ⋀[B]^n (Ω[B⁄R])) ∈ _
      rw [Submodule.coe_smul_of_tower, ← algebraMap_smul B a (y : ⋀[B]^n (Ω[B⁄R])),
        ← algebraMap_smul B a]
      exact deRhamDifferential_smul_sub_mem R A B a y.2

/-- The differential of `gr^k` sends the class of `y` to the class of `d y`. -/
@[simp]
theorem gradedD_mk (k n : ℕ) (y : F k n) :
    gradedD R A B k n (Submodule.Quotient.mk y) = Submodule.Quotient.mk (stepD R A B k n y) :=
  rfl

/-- **The twisted identification** `a ⊗ [η] ↦ (-1)^{km} [a ∧ η]` of
`⋀ᵏ_A Ω_{A/R} ⊗_A gr^0_m` with `gr^k_{k+m}`. -/
noncomputable def gradedMulSigned {k m n : ℕ} (h : k + m = n) :
    ⋀[A]^k (Ω[A⁄R]) ⊗[A] exteriorPower.wedgeZeroGraded (mapBaseChange R A B) m →ₗ[A]
      exteriorPower.wedgeGraded (mapBaseChange R A B) k n :=
  ((-1 : A) ^ (k * m)) • gradedMul R A B h

/-- For `B` formally smooth over `A`, the twisted identification `gradedMulSigned` is bijective. -/
theorem gradedMulSigned_bijective [Algebra.FormallySmooth A B] {k m n : ℕ} (h : k + m = n) :
    Function.Bijective (gradedMulSigned R A B h) := by
  have hc : ((-1 : A) ^ (k * m)) * ((-1 : A) ^ (k * m)) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hinv : Function.Involutive fun z : exteriorPower.wedgeGraded (mapBaseChange R A B) k n =>
      ((-1 : A) ^ (k * m)) • z := fun z => by
    simp only [smul_smul, hc, one_smul]
  have e : ⇑(gradedMulSigned R A B h) =
      (fun z => ((-1 : A) ^ (k * m)) • z) ∘ gradedMul R A B h := rfl
  rw [e]
  exact hinv.bijective.comp (gradedMul_bijective R A B h)

/-- The left factor of `gradedMul`, read in the exterior algebra of `Ω_{B/R}`: the restriction
of `a` to `B`. -/
theorem coe_map_tensorBaseChange_one_tmul (k : ℕ) (a : ⋀[A]^k (Ω[A⁄R])) :
    ExteriorAlgebra.map (mapBaseChange R A B)
        ((exteriorPower.tensorBaseChange A B (Ω[A⁄R]) k (1 ⊗ₜ a) : ⋀[B]^k (B ⊗[A] Ω[A⁄R])) :
          ExteriorAlgebra B (B ⊗[A] Ω[A⁄R])) =
      (mapExteriorPower R A B k a : ExteriorAlgebra B (Ω[B⁄R])) := by
  rw [← map_tensorBaseChange_one_tmul, exteriorPower.coe_map]

/-- Left multiplication by the base change of a form from `A` is the wedge product with its
restriction to `B`. -/
private theorem wedgeLeftMul_tensorBaseChange_eq_wedgeMul {k m : ℕ} (a : ⋀[A]^k (Ω[A⁄R]))
    (y : ⋀[B]^m (Ω[B⁄R])) :
    exteriorPower.wedgeLeftMul (mapBaseChange R A B) (rfl : k + m = k + m)
        (exteriorPower.tensorBaseChange A B (Ω[A⁄R]) k (1 ⊗ₜ a)) y =
      exteriorPower.wedgeMul k m (mapExteriorPower R A B k a) y :=
  Subtype.ext (by
    rw [exteriorPower.coe_wedgeLeftMul, coe_map_tensorBaseChange_one_tmul,
      exteriorPower.wedgeMul_apply_coe])

/-- **The twisted identification commutes with the differentials**: `d ∘ μ = μ ∘ (1 ⊗ d)` for
`μ(a ⊗ [η]) = (-1)^{km} [a ∧ η]`. -/
theorem gradedD_gradedMulSigned {k m : ℕ} (a : ⋀[A]^k (Ω[A⁄R]))
    (q : exteriorPower.wedgeZeroGraded (mapBaseChange R A B) m) :
    gradedD R A B k (k + m) (gradedMulSigned R A B (k := k) (m := m) rfl (a ⊗ₜ q)) =
      gradedMulSigned R A B (k := k) (m := m + 1) (n := k + m + 1) rfl
        (a ⊗ₜ zeroGradedD R A B m q) := by
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    set ρ := exteriorPower.tensorBaseChange A B (Ω[A⁄R]) k (1 ⊗ₜ a)
    have key : (Submodule.Quotient.mk (stepD R A B k (k + m)
        ⟨exteriorPower.wedgeLeftMul (mapBaseChange R A B) (rfl : k + m = k + m) ρ y,
          exteriorPower.wedgeLeftMul_mem_wedgeStep (mapBaseChange R A B) (rfl : k + m = k + m)
            le_rfl ρ y⟩) :
          exteriorPower.wedgeGraded (mapBaseChange R A B) k (k + m + 1)) =
        ((-1 : A) ^ k) • Submodule.Quotient.mk
          ⟨exteriorPower.wedgeLeftMul (mapBaseChange R A B) (rfl : k + (m + 1) = k + m + 1) ρ
            (deRhamDifferential (A := R) m y),
          exteriorPower.wedgeLeftMul_mem_wedgeStep (mapBaseChange R A B)
            (rfl : k + (m + 1) = k + m + 1) le_rfl ρ (deRhamDifferential (A := R) m y)⟩ := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
      have hρ' := exteriorPower.wedgeLeftMul_mem_wedgeStep (mapBaseChange R A B)
        (by omega : (k + 1) + m = k + m + 1) le_rfl
        (exteriorPower.tensorBaseChange A B (Ω[A⁄R]) (k + 1)
          (1 ⊗ₜ deRhamDifferential (A := R) k a)) y
      convert hρ' using 1
      refine Subtype.ext ?_
      rw [exteriorPower.coe_wedgeLeftMul, coe_map_tensorBaseChange_one_tmul,
        mapExteriorPower_deRhamDifferential]
      show ((deRhamDifferential (A := R) (k + m)
          (exteriorPower.wedgeLeftMul (mapBaseChange R A B) rfl ρ y) : ⋀[B]^(k + m + 1) _) :
            ExteriorAlgebra B (Ω[B⁄R])) - ((((-1 : A) ^ k) • exteriorPower.wedgeLeftMul
              (mapBaseChange R A B) (rfl : k + (m + 1) = k + m + 1) ρ
              (deRhamDifferential (A := R) m y) : ⋀[B]^(k + m + 1) _) :
            ExteriorAlgebra B (Ω[B⁄R])) = _
      rw [wedgeLeftMul_tensorBaseChange_eq_wedgeMul R A B a y, coe_deRhamDifferential_wedgeMul,
        Submodule.coe_smul_of_tower, exteriorPower.coe_wedgeLeftMul,
        coe_map_tensorBaseChange_one_tmul, Algebra.smul_def, map_pow, map_neg, map_one,
        add_sub_cancel_right]
    simp only [gradedMulSigned, LinearMap.smul_apply, map_smul, gradedMul_tmul,
      zeroGradedD_mk, exteriorPower.gradedLeftMul_tmul_mk, gradedD_mk]
    rw [key, smul_smul, ← pow_add, mul_add, mul_one]

/-- **The comparison `Ω_{B/R} ⟶ Ω_{B/A}` commutes with the de Rham differentials**, on exterior
powers. -/
theorem map_exteriorPower_deRhamDifferential (n : ℕ) (x : ⋀[B]^n (Ω[B⁄R])) :
    exteriorPower.map (n + 1) (map R A B B) (deRhamDifferential (A := R) n x) =
      deRhamDifferential (A := A) n (exteriorPower.map n (map R A B B) x) := by
  have key : ((exteriorPower.map (n + 1) (map R A B B)).restrictScalars R) ∘ₗ
      deRhamDifferential (A := R) n =
      ((deRhamDifferential (A := A) (B := B) n).restrictScalars R) ∘ₗ
        (exteriorPower.map n (map R A B B)).restrictScalars R := by
    refine LinearMap.ext_on (Crystalline.span_range_smul_ιMulti_eq_top (R := R) (D R B)
      (span_range_derivation R B) n) ?_
    rintro _ ⟨c, rfl⟩
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      deRhamDifferential_smul_ιMulti_D, map_smul, exteriorPower.map_apply_ιMulti]
    have h₁ : (fun i => map R A B B (D R B (c i))) = fun i => D A B (c i) := by
      funext i; simp [map_D]
    have h₂ : (fun i : Fin n => map R A B B (D R B (c i.succ))) = fun i => D A B (c i.succ) := by
      funext i; simp [map_D]
    simp only [Function.comp_def, h₁, h₂]
    exact (deRhamDifferential_smul_ιMulti_D (A := A) n c).symm
  exact LinearMap.congr_fun key x

/-- **`gr^0 ≅ ⋀ᵐ Ω_{B/A}` commutes with the differentials.** -/
theorem wedgeZeroGradedEquiv_zeroGradedD [Algebra.FormallySmooth A B] (m : ℕ)
    (q : exteriorPower.wedgeZeroGraded (mapBaseChange R A B) m) :
    wedgeZeroGradedEquiv R A B (m + 1) (zeroGradedD R A B m q) =
      deRhamDifferential (A := A) m (wedgeZeroGradedEquiv R A B m q) := by
  induction q using Submodule.Quotient.induction_on with
  | H y => rw [zeroGradedD_mk, wedgeZeroGradedEquiv_mk, wedgeZeroGradedEquiv_mk,
      map_exteriorPower_deRhamDifferential]

/-- **The differential of `gr^k` on a product with a form from `A`**:
`d [ρ(a) ∧ y] = (-1)^k [ρ(a) ∧ d y]` modulo `F^{k+1}`. -/
theorem gradedD_mk_wedgeMul {k m : ℕ} (a : ⋀[A]^k (Ω[A⁄R])) (y : ⋀[B]^m (Ω[B⁄R]))
    (hy : exteriorPower.wedgeMul k m (mapExteriorPower R A B k a) y ∈ F k (k + m))
    (hy' : exteriorPower.wedgeMul k (m + 1) (mapExteriorPower R A B k a)
      (deRhamDifferential (A := R) m y) ∈ F k (k + (m + 1))) :
    gradedD R A B k (k + m) (Submodule.Quotient.mk ⟨exteriorPower.wedgeMul k m
        (mapExteriorPower R A B k a) y, hy⟩) =
      ((-1 : A) ^ k) • Submodule.Quotient.mk ⟨exteriorPower.wedgeMul k (m + 1)
        (mapExteriorPower R A B k a) (deRhamDifferential (A := R) m y), hy'⟩ := by
  have hw : ∀ (j : ℕ) (z : ⋀[B]^j (Ω[B⁄R])) (hz) ,
      (Submodule.Quotient.mk ⟨exteriorPower.wedgeMul k j (mapExteriorPower R A B k a) z, hz⟩ :
        exteriorPower.wedgeGraded (mapBaseChange R A B) k (k + j)) =
      ((-1 : A) ^ (k * j)) • gradedMulSigned R A B (k := k) (m := j) rfl
        (a ⊗ₜ Submodule.Quotient.mk z) := by
    intro j z hz
    rw [gradedMulSigned, LinearMap.smul_apply, smul_smul, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul, gradedMul_tmul, exteriorPower.gradedLeftMul_tmul_mk]
    congr 2
    exact (wedgeLeftMul_tensorBaseChange_eq_wedgeMul R A B a z).symm
  rw [hw m y hy, map_smul, gradedD_gradedMulSigned, zeroGradedD_mk, hw (m + 1) _ hy', smul_smul,
    ← pow_add]
  congr 1
  rw [show k + k * (m + 1) = k * m + 2 * k by ring, pow_add (-1 : A) (k * m) (2 * k),
    pow_mul (-1 : A) 2 k, neg_one_sq, one_pow, mul_one]

end KaehlerDifferential
