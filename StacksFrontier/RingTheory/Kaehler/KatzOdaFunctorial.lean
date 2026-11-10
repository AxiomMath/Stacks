module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaGraded
public import StacksFrontier.RingTheory.DeRham.WedgeLeibniz
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy

/-!
# The filtration of `Ω^•_{B/R}` by the forms pulled back from `A`: generators, `d`, functoriality

Let `R → A → B` be ring maps. The filtration `F^k ⋀ⁿ Ω_{B/R}` by the wedges with forms pulled back
from `A` (`exteriorPower.wedgeStep (KaehlerDifferential.mapBaseChange R A B) k n`, see
`StacksFrontier.RingTheory.Kaehler.KatzOdaGraded`) is generated, as a `B`-module, by the wedges

`d a₁ ∧ ⋯ ∧ d a_j ∧ η`,  `j ≥ k`, `a_i ∈ A`, `η ∈ ⋀ⁿ⁻ʲ Ω_{B/R}`

(`KaehlerDifferential.wedgeStep_le_of`). From this description:

* the de Rham differential carries `F^k` into `F^k`, since `d a₁ ∧ ⋯ ∧ d a_j` is closed
  (`KaehlerDifferential.deRhamDifferential_mem_wedgeStep`);
* the restriction of forms along a map of `A`-algebras `B → B'` carries `F^k` into `F^k`
  (`KaehlerDifferential.mapExteriorPower_mem_wedgeStep`);
* the wedge with a form `d a` pulled back from `A` raises the filtration by one
  (`KaehlerDifferential.ι_D_mul_mem_wedgeStep_succ`).

These are the compatibilities of the filtration of [Stacks, Section 0FMK] with the differentials
and the restriction maps of a Čech complex, as in [Stacks, Tag 0FUM].

## Main definitions

* `KaehlerDifferential.dWedge`: the wedge `d a₁ ∧ ⋯ ∧ d a_j` in `⋀ʲ Ω_{B/R}` of the differentials
  of elements of `A`.

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

/-- **The wedge `d a₁ ∧ ⋯ ∧ d a_j` of the differentials of elements of `A`**, as an element of
`⋀ʲ_B Ω_{B/R}`. -/
noncomputable def dWedge {j : ℕ} (a : Fin j → A) : ⋀[B]^j (Ω[B⁄R]) :=
  exteriorPower.ιMulti B j fun i => D R B (algebraMap A B (a i))

omit [Algebra R A] [IsScalarTower R A B] in
/-- In the exterior algebra, `dWedge R A B a` is the product `d a₁ ∧ ⋯ ∧ d a_j`. -/
theorem coe_dWedge {j : ℕ} (a : Fin j → A) :
    (dWedge R A B a : ExteriorAlgebra B (Ω[B⁄R])) =
      ExteriorAlgebra.ιMulti B j fun i => D R B (algebraMap A B (a i)) :=
  rfl

omit [Algebra R B] [IsScalarTower R A B] in
/-- The `B`-module `B ⊗_A Ω_{A/R}` is spanned by the elements `1 ⊗ d a`. -/
theorem span_one_tmul_D :
    Submodule.span B (Set.range fun a : A => (1 : B) ⊗ₜ[A] D R A a) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  clear ‹z ∈ ⊤›
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => exact add_mem hx hy
  | tmul b ω =>
    have hω : ω ∈ Submodule.span A (Set.range (D R A)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [show b ⊗ₜ[A] D R A a = b • ((1 : B) ⊗ₜ[A] D R A a) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [← TensorProduct.smul_tmul, ← algebraMap_smul B c b, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ _ hx

/-- The image of `ιMulti (1 ⊗ d a)` under `⋀ʲ` of `B ⊗_A Ω_{A/R} ⟶ Ω_{B/R}` is `dWedge`. -/
theorem map_ιMulti_one_tmul_D {j : ℕ} (a : Fin j → A) :
    ExteriorAlgebra.map (mapBaseChange R A B)
        (ExteriorAlgebra.ιMulti B j fun i => (1 : B) ⊗ₜ[A] D R A (a i)) =
      (dWedge R A B a : ExteriorAlgebra B (Ω[B⁄R])) := by
  rw [ExteriorAlgebra.map_apply_ιMulti, coe_dWedge]
  congr 1
  funext i
  simp [mapBaseChange_tmul, map_D]

/-- For `k ≤ j`, the wedge `d a₁ ∧ ⋯ ∧ d a_j ∧ y` of `j` differentials of elements of `A` with a
form `y ∈ ⋀ᵐ Ω_{B/R}` lies in `F^k ⋀ⁿ Ω_{B/R}`, where `j + m = n`. -/
theorem dWedge_mul_mem_wedgeStep {k j m n : ℕ} (h : j + m = n) (hk : k ≤ j) (a : Fin j → A)
    (y : ⋀[B]^m (Ω[B⁄R])) :
    (⟨(dWedge R A B a : ExteriorAlgebra B (Ω[B⁄R])) * y,
        exteriorPower.mul_mem_of_mem h (dWedge R A B a).2 y.2⟩ : ⋀[B]^n (Ω[B⁄R])) ∈
      exteriorPower.wedgeStep (mapBaseChange R A B) k n := by
  have := exteriorPower.wedgeLeftMul_mem_wedgeStep (mapBaseChange R A B) h hk
    (exteriorPower.ιMulti B j fun i => (1 : B) ⊗ₜ[A] D R A (a i)) y
  convert this using 1
  refine Subtype.ext ?_
  rw [exteriorPower.coe_wedgeLeftMul, exteriorPower.ιMulti_apply_coe, map_ιMulti_one_tmul_D]

/-- **The generators of the filtration**: a submodule of `⋀ⁿ Ω_{B/R}` containing every
`d a₁ ∧ ⋯ ∧ d a_j ∧ η` with `j ≥ k` contains the `k`-th step. -/
theorem wedgeStep_le_of {k n : ℕ} (P : Submodule B (⋀[B]^n (Ω[B⁄R])))
    (hP : ∀ (j m : ℕ) (h : j + m = n), k ≤ j → ∀ (a : Fin j → A) (y : ⋀[B]^m (Ω[B⁄R])),
      (⟨(dWedge R A B a : ExteriorAlgebra B (Ω[B⁄R])) * y,
        exteriorPower.mul_mem_of_mem h (dWedge R A B a).2 y.2⟩ : ⋀[B]^n (Ω[B⁄R])) ∈ P) :
    exteriorPower.wedgeStep (mapBaseChange R A B) k n ≤ P := by
  rw [exteriorPower.wedgeStep_le_iff]
  intro j m h hk x y
  let L : ⋀[B]^j (B ⊗[A] Ω[A⁄R]) →ₗ[B] ⋀[B]^n (Ω[B⁄R]) :=
    { toFun := fun x => exteriorPower.wedgeLeftMul (mapBaseChange R A B) h x y
      map_add' := fun x x' => Subtype.ext (by simp [add_mul])
      map_smul' := fun c x => Subtype.ext (by simp [Algebra.smul_mul_assoc]) }
  suffices hL : (⊤ : Submodule B (⋀[B]^j (B ⊗[A] Ω[A⁄R]))) ≤ P.comap L from hL trivial
  rw [← exteriorPower.ιMulti_span_of_span B j _ (span_one_tmul_D R A B), Submodule.span_le]
  rintro _ ⟨e, he, rfl⟩
  choose a ha using fun i => he ⟨i, rfl⟩
  have he' : e = fun i => (1 : B) ⊗ₜ[A] D R A (a i) := funext fun i => (ha i).symm
  subst he'
  change L _ ∈ P
  convert hP j m h hk a y using 1
  refine Subtype.ext ?_
  change ExteriorAlgebra.map (mapBaseChange R A B) _ * _ = _
  rw [exteriorPower.ιMulti_apply_coe, map_ιMulti_one_tmul_D]
  rfl

/-- A linear map carries `F^k` into `F^k'` once it carries the generators of `F^k` into `F^k'`. -/
private theorem map_mem_wedgeStep_of {k k' n n' : ℕ} (L : ⋀[B]^n (Ω[B⁄R]) →ₗ[B] ⋀[B]^n' (Ω[B⁄R]))
    (hL : ∀ (j m : ℕ) (h : j + m = n), k ≤ j → ∀ (a : Fin j → A) (y : ⋀[B]^m (Ω[B⁄R])),
      L ⟨(dWedge R A B a : ExteriorAlgebra B (Ω[B⁄R])) * y,
        exteriorPower.mul_mem_of_mem h (dWedge R A B a).2 y.2⟩ ∈
        exteriorPower.wedgeStep (mapBaseChange R A B) k' n')
    {x : ⋀[B]^n (Ω[B⁄R])} (hx : x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k n) :
    L x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k' n' :=
  wedgeStep_le_of R A B ((exteriorPower.wedgeStep (mapBaseChange R A B) k' n').comap L) hL hx

omit [Algebra R A] [IsScalarTower R A B] in
/-- `d a₁ ∧ ⋯ ∧ d a_j` is closed. -/
theorem deRhamDifferential_dWedge {j : ℕ} (a : Fin j → A) :
    deRhamDifferential (A := R) j (dWedge R A B a) = 0 := by
  have h := deRhamDifferential_smul_ιMulti_D (A := R) j
    (Fin.cons (1 : B) fun i => algebraMap A B (a i))
  simp only [Fin.cons_zero, Fin.cons_succ, one_smul] at h
  rw [dWedge, h]
  refine (exteriorPower.ιMulti B (j + 1)).map_coord_zero 0 ?_
  simp

/-- **The filtration is a right ideal**: wedging an element of `F^k` on the right with any form
stays in `F^k`. -/
theorem mul_mem_wedgeStep {k n l : ℕ} {x : ⋀[B]^n (Ω[B⁄R])}
    (hx : x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k n) (ω : ⋀[B]^l (Ω[B⁄R])) :
    (⟨(x : ExteriorAlgebra B (Ω[B⁄R])) * ω, exteriorPower.mul_mem_of_mem rfl x.2 ω.2⟩ :
      ⋀[B]^(n + l) (Ω[B⁄R])) ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k (n + l) := by
  let L := LinearMap.flip (exteriorPower.wedgeMul (R := B) (M := Ω[B⁄R]) n l) ω
  refine map_mem_wedgeStep_of R A B L (fun j m h hk a y => ?_) hx
  have := dWedge_mul_mem_wedgeStep R A B (k := k) (m := m + l) (n := n + l) (by omega) hk a
    ⟨(y : ExteriorAlgebra B (Ω[B⁄R])) * ω, exteriorPower.mul_mem_of_mem rfl y.2 ω.2⟩
  convert this using 1
  exact Subtype.ext (mul_assoc _ _ _)

/-- `d (b • x) = b • d x + (-1)ⁿ x ∧ d b`, the Leibniz rule with the function on the right. -/
theorem coe_deRhamDifferential_smul {n : ℕ} (b : B) (x : ⋀[B]^n (Ω[B⁄R])) :
    ((deRhamDifferential (A := R) n (b • x) : ⋀[B]^(n + 1) (Ω[B⁄R])) :
        ExteriorAlgebra B (Ω[B⁄R])) =
      b • ((deRhamDifferential (A := R) n x : ⋀[B]^(n + 1) (Ω[B⁄R])) :
        ExteriorAlgebra B (Ω[B⁄R])) +
      (-1) ^ n * ((x : ExteriorAlgebra B (Ω[B⁄R])) *
        ((deRhamDifferential (A := R) 0 ((exteriorPower.zeroEquiv B (Ω[B⁄R])).symm b) :
          ⋀[B]^(0 + 1) (Ω[B⁄R])) : ExteriorAlgebra B (Ω[B⁄R]))) := by
  have h := coe_deRhamDifferential_wedgeMul (A := R) n 0 x
    ((exteriorPower.zeroEquiv B (Ω[B⁄R])).symm b)
  have hb : (((exteriorPower.zeroEquiv B (Ω[B⁄R])).symm b : ⋀[B]^0 (Ω[B⁄R])) :
      ExteriorAlgebra B (Ω[B⁄R])) = algebraMap B _ b := by
    simp [exteriorPower.zeroEquiv, Algebra.algebraMap_eq_smul_one]
  have hx : exteriorPower.wedgeMul n 0 x ((exteriorPower.zeroEquiv B (Ω[B⁄R])).symm b) = b • x :=
    Subtype.ext (by
      rw [exteriorPower.wedgeMul_apply_coe, hb, SetLike.val_smul, Algebra.smul_def,
        Algebra.commutes])
  rw [hx] at h
  refine h.trans ?_
  rw [hb, ← Algebra.commutes, ← Algebra.smul_def]

/-- **The de Rham differential preserves the filtration.** -/
theorem deRhamDifferential_mem_wedgeStep {k n : ℕ} {x : ⋀[B]^n (Ω[B⁄R])}
    (hx : x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k n) :
    deRhamDifferential (A := R) n x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k (n + 1) := by
  let Q : Submodule B (⋀[B]^n (Ω[B⁄R])) :=
    { carrier := {x | x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k n ∧
        deRhamDifferential (A := R) n x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k (n + 1)}
      add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, by rw [map_add]; exact add_mem hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun b x hx => by
        refine ⟨Submodule.smul_mem _ b hx.1, ?_⟩
        have hd : deRhamDifferential (A := R) n (b • x) =
            b • deRhamDifferential (A := R) n x + (-1 : B) ^ n •
              ⟨(x : ExteriorAlgebra B (Ω[B⁄R])) *
                (deRhamDifferential (A := R) 0 ((exteriorPower.zeroEquiv B (Ω[B⁄R])).symm b) :
                  ExteriorAlgebra B (Ω[B⁄R])),
                exteriorPower.mul_mem_of_mem rfl x.2 (deRhamDifferential (A := R) 0 _).2⟩ := by
          refine Subtype.ext ?_
          rw [coe_deRhamDifferential_smul, Submodule.coe_add, SetLike.val_smul, SetLike.val_smul,
            Algebra.smul_def ((-1 : B) ^ n), map_pow, map_neg, map_one]
        rw [hd]
        exact add_mem (Submodule.smul_mem _ _ hx.2)
          (Submodule.smul_mem _ _ (mul_mem_wedgeStep R A B hx.1 _)) }
  suffices h : exteriorPower.wedgeStep (mapBaseChange R A B) k n ≤ Q from (h hx).2
  refine wedgeStep_le_of R A B _ fun j m h hk a y => ⟨dWedge_mul_mem_wedgeStep R A B h hk a y, ?_⟩
  have hd := coe_deRhamDifferential_wedgeMul (A := R) j m (dWedge R A B a) y
  rw [deRhamDifferential_dWedge, ZeroMemClass.coe_zero, zero_mul, zero_add] at hd
  have hmem := dWedge_mul_mem_wedgeStep R A B (k := k) (m := m + 1) (n := n + 1) (by omega) hk a
    (deRhamDifferential (A := R) m y)
  have hsmul := Submodule.smul_mem (exteriorPower.wedgeStep (mapBaseChange R A B) k (n + 1))
    ((-1 : B) ^ j) hmem
  convert hsmul using 1
  refine Subtype.ext ?_
  subst h
  rw [SetLike.val_smul, Algebra.smul_def, map_pow, map_neg, map_one]
  exact hd

/-- **The wedge on the left with a form `d a` pulled back from `A` raises the filtration.** -/
theorem ι_D_mul_mem_wedgeStep_succ {k n : ℕ} {x : ⋀[B]^n (Ω[B⁄R])}
    (hx : x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k n) (a : A) :
    (⟨ExteriorAlgebra.ι B (D R B (algebraMap A B a)) * x,
        exteriorPower.mul_mem_of_mem (by omega : 1 + n = n + 1)
          (by
            change _ ∈ LinearMap.range (ExteriorAlgebra.ι B) ^ 1
            rw [pow_one]
            exact LinearMap.mem_range_self _ _) x.2⟩ :
      ⋀[B]^(n + 1) (Ω[B⁄R])) ∈ exteriorPower.wedgeStep (mapBaseChange R A B) (k + 1) (n + 1) := by
  let L : ⋀[B]^n (Ω[B⁄R]) →ₗ[B] ⋀[B]^(n + 1) (Ω[B⁄R]) :=
    { toFun := fun x => ⟨ExteriorAlgebra.ι B (D R B (algebraMap A B a)) * x,
        exteriorPower.mul_mem_of_mem (by omega : 1 + n = n + 1)
          (by
            change _ ∈ LinearMap.range (ExteriorAlgebra.ι B) ^ 1
            rw [pow_one]
            exact LinearMap.mem_range_self _ _) x.2⟩
      map_add' := fun x x' => Subtype.ext (by simp [mul_add])
      map_smul' := fun c x => Subtype.ext (by simp [Algebra.mul_smul_comm]) }
  refine map_mem_wedgeStep_of R A B L (fun j m h hk α y => ?_) hx
  have := dWedge_mul_mem_wedgeStep R A B (k := k + 1) (j := j + 1) (m := m) (n := n + 1)
    (by omega) (by omega) (Fin.cons a α) y
  convert this using 1
  refine Subtype.ext ?_
  change ExteriorAlgebra.ι B _ * ((dWedge R A B α : ExteriorAlgebra B (Ω[B⁄R])) *
    (y : ExteriorAlgebra B (Ω[B⁄R]))) =
      (dWedge R A B (Fin.cons a α) : ExteriorAlgebra B (Ω[B⁄R])) * (y : ExteriorAlgebra B (Ω[B⁄R]))
  rw [← mul_assoc, coe_dWedge, coe_dWedge, ExteriorAlgebra.ιMulti_succ_apply]
  simp only [Fin.cons_zero]
  rfl

/-- **On the graded pieces the de Rham differential is `A`-linear**: for `x ∈ F^k`,
`d (a • x) - a • d x = d a ∧ x` lies in `F^{k+1}`. -/
theorem deRhamDifferential_smul_sub_mem {k n : ℕ} (a : A) {x : ⋀[B]^n (Ω[B⁄R])}
    (hx : x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k n) :
    deRhamDifferential (A := R) n (algebraMap A B a • x) -
        algebraMap A B a • deRhamDifferential (A := R) n x ∈
      exteriorPower.wedgeStep (mapBaseChange R A B) (k + 1) (n + 1) := by
  convert ι_D_mul_mem_wedgeStep_succ R A B hx a using 1
  refine Subtype.ext ?_
  set b := algebraMap A B a
  let ξ : ⋀[B]^0 (Ω[B⁄R]) := b • exteriorPower.ιMulti B 0 Fin.elim0
  have hξ : (ξ : ExteriorAlgebra B (Ω[B⁄R])) = algebraMap B _ b := by
    simp [ξ, Algebra.algebraMap_eq_smul_one]
  have hdξ : ((deRhamDifferential (A := R) 0 ξ : ⋀[B]^(0 + 1) (Ω[B⁄R])) :
      ExteriorAlgebra B (Ω[B⁄R])) = ExteriorAlgebra.ι B (D R B b) := by
    have h := deRhamDifferential_smul_ιMulti_D (A := R) 0 (fun _ : Fin 1 => b)
    change deRhamDifferential (A := R) 0 ξ = _ at h
    rw [h, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
    simp
  have hL := coe_deRhamDifferential_wedgeMul (A := R) 0 n ξ x
  have hw : ((exteriorPower.wedgeMul 0 n ξ x : ⋀[B]^(0 + n) (Ω[B⁄R])) :
      ExteriorAlgebra B (Ω[B⁄R])) = ((b • x : ⋀[B]^n (Ω[B⁄R])) : ExteriorAlgebra B (Ω[B⁄R])) := by
    rw [exteriorPower.wedgeMul_apply_coe, hξ, SetLike.val_smul, Algebra.smul_def]
  rw [coe_deRhamDifferential_congr (Nat.zero_add n) hw, hdξ, pow_zero, one_mul, hξ,
    ← Algebra.smul_def] at hL
  rw [Submodule.coe_sub, hL, SetLike.val_smul, add_sub_cancel_right]


section Functorial

variable (B' : Type u) [CommRing B'] [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
  [Algebra B B'] [IsScalarTower R B B'] [IsScalarTower A B B']

/-- Restriction of forms along `B → B'` is multiplicative. -/
private theorem mapExteriorPower_wedgeMul_aux (p q : ℕ) (x : ⋀[B]^p (Ω[B⁄R]))
    (y : ⋀[B]^q (Ω[B⁄R])) :
    mapExteriorPower R B B' (p + q) (exteriorPower.wedgeMul p q x y) =
      exteriorPower.wedgeMul p q (mapExteriorPower R B B' p x) (mapExteriorPower R B B' q y) := by
  have key : ∀ (u : Fin p → Ω[B⁄R]) (v : Fin q → Ω[B⁄R]),
      mapExteriorPower R B B' (p + q)
          (exteriorPower.wedgeMul p q (exteriorPower.ιMulti B p u) (exteriorPower.ιMulti B q v)) =
        exteriorPower.wedgeMul p q (mapExteriorPower R B B' p (exteriorPower.ιMulti B p u))
          (mapExteriorPower R B B' q (exteriorPower.ιMulti B q v)) := by
    intro u v
    rw [exteriorPower.wedgeMul_ιMulti, mapExteriorPower_ιMulti, mapExteriorPower_ιMulti,
      mapExteriorPower_ιMulti, exteriorPower.wedgeMul_ιMulti]
    congr 1
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have smul_map : ∀ (r : ℕ) (c : B) (z : ⋀[B]^r (Ω[B⁄R])),
      mapExteriorPower R B B' r (c • z) = algebraMap B B' c • mapExteriorPower R B B' r z :=
    fun r c z => by rw [map_smul, algebraMap_smul]
  have hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B p)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  have hy : y ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B q)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem _ hx' =>
    obtain ⟨u, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem _ hy' => obtain ⟨v, rfl⟩ := hy'; exact key u v
    | zero => simp
    | add y y' _ _ h h' => simp only [map_add, h, h']
    | smul c y _ h =>
      rw [map_smul, smul_map, h, smul_map, map_smul]
  | zero => simp
  | add x x' _ _ h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | smul c x _ h =>
    rw [map_smul, LinearMap.smul_apply, smul_map, h, smul_map, map_smul, LinearMap.smul_apply]

omit [Algebra R A] [IsScalarTower R A B] [IsScalarTower R A B'] in
/-- Restriction of forms along `B → B'` carries `d a₁ ∧ ⋯ ∧ d a_j ∧ η` to
`d a₁ ∧ ⋯ ∧ d a_j ∧ (restriction of η)`. -/
theorem mapExteriorPower_wedgeMul_dWedge {j m : ℕ} (a : Fin j → A) (y : ⋀[B]^m (Ω[B⁄R])) :
    mapExteriorPower R B B' (j + m) (exteriorPower.wedgeMul j m (dWedge R A B a) y) =
      exteriorPower.wedgeMul j m (dWedge R A B' a) (mapExteriorPower R B B' m y) := by
  rw [mapExteriorPower_wedgeMul_aux]
  congr 2
  rw [dWedge, dWedge, mapExteriorPower_ιMulti]
  congr 1
  funext i
  simp [map_D, ← IsScalarTower.algebraMap_apply]

/-- **Restriction of forms along a map of `A`-algebras preserves the filtration.** -/
theorem mapExteriorPower_mem_wedgeStep {k n : ℕ} {x : ⋀[B]^n (Ω[B⁄R])}
    (hx : x ∈ exteriorPower.wedgeStep (mapBaseChange R A B) k n) :
    mapExteriorPower R B B' n x ∈ exteriorPower.wedgeStep (mapBaseChange R A B') k n := by
  let P : Submodule B (⋀[B]^n (Ω[B⁄R])) :=
    { carrier :=
        {x | mapExteriorPower R B B' n x ∈ exteriorPower.wedgeStep (mapBaseChange R A B') k n}
      add_mem' := fun hx hy => by simp only [Set.mem_ofPred_eq, map_add]; exact add_mem hx hy
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact zero_mem _
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, map_smul]
        rw [← algebraMap_smul B' c]
        exact Submodule.smul_mem _ _ hx }
  suffices h : exteriorPower.wedgeStep (mapBaseChange R A B) k n ≤ P from h hx
  refine wedgeStep_le_of R A B P fun j m h hk a y => ?_
  subst h
  change mapExteriorPower R B B' (j + m) _ ∈
    exteriorPower.wedgeStep (mapBaseChange R A B') k (j + m)
  have h₁ : (⟨(dWedge R A B a : ExteriorAlgebra B (Ω[B⁄R])) * y,
      exteriorPower.mul_mem_of_mem rfl (dWedge R A B a).2 y.2⟩ : ⋀[B]^(j + m) (Ω[B⁄R])) =
      exteriorPower.wedgeMul j m (dWedge R A B a) y :=
    Subtype.ext (exteriorPower.wedgeMul_apply_coe _ _ _ _).symm
  rw [h₁, mapExteriorPower_wedgeMul_dWedge]
  convert dWedge_mul_mem_wedgeStep R A B' rfl hk a (mapExteriorPower R B B' m y) using 1
  exact Subtype.ext (exteriorPower.wedgeMul_apply_coe _ _ _ _)

/-- **Restriction of forms along `B → B'` is multiplicative.** -/
theorem mapExteriorPower_wedgeMul (p q : ℕ) (x : ⋀[B]^p (Ω[B⁄R])) (y : ⋀[B]^q (Ω[B⁄R])) :
    mapExteriorPower R B B' (p + q) (exteriorPower.wedgeMul p q x y) =
      exteriorPower.wedgeMul p q (mapExteriorPower R B B' p x) (mapExteriorPower R B B' q y) :=
  mapExteriorPower_wedgeMul_aux R B B' p q x y

end Functorial

end KaehlerDifferential
