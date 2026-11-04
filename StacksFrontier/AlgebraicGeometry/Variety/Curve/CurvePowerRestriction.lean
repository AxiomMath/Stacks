/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerDivisors
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianTrace
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.GraphFibreDegree

/-!
# Restricting intersection numbers on `C^m` to fibres and diagonals

Let `C` be a smooth proper curve over an algebraically closed field `k`, with a rational point
`c₀`, and let `C^m` be its fibre powers (`Stacks.CurvePower.power`). This file proves two
restriction rules for intersection numbers on `C^m`:

* **fibres.** For a class `A` on `C` (on `C^1`, which is `C`), the class `p_i^* A` pulled back
  along the `i`-th coordinate meets the other `m` classes like `deg A` copies of the fibre
  `{c₀}` in slot `i`:
  `(p_i^* A · x_1 ⋯ x_m · C^(m+1)) = deg A · (ι_i^* x_1 ⋯ ι_i^* x_m · C^m)`,
  where `ι_i : C^m ⟶ C^(m+1)` inserts `c₀` in slot `i`
  (`Stacks.CurvePower.powerForm_cons_coordPullback`).
* **diagonals.** The diagonal `Δ_{jl} = {x_j = x_l}` meets the other classes like their
  restrictions along the map `C^(m+1) ⟶ C^(m+2)` which doubles a coordinate
  (`Stacks.CurvePower.powerForm_cons_diagonal`).

## Main definitions

* `Stacks.CurvePower.insertPoint`: `ι_i`, inserting `c₀` in slot `i`.
* `Stacks.CurvePower.mergeMap`: the map `C^(n+1) ⟶ C^(n+2)` doubling a coordinate.
* `Stacks.CurvePower.curveDeg`: the degree of a class on `C^1`.
* `Stacks.CurvePower.diagClass`: the class of the diagonal `{x_0 = x_1}` on `C^2`.

## Main results

* `Stacks.CurvePower.powerForm_cons_coordPullback`: the fibre rule in slot `i`.
* `Stacks.CurvePower.powerForm_cons_diagonal`: the diagonal rule.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.CurvePower

section Maps

variable {S : Scheme.{u}} (C : Over S)

/-- The `lift` of the coordinates of `C^m` is the identity. -/
theorem lift_coord_self (m : ℕ) : lift m (coord C m) = 𝟙 (power C m) :=
  hom_ext m fun i => by simp

/-- The structure morphism `C^m ⟶ C^0` of a power. -/
abbrev toPowerZero (m : ℕ) : power C m ⟶ power C 0 :=
  toUnit (power C m)

variable (c₀ : power C 0 ⟶ C)

/-- **`ι_i : C^m ⟶ C^(m+1)`**, inserting the point `c₀` in slot `i`. -/
def insertPoint (m : ℕ) (i : Fin (m + 1)) : power C m ⟶ power C (m + 1) :=
  lift (m + 1) (Fin.insertNth i (toPowerZero C m ≫ c₀) (coord C m))

/-- The `i`-th coordinate of `ι_i` is the constant map `c₀`. -/
@[reassoc (attr := simp)]
theorem insertPoint_coord_self (m : ℕ) (i : Fin (m + 1)) :
    insertPoint C c₀ m i ≫ coord C (m + 1) i = toPowerZero C m ≫ c₀ := by
  rw [insertPoint, lift_coord, Fin.insertNth_apply_same]

/-- The `i.succAbove j`-th coordinate of `ι_i` is the `j`-th coordinate. -/
@[reassoc (attr := simp)]
theorem insertPoint_coord_succAbove (m : ℕ) (i : Fin (m + 1)) (j : Fin m) :
    insertPoint C c₀ m i ≫ coord C (m + 1) (i.succAbove j) = coord C m j := by
  rw [insertPoint, lift_coord, Fin.insertNth_apply_succAbove]

/-- The graph section of `y : C^m ⟶ C` is the morphism `(y, 𝟙) : C^m ⟶ C^(m+1)`. -/
theorem pointGraph_eq_lift (m : ℕ) (y : power C m ⟶ C) :
    Stacks.Hilbert.pointGraph C (power C m) y = (lift (m + 1) (Fin.cons y (coord C m))).left := by
  refine pullback.hom_ext ?_ ?_
  · show _ = (lift (m + 1) (Fin.cons y (coord C m)) ≫ fst C (power C m)).left
    rw [lift_succ_fst]
    simp [Stacks.Hilbert.pointGraph]
  · show _ = (lift (m + 1) (Fin.cons y (coord C m)) ≫ snd C (power C m)).left
    rw [lift_succ_snd]
    simp only [Fin.cons_succ]
    rw [lift_coord_self]
    simp [Stacks.Hilbert.pointGraph]

/-- The graph section of the constant map `c₀` is `ι_0`. -/
theorem pointGraph_point_eq_insertPoint (m : ℕ) :
    Stacks.Hilbert.pointGraph C (power C m) (toPowerZero C m ≫ c₀) =
      (insertPoint C c₀ m 0).left := by
  rw [pointGraph_eq_lift, insertPoint, Fin.insertNth_zero']

/-- The projection `C^(m+1) ⟶ C^1` to the first coordinate, as a morphism of powers. -/
abbrev firstProj (m : ℕ) : power C (m + 1) ⟶ power C 1 :=
  reindex C (fun _ : Fin 1 => (0 : Fin (m + 1)))

/-- The first projection `C^(m+1) ⟶ C^1` is the base change of `C ⟶ S` along `C^m ⟶ S`. -/
theorem firstProj_left (m : ℕ) :
    (firstProj C m).left = Stacks.Hilbert.familyBaseChangeMap C (toPowerZero C m) := by
  refine pullback.hom_ext ?_ ?_
  · show (firstProj C m ≫ fst C (power C 0)).left = _
    rw [← coord_zero, reindex_coord, coord_zero]
    simp [Stacks.Hilbert.familyBaseChangeMap]
  · have h1 : (firstProj C m).left ≫ (power C 1).hom = (power C (m + 1)).hom :=
      Over.w (firstProj C m)
    have h2 : pullback.snd C.hom (power C 0).hom = (power C 1).hom := by
      show _ = pullback.fst C.hom (power C 0).hom ≫ C.hom
      rw [pullback.condition]
      exact (Category.comp_id _).symm
    rw [h2]
    refine h1.trans ?_
    show _ = pullback.map C.hom (power C m).hom C.hom (power C 0).hom (𝟙 _)
      (toPowerZero C m).left (𝟙 _) (by simp) (by simp) ≫ pullback.fst C.hom (power C 0).hom ≫ C.hom
    rw [pullback.lift_fst_assoc, Category.comp_id]
    rfl

/-- The base change map along `g : T' ⟶ T` is `C ⊗ T' ⟶ C ⊗ T`, `(c, t) ↦ (c, g t)`. -/
theorem familyBaseChangeMap_eq {T T' : Over S} (g : T' ⟶ T) :
    Stacks.Hilbert.familyBaseChangeMap C g =
      (CartesianMonoidalCategory.lift (fst C T') (snd C T' ≫ g)).left := by
  refine pullback.hom_ext ?_ ?_
  · show _ = (CartesianMonoidalCategory.lift (fst C T') (snd C T' ≫ g) ≫ fst C T).left
    simp [Stacks.Hilbert.familyBaseChangeMap]
  · show _ = (CartesianMonoidalCategory.lift (fst C T') (snd C T' ≫ g) ≫ snd C T).left
    simp [Stacks.Hilbert.familyBaseChangeMap]

/-- The map `C^(n+1) ⟶ C^(n+2)` doubling the first coordinate,
`(x_0, …, x_n) ↦ (x_0, x_0, x_1, …, x_n)`: the graph section of the first coordinate. -/
abbrev doubleFirst (n : ℕ) : power C (n + 1) ⟶ power C (n + 2) :=
  lift (n + 2) (Fin.cons (coord C (n + 1) 0) (coord C (n + 1)))

/-- **The merging map for a permutation `σ`**: `doubleFirst` followed by the reindexing by
`σ⁻¹`, so that slots `σ 0` and `σ 1` of the target both receive the first coordinate. -/
def mergeMap (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) : power C (n + 1) ⟶ power C (n + 2) :=
  doubleFirst C n ≫ reindex C σ.symm

/-- The projection `C^(n+2) ⟶ C^2` to the first two coordinates is `𝟙 ⊗` the projection
`C^(n+1) ⟶ C^1` to the first coordinate. -/
theorem reindex_zero_one_eq (n : ℕ) :
    reindex C ![(0 : Fin (n + 2)), 1] =
      (CartesianMonoidalCategory.lift (fst C (power C (n + 1)))
        (snd C (power C (n + 1)) ≫ reindex C (fun _ : Fin 1 => (0 : Fin (n + 1)))) :
          power C (n + 2) ⟶ power C 2) := by
  refine hom_ext 2 fun j => ?_
  refine Fin.cases ?_ (fun t => ?_) j
  · exact (reindex_coord _ 0).trans (CartesianMonoidalCategory.lift_fst _ _).symm
  · rw [Fin.fin_one_eq_zero t]
    refine (reindex_coord _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ coord C 1 0) (CartesianMonoidalCategory.lift_snd _ _).symm)
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (snd C (power C (n + 1)) ≫ ·)
      (reindex_coord (C := C) (fun _ : Fin 1 => (0 : Fin (n + 1))) 0).symm

end Maps

variable {k : Type u} [Field k] [IsAlgClosed k] (C : Over (Spec (.of k))) [IsVariety k C.hom]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] (hC : topologicalKrullDim C.left = 1)
  (c₀ : power C 0 ⟶ C)

/-- The Picard group of `C^m`. -/
abbrev PowerPic (m : ℕ) : Type (u + 1) :=
  Stacks.SheafOfModules.PicardGroup (power C m).left.presheaf (power C m).left.ringCatIsSheaf

/-- **The degree of a class on `C^1`**, as its intersection number. -/
abbrev curveDeg (A : PowerPic C 1) : ℤ :=
  powerForm C hC 1 fun _ => A

/-- The class of the point `c₀` on `C^1`: the graph of `c₀ : C^0 ⟶ C`. -/
abbrev pointClass : PowerPic C 1 :=
  @Stacks.Divisors.picardClass _ (Stacks.Hilbert.pointIdeal C (power C 0) c₀)
    (isEffectiveCartierDivisor_graph C 0 c₀)

/-- The class of the fibre `{c₀} × C^m` on `C^(m+1)`: the graph of the constant map `c₀`. -/
abbrev fibreClass (m : ℕ) : PowerPic C (m + 1) :=
  @Stacks.Divisors.picardClass _ (Stacks.Hilbert.pointIdeal C (power C m) (toPowerZero C m ≫ c₀))
    (isEffectiveCartierDivisor_graph C m _)

/-- Equal effective Cartier divisors have equal Picard classes. -/
theorem picardClass_congr {X : Scheme.{u}} {D D' : X.IdealSheafData}
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsEffectiveCartierDivisor D']
    (h : D = D') : Stacks.Divisors.picardClass D = Stacks.Divisors.picardClass D' := by
  subst h
  rfl

omit [IsAlgClosed k] [IsProper C.hom] in
/-- **The fibre class is pulled back from the point class** along the first projection. -/
theorem schemePullbackClass_firstProj_pointClass (m : ℕ) :
    Stacks.Picard.schemePullbackClass (firstProj C m).left (pointClass C c₀) =
      fibreClass C c₀ m := by
  have : IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C 0) c₀) :=
    Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 0) c₀
  have hcomap := Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap C (toPowerZero C m) c₀
  have hD : (Stacks.Hilbert.pointIdeal C (power C 0) c₀).comap (firstProj C m).left =
      Stacks.Hilbert.pointIdeal C (power C m) (toPowerZero C m ≫ c₀) := by
    rwa [firstProj_left]
  have : Stacks.Divisors.IsPullbackDefined (firstProj C m).left
      (Stacks.Hilbert.pointIdeal C (power C 0) c₀) :=
    (congrArg Stacks.Divisors.IsEffectiveCartierDivisor hD).mpr
      (isEffectiveCartierDivisor_graph C m _)
  exact (@Stacks.Divisors.schemePullbackClass_picardClass _ _ (firstProj C m).left _
    (isEffectiveCartierDivisor_graph C 0 c₀) this).trans
    (@picardClass_congr _ _ _ this (isEffectiveCartierDivisor_graph C m _) hD)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- **The empty intersection number of `C^0 = Spec k` is `1`.** -/
theorem powerForm_zero (x : Fin 0 → PowerPic C 0) : powerForm C hC 0 x = 1 := by
  rw [powerForm, picardIntersection_apply, intersectionNumber_zero_eq_finrank_globalSections]
  let : Algebra k Γ((power C 0).left, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (𝟙 (power C 0).left ≫ (power C 0).hom).appTop).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap k Γ((power C 0).left, ⊤)) := by
    show Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫
      (𝟙 (Spec (.of k)) ≫ 𝟙 (Spec (.of k))).appTop).hom
    rw [Category.comp_id, Scheme.Hom.id_appTop, Category.comp_id]
    exact ConcreteCategory.bijective_of_isIso _
  have e : k ≃ₗ[k] Γ((power C 0).left, ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap k _) hbij
  rw [← e.finrank_eq, Module.finrank_self, Nat.cast_one]

/-- A constant family indexed by `Fin 1` is `Fin.cons` of its value and the empty family. -/
theorem fun_eq_cons_elim0 {α : Type*} (a : α) (x : Fin 0 → α) :
    (fun _ : Fin 1 => a) = Fin.cons a x := by
  funext i
  rw [Fin.fin_one_eq_zero i, Fin.cons_zero]

/-- **The point has degree one.** -/
theorem curveDeg_pointClass : curveDeg C hC (pointClass C c₀) = 1 := by
  refine (congrArg (powerForm C hC 1) (fun_eq_cons_elim0 _ Fin.elim0)).trans ?_
  rw [powerForm_cons_graph C hC 0 c₀, powerForm_zero]

/-- **The fibre rule for the point class.** -/
theorem powerForm_cons_fibreClass (m : ℕ) (x : Fin m → PowerPic C (m + 1)) :
    powerForm C hC (m + 1) (Fin.cons (fibreClass C c₀ m) x) =
      powerForm C hC m
        (fun q => Stacks.Picard.schemePullbackClass (insertPoint C c₀ m 0).left (x q)) := by
  rw [fibreClass, powerForm_cons_graph C hC m (toPowerZero C m ≫ c₀) x]
  simp only [graphSection, pointGraph_point_eq_insertPoint]

omit [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
include hC in
/-- `C^1` is a curve. -/
theorem isCurve_power_one : IsCurve k (power C 1).hom :=
  { toIsVariety := isVariety_power C 1
    topologicalKrullDim_eq_one := by rw [topologicalKrullDim_power hC 1]; rfl }

/-- `C^1` is smooth over `k`. -/
instance smooth_power_one : Smooth (power C 1).hom := by
  have : Smooth (power C 0).hom := by
    change Smooth (𝟙 (Spec (.of k)))
    infer_instance
  have : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  have : Smooth (pullback.fst C.hom (power C 0).hom) := inferInstance
  change Smooth (pullback.fst C.hom (power C 0).hom ≫ C.hom)
  infer_instance

omit [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
include hC in
/-- `C^1` has dimension at most one. -/
theorem topologicalKrullDim_power_one_le : topologicalKrullDim (power C 1).left ≤ 1 := by
  rw [topologicalKrullDim_power hC 1]
  rfl

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- `curveDeg` is the degree on the curve `C^1`. -/
theorem curveDeg_eq_picardDegree (A : PowerPic C 1) :
    haveI := isCurve_power_one C hC
    curveDeg C hC A = picardDegree k (power C 1).hom (topologicalKrullDim_power_one_le C hC)
      (Stacks.GluePicard.picardModelAddEquiv (power C 1).left.toRingedSpace A) := by
  have := isCurve_power_one C hC
  rw [AlgebraicGeometry.CurveGraph.picardDegree_eq_invertibleCurveDegree_rep, curveDeg, powerForm,
    picardIntersection_apply,
    intersectionNumber_one_eq_invertibleCurveDegree k (power C 1).hom (𝟙 _)
      (topologicalKrullDim_power_one_le C hC),
    AlgebraicGeometry.CurveGraph.invertibleCurveDegree_congr (Category.id_comp _)]
  exact invertibleCurveDegree_eq_of_iso k _ _ ((Scheme.Modules.pullbackId _).app _)

/-- `curveDeg` is additive. -/
def curveDegHom : PowerPic C 1 →+ ℤ :=
  AddMonoidHom.mk' (curveDeg C hC) fun a b => by
    rw [curveDeg_eq_picardDegree, curveDeg_eq_picardDegree, curveDeg_eq_picardDegree, map_add,
      map_add]

omit [IsAlgClosed k] in
/-- Some natural number `ℓ ≥ 2` is invertible in `k`. -/
theorem exists_isUnit_natCast_two_le : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ IsUnit (ℓ : k) := by
  by_cases h : IsUnit ((2 : ℕ) : k)
  · exact ⟨2, le_rfl, h⟩
  · refine ⟨3, by norm_num, ?_⟩
    have h2 : ((2 : ℕ) : k) = 0 := by simpa [isUnit_iff_ne_zero] using h
    have : ((3 : ℕ) : k) = 1 := by
      have : ((3 : ℕ) : k) = ((2 : ℕ) : k) + 1 := by norm_num
      rw [this, h2, zero_add]
    rw [this]
    exact isUnit_one

/-- **Degree-zero classes on `C^1` are `ℓ`-divisible** for `ℓ` invertible in `k`. -/
theorem exists_nsmul_eq_of_curveDeg_eq_zero {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) (A : PowerPic C 1)
    (hA : curveDeg C hC A = 0) : ∃ B : PowerPic C 1, curveDeg C hC B = 0 ∧ ℓ • B = A := by
  have := isCurve_power_one C hC
  have := smooth_power_one C
  set e := Stacks.GluePicard.picardModelAddEquiv (power C 1).left.toRingedSpace
  have hA' : (e A : schemePicard (power C 1).left) ∈
      picardDegreeZero k (power C 1).hom (topologicalKrullDim_power_one_le C hC) :=
    (mem_picardDegreeZero_iff _ _ _ _).2 ((curveDeg_eq_picardDegree C hC A).symm.trans hA)
  obtain ⟨y, hy⟩ := AlgebraicGeometry.CurveGraph.picardDegreeZero_divisible (power C 1).hom
    (topologicalKrullDim_power_one_le C hC) hℓ ⟨e A, hA'⟩
  refine ⟨e.symm y.1, ?_, ?_⟩
  · rw [curveDeg_eq_picardDegree, AddEquiv.apply_symm_apply]
    exact y.2
  · apply e.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val hy

include hC in
/-- **An additive map `Pic(C^1) → 𝐙` vanishing on the point class is zero.** -/
theorem addMonoidHom_eq_zero_of_pointClass (φ : PowerPic C 1 →+ ℤ)
    (hφ : φ (pointClass C c₀) = 0) : φ = 0 := by
  obtain ⟨ℓ, hℓ2, hℓ⟩ := exists_isUnit_natCast_two_le (k := k)
  have hdiv : ∀ n : ℕ, ∀ A : PowerPic C 1, curveDeg C hC A = 0 → (ℓ ^ n : ℤ) ∣ φ A := by
    intro n
    induction n with
    | zero => intro A _; simp
    | succ n ih =>
      intro A hA
      obtain ⟨B, hB, rfl⟩ := exists_nsmul_eq_of_curveDeg_eq_zero C hC hℓ A hA
      rw [map_nsmul, nsmul_eq_mul, pow_succ, mul_comm ((ℓ : ℤ) ^ n)]
      exact mul_dvd_mul_left _ (ih B hB)
  have h0 : ∀ A : PowerPic C 1, curveDeg C hC A = 0 → φ A = 0 := by
    intro A hA
    by_contra hne
    have hlt : (φ A).natAbs < ℓ ^ (φ A).natAbs := Nat.lt_pow_self (by lia)
    have := Int.natAbs_dvd_natAbs.2 (hdiv (φ A).natAbs A hA)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hne) this) (not_le.2 hlt)
  ext A
  have hA : curveDeg C hC (A - curveDeg C hC A • pointClass C c₀) = 0 := by
    have h := (curveDegHom C hC).map_sub A (curveDeg C hC A • pointClass C c₀)
    rw [(curveDegHom C hC).map_zsmul] at h
    change curveDeg C hC _ =
      curveDeg C hC A - curveDeg C hC A • curveDeg C hC (pointClass C c₀) at h
    rw [h, curveDeg_pointClass, smul_eq_mul, mul_one, sub_self]
  have := h0 _ hA
  rw [map_sub, map_zsmul, hφ, smul_zero, sub_zero] at this
  simpa using this

/-- **The fibre rule in slot `0`.** For a class `A` on `C^1`,
`(π_0^* A · x_1 ⋯ x_m · C^(m+1)) = deg A · (ι_0^* x_1 ⋯ ι_0^* x_m · C^m)`. -/
theorem powerForm_cons_firstProj (m : ℕ) (A : PowerPic C 1) (x : Fin m → PowerPic C (m + 1)) :
    powerForm C hC (m + 1) (Fin.cons (Stacks.Picard.schemePullbackClass (firstProj C m).left A) x) =
      curveDeg C hC A *
        powerForm C hC m
          (fun q => Stacks.Picard.schemePullbackClass (insertPoint C c₀ m 0).left (x q)) := by
  let φ : PowerPic C 1 →+ ℤ :=
    { toFun := fun A => powerForm C hC (m + 1)
          (Fin.cons (Stacks.Picard.schemePullbackClass (firstProj C m).left A) x) -
        curveDeg C hC A * powerForm C hC m
          (fun q => Stacks.Picard.schemePullbackClass (insertPoint C c₀ m 0).left (x q))
      map_zero' := by
        have h1 : Stacks.Picard.schemePullbackClass (firstProj C m).left (0 : PowerPic C 1) = 0 :=
          (Stacks.Picard.schemePullbackClassHom (firstProj C m).left).map_zero
        have h2 : curveDeg C hC 0 = 0 := (curveDegHom C hC).map_zero
        rw [h1, h2, zero_mul, sub_zero]
        exact MultilinearMap.map_coord_zero _ (0 : Fin (m + 1)) (Fin.cons_zero _ _)
      map_add' := fun a b => by
        rw [Stacks.Picard.schemePullbackClass_add, MultilinearMap.cons_add]
        have h := (curveDegHom C hC).map_add a b
        change curveDeg C hC (a + b) = curveDeg C hC a + curveDeg C hC b at h
        rw [h]
        ring }
  have hφ : φ (pointClass C c₀) = 0 := by
    show _ - _ = (0 : ℤ)
    rw [schemePullbackClass_firstProj_pointClass, powerForm_cons_fibreClass, curveDeg_pointClass,
      one_mul, sub_self]
  have := DFunLike.congr_fun (addMonoidHom_eq_zero_of_pointClass C hC c₀ φ hφ) A
  change _ - _ = (0 : ℤ) at this
  exact sub_eq_zero.1 this

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- Pulling back along a reindexing by a permutation and then along its inverse is the
identity. -/
theorem schemePullbackClass_reindex_symm (m : ℕ) (σ : Equiv.Perm (Fin m)) (z : PowerPic C m) :
    Stacks.Picard.schemePullbackClass (reindex C σ).left
      (Stacks.Picard.schemePullbackClass (reindex C σ.symm).left z) = z := by
  rw [Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, reindex_comp]
  have : (⇑σ ∘ ⇑σ.symm) = id := by funext j; simp
  rw [this, reindex_id, Over.id_left, Stacks.Picard.schemePullbackClass_id]

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- `ι_0` followed by the reindexing along `Fin.cycleRange i` is `ι_i`. -/
theorem insertPoint_zero_comp_reindex (m : ℕ) (i : Fin (m + 1)) :
    insertPoint C c₀ m 0 ≫ reindex C (Fin.cycleRange i) = insertPoint C c₀ m i := by
  refine hom_ext (m + 1) fun j => ?_
  rw [Category.assoc, reindex_coord]
  induction j using Fin.succAboveCases i with
  | x => rw [Fin.cycleRange_self, insertPoint_coord_self, insertPoint_coord_self]
  | p t =>
    rw [Fin.cycleRange_succAbove, insertPoint_coord_succAbove, ← Fin.succAbove_zero,
      insertPoint_coord_succAbove]

/-- **The fibre rule in slot `i`.** For a class `A` on `C^1` and its pullback `p_i^* A` along the
`i`-th coordinate, `(p_i^* A · x_1 ⋯ x_m · C^(m+1)) = deg A · (ι_i^* x_1 ⋯ ι_i^* x_m · C^m)`. -/
theorem powerForm_cons_coordPullback (m : ℕ) (i : Fin (m + 1)) (A : PowerPic C 1)
    (x : Fin m → PowerPic C (m + 1)) :
    powerForm C hC (m + 1)
        (Fin.cons (Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => i)).left A) x) =
      curveDeg C hC A *
        powerForm C hC m
          (fun q => Stacks.Picard.schemePullbackClass (insertPoint C c₀ m i).left (x q)) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (m + 1)), σ = (Fin.cycleRange i).symm := ⟨_, rfl⟩
  have hf : (⇑σ ∘ fun _ : Fin 1 => (0 : Fin (m + 1))) = fun _ => i := by
    funext t
    rw [hσ]
    exact Fin.cycleRange_symm_zero i
  have hcons : (Fin.cons (Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => i)).left A)
      x : Fin (m + 1) → PowerPic C (m + 1)) = fun q => Stacks.Picard.schemePullbackClass
        (reindex C σ).left ((Fin.cons (Stacks.Picard.schemePullbackClass (firstProj C m).left A)
          (fun q => Stacks.Picard.schemePullbackClass (reindex C σ.symm).left (x q)) :
            Fin (m + 1) → PowerPic C (m + 1)) q) := by
    funext q
    refine Fin.cases ?_ (fun t => ?_) q
    · rw [Fin.cons_zero, Fin.cons_zero, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left,
        reindex_comp, hf]
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact (schemePullbackClass_reindex_symm C (m + 1) σ (x t)).symm
  rw [hcons, powerForm_reindex C hC (m + 1) σ, powerForm_cons_firstProj C hC c₀]
  congr 2
  funext q
  rw [Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, hσ, Equiv.symm_symm,
    insertPoint_zero_comp_reindex]

/-- **The class of the diagonal `Δ = {x_0 = x_1}` on `C^2`**: the graph of the first coordinate
of `C^1`. -/
abbrev diagClass : PowerPic C 2 :=
  @Stacks.Divisors.picardClass _ (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0))
    (isEffectiveCartierDivisor_graph C 1 _)

/-- The class of `{x_0 = x_1}` on `C^(n+2)`: the graph of the first coordinate of `C^(n+1)`. -/
abbrev diagZeroOneClass (n : ℕ) : PowerPic C (n + 2) :=
  @Stacks.Divisors.picardClass _
    (Stacks.Hilbert.pointIdeal C (power C (n + 1)) (coord C (n + 1) 0))
    (isEffectiveCartierDivisor_graph C (n + 1) _)

omit [IsAlgClosed k] [IsProper C.hom] in
/-- The pullback of the diagonal class of `C^2` along the projection to the first two
coordinates is the class of `{x_0 = x_1}` on `C^(n+2)`. -/
theorem schemePullbackClass_reindex_diagClass (n : ℕ) :
    Stacks.Picard.schemePullbackClass (reindex C ![(0 : Fin (n + 2)), 1]).left (diagClass C) =
      diagZeroOneClass C n := by
  have : IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C 1) (coord C 1 0)) :=
    Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 1) _
  have hcomap := Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap C
    (reindex C (fun _ : Fin 1 => (0 : Fin (n + 1)))) (coord C 1 0)
  have hg : reindex C (fun _ : Fin 1 => (0 : Fin (n + 1))) ≫ coord C 1 0 = coord C (n + 1) 0 :=
    reindex_coord (C := C) (fun _ : Fin 1 => (0 : Fin (n + 1))) 0
  have hD : (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0)).comap
      (reindex C ![(0 : Fin (n + 2)), 1]).left =
      Stacks.Hilbert.pointIdeal C (power C (n + 1)) (coord C (n + 1) 0) := by
    have e1 : (reindex C ![(0 : Fin (n + 2)), 1]).left =
        Stacks.Hilbert.familyBaseChangeMap C (reindex C (fun _ : Fin 1 => (0 : Fin (n + 1)))) := by
      rw [familyBaseChangeMap_eq]
      exact congrArg Over.Hom.left (reindex_zero_one_eq C n)
    rw [e1]
    exact hcomap.trans (by rw [hg])
  have : Stacks.Divisors.IsPullbackDefined (reindex C ![(0 : Fin (n + 2)), 1]).left
      (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0)) :=
    (congrArg Stacks.Divisors.IsEffectiveCartierDivisor hD).mpr
      (isEffectiveCartierDivisor_graph C (n + 1) _)
  exact (@Stacks.Divisors.schemePullbackClass_picardClass _ _ _ _
    (isEffectiveCartierDivisor_graph C 1 _) this).trans
    (@picardClass_congr _ _ _ this (isEffectiveCartierDivisor_graph C (n + 1) _) hD)

/-- **The diagonal rule in slots `(0, 1)`.** -/
theorem powerForm_cons_diagZeroOneClass (n : ℕ) (x : Fin (n + 1) → PowerPic C (n + 2)) :
    powerForm C hC (n + 2) (Fin.cons (diagZeroOneClass C n) x) =
      powerForm C hC (n + 1)
        (fun q => Stacks.Picard.schemePullbackClass (doubleFirst C n).left (x q)) := by
  rw [diagZeroOneClass, powerForm_cons_graph C hC (n + 1) (coord C (n + 1) 0) x]
  simp only [graphSection, pointGraph_eq_lift]

/-- **The diagonal rule.** For a permutation `σ` of the coordinates, the diagonal
`Δ = {x_{σ 0} = x_{σ 1}}` of `C^(n+2)` meets the other classes like their restrictions along
the merging map: `(Δ · x_1 ⋯ x_{n+1} · C^(n+2)) = (μ^* x_1 ⋯ μ^* x_{n+1} · C^(n+1))`. -/
theorem powerForm_cons_diagonal (n : ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (x : Fin (n + 1) → PowerPic C (n + 2)) :
    powerForm C hC (n + 2)
        (Fin.cons
          (Stacks.Picard.schemePullbackClass (reindex C ![σ 0, σ 1]).left (diagClass C)) x) =
      powerForm C hC (n + 1)
        (fun q => Stacks.Picard.schemePullbackClass (mergeMap C n σ).left (x q)) := by
  have hf : (⇑σ ∘ ![(0 : Fin (n + 2)), 1]) = ![σ 0, σ 1] := by
    funext t
    refine Fin.cases ?_ (fun t => ?_) t
    · rfl
    · rw [Fin.fin_one_eq_zero t]
      rfl
  have hcons : (Fin.cons (Stacks.Picard.schemePullbackClass (reindex C ![σ 0, σ 1]).left
      (diagClass C)) x : Fin (n + 2) → PowerPic C (n + 2)) = fun q =>
        Stacks.Picard.schemePullbackClass (reindex C σ).left
          ((Fin.cons (diagZeroOneClass C n)
            (fun q => Stacks.Picard.schemePullbackClass (reindex C σ.symm).left (x q)) :
              Fin (n + 2) → PowerPic C (n + 2)) q) := by
    funext q
    refine Fin.cases ?_ (fun t => ?_) q
    · rw [Fin.cons_zero, Fin.cons_zero, ← schemePullbackClass_reindex_diagClass,
        Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, reindex_comp, hf]
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact (schemePullbackClass_reindex_symm C (n + 2) σ (x t)).symm
  rw [hcons, powerForm_reindex C hC (n + 2) σ, powerForm_cons_diagZeroOneClass]
  congr 1
  funext q
  rw [Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left]
  rfl

end Stacks.CurvePower
