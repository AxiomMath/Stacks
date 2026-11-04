module

public import StacksFrontier.Algebra.DifferentialGraded.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.Algebra.DifferentialGraded.NativeCover.DirectSumOfShifts

/-!
# A cover surjective on cocycles, and products of direct sums of shifts

Let `R` be a commutative ring, let `(A, d)` be a differential graded `R`-algebra and let `M`
be a right differential graded `A`-module. For every cocycle `c ∈ M^k` the shift `A[-k]` maps
to `M` by sending its degree-`k` generator `1` to `c`, which is a chain map precisely because
`d_M c = 0`; summing over all cocycles gives a map from a direct sum of shifts of `A` which is
surjective on cocycles in every degree.

This file also constructs the binary product of differential graded modules and shows that
the product of two direct sums of shifts of `A` is again a direct sum of shifts; this is what
allows the cocycle cover to be combined with the surjective cover.

## Main results

* `DifferentialGraded.NativeCover.exists_cocycle_cover`: a cover by a direct sum of shifts which is
  surjective on cocycles in every degree.
* `DifferentialGraded.NativeCover.isDirectSumOfShifts_prodDG`: the product of two direct sums of
  shifts is a direct sum of shifts.

## References

* [The Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace DifferentialGraded.NativeCover

universe u v w w' w₁ w₂ w₃ t

namespace CocycleCover

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
variable {M : Type w} [AddCommGroup M] [Module R M] (PM : DGModule R A 𝒜 dA M)

/-- Index set of homogeneous cocycles of `M`. -/
abbrev Idx : Type w := Σ n : ℤ, (PM.gradedCocycles n)

/-- The degree of an index. -/
def deg (c : Idx PM) : ℤ := c.1

/-- The cocycle of `M` represented by an index. -/
def elt (c : Idx PM) : M := (c.2 : M)

/-- The cocycle indexed by `c` is homogeneous of degree `deg c`. -/
theorem elt_grade (c : Idx PM) : elt PM c ∈ PM.grading (deg PM c) := c.2.2.2

/-- The element indexed by `c` is a cocycle. -/
theorem elt_cocycle (c : Idx PM) : PM.d (elt PM c) = 0 := c.2.2.1

/-- Shift witness: `A[-deg c]`. -/
def k (c : Idx PM) : ℤ := -deg PM c

/-- The cover end `P₂ = ⨁_c A[-deg c]`. -/
noncomputable def Pend : DGModule R A 𝒜 dA (DirectSum (Idx PM) (fun _ => A)) :=
  ShiftSum.shiftDG R A 𝒜 dA (Idx PM) (k PM)

open Classical in
/-- The covering linear map: `lof c a ↦ (elt c) • a`. -/
noncomputable def coverHom₂ : (DirectSum (Idx PM) (fun _ => A)) →ₗ[R] M :=
  DirectSum.toModule R (Idx PM) M (fun c => PM.smul (elt PM c))

open Classical in
/-- The cocycle cover sends the generator `1_c` to the cocycle `elt c`. -/
theorem coverHom₂_lof (c : Idx PM) (a : A) :
    coverHom₂ PM (DirectSum.lof R (Idx PM) (fun _ => A) c a)
      = PM.smul (elt PM c) a := by
  unfold coverHom₂; rw [DirectSum.toModule_lof]

open Classical in
/-- The cocycle cover map is `A`-linear for the right action. -/
theorem coverHom₂_rsmul (s : DirectSum (Idx PM) (fun _ => A)) (a : A) :
    coverHom₂ PM (ShiftSum.rsmul R A (Idx PM) s a)
      = PM.smul (coverHom₂ PM s) a := by
  classical
  induction s using DirectSum.induction_on with
  | zero => simp
  | of c b =>
      rw [show DirectSum.of (fun _ : Idx PM => A) c b
            = DirectSum.lof R (Idx PM) (fun _ => A) c b from rfl]
      have hr : ShiftSum.rsmul R A (Idx PM)
            (DirectSum.lof R (Idx PM) (fun _ => A) c b) a
          = DirectSum.lof R (Idx PM) (fun _ => A) c (b * a) := by
        refine DirectSum.ext (fun j => ?_)
        rw [ShiftSum.rsmul_apply]
        rw [show DirectSum.lof R (Idx PM) (fun _ => A) c b
              = DirectSum.of (fun _ : Idx PM => A) c b from rfl,
            show DirectSum.lof R (Idx PM) (fun _ => A) c (b * a)
              = DirectSum.of (fun _ : Idx PM => A) c (b * a) from rfl,
            DirectSum.of_apply, DirectSum.of_apply]
        by_cases h : c = j
        · subst h; simp
        · simp [h]
      rw [hr, coverHom₂_lof, coverHom₂_lof, PM.smul_smul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- If every component of `s` lands in the right graded piece, `coverHom₂ s`
is homogeneous of degree `n`. -/
theorem coverHom₂_mem_grade (n : ℤ) (s : DirectSum (Idx PM) (fun _ => A))
    (hs : ∀ j, s j ∈ 𝒜 (n + k PM j)) :
    coverHom₂ PM s ∈ PM.grading n := by
  classical
  have hdecomp : s = ∑ j ∈ DFinsupp.support s, DirectSum.of (fun _ : Idx PM => A) j (s j) :=
    (DirectSum.sum_support_of s).symm
  rw [hdecomp, map_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [show DirectSum.of (fun _ : Idx PM => A) j (s j)
        = DirectSum.lof R (Idx PM) (fun _ => A) j (s j) from rfl, coverHom₂_lof]
  have hsmul := PM.smul_grade (deg PM j) (n + k PM j) (elt PM j) (s j)
    (elt_grade PM j) (hs j)
  rwa [show deg PM j + (n + k PM j) = n by simp only [k]; ring] at hsmul

open Classical in
/-- The chain-map identity: `coverHom₂` intertwines `Pend.d` with `PM.d`. -/
theorem coverHom₂_dchain (s : DirectSum (Idx PM) (fun _ => A)) :
    coverHom₂ PM ((Pend PM).d s) = PM.d (coverHom₂ PM s) := by
  classical
  induction s using DirectSum.induction_on with
  | zero => simp
  | of c b =>
      have hdd : (Pend PM).d (DirectSum.lof R (Idx PM) (fun _ => A) c b)
          = ((-1 : R) ^ (k PM c).natAbs)
              • DirectSum.lof R (Idx PM) (fun _ => A) c (dA.d b) := by
        refine DirectSum.ext (fun j => ?_)
        show ShiftSum.diffDiag R A dA (Idx PM) (k PM)
              (DirectSum.lof R (Idx PM) (fun _ => A) c b) j = _
        rw [ShiftSum.diffDiag_apply, DirectSum.smul_apply]
        rw [show DirectSum.lof R (Idx PM) (fun _ => A) c b
              = DirectSum.of (fun _ : Idx PM => A) c b from rfl,
            show DirectSum.lof R (Idx PM) (fun _ => A) c (dA.d b)
              = DirectSum.of (fun _ : Idx PM => A) c (dA.d b) from rfl,
            DirectSum.of_apply, DirectSum.of_apply]
        by_cases h : c = j
        · subst h; simp
        · simp [h]
      rw [show DirectSum.of (fun _ : Idx PM => A) c b
            = DirectSum.lof R (Idx PM) (fun _ => A) c b from rfl]
      rw [hdd, map_smul, coverHom₂_lof, coverHom₂_lof]
      -- RHS via Leibniz on `elt c ∈ grading (deg c)`; `d (elt c) = 0`.
      have hL := PM.leibniz (deg PM c) (elt PM c) (elt_grade PM c) b
      rw [hL, elt_cocycle]
      rw [map_zero, LinearMap.zero_apply, zero_add]
      congr 1
      have hsign : (k PM c).natAbs = (deg PM c).natAbs := by
        simp only [k]; rw [Int.natAbs_neg]
      rw [hsign]
  | add x y hx hy => simp [map_add, hx, hy]

/-- The covering DG-hom `φ₂ : P₂ → M`. -/
noncomputable def coverHom : DGModule.Hom (Pend PM) PM where
  toFun := coverHom₂ PM
  map_smul' := by
    intro s a
    change coverHom₂ PM (ShiftSum.rsmul R A (Idx PM) s a) = PM.smul (coverHom₂ PM s) a
    rw [coverHom₂_rsmul]
  map_grade := by
    intro n s hs
    change coverHom₂ PM s ∈ PM.grading n
    exact coverHom₂_mem_grade PM n s
      (fun j => (ShiftSum.mem_gradingSub R A 𝒜 (Idx PM) (k PM) n s).mp hs j)
  map_d := by
    intro s
    change coverHom₂ PM ((Pend PM).d s) = PM.d (coverHom₂ PM s)
    exact coverHom₂_dchain PM s

/-- `d_A 1 = 0`. -/
theorem dA_one : dA.d (1 : A) = 0 := by
  have h := dA.leibniz 0 (1 : A) (SetLike.one_mem_graded 𝒜) (1 : A)
  rw [mul_one, mul_one, one_mul] at h
  -- h : dA.d 1 = dA.d 1 + (-1)^0 • dA.d 1
  simp only [Int.natAbs_zero, pow_zero, one_smul] at h
  -- h : dA.d 1 = dA.d 1 + dA.d 1
  have h2 : dA.d (1 : A) + dA.d (1 : A) = dA.d (1 : A) + 0 := by
    rw [add_zero]; exact h.symm
  exact (add_left_cancel h2)

open Classical in
/-- **Graded surjectivity on cocycles** for `φ₂`. -/
theorem coverHom_gradedSurjectiveOnCocycles :
    (coverHom PM).GradedSurjectiveOnCocycles := by
  classical
  intro n m hm
  obtain ⟨hmcoc, hmgr⟩ := hm
  have hmd : PM.d m = 0 := hmcoc
  -- The index for the cocycle `m`.
  refine ⟨DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ 1, ⟨?_, ?_⟩, ?_⟩
  · -- x ∈ Pend.cocycles, i.e. Pend.d x = 0
    show (Pend PM).d (DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ 1) = 0
    refine DirectSum.ext (fun j => ?_)
    rw [DirectSum.zero_apply]
    show ShiftSum.diffDiag R A dA (Idx PM) (k PM)
          (DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ 1) j = 0
    rw [ShiftSum.diffDiag_apply]
    rw [show DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ (1 : A)
          = DirectSum.of (fun _ : Idx PM => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ (1 : A) from rfl,
        DirectSum.of_apply]
    by_cases h : (⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ : Idx PM) = j
    · subst h; simp [dA_one]
    · simp [h]
  · -- x ∈ Pend.grading n
    show DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ (1 : A)
        ∈ (Pend PM).grading n
    rw [show (Pend PM).grading n = ShiftSum.gradingSub R A 𝒜 (Idx PM) (k PM) n from rfl,
        ShiftSum.mem_gradingSub]
    intro j
    rw [show DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ (1 : A)
          = DirectSum.of (fun _ : Idx PM => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ (1 : A) from rfl,
        DirectSum.of_apply]
    by_cases h : (⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ : Idx PM) = j
    · subst h
      simp only [dite_eq_left]
      rw [show n + k PM (⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ : Idx PM) = 0 by
            simp only [k, deg]; ring]
      exact SetLike.one_mem_graded 𝒜
    · simp [h]
  · -- φ₂ x = m
    show coverHom₂ PM (DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩ 1) = m
    rw [coverHom₂_lof]
    show PM.smul (elt PM ⟨n, ⟨m, ⟨hmcoc, hmgr⟩⟩⟩) 1 = m
    rw [PM.smul_one]
    rfl

end CocycleCover

/-- **Cocycle cover** (property (2) of `exists_dgModule_surjective_cover`). For every DG
`A`-module `M` there is a DG `A`-module `P₂` that is a direct sum of shifts of `A`,
together with a DG-hom `φ₂ : P₂ → M` whose induced map on cocycles is graded surjective.

*Argument.* Let `ι₂ := Σ n : ℤ, Ker(d_M)^n` index the homogeneous cocycles of
`M`.  For `c = ⟨n, z⟩` (so `z ∈ M^n`, `d_M z = 0`) take the shift `A[-n]`, whose
degree-`n` part contains the unit `1` (which is a cocycle of `A[-n]` since
`d_{A[-n]} 1 = ±d_A 1 = 0`).  The DG-map `A[-n] → M`, `1 ↦ z`, `a ↦ z·a`
extended `A`-linearly, is a chain map *because* `d_M z = 0`: indeed for `a ∈ A^p`,
`d_M(z·a) = d_M z · a + (-1)^n z · d_A a = (-1)^n z · d_A a`, matching the image
of `d_{A[-n]} a` under the map (here the sign matches the shift differential).
Set `P₂ := ⨁_c A[-n_c]` (a `shiftDG`, hence `IsDirectSumOfShifts` by
`shiftDG_isDirectSumOfShifts`) and `φ₂ := ⨁_c (A[-n_c] → M)`.  Given a degree-`n`
cocycle `z` of `M`, its preimage is the generator `1` of the `c = ⟨n,z⟩`
summand: it lies in `P₂^n` and is a cocycle of `P₂` (the differential is the
diagonal `±d_A`, which kills `1`), and `φ₂` sends it to `z`.  Hence `φ₂` is
graded surjective on cocycles. -/
theorem exists_cocycle_cover
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    {M : Type w} [AddCommGroup M] [Module R M] (PM : DGModule R A 𝒜 dA M) :
    ∃ (P₂ : Type (max v w)) (_ : AddCommGroup P₂) (_ : Module R P₂)
      (PP₂ : DGModule R A 𝒜 dA P₂) (φ₂ : DGModule.Hom PP₂ PM),
      IsDirectSumOfShifts.{u, v, _, w} PP₂ ∧ φ₂.GradedSurjectiveOnCocycles := by
  -- Construct P₂ = ⨁_{cocycle z} A[-deg z], φ₂ : 1_z ↦ z.
  exact ⟨DirectSum (CocycleCover.Idx PM) (fun _ => A), inferInstance, inferInstance,
    CocycleCover.Pend PM, CocycleCover.coverHom PM,
    shiftDG_isDirectSumOfShifts dA _ _,
    CocycleCover.coverHom_gradedSurjectiveOnCocycles PM⟩

namespace SumDS

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

open Classical in
/-- Forward direction of the splitting `⨁_{ιA⊕ιB} A ≃ (⨁_{ιA} A) × (⨁_{ιB} A)`. -/
noncomputable def fwd (ιA ιB : Type t) :
    DirectSum (ιA ⊕ ιB) (fun _ => A)
      →ₗ[R] (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A)) :=
  DirectSum.toModule R (ιA ⊕ ιB)
    ((DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A)))
    (fun i => match i with
      | Sum.inl a => (LinearMap.inl R _ _).comp (DirectSum.lof R ιA (fun _ => A) a)
      | Sum.inr b => (LinearMap.inr R _ _).comp (DirectSum.lof R ιB (fun _ => A) b))

open Classical in
/-- Backward direction. -/
noncomputable def bwd (ιA ιB : Type t) :
    (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A))
      →ₗ[R] DirectSum (ιA ⊕ ιB) (fun _ => A) :=
  LinearMap.coprod
    (DirectSum.toModule R ιA _
      (fun a => DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inl a)))
    (DirectSum.toModule R ιB _
      (fun b => DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inr b)))

open Classical in
/-- The forward map sends a generator indexed by `inl a` into the first factor. -/
theorem fwd_lof_inl (ιA ιB : Type t) (a : ιA) (c : A) :
    fwd (R := R) ιA ιB (DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inl a) c)
      = (DirectSum.lof R ιA (fun _ => A) a c, 0) := by
  unfold fwd
  rw [DirectSum.toModule_lof]
  simp

open Classical in
/-- The forward map sends a generator indexed by `inr b` into the second factor. -/
theorem fwd_lof_inr (ιA ιB : Type t) (b : ιB) (c : A) :
    fwd (R := R) ιA ιB (DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inr b) c)
      = (0, DirectSum.lof R ιB (fun _ => A) b c) := by
  unfold fwd
  rw [DirectSum.toModule_lof]
  simp

open Classical in
/-- The backward map sends a generator of the first factor to the one indexed by `inl a`. -/
theorem bwd_inl (ιA ιB : Type t) (a : ιA) (c : A) :
    bwd (R := R) ιA ιB (DirectSum.lof R ιA (fun _ => A) a c, 0)
      = DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inl a) c := by
  unfold bwd
  rw [show ((DirectSum.lof R ιA (fun _ => A) a c, 0) :
        (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A)))
      = (DirectSum.lof R ιA (fun _ => A) a c, 0) from rfl]
  rw [LinearMap.coprod_apply]
  simp [DirectSum.toModule_lof]

open Classical in
/-- The backward map sends a generator of the second factor to the one indexed by `inr b`. -/
theorem bwd_inr (ιA ιB : Type t) (b : ιB) (c : A) :
    bwd (R := R) ιA ιB (0, DirectSum.lof R ιB (fun _ => A) b c)
      = DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inr b) c := by
  unfold bwd
  rw [LinearMap.coprod_apply]
  simp [DirectSum.toModule_lof]

open Classical in
/-- The backward map is a left inverse of the forward map. -/
theorem bwd_fwd (ιA ιB : Type t)
    (x : DirectSum (ιA ⊕ ιB) (fun _ => A)) :
    bwd (R := R) ιA ιB (fwd (R := R) ιA ιB x) = x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i c =>
      rw [show DirectSum.of (fun _ : ιA ⊕ ιB => A) i c
            = DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) i c from rfl]
      cases i with
      | inl a => rw [fwd_lof_inl, bwd_inl]
      | inr b => rw [fwd_lof_inr, bwd_inr]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

open Classical in
/-- The backward map is a right inverse of the forward map. -/
theorem fwd_bwd (ιA ιB : Type t)
    (p : (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A))) :
    fwd (R := R) ιA ιB (bwd (R := R) ιA ιB p) = p := by
  classical
  obtain ⟨x, y⟩ := p
  have hx : ∀ x : DirectSum ιA (fun _ => A),
      fwd (R := R) ιA ιB (bwd (R := R) ιA ιB (x, 0)) = (x, (0 : DirectSum ιB (fun _ => A))) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero =>
        rw [show ((0 : DirectSum ιA (fun _ => A)), (0 : DirectSum ιB (fun _ => A)))
              = (0 : (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A))) from rfl,
            map_zero, map_zero]
    | of a c =>
        rw [show DirectSum.of (fun _ : ιA => A) a c
              = DirectSum.lof R ιA (fun _ => A) a c from rfl]
        rw [bwd_inl, fwd_lof_inl]
    | add x y hx hy =>
        have hxy : ((x + y, 0) : (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A)))
            = (x, 0) + (y, 0) := by ext <;> simp
        rw [hxy, map_add, map_add, hx, hy, Prod.mk_add_mk, add_zero]
  have hy : ∀ y : DirectSum ιB (fun _ => A),
      fwd (R := R) ιA ιB (bwd (R := R) ιA ιB (0, y)) = ((0 : DirectSum ιA (fun _ => A)), y) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero =>
        rw [show ((0 : DirectSum ιA (fun _ => A)), (0 : DirectSum ιB (fun _ => A)))
              = (0 : (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A))) from rfl,
            map_zero, map_zero]
    | of b c =>
        rw [show DirectSum.of (fun _ : ιB => A) b c
              = DirectSum.lof R ιB (fun _ => A) b c from rfl]
        rw [bwd_inr, fwd_lof_inr]
    | add x y hx hy =>
        have hxy : ((0, x + y) : (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A)))
            = (0, x) + (0, y) := by ext <;> simp
        rw [hxy, map_add, map_add, hx, hy, Prod.mk_add_mk, add_zero]
  have hsplit : ((x, y) : (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A)))
      = (x, 0) + (0, y) := by ext <;> simp
  rw [hsplit, map_add, map_add, hx, hy, Prod.mk_add_mk, add_zero, zero_add]

/-- The splitting linear equivalence. -/
noncomputable def equiv (ιA ιB : Type t) :
    DirectSum (ιA ⊕ ιB) (fun _ => A)
      ≃ₗ[R] (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A)) :=
  LinearEquiv.ofLinearMap (fwd (R := R) ιA ιB) (bwd (R := R) ιA ιB)
    (LinearMap.ext fun p => by
      change fwd (R := R) ιA ιB (bwd (R := R) ιA ιB p) = p
      exact fwd_bwd ιA ιB p)
    (LinearMap.ext fun x => by
      change bwd (R := R) ιA ιB (fwd (R := R) ιA ιB x) = x
      exact bwd_fwd ιA ιB x)

/-- The splitting equivalence is given by the forward map. -/
theorem equiv_apply (ιA ιB : Type t) (x : DirectSum (ιA ⊕ ιB) (fun _ => A)) :
    equiv (R := R) ιA ιB x = fwd (R := R) ιA ιB x := rfl

/-- The inverse of the splitting equivalence is given by the backward map. -/
theorem equiv_symm_apply (ιA ιB : Type t)
    (p : (DirectSum ιA (fun _ => A)) × (DirectSum ιB (fun _ => A))) :
    (equiv (R := R) ιA ιB).symm p = bwd (R := R) ιA ιB p := rfl

open Classical in
/-- The `inl j`-component of `fwd x` is `(x (inl j))`. -/
theorem fwd_fst_apply (ιA ιB : Type t) (x : DirectSum (ιA ⊕ ιB) (fun _ => A))
    (j : ιA) : (fwd (R := R) ιA ιB x).1 j = x (Sum.inl j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i c =>
      rw [show DirectSum.of (fun _ : ιA ⊕ ιB => A) i c
            = DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) i c from rfl]
      cases i with
      | inl a =>
          rw [fwd_lof_inl]
          show (DirectSum.lof R ιA (fun _ => A) a c) j
            = (DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inl a) c) (Sum.inl j)
          rw [show DirectSum.lof R ιA (fun _ => A) a c
                = DirectSum.of (fun _ : ιA => A) a c from rfl,
              show DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inl a) c
                = DirectSum.of (fun _ : ιA ⊕ ιB => A) (Sum.inl a) c from rfl,
              DirectSum.of_apply, DirectSum.of_apply]
          by_cases h : a = j
          · subst h; simp
          · rw [dite_eq_right h, dite_eq_right (by simpa using h)]
      | inr b =>
          rw [fwd_lof_inr]
          show (0 : DirectSum ιA (fun _ => A)) j
            = (DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inr b) c) (Sum.inl j)
          rw [DirectSum.zero_apply,
              show DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inr b) c
                = DirectSum.of (fun _ : ιA ⊕ ιB => A) (Sum.inr b) c from rfl,
              DirectSum.of_apply, dite_eq_right (by simp)]
  | add x y hx hy =>
      rw [map_add, Prod.fst_add, DirectSum.add_apply, hx, hy, DirectSum.add_apply]

open Classical in
/-- The `inr j`-component of `fwd x` is `x (inr j)`. -/
theorem fwd_snd_apply (ιA ιB : Type t) (x : DirectSum (ιA ⊕ ιB) (fun _ => A))
    (j : ιB) : (fwd (R := R) ιA ιB x).2 j = x (Sum.inr j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i c =>
      rw [show DirectSum.of (fun _ : ιA ⊕ ιB => A) i c
            = DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) i c from rfl]
      cases i with
      | inr b =>
          rw [fwd_lof_inr]
          show (DirectSum.lof R ιB (fun _ => A) b c) j
            = (DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inr b) c) (Sum.inr j)
          rw [show DirectSum.lof R ιB (fun _ => A) b c
                = DirectSum.of (fun _ : ιB => A) b c from rfl,
              show DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inr b) c
                = DirectSum.of (fun _ : ιA ⊕ ιB => A) (Sum.inr b) c from rfl,
              DirectSum.of_apply, DirectSum.of_apply]
          by_cases h : b = j
          · subst h; simp
          · rw [dite_eq_right h, dite_eq_right (by simpa using h)]
      | inl a =>
          rw [fwd_lof_inl]
          show (0 : DirectSum ιB (fun _ => A)) j
            = (DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inl a) c) (Sum.inr j)
          rw [DirectSum.zero_apply,
              show DirectSum.lof R (ιA ⊕ ιB) (fun _ => A) (Sum.inl a) c
                = DirectSum.of (fun _ : ιA ⊕ ιB => A) (Sum.inl a) c from rfl,
              DirectSum.of_apply, dite_eq_right (by simp)]
  | add x y hx hy =>
      rw [map_add, Prod.snd_add, DirectSum.add_apply, hx, hy, DirectSum.add_apply]

end SumDS

namespace ProdDG

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
variable {PA : Type w₁} [AddCommGroup PA] [Module R PA]
variable {PB : Type w₂} [AddCommGroup PB] [Module R PB]

/-- The right `A`-action on `PA × PB`, componentwise. -/
noncomputable def smulProd (QA : DGModule R A 𝒜 dA PA) (QB : DGModule R A 𝒜 dA PB) :
    (PA × PB) →ₗ[R] A →ₗ[R] (PA × PB) :=
  LinearMap.mk₂ R
    (fun (pq : PA × PB) (a : A) => (QA.smul pq.1 a, QB.smul pq.2 a))
    (by intro pq₁ pq₂ a; simp)
    (by intro c pq a; simp [Prod.smul_def])
    (by intro pq a₁ a₂; simp)
    (by intro pq c a; simp)

/-- The product action is componentwise. -/
theorem smulProd_apply (QA : DGModule R A 𝒜 dA PA) (QB : DGModule R A 𝒜 dA PB)
    (pq : PA × PB) (a : A) :
    smulProd QA QB pq a = (QA.smul pq.1 a, QB.smul pq.2 a) := rfl

/-- The product differential `d (p, q) = (d p, d q)`. -/
noncomputable def dProd (QA : DGModule R A 𝒜 dA PA) (QB : DGModule R A 𝒜 dA PB) :
    (PA × PB) →ₗ[R] (PA × PB) :=
  (QA.d ∘ₗ LinearMap.fst R _ _).prod (QB.d ∘ₗ LinearMap.snd R _ _)

/-- The product differential is componentwise. -/
theorem dProd_apply (QA : DGModule R A 𝒜 dA PA) (QB : DGModule R A 𝒜 dA PB)
    (pq : PA × PB) :
    dProd QA QB pq = (QA.d pq.1, QB.d pq.2) := rfl

/-- The grading on `PA × PB`: product of the two gradings. -/
def gradingProd (QA : DGModule R A 𝒜 dA PA) (QB : DGModule R A 𝒜 dA PB) (n : ℤ) :
    Submodule R (PA × PB) :=
  (QA.grading n).prod (QB.grading n)

/-- The product grading is an internal direct sum. -/
theorem isInternal_gradingProd (QA : DGModule R A 𝒜 dA PA)
    (QB : DGModule R A 𝒜 dA PB) :
    DirectSum.IsInternal (gradingProd QA QB) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  obtain ⟨hX1, hX2⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      QA.isInternal
  obtain ⟨hY1, hY2⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      QB.isInternal
  have hprod : ⨆ n, (QA.grading n).prod (QB.grading n)
      = (⨆ n, QA.grading n).prod (⨆ n, QB.grading n) := by
    apply le_antisymm
    · exact iSup_le fun n => Submodule.prod_mono (le_iSup _ n) (le_iSup _ n)
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      have hx0 : ((x, 0) : PA × PB) ∈ ⨆ n, (QA.grading n).prod (QB.grading n) := by
        refine Submodule.iSup_induction (motive := fun x => ((x, 0) : PA × PB) ∈
            ⨆ n, (QA.grading n).prod (QB.grading n))
          (fun n => QA.grading n) hx
          (fun n a ha => Submodule.mem_iSup_of_mem n ⟨ha, Submodule.zero_mem _⟩) ?_ ?_
        · exact Submodule.zero_mem _
        · intro a b ha hb
          have := Submodule.add_mem _ ha hb
          simpa using this
      have hy0 : ((0, y) : PA × PB) ∈ ⨆ n, (QA.grading n).prod (QB.grading n) := by
        refine Submodule.iSup_induction (motive := fun y => ((0, y) : PA × PB) ∈
            ⨆ n, (QA.grading n).prod (QB.grading n))
          (fun n => QB.grading n) hy
          (fun n a ha => Submodule.mem_iSup_of_mem n ⟨Submodule.zero_mem _, ha⟩) ?_ ?_
        · exact Submodule.zero_mem _
        · intro a b ha hb
          have := Submodule.add_mem _ ha hb
          simpa using this
      have := Submodule.add_mem _ hx0 hy0
      simpa using this
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def] at hX1 hY1 ⊢
    intro i
    have hXle : (⨆ (j : ℤ) (_ : j ≠ i), QA.grading j) ⊓ QA.grading i = ⊥ := by
      rw [inf_comm, ← disjoint_iff]; exact hX1 i
    have hYle : (⨆ (j : ℤ) (_ : j ≠ i), QB.grading j) ⊓ QB.grading i = ⊥ := by
      rw [inf_comm, ← disjoint_iff]; exact hY1 i
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    calc (QA.grading i).prod (QB.grading i)
            ⊓ ⨆ (j : ℤ) (_ : j ≠ i), (QA.grading j).prod (QB.grading j)
          ≤ (QA.grading i).prod (QB.grading i)
            ⊓ (⨆ (j : ℤ) (_ : j ≠ i), QA.grading j).prod
                (⨆ (j : ℤ) (_ : j ≠ i), QB.grading j) := by
            apply inf_le_inf_left
            refine iSup_le fun j => iSup_le fun hj => ?_
            exact Submodule.prod_mono (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
              (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
      _ = ((QA.grading i) ⊓ ⨆ (j : ℤ) (_ : j ≠ i), QA.grading j).prod
            ((QB.grading i) ⊓ ⨆ (j : ℤ) (_ : j ≠ i), QB.grading j) := by
            rw [Submodule.prod_inf_prod]
      _ = ⊥ := by
            rw [inf_comm (QA.grading i), inf_comm (QB.grading i),
              hXle, hYle, Submodule.prod_bot]
  · show (⨆ n, (QA.grading n).prod (QB.grading n)) = ⊤
    rw [hprod, hX2, hY2, Submodule.prod_top]

/-- The binary product DG `A`-module `PA × PB`. -/
noncomputable def prodDG (QA : DGModule R A 𝒜 dA PA) (QB : DGModule R A 𝒜 dA PB) :
    DGModule R A 𝒜 dA (PA × PB) where
  smul := smulProd QA QB
  grading := gradingProd QA QB
  isInternal := isInternal_gradingProd QA QB
  smul_one pq := by
    apply Prod.ext
    · change QA.smul pq.1 1 = pq.1; rw [QA.smul_one]
    · change QB.smul pq.2 1 = pq.2; rw [QB.smul_one]
  smul_smul pq a b := by
    apply Prod.ext
    · change QA.smul (QA.smul pq.1 a) b = QA.smul pq.1 (a * b); rw [QA.smul_smul]
    · change QB.smul (QB.smul pq.2 a) b = QB.smul pq.2 (a * b); rw [QB.smul_smul]
  smul_grade n m pq a hpq ha := by
    obtain ⟨h1, h2⟩ := hpq
    exact ⟨QA.smul_grade n m pq.1 a h1 ha, QB.smul_grade n m pq.2 a h2 ha⟩
  d := dProd QA QB
  d_grade n pq hpq := by
    obtain ⟨h1, h2⟩ := hpq
    exact ⟨QA.d_grade n pq.1 h1, QB.d_grade n pq.2 h2⟩
  d_comp_d pq := Prod.ext (QA.d_comp_d pq.1) (QB.d_comp_d pq.2)
  leibniz n pq hpq a := Prod.ext (QA.leibniz n pq.1 hpq.1 a) (QB.leibniz n pq.2 hpq.2 a)

/-- The product of two DG-homs as a DG-hom between the product DG modules. -/
noncomputable def prodHom
    {PA' : Type w₃} [AddCommGroup PA'] [Module R PA']
    {PB' : Type w'} [AddCommGroup PB'] [Module R PB']
    {QA : DGModule R A 𝒜 dA PA} {QA' : DGModule R A 𝒜 dA PA'}
    {QB : DGModule R A 𝒜 dA PB} {QB' : DGModule R A 𝒜 dA PB'}
    (f : DGModule.Hom QA QA') (g : DGModule.Hom QB QB') :
    DGModule.Hom (prodDG QA QB) (prodDG QA' QB') where
  toFun := (f.toFun ∘ₗ LinearMap.fst R _ _).prod (g.toFun ∘ₗ LinearMap.snd R _ _)
  map_smul' := by
    intro pq a
    change (f.toFun (smulProd QA QB pq a).1, g.toFun (smulProd QA QB pq a).2)
        = smulProd QA' QB' (f.toFun pq.1, g.toFun pq.2) a
    rw [smulProd_apply, smulProd_apply]
    exact Prod.ext (f.map_smul' pq.1 a) (g.map_smul' pq.2 a)
  map_grade := by
    intro n pq hpq
    obtain ⟨h1, h2⟩ := hpq
    exact ⟨f.map_grade n pq.1 h1, g.map_grade n pq.2 h2⟩
  map_d := by
    intro pq
    change (f.toFun (dProd QA QB pq).1, g.toFun (dProd QA QB pq).2)
        = dProd QA' QB' (f.toFun pq.1, g.toFun pq.2)
    rw [dProd_apply, dProd_apply]
    exact Prod.ext (f.map_d pq.1) (g.map_d pq.2)

end ProdDG

/-- The binary product of two direct-sums-of-shifts is again a direct
sum of shifts of `A` (concatenate the index sets and shift functions). -/
theorem isDirectSumOfShifts_prodDG
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
    {PA : Type w₁} [AddCommGroup PA] [Module R PA]
    {PB : Type w₂} [AddCommGroup PB] [Module R PB]
    {QA : DGModule R A 𝒜 dA PA} {QB : DGModule R A 𝒜 dA PB}
    (hA : IsDirectSumOfShifts.{u, v, _, t} QA) (hB : IsDirectSumOfShifts.{u, v, _, t} QB) :
    IsDirectSumOfShifts.{u, v, _, t} (ProdDG.prodDG QA QB) := by
  classical
  obtain ⟨ιA, kA, SA, _, _, PSA, ⟨eA, hAact, hAgr, hAd⟩, fA, gA, hgfA, hfgA⟩ := hA
  obtain ⟨ιB, kB, SB, _, _, PSB, ⟨eB, hBact, hBgr, hBd⟩, fB, gB, hgfB, hfgB⟩ := hB
  refine ⟨ιA ⊕ ιB, Sum.elim kA kB, SA × SB, inferInstance, inferInstance,
    ProdDG.prodDG PSA PSB, ?_, ?_⟩
  · -- the model description
    have hes : ∀ (t : SA × SB) (i : ιA ⊕ ιB),
        ((eA.prodCongr eB).trans (SumDS.equiv ιA ιB).symm t) i
          = (Sum.elim (fun jₐ => (eA t.1) jₐ) (fun jᵦ => (eB t.2) jᵦ)) i := by
      intro t i
      show (SumDS.equiv ιA ιB).symm (eA t.1, eB t.2) i = _
      rw [SumDS.equiv_symm_apply]
      cases i with
      | inl jₐ =>
          have := SumDS.fwd_fst_apply (R := R) ιA ιB (SumDS.bwd (R := R) ιA ιB (eA t.1, eB t.2))
              jₐ
          rw [SumDS.fwd_bwd] at this
          simpa using this.symm
      | inr jᵦ =>
          have := SumDS.fwd_snd_apply (R := R) ιA ιB (SumDS.bwd (R := R) ιA ιB (eA t.1, eB t.2))
              jᵦ
          rw [SumDS.fwd_bwd] at this
          simpa using this.symm
    refine ⟨(eA.prodCongr eB).trans (SumDS.equiv ιA ιB).symm, ?_, ?_, ?_⟩
    · -- action componentwise
      intro s a j
      rw [hes, hes]
      cases j with
      | inl jₐ =>
          show (eA ((ProdDG.smulProd PSA PSB s a).1)) jₐ
              = (eA s.1) jₐ * a
          rw [ProdDG.smulProd_apply]
          exact hAact s.1 a jₐ
      | inr jᵦ =>
          show (eB ((ProdDG.smulProd PSA PSB s a).2)) jᵦ
              = (eB s.2) jᵦ * a
          rw [ProdDG.smulProd_apply]
          exact hBact s.2 a jᵦ
    · -- grading
      intro n s
      show s ∈ (ProdDG.gradingProd PSA PSB n) ↔ _
      rw [ProdDG.gradingProd, Submodule.mem_prod, hAgr, hBgr]
      constructor
      · rintro ⟨h1, h2⟩ j
        rw [hes]
        cases j with
        | inl jₐ => exact h1 jₐ
        | inr jᵦ => exact h2 jᵦ
      · intro h
        refine ⟨fun jₐ => ?_, fun jᵦ => ?_⟩
        · have := h (Sum.inl jₐ); rw [hes] at this; exact this
        · have := h (Sum.inr jᵦ); rw [hes] at this; exact this
    · -- differential
      intro s j
      rw [hes, hes]
      show _ = ((-1 : R) ^ (Sum.elim kA kB j).natAbs) • dA.d _
      cases j with
      | inl jₐ =>
          show (eA ((ProdDG.dProd PSA PSB s).1)) jₐ
              = ((-1 : R) ^ (kA jₐ).natAbs) • dA.d ((eA s.1) jₐ)
          rw [ProdDG.dProd_apply]
          exact hAd s.1 jₐ
      | inr jᵦ =>
          show (eB ((ProdDG.dProd PSA PSB s).2)) jᵦ
              = ((-1 : R) ^ (kB jᵦ).natAbs) • dA.d ((eB s.2) jᵦ)
          rw [ProdDG.dProd_apply]
          exact hBd s.2 jᵦ
  · -- DG-isomorphism
    refine ⟨ProdDG.prodHom fA fB, ProdDG.prodHom gA gB, ?_, ?_⟩
    · intro m
      show ((ProdDG.prodHom gA gB).toFun ((ProdDG.prodHom fA fB).toFun m)) = m
      apply Prod.ext
      · show gA.toFun (fA.toFun m.1) = m.1; rw [hgfA]
      · show gB.toFun (fB.toFun m.2) = m.2; rw [hgfB]
    · intro s
      show ((ProdDG.prodHom fA fB).toFun ((ProdDG.prodHom gA gB).toFun s)) = s
      apply Prod.ext
      · show fA.toFun (gA.toFun s.1) = s.1; rw [hfgA]
      · show fB.toFun (gB.toFun s.2) = s.2; rw [hfgB]

end DifferentialGraded.NativeCover

end
