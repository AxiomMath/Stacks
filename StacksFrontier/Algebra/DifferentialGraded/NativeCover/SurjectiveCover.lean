module

public import StacksFrontier.Algebra.DifferentialGraded.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.Algebra.DifferentialGraded.NativeCover.DirectSumOfShifts

/-!
# A surjective cover by direct sums of shifts of the algebra

Let `R` be a commutative ring, let `(A, d)` be a differential graded `R`-algebra and let `M`
be a right differential graded `A`-module. For every homogeneous element `m ∈ M^k` one takes
the free differential graded module on two generators `x` of degree `k` and `y` of degree
`k + 1` with `d x = y` and `d y = 0`; as a graded module it is `A[-k] ⊕ A[-k-1]`, it sits in
an admissible short exact sequence with those two ends, and it maps to `M` by `x ↦ m`,
`y ↦ d_M m`. Summing over all homogeneous elements of `M` gives a surjection, sitting in an
admissible short exact sequence `0 → P' → P → P'' → 0` whose two ends are direct sums of
shifts of `A`.

## Main results

* `DifferentialGraded.NativeCover.exists_surjective_cover`: a surjective cover sitting in an
  admissible short exact sequence with both ends direct sums of shifts.

## References

* [The Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace DifferentialGraded.NativeCover

universe u v w w' w₁ w₂ w₃ t

/-! ### Construction data for `exists_surjective_cover`.

The surjective-cover construction is packaged in a namespace so that each
structural obligation becomes an individually-named lemma. The cover module is
`P₁ = S × S` where
`S := ⨁_{g : ι} A`, `ι := Σ n, M^n` indexes the homogeneous elements of `M`.
The first factor is the *x-part* (shift `A[-deg g]`, witness `kX g = -g.1`), the
second is the *y-part* (shift `A[-deg g - 1]`, witness `kY g = -g.1 - 1`).
The differential is `d (s, t) = (d_X s, d_Y t + s)`: the x-summand `x_g` maps to
the y-summand `y_g`, and `d y_g = 0` (up to the diagonal shift differential).
`φ₁ (s, t) = Σ_g (s g) • elt g + Σ_g (t g) • d_M (elt g)`. -/
namespace SurjCover

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : DGAlgebra R A 𝒜}
variable {M : Type w} [AddCommGroup M] [Module R M] (PM : DGModule R A 𝒜 dA M)

/-- Index set of homogeneous elements of `M`. -/
abbrev Idx : Type w := Σ n : ℤ, (PM.grading n)

/-- The degree of an index. -/
def deg (g : Idx PM) : ℤ := g.1

/-- The element of `M` represented by an index. -/
def elt (g : Idx PM) : M := (g.2 : M)

/-- The element indexed by `g` is homogeneous of degree `deg g`. -/
theorem elt_grade (g : Idx PM) : elt PM g ∈ PM.grading (deg PM g) := g.2.2

/-- Shift witness for the x-part. -/
def kX (g : Idx PM) : ℤ := -deg PM g

/-- Shift witness for the y-part. -/
def kY (g : Idx PM) : ℤ := -deg PM g - 1

/-- The x-part end `P'' = ⨁_g A[-deg g]`. -/
noncomputable def PXend : DGModule R A 𝒜 dA (DirectSum (Idx PM) (fun _ => A)) :=
  ShiftSum.shiftDG R A 𝒜 dA (Idx PM) (kX PM)

/-- The y-part end `P' = ⨁_g A[-deg g - 1]`. -/
noncomputable def PYend : DGModule R A 𝒜 dA (DirectSum (Idx PM) (fun _ => A)) :=
  ShiftSum.shiftDG R A 𝒜 dA (Idx PM) (kY PM)

/-- The carrier of the cover: `S × S`. -/
abbrev Carrier : Type (max v w) :=
  (DirectSum (Idx PM) (fun _ => A)) × (DirectSum (Idx PM) (fun _ => A))

/-- The right `A`-action on `P₁`, componentwise. -/
noncomputable def smulP : Carrier PM →ₗ[R] A →ₗ[R] Carrier PM :=
  LinearMap.mk₂ R
    (fun (st : Carrier PM) (a : A) =>
      (ShiftSum.rsmul R A (Idx PM) st.1 a, ShiftSum.rsmul R A (Idx PM) st.2 a))
    (by intro st₁ st₂ a; simp)
    (by intro c st a; simp [Prod.smul_def])
    (by intro st a₁ a₂; simp)
    (by intro st c a; simp)

/-- The differential on `P₁`: `d (s, t) = (d_X s, d_Y t + s)`. -/
noncomputable def dP : Carrier PM →ₗ[R] Carrier PM :=
  ((PXend PM).d ∘ₗ LinearMap.fst R _ _).prod
    (((PYend PM).d ∘ₗ LinearMap.snd R _ _) + LinearMap.fst R _ _)

/-- The grading on `P₁`: degree-`n` part is the product of the two ends' parts. -/
noncomputable def gradingP (n : ℤ) : Submodule R (Carrier PM) :=
  ((PXend PM).grading n).prod ((PYend PM).grading n)

/-- The action on the cover is componentwise on the x- and y-parts. -/
theorem smulP_apply (st : Carrier PM) (a : A) :
    smulP PM st a
      = (ShiftSum.rsmul R A (Idx PM) st.1 a, ShiftSum.rsmul R A (Idx PM) st.2 a) := rfl

/-- The cover differential sends `(s, t)` to `(d_X s, d_Y t + s)`: each x-generator maps to
the corresponding y-generator. -/
theorem dP_apply (st : Carrier PM) :
    dP PM st = ((PXend PM).d st.1, (PYend PM).d st.2 + st.1) := rfl

/-- The product grading on `P₁` is an internal direct sum. -/
theorem isInternal_gradingP :
    DirectSum.IsInternal (gradingP PM) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  obtain ⟨hX1, hX2⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp (PXend
      PM).isInternal
  obtain ⟨hY1, hY2⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp (PYend
      PM).isInternal
  have hprod : ⨆ n, ((PXend PM).grading n).prod ((PYend PM).grading n)
      = (⨆ n, (PXend PM).grading n).prod (⨆ n, (PYend PM).grading n) := by
    apply le_antisymm
    · exact iSup_le fun n => Submodule.prod_mono (le_iSup _ n) (le_iSup _ n)
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      have hx0 : ((x, 0) : Carrier PM) ∈
          ⨆ n, ((PXend PM).grading n).prod ((PYend PM).grading n) := by
        refine Submodule.iSup_induction (motive := fun x => ((x, 0) : Carrier PM) ∈
            ⨆ n, ((PXend PM).grading n).prod ((PYend PM).grading n))
          (fun n => (PXend PM).grading n) hx
          (fun n a ha => Submodule.mem_iSup_of_mem n ⟨ha, Submodule.zero_mem _⟩) ?_ ?_
        · exact Submodule.zero_mem _
        · intro a b ha hb
          have := Submodule.add_mem _ ha hb
          simpa using this
      have hy0 : ((0, y) : Carrier PM) ∈
          ⨆ n, ((PXend PM).grading n).prod ((PYend PM).grading n) := by
        refine Submodule.iSup_induction (motive := fun y => ((0, y) : Carrier PM) ∈
            ⨆ n, ((PXend PM).grading n).prod ((PYend PM).grading n))
          (fun n => (PYend PM).grading n) hy
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
    have hXle : (⨆ (j : ℤ) (_ : j ≠ i), (PXend PM).grading j) ⊓ (PXend PM).grading i = ⊥ := by
      rw [inf_comm, ← disjoint_iff]; exact hX1 i
    have hYle : (⨆ (j : ℤ) (_ : j ≠ i), (PYend PM).grading j) ⊓ (PYend PM).grading i = ⊥ := by
      rw [inf_comm, ← disjoint_iff]; exact hY1 i
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    calc ((PXend PM).grading i).prod ((PYend PM).grading i)
            ⊓ ⨆ (j : ℤ) (_ : j ≠ i), ((PXend PM).grading j).prod ((PYend PM).grading j)
          ≤ ((PXend PM).grading i).prod ((PYend PM).grading i)
            ⊓ (⨆ (j : ℤ) (_ : j ≠ i), (PXend PM).grading j).prod
                (⨆ (j : ℤ) (_ : j ≠ i), (PYend PM).grading j) := by
            apply inf_le_inf_left
            refine iSup_le fun j => iSup_le fun hj => ?_
            exact Submodule.prod_mono (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
              (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
      _ = (((PXend PM).grading i) ⊓ ⨆ (j : ℤ) (_ : j ≠ i), (PXend PM).grading j).prod
            (((PYend PM).grading i) ⊓ ⨆ (j : ℤ) (_ : j ≠ i), (PYend PM).grading j) := by
            rw [Submodule.prod_inf_prod]
      _ = ⊥ := by
            rw [inf_comm ((PXend PM).grading i), inf_comm ((PYend PM).grading i),
              hXle, hYle, Submodule.prod_bot]
  · change (⨆ n, ((PXend PM).grading n).prod ((PYend PM).grading n)) = ⊤
    rw [hprod, hX2, hY2, Submodule.prod_top]

/-- The differential of `P₁` raises degree by one. The interesting part is
the cross term: the x-summand `s ∈ X^n` (i.e. `s ∈ gradingSub kX n`) lands, via
the `+ s` term, in `Y^{n+1}` (i.e. `gradingSub kY (n+1)`); indeed
`n + 1 + kY g = n + 1 + (-deg g - 1) = n + kX g`. -/
theorem dP_grade (n : ℤ) (st : Carrier PM) (hst : st ∈ gradingP PM n) :
    dP PM st ∈ gradingP PM (n + 1) := by
  rw [dP_apply]
  obtain ⟨hX, hY⟩ := hst
  refine ⟨(PXend PM).d_grade n st.1 hX, Submodule.add_mem _ ((PYend PM).d_grade n st.2 hY) ?_⟩
  show st.1 ∈ (PYend PM).grading (n + 1)
  intro g
  have hg : st.1 g ∈ 𝒜 (n + kX PM g) := hX g
  rwa [show n + 1 + kY PM g = n + kX PM g by unfold kX kY deg; ring]

/-- The differential of `P₁` squares to zero. The y-component requires the sign
identity `(-1)^|kY g| = -(-1)^|kX g|` (since `kY g = kX g - 1`), so the two
contributions `d_Y(s) + s` followed by `d_Y` plus the carried `d_X s` cancel. -/
theorem dP_comp_dP (st : Carrier PM) : dP PM (dP PM st) = 0 := by
  rw [dP_apply, dP_apply]
  refine Prod.ext ((PXend PM).d_comp_d st.1) ?_
  · change (PYend PM).d ((PYend PM).d st.2 + st.1) + (PXend PM).d st.1 = 0
    rw [map_add, (PYend PM).d_comp_d st.2, zero_add]
    -- remaining: (PYend).d st.1 + (PXend).d st.1 = 0
    refine DirectSum.ext (fun j => ?_)
    rw [DirectSum.add_apply, DirectSum.zero_apply]
    change (ShiftSum.diffDiag R A dA (Idx PM) (kY PM) st.1) j
        + (ShiftSum.diffDiag R A dA (Idx PM) (kX PM) st.1) j = 0
    rw [ShiftSum.diffDiag_apply, ShiftSum.diffDiag_apply]
    have hsign : ((-1 : R) ^ (kY PM j).natAbs) = -((-1 : R) ^ (kX PM j).natAbs) := by
      have hpar : (kY PM j).natAbs % 2 ≠ (kX PM j).natAbs % 2 := by
        unfold kY kX deg; omega
      rcases Nat.even_or_odd ((kX PM j).natAbs) with he | ho
      · have ho' : Odd ((kY PM j).natAbs) := by
          rw [Nat.odd_iff]; rw [Nat.even_iff] at he; omega
        rw [Even.neg_one_pow he, Odd.neg_one_pow ho']
      · have he' : Even ((kY PM j).natAbs) := by
          rw [Nat.even_iff]; rw [Nat.odd_iff] at ho; omega
        rw [Even.neg_one_pow he', Odd.neg_one_pow ho]; ring
    rw [hsign, neg_smul, neg_add_cancel]

/-- The cover differential satisfies the graded Leibniz rule. -/
theorem leibnizP (n : ℤ) (st : Carrier PM) (hst : st ∈ gradingP PM n) (a : A) :
    dP PM (smulP PM st a)
      = smulP PM (dP PM st) a + ((-1 : R) ^ n.natAbs) • smulP PM st (dA.d a) := by
  obtain ⟨hX, hY⟩ := hst
  rw [smulP_apply, dP_apply, dP_apply, smulP_apply, smulP_apply]
  apply Prod.ext
  · change (PXend PM).d (ShiftSum.rsmul R A (Idx PM) st.1 a)
        = ShiftSum.rsmul R A (Idx PM) ((PXend PM).d st.1) a
          + ((-1 : R) ^ n.natAbs) • ShiftSum.rsmul R A (Idx PM) st.1 (dA.d a)
    exact (PXend PM).leibniz n st.1 hX a
  · change (PYend PM).d (ShiftSum.rsmul R A (Idx PM) st.2 a) + ShiftSum.rsmul R A (Idx PM) st.1 a
        = ShiftSum.rsmul R A (Idx PM) ((PYend PM).d st.2 + st.1) a
          + ((-1 : R) ^ n.natAbs) • ShiftSum.rsmul R A (Idx PM) st.2 (dA.d a)
    have hL : (PYend PM).d (ShiftSum.rsmul R A (Idx PM) st.2 a)
        = ShiftSum.rsmul R A (Idx PM) ((PYend PM).d st.2) a
          + ((-1 : R) ^ n.natAbs) • ShiftSum.rsmul R A (Idx PM) st.2 (dA.d a) :=
      (PYend PM).leibniz n st.2 hY a
    have hadd : ShiftSum.rsmul R A (Idx PM) ((PYend PM).d st.2 + st.1) a
        = ShiftSum.rsmul R A (Idx PM) ((PYend PM).d st.2) a
          + ShiftSum.rsmul R A (Idx PM) st.1 a := by
      rw [map_add]; rfl
    rw [hadd]
    change (PYend PM).d (ShiftSum.rsmul R A (Idx PM) st.2 a) + ShiftSum.rsmul R A (Idx PM) st.1 a
        = ShiftSum.rsmul R A (Idx PM) ((PYend PM).d st.2) a
          + ShiftSum.rsmul R A (Idx PM) st.1 a
          + ((-1 : R) ^ n.natAbs) • ShiftSum.rsmul R A (Idx PM) st.2 (dA.d a)
    rw [hL]
    abel

/-- The cover DG `A`-module `P₁`. -/
noncomputable def coverDG : DGModule R A 𝒜 dA (Carrier PM) where
  smul := smulP PM
  grading := gradingP PM
  isInternal := isInternal_gradingP PM
  smul_one st := by
    apply Prod.ext
    · change ShiftSum.rsmul R A (Idx PM) st.1 1 = st.1
      refine DirectSum.ext (fun j => ?_); rw [ShiftSum.rsmul_apply]; simp
    · change ShiftSum.rsmul R A (Idx PM) st.2 1 = st.2
      refine DirectSum.ext (fun j => ?_); rw [ShiftSum.rsmul_apply]; simp
  smul_smul st a b := by
    apply Prod.ext
    · change ShiftSum.rsmul R A (Idx PM) (ShiftSum.rsmul R A (Idx PM) st.1 a) b
          = ShiftSum.rsmul R A (Idx PM) st.1 (a * b)
      refine DirectSum.ext (fun j => ?_)
      rw [ShiftSum.rsmul_apply, ShiftSum.rsmul_apply, ShiftSum.rsmul_apply, mul_assoc]
    · change ShiftSum.rsmul R A (Idx PM) (ShiftSum.rsmul R A (Idx PM) st.2 a) b
          = ShiftSum.rsmul R A (Idx PM) st.2 (a * b)
      refine DirectSum.ext (fun j => ?_)
      rw [ShiftSum.rsmul_apply, ShiftSum.rsmul_apply, ShiftSum.rsmul_apply, mul_assoc]
  smul_grade n m st a hst ha := by
    obtain ⟨hs1, hs2⟩ := hst
    exact ⟨(PXend PM).smul_grade n m st.1 a hs1 ha,
           (PYend PM).smul_grade n m st.2 a hs2 ha⟩
  d := dP PM
  d_grade := dP_grade PM
  d_comp_d := dP_comp_dP PM
  leibniz := leibnizP PM

open Classical in
/-- The x-component of `φ₁`: `lof g c ↦ (elt g) • c`. -/
noncomputable def coverHomX : (DirectSum (Idx PM) (fun _ => A)) →ₗ[R] M :=
  DirectSum.toModule R (Idx PM) M (fun g => PM.smul (elt PM g))

open Classical in
/-- The y-component of `φ₁`: `lof g c ↦ (d_M (elt g)) • c`. -/
noncomputable def coverHomY : (DirectSum (Idx PM) (fun _ => A)) →ₗ[R] M :=
  DirectSum.toModule R (Idx PM) M (fun g => PM.smul (PM.d (elt PM g)))

open Classical in
/-- The x-part of the cover map sends the generator `1_g` to the element `elt g`. -/
theorem coverHomX_lof (g : Idx PM) (c : A) :
    coverHomX PM (DirectSum.lof R (Idx PM) (fun _ => A) g c)
      = PM.smul (elt PM g) c := by
  unfold coverHomX; rw [DirectSum.toModule_lof]

open Classical in
/-- The y-part of the cover map sends the generator `1_g` to `d_M (elt g)`. -/
theorem coverHomY_lof (g : Idx PM) (c : A) :
    coverHomY PM (DirectSum.lof R (Idx PM) (fun _ => A) g c)
      = PM.smul (PM.d (elt PM g)) c := by
  unfold coverHomY; rw [DirectSum.toModule_lof]

/-- The right action on the direct sum multiplies a single summand on the right. -/
private theorem rsmul_lof [DecidableEq (Idx PM)] (g : Idx PM) (c a : A) :
    ShiftSum.rsmul R A (Idx PM) (DirectSum.lof R (Idx PM) (fun _ => A) g c) a
      = DirectSum.lof R (Idx PM) (fun _ => A) g (c * a) := by
  refine DirectSum.ext (fun j => ?_)
  rw [ShiftSum.rsmul_apply]
  rw [show DirectSum.lof R (Idx PM) (fun _ => A) g c
        = DirectSum.of (fun _ : Idx PM => A) g c from rfl,
      show DirectSum.lof R (Idx PM) (fun _ => A) g (c * a)
        = DirectSum.of (fun _ : Idx PM => A) g (c * a) from rfl,
      DirectSum.of_apply, DirectSum.of_apply]
  by_cases h : g = j
  · subst h; simp
  · simp [h]

/-- The shifted differential acts on a single summand by a sign times `dA.d`. -/
private theorem diffDiag_lof [DecidableEq (Idx PM)] (k : Idx PM → ℤ) (g : Idx PM) (c : A) :
    ShiftSum.diffDiag R A dA (Idx PM) k (DirectSum.lof R (Idx PM) (fun _ => A) g c)
      = ((-1 : R) ^ (k g).natAbs) • DirectSum.lof R (Idx PM) (fun _ => A) g (dA.d c) := by
  refine DirectSum.ext (fun j => ?_)
  rw [ShiftSum.diffDiag_apply, DirectSum.smul_apply]
  rw [show DirectSum.lof R (Idx PM) (fun _ => A) g c
        = DirectSum.of (fun _ : Idx PM => A) g c from rfl,
      show DirectSum.lof R (Idx PM) (fun _ => A) g (dA.d c)
        = DirectSum.of (fun _ : Idx PM => A) g (dA.d c) from rfl,
      DirectSum.of_apply, DirectSum.of_apply]
  by_cases h : g = j
  · subst h; simp
  · simp [h]

/-- A linear map out of the direct sum that is right `A`-linear on each summand is right
`A`-linear. -/
private theorem map_rsmul_of_lof [DecidableEq (Idx PM)] (v : Idx PM → M)
    (f : DirectSum (Idx PM) (fun _ => A) →ₗ[R] M)
    (hf : ∀ g c, f (DirectSum.lof R (Idx PM) (fun _ => A) g c) = PM.smul (v g) c)
    (s : DirectSum (Idx PM) (fun _ => A)) (a : A) :
    f (ShiftSum.rsmul R A (Idx PM) s a) = PM.smul (f s) a := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of g c =>
      rw [show DirectSum.of (fun _ : Idx PM => A) g c
            = DirectSum.lof R (Idx PM) (fun _ => A) g c from rfl,
        rsmul_lof, hf, hf, PM.smul_smul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- A linear map out of the direct sum sends `s` into `N` once it sends each summand into `N`. -/
private theorem map_mem_of_forall_lof_mem [DecidableEq (Idx PM)]
    (f : DirectSum (Idx PM) (fun _ => A) →ₗ[R] M)
    (N : Submodule R M) (s : DirectSum (Idx PM) (fun _ => A))
    (h : ∀ j, f (DirectSum.lof R (Idx PM) (fun _ => A) j (s j)) ∈ N) : f s ∈ N := by
  classical
  have hdecomp : s = ∑ j ∈ DFinsupp.support s, DirectSum.of (fun _ : Idx PM => A) j (s j) :=
    (DirectSum.sum_support_of s).symm
  rw [hdecomp, map_sum]
  exact Submodule.sum_mem _ (fun j _ => h j)

open Classical in
/-- The x-part of the cover map is `A`-linear for the right action. -/
theorem coverHomX_rsmul (s : DirectSum (Idx PM) (fun _ => A)) (a : A) :
    coverHomX PM (ShiftSum.rsmul R A (Idx PM) s a)
      = PM.smul (coverHomX PM s) a :=
  map_rsmul_of_lof PM (elt PM) _ (coverHomX_lof PM) s a

open Classical in
/-- The y-part of the cover map is `A`-linear for the right action. -/
theorem coverHomY_rsmul (s : DirectSum (Idx PM) (fun _ => A)) (a : A) :
    coverHomY PM (ShiftSum.rsmul R A (Idx PM) s a)
      = PM.smul (coverHomY PM s) a :=
  map_rsmul_of_lof PM (fun g => PM.d (elt PM g)) _ (coverHomY_lof PM) s a

/-- If every component of `s` lands in the right graded piece, `coverHomX s`
is homogeneous of degree `n`. -/
theorem coverHomX_mem_grade (n : ℤ) (s : DirectSum (Idx PM) (fun _ => A))
    (hs : ∀ j, s j ∈ 𝒜 (n + kX PM j)) :
    coverHomX PM s ∈ PM.grading n := by
  classical
  refine map_mem_of_forall_lof_mem PM _ _ s (fun j => ?_)
  rw [coverHomX_lof]
  have hsmul := PM.smul_grade (deg PM j) (n + kX PM j) (elt PM j) (s j)
    (elt_grade PM j) (hs j)
  rwa [show deg PM j + (n + kX PM j) = n by simp only [kX]; ring] at hsmul

/-- If every component of `s` lands in the right graded piece, `coverHomY s`
is homogeneous of degree `n`. -/
theorem coverHomY_mem_grade (n : ℤ) (s : DirectSum (Idx PM) (fun _ => A))
    (hs : ∀ j, s j ∈ 𝒜 (n + kY PM j)) :
    coverHomY PM s ∈ PM.grading n := by
  classical
  refine map_mem_of_forall_lof_mem PM _ _ s (fun j => ?_)
  rw [coverHomY_lof]
  have hd : PM.d (elt PM j) ∈ PM.grading (deg PM j + 1) :=
    PM.d_grade (deg PM j) (elt PM j) (elt_grade PM j)
  have hsmul := PM.smul_grade (deg PM j + 1) (n + kY PM j) (PM.d (elt PM j)) (s j)
    hd (hs j)
  rwa [show deg PM j + 1 + (n + kY PM j) = n by simp only [kY]; ring] at hsmul

open Classical in
/-- The y-chain identity: `coverHomY` intertwines `PYend.d` with `PM.d`. -/
theorem coverHomY_dchain (t : DirectSum (Idx PM) (fun _ => A)) :
    coverHomY PM ((PYend PM).d t) = PM.d (coverHomY PM t) := by
  classical
  induction t using DirectSum.induction_on with
  | zero => simp
  | of g c =>
      have hdd : (PYend PM).d (DirectSum.lof R (Idx PM) (fun _ => A) g c)
          = ((-1 : R) ^ (kY PM g).natAbs)
              • DirectSum.lof R (Idx PM) (fun _ => A) g (dA.d c) :=
        diffDiag_lof PM (kY PM) g c
      rw [show DirectSum.of (fun _ : Idx PM => A) g c
            = DirectSum.lof R (Idx PM) (fun _ => A) g c from rfl]
      rw [hdd, map_smul, coverHomY_lof, coverHomY_lof]
      -- RHS via Leibniz on `PM.d (elt g) ∈ grading (deg g + 1)`
      have hL := PM.leibniz (deg PM g + 1) (PM.d (elt PM g))
        (PM.d_grade (deg PM g) (elt PM g) (elt_grade PM g)) c
      rw [hL, PM.d_comp_d]
      -- now goal: c^|kY| • smul (PM.d (elt g)) (dA.d c)
      --   = smul 0 c + (-1)^|deg g+1| • smul (PM.d (elt g)) (dA.d c)
      rw [map_zero, LinearMap.zero_apply, zero_add]
      congr 1
      -- sign: |kY g| = |deg g + 1|
      have hsign : (kY PM g).natAbs = (deg PM g + 1).natAbs := by
        simp only [kY]; rw [show -deg PM g - 1 = -(deg PM g + 1) by ring,
          Int.natAbs_neg]
      rw [hsign]
  | add x y hx hy => simp [map_add, hx, hy]

open Classical in
/-- The x-chain (plus cross-term) identity. -/
theorem coverHomX_dchain (s : DirectSum (Idx PM) (fun _ => A)) :
    coverHomX PM ((PXend PM).d s) + coverHomY PM s = PM.d (coverHomX PM s) := by
  classical
  induction s using DirectSum.induction_on with
  | zero => simp
  | of g c =>
      have hdd : (PXend PM).d (DirectSum.lof R (Idx PM) (fun _ => A) g c)
          = ((-1 : R) ^ (kX PM g).natAbs)
              • DirectSum.lof R (Idx PM) (fun _ => A) g (dA.d c) :=
        diffDiag_lof PM (kX PM) g c
      rw [show DirectSum.of (fun _ : Idx PM => A) g c
            = DirectSum.lof R (Idx PM) (fun _ => A) g c from rfl]
      rw [hdd, map_smul, coverHomX_lof, coverHomX_lof, coverHomY_lof]
      have hL := PM.leibniz (deg PM g) (elt PM g) (elt_grade PM g) c
      rw [hL]
      have hsign : (kX PM g).natAbs = (deg PM g).natAbs := by
        simp only [kX]; rw [Int.natAbs_neg]
      rw [hsign, add_comm]
  | add x y hx hy =>
      simp only [map_add]
      rw [show coverHomX PM ((PXend PM).d x) + coverHomX PM ((PXend PM).d y)
            + (coverHomY PM x + coverHomY PM y)
          = (coverHomX PM ((PXend PM).d x) + coverHomY PM x)
            + (coverHomX PM ((PXend PM).d y) + coverHomY PM y) by abel]
      rw [hx, hy]

/-- The covering DG-hom `φ₁ : P₁ → M`. -/
noncomputable def coverHom : DGModule.Hom (coverDG PM) PM where
  toFun := (coverHomX PM ∘ₗ LinearMap.fst R _ _) + (coverHomY PM ∘ₗ LinearMap.snd R _ _)
  map_smul' := by
    intro st a
    change coverHomX PM ((smulP PM st a).1) + coverHomY PM ((smulP PM st a).2)
        = PM.smul (coverHomX PM st.1 + coverHomY PM st.2) a
    rw [smulP_apply]
    simp only []
    rw [coverHomX_rsmul, coverHomY_rsmul, ← LinearMap.add_apply, ← map_add]
  map_grade := by
    intro n st hst
    change coverHomX PM st.1 + coverHomY PM st.2 ∈ PM.grading n
    obtain ⟨hs1, hs2⟩ := hst
    refine (PM.grading n).add_mem ?_ ?_
    · exact coverHomX_mem_grade PM n st.1 (fun j => (ShiftSum.mem_gradingSub
        R A 𝒜 (Idx PM) (kX PM) n st.1).mp hs1 j)
    · exact coverHomY_mem_grade PM n st.2 (fun j => (ShiftSum.mem_gradingSub
        R A 𝒜 (Idx PM) (kY PM) n st.2).mp hs2 j)
  map_d := by
    intro st
    change coverHomX PM ((dP PM st).1) + coverHomY PM ((dP PM st).2)
        = PM.d (coverHomX PM st.1 + coverHomY PM st.2)
    rw [dP_apply]
    simp only [map_add]
    rw [coverHomY_dchain]
    rw [show coverHomX PM ((PXend PM).d st.1)
            + (PM.d (coverHomY PM st.2) + coverHomY PM st.1)
          = (coverHomX PM ((PXend PM).d st.1) + coverHomY PM st.1)
            + PM.d (coverHomY PM st.2) by abel]
    rw [coverHomX_dchain]

open Classical in
/-- The cover map `φ₁` is surjective. -/
theorem coverHom_surjective : (coverHom PM).Surjective := by
  rw [DGModule.Hom.Surjective, ← LinearMap.range_eq_top]
  rw [← top_le_iff]
  have hsup : (⨆ n, PM.grading n) = ⊤ :=
    PM.isInternal.submodule_iSup_eq_top
  rw [← hsup, iSup_le_iff]
  intro n
  rw [IsConcreteLE.le_iff]
  intro m hm
  refine ⟨(DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, hm⟩⟩ 1, 0), ?_⟩
  change coverHomX PM (DirectSum.lof R (Idx PM) (fun _ => A) ⟨n, ⟨m, hm⟩⟩ 1) + coverHomY PM 0 = m
  rw [coverHomX_lof, map_zero, add_zero]
  show PM.smul (elt PM ⟨n, ⟨m, hm⟩⟩) 1 = m
  rw [PM.smul_one]
  rfl

/-- The admissible short exact sequence
`0 → P' → P₁ → P'' → 0` (y-part included, x-part projected). -/
theorem admissibleSES_cover :
    Nonempty (AdmissibleSES (PYend PM) (coverDG PM) (PXend PM)) := by
  classical
  refine ⟨{
    i := {
      toFun := LinearMap.inr R _ _
      map_smul' := by
        intro t a
        change smulP PM (0, t) a = (0, ShiftSum.rsmul R A (Idx PM) t a)
        rw [smulP_apply]
        simp
      map_grade := by
        intro n t ht
        exact ⟨Submodule.zero_mem _, ht⟩
      map_d := by
        intro t
        change (0, (PYend PM).d t) = dP PM (0, t)
        rw [dP_apply]
        simp }
    p := {
      toFun := LinearMap.fst R _ _
      map_smul' := by
        intro st a
        change (smulP PM st a).1 = ShiftSum.rsmul R A (Idx PM) st.1 a
        rw [smulP_apply]
      map_grade := by
        intro n st hst
        exact hst.1
      map_d := by
        intro st
        change (dP PM st).1 = (PXend PM).d st.1
        rw [dP_apply] }
    i_inj := by
      intro t₁ t₂ h
      have := congrArg Prod.snd h
      simpa using this
    p_surj := by
      intro s
      exact ⟨(s, 0), rfl⟩
    exact := by
      apply Submodule.ext
      intro st
      constructor
      · rintro ⟨t, rfl⟩
        change (0 : DirectSum (Idx PM) (fun _ => A)) = 0
        rfl
      · intro hst
        refine ⟨st.2, ?_⟩
        have h0 : st.1 = 0 := hst
        change (0, st.2) = st
        rw [← h0]
    splitEquiv := LinearEquiv.prodComm R _ _
    splitEquiv_smul := by
      intro st a
      rfl
    splitEquiv_grade := by
      intro n st hst
      exact ⟨hst.2, hst.1⟩
    splitEquiv_symm_grade := by
      intro n k x hk hx
      exact ⟨hx, hk⟩
    splitEquiv_i := by
      intro t
      rfl
    splitEquiv_p := by
      intro st
      rfl }⟩

end SurjCover

/-- **Cover data.** Packages the full output of `exists_surjective_cover`
(the cover module, the surjective DG-hom, and the admissible SES with
`IsDirectSumOfShifts` ends) from the `SurjCover` construction. -/
theorem exists_surjective_cover_data
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    {M : Type w} [AddCommGroup M] [Module R M] (PM : DGModule R A 𝒜 dA M) :
    ∃ (P₁ : Type (max v w)) (_ : AddCommGroup P₁) (_ : Module R P₁)
      (PP₁ : DGModule R A 𝒜 dA P₁) (φ₁ : DGModule.Hom PP₁ PM),
      φ₁.Surjective ∧
      (∃ (P' : Type (max v w)) (_ : AddCommGroup P') (_ : Module R P')
        (PP' : DGModule R A 𝒜 dA P')
        (P'' : Type (max v w)) (_ : AddCommGroup P'') (_ : Module R P'')
        (PP'' : DGModule R A 𝒜 dA P''),
        IsDirectSumOfShifts.{u, v, _, w} PP' ∧ IsDirectSumOfShifts.{u, v, _, w} PP'' ∧
        Nonempty (AdmissibleSES PP' PP₁ PP'')) :=
  ⟨SurjCover.Carrier PM, inferInstance, inferInstance, SurjCover.coverDG PM,
    SurjCover.coverHom PM, SurjCover.coverHom_surjective PM,
    _, inferInstance, inferInstance, SurjCover.PYend PM,
    _, inferInstance, inferInstance, SurjCover.PXend PM,
    shiftDG_isDirectSumOfShifts dA _ _, shiftDG_isDirectSumOfShifts dA _ _,
    SurjCover.admissibleSES_cover PM⟩

/-- **Surjective cover** (properties (1) and (3) of `exists_dgModule_surjective_cover`).
For every DG `A`-module `M` there is a DG `A`-module `P₁`, a *surjective*
DG-hom `φ₁ : P₁ → M`, and an admissible short exact sequence `0 → P' → P₁ → P'' → 0`
with both ends direct sums of shifts of `A`.

*Argument.* Let `ι₁ := Σ n : ℤ, M^n` index the homogeneous elements of `M`
(using internality of `M`'s grading, every element of `M` is a finite sum of
homogeneous ones).  For `g = ⟨n, m⟩` build the free two-generator module `P_g`
with generators `x_g` (degree `n`, `d x_g = y_g`) and `y_g` (degree `n+1`,
`d y_g = 0`); as a graded `A`-module `P_g ≅ A[-n] ⊕ A[-n-1]`.  Set
`P₁ := ⨁_g P_g`, with `φ₁ : P₁ → M`, `x_g ↦ m`, `y_g ↦ d_M m`, extended
`A`-linearly; `φ₁` is a DG-hom because `φ₁(d x_g) = φ₁ y_g = d_M m = d_M(φ₁ x_g)`
and `φ₁(d y_g) = 0 = d_M(d_M m) = d_M(φ₁ y_g)`.  It is surjective since every
homogeneous `m ∈ M^n` equals `φ₁(x_{⟨n,m⟩})` and the homogeneous elements span
`M`.  Put `P'' := ⨁_g A[-n_g]` (the `x`-summands) and `P' := ⨁_g A[-n_g-1]` (the
`y`-summands); both are `IsDirectSumOfShifts` (they are `shiftDG`s, by
`shiftDG_isDirectSumOfShifts`).  The inclusion `i : P' → P₁` of the `y`-part and
the projection `p : P₁ → P''` onto the `x`-part are DG-homs (the differential of
`P₁` maps the `x`-part to the `y`-part and kills the `y`-part, so `i` and `p`
commute with `d`); `i` is injective, `p` surjective, `range i = ker p`, and the
graded `A`-module splitting `P₁ ≅ P' ⊕ P''` is the obvious one (it is graded and
`A`-linear, and need NOT commute with `d`).  Hence `AdmissibleSES P' P₁ P''`. -/
alias exists_surjective_cover := DifferentialGraded.NativeCover.exists_surjective_cover_data

end DifferentialGraded.NativeCover

end
