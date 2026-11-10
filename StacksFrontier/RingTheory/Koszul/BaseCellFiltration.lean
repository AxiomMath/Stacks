module

public import Mathlib.Algebra.DirectSum.Finsupp
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedCellFiltration
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductInclusion
public import StacksFrontier.RingTheory.Koszul.CohomologicalDifferentialGradedAlgebra

/-!
# The Koszul algebra over the base ring is orthogonal to the acyclic modules

Let `R` be a commutative ring and let `φ : Rʳ → R` be a functional. The Koszul algebra of `φ` — the
exterior algebra `⋀[R] Rʳ` with contraction by `φ` as its differential and with the `k`-th exterior
power in cohomological degree `-k` — is a differential graded `R`-algebra `K`. Restricting its
right action on itself along the structure map `R ⟶ K` makes it a right differential graded module
over `R` placed in degree zero, and that module is orthogonal on the left to the acyclic
differential graded modules over `R` in degree zero.

The reason is the exterior grading itself: over the base ring in degree zero the cells are the
wedge monomials `ξ_s` for `s ⊆ {1, …, r}`, the cell of exterior degree `m` sits in degree `-m`,
there are none above exterior degree `r`, and the Koszul differential lowers the exterior degree by
one, so the decomposition by exterior degree is a triangular cell decomposition in the sense of
`DifferentialGradedModule.GradedCellData`. No signs appear: the base algebra is concentrated in
degree zero with vanishing differential, so compatibility of the coordinates with the action is
plain `R`-linearity, and the signs carried by the shifts multiply zero.

## Main definitions

* `DifferentialGradedAlgebra.baseHom`: the structure map from `R` in degree zero to a
  differential graded `R`-algebra.
* `Koszul.exteriorDecompose`: the exterior algebra as the direct sum of its exterior powers.
* `Koszul.exteriorCellIndex` and `Koszul.exteriorCellEquiv`: the wedge monomials of a fixed
  exterior degree in `Rʳ`, and the resulting coordinates on that exterior power.
* `Koszul.exteriorCellCoords`: the coordinates of an element of `⋀[R] Rʳ` on the wedge monomials,
  grouped by exterior degree.
* `Koszul.baseModule`: the Koszul algebra as a right differential graded module over `R` placed in
  degree zero.
* `Koszul.gradedCellDataBaseModule`: the triangular cell decomposition of `Koszul.baseModule` by
  exterior degree.

## Main results

* `Koszul.mem_exteriorPower_iff_exteriorDecompose` and
  `Koszul.mem_cohomologicalExteriorGrade_iff_exteriorDecompose`: an element is homogeneous exactly
  when its coordinates outside the corresponding exterior degree vanish.
* `Koszul.exteriorDecompose_contraction_eq_zero`: the Koszul differential strictly lowers the
  exterior degree, read in coordinates.
* `Koszul.leftOrthogonal_acyclic_baseModule`: the Koszul algebra of a functional on `Rʳ`, viewed
  over `R` in degree zero, is orthogonal on the left to the acyclic modules.
* `Koszul.leftOrthogonal_acyclic_powAlgebra_baseModule`: the same for `K_n`, the Koszul algebra of
  the `n`-th powers of a finite sequence.

## Implementation notes

The coordinates are assembled from three pieces: the decomposition of the exterior algebra into its
exterior powers, the basis of the `m`-th exterior power of a free module attached to a basis of
that module (`Module.Basis.exteriorPower`, indexed by the subsets of size `m` of the index set),
and the identification of a finitely supported function with a direct sum. The index set of the
basis lives in the universe of `Fin r`, so it is lifted into the universe of `R`, which is where
`DifferentialGradedModule.GradedCellData` needs it.

Both triangularity properties of the differential come from one lemma: the coordinate of exterior
degree `p` of a contraction depends only on the coordinate of exterior degree `p + 1` of its
argument. That is proved by induction on the direct sum, which avoids having to sum an element over
the support of its decomposition.

Compatibility of the coordinates with the right action is stated here, as
`DifferentialGradedModule.op_smul_eq_smul` and
`DifferentialGradedModule.op_smul_eq_smul_directSum`, for a *variable* differential graded algebra
and a scalar coming from the base ring. Instance synthesis for a right action by
`(DifferentialGradedAlgebra.degreeZero R R).A` does not succeed on its own — the field projection
carrying it is not found once the algebra is this concrete term — so the two statements are made
where the algebra is still a variable and are then used at the concrete one, where the action
appears in a goal that already carries the instance.

## References

* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P).
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality to the
  acyclic modules.
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622), the Koszul algebra.
-/

@[expose] public noncomputable section

open scoped DirectSum ExteriorAlgebra

universe u v

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

variable {A : Type u} [CommRing A] [Algebra R A]

/-- An element of the base ring placed in degree zero is homogeneous of degree `p` exactly when it
vanishes or `p` is zero. -/
theorem mem_degreeZero_grading_iff (p : ℤ) (y : A) :
    y ∈ (degreeZero R A).grading p ↔ (p ≠ 0 → y = 0) := by
  change y ∈ degreeZeroGrading R A p ↔ _
  by_cases hp : p = 0 <;> simp [degreeZeroGrading, hp]

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **The right action of the image of a scalar is the action of that scalar.** -/
theorem op_smul_eq_smul {A : DifferentialGradedAlgebra.{u, u} R}
    {M : DifferentialGradedModule.{u, u, u} A} {a : A.A} {s : R}
    (h : a = algebraMap R A.A s) (x : M.M) : MulOpposite.op a • x = s • x := by
  subst h
  rw [Algebra.algebraMap_eq_smul_one,
    show MulOpposite.op (s • (1 : A.A)) = s • MulOpposite.op (1 : A.A) from rfl,
    smul_assoc s (MulOpposite.op (1 : A.A)) x, MulOpposite.op_one, one_smul]

/-- **The right action of the image of a scalar on a direct sum of copies of the algebra is the
action of that scalar.** -/
theorem op_smul_eq_smul_directSum {A : DifferentialGradedAlgebra.{u, u} R} {ι : Type u}
    {a : A.A} {s : R} (h : a = algebraMap R A.A s) (y : ⨁ (_ : ι), A.A) :
    MulOpposite.op a • y = s • y := by
  subst h
  refine DirectSum.ext fun i => ?_
  rw [DFinsupp.smul_apply, DFinsupp.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    ← Algebra.commutes s (y i), ← Algebra.smul_def]

end DifferentialGradedModule

namespace Koszul

/-! ### The exterior algebra as the direct sum of its exterior powers -/

section Decomposition

variable (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]

/-- **The exterior algebra as the direct sum of its exterior powers**, as an `R`-linear
equivalence. -/
def exteriorDecompose : ExteriorAlgebra R E ≃ₗ[R] ⨁ (m : ℕ), ↥(⋀[R]^m E) :=
  DirectSum.decomposeLinearEquiv fun m : ℕ => ⋀[R]^m E

variable {R E}

/-- The coordinates of a homogeneous element are concentrated in its own exterior degree. -/
theorem exteriorDecompose_coe {m : ℕ} (y : ↥(⋀[R]^m E)) :
    exteriorDecompose R E (y : ExteriorAlgebra R E)
      = DirectSum.of (fun j : ℕ => ↥(⋀[R]^j E)) m y := by
  rw [exteriorDecompose, DirectSum.decomposeLinearEquiv_apply]
  exact DirectSum.decompose_coe (fun j : ℕ => ⋀[R]^j E) y

/-- An element of the `j`-th exterior power has no coordinate in any other exterior degree. -/
theorem exteriorDecompose_eq_zero_of_mem_of_ne {j m : ℕ} (hjm : j ≠ m)
    {x : ExteriorAlgebra R E} (hx : x ∈ ⋀[R]^j E) : exteriorDecompose R E x m = 0 := by
  apply Subtype.ext
  rw [exteriorDecompose, DirectSum.decomposeLinearEquiv_apply]
  simpa using DirectSum.decompose_of_mem_ne (fun j : ℕ => ⋀[R]^j E) hx hjm

/-- **An element lies in the `k`-th exterior power exactly when its coordinates in the other
exterior degrees vanish.** -/
theorem mem_exteriorPower_iff_exteriorDecompose (k : ℕ) (x : ExteriorAlgebra R E) :
    x ∈ ⋀[R]^k E ↔ ∀ m : ℕ, m ≠ k → exteriorDecompose R E x m = 0 := by
  refine ⟨fun hx m hm => exteriorDecompose_eq_zero_of_mem_of_ne (Ne.symm hm) hx, fun h => ?_⟩
  have hy : exteriorDecompose R E x
      = DirectSum.of (fun j : ℕ => ↥(⋀[R]^j E)) k (exteriorDecompose R E x k) := by
    refine DFinsupp.ext fun m => ?_
    by_cases hm : m = k
    · subst hm
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hm, h m hm]
  have hx : x = ((exteriorDecompose R E x k : ↥(⋀[R]^k E)) : ExteriorAlgebra R E) :=
    (exteriorDecompose R E).injective (hy.trans (exteriorDecompose_coe _).symm)
  exact hx ▸ (exteriorDecompose R E x k).2

/-- An element of the exterior algebra vanishes exactly when all of its coordinates do. -/
theorem eq_zero_iff_exteriorDecompose (x : ExteriorAlgebra R E) :
    x = 0 ↔ ∀ m : ℕ, exteriorDecompose R E x m = 0 := by
  refine ⟨fun hx m => by simp [hx], fun h => (exteriorDecompose R E).injective ?_⟩
  exact DFinsupp.ext fun m => by simp [h m]

/-- **An element is homogeneous of cohomological degree `n` exactly when its coordinates in the
exterior degrees `m` with `n + m ≠ 0` vanish.** -/
theorem mem_cohomologicalExteriorGrade_iff_exteriorDecompose (n : ℤ) (x : ExteriorAlgebra R E) :
    x ∈ cohomologicalExteriorGrade R E n ↔
      ∀ m : ℕ, n + (m : ℤ) ≠ 0 → exteriorDecompose R E x m = 0 := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [cohomologicalExteriorGrade_neg_natCast, mem_exteriorPower_iff_exteriorDecompose]
    exact forall_congr' fun m => ⟨fun h hm => h (by omega), fun h hm => h (by omega)⟩
  · rw [cohomologicalExteriorGrade_of_pos R E (by omega), Submodule.mem_bot,
      eq_zero_iff_exteriorDecompose]
    exact forall_congr' fun m => ⟨fun h _ => h, fun h => h (by omega)⟩

/-- **The coordinate of exterior degree `p` of a contraction depends only on the coordinate of
exterior degree `p + 1` of its argument.** This is the form of "the Koszul differential lowers the
exterior degree by one" that avoids summing an element over the support of its decomposition. -/
theorem exteriorDecompose_contraction_of (φ : Module.Dual R E)
    (y : ⨁ (m : ℕ), ↥(⋀[R]^m E)) (p : ℕ) :
    exteriorDecompose R E (contraction φ ((exteriorDecompose R E).symm y)) p
      = exteriorDecompose R E
          (contraction φ ((y (p + 1) : ↥(⋀[R]^(p + 1) E)) : ExteriorAlgebra R E)) p := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | of j b =>
      rw [(exteriorDecompose R E).symm_apply_eq.2 (exteriorDecompose_coe b).symm]
      by_cases hj : j = p + 1
      · subst hj
        rw [DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
        have hzero : exteriorDecompose R E
            (contraction φ ((b : ↥(⋀[R]^j E)) : ExteriorAlgebra R E)) p = 0 := by
          match j with
          | 0 =>
              rw [Stacks.MappingCone.NatIndexed.contraction_eq_zero_of_mem_exteriorPower_zero
                  φ b.2, map_zero]
              rfl
          | (i + 1) =>
              exact exteriorDecompose_eq_zero_of_mem_of_ne (by omega) (contraction_mem φ i b.2)
        rw [hzero]
        simp
  | add y z hy hz =>
      simp only [map_add, DirectSum.add_apply, Submodule.coe_add, hy, hz]

/-- **The Koszul differential strictly lowers the exterior degree**, in coordinates. -/
theorem exteriorDecompose_contraction_eq_zero (φ : Module.Dual R E)
    {x : ExteriorAlgebra R E} {p : ℕ} (hx : exteriorDecompose R E x (p + 1) = 0) :
    exteriorDecompose R E (contraction φ x) p = 0 := by
  have h := exteriorDecompose_contraction_of φ (exteriorDecompose R E x) p
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h, hx]
  simp

end Decomposition

/-! ### The cells of the exterior algebra on a finite free module -/

section Cells

variable (R : Type u) [CommRing R] (r : ℕ)

/-- **The cells of exterior degree `m` of the exterior algebra on `Rʳ`**: the subsets of size `m`
of `{1, …, r}`, indexing the wedge monomials `ξ_s`. The index set is lifted into the universe of
`R`, which is where a cell decomposition of a differential graded module needs it. -/
abbrev exteriorCellIndex (m : ℕ) : Type u := ULift.{u} ↥(Set.powersetCard (Fin r) m)

/-- Above the length of the sequence there are no cells. -/
theorem isEmpty_exteriorCellIndex {m : ℕ} (h : r < m) : IsEmpty (exteriorCellIndex.{u} r m) := by
  constructor
  rintro ⟨⟨t, ht⟩⟩
  have h2 : t.card ≤ r := by simpa using Finset.card_le_univ t
  have h3 : t.card = m := ht
  omega

/-- **The coordinates of an element of the `m`-th exterior power of `Rʳ` on the wedge monomials**
of exterior degree `m`. -/
def exteriorCellEquiv (m : ℕ) :
    ↥(⋀[R]^m (Fin r → R)) ≃ₗ[R] ⨁ (_ : exteriorCellIndex.{u} r m), R :=
  ((Pi.basisFun R (Fin r)).exteriorPower m).repr.trans
    ((Finsupp.domLCongr (Equiv.ulift (α := ↥(Set.powersetCard (Fin r) m))).symm).trans
      (finsuppLEquivDirectSum R R _))

/-- **The coordinates of an element of the exterior algebra of `Rʳ` on the wedge monomials**,
grouped by exterior degree. -/
def exteriorCellCoords :
    ExteriorAlgebra R (Fin r → R) ≃ₗ[R] ⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), R :=
  (exteriorDecompose R (Fin r → R)).trans
    (DFinsupp.mapRange.linearEquiv fun m => exteriorCellEquiv R r m)

variable {R r}

/-- The coordinates of exterior degree `m` of an element are the wedge coordinates of its
component in the `m`-th exterior power. -/
theorem exteriorCellCoords_apply (x : ExteriorAlgebra R (Fin r → R)) (m : ℕ) :
    exteriorCellCoords R r x m
      = exteriorCellEquiv R r m (exteriorDecompose R (Fin r → R) x m) := by
  rw [exteriorCellCoords, LinearEquiv.trans_apply, DFinsupp.mapRange.linearEquiv_apply,
    DFinsupp.mapRange_apply]

/-- The wedge coordinates of exterior degree `m` of an element vanish exactly when its component
in the `m`-th exterior power does. -/
theorem exteriorCellCoords_eq_zero_iff (x : ExteriorAlgebra R (Fin r → R)) (m : ℕ) :
    exteriorCellCoords R r x m = 0 ↔ exteriorDecompose R (Fin r → R) x m = 0 := by
  rw [exteriorCellCoords_apply]
  exact (exteriorCellEquiv R r m).map_eq_zero_iff

end Cells

/-! ### Orthogonality to the acyclic modules -/

section Orthogonality

open DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The Koszul algebra of a functional on `Rʳ`, as a right differential graded module over the
base ring placed in degree zero.** Its underlying module is the exterior algebra, its grading and
its differential are those of the Koszul algebra, and the right action of `R` is multiplication by
the image of `R` in the exterior algebra. -/
def baseModule (φ : Module.Dual R (Fin r → R)) :
    DifferentialGradedModule.{u, u, u} (degreeZero R R) :=
  restrictScalars (baseHom (cohomologicalDifferentialGradedAlgebra R (Fin r → R) φ))
    (regularModule (cohomologicalDifferentialGradedAlgebra R (Fin r → R) φ))

variable (φ : Module.Dual R (Fin r → R))

/-- The underlying module of `Koszul.baseModule φ` is the exterior algebra of `Rʳ`. -/
theorem baseModule_M : (baseModule φ).M = ExteriorAlgebra R (Fin r → R) := rfl

/-- The degree `n` part of `Koszul.baseModule φ` is the cohomological exterior grade `n`. -/
theorem baseModule_grading (n : ℤ) :
    (baseModule φ).grading n = cohomologicalExteriorGrade R (Fin r → R) n := rfl

/-- The differential of `Koszul.baseModule φ` is contraction by `φ`. -/
theorem baseModule_d : (baseModule φ).d = contraction φ := rfl

/-- An element of the Koszul algebra is homogeneous of degree `n` exactly when its wedge
coordinates of exterior degree `m` vanish whenever `n + m ≠ 0`: the cell of exterior degree `m`
sits in degree `-m`. -/
theorem baseModule_mem_grading_iff (n : ℤ) (x : (baseModule φ).M) :
    x ∈ (baseModule φ).grading n ↔ ∀ (m : ℕ) (i : exteriorCellIndex.{u} r m),
      ((exteriorCellCoords R r x) m) i ∈ (degreeZero R R).grading (n + (m : ℤ)) := by
  refine (mem_cohomologicalExteriorGrade_iff_exteriorDecompose n x).trans
    ⟨fun h m i => (mem_degreeZero_grading_iff _ _).2 fun hm => by
        simp [(exteriorCellCoords_eq_zero_iff x m).2 (h m hm)],
      fun h m hm => (exteriorCellCoords_eq_zero_iff x m).1
        (DirectSum.ext fun i => (mem_degreeZero_grading_iff _ _).1 (h m i) hm)⟩

/-- There are no cells above exterior degree `r`, so the coordinates vanish from `r + 1` on. -/
theorem baseModule_coords_eq_zero (x : (baseModule φ).M) (m : ℕ) (hm : r + 1 ≤ m) :
    exteriorCellCoords R r x m = 0 := by
  have : IsEmpty (exteriorCellIndex.{u} r m) := isEmpty_exteriorCellIndex r (by omega)
  exact DirectSum.ext fun i => isEmptyElim i

/-- **The differential lowers the exterior degree strictly**: if the coordinates of `x` of exterior
degree at least `k + 1` vanish, then those of `d x` of exterior degree at least `k` do. -/
theorem baseModule_coords_d_eq_zero (k : ℕ) (x : (baseModule φ).M)
    (hx : exteriorCellCoords R r x (k + 1) = 0) :
    exteriorCellCoords R r ((baseModule φ).d x) k = 0 :=
  (exteriorCellCoords_eq_zero_iff _ k).2
    (exteriorDecompose_contraction_eq_zero φ ((exteriorCellCoords_eq_zero_iff x (k + 1)).1 hx))

/-- **The triangular cell decomposition of the Koszul algebra over the base ring, by exterior
degree.** The cells of exterior degree `m` are the wedge monomials `ξ_s` with `|s| = m`, each in
degree `-m`; there are none above exterior degree `r`, and the Koszul differential lowers the
exterior degree, so it is lower triangular for this decomposition. -/
def gradedCellDataBaseModule : GradedCellData (baseModule φ) := by
  refine gradedCellDataOfCellCoords (I := exteriorCellIndex.{u} r) (fun m _ => (m : ℤ)) (r + 1)
    (exteriorCellCoords R r) ?_ (baseModule_mem_grading_iff φ) (baseModule_coords_eq_zero φ) ?_ ?_
  · intro a x m
    rw [op_smul_eq_smul (s := a) (by simp), op_smul_eq_smul_directSum (s := a) (by simp)]
    exact (congrArg (fun y : ⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), R => y m)
      (map_smul (exteriorCellCoords R r) a x)).trans (DFinsupp.smul_apply _ _ _)
  · intro k x hx m hm
    exact baseModule_coords_d_eq_zero φ m x (hx (m + 1) (by omega))
  · intro k x hx i
    have h0 : exteriorCellCoords R r ((baseModule φ).d x) k = 0 :=
      baseModule_coords_d_eq_zero φ k x (hx (k + 1) (by omega))
    have hl : ((exteriorCellCoords R r ((baseModule φ).d x)) k) i = 0 :=
      (congrArg (fun y : ⨁ (_ : exteriorCellIndex.{u} r k), R => y i) h0).trans rfl
    have hr : ((-1 : ℤ) ^ ((k : ℤ)).natAbs)
        • (degreeZero R R).d ((exteriorCellCoords R r x k) i) = 0 := by
      have hd : (degreeZero R R).d ((exteriorCellCoords R r x k) i) = 0 := rfl
      rw [hd, smul_zero]
    exact hl.trans hr.symm

/-- **The Koszul algebra of a functional on `Rʳ`, viewed as a differential graded module over `R`
placed in degree zero, is orthogonal on the left to the acyclic modules.** The decomposition by
exterior degree is a triangular cell decomposition whose cells are the wedge monomials, so
`DifferentialGradedModule.leftOrthogonal_acyclic_of_gradedCellData` applies. -/
theorem leftOrthogonal_acyclic_baseModule :
    (acyclic' (degreeZero R R)).leftOrthogonal
      ((toHomotopyCategory (degreeZero R R)).obj (baseModule φ)) :=
  leftOrthogonal_acyclic_of_gradedCellData (gradedCellDataBaseModule φ)

/-- **The Koszul algebra `K_n` of the `n`-th powers of a finite sequence, viewed over `R` in degree
zero, is orthogonal on the left to the acyclic modules.** This is
`Koszul.leftOrthogonal_acyclic_baseModule` for the functional cutting out `K_n`. -/
theorem leftOrthogonal_acyclic_powAlgebra_baseModule (f : Fin r → R) (n : ℕ) :
    (acyclic' (degreeZero R R)).leftOrthogonal
      ((toHomotopyCategory (degreeZero R R)).obj
        (restrictScalars (baseHom (powAlgebra f n))
          (regularModule (powAlgebra f n)))) :=
  leftOrthogonal_acyclic_baseModule (seqDual fun i => f i ^ n)

end Orthogonality

end Koszul

end
