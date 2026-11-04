module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.DeterminantHypersurface
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# The locus in the parameter space where the rank of an endomorphism drops by at least two

Let `V` be a vector space of dimension at least two over an algebraically closed field and let
`𝐏 = 𝐏((End V)ᵛ)` be the parameter space of the projective transformations of `𝐏(V)`. The
source's proof of Tag 0B1S analyses the determinant hypersurface `Z = 𝐏 ∖ PGL(V)` by observing
that *for a general point `[g]` of `Z` the cokernel of `g` has dimension one*: the classes whose
rank drops by two or more form a subset of `Z` of codimension at least two in `𝐏`, and so may be
discarded along with the rest of the bad locus.

This file supplies that step in the form the reducible version of Tag 0B2T consumes. The
discarded set is cut out of `Z` by a single minor of size `dim V - 1`: every class of rank at
most `dim V - 2` kills every such minor, so one of them suffices, and the resulting closed set is
a *proper* subset of `Z` because the endomorphism fixing all but the last basis vector is
singular with leading minor `1`. Since `Z` is irreducible and is itself a proper closed subset of
`𝐏`, the closure of any point of that set sits in a strict chain of length two below `𝐏`, which
is codimension at least two.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.leadingMinorLocus`: the closed subset of `Z` where
  the leading minor of size `dim V - 1` also vanishes.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.coe_mem_leadingMinorLocus_of_finrank_range_add_two_le`
  — every class of endomorphisms whose rank drops by at least two lies in that locus.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.leadingMinorLocus_ne_determinantHypersurface`: the
  locus is a proper subset of the determinant hypersurface.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.two_le_codimension_of_mem_leadingMinorLocus`:
  **every point of the locus has codimension at least two in `𝐏`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.two_le_codimension_of_mem_of_isClosed_ssubset`: the
  chain argument in general — a proper closed subset of a proper irreducible closed subset of an
  irreducible space has codimension at least two at each of its points.

## Implementation notes

Which minor is used is immaterial, and the definition fixes the leading one rather than
quantifying over all of them: the locus is only ever an upper bound for the rank-drop locus, so
one minor in the ideal of that locus does as well as all of them, and only the easy half of the
rank-versus-minors correspondence is needed — a square submatrix with nonzero determinant has
full rank, and a submatrix does not have larger rank than the matrix. The converse half, that a
matrix of rank `r` has a nonvanishing minor of size `r`, is not in Mathlib and is not needed:
properness of the inclusion into `Z` is witnessed by an explicit endomorphism instead.

The codimension here is `codimension`, the coheight in the poset of irreducible closed subsets.
What is produced is the pointwise form `∀ x ∈ B, 2 ≤ codimension (closureSingleton x)`, which on
a sober space says that every irreducible closed subset of `B`, in particular every irreducible
component, has codimension at least two.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [IsAlgClosed k]
  [Module.Finite k V]

/-- The embedding of the first `dim V - 1` coordinates into all `dim V` of them. -/
private def leadingIndex (i : Fin (Module.finrank k V - 1)) : Fin (Module.finrank k V) :=
  ⟨i, by have := i.isLt; omega⟩

omit [IsAlgClosed k] [Module.Finite k V] in
private theorem leadingIndex_injective : Function.Injective (leadingIndex k V) := by
  intro i j hij
  have h : ((leadingIndex k V i : Fin (Module.finrank k V)) : ℕ) =
      ((leadingIndex k V j : Fin (Module.finrank k V)) : ℕ) := congrArg Fin.val hij
  exact Fin.ext h

omit [IsAlgClosed k] [Module.Finite k V] in
private theorem val_leadingIndex_succ_ne (i : Fin (Module.finrank k V - 1)) :
    ((leadingIndex k V i : Fin (Module.finrank k V)) : ℕ) + 1 ≠ Module.finrank k V := by
  have := i.isLt
  have : ((leadingIndex k V i : Fin (Module.finrank k V)) : ℕ) = (i : ℕ) := rfl
  omega

/-- **The locus in `Z` cut out by the leading minor.** The points of the determinant
hypersurface at which the leading `(dim V - 1) × (dim V - 1)` minor also vanishes. Every class
of endomorphisms whose rank drops by at least two lies here, and the locus is a proper subset of
the irreducible `Z`, so every one of its points has codimension at least two in `𝐏`. Which minor
is used is immaterial: the locus is only ever an upper bound for the rank-drop locus. -/
@[no_expose] public def leadingMinorLocus :
    Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) :=
  determinantHypersurface k V ∩
    ((Proj.basicOpen (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
        (minorForm k V (leadingIndex k V) (leadingIndex k V)) :
      (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))).Opens) :
      Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))))ᶜ

omit [IsAlgClosed k] in
/-- The leading-minor locus is closed. -/
public theorem isClosed_leadingMinorLocus : IsClosed (leadingMinorLocus k V) :=
  (isClosed_determinantHypersurface k V).inter
    (Proj.basicOpen (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
      (minorForm k V (leadingIndex k V) (leadingIndex k V))).isOpen.isClosed_compl

omit [IsAlgClosed k] in
/-- The leading-minor locus lies inside the determinant hypersurface. -/
public theorem leadingMinorLocus_subset_determinantHypersurface :
    leadingMinorLocus k V ⊆ determinantHypersurface k V := Set.inter_subset_left

/-- **A closed point lies in the zero locus of a minor form exactly when that minor of any
representative vanishes.** -/
public theorem coe_mem_zeroLocus_minorForm_iff {m : ℕ}
    (s t : Fin m → Fin (Module.finrank k V))
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∉
        Proj.basicOpen (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
          (minorForm k V s t) ↔
      ((LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).submatrix s t).det
        = 0 := by
  rw [Proj.mem_basicOpen, not_not, val_eq_linearFunctionalPoint k V p g hg hpg,
    linearFunctionalPoint_mem,
    SymPow.symAlgMap_eq_zero_iff_lift_eq_zero _ (minorForm_mem_symmetricPower k V s t),
    lift_eval_minorForm]

omit [IsAlgClosed k] in
/-- The rank of the matrix of an endomorphism is the dimension of its range. -/
private theorem rank_toMatrix (g : V →ₗ[k] V) :
    (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).rank =
      Module.finrank k ↥(LinearMap.range g) := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin _ (Module.finBasis k V) (Module.finBasis k V),
    Matrix.toLin_toMatrix]

omit [IsAlgClosed k] in
/-- **A rank drop of at least two kills every minor of size `dim V - 1`.** A nonvanishing minor
of that size would force the rank to be at least `dim V - 1`, because taking a square submatrix
with nonzero determinant produces a submatrix of full rank and submatrices do not gain rank. -/
public theorem det_submatrix_eq_zero_of_finrank_range_add_two_le
    (s t : Fin (Module.finrank k V - 1) → Fin (Module.finrank k V)) (g : V →ₗ[k] V)
    (hg : Module.finrank k ↥(LinearMap.range g) + 2 ≤ Module.finrank k V) :
    ((LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).submatrix s t).det
      = 0 := by
  classical
  by_contra hdet
  have hfull := Matrix.rank_of_det_ne_zero hdet
  have hle := Matrix.rank_submatrix_le
    (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g) s t
  rw [hfull, rank_toMatrix k V g, Fintype.card_fin] at hle
  omega

/-- Every nonzero endomorphism is represented by a closed point. -/
private theorem exists_closedPoint_eq_mk (g : V →ₗ[k] V) (hg : g ≠ 0) :
    ∃ p : ClosedPoints k (Module.Dual k (V →ₗ[k] V)),
      dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg :=
  ⟨_, Equiv.apply_symm_apply _ _⟩

/-- A class represented by an endomorphism of determinant zero lies in the determinant
hypersurface. -/
private theorem coe_mem_determinantHypersurface_of_det_eq_zero
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg)
    (hdet : LinearMap.det g = 0) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈
      determinantHypersurface k V :=
  (mem_determinantHypersurface_iff k V).mpr fun hmem =>
    (coe_mem_invertibleLocus_iff_det_ne_zero k V p g hg hpg).mp hmem hdet

/-- **Every class of endomorphisms whose rank drops by at least two lies in the leading-minor
locus.** -/
public theorem coe_mem_leadingMinorLocus_of_finrank_range_add_two_le
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg)
    (hrank : Module.finrank k ↥(LinearMap.range g) + 2 ≤ Module.finrank k V) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈ leadingMinorLocus k V := by
  have hdet : LinearMap.det g = 0 := by
    classical
    by_contra hne
    have hne' : (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).det ≠ 0 := by
      rwa [LinearMap.det_toMatrix]
    have hfull := Matrix.rank_of_det_ne_zero hne'
    rw [rank_toMatrix k V g, Fintype.card_fin] at hfull
    omega
  refine ⟨coe_mem_determinantHypersurface_of_det_eq_zero k V p g hg hpg hdet, ?_⟩
  exact (coe_mem_zeroLocus_minorForm_iff k V _ _ p g hg hpg).mpr
      (det_submatrix_eq_zero_of_finrank_range_add_two_le k V _ _ g hrank)

/-- The endomorphism fixing all but the last basis vector, which it kills: a singular
endomorphism whose leading minor is `1`. -/
private def rankDropWitness : V →ₗ[k] V :=
  (Module.finBasis k V).constr k fun j =>
    if (j : ℕ) + 1 = Module.finrank k V then 0 else (Module.finBasis k V) j

omit [IsAlgClosed k] in
private theorem toMatrix_rankDropWitness
    (i j : Fin (Module.finrank k V)) :
    LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) (rankDropWitness k V) i j =
      if (j : ℕ) + 1 = Module.finrank k V then 0 else if i = j then 1 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, rankDropWitness, Module.Basis.constr_basis]
  by_cases hj : (j : ℕ) + 1 = Module.finrank k V
  · simp [hj]
  · simp [hj, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

omit [IsAlgClosed k] in
private theorem submatrix_rankDropWitness :
    (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
        (rankDropWitness k V)).submatrix (leadingIndex k V) (leadingIndex k V) = 1 := by
  classical
  ext i j
  rw [Matrix.submatrix_apply, toMatrix_rankDropWitness,
    if_neg (val_leadingIndex_succ_ne k V j), Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos (congrArg (leadingIndex k V) hij), if_pos hij]
  · rw [if_neg (fun h => hij (leadingIndex_injective k V h)), if_neg hij]

omit [IsAlgClosed k] in
private theorem det_rankDropWitness (h2 : 2 ≤ Module.finrank k V) :
    LinearMap.det (rankDropWitness k V) = 0 := by
  classical
  have hlt : Module.finrank k V - 1 < Module.finrank k V := by omega
  obtain ⟨l, hl⟩ : ∃ l : Fin (Module.finrank k V), (l : ℕ) + 1 = Module.finrank k V :=
    ⟨⟨Module.finrank k V - 1, hlt⟩,
      by change Module.finrank k V - 1 + 1 = Module.finrank k V; omega⟩
  rw [← LinearMap.det_toMatrix (Module.finBasis k V)]
  refine Matrix.det_eq_zero_of_column_eq_zero l fun i => ?_
  rw [toMatrix_rankDropWitness, if_pos hl]

omit [IsAlgClosed k] in
private theorem rankDropWitness_ne_zero (h2 : 2 ≤ Module.finrank k V) :
    rankDropWitness k V ≠ 0 := by
  classical
  intro hzero
  have hzlt : 0 < Module.finrank k V := by omega
  obtain ⟨z, hz⟩ : ∃ z : Fin (Module.finrank k V), (z : ℕ) = 0 := ⟨⟨0, hzlt⟩, rfl⟩
  have h : rankDropWitness k V (Module.finBasis k V z) = Module.finBasis k V z := by
    rw [rankDropWitness, Module.Basis.constr_basis, if_neg (by rw [hz]; omega)]
  rw [hzero] at h
  simp only [LinearMap.zero_apply] at h
  exact (Module.finBasis k V).ne_zero z h.symm

/-- **The leading-minor locus is a proper subset of the determinant hypersurface.** The
endomorphism fixing all but the last basis vector is singular, so its class lies in `Z`, but its
leading minor is `1`. -/
public theorem leadingMinorLocus_ne_determinantHypersurface (h2 : 2 ≤ Module.finrank k V) :
    leadingMinorLocus k V ≠ determinantHypersurface k V := by
  set g := rankDropWitness k V with hgdef
  have hg : g ≠ 0 := rankDropWitness_ne_zero k V h2
  obtain ⟨p, hpg⟩ := exists_closedPoint_eq_mk k V g hg
  have hZ := coe_mem_determinantHypersurface_of_det_eq_zero k V p g hg hpg
    (det_rankDropWitness k V h2)
  have hnot : (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∉
      leadingMinorLocus k V := by
    intro hmem
    have hz := (coe_mem_zeroLocus_minorForm_iff k V (leadingIndex k V) (leadingIndex k V)
      p g hg hpg).mp hmem.2
    rw [submatrix_rankDropWitness, Matrix.det_one] at hz
    exact one_ne_zero hz
  intro heq
  exact hnot (heq ▸ hZ)

/-- A strict chain of length two in the poset of irreducible closed subsets bounds the
codimension of its bottom below by two. -/
private theorem two_le_codimension_of_lt_lt {X : Type*} [TopologicalSpace X]
    {A B C : IrreducibleCloseds X} (h₁ : A < B) (h₂ : B < C) :
    (2 : ℕ∞) ≤ codimension A := by
  rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl, codimension_iff_exists_chain]
  have hstep : ∀ i : Fin 2, (![A, B, C] i.castSucc) < (![A, B, C] i.succ) := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
  exact ⟨⟨2, ![A, B, C], hstep⟩, rfl, rfl⟩

/-- An inclusion of irreducible closed subsets which is not an equality of underlying sets is
strict. -/
private theorem irreducibleCloseds_lt_of_subset_of_ne {X : Type*} [TopologicalSpace X]
    {A B : IrreducibleCloseds X} (hsub : (A : Set X) ⊆ (B : Set X))
    (hne : (A : Set X) ≠ (B : Set X)) : A < B :=
  lt_of_le_of_ne (SetLike.coe_subset_coe.mp hsub) fun h => hne (SetLike.coe_set_eq.mpr h)

/-- **Codimension at least two from a strict chain of length two.** If `W ⊆ Z` are closed subsets
of an irreducible space with `W ≠ Z`, `Z` irreducible and `Z` not the whole space, then the
closure of every point of `W` is the bottom of the strict chain `W ⊆ cl{x} < Z < ⊤` in the poset
of irreducible closed subsets, so it has codimension at least two. On a sober space this says
that every irreducible component of `W` has codimension at least two. -/
public theorem two_le_codimension_of_mem_of_isClosed_ssubset {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {W Z : Set T} (hW : IsClosed W) (hZc : IsClosed Z)
    (hZ : IsIrreducible Z) (hWZ : W ⊆ Z) (hWne : W ≠ Z) (hZne : Z ≠ Set.univ)
    {x : T} (hx : x ∈ W) :
    (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  have hxW : closure ({x} : Set T) ⊆ W :=
    hW.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  refine two_le_codimension_of_lt_lt (B := ⟨Z, hZ, hZc⟩)
    (C := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩)
    (irreducibleCloseds_lt_of_subset_of_ne ?_ ?_) (irreducibleCloseds_lt_of_subset_of_ne ?_ ?_)
  · rw [IrreducibleCloseds.coe_closureSingleton]
    exact hxW.trans hWZ
  · rw [IrreducibleCloseds.coe_closureSingleton]
    intro hcar
    have hcar' : closure ({x} : Set T) = Z := hcar
    exact hWne (Set.Subset.antisymm hWZ (by rw [← hcar']; exact hxW))
  · exact Set.subset_univ _
  · exact hZne

/-- **`Z` is not all of `𝐏`:** the class of the identity is invertible. -/
public theorem determinantHypersurface_ne_univ (h2 : 2 ≤ Module.finrank k V) :
    determinantHypersurface k V ≠
      (Set.univ : Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V)))) := by
  have hntV : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hid : (LinearMap.id : V →ₗ[k] V) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h
    exact hv (by simpa using LinearMap.congr_fun h v)
  obtain ⟨p, hpg⟩ := exists_closedPoint_eq_mk k V _ hid
  intro huniv
  have hmem : (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈
      determinantHypersurface k V := huniv ▸ Set.mem_univ _
  exact (mem_determinantHypersurface_iff k V).mp hmem
    ((coe_mem_invertibleLocus_iff_det_ne_zero k V p _ hid hpg).mpr (by simp))

/-- **Every point of the leading-minor locus has codimension at least two in `𝐏`.** Its closure
is contained in the leading-minor locus, which is a proper closed subset of the irreducible
determinant hypersurface `Z`, and `Z` is itself a proper closed subset of `𝐏`; that is a strict
chain of length two. This is the hypothesis shape that the form of Stacks 0B2T for a reducible
closed subset consumes. -/
public theorem two_le_codimension_of_mem_leadingMinorLocus
    (h2 : 2 ≤ Module.finrank k V)
    (x : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V)))
    (hx : x ∈ leadingMinorLocus k V) :
    (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  have hV0 : 0 < Module.finrank k V := by omega
  have : FiniteDimensional k (V →ₗ[k] V) := inferInstance
  have : FiniteDimensional k (Module.Dual k (V →ₗ[k] V)) := inferInstance
  have hnt : Nontrivial (Module.Dual k (V →ₗ[k] V)) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
    exact Nat.mul_pos hV0 hV0
  exact two_le_codimension_of_mem_of_isClosed_ssubset (isClosed_leadingMinorLocus k V)
    (isClosed_determinantHypersurface k V) (isIrreducible_determinantHypersurface k V h2)
    (leadingMinorLocus_subset_determinantHypersurface k V)
    (leadingMinorLocus_ne_determinantHypersurface k V h2)
    (determinantHypersurface_ne_univ k V h2) hx


end AlgebraicGeometry.ProjectiveSpaceOfModule

end
