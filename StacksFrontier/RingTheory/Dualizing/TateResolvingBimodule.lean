module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomLeftOrthogonal
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExhaustiveCellFiltration
public import StacksFrontier.RingTheory.Dualizing.TateDifferentialGradedResolution

/-!
# The resolving bimodule of a free nonnegatively graded resolution computes derived Hom

Let `(E, d)` be a differential graded `R`-algebra and let `E` be its resolving differential
graded `(E, R)`-bimodule, whose underlying right module over `R` placed in degree zero is the
complex `E^•`. Hypothesis (2) of [Stacks, Tag 0BZ0] for that bimodule — that the internal hom
`Hom^•_R(E^•, R)` computes `R Hom(E^•, R)`, recorded as `Dualizing.ComputesDerivedHom` — holds as
soon as `E^•` is orthogonal on the left to the acyclic complexes, by Tag 0BYW.

That orthogonality holds when `E^•` is bounded above and free in every degree, which is the case
for the algebra underlying a Tate resolution: it is graded by `ℕ` placed in nonpositive
cohomological degrees, and each homogeneous piece is free over `R`. A choice of basis in each
degree exhibits `E^•` as an unbounded triangular cell complex over `R` placed in degree zero, and
`DifferentialGradedModule.leftOrthogonal_acyclic_of_exhaustiveCellCoords` applies.

## Main definitions

* `DividedPowers.TateResolution.gradeCoords`: the coordinates of an element of a nonnegatively
  graded module with free homogeneous pieces, against a chosen basis in each degree.

## Main results

* `Dualizing.leftOrthogonal_acyclic_resolvingBimodule`: coordinates on `E^•` of the shape an
  unbounded triangular cell decomposition asks for make `E^•` orthogonal on the left to the
  acyclic modules.
* `Dualizing.computesDerivedHom_of_leftOrthogonal`: **Tag 0BYW for the resolving bimodule**,
  that this orthogonality gives `Dualizing.ComputesDerivedHom`.
* `DividedPowers.TateResolution.computesDerivedHom_resolvingBimodule_regraded`: the resolving
  bimodule of a nonnegatively graded algebra with free homogeneous pieces, read cohomologically,
  computes derived Hom.
* `DividedPowers.TateResolution.Resolution.computesDerivedHom_resolvingBimodule`: the same for a
  Tate resolution, whose homogeneous pieces are free by its `free` field.

## Implementation notes

The hypotheses of `Dualizing.leftOrthogonal_acyclic_resolvingBimodule` are phrased in terms of
`E` and the chosen coordinates alone, not in terms of the bimodule's underlying module: the
underlying module is a restriction of scalars of the regular module, so a statement about its
right action or its grading has to be converted before it can be proved, and doing that once
inside the proof keeps it out of every statement.

A shift of `R` placed in degree zero is `R` itself placed in the corresponding degree, and the
differential of `R` placed in degree zero is zero, so the two conditions that
`DifferentialGradedModule.leftOrthogonal_acyclic_of_exhaustiveCellCoords` imposes on the
differential both reduce to the vanishing of coordinates: the differential of an element
supported in homological degrees `< k` is supported in homological degrees `< k - 1`.

## References

* [Stacks Project, Tag 0BYW](https://stacks.math.columbia.edu/tag/0BYW), that ordinary Hom out
  of a module with property (P) computes derived Hom.
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P).
* [Stacks Project, Tag 0BZ0](https://stacks.math.columbia.edu/tag/0BZ0), of whose hypothesis (2)
  `Dualizing.ComputesDerivedHom` is the statement.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule
open scoped DirectSum

universe u

/-! ### Orthogonality of the resolving bimodule from coordinates -/

namespace Dualizing

variable {R : Type u} [CommRing R]

/-- **The right action of a scalar is the action of the base ring.** On a differential graded
module the right action of the image of `r : R` in the algebra is the `R`-module structure, which
is the compatibility that `DifferentialGradedModule` records as a scalar tower. -/
theorem op_smul_eq_smul {A : DifferentialGradedAlgebra.{u, u} R}
    (M : DifferentialGradedModule A) {a : A.A} {r : R} (ha : a = algebraMap R A.A r) (x : M.M) :
    MulOpposite.op a • x = r • x := by
  subst ha
  rw [show MulOpposite.op (algebraMap R A.A r) = algebraMap R A.Aᵐᵒᵖ r from rfl,
    IsScalarTower.algebraMap_smul A.Aᵐᵒᵖ r x]

variable (E : DifferentialGradedAlgebra.{u, u} R)

/-- **Coordinates make the resolving bimodule orthogonal on the left to the acyclic modules.**
Suppose the algebra `E` has, in each homological degree `m` — that is, in cohomological degree
`-m` — a basis indexed by `I m`, in such a way that an element is homogeneous of cohomological
degree `n` exactly when its coordinates vanish outside homological degree `-n`, and that the
differential of an element supported in homological degrees `< k` is supported in homological
degrees `< k - 1`. Then `E^•`, the underlying right module over `R` placed in degree zero, is
orthogonal on the left to the acyclic modules.

This is `DifferentialGradedModule.leftOrthogonal_acyclic_of_exhaustiveCellCoords` for the
coordinates given: a shift of `R` placed in degree zero is again `R` placed in a single degree,
and its differential vanishes, so the two triangularity conditions there both say that the
coordinates of a differential vanish in high degrees. -/
theorem leftOrthogonal_acyclic_resolvingBimodule {I : ℕ → Type u}
    (coords : E.A ≃ₗ[R] ⨁ (m : ℕ), (⨁ (_ : I m), R))
    (hgrading : ∀ (n : ℤ) (x : E.A), x ∈ E.grading n ↔ ∀ m : ℕ, n + (m : ℤ) ≠ 0 → coords x m = 0)
    (hd : ∀ (k : ℕ) (x : E.A), (∀ m : ℕ, k ≤ m → coords x m = 0) →
      ∀ m : ℕ, k ≤ m + 1 → coords (E.d x) m = 0) :
    (acyclic' (baseAlgebra R)).leftOrthogonal
      ((toHomotopyCategory (baseAlgebra R)).obj (resolvingBimodule E).rightModule) := by
  refine leftOrthogonal_acyclic_of_exhaustiveCellCoords (A := baseAlgebra R)
    (M := (resolvingBimodule E).rightModule) (I := I) (fun m _ => (m : ℤ)) coords ?_ ?_ ?_ ?_
  · intro a x m
    have key : ∀ (y : E.A) (b : R), coords (b • y) m = MulOpposite.op b • coords y m := by
      intro y b
      rw [map_smul]
      refine DirectSum.ext fun i => ?_
      change b • (((coords y) m) i) = ((coords y) m) i * b
      rw [smul_eq_mul, mul_comm]
    rw [op_smul_eq_smul (resolvingBimodule E).rightModule (a := a) (r := a) rfl x]
    exact key x a
  · intro n x
    refine (hgrading n x).trans ?_
    refine ⟨fun h m i => ?_, fun h m hn => ?_⟩
    · by_cases hn : n + (m : ℤ) = 0
      · rw [hn]
        change ((coords x) m) i ∈ DifferentialGradedAlgebra.degreeZeroGrading R R 0
        rw [DifferentialGradedAlgebra.degreeZeroGrading_zero]
        exact Submodule.mem_top
      · change ((coords x) m) i ∈ DifferentialGradedAlgebra.degreeZeroGrading R R (n + (m : ℤ))
        rw [DifferentialGradedAlgebra.degreeZeroGrading_eq_bot R R hn, Submodule.mem_bot, h m hn]
        rfl
    · refine DirectSum.ext fun i => ?_
      have hi : ((coords x) m) i ∈
          DifferentialGradedAlgebra.degreeZeroGrading R R (n + (m : ℤ)) := h m i
      rw [DifferentialGradedAlgebra.degreeZeroGrading_eq_bot R R hn, Submodule.mem_bot] at hi
      rw [hi]
      rfl
  · exact fun k x hx m hm => hd k x hx m (by omega)
  · intro k x hx i
    exact show ((coords (E.d x)) k) i = ((-1 : ℤ) ^ (k : ℤ).natAbs) • (0 : R) by
      rw [hd (k + 1) x hx k (by omega), DirectSum.zero_apply, smul_zero]

/-- **Tag 0BYW for the resolving bimodule.** If `E^•` is orthogonal on the left to the acyclic
modules then the internal hom `Hom^•_R(E^•, R)` computes `R Hom(E^•, R)`, which is hypothesis (2)
of [Stacks, Tag 0BZ0] for the resolving bimodule.

Orthogonality on the left makes the localization bijective on the morphisms out of `E^•`
(`DifferentialGradedModule.bijective_q_map_of_leftOrthogonal`), which is the hypothesis of
`DifferentialGradedModule.DerivedHomData.isIso_comparison_of_bijective_q_map`. -/
theorem computesDerivedHom_of_leftOrthogonal
    (h : (acyclic' (baseAlgebra R)).leftOrthogonal
      ((toHomotopyCategory (baseAlgebra R)).obj (resolvingBimodule E).rightModule)) :
    ComputesDerivedHom (resolvingBimodule E) := by
  have := DerivedHomData.isIso_comparison_of_bijective_q_map E (baseAlgebra R)
    (resolvingBimodule E).rightModule (resolvingBimodule E).leftAction
    (derivedHomData E (baseAlgebra R) (resolvingBimodule E).rightModule
      (resolvingBimodule E).leftAction)
    (fun P => bijective_q_map_of_leftOrthogonal h P)
  exact NatIso.isIso_app_of_isIso _ _

end Dualizing

/-! ### Coordinates on a nonnegatively graded module with free homogeneous pieces -/

namespace DividedPowers.TateResolution

section Coords

variable {R : Type u} [CommRing R] {A : Type u} [AddCommGroup A] [Module R A]
  (𝒜 : ℕ → Submodule R A) [DirectSum.Decomposition 𝒜]

omit [DirectSum.Decomposition 𝒜] in
/-- An element is homogeneous of degree `p` exactly when all its other components vanish. -/
theorem mem_grade_iff_forall_decompose_eq_zero [DirectSum.Decomposition 𝒜] (x : A) (p : ℕ) :
    x ∈ 𝒜 p ↔ ∀ m : ℕ, m ≠ p → ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) = 0 := by
  refine ⟨fun hx m hm => DirectSum.decompose_of_mem_ne 𝒜 hx (Ne.symm hm), fun h => ?_⟩
  have hdec : DirectSum.decompose 𝒜 x =
      DirectSum.of (fun i => 𝒜 i) p (DirectSum.decompose 𝒜 x p) := by
    refine DirectSum.ext fun m => ?_
    rcases eq_or_ne m p with rfl | hm
    · rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hm]
      exact Subtype.ext (h m hm)
  have hx := congrArg (DirectSum.decompose 𝒜).symm hdec
  rw [Equiv.symm_apply_apply, DirectSum.decompose_symm_of] at hx
  rw [hx]
  exact (DirectSum.decompose 𝒜 x p).2

/-- An element vanishes exactly when all its homogeneous components do. -/
theorem eq_zero_iff_forall_decompose_eq_zero (x : A) :
    x = 0 ↔ ∀ m : ℕ, ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) = 0 := by
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl m
    simp
  · classical
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    exact Finset.sum_eq_zero fun m _ => h m

variable [∀ n, Module.Free R (𝒜 n)]

/-- The index set of the chosen basis of the homogeneous piece of degree `n`. -/
abbrev gradeBasisIndex (n : ℕ) : Type u := Module.Free.ChooseBasisIndex R (𝒜 n)

/-- The homogeneous piece of degree `n`, in the coordinates of its chosen basis. -/
def gradeCoordEquiv (n : ℕ) : 𝒜 n ≃ₗ[R] (⨁ (_ : gradeBasisIndex 𝒜 n), R) :=
  letI := Classical.decEq (gradeBasisIndex 𝒜 n)
  (Module.Free.chooseBasis R (𝒜 n)).repr.trans
    (finsuppLEquivDirectSum R R (gradeBasisIndex 𝒜 n))

/-- **The graded coordinates of a nonnegatively graded module with free homogeneous pieces.**
Decompose into homogeneous pieces, then take the coordinates of each piece against its chosen
basis. -/
def gradeCoords : A ≃ₗ[R] ⨁ (m : ℕ), (⨁ (_ : gradeBasisIndex 𝒜 m), R) :=
  (DirectSum.decomposeLinearEquiv 𝒜).trans
    (DFinsupp.mapRange.linearEquiv (gradeCoordEquiv 𝒜))

/-- The coordinate block of degree `m` of `x` is the coordinate vector of the degree-`m`
homogeneous component of `x`. -/
theorem gradeCoords_apply (x : A) (m : ℕ) :
    gradeCoords 𝒜 x m = gradeCoordEquiv 𝒜 m (DirectSum.decompose 𝒜 x m) := rfl

/-- A coordinate block vanishes exactly when the corresponding homogeneous component does. -/
theorem gradeCoords_eq_zero_iff (x : A) (m : ℕ) :
    gradeCoords 𝒜 x m = 0 ↔ ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) = 0 := by
  rw [gradeCoords_apply, LinearEquiv.map_eq_zero_iff, Submodule.coe_eq_zero]

end Coords

/-! ### The cohomological grading, read in coordinates -/

section Cohomological

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [DirectSum.Decomposition 𝒜]

/-- **Membership in a cohomological degree, read on the homogeneous components.** An element is
homogeneous of cohomological degree `n` exactly when its component of homological degree `m`
vanishes whenever `n + m ≠ 0`; in positive cohomological degree that forces the element to
vanish. -/
theorem mem_cohomologicalGrade_iff_forall_decompose_eq_zero (n : ℤ) (x : A) :
    x ∈ cohomologicalGrade 𝒜 n ↔
      ∀ m : ℕ, n + (m : ℤ) ≠ 0 → ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) = 0 := by
  rcases lt_or_ge 0 n with hn | hn
  · rw [cohomologicalGrade_of_pos 𝒜 hn, Submodule.mem_bot,
      eq_zero_iff_forall_decompose_eq_zero 𝒜 x]
    exact ⟨fun h m _ => h m, fun h m => h m (by omega)⟩
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [cohomologicalGrade_neg_natCast, mem_grade_iff_forall_decompose_eq_zero 𝒜 x p]
    exact ⟨fun h m hm => h m (by omega), fun h m hm => h m (by omega)⟩

end Cohomological

/-! ### The differential lowers the degree -/

section Differential

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d]

/-- The differential of a homogeneous element of degree `j` has no component in any degree
`≥ j`: it is homogeneous of degree `j - 1`, and it vanishes when `j = 0`. -/
theorem decompose_d_eq_zero_of_mem {j m : ℕ} {x : A} (hx : x ∈ 𝒜 j) (hjm : j ≤ m) :
    ((DirectSum.decompose 𝒜 (d x) m : 𝒜 m) : A) = 0 := by
  cases j with
  | zero =>
      rw [IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) hx]
      simp
  | succ n =>
      exact DirectSum.decompose_of_mem_ne 𝒜
        (IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d) hx) (by omega)

/-- The homogeneous component of a given degree, as an additive map. -/
private def gradeComponent (m : ℕ) : A →+ A :=
  ((𝒜 m).subtype.toAddMonoidHom).comp
    ((DFinsupp.evalAddMonoidHom (β := fun i => 𝒜 i) m).comp
      (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom)

private theorem gradeComponent_apply (m : ℕ) (x : A) :
    gradeComponent 𝒜 m x = ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) := rfl

/-- **The differential of an element supported in degrees below `k` is supported in degrees
below `k - 1`.** -/
theorem decompose_d_eq_zero {k : ℕ} {x : A}
    (hx : ∀ m : ℕ, k ≤ m → ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) = 0)
    {m : ℕ} (hm : k ≤ m + 1) : ((DirectSum.decompose 𝒜 (d x) m : 𝒜 m) : A) = 0 := by
  classical
  have hdx : d x = ∑ j ∈ (DirectSum.decompose 𝒜 x).support,
      d ((DirectSum.decompose 𝒜 x j : 𝒜 j) : A) := by
    rw [← map_sum, DirectSum.sum_support_decompose 𝒜 x]
  rw [← gradeComponent_apply 𝒜 m, hdx, map_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : j < k := by
    by_contra hc
    exact (DFinsupp.mem_support_iff.mp hj) (Subtype.ext (hx j (by omega)))
  rw [gradeComponent_apply]
  exact decompose_d_eq_zero_of_mem 𝒜 d (DirectSum.decompose 𝒜 x j).2 (by omega)

end Differential

/-! ### The resolving bimodule of a free nonnegatively graded algebra -/

section Regraded

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [∀ n, Module.Free R (𝒜 n)] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d]

/-- **The resolving bimodule of a free nonnegatively graded algebra computes derived Hom.** The
graded coordinates of `DividedPowers.TateResolution.gradeCoords` exhibit the algebra, read
cohomologically, as an unbounded triangular cell complex over `R` placed in degree zero, so it is
orthogonal on the left to the acyclic modules and Tag 0BYW applies. -/
theorem computesDerivedHom_resolvingBimodule_regraded :
    Dualizing.ComputesDerivedHom
      (Dualizing.resolvingBimodule (regradedDifferentialGradedAlgebra 𝒜 d)) := by
  refine Dualizing.computesDerivedHom_of_leftOrthogonal _
    (Dualizing.leftOrthogonal_acyclic_resolvingBimodule _ (gradeCoords 𝒜) ?_ ?_)
  · intro n x
    exact (mem_cohomologicalGrade_iff_forall_decompose_eq_zero 𝒜 n x).trans
      (forall₂_congr fun m _ => (gradeCoords_eq_zero_iff 𝒜 x m).symm)
  · intro k x hx m hm
    exact (gradeCoords_eq_zero_iff 𝒜 _ m).mpr (decompose_d_eq_zero 𝒜 d (k := k)
      (fun j hj => (gradeCoords_eq_zero_iff 𝒜 x j).mp (hx j hj)) hm)

end Regraded

/-! ### A Tate resolution -/

namespace Resolution

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

section General

variable {σ : Type u} {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ)

/-- **The resolving bimodule of a Tate resolution computes derived Hom.** The homogeneous pieces
of a Tate resolution are free over the base ring, which is its `free` field. -/
theorem computesDerivedHom_resolvingBimodule :
    Dualizing.ComputesDerivedHom (Dualizing.resolvingBimodule T.regradedAlgebra) :=
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  let : GradedAlgebra T.grade := T.graded
  let : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  let : ∀ n, Module.Free R (T.grade n) := T.free
  computesDerivedHom_resolvingBimodule_regraded T.grade T.differential

end General

section Finite

variable {k : ℕ} {φ : MvPolynomial (Fin k) R →ₐ[R] S} (T : Resolution R S (Fin k) φ)

/-- **The resolving bimodule of a Tate resolution along a presentation by finitely many
variables computes derived Hom.** -/
theorem computesDerivedHom_resolvingBimoduleFin :
    Dualizing.ComputesDerivedHom (Dualizing.resolvingBimodule (toDGAResolutionFin T).E) :=
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  let : GradedAlgebra T.grade := T.graded
  let : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  let : ∀ n, Module.Free R (T.grade n) := T.free
  computesDerivedHom_resolvingBimodule_regraded T.grade T.differential

end Finite

end Resolution

end DividedPowers.TateResolution

end
