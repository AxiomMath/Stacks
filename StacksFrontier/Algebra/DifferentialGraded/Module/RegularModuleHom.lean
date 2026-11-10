module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Maps out of a shift of the regular module in the homotopy category

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, regarded as a right
differential graded module over itself. A homomorphism `A[k] ⟶ N` of right differential graded
`A`-modules is determined by the image of `1`, which is a cocycle of degree `-k` in `N`, and it
is null-homotopic as soon as that cocycle is a coboundary. Consequently, if `N` is acyclic then
every morphism `A[k] ⟶ N` of the homotopy category `K(A, d)` vanishes, that is, every shift of
the regular module lies in the left orthogonal of the acyclic objects.

## Main results

* `DifferentialGradedModule.exists_d_eq_of_acyclic`: in an acyclic differential graded module
  every homogeneous cocycle is a coboundary.
* `DifferentialGradedModule.homotopic_zero_of_acyclic`: a homomorphism from a shift of the
  regular module to an acyclic differential graded module is null-homotopic.
* `DifferentialGradedModule.isZero_hom_toHomotopyCategory_shift_regularModule` and
  `DifferentialGradedModule.leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule`:
  every morphism of `K(A, d)` out of the image of the shifted regular module into an acyclic
  object is zero, and the same statement as membership in the left orthogonal of the acyclic
  objects.
* `DifferentialGradedModule.isZero_hom_shift_regularModule` and
  `DifferentialGradedModule.leftOrthogonal_shift_regularModule`: the same two statements for the
  shift taken in `K(A, d)` rather than in the category of differential graded modules.

## Implementation notes

As everywhere in this chapter's differential graded interface, the base ring, the algebra and the
modules all live in a single universe `u`, following Stacks Tag 09JJ.

The null-homotopy is written down explicitly rather than extracted from the identification of the
graded Hom out of the regular module: if `g : A[k] ⟶ N` sends `1` to `d_N y` with `y` homogeneous
of degree `-k - 1`, then right multiplication by `y` is a homotopy from `g` to `0`. The sign
`(-1)^k` in the differential of the shift `A[k]` cancels against the sign `(-1)^(-k-1)` produced
by the Leibniz rule for `y`, which is why no sign appears in the homotopy itself.

Acyclicity is unfolded to the elementwise statement that a cocycle is a coboundary through
exactness of the three-term complex of `R`-modules in degrees `m`, `m + 1`, `m + 2`; the degrees
are written in that form rather than as `n - 1`, `n`, `n + 1` so that the two differentials are
literally the ones named by `DifferentialGradedModule.toCochainComplex_d`.

The underlying module of the shifted regular module is the algebra itself, but only by
definitional unfolding of `DifferentialGradedModule.shift`, which instance search does not
perform. Every statement about the homotopy is therefore quantified over elements of `A` and
applied to elements of the shift only later, which is what makes the right action elaborate.

## References

* [Stacks Project, Tag 09K1](https://stacks.math.columbia.edu/tag/09K1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGradedModule

/- The underlying cochain complex and its differential are made locally reducible: the exactness
statement extracted from acyclicity is about elements of `M.toCochainComplex.X n`, which is the
homogeneous component `M.grading n` by definition but not reducibly so. -/
attribute [local implicit_reducible] toCochainComplex gradedDifferential

variable {R : Type u} [CommRing R]

/-- The differential of a differential graded algebra kills the unit. -/
theorem algebraDifferential_one (A : DifferentialGradedAlgebra R) :
    A.d (1 : A.A) = 0 := by
  have h1 : (1 : A.A) ∈ A.grading 0 := SetLike.one_mem_graded A.grading
  simpa using A.leibniz 0 0 (1 : A.A) 1 h1 h1

/-- Right multiplication by a fixed element of a right differential graded module, as a map of
right modules out of the algebra. -/
private def rightMulBy {A : DifferentialGradedAlgebra R} {N : DifferentialGradedModule A}
    (y : N.M) : A.A →ₗ[MulOpposite A.A] N.M where
  toFun a := MulOpposite.op a • y
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' c a := by
    change MulOpposite.op (a * c.unop) • y = c • (MulOpposite.op a • y)
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

@[simp] private theorem rightMulBy_apply {A : DifferentialGradedAlgebra R}
    {N : DifferentialGradedModule A} (y : N.M) (a : A.A) :
    rightMulBy y a = MulOpposite.op a • y := rfl

/-- In an acyclic differential graded module every homogeneous cocycle is a coboundary: an
element of degree `m + 1` killed by the differential is the differential of an element of
degree `m`. -/
theorem exists_d_eq_of_acyclic {A : DifferentialGradedAlgebra R}
    {N : DifferentialGradedModule A} (hN : N.toCochainComplex.Acyclic) (m : ℤ)
    (x : N.M) (hx : x ∈ N.grading (m + 1)) (hdx : N.d x = 0) :
    ∃ y ∈ N.grading m, N.d y = x := by
  have hex := hN (m + 1)
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    N.toCochainComplex_d m, N.toCochainComplex_d (m + 1)] at hex
  obtain ⟨w, hw⟩ := hex ⟨x, hx⟩ (Subtype.ext hdx)
  refine ⟨Subtype.val (p := fun z : N.M => z ∈ N.grading m) w, ?_, ?_⟩
  · exact Subtype.property (p := fun z : N.M => z ∈ N.grading m) w
  · exact congrArg Subtype.val hw

/-- A homomorphism from the `k`-th shift of the regular module to an acyclic differential graded
module is null-homotopic: it is right multiplication by its value at `1`, a cocycle of degree
`-k`, and writing that cocycle as a coboundary `d y` makes right multiplication by `y` a
homotopy to zero. -/
theorem homotopic_zero_of_acyclic {A : DifferentialGradedAlgebra R}
    {N : DifferentialGradedModule A} (hN : N.toCochainComplex.Acyclic) (k : ℤ)
    (g : shift (regularModule A) k ⟶ N) : Homotopic g 0 := by
  -- the differential of the shift, on an element of the algebra
  have hdshift : ∀ b : A.A,
      (shift (regularModule A) k).d b = (k.negOnePow : ℤ) • A.d b := fun b => by
    rw [shift_d, LinearMap.smul_apply, Units.smul_def]
  -- `g` is right multiplication by its value at the unit
  have hgmul : ∀ b : A.A, g.toFun b = MulOpposite.op b • g.toFun (1 : A.A) := fun b =>
    (congrArg g.toFun (one_mul b).symm).trans (g.map_smul (1 : A.A) b)
  -- that value is a cocycle of degree `-k`
  have h1 : (1 : A.A) ∈ (shift (regularModule A) k).grading (-k) := by
    simp only [shift_grading, neg_add_cancel]
    exact SetLike.one_mem_graded A.grading
  have hx : g.toFun (1 : A.A) ∈ N.grading (-k) := g.map_grading (-k) (1 : A.A) h1
  have hdx : N.d (g.toFun (1 : A.A)) = 0 := by
    have hmd := LinearMap.congr_fun g.map_d (1 : A.A)
    simp only [LinearMap.comp_apply] at hmd
    rw [hdshift (1 : A.A), algebraDifferential_one, smul_zero, map_zero] at hmd
    exact hmd.symm
  -- acyclicity makes it a coboundary
  obtain ⟨y, hy, hyd⟩ := exists_d_eq_of_acyclic hN (-k - 1) (g.toFun (1 : A.A))
    (by rwa [show -k - 1 + 1 = -k by ring]) hdx
  have hop : ∀ b : A.A, MulOpposite.op ((k.negOnePow : ℤ) • A.d b) • y
      = (k.negOnePow : ℤ) • (MulOpposite.op (A.d b) • y) := fun b => by
    rw [MulOpposite.op_smul, smul_assoc]
  have hlb : ∀ b : A.A, N.d (MulOpposite.op b • y)
      = MulOpposite.op b • N.d y + ((-k - 1).negOnePow : ℤ) • (MulOpposite.op (A.d b) • y) :=
    fun b => leibniz_apply N (-k - 1) y hy b
  have hsign : ((-k - 1).negOnePow : ℤ) + (k.negOnePow : ℤ) = 0 := by
    have hne : (-k - 1).negOnePow = -k.negOnePow := by
      rw [show -k - 1 = -(k + 1) from by ring, Int.negOnePow_neg, Int.negOnePow_add,
        Int.negOnePow_one, mul_neg_one]
    rw [hne]
    simp
  refine ⟨{ toLinearMap := rightMulBy y, map_grading := ?_, homotopy_eq := ?_ }⟩
  · intro n a ha
    have ha' : a ∈ A.grading (n + k) := ha
    have hmem := N.smul_mem (-k - 1) (n + k) y a hy ha'
    rwa [show -k - 1 + (n + k) = n - 1 by ring] at hmem
  · -- the homotopy equation, stated on elements of the algebra
    have key : ∀ b : A.A, g.toFun b - (0 : shift (regularModule A) k ⟶ N).toFun b
        = N.d (rightMulBy y b) + rightMulBy y ((shift (regularModule A) k).d b) := fun b => by
      rw [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero, hdshift b]
      simp only [rightMulBy_apply]
      rw [hop b, hlb b, hyd, add_assoc, ← add_smul, hsign, zero_smul, add_zero]
      exact hgmul b
    exact key

/-- Every morphism of the homotopy category from the image of a shift of the regular module to
an acyclic object is zero. -/
@[stacks 09K1 "vanishing of the homotopy classes"]
theorem isZero_hom_toHomotopyCategory_shift_regularModule (A : DifferentialGradedAlgebra R)
    (k : ℤ) {N : HomotopyCategory A} (hN : acyclic' A N) :
    ∀ f : (toHomotopyCategory A).obj (shift (regularModule A) k) ⟶ N, f = 0 := by
  obtain ⟨N'⟩ := N
  intro f
  induction f using Quot.inductionOn with
  | _ g =>
    change (toHomotopyCategory A).map g = 0
    exact (CategoryTheory.Quotient.sound (homotopyRel A) (homotopic_zero_of_acyclic hN k g)).trans
      ((toHomotopyCategory A).map_zero _ _)

/-- The image of a shift of the regular module lies in the left orthogonal of the acyclic
objects of the homotopy category. -/
@[stacks 09K1 "left orthogonality of the shifted regular module"]
theorem leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule
    (A : DifferentialGradedAlgebra R) (k : ℤ) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (shift (regularModule A) k)) :=
  fun _ f hN => isZero_hom_toHomotopyCategory_shift_regularModule A k hN f

/-- Every morphism of the homotopy category from the `k`-th shift, taken in `K(A, d)`, of the
regular module to an acyclic object is zero. -/
@[stacks 09K1]
theorem isZero_hom_shift_regularModule (A : DifferentialGradedAlgebra R) (k : ℤ)
    {N : HomotopyCategory A} (hN : acyclic' A N) :
    ∀ f : ((toHomotopyCategory A).obj (regularModule A))⟦k⟧ ⟶ N, f = 0 := by
  have hshift : (((toHomotopyCategory A).obj (regularModule A))⟦k⟧) =
      (toHomotopyCategory A).obj (shift (regularModule A) k) :=
    CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ (regularModule A) k
  intro f
  refine (cancel_epi (eqToHom hshift.symm)).mp ?_
  rw [comp_zero]
  exact isZero_hom_toHomotopyCategory_shift_regularModule A k hN _

/-- The `k`-th shift, taken in `K(A, d)`, of the regular module lies in the left orthogonal of
the acyclic objects. -/
@[stacks 09K1 "left orthogonality, with the shift taken in the homotopy category"]
theorem leftOrthogonal_shift_regularModule (A : DifferentialGradedAlgebra R) (k : ℤ) :
    (acyclic' A).leftOrthogonal (((toHomotopyCategory A).obj (regularModule A))⟦k⟧) :=
  fun _ f hN => isZero_hom_shift_regularModule A k hN f

end DifferentialGradedModule
