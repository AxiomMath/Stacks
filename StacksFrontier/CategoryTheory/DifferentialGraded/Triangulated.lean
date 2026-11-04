module

public import Mathlib.CategoryTheory.Triangulated.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.Biproduct

/-!
# The connecting morphism of a graded-split short exact sequence

An admissible short exact sequence `x → y → z` in a differential graded category is split in
the underlying graded category; a chosen splitting `(π, s)` defines the degree-one *connecting
morphism* `π d(s) : z ⟶ x`, which is closed and independent of the splitting up to a boundary.
With a shift functor available on the differential graded category, the connecting morphism
becomes a closed map `z ⟶ x[1]`, and the four objects and three arrows
`x → y → z → x[1]` form a triangle, both in the category of complexes and in the homotopy
category. This file constructs that triangle and proves that each of its consecutive composites,
including the rotated one out of `z[-1]`, vanishes in the homotopy category.

## Main definitions

* `DGCategory.ShiftAxiomB`: shift functors on a differential graded category together with
  compatible identifications of the Hom complexes — axiom (B).
* `DGCategory.DirectSumAxiomA`: a differential graded zero object and differential graded
  binary direct sums — axiom (A).
* `DGCategory.GradedSplitShortExact`: an admissible short exact sequence with a chosen splitting
  in the underlying graded category.
* `DGCategory.GradedSplitShortExact.connectingHom` and
  `DGCategory.GradedSplitShortExact.connectingCocycle`: the connecting morphism before and after
  shifting.
* `DGCategory.GradedSplitShortExact.associatedCompTriangle` and
  `DGCategory.GradedSplitShortExact.associatedKTriangle`: the associated triangles in the
  category of complexes and in the homotopy category.

## Main results

* `DGCategory.GradedSplitShortExact.connectingHom_closed`: the connecting morphism is closed.
* `DGCategory.GradedSplitShortExact.connectingHom_eq_neg_d_comp`: the connecting morphism is
  also `-d(π) s`.
* `DGCategory.GradedSplitShortExact.comp_zero`,
  `DGCategory.GradedSplitShortExact.connectingHom_comp` and
  `DGCategory.GradedSplitShortExact.comp_connectingHom`: the three consecutive composites, the
  last two as explicit boundaries.
* `DGCategory.GradedSplitShortExact.first_comp_zero_in_K`,
  `DGCategory.GradedSplitShortExact.connecting_comp_zero_in_K`,
  `DGCategory.GradedSplitShortExact.comp_connecting_zero_in_K` and
  `DGCategory.GradedSplitShortExact.shifted_connecting_comp_zero_in_K`: all four consecutive
  composites of the triangle vanish in the homotopy category.

## Implementation notes

The splitting is recorded by morphisms `π` and `s` of degree zero satisfying the direct-sum
identities; `π` and `s` are not required to be closed, which is exactly why the connecting
morphism `π d(s)` is not zero. The shift axiom converts it into a cocycle `z ⟶ x[1]` and
supplies coherent shifts on both `Comp(A)` and `K(A)` compatible with the differential graded
shifts, which is what lets the triangle be formed in those two ordinary categories. The
vanishing composites are stated with categorical composition in the homotopy category, the
rotated one out of `z[-1]`.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- Axiom (B): DG shift functors and their compatible identifications of Hom
complexes. The sign in `toShift_d` is the differential of a shifted complex. -/
public structure ShiftAxiomB (A : DGCategory.{v, u} R) where
  /-- The shift functor `x ↦ x[n]` on `A`, for each `n : ℤ`. -/
  shiftFunctor : ℤ → DGCategory.DGFunctor A A
  /-- A shift on the category of complexes `Comp(A)`. -/
  compShift : HasShift A.Comp ℤ
  /-- A shift on the homotopy category `K(A)`. -/
  kShift : HasShift A.K ℤ
  /-- The shift by `n` on `Comp(A)` is the functor induced by `shiftFunctor n`. -/
  compShift_functor : ∀ n : ℤ,
    letI := compShift
    CategoryTheory.shiftFunctor A.Comp n = (shiftFunctor n).onComp
  /-- The shift by `n` on `K(A)` is the functor induced by `shiftFunctor n`. -/
  kShift_functor : ∀ n : ℤ,
    letI := kShift
    CategoryTheory.shiftFunctor A.K n = (shiftFunctor n).onK
  /-- The shift by `0` is the identity on objects. -/
  zero_obj : ∀ x, (shiftFunctor 0).obj x = x
  /-- On objects, the shift by `n + m` is the shift by `m` followed by the shift by `n`. -/
  add_obj : ∀ n m x, (shiftFunctor (n + m)).obj x =
    (shiftFunctor n).obj ((shiftFunctor m).obj x)
  /-- The shift by `0` is the identity on morphisms. -/
  zero_map : ∀ {x y : A.Obj} {k : ℤ} (f : A.Hom x y k),
    HEq ((shiftFunctor 0).map f) f
  /-- On morphisms, the shift by `n + m` is the shift by `m` followed by the shift by `n`. -/
  add_map : ∀ n m {x y : A.Obj} {k : ℤ} (f : A.Hom x y k),
    HEq ((shiftFunctor (n + m)).map f)
      ((shiftFunctor n).map ((shiftFunctor m).map f))
  /-- The identification of `Hom^(k + n)(x, y)` with `Hom^k(x, y[n])`. -/
  toShift : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ),
    A.Hom x y (k + n) ≃ₗ[R] A.Hom x ((shiftFunctor n).obj y) k
  /-- `toShift` intertwines the differentials up to the sign `(-1)^n`. -/
  toShift_d : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ)
    (f : A.Hom x y (k + n)),
    toShift n x y (k + 1) (A.d' (by omega : (k + n) + 1 = (k + 1) + n) f) =
      (-1 : R) ^ n.natAbs • A.d (toShift n x y k f)
  /-- `toShift` commutes with precomposition. -/
  toShift_comp_right : ∀ (n : ℤ) {x y z : A.Obj} {l m : ℤ}
    (g : A.Hom y z (m + n)) (f : A.Hom x y l),
    toShift n x z (m + l)
      (A.comp (by omega : (m + n) + l = (m + l) + n) g f) =
      A.comp (by omega : m + l = m + l) (toShift n y z m g) f
  /-- `toShift` commutes with postcomposition by the shifted morphism, up to the sign
  `(-1)^(n m)`. -/
  toShift_comp_left : ∀ (n : ℤ) {x y z : A.Obj} {l m : ℤ}
    (g : A.Hom y z m) (f : A.Hom x y (l + n)),
    toShift n x z (m + l)
      (A.comp (by omega : m + (l + n) = (m + l) + n) g f) =
      (-1 : R) ^ (n * m).natAbs •
        A.comp (by omega : m + l = m + l) ((shiftFunctor n).map g)
          (toShift n x y l f)

/-- Axiom (A): a DG zero object and DG binary direct sums. -/
public structure DirectSumAxiomA (A : DGCategory.{v, u} R) where
  /-- The zero object. -/
  zero : A.Obj
  /-- Every Hom complex out of `zero` is trivial. -/
  zero_from : ∀ (x : A.Obj) (n : ℤ), Subsingleton (A.Hom zero x n)
  /-- Every Hom complex into `zero` is trivial. -/
  zero_to : ∀ (x : A.Obj) (n : ℤ), Subsingleton (A.Hom x zero n)
  /-- Any two objects have a differential graded binary direct sum. -/
  binaryBiproduct : ∀ x y, Nonempty (BinaryBiproductData A x y)

/-- An admissible short exact sequence with its chosen splitting in the underlying graded
category. The inclusions and projections of the sequence are closed; the splittings need
not be closed. -/
public structure GradedSplitShortExact (x y z : A.Obj) where
  /-- The closed inclusion `x ⟶ y`. -/
  a : A.Cocycle x y
  /-- The closed projection `y ⟶ z`. -/
  b : A.Cocycle y z
  /-- The degree-zero retraction `y ⟶ x` of `a`. -/
  π : A.Hom y x 0
  /-- The degree-zero section `z ⟶ y` of `b`. -/
  s : A.Hom z y 0
  /-- `π a = 1`. -/
  π_a : A.comp (by omega : (0 : ℤ) + 0 = 0) π a.1 = A.id x
  /-- `b s = 1`. -/
  b_s : A.comp (by omega : (0 : ℤ) + 0 = 0) b.1 s = A.id z
  /-- `π s = 0`. -/
  π_s : A.comp (by omega : (0 : ℤ) + 0 = 0) π s = 0
  /-- `a π + s b = 1`. -/
  a_π_add_s_b :
    A.comp (by omega : (0 : ℤ) + 0 = 0) a.1 π +
      A.comp (by omega : (0 : ℤ) + 0 = 0) s b.1 = A.id y

namespace GradedSplitShortExact

/-- The connecting morphism `π d(s)`, as a homogeneous morphism of degree one. -/
@[stacks 09P6 "the connecting morphism"]
public def connectingHom {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    A.Hom z x 1 :=
  A.comp (by omega : (0 : ℤ) + (0 + 1) = 1) E.π (A.d E.s)

private lemma d_pi_comp_a {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.a.1 = 0 := by
  have h := A.leibniz (by omega : (0 : ℤ) + 0 = 0) E.π E.a.1
  rw [E.π_a, A.d_id, E.a.2, A.comp_zero_right, smul_zero, add_zero] at h
  exact h.symm

private lemma b_comp_d_s {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 1 = 1) E.b.1 (A.d E.s) = 0 := by
  have h := A.leibniz (by omega : (0 : ℤ) + 0 = 0) E.b.1 E.s
  rw [E.b_s, A.d_id, E.b.2, A.comp_zero_left] at h
  norm_num at h
  exact h.symm

private lemma pi_comp_d_s_eq_neg_d_pi_comp_s {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 1 = 1) E.π (A.d E.s) =
      -A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.s := by
  have h := A.leibniz (by omega : (0 : ℤ) + 0 = 0) E.π E.s
  rw [E.π_s, A.d_zero] at h
  have h' : A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.s +
      A.comp (by omega : (0 : ℤ) + 1 = 1) E.π (A.d E.s) = 0 := by
    simpa [show (-1 : R) ^ (Int.natAbs 0) = (1 : R) by norm_num,
      one_smul] using h.symm
  exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using h')

/-- Composing with the negative `-g` of the left factor negates the composite. -/
lemma comp_neg_first {x y z : A.Obj} {m n k : ℤ}
    (h : m + n = k) (g : A.Hom y z m) (f : A.Hom x y n) :
    A.comp h (-g) f = -A.comp h g f := by
  rw [show -g = (-1 : R) • g by rw [neg_one_smul],
    A.comp_smul_left, neg_one_smul]

/-- The differential commutes with negation. -/
private lemma d_neg {x y : A.Obj} {n : ℤ} (f : A.Hom x y n) : A.d (-f) = -A.d f := by
  rw [show -f = (-1 : R) • f by rw [neg_one_smul], A.d_smul, neg_one_smul]

private lemma d_s_eq_a_pi_d_s {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d E.s = A.comp (by omega : (0 : ℤ) + 1 = 1)
      (A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 E.π) (A.d E.s) := by
  have h := congrArg (fun q : A.Hom y y 0 =>
    A.comp (by omega : (0 : ℤ) + 1 = 1) q (A.d E.s)) E.a_π_add_s_b
  rw [A.comp_add_left, A.id_comp] at h
  rw [← A.assoc (show (0 : ℤ) + 1 = 1 by omega)
      (show (0 : ℤ) + 1 = 1 by omega) (show (0 : ℤ) + 0 = 0 by omega)
      (show (0 : ℤ) + 1 = 1 by omega) E.a.1 E.π (A.d E.s),
    ← A.assoc (show (0 : ℤ) + 1 = 1 by omega)
      (show (0 : ℤ) + 1 = 1 by omega) (show (0 : ℤ) + 0 = 0 by omega)
      (show (0 : ℤ) + 1 = 1 by omega) E.s E.b.1 (A.d E.s),
    b_comp_d_s E, A.comp_zero_right, add_zero] at h
  exact h.symm.trans (A.assoc (show (0 : ℤ) + 1 = 1 by omega)
    (show (0 : ℤ) + 1 = 1 by omega) (show (0 : ℤ) + 0 = 0 by omega)
    (show (0 : ℤ) + 1 = 1 by omega) E.a.1 E.π (A.d E.s))

private lemma d_pi_eq_d_pi_s_b {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d E.π = A.comp (by omega : (1 : ℤ) + 0 = 1)
      (A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.s) E.b.1 := by
  have h := congrArg (fun q : A.Hom y y 0 =>
    A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) q) E.a_π_add_s_b
  rw [A.comp_add_right, A.comp_id] at h
  rw [A.assoc (show (0 : ℤ) + 0 = 0 by omega)
      (show (1 : ℤ) + 0 = 1 by omega) (show (1 : ℤ) + 0 = 1 by omega)
      (show (1 : ℤ) + 0 = 1 by omega) (A.d E.π) E.a.1 E.π,
    A.assoc (show (0 : ℤ) + 0 = 0 by omega)
      (show (1 : ℤ) + 0 = 1 by omega) (show (1 : ℤ) + 0 = 1 by omega)
      (show (1 : ℤ) + 0 = 1 by omega) (A.d E.π) E.s E.b.1,
    d_pi_comp_a E, A.comp_zero_left, zero_add] at h
  exact h.symm

private lemma d_pi_comp_d_s {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (1 : ℤ) + 1 = 2) (A.d E.π) (A.d E.s) = 0 := by
  rw [d_pi_eq_d_pi_s_b E,
    ← A.assoc (show (0 : ℤ) + 1 = 1 by omega) (show (1 : ℤ) + 1 = 2 by omega)
      (show (1 : ℤ) + 0 = 1 by omega) (show (1 : ℤ) + 1 = 2 by omega)
      (A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.s) E.b.1 (A.d E.s),
    b_comp_d_s E, A.comp_zero_right]

private lemma b_comp_a {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 E.a.1 = 0 := by
  have h := congrArg (fun q : A.Hom y y 0 =>
    A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 q) E.a_π_add_s_b
  rw [A.comp_add_right, A.comp_id] at h
  have hbaπ : A.comp (by omega : (0 : ℤ) + 0 = 0)
      (A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 E.a.1) E.π = 0 := by
    rw [A.assoc (show (0 : ℤ) + 0 = 0 by omega)
        (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
        (show (0 : ℤ) + 0 = 0 by omega)
        E.b.1 E.a.1 E.π,
      A.assoc (show (0 : ℤ) + 0 = 0 by omega)
        (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
        (show (0 : ℤ) + 0 = 0 by omega)
        E.b.1 E.s E.b.1,
      E.b_s, A.id_comp] at h
    have hc : A.comp (by omega : (0 : ℤ) + 0 = 0)
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 E.a.1) E.π + E.b.1 =
        0 + E.b.1 := by simpa using h
    exact add_right_cancel hc
  have hm := congrArg (fun q : A.Hom y z 0 =>
    A.comp (by omega : (0 : ℤ) + 0 = 0) q E.a.1) hbaπ
  rw [← A.assoc (show (0 : ℤ) + 0 = 0 by omega)
      (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + 0 = 0 by omega)
      (show (0 : ℤ) + 0 = 0 by omega)
      (A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 E.a.1) E.π E.a.1,
    E.π_a, A.comp_id] at hm
  simpa using hm

/-- The alternative formula `δ = -d(π)s` for the connecting morphism. -/
@[stacks 09P6 "alternative formula for the connecting morphism"]
public theorem connectingHom_eq_neg_d_comp {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    connectingHom E =
      -A.comp (by omega : (0 + 1 : ℤ) + 0 = 1) (A.d E.π) E.s := by
  simpa only [connectingHom] using (pi_comp_d_s_eq_neg_d_pi_comp_s (A := A) E)

/-- The connecting morphism is a cocycle. -/
@[stacks 09P6 "the connecting morphism is closed"]
public theorem connectingHom_closed {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) : A.d (connectingHom E) = 0 := by
  rw [connectingHom]
  have h := A.leibniz (by omega : (0 : ℤ) + 1 = 1) E.π (A.d E.s)
  rw [A.d_d, A.comp_zero_right, smul_zero, add_zero] at h
  rw [d_pi_comp_d_s E] at h
  exact h

/-- The composite `x ⟶ y ⟶ z` is zero. -/
@[stacks 09P6 "the first consecutive composite"]
public theorem comp_zero {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 E.a.1 = 0 := b_comp_a (A := A) E

private lemma a_comp_connectingHom_eq_d_s {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 1 = 1) E.a.1 (connectingHom E) = A.d E.s := by
  rw [connectingHom]
  calc
    A.comp (by omega : (0 : ℤ) + 1 = 1) E.a.1
        (A.comp (by omega : (0 : ℤ) + 1 = 1) E.π (A.d E.s)) =
      A.comp (by omega : (0 : ℤ) + 1 = 1)
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 E.π)
        (A.d E.s) := A.assoc (show (0 : ℤ) + 1 = 1 by omega)
          (show (0 : ℤ) + 1 = 1 by omega) (show (0 : ℤ) + 0 = 0 by omega)
          (show (0 : ℤ) + 1 = 1 by omega)
          E.a.1 E.π (A.d E.s)
    _ = A.d E.s := (d_s_eq_a_pi_d_s (A := A) E).symm

private lemma connectingHom_comp_b_eq_d_neg_pi {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom E) E.b.1 = A.d (-E.π) := by
  rw [connectingHom]
  calc
    A.comp (by omega : (1 : ℤ) + 0 = 1)
        (A.comp (by omega : (0 : ℤ) + 1 = 1) E.π (A.d E.s)) E.b.1 =
      A.comp (by omega : (1 : ℤ) + 0 = 1)
        (-A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.s) E.b.1 := by
          rw [pi_comp_d_s_eq_neg_d_pi_comp_s (A := A) E]
    _ = -A.comp (by omega : (1 : ℤ) + 0 = 1)
        (A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.s) E.b.1 := by
          exact comp_neg_first (A := A) (by omega : (1 : ℤ) + 0 = 1)
            (A.comp (by omega : (1 : ℤ) + 0 = 1) (A.d E.π) E.s) E.b.1
    _ = -A.d E.π := congrArg Neg.neg (d_pi_eq_d_pi_s_b (A := A) E).symm
    _ = A.d (-E.π) := (d_neg E.π).symm

/-- The composite `z ⟶ x[1] ⟶ y[1]` is the boundary `d(s)` before shifting. -/
@[stacks 09P6 "the third consecutive composite"]
public theorem comp_connectingHom {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 1 = 1) E.a.1 (connectingHom E) = A.d E.s :=
  by exact a_comp_connectingHom_eq_d_s E

/-- The composite `y ⟶ z ⟶ x[1]` is the boundary `d(-π)` before shifting. -/
@[stacks 09P6 "the second consecutive composite"]
public theorem connectingHom_comp {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom E) E.b.1 = A.d (-E.π) :=
  by exact connectingHom_comp_b_eq_d_neg_pi E

/-- The degree-one connecting cocycle remains closed after conversion to a map into
the shifted object. -/
@[stacks 09P6 "closed connecting map into the shift"]
public theorem connecting_shift_closed {x y z : A.Obj}
    (S : ShiftAxiomB A) (E : GradedSplitShortExact (A := A) x y z) :
    A.d ((S.toShift 1 z x 0) (connectingHom E)) = 0 := by
  have h := S.toShift_d 1 z x 0 (connectingHom E)
  have hδ : A.d' (by omega : (1 : ℤ) + 1 = 2) (connectingHom E) = 0 := by
    simpa [DGCategory.d'] using connectingHom_closed (A := A) E
  rw [hδ] at h
  simp only [map_zero] at h
  norm_num at h
  exact h

/-- The actual connecting arrow `z ⟶ x[1]` in `Comp(A)`. -/
@[stacks 09P6 "the triangle's connecting arrow"]
public def connectingCocycle {x y z : A.Obj}
    (S : ShiftAxiomB A) (E : GradedSplitShortExact (A := A) x y z) :
    A.Cocycle z ((S.shiftFunctor 1).obj x) :=
  ⟨(S.toShift 1 z x 0) (connectingHom E), connecting_shift_closed S E⟩

/-- The preceding arrow `z[-1] ⟶ x` is the negative shift of the
connecting arrow. -/
public def shiftedConnecting {x y z : A.Obj}
    (S : ShiftAxiomB A) (E : GradedSplitShortExact (A := A) x y z) :
    A.Cocycle ((S.shiftFunctor (-1)).obj z) x := by
  have hx : (S.shiftFunctor (-1)).obj ((S.shiftFunctor 1).obj x) = x := by
    have h := S.add_obj (-1) 1 x
    simpa only [neg_add_cancel_left] using h.symm.trans (S.zero_obj x)
  exact hx ▸ (S.shiftFunctor (-1)).mapCocycle (connectingCocycle S E)

/-- The associated triangle in the category of complexes, with the arrow
`z ⟶ x[1]` given by `π d(s)`. -/
@[stacks 09P6 "the associated triangle in the category of complexes"]
public def associatedCompTriangle {x y z : A.Obj}
    (S : ShiftAxiomB A) (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.Comp ℤ := S.compShift
    Pretriangulated.Triangle A.Comp := by
  letI : HasShift A.Comp ℤ := S.compShift
  have h : (CategoryTheory.shiftFunctor A.Comp (1 : ℤ)).obj x =
      (S.shiftFunctor (1 : ℤ)).obj x :=
    congrArg (fun F : A.Comp ⥤ A.Comp => F.obj x) (S.compShift_functor 1)
  exact Pretriangulated.Triangle.mk E.a E.b
    (connectingCocycle S E ≫ eqToHom h.symm)

/-- The same triangle, regarded in the homotopy category. -/
@[stacks 09P6 "the associated triangle in the homotopy category"]
public def associatedKTriangle {x y z : A.Obj}
    (S : ShiftAxiomB A) (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := S.kShift
    Pretriangulated.Triangle A.K := by
  letI : HasShift A.K ℤ := S.kShift
  have h : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x =
      (S.shiftFunctor (1 : ℤ)).obj x :=
    congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.kShift_functor 1)
  exact Pretriangulated.Triangle.mk
    (Quotient.mk (A.homotopySetoid x y) E.a)
    (Quotient.mk (A.homotopySetoid y z) E.b)
    ((Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x))
      (connectingCocycle S E)) ≫ eqToHom h.symm)

/-- The first two arrows compose to zero in the homotopy category. -/
@[stacks 09P6 "first composite vanishes in the homotopy category"]
public theorem first_comp_zero_in_K {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.compK (Quotient.mk (A.homotopySetoid y z) E.b)
      (Quotient.mk (A.homotopySetoid x y) E.a) =
    Quotient.mk (A.homotopySetoid x z)
      (⟨0, A.d_zero⟩ : A.Cocycle x z) := by
  show Quotient.mk (A.homotopySetoid x z) (A.compCocycle E.b E.a) = _
  apply congrArg (Quotient.mk (A.homotopySetoid x z))
  apply Subtype.ext
  exact comp_zero E

/-- Shifting a degree-zero morphism `f` after `d` gives `d'` of the negated shift of `f`. -/
private lemma toShift_d_eq_d'_neg (S : ShiftAxiomB A) {x y : A.Obj} (f : A.Hom x y 0) :
    S.toShift 1 x y 0 (A.d f) =
      A.d' (by omega : (-1 : ℤ) + 1 = 0) (-S.toShift 1 x y (-1) f) := by
  have hd := S.toShift_d 1 x y (-1) (show A.Hom x y ((-1 : ℤ) + 1) from f)
  have h : A.d' (by omega : (-1 : ℤ) + 1 = 0) (-S.toShift 1 x y (-1) f) =
      -A.d (S.toShift 1 x y (-1) f) := d_neg _
  rw [h]
  simpa [DGCategory.d'] using hd

/-- The composite `y ⟶ z ⟶ x[1]` is zero in `K(A)`. -/
@[stacks 09P6 "second composite vanishes in the homotopy category"]
public theorem connecting_comp_zero_in_K {x y z : A.Obj}
    (S : ShiftAxiomB A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.compK (Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x))
        (connectingCocycle S E))
      (Quotient.mk (A.homotopySetoid y z) E.b) =
    Quotient.mk (A.homotopySetoid y ((S.shiftFunctor 1).obj x))
      (⟨0, A.d_zero⟩ : A.Cocycle y ((S.shiftFunctor 1).obj x)) := by
  show Quotient.mk (A.homotopySetoid y ((S.shiftFunctor 1).obj x))
      (A.compCocycle (connectingCocycle S E) E.b) = _
  apply Quotient.sound
  refine ⟨-S.toShift 1 y x (-1) (-E.π), ?_⟩
  show A.comp (by omega : (0 : ℤ) + 0 = 0)
      (S.toShift 1 z x 0 (connectingHom E)) E.b.1 - 0 =
    A.d' (by omega : (-1 : ℤ) + 1 = 0)
      (-S.toShift 1 y x (-1) (-E.π))
  simp only [sub_zero]
  have hshift : A.comp (by omega : (0 : ℤ) + 0 = 0)
      (S.toShift 1 z x 0 (connectingHom E)) E.b.1 =
      S.toShift 1 y x 0
        (A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom E) E.b.1) := by
    simpa using
      (S.toShift_comp_right (n := 1) (x := y) (y := z) (z := x)
        (m := 0) (l := 0) (g := connectingHom E) (f := E.b.1)).symm
  rw [hshift, connectingHom_comp]
  exact toShift_d_eq_d'_neg S (-E.π)

/-- The composite `z ⟶ x[1] ⟶ y[1]` is zero in `K(A)`. -/
@[stacks 09P6 "third composite vanishes in the homotopy category"]
public theorem comp_connecting_zero_in_K {x y z : A.Obj}
    (S : ShiftAxiomB A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.compK (Quotient.mk (A.homotopySetoid ((S.shiftFunctor 1).obj x)
        ((S.shiftFunctor 1).obj y)) ((S.shiftFunctor 1).mapCocycle E.a))
      (Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x))
        (connectingCocycle S E)) =
    Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj y))
      (⟨0, A.d_zero⟩ : A.Cocycle z ((S.shiftFunctor 1).obj y)) := by
  show Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj y))
      (A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a) (connectingCocycle S E)) = _
  apply Quotient.sound
  refine ⟨-S.toShift 1 z y (-1) E.s, ?_⟩
  show A.comp (by omega : (0 : ℤ) + 0 = 0)
      ((S.shiftFunctor 1).map E.a.1)
      ((S.toShift 1 z x 0) (connectingHom E)) - 0 =
    A.d' (by omega : (-1 : ℤ) + 1 = 0)
      (-S.toShift 1 z y (-1) E.s)
  simp only [sub_zero]
  have hshift := S.toShift_comp_left 1 (m := 0) (l := 0)
    E.a.1 (connectingHom E)
  have hshift' : S.toShift 1 z y 0
      (A.comp (by omega : (0 : ℤ) + 1 = 1) E.a.1 (connectingHom E)) =
      A.comp (by omega : (0 : ℤ) + 0 = 0)
        ((S.shiftFunctor 1).map E.a.1) ((S.toShift 1 z x 0) (connectingHom E)) := by
    simpa using hshift
  rw [← hshift', comp_connectingHom]
  exact toShift_d_eq_d'_neg S E.s

private lemma shift_neg_one_shift_one_obj (S : ShiftAxiomB A) (x : A.Obj) :
    (S.shiftFunctor (-1)).obj ((S.shiftFunctor 1).obj x) = x := by
  have h := S.add_obj (-1) 1 x
  simpa only [neg_add_cancel_left] using h.symm.trans (S.zero_obj x)

private lemma transport_comp {x' x y' y z : A.Obj} {m n k : ℤ}
    (hx : x' = x) (hy : y' = y) (h : m + n = k)
    (g : A.Hom x' y' m) (f : A.Hom z x' n) :
    hy ▸ A.comp h g f = A.comp h (hy ▸ (hx ▸ g)) (hx ▸ f) := by
  cases hx
  cases hy
  rfl

private lemma transport_d {x y' y : A.Obj} {n : ℤ}
    (hy : y' = y) (f : A.Hom x y' n) :
    hy ▸ A.d f = A.d (hy ▸ f) := by
  cases hy
  rfl

private lemma transport_heq {x' x y' y : A.Obj} {n : ℤ}
    (hx : x' = x) (hy : y' = y) (f : A.Hom x' y' n) :
    HEq (hy ▸ (hx ▸ f)) f := by
  cases hx
  cases hy
  rfl

private lemma transport_cocycle_val {x y' y : A.Obj} (hy : y' = y)
    (f : A.Cocycle x y') : (hy ▸ f).1 = hy ▸ f.1 := by
  cases hy
  rfl

/-- The rotated composite `z[-1] ⟶ x ⟶ y` is zero in `K(A)`. -/
@[stacks 09P6 "rotated composite vanishes in the homotopy category"]
public theorem shifted_connecting_comp_zero_in_K {x y z : A.Obj}
    (S : ShiftAxiomB A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.compK (Quotient.mk (A.homotopySetoid x y) E.a)
      (Quotient.mk (A.homotopySetoid ((S.shiftFunctor (-1)).obj z) x)
        (shiftedConnecting S E)) =
    Quotient.mk (A.homotopySetoid ((S.shiftFunctor (-1)).obj z) y)
      (⟨0, A.d_zero⟩ : A.Cocycle ((S.shiftFunctor (-1)).obj z) y) := by
  let F := S.shiftFunctor (-1)
  let G := S.shiftFunctor 1
  have hx : F.obj (G.obj x) = x := shift_neg_one_shift_one_obj S x
  have hy : F.obj (G.obj y) = y := shift_neg_one_shift_one_obj S y
  show Quotient.mk (A.homotopySetoid (F.obj z) y)
      (A.compCocycle E.a (shiftedConnecting S E)) = _
  apply Quotient.sound
  obtain ⟨t, ht⟩ := Quotient.exact (comp_connecting_zero_in_K S E)
  refine ⟨hy ▸ F.map t, ?_⟩
  show A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1
      (shiftedConnecting S E).1 - 0 =
    A.d' (by omega : (-1 : ℤ) + 1 = 0) (hy ▸ F.map t)
  simp only [sub_zero]
  have hmap : F.map ((A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a)
      (connectingCocycle S E)).1) = A.d' (by omega : (-1 : ℤ) + 1 = 0) (F.map t) := by
    have h := congrArg F.map ht
    simpa [DGCategory.compCocycle, DGCategory.d', sub_eq_add_neg,
      F.map_add, F.map_smul, neg_one_smul, F.map_d] using h
  have hcomp := F.map_comp (by omega : (0 : ℤ) + 0 = 0)
    ((S.shiftFunctor 1).map E.a.1) ((connectingCocycle S E).1)
  have hfirst : hy ▸ (hx ▸ F.map ((S.shiftFunctor 1).map E.a.1)) = E.a.1 := by
    apply eq_of_heq
    have hindex : (-1 : ℤ) + 1 = 0 := by omega
    have hindexMap : HEq ((S.shiftFunctor (-1 + 1)).map E.a.1)
        ((S.shiftFunctor 0).map E.a.1) := by
      cases hindex
      rfl
    have hzero : HEq ((S.shiftFunctor (-1 + 1)).map E.a.1) E.a.1 :=
      hindexMap.trans (S.zero_map E.a.1)
    have hraw : HEq (F.map ((S.shiftFunctor 1).map E.a.1)) E.a.1 :=
      (S.add_map (-1) 1 E.a.1).symm.trans hzero
    exact (transport_heq hx hy (F.map ((S.shiftFunctor 1).map E.a.1))).trans hraw
  have hsecond : (shiftedConnecting S E).1 = hx ▸ F.map (connectingCocycle S E).1 := by
    have heq : shiftedConnecting S E = hx ▸ F.mapCocycle (connectingCocycle S E) := by
      unfold shiftedConnecting
      rfl
    exact (congrArg Subtype.val heq).trans
      (transport_cocycle_val (A := A) hx (F.mapCocycle (connectingCocycle S E)))
  have hmapCast : hy ▸ F.map
      ((A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a)
        (connectingCocycle S E)).1) =
      A.d' (by omega : (-1 : ℤ) + 1 = 0) (hy ▸ F.map t) := by
    have h := congrArg (fun f => hy ▸ f) hmap
    change hy ▸ F.map ((A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a)
      (connectingCocycle S E)).1) = hy ▸ A.d (F.map t) at h
    rw [transport_d (A := A) hy (F.map t)] at h
    show hy ▸ F.map ((A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a)
      (connectingCocycle S E)).1) = A.d' (by omega : (-1 : ℤ) + 1 = 0)
      (hy ▸ F.map t)
    exact h
  have hcomp' : F.map ((A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a)
      (connectingCocycle S E)).1) =
      A.comp (by omega : (0 : ℤ) + 0 = 0)
        (F.map ((S.shiftFunctor 1).map E.a.1))
        (F.map (connectingCocycle S E).1) := by
    show F.map (A.comp (by omega : (0 : ℤ) + 0 = 0)
      ((S.shiftFunctor 1).map E.a.1) (connectingCocycle S E).1) = _
    exact hcomp
  have hcompCast := congrArg (fun f => hy ▸ f) hcomp'
  calc
    A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 (shiftedConnecting S E).1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0)
        (hy ▸ (hx ▸ F.map ((S.shiftFunctor 1).map E.a.1)))
        (hx ▸ F.map (connectingCocycle S E).1) := by
          rw [hfirst, hsecond]
    _ = hy ▸ A.comp (by omega : (0 : ℤ) + 0 = 0)
        (F.map ((S.shiftFunctor 1).map E.a.1))
        (F.map (connectingCocycle S E).1) :=
          (transport_comp (A := A) hx hy (by omega : (0 : ℤ) + 0 = 0)
            (F.map ((S.shiftFunctor 1).map E.a.1))
            (F.map (connectingCocycle S E).1)).symm
    _ = hy ▸ F.map ((A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a)
        (connectingCocycle S E)).1) := by
          exact hcompCast.symm
    _ = A.d' (by omega : (-1 : ℤ) + 1 = 0) (hy ▸ F.map t) := hmapCast

end GradedSplitShortExact

end DGCategory
