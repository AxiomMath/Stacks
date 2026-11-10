module

public import Mathlib.CategoryTheory.Triangulated.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.AdmissibleMonoFactorization
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeHomotopyEquivalence

/-!
# Cones and the triangles of admissible sequences in the homotopy category

An admissible short exact sequence of a differential graded category identifies its quotient, up
to homotopy, with the cone of its first arrow, and that identification carries its associated
triangle to the cone triangle. The same comparison applies to any factorization of a closed
degree-zero arrow through an admissible monomorphism.

## Main definitions

* `DGCategory.negativeConeTriangle`: the cone triangle with the negative of the sequence's
  projection as its third arrow.

## Main results

* `DGCategory.coneTriangleIsoOfShortExact`: the comparison of a cone triangle with the triangle
  of an admissible short exact sequence.
* `DGCategory.shortExactTriangleIsoOfFactorization`: the comparison of the triangle of an
  admissible-monomorphism factorization with the cone triangle of the factored arrow.

## Implementation notes

An admissible factorization is given through its graded-split sequence together with a strict
section and a homotopy inverse on the target. Both comparisons are morphisms of triangles which
are the identity, resp. the factorization's comparison map, on the first two vertices and an
isomorphism on the third.

## References

* [Stacks Project, Tag 09QU](https://stacks.math.columbia.edu/tag/09QU)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe u v w

open CategoryTheory

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- The cone triangle with its third arrow negated, for a shift additive on objects only up to
isomorphism. -/
public def ConeSituationIso.negativeConeTriangle (S : ConeSituationIso A)
    {x y : A.Obj} (f : A.Cocycle x y) :
    letI : HasShift A.K ℤ := S.shift.kShift
    Pretriangulated.Triangle A.K := by
  letI : HasShift A.K ℤ := S.shift.kShift
  let E := S.coneSequence f
  have h : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x =
      (S.shift.shiftFunctor (1 : ℤ)).obj x :=
    congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.shift.kShift_functor 1)
  have hc : A.d (-E.b.1) = 0 := by
    rw [show -E.b.1 = (-1 : R) • E.b.1 by rw [neg_one_smul], A.d_smul,
      E.b.2, smul_zero]
  exact Pretriangulated.Triangle.mk
    (Quotient.mk (A.homotopySetoid x y) f)
    (Quotient.mk (A.homotopySetoid y (S.cone f)) E.a)
    ((Quotient.mk (A.homotopySetoid (S.cone f) ((S.shift.shiftFunctor 1).obj x))
      (⟨-E.b.1, hc⟩ : A.Cocycle (S.cone f) ((S.shift.shiftFunctor 1).obj x))) ≫
      eqToHom h.symm)

/-- The triangle of a cone with the negative projection as connecting arrow. -/
public def negativeConeTriangle (S : ConeSituation A)
    {x y : A.Obj} (f : A.Cocycle x y) :
    letI : HasShift A.K ℤ := S.shift.kShift
    Pretriangulated.Triangle A.K :=
  S.toConeSituationIso.negativeConeTriangle f

private lemma toShift_connectingHom_cone {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) y 0
      (GradedSplitShortExact.connectingHom (S.coneSequence E.a)) =
      (S.shift.shiftFunctor 1).map E.a.1 := by
  simpa [ShiftAxiomBIso.connectingCocycle, DGCategory.DGFunctor.mapCocycle] using
    congrArg Subtype.val (S.cone_connecting E.a)

/-- The first projection of a graded-split sequence kills the differential of its section. -/
private lemma b_comp_d_section {x y z : A.Obj} (D : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 1 = 1) D.b.1 (A.d D.s) = 0 := by
  simpa [D.b_s, A.d_id, D.b.2, A.comp_zero_left, pow_zero, one_smul] using
    (A.leibniz (by lia : (0 : ℤ) + 0 = 0) D.b.1 D.s).symm

private lemma coneConnecting_comp {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (1 : ℤ) + 0 = 1)
      (GradedSplitShortExact.connectingHom (S.coneSequence E.a))
      (S.shift.connectingCocycle E).1 = A.d E.s := by
  let G := S.shift.shiftFunctor 1
  let D := S.coneSequence E.a
  have hconn := toShift_connectingHom_cone S E
  apply (S.shift.toShift 1 z y 0).injective
  calc
    S.shift.toShift 1 z y 0
        (A.comp (by lia : (1 : ℤ) + 0 = 1)
          (GradedSplitShortExact.connectingHom D)
          (S.shift.connectingCocycle E).1) =
        A.comp (by lia : (0 : ℤ) + 0 = 0)
          (S.shift.toShift 1 (G.obj x) y 0 (GradedSplitShortExact.connectingHom D))
          (S.shift.connectingCocycle E).1 := by
      simpa using (S.shift.toShift_comp_right (n := 1) (m := 0) (l := 0)
        (g := GradedSplitShortExact.connectingHom D)
        (f := (S.shift.connectingCocycle E).1))
    _ = A.comp (by lia : (0 : ℤ) + 0 = 0) (G.map E.a.1)
          (S.shift.connectingCocycle E).1 := by rw [hconn]
    _ = S.shift.toShift 1 z y 0
          (A.comp (by lia : (0 : ℤ) + 1 = 1) E.a.1
            (GradedSplitShortExact.connectingHom E)) := by
      symm
      simpa [ShiftAxiomBIso.connectingCocycle] using
        (S.shift.toShift_comp_left (n := 1) (m := 0) (l := 0)
          (g := E.a.1) (f := GradedSplitShortExact.connectingHom E))
    _ = S.shift.toShift 1 z y 0 (A.d E.s) := by
      rw [GradedSplitShortExact.comp_connectingHom]

private lemma split_kill_by_precomp {x y z w : A.Obj} {n : ℤ}
    (D : GradedSplitShortExact (A := A) x y z)
    (q : A.Hom y w n)
    (hq₁ : A.comp (by omega : n + 0 = n) q D.a.1 = 0)
    (hq₂ : A.comp (by omega : n + 0 = n) q D.s = 0) : q = 0 := by
  have h := congrArg (fun t : A.Hom y y 0 =>
    A.comp (by lia : n + 0 = n) q t) D.a_π_add_s_b
  rw [A.comp_add_right, A.comp_id] at h
  rw [A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : n + 0 = n)
        (by lia : n + 0 = n) (by lia : n + 0 = n) q D.a.1 D.π,
      A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : n + 0 = n)
        (by lia : n + 0 = n) (by lia : n + 0 = n) q D.s D.b.1,
      hq₁, hq₂,
      A.comp_zero_left, A.comp_zero_left] at h
  simpa using h.symm

private lemma split_kill_by_postcomp {x y z w : A.Obj} {n : ℤ}
    (D : GradedSplitShortExact (A := A) x y z)
    (q : A.Hom w y n)
    (hq₁ : A.comp (by omega : (0 : ℤ) + n = n) D.π q = 0)
    (hq₂ : A.comp (by omega : (0 : ℤ) + n = n) D.b.1 q = 0) : q = 0 := by
  have h := congrArg (fun t : A.Hom y y 0 =>
    A.comp (by lia : (0 : ℤ) + n = n) t q) D.a_π_add_s_b
  rw [A.comp_add_left, A.id_comp] at h
  rw [← A.assoc (by lia : (0 : ℤ) + n = n) (by lia : (0 : ℤ) + n = n)
        (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + n = n) D.a.1 D.π q,
      ← A.assoc (by lia : (0 : ℤ) + n = n) (by lia : (0 : ℤ) + n = n)
        (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + n = n) D.s D.b.1 q,
      hq₁, hq₂,
      A.comp_zero_right, A.comp_zero_right] at h
  simpa using h.symm

private lemma d_neg {x y : A.Obj} {n : ℤ} (f : A.Hom x y n) : A.d (-f) = -A.d f := by
  rw [show -f = (-1 : R) • f by rw [neg_one_smul], A.d_smul, neg_one_smul]

/-- A cocycle whose composites with a cocycle in the other direction are homotopic to the
identities is an isomorphism in the homotopy category. -/
private lemma isIso_mk_of_homotopic_inverse {x y : A.Obj} (e : A.Cocycle x y)
    (f : A.Cocycle y x) (h₁ : A.Homotopic (A.compCocycle f e) ⟨A.id x, A.d_id x⟩)
    (h₂ : A.Homotopic (A.compCocycle e f) ⟨A.id y, A.d_id y⟩) :
    @CategoryTheory.IsIso (A.K) (DGCategory.instCategoryK A) x y (Quotient.mk _ e) :=
  ⟨⟨Quotient.mk _ f, Quotient.sound h₁, Quotient.sound h₂⟩⟩

private def cocycleNeg {x y : A.Obj} (f : A.Cocycle x y) : A.Cocycle x y :=
  ⟨-f.1, by rw [d_neg, f.2, neg_zero]⟩

private lemma homotopic_neg {x y : A.Obj} {f g : A.Cocycle x y}
    (h : A.Homotopic f g) : A.Homotopic (cocycleNeg f) (cocycleNeg g) := by
  obtain ⟨H, hH⟩ := h
  refine ⟨-H, ?_⟩
  change -f.1 - (-g.1) = A.d (-H)
  rw [d_neg]
  change f.1 - g.1 = A.d H at hH
  rw [← hH]
  abel

private lemma cone_projection_closed {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1
      (S.coneSequence E.a).π) = 0 := by
  let D := S.coneSequence E.a
  let t := GradedSplitShortExact.connectingHom D
  have hdπa : A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d D.π) D.a.1 = 0 := by
    have h := A.leibniz (by lia : (0 : ℤ) + 0 = 0) D.π D.a.1
    rw [D.π_a, A.d_id, D.a.2, A.comp_zero_right, smul_zero, add_zero] at h
    exact h.symm
  have hdπs : A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d D.π) D.s = -t := by
    have h := A.leibniz (by lia : (0 : ℤ) + 0 = 0) D.π D.s
    rw [D.π_s, A.d_zero] at h
    exact eq_neg_iff_add_eq_zero.mpr
      (by simpa [t, GradedSplitShortExact.connectingHom, pow_zero, one_smul] using h.symm)
  have hbt : A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 t = 0 := by
    apply (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) z 0).injective
    have hconn := toShift_connectingHom_cone S E
    calc
      S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) z 0
          (A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 t) =
        A.comp (by lia : (0 : ℤ) + 0 = 0) ((S.shift.shiftFunctor 1).map E.b.1)
            (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) y 0 t) := by
        simpa using (S.shift.toShift_comp_left (n := 1) (m := 0) (l := 0)
          (g := E.b.1) (f := t))
      _ = S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) z 0 0 := by
        rw [hconn, ← (S.shift.shiftFunctor 1).map_comp, GradedSplitShortExact.comp_zero,
          DGCategory.DGFunctor.map_zero]
        exact (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) z 0).map_zero.symm
  have hq₁ : A.comp (by lia : (1 : ℤ) + 0 = 1)
      (A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 (A.d D.π)) D.a.1 = 0 := by
    rw [← A.assoc (by lia : (1 : ℤ) + 0 = 1) (by lia : (0 : ℤ) + 1 = 1)
        (by lia : (0 : ℤ) + 1 = 1) (by lia : (1 : ℤ) + 0 = 1)
        E.b.1 (A.d D.π) D.a.1, hdπa, A.comp_zero_right]
  have hq₂ : A.comp (by lia : (1 : ℤ) + 0 = 1)
      (A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 (A.d D.π)) D.s = 0 := by
    rw [← A.assoc (by lia : (1 : ℤ) + 0 = 1) (by lia : (0 : ℤ) + 1 = 1)
        (by lia : (0 : ℤ) + 1 = 1) (by lia : (1 : ℤ) + 0 = 1)
        E.b.1 (A.d D.π) D.s, hdπs]
    rw [comp_neg_right, hbt, neg_zero]
  have hzero := split_kill_by_precomp D
    (A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 (A.d D.π)) hq₁ hq₂
  calc
    A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π) =
        A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 (A.d D.π) := by
      simp [A.leibniz, E.b.2, pow_zero, one_smul, A.comp_zero_left]
    _ = 0 := hzero

private lemma cone_retraction_lift_closed {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d (A.comp (by omega : (0 : ℤ) + 0 = 0)
        (S.coneSequence E.a).a.1 E.s -
      A.comp (by omega : (0 : ℤ) + 0 = 0) (S.coneSequence E.a).s
        (S.shift.connectingCocycle E).1) = 0 := by
  let D := S.coneSequence E.a
  let δ := S.shift.connectingCocycle E
  let t := GradedSplitShortExact.connectingHom D
  have hd₁ : A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s) =
      A.comp (by lia : (0 : ℤ) + 1 = 1) D.a.1 (A.d E.s) := by
    simpa [D.a.2, pow_zero, one_smul, A.comp_zero_left, add_zero] using
      A.leibniz (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s
  have hd₂ : A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1) =
      A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d D.s) δ.1 := by
    simpa [δ.2, pow_zero, one_smul, A.comp_zero_right, add_zero] using
      A.leibniz (by lia : (0 : ℤ) + 0 = 0) D.s δ.1
  have hdiff : A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s -
      A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1) =
      A.comp (by lia : (0 : ℤ) + 1 = 1) D.a.1 (A.d E.s) -
        A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d D.s) δ.1 := by
    rw [sub_eq_add_neg, A.d_add, d_neg, hd₁, hd₂, ← sub_eq_add_neg]
  have hπ : A.comp (by lia : (0 : ℤ) + 1 = 1) D.π
      (A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s -
        A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1)) = 0 := by
    rw [hdiff, A.comp_sub_right]
    have hleft : A.comp (by lia : (0 : ℤ) + 1 = 1) D.π
        (A.comp (by lia : (0 : ℤ) + 1 = 1) D.a.1 (A.d E.s)) = A.d E.s := by
      rw [A.assoc (by lia : (0 : ℤ) + 1 = 1) (by lia : (0 : ℤ) + 1 = 1)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 1 = 1)
          D.π D.a.1 (A.d E.s), D.π_a, A.id_comp]
    have hright : A.comp (by lia : (0 : ℤ) + 1 = 1) D.π
        (A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d D.s) δ.1) =
        A.comp (by lia : (1 : ℤ) + 0 = 1) t δ.1 := by
      rw [A.assoc (by lia : (1 : ℤ) + 0 = 1) (by lia : (0 : ℤ) + 1 = 1)
          (by lia : (0 : ℤ) + 1 = 1) (by lia : (1 : ℤ) + 0 = 1)
          D.π (A.d D.s) δ.1]
      rfl
    rw [hleft, hright, coneConnecting_comp, sub_self]
  have hb : A.comp (by lia : (0 : ℤ) + 1 = 1) D.b.1
      (A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s -
        A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1)) = 0 := by
    rw [hdiff, A.comp_sub_right]
    have hleft : A.comp (by lia : (0 : ℤ) + 1 = 1) D.b.1
        (A.comp (by lia : (0 : ℤ) + 1 = 1) D.a.1 (A.d E.s)) = 0 := by
      rw [A.assoc (by lia : (0 : ℤ) + 1 = 1) (by lia : (0 : ℤ) + 1 = 1)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 1 = 1)
          D.b.1 D.a.1 (A.d E.s), GradedSplitShortExact.comp_zero, A.comp_zero_left]
    have hright : A.comp (by lia : (0 : ℤ) + 1 = 1) D.b.1
        (A.comp (by lia : (1 : ℤ) + 0 = 1) (A.d D.s) δ.1) = 0 := by
      rw [A.assoc (by lia : (1 : ℤ) + 0 = 1) (by lia : (0 : ℤ) + 1 = 1)
          (by lia : (0 : ℤ) + 1 = 1) (by lia : (1 : ℤ) + 0 = 1)
          D.b.1 (A.d D.s) δ.1, b_comp_d_section, A.comp_zero_left]
    rw [hleft, hright, sub_self]
  exact split_kill_by_postcomp D _ hπ hb

private def coneProjectionAux {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.Hom (S.cone E.a) ((S.shift.shiftFunctor 1).obj x) (-1) :=
  S.shift.toShift 1 (S.cone E.a) x (-1)
    (A.comp (by omega : (0 : ℤ) + 0 = 0) E.π (S.coneSequence E.a).π)

private lemma cone_d_section_comp {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (1 : ℤ) + (-1) = 0)
        (A.d (S.coneSequence E.a).s) (coneProjectionAux S E) =
      A.comp (by omega : (0 : ℤ) + 0 = 0) (S.coneSequence E.a).a.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1
          (A.comp (by omega : (0 : ℤ) + 0 = 0) E.π
            (S.coneSequence E.a).π)) := by
  let D := S.coneSequence E.a
  let p := coneProjectionAux S E
  let t := GradedSplitShortExact.connectingHom D
  have hconn := toShift_connectingHom_cone S E
  have hπ : A.comp (by lia : (0 : ℤ) + 0 = 0)
      D.π (A.comp (by lia : (1 : ℤ) + (-1) = 0) (A.d D.s) p) =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) := by
    apply (S.shift.toShift 1 (S.cone E.a) y (-1)).injective
    have hleft := S.shift.toShift_comp_right (n := 1) (m := 0) (l := -1)
      (g := GradedSplitShortExact.connectingHom D) (f := p)
    have hright := S.shift.toShift_comp_left (n := 1) (m := 0) (l := -1)
      (g := E.a.1) (f := A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π)
    calc
      S.shift.toShift 1 (S.cone E.a) y (-1)
          (A.comp (by lia : (0 : ℤ) + 0 = 0) D.π
            (A.comp (by lia : (1 : ℤ) + (-1) = 0) (A.d D.s) p)) =
          A.comp (by lia : (0 : ℤ) + (-1) = -1)
            (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) y 0
              (GradedSplitShortExact.connectingHom D)) p := by
            rw [A.assoc (by lia : (1 : ℤ) + (-1) = 0)
              (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 1 = 1)
              (by lia : (1 : ℤ) + (-1) = 0) D.π (A.d D.s) p]
            simpa [t, GradedSplitShortExact.connectingHom] using hleft
      _ = A.comp (by lia : (0 : ℤ) + (-1) = -1)
            ((S.shift.shiftFunctor 1).map E.a.1) p := by rw [hconn]
      _ = S.shift.toShift 1 (S.cone E.a) y (-1)
            (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
              (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π)) := by
            simpa [p, coneProjectionAux] using hright.symm
  have hb : A.comp (by lia : (0 : ℤ) + 0 = 0) D.b.1
      (A.comp (by lia : (1 : ℤ) + (-1) = 0) (A.d D.s) p) = 0 := by
    rw [A.assoc (by lia : (1 : ℤ) + (-1) = 0) (by lia : (0 : ℤ) + 0 = 0)
        (by lia : (0 : ℤ) + 1 = 1) (by lia : (1 : ℤ) + (-1) = 0)
        D.b.1 (A.d D.s) p]
    rw [b_comp_d_section, A.comp_zero_left]
  have hleftRhs : A.comp (by lia : (0 : ℤ) + 0 = 0) D.b.1
      (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π))) = 0 := by
    rw [A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
        (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
        D.b.1 D.a.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π)),
      GradedSplitShortExact.comp_zero, A.comp_zero_left]
  have hπRhs : A.comp (by lia : (0 : ℤ) + 0 = 0) D.π
      (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π))) =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) := by
    rw [A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
        (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
        D.π D.a.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π)),
      D.π_a, A.id_comp]
  exact sub_eq_zero.mp (split_kill_by_postcomp D
    (A.comp (by lia : (1 : ℤ) + (-1) = 0) (A.d D.s) p -
      A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π)))
    (by rw [A.comp_sub_right, hπ, hπRhs, sub_self])
    (by rw [A.comp_sub_right, hb, hleftRhs, sub_self]))

private lemma coneProjectionAux_d_inclusion {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (0 : ℤ) + 0 = 0)
        (A.d' (by omega : (-1 : ℤ) + 1 = 0) (coneProjectionAux S E))
        (S.coneSequence E.a).a.1 =
      A.comp (by omega : (0 : ℤ) + 0 = 0)
        (S.shift.connectingCocycle E).1 E.b.1 := by
  let D := S.coneSequence E.a
  let p := coneProjectionAux S E
  let G := S.shift.shiftFunctor 1
  let δ := S.shift.connectingCocycle E
  let t := GradedSplitShortExact.connectingHom D
  have hpA : A.comp (by lia : (-1 : ℤ) + 0 = -1) p D.a.1 =
      S.shift.toShift 1 y x (-1) E.π := by
    have h := S.shift.toShift_comp_right (n := 1) (m := -1) (l := 0)
      (g := A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) (f := D.a.1)
    calc
      A.comp (by lia : (-1 : ℤ) + 0 = -1) p D.a.1 =
          S.shift.toShift 1 y x (-1)
            (A.comp (by lia : (0 : ℤ) + 0 = 0)
              (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) D.a.1) := by
                simpa [p, coneProjectionAux, D] using h.symm
      _ = S.shift.toShift 1 y x (-1) E.π := by
        congr 1
        rw [← A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          E.π D.π D.a.1, D.π_a, A.comp_id]
  have hdEπ : A.d E.π = -A.comp (by lia : (1 : ℤ) + 0 = 1)
      (GradedSplitShortExact.connectingHom E) E.b.1 := by
    have h := GradedSplitShortExact.connectingHom_comp E
    rw [d_neg] at h
    rw [h, neg_neg]
  have hshiftD : A.d (S.shift.toShift 1 y x (-1) E.π) =
      -S.shift.toShift 1 y x 0 (A.d E.π) := by
    have h := S.shift.toShift_d 1 y x (-1)
      (show A.Hom y x ((-1 : ℤ) + 1) from by simpa using E.π)
    simpa [DGCategory.d', Int.natAbs] using
      (congrArg (fun v => -v) h).symm
  have htoShiftComp : S.shift.toShift 1 y x 0
      (A.comp (by lia : (1 : ℤ) + 0 = 1)
        (GradedSplitShortExact.connectingHom E) E.b.1) =
      A.comp (by lia : (0 : ℤ) + 0 = 0)
        (S.shift.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E)) E.b.1 := by
    simpa [ShiftAxiomBIso.connectingCocycle] using
      (S.shift.toShift_comp_right (n := 1) (m := 0) (l := 0)
        (g := GradedSplitShortExact.connectingHom E) (f := E.b.1))
  have hderiv : A.d (A.comp (by lia : (-1 : ℤ) + 0 = -1) p D.a.1) =
      A.comp (by lia : (0 : ℤ) + 0 = 0) (A.d p) D.a.1 := by
    simpa [D.a.2, pow_one, neg_one_smul, A.comp_zero_right, add_zero] using
      A.leibniz (by lia : (-1 : ℤ) + 0 = -1) p D.a.1
  calc
    A.comp (by lia : (0 : ℤ) + 0 = 0) (A.d p) D.a.1 =
        A.d (A.comp (by lia : (-1 : ℤ) + 0 = -1) p D.a.1) := hderiv.symm
    _ = A.d (S.shift.toShift 1 y x (-1) E.π) := by rw [hpA]
    _ = -S.shift.toShift 1 y x 0 (A.d E.π) := hshiftD
    _ = S.shift.toShift 1 y x 0
        (A.comp (by lia : (1 : ℤ) + 0 = 1)
          (GradedSplitShortExact.connectingHom E) E.b.1) := by rw [hdEπ, map_neg, neg_neg]
    _ = A.comp (by lia : (0 : ℤ) + 0 = 0)
        (S.shift.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E)) E.b.1 := htoShiftComp
    _ = A.comp (by lia : (0 : ℤ) + 0 = 0) δ.1 E.b.1 := rfl

private lemma coneProjectionAux_comp_section {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.comp (by omega : (-1 : ℤ) + 1 = 0) (coneProjectionAux S E)
      (A.d (S.coneSequence E.a).s) = A.id ((S.shift.shiftFunctor 1).obj x) := by
  let D := S.coneSequence E.a
  let G := S.shift.shiftFunctor 1
  let t := GradedSplitShortExact.connectingHom D
  have hconn := toShift_connectingHom_cone S E
  have hcomp := S.shift.toShift_comp_right (n := 1) (m := -1) (l := 1)
    (g := A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) (f := A.d D.s)
  calc
    A.comp (by lia : (-1 : ℤ) + 1 = 0) (coneProjectionAux S E) (A.d D.s) =
        S.shift.toShift 1 (G.obj x) x 0
          (A.comp (by lia : (0 : ℤ) + 1 = 1)
            (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) (A.d D.s)) := by
              simpa [coneProjectionAux, D, G] using hcomp.symm
    _ = S.shift.toShift 1 (G.obj x) x 0
          (A.comp (by lia : (0 : ℤ) + 1 = 1) E.π t) := by
              congr 1
              rw [← A.assoc (by lia : (0 : ℤ) + 1 = 1)
                (by lia : (0 : ℤ) + 1 = 1) (by lia : (0 : ℤ) + 0 = 0)
                (by lia : (0 : ℤ) + 1 = 1) E.π D.π (A.d D.s)]
              rfl
    _ = A.comp (by lia : (0 : ℤ) + 0 = 0)
          (G.map E.π) (S.shift.toShift 1 (G.obj x) y 0 t) := by
              simpa using (S.shift.toShift_comp_left (n := 1) (m := 0) (l := 0)
                (g := E.π) (f := t))
    _ = A.comp (by lia : (0 : ℤ) + 0 = 0) (G.map E.π) (G.map E.a.1) := by
              rw [hconn]
    _ = A.id (G.obj x) := by
              rw [← G.map_comp, E.π_a, G.map_id]

private lemma coneProjectionAux_d {x y z : A.Obj}
    (S : ConeSituationIso A)
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d' (by omega : (-1 : ℤ) + 1 = 0) (coneProjectionAux S E) =
      (S.coneSequence E.a).b.1 +
        A.comp (by omega : (0 : ℤ) + 0 = 0)
          (S.shift.connectingCocycle E).1
          (A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 (S.coneSequence E.a).π) := by
  let D := S.coneSequence E.a
  let δ := S.shift.connectingCocycle E
  let p := coneProjectionAux S E
  let dp : A.Hom (S.cone E.a) ((S.shift.shiftFunctor 1).obj x) 0 :=
    A.d' (by lia : (-1 : ℤ) + 1 = 0) p
  have hqa : A.comp (by lia : (0 : ℤ) + 0 = 0)
      (dp - (D.b.1 + A.comp (by lia : (0 : ℤ) + 0 = 0)
        δ.1 (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π))) D.a.1 = 0 := by
    rw [A.comp_sub_left, A.comp_add_left, coneProjectionAux_d_inclusion]
    have hba : A.comp (by lia : (0 : ℤ) + 0 = 0) D.b.1 D.a.1 = 0 :=
      GradedSplitShortExact.comp_zero D
    have hcomp : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) δ.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π)) D.a.1 =
        A.comp (by lia : (0 : ℤ) + 0 = 0) δ.1 E.b.1 := by
      rw [← A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          δ.1 (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π) D.a.1,
        ← A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          E.b.1 D.π D.a.1,
        D.π_a, A.comp_id]
    simp only [hcomp, hba, zero_add]
    exact sub_self _
  have hps : A.comp (by lia : (-1 : ℤ) + 0 = -1) p D.s = 0 := by
    have h := S.shift.toShift_comp_right (n := 1) (m := -1) (l := 0)
      (g := A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) (f := D.s)
    calc
      A.comp (by lia : (-1 : ℤ) + 0 = -1) p D.s =
          S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) x (-1)
            (A.comp (by lia : (0 : ℤ) + 0 = 0)
              (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π) D.s) := by
                simpa [p, coneProjectionAux, D] using h.symm
      _ = 0 := by
        rw [← A.assoc (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) E.π D.π D.s,
          D.π_s, A.comp_zero_right]
        exact (S.shift.toShift 1 ((S.shift.shiftFunctor 1).obj x) x (-1)).map_zero
  have hdpS : A.comp (by lia : (0 : ℤ) + 0 = 0) dp D.s =
      A.id ((S.shift.shiftFunctor 1).obj x) := by
    have hlib' : A.d (A.comp (by lia : (-1 : ℤ) + 0 = -1) p D.s) =
        A.comp (by lia : (0 : ℤ) + 0 = 0) dp D.s -
          A.comp (by lia : (-1 : ℤ) + 1 = 0) p (A.d D.s) := by
      simpa [DGCategory.d', dp, pow_one, neg_one_smul, sub_eq_add_neg] using
        A.leibniz (by lia : (-1 : ℤ) + 0 = -1) p D.s
    rw [hps, A.d_zero, coneProjectionAux_comp_section] at hlib'
    exact sub_eq_zero.mp (by simpa using hlib'.symm)
  have hqs : A.comp (by lia : (0 : ℤ) + 0 = 0)
      (dp - (D.b.1 + A.comp (by lia : (0 : ℤ) + 0 = 0)
        δ.1 (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π))) D.s = 0 := by
    rw [A.comp_sub_left, A.comp_add_left, hdpS]
    have hbs : A.comp (by lia : (0 : ℤ) + 0 = 0) D.b.1 D.s =
        A.id ((S.shift.shiftFunctor 1).obj x) := D.b_s
    have hδ : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) δ.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π)) D.s = 0 := by
      rw [← A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          δ.1 (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π) D.s,
        ← A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          E.b.1 D.π D.s,
        D.π_s, A.comp_zero_right, A.comp_zero_right]
    rw [hbs, hδ]
    simp
  simpa [dp] using sub_eq_zero.mp (split_kill_by_precomp D _ hqa hqs)

/-- For a shift additive on objects up to isomorphism, an admissible short exact sequence
identifies its quotient with the cone of its first arrow, compatibly with the two triangles and
the identity on their first two terms. -/
public theorem ConeSituationIso.coneTriangleIsoOfShortExact (S : ConeSituationIso A)
    {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := S.shift.kShift
    ∃ φ : S.negativeConeTriangle E.a ⟶ S.shift.associatedKTriangle E,
      φ.hom₁ = 𝟙 _ ∧ φ.hom₂ = 𝟙 _ ∧ IsIso φ.hom₃ := by
  let _ : HasShift A.K ℤ := S.shift.kShift
  let D := S.coneSequence E.a
  let δ := S.shift.connectingCocycle E
  let e : A.Cocycle (S.cone E.a) z :=
    ⟨A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π,
      cone_projection_closed S E⟩
  let f : A.Cocycle z (S.cone E.a) :=
    ⟨A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s -
        A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1,
      cone_retraction_lift_closed S E⟩
  have hef : A.comp (by lia : (0 : ℤ) + 0 = 0) e.1 f.1 = A.id z := by
    change A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s -
          A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1) = A.id z
    rw [A.comp_sub_right]
    have h₁ : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s) = A.id z := by
      rw [A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π) D.a.1 E.s,
        ← A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          E.b.1 D.π D.a.1,
        D.π_a, A.comp_id, E.b_s]
    have h₂ : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1) = 0 := by
      rw [A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π) D.s δ.1,
        ← A.assoc (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
          E.b.1 D.π D.s,
        D.π_s, A.comp_zero_right, A.comp_zero_left]
    rw [h₁, h₂, sub_zero]
  let p := coneProjectionAux S E
  let H : A.Hom (S.cone E.a) (S.cone E.a) (-1) :=
    A.comp (by lia : (0 : ℤ) + (-1) = -1) D.s p
  let dp : A.Hom (S.cone E.a) ((S.shift.shiftFunctor 1).obj x) 0 :=
    A.d' (by lia : (-1 : ℤ) + 1 = 0) p
  let t₁ := A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
    (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E.π D.π))
  let t₂ := A.comp (by lia : (0 : ℤ) + 0 = 0)
    (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s)
    (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π)
  let t₃ := A.comp (by lia : (0 : ℤ) + 0 = 0) D.s D.b.1
  let t₄ := A.comp (by lia : (0 : ℤ) + 0 = 0) D.s
    (A.comp (by lia : (0 : ℤ) + 0 = 0) δ.1
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π))
  have hmid : A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 D.π = t₁ + t₂ := by
    calc
      A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 D.π =
          A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
            (A.comp (by lia : (0 : ℤ) + 0 = 0) (A.id y) D.π) := by rw [A.id_comp]
      _ = A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
            (A.comp (by lia : (0 : ℤ) + 0 = 0)
              (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1 E.π +
                A.comp (by lia : (0 : ℤ) + 0 = 0) E.s E.b.1) D.π) := by
            rw [← E.a_π_add_s_b]
      _ = A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
            (A.comp (by lia : (0 : ℤ) + 0 = 0)
              (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1 E.π) D.π) +
          A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1
            (A.comp (by lia : (0 : ℤ) + 0 = 0)
              (A.comp (by lia : (0 : ℤ) + 0 = 0) E.s E.b.1) D.π) := by
            rw [A.comp_add_left, A.comp_add_right]
      _ = t₁ + t₂ := by simp [t₁, t₂, A.assoc]
  have hH : A.d' (by lia : (-1 : ℤ) + 1 = 0) H = t₁ + t₃ + t₄ := by
    have hlib' : A.d' (by lia : (-1 : ℤ) + 1 = 0) H =
        A.comp (by lia : (1 : ℤ) + (-1) = 0) (A.d D.s) p +
          A.comp (by lia : (0 : ℤ) + 0 = 0) D.s dp := by
      simpa [DGCategory.d', H, dp, pow_zero, one_smul] using
        A.leibniz (by lia : (0 : ℤ) + (-1) = -1) D.s p
    rw [hlib', cone_d_section_comp,
      show dp = A.d' (by lia : (-1 : ℤ) + 1 = 0) (coneProjectionAux S E) by rfl,
      coneProjectionAux_d, A.comp_add_right]
    simp only [t₁, t₃, t₄]
    abel
  have hfe : A.comp (by lia : (0 : ℤ) + 0 = 0) f.1 e.1 = t₂ - t₄ := by
    change A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) D.a.1 E.s -
          A.comp (by lia : (0 : ℤ) + 0 = 0) D.s δ.1)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π) = _
    rw [A.comp_sub_left]
    simp [t₂, t₄, A.assoc]
  have hid : A.id (S.cone E.a) = A.comp (by lia : (0 : ℤ) + 0 = 0) f.1 e.1 +
      A.d' (by lia : (-1 : ℤ) + 1 = 0) H := by
    rw [← D.a_π_add_s_b, hmid, hfe, hH]
    simp only [t₁, t₂, t₃, t₄]
    abel
  have hfe_homotopic : A.Homotopic (A.compCocycle f e)
      (⟨A.id (S.cone E.a), A.d_id (S.cone E.a)⟩ : A.Cocycle (S.cone E.a) (S.cone E.a)) := by
    refine ⟨-H, ?_⟩
    change A.comp (by lia : (0 : ℤ) + 0 = 0) f.1 e.1 - A.id (S.cone E.a) = A.d (-H)
    rw [d_neg, hid]
    change _ = -A.d H
    abel
  let eK : A.HomotopyClass (S.cone E.a) z := Quotient.mk _ e
  have heiso : @CategoryTheory.IsIso (A.K) (DGCategory.instCategoryK A)
      (S.cone E.a) z eK :=
    isIso_mk_of_homotopic_inverse e f hfe_homotopic
      (by rw [show A.compCocycle e f = ⟨A.id z, A.d_id z⟩ from Subtype.ext hef]
          exact A.homotopic_refl _)
  let φ : S.negativeConeTriangle E.a ⟶ S.shift.associatedKTriangle E :=
    Pretriangulated.Triangle.homMk _ _ (𝟙 _) (𝟙 _) eK (by
      dsimp [negativeConeTriangle, ShiftAxiomBIso.associatedKTriangle]
      simp
      rfl) (by
        dsimp [negativeConeTriangle, ShiftAxiomBIso.associatedKTriangle]
        rw [CategoryTheory.Category.id_comp]
        change A.compK eK (Quotient.mk _ D.a) =
          Quotient.mk _ E.b
        change Quotient.mk _ (A.compCocycle e D.a) = _
        apply congrArg (Quotient.mk _)
        apply Subtype.ext
        change A.comp (by lia : (0 : ℤ) + 0 = 0) e.1 D.a.1 = E.b.1
        rw [show e.1 = A.comp (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π by rfl,
          ← A.assoc (by lia : (0 : ℤ) + 0 = 0)
            (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
            (by lia : (0 : ℤ) + 0 = 0) E.b.1 D.π D.a.1,
          D.π_a, A.comp_id]) (by
        let nb := cocycleNeg D.b
        have hhom : A.Homotopic (A.compCocycle δ e) nb := by
          refine ⟨p, ?_⟩
          change A.comp (by lia : (0 : ℤ) + 0 = 0) δ.1 e.1 - (-D.b.1) =
            A.d' (by lia : (-1 : ℤ) + 1 = 0) p
          rw [coneProjectionAux_d]
          simp only [e]
          rw [A.assoc (by lia : (0 : ℤ) + 0 = 0)
            (by lia : (0 : ℤ) + 0 = 0) (by lia : (0 : ℤ) + 0 = 0)
            (by lia : (0 : ℤ) + 0 = 0) δ.1 E.b.1 D.π]
          abel
        have hraw : Quotient.mk _ nb = A.compK (Quotient.mk _ δ) eK :=
          Quotient.sound (A.homotopic_symm hhom)
        dsimp [negativeConeTriangle, ShiftAxiomBIso.associatedKTriangle]
        have hshift : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x =
            (S.shift.shiftFunctor (1 : ℤ)).obj x :=
          congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.shift.kShift_functor 1)
        change (Quotient.mk _ nb ≫ eqToHom hshift.symm) ≫
            (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map
              (@CategoryTheory.CategoryStruct.id (A.K) _ x) =
          eK ≫ (Quotient.mk _ δ ≫ eqToHom hshift.symm)
        have hmap : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map
              (@CategoryTheory.CategoryStruct.id (A.K) _ x) =
            @CategoryTheory.CategoryStruct.id (A.K) _
              ((CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x) :=
          (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map_id x
        rw [hmap]
        refine Eq.trans (CategoryTheory.Category.comp_id _) ?_
        rw [hraw]
        simpa [CategoryStruct.comp, DGCategory.instCategoryK] using
          (CategoryTheory.Category.assoc eK (Quotient.mk _ δ)
            (eqToHom hshift.symm)))
  exact ⟨φ, rfl, rfl, heiso⟩

/-- An admissible short exact sequence identifies its quotient with the cone of its
first arrow, compatibly with the two triangles and the identity on their first two terms. -/
@[stacks 09QU "part (1)", sga "4 XVII 1.1.1" "DG category setting"]
public theorem coneTriangleIsoOfShortExact (S : ConeSituation A)
    {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := S.shift.kShift
    ∃ φ : negativeConeTriangle S E.a ⟶ GradedSplitShortExact.associatedKTriangle S.shift E,
      φ.hom₁ = 𝟙 _ ∧ φ.hom₂ = 𝟙 _ ∧ IsIso φ.hom₃ :=
  ConeSituationIso.coneTriangleIsoOfShortExact S.toConeSituationIso E

/-- For a shift additive on objects up to isomorphism, the triangle of an admissible short exact
sequence is isomorphic to the negated cone triangle of any morphism it factors. -/
public theorem ConeSituationIso.shortExactTriangleIsoOfFactorization (S : ConeSituationIso A)
    {x y y' z : A.Obj} (α : A.Cocycle x y)
    (E : GradedSplitShortExact (A := A) x y' z)
    (π : A.Cocycle y' y) (hπα : A.compCocycle π E.a = α)
    (s : A.Cocycle y y')
    (hπs : A.compCocycle π s = (⟨A.id y, A.d_id y⟩ : A.Cocycle y y))
    (hsπ : A.Homotopic (A.compCocycle s π)
      (⟨A.id y', A.d_id y'⟩ : A.Cocycle y' y')) :
    letI : HasShift A.K ℤ := S.shift.kShift
    ∃ φ : S.shift.associatedKTriangle E ⟶ S.negativeConeTriangle α,
      φ.hom₁ = 𝟙 _ ∧
      φ.hom₂ = Quotient.mk (A.homotopySetoid y' y) π ∧
      IsIso φ.hom₃ := by
  let _ : HasShift A.K ℤ := S.shift.kShift
  let u : A.Cocycle x x := ⟨A.id x, A.d_id x⟩
  have hsquare : A.compK (Quotient.mk (A.homotopySetoid y' y) π)
        (Quotient.mk (A.homotopySetoid x y') E.a) =
      A.compK (Quotient.mk (A.homotopySetoid x y) α)
        (Quotient.mk (A.homotopySetoid x x) u) := by
    change Quotient.mk _ (A.compCocycle π E.a) =
      Quotient.mk _ (A.compCocycle α u)
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change A.comp (by lia : (0 : ℤ) + 0 = 0) π.1 E.a.1 =
      A.comp (by lia : (0 : ℤ) + 0 = 0) α.1 u.1
    rw [A.comp_id]
    exact congrArg Subtype.val hπα
  obtain ⟨c, hc₁, hc₂⟩ := ConeSituationIso.exists_coneTriangleMorphism S E.a α u π hsquare
  let cK : A.HomotopyClass (S.cone E.a) (S.cone α) :=
    Quotient.mk (A.homotopySetoid (S.cone E.a) (S.cone α)) c
  let D₁ := S.coneSequence E.a
  let D₂ := S.coneSequence α
  let γ := (S.shift.shiftFunctor 1).mapCocycle u
  have hshift : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x =
      (S.shift.shiftFunctor (1 : ℤ)).obj x :=
    congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.shift.kShift_functor 1)
  have hshiftId : Quotient.mk
      (A.homotopySetoid ((S.shift.shiftFunctor 1).obj x)
        ((S.shift.shiftFunctor 1).obj x)) γ =
      @CategoryTheory.CategoryStruct.id (A.K) _ ((S.shift.shiftFunctor 1).obj x) := by
    change Quotient.mk _ γ = Quotient.mk _
      (⟨A.id ((S.shift.shiftFunctor 1).obj x),
        A.d_id ((S.shift.shiftFunctor 1).obj x)⟩ :
          A.Cocycle ((S.shift.shiftFunctor 1).obj x) ((S.shift.shiftFunctor 1).obj x))
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change (S.shift.shiftFunctor 1).map (A.id x) = A.id ((S.shift.shiftFunctor 1).obj x)
    exact (S.shift.shiftFunctor 1).map_id x
  have hsq : ∀ (b₁ : A.Cocycle (S.cone E.a) ((S.shift.shiftFunctor 1).obj x))
      (b₂ : A.Cocycle (S.cone α) ((S.shift.shiftFunctor 1).obj x)),
      A.compK (Quotient.mk _ b₂) cK = A.compK (Quotient.mk _ γ) (Quotient.mk _ b₁) →
      (Quotient.mk _ b₁ : A.HomotopyClass _ _) ≫ eqToHom hshift.symm =
        cK ≫ ((Quotient.mk _ b₂ : A.HomotopyClass _ _) ≫ eqToHom hshift.symm) := by
    intro b₁ b₂ hb
    have hleft : A.compK
        (@CategoryTheory.CategoryStruct.id (A.K) _ ((S.shift.shiftFunctor 1).obj x))
        (Quotient.mk _ b₁) = Quotient.mk _ b₁ := by
      simpa [CategoryStruct.comp, CategoryStruct.id, DGCategory.instCategoryK] using
        (@CategoryTheory.Category.comp_id (A.K) (DGCategory.instCategoryK A)
          (S.cone E.a) ((S.shift.shiftFunctor 1).obj x) (Quotient.mk _ b₁))
    have hcast := congrArg (fun q => q ≫ eqToHom hshift.symm) hb.symm
    rw [hshiftId, hleft] at hcast
    have hcast' : (Quotient.mk _ b₁ : A.HomotopyClass _ _) ≫ eqToHom hshift.symm =
        (cK ≫ (Quotient.mk _ b₂ : A.HomotopyClass _ _)) ≫ eqToHom hshift.symm := by
      simpa [CategoryStruct.comp, DGCategory.instCategoryK] using hcast
    rw [hcast']
    exact CategoryTheory.Category.assoc _ _ _
  let θpos : S.coneTriangle E.a ⟶ S.coneTriangle α :=
    Pretriangulated.Triangle.homMk _ _ (𝟙 _) (Quotient.mk _ π) cK
      (by exact hsquare) (by exact hc₁) (by
        dsimp [coneTriangle]
        simp only [CategoryTheory.Functor.map_id]
        exact (CategoryTheory.Category.comp_id _).trans (hsq _ _ hc₂))
  have hπiso : @CategoryTheory.IsIso (A.K) (DGCategory.instCategoryK A) y' y
      (Quotient.mk (A.homotopySetoid y' y) π) :=
    isIso_mk_of_homotopic_inverse π s hsπ (hπs ▸ A.homotopic_refl _)
  have hcIso : IsIso θpos.hom₃ :=
    ConeSituationIso.isIso_cone_of_isIso_source_target S E.a α θpos
      (by change IsIso (𝟙 (S.coneTriangle E.a).obj₁); infer_instance)
      hπiso
  let θneg : S.negativeConeTriangle E.a ⟶ S.negativeConeTriangle α :=
    Pretriangulated.Triangle.homMk _ _ (𝟙 _) (Quotient.mk _ π) cK
      (by exact hsquare) (by exact hc₁) (by
        dsimp [negativeConeTriangle]
        let n₁ : A.Cocycle (S.cone E.a) ((S.shift.shiftFunctor 1).obj x) :=
          cocycleNeg D₁.b
        let n₂ : A.Cocycle (S.cone α) ((S.shift.shiftFunctor 1).obj x) :=
          cocycleNeg D₂.b
        have hc₂' : Quotient.mk (A.homotopySetoid (S.cone E.a)
              ((S.shift.shiftFunctor 1).obj x)) (A.compCocycle D₂.b c) =
            Quotient.mk (A.homotopySetoid (S.cone E.a)
              ((S.shift.shiftFunctor 1).obj x)) (A.compCocycle γ D₁.b) := by
          simpa only [DGCategory.compK, Quotient.map₂_mk] using hc₂
        have hbase : A.Homotopic (A.compCocycle D₂.b c)
            (A.compCocycle γ D₁.b) :=
          Quotient.exact hc₂'
        have hcomp₁ : A.compCocycle n₂ c =
            cocycleNeg (A.compCocycle D₂.b c) := by
          exact Subtype.ext (comp_neg_left _ _ _)
        have hcomp₂ : A.compCocycle γ n₁ =
            cocycleNeg (A.compCocycle γ D₁.b) := by
          exact Subtype.ext (comp_neg_right _ _ _)
        have hnegrel : A.Homotopic (A.compCocycle n₂ c)
            (A.compCocycle γ n₁) := by
          rw [hcomp₁, hcomp₂]
          exact homotopic_neg hbase
        have hnegK : A.compK (Quotient.mk _ n₂) cK =
            A.compK (Quotient.mk _ γ) (Quotient.mk _ n₁) := by
          change Quotient.mk _ (A.compCocycle n₂ c) =
            Quotient.mk _ (A.compCocycle γ n₁)
          exact Quotient.sound hnegrel
        simp only [CategoryTheory.Functor.map_id]
        exact (CategoryTheory.Category.comp_id _).trans (hsq n₁ n₂ hnegK))
  obtain ⟨φE, hE₁, hE₂, hE₃⟩ := ConeSituationIso.coneTriangleIsoOfShortExact S E
  have : IsIso φE := by
    apply CategoryTheory.Pretriangulated.Triangle.isIso_of_isIsos
    · exact hE₁ ▸ @IsIso.id A.K (DGCategory.instCategoryK A) _
    · exact hE₂ ▸ @IsIso.id A.K (DGCategory.instCategoryK A) _
    · exact hE₃
  have hinv₁ : (inv φE).hom₁ = 𝟙 _ := by
    have h := congrArg (·.hom₁) (IsIso.inv_hom_id φE)
    simp only [Pretriangulated.comp_hom₁,
      Pretriangulated.id_hom₁, hE₁] at h
    exact (Category.comp_id _).symm.trans h
  have hinv₂ : (inv φE).hom₂ = 𝟙 _ := by
    have h := congrArg (·.hom₂) (IsIso.inv_hom_id φE)
    simp only [Pretriangulated.comp_hom₂,
      Pretriangulated.id_hom₂, hE₂] at h
    exact (Category.comp_id _).symm.trans h
  have : IsIso φE.hom₃ := hE₃
  have : IsIso θneg.hom₃ := by
    simpa [θneg, θpos, negativeConeTriangle, coneTriangle] using hcIso
  refine ⟨inv φE ≫ θneg, ?_, ?_, ?_⟩
  · exact (congrArg (· ≫ θneg.hom₁) hinv₁).trans (Category.id_comp _)
  · exact (congrArg (· ≫ θneg.hom₂) hinv₂).trans (Category.id_comp _)
  · change IsIso ((inv φE).hom₃ ≫ θneg.hom₃)
    infer_instance

/-- The admissible sequence in a factorization of a closed arrow gives a triangle
isomorphic to the cone triangle of that arrow, by the identity on the source and the
factorization's homotopy equivalence on the target. -/
@[stacks 09QU "part (2)", sga "4 XVII 1.1.1" "DG cat. with cone situat"]
public theorem shortExactTriangleIsoOfFactorization (S : ConeSituation A)
    {x y y' z : A.Obj} (α : A.Cocycle x y)
    (E : GradedSplitShortExact (A := A) x y' z)
    (π : A.Cocycle y' y) (hπα : A.compCocycle π E.a = α)
    (s : A.Cocycle y y')
    (hπs : A.compCocycle π s = (⟨A.id y, A.d_id y⟩ : A.Cocycle y y))
    (hsπ : A.Homotopic (A.compCocycle s π)
      (⟨A.id y', A.d_id y'⟩ : A.Cocycle y' y')) :
    letI : HasShift A.K ℤ := S.shift.kShift
    ∃ φ : GradedSplitShortExact.associatedKTriangle S.shift E ⟶ negativeConeTriangle S α,
      φ.hom₁ = 𝟙 _ ∧
      φ.hom₂ = Quotient.mk (A.homotopySetoid y' y) π ∧
      IsIso φ.hom₃ :=
  ConeSituationIso.shortExactTriangleIsoOfFactorization S.toConeSituationIso α E π hπα s hπs hsπ
end DGCategory
