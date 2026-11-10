module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Independence of the associated triangle from the graded splitting

For an admissible short exact sequence in a differential graded category, the triangle it
determines in the homotopy category does not depend on the splitting chosen for the underlying
graded sequence.

## Main results

* `DGCategory.associatedKTriangle_eq_of_same_sequence`: two graded splittings with the same two
  closed arrows give the same triangle in the homotopy category.

## Implementation notes

The identification is an equality of triangles, not merely an isomorphism: the objects and the
first two arrows are literally the same, so the only thing to prove is that the connecting arrows
agree in the homotopy category. Changing the splitting changes the connecting morphism by the
coboundary of `π ∘ s'`; after transport into the shift that coboundary becomes a homotopy.

Only the shift axiom (B) is assumed, not the cone axiom (C).

## References

* [Stacks Project, Tag 09QQ](https://stacks.math.columbia.edu/tag/09QQ)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- Changing the graded splitting changes the connecting morphism by the coboundary of
`π ∘ s'`. -/
private theorem connectingHom_change_splitting {x y z : A.Obj}
    (E E' : GradedSplitShortExact (A := A) x y z) (ha : E.a = E'.a) (hb : E.b = E'.b) :
    GradedSplitShortExact.connectingHom E' = GradedSplitShortExact.connectingHom E +
      A.d' (by omega : (0 : ℤ) + 1 = 1)
        (A.comp (by omega : (0 : ℤ) + 0 = 0) E.π E'.s) := by
  let h0 : (0 : ℤ) + 0 = 0 := by lia
  let h01 : (0 : ℤ) + 1 = 1 := by lia
  have hpa : A.comp h0 E'.π E.a.1 = A.id x := by
    simpa [ha] using E'.π_a
  have hbs : A.comp h0 E.b.1 E'.s = A.id z := by
    simpa [hb] using E'.b_s
  have hs : E'.s = E.s + A.comp h0 E.a.1 (A.comp h0 E.π E'.s) := by
    calc
      E'.s = A.comp h0 (A.id y) E'.s := (A.id_comp E'.s).symm
      _ = A.comp h0 (A.comp h0 E.a.1 E.π + A.comp h0 E.s E.b.1) E'.s := by
        rw [← E.a_π_add_s_b]
      _ = A.comp h0 (A.comp h0 E.a.1 E.π) E'.s +
          A.comp h0 (A.comp h0 E.s E.b.1) E'.s := A.comp_add_left h0 _ _ _
      _ = A.comp h0 E.a.1 (A.comp h0 E.π E'.s) +
          A.comp h0 E.s (A.comp h0 E.b.1 E'.s) := by
        rw [A.assoc, A.assoc]
      _ = E.s + A.comp h0 E.a.1 (A.comp h0 E.π E'.s) := by
        rw [hbs, A.comp_id]
        abel
  have hbd : A.comp (by lia : (0 : ℤ) + 1 = 1) E.b.1 (A.d E'.s) = 0 := by
    have hlib := A.leibniz h0 E.b.1 E'.s
    rw [hbs, A.d_id, E.b.2, A.comp_zero_left,
      show ((-1 : R) ^ (Int.natAbs 0)) = 1 by norm_num, one_smul] at hlib
    simpa using hlib.symm
  have hds : A.d' (by lia : (0 : ℤ) + 1 = 1) E'.s =
      A.d' (by lia : (0 : ℤ) + 1 = 1) E.s +
      A.comp (by lia : (0 : ℤ) + 1 = 1) E.a.1
        (A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s)) := by
    have hlib := A.leibniz h0 E.a.1 (A.comp h0 E.π E'.s)
    rw [E.a.2, A.comp_zero_left,
      show ((-1 : R) ^ (Int.natAbs 0)) = 1 by norm_num, one_smul] at hlib
    have hlib' : A.d' (by lia : (0 : ℤ) + 1 = 1)
          (A.comp h0 E.a.1 (A.comp h0 E.π E'.s)) =
        A.comp (by lia : (0 : ℤ) + 1 = 1) E.a.1
          (A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s)) := by
      simpa [DGCategory.d', zero_add] using hlib
    calc
      A.d' (by lia : (0 : ℤ) + 1 = 1) E'.s =
          A.d' (by lia : (0 : ℤ) + 1 = 1)
            (E.s + A.comp h0 E.a.1 (A.comp h0 E.π E'.s)) := by
        conv_lhs => rw [hs]
      _ = A.d' (by lia : (0 : ℤ) + 1 = 1) E.s +
            A.d' (by lia : (0 : ℤ) + 1 = 1)
              (A.comp h0 E.a.1 (A.comp h0 E.π E'.s)) := by
        simp only [DGCategory.d']
        rw [A.d_add]
      _ = A.d' (by lia : (0 : ℤ) + 1 = 1) E.s +
            A.comp h01 E.a.1
              (A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s)) := by
        rw [hlib']
  calc
    GradedSplitShortExact.connectingHom E' = A.comp h01 E'.π (A.d E'.s) := rfl
    _ = A.comp h01 (E.π + A.comp h0 E'.π (A.comp h0 E.s E.b.1)) (A.d E'.s) := by
      congr 1
      calc
        E'.π = A.comp h0 E'.π (A.id y) := (A.comp_id E'.π).symm
        _ = A.comp h0 E'.π (A.comp h0 E.a.1 E.π + A.comp h0 E.s E.b.1) := by
          rw [← E.a_π_add_s_b]
        _ = A.comp h0 E'.π (A.comp h0 E.a.1 E.π) +
              A.comp h0 E'.π (A.comp h0 E.s E.b.1) := A.comp_add_right h0 _ _ _
        _ = E.π + A.comp h0 E'.π (A.comp h0 E.s E.b.1) := by
          rw [A.assoc h0 h0 h0 h0 E'.π E.a.1 E.π, hpa, A.id_comp]
    _ = A.comp h01 E.π (A.d E'.s) := by
      rw [A.comp_add_left]
      have hkill : A.comp h01 (A.comp h0 E'.π (A.comp h0 E.s E.b.1)) (A.d E'.s) = 0 := by
        rw [A.assoc h0 h0 h0 h0 E'.π E.s E.b.1,
          ← A.assoc h01 h01 h0 h01 (A.comp h0 E'.π E.s) E.b.1 (A.d E'.s), hbd, A.comp_zero_right]
      rw [hkill, add_zero]
    _ = A.comp h01 E.π (A.d' (by lia : (0 : ℤ) + 1 = 1) E'.s) := rfl
    _ = A.comp h01 E.π
          (A.d' (by lia : (0 : ℤ) + 1 = 1) E.s +
            A.comp (by lia : (0 : ℤ) + 1 = 1) E.a.1
              (A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s))) := by
      rw [hds]
    _ = A.comp h01 E.π (A.d E.s) +
          A.comp h01 E.π
            (A.comp h01 E.a.1
              (A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s))) := by
      rw [A.comp_add_right]
      simp [DGCategory.d']
    _ = A.comp h01 E.π (A.d E.s) +
          A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s) := by
      rw [A.assoc h01 h01 h0 h01 E.π E.a.1
        (A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s)), E.π_a, A.id_comp]
    _ = GradedSplitShortExact.connectingHom E +
          A.d' (by lia : (0 : ℤ) + 1 = 1) (A.comp h0 E.π E'.s) := rfl

/-- Changing the graded splitting of an admissible short exact sequence does not change its
associated triangle in the homotopy category. -/
@[stacks 09QQ]
theorem associatedKTriangle_eq_of_same_sequence {x y z : A.Obj} (S : ShiftAxiomB A)
    (E E' : GradedSplitShortExact (A := A) x y z) (ha : E.a = E'.a) (hb : E.b = E'.b) :
    GradedSplitShortExact.associatedKTriangle S E =
      GradedSplitShortExact.associatedKTriangle S E' := by
  let h0 : (0 : ℤ) + 0 = 0 := by lia
  let g : A.Hom z x 0 := A.comp h0 E.π E'.s
  let g' : A.Hom z x (-1 + 1) := by simpa using g
  let h : A.Hom z ((S.shiftFunctor 1).obj x) (-1) := S.toShift 1 z x (-1) g'
  have hmap := congrArg (S.toShift 1 z x 0) (connectingHom_change_splitting E E' ha hb)
  rw [map_add] at hmap
  have hdiff :
      S.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E') -
        S.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E) =
      S.toShift 1 z x 0 (A.d' (by lia : (0 : ℤ) + 1 = 1) g) := by
    rw [hmap]
    abel
  have hshiftD' :
      S.toShift 1 z x 0 (A.d' (by lia : (0 : ℤ) + 1 = 1) g) = -A.d h := by
    simpa [h, g', Int.natAbs] using S.toShift_d 1 z x (-1) g'
  have hnegD : A.d' (by lia : (-1 : ℤ) + 1 = 0) (-h) = -A.d h := by
    change A.d (-h) = -A.d h
    rw [show -h = (-1 : R) • h by rw [neg_one_smul], A.d_smul, neg_one_smul]
  have hhomotopy : A.Homotopic (GradedSplitShortExact.connectingCocycle S E')
      (GradedSplitShortExact.connectingCocycle S E) := by
    refine ⟨-h, ?_⟩
    change S.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E') -
      S.toShift 1 z x 0 (GradedSplitShortExact.connectingHom E) =
        A.d' (by lia : (-1 : ℤ) + 1 = 0) (-h)
    rw [hdiff, hshiftD', hnegD]
  let _ : HasShift A.K ℤ := S.kShift
  have hK : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x = (S.shiftFunctor (1 : ℤ)).obj x :=
    congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.kShift_functor 1)
  have hthird :
      (Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x))
          (GradedSplitShortExact.connectingCocycle S E')) ≫ eqToHom hK.symm =
        (Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x))
          (GradedSplitShortExact.connectingCocycle S E)) ≫ eqToHom hK.symm :=
    congrArg (fun f => f ≫ eqToHom hK.symm) (Quotient.sound hhomotopy)
  unfold GradedSplitShortExact.associatedKTriangle
  rw [ha, hb]
  exact congrArg (fun f => Pretriangulated.Triangle.mk
    (Quotient.mk (A.homotopySetoid x y) E'.a)
    (Quotient.mk (A.homotopySetoid y z) E'.b) f) hthird.symm

end DGCategory
