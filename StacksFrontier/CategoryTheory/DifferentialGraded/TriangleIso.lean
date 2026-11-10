module

public import StacksFrontier.CategoryTheory.DifferentialGraded.TriangulatedIso

/-!
# The triangle of a graded-split short exact sequence, for a shift additive up to isomorphism

The triangle `x → y → z → x[1]` of an admissible short exact sequence, and the vanishing of each
of its consecutive composites in the homotopy category, are the content of Tag 09P6. They are
proved in `StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated` for a differential graded
category carrying `DGCategory.ShiftAxiomB`, the strict form of axiom (B). This file proves the
same statements for `DGCategory.ShiftAxiomBIso`, in which the shift is additive on objects only
up to isomorphism.

## Main definitions

* `DGCategory.ShiftAxiomBIso.connectingCocycle`: the connecting arrow `z ⟶ x[1]`.
* `DGCategory.ShiftAxiomBIso.shiftedConnecting`: the rotated arrow `z[-1] ⟶ x`, the shift of the
  connecting arrow composed with `DGCategory.ShiftAxiomBIso.unshiftIso`.
* `DGCategory.ShiftAxiomBIso.associatedCompTriangle` and
  `DGCategory.ShiftAxiomBIso.associatedKTriangle`: the associated triangles in the category of
  complexes and in the homotopy category.

## Main results

* `DGCategory.ShiftAxiomBIso.connecting_comp_zero_in_K`,
  `DGCategory.ShiftAxiomBIso.comp_connecting_zero_in_K` and
  `DGCategory.ShiftAxiomBIso.shifted_connecting_comp_zero_in_K`: the three composites involving
  the connecting arrow vanish in the homotopy category.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory
open GradedSplitShortExact (connectingHom connectingHom_comp comp_connectingHom)

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- A differential graded functor commutes with the differential reaching a prescribed
degree. -/
private lemma DGFunctor.map_d' {B : DGCategory.{v, u} R} (F : DGFunctor A B)
    {x y : A.Obj} {m n : ℤ} (e : m + 1 = n) (f : A.Hom x y m) :
    F.map (A.d' e f) = B.d' e (F.map f) := by
  subst e
  change F.map (A.d f) = B.d (F.map f)
  exact F.map_d f

namespace ShiftAxiomBIso

variable (S : ShiftAxiomBIso A)

/-- The shift conversion of the differential of a degree `-1` morphism is the differential of the
negated conversion. -/
private theorem toShift_d_eq_d'_neg (S : ShiftAxiomBIso A) {x y : A.Obj}
    (u : A.Hom x y 0) :
    S.toShift 1 x y 0 (A.d u) = A.d' (by omega : (-1 : ℤ) + 1 = 0) (-S.toShift 1 x y (-1) u) := by
  change _ = A.d (-S.toShift 1 x y (-1) u)
  rw [← neg_one_smul R (S.toShift 1 x y (-1) u), A.d_smul, neg_one_smul]
  simpa [DGCategory.d'] using
    S.toShift_d 1 x y (-1) (show A.Hom x y ((-1 : ℤ) + 1) from u)

/-- The degree-one connecting cocycle remains closed after conversion to a map into the shifted
object. -/
theorem connecting_shift_closed {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d ((S.toShift 1 z x 0) (connectingHom E)) = 0 := by
  have hδ : A.d' (by omega : (1 : ℤ) + 1 = 2) (connectingHom E) = 0 := by
    simpa [DGCategory.d'] using GradedSplitShortExact.connectingHom_closed (A := A) E
  simpa [hδ] using S.toShift_d 1 z x 0 (connectingHom E)

/-- The connecting arrow `z ⟶ x[1]` of `Comp(A)`. -/
def connectingCocycle {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    A.Cocycle z ((S.shiftFunctor 1).obj x) :=
  ⟨(S.toShift 1 z x 0) (connectingHom E), S.connecting_shift_closed E⟩

/-- The rotated arrow `z[-1] ⟶ x`: the negative shift of the connecting arrow, followed by the
isomorphism `x[1][-1] ≅ x`. -/
def shiftedConnecting {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    A.Cocycle ((S.shiftFunctor (-1)).obj z) x :=
  A.compCocycle (S.unshiftIso x).hom
    ((S.shiftFunctor (-1)).mapCocycle (S.connectingCocycle E))

/-- The associated triangle in the category of complexes, with the arrow `z ⟶ x[1]` given by
`π d(s)`. -/
def associatedCompTriangle {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.Comp ℤ := S.compShift
    Pretriangulated.Triangle A.Comp := by
  letI : HasShift A.Comp ℤ := S.compShift
  have h : (CategoryTheory.shiftFunctor A.Comp (1 : ℤ)).obj x =
      (S.shiftFunctor (1 : ℤ)).obj x :=
    congrArg (fun F : A.Comp ⥤ A.Comp => F.obj x) (S.compShift_functor 1)
  exact Pretriangulated.Triangle.mk E.a E.b (S.connectingCocycle E ≫ eqToHom h.symm)

/-- The same triangle, regarded in the homotopy category. -/
def associatedKTriangle {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
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
      (S.connectingCocycle E)) ≫ eqToHom h.symm)

/-- The composite `y ⟶ z ⟶ x[1]` is zero in `K(A)`. -/
theorem connecting_comp_zero_in_K {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.compK (Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x))
        (S.connectingCocycle E))
      (Quotient.mk (A.homotopySetoid y z) E.b) =
    Quotient.mk (A.homotopySetoid y ((S.shiftFunctor 1).obj x))
      (⟨0, A.d_zero⟩ : A.Cocycle y ((S.shiftFunctor 1).obj x)) := by
  change Quotient.mk (A.homotopySetoid y ((S.shiftFunctor 1).obj x))
      (A.compCocycle (S.connectingCocycle E) E.b) = _
  apply Quotient.sound
  refine ⟨-S.toShift 1 y x (-1) (-E.π), ?_⟩
  change A.comp (by omega : (0 : ℤ) + 0 = 0)
      (S.toShift 1 z x 0 (connectingHom E)) E.b.1 - 0 =
    A.d' (by omega : (-1 : ℤ) + 1 = 0) (-S.toShift 1 y x (-1) (-E.π))
  simp only [sub_zero]
  calc
    A.comp (by omega : (0 : ℤ) + 0 = 0)
        (S.toShift 1 z x 0 (connectingHom E)) E.b.1 =
      S.toShift 1 y x 0
        (A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom E) E.b.1) := by
      simpa using
        (S.toShift_comp_right (n := 1) (x := y) (y := z) (z := x)
          (m := 0) (l := 0) (g := connectingHom E) (f := E.b.1)).symm
    _ = S.toShift 1 y x 0 (A.d (-E.π)) := by rw [connectingHom_comp]
    _ = _ := S.toShift_d_eq_d'_neg _

/-- The composite `z ⟶ x[1] ⟶ y[1]` is zero in `K(A)`. -/
theorem comp_connecting_zero_in_K {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.compK (Quotient.mk (A.homotopySetoid ((S.shiftFunctor 1).obj x)
        ((S.shiftFunctor 1).obj y)) ((S.shiftFunctor 1).mapCocycle E.a))
      (Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj x))
        (S.connectingCocycle E)) =
    Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj y))
      (⟨0, A.d_zero⟩ : A.Cocycle z ((S.shiftFunctor 1).obj y)) := by
  change Quotient.mk (A.homotopySetoid z ((S.shiftFunctor 1).obj y))
      (A.compCocycle ((S.shiftFunctor 1).mapCocycle E.a) (S.connectingCocycle E)) = _
  apply Quotient.sound
  refine ⟨-S.toShift 1 z y (-1) E.s, ?_⟩
  change A.comp (by omega : (0 : ℤ) + 0 = 0)
      ((S.shiftFunctor 1).map E.a.1) ((S.toShift 1 z x 0) (connectingHom E)) - 0 =
    A.d' (by omega : (-1 : ℤ) + 1 = 0) (-S.toShift 1 z y (-1) E.s)
  simp only [sub_zero]
  calc
    A.comp (by omega : (0 : ℤ) + 0 = 0)
        ((S.shiftFunctor 1).map E.a.1) ((S.toShift 1 z x 0) (connectingHom E)) =
      S.toShift 1 z y 0
        (A.comp (by omega : (0 : ℤ) + 1 = 1) E.a.1 (connectingHom E)) := by
      simpa using (S.toShift_comp_left 1 (m := 0) (l := 0) E.a.1 (connectingHom E)).symm
    _ = S.toShift 1 z y 0 (A.d E.s) := by rw [comp_connectingHom]
    _ = _ := S.toShift_d_eq_d'_neg E.s

/-- The rotated composite `z[-1] ⟶ x ⟶ y` is zero in `K(A)`. -/
theorem shifted_connecting_comp_zero_in_K {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.compK (Quotient.mk (A.homotopySetoid x y) E.a)
      (Quotient.mk (A.homotopySetoid ((S.shiftFunctor (-1)).obj z) x)
        (S.shiftedConnecting E)) =
    Quotient.mk (A.homotopySetoid ((S.shiftFunctor (-1)).obj z) y)
      (⟨0, A.d_zero⟩ : A.Cocycle ((S.shiftFunctor (-1)).obj z) y) := by
  set F := S.shiftFunctor (-1) with hF
  set G := S.shiftFunctor 1 with hG
  obtain ⟨t, ht⟩ := Quotient.exact (S.comp_connecting_zero_in_K E)
  change A.comp (by omega : (0 : ℤ) + 0 = 0) (G.map E.a.1)
      ((S.connectingCocycle E).1) - 0 =
    A.d' (by omega : (-1 : ℤ) + 1 = 0) t at ht
  rw [sub_zero] at ht
  change Quotient.mk (A.homotopySetoid (F.obj z) y)
      (A.compCocycle E.a (S.shiftedConnecting E)) = _
  apply Quotient.sound
  refine ⟨A.comp (by omega : (0 : ℤ) + (-1) = -1) (S.unshiftIso y).hom.1 (F.map t), ?_⟩
  change A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 (S.shiftedConnecting E).1 - 0 =
    A.d' (by omega : (-1 : ℤ) + 1 = 0)
      (A.comp (by omega : (0 : ℤ) + (-1) = -1) (S.unshiftIso y).hom.1 (F.map t))
  rw [sub_zero]
  calc
    A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 (S.shiftedConnecting E).1 =
        A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 (S.unshiftIso x).hom.1)
          (F.map (S.connectingCocycle E).1) :=
      A.assoc (by omega : (0 : ℤ) + 0 = 0) (by omega : (0 : ℤ) + 0 = 0)
        (by omega : (0 : ℤ) + 0 = 0) (by omega : (0 : ℤ) + 0 = 0) E.a.1
        (S.unshiftIso x).hom.1 (F.map (S.connectingCocycle E).1)
    _ = A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0) (S.unshiftIso y).hom.1
            (F.map (G.map E.a.1)))
          (F.map (S.connectingCocycle E).1) := by
      rw [S.unshiftIso_natural E.a.1]
    _ = A.comp (by omega : (0 : ℤ) + 0 = 0) (S.unshiftIso y).hom.1
          (A.comp (by omega : (0 : ℤ) + 0 = 0) (F.map (G.map E.a.1))
            (F.map (S.connectingCocycle E).1)) :=
      (A.assoc (by omega : (0 : ℤ) + 0 = 0) (by omega : (0 : ℤ) + 0 = 0)
        (by omega : (0 : ℤ) + 0 = 0) (by omega : (0 : ℤ) + 0 = 0)
        (S.unshiftIso y).hom.1 (F.map (G.map E.a.1))
        (F.map (S.connectingCocycle E).1)).symm
    _ = A.comp (by omega : (0 : ℤ) + 0 = 0) (S.unshiftIso y).hom.1
          (F.map (A.comp (by omega : (0 : ℤ) + 0 = 0) (G.map E.a.1)
            (S.connectingCocycle E).1)) := by
      rw [F.map_comp]
    _ = A.comp (by omega : (0 : ℤ) + 0 = 0) (S.unshiftIso y).hom.1
          (F.map (A.d' (by omega : (-1 : ℤ) + 1 = 0) t)) := by
      rw [ht]
    _ = A.comp (by omega : (0 : ℤ) + 0 = 0) (S.unshiftIso y).hom.1
          (A.d' (by omega : (-1 : ℤ) + 1 = 0) (F.map t)) := by
      rw [DGFunctor.map_d']
    _ = A.d' (by omega : (-1 : ℤ) + 1 = 0)
          (A.comp (by omega : (0 : ℤ) + (-1) = -1) (S.unshiftIso y).hom.1 (F.map t)) :=
      A.comp_dboundary_right (S.unshiftIso y).hom.1 (S.unshiftIso y).hom.2 (F.map t)

end ShiftAxiomBIso

end DGCategory
