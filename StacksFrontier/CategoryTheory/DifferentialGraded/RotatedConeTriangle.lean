module

public import Mathlib.CategoryTheory.Triangulated.Rotate
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituation

/-!
# Rotation of an admissible triangle and the cone triangle

In a differential graded category with cones, the triangle obtained from an admissible short
exact sequence by moving its connecting map to the first position is isomorphic to the cone
triangle of that connecting map.

## Main definitions

* `DGCategory.resuspension`: the canonical map `z ⟶ z[-1][1]` in the homotopy category.
* `DGCategory.rotatedAssociatedTriangle`: the triangle on the desuspended connecting map, the
  inclusion and the projection.
* `DGCategory.connectingConeTriangle`: the cone triangle of that desuspended connecting map.

## Main results

* `DGCategory.associatedCompTriangle_coneSequence`,
  `DGCategory.associatedKTriangle_coneSequence`: the triangle `(y, c(f), x[1], i, p, f[1])` is the
  triangle associated to the admissible short exact sequence `y ⟶ c(f) ⟶ x[1]`.
* `DGCategory.rotatedAssociatedTriangle_iso_connectingConeTriangle`: the two triangles are
  isomorphic.

## Implementation notes

The isomorphism is the identity on the first two objects, and on the third it is the morphism
`u = a' π + s' q b` of the cone, with inverse `v = a π' + s q⁻¹ b'`.

The terminal arrows of both triangles factor through `resuspension`, the canonical map
`z ⟶ z[-1][1]` built from the counit of the shift equivalence of the homotopy category.

## References

* [Stacks Project, Tag 09QR](https://stacks.math.columbia.edu/tag/09QR)
* [Stacks Project, Tag 09QS](https://stacks.math.columbia.edu/tag/09QS)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- Let `f : x ⟶ y` be a morphism in `Comp(𝒜)`. The triangle `(y, c(f), x[1], i, p, f[1])` is
the triangle associated to the admissible short exact sequence `y ⟶ c(f) ⟶ x[1]`. -/
@[stacks 09QR "the statement in `Comp(A)`: the triangle associated to the cone sequence of `f` is
  the triangle on `y`, `c(f)`, `x[1]` whose first two arrows are that sequence's inclusion and
  projection and whose connecting arrow is `f[1]`. The homotopy-category form is
  `associatedKTriangle_coneSequence`; neither covers the comparison with the cone triangle of `f`
  (Tag 09QU) nor the rotation of this triangle (Tag 09QS)"]
theorem associatedCompTriangle_coneSequence (C : ConeSituation A) {x y : A.Obj}
    (f : A.Cocycle x y) :
    letI : HasShift A.Comp ℤ := C.shift.compShift
    GradedSplitShortExact.associatedCompTriangle C.shift (C.coneSequence f) =
      Pretriangulated.Triangle.mk
        ((C.coneSequence f).a : (show A.Comp from y) ⟶ (show A.Comp from C.cone f))
        ((C.coneSequence f).b :
          (show A.Comp from C.cone f) ⟶
            (show A.Comp from (C.shift.shiftFunctor 1).obj x))
        (((C.shift.shiftFunctor 1).mapCocycle f :
            (show A.Comp from (C.shift.shiftFunctor 1).obj x) ⟶
              (show A.Comp from (C.shift.shiftFunctor 1).obj y)) ≫
          eqToHom (congrArg (fun F : A.Comp ⥤ A.Comp => F.obj y)
            (C.shift.compShift_functor 1)).symm) := by
  unfold GradedSplitShortExact.associatedCompTriangle
  rw [C.cone_connecting f]
  rfl

/-- The same identification in the homotopy category: the triangle
`(y, c(f), x[1], i, p, f[1])` is the triangle associated to the admissible short exact sequence
`y ⟶ c(f) ⟶ x[1]`. -/
@[stacks 09QR "the statement in `K(A)`: the triangle associated to the cone sequence of `f` is the
  triangle on `y`, `c(f)`, `x[1]` whose first two arrows are the homotopy classes of that
  sequence's inclusion and projection and whose connecting arrow is the class of `f[1]`. The form
  in `Comp(A)` is `associatedCompTriangle_coneSequence`; neither covers the comparison with the
  cone triangle of `f` (Tag 09QU) nor the rotation of this triangle (Tag 09QS)"]
theorem associatedKTriangle_coneSequence (C : ConeSituation A) {x y : A.Obj}
    (f : A.Cocycle x y) :
    letI : HasShift A.K ℤ := C.shift.kShift
    GradedSplitShortExact.associatedKTriangle C.shift (C.coneSequence f) =
      Pretriangulated.Triangle.mk
        (Quotient.mk (A.homotopySetoid y (C.cone f)) (C.coneSequence f).a)
        (Quotient.mk (A.homotopySetoid (C.cone f) ((C.shift.shiftFunctor 1).obj x))
          (C.coneSequence f).b)
        ((Quotient.mk (A.homotopySetoid ((C.shift.shiftFunctor 1).obj x)
              ((C.shift.shiftFunctor 1).obj y))
            ((C.shift.shiftFunctor 1).mapCocycle f)) ≫
          eqToHom (congrArg (fun F : A.K ⥤ A.K => F.obj y)
            (C.shift.kShift_functor 1)).symm) := by
  unfold GradedSplitShortExact.associatedKTriangle
  rw [C.cone_connecting f]
  rfl

/-- Two cocycles that are heterogeneously equal along equalities of their source and target
objects become equal after conjugating by the corresponding `eqToHom`s. -/
theorem cocycle_eq_transport_of_val_heq {x x' y y' : A.Obj}
    (f : A.Cocycle x y) (g : A.Cocycle x' y')
    (h₁ : x = x') (h₂ : y = y') (h : HEq f g) :
    (f : (show A.Comp from x) ⟶ (show A.Comp from y)) =
      (eqToHom (congrArg (fun t : A.Obj => (show A.Comp from t)) h₁) :
        (show A.Comp from x) ⟶ (show A.Comp from x')) ≫
        (g : (show A.Comp from x') ⟶ (show A.Comp from y')) ≫
        (eqToHom (congrArg (fun t : A.Obj => (show A.Comp from t)) h₂).symm :
          (show A.Comp from y') ⟶ (show A.Comp from y)) := by
  let _ : Category A.Obj := DGCategory.instCategoryComp A
  let _ : Category A.Comp := DGCategory.instCategoryComp A
  let h₁' : (show A.Comp from x) = (show A.Comp from x') :=
    congrArg (fun t : A.Obj => (show A.Comp from t)) h₁
  let h₂' : (show A.Comp from y) = (show A.Comp from y') :=
    congrArg (fun t : A.Obj => (show A.Comp from t)) h₂
  exact (CategoryTheory.conj_eqToHom_iff_heq
    (f := (f : (show A.Comp from x) ⟶ (show A.Comp from y)))
    (g := (g : (show A.Comp from x') ⟶ (show A.Comp from y'))) h₁' h₂').2 h

/-- Cocycles are heterogeneously equal as soon as their underlying morphisms are, along
equalities of their source and target objects. -/
theorem cocycle_heq_of_val_heq {x x' y y' : A.Obj}
    (f : A.Cocycle x y) (g : A.Cocycle x' y')
    (h₁ : x = x') (h₂ : y = y') (h : HEq f.1 g.1) : HEq f g := by
  cases h₁
  cases h₂
  exact heq_of_eq (Subtype.ext (eq_of_heq h))

private theorem dgOnComp_map_eqToHom
    (F : DGCategory.DGFunctor A A)
    {x y : A.Obj} (h : x = y) :
    F.onComp.map (eqToHom h : (show A.Comp from x) ⟶ (show A.Comp from y)) =
      (eqToHom (congrArg F.obj h) : (show A.Comp from F.obj x) ⟶
        (show A.Comp from F.obj y)) := by
  let _ : Category A.Obj := DGCategory.instCategoryComp A
  let _ : Category A.Comp := DGCategory.instCategoryComp A
  cases h
  apply Subtype.ext
  show F.map (A.id x) = A.id (F.obj x)
  rw [F.map_id]

private theorem eqToIso_hom_square {C : Type*} [Category C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    f ≫ (eqToIso hY).hom = (eqToIso hX).hom ≫ g := by
  cases hX
  cases hY
  cases h
  simp only [eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp]

private theorem eqToIso_hom_left_square {C : Type*} [Category C]
    {X X' Y : C} (hX : X = X') (f : X ⟶ Y) (g : X' ⟶ Y)
    (h : HEq f g) : f = (eqToIso hX).hom ≫ g := by
  cases hX
  cases h
  simp only [eqToIso.hom, eqToHom_refl, Category.id_comp]

/-- Associativity of the composition of three degree-zero morphisms of a differential graded
category. -/
theorem comp_assoc_zero {R : Type w} [CommRing R]
    {A : DGCategory.{v, u} R} {w₀ x y z : A.Obj}
    (e : A.Hom y z 0) (g : A.Hom x y 0) (f : A.Hom w₀ x 0) :
    A.comp (by omega : (0 : ℤ) + 0 = 0) e
      (A.comp (by omega : (0 : ℤ) + 0 = 0) g f) =
      A.comp (by omega : (0 : ℤ) + 0 = 0)
        (A.comp (by omega : (0 : ℤ) + 0 = 0) e g) f :=
  A.assoc (l := 0) (m := 0) (n := 0) (p := 0) (q := 0) (r := 0)
    (by lia) (by lia) (by lia) (by lia) e g f

/-- The differential of the retraction `π` of an admissible sequence is `-(δ b)`. -/
private theorem d_pi_eq_neg_connectingHom_comp {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d E.π = -A.comp (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom E) E.b.1 := by
  have hh := GradedSplitShortExact.connectingHom_comp E
  have hdneg : A.d (-E.π) = -A.d E.π := by
    rw [show (-E.π) = (-1 : R) • E.π by rw [neg_one_smul], A.d_smul, neg_one_smul]
  change A.comp (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom E) E.b.1 =
    A.d (-E.π) at hh
  rw [hdneg] at hh
  rw [hh]
  simp

/-- The map `a' π + s' q b` between the middle terms of two admissible sequences with the same
first term is closed, if `q` is closed and compatible with the connecting maps. -/
private theorem d_a_pi_add_s_q_b {x y y' z z' : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) (F : GradedSplitShortExact (A := A) x y' z')
    (q : A.Cocycle z z')
    (h : A.comp (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom F) q.1 =
      GradedSplitShortExact.connectingHom E) :
    A.d (A.comp (by lia : (0 : ℤ) + 0 = 0) F.a.1 E.π +
      A.comp (by lia : (0 : ℤ) + 0 = 0) F.s
        (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1)) = 0 := by
  have hδb : A.comp (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom F)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1) =
      A.comp (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom E) E.b.1 := by
    rw [← h]
    exact A.assoc (l := 1) (m := 0) (n := 0) (p := 0) (q := 1) (r := 1)
      (by lia) (by lia) (by lia) (by lia) _ q.1 E.b.1
  have hterm : A.comp (by lia : (1 : ℤ) + 0 = 1)
        (A.comp (by lia : (0 : ℤ) + 1 = 1) F.a.1 (GradedSplitShortExact.connectingHom F))
        (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1) =
      A.comp (by lia : (0 : ℤ) + 1 = 1) F.a.1
        (A.comp (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom E) E.b.1) := by
    rw [← hδb]
    exact (A.assoc (l := 0) (m := 1) (n := 0) (p := 1) (q := 1) (r := 1)
      (by lia) (by lia) (by lia) (by lia) _ _ _).symm
  simp only [A.d_add, Int.reduceAdd, A.leibniz, F.a.2, comp_zero_left, Int.natAbs_zero,
    pow_zero, d_pi_eq_neg_connectingHom_comp E, one_smul, zero_add,
    (GradedSplitShortExact.comp_connectingHom F).symm, q.2, E.b.2, comp_zero_right, smul_zero,
    add_zero]
  rw [hterm, show (-A.comp (by lia : (1 : ℤ) + 0 = 1) (GradedSplitShortExact.connectingHom E)
      E.b.1) = (-1 : R) • A.comp (by lia : (1 : ℤ) + 0 = 1)
        (GradedSplitShortExact.connectingHom E) E.b.1 by rw [neg_one_smul],
    A.comp_smul_right, neg_one_smul]
  abel

/-- If `q' q = 1`, then `(a π' + s q' b')(a' π + s' q b) = 1` for two admissible sequences with
the same first term. -/
private theorem a_pi_add_s_q_b_comp_eq_id {x y y' z z' : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) (F : GradedSplitShortExact (A := A) x y' z')
    (q : A.Hom z z' 0) (q' : A.Hom z' z 0)
    (h : A.comp (by lia : (0 : ℤ) + 0 = 0) q' q = A.id z) :
    A.comp (by lia : (0 : ℤ) + 0 = 0)
      (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1 F.π +
        A.comp (by lia : (0 : ℤ) + 0 = 0) E.s (A.comp (by lia : (0 : ℤ) + 0 = 0) q' F.b.1))
      (A.comp (by lia : (0 : ℤ) + 0 = 0) F.a.1 E.π +
        A.comp (by lia : (0 : ℤ) + 0 = 0) F.s (A.comp (by lia : (0 : ℤ) + 0 = 0) q E.b.1)) =
      A.id y := by
  have hFba := GradedSplitShortExact.comp_zero F
  have hTerm1 : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1 F.π)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) F.a.1 E.π) =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1 E.π := by
    rw [← comp_assoc_zero E.a.1 F.π _, comp_assoc_zero F.π F.a.1 E.π, F.π_a, A.id_comp]
  have hTerm2 : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1 F.π)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) F.s
          (A.comp (by lia : (0 : ℤ) + 0 = 0) q E.b.1)) = 0 := by
    rw [← comp_assoc_zero E.a.1 F.π _, comp_assoc_zero F.π F.s _, F.π_s]
    simp
  have hTerm3 : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.s
          (A.comp (by lia : (0 : ℤ) + 0 = 0) q' F.b.1))
        (A.comp (by lia : (0 : ℤ) + 0 = 0) F.a.1 E.π) = 0 := by
    rw [← comp_assoc_zero E.s _ _, ← comp_assoc_zero q' F.b.1 _,
      comp_assoc_zero F.b.1 F.a.1 E.π, hFba]
    simp
  have hTerm4 : A.comp (by lia : (0 : ℤ) + 0 = 0)
        (A.comp (by lia : (0 : ℤ) + 0 = 0) E.s
          (A.comp (by lia : (0 : ℤ) + 0 = 0) q' F.b.1))
        (A.comp (by lia : (0 : ℤ) + 0 = 0) F.s
          (A.comp (by lia : (0 : ℤ) + 0 = 0) q E.b.1)) =
      A.comp (by lia : (0 : ℤ) + 0 = 0) E.s E.b.1 := by
    rw [← comp_assoc_zero E.s _ _, ← comp_assoc_zero q' F.b.1 _,
      comp_assoc_zero F.b.1 F.s _, F.b_s, A.id_comp,
      comp_assoc_zero q' q E.b.1, h, A.id_comp]
  simp only [A.comp_add_left, A.comp_add_right]
  rw [hTerm1, hTerm2, hTerm3, hTerm4]
  simpa using E.a_π_add_s_b

/-- The canonical map from an object to its desuspension followed by suspension. -/
def resuspension (S : ShiftAxiomB A) (z : A.Obj) :
    let _ : HasShift A.K ℤ := S.kShift
    (show A.K from z) ⟶
      (show A.K from (S.shiftFunctor (-1)).obj z)⟦(1 : ℤ)⟧ := by
  let _ : HasShift A.K ℤ := S.kShift
  have h : (shiftFunctor A.K (-1)).obj z = (S.shiftFunctor (-1)).obj z :=
    congrArg (fun F : A.K ⥤ A.K => F.obj z) (S.kShift_functor (-1))
  exact (shiftEquiv A.K (1 : ℤ)).counitIso.inv.app z ≫ (eqToHom h)⟦(1 : ℤ)⟧'

/-- The rotated triangle associated to an admissible short exact sequence. -/
def rotatedAssociatedTriangle (C : ConeSituation A)
    {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := C.shift.kShift
    Pretriangulated.Triangle A.K := by
  letI : HasShift A.K ℤ := C.shift.kShift
  exact Pretriangulated.Triangle.mk
    (Quotient.mk (A.homotopySetoid _ _) (GradedSplitShortExact.shiftedConnecting C.shift E))
    (Quotient.mk (A.homotopySetoid _ _) E.a)
    ((Quotient.mk (A.homotopySetoid _ _) E.b) ≫ resuspension C.shift z)

/-- The cone triangle of the desuspended connecting map. -/
def connectingConeTriangle (C : ConeSituation A)
    {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := C.shift.kShift
    Pretriangulated.Triangle A.K := by
  letI : HasShift A.K ℤ := C.shift.kShift
  let f := GradedSplitShortExact.shiftedConnecting C.shift E
  have hz : (C.shift.shiftFunctor 1).obj ((C.shift.shiftFunctor (-1)).obj z) = z := by
    calc
      (C.shift.shiftFunctor 1).obj ((C.shift.shiftFunctor (-1)).obj z) =
          (C.shift.shiftFunctor (1 + -1)).obj z := (C.shift.add_obj 1 (-1) z).symm
      _ = (C.shift.shiftFunctor 0).obj z := by norm_num
      _ = z := C.shift.zero_obj z
  exact Pretriangulated.Triangle.mk
    (Quotient.mk (A.homotopySetoid _ _) f)
    (Quotient.mk (A.homotopySetoid _ _) (C.coneSequence f).a)
    ((Quotient.mk (A.homotopySetoid _ _) (C.coneSequence f).b) ≫
      eqToHom hz ≫ resuspension C.shift z)

/-- The rotated triangle of an admissible sequence is isomorphic to the cone
triangle of its desuspended connecting map. -/
@[stacks 09QS]
theorem rotatedAssociatedTriangle_iso_connectingConeTriangle
    (C : ConeSituation A) {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := C.shift.kShift
    Nonempty (rotatedAssociatedTriangle C E ≅ connectingConeTriangle C E) := by
  classical
  let _ : Category A.Obj := DGCategory.instCategoryComp A
  let _ : Category A.Comp := DGCategory.instCategoryComp A
  let S := C.shift
  let w := (S.shiftFunctor (-1)).obj z
  let z₁ := (S.shiftFunctor 1).obj w
  let x₁ := (S.shiftFunctor 1).obj x
  let x₀ := (S.shiftFunctor (-1)).obj x₁
  have hz : z₁ = z := by
    dsimp [z₁, w]
    calc
      (S.shiftFunctor 1).obj ((S.shiftFunctor (-1)).obj z) =
          (S.shiftFunctor (1 + -1)).obj z := (S.add_obj 1 (-1) z).symm
      _ = (S.shiftFunctor 0).obj z := by norm_num
      _ = z := S.zero_obj z
  have hx : x₀ = x := by
    dsimp [x₀, x₁]
    have h := S.add_obj (-1) 1 x
    simpa only [neg_add_cancel_left] using h.symm.trans (S.zero_obj x)
  have ht : (S.shiftFunctor 1).obj x₀ = (S.shiftFunctor 1).obj x :=
    congrArg (fun t => (S.shiftFunctor 1).obj t) hx
  have hzComp : (show A.Comp from z₁) = (show A.Comp from z) :=
    congrArg (fun t : A.Obj => (show A.Comp from t)) hz
  have hzK : (show A.K from z₁) = (show A.K from z) :=
    congrArg (fun t : A.Obj => (show A.K from t)) hz
  have hxComp : (show A.Comp from x₀) = (show A.Comp from x) :=
    congrArg (fun t : A.Obj => (show A.Comp from t)) hx.symm |>.symm
  have htComp : (show A.Comp from (S.shiftFunctor 1).obj x₀) =
      (show A.Comp from (S.shiftFunctor 1).obj x) :=
    congrArg (fun t : A.Obj => (show A.Comp from t)) ht
  let q : A.Cocycle z z₁ :=
    (eqToHom hzComp.symm : (show A.Comp from z) ⟶ (show A.Comp from z₁))
  let qinv : A.Cocycle z₁ z :=
    (eqToHom hzComp : (show A.Comp from z₁) ⟶ (show A.Comp from z))
  let f : A.Cocycle w x := GradedSplitShortExact.shiftedConnecting S E
  let g := GradedSplitShortExact.connectingCocycle S E
  let F := C.coneSequence f
  let δ := GradedSplitShortExact.connectingHom E
  let δ' := GradedSplitShortExact.connectingHom F
  have hδ : A.comp (by lia : (1 : ℤ) + 0 = 1) δ' q.1 = δ := by
    apply (S.toShift 1 z x 0).injective
    have hcomp' : (S.toShift 1 z x 0)
        (A.comp (by lia : (1 : ℤ) + 0 = 1) δ' q.1) =
        A.comp (by lia : (0 : ℤ) + 0 = 0) ((S.toShift 1 z₁ x 0) δ') q.1 := by
      simpa using S.toShift_comp_right (n := 1) (x := z) (y := z₁)
        (z := x) (l := 0) (m := 0) δ' q.1
    rw [hcomp']
    show A.comp (by lia : (0 : ℤ) + 0 = 0)
        ((S.toShift 1 z₁ x 0) δ') q.1 = (S.toShift 1 z x 0) δ
    rw [show (S.toShift 1 z₁ x 0) δ' =
        (S.shiftFunctor 1).map f.1 by
          exact congrArg Subtype.val (C.cone_connecting f)]
    let FMinus := (S.shiftFunctor (-1)).onComp
    let FPlus := (S.shiftFunctor 1).onComp
    let fMinus : (show A.Comp from w) ⟶ (show A.Comp from x₀) := FMinus.map g
    have hf : (f : (show A.Comp from w) ⟶ (show A.Comp from x)) =
        fMinus ≫ eqToHom hxComp := by
      have htransport := cocycle_eq_transport_of_val_heq f fMinus rfl hx.symm (by
        dsimp [f, GradedSplitShortExact.shiftedConnecting]
        exact eqRec_heq _ _)
      have hleft :
          congrArg (fun t : A.Obj => (show A.Comp from t)) (rfl : w = w) = rfl :=
        Subsingleton.elim _ _
      rw [hleft, eqToHom_refl, Category.id_comp] at htransport
      exact htransport
    have hmap₂ : HEq
        ((S.shiftFunctor 1).map ((S.shiftFunctor (-1)).map g.1)) g.1 := by
      exact (S.add_map 1 (-1) g.1).symm.trans (S.zero_map g.1)
    let m₀ : A.Cocycle z₁ ((S.shiftFunctor 1).obj x₀) := FPlus.map fMinus
    have hmap₂' : HEq m₀.1 g.1 := by
      dsimp [m₀, FPlus, FMinus, fMinus, DGCategory.DGFunctor.onComp]
      show HEq ((S.shiftFunctor 1).map ((S.shiftFunctor (-1)).map g.1)) g.1
      exact hmap₂
    have hm₀heq : HEq m₀ g := cocycle_heq_of_val_heq m₀ g hz ht hmap₂'
    have hm₀ : (m₀ : (show A.Comp from z₁) ⟶
        (show A.Comp from (S.shiftFunctor 1).obj x₀)) =
        (eqToHom hzComp : (show A.Comp from z₁) ⟶ (show A.Comp from z)) ≫
        (g : (show A.Comp from z) ⟶ (show A.Comp from (S.shiftFunctor 1).obj x)) ≫
          (eqToHom htComp.symm :
            (show A.Comp from (S.shiftFunctor 1).obj x) ⟶
              (show A.Comp from (S.shiftFunctor 1).obj x₀)) :=
      cocycle_eq_transport_of_val_heq m₀ g hz ht hm₀heq
    let m : (show A.Comp from z₁) ⟶
        (show A.Comp from (S.shiftFunctor 1).obj x) := FPlus.map f
    have hmapcomp : FPlus.map (fMinus ≫ eqToHom hxComp) =
        FPlus.map fMinus ≫ FPlus.map (eqToHom hxComp) :=
      FPlus.map_comp fMinus (eqToHom hxComp)
    have hmStart : m = FPlus.map fMinus ≫ FPlus.map (eqToHom hxComp) := by
      show FPlus.map f = _
      rw [hf, hmapcomp]
    have hmStep : FPlus.map fMinus ≫ FPlus.map (eqToHom hxComp) =
        m₀ ≫ eqToHom ht := by
      rw [dgOnComp_map_eqToHom (S.shiftFunctor 1) hx]
      rfl
    have hmStart₂ : m = m₀ ≫ eqToHom ht := hmStart.trans hmStep
    have hht : htComp = ht := Subsingleton.elim _ _
    have hm' : m = qinv ≫ (g : (show A.Comp from z) ⟶
        (show A.Comp from (S.shiftFunctor 1).obj x)) := by
      calc
        m = m₀ ≫ eqToHom ht := hmStart₂
        _ = ((eqToHom hzComp : (show A.Comp from z₁) ⟶ (show A.Comp from z)) ≫
          (g : (show A.Comp from z) ⟶ (show A.Comp from (S.shiftFunctor 1).obj x)) ≫
          (eqToHom htComp.symm :
            (show A.Comp from (S.shiftFunctor 1).obj x) ⟶
              (show A.Comp from (S.shiftFunctor 1).obj x₀))) ≫
              (eqToHom htComp :
                (show A.Comp from (S.shiftFunctor 1).obj x₀) ⟶
                  (show A.Comp from (S.shiftFunctor 1).obj x)) := by
            rw [hm₀, hht]
            rfl
        _ = qinv ≫ g := by
          have hcancel :
              (eqToHom htComp.symm :
                (show A.Comp from (S.shiftFunctor 1).obj x) ⟶
                  (show A.Comp from (S.shiftFunctor 1).obj x₀)) ≫
              (eqToHom htComp :
                (show A.Comp from (S.shiftFunctor 1).obj x₀) ⟶
                  (show A.Comp from (S.shiftFunctor 1).obj x)) =
              𝟙 (show A.Comp from (S.shiftFunctor 1).obj x) := by
            rw [eqToHom_trans]
            have hp : htComp.symm.trans htComp = rfl := Subsingleton.elim _ _
            rw [hp, eqToHom_refl]
          let aHom : (show A.Comp from z₁) ⟶ (show A.Comp from z) := eqToHom hzComp
          let bHom : (show A.Comp from z) ⟶
              (show A.Comp from (S.shiftFunctor 1).obj x) := g
          let cHom : (show A.Comp from (S.shiftFunctor 1).obj x) ⟶
              (show A.Comp from (S.shiftFunctor 1).obj x₀) := eqToHom htComp.symm
          let dHom : (show A.Comp from (S.shiftFunctor 1).obj x₀) ⟶
              (show A.Comp from (S.shiftFunctor 1).obj x) := eqToHom htComp
          calc
            _ = aHom ≫ ((bHom ≫ cHom) ≫ dHom) :=
              Category.assoc (self := (inferInstance : Category A.Comp)) aHom
                (bHom ≫ cHom) dHom
            _ = aHom ≫ (bHom ≫ (cHom ≫ dHom)) :=
              congrArg (fun t => aHom ≫ t)
                (Category.assoc (self := (inferInstance : Category A.Comp)) bHom cHom dHom)
            _ = (aHom ≫ bHom) ≫ (cHom ≫ dHom) :=
              (Category.assoc (self := (inferInstance : Category A.Comp)) aHom bHom
                (cHom ≫ dHom)).symm
            _ = aHom ≫ bHom := by
              rw [hcancel]
              exact Category.comp_id (self := (inferInstance : Category A.Comp)) _
            _ = qinv ≫ g := rfl
    have hcat : q ≫ m = (g : (show A.Comp from z) ⟶
        (show A.Comp from (S.shiftFunctor 1).obj x)) := by
      have hqq : q ≫ qinv = (𝟙 (show A.Comp from z)) := by
        show eqToHom hzComp.symm ≫ eqToHom hzComp = 𝟙 (show A.Comp from z)
        rw [eqToHom_trans]
        have hp : hzComp.symm.trans hzComp = rfl := Subsingleton.elim _ _
        rw [hp, eqToHom_refl]
      calc
        q ≫ m = q ≫ (qinv ≫ g) := congrArg (fun t => q ≫ t) hm'
        _ = (q ≫ qinv) ≫ g :=
          (Category.assoc (self := (inferInstance : Category A.Comp))
            (q : (show A.Comp from z) ⟶ (show A.Comp from z₁))
            (qinv : (show A.Comp from z₁) ⟶ (show A.Comp from z))
            (g : (show A.Comp from z) ⟶ (show A.Comp from (S.shiftFunctor 1).obj x))).symm
        _ = (𝟙 (show A.Comp from z)) ≫ g := by rw [hqq]
        _ = g := by
          exact Category.id_comp (self := (inferInstance : Category A.Comp))
            (g : (show A.Comp from z) ⟶ (show A.Comp from (S.shiftFunctor 1).obj x))
    show A.comp (by lia : (0 : ℤ) + 0 = 0)
        ((S.shiftFunctor 1).map f.1) q.1 =
      (S.toShift 1 z x 0) δ
    have hval := congrArg (fun h : (show A.Comp from z) ⟶
      (show A.Comp from (S.shiftFunctor 1).obj x) => h.1) hcat
    change A.comp (by lia : (0 : ℤ) + 0 = 0)
        ((S.shiftFunctor 1).map f.1) q.1 =
      (S.toShift 1 z x 0) δ at hval
    simpa [g, GradedSplitShortExact.connectingCocycle] using hval
  let uVal : A.Hom y (C.cone f) 0 :=
      A.comp (by lia : (0 : ℤ) + 0 = 0) F.a.1 E.π +
      A.comp (by lia : (0 : ℤ) + 0 = 0) F.s
        (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1)
  have huClosed : A.d uVal = 0 := d_a_pi_add_s_q_b E F q hδ
  let u : A.Cocycle y (C.cone f) := ⟨uVal, huClosed⟩
  have hqinvq : A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 qinv.1 = A.id z₁ := by
    have hc : qinv ≫ q = 𝟙 (show A.Comp from z₁) := by
      show eqToHom hzComp ≫ eqToHom hzComp.symm = 𝟙 _
      rw [eqToHom_trans]
      have hp : hzComp.trans hzComp.symm = rfl := Subsingleton.elim _ _
      rw [hp, eqToHom_refl]
    exact congrArg (fun k : (show A.Comp from z₁) ⟶ (show A.Comp from z₁) => k.1) hc
  have hδinv : A.comp (by lia : (1 : ℤ) + 0 = 1) δ qinv.1 = δ' := by
    calc
      _ = A.comp (by lia : (1 : ℤ) + 0 = 1) δ'
          (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 qinv.1) := by
            rw [← hδ]
            exact (A.assoc (l := 1) (m := 0) (n := 0) (p := 0) (q := 1) (r := 1)
              (by lia) (by lia) (by lia) (by lia) δ' q.1 qinv.1).symm
      _ = _ := by rw [hqinvq, A.comp_id]
  let vVal : A.Hom (C.cone f) y 0 :=
    A.comp (by lia : (0 : ℤ) + 0 = 0) E.a.1 F.π +
      A.comp (by lia : (0 : ℤ) + 0 = 0) E.s
        (A.comp (by lia : (0 : ℤ) + 0 = 0) qinv.1 F.b.1)
  have hvClosed : A.d vVal = 0 := d_a_pi_add_s_q_b F E qinv hδinv
  let v : A.Cocycle (C.cone f) y := ⟨vVal, hvClosed⟩
  have hqqRaw : A.comp (by lia : (0 : ℤ) + 0 = 0) qinv.1 q.1 = A.id z := by
    have hc : q ≫ qinv = 𝟙 (show A.Comp from z) := by
      show eqToHom hzComp.symm ≫ eqToHom hzComp = 𝟙 _
      rw [eqToHom_trans]
      have hp : hzComp.symm.trans hzComp = rfl := Subsingleton.elim _ _
      rw [hp, eqToHom_refl]
    exact congrArg (fun k : (show A.Comp from z) ⟶ (show A.Comp from z) => k.1) hc
  have hEba := GradedSplitShortExact.comp_zero E
  have hFba := GradedSplitShortExact.comp_zero F
  have hvuRaw : A.comp (by lia : (0 : ℤ) + 0 = 0) vVal uVal = A.id y :=
    a_pi_add_s_q_b_comp_eq_id E F q.1 qinv.1 hqqRaw
  have huvRaw : A.comp (by lia : (0 : ℤ) + 0 = 0) uVal vVal = A.id (C.cone f) :=
    a_pi_add_s_q_b_comp_eq_id F E qinv.1 q.1 hqinvq
  have hUA : A.comp (by lia : (0 : ℤ) + 0 = 0) uVal E.a.1 = F.a.1 := by
    dsimp [uVal]
    rw [A.comp_add_left, ← comp_assoc_zero F.a.1 E.π E.a.1, E.π_a, A.comp_id,
      comp_assoc_zero F.s q.1 E.b.1,
      ← comp_assoc_zero (A.comp (by lia : (0 : ℤ) + 0 = 0) F.s q.1) E.b.1 E.a.1,
      ← comp_assoc_zero F.s q.1 _, hEba]
    simp
  have hUB : A.comp (by lia : (0 : ℤ) + 0 = 0) F.b.1 uVal =
      A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1 := by
    dsimp [uVal]
    rw [A.comp_add_right]
    have h1 : A.comp (by lia : (0 : ℤ) + 0 = 0) F.b.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) F.a.1 E.π) = 0 := by
      calc
        _ = A.comp (by lia : (0 : ℤ) + 0 = 0)
            (A.comp (by lia : (0 : ℤ) + 0 = 0) F.b.1 F.a.1) E.π :=
          comp_assoc_zero F.b.1 F.a.1 E.π
        _ = 0 := by rw [hFba]; simp
    have h2 : A.comp (by lia : (0 : ℤ) + 0 = 0) F.b.1
        (A.comp (by lia : (0 : ℤ) + 0 = 0) F.s
          (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1)) =
        A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1 := by
      calc
        _ = A.comp (by lia : (0 : ℤ) + 0 = 0)
            (A.comp (by lia : (0 : ℤ) + 0 = 0) F.b.1 F.s)
            (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1) :=
          comp_assoc_zero F.b.1 F.s (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1)
        _ = _ := by rw [F.b_s, A.id_comp]
    rw [h1, h2]
    simp
  have htermUB : A.comp (by lia : (0 : ℤ) + 0 = 0) qinv.1
      (A.comp (by lia : (0 : ℤ) + 0 = 0) F.b.1 uVal) = E.b.1 := by
    calc
      _ = A.comp (by lia : (0 : ℤ) + 0 = 0) qinv.1
          (A.comp (by lia : (0 : ℤ) + 0 = 0) q.1 E.b.1) := congrArg
            (fun t => A.comp (by lia : (0 : ℤ) + 0 = 0) qinv.1 t) hUB
      _ = A.comp (by lia : (0 : ℤ) + 0 = 0)
          (A.comp (by lia : (0 : ℤ) + 0 = 0) qinv.1 q.1) E.b.1 :=
        comp_assoc_zero qinv.1 q.1 E.b.1
      _ = _ := by rw [hqqRaw, A.id_comp]
  let _ : Category A.Obj := DGCategory.instCategoryK A
  let _ : Category A.K := DGCategory.instCategoryK A
  let _ : HasShift A.K ℤ := S.kShift
  let e : (show A.K from y) ≅ (show A.K from C.cone f) := {
    hom := (DGCategory.compToK A).map u
    inv := (DGCategory.compToK A).map v
    hom_inv_id := by
      show Quotient.mk _ (A.compCocycle v u) = Quotient.mk _
        (⟨A.id y, A.d_id y⟩ : A.Cocycle y y)
      exact congrArg (Quotient.mk _) (Subtype.ext hvuRaw)
    inv_hom_id := by
      show Quotient.mk _ (A.compCocycle u v) = Quotient.mk _
        (⟨A.id (C.cone f), A.d_id (C.cone f)⟩ : A.Cocycle (C.cone f) (C.cone f))
      exact congrArg (Quotient.mk _) (Subtype.ext huvRaw)
  }
  have hobj₁ : (rotatedAssociatedTriangle C E).obj₁ =
      (connectingConeTriangle C E).obj₁ := rfl
  have hobj₂ : (rotatedAssociatedTriangle C E).obj₂ =
      (connectingConeTriangle C E).obj₂ := rfl
  refine ⟨Pretriangulated.Triangle.isoMk _ _
    (Iso.refl (show A.K from w)) (Iso.refl (show A.K from x)) e ?_ ?_ ?_⟩
  · have hi₁ : (Iso.refl (show A.K from w)).hom = (eqToIso hobj₁).hom := rfl
    have hi₂ : (Iso.refl (show A.K from x)).hom = (eqToIso hobj₂).hom := rfl
    rw [hi₁, hi₂]
    apply eqToIso_hom_square hobj₁ hobj₂
    rfl
  · have hUA_K : (DGCategory.compToK A).map E.a ≫ (DGCategory.compToK A).map u =
        (DGCategory.compToK A).map F.a := by
      show Quotient.mk _ (A.compCocycle u E.a) = Quotient.mk _ F.a
      exact congrArg (Quotient.mk _) (Subtype.ext hUA)
    have hi₂ : (Iso.refl (show A.K from x)).hom = (eqToIso hobj₂).hom := rfl
    rw [hi₂]
    apply eqToIso_hom_left_square hobj₂ _ _
    show HEq ((DGCategory.compToK A).map E.a ≫ (DGCategory.compToK A).map u)
      ((DGCategory.compToK A).map F.a)
    exact heq_of_eq hUA_K
  · have htermK :
        ((DGCategory.compToK A).map u ≫ (DGCategory.compToK A).map F.b) ≫
          (DGCategory.compToK A).map qinv = (DGCategory.compToK A).map E.b := by
      show Quotient.mk _ (A.compCocycle qinv (A.compCocycle F.b u)) = Quotient.mk _ E.b
      exact congrArg (Quotient.mk _) (Subtype.ext htermUB)
    have hqinvK : (DGCategory.compToK A).map qinv =
        (eqToHom hzK : (show A.K from z₁) ⟶ (show A.K from z)) := by
      show (DGCategory.compToK A).map (eqToHom hzComp) = _
      rw [eqToHom_map]
      congr 1
    have hbefore :
        (DGCategory.compToK A).map u ≫ (DGCategory.compToK A).map F.b ≫
          (eqToHom hzK : (show A.K from z₁) ⟶ (show A.K from z)) =
          (DGCategory.compToK A).map E.b := by
      rw [← hqinvK]
      exact (Category.assoc (self := (inferInstance : Category A.K))
        ((DGCategory.compToK A).map u) ((DGCategory.compToK A).map F.b)
        ((DGCategory.compToK A).map qinv)).symm.trans htermK
    have hres := congrArg (fun g => g ≫ resuspension C.shift z) hbefore
    have hleft : (rotatedAssociatedTriangle C E).mor₃ =
        (DGCategory.compToK A).map E.b ≫ resuspension C.shift z := rfl
    have hright : (connectingConeTriangle C E).mor₃ =
        (DGCategory.compToK A).map F.b ≫
          (eqToHom hzK : (show A.K from z₁) ⟶ (show A.K from z)) ≫
            resuspension C.shift z := rfl
    have hid₁ : (Iso.refl (show A.K from w)).hom = 𝟙 (show A.K from w) := rfl
    rw [hleft, hright, hid₁]
    calc
      _ = ((DGCategory.compToK A).map E.b ≫ resuspension C.shift z) ≫
          (shiftFunctor A.K (1 : ℤ)).map (𝟙 (show A.K from w)) := rfl
      _ = (DGCategory.compToK A).map E.b ≫ resuspension C.shift z := by
        rw [(shiftFunctor A.K (1 : ℤ)).map_id (show A.K from w), Category.comp_id]
      _ = _ := by
        rw [show e.hom = (DGCategory.compToK A).map u by rfl]
        have hassoc :
            ((DGCategory.compToK A).map u ≫ (DGCategory.compToK A).map F.b ≫
              eqToHom hzK) ≫ resuspension C.shift z =
              (DGCategory.compToK A).map u ≫ (DGCategory.compToK A).map F.b ≫
                eqToHom hzK ≫ resuspension C.shift z := by
          rw [Category.assoc, Category.assoc]
        exact hres.symm.trans hassoc

end DGCategory
