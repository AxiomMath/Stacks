module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDirectSum
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexGradedSplit
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftAxiomBIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituationIso

/-!
# Axioms (A), (B) and (C) for the differential graded category of complexes

The cone of a map of complexes `φ : x ⟶ y` sits in a degreewise split short exact sequence
`y ⟶ c(φ) ⟶ x[1]`, namely the rotation of Mathlib's cone triangle, and a degreewise split short
exact sequence of complexes is a graded-split short exact sequence of
`CochainComplex.dgCategory B` — that is `CochainComplex.gradedSplitOfDegreewiseSplit`. Together
with axiom (A) and the isomorphism-valued axiom (B) this is the cone situation of Tag 09QJ for the
differential graded category of complexes, the `C` of Tag 09LK.

One sign has to be fixed. Axiom (C) asks that the connecting arrow of the chosen sequence be
`φ[1]`, while Mathlib's rotation of the cone triangle has third arrow `-φ[1]`: its splitting
produces the connecting cocycle `-φ`, which is
`CochainComplex.mappingCone.cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v`. The
correction is made in the differential graded language rather than in Mathlib's, by
`DGCategory.GradedSplitShortExact.negSurjection`: negating the surjection of a graded-split short
exact sequence together with its section gives another one — every identity a splitting asks for
has the two negations cancelling — and negates the connecting morphism.

## Main definitions

* `DGCategory.GradedSplitShortExact.negSurjection`: a graded-split short exact sequence with its
  surjection and section negated.
* `CochainComplex.dgCone` and `CochainComplex.dgConeSequence`: the cone of a closed degree-zero
  morphism of `CochainComplex.dgCategory B` and its graded-split short exact sequence.
* `CochainComplex.dgConeSituationIso`: **axioms (A), (B) and (C) for the differential graded
  category of complexes, with the shift additive on objects up to isomorphism.**

## Main results

* `DGCategory.GradedSplitShortExact.connectingHom_negSurjection`: the connecting morphism of the
  negated sequence is the negative of the original one.
* `CochainComplex.rightShift_connectingHom_coneSequence`: the connecting arrow of the cone
  sequence, read as a closed degree-zero morphism `x[1] ⟶ y[1]`, is the shift of `φ`. This is
  axiom (C)'s condition, and the place the sign correction is cashed in.

## Implementation notes

`CochainComplex.dgConeSequence` is stated with
`CategoryTheory.shiftFunctor (CochainComplex B ℤ) 1` rather than
`CochainComplex.dgShiftFunctor B 1`, which are equal only by unfolding a semireducible
definition. The fields of the structure are then discharged by `exact`, crossing that gap once at
default transparency; rewriting across it inside a tactic block does not typecheck. This is the
same discipline as in
`StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftAxiomBIso`.

## References

* [Stacks Project, Tag 09QJ](https://stacks.math.columbia.edu/tag/09QJ), axiom (C);
  [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axioms (A) and (B);
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded category of
  complexes; [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace DGCategory.GradedSplitShortExact

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- A homogeneous morphism composed with the negative of another. -/
alias comp_neg_left := comp_neg_first

/-- The negative of a homogeneous morphism composed with another. -/
theorem comp_neg_right {x y z : A.Obj} {m n k : ℤ} (h : m + n = k)
    (g : A.Hom y z m) (f : A.Hom x y n) : A.comp h g (-f) = -A.comp h g f := by
  rw [show -f = (-1 : R) • f from (neg_one_smul R f).symm, A.comp_smul_right, neg_one_smul]

/-- The Hom differential is additive, hence commutes with negation. -/
theorem d_neg {x y : A.Obj} {n : ℤ} (f : A.Hom x y n) : A.d (-f) = -A.d f := by
  rw [show -f = (-1 : R) • f from (neg_one_smul R f).symm, A.d_smul, neg_one_smul]

/-- **A graded-split short exact sequence with its surjection and its section negated.** It is
again one: in each of the four identities the two negations cancel. -/
def negSurjection {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact (A := A) x y z where
  a := E.a
  b := ⟨-E.b.1, by rw [d_neg, E.b.2, neg_zero]⟩
  π := E.π
  s := -E.s
  π_a := E.π_a
  b_s := by
    change A.comp (by omega : (0 : ℤ) + 0 = 0) (-E.b.1) (-E.s) = A.id z
    rw [comp_neg_left, comp_neg_right, neg_neg, E.b_s]
  π_s := by
    change A.comp (by omega : (0 : ℤ) + 0 = 0) E.π (-E.s) = 0
    rw [comp_neg_right, E.π_s, neg_zero]
  a_π_add_s_b := by
    change A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 E.π +
      A.comp (by omega : (0 : ℤ) + 0 = 0) (-E.s) (-E.b.1) = A.id y
    rw [comp_neg_left, comp_neg_right, neg_neg, E.a_π_add_s_b]

/-- **The connecting morphism of the negated sequence is the negative of the original one.** The
connecting morphism is `π d(s)`, and only `s` has changed sign. -/
theorem connectingHom_negSurjection {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    connectingHom E.negSurjection = -connectingHom E := by
  show A.comp (by omega : (0 : ℤ) + (0 + 1) = 1) E.π (A.d (-E.s)) = -connectingHom E
  rw [d_neg, comp_neg_right]
  rfl

end DGCategory.GradedSplitShortExact

universe v u

namespace CochainComplex

open CochainComplex.HomComplex HomologicalComplex

variable {B : Type u} [Category.{v} B] [Preadditive B] [HasBinaryBiproducts B]

/-- **The graded-split short exact sequence `y ⟶ c(φ) ⟶ x[1]` of the cone of a map of
complexes**: the rotation of Mathlib's cone triangle, with its surjection and section negated so
that the connecting arrow comes out as `+φ` and not `-φ`. -/
noncomputable def coneGradedSplit {X Y : CochainComplex B ℤ} (φ : X ⟶ Y) :
    DGCategory.GradedSplitShortExact (A := dgCategory B) Y (mappingCone φ)
      ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).obj X) :=
  (gradedSplitOfDegreewiseSplit (mappingCone.triangleRotateShortComplex φ)
    (mappingCone.triangleRotateShortComplexSplitting φ)).negSurjection

/-- **The components of the connecting morphism of the cone sequence are those of `φ`**, the
minus sign of Mathlib's rotation having been cancelled by `negSurjection`. -/
theorem connectingHom_coneGradedSplit_v {X Y : CochainComplex B ℤ} (φ : X ⟶ Y) (p : ℤ) :
    (DGCategory.GradedSplitShortExact.connectingHom (coneGradedSplit φ)).v p (p + 1) rfl =
      φ.f (p + 1) := by
  have h2 := Cochain.congr_v
    ((DGCategory.GradedSplitShortExact.connectingHom_negSurjection
        (gradedSplitOfDegreewiseSplit (mappingCone.triangleRotateShortComplex φ)
          (mappingCone.triangleRotateShortComplexSplitting φ))).trans
      (congrArg Neg.neg (connectingHom_gradedSplitOfDegreewiseSplit _ _))) p (p + 1) rfl
  rw [Cochain.neg_v,
    mappingCone.cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v] at h2
  exact h2.trans (neg_neg _)

/-- **The connecting arrow of the cone sequence, read as a closed degree-zero morphism
`x[1] ⟶ y[1]`, is the shift of `φ`.** This is the condition of axiom (C). -/
theorem rightShift_connectingHom_coneSequence {X Y : CochainComplex B ℤ} (φ : X ⟶ Y) :
    (DGCategory.GradedSplitShortExact.connectingHom (coneGradedSplit φ)).rightShift 1 0 rfl =
      (Cochain.ofHom φ).shift 1 := by
  ext p
  rw [Cochain.rightShift_v _ 1 0 rfl p p (add_zero p) (p + 1) rfl,
    connectingHom_coneGradedSplit_v, (Cochain.ofHom φ).shift_v' 1 p p (add_zero p),
    Cochain.ofHom_v]
  simp

/-- **The cone of a closed degree-zero morphism of the differential graded category of
complexes**: Mathlib's mapping cone of the underlying map of complexes. -/
noncomputable def dgCone {x y : CochainComplex B ℤ} (f : (dgCategory B).Cocycle x y) :
    CochainComplex B ℤ :=
  mappingCone (Cocycle.homOf f)

/-- **The graded-split short exact sequence `y ⟶ c(f) ⟶ x[1]` of the cone.** -/
noncomputable def dgConeSequence {x y : CochainComplex B ℤ} (f : (dgCategory B).Cocycle x y) :
    DGCategory.GradedSplitShortExact (A := dgCategory B) y (dgCone f)
      ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).obj x) :=
  coneGradedSplit (Cocycle.homOf f)

/-- The condition of axiom (C) for `CochainComplex.dgConeSequence`, with the Koszul sign of the
differential graded shift in degree zero made explicit. -/
theorem dgCone_connecting {x y : CochainComplex B ℤ} (f : (dgCategory B).Cocycle x y) :
    (DGCategory.GradedSplitShortExact.connectingHom (dgConeSequence f)).rightShift 1 0 rfl =
      ((1 : ℤ) * 0).negOnePow • (f.1.shift 1) := by
  rw [mul_zero, Int.negOnePow_zero, one_smul,
    show f.1 = Cochain.ofHom (Cocycle.homOf f) from
      (congrArg Subtype.val (Cocycle.ofHom_homOf_eq_self f)).symm]
  exact rightShift_connectingHom_coneSequence (Cocycle.homOf f)

/-- **Axioms (A), (B) and (C) for the differential graded category of complexes, with the shift
additive on objects only up to isomorphism.** This is the cone situation of Tag 09QJ for the `C`
of Tag 09LK. -/
noncomputable def dgConeSituationIso (B : Type u) [Category.{v} B] [Preadditive B]
    [HasZeroObject B] [HasBinaryBiproducts B] :
    DGCategory.ConeSituationIso (dgCategory B) where
  directSum := dgDirectSumAxiomA B
  shift := dgShiftAxiomBIso B
  cone := by intro x y f; exact dgCone f
  coneSequence := by intro x y f; exact dgConeSequence f
  cone_connecting := by intro x y f; exact Subtype.ext (dgCone_connecting f)

end CochainComplex
