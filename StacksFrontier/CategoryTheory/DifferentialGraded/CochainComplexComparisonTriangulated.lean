module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexCompShift
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexGradedSplit
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexTriangulated

/-!
# The comparison of the two homotopy categories is an equivalence of triangulated categories

The equivalence `CochainComplex.homotopyCategoryEquivalence` of [Stacks, Tag 09L9] identifies the
ordinary homotopy category `K(B)` with the homotopy category `K(Comp^dg(B))` of the differential
graded category of complexes, the `C` of [Stacks, Tag 09LK]. Both sides are pretriangulated —
Mathlib's structure on the left, `CochainComplex.dgCategoryKPretriangulated` on the right — but the
two structures were built from unrelated data: on the left from Mathlib's mapping cones, on the
right from the admissible graded-split short exact sequences of
`CochainComplex.dgConeSituationIso`. This file shows that the comparison carries one to the other,
so that the equivalence is one of triangulated categories.

The bridge is Mathlib's description of the distinguished triangles of `K(B)` as those isomorphic
to the triangle of a degreewise split short exact sequence of complexes
(`CategoryTheory.HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`) together with
`CochainComplex.gradedSplitOfDegreewiseSplit`, which reads such a sequence as a graded-split short
exact sequence of `CochainComplex.dgCategory B`. On the two triangles the first two arrows agree
by definition, and the third ones agree because both are the right shift of the same degree-one
cocycle: `CochainComplex.cocycleOfDegreewiseSplit` on Mathlib's side, and the connecting morphism
`π d(s)` of the graded splitting on the other, which is that same cocycle by
`CochainComplex.connectingHom_gradedSplitOfDegreewiseSplit`.

## Main results

* `CochainComplex.mapTriangle_triangleOfDegreewiseSplit`: the triangle of a degreewise split
  short exact sequence, pushed into `K(Comp^dg(B))`, **is** the triangle of the associated
  graded-split sequence — an equality of triangles, not merely an isomorphism.
* `CochainComplex.homotopyCategoryComparisonFunctor_isTriangulated` and
  `CochainComplex.homotopyCategoryEquivalence_functor_isTriangulated`: the comparison functor is
  exact.
* `CochainComplex.homotopyCategoryEquivalence_isTriangulated` and
  `CochainComplex.homotopyCategoryEquivalence_inverse_isTriangulated`: **the comparison is an
  equivalence of triangulated categories**, and in particular its quasi-inverse is exact. This is
  what carries a localization of `K(B)` at the acyclics over to `K(Comp^dg(B))`.

## Implementation notes

The comparison of the third arrows is organized the way
`DGCategory.DGFunctor.CommShiftBIso.mapTriangleK_obj_associatedKTriangle` organizes the same
computation for a differential graded functor, and for the same reason: a connecting arrow of
`K(A)` is a morphism into the shifted object of axiom (B) followed by an `eqToHom` correcting that
object to the one of the translation, and a goal in which an object of the differential graded
category has to be read as an object of its homotopy category is not type-correct at the
transparency `rw` and `simp` use, so they refuse to fire. `CochainComplex.comp_eqToHom_congr`
therefore does the cancellation for morphisms of the homotopy category, with the two `eqToHom`s
left as hypotheses.

The comparison functor is reached through
`CategoryTheory.Functor.mapTriangleCompIso` and `CategoryTheory.Functor.mapTriangleIso` applied to
`CategoryTheory.Quotient.lift.isLift`, whose compatibility with the translations is Mathlib's
`CategoryTheory.Quotient.liftCommShift_compatibility`. That is what lets the computation be done
on the category of complexes, where the triangle of a degreewise split sequence lives, rather
than on the homotopy category.

## References

* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the comparison;
  [Tag 09QY](https://stacks.math.columbia.edu/tag/09QY), the triangulated structure on
  `K(Comp^dg(B))`; [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.HomComplex
open DGCategory.GradedSplitShortExact (connectingHom)

namespace CochainComplex

universe v u

variable (B : Type u) [Category.{v} B] [Preadditive B]

/-- **Cancellation of the two object corrections in a connecting arrow.** Two equal morphisms of
`K(Comp^dg(B))` followed by `eqToHom`s with the same source and target are equal. The two
`eqToHom`s are hypotheses rather than terms so that no object of the differential graded category
has to be read as an object of its homotopy category inside the statement. -/
theorem comp_eqToHom_congr {W a z : (dgCategory B).K}
    (m m' : z ⟶ a) (hm : m = m') (p q : a = W) :
    m ≫ eqToHom p = m' ≫ eqToHom q := by
  subst hm
  congr 1

section DegreewiseSplit

variable {B}
variable (S : ShortComplex (CochainComplex B ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval B (ComplexShape.up ℤ) n)).Splitting)

/-- **The connecting arrow of a degreewise split sequence is the connecting cocycle of its graded
splitting.** Mathlib's `CochainComplex.homOfDegreewiseSplit` is the right shift of
`CochainComplex.cocycleOfDegreewiseSplit`, and the connecting morphism `π d(s)` of
`CochainComplex.gradedSplitOfDegreewiseSplit` is that same cocycle, so the two agree after the
identification of Hom modules of axiom (B) — which is the right shift again. -/
theorem cochain_ofHom_homOfDegreewiseSplit :
    Cochain.ofHom (homOfDegreewiseSplit S σ) =
      (dgShiftAxiomBIso B).toShift 1 S.X₃ S.X₁ 0
        (connectingHom (gradedSplitOfDegreewiseSplit S σ)) := by
  rw [connectingHom_gradedSplitOfDegreewiseSplit]
  show _ = (cocycleOfDegreewiseSplit S σ).1.rightShift 1 0 (by omega)
  ext p
  rw [Cochain.ofHom_v, homOfDegreewiseSplit_f,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl]
  simp

/-- The same identity between closed degree-zero morphisms of `Comp^dg(B)`. -/
theorem cocycle_ofHom_homOfDegreewiseSplit :
    (Cocycle.ofHom (homOfDegreewiseSplit S σ) : (dgCategory B).Cocycle S.X₃ _) =
      (dgShiftAxiomBIso B).connectingCocycle (gradedSplitOfDegreewiseSplit S σ) :=
  Subtype.ext (cochain_ofHom_homOfDegreewiseSplit S σ)

/-- **The triangle of a degreewise split short exact sequence of complexes is the triangle of its
graded splitting.** Pushing Mathlib's `CochainComplex.triangleOfDegreewiseSplit` into
`K(Comp^dg(B))` gives exactly
`DGCategory.ShiftAxiomBIso.associatedKTriangle` of `CochainComplex.gradedSplitOfDegreewiseSplit`,
on the nose. The first two arrows are the two chain maps read as closed degree-zero cochains on
both sides; the third is `CochainComplex.cocycle_ofHom_homOfDegreewiseSplit`, the two object
corrections cancelling by `CochainComplex.comp_eqToHom_congr`. -/
theorem mapTriangle_triangleOfDegreewiseSplit :
    (cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B)).mapTriangle.obj
        (triangleOfDegreewiseSplit S σ) =
      DGCategory.ShiftAxiomBIso.associatedKTriangle (dgShiftAxiomBIso B)
        (gradedSplitOfDegreewiseSplit S σ) := by
  dsimp [Functor.mapTriangle, triangleOfDegreewiseSplit, Triangle.mk,
    DGCategory.ShiftAxiomBIso.associatedKTriangle]
  congr 1
  simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_eq_ofInduced,
    Iso.symm_hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
  refine comp_eqToHom_congr B _ _ ?_ _ _
  exact congrArg (Quotient.mk _) (cocycle_ofHom_homOfDegreewiseSplit S σ)

end DegreewiseSplit

variable [HasZeroObject B] [HasBinaryBiproducts B]

/-- **The image of the triangle of a degreewise split sequence under the comparison is the
triangle of its graded splitting.** This is
`CochainComplex.mapTriangle_triangleOfDegreewiseSplit` read through the comparison functor: the
descent along the homotopy quotient is compatible with the translations by
`CategoryTheory.Quotient.liftCommShift_compatibility`, so
`CategoryTheory.Functor.mapTriangleIso` applies to
`CategoryTheory.Quotient.lift.isLift`. -/
noncomputable def comparisonMapTriangleIso (S : ShortComplex (CochainComplex B ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval B (ComplexShape.up ℤ) n)).Splitting) :
    (homotopyCategoryComparisonFunctor B).mapTriangle.obj (trianglehOfDegreewiseSplit S σ) ≅
      DGCategory.ShiftAxiomBIso.associatedKTriangle (dgShiftAxiomBIso B)
        (gradedSplitOfDegreewiseSplit S σ) :=
  ((Functor.mapTriangleCompIso (HomotopyCategory.quotient B (.up ℤ))
      (homotopyCategoryComparisonFunctor B)).app (triangleOfDegreewiseSplit S σ)).symm ≪≫
    (Functor.mapTriangleIso (quotientCompComparisonIso B)).app
      (triangleOfDegreewiseSplit S σ) ≪≫
    eqToIso (mapTriangle_triangleOfDegreewiseSplit S σ)

/-- **The comparison functor of the two homotopy categories is exact.** Every distinguished
triangle of `K(B)` is isomorphic to the triangle of a degreewise split short exact sequence of
complexes, and `CochainComplex.comparisonMapTriangleIso` identifies its image with the triangle
of a graded-split short exact sequence of `Comp^dg(B)`, which is a distinguished triangle of
`K(Comp^dg(B))` by `CochainComplex.distinguishedTriangles_dgCategoryK`. -/
instance homotopyCategoryComparisonFunctor_isTriangulated :
    (homotopyCategoryComparisonFunctor B).IsTriangulated where
  map_distinguished T hT := by
    rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit] at hT
    obtain ⟨S, σ, ⟨e⟩⟩ := hT
    refine isomorphic_distinguished _ ?_ _
      ((homotopyCategoryComparisonFunctor B).mapTriangle.mapIso e)
    rw [show distinguishedTriangles (C := (dgCategory B).K) = _ from
      distinguishedTriangles_dgCategoryK B]
    exact ⟨S.X₁, S.X₂, S.X₃, gradedSplitOfDegreewiseSplit S σ,
      ⟨comparisonMapTriangleIso B S σ⟩⟩

/-- **The functor of the comparison equivalence is exact.** -/
instance homotopyCategoryEquivalence_functor_isTriangulated :
    (homotopyCategoryEquivalence B).functor.IsTriangulated :=
  homotopyCategoryComparisonFunctor_isTriangulated B

/-- **The comparison of the two homotopy categories is an equivalence of triangulated
categories.** This is [Stacks, Tag 09L9] read as a statement about triangulated categories: the
two pretriangulated structures, Mathlib's on `K(B)` and
`CochainComplex.dgCategoryKPretriangulated` on `K(Comp^dg(B))`, correspond under it. -/
@[stacks 09L9 "the comparison of the homotopy category of the differential graded category of \
complexes with the ordinary homotopy category is an equivalence of TRIANGULATED categories"]
instance homotopyCategoryEquivalence_isTriangulated :
    (homotopyCategoryEquivalence B).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ inferInstance

/-- **The quasi-inverse of the comparison is exact.** This is the instance that
`CochainComplex.dgCategoryKAcyclic` and
`CochainComplex.comparisonInverse_comp_isLocalization` carry as a hypothesis. -/
instance homotopyCategoryEquivalence_inverse_isTriangulated :
    (homotopyCategoryEquivalence B).inverse.IsTriangulated :=
  inferInstance

end CochainComplex
