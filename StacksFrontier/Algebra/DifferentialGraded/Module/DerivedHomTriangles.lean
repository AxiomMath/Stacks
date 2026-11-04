module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedSplitAdmissible
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexGradedSplit
public import StacksFrontier.CategoryTheory.DifferentialGraded.DGFunctorAdmissible
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation

/-!
# `Hom(K, -)` carries the triangles of `K(B)` to distinguished triangles

Let `K` be a cochain complex in a preadditive category `B` and let `E = End(K)` be its
endomorphism differential graded algebra. The functor `Hom(K, -)` of Tag 09LE, read as an
ordinary functor `CochainComplex B ℤ ⥤ Mod_{(E, d)}`, carries the triangle that Mathlib attaches
to a degreewise split short exact sequence of complexes to the triangle of an admissible short
exact sequence of differential graded `E`-modules, its third arrow being corrected by the shift
comparison `Hom(K, X[1]) ≅ Hom(K, X)[1]`.

Since `CategoryTheory.HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`
describes every distinguished triangle of `K(B)` as isomorphic to such a triangle, and
`DifferentialGradedModule.distinguishedTriangles_eq` describes the distinguished triangles of
`K(E, d)` as the triangles of admissible short exact sequences, this is the preservation of
distinguished triangles required of `Hom(K, -)` by Tag 09LK — the triangle half of the assertion
that the derived functor `R Hom(K, -)` is exact.

## Main definitions

* `CochainComplex.homComplexesFunctor`: `Hom(K, -) : CochainComplex B ℤ ⥤ Mod_{(E, d)}`.

## Main results

* `CochainComplex.homComplexesFunctor_map_toFun`: on underlying maps the functor is
  postcomposition with a chain map.
* `CochainComplex.connectingHom_map_gradedSplitOfDegreewiseSplit`: the connecting homomorphism of
  the image of a degreewise split sequence is `Hom(K, -)` applied to Mathlib's
  `CochainComplex.cocycleOfDegreewiseSplit`.
* `CochainComplex.homShift_comp_map_homOfDegreewiseSplit_toFun`: the image of Mathlib's third
  arrow `S.X₃ ⟶ S.X₁[1]`, followed by the shift comparison, has that connecting homomorphism as
  its underlying map.
* `CochainComplex.isDistinguishedTriangle_homComplexesFunctor_triangleOfDegreewiseSplit`: hence
  the image triangle is distinguished.
* `CochainComplex.exists_isDistinguishedTriangle_homComplexesFunctor`: the same for an arbitrary
  distinguished triangle of `K(B)`, presented by a degreewise split short exact sequence.

## What is not included

`CategoryTheory.Functor.IsTriangulated` itself. It asks for two things: that the shift
comparisons `CochainComplex.homShiftIso` be assembled into a
`CategoryTheory.Functor.CommShift ℤ` — natural in `X` and compatible with `shiftFunctorZero` and
`shiftFunctorAdd` on both sides — and that the image of `CategoryTheory.Functor.mapTriangle` be
distinguished, `mapTriangle` being formed with the degree-one component of that `CommShift`.

The first is `CochainComplex.homComplexesFunctorCommShift` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCommShift.lean`, and its descent to the
homotopy category is `CochainComplex.homHomotopyFunctorCommShift`. The content of preservation is
the result below. The translation between the two shapes is
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomExactness.lean`, where
`CochainComplex.homHomotopyFunctor_isTriangulated` is proved: the third arrow of `mapTriangle`
for the homotopy-level functor is the comparison used below transported along
`CochainComplex.homHomotopyFunctorLiftIso`, which is not the identity, so the statement is proved
for the descent of `Hom(K, -)` along the quotient by homotopy and transported back.

## Implementation notes

The three inputs are the two translations between the encodings of an admissible short exact
sequence — `CochainComplex.gradedSplitOfDegreewiseSplit` on the source side and
`DifferentialGradedModule.isDistinguishedTriangle_gradedSplit` on the target side — and the
shift comparison `CochainComplex.homShiftIso`. The differential graded functor transports the
graded splitting by `DGCategory.DGFunctor.mapGradedSplitShortExact`, which is where the fact that
a graded splitting is not a chain map is accommodated: the functor acts on homogeneous morphisms
of every degree.

Identifying the third arrows is the only computation. Mathlib's arrow `S.X₃ ⟶ S.X₁[1]` is the
degree-one cocycle `cocycleOfDegreewiseSplit` read through
`CochainComplex.HomComplex.Cochain.rightShift`; postcomposition with it, followed by the shift
comparison — which is `rightUnshift` on each graded piece — is postcomposition with the cocycle
itself, by `CochainComplex.HomComplex.Cochain.rightUnshift_comp`. The degrees of the two
`DirectSum` summands involved are `(0 + k) + 1` and `1 + k`, which are equal but not
definitionally so; `DGCategory.comp_heq` performs the transport.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose exactness clause
  this is part of; [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for `Hom(K, -)`;
  [Tag 09K8](https://stacks.math.columbia.edu/tag/09K8) for the triangles of `K(E, d)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

open CochainComplex.HomComplex HomologicalComplex DifferentialGradedModule

variable (B : Type u) [Category.{v} B] [Preadditive B] (K : CochainComplex B ℤ)

/-- `Hom(K, -)` as an ordinary functor from cochain complexes to differential graded modules over
the endomorphism algebra `E = End(K)`: the functor of Tag 09LE on closed degree-zero morphisms,
read through the identification of the category of complexes of the differential graded category
of differential graded modules with the differential graded modules themselves. -/
noncomputable def homComplexesFunctor :
    CochainComplex B ℤ ⥤ DifferentialGradedModule (DGCategory.endAlgebra (dgCategory B) K) :=
  cochainToComplexFunctor B ⋙ (DGCategory.representableDGFunctor (dgCategory B) K).onComp ⋙
    DifferentialGradedModule.compToModules (DGCategory.endAlgebra (dgCategory B) K)

/-- `Hom(K, -)` sends a cochain complex `X` to the representable module
`DGCategory.representableModule (dgCategory B) K X`. -/
@[simp] theorem homComplexesFunctor_obj (X : CochainComplex B ℤ) :
    (homComplexesFunctor B K).obj X = DGCategory.representableModule (dgCategory B) K X := rfl

/-- On underlying linear maps, `Hom(K, -)` is postcomposition with a chain map. -/
theorem homComplexesFunctor_map_toFun {X Y : CochainComplex B ℤ} (φ : X ⟶ Y) :
    ((homComplexesFunctor B K).map φ).toFun =
      DGCategory.repPostcomp (dgCategory B) K (Cochain.ofHom φ) := rfl

section

variable (S : ShortComplex (CochainComplex B ℤ))
  (σ : ∀ n, (S.map (eval B (ComplexShape.up ℤ) n)).Splitting)

/-- The image under `Hom(K, -)` of the graded-split short exact sequence of a degreewise split
short complex of cochain complexes. -/
noncomputable def mapGradedSplitOfDegreewiseSplit :
    DGCategory.GradedSplitShortExact
      (A := DifferentialGradedModule.dgCategory (DGCategory.endAlgebra (dgCategory B) K))
      (DGCategory.representableModule (dgCategory B) K S.X₁)
      (DGCategory.representableModule (dgCategory B) K S.X₂)
      (DGCategory.representableModule (dgCategory B) K S.X₃) :=
  (DGCategory.representableDGFunctor (dgCategory B) K).mapGradedSplitShortExact
    (gradedSplitOfDegreewiseSplit S σ)

/-- The first closed arrow of the image sequence is the image of `S.f` under `Hom(K, -)`. -/
theorem homOfCocycle_mapGradedSplitOfDegreewiseSplit_a :
    homOfCocycle (DGCategory.endAlgebra (dgCategory B) K)
        (mapGradedSplitOfDegreewiseSplit B K S σ).a =
      (homComplexesFunctor B K).map S.f := rfl

/-- The second closed arrow of the image sequence is the image of `S.g` under `Hom(K, -)`. -/
theorem homOfCocycle_mapGradedSplitOfDegreewiseSplit_b :
    homOfCocycle (DGCategory.endAlgebra (dgCategory B) K)
        (mapGradedSplitOfDegreewiseSplit B K S σ).b =
      (homComplexesFunctor B K).map S.g := rfl

/-- **The connecting morphism of the image sequence is `Hom(K, -)` applied to Mathlib's
`CochainComplex.cocycleOfDegreewiseSplit`.** -/
theorem connectingHom_map_gradedSplitOfDegreewiseSplit :
    DGCategory.GradedSplitShortExact.connectingHom
        (mapGradedSplitOfDegreewiseSplit B K S σ) =
      DGCategory.repPostcompHomogeneousMap (dgCategory B) K
        ((cocycleOfDegreewiseSplit S σ).1 : (dgCategory B).Hom S.X₃ S.X₁ 1) := by
  have h := DGCategory.DGFunctor.connectingHom_mapGradedSplitShortExact
    (DGCategory.representableDGFunctor (dgCategory B) K) (gradedSplitOfDegreewiseSplit S σ)
  rw [connectingHom_gradedSplitOfDegreewiseSplit] at h
  exact h

/-- The third arrow of the image triangle: `Hom(K, -)` applied to Mathlib's
`CochainComplex.homOfDegreewiseSplit`, followed by the shift comparison
`Hom(K, S.X₁[1]) ≅ Hom(K, S.X₁)[1]`. -/
noncomputable def homComplexesConnecting :
    DGCategory.representableModule (dgCategory B) K S.X₃ ⟶
      (DGCategory.representableModule (dgCategory B) K S.X₁).shift 1 :=
  (homComplexesFunctor B K).map (homOfDegreewiseSplit S σ) ≫ (homShiftIso K 1 S.X₁).hom

/-- **The third arrow of the image triangle is the connecting homomorphism of the image
sequence.** The shift comparison is `rightUnshift` on each graded piece, and `rightUnshift`
undoes the `rightShift` by which Mathlib's arrow `S.X₃ ⟶ S.X₁[1]` is built from the degree-one
cocycle. -/
theorem homShift_comp_map_homOfDegreewiseSplit_toFun
    (z : (DGCategory.representableModule (dgCategory B) K S.X₃).M) :
    (homComplexesConnecting B K S σ).toFun z =
      (DGCategory.GradedSplitShortExact.connectingHom
        (mapGradedSplitOfDegreewiseSplit B K S σ)).1 z := by
  classical
  rw [connectingHom_map_gradedSplitOfDegreewiseSplit]
  show (homShiftIso K 1 S.X₁).hom.toFun
      (DGCategory.repPostcomp (dgCategory B) K
        (Cochain.ofHom (homOfDegreewiseSplit S σ)) z) =
    DGCategory.repPostcomp (dgCategory B) K ((cocycleOfDegreewiseSplit S σ).1) z
  have hofHom : Cochain.ofHom (homOfDegreewiseSplit S σ) =
      (cocycleOfDegreewiseSplit S σ).1.rightShift 1 0 (zero_add 1) := by
    rw [homOfDegreewiseSplit]
    exact (Cocycle.cochain_ofHom_homOf_eq_coe
      ((cocycleOfDegreewiseSplit S σ).rightShift 1 0 (zero_add 1))).trans
      (Cocycle.rightShift_coe (cocycleOfDegreewiseSplit S σ) 1 0 (zero_add 1))
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | of k g =>
    rw [DGCategory.repPostcomp_of,
      homShiftIso_hom_toFun_of' K 1 S.X₁ (0 + k) (1 + k) (by omega),
      DGCategory.repPostcomp_of]
    congr 1
    show Cochain.rightUnshift
        (Cochain.comp g (Cochain.ofHom (homOfDegreewiseSplit S σ))
          (show k + 0 = 0 + k by omega)) (1 + k) (by omega) =
      Cochain.comp g ((cocycleOfDegreewiseSplit S σ).1) (show k + 1 = 1 + k by omega)
    rw [hofHom, Cochain.rightUnshift_comp (a := 1) g
      ((cocycleOfDegreewiseSplit S σ).1.rightShift 1 0 (zero_add 1))
      (show k + 0 = 0 + k by omega) (1 + k) (by omega) 1 (zero_add 1),
      Cochain.rightUnshift_rightShift]

/-- **`Hom(K, -)` carries the triangle of a degreewise split short exact sequence of complexes to
a distinguished triangle of `K(E, d)`.** This is the triangle half of the exactness clause of Tag
09LK for the functor being derived. -/
@[stacks 09LK "the functor Hom(K, -) carries the triangle of a degreewise split short exact \
sequence of complexes to a distinguished triangle of K(E, d) -- preservation of distinguished \
triangles for the functor being derived"]
theorem isDistinguishedTriangle_homComplexesFunctor_triangleOfDegreewiseSplit :
    IsDistinguishedTriangle (DGCategory.endAlgebra (dgCategory B) K)
      (Pretriangulated.Triangle.mk
        ((toHomotopyCategory _).map ((homComplexesFunctor B K).map S.f))
        ((toHomotopyCategory _).map ((homComplexesFunctor B K).map S.g))
        ((toHomotopyCategory _).map (homComplexesConnecting B K S σ) ≫
          eqToHom (CategoryTheory.Quotient.functor_obj_shift
            (homotopyRel (DGCategory.endAlgebra (dgCategory B) K)) ℤ
            (DGCategory.representableModule (dgCategory B) K S.X₁) 1).symm)) :=
  isDistinguishedTriangle_gradedSplit (DGCategory.endAlgebra (dgCategory B) K)
    (mapGradedSplitOfDegreewiseSplit B K S σ) (homComplexesConnecting B K S σ)
    (homShift_comp_map_homOfDegreewiseSplit_toFun B K S σ)

end

/-- **`Hom(K, -)` preserves distinguished triangles.** Every distinguished triangle of `K(B)` is
isomorphic to the triangle of a degreewise split short exact sequence of complexes, and the
image of that triangle under `Hom(K, -)` — with its third arrow corrected by the shift
comparison `Hom(K, X[1]) ≅ Hom(K, X)[1]` — is a distinguished triangle of `K(E, d)`.

This is the preservation of distinguished triangles asserted by Tag 09LK of the functor being
derived. It is stated for a presentation of the triangle by a degreewise split sequence rather
than as `CategoryTheory.Functor.IsTriangulated`; the `CategoryTheory.Functor.CommShift ℤ` that
the latter also requires is `CochainComplex.homComplexesFunctorCommShift`, whose degree-one
component is the comparison appearing here. -/
@[stacks 09LK "the functor Hom(K, -) being derived preserves distinguished triangles: every \
distinguished triangle of K(B) is the triangle of a degreewise split short exact sequence of \
complexes, and its image, with the third arrow read through the shift comparison \
Hom(K, X[1]) = Hom(K, X)[1], is a distinguished triangle of K(E, d)", sga "4½ Etat_0 1.2.4"]
theorem exists_isDistinguishedTriangle_homComplexesFunctor [HasZeroObject B]
    [HasBinaryBiproducts B]
    (T : Pretriangulated.Triangle (HomotopyCategory B (ComplexShape.up ℤ)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles
      (C := HomotopyCategory B (ComplexShape.up ℤ))) :
    ∃ (S : ShortComplex (CochainComplex B ℤ))
      (σ : ∀ n, (S.map (eval B (ComplexShape.up ℤ) n)).Splitting),
      Nonempty (T ≅ trianglehOfDegreewiseSplit S σ) ∧
        IsDistinguishedTriangle (DGCategory.endAlgebra (dgCategory B) K)
          (Pretriangulated.Triangle.mk
            ((toHomotopyCategory _).map ((homComplexesFunctor B K).map S.f))
            ((toHomotopyCategory _).map ((homComplexesFunctor B K).map S.g))
            ((toHomotopyCategory _).map (homComplexesConnecting B K S σ) ≫
              eqToHom (CategoryTheory.Quotient.functor_obj_shift
                (homotopyRel (DGCategory.endAlgebra (dgCategory B) K)) ℤ
                (DGCategory.representableModule (dgCategory B) K S.X₁) 1).symm)) := by
  obtain ⟨S, σ, he⟩ :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).1 hT
  exact ⟨S, σ, he,
    isDistinguishedTriangle_homComplexesFunctor_triangleOfDegreewiseSplit B K S σ⟩

end CochainComplex
