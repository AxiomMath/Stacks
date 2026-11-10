module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility

/-!
# The projection-formula morphism and distinguished triangles

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let
`E ∈ D(𝒪_X)`.  The objects `K ∈ D(𝒪_Y)` at which the projection-formula morphism

`Rf_*E ⊗^L_{𝒪_Y} K ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)`

of [Stacks, Tag 0B53] is invertible, *at every shift of `K`*, satisfy two-out-of-three for a
distinguished triangle of `D(𝒪_Y)`.

## Main results

* `Stacks.Cohomology.ProjectionFormulaTriangles.isIso_projectionFormulaMap_triangle`: the three
  implications above, in exactly the shape that the dévissage of [Stacks, Tag 09PB] —
  `CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts` — asks for as its
  `htriangle` argument.
* `Stacks.Cohomology.ProjectionFormulaTriangles.isIso_app_shifts_triangle`: the same three
  implications for an arbitrary natural transformation between two exact functors of
  pretriangulated categories.

## Implementation notes

This is step (c) of the dévissage of [Stacks, Tag 08EU], and it needs no hypothesis on `f` or on
`E` at all: no quasi-compactness, no quasi-separatedness, no quasi-coherence.  The content is
purely triangulated.  The projection-formula morphism is the natural transformation
`Stacks.Cohomology.ProjectionFormulaPerfect.projectionFormulaTransformation` between two functors
`D(𝒪_Y) ⥤ D(𝒪_Y)` that commute with the shift and are exact, and for such a transformation the
three implications follow from the five lemma applied to the two long exact sequences, which is
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_third_of_distinguished`.

Everything here is for an arbitrary natural transformation between exact functors; only the final
theorem mentions the projection formula.  The generic statement is `isIso_app_shifts_triangle`,
which is the companion of
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts` for the other
two vertices and is stated for its own sake.

The hypothesis is quantified over all shifts for two separate reasons, and neither can be
dropped:

* even to get the *third* vertex, `isIso_app_third_of_distinguished` needs invertibility at the
  first two vertices **and** at their shifts by one, because the fourth and fifth morphisms of
  the five lemma live at the shifted objects;
* the other two implications are obtained by rotating the triangle, and a rotation moves a vertex
  to a shift of a vertex, so the conclusion is only ever about `T.objᵢ⟦1⟧` and has to be
  transported back along `shiftFunctorAdd'`.

Crucially, none of this uses a `CategoryTheory.NatTrans.CommShift` for the transformation.  That
would be a shift compatibility of the comparison of [Stacks, Tag 079U], which
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` does not carry; compare
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_singleUnit_iff_unitShift`.
The five-morphism form of the five lemma is what makes that avoidable: the fourth and fifth
morphisms are the component of the transformation at the shifted object, conjugated by the two
`commShiftIso`s of the two *functors*, and no compatibility between them is required.

The four structural hypotheses on the two functors are explicit arguments rather than instance
binders: the two spellings of the structure sheaf of rings of a ringed space make the `HasShift`
instance a consumer has agree with the one here only after a semireducible definition is unfolded,
which instance search does not do.

The same unfolding problem is what the four local transparency attributes are for, and all
four are needed: without them the additivity of the shift functor of
`D(SheafOfModules (structureSheafRing Y))` — one of the standing hypotheses of
`Pretriangulated`, and so an instance argument of the generic statement — is not found, even
though it is constructible by hand from `DerivedCategory.instAdditiveShiftFunctorInt`.  Supplying
it by hand does not help: the instance the application then asks for is a different one, assembled
through a different unfolding of `structureSheafRing`, so the two do not meet.  Making
`structureSheafRing`, `Stacks.SheafOfModules.Tensor.ringSheaf`, `CategoryTheory.sheafCompose` and
`AlgebraicGeometry.SheafedSpace.sheaf` transparent to instance search is what makes the two the
same instance.  `Tensor.ringSheaf` is the spelling the derived tensor product of [Stacks,
Tag 06YU] is indexed at, and it is semireducible, so its reduct is reached from neither side
without it.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.ProjectionFormulaPerfect
open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaTriangles

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The generic triangulated statement -/

/-- Invertibility of a natural transformation at every shift of an object gives invertibility at
an iterated shift of it: `K⟦a⟧⟦b⟧ ≅ K⟦a + b⟧`. -/
private theorem isIso_app_shift_comp {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ]
    {F G : C ⥤ D} (α : F ⟶ G) {K : C} (h : ∀ n : ℤ, IsIso (α.app (K⟦n⟧))) (a b : ℤ) :
    IsIso (α.app ((K⟦a⟧)⟦b⟧)) :=
  (α.isIso_app_iff_of_iso ((shiftFunctorAdd C a b).app K)).1 (h (a + b))

/-- Invertibility of a natural transformation at every shift of `K⟦a⟧` gives invertibility at
every shift of `K`: the shift by `n` of `K` is the shift by `n - a` of `K⟦a⟧`. -/
private theorem isIso_app_shifts_of_shifts_shift {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] {F G : C ⥤ D} (α : F ⟶ G) {K : C} (a : ℤ)
    (h : ∀ n : ℤ, IsIso (α.app ((K⟦a⟧)⟦n⟧))) (n : ℤ) :
    IsIso (α.app (K⟦n⟧)) :=
  (α.isIso_app_iff_of_iso ((shiftFunctorAdd' C a (n - a) n (by omega)).app K)).2 (h (n - a))

/-- **Two-out-of-three in all shifts for a natural transformation between exact functors.**  For
a distinguished triangle `T`, if a natural transformation between two exact functors is
invertible at every shift of two of the vertices of `T`, it is invertible at every shift of the
third.

The three implications are stated as a conjunction, in the order and the shape that
`CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts` ([Stacks, Tag 09PB])
consumes.  No compatibility of the transformation with the shift is used.

This is the companion, for the first and the third vertex, of
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts`, whose second
component it reproves. -/
theorem isIso_app_shifts_triangle {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : C ⥤ D) (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated)
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distinguishedTriangles) :
    ((∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧))) → (∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) →
        ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧))) → (∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) → (∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧))) := by
  let := hFs
  let := hGs
  let := hFt
  let := hGt
  have third (S : Triangle C) (hS : S ∈ distinguishedTriangles)
      (h₁ : ∀ n : ℤ, IsIso (α.app (S.obj₁⟦n⟧)))
      (h₂ : ∀ n : ℤ, IsIso (α.app (S.obj₂⟦n⟧))) (n : ℤ) :
      IsIso (α.app (S.obj₃⟦n⟧)) :=
    isIso_app_third_of_distinguished F G α ((shiftFunctor (Triangle C) n).obj S)
      (S.shift_distinguished hS n) (h₁ n) (h₂ n)
      (isIso_app_shift_comp α h₁ n 1) (isIso_app_shift_comp α h₂ n 1)
  refine ⟨third T hT, ?_, ?_⟩
  · intro h₁ h₃
    exact isIso_app_shifts_of_shifts_shift α 1
      (third T.rotate.rotate (rot_of_distTriang _ (rot_of_distTriang T hT)) h₃
        (isIso_app_shift_comp α h₁ 1))
  · intro h₂ h₃
    exact isIso_app_shifts_of_shifts_shift α 1
      (third T.rotate (rot_of_distTriang T hT) h₂ h₃)

/-! ### The projection formula -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Step (c) of the dévissage of [Stacks, Tag 08EU]: the projection-formula morphism satisfies
two-out-of-three in all shifts.**  For a morphism of ringed spaces `f`, an arbitrary `E ∈ D(𝒪_X)`
and a distinguished triangle `T` of `D(𝒪_Y)`, if the projection-formula morphism of
[Stacks, Tag 0B53] is invertible at every shift of two of the vertices of `T`, then it is
invertible at every shift of the third.

The three implications are given in the shape of the `htriangle` argument of
`CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts`
([Stacks, Tag 09PB]), for the property "invertible at every shift of this object".

No hypothesis on `f` or on `E` is needed.  The projection-formula morphism is the natural
transformation `Stacks.Cohomology.ProjectionFormulaPerfect.projectionFormulaTransformation`, its
source `K ↦ Rf_*E ⊗^L_{𝒪_Y} K` is exact by the `commShift_right`/`exact_right` data of the
derived tensor product of [Stacks, Tag 06YU], and its target `K ↦ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)` is a
composite of three exact functors; the rest is the five lemma, which is
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_third_of_distinguished`. -/
theorem isIso_projectionFormulaMap_triangle
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (T : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))))
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles) :
    ((∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₁⟦n⟧))) →
        (∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₂⟦n⟧))) →
        ∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₃⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₁⟦n⟧))) →
        (∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₂⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₂⟦n⟧))) →
        (∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E
          (T.obj₁⟦n⟧))) :=
  isIso_app_shifts_triangle (projectionFormulaSource f E) (projectionFormulaTarget f E)
    ((canonicalDerivedTensorProduct Y.sheaf).commShift_right _)
    (projectionFormulaTargetCommShift f E)
    ((canonicalDerivedTensorProduct Y.sheaf).exact_right _)
    (projectionFormulaTarget_isTriangulated f E)
    (projectionFormulaTransformation f E) T hT

end Stacks.Cohomology.ProjectionFormulaTriangles

end

end
