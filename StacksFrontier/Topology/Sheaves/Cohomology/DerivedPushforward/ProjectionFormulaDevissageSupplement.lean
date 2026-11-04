module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaDevissage
public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Unit
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfect
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect

/-!
# Dévissage for natural transformations between exact functors

Two-out-of-three and coproduct closure for the property "a natural transformation between exact
functors is invertible at every shift of the object", and the resulting dévissage: such a
transformation which is invertible at every shift of a generator is invertible everywhere.

## Main results

* `isIso_app_two_out_of_three_of_all_shifts`: two-out-of-three for invertibility at every shift,
  in all three rotations of a distinguished triangle.
* `isIso_app_of_generation`: a natural transformation between exact coproduct-preserving functors
  which is invertible at every shift of a generator in the sense of [Stacks, Tag 09PB] is
  invertible everywhere.
* `isIso_app_of_isIso_app_shift_regular`: the same over `D(R)`, with `R` as the generator.
* `isIso_projectionFormulaMap_of_generation`: the projection-formula morphism of
  [Stacks, Tag 0B53] is invertible at every target complex.
* `derivedPushforwardDerivedPullbackIsoOfGeneration`: the isomorphism
  `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ≅ Rf_*Lf^*K` of [Stacks, Tag 08I9].
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe v u

namespace Stacks.Cohomology.DerivedProjectionFormulaDevissage

/-- Invertibility of `α` at every shift of `A` gives invertibility at every iterated shift. -/
private theorem isIso_app_shift_shift_of_all_shifts
    {C : Type*} [Category* C] {D : Type*} [Category* D] [HasShift C ℤ]
    {F G : C ⥤ D} (α : F ⟶ G) (A : C)
    (h : ∀ n : ℤ, IsIso (α.app (A⟦n⟧))) (k n : ℤ) : IsIso (α.app ((A⟦k⟧)⟦n⟧)) :=
  (α.isIso_app_iff_of_iso ((shiftFunctorAdd C k n).app A)).1 (h (k + n))

/-! ### Two-out-of-three for a distinguished triangle, in the all-shifts form

The middle rotation is
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts`. -/

section TwoOutOfThree

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (α : F ⟶ G)

/-- A natural transformation between exact functors which is invertible at every shift of the
first and second vertices of a distinguished triangle is invertible at every shift of the
third. -/
theorem isIso_app_third_of_all_shifts (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) (n : ℤ) :
    IsIso (α.app (T.obj₃⟦n⟧)) := by
  exact isIso_app_third_of_distinguished F G α _ (T.shift_distinguished hT n) (h₁ n) (h₂ n)
    (isIso_app_shift_shift_of_all_shifts α _ h₁ n 1)
    (isIso_app_shift_shift_of_all_shifts α _ h₂ n 1)

/-- A natural transformation between exact functors which is invertible at every shift of the
second and third vertices of a distinguished triangle is invertible at every shift of the
first. -/
theorem isIso_app_first_of_all_shifts (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) (n : ℤ) :
    IsIso (α.app (T.obj₁⟦n⟧)) :=
  (α.isIso_app_iff_of_iso ((shiftFunctorAdd' C 1 (n - 1) n (by omega)).app T.obj₁)).2
    (isIso_app_third_of_all_shifts F G α T.rotate (rot_of_distTriang T hT) h₂ h₃ (n - 1))

/-- Two-out-of-three for the property "invertible at every shift", in all three rotations of a
distinguished triangle. -/
theorem isIso_app_two_out_of_three_of_all_shifts (T : Triangle C) (hT : T ∈ distTriang C) :
    ((∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧))) → (∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) →
        ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧))) → (∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) → (∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧))) :=
  ⟨fun h₁ h₂ => isIso_app_third_of_all_shifts F G α T hT h₁ h₂,
    fun h₁ h₃ => isIso_app_middle_of_all_shifts F G α T hT h₁ h₃,
    fun h₂ h₃ => isIso_app_first_of_all_shifts F G α T hT h₂ h₃⟩

end TwoOutOfThree

/-! ### Closure under an arbitrary direct sum -/

section Coproducts

variable {C : Type*} [Category* C] {D : Type*} [Category* D] [HasShift C ℤ]
  (F G : C ⥤ D) (α : F ⟶ G)

/-- A natural transformation invertible at every shift of each member of a family is invertible
at every shift of the coproduct, provided both functors preserve coproducts of that shape. -/
theorem isIso_app_coproduct_of_all_shifts {ι : Type*} (K : ι → C) [HasCoproduct K]
    [PreservesColimitsOfShape (Discrete ι) F] [PreservesColimitsOfShape (Discrete ι) G]
    (h : ∀ (i : ι) (n : ℤ), IsIso (α.app ((K i)⟦n⟧))) (n : ℤ) :
    IsIso (α.app ((∐ K)⟦n⟧)) :=
  Stacks.AlgebraicGeometry.PushforwardColimits.isIso_app_of_isColimit α
    (isColimitOfPreserves F
      (isColimitOfPreserves (shiftFunctor C n) (colimit.isColimit (Discrete.functor K))))
    (isColimitOfPreserves G
      (isColimitOfPreserves (shiftFunctor C n) (colimit.isColimit (Discrete.functor K))))
    fun j => h j.as n

end Coproducts

/-! ### The dévissage -/

section Assembly

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (α : F ⟶ G)
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G]

/-- Let `α : F ⟶ G` be a natural transformation between exact functors out of a pretriangulated
category `C`, both preserving coproducts. Let `P` be an object of `C` such that every property of
objects of `C` which is closed under coproducts, satisfies two-out-of-three for distinguished
triangles and holds at every shift of `P`, holds everywhere — the hypothesis `hgen`, which is the
conclusion of [Stacks, Tag 09PB] for `C = D(A)` and `P = A`. If `α` is invertible at every shift
of `P`, it is invertible at every object of `C`. -/
theorem isIso_app_of_generation (P : C)
    (hgen : ∀ T : C → Prop,
      (∀ {J : Type v} (Z : J → C) [HasCoproduct Z], (∀ j, T (Z j)) → T (∐ Z)) →
      (∀ Δ : Triangle C, Δ ∈ distTriang C →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T (P⟦k⟧)) → ∀ K, T K)
    (hP : ∀ n : ℤ, IsIso (α.app (P⟦n⟧))) (K : C) : IsIso (α.app K) :=
  have hall : ∀ n : ℤ, IsIso (α.app (K⟦n⟧)) :=
    hgen (fun Z => ∀ n : ℤ, IsIso (α.app (Z⟦n⟧)))
      (fun Z _ hZ => isIso_app_coproduct_of_all_shifts F G α Z fun j => hZ j)
      (fun Δ hΔ => isIso_app_two_out_of_three_of_all_shifts F G α Δ hΔ)
      (isIso_app_shift_shift_of_all_shifts α P hP) K
  (α.isIso_app_iff_of_iso ((shiftFunctorZero C ℤ).app K)).1 (hall 0)

end Assembly

/-! ### The dévissage over a ring -/

section ModuleCat

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [Ring R] [Small.{v} R]
  {D : Type*} [Category* D] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F G : DerivedCategory (ModuleCat.{v} R) ⥤ D)
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (α : F ⟶ G)
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G]

/-- A natural transformation between exact coproduct-preserving functors out of `D(R)` which is
invertible at every shift of `R` is invertible at every object of `D(R)`. -/
theorem isIso_app_of_isIso_app_shift_regular
    (hP : ∀ n : ℤ, IsIso (α.app
      (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
        (ModuleCat.of R (Shrink.{v} R)))⟦n⟧)))
    (K : DerivedCategory (ModuleCat.{v} R)) : IsIso (α.app K) :=
  isIso_app_of_generation.{v} F G α
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R (Shrink.{v} R)))
    (fun T hsum htri hshift =>
      (CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts
        (R := R)).2 T (fun Z _ hZ => hsum Z hZ) htri hshift)
    hP K

end ModuleCat

/-! ### The dévissage of the derived projection formula

The projection-formula morphism of [Stacks, Tag 0B53], read as a natural transformation in the
target complex. -/

section DerivedProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- [Stacks, Tag 08EU] at a general target complex. For an arbitrary morphism of ringed spaces
`f : X ⟶ Y` and an arbitrary `E ∈ D(𝒪_X)`, the projection-formula morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

of [Stacks, Tag 0B53] is invertible for every `K ∈ D(𝒪_Y)`, provided that:

* `hunit`: it is invertible at the structure sheaf of `Y` placed in each degree;
* both of its sides preserve coproducts;
* `hgen`: `D(𝒪_Y)` is generated by its structure sheaf in the sense of [Stacks, Tag 09PB]. -/
theorem isIso_projectionFormulaMap_of_generation
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J)
      (ProjectionFormulaPerfect.projectionFormulaSource f E)]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J)
      (ProjectionFormulaPerfect.projectionFormulaTarget f E)]
    (hgen : ∀ T : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) → Prop,
      (∀ {J : Type v} (Z : J → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
        [HasCoproduct Z], (∀ j, T (Z j)) → T (∐ Z)) →
      (∀ Δ : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))),
        Δ ∈ distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T ((ProjectionFormulaPerfectDevissage.singleUnit Y.sheaf 0)⟦k⟧)) → ∀ K, T K)
    (hunit : ∀ i : ℤ, IsIso (projectionFormulaMap f E
      (ProjectionFormulaPerfectDevissage.singleUnit Y.sheaf i)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso (projectionFormulaMap f E K) := by
  let _ : (ProjectionFormulaPerfect.projectionFormulaSource f E).CommShift ℤ :=
    (canonicalDerivedTensorProduct Y.sheaf).commShift_right _
  have _ : (ProjectionFormulaPerfect.projectionFormulaSource f E).IsTriangulated :=
    (canonicalDerivedTensorProduct Y.sheaf).exact_right _
  let _ : (ProjectionFormulaPerfect.projectionFormulaTarget f E).CommShift ℤ :=
    ProjectionFormulaPerfect.projectionFormulaTargetCommShift f E
  have _ : (ProjectionFormulaPerfect.projectionFormulaTarget f E).IsTriangulated :=
    ProjectionFormulaPerfect.projectionFormulaTarget_isTriangulated f E
  exact isIso_app_of_generation.{v}
    (ProjectionFormulaPerfect.projectionFormulaSource f E)
    (ProjectionFormulaPerfect.projectionFormulaTarget f E)
    (ProjectionFormulaPerfect.projectionFormulaTransformation f E) _ hgen
    (fun n => ProjectionFormulaPerfectDevissage.isIso_app_singleUnit_shift Y.sheaf
      (ProjectionFormulaPerfect.projectionFormulaSource f E)
      (ProjectionFormulaPerfect.projectionFormulaTarget f E)
      (ProjectionFormulaPerfect.projectionFormulaTransformation f E) hunit 0 n) K

/-- The isomorphism

`Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ≅ Rf_*Lf^*K`

of [Stacks, Tag 08I9], for an arbitrary `K ∈ D(𝒪_Y)`, given an identification `unitLeft` of
`𝒪_X[0] ⊗^𝐋 -` with the identity and the hypotheses of `isIso_projectionFormulaMap_of_generation`
at `E = 𝒪_X[0]`. -/
def derivedPushforwardDerivedPullbackIsoOfGeneration
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J)
      (ProjectionFormulaPerfect.projectionFormulaSource f (singleUnit X))]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J)
      (ProjectionFormulaPerfect.projectionFormulaTarget f (singleUnit X))]
    (unitLeft : ∀ W : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj (singleUnit X)).obj W ≅ W)
    (hgen : ∀ T : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) → Prop,
      (∀ {J : Type v} (Z : J → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
        [HasCoproduct Z], (∀ j, T (Z j)) → T (∐ Z)) →
      (∀ Δ : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))),
        Δ ∈ distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T ((ProjectionFormulaPerfectDevissage.singleUnit Y.sheaf 0)⟦k⟧)) → ∀ K, T K)
    (hunit : ∀ i : ℤ, IsIso (projectionFormulaMap f (singleUnit X)
      (ProjectionFormulaPerfectDevissage.singleUnit Y.sheaf i)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((derivedTensorProductFunctor Y.sheaf).obj
        ((derivedPushforward f).obj (singleUnit X))).obj K ≅
      (derivedPushforward f).obj ((derivedPullback f).obj K) :=
  derivedPushforwardDerivedPullbackIsoOfIsIso f unitLeft K
    (isIso_projectionFormulaMap_of_generation.{v} f (singleUnit X) hgen hunit K)

end DerivedProjectionFormula

end Stacks.Cohomology.DerivedProjectionFormulaDevissage

end
