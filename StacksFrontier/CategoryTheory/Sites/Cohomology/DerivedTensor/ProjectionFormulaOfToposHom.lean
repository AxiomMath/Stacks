module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Abstract
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom

/-!
# The projection formula map of a morphism of ringed topoi, and strictly perfect complexes

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi, `E ∈ D(𝒪_𝒞)` and
`K ∈ D(𝒪_𝒟)`. Equation 21.50.0.1 of [Stacks, Tag 0B56] is the canonical map

`Rf_*E ⊗^𝐋_{𝒪_𝒟} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)`,

adjoint, for `Lf^* ⊣ Rf_*` ([Stacks, Tag 07A6]), to the comparison
`Lf^*(Rf_*E ⊗^𝐋 K) ≅ Lf^*Rf_*E ⊗^𝐋 Lf^*K` of [Stacks, Tag 07A4] followed by the counit in the
first factor. This file constructs it for an arbitrary morphism of ringed topoi and proves the
part of [Stacks, Tag 0944] which does not localize on `𝒟`: the map is an isomorphism when `K` is
the structure sheaf placed in any degree, and hence, by the dévissage on stupid truncations and
direct summands, at every shift of every strictly perfect complex of `𝒪_𝒟`-modules.

## Main definitions

* `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap`: Equation 21.50.0.1.
* `Stacks.Cohomology.ProjectionFormulaOfToposHom.derivedPullbackUnitShiftIso`:
  `Lf^*(𝒪_𝒟[0]⟦m⟧) ≅ 𝒪_𝒞[0]⟦m⟧`.

## Main results

* `projectionFormulaMap_naturality_target`: the map is natural in `K`.
* `isIso_projectionFormulaMap_of_isEquivalence`: the map is invertible at any `K` by which
  tensoring is an equivalence on both sides.
* `isIso_projectionFormulaMap_singleUnit`: the map is invertible at `𝒪_𝒟` placed in any degree.
* `isIso_projectionFormulaMap_of_isStrictlyPerfect`: the map is invertible at every shift of the
  image of a strictly perfect complex.

## Implementation notes

The base case does not use any coherence of the comparison of [Stacks, Tag 07A4] with the unit
constraints: tensoring with a shift of the structure sheaf is an equivalence on both sides, and
for such an object the abstract projection formula map of an adjunction is invertible as soon as
the comparison is, by a Yoneda argument (`Stacks.ProjectionFormula.isIso_adjunctionTensorMap`).

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- **Equation 21.50.0.1 of [Stacks, Tag 0B56]** for a morphism of ringed topoi
`f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)`: the canonical map
`Rf_*E ⊗^𝐋_{𝒪_𝒟} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)`, adjoint for `Lf^* ⊣ Rf_*` to the comparison of
[Stacks, Tag 07A4] followed by the counit `Lf^*Rf_*E ⟶ E` in the first factor. -/
def projectionFormulaMap
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward (X := X) (Y := Y) f).obj E)).obj K ⟶
      (derivedPushforward (X := X) (Y := Y) f).obj
        (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj K)) :=
  CategoryTheory.adjunctionTensorMap (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom E K

/-- Equation 21.50.0.1 is natural in the complex on the target. -/
theorem projectionFormulaMap_naturality_target
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (k : K ⟶ K') :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward (X := X) (Y := Y) f).obj E)).map k ≫
        projectionFormulaMap f E K' =
      projectionFormulaMap f E K ≫
        (derivedPushforward (X := X) (Y := Y) f).map
          (((derivedTensorProductFunctor X.O).obj E).map ((derivedPullback f).map k)) := by
  have h := CategoryTheory.adjunctionTensorMap_natural (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom (𝟙 E) k
  simpa [projectionFormulaMap] using h

/-- Equation 21.50.0.1, for a fixed `E`, as a natural transformation between functors of the
complex on the target. -/
def projectionFormulaNatTrans
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorProductFunctor Y.O).obj ((derivedPushforward (X := X) (Y := Y) f).obj E) ⟶
      (derivedPullback f : DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
        (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward (X := X) (Y := Y) f where
  app := projectionFormulaMap f E
  naturality _ _ k := projectionFormulaMap_naturality_target f E k

/-- **Equation 21.50.0.1 is invertible at a `K` by which tensoring is an equivalence**, on both
sides. This is the abstract projection formula `Stacks.ProjectionFormula.isIso_adjunctionTensorMap`
at the derived adjunction of [Stacks, Tag 07A6] and the comparison of [Stacks, Tag 07A4], which
is invertible at every pair. -/
theorem isIso_projectionFormulaMap_of_isEquivalence
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hY : (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.O)) K).IsEquivalence)
    (hX : (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
      ((derivedPullback f).obj K)).IsEquivalence) :
    IsIso (projectionFormulaMap f E K) :=
  @Stacks.ProjectionFormula.isIso_adjunctionTensorMap _ _ _ _ _ _ (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom E K hY hX
    (fun M => ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).app
      (M, K)).isIso_hom)

/-- **Tensoring on the right by a shift of the structure sheaf is an equivalence** of `D(𝒪)`,
for a ringed topos: it is the shift. -/
theorem isEquivalence_tensorRight_unitShift (Z : RingedTopos.{u, u, u})
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (m : ℤ) :
    (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor Z.O))
      ((unitObject ⟨Z.C, Z.J, Z.O⟩)⟦m⟧)).IsEquivalence :=
  Functor.isEquivalence_tensorRightOf_shiftedUnit (derivedTensorProductFunctor Z.O)
    (unitObject ⟨Z.C, Z.J, Z.O⟩)
    ((canonicalDerivedTensorProduct Z.O).rightUnitorNatIso ⟨Z.C, Z.J, Z.O⟩) m

/-- **The derived pullback of a shift of the structure sheaf**, `Lf^*(𝒪_𝒟[0]⟦m⟧) ≅ 𝒪_𝒞[0]⟦m⟧`,
for a morphism of ringed topoi: `Lf^*` commutes with the shift and carries `𝒪_𝒟[0]` to
`𝒪_𝒞[0]`. -/
def derivedPullbackUnitShiftIso (m : ℤ) :
    (derivedPullback f).obj ((unitObject ⟨Y.C, Y.J, Y.O⟩)⟦m⟧) ≅
      (unitObject ⟨X.C, X.J, X.O⟩)⟦m⟧ :=
  ((derivedPullback f).commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (derivedPullbackUnitIso f)

/-- **[Stacks, Tag 0944] for `K` a shift of the structure sheaf**: Equation 21.50.0.1 is
invertible at `𝒪_𝒟[0]⟦m⟧`, for every morphism of ringed topoi and every `E`. -/
theorem isIso_projectionFormulaMap_unitShift
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (m : ℤ) :
    IsIso (projectionFormulaMap f E ((unitObject ⟨Y.C, Y.J, Y.O⟩)⟦m⟧)) :=
  isIso_projectionFormulaMap_of_isEquivalence f E _
    (isEquivalence_tensorRight_unitShift Y m)
    (Functor.isEquivalence_tensorRightOf_of_iso (derivedTensorProductFunctor X.O)
      (derivedPullbackUnitShiftIso f m) (isEquivalence_tensorRight_unitShift X m))

/-- **[Stacks, Tag 0944] for `K` the structure sheaf placed in any degree.** -/
theorem isIso_projectionFormulaMap_singleUnit
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (i : ℤ) :
    IsIso (projectionFormulaMap f E
      (Stacks.Cohomology.ProjectionFormulaPerfectDevissage.singleUnit Y.O i)) := by
  have e : (unitObject ⟨Y.C, Y.J, Y.O⟩)⟦-i⟧ ≅
      Stacks.Cohomology.ProjectionFormulaPerfectDevissage.singleUnit Y.O i :=
    ((DerivedCategory.singleFunctors
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).shiftIso
        (-i) i 0 (by omega)).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  exact ((projectionFormulaNatTrans f E).isIso_app_iff_of_iso e).mp
    (isIso_projectionFormulaMap_unitShift f E (-i))

/-- **[Stacks, Tag 0944] for a strictly perfect complex.** For a morphism of ringed topoi `f` and
every `E ∈ D(𝒪_𝒞)`, Equation 21.50.0.1 is invertible at every shift of the image in `D(𝒪_𝒟)` of
a strictly perfect complex of `𝒪_𝒟`-modules. Both sides are exact functors of `K` and the map is
invertible at the structure sheaf placed in every degree, so the dévissage of a strictly perfect
complex along its stupid truncations and the direct summands of its terms applies. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (n : ℤ) :
    IsIso (projectionFormulaMap f E ((DerivedCategory.Q.obj P)⟦n⟧)) := by
  let _ : ((derivedTensorProductFunctor X.O).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.O).commShift_right _
  let _ : ((derivedTensorProductFunctor X.O).obj E).IsTriangulated :=
    (canonicalDerivedTensorProduct X.O).exact_right _
  let _ : (derivedPullback f).IsTriangulated := derivedPullback_isTriangulated f
  let _ : (derivedPushforward (X := X) (Y := Y) f).CommShift ℤ :=
    (derivedAdjunction f).rightAdjointCommShift ℤ
  let _ : (derivedAdjunction f).CommShift ℤ := (derivedAdjunction f).commShift_of_leftAdjoint ℤ
  let _ : (derivedPushforward (X := X) (Y := Y) f).IsTriangulated :=
    (derivedAdjunction f).isTriangulated_rightAdjoint
  let _ : ((derivedTensorProductFunctor X.O).obj E ⋙
      derivedPushforward (X := X) (Y := Y) f).CommShift ℤ :=
    Functor.CommShift.comp _ _
  exact
    Stacks.Cohomology.ProjectionFormulaPerfectDevissage.isIso_app_of_isStrictlyPerfect_of_singleUnit
    Y.O ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward (X := X) (Y := Y) f).obj E))
    ((derivedPullback f : DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
      (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward (X := X) (Y := Y) f)
    ((canonicalDerivedTensorProduct Y.O).commShift_right _) (Functor.CommShift.comp _ _)
    ((canonicalDerivedTensorProduct Y.O).exact_right _) inferInstance
    (projectionFormulaNatTrans f E) (isIso_projectionFormulaMap_singleUnit f E) P hP n

end Stacks.Cohomology.ProjectionFormulaOfToposHom

end
