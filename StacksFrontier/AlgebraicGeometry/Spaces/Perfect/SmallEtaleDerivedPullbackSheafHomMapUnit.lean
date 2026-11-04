module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomShiftedUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# The map of Stacks 08I3 on algebraic spaces out of a translate of the structure sheaf

Let `f : X ⟶ Y` be a morphism of algebraic spaces. The canonical map of Stacks 08I3,
`Lf^*R𝓗om(K, L) ⟶ R𝓗om(Lf^*K, Lf^*L)`
(`AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomMap`), is an isomorphism for every
`L` when `K` is isomorphic to a translate `𝒪_Y[0]⟦n⟧` of the structure sheaf. This is the unit
case of the dévissage to perfect `K`, with every translate included, which is what the
dévissage consumes.

The argument uses no compatibility of Stacks 07A4 with a unitor. The map is the transpose of
`Lf^*R𝓗om(K, L) ⊗^L Lf^*K ≅ Lf^*(R𝓗om(K, L) ⊗^L K) ⟶ Lf^*L`, so it is invertible as soon as
tensoring with `K` on `Y` and with `Lf^*K` on `X` are equivalences
(`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.isIso_homComparison_of_isEquivalence`).
For `K ≅ 𝒪_Y[0]⟦n⟧` we have `Lf^*K ≅ 𝒪_X[0]⟦n⟧`, and on either space `R𝓗om(𝒪[0]⟦n⟧, -)` is the
translation `(-)⟦-n⟧` (`AlgebraicGeometry.RingedSite.derivedSheafHomShiftedUnitIso` on the
model), an equivalence, so its left adjoint `- ⊗^L 𝒪[0]⟦n⟧` is one too.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleShiftedUnit`: the translate `𝒪_X[0]⟦n⟧`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackShiftedUnitIso`:
  `Lf^*(𝒪_Y[0]⟦n⟧) ≅ 𝒪_X[0]⟦n⟧`.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_smallEtaleDerivedSheafHom_obj_of_iso`:
  `R𝓗om(P, -)` is an autoequivalence of `D(𝒪_X)` for `P ≅ 𝒪_X[0]⟦n⟧`.
* `AlgebraicGeometry.Space.isEquivalence_tensorRightOf_smallEtaleDerivedTensor_of_iso`: so is
  `- ⊗^L P`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_iso_shiftedUnit`:
  the map of Stacks 08I3 is an isomorphism out of `K ≅ 𝒪_Y[0]⟦n⟧`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_singleFunctor_unit`:
  the same at the structure sheaf placed in an arbitrary degree.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance 2000] abelian_ringedToposStructureRingSheafModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The translate `𝒪_X[0]⟦n⟧` of the structure sheaf of an algebraic space placed in degree
zero. -/
abbrev smallEtaleShiftedUnit (X : AlgebraicSpaces B S hS) (n : ℤ) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))⟦n⟧

/-- **`R𝓗om(P, -)` is an autoequivalence of `D(𝒪_X)` when `P` is a translate of the structure
sheaf.** On the model it is the translation `(-)⟦-n⟧`, and the derived equivalence with the
model carries `𝒪_X[0]⟦n⟧` to the translate of the structure sheaf of the model. -/
theorem isEquivalence_smallEtaleDerivedSheafHom_obj_of_iso (X : AlgebraicSpaces B S hS)
    {P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))} (n : ℤ)
    (e : P ≅ smallEtaleShiftedUnit B S hS X n) :
    ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).IsEquivalence := by
  let E := smallEtaleModelDerivedEquivalence B S hS X
  let M := smallEtaleModelRingedSite B S hS X.1 X.2
  have e' : E.functor.obj P ≅ (RingedSite.derivedStructureSheaf M)⟦n⟧ :=
    E.functor.mapIso e ≪≫
      ((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategory.commShiftIso
        n).app _ ≪≫
      (shiftFunctor _ n).mapIso (smallEtaleModelDerivedStructureSheafIso B S hS X)
  have := RingedSite.isEquivalence_derivedSheafHomBifunctor_obj_of_iso M n e'
  exact inferInstanceAs
    ((E.functor ⋙ (RingedSite.derivedSheafHomBifunctor M).obj (op (E.functor.obj P))) ⋙
      E.inverse).IsEquivalence

/-- **Tensoring with a translate of the structure sheaf is an autoequivalence of `D(𝒪_X)`**: it is
left adjoint to `R𝓗om(P, -)`, an equivalence by
`AlgebraicGeometry.Space.isEquivalence_smallEtaleDerivedSheafHom_obj_of_iso`. -/
theorem isEquivalence_tensorRightOf_smallEtaleDerivedTensor_of_iso (X : AlgebraicSpaces B S hS)
    {P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))} (n : ℤ)
    (e : P ≅ smallEtaleShiftedUnit B S hS X n) :
    (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)) P).IsEquivalence := by
  have := isEquivalence_smallEtaleDerivedSheafHom_obj_of_iso X n e
  have :=
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).isEquivalence_left_of_isEquivalence_right
  exact Functor.isEquivalence_of_iso
    (Functor.tensorRightOfUncurryIso (smallEtaleDerivedTensor B S hS X) P).symm

variable {X Y : AlgebraicSpaces B S hS}

/-- **`Lf^*(𝒪_Y[0]⟦n⟧) ≅ 𝒪_X[0]⟦n⟧`**: the derived pullback commutes with the translation and
carries the structure sheaf to the structure sheaf. -/
def smallEtaleDerivedModulePullbackShiftedUnitIso (f : X ⟶ Y) (n : ℤ) :
    (smallEtaleDerivedModulePullback B S hS f).obj (smallEtaleShiftedUnit B S hS Y n) ≅
      smallEtaleShiftedUnit B S hS X n :=
  ((smallEtaleDerivedModulePullback B S hS f).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso (smallEtaleDerivedModulePullbackUnitIso f)

/-- **Stacks 08I3 out of a translate of the structure sheaf.** For `f : X ⟶ Y` and
`K ≅ 𝒪_Y[0]⟦n⟧`, the map `Lf^*R𝓗om(K, L) ⟶ R𝓗om(Lf^*K, Lf^*L)` is an isomorphism for every `L`. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_iso_shiftedUnit (f : X ⟶ Y)
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} (n : ℤ)
    (e : K ≅ smallEtaleShiftedUnit B S hS Y n)
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap f K L) := by
  have := isEquivalence_tensorRightOf_smallEtaleDerivedTensor_of_iso Y n e
  have := isEquivalence_tensorRightOf_smallEtaleDerivedTensor_of_iso X n
    ((smallEtaleDerivedModulePullback B S hS f).mapIso e ≪≫
      smallEtaleDerivedModulePullbackShiftedUnitIso f n)
  exact Transpose.isIso_homComparison_of_isEquivalence _ _ _ _ _ _ _ _
    (tensorHomEquivNaturalLeft_smallEtale B S hS Y) (tensorHomEquivNaturalLeft_smallEtale B S hS X)
    K L

/-- **Stacks 08I3 at the structure sheaf placed in an arbitrary degree**: `𝒪_Y[0]` placed in
degree `i` is the translate `𝒪_Y[0]⟦-i⟧`. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_singleFunctor_unit (f : X ⟶ Y) (i : ℤ)
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap f
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) i).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) L) :=
  isIso_smallEtaleDerivedPullbackSheafHomMap_of_iso_shiftedUnit f (-i)
    (((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by omega)).app _).symm L

end AlgebraicGeometry.Space

end
