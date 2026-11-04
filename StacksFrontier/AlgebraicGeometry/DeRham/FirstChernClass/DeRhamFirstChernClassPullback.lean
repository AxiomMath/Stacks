module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DerivedSectionsPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.LogarithmicDifferentialPullback
public import StacksFrontier.AlgebraicGeometry.Picard.FirstCohomologyNaturality
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The de Rham first Chern class commutes with pullback

Let

```
X' --f--> X
|         |
S' -----> S
```

be a commutative square of schemes. The de Rham first Chern class
`c₁^{dR} : Pic(X) ⟶ H²_{dR}(X/S)` of [Stacks, Tag 0FLE] is built out of `d log`, read as a
morphism of complexes of abelian sheaves `𝒪_X^*[-1] ⟶ Ω^•_{X/S}`, and the identification
`Pic(X) = H¹(X, 𝒪_X^*) = H²(X, 𝒪_X^*[-1])` of [Stacks, Tag 09NU]. This file carries the first of
those two steps across the square: `d log` commutes with the pullback maps, hence so does the
map it induces on degree-two hypercohomology.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.shiftedUnitsDerivedSectionsPullback`: **pullback on
  `RΓ(X, 𝒪_X^*[-1])`** along the square — pullback on derived global sections
  (`AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback`) along the map of complexes
  `𝒪_X^*[-1] ⟶ f_*(𝒪_{X'}^*[-1])` of
  `AlgebraicGeometry.Scheme.Hom.unitsComplexPushforwardMapPlus`.
* `AlgebraicGeometry.Scheme.Hom.shiftedUnitsCohomologyTwoPullback`: **pullback on
  `H²(X, 𝒪_X^*[-1])`**, the map it induces on degree-two hypercohomology.

## Main results

* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_logarithmicDifferential`: **`d log`
  commutes with pullback on derived global sections**: the square formed by `d log`, by pullback
  on `RΓ(-, 𝒪^*[-1])` and by the de Rham pullback of [Stacks, Tag 0FL6] commutes.
* `AlgebraicGeometry.Scheme.Hom.logarithmicDifferentialCohomologyMap_pullback`: the same square
  on degree-two hypercohomology, against the de Rham pullback
  `f^* : H²_{dR}(X/S) ⟶ H²_{dR}(X'/S')`.
* `AlgebraicGeometry.Scheme.Hom.h1UnitsAddEquivPicard_symm_schemePullbackClassHom`: **Tag 09NU's
  naturality read backwards**, which is the orientation the first Chern classes consume it in.
* `AlgebraicGeometry.Scheme.Hom.unitsPushforward_edge_comp_rightDerivedIso`: the pullback of
  first cohomology classes of the sheaf of units, transported from Mathlib's `ℕ`-indexed right
  derived functor to the `ℤ`-indexed one of
  `CategoryTheory.Functor.rightDerivedPlus`.

## Implementation notes

Both squares are instances of the functoriality
`AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_naturality` of pullback on derived global
sections, applied to the complex-level `d log` square
`AlgebraicGeometry.Scheme.Hom.unitsComplexPushforwardMapPlus_logarithmicDifferentialComplexMapPlus`.
That the de Rham pullback of [Stacks, Tag 0FL6] is the generic construction at the de Rham map
of complexes is `AlgebraicGeometry.Scheme.Hom.deRhamDerivedSectionsPullback_eq`, which holds by
definition. It is nevertheless rewritten with rather than left to unification, and the four
complexes of the square are supplied explicitly: left to solve `f_*(-)` applied to an unknown
bounded-below complex against `AlgebraicGeometry.Scheme.Hom.deRhamPushforwardPlus`, elaboration
spends the whole heartbeat budget on the structural eta of the full subcategory of bounded-below
complexes, while with the four complexes named the same check is immediate.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  (hcomm : f ≫ p = p' ≫ g)

/-- **Pullback on derived global sections of the sheaf of units placed in degree one**,
`RΓ(X, 𝒪_X^*[-1]) ⟶ RΓ(X', 𝒪_{X'}^*[-1])`: pullback along the morphism of complexes
`𝒪_X^*[-1] ⟶ f_*(𝒪_{X'}^*[-1])` carrying the pullback of units. -/
def shiftedUnitsDerivedSectionsPullback :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (SheafOfModules.unitsComplexPlus X.toRingedSpace)) ⟶
      (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (SheafOfModules.unitsComplexPlus X'.toRingedSpace)) :=
  derivedSectionsPullback f (unitsComplexPushforwardMapPlus f)

/-- **Pullback on the degree-two hypercohomology of the sheaf of units placed in degree one**,
`H²(X, 𝒪_X^*[-1]) ⟶ H²(X', 𝒪_{X'}^*[-1])`. -/
def shiftedUnitsCohomologyTwoPullback :
    SheafOfModules.shiftedUnitsCohomologyTwo X.toRingedSpace ⟶
      SheafOfModules.shiftedUnitsCohomologyTwo X'.toRingedSpace :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
    (shiftedUnitsDerivedSectionsPullback f)

/-- **Logarithmic differentiation commutes with pullback on derived global sections**: the square
formed by `d log : 𝒪^*[-1] ⟶ Ω^•`, by pullback on `RΓ(-, 𝒪^*[-1])` and by the de Rham pullback
`f^* : RΓ(X, Ω^•_{X/S}) ⟶ RΓ(X', Ω^•_{X'/S'})` of [Stacks, Tag 0FL6] commutes.

This is the functoriality of pullback on derived global sections applied to the complex-level
`d log` square, the de Rham pullback being that construction at the canonical map of de Rham
complexes. -/
theorem derivedSectionsPullback_logarithmicDifferential :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (SheafOfModules.logarithmicDifferentialComplexMapPlus (deRhamAlgebras p)
              (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))) ≫
        deRhamDerivedSectionsPullback f p p' g hcomm =
      shiftedUnitsDerivedSectionsPullback f ≫
        (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (SheafOfModules.logarithmicDifferentialComplexMapPlus (deRhamAlgebras p')
              (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))) := by
  rw [deRhamDerivedSectionsPullback_eq, shiftedUnitsDerivedSectionsPullback]
  exact derivedSectionsPullback_naturality f
    (K := SheafOfModules.unitsComplexPlus X.toRingedSpace)
    (L := SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
    (K' := SheafOfModules.unitsComplexPlus X'.toRingedSpace)
    (L' := SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))
    (unitsComplexPushforwardMapPlus f)
    (deRhamAbelianPushforwardMapPlus f p p' g hcomm)
    (SheafOfModules.logarithmicDifferentialComplexMapPlus (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
    (SheafOfModules.logarithmicDifferentialComplexMapPlus (deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))
    (unitsComplexPushforwardMapPlus_logarithmicDifferentialComplexMapPlus f p p' g hcomm)

/-- **Logarithmic differentiation commutes with pullback on degree-two hypercohomology**: the
map `H²(X, 𝒪_X^*[-1]) ⟶ H²_{dR}(X/S)` induced by `d log` commutes with pullback on the two
groups. -/
theorem logarithmicDifferentialCohomologyMap_pullback :
    SheafOfModules.logarithmicDifferentialCohomologyMap (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ≫
        deRhamCohomologyPullback f p p' g hcomm 2 =
      shiftedUnitsCohomologyTwoPullback f ≫
        SheafOfModules.logarithmicDifferentialCohomologyMap (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p')) :=
  Eq.trans
    (Eq.trans ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map_comp _ _).symm
      (congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        (derivedSectionsPullback_logarithmicDifferential f p p' g hcomm)))
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map_comp _ _)

/-! ### Tag 09NU read backwards -/

/-- **Stacks Project, Tag 09NU, naturality read backwards.** The inverse of the identification
`Pic(X) = H¹(X, 𝒪_X^*)` carries the pullback of a Picard class to the pullback of its first
cohomology class.

This is the form in which the first Chern classes consume Tag 09NU: both
`AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass` and
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian` are the *inverse* equivalence
followed by the map induced by `d log`. It is
`Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_naturality` applied at the first cohomology
class of `c`.

Note that `Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard` is by definition
`Stacks.GluePicard.h1UnitsAddEquivSmallPicard` followed by
`Stacks.GluePicard.picardModelAddEquiv`, so this statement is simultaneously about both models of
the Picard group: the model `Stacks.Picard.ofScheme` one universe up, which the Hodge first Chern
class is stated in, and the model `Stacks.SheafOfModules.Picard.PicardGroup` in the universe of
the scheme, which the de Rham first Chern class is stated in. -/
@[ega "0 5.4.8" "5.4.8, special case"]
theorem h1UnitsAddEquivPicard_symm_schemePullbackClassHom (c : Stacks.Picard.ofScheme X) :
    (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X').symm
        (Stacks.Picard.schemePullbackClassHom f c) =
      (abelianEdgeMap.{u, u} f.base 1).app
        (Stacks.Cohomology.Generators.unitsSheaf X'.toRingedSpace)
        ((abelianCohomology.{u, u} _ ⊤ 1).map (Stacks.GlueSquishUnits.unitsPushforwardMap f)
          ((Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X).symm c)) := by
  have hnat := Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_naturality f
    ((Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X).symm c)
  rw [(Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X).apply_symm_apply] at hnat
  exact (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X').symm_apply_eq.mpr hnat.symm

/-- **Pullback of first cohomology classes of the sheaf of units, transported to the `ℤ`-indexed
right derived functor.** The pullback Tag 09NU is natural for — the map induced by
`𝒪_X^* ⟶ f_*𝒪_{X'}^*` on `H¹`, followed by the first Leray edge map — corresponds under
`Stacks.DerivedIndexing.rightDerivedIso` to the map induced by the pullback of units on
`CategoryTheory.Functor.rightDerivedPlus`, followed by the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge` of a composite of right derived functors.

This is the first of the two steps carrying Tag 09NU into the spelling the de Rham first Chern
class is stated in. The remaining step is the degree shift
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`, which moves a statement about
`H¹` of a sheaf placed in degree zero to one about `H²` of that sheaf placed in degree one. -/
theorem unitsPushforward_edge_comp_rightDerivedIso :
    (abelianCohomology.{u, u} _ ⊤ 1).map (Stacks.GlueSquishUnits.unitsPushforwardMap f) ≫
          (abelianEdgeMap.{u, u} f.base 1).app
            (Stacks.Cohomology.Generators.unitsSheaf X'.toRingedSpace) ≫
        (Stacks.DerivedIndexing.rightDerivedIso
          (sectionsFunctor X'.toRingedSpace.carrier ⊤) 1).hom.app
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) =
      (Stacks.DerivedIndexing.rightDerivedIso
          (sectionsFunctor X.toRingedSpace.carrier ⊤) 1).hom.app
            (SheafOfModules.unitsAbelianSheaf X.toRingedSpace) ≫
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedPlus (1 : ℤ)).map
            (Stacks.GlueSquishUnits.unitsPushforwardMap f) ≫
          (Stacks.DerivedIndexing.rightDerivedPlusEdge (abelianPushforward.{u, u} f.base)
            (sectionsFunctor X.toRingedSpace.carrier ⊤) (1 : ℤ)).app
              (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) :=
  Stacks.DerivedIndexing.map_comp_edge_comp_rightDerivedIso
    (abelianPushforward.{u, u} f.base) (sectionsFunctor X.toRingedSpace.carrier ⊤) 1
    (Stacks.GlueSquishUnits.unitsPushforwardMap f)

end AlgebraicGeometry.Scheme.Hom

end
