module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualTriangleFirstMap
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedUnitSource

/-!
# The remaining obligation of Tag 0B4B as a cochain-level identity

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`.
The isomorphism assertion of [Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B) is
reduced, in
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleFirstMap.lean`, to the single
derived identity `Stacks.Divisors.DualTriangleFirstMapDerivedCore` at the class of a K-injective
complex.

**This file reduces that identity to a single identity of morphisms of cochain complexes**,
`Stacks.Divisors.DualTriangleFirstMapCochainCore`: that the complex-level isomorphism of
[Stacks, Tag 0E2I] at the source `𝒪_D[0]`, read backwards and followed by the pushforward of
evaluation at the unit section on `D` and by the degreewise trace of [Stacks, Tag 0A75], is
restriction along the unit `𝒪_X ⟶ i_* 𝒪_D` followed by evaluation at the unit section on `X`.
Nothing below `DerivedCategory.Q` is left: the whole of the derived bookkeeping — the two
trivialisations of the derived internal Hom out of the structure sheaf at a K-injective class,
the trace of [Stacks, Tag 0A76] there, and the passage from the unit of `D(𝒪_X)` to a morphism
of complexes — is discharged.

## Main definitions

* `Stacks.Divisors.pushforwardStructureSheafUnitCochain`: **the unit `𝒪_X ⟶ i_* 𝒪_D` as a
  morphism of cochain complexes** `𝒪_X[0] ⟶ i_*(𝒪_D[0])`, namely the second morphism of the
  ideal sequence placed in degree zero, followed by the comparison of the degree-zero single
  functor with pushforward.
* `Stacks.Divisors.DualTriangleFirstMapCochainCore`: the cochain-level identity.

## Main results

* `Stacks.Divisors.pushforwardStructureSheafDerivedUnit_comp_mapDerivedCategoryFactors`: **the
  derived unit `𝒪_X[0] ⟶ Ri_* 𝒪_D[0]` is the class of that morphism of complexes**, read through
  `CategoryTheory.Functor.mapDerivedCategoryFactors`.  This is what lets
  `…derivedSheafHomComparison_naturality_source` be applied to `R ℰom_X(u, -)`.
* `Stacks.Divisors.dualTriangleFirstMapDerivedCore_of_cochainCore`: **the cochain-level identity
  gives `Stacks.Divisors.DualTriangleFirstMapDerivedCore`.**
* `Stacks.Divisors.dualTriangleFirstMap_of_cochainCore`,
  `Stacks.Divisors.isIso_normalShiftToDualTriangleVertex_of_cochainCore` and
  `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_cochainCore`: **the
  cochain-level identity gives the isomorphism assertion of [Stacks, Tag 0B4B]**, through
  `Stacks.Divisors.dualTriangleFirstMap_of_derivedCore`.

## Implementation notes

The derived reduction itself is
`…ClosedQuotientMorphismOfRingedSpaces.derivedCore_of_cochainCore`, stated for a closed quotient
morphism of ringed spaces and an arbitrary pair `(cu, u)` of a morphism of complexes and a
morphism of the derived category matching it; this file only instantiates it at
`closedQuotient D` with the unit.  That the statement has to be made with no scheme in it is not
a matter of generality: the goal of the reduction mixes the spellings `X.sheaf` and
`(closedQuotient D).X.sheaf` of one sheaf of rings, which makes it ill-typed at `implicit`
transparency and so unusable by `rw`.

For the unit as a morphism of complexes, the two factors are Mathlib's: the second morphism of
`CategoryTheory.ShortComplex.ShortExact.singleTriangle` is the degree-zero single functor applied
to the short complex's second map, and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`
says that the comparison of the single functor with `Ri_*`, followed by the identification of
`Ri_*` with the pushforward of complexes, is the class of the corresponding comparison of
complexes.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (derivedSheafHom ringedSite StructureSheafModules)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **The unit `𝒪_X ⟶ i_* 𝒪_D` as a morphism of cochain complexes** `𝒪_X[0] ⟶ i_*(𝒪_D[0])`: the
second morphism of the ideal sequence of [Stacks, Tag 0C6K] placed in degree zero, followed by
the comparison `CategoryTheory.Functor.mapCochainComplexSingleFunctor` of the degree-zero single
functor with pushforward.

Its class in `D(𝒪_X)` is the derived unit
`Stacks.Divisors.pushforwardStructureSheafDerivedUnit`, by
`Stacks.Divisors.pushforwardStructureSheafDerivedUnit_comp_mapDerivedCategoryFactors`. -/
def pushforwardStructureSheafUnitCochain :
    RingedSite.structureSheafComplex (ringedSite X.sheaf) ⟶
      ((modulePushforward (closedQuotient D).i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSite.structureSheafComplex (ringedSite (closedQuotient D).Z.sheaf)) :=
  (CochainComplex.singleFunctor (StructureSheafModules X.sheaf) 0).map
      (divisorIdealShortComplex D).g ≫
    ((modulePushforward (closedQuotient D).i).mapCochainComplexSingleFunctor 0).inv.app
      (SheafOfModules.unit
        (structureSheafRing D.subscheme.toRingedSpace))

omit [IsEffectiveCartierDivisor D] in
/-- **The derived unit `𝒪_X[0] ⟶ Ri_* 𝒪_D[0]` is the class of a morphism of complexes**: read
through the identification `CategoryTheory.Functor.mapDerivedCategoryFactors` of `Ri_*` with the
degreewise pushforward, it is the class of
`Stacks.Divisors.pushforwardStructureSheafUnitCochain`.

The derived unit is the second morphism of the triangle of the ideal sequence followed by the
inverse of the comparison of the degree-zero single functor with `Ri_*`; the first factor is
already the class of a morphism of complexes, and for the second this is
`CategoryTheory.Functor`
`.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`. -/
theorem pushforwardStructureSheafDerivedUnit_comp_mapDerivedCategoryFactors :
    pushforwardStructureSheafDerivedUnit D ≫
        (modulePushforward (closedQuotient D).i).mapDerivedCategoryFactors.hom.app
          (RingedSite.structureSheafComplex (ringedSite (closedQuotient D).Z.sheaf)) =
      DerivedCategory.Q.map (pushforwardStructureSheafUnitCochain D) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂ ≫ t)
        (Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
          (modulePushforward (closedQuotient D).i)
          (SheafOfModules.unit
            (structureSheafRing D.subscheme.toRingedSpace)))).trans
      (DerivedCategory.Q.map_comp _ _).symm)

/-- **The cochain-level core of the remaining obligation of [Stacks, Tag 0B4B]:** for every
cochain complex `I` of `𝒪_X`-modules, the complex-level isomorphism of [Stacks, Tag 0E2I]

`i_* SheafHom^•_D(𝒪_D[0], ℰom^•(𝒪_D, I)) ≅ SheafHom^•_X(i_* 𝒪_D[0], I)`,

read backwards and followed by the pushforward of evaluation at the unit section on `D` and by
the degreewise trace of [Stacks, Tag 0A75], is restriction along the unit `𝒪_X ⟶ i_* 𝒪_D`
followed by evaluation at the unit section on `X`.

Both sides are morphisms of complexes `SheafHom^•_X(i_* 𝒪_D[0], I) ⟶ I`.  This is the whole of
the remaining content of the isomorphism assertion of [Stacks, Tag 0B4B], by
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_cochainCore`.

Its underived core — the same identity for sheaves rather than complexes — is
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit`, which
is proved; what this needs beyond it is that core applied degreewise on sections, through
`…pushforwardSheafHomComplexIso_sections_v`, together with the matching of the two collapses of
`SheafHom^•(𝒪[0], -)`. -/
def DualTriangleFirstMapCochainCore : Prop :=
  ∀ (I : CochainComplex
      (SheafOfModules.{u} (structureSheafRing (closedQuotient D).X)) ℤ),
    ((closedQuotient D).pushforwardSheafHomComplex.iso
          (RingedSite.structureSheafComplex (ringedSite (closedQuotient D).Z.sheaf)) I).inv ≫
        ((modulePushforward (closedQuotient D).i).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            (RingedSite.structureSheafHomEvaluation (ringedSite (closedQuotient D).Z.sheaf)
              (((closedQuotient D).sheafHomExactSupport.mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I)) ≫
          (Adjunction.mapHomologicalComplexAdjunction
            (closedQuotient D).modulePushforwardSheafHomExactSupportAdjunction
              (ComplexShape.up ℤ)).counit.app I =
      sheafHomComplexHomMap (closedQuotient D).X
          (pushforwardStructureSheafUnitCochain D) (𝟙 I) ≫
        RingedSite.structureSheafHomEvaluation (ringedSite X.sheaf) I

omit [IsEffectiveCartierDivisor D] in
/-- **The cochain-level core gives the derived core** of
`Stacks.Divisors.DualTriangleFirstMapDerivedCore`.  This is
`…ClosedQuotientMorphismOfRingedSpaces.derivedCore_of_cochainCore` at the closed quotient
morphism of the divisor, with the unit supplied as a morphism of complexes by
`Stacks.Divisors.pushforwardStructureSheafDerivedUnit_comp_mapDerivedCategoryFactors`. -/
theorem dualTriangleFirstMapDerivedCore_of_cochainCore
    (hc : DualTriangleFirstMapCochainCore D) : DualTriangleFirstMapDerivedCore D := by
  intro I _
  exact (closedQuotient D).derivedCore_of_cochainCore
    (pushforwardStructureSheafUnitCochain D) (pushforwardStructureSheafDerivedUnit D)
    (pushforwardStructureSheafDerivedUnit_comp_mapDerivedCategoryFactors D) I (hc I)

/-- **The cochain-level core gives the hypothesis `hmor₁`** of
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`. -/
theorem dualTriangleFirstMap_of_cochainCore (hc : DualTriangleFirstMapCochainCore D) :
    ((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫
        (dualTriangleSecondVertexIso D).hom =
      (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).inv ≫
        derivedSheafHomEvaluationAtOne D :=
  dualTriangleFirstMap_of_derivedCore D (dualTriangleFirstMapDerivedCore_of_cochainCore D hc)

/-- **The cochain-level core gives the isomorphism assertion of [Stacks, Tag 0B4B]** in the form
carried by the dual triangle of the ideal sequence. -/
theorem isIso_normalShiftToDualTriangleVertex_of_cochainCore
    (hc : DualTriangleFirstMapCochainCore D) :
    IsIso (normalShiftToDualTriangleVertex D) :=
  isIso_normalShiftToDualTriangleVertex_of_derivedCore D
    (dualTriangleFirstMapDerivedCore_of_cochainCore D hc)

/-- **The cochain-level core gives the isomorphism assertion of [Stacks, Tag 0B4B]:** the
canonical comparison morphism `𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)` of an effective
Cartier divisor is an isomorphism. -/
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_cochainCore
    (hc : DualTriangleFirstMapCochainCore D) :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) :=
  isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_derivedCore D
    (dualTriangleFirstMapDerivedCore_of_cochainCore D hc)

end Stacks.Divisors

end
