module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualTriangleComparison

/-!
# The first morphism of the dual triangle, from a derived identity at a K-injective target

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`.
The isomorphism assertion of [Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B) is
proved in `StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleComparison.lean`
from a single hypothesis `hmor₁`: that under the identification
`Stacks.Divisors.dualTriangleSecondVertexIso` of the second vertex of the dual triangle of the
ideal sequence, the triangle's first morphism is the derived evaluation at one.

**This file reduces `hmor₁` to one identity at the class of a K-injective complex**, namely
`Stacks.Divisors.DualTriangleFirstMapDerivedCore`: that restriction along the unit
`𝒪_X ⟶ i_* 𝒪_D` followed by the trivialisation of `R ℰom_X(𝒪_X[0], -)` agrees with the
identification on K-injective representatives of [Stacks, Tag 0E2I] at the source `𝒪_D[0]`,
followed by the trivialisation of `R ℰom_D(𝒪_D[0], -)` pushed forward and by the trace of
[Stacks, Tag 0A76].  No hypothesis beyond that is used, and none of the reduction is conditional.

## Why the reduction is not automatic

Both sides of `hmor₁` are natural transformations `R ℰom(Ri_* 𝒪_D, -) ⟶ 𝟭`
(`Stacks.Divisors.dualTriangleFirstNatTrans` and
`Stacks.Divisors.derivedEvaluationAtOneNatTrans`), and
`Stacks.Divisors.dualTriangleFirstMap_of_natTrans_app` turns an agreement of those two at *any*
object isomorphic to `𝒪_X[0]` into `hmor₁`.  The agreement is to be checked at the class of a
K-injective complex, because that is where the bifunctor form of [Stacks, Tag 0A77] has a
component formula (`derivedSheafHomExactSupportPushforwardNatIso_app_isKInjective`), and the
right-hand side is the trace of [Stacks, Tag 0A76] carried across that bifunctor form by
`Stacks.Divisors.derivedEvaluationAtOneNatTrans_eq_counit`. A K-injective complex whose class
*is* isomorphic to `𝒪_X[0]` is supplied by [Stacks, Tag 079P] in the form
`Stacks.DerivedFunctor.exists_quasiIso_isKInjective`, whose quasi-isomorphism becomes invertible
in the derived category.

## Main definitions

* `Stacks.Divisors.DualTriangleFirstMapDerivedCore`: the one remaining identity, stated at every
  K-injective cochain complex of `𝒪_X`-modules.

## Main results

* `Stacks.Divisors.dualTriangleFirstNatTrans_app_eq_of_derivedCore`: the core gives the agreement
  of the two natural transformations at the class of a K-injective complex.
* `Stacks.Divisors.dualTriangleFirstMap_of_derivedCore`: **the core gives `hmor₁`.**  The core
  itself follows from a cochain-level identity, by
  `Stacks.Divisors.dualTriangleFirstMapDerivedCore_of_cochainCore`.
* `Stacks.Divisors.isIso_normalShiftToDualTriangleVertex_of_derivedCore` and
  `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_derivedCore`: **the
  core gives the isomorphism assertion of [Stacks, Tag 0B4B]**, through the triangulated argument
  of `Stacks.Divisors.isIso_normalShiftToDualTriangleVertex_of_dualTriangleFirstMap`.

## What is not done

The core itself is now proved, by way of the identity of sections it reduces to; see
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`
(`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleFirstMapSectionsCore.lean`).
It is the derived shadow of the cochain-level identity about
`…ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplex` at the source `𝒪_D[0]`
described in the "What is not done" section of
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleComparison.lean`, whose
underived core
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit` is
proved.

**Deriving the core from that cochain-level identity is now done.** It is
`Stacks.Divisors.dualTriangleFirstMapDerivedCore_of_cochainCore`
(`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleFirstMapCochain.lean`),
which takes the cochain-level identity in the form
`Stacks.Divisors.DualTriangleFirstMapCochainCore` and returns the core; so the whole of the
remaining obligation of [Stacks, Tag 0B4B] is that identity of morphisms of cochain complexes,
and `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_cochainCore` is the
isomorphism assertion from it alone.  The three passages it needed are all discharged: the unit
`𝒪_X[0] ⟶ Ri_* 𝒪_D[0]` (`Stacks.Divisors.pushforwardStructureSheafDerivedUnit`) as the class of a
morphism of complexes, by
`Stacks.Divisors.pushforwardStructureSheafDerivedUnit_comp_mapDerivedCategoryFactors`; the trace
of [Stacks, Tag 0A76] at a K-injective class in terms of the underived trace of
[Stacks, Tag 0A75], by
`…derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q_of_isKInjective`
(`…/RightAdjointLemmas/ExactSupportDerivedTrace.lean`); and the two trivialisations of the
derived internal Hom out of the structure sheaf at a K-injective class, by
`…ClosedQuotientMorphismOfRingedSpaces.derivedStructureSheafHomNatIso_hom_app_Q` and
`…ClosedQuotientMorphismOfRingedSpaces.derivedStructureSheafHomIso_exactSupport_kInjective`
(`…/RightAdjointLemmas/ExactSupportDerivedUnitSource.lean`), both off
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_model`.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (derivedSheafHom ringedSite)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **The derived core of the remaining obligation of [Stacks, Tag 0B4B]:** at the class of every
K-injective cochain complex `I` of `𝒪_X`-modules, restriction along the unit `𝒪_X ⟶ i_* 𝒪_D`
followed by the trivialisation of `R ℰom_X(𝒪_X[0], -)` is the identification on K-injective
representatives of [Stacks, Tag 0E2I] at the source `𝒪_D[0]`, followed by the trivialisation of
`R ℰom_D(𝒪_D[0], -)` pushed forward and by the trace of [Stacks, Tag 0A76].

Both sides are morphisms `R ℰom_X(Ri_* 𝒪_D[0], Q I) ⟶ Q I` in `D(𝒪_X)`.  This is the whole of
the remaining content of the hypothesis `hmor₁` of
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`, by
`Stacks.Divisors.dualTriangleFirstMap_of_derivedCore`. -/
def DualTriangleFirstMapDerivedCore : Prop :=
  ∀ (I : CochainComplex
      (SheafOfModules.{u} (structureSheafRing (closedQuotient D).X)) ℤ)
    [I.IsKInjective],
    ((derivedSheafHom X.sheaf).map (pushforwardStructureSheafDerivedUnit D).op).app
          (DerivedCategory.Q.obj I) ≫
        (RingedSite.derivedStructureSheafHomNatIso (ringedSite X.sheaf)).hom.app
          (DerivedCategory.Q.obj I) =
      ((closedQuotient D).derivedSheafHomPushforwardModelIso
            (RingedSite.structureSheafComplex (ringedSite (closedQuotient D).Z.sheaf)) I).hom ≫
        (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
            ((RingedSite.derivedStructureSheafHomNatIso
              (ringedSite (closedQuotient D).Z.sheaf)).hom.app
                ((closedQuotient D).derivedSheafHomExactSupport.obj
                  (DerivedCategory.Q.obj I))) ≫
          (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
            (DerivedCategory.Q.obj I)

omit [IsEffectiveCartierDivisor D] in
/-- **The derived core gives the agreement of the two natural transformations
`R ℰom(Ri_* 𝒪_D, -) ⟶ 𝟭` at the class of a K-injective complex.**

The right-hand side is the trace of [Stacks, Tag 0A76] read backwards through the bifunctor form
of [Stacks, Tag 0A77] (`Stacks.Divisors.derivedEvaluationAtOneNatTrans_eq_counit`), and at a
K-injective class that form has the component formula
`…derivedSheafHomExactSupportPushforwardNatIso_app_isKInjective`; inverting the two factors of
that formula turns the component of its inverse into the two factors the core is stated with. -/
theorem dualTriangleFirstNatTrans_app_eq_of_derivedCore
    (hcore : DualTriangleFirstMapDerivedCore D)
    (I : CochainComplex
      (SheafOfModules.{u} (structureSheafRing (closedQuotient D).X)) ℤ)
    [I.IsKInjective] :
    (dualTriangleFirstNatTrans D).app (DerivedCategory.Q.obj I) =
      (derivedEvaluationAtOneNatTrans D).app (DerivedCategory.Q.obj I) := by
  have h := (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso_app_isKInjective I
  have hinv : (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.inv.app
        (DerivedCategory.Q.obj I) =
      ((closedQuotient D).derivedSheafHomPushforwardModelIso
            (RingedSite.structureSheafComplex (ringedSite (closedQuotient D).Z.sheaf)) I).hom ≫
        (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
          ((RingedSite.derivedStructureSheafHomNatIso
            (ringedSite (closedQuotient D).Z.sheaf)).hom.app
              ((closedQuotient D).derivedSheafHomExactSupport.obj
                (DerivedCategory.Q.obj I))) :=
    congrArg Iso.inv (Iso.ext h :
      (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.app
          (DerivedCategory.Q.obj I) =
        (modulePushforward (closedQuotient D).i).mapDerivedCategory.mapIso
            ((RingedSite.derivedStructureSheafHomNatIso
              (ringedSite (closedQuotient D).Z.sheaf)).app
                ((closedQuotient D).derivedSheafHomExactSupport.obj
                  (DerivedCategory.Q.obj I))).symm ≪≫
          ((closedQuotient D).derivedSheafHomPushforwardModelIso
              (RingedSite.structureSheafComplex
                (ringedSite (closedQuotient D).Z.sheaf)) I).symm)
  rw [derivedEvaluationAtOneNatTrans_eq_counit]
  change ((derivedSheafHom X.sheaf).map (pushforwardStructureSheafDerivedUnit D).op).app
        (DerivedCategory.Q.obj I) ≫
      (RingedSite.derivedStructureSheafHomNatIso (ringedSite X.sheaf)).hom.app
        (DerivedCategory.Q.obj I) =
    (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.inv.app
        (DerivedCategory.Q.obj I) ≫
      (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        (DerivedCategory.Q.obj I)
  refine (hcore I).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg
    (fun t => t ≫
      (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        (DerivedCategory.Q.obj I))
    hinv.symm

/-- **The derived core gives the hypothesis `hmor₁`** of
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`:
that under `Stacks.Divisors.dualTriangleSecondVertexIso` the dual triangle's first morphism is
the derived evaluation at one.

The structure sheaf of `X` in degree zero admits a quasi-isomorphism into a K-injective complex
by [Stacks, Tag 079P]; that quasi-isomorphism becomes invertible in the derived category, so the
class of the K-injective complex is isomorphic to `𝒪_X[0]`, and
`Stacks.Divisors.dualTriangleFirstMap_of_natTrans_app` descends the agreement of the two natural
transformations there to the component at `𝒪_X[0]`, which is `hmor₁`. -/
theorem dualTriangleFirstMap_of_derivedCore (hcore : DualTriangleFirstMapDerivedCore D) :
    ((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫
        (dualTriangleSecondVertexIso D).hom =
      (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).inv ≫
        derivedSheafHomEvaluationAtOne D := by
  obtain ⟨J, q, hJ, hq⟩ := Stacks.DerivedFunctor.exists_quasiIso_isKInjective
    (RingedSite.structureSheafComplex (ringedSite X.sheaf) :
      CochainComplex (SheafOfModules.{u}
        (structureSheafRing (closedQuotient D).X)) ℤ)
  have : CochainComplex.IsKInjective
      (show CochainComplex (SheafOfModules.{u}
        (structureSheafRing (closedQuotient D).X)) ℤ from J) := hJ
  have := hq
  have : IsIso (DerivedCategory.Q.map q) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact dualTriangleFirstMap_of_natTrans_app D _ (asIso (DerivedCategory.Q.map q)).symm
    (dualTriangleFirstNatTrans_app_eq_of_derivedCore D hcore J)

/-- **The derived core gives the isomorphism assertion of [Stacks, Tag 0B4B]** in the form
carried by the dual triangle of the ideal sequence: the comparison morphism
`Ri_*(𝒩[-1]) ⟶ R ℰom((i_* 𝒪_D)[0], 𝒪_X)` is invertible.  This is
`Stacks.Divisors.isIso_normalShiftToDualTriangleVertex_of_dualTriangleFirstMap` with its
hypothesis supplied by `Stacks.Divisors.dualTriangleFirstMap_of_derivedCore`. -/
theorem isIso_normalShiftToDualTriangleVertex_of_derivedCore
    (hcore : DualTriangleFirstMapDerivedCore D) :
    IsIso (normalShiftToDualTriangleVertex D) :=
  isIso_normalShiftToDualTriangleVertex_of_dualTriangleFirstMap D
    (dualTriangleFirstMap_of_derivedCore D hcore)

/-- **The derived core gives the isomorphism assertion of [Stacks, Tag 0B4B]:** the canonical
comparison morphism `𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)` of an effective Cartier divisor
is an isomorphism.  This is
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`
with its hypothesis supplied by `Stacks.Divisors.dualTriangleFirstMap_of_derivedCore`. -/
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_derivedCore
    (hcore : DualTriangleFirstMapDerivedCore D) :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) :=
  isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap D
    (dualTriangleFirstMap_of_derivedCore D hcore)

end Stacks.Divisors

end
