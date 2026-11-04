module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.ShiftedUnitsPullback
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreePullbackShift

/-!
# The de Rham first Chern class commutes with pullback

Let `f : X' ⟶ X` and `g : S' ⟶ S` be the horizontal arrows of a commutative square of schemes.
The de Rham first Chern class of [Stacks, Tag 0FLE] is the identification
`Pic(X) = H¹(X, 𝒪_X^*)` of [Stacks, Tag 09NU] followed by the map induced on degree-two
hypercohomology by logarithmic differentiation `𝒪_X^*[-1] ⟶ Ω^•_{X/S}`. This file proves
[Stacks, Tag 0FMD] for it: the square formed by `c₁^{dR}`, by pullback of Picard classes and by
the de Rham pullback of [Stacks, Tag 0FL6] commutes.

The second half of the composite is already known to commute with pullback — that is
`AlgebraicGeometry.Scheme.Hom.logarithmicDifferentialCohomologyMap_pullback` — so what is proved
here is the first half: that `Pic(X) ⟶ H²(X, 𝒪_X^*[-1])` commutes with pullback. The
identification of [Stacks, Tag 09NU] is natural for the pullback of *first* cohomology classes,
and the degree shift between that and the degree-two hypercohomology the Chern class lives in is
supplied by `Stacks.DerivedIndexing.homologyFunctor_map_singleDerivedPullback_comm`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.shiftedUnitsCohomologyTwoPullback_comp`: **the identification
  `H¹(X, 𝒪_X^*) ≅ H²(X, 𝒪_X^*[-1])` carries the pullback of first cohomology classes of the
  sheaf of units to pullback on degree-two hypercohomology.**
* `AlgebraicGeometry.Scheme.Hom.picardGroupToShiftedUnitsCohomologyTwo_schemePullbackClassHom`:
  the same, read on Picard classes.
* `AlgebraicGeometry.Scheme.Hom.deRhamFirstChernClassAbelian_schemePullbackClassHom`:
  **[Stacks, Tag 0FMD] for the de Rham first Chern class.**

## Implementation notes

The chain carrying [Stacks, Tag 09NU]'s naturality to the degree-two statement has four steps,
each already available: the pullback of first cohomology classes is transported to the
`ℤ`-indexing and read as the degreewise comparison of a composite of right derived functors
(`AlgebraicGeometry.Scheme.Hom.unitsPushforward_edge_comp_rightDerivedIso`); that comparison is
the degree-one homology of the pullback attached to a complex concentrated in degree zero
(`Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq`); the degree shift to the degree-two
homology of the pullback attached to a complex concentrated in degree one is
`Stacks.DerivedIndexing.homologyFunctor_map_singleDerivedPullback_comm`; and the pullback of
units is peeled off by the naturality of
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`, after which
`AlgebraicGeometry.Scheme.Hom.shiftedUnitsDerivedSectionsPullback_eq` recognises what is left as
pullback on the hypercohomology of the sheaf of units placed in degree one.

The reassociation of that four-fold composite is done through a private lemma stated on
variables: the junction objects carry two spellings which are only definitionally equal — a
complex concentrated in degree one, read as a bounded-below complex and then localized, is the
value of `DerivedCategory.Plus.singleFunctor` only definitionally — so `rw` and `simp` refuse to
rewrite inside the composite.

The passage from morphisms of abelian groups to their values on Picard classes needs no
computation: `AddMonoidHom.comp` and composition in `AddCommGrpCat` are applied to elements by
definition, so the class-level statements are `CategoryTheory.ConcreteCategory.congr_hom` of the
morphism-level ones, with
`AlgebraicGeometry.Scheme.Hom.h1UnitsAddEquivPicard_symm_schemePullbackClassHom` inserted on one
side.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree
open Stacks.Cohomology.DerivedPushforwardSections
open Stacks.GlueSquishUnits (unitsPushforwardMap)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit

/-- The reassociation of a four-fold composite with the three commuting squares it is built from
as hypotheses. Stated on variables because the junction objects carry two spellings which are
only definitionally equal. -/
private theorem square_algebra {V : Type*} [Category V] {A₀ B₀ C₀ D₀ E₀ F₀ G₀ H₀ K₀ : V}
    {a : A₀ ⟶ B₀} {b : B₀ ⟶ C₀} {c : C₀ ⟶ D₀} {d : D₀ ⟶ E₀}
    {r : A₀ ⟶ F₀} {m : F₀ ⟶ G₀} {n : G₀ ⟶ D₀}
    {s' : G₀ ⟶ H₀} {k : H₀ ⟶ E₀} {s : F₀ ⟶ K₀} {j : K₀ ⟶ H₀} {t : K₀ ⟶ E₀}
    (h3 : a ≫ b ≫ c = r ≫ m ≫ n) (h1 : n ≫ d = s' ≫ k) (h2 : m ≫ s' = s ≫ j)
    (h4 : j ≫ k = t) : a ≫ b ≫ c ≫ d = r ≫ s ≫ t := by
  subst h4
  rw [reassoc_of% h3, h1, reassoc_of% h2]

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X)

/-- **The degreewise comparison of a composite of right derived functors, moved from degree one
to degree two.** The degree-one instance is what [Stacks, Tag 09NU]'s pullback of first
cohomology classes becomes; the degree-two instance is the pullback on the hypercohomology the
de Rham first Chern class of [Stacks, Tag 0FLE] lives in. This is
`Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq` followed by
`Stacks.DerivedIndexing.homologyFunctor_map_singleDerivedPullback_comm`. -/
theorem rightDerivedPlusEdge_comp_singleFunctorCompHomologyFunctorShiftIso_inv :
    (Stacks.DerivedIndexing.rightDerivedPlusEdge (abelianPushforward.{u, u} f.base)
          (sectionsFunctor X.toRingedSpace.carrier ⊤) (1 : ℤ)).app
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) ≫
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).app
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)).inv =
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).app
            ((abelianPushforward.{u, u} f.base).obj
              (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace))).inv ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
          (Stacks.DerivedIndexing.singleDerivedPullback (abelianPushforward.{u, u} f.base)
            (sectionsFunctor X.toRingedSpace.carrier ⊤) 1
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)) := by
  refine Eq.trans (congrArg (fun z => z ≫ _)
    (Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq (abelianPushforward.{u, u} f.base)
      (sectionsFunctor X.toRingedSpace.carrier ⊤) 1
      (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace))) ?_
  exact Stacks.DerivedIndexing.homologyFunctor_map_singleDerivedPullback_comm
    (abelianPushforward.{u, u} f.base) (sectionsFunctor X.toRingedSpace.carrier ⊤) 1 1
    (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)

/-- **The pullback of units `𝒪_X^* ⟶ f_*𝒪_{X'}^*` moved across the degree shift**: the
naturality of `DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso` at that
morphism. -/
theorem rightDerivedPlus_map_comp_singleFunctorCompHomologyFunctorShiftIso_inv :
    ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedPlus (1 : ℤ)).map
          (unitsPushforwardMap f) ≫
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).app
            ((abelianPushforward.{u, u} f.base).obj
              (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace))).inv =
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).app
            (SheafOfModules.unitsAbelianSheaf X.toRingedSpace)).inv ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
          ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              ((Stacks.DerivedIndexing.singlePlusFunctor
                (AbelianSheaf X.toRingedSpace.carrier) 1).map (unitsPushforwardMap f)))) :=
  (DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).inv.naturality
      (unitsPushforwardMap f)

/-- **The identification `H¹(X, 𝒪_X^*) ≅ H²(X, 𝒪_X^*[-1])` carries the pullback of first
cohomology classes to pullback on degree-two hypercohomology.** This is [Stacks, Tag 0FMD]'s
remaining square: the left-hand side is the pullback [Stacks, Tag 09NU] is natural for, read in
the `ℤ`-indexing, and the right-hand side is the pullback the de Rham first Chern class is
natural for. -/
theorem shiftedUnitsCohomologyTwoPullback_comp :
    (abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) ≫
          (abelianEdgeMap.{u, u} f.base 1).app
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) ≫
          (Stacks.DerivedIndexing.rightDerivedIso
            (sectionsFunctor X'.toRingedSpace.carrier ⊤) 1).hom.app
              (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) ≫
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).app
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)).inv =
      (Stacks.DerivedIndexing.rightDerivedIso
          (sectionsFunctor X.toRingedSpace.carrier ⊤) 1).hom.app
            (SheafOfModules.unitsAbelianSheaf X.toRingedSpace) ≫
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
            (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus 1 1).app
              (SheafOfModules.unitsAbelianSheaf X.toRingedSpace)).inv ≫
          shiftedUnitsCohomologyTwoPullback f :=
  square_algebra (unitsPushforward_edge_comp_rightDerivedIso f)
    (rightDerivedPlusEdge_comp_singleFunctorCompHomologyFunctorShiftIso_inv f)
    (rightDerivedPlus_map_comp_singleFunctorCompHomologyFunctorShiftIso_inv f)
    (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map_comp _ _).symm.trans
      (congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        (shiftedUnitsDerivedSectionsPullback_eq f).symm))

/-! The abelian group structure on the Picard group of the underlying ringed space of a scheme is
`Stacks.Cohomology.Generators.picardGroupAddCommGroup`: instance search reaches
`Y.toRingedSpace.sheaf` through that instance's `RingedSpace` argument without any further
restatement. -/

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- `AlgebraicGeometry.Scheme.Hom.shiftedUnitsCohomologyTwoPullback_comp` with the two factors of
the degree shift collected into
`AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo`, which is their
composite by definition. -/
theorem sheafCohomologyOneIso_pullback :
    (abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) ≫
          (abelianEdgeMap.{u, u} f.base 1).app
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) ≫
        (SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo X'.toRingedSpace.carrier
          (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)).hom =
      (SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo X.toRingedSpace.carrier
          (SheafOfModules.unitsAbelianSheaf X.toRingedSpace)).hom ≫
        shiftedUnitsCohomologyTwoPullback f :=
  shiftedUnitsCohomologyTwoPullback_comp f

/-- **The identification `Pic(X) = H²(X, 𝒪_X^*[-1])` commutes with pullback.** It is
`AlgebraicGeometry.Scheme.Hom.sheafCohomologyOneIso_pullback` evaluated at the first cohomology
class of `c`, with [Stacks, Tag 09NU]'s naturality read backwards on one side. -/
theorem picardGroupToShiftedUnitsCohomologyTwo_schemePullbackClassHom
    (c : Stacks.Picard.ofScheme X) :
    SheafOfModules.picardGroupToShiftedUnitsCohomologyTwo (X := X'.toRingedSpace)
        (Stacks.GluePicard.picardModelAddEquiv X'.toRingedSpace
          (Stacks.Picard.schemePullbackClassHom f c)) =
      (shiftedUnitsCohomologyTwoPullback f).hom
        (SheafOfModules.picardGroupToShiftedUnitsCohomologyTwo (X := X.toRingedSpace)
          (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace c)) := by
  refine Eq.trans (congrArg (fun z =>
    (SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo X'.toRingedSpace.carrier
      (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)).hom.hom z)
    (h1UnitsAddEquivPicard_symm_schemePullbackClassHom f c)) ?_
  exact ConcreteCategory.congr_hom (sheafCohomologyOneIso_pullback f)
    ((Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X).symm c)

variable (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g)

/-- **Stacks Project, Tag 0FMD.** **The de Rham first Chern class commutes with pullback**: for
a commutative square of schemes with horizontal arrows `f : X' ⟶ X` and `g : S' ⟶ S`, the square
formed by `c₁^{dR}`, by pullback of Picard classes and by the de Rham pullback
`H²_{dR}(X/S) ⟶ H²_{dR}(X'/S')` of [Stacks, Tag 0FL6] commutes. -/
@[stacks 0FMD "the de Rham square"]
theorem deRhamFirstChernClassAbelian_schemePullbackClassHom (c : Stacks.Picard.ofScheme X) :
    SheafOfModules.deRhamFirstChernClassAbelian (deRhamAlgebras p')
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))
        (Stacks.GluePicard.picardModelAddEquiv X'.toRingedSpace
          (Stacks.Picard.schemePullbackClassHom f c)) =
      (deRhamCohomologyPullback f p p' g hcomm 2).hom
        (SheafOfModules.deRhamFirstChernClassAbelian (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))
          (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace c)) := by
  refine Eq.trans (congrArg (fun z =>
    (SheafOfModules.logarithmicDifferentialCohomologyMap (deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))).hom z)
    (picardGroupToShiftedUnitsCohomologyTwo_schemePullbackClassHom f c)) ?_
  exact (ConcreteCategory.congr_hom
    (logarithmicDifferentialCohomologyMap_pullback f p p' g hcomm)
    (SheafOfModules.picardGroupToShiftedUnitsCohomologyTwo (X := X.toRingedSpace)
      (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace c))).symm

end AlgebraicGeometry.Scheme.Hom

end
