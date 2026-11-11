module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleComparisonSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyComparisonIsomorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyAlongAnAdjunction

/-!
# Cohomology on the small étale site and on a finer big site

Let `E` be a big étale site and `X` one of its objects. Write `π_X` for the projection from the
big étale topos over `X` to the small étale topos of `X`. This file proves that the derived
global sections of an object `K` of `D⁺(X_étale)` are the derived global sections of `π_X⁻¹K`
on the big étale site over `X`,

`RΓ(X_étale, K) = RΓ((Sch/X)_étale, π_X⁻¹K)`,

a consequence of Stacks 0DDI (stated in full as
`AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso`) in which cohomology is compared. Combined with the comparison of
cohomology for a change of topology (Stacks 0EZH) in the situation of Stacks 0F0I or Stacks 0F0J,
it computes étale cohomology on the ph or h site; that step is the generic form of Stacks 0DE6
and Stacks 0EWH.

## Main definitions

* `AlgebraicGeometry.derivedGlobalSectionsSmallEtaleIso`:
  `π_X⁻¹ ⋙ RΓ((Sch/X)_étale, -) ≅ RΓ(X_étale, -)` on `D⁺(X_étale)`.
* `AlgebraicGeometry.derivedGlobalSectionsFineComparisonIso`: in the comparison situation
  `AlgebraicGeometry.properEtaleCohomologyComparison` of a finer precoverage `K` with the étale
  one, `RΓ(X_étale, M) ≅ RΓ_K(X, ε_X⁻¹π_X⁻¹M)` for `M` in `D⁺(X_étale)` with torsion cohomology
  sheaves — the generic form of Stacks 0DE6 (2) and Stacks 0EWH (2).
* `AlgebraicGeometry.cohomologyFineComparisonIso`: `H^q(X_étale, F) ≅ H^q_K(X, ε_X⁻¹π_X⁻¹F)` for a
  torsion abelian sheaf `F` — the generic form of Stacks 0DE6 (1) and Stacks 0EWH (1).
* `AlgebraicGeometry.cohomologyConstantFineComparisonIso`: `H^q_étale(X, A) ≅ H^q_K(X, A)` for a
  torsion abelian group `A` — the example of Stacks 0DE6 and Stacks 0EWH.

## References

* [Stacks Project, Tag 0DDI](https://stacks.math.columbia.edu/tag/0DDI)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0DE6](https://stacks.math.columbia.edu/tag/0DE6)
* [Stacks Project, Tag 0EWH](https://stacks.math.columbia.edu/tag/0EWH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section ProjectionGlobalSections

variable (E : BigEtaleSite.{u}) (X : E.Scheme)
  {J : GrothendieckTopology (BigEtaleOver E X.obj X.property)}
  [(SmallEtale.inclusion E X.obj X.property).IsContinuous
    (SmallEtale.topology E X.obj X.property) J]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  [PreservesFiniteLimits ((SmallEtale.inclusion E X.obj X.property).sheafPullback
    AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) J)]
  [PreservesFiniteColimits ((SmallEtale.inclusion E X.obj X.property).sheafPullback
    AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) J)]
  [((SmallEtale.inclusion E X.obj X.property).sheafPullback
    AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) J).Additive]

/-- Global sections on the big site over `X` are global sections on the small étale site of the
direct image `π_{X,*}`: restriction along the inclusion of the small site carries the final object
`X / X` to the final object of the slice. -/
def sheafPushforwardSmallEtaleGlobalSectionsIso :
    (SmallEtale.inclusion E X.obj X.property).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology E X.obj X.property) J ⋙
      (sheafSections (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final E X.obj X.property)) ≅
    (sheafSections J AddCommGrpCat.{u + 1}).obj (op (Over.mk (𝟙 (E.obj X.obj X.property)))) :=
  Iso.refl _

/-- The direct image `π_{X,*}` of an injective abelian sheaf is acyclic for global sections on
the small étale site. -/
theorem rightAcyclic_smallEtaleGlobalSections_sheafPushforward
    (I : Sheaf J AddCommGrpCat.{u + 1}) (hI : Injective I) :
    ((sheafSections (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final E X.obj X.property))).rightAcyclic
      (((SmallEtale.inclusion E X.obj X.property).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) J).obj I) :=
  have := ((SmallEtale.inclusion E X.obj X.property).sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) J).map_injective I hI
  Functor.rightAcyclic_of_injective _ _

variable {E X}

/-- **A consequence of Stacks 0DDI, on derived global sections.** This is not Stacks 0DDI
itself, which is `AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso` (the derived unit
`K ⟶ Rπ_{X,*}π_X⁻¹K` is an isomorphism in the unbounded `D(X_étale)`); it is that statement after
applying derived global sections, on `D⁺`. For `K` in `D⁺(X_étale)` the derived global
sections of `π_X⁻¹K` on the big étale site over `X` are those of `K` on the small étale site:
`RΓ((Sch/X)_étale, π_X⁻¹K) = RΓ(X_étale, K)`, naturally in `K`. -/
def derivedGlobalSectionsSmallEtaleIso
    (hJ : BigEtaleOver.topology E X.obj X.property = J) :
    ((SmallEtale.inclusion E X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology E X.obj X.property) J).mapDerivedCategoryPlus ⋙
      ((sheafSections J AddCommGrpCat.{u + 1}).obj
        (op (Over.mk (𝟙 (E.obj X.obj X.property))))).rightDerivedFunctorPlus ≅
    ((sheafSections (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final E X.obj X.property))).rightDerivedFunctorPlus := by
  let L := (SmallEtale.inclusion E X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology E X.obj X.property) J
  let R := (SmallEtale.inclusion E X.obj X.property).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) J
  let adj : L ⊣ R := (SmallEtale.inclusion E X.obj X.property).sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) J
  obtain ⟨hR₁, hR₂⟩ := smallEtaleInclusion_sheafPushforward_exact E X hJ
  haveI := isIso_smallEtaleInclusion_sheafAdjunction_unit E X hJ
  haveI : R.Additive := Functor.additive_of_preserves_binary_products _
  exact Functor.isoWhiskerLeft L.mapDerivedCategoryPlus
      ((Functor.rightDerivedFunctorPlusNatIso
          (sheafPushforwardSmallEtaleGlobalSectionsIso E X (J := J))).symm ≪≫
        Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic R _
          (rightAcyclic_smallEtaleGlobalSections_sheafPushforward E X) ≪≫
        Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus R)
          _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso L R ≪≫
        (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus (L ⋙ R)).symm ≪≫
        Functor.rightDerivedFunctorPlusIdIsoOf (L ⋙ R) (asIso adj.unit).symm)
      _ ≪≫
    Functor.leftUnitor _

end ProjectionGlobalSections

section FineTopology

open Stacks.ComparingTopologies Stacks.Cohomology.Localization

variable (E : BigEtaleSite.{u}) (K : Precoverage E.Scheme)
  [K.HasIsos] [K.IsStableUnderComposition] [K.HasPullbacks] [K.IsStableUnderBaseChange]
  (hle : E.precoverage ≤ K)
  (hsheaf : ∀ (X : E.Scheme) (F : Sheaf (SmallEtale.topology E X.obj X.property) (Type (u + 1))),
    Presieve.IsSheaf (K.toGrothendieck.over X)
      ((bigEtaleToSmallEtaleMorphism E X.obj X.property).inverseImage.obj F).obj)
  (hR : ProperDirectImageComparison E)
  (hrefine : ∀ (U : E.Scheme) (R : Presieve U), R ∈ K U →
    ∃ S : Presieve U, S ∈ E.precoverage U ∧
      ∀ ⦃V : E.Scheme⦄ (v : V ⟶ U), S v →
        ∃ (W : E.Scheme) (f : W ⟶ V), IsProper (E.inclusion.map f) ∧
          Presieve.singleton f ∈ K V ∧
          ∃ T : Presieve W, T ∈ E.precoverage W ∧ T.FactorsThruAlong R (f ≫ v))
  (X : E.Scheme)

/-- **Étale cohomology is cohomology on the finer site (Stacks 0DE6 (2), Stacks 0EWH (2)),
generically.** In the comparison situation `properEtaleCohomologyComparison` of a finer
precoverage `K` with the étale precoverage of `E`, let `M` be an object of `D⁺(X_étale)` whose
cohomology sheaves are torsion. Then

`RΓ(X_étale, M) = RΓ_K(X, a_X⁻¹M)`, where `a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`.

It is the composite of the small-to-big comparison `derivedGlobalSectionsSmallEtaleIso`
(Stacks 0DDI) and the comparison of Stacks 0EZH (2) at `π_X⁻¹M`, whose cohomology sheaves
`π_X⁻¹H^i(M)` lie in the class `𝒜'_X`, `π_X⁻¹` being exact.

The isomorphism is the canonical map, the pullback along `a_X` on cohomology, and not merely some
isomorphism: its `hom` is `RΓ(X_étale, -)` of the unit `M ⟶ π_{X,*}π_X⁻¹M` (Stacks 0DDI) read
through `RΓ(X_étale, π_{X,*}-) = RΓ((Sch/X)_étale, -)`, followed by the change-of-topology map
`Stacks.ComparingTopologies.derivedCohomologyComparison` at `π_X⁻¹M`, which is `RΓ` of the
canonical map `K' ⟶ Rε_{X,*}ε_X⁻¹K'` read through `RΓ ∘ Rε_{X,*} = RΓ_K` (Stacks 0D6H). Together
these are the map `RΓ(X_étale, M) ⟶ RΓ(X_étale, Ra_{X,*}a_X⁻¹M) = RΓ_K(X, a_X⁻¹M)` of
Stacks 0EWG. -/
def derivedGlobalSectionsFineComparisonIso
    (M : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}))
    (hM : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology E X.obj X.property) ((DerivedCategory.Plus.homologyFunctor _ i).obj M)) :
    ((sheafSections (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final E X.obj X.property))).rightDerivedFunctorPlus.obj M ≅
      (Stacks.globalSectionsOver (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).fineCoverage.toGrothendieck X).rightDerivedFunctorPlus.obj
        ((abelianComparisonPullback (properEtaleCohomologyComparison E K hle hsheaf hR
            hrefine).fineCoverage (properEtaleCohomologyComparison E K hle hsheaf hR
            hrefine).coarseCoverage X).mapDerivedCategoryPlus.obj
          (((SmallEtale.inclusion E X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
            (SmallEtale.topology E X.obj X.property)
            (E.topology.over X)).mapDerivedCategoryPlus.obj M)) := by
  let L := (SmallEtale.inclusion E X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology E X.obj X.property) (E.topology.over X)
  have hK : ∀ i : ℤ, (properEtaleCohomologyComparison E K hle hsheaf hR hrefine).weakSerre X
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (E.topology.over X) AddCommGrpCat.{u + 1})
        i).obj (L.mapDerivedCategoryPlus.obj M)) :=
    fun i => ⟨_, hM i, ⟨((Stacks.DerivedFunctor.derivedHomologyIso L i).app
      (DerivedCategory.Plus.ι.obj M)).symm⟩⟩
  have h0EZH := isIso_derivedCohomologyComparison_app_of_weakSerre
    (properEtaleCohomologyComparison E K hle hsheaf hR hrefine) X
    (L.mapDerivedCategoryPlus.obj M) hK
  exact ((derivedGlobalSectionsSmallEtaleIso (bigEtaleOver_topology_eq_of_obj E X)).app M).symm ≪≫
    @asIso _ _ _ _ ((derivedCohomologyComparison (properEtaleCohomologyComparison E K hle hsheaf
      hR hrefine) X).app (L.mapDerivedCategoryPlus.obj M)) h0EZH

/-- The cohomology sheaves of a torsion abelian sheaf placed in degree zero are torsion. -/
theorem torsionSheafProperty_homology_singleFunctor
    (F : Sheaf (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology E X.obj X.property) F)
    (i : ℤ) :
    Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology E X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  by_cases hi : i = 0
  · subst hi
    exact (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · refine (Stacks.Torsion.torsionSheafProperty _).prop_of_isZero ?_
    exact IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ i hi)
      ((DerivedCategory.homologyFunctor _ i).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app
          ((CochainComplex.singleFunctor _ 0).obj F))

/-- **Étale cohomology of a torsion sheaf is cohomology on the finer site (Stacks 0DE6 (1),
Stacks 0EWH (1)), generically.** In the comparison situation `properEtaleCohomologyComparison`,
for a torsion abelian sheaf `F` on `X_étale` and every `q`,

`H^q(X_étale, F) = H^q_K(X, a_X⁻¹F)`, where `a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`.

This is `derivedGlobalSectionsFineComparisonIso` at `F` placed in degree zero, read in degree `q`
through the identification of `ℕ`-indexed right derived functors with the cohomology of the
derived functor on `D⁺` (`Stacks.DerivedIndexing.rightDerivedIso`). -/
def cohomologyFineComparisonIso
    (F : Sheaf (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology E X.obj X.property) F)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final E X.obj X.property))).rightDerived q).obj F ≅
      ((Stacks.globalSectionsOver (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).fineCoverage.toGrothendieck X).rightDerived q).obj
        ((abelianComparisonPullback (properEtaleCohomologyComparison E K hle hsheaf hR
            hrefine).fineCoverage (properEtaleCohomologyComparison E K hle hsheaf hR
            hrefine).coarseCoverage X).obj
          (((SmallEtale.inclusion E X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
            (SmallEtale.topology E X.obj X.property) (E.topology.over X)).obj F)) :=
  (Stacks.DerivedIndexing.rightDerivedIso _ q).app F ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).mapIso
      (derivedGlobalSectionsFineComparisonIso E K hle hsheaf hR hrefine X
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
          (torsionSheafProperty_homology_singleFunctor E X F hF) ≪≫
        (Stacks.globalSectionsOver (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).fineCoverage.toGrothendieck X).rightDerivedFunctorPlus.mapIso
          ((abelianComparisonPullback (properEtaleCohomologyComparison E K hle hsheaf hR
              hrefine).fineCoverage (properEtaleCohomologyComparison E K hle hsheaf hR
              hrefine).coarseCoverage X).mapDerivedCategoryPlus.mapIso
              ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle _ 0).app F) ≪≫
            (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle _ 0).app _)) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _).symm

/-- `a_X⁻¹` carries constant sheaves to constant sheaves: `ε_X⁻¹π_X⁻¹A = A` for an abelian group
`A`, both composites being left adjoint to global sections. -/
def constantSheafFineComparisonIso :
    constantSheaf (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1} ⋙
        (SmallEtale.inclusion E X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology E X.obj X.property) (E.topology.over X) ⋙
        abelianComparisonPullback (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).fineCoverage (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).coarseCoverage X ≅
      constantSheaf ((properEtaleCohomologyComparison E K hle hsheaf hR
        hrefine).fineCoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.ExtAdjunction.constantSheafPullbackIso
        ((SmallEtale.inclusion E X.obj X.property).sheafAdjunctionContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology E X.obj X.property) (E.topology.over X))
        (SmallEtale.finalIsTerminal E X.obj X.property) Over.mkIdTerminal (Iso.refl _)) _ ≪≫
    Stacks.ExtAdjunction.constantSheafPullbackIso
      (abelianComparisonAdjunction (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).fineCoverage (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).coarseCoverage (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).coarse_le_fine X)
      Over.mkIdTerminal Over.mkIdTerminal (Iso.refl _)

/-- **Étale cohomology with torsion constant coefficients is cohomology on the finer site (the
example of Stacks 0DE6 and of Stacks 0EWH), generically.** For a torsion abelian group `A`,

`H^q_étale(X, A) = H^q_K(X, A)`,

the constant sheaves on the small étale site of `X` and on the finer site over `X`. It is
`cohomologyFineComparisonIso` at the constant sheaf, which is torsion, followed by
`constantSheafFineComparisonIso`. -/
def cohomologyConstantFineComparisonIso (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final E X.obj X.property))).rightDerived q).obj
        ((constantSheaf (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}).obj A) ≅
      ((Stacks.globalSectionsOver (properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).fineCoverage.toGrothendieck X).rightDerived q).obj
        ((constantSheaf ((properEtaleCohomologyComparison E K hle hsheaf hR
          hrefine).fineCoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}).obj A) :=
  cohomologyFineComparisonIso E K hle hsheaf hR hrefine X _
      (Stacks.Torsion.torsionSheafProperty_constantSheaf_of_isAddTorsion _ A hA) q ≪≫
    ((Stacks.globalSectionsOver (properEtaleCohomologyComparison E K hle hsheaf hR
        hrefine).fineCoverage.toGrothendieck X).rightDerived q).mapIso
      ((constantSheafFineComparisonIso E K hle hsheaf hR hrefine X).app A)

end FineTopology

end AlgebraicGeometry

end
