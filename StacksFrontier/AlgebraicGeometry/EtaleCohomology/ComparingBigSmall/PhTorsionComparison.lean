module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional

/-!
# Comparing ph and étale cohomology of torsion sheaves (Stacks 0DE4)

Let `B` be a big ph site, `ε_X : Sh((Sch/X)_ph) ⟶ Sh((Sch/X)_étale)` the change of topology over
an object `X`, `π_X : Sh((Sch/X)_étale) ⟶ Sh(X_étale)` the projection to the small étale site and
`a_X = π_X ∘ ε_X`. The statements of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhCohomologyComparison` are
the four parts of Stacks 0DE4 (and Stacks 0DE5, 0DE6) for the comparison situation of Stacks 0F0I,
taking as arguments the two forms of the proper base change theorem the source's proof of
Stacks 0F0I uses. Both are now proved:

* Stacks 0A3U, for sheaves of sets:
  `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`;
* Stacks 095T: `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`.

This file supplies them, which gives Stacks 0F0I (`AlgebraicGeometry.phEtaleTorsionComparison`)
and Stacks 0DE4 with no further input.

## Main results

* `AlgebraicGeometry.properDirectImageComparison` — Stacks 0DDJ (2) in each degree, for every big
  étale site: `R^i f_{big,*}(π_X⁻¹F) ≅ π_Y⁻¹(R^i f_{small,*}F)` for `f` proper and `F` torsion.
* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph` — Stacks 0DDW: `π_S⁻¹F` is a ph sheaf and
  equals `ε_S⁻¹π_S⁻¹F`, for every sheaf of sets `F` on `S_étale`.
* `AlgebraicGeometry.phEtaleTorsionComparison` — Stacks 0F0I: the comparison situation (0EZ3) of
  the ph and étale topologies.
* `AlgebraicGeometry.phEtaleTorsionComparison_smallEtaleInclusion` — **Stacks 0DE4 (1)**.
* `AlgebraicGeometry.isIso_phEtaleTorsionHigherBaseChange` — **Stacks 0DE4 (2)**.
* `AlgebraicGeometry.isIso_phEtaleTorsionDerivedComparisonUnit_app` — **Stacks 0DE4 (3)**.
* `AlgebraicGeometry.isIso_phEtaleTorsionDerivedBaseChange` — **Stacks 0DE4 (4)**.

## Implementation notes

Objects of the big ph site are the schemes `X` of the statement; every scheme is one, for a
suitable big ph site. Parts (2) and (4) are stated for the canonical base change maps
`AlgebraicGeometry.higherSmallEtaleFineBaseChange` and
`AlgebraicGeometry.derivedSmallEtaleFineBaseChange` of the square of topoi
`a_Y ∘ f_{big,ph} = f_{small} ∘ a_X`.

## References

* [Stacks Project, Tag 0DE4](https://stacks.math.columbia.edu/tag/0DE4)
* [Stacks Project, Tag 0F0I](https://stacks.math.columbia.edu/tag/0F0I)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ComparingTopologies

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The hypothesis of Stacks 0A3U in the form taken by the ph comparison results. -/
private theorem isIso_smallEtaleSetBaseChange_of_isProper
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (_ : IsProper f) :
    IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w) :=
  Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq

/-- **Stacks 0DDJ (2) in each degree**, for every big étale site `E`: for a proper morphism
`f : X ⟶ Y` of `E`, a torsion abelian sheaf `F` on `X_étale` and every `i`,
`R^i f_{big,*}(π_X⁻¹F) ≅ π_Y⁻¹(R^i f_{small,*}F)`. It is the degree `i` cohomology of the derived
comparison at `F[0]`, which is an isomorphism by the proper base change theorem (Stacks 095T). -/
public theorem properDirectImageComparison (E : BigEtaleSite.{u}) :
    ProperDirectImageComparison E :=
  properDirectImageComparison_of_cohomologyCommutesWithBaseChange E
    fun f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f

/-- **Stacks 0DDW, for the ph topology.** For a big ph site `B`, a scheme `S` of `B` and a sheaf of
sets `F` on `S_étale`, the presheaf `π_S⁻¹F` on the big category over `S` is a sheaf for the ph
topology, and the unit of `ε_S⁻¹ ⊣ ε_{S,*}` at `π_S⁻¹F` is an isomorphism. The input of the
descent argument is the proper base change theorem for sheaves of sets (Stacks 0A3U). -/
public theorem smallEtaleInverseImage_isSheaf_ph (B : BigPHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) S hS) (Type (u + 1))) :
    Presieve.IsSheaf (BigPHOver.topology B S hS)
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
          F).obj ∧
      IsIso ((phToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) :=
  smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B S hS F
    isIso_smallEtaleSetBaseChange_of_isProper

/-- **Stacks 0F0I.** For a big ph site `B`, the comparison of the ph topology with the étale
topology on its underlying category, with the proper morphisms as distinguished class and, over
every object `X`, the class `𝒜'_X` of abelian sheaves `π_X⁻¹F` with `F` a torsion abelian sheaf
on `X_étale`, is a comparison situation in the sense of Stacks 0EZ3: properties (0EZ4)–(0EZ8)
hold and `𝒜'_X` is a weak Serre subcategory. It is
`AlgebraicGeometry.phEtaleCohomologyComparison` with its two proper base change inputs proved. -/
public abbrev phEtaleTorsionComparison (B : BigPHSite.{u}) :
    CohomologyComparison (phAssociatedBigEtaleSite B).Scheme :=
  phEtaleCohomologyComparison B
    (fun f g g' f' sq _ =>
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)
    (fun f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f)

variable (B : BigPHSite.{u})

/-- The category of abelian sheaves on the small étale site of an object `X` of the étale site
associated to a big ph site is Grothendieck abelian. -/
local instance (X : (phAssociatedBigEtaleSite B).Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B)
      X.obj X.property) Ab.{u + 1}) :=
  smallEtaleSheaf_isGrothendieckAbelian _ X

/-- **Stacks 0DE4 (1).** For an object `X` of the big ph site and an abelian torsion sheaf `F` on
`X_étale`, `ε_{X,*}a_X⁻¹F = π_X⁻¹F` — the unit `π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹F` of
`ε_X⁻¹ ⊣ ε_{X,*}` is an isomorphism, `a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹` — and
`R^i ε_{X,*}(a_X⁻¹F) = 0` for `i > 0`. -/
@[stacks 0DE4 "(1)"]
public theorem phEtaleTorsionComparison_smallEtaleInclusion
    (X : (phAssociatedBigEtaleSite B).Scheme)
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) F) :
    IsIso ((abelianComparisonAdjunction B.precoverage
        (phAssociatedBigEtaleSite B).precoverage
        (BigPHSite.etalePrecoverage_le_precoverage B) X).unit.app
        (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
          Ab.{u + 1} (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
          ((phAssociatedBigEtaleSite B).topology.over X)).obj F)) ∧
      ∀ i : ℕ, 0 < i → IsZero (((abelianComparisonPushforward B.precoverage
          (phAssociatedBigEtaleSite B).precoverage
          (BigPHSite.etalePrecoverage_le_precoverage B) X).rightDerived i).obj
        ((abelianComparisonPullback B.precoverage
          (phAssociatedBigEtaleSite B).precoverage X).obj
          (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
            Ab.{u + 1} (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
            ((phAssociatedBigEtaleSite B).topology.over X)).obj F))) :=
  have h := phComparison_smallEtaleInclusion B
    isIso_smallEtaleSetBaseChange_of_isProper
    Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper X F hF
  ⟨h.1, fun i hi => h.2 i hi⟩

/-- **Stacks 0DE4 (2).** For a proper morphism `f : X ⟶ Y` of the big ph site and an abelian
torsion sheaf `F` on `X_étale`, the base change map
`a_Y⁻¹(R^i f_{small,*}F) ⟶ R^i f_{big,ph,*}(a_X⁻¹F)` is an isomorphism for every `i`. The map is
`AlgebraicGeometry.higherSmallEtaleFineBaseChange`, the degree `i` cohomology of the derived base
change map of part (4) at `F` placed in degree zero; `f_{big,ph,*}` is the direct image
`overPushforward` of the ph topology along `f`. -/
@[stacks 0DE4 "(2)"]
public theorem isIso_phEtaleTorsionHigherBaseChange
    {X Y : (phAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
    (hf : IsProper ((phAssociatedBigEtaleSite B).inclusion.map f))
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) F)
    (i : ℕ) :
    IsIso (higherSmallEtaleFineBaseChange (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph B X.1 X.2 F).1)
      (properDirectImageComparison _) (BigPHSite.exists_properRefinement B) f F i) :=
  isIso_phHigherSmallEtaleBaseChange B
    isIso_smallEtaleSetBaseChange_of_isProper
    Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f hf F hF i

/-- **Stacks 0DE4 (3).** For an object `X` of the big ph site and `K` in `D⁺(X_étale)` with torsion
cohomology sheaves, the map `π_X⁻¹K ⟶ Rε_{X,*}(a_X⁻¹K)` is an isomorphism: it is the derived unit
of `ε_X⁻¹ ⊣ ε_{X,*}` at `π_X⁻¹K`, and `a_X⁻¹K = ε_X⁻¹π_X⁻¹K`. -/
@[stacks 0DE4 "(3)"]
public theorem isIso_phEtaleTorsionDerivedComparisonUnit_app
    (X : (phAssociatedBigEtaleSite B).Scheme)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso ((derivedComparisonUnit (phEtaleTorsionComparison B) X).app
      (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
        Ab.{u + 1} (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
        ((phAssociatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K)) :=
  isIso_phDerivedComparisonUnit_app B
    isIso_smallEtaleSetBaseChange_of_isProper
    Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper X K hK

/-- **Stacks 0DE4 (4).** For a proper morphism `f : X ⟶ Y` of the big ph site and `K` in
`D⁺(X_étale)` with torsion cohomology sheaves, the base change map
`a_Y⁻¹(Rf_{small,*}K) ⟶ Rf_{big,ph,*}(a_X⁻¹K)` is an isomorphism. The map is
`AlgebraicGeometry.derivedSmallEtaleFineBaseChange`, the base change map of the square of topoi
`a_Y ∘ f_{big,ph} = f_{small} ∘ a_X`. -/
@[stacks 0DE4 "(4)"]
public theorem isIso_phEtaleTorsionDerivedBaseChange
    {X Y : (phAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
    (hf : IsProper ((phAssociatedBigEtaleSite B).inclusion.map f))
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso (derivedSmallEtaleFineBaseChange (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph B X.1 X.2 F).1)
      (properDirectImageComparison _) (BigPHSite.exists_properRefinement B) f K) :=
  isIso_phDerivedSmallEtaleBaseChange B
    isIso_smallEtaleSetBaseChange_of_isProper
    Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f hf K hK

end AlgebraicGeometry

end
