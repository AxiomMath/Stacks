module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of higher direct images along a proper morphism of algebraic spaces

Let `T` be a big étale site of algebraic spaces over a scheme `S`, `f : Y ⟶ X` a proper morphism
of its objects and `x̄ : Spec Ω ⟶ X` a geometric point, with geometric fibre
`Y_x̄ = Y ×_X Spec Ω` and projection `g' : Y_x̄ ⟶ Y`. This file constructs the two isomorphisms of
[Stacks, Tag 0DG4]: `(Rⁿf_* F)_x̄ ≅ Hⁿ_étale(Y_x̄, F_x̄)` for a torsion abelian sheaf `F`, and
`(Hⁿ(Rf_* E))_x̄ ≅ Hⁿ(RΓ(Y_x̄, E_x̄))` for `E` bounded below with torsion cohomology sheaves, where
`F_x̄ = (g')⁻¹ F` and `E_x̄ = (g')⁻¹ E`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.abelianSheafFiberRightDerivedPushforwardIso`:
  `(Rⁿf_* F)_x̄ ≅ Hⁿ_étale(Y_x̄, F_x̄)` for a torsion abelian sheaf `F` and `f` proper.
* `AlgebraicGeometry.BigEtaleSpaceSite.abelianSheafFiberHomologyDerivedPushforwardIso`:
  `(Hⁿ(Rf_* E))_x̄ ≅ Hⁿ(RΓ(Y_x̄, E_x̄))` for `E` bounded below with torsion cohomology sheaves and
  `f` proper.

## References

* [Stacks Project, Tag 0DG4](https://stacks.math.columbia.edu/tag/0DG4)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DG2](https://stacks.math.columbia.edu/tag/0DG2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Homology.DerivedSquare (totalRightDerived totalRightDerivedUnit)
open AlgebraicGeometry.Space

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive
  additive_globalSections_spacesEtale

/-- The category of abelian sheaves on a spaces-étale site has `Ext` groups in the universe of
its morphisms: it is locally small with enough injectives. -/
local instance hasExt_spacesEtale (Z : T.Spaces) :
    HasExt.{u + 1} (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) Ab.{u + 1}) :=
  hasExt_of_enoughInjectives _

section Stalk

variable {X Y : T.Spaces} (f : Y ⟶ X) (x : Space.GeometricPoint T.fppfSite S T.fppf_mem X.1)

/-- Let `f : Y ⟶ X` be a proper morphism of algebraic spaces over a
scheme `S` and `x̄ : Spec Ω ⟶ X` a geometric point, with geometric fibre `Y_x̄ = Y ×_X Spec Ω`
and projection `g' : Y_x̄ ⟶ Y`. For an object `E` of `D⁺(Y_étale)` with torsion cohomology
sheaves, `(Hⁿ(Rf_* E))_x̄ ≅ Hⁿ(RΓ(Y_x̄, E_x̄))` for every `n`, where `E_x̄ = (g')⁻¹ E`. -/
@[stacks 0DG4 "(2)", sga "4 XVI 2.1" "more general", sga "4 XVI 2.2" "more general"]
def abelianSheafFiberHomologyDerivedPushforwardIso
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (m : ℤ) (hE : E.IsGE m) (hT : HasTorsionCohomology T E) (n : ℤ) :
    ((spacesEtaleSitePoint x).sheafFiber (A := Ab.{u + 1})).obj
      ((DerivedCategory.homologyFunctor
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) n).obj
          ((totalRightDerived (smallEtalePushforward T f)).obj E)) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((totalRightDerived (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
          (pullback f (geometricPointHom x))) Ab.{u + 1})).obj
        ((CategoryTheory.Sites.abelianInverseImage
          (smallEtaleMorphism T (pullback.fst f (geometricPointHom x)))).mapDerivedCategory.obj
            E)) :=
  abelianSheafFiberHomologyDerivedPushforwardIsoOfIsIso T f x E
    (isIso_spacesEtaleDerivedBaseChange_app_of_isProper T f hf _ _ _
      (IsPullback.of_hasPullback f (geometricPointHom x)) E m hE hT) n

set_option synthInstance.maxHeartbeats 400000 in
/-- Let `f : Y ⟶ X` be a proper morphism of algebraic spaces over a
scheme `S` and `x̄ : Spec Ω ⟶ X` a geometric point, with geometric fibre `Y_x̄ = Y ×_X Spec Ω`
and projection `g' : Y_x̄ ⟶ Y`. For a torsion abelian sheaf `F` on `Y_étale`,
`(Rⁿf_* F)_x̄ ≅ Hⁿ_étale(Y_x̄, F_x̄)` for every `n`, where `F_x̄ = (g')⁻¹ F`. -/
@[stacks 0DG4 "(1)",
  sga "4 XII 5.2" "more general",
  sga "4 XVI 2.1" "more general",
  sga "4 XVI 2.2" "more general",
  sga "4½ Arcata 4.1.1" "more general"]
def abelianSheafFiberRightDerivedPushforwardIso
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) F) (n : ℕ) :
    ((spacesEtaleSitePoint x).sheafFiber (A := Ab.{u + 1})).obj
      (((smallEtalePushforward T f).rightDerived n).obj F) ≅
    AddCommGrpCat.of (Sheaf.H.{u + 1} ((CategoryTheory.Sites.abelianInverseImage
      (smallEtaleMorphism T (pullback.fst f (geometricPointHom x)))).obj F) n) :=
  let Γ' := Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
    (pullback f (geometricPointHom x))) Ab.{u + 1}
  let g' := pullback.fst f (geometricPointHom x)
  ((spacesEtaleSitePoint x).sheafFiber (A := Ab.{u + 1})).mapIso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (smallEtalePushforward T f)
        (totalRightDerived (smallEtalePushforward T f))
        (totalRightDerivedUnit (smallEtalePushforward T f))
        (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) F n).symm ≪≫
    abelianSheafFiberHomologyDerivedPushforwardIso T f x hf _ 0 inferInstance
      (hasTorsionCohomology_singleFunctor T F hF) n ≪≫
    (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      ((totalRightDerived Γ').mapIso
        (((CategoryTheory.Sites.abelianInverseImage
          (smallEtaleMorphism T g')).mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso Γ' (totalRightDerived Γ')
      (totalRightDerivedUnit Γ')
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) _ n ≪≫
    (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem (pullback f (geometricPointHom x)))
        n).app _

end Stalk

end AlgebraicGeometry.BigEtaleSpaceSite

end
