module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnitIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineSchemesOverDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# `𝒪_X`-modules on the small étale site and on the spaces-étale site

Let `X` be an algebraic space over a scheme `S`. Stacks 03G1 says the small étale site `X_étale`
(étale scheme charts) and the spaces-étale site `X_{spaces,étale}` have equivalent topoi. This
file builds the same comparison for `𝒪`-modules. The two structure sheaves live in different
universes, so the comparison has three steps:
1. lift an `𝒪_X`-module on `X_étale` to the next universe;
2. identify the lifted structure sheaf of `X_étale` with the structure sheaf of
   `X_{spaces,étale}` restricted to the scheme charts;
3. extend along the comparison of 03G1 by the Comparison Lemma for sheaves of modules.

## Main definitions

* `AlgebraicGeometry.Space.comparisonRingIso`: the universe lift of the structure sheaf of
  `X_étale` is the restriction of the structure sheaf of `X_{spaces,étale}` along the comparison
  functor of Stacks 03G1. On an étale chart `U` it is `Γ(U, 𝒪_U) ≅ Γ(h_U, 𝒪)` of
  `AlgebraicGeometry.Space.globalFunctionsSchemeSpaceIso`.
* `AlgebraicGeometry.Space.comparisonModuleEquivalence`: the resulting equivalence between the
  `𝒪`-modules on `X_{spaces,étale}` and the modules over the lifted structure sheaf of `X_étale`.
* `AlgebraicGeometry.Space.toSpacesEtaleModules`: the transport `ι` of an `𝒪_X`-module on
  `X_étale` (a `AlgebraicGeometry.Space.Modules`) to an `𝒪`-module on `X_{spaces,étale}`.

## Main results

* `AlgebraicGeometry.Space.fullyFaithfulToSpacesEtaleModules`: `ι` is fully faithful.
* `AlgebraicGeometry.Space.toSpacesEtaleModulesUnitIso`: `ι𝒪_X ≅ 𝒪`.

## Implementation notes

The objects of both sites lie in `Type (u + 1)`. The structure sheaf of `X_étale` takes values in
`CommRingCat.{u}`, while that of `X_{spaces,étale}`, whose value at an algebraic space is the ring
of compatible families of regular functions on its charts, takes values in `CommRingCat.{u + 1}`.
So step 1 cannot be skipped. Lifting the module together with its ring is
`Stacks.SheafOfModules.CoherentLift.liftModuleFunctor`. Step 3 is
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` for the dense subsite of
Stacks 03G1, `AlgebraicGeometry.Space.comparisonFunctor_isDenseSubsite`. Step 2 is
restriction of scalars along an isomorphism of sheaves of rings,
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The structure sheaves of the two étale sites of an algebraic space agree on scheme
charts.** The universe lift of the structure sheaf of `X_étale` is the restriction of the
structure sheaf of `X_{spaces,étale}` along the comparison functor of Stacks 03G1. At an étale
chart `U` it is the inverse of `Γ(h_U, 𝒪) ≅ Γ(U, 𝒪_U)`. -/
noncomputable def comparisonRingIso :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2)).O) ≅
      Stacks.DenseSubsiteModules.ringRestriction (SmallEtale.topology B S hS X.1)
        (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => (forget₂ CommRingCat RingCat).mapIso
      (globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X.1).obj U.unop)).symm)
    (by
      intro U V g
      have h := globalFunctionsSchemeSpaceIso_naturality B S hS
        ((SmallEtale.toOver B S hS X.1).map g.unop)
      have h2 : (globalFunctionsSchemeSpaceIso B S hS
            ((SmallEtale.toOver B S hS X.1).obj U.unop)).inv ≫
          (globalFunctionsPresheaf B S hS).map
            ((schemeSpaceFunctor B S hS).map ((SmallEtale.toOver B S hS X.1).map g.unop)).op =
          CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1, u, u} (CommRingCat.Hom.hom
            (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
              ((SmallEtale.toOver B S hS X.1).map g.unop)).op))) ≫
          (globalFunctionsSchemeSpaceIso B S hS
            ((SmallEtale.toOver B S hS X.1).obj V.unop)).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      have h3 := congrArg (forget₂ CommRingCat RingCat).map h2
      rw [Functor.map_comp, Functor.map_comp] at h3
      exact h3.symm))

set_option synthInstance.maxHeartbeats 400000 in
/-- Stacks 03G1 for sheaves of abelian groups at the universe of the structure sheaf of
`X_{spaces,étale}`: restriction along the comparison functor is an equivalence. -/
instance comparisonFunctor_sheafEquivalence_addCommGrp :
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).IsEquivalence :=
  inferInstance

/-- **Stacks 03G1 for `𝒪`-modules.** Restricting to scheme charts gives an equivalence between
the `𝒪`-modules on the spaces-étale site of `X` and the modules over the universe lift of the
structure sheaf of the small étale site of `X`. Scalars are read along
`AlgebraicGeometry.Space.comparisonRingIso`. -/
noncomputable def comparisonModuleEquivalence :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O) ≌
      SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2)).O) :=
  (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)).trans
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso (comparisonRingIso B S hS X).symm)

/-- **The transport `ι` of `𝒪_X`-modules from the small étale site to the spaces-étale site.**
An `𝒪_X`-module on `X_étale` (étale scheme charts, sections in `Type u`) is lifted to the next
universe, and then extended to `X_{spaces,étale}` through the equivalence
`AlgebraicGeometry.Space.comparisonModuleEquivalence`. -/
noncomputable def toSpacesEtaleModules :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O) :=
  Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2) ⋙
    (comparisonModuleEquivalence B S hS X).inverse

/-- **`ι` is fully faithful**: the universe lift of `𝒪_X`-modules is fully faithful and the
second step is an equivalence. -/
noncomputable def fullyFaithfulToSpacesEtaleModules :
    (toSpacesEtaleModules B S hS X).FullyFaithful :=
  (Stacks.SheafOfModules.CoherentLift.fullyFaithfulLiftModuleFunctor.{u + 1, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2)).comp
    (comparisonModuleEquivalence B S hS X).fullyFaithfulInverse

/-- Restricting `ι𝓕` back to the scheme charts gives the universe lift of `𝓕`. -/
noncomputable def toSpacesEtaleModulesRestrictionIso :
    toSpacesEtaleModules B S hS X ⋙ (comparisonModuleEquivalence B S hS X).functor ≅
      Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (comparisonModuleEquivalence B S hS X).counitIso ≪≫
      Functor.rightUnitor _

/-- **`ι𝒪_X = 𝒪`.** The transport of the structure sheaf of `X_étale` is the structure sheaf of
`X_{spaces,étale}`. -/
noncomputable def toSpacesEtaleModulesUnitIso :
    (toSpacesEtaleModules B S hS X).obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
  (comparisonModuleEquivalence B S hS X).inverse.mapIso
      (Stacks.Sheaves.RingedPoint.restrictScalarsUnitIsoOfIso (comparisonRingIso B S hS X)).symm ≪≫
    ((comparisonModuleEquivalence B S hS X).unitIso.app
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O))).symm

end AlgebraicGeometry.Space

end
