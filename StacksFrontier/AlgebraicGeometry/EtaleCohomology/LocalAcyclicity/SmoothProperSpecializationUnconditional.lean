module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SmoothProperSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationMapDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Unconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# The specialization maps of a smooth proper morphism

[Stacks, Lemma 0GKD]: for `f : X ⟶ S` smooth and proper and `F` a locally constant abelian sheaf
on `X_étale` whose stalks are torsion of orders prime to the residue characteristics, every
specialization map `sp : (Rf_*F)_s ⟶ (Rf_*F)_t` is an isomorphism.

This is `AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper` with every input
supplied by a proved theorem: the proper base change theorem [Stacks, Tag 095T]
(`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`), the stalk computation
[Stacks, Tag 03Q9] (`AlgebraicGeometry.derivedPushforwardStalkFormula`), and the inputs of the
smooth base change theorem exactly as in its unconditional form
`Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth`
([Stacks, Theorem 0EYU]).

The unbounded derived functors of the small étale sites are defined in the model
`HasDerivedCategory.standard`, which is therefore the local instance here.

## Main results

* `AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper_unconditional`: for `f`
  smooth and proper and `F` locally constant with torsion stalks of orders prime to the residue
  characteristics, the specialization maps of `Rf_*F` are isomorphisms.

## References

* [Stacks Project, Tag 0GKD](https://stacks.math.columbia.edu/tag/0GKD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Let `f : X ⟶ S` be a morphism of schemes and `F` an abelian sheaf on `X_étale`. Assume

1. `f` is smooth and proper,
2. `F` is locally constant, and
3. for every geometric point `x̄` of `X` the stalk `F_{x̄}` is a torsion group all of whose
   elements have order prime to the residue characteristic of `x̄`.

Then for every geometric point `s̄` of `S` and every geometric point `t̄` of
`Spec 𝒪^{sh}_{S,s̄}` the specialization map `sp : (Rf_*F)_{s̄} ⟶ (Rf_*F)_{t̄}` is an
isomorphism; the stalk at `t̄` is taken at its image in `S`.

The strict henselization is formed in a big étale site `B` containing `X` and `S`, which exists
for every pair of schemes; the statement holds for every such `B`. -/
@[stacks 0GKD,
  sga "4 XVI 2.3" "special case",
  sga "4½ Th_finitude 5.2.4" "partial",
  sga "7 I 2.1" "more general"]
theorem isIso_specializationMap_of_smooth_of_isProper_unconditional (B : BigEtaleSite.{u})
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) [Smooth f]
    [IsProper f] (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hFlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F)
    (hFtors : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
      ∃ n : ℕ, 0 < n ∧
        (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0)
    (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s)) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) :=
  isIso_specializationMap_of_smooth_of_isProper B
    (fun _ _ g _ => cohomologyCommutesWithBaseChange_of_isProper g)
    (derivedPushforwardStalkFormula B)
    SmoothBaseChange.flatReducedFibresBaseChange SmoothBaseChange.etaleLocalHigherBaseChange
    SmoothBaseChange.higherBaseChangePaste SmoothBaseChange.firstFailureNormalization
    SmoothBaseChange.affineCurveCohomologyVanishing
    SmoothBaseChange.curveCohomologyAlgClosedInvariance
    (fun D hD => Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne D hD)
    hX hS f F hFlc hFtors s t

end AlgebraicGeometry
