module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.ProperSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Specialization and cospecialization for a proper locally acyclic morphism

Let `f : X ⟶ S` be a morphism of schemes, `K` an object of `D(X_étale)`, `s` a geometric point of
`S` and `t` a geometric point of `Spec 𝒪^{sh}_{S,s}`. This file states, with no hypothesis beyond
the source's, two results of the section on local acyclicity:

* Tag 0GJU: if `K` is bounded below and `f` is locally acyclic relative to `K`, then the inverse
  image `i⁻¹β_{K,s,t}` on the closed geometric fibre of the comparison
  `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})` is an isomorphism, so that the cospecialization map
  `cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)` of Section 0GJT is defined;
* Tag 0GJW: if moreover `f` is proper and `K` has torsion cohomology sheaves, then the
  specialization map `sp : (Rf_*K)_s ⟶ (Rf_*K)_t` and the cospecialization map are isomorphisms.

## Main results

* `AlgebraicGeometry.isIso_pullback_cospecializationUnit_of_isGE` — **[Stacks, Tag 0GJU]**.
* `AlgebraicGeometry.isIso_specializationStalk_and_cospecializationMap_of_isProper` —
  **[Stacks, Tag 0GJW]**.

## Implementation notes

Both statements are proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationUnitStalk` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.ProperSpecialization` from the
stalk computation of Tag 03Q9, `AlgebraicGeometry.DerivedPushforwardStalkFormula`, and, for Tag
0GJW, the proper base change theorem of Tag 095T in the form
`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange` for every proper morphism. Here those two
inputs are supplied by the theorems proving them:
`AlgebraicGeometry.derivedPushforwardStalkFormula` (Tag 03Q9) and
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper` (Tag 095T).

The varieties of vanishing cycles defining local acyclicity are formed in a big étale site `B`
containing `X` and `S`; that site is a size device, not a hypothesis of the source
(`AlgebraicGeometry.exists_bigEtaleSite_contains_pullback`). The stalk of `Rf_*K` at `t` is taken
at the image of `t` in `S`, as the source does.

## References

* [Stacks Project, Tag 0GJT](https://stacks.math.columbia.edu/tag/0GJT)
* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
* [Stacks Project, Tag 0GJW](https://stacks.math.columbia.edu/tag/0GJW)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- **[Stacks, Tag 0GJU].** Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of
`S`, `t` a geometric point of `Spec 𝒪^{sh}_{S,s}`, and `K` an object of `D(X_étale)` which is
bounded below and relative to which `f` is locally acyclic. Write `Y = X ×_S Spec 𝒪^{sh}_{S,s}`,
`h : X_t ⟶ Y` for the fibre over `t` and `i : X_s ⟶ Y` for the closed geometric fibre. Then the
inverse image `i⁻¹β_{K,s,t}` of the comparison `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})` is an
isomorphism. -/
@[stacks 0GJU]
theorem isIso_pullback_cospecializationUnit_of_isGE (K : smallEtaleDerivedCategory X) (m : ℤ)
    (hK : K.IsGE m) (hla : IsLocallyAcyclicRelative B hX hS f K) :
    IsIso ((smallEtaleDerivedPullbackAb
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
        (cospecializationUnit B hS f s t K)) :=
  isIso_pullback_cospecializationUnit_of_derivedPushforwardStalkFormula B hX hS f s t
    (derivedPushforwardStalkFormula B) K m hK hla

/-- **[Stacks, Tag 0GJW].** Let `f : X ⟶ S` be a morphism of schemes and `K` an object of
`D(X_étale)` such that

1. `K` is bounded below,
2. `f` is locally acyclic relative to `K`,
3. `f` is proper, and
4. `K` has torsion cohomology sheaves.

Then for every geometric point `s` of `S` and every geometric point `t` of `Spec 𝒪^{sh}_{S,s}`
the specialization map `sp : (Rf_*K)_s ⟶ (Rf_*K)_t` is an isomorphism, and the cospecialization
map `cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)` — defined because `i⁻¹β_{K,s,t}` is an isomorphism (Tag
0GJU) — is an isomorphism.

The objects named in the statement, all defined in this library with no hypothesis beyond their
data:

* `smallEtaleDerivedCategory X` (`EtaleCohomology/DerivedEtale.lean`) is `D(X_étale)`, the derived
  category of abelian sheaves on the small étale site; `K.IsGE m` says `K` is bounded below.
* `IsLocallyAcyclicRelative B hX hS f K` (`LocalAcyclicity/Basic.lean`) is part (2) of
  Definition 0GJP: at every geometric point `x` of `X` and every geometric point `t` of
  `Spec 𝒪^{sh}_{S,f(x)}` the map `α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)` to the cohomology of the
  variety of vanishing cycles is an isomorphism; `B` is a big étale site containing `X` and `S`, a
  size device only.
* `Stacks.Torsion.torsionCohomologyProperty` (`CategoryTheory/Sites/Cohomology/Torsion/
  StacksFrontier/CategoryTheory/Sites/Cohomology/Torsion/DerivedCategoryOfTorsionSheaves.lean`)
  says every cohomology sheaf of `K` is torsion.
* `smallEtaleDerivedPushforwardAb f` (`EtaleCohomology/StalkOfDerivedPushforward.lean`) is
  `Rf_*`, the total right derived functor of direct image; its existence is the proved instance
  `Stacks.EtaleCohomology.hasRightDerivedFunctor_smallEtalePushforwardAb`
  (`EtaleCohomology/SmallEtaleUnboundedDerivations.lean`), and that of `RΓ` the proved instance
  `Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor`
  (`EtaleCohomology/SmallEtaleDerivedGlobalSectionsExistence.lean`).
* `smallEtaleDerivedSpecializationStalkAbAt B S hS s t`
  (`EtaleCohomology/SpecializationMapAndFibres.lean`) is the specialization map
  `sp : (−)_s ⟶ (−)_t` on derived stalks, at the image of `t` in `S`.
* `cospecializationUnit B hS f s t K` (`LocalAcyclicity/CospecializationMap.lean`) is
  `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})`, and `geometricFibreToStrictHenselizationBaseChange B hS f s`
  (`EtaleCohomology/StalkOfDerivedPushforward.lean`) is `i : X_s ⟶ Y`.
* `cospecializationMap B hS f s t K` (`LocalAcyclicity/CospecializationMapDerived.lean`) is the
  cospecialization map of Section 0GJT. -/
@[stacks 0GJW,
  sga "4 XVI 2.3" "special case",
  sga "4½ Arcata 5.3.1" "more general",
  sga "4½ Th_finitude 5.2.4" "for proper f"]
theorem isIso_specializationStalk_and_cospecializationMap_of_isProper [IsProper f]
    (K : smallEtaleDerivedCategory X) (m : ℤ) (hK : K.IsGE m)
    (hla : IsLocallyAcyclicRelative B hX hS f K)
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
        ((smallEtaleDerivedPushforwardAb f).obj K)) ∧
      ∃ _ : IsIso ((smallEtaleDerivedPullbackAb
          (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
            (cospecializationUnit B hS f s t K)),
        IsIso (cospecializationMap B hS f s t K) :=
  isIso_specializationMap_and_cospecializationMap_of_isProper B hS f s t
    (fun _ _ g _ => cohomologyCommutesWithBaseChange_of_isProper g)
    (derivedPushforwardStalkFormula B) hX K m hK hla hKt

end AlgebraicGeometry

end
