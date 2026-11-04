module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictlyHenselianFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionUnboundedDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationUnitStalk
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# The cospecialization map of a proper morphism

Let `f : X ⟶ S` be a proper morphism of schemes, `s` a geometric point of `S`, `t` a geometric
point of `Spec 𝒪^{sh}_{S,s}`, and write `Y = X ×_S Spec 𝒪^{sh}_{S,s}`, `i : X_s ⟶ Y` for the
closed geometric fibre and `h : X_t ⟶ Y` for the fibre over `t`. The proof of Tag 0GJW rests on
one consequence of the proper base change theorem: for every bounded below object `M` of
`D(Y_étale)` with torsion cohomology sheaves, pullback of derived sections

`RΓ(Y, M) ⟶ RΓ(X_s, i⁻¹M)`

to the closed geometric fibre is an isomorphism. In the source this is Lemma 0DDF for the proper
morphism `Y ⟶ Spec 𝒪^{sh}_{S,s}` at the closed point, the stalk of a complex on the spectrum of a
strictly henselian local ring at its closed point being its derived global sections. This file
names that input, `AlgebraicGeometry.HasClosedGeometricFibreRestrictionIso`, proves it from the
proper base change theorem (Tag 095T, carried as the single argument `h095T`), and derives the two
invertibility statements of the proof of Tag 0GJW that concern the cospecialization map.

## Main definitions

* `AlgebraicGeometry.HasClosedGeometricFibreRestrictionIso` — pullback of derived sections from
  the base change of a proper morphism to the strict henselization to its closed geometric fibre
  is an isomorphism on bounded below objects with torsion cohomology sheaves.

## Main results

* `AlgebraicGeometry.hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange`
  — that property holds as soon as cohomology commutes with base change for proper morphisms.
* `AlgebraicGeometry.torsionCohomologyProperty_pushforward_cospecializationFibre` —
  `Rh_*(K|_{X_t})` has torsion cohomology sheaves when `K` is bounded below with torsion
  cohomology sheaves.
* `AlgebraicGeometry.isIso_cospecializationMap_of_cohomologyCommutesWithBaseChange` — the
  cospecialization map is an isomorphism.
* `AlgebraicGeometry.isIso_globalSections_map_cospecializationUnit` — the comparison
  `β_{K,s,t}` induces an isomorphism `RΓ(Y, K|_Y) ⟶ RΓ(Y, Rh_*(K|_{X_t}))` on derived sections.

The closing step, once Tag 095T is in the library as
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, is to pass
`fun _ _ f _ => cohomologyCommutesWithBaseChange_of_isProper.{u, 0} f` as `h095T`.

## References

* [Stacks Project, Tag 0GJW](https://stacks.math.columbia.edu/tag/0GJW)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Proper base change at the closed geometric fibre over the strict henselization.** For every
proper morphism `f : X ⟶ S` in the big étale site `B`, every geometric point `s` of `S` and every
bounded below object `M` of `D(Y_étale)` with torsion cohomology sheaves, where
`Y = X ×_S Spec 𝒪^{sh}_{S,s}`, pullback of derived sections

`RΓ(Y, M) ⟶ RΓ(X_s, i⁻¹M)`

along the canonical morphism `i : X_s ⟶ Y` from the geometric fibre is an isomorphism.

This is the consequence of the proper base change theorem (Tag 095T, through Lemmas 0DDE and
0DDF for the proper base change `Y ⟶ Spec 𝒪^{sh}_{S,s}`) that the proof of Tag 0GJW uses. -/
def HasClosedGeometricFibreRestrictionIso (B : BigEtaleSite.{u}) : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (hS : B.Contains S) (f : X ⟶ S) [IsProper f] (s : GeometricPoint S)
    (M : smallEtaleDerivedCategory (strictHenselizationBaseChange B hS f s)) (m : ℤ),
    M.IsGE m →
    Stacks.Torsion.torsionCohomologyProperty.{u + 1}
      (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) M →
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).app M)

/-- The geometric fibre `X_s` is the fibre of the base change `Y = X ×_S Spec 𝒪^{sh}_{S,s}` over
the canonical lift of `s` to `Spec 𝒪^{sh}_{S,s}`: the square

```
X_s ----i----> Y
 |             |
 v             v
 s ----------> Spec 𝒪^{sh}_{S,s}
```

is cartesian, being the left half of the cartesian rectangle of `X_s = X ×_S s` whose right half
is the cartesian square of `Y`. -/
theorem isPullback_geometricFibreToStrictHenselizationBaseChange (B : BigEtaleSite.{u})
    {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S) (s : GeometricPoint S) :
    IsPullback (geometricFibreToStrictHenselizationBaseChange B hS f s)
      (geometricFibreToPoint f s) (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      (geometricPointToStrictHenselization B S hS s) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f (strictHenselizationToBase B S hS s))
  rw [geometricFibreToStrictHenselizationBaseChange_comp_toSource,
    geometricPointToStrictHenselization_comp]
  exact IsPullback.of_hasPullback f s.hom

/-- **Proper base change at the closed geometric fibre over the strict henselization, from Tag
095T.** If cohomology commutes with base change for every proper morphism (Tag 095T), then
`AlgebraicGeometry.HasClosedGeometricFibreRestrictionIso` holds for every big étale site.

The base change `Y ⟶ Spec 𝒪^{sh}_{S,s}` of a proper `f` is proper, `𝒪^{sh}_{S,s}` is strictly
henselian, the canonical lift of `s` lies over its closed point, and `X_s` is the fibre of `Y`
there (`AlgebraicGeometry.isPullback_geometricFibreToStrictHenselizationBaseChange`), so this is
`isIso_smallEtaleDerivedGlobalSectionsRestriction_of_cohomologyCommutesWithBaseChange` in the
namespace `Stacks.EtaleCohomology`.

The single argument `h095T` is the statement of the proper base change theorem. -/
theorem hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange
    (B : BigEtaleSite.{u})
    (h095T : ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [IsProper f],
      CohomologyCommutesWithBaseChange.{u, 0} f) :
    HasClosedGeometricFibreRestrictionIso B := by
  intro X S hS f _ s M m hM hMt
  have := etaleLocalRing_strictHenselian B S hS s
  exact isIso_smallEtaleDerivedGlobalSectionsRestriction_of_cohomologyCommutesWithBaseChange
    (geometricPointToStrictHenselization B S hS s)
    ((congrArg (geometricPointToStrictHenselization B S hS s) (Subsingleton.elim _ _)).trans
      (geometricPointToStrictHenselization_closedPoint B S hS s))
    (strictHenselizationBaseChangeToStrictHenselization B hS f s)
    (geometricFibreToStrictHenselizationBaseChange B hS f s) (geometricFibreToPoint f s)
    (h095T _) (isPullback_geometricFibreToStrictHenselizationBaseChange B hS f s) M m hM hMt

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))
  (K : smallEtaleDerivedCategory X)

/-- The restriction `K|_{X_t}` of a bounded below object to the fibre over `t`, and its derived
direct image `Rh_*(K|_{X_t})` on `Y`, are bounded below in the same degree: inverse image is
exact, and an unbounded right derived functor is left t-exact. -/
theorem isGE_pushforward_cospecializationFibre (m : ℤ) (hK : K.IsGE m) :
    ((smallEtaleDerivedPushforwardAb (cospecializationFibreToBaseChange B hS f s t)).obj
      ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K)).IsGE m := by
  have := (smallEtalePullbackAb
    (cospecializationFibreToSource B hS f s t)).isGE_obj_mapDerivedCategory K m hK
  exact Stacks.DerivedFunctor.isGE_totalRightDerived_obj
    (smallEtalePushforwardAb (cospecializationFibreToBaseChange B hS f s t)) _ m

/-- **`Rh_*(K|_{X_t})` has torsion cohomology sheaves** when `K` is bounded below with torsion
cohomology sheaves (the use of Tag 0DDD in the proof of Tag 0GJW). Inverse image preserves torsion
cohomology sheaves, and `h : X_t ⟶ Y`, a base change of the morphism of affine schemes
`t ⟶ Spec 𝒪^{sh}_{S,s}`, is quasi-compact and quasi-separated, so its unbounded derived direct
image carries bounded below objects with torsion cohomology sheaves to objects with torsion
cohomology sheaves
(`Stacks.EtaleCohomology.torsionCohomologyProperty_smallEtaleDerivedPushforwardAb`). -/
theorem torsionCohomologyProperty_pushforward_cospecializationFibre (m : ℤ) (hK : K.IsGE m)
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K) :
    Stacks.Torsion.torsionCohomologyProperty.{u + 1}
      (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
      ((smallEtaleDerivedPushforwardAb (cospecializationFibreToBaseChange B hS f s t)).obj
        ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K)) :=
  torsionCohomologyProperty_smallEtaleDerivedPushforwardAb _ _ m
    ((smallEtalePullbackAb (cospecializationFibreToSource B hS f s t)).isGE_obj_mapDerivedCategory
      K m hK)
    (torsionCohomologyProperty_smallEtaleDerivedPullbackAb _ K hKt)

/-- **The cospecialization map of a proper morphism is an isomorphism** (the cospecialization
half of Tag 0GJW) for a bounded below object `K` with torsion cohomology sheaves, granted the
proper base change theorem (Tag 095T) as the single argument `h095T`.

By `AlgebraicGeometry.isIso_cospecializationMap_iff` it is enough that pullback by `i` on derived
sections of `Rh_*(K|_{X_t})` be invertible. That object is bounded below with torsion cohomology
sheaves (`AlgebraicGeometry.isGE_pushforward_cospecializationFibre`,
`AlgebraicGeometry.torsionCohomologyProperty_pushforward_cospecializationFibre`), and pullback
of derived sections to the closed geometric fibre is invertible on such objects
(`AlgebraicGeometry.hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange`).

The invertibility of `i⁻¹β_{K,s,t}`, which the map is defined from, is Tag 0GJU
(`AlgebraicGeometry.isIso_pullback_cospecializationUnit`); the map exists whenever it holds, and
it is invertible for any such instance. -/
theorem isIso_cospecializationMap_of_cohomologyCommutesWithBaseChange
    [IsIso ((smallEtaleDerivedPullbackAb
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
        (cospecializationUnit B hS f s t K))]
    (h095T : ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [IsProper f],
      CohomologyCommutesWithBaseChange.{u, 0} f) [IsProper f] (m : ℤ) (hK : K.IsGE m)
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K) :
    IsIso (cospecializationMap B hS f s t K) :=
  (isIso_cospecializationMap_iff B hS f s t K).2
    (hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange B h095T hS f s _ m
      (isGE_pushforward_cospecializationFibre B hS f s t K m hK)
      (torsionCohomologyProperty_pushforward_cospecializationFibre B hS f s t K m hK hKt))

/-- **`β_{K,s,t}` is an isomorphism on derived sections over `Y`** for a bounded below object `K`
with torsion cohomology sheaves relative to which `f` is locally acyclic, granted the proper base
change theorem (Tag 095T) as `h095T` and the stalk computation of Tag 03Q9 as `h03Q9`. Pullback
of derived sections to `X_s` is invertible at source and target of `β_{K,s,t}`, both being bounded
below with torsion cohomology sheaves, and it carries `RΓ(Y, β_{K,s,t})` to
`RΓ(X_s, i⁻¹β_{K,s,t})`, which is invertible by Tag 0GJU
(`AlgebraicGeometry.isIso_pullback_cospecializationUnit`). -/
theorem isIso_globalSections_map_cospecializationUnit (hX : B.Contains X)
    (h095T : ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [IsProper f],
      CohomologyCommutesWithBaseChange.{u, 0} f)
    (h03Q9 : DerivedPushforwardStalkFormula B) [IsProper f] (m : ℤ) (hK : K.IsGE m)
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K)
    (hla : IsLocallyAcyclicRelative B hX hS f K) :
    IsIso ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).map
      (cospecializationUnit B hS f s t K)) := by
  have := isIso_pullback_cospecializationUnit_of_derivedPushforwardStalkFormula B hX hS f s t h03Q9
    K m hK hla
  have hpbc := hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange B h095T
  have := hpbc hS f s _ m
    ((smallEtalePullbackAb
      (strictHenselizationBaseChangeToSource B hS f s)).isGE_obj_mapDerivedCategory K m hK)
    (torsionCohomologyProperty_smallEtaleDerivedPullbackAb _ K hKt)
  have := hpbc hS f s _ m (isGE_pushforward_cospecializationFibre B hS f s t K m hK)
    (torsionCohomologyProperty_pushforward_cospecializationFibre B hS f s t K m hK hKt)
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ ((smallEtaleDerivedGlobalSectionsRestriction
    (geometricFibreToStrictHenselizationBaseChange B hS f s)).app _) inferInstance ?_
  rw [(smallEtaleDerivedGlobalSectionsRestriction
    (geometricFibreToStrictHenselizationBaseChange B hS f s)).naturality, Functor.comp_map]
  infer_instance

end AlgebraicGeometry

end
