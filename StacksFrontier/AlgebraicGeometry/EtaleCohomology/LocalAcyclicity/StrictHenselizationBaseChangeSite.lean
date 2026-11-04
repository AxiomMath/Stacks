module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationContains
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.BaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local acyclicity under base change to the strict henselization

Let `f : X ⟶ S` be a morphism of schemes of a big étale site `B`, let `s` be a geometric point of
`S` and let `Y = X ×_S Spec 𝒪^{sh}_{S,s}` be the base change of `X` to the strict henselization.
This file proves that local acyclicity of `f` relative to an object `K` of `D(X_étale)` survives
that base change: the projection `Y ⟶ Spec 𝒪^{sh}_{S,s}` is locally acyclic relative to the
restriction `K|_Y`.

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodAffineToBase` — the structure morphism to `S` of a member
  of the small cofinal family of affine étale neighbourhoods.

## Main results

* `AlgebraicGeometry.etaleNeighborhoodDiagram_map_comp_hom` — a transition morphism of étale
  neighbourhoods of a geometric point, followed by the structure morphism of its target, is the
  structure morphism of its source.
* `AlgebraicGeometry.isLocallyAcyclicAt_strictHenselizationBaseChange` — local acyclicity at a
  geometric point survives base change along `Spec 𝒪^{sh}_{S,s} ⟶ S`.
* `AlgebraicGeometry.isLocallyAcyclicRelative_strictHenselizationBaseChange` — the same for local
  acyclicity relative to `K` at every geometric point.

## References

* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-! ### The étale neighbourhoods as a system of schemes over the base -/

section Neighborhood

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The structure morphism to `S` of a member of the small cofinal family of affine étale
neighbourhoods of a geometric point. -/
abbrev etaleNeighborhoodAffineToBase (a : etaleNeighborhoodAffineIndex B S hS s) :
    (etaleNeighborhoodAffineDiagram B S hS s).obj a ⟶ S :=
  B.inclusion.map ((etaleNeighborhoodAffineInclusion B S hS s).obj a).1.obj.hom

/-- A transition morphism of the diagram of étale neighbourhoods of a geometric point, followed by
the structure morphism of its target, is the structure morphism of its source. -/
theorem etaleNeighborhoodDiagram_map_comp_hom
    {U V : (geometricPointFiber B S hS s).Elements} (m : U ⟶ V) :
    (etaleNeighborhoodDiagram B S hS s).map m ≫ B.inclusion.map V.1.obj.hom =
      B.inclusion.map U.1.obj.hom :=
  (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (Over.w ((SmallEtale.inclusion B S hS).map m.1)))

end Neighborhood

/-! ### Base change along `Spec 𝒪^{sh}_{S,s} ⟶ S` -/

section BaseChange

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (s : GeometricPoint S) (K : smallEtaleDerivedCategory X)

/-- **Local acyclicity survives base change to the strict henselization.** Let `f : X ⟶ S` be
a morphism of schemes of a big étale site `B`, let `K` be an object of `D(X_étale)`, let `s` be a
geometric point of `S` and let `x` be a geometric point of the base change
`Y = X ×_S Spec 𝒪^{sh}_{S,s}` with image `y` in `X`. If `f` is locally acyclic at `y` relative to
`K`, then the projection `Y ⟶ Spec 𝒪^{sh}_{S,s}` is locally acyclic at `x` relative to `K|_Y`. -/
@[stacks 0GJS "base change along the strict henselization at a geometric point",
  sga "4½ Arcata 5.1.4" "special case",
  sga "4½ Arcata 5.1.6" "more general"]
theorem isLocallyAcyclicAt_strictHenselizationBaseChange
    (x : GeometricPoint (strictHenselizationBaseChange B hS f s))
    (h : IsLocallyAcyclicAt B hX hS f K
      (x.map (strictHenselizationBaseChangeToSource B hS f s))) :
    IsLocallyAcyclicAt B (contains_strictHenselizationBaseChange B hS hX f s)
      (contains_strictHenselization_of_contains B hS s)
      (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      ((smallEtaleDerivedPullbackAb
        (strictHenselizationBaseChangeToSource B hS f s)).obj K) x :=
  isLocallyAcyclicAt_of_limit B hX hS (strictHenselizationAffineConeIsLimit B S hS s)
    (contains_strictHenselization_of_contains B hS s)
    (contains_strictHenselizationBaseChange B hS hX f s)
    (IsPullback.of_hasPullback f (strictHenselizationToBase B S hS s)) K
    (etaleNeighborhoodAffineToBase B S hS s)
    (strictHenselizationAffineCone_π_comp_hom_eq B S hS s)
    (fun m => etaleNeighborhoodDiagram_map_comp_hom B S hS s
      ((etaleNeighborhoodAffineInclusion B S hS s).map m)) h

/-- **Local acyclicity survives base change to the strict henselization.** If `f : X ⟶ S` is
locally acyclic relative to an object `K` of `D(X_étale)`, then the projection
`X ×_S Spec 𝒪^{sh}_{S,s} ⟶ Spec 𝒪^{sh}_{S,s}` is locally acyclic relative to the restriction of
`K` to the base change. -/
@[stacks 0GJS "base change along the strict henselization at a geometric point",
  sga "4½ Arcata 5.1.6" "more general"]
theorem isLocallyAcyclicRelative_strictHenselizationBaseChange
    (hla : IsLocallyAcyclicRelative B hX hS f K) :
    IsLocallyAcyclicRelative B (contains_strictHenselizationBaseChange B hS hX f s)
      (contains_strictHenselization_of_contains B hS s)
      (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      ((smallEtaleDerivedPullbackAb
        (strictHenselizationBaseChangeToSource B hS f s)).obj K) := fun x =>
  isLocallyAcyclicAt_strictHenselizationBaseChange B hX hS f s K x
    (hla (x.map (strictHenselizationBaseChangeToSource B hS f s)))

end BaseChange

end AlgebraicGeometry

end
