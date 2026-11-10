module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementExistence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementUniqueness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.PushforwardImprovement
public import StacksFrontier.RingTheory.Depth.AssociatedPrime
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The existence of an improvement across the unreached points of a closed subset

Let `X` be a Noetherian scheme, `Z ⊆ X` a subset stable under specialization, `F` a coherent
`𝒪_X`-module and `U ⊆ X` an open whose complement consists of points of `Z` *not* reached by an
immediate specialization from an associated point of `F` outside `Z`. The construction of an
improvement of `F` along `Z` extends the depth-one quotient `F'` of `F` across that complement by
pushing forward from `U`, and the coherence of the extension is Kollár's criterion: the reduced
closure of every associated point of `F'|_U` must have local dimension at least two at each of its
points outside `U`.

This file discharges that condition for every such `U` — the two ingredients are a dimension
estimate for the closure of a point and the computation of the associated points of a depth-one
quotient — and then settles which `U` exist. A suitable `U` is available exactly when the closure
of the *bad locus*, the part of `Z` which is neither reached from outside `Z` nor already of depth
at least two in `F'`, avoids the reached points; the smallest one is then the complement of that
closure. Under that criterion the existence assertion of [Stacks, Tag 0DX5] holds, and it is not
a consequence of the source's hypotheses.

## Main results

* `AlgebraicGeometry.two_le_ringKrullDim_pointClosureStalk_of_not_isImmediateSpecialization`,
  and its form taking a point of the subscheme rather than of `X`: the reduced closure of `x` has
  local dimension at least two at a specialization `y` of `x` which is neither `x` itself nor an
  immediate specialization of `x`.
* `AlgebraicGeometry.associatedPoints_pullback_opensι`: the associated points of the restriction
  of a module to an open subscheme are the preimage of its associated points.
* `AlgebraicGeometry.associatedPoints_depthOneQuotient_eq`: the associated points of the depth-one
  quotient of `F` along `Z` are the associated points of `F` lying outside `Z`.
* `AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_notReachedFromOutside`:
  the extension of the restricted depth-one quotient is coherent when the complement of `U`
  consists of points of `Z` not reached from outside `Z`.
* `AlgebraicGeometry.LowDepthNotReached`: the bad locus — the points of `Z` which are neither
  reached from outside `Z` nor already of depth at least two in the depth-one quotient.
* `AlgebraicGeometry.existsUnique_improvement_of_disjoint_closure_lowDepthNotReached`: existence
  and uniqueness of an improvement under the criterion that the closure of the bad locus be
  disjoint from the reached points, which is not one of the source's hypotheses.
* `AlgebraicGeometry.disjoint_closure_lowDepthNotReached_of_open`: that criterion is necessary,
  so the theorem above is sharp.
* `AlgebraicGeometry.existsUnique_improvement_of_isClosed_notReachedFromOutside`: the weaker
  form of the criterion asking the whole non-reached locus to be closed.

## Implementation notes

The dimension estimate is read off the coheight of the point in the specialization order on the
integral closed subscheme `W = closure {x}`, through Mathlib's
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`; the specialization preorder on the points of a
scheme is a global instance, and `W` is integral by
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure`. Coheight
zero means being the generic point of `W`, which
`Stacks.Chow.genericPoint_subscheme_vanishingIdeal_closure_singleton` identifies with `x`;
coheight one means immediate specialization from `x` inside `W` by
`Stacks.Chow.coheight_eq_one_iff_isImmediateSpecialization_pointClosure`, and
`TopologicalSpace.IsImmediateSpecialization.map_of_isClosedEmbedding` transports that forward
along the closed immersion of `W`. Both values being excluded, the coheight is at least two.

For the associated points of the depth-one quotient, the two clauses of
`AlgebraicGeometry.IsDepthOneQuotient` supply the two inclusions. Outside `Z` the stalk map of the
quotient map is bijective, so it and the inverse of the linear equivalence it determines both
carry an associated prime to an associated prime by
`AlgebraicGeometry.isAssociatedPrimeStacks_of_injective`. At a point of `Z` the quotient has depth
at least one, and `maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth` rules the point out;
the finiteness of the stalk that needs is
`AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent`.

The module structure on a stalk is spelled out as
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier` wherever a
depth or an associated prime is transported, as in `AlgebraicGeometry.IsDepthOneQuotient` itself,
so that the statements fit together without transport.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The local dimension of the reduced closure of a point -/

/-- **The reduced closure of `x` has dimension at least two at a non-immediate specialization.**
Let `z` be a point of the integral closed subscheme `W` supported on `closure {x}` whose image in
`X` is neither `x` itself nor an immediate specialization of `x`. Then the local ring of `W` at
`z` has Krull dimension at least two.

The dimension is the coheight of `z` in the specialization order on `W`. Coheight zero would make
`z` the generic point of `W`, which is `x`; coheight one would make `x ⤳ z` immediate inside `W`,
hence immediate in `X` because `W → X` is a closed embedding. -/
@[sga "2 VIII 2.5" "partial"]
public theorem
    two_le_ringKrullDim_pointClosureStalk_of_not_isImmediateSpecialization_subscheme
    {X : Scheme.{u}} (x : X)
    (z : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme)
    (hne : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι z ≠ x)
    (himm : ¬ TopologicalSpace.IsImmediateSpecialization x
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι z)) :
    2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk z) := by
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  -- coheight one would give an immediate specialization `x ⤳ z` in `X`
  have h1 : Order.coheight z ≠ 1 := fun h =>
    himm (((Stacks.Chow.coheight_eq_one_iff_isImmediateSpecialization_pointClosure x z).mp
      h).map_of_isClosedEmbedding
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι.isClosedEmbedding)
  -- coheight zero would make `z` the generic point of the closure, which is `x`
  have h0 : Order.coheight z ≠ 0 := by
    intro h
    have hle : z ≤ genericPoint (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme :=
      Scheme.le_iff_specializes.mpr (genericPoint_specializes z)
    rw [Stacks.Chow.scheme_eq_of_le_of_le hle (Order.coheight_eq_zero.mp h hle)] at hne
    exact hne (Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x)
  have h2 : (2 : ℕ∞) ≤ Order.coheight z := by
    simpa [one_add_one_eq_two] using
      Order.add_one_le_of_lt (lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr h0) (Ne.symm h1))
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z]
  exact WithBot.coe_le_coe.mpr h2

/-- **[Stacks, Tag 0AWB]'s dimension condition at a non-immediate specialization.** If `x`
specializes to `y`, with `y` neither equal to `x` nor an immediate specialization of `x`, then the
local ring at `y` of the reduced closed subscheme supported on `closure {x}` has Krull dimension
at least two.

This is
`AlgebraicGeometry.two_le_ringKrullDim_pointClosureStalk_of_not_isImmediateSpecialization_subscheme`
read at the point of the subscheme given by `y`. -/
@[sga "2 VIII 2.5" "Converse"]
public theorem two_le_ringKrullDim_pointClosureStalk_of_not_isImmediateSpecialization
    {X : Scheme.{u}} {x y : X} (hxy : x ⤳ y) (hne : y ≠ x)
    (himm : ¬ TopologicalSpace.IsImmediateSpecialization x y) :
    2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk
      ⟨y, specializes_iff_mem_closure.mp hxy⟩) :=
  two_le_ringKrullDim_pointClosureStalk_of_not_isImmediateSpecialization_subscheme x
    ⟨y, specializes_iff_mem_closure.mp hxy⟩ hne himm

/-! ### The associated points of a depth-one quotient -/

/-- A bijective linear map carries associated primes to associated primes in both directions: it
and the inverse of the linear equivalence it determines are both injective. -/
private theorem isAssociatedPrimeStacks_congr_of_bijective {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M →ₗ[R] N)
    (he : Function.Bijective e) (p : Ideal R) :
    IsAssociatedPrimeStacks R M p ↔ IsAssociatedPrimeStacks R N p :=
  ⟨isAssociatedPrimeStacks_of_injective e he.1 p,
    isAssociatedPrimeStacks_of_injective (LinearEquiv.ofBijective e he).symm.toLinearMap
      (LinearEquiv.ofBijective e he).symm.injective p⟩

/-- **The associated points of a restriction to an open subscheme.** For an open `U` of `X` and an
`𝒪_X`-module `G`, the associated points of `G|_U` are the points of `U` associated to `G`.

The stalk maps of an open immersion are isomorphisms, so the base change in
`Stacks.Divisors.isAssociatedPoint_pullback_iff` does nothing to the associated-prime
condition. -/
public theorem associatedPoints_pullback_opensι {X : Scheme.{u}} (U : X.Opens) (G : X.Modules) :
    Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback U.ι).obj G) =
      U.ι ⁻¹' Stacks.Divisors.associatedPoints G := by
  ext x
  have hbij : Function.Bijective (U.ι.stalkMap x).hom :=
    ConcreteCategory.bijective_of_isIso _
  let : Algebra (X.presheaf.stalk (U.ι.base x)) (U.toScheme.presheaf.stalk x) :=
    (U.ι.stalkMap x).hom.toAlgebra
  rw [Stacks.Divisors.mem_associatedPoints_iff, Set.mem_preimage,
    Stacks.Divisors.mem_associatedPoints_iff,
    Stacks.Divisors.isAssociatedPoint_pullback_iff U.ι G x]
  exact Stacks.Divisors.isAssociatedPrimeStacks_baseChange_bijective_iff hbij _

/-- **The associated points of the depth-one quotient.** The associated points of the depth-one
quotient of a coherent module `F` along a specialization-stable subset `Z` are exactly the
associated points of `F` lying outside `Z`.

Outside `Z` the quotient map is an isomorphism on stalks, which carries associated primes both
ways; at a point of `Z` the quotient has depth at least one, so the maximal ideal is not an
associated prime of its stalk there. -/
public theorem associatedPoints_depthOneQuotient_eq (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : StableUnderSpecialization Z) (F : X.Modules) [F.IsCoherent] :
    Stacks.Divisors.associatedPoints (depthOneQuotient X Z hZ F) =
      Stacks.Divisors.associatedPoints F \ Z := by
  have hq := depthOneQuotient_spec X Z hZ F
  let : (depthOneQuotient X Z hZ F).IsCoherent := hq.1
  -- depth at least one along `Z` keeps the points of `Z` out of the associated points
  have hZno : ∀ x : X, x ∈ Z →
      x ∉ Stacks.Divisors.associatedPoints (depthOneQuotient X Z hZ F) := by
    intro x hxZ hxass
    let : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (depthOneQuotient X Z hZ F).val x
    let : Module.Finite (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
      Scheme.Modules.finite_stalk_of_isCoherent (depthOneQuotient X Z hZ F) x
    exact maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth (hq.2.2.2 x hxZ) hxass
  -- outside `Z` the quotient map is bijective on stalks, so it preserves and reflects
  -- associated points
  have hass : ∀ x : X, x ∉ Z →
      (x ∈ Stacks.Divisors.associatedPoints F ↔
        x ∈ Stacks.Divisors.associatedPoints (depthOneQuotient X Z hZ F)) := by
    intro x hxZ
    let : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    let : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (depthOneQuotient X Z hZ F).val x
    have hbij : Function.Bijective
        (stalkMapLinear (R := X.presheaf) F.val (depthOneQuotient X Z hZ F).val
          (toDepthOneQuotient X Z hZ F).val x) := by
      have hs := (ConcreteCategory.isIso_iff_bijective _).mp (hq.2.2.1 x hxZ)
      exact hs
    exact @isAssociatedPrimeStacks_congr_of_bijective (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) _ _
      (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x) _
      (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (depthOneQuotient X Z hZ F).val x)
      (stalkMapLinear (R := X.presheaf) F.val (depthOneQuotient X Z hZ F).val
        (toDepthOneQuotient X Z hZ F).val x) hbij _
  ext x
  exact ⟨fun hx => ⟨(hass x fun h => hZno x h hx).mpr hx, fun h => hZno x h hx⟩,
    fun hx => (hass x hx.2).mp hx.1⟩

/-! ### Coherence of the extension of the depth-one quotient -/

/-- **[Stacks, Tag 0AWB] for the extension of the depth-one quotient across unreached points.**
Let `X` be a Noetherian universally catenary scheme whose local rings have `(S₁)` formal
fibres, let `Z` be stable under specialization, let `F` be coherent and let `U` be an open whose
complement consists of points of `Z` not reached from outside `Z`. Then the extension of the
restriction to `U` of the depth-one quotient of `F` along `Z` is coherent.

The dimension condition of
`AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary` holds
for this `U`: an associated point `x` of the restricted quotient is, by
`AlgebraicGeometry.associatedPoints_depthOneQuotient_eq`, an associated point of `F` outside `Z`,
and a point `w` of its closure outside `U` lies in `Z` and is not reached from outside `Z`. So `w`
is neither `x` nor an immediate specialization of `x`, since the latter would witness that `w` is
reached from `x`; and
`AlgebraicGeometry.two_le_ringKrullDim_pointClosureStalk_of_not_isImmediateSpecialization` gives
the bound. -/
public theorem isCoherent_pushforward_restrict_depthOneQuotient_of_notReachedFromOutside
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : StableUnderSpecialization Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens)
    (hU : ((U : Set X))ᶜ ⊆ NotReachedFromOutside Z F)
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1) :
    ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F))).IsCoherent := by
  refine isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary
    X Z hZ F U hX (fun z _ => hFibres z) ?_
  intro x hxass y hy
  -- the associated point, pushed to `X`, is an associated point of `F` outside `Z`
  rw [associatedPoints_pullback_opensι, associatedPoints_depthOneQuotient_eq] at hxass
  obtain ⟨hxF, hxZ⟩ := hxass
  -- the point of the closure outside `U` is a point of `Z` not reached from outside `Z`
  rw [Scheme.Opens.opensRange_ι] at hy
  obtain ⟨hwZ, hwnr⟩ := hU hy
  -- distinct from the associated point, and not an immediate specialization of it
  exact two_le_ringKrullDim_pointClosureStalk_of_not_isImmediateSpecialization_subscheme
    (U.ι x) y (fun h => hxZ (h ▸ hwZ)) fun h => hwnr ⟨U.ι x, hxZ, hxF, h⟩

/-! ### The locus at which the depth-one quotient still has to be improved -/

/-- **The bad locus.** The points of `Z` which are not reached from outside `Z` and at which the
depth-one quotient `F'` of `F` along `Z` does not already have depth at least two.

These are exactly the points at which an improvement of `F` along `Z` has to differ from `F'`:
condition (3) of [Stacks, Tag 0DX5] asks for depth at least two at every point of `Z` which is
not reached from outside `Z`, and the construction leaves `F'` untouched elsewhere. -/
public def LowDepthNotReached {X : Scheme.{u}} [IsNoetherian X] (Z : Set X)
    (hZ : StableUnderSpecialization Z) (F : X.Modules) [F.IsCoherent] : Set X :=
  {x | x ∈ NotReachedFromOutside Z F ∧
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (depthOneQuotient X Z hZ F).val x
    ¬ (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x)}

/-- A point lies in `LowDepthNotReached Z hZ F` if and only if it is not reached from outside `Z`
and the stalk of `depthOneQuotient X Z hZ F` there has depth less than two. -/
@[simp]
public theorem mem_lowDepthNotReached {X : Scheme.{u}} [IsNoetherian X] (Z : Set X)
    (hZ : StableUnderSpecialization Z) (F : X.Modules) [F.IsCoherent] (x : X) :
    x ∈ LowDepthNotReached Z hZ F ↔ x ∈ NotReachedFromOutside Z F ∧
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (depthOneQuotient X Z hZ F).val x
      ¬ (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (depthOneQuotient X Z hZ F).val.presheaf x) :=
  Iff.rfl

/-- The bad locus lies in `Z`, hence so does its closure when `Z` is closed. -/
public theorem closure_lowDepthNotReached_subset {X : Scheme.{u}} [IsNoetherian X] {Z : Set X}
    (hZ : IsClosed Z) (F : X.Modules) [F.IsCoherent] :
    closure (LowDepthNotReached Z hZ.stableUnderSpecialization F) ⊆ Z :=
  closure_minimal (fun _ hx => hx.1.1) hZ

/-! ### The criterion for the existence of an improvement -/

/-- **Stacks Project, Tag 0DX5, existence under the sharp criterion.** Let `X` be a Noetherian
scheme which is universally catenary and whose local rings have `(S₁)` formal fibres, let
`Z ⊆ X` be closed and let `F` be a coherent `𝒪_X`-module. Assume the closure of the bad locus
`AlgebraicGeometry.LowDepthNotReached` is disjoint from the points reached from outside `Z`. Then
there is a map `F → F''` of coherent `𝒪_X`-modules satisfying conditions (1), (2) and (3) of the
source along `Z`, and it is unique up to a unique isomorphism under `F`.

The disjointness is not one of the source's hypotheses, and the existence clause of
[Stacks, Tag 0DX5] is false without it; see the implementation notes of the module
`StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementExistence`.
It is exactly the right hypothesis:
`AlgebraicGeometry.disjoint_closure_lowDepthNotReached_of_open` shows it also follows from the
existence of an open as in `AlgebraicGeometry.isImprovement_toDepthOneQuotient_comp_unit`.

The open used is the complement `U` of the closure of the bad locus, which is the smallest
admissible one. Its complement lies in `Z` by
`AlgebraicGeometry.closure_lowDepthNotReached_subset` and consists of unreached points by the
disjointness, which also puts every reached point of `Z` in `U` and discharges the dimension
condition of [Stacks, Tag 0AWB] through
`AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_notReachedFromOutside`;
and a point of `Z ∩ U` which is not reached is outside the bad locus, so the depth-one quotient
already has depth at least two there.

**Deliberately untagged.**  This asks for the disjointness criterion, which is NOT one of the
hypotheses of [Stacks, Tag 0DX5]; an extra hypothesis does not discharge a clause, however
necessary that hypothesis happens to be.  The source's existence clause is false at its own
hypotheses (`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf` of
`ImprovementExistenceCounterexample.lean`), and its corrected form is registered, at exactly the
source's hypotheses, in `CorrectedImprovement.lean`:
`AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient` states the criterion
pointwise as an equivalence, and `AlgebraicGeometry.existsUnique_isCorrectedImprovement` corrects
the conditions instead so that existence holds unconditionally. -/
public theorem existsUnique_improvement_of_disjoint_closure_lowDepthNotReached
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : IsClosed Z)
    (F : X.Modules) [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (hdisj : Disjoint (closure (LowDepthNotReached Z hZ.stableUnderSpecialization F))
      {x : X | ReachedFromOutside Z F x}) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsImprovement Z φ ∧
      ∀ (H : X.Modules) (ψ : F ⟶ H), IsImprovement Z ψ → ∃! e : G ≅ H, φ ≫ e.hom = ψ := by
  have hd := Set.disjoint_left.mp hdisj
  let U : X.Opens := ⟨(closure (LowDepthNotReached Z hZ.stableUnderSpecialization F))ᶜ,
    isClosed_closure.isOpen_compl⟩
  have hUcl : ∀ x : X, x ∈ ((U : Set X))ᶜ →
      x ∈ closure (LowDepthNotReached Z hZ.stableUnderSpecialization F) :=
    fun _ hx => not_not.mp hx
  -- the complement of `U` consists of points of `Z` not reached from outside `Z`
  have hsub : ((U : Set X))ᶜ ⊆ NotReachedFromOutside Z F := fun x hx =>
    ⟨closure_lowDepthNotReached_subset hZ F (hUcl x hx), fun hr => hd (hUcl x hx) hr⟩
  -- every reached point of `Z` lies in `U`
  have hreached : ∀ x : X, x ∈ Z → ReachedFromOutside Z F x → x ∈ (U : Set X) :=
    fun _ _ hr hc => hd hc hr
  have := isCoherent_pushforward_restrict_depthOneQuotient_of_notReachedFromOutside
    X Z hZ.stableUnderSpecialization F U hsub hX hFibres
  -- at an unreached point of `Z ∩ U` the depth-one quotient already has depth at least two
  have himp := isImprovement_toDepthOneQuotient_comp_unit X Z hZ.stableUnderSpecialization F U
    (fun _ hx => (hsub hx).1) hreached fun x hxU hxZ hxr => not_not.mp fun h =>
      hxU (subset_closure
        ((mem_lowDepthNotReached Z hZ.stableUnderSpecialization F x).mpr ⟨⟨hxZ, hxr⟩, h⟩))
  exact ⟨_, _, himp, fun H ψ hψ => improvement_unique X Z hZ F _ H _ ψ himp hψ⟩

/-- **The criterion is necessary.** If some open `U` contains every point of `Z` reached from
outside `Z` and the depth-one quotient of `F` along `Z` already has depth at least two at the
remaining points of `Z ∩ U` — the two hypotheses on `U` of
`AlgebraicGeometry.isImprovement_toDepthOneQuotient_comp_unit` — then the closure of the bad
locus is disjoint from the points reached from outside `Z`.

Indeed the bad locus misses `U` by the depth hypothesis, so its closure lies in the closed set
`X ∖ U`, which the first hypothesis keeps away from the reached points of `Z`; and the closure
lies in `Z`, so it has no reached point outside `Z` either. -/
public theorem disjoint_closure_lowDepthNotReached_of_open
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : IsClosed Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens)
    (hreached : ∀ x : X, x ∈ Z → ReachedFromOutside Z F x → x ∈ (U : Set X))
    (hdepth : ∀ x : X, x ∈ (U : Set X) → x ∈ Z → ¬ ReachedFromOutside Z F x →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (depthOneQuotient X Z hZ.stableUnderSpecialization F).val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (depthOneQuotient X Z hZ.stableUnderSpecialization F).val.presheaf x)) :
    Disjoint (closure (LowDepthNotReached Z hZ.stableUnderSpecialization F))
      {x : X | ReachedFromOutside Z F x} := by
  -- the bad locus misses `U`, so its closure lies in the closed complement of `U`
  have hcl : closure (LowDepthNotReached Z hZ.stableUnderSpecialization F) ⊆ ((U : Set X))ᶜ :=
    closure_minimal (fun x hx hxU => hx.2 (hdepth x hxU hx.1.1 hx.1.2))
      U.isOpen.isClosed_compl
  exact Set.disjoint_left.mpr fun x hx hr =>
    hcl hx (hreached x (closure_lowDepthNotReached_subset hZ F hx) hr)

/-- **Stacks Project, Tag 0DX5.** Let `X` be a Noetherian scheme which is universally catenary and
whose local rings have `(S₁)` formal fibres, let `Z ⊆ X` be closed and let `F` be a coherent
`𝒪_X`-module whose non-reached locus in `Z` is closed. Then there is a map `F → F''` of coherent
`𝒪_X`-modules satisfying conditions (1), (2) and (3) of the source along `Z`, and it is unique up
to a unique isomorphism under `F`.

This is the special case of
`AlgebraicGeometry.existsUnique_improvement_of_disjoint_closure_lowDepthNotReached` in which the
whole non-reached locus, rather than only the closure of the bad locus inside it, is closed: the
bad locus is contained in the non-reached locus, so its closure is too, and the non-reached locus
misses the reached points by definition.

The hypothesis is sufficient but far from necessary — it already fails for the structure sheaf of
a line in the affine plane — and the disjointness criterion of the theorem above should be
preferred.

**Deliberately untagged.**  This is a corollary of
`AlgebraicGeometry.existsUnique_improvement_of_disjoint_closure_lowDepthNotReached` with a
strictly stronger hypothesis, so it asserts strictly less about [Stacks, Tag 0DX5] than that
theorem does; registering the tag here as well would record the same clause twice, once on the
weaker statement.  It is kept because a caller who happens to know the non-reached locus is closed
can use it without computing the bad locus. -/
public theorem existsUnique_improvement_of_isClosed_notReachedFromOutside
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : IsClosed Z)
    (F : X.Modules) [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (hclosed : IsClosed (NotReachedFromOutside Z F)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsImprovement Z φ ∧
      ∀ (H : X.Modules) (ψ : F ⟶ H), IsImprovement Z ψ → ∃! e : G ≅ H, φ ≫ e.hom = ψ :=
  existsUnique_improvement_of_disjoint_closure_lowDepthNotReached X Z hZ F hX hFibres
    (Set.disjoint_left.mpr fun _ hx hr => (closure_minimal (fun _ hy => hy.1) hclosed hx).2 hr)

end AlgebraicGeometry

end
