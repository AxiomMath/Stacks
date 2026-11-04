module

public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.FlatPullback
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.FlatPullbackDepth
public import StacksFrontier.Topology.Dimension.DimensionFunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Improving a coherent module along a closed subset

An *improvement* of a coherent `𝒪_X`-module `F` along a closed subset `Z` is a map
`F → F''` of coherent modules which is an isomorphism on stalks away from `Z`, is
surjective on stalks with target of depth exactly one at the points of `Z` reached by an
immediate specialization from an associated point of `F` outside `Z`, and has target of
depth at least two at the remaining points of `Z`.

An improvement has depth at least one at every point of `Z`, so it factors uniquely through
the depth-one quotient of `F` along `Z`; this is the first step of the uniqueness argument
for an improvement. The conditions away from `Z` and the depth bound at the remaining points
of `Z` are inherited by the pullback of an improvement along a flat morphism.

## An improvement need not exist

[Stacks, Tag 0DX5] asserts that an improvement exists for every coherent `F` on a Noetherian,
universally catenary `X` whose local rings have `(S₁)` formal fibres.  **That is false**:
`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf` exhibits
`X = Spec k[u, v, w]`, `Z = V(u, v)` and `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` — all of the
source's hypotheses hold, `k[u, v, w]` being excellent — for which no map out of `F` satisfies
`AlgebraicGeometry.IsImprovement Z`.  The obstruction is that clause (2) at `(u, v, w)` forces the
improvement to agree with `F` at the generalization `(u, v)`, where `F` has depth one, while
clause (3) demands depth at least two there.

The other clauses of [Stacks, Tag 0DX5] hold as stated.  For existence,
`AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient` shows that a map
satisfying the three conditions exists if and only if the depth-one quotient of `F` along `Z` has
depth at least two at every point of `Z` generalizing a reached point without being one, and
`AlgebraicGeometry.existsUnique_isCorrectedImprovement` shows that, with condition (3) at those
points replaced by surjectivity and depth at least one, a map always exists and is unique.
[Stacks, Tag 0EI4] is the later form of the result, in which the depth-two subset is free data
rather than read off `Z` and `F`.

## Main definitions

* `AlgebraicGeometry.IsImprovement`: the three local conditions on a map out of a coherent
  module.

## Main results

* `AlgebraicGeometry.one_le_depth_stalk_of_isImprovement`: an improvement has depth at least
  one at every point of the closed subset.
* `AlgebraicGeometry.existsUnique_lift_depthOneQuotient_of_isImprovement`: an improvement
  factors uniquely through the depth-one quotient of its source along the closed subset.
* `AlgebraicGeometry.isCoherent_pullback_of_isImprovement`: the target of the pullback of an
  improvement is coherent.
* `AlgebraicGeometry.isIso_stalk_pullback_map_of_isImprovement`: the pullback of an
  improvement along an arbitrary morphism is an isomorphism on stalks away from the inverse
  image of the closed subset.
* `AlgebraicGeometry.two_le_depth_stalk_pullback_of_isImprovement`: the depth bound at a
  point of the inverse image whose image is one of the remaining points.

## Implementation notes

The closed subset is a bare `Set X` rather than a closed immersion, and the inverse image of
a closed subscheme is the preimage of that set. Surjectivity on a stalk is epimorphy in `Ab`,
matching `AlgebraicGeometry.IsDepthOneQuotient`, and the two depth conditions are stated with
the module structure on the stalk spelled out, as in
`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`, so that the conditions
fit together with the existing depth results without transport.

Immediate specialization is `TopologicalSpace.IsImmediateSpecialization`, and the associated
points of a module are `Stacks.Divisors.associatedPoints`, the set of points whose stalk has
the maximal ideal of the local ring as an associated prime.

The depth-one quotient of `F` along `Z` is `AlgebraicGeometry.depthOneQuotient`, the quotient
of `F` by the subsheaf of sections supported on `Z`. Its universal property
`AlgebraicGeometry.depthOneQuotient_lift` requires only depth at least one along `Z` of the
target, which both depth conditions of an improvement supply.

The pullback statements in this module are those assertions about a Cohen–Macaulay pullback
that need no hypothesis on the morphism at all: coherence of a pullback is
`AlgebraicGeometry.isCoherent_pullback`, and the stalk of a pullback is the base change of
the stalk, so a bijective stalk map stays bijective, which is
`AlgebraicGeometry.modulePullback_stalkMap_bijective`. The depth bound transports along a
flat morphism by `AlgebraicGeometry.two_le_depth_stalk_pullback_of_flat`, but its hypothesis
is on the image point rather than on the point itself, which is weaker than the condition
upstairs.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of `Z` is *reached from outside* `Z` for `F` when some associated point of `F`
lying outside `Z` specializes to it immediately. These are the points at which an improvement
of `F` along `Z` is required to have depth exactly one. -/
public def ReachedFromOutside {X : Scheme.{u}} (Z : Set X) (F : X.Modules) (x : X) : Prop :=
  ∃ x' : X, x' ∉ Z ∧ x' ∈ Stacks.Divisors.associatedPoints F ∧
    IsImmediateSpecialization x' x

/-- The three local conditions defining an improvement of a coherent module `F` along a closed
subset `Z`: an isomorphism on stalks outside `Z`, surjective on stalks with target of depth
exactly one at the points of `Z` reached from outside `Z`, and target of depth at least two at
the remaining points of `Z`. -/
public def IsImprovement {X : Scheme.{u}} (Z : Set X) {F G : X.Modules} (f : F ⟶ G) : Prop :=
  G.IsCoherent ∧
    (∀ x : X, x ∉ Z →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)) ∧
    (∀ x : X, x ∈ Z → ReachedFromOutside Z F x →
      Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf) ∧
        (letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val x
        Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) = (1 : ℕ∞))) ∧
    (∀ x : X, x ∈ Z → ¬ ReachedFromOutside Z F x →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))

/-- The target of an improvement along `Z` has depth at least one at every point of `Z`: depth
exactly one at the points reached from outside `Z`, and at least two at the others. -/
public theorem one_le_depth_stalk_of_isImprovement {X : Scheme.{u}} {Z : Set X}
    {F G : X.Modules} {f : F ⟶ G} (h : IsImprovement Z f) (x : X) (hx : x ∈ Z) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) := by
  by_cases hr : ReachedFromOutside Z F x
  · exact le_of_eq (h.2.2.1 x hx hr).2.symm
  · exact le_trans (by norm_num) (h.2.2.2 x hx hr)

/-- An improvement of `F` along a closed subset `Z` factors uniquely through the depth-one
quotient of `F` along `Z`: the target has depth at least one along `Z`, which is exactly the
universal property of that quotient. -/
public theorem existsUnique_lift_depthOneQuotient_of_isImprovement {X : Scheme.{u}}
    [IsNoetherian X] {Z : Set X} (hZ : IsClosed Z) (F : X.Modules) [F.IsCoherent]
    {G : X.Modules} (f : F ⟶ G) (h : IsImprovement Z f) :
    ∃! l : depthOneQuotient X Z hZ.stableUnderSpecialization F ⟶ G,
      toDepthOneQuotient X Z hZ.stableUnderSpecialization F ≫ l = f := by
  have := h.1
  exact depthOneQuotient_lift X Z hZ.stableUnderSpecialization F G f
    fun x hx => one_le_depth_stalk_of_isImprovement h x hx

/-- The target of the pullback of an improvement along a morphism with locally Noetherian
source is again coherent. -/
@[stacks 0DX5 "coherence of the target of the pullback, in the assertion about the pullback \
along a Cohen-Macaulay morphism"]
public theorem isCoherent_pullback_of_isImprovement {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) {Z : Set X} {F G : X.Modules} (φ : F ⟶ G) (h : IsImprovement Z φ) :
    ((Scheme.Modules.pullback f).obj G).IsCoherent :=
  have := h.1
  isCoherent_pullback f G

/-- The pullback of an improvement along any morphism of schemes is an isomorphism on stalks at
every point outside the inverse image of the closed subset. -/
@[stacks 0DX5 "the isomorphism away from the inverse image of the closed subscheme, in the \
assertion about the pullback along a Cohen-Macaulay morphism"]
public theorem isIso_stalk_pullback_map_of_isImprovement {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Z : Set X} {F G : X.Modules} (φ : F ⟶ G) (h : IsImprovement Z φ)
    (y : Y) (hy : y ∉ f.base ⁻¹' Z) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      ((Scheme.Modules.pullback f).map φ).mapPresheaf) := by
  have hbij : Function.Bijective
      (stalkMapLinear (R := X.presheaf) F.val G.val φ.val (f.base y)) := by
    have hq := (ConcreteCategory.isIso_iff_bijective _).mp (h.2.1 (f.base y) hy)
    change Function.Bijective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} (f.base y)).map
        ((PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map φ.val)).hom at hq
    exact hq
  have hpb := modulePullback_stalkMap_bijective f.toLRSHom.toShHom F G φ y hbij
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  change Function.Bijective
    ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      ((PresheafOfModules.toPresheaf
        (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map
        ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map
          φ).val)).hom at hpb
  exact hpb

/-- The pullback of an improvement along a flat morphism has depth at least two on its stalk at
every point whose image is a point of the closed subset not reached from outside it. -/
public theorem two_le_depth_stalk_pullback_of_isImprovement {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : Y ⟶ X) [Flat f]
    {Z : Set X} {F G : X.Modules} (φ : F ⟶ G) (h : IsImprovement Z φ)
    (y : Y) (hy : f.base y ∈ Z) (hr : ¬ ReachedFromOutside Z F (f.base y)) :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf y) := by
  have := h.1
  have : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  exact two_le_depth_stalk_pullback_of_flat f G y (h.2.2.2 (f.base y) hy hr)

end AlgebraicGeometry

end
