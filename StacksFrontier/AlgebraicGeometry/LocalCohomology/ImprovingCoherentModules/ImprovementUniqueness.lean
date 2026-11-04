module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImmediateSpecializationDepth
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.Improvement
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# An improvement is an improvement along a nested pair, and is unique

An improvement of a coherent `𝒪_X`-module `F` along a closed subset `Z`
(`AlgebraicGeometry.IsImprovement`) differs from an improvement along the nested pair
`Z' ⊆ Z` (`AlgebraicGeometry.IsNestedImprovement`) in one clause only: at the points of `Z`
reached by an immediate specialization from an associated point of `F` outside `Z`, the former
asks for depth exactly one and the latter for depth at least one. The two notions agree for
`Z' = Z ∖ {reached points}`, because the depth at a reached point is automatically at most one:
the reached point witnesses an associated point of the target whose closure has dimension one at
that point.

Consequently the uniqueness of an improvement is the uniqueness of an improvement along a nested
pair, which this library already has unconditionally.

## Main definitions

* `AlgebraicGeometry.NotReachedFromOutside`: the points of the closed subset which are *not*
  reached from outside it, that is the points at which an improvement must have depth at least
  two.

## Main results

* `AlgebraicGeometry.depth_stalk_le_one_of_reachedFromOutside`: a map of coherent modules which
  is an isomorphism on the stalks away from `Z` has target of depth at most one at every point of
  `Z` reached from outside `Z`.
* `AlgebraicGeometry.isNestedImprovement_of_isImprovement` and
  `AlgebraicGeometry.isImprovement_of_isNestedImprovement`: an improvement along `Z` is exactly an
  improvement along the nested pair `NotReachedFromOutside Z F ⊆ Z`.
* `AlgebraicGeometry.improvement_unique`: two improvements of one coherent module along one closed
  subset are isomorphic by a unique isomorphism over that module. This is the uniqueness assertion
  of [Stacks, Tag 0DX5].

## Implementation notes

The depth bound at a reached point is
`AlgebraicGeometry.depth_stalk_le_one_of_isAssociatedPoint_of_isImmediateSpecialization`. Its
input is an associated point of the *target*, which is obtained from the associated point of the
source by `AlgebraicGeometry.isAssociatedPrimeStacks_of_injective`: the stalk map at a point
outside `Z` is bijective, hence injective, and an injective linear map carries an associated prime
of its source to one of its target. So the bound needs only the clause away from `Z` and not the
clause at the reached points themselves, which is why it also applies to a map that is only known
to be an improvement along a nested pair.

The module structure on a stalk is spelled out wherever a depth appears, as in
`AlgebraicGeometry.IsImprovement` and `AlgebraicGeometry.IsNestedImprovement`, so that the
statements fit together without transport.

Uniqueness is `AlgebraicGeometry.nestedImprovement_unique`, which needs the subset to be stable
under specialization; a closed subset is, by `IsClosed.stableUnderSpecialization`. No dualizing
complex and no condition on immediate specializations is used, and in particular neither the
universal catenarity of `X` nor the `(S₁)` condition on the formal fibres of its local rings —
those two hypotheses of the source enter only its existence proof.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The points of `Z` which are *not* reached from outside `Z` for `F`: those at which an
improvement of `F` along `Z` is required to have depth at least two. -/
public def NotReachedFromOutside {X : Scheme.{u}} (Z : Set X) (F : X.Modules) : Set X :=
  {x | x ∈ Z ∧ ¬ ReachedFromOutside Z F x}

/-- A point lies in `NotReachedFromOutside Z F` if and only if it lies in `Z` and is not reached
from outside `Z` for `F`. -/
@[simp]
public theorem mem_notReachedFromOutside {X : Scheme.{u}} (Z : Set X) (F : X.Modules) (x : X) :
    x ∈ NotReachedFromOutside Z F ↔ x ∈ Z ∧ ¬ ReachedFromOutside Z F x :=
  Iff.rfl

/-- A point of `Z` reached from outside `Z` for `F` is a point of `Z` outside
`NotReachedFromOutside Z F`, and conversely. -/
public theorem reachedFromOutside_of_notMem_notReachedFromOutside {X : Scheme.{u}} {Z : Set X}
    {F : X.Modules} {x : X} (hx : x ∈ Z) (hx' : x ∉ NotReachedFromOutside Z F) :
    ReachedFromOutside Z F x :=
  not_not.mp fun h => hx' ⟨hx, h⟩

/-- A map of coherent modules which is an isomorphism on the stalks away from `Z` has target of
depth at most one at every point of `Z` reached from outside `Z`.

The point `x'` witnessing that `x` is reached is an associated point of the source lying outside
`Z`, so the stalk map at `x'` is bijective and `x'` is an associated point of the target as well;
and the target has depth at most one at an immediate specialization of one of its associated
points. -/
public theorem depth_stalk_le_one_of_reachedFromOutside {X : Scheme.{u}} [IsLocallyNoetherian X]
    {Z : Set X} {F G : X.Modules} [G.IsCoherent] (φ : F ⟶ G)
    (hiso : ∀ x : X, x ∉ Z →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf))
    (x : X) (hr : ReachedFromOutside Z F x) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) ≤ 1 := by
  obtain ⟨x', hx'Z, hass, himm⟩ := hr
  let : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let : Module (X.presheaf.stalk x')
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x') :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x'
  let : Module (X.presheaf.stalk x')
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x') :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x'
  -- the stalk map at `x'` is bijective, hence injective
  have hbij : Function.Bijective
      (stalkMapLinear (R := X.presheaf) F.val G.val φ.val x') :=
    (ConcreteCategory.isIso_iff_bijective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x').map φ.mapPresheaf)).mp (hiso x' hx'Z)
  -- so `x'` is an associated point of the target
  have hassG : x' ∈ Stacks.Divisors.associatedPoints G :=
    @isAssociatedPrimeStacks_of_injective (X.presheaf.stalk x')
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x')
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x') _ _ _ _ _
      (stalkMapLinear (R := X.presheaf) F.val G.val φ.val x') hbij.1 _ hass
  exact depth_stalk_le_one_of_isAssociatedPoint_of_isImmediateSpecialization G x' x hassG himm
    (Scheme.Modules.finite_stalk_of_isCoherent G x)

/-- An improvement of `F` along `Z` is an improvement along the nested pair
`NotReachedFromOutside Z F ⊆ Z`: the depth equality at the reached points is in particular a lower
bound. -/
public theorem isNestedImprovement_of_isImprovement {X : Scheme.{u}} {Z : Set X}
    {F G : X.Modules} {φ : F ⟶ G} (h : IsImprovement Z φ) :
    IsNestedImprovement Z (NotReachedFromOutside Z F) φ := by
  refine ⟨h.1, h.2.1, fun x hx hx' => ?_, fun x hx => h.2.2.2 x hx.1 hx.2⟩
  obtain ⟨h₁, h₂⟩ := h.2.2.1 x hx (reachedFromOutside_of_notMem_notReachedFromOutside hx hx')
  exact ⟨h₁, h₂.ge⟩

/-- An improvement along the nested pair `NotReachedFromOutside Z F ⊆ Z` is an improvement of `F`
along `Z`: the depth at a reached point is at least one by the nested condition and at most one by
`AlgebraicGeometry.depth_stalk_le_one_of_reachedFromOutside`, hence exactly one. -/
public theorem isImprovement_of_isNestedImprovement {X : Scheme.{u}} [IsLocallyNoetherian X]
    {Z : Set X} {F G : X.Modules} {φ : F ⟶ G}
    (h : IsNestedImprovement Z (NotReachedFromOutside Z F) φ) : IsImprovement Z φ := by
  have : G.IsCoherent := h.1
  refine ⟨h.1, h.2.1, fun x hx hr => ?_, fun x hx hr => h.2.2.2 x ⟨hx, hr⟩⟩
  have hx' : x ∉ NotReachedFromOutside Z F := fun hc => hc.2 hr
  obtain ⟨h₁, h₂⟩ := h.2.2.1 x hx hx'
  exact ⟨h₁, le_antisymm (depth_stalk_le_one_of_reachedFromOutside φ h.2.1 x hr) h₂⟩

/-- **Stacks Project, Tag 0DX5, uniqueness.** Two improvements of a coherent module along the same
closed subset are isomorphic by a unique isomorphism compatible with the two maps.

Each is an improvement along the nested pair `NotReachedFromOutside Z F ⊆ Z`, a subset determined
by `Z` and `F` alone, so the comparison is the one of [Stacks, Tag 0EI4]. Neither the universal
catenarity of `X` nor the `(S₁)` condition on the formal fibres of its local rings is used: those
hypotheses of the source enter only its existence proof. -/
@[stacks 0DX5 "uniqueness of the map F → F'': two maps satisfying conditions (1), (2) and (3) \
are isomorphic by a unique isomorphism under F"]
public theorem improvement_unique (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : IsClosed Z)
    (F G H : X.Modules) [F.IsCoherent] (φ : F ⟶ G) (ψ : F ⟶ H)
    (hφ : IsImprovement Z φ) (hψ : IsImprovement Z ψ) :
    ∃! e : G ≅ H, φ ≫ e.hom = ψ :=
  nestedImprovement_unique X Z (NotReachedFromOutside Z F) hZ.stableUnderSpecialization F G H φ ψ
    (isNestedImprovement_of_isImprovement hφ) (isNestedImprovement_of_isImprovement hψ)

end AlgebraicGeometry

end
