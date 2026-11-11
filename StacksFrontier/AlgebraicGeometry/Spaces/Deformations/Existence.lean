module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Compatible systems of flat modules with proper support on an algebraic space

Let `(Aₙ)` be an inverse system of rings whose transition maps are surjective with locally
nilpotent kernels, let `A = lim Aₙ`, and fix a big fppf site containing `Spec A` and every
`Spec Aₙ`. Over `Spec A`, read as an algebraic space, fix an algebraic space `X` which is
separated and of finite presentation, and write `Xₙ = X ×_{Spec A} Spec Aₙ` for its
infinitesimal base changes, each a closed subspace of `X`. Grothendieck's existence theorem for
algebraic spaces starts from a compatible system `(Fₙ, φₙ)` in which `Fₙ` is a finitely
presented quasi-coherent `𝒪_{Xₙ}`-module, flat over `Aₙ` and with support proper over `Aₙ`, and
`φₙ : Fₙ ⊗_{𝒪_{Xₙ}} 𝒪_{Xₙ₋₁} ⟶ Fₙ₋₁` is an isomorphism. This module records the standing data
of that theorem.

It is the undetermined-level form of `AlgebraicGeometry.Space.DerivedExistenceSituation`
(Tag 0DIK) and shares all of its geometry: the inverse-limit base, the affine base at a level,
the infinitesimal base changes of `X` and the transitions between them are imported from that
module rather than restated. It is also the algebraic-space form of
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation` (Tag 0CTC), which is the same
situation for schemes.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentSheavesAt`: the quasi-coherent `𝒪_{Xₙ}`-modules on the
  infinitesimal base change at a level, and `AlgebraicGeometry.Space.supportAt` the support of
  such a module as a subset of the points of that base change.
* `AlgebraicGeometry.Space.InverseSystemExistenceSituation`: the data of Stacks 0CX4, the rings,
  the space and the compatible family of finitely presented flat modules with proper support,
  together with three consequences of those data carried as fields (see below).

## Implementation notes

The index `n : ℕ` stands for the level `n + 1` of the source, as for Tags 0CTC and 0DIK, so
that the inverse system is a functor out of `ℕᵒᵖ` and its transitions are the images of
`homOfLE (Nat.le_succ n)`. Surjectivity and local nilpotence are recorded for those consecutive
transitions; every transition of the system is a composite of them, and both properties pass to
composites, the second because a preimage of a nilpotent element under a map with locally
nilpotent kernel is nilpotent.

The inverse-limit ring is Mathlib's `CategoryTheory.Limits.limit` of the system, so `A = lim Aₙ`
holds by construction and needs no field; `AlgebraicGeometry.GrothendieckExistence.limitBase` is
its spectrum. The base changes `Xₙ = X ×_{Spec A} Spec Aₙ` are likewise *defined*, as
`AlgebraicGeometry.Space.spaceAt`, so the cartesian square presenting them is
`AlgebraicGeometry.Space.isPullback_spaceAt` rather than a hypothesis; only the assertion that
the projection `Xₙ ⟶ X` is a closed immersion, which is how the source views `Xₙ` as a closed
subspace, is carried as a field. For the same reason the inclusion `Xₙ ⊂ Xₙ₊₁` is
`AlgebraicGeometry.Space.transitionSpace`, the unique morphism lying over `X` and over the
transition of affine bases.

Flatness over `Aₙ` and properness of the support over `Aₙ` are flatness and properness relative
to `AlgebraicGeometry.Space.spaceBaseProjection`, the projection `Xₙ ⟶ Spec Aₙ`. Properness of
a closed subset over a base is stated in Tag 0CZD for a morphism which is locally of finite
type, so the field `locallyOfFiniteType` precedes `properSupport` and is consumed by it; the
topology on the points in which the support is closed is
`AlgebraicGeometry.Space.pointTopology`, installed as a local instance.

The comparison `φₙ` is the restriction `Fₙ₊₁ ⊗_{𝒪_{Xₙ₊₁}} 𝒪_{Xₙ}` read as the inverse image
`AlgebraicGeometry.Space.modulePullback` along the closed immersion `Xₙ ⟶ Xₙ₊₁`, which is the
form the equivalence of Tag 04CJ gives it.

Membership of the affine bases in the chosen big fppf site is recorded as the fields
`containsLimitBase` and `containsBaseAt`, because `AlgebraicGeometry.BigFppfSite.Contains` is a
size condition that no geometric hypothesis supplies; it is not a restriction on the inverse
system.

## References

* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
* [Stacks Project, Tag 0CTC](https://stacks.math.columbia.edu/tag/0CTC)
* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase A)) (hSn : ∀ n : ℕ, B.Contains (baseAt A n))
    (X : Over (schemeSpace (limitBaseObject A B hS)))

/-- The quasi-coherent `𝒪_{Xₙ}`-modules on the infinitesimal base change at level `n` of an
algebraic space over the inverse-limit base, that is, the category `QCoh(𝒪_{Xₙ})` of Tag 03G9 of
`AlgebraicGeometry.Space.spaceAt`. -/
abbrev QuasicoherentSheavesAt (n : ℕ) :=
  QuasicoherentSheaves.{u, u} B (limitBase A) hS (spaceAt A B hS hSn X n).1
    (spaceAt A B hS hSn X n).2

/-- The support of a quasi-coherent module on the infinitesimal base change at level `n`, as a
subset of the points of that base change: the support of Tag 04KA of the underlying abelian
sheaf. -/
abbrev supportAt (n : ℕ) (G : QuasicoherentSheavesAt A B hS hSn X n) :
    Set (points B (limitBase A) hS (spaceAt A B hS hSn X n).1) :=
  supportOfSheaf B (limitBase A) hS (spaceAt A B hS hSn X n).1
    ((SheafOfModules.toSheaf _).obj G.obj)

/-- The standing data of Grothendieck's existence theorem for algebraic spaces (Stacks 0CX4):
an inverse system of rings with surjective, locally nilpotent transitions, a separated algebraic
space of finite presentation over the inverse-limit ring, and a compatible system of finitely
presented quasi-coherent modules on its infinitesimal base changes which are flat over, and have
support proper over, the affine base at their level.

Besides the source's data and hypotheses this structure carries three fields that follow from
them: `closedSpaceProjection` (the projection `Xₙ ⟶ X` is a closed immersion, which follows from
the surjectivity of the transitions), `closed_support` (part of support proper over `Aₙ`) and
`locallyOfFiniteType` (which follows from the finite presentation of `X`). The Situation exactly
as stated is `AlgebraicGeometry.Space.FlatSheafExistenceSituation`. -/
structure InverseSystemExistenceSituation where
  /-- The inverse system of rings `(Aₙ)`. -/
  system : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- Its consecutive transition maps are surjective. -/
  transition_surjective (n : ℕ) :
    Function.Surjective (system.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of those transition maps are locally nilpotent ideals. -/
  transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (system.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The big fppf site in which the algebraic spaces are taken. -/
  B : BigFppfSite.{u}
  /-- The inverse-limit base `Spec A` belongs to the site. -/
  containsLimitBase : B.Contains (limitBase system)
  /-- Every affine base `Spec Aₙ` belongs to the site. -/
  containsBaseAt (n : ℕ) : B.Contains (baseAt system n)
  /-- The algebraic space `X` over the inverse-limit base `Spec A`. -/
  X : Over (schemeSpace
    (limitBaseObject system B containsLimitBase))
  /-- `X` is separated over `Spec A`: its diagonal is a closed immersion. -/
  separated : IsSeparatedOver B (limitBase system) containsLimitBase X.left.1
  /-- `X` is of finite presentation over `Spec A`. -/
  finitePresentation :
    IsFinitePresentation B (limitBase system) containsLimitBase X.hom.hom
  /-- Each infinitesimal base change `Xₙ = X ×_{Spec A} Spec Aₙ` is a closed subspace of `X`:
  its projection to `X` is a closed immersion. -/
  closedSpaceProjection (n : ℕ) :
    IsClosedImmersion B (limitBase system) containsLimitBase
      (spaceProjection system B containsLimitBase containsBaseAt X n).hom
  /-- The quasi-coherent `𝒪_{Xₙ}`-module `Fₙ`. -/
  sheaf (n : ℕ) :
    QuasicoherentSheavesAt system B containsLimitBase containsBaseAt X n
  /-- Each `Fₙ` is of finite presentation. -/
  finitePresentation_sheaf (n : ℕ) : (sheaf n).obj.IsFinitePresentationOnSite
  /-- Each `Fₙ` is flat over `Aₙ`, that is, flat relative to the projection
  `Xₙ ⟶ Spec Aₙ`. -/
  flat_sheaf (n : ℕ) :
    IsFlatOver B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).2
      (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom (sheaf n).obj
  /-- The support of each `Fₙ` is a closed subset of the points of `Xₙ`. -/
  closed_support (n : ℕ) :
    IsClosed (supportAt system B containsLimitBase containsBaseAt X n (sheaf n))
  /-- The projection `Xₙ ⟶ Spec Aₙ` is locally of finite type, which is what properness of a
  closed subset of `Xₙ` over `Spec Aₙ` is stated relative to. -/
  locallyOfFiniteType (n : ℕ) :
    IsLocallyOfFiniteType B (limitBase system) containsLimitBase
      (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom
  /-- The support of each `Fₙ` is proper over `Aₙ`: the reduced induced closed subspace of `Xₙ`
  it carries is proper over `Spec Aₙ`. -/
  properSupport (n : ℕ) :
    IsProperOver B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).2
      (schemeSpace
        (baseObjectAt system B containsLimitBase containsBaseAt n)).2
      (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom
      (locallyOfFiniteType n)
      (supportAt system B containsLimitBase containsBaseAt X n (sheaf n))
      (closed_support n)
  /-- The comparison isomorphism `φₙ₊₁ : Fₙ₊₁ ⊗_{𝒪_{Xₙ₊₁}} 𝒪_{Xₙ} ⟶ Fₙ`, the restriction being
  the inverse image along the closed immersion `Xₙ ⟶ Xₙ₊₁`. -/
  φ (n : ℕ) :
    (modulePullback B (limitBase system) containsLimitBase
        (transitionSpace system B containsLimitBase containsBaseAt X n)).obj
      (sheaf (n + 1)).obj ≅ (sheaf n).obj

end AlgebraicGeometry.Space

end
