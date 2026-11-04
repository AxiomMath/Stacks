module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethSchemeTorIndependent
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0FLQ] at the fibre product of two schemes, with nothing carried

`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_pullback_of_torIndependent_of_baseChange`
reduces the relative conclusion of [Stacks, Tag 0FLQ] to the single carried proposition
`AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent`, which is [Stacks, Tag 08IB].  That
proposition is now proved, by
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`, so the reduction can be composed and
the tag's relative conclusion holds under the tag's own hypotheses alone.

This module exists only to compose the two.  It cannot be done in either of their files: the
module proving Tag 08IB already imports the Künneth module, so an import the other way would be
a cycle.

## Main results

* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme`: **the relative conclusion of
  [Stacks, Tag 0FLQ]**, with no hypothesis beyond the tag's own.

## Also here

* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme`, in
  `StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/KunnethGlobalCupProduct.lean`: **the
  tag's second conclusion**, that over an affine base the global Künneth map of
  [Stacks, Tag 0G7V] is an isomorphism, also with no hypothesis beyond the tag's own.  It is no
  longer stated for a quantified global cup product: the cup product is the canonical one,
  `Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct` of the one-point comparison
  `Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace`, whose three
  fields are all constructed on an arbitrary ringed space — the derived pullback along the
  structure morphism `π : S ⟶ ({*}, A)` of [Stacks, Tag 01BH], its adjunction, and an
  *invertible* comparison of the derived tensor product over `A = Γ(S, 𝒪_S)` with the one over
  `𝒪_S`.  The affineness of the base enters through the Spec–Γ equivalence of
  [Stacks, Tag 06Z0], in the form of the instances
  `AlgebraicGeometry.AffineDerivedSections.full_derivedSectionsLeftAdjoint` and
  `faithful_derivedSectionsLeftAdjoint`, which make the unit invertible, and of
  `AlgebraicGeometry.AffineDerivedSections.isIso_derivedSectionsAdjunction_counit_app`.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.DerivedKunneth

variable {S : Scheme.{u}} {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **[Stacks, Tag 0FLQ], the relative conclusion, with no hypothesis beyond the tag's own.**
Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes with
`X` and `Y` Tor independent over `S`, let `W = X ×_S Y` with projections `p` and `q`, and let
`K ∈ D_QCoh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)`.  Then the relative Künneth morphism of
[Stacks, Tag 0FLP]

`Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ R(p ≫ a)_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is an isomorphism.

This is `isIso_kunnethMap_pullback_of_torIndependent_of_baseChange` with its one remaining
carried proposition discharged against the proved [Stacks, Tag 08IB].  All three comparisons the
source's proof chains together are now proved in this library: `hproj₁` and `hproj₂` from
[Stacks, Tag 08EU], with the interchanged-order conjugation supplied by the proved braiding
compatibility of [Stacks, Tag 079U], and `hbase` from [Stacks, Tag 08IB]. -/
@[stacks 0FLQ "the relative conclusion, at the fibre product of two schemes, with no \
hypothesis beyond the tag's own"]
theorem isIso_kunnethMapScheme
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M) :=
  isIso_kunnethMap_pullback_of_torIndependent_of_baseChange a b
    AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent hTor K M hK hM

end Stacks.Cohomology.DerivedKunneth

end
