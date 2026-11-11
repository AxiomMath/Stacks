module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethDischarged
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedSectionsLeftAdjoint
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointComparisonOnARingedSpace

/-!
# The global conclusion of [Stacks, Tag 0FLQ] for the canonical cup product

`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme` is the relative conclusion of
[Stacks, Tag 0FLQ] with no hypothesis beyond the tag's own.  The tag's *second* conclusion, that
over an affine base the global Künneth morphism of [Stacks, Tag 0G7V]

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is an isomorphism, needs one further input: the invertibility of the `A`-linear global cup
product of Cohomology, Section 0FKU at the pair `(Ra_*K, Rb_*M)`.

This module reduces that second conclusion to the three properties of a
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison` which
`Stacks.Cohomology.DerivedGlobalCupProduct.isIso_globalCupProduct_app` consumes — invertibility
of its tensor comparison, of the unit of its adjunction, and of the counit at complexes with
quasi-coherent cohomology.  Everything else the tag's second conclusion needs is discharged
here: the relative conclusion against the proved [Stacks, Tag 08IB], and the quasi-coherence of
`Ra_*K` and `Rb_*M` against [Stacks, Tag 08D5].

The three properties are then discharged against the one-point comparison of
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace` and the affine
Spec–Γ equivalence of [Stacks, Tag 06Z0], so the tag's second conclusion holds under the tag's
own hypotheses alone.

## Main results

* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme_of_onePointComparison`: the
  global Künneth morphism of [Stacks, Tag 0G7V] at the cup product built from a one-point
  comparison is an isomorphism, over an affine base, as soon as that comparison has invertible
  tensor comparison, invertible unit and invertible counit on the quasi-coherent part.
* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme`: **the second conclusion of
  [Stacks, Tag 0FLQ]**, for the canonical global cup product of Cohomology, Section 0FKU and
  with no hypothesis beyond the tag's own.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.DerivedKunneth

attribute [local instance 100000] HasDerivedCategory.standard

variable {S : Scheme.{u}} {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The second conclusion of [Stacks, Tag 0FLQ] for the canonical cup product, reduced to the
three properties of the one-point comparison.**

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact quasi-separated morphisms of schemes with `S`
affine and `X`, `Y` Tor independent over `S`, and let `K ∈ D_QCoh(𝒪_X)`, `M ∈ D_QCoh(𝒪_Y)`.
Then the global Künneth morphism of [Stacks, Tag 0G7V] for the global cup product built from a
one-point comparison `c` is an isomorphism, provided the tensor comparison of `c` is invertible,
the unit of its adjunction is invertible, and its counit is invertible at every complex with
quasi-coherent cohomology.

The relative conclusion is `isIso_kunnethMapScheme`, which rests on the tag's own hypotheses
alone, and the invertibility of the cup product at `(Ra_*K, Rb_*M)` is
`Stacks.Cohomology.DerivedGlobalCupProduct.isIso_globalCupProduct_app` fed the three
hypotheses, the quasi-coherence of `Ra_*K` and of `Rb_*M` coming from [Stacks, Tag 08D5]. -/
theorem isIso_kunnethGlobalMapScheme_of_onePointComparison
    [IsAffine S] [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (c : OnePointComparison S.toRingedSpace)
    (hcmp : ∀ xy, IsIso (c.tensorComparison.app xy))
    (hunit : ∀ x, IsIso (c.adjunction.unit.app x))
    (hcounit : ∀ U : DerivedCategory S.Modules, IsQCohAll U →
      IsIso (c.adjunction.counit.app U))
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme a b (globalCupProduct c)
      K M) :=
  isIso_kunnethGlobalMapScheme_of_torIndependent_of_baseChange a b
    AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent hTor (globalCupProduct c) K M hK hM
    (isIso_globalCupProduct_app c _ _ (hunit _) (hcmp _)
      (hcounit _ (isQCohAll_derivedPushforward a hK))
      (hcounit _ (isQCohAll_derivedPushforward b hM)))

/-! ### The second conclusion of Tag 0FLQ, with no hypothesis beyond the tag's own -/

/-- **[Stacks, Tag 0FLQ], the global conclusion over an affine base, with no hypothesis beyond
the tag's own.**

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes with
`S` affine and `X` and `Y` Tor independent over `S`, let `W = X ×_S Y` with projections `p` and
`q`, and let `K ∈ D_QCoh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)`.  Then the global Künneth morphism of
[Stacks, Tag 0G7V]

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

for the global cup product of Cohomology, Section 0FKU is an isomorphism.

The cup product is the canonical one, not a parameter: it is
`Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct` of the one-point comparison
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace`, which is the
relative cup product of [Stacks, Tag 0B68] for the structure morphism `π : S ⟶ ({*}, A)` of
[Stacks, Tag 01BH] read through the identification of modules on the point with `A`-modules,
exactly as the source defines `μ`.

The three inputs of `isIso_kunnethGlobalMapScheme_of_onePointComparison` are discharged: the
tensor comparison of that one-point comparison is invertible because it is the `hom` of an
isomorphism of bifunctors, and affineness of the base supplies the invertibility of the unit and
of the counit on the quasi-coherent part, which is the Spec–Γ equivalence of
[Stacks, Tag 06Z0]. -/
@[stacks 0FLQ "second statement: under the same hypotheses with S affine, the global Künneth \
map (0G7V) RΓ(X, K) ⊗^L_A RΓ(Y, M) → RΓ(X ×_S Y, Lp^*K ⊗^L Lq^*M), built from the cup product \
of Section 0FKU, is an isomorphism"]
theorem isIso_kunnethGlobalMapScheme
    [IsAffine S] [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme a b
      (globalCupProduct
        (Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace
          S.toRingedSpace)) K M) :=
  isIso_kunnethGlobalMapScheme_of_onePointComparison a b hTor
    (Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace
      S.toRingedSpace)
    (fun _ => inferInstance)
    (fun x =>
      inferInstanceAs (IsIso
        ((Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedSectionsAdjunction
          S.toRingedSpace).unit.app x)))
    (fun U hU =>
      AlgebraicGeometry.AffineDerivedSections.isIso_derivedSectionsAdjunction_counit_app S U hU)
    K M hK hM

end Stacks.Cohomology.DerivedKunneth

end
