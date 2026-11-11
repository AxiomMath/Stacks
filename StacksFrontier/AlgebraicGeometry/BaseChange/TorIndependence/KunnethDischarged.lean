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
* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme_of_isPullback`: the same at an
  arbitrary cartesian square of schemes, of which the chosen fibre product is one.

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
@[stacks 0FLQ "first statement: for qcqs a and b with X and Y Tor independent over S, the \
relative Künneth map (0FLP) at X ×_S Y is an isomorphism for K ∈ D_QCoh(𝒪_X) and \
M ∈ D_QCoh(𝒪_Y)"]
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

section IsPullback

-- The three comparisons are assembled at the spellings of
-- `StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/KunnethSchemeTorIndependent.lean`:
-- the standard derived-category model, and `structureSheafRing` unfolded so that the symmetry
-- of the derived tensor product, stated at `Stacks.SheafOfModules.Tensor.ringSheaf`, applies.
attribute [local instance 100000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing

/-- **[Stacks, Tag 0FLQ], the relative conclusion, at an arbitrary cartesian square of
schemes.**  Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of
schemes with `X` and `Y` Tor independent over `S`, let `p : W ⟶ X` and `q : W ⟶ Y` make `W` a
fibre product of `a` and `b`, and let `K ∈ D_QCoh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)`.  Then the
relative Künneth morphism of [Stacks, Tag 0FLP]

`Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ R(p ≫ a)_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is an isomorphism.

The three comparisons of
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` are
proved at the given square: the projection formula at `a` by [Stacks, Tag 08EU], the base change
leg by [Stacks, Tag 08IB] at the flipped square, and the interchanged-order projection formula at
`p` by [Stacks, Tag 08EU] at `p` (quasi-compact and quasi-separated as a base change of `b`)
conjugated by the symmetries of the derived tensor product. -/
@[stacks 0FLQ "the relative conclusion, at an arbitrary cartesian square of schemes"]
theorem isIso_kunnethMapScheme_of_isPullback {W : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ Y)
    (hW : IsPullback p q a b)
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom
      p.toLRSHom.toShHom q.toLRSHom.toShHom (p ≫ a).toLRSHom.toShHom rfl
      (congrArg (fun g : W ⟶ S => g.toLRSHom.toShHom) hW.w.symm) K M) := by
  have : QuasiCompact p := MorphismProperty.of_isPullback (P := @QuasiCompact) hW.flip ‹_›
  have : QuasiSeparated p := MorphismProperty.of_isPullback (P := @QuasiSeparated) hW.flip ‹_›
  exact isIso_kunnethMap_of_projectionFormulas_of_baseChange a.toLRSHom.toShHom
    b.toLRSHom.toShHom p.toLRSHom.toShHom q.toLRSHom.toShHom
    (congrArg (fun g : W ⟶ S => g.toLRSHom.toShHom) hW.w.symm) K M
    (pullbackTensorComparisonComp a.toLRSHom.toShHom p.toLRSHom.toShHom _ _)
    (AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent a inferInstance inferInstance K
      _ hK (isQCohAll_derivedPushforward b hM))
    (isIso_kunnethBaseChangeLeg_of_isIso_derivedBaseChangeMap a.toLRSHom.toShHom
      b.toLRSHom.toShHom p.toLRSHom.toShHom q.toLRSHom.toShHom
      (congrArg (fun g : W ⟶ S => g.toLRSHom.toShHom) hW.w.symm) M
      (AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent q p b a hW.flip inferInstance
        inferInstance (AlgebraicGeometry.TorIndependent.symm hTor)
        (congrArg (fun g : W ⟶ S => g.toLRSHom.toShHom) hW.w.symm) M hM))
    (isIso_adjunctionTensorMapRight_of_braiding
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction p.toLRSHom.toShHom)
      (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf))
      (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.toRingedSpace.sheaf))
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison p.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding X.toRingedSpace)
      (Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding W.toRingedSpace)
      (fun g g' =>
        Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding_naturality W.toRingedSpace g g')
      (Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonBraided
        p.toLRSHom.toShHom) K
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        q.toLRSHom.toShHom).obj M)
      (isIso_derivedBraiding X.toRingedSpace _ _)
      (isIso_derivedBraiding W.toRingedSpace _ _)
      (AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent p inferInstance inferInstance
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          q.toLRSHom.toShHom).obj M) K
        (isQCohAll_dpull q hM) hK))

end IsPullback

end Stacks.Cohomology.DerivedKunneth

end
