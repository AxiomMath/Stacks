module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapRingChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethDischarged

/-!
# The Künneth map of the inverse-image ringed spaces and the one of the fibre product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and `W = X ×_S Y` with projections `p`,
`q`. The relative Künneth map of [Stacks, Tag 0G4B] is built on the Künneth map of
[Stacks, Tag 0FLP] for the inverse-image ringed spaces `(X, a^{-1}𝒪_S)`, `(Y, b^{-1}𝒪_S)` and
`(W, f^{-1}𝒪_S)`. This file compares that map with the Künneth map of the fibre product of
schemes, whose invertibility on quasi-coherent inputs is [Stacks, Tag 0FLQ]
(`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme`), through the identity-on-spaces
morphisms `(X, 𝒪_X) ⟶ (X, a^{-1}𝒪_S)`.

## Main results

* `Stacks.Cohomology.BoxKunneth.toInverseImageBase_comp_sndProjection`: the square for the second
  projection.
* `Stacks.Cohomology.BoxKunneth.kunnethMap_inverseImageBase`: the comparison, the specialization
  of `Stacks.Cohomology.DerivedKunneth.kunnethMap_ringChange`.
* `Stacks.Cohomology.BoxKunneth.isIso_kunnethMap_inverseImageBase`: its invertible form, from
  [Stacks, Tag 0FLQ].

## Implementation notes

The two comparisons are stated through `type_of%` of the term proving them. Their statements mix
the instance terms elaborated in `KunnethMapRingChange` with those of the de Rham files (which
import `StacksFrontier.AlgebraicGeometry.RingedSpaceModuleSpellings`); a restated type elaborated
here picks the latter, and checking it against the former unfolds the abelian structures of the
categories of sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage

universe u

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 100000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The square for the first projection**: `p` followed by the identity-on-spaces morphism to
`(X, a^{-1}𝒪_S)` is the identity-on-spaces morphism to `(W, f^{-1}𝒪_S)` followed by the first
projection of the inverse-image ringed spaces. -/
theorem toInverseImageBase_comp_fstProjection :
    (pullback.fst a b).toLRSHom.toShHom ≫ toInverseImageBase a =
      toInverseImageBase (pullback.fst a b ≫ a) ≫ fstProjection a b :=
  (toInverseImageBase_comp_relativeInverseImageProjection (pullback.fst a b) a).symm

/-- The square for a projection presented as a factorization. -/
theorem toInverseImageBase_comp_relativeInverseImageProjectionOfFactors {W X' S' : Scheme.{u}}
    (p : W ⟶ X') (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g) :
    toInverseImageBase g ≫
        FiniteOrderDifferentialOperatorCategory.relativeInverseImageProjectionOfFactors p c g hg =
      p.toLRSHom.toShHom ≫ toInverseImageBase c := by
  subst hg
  exact toInverseImageBase_comp_relativeInverseImageProjection p c

/-- **The square for the second projection.** -/
theorem toInverseImageBase_comp_sndProjection :
    (pullback.snd a b).toLRSHom.toShHom ≫ toInverseImageBase b =
      toInverseImageBase (pullback.fst a b ≫ a) ≫ sndProjection a b :=
  (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
    (pullback.fst a b ≫ a) pullback.condition.symm).symm

section Comparison

/- The two comparisons below are elaborated without the `Stacks.SheafOfModules.Tensor.ringSheaf`
spellings of the abelian structures, which are not those of `KunnethMapRingChange`; nothing else
in this file needs this. -/
attribute [-instance] Stacks.RingedSpaceModules.abelian_sheafOfModules_tensorRingSheaf
  Stacks.RingedSpaceModules.isGrothendieckAbelian_sheafOfModules_tensorRingSheaf
  Stacks.RingedSpaceModules.enoughInjectives_sheafOfModules_tensorRingSheaf

/-- **The Künneth map of the inverse-image ringed spaces and the one of the fibre product.**
The Künneth map of [Stacks, Tag 0FLP] for the fibre product of schemes, read through the
composition isomorphisms of the identity-on-spaces morphisms to the inverse-image ringed
spaces, is the Künneth map of the inverse-image ringed spaces at `Rι_{X*}K` and `Rι_{Y*}M`,
followed by the two derived base change maps and the relative cup product of
`(W, 𝒪_W) ⟶ (W, f^{-1}𝒪_S)`. -/
theorem kunnethMap_inverseImageBase
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :
    type_of% (Stacks.Cohomology.DerivedKunneth.kunnethMap_ringChange (inverseImageBaseProjection a)
    (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
    (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
    (sndProjection_comp a b) (toInverseImageBase a) (toInverseImageBase b)
    (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
    (pullback.snd a b).toLRSHom.toShHom (toInverseImageBase_comp_fstProjection a b)
    (toInverseImageBase_comp_sndProjection a b) a.toLRSHom.toShHom (toInverseImageBase_comp a)
    b.toLRSHom.toShHom (toInverseImageBase_comp b) (pullback.fst a b ≫ a).toLRSHom.toShHom
    (toInverseImageBase_comp (pullback.fst a b ≫ a)) rfl
    (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M) :=
  Stacks.Cohomology.DerivedKunneth.kunnethMap_ringChange (inverseImageBaseProjection a)
    (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
    (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
    (sndProjection_comp a b) (toInverseImageBase a) (toInverseImageBase b)
    (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
    (pullback.snd a b).toLRSHom.toShHom (toInverseImageBase_comp_fstProjection a b)
    (toInverseImageBase_comp_sndProjection a b) a.toLRSHom.toShHom (toInverseImageBase_comp a)
    b.toLRSHom.toShHom (toInverseImageBase_comp b) (pullback.fst a b ≫ a).toLRSHom.toShHom
    (toInverseImageBase_comp (pullback.fst a b ≫ a)) rfl
    (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M

/-- **[Stacks, Tag 0FLQ] read on the inverse-image ringed spaces.** For `a` and `b` quasi-compact
and quasi-separated with `X` and `Y` Tor independent over `S`, and `K`, `M` with quasi-coherent
cohomology, the Künneth map of the inverse-image ringed spaces at `Rι_{X*}K` and `Rι_{Y*}M`,
followed by the two derived base change maps and the relative cup product of
`(W, 𝒪_W) ⟶ (W, f^{-1}𝒪_S)`, is invertible: by `kunnethMap_inverseImageBase` it is the Künneth
map of the fibre product, invertible by `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme`,
read through composition isomorphisms. -/
theorem isIso_kunnethMap_inverseImageBase [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b]
    [QuasiSeparated b] (hTor : AlgebraicGeometry.TorIndependent a b)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : AlgebraicGeometry.IsQCohAll K)
    (hM : AlgebraicGeometry.IsQCohAll M) :
    type_of% (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_ringChange
      (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (toInverseImageBase a) (toInverseImageBase b)
      (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom (toInverseImageBase_comp_fstProjection a b)
      (toInverseImageBase_comp_sndProjection a b) a.toLRSHom.toShHom (toInverseImageBase_comp a)
      b.toLRSHom.toShHom (toInverseImageBase_comp b) (pullback.fst a b ≫ a).toLRSHom.toShHom
      (toInverseImageBase_comp (pullback.fst a b ≫ a)) rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M
      (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme a b hTor K M hK hM)) :=
  Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_ringChange
      (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (toInverseImageBase a) (toInverseImageBase b)
      (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom (toInverseImageBase_comp_fstProjection a b)
      (toInverseImageBase_comp_sndProjection a b) a.toLRSHom.toShHom (toInverseImageBase_comp a)
      b.toLRSHom.toShHom (toInverseImageBase_comp b) (pullback.fst a b ≫ a).toLRSHom.toShHom
      (toInverseImageBase_comp (pullback.fst a b ≫ a)) rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M
      (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme a b hTor K M hK hM)

end Comparison

end Stacks.Cohomology.BoxKunneth

end
