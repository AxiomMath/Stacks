module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.Topology.Sheaves.Modules.Differentials

/-!
# The universal derivation of a morphism of schemes

Stacks Project, Tag 01UQ defines the sheaf of differentials `Ω_{X/S}` of a morphism of schemes
`f : X ⟶ S` to be the sheaf of differentials of `f` viewed as a morphism of ringed spaces,
*equipped with* its universal `S`-derivation `d_{X/S} : 𝒪_X ⟶ Ω_{X/S}`. The sheaf is
`Stacks.Smooth.cotangentSheaf`; this file supplies the derivation it is equipped with, stated
over the structural map `f⁻¹𝒪_S ⟶ 𝒪_X` of the morphism of *schemes*.

## Main definitions

* `Stacks.Smooth.cotangentDerivation f` is `d_{X/S}`, a relative derivation of `𝒪_X` over
  `f⁻¹𝒪_S` with values in `Ω_{X/S}`.

## Main results

* `Stacks.Smooth.cotangentDerivation_eq` holds by `rfl`, so the ringed-space API of
  `Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation` applies to it unchanged.
* `Stacks.Smooth.cotangentDerivation_isUniversal` is the universal property of `d_{X/S}`
  in this vocabulary: every relative derivation factors through it by a unique morphism of
  sheaves of `𝒪_X`-modules. It is the statement
  `AlgebraicGeometry.Scheme.Hom.existsUnique_hom_cotangentSheaf` of
  `StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison`, with the
  universal derivation named rather than spelled out at the ringed space.

## Implementation notes

The ringed-space universal derivation has the type
`Stacks.Sheaves.Differentials.SheafDerivation _ _ (inverseImageStructureMap (ringedSpaceHom f))`
for the ringed-space `inverseImageStructureMap`, while `Ω_{X/S}` is an object of `X.Modules`
and the derivation wanted of a morphism of schemes is one over
`AlgebraicGeometry.inverseImageStructureMap f`. Both derivation types unfold to
`M.val.Derivation' φ.hom`, and the two structural maps are the same morphism —
`AlgebraicGeometry.Scheme.Hom.inverseImageStructureMap_ringedSpaceHom` records that by `rfl` —
so the two spellings describe the same type and `cotangentDerivation` is the ringed-space
derivation with no transport.

The module is kept apart from `StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafScheme`
because the two `inverseImageStructureMap`s differ only in namespace: importing
`StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over` into that file makes the bare name
ambiguous in the modules that build on it, where it is used at the ringed-space one.

## References

* [Stacks Project, Tag 01UQ](https://stacks.math.columbia.edu/tag/01UQ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The universal `S`-derivation `d_{X/S} : 𝒪_X ⟶ Ω_{X/S}` that the sheaf of differentials of a
morphism of schemes `f : X ⟶ S` is equipped with: the universal derivation of the underlying
morphism of ringed spaces, read as a relative derivation over the structural map
`f⁻¹𝒪_S ⟶ 𝒪_X` of `f`. -/
@[stacks 01UQ "the universal S-derivation d_{X/S} that the sheaf of differentials \
`Stacks.Smooth.cotangentSheaf` of a morphism of schemes is equipped with"]
noncomputable def cotangentDerivation :
    SheafOfModules.SheafDerivation (inverseImageStructureMap f) (cotangentSheaf f) :=
  Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation (ringedSpaceHom f)

/-- `Stacks.Smooth.cotangentDerivation` is the universal derivation of the underlying morphism
of ringed spaces, on the nose: the two spellings of the derivation type agree, so every result
about the latter applies to the former. -/
theorem cotangentDerivation_eq :
    cotangentDerivation f =
      Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation (ringedSpaceHom f) :=
  rfl

/-- **Stacks Project, Tag 01UQ**, universal property of the derivation it equips `Ω_{X/S}`
with: every relative derivation of `𝒪_X` over `f⁻¹𝒪_S` factors through `d_{X/S}` by a unique
morphism of sheaves of `𝒪_X`-modules. -/
theorem cotangentDerivation_isUniversal (F : X.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap f) F) :
    ∃! α : cotangentSheaf f ⟶ F, (cotangentDerivation f).postcomp α.val = D :=
  Stacks.Sheaves.Differentials.universalDerivation_isUniversal _ _ _ F D

end Stacks.Smooth

end
