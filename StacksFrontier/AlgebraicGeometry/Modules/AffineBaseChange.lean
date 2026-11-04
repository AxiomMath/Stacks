module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence around the affine base-change square

Let
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
be a cartesian square of schemes and let `𝓕` be a quasi-coherent module on `X`. When `f` is
affine, the canonical base-change morphism `g^*f_*𝓕 ⟶ f'_*(g')^*𝓕` is expected to be an
isomorphism.

This file supplies the context that invertibility is asserted in, and does **not** prove
invertibility: direct image along an affine morphism as a functor on quasi-coherent modules,
affineness of the base-changed morphism, and quasi-coherence of the two modules the base-change
morphism compares. See the implementation notes for exactly what remains.

Quasi-coherence of the direct image along an affine morphism itself is not proved or restated
here. It is already available twice: as the theorem
`Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom`, which this file uses, and in
instance form, carrying the corresponding clause of Tag 02KG, as
`AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`.

## Main definitions

* `Stacks.Modules.pushforwardQcoh` is direct image along an affine morphism of schemes, as a
  functor between the categories of quasi-coherent modules. It is the counterpart for an affine
  morphism of arbitrary schemes of `Stacks.Descent.pushforwardQcoh`, which is stated for a
  morphism of affine schemes, and the dual of `Stacks.Modules.pullbackQcoh`.
* `Stacks.Modules.diagramBaseChange` abbreviates the base-change morphism of a base-change
  diagram, that is `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` instantiated
  at the diagram's square.

## Main results

* `Stacks.Modules.instIsAffineHomBaseChangeDiagramF'`: the morphism obtained from an affine
  morphism by base change is affine.
* `Stacks.Modules.instIsQuasicoherentPullbackPushforward` and
  `Stacks.Modules.instIsQuasicoherentPushforwardPulledBack`: the source and target of the
  base-change morphism of a base-change diagram with affine `f` are quasi-coherent.

## Implementation notes

The base-change morphism used here is the library's
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the inverse mate, with respect
to the adjunctions of `g'` and `g`, of the comparison of the two composite direct images around
the square. It is equally the mate of `Stacks.Modules.pullbackSquareIso` with respect to the
adjunctions `f^* ⊣ f_*` and `(f')^* ⊣ (f')_*` — that is
`Stacks.Modules.baseChangeNatTrans_eq_mateEquiv` of
`StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison`, proved from
`iterated_mateEquiv_conjugateEquiv` and `Stacks.Modules.conjugateEquiv_pullbackSquareIso_hom` —
and in that second description it is pinned down by
`Stacks.Modules.eq_baseChangeNatTrans_app` as the unique morphism with a prescribed adjoint
transpose. Nothing below depends on the second description.
`Stacks.Modules.diagramBaseChange` is an abbreviation for the library morphism instantiated at
the diagram, not a second construction of it.

Quasi-coherence of the two corners is what makes invertibility of the base-change morphism a
question that may be settled affine-locally, since a morphism of quasi-coherent modules on an
affine scheme is determined by the corresponding map of modules. The three bricks still absent
for that reduction are: local-to-global invertibility for a morphism of sheaves of modules on
a scheme, that is that `CategoryTheory.IsIso` of such a morphism may be checked on an affine
open cover (the repository has the analogous statement for quasi-coherence,
`AlgebraicGeometry.isQuasicoherent_of_restrict`, but none for invertibility); compatibility of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` with restriction of the square
to an affine open of `S'`; and the
computation, for a cartesian square of affine schemes, identifying the base-change morphism
with the canonical map `A' ⊗_A M ⟶ M ⊗_B (B ⊗_A A')` through the two halves of Tag 01I9,
`AlgebraicGeometry.pullbackTildeIso` and `AlgebraicGeometry.pushforwardTildeIso`.

Quasi-coherence of a direct image is obtained below from the explicit theorem rather than by
instance search, so that this file introduces no instance competing with the one in
`AlgebraicGeometry.AffinePushforward`, whose tree is imported for the base-change morphism
itself.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Modules

/-- Direct image along an affine morphism of schemes, as a functor between the full
subcategories of quasi-coherent modules. This is the counterpart for an affine morphism of
arbitrary schemes of `Stacks.Descent.pushforwardQcoh`, which is stated for a morphism of
affine schemes, and the dual of `Stacks.Modules.pullbackQcoh`. -/
def pushforwardQcoh {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f)
    fun M ↦ isQuasicoherent_pushforward_of_isAffineHom f M.obj M.property

/-- Forgetting quasi-coherence identifies `Stacks.Modules.pushforwardQcoh` with direct image of
modules. -/
lemma pushforwardQcoh_comp_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    pushforwardQcoh f ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f := rfl

/-- The morphism obtained from an affine morphism by base change along the square of a
base-change diagram is affine, affineness of morphisms being stable under base change. -/
@[ega "II 1.6.2"]
instance instIsAffineHomBaseChangeDiagramF' (d : BaseChangeDiagram.{u}) [IsAffineHom d.f] :
    IsAffineHom d.f' :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) d.isPullback ‹_›

/-- The source `g^*f_*𝓕` of the base-change morphism of a base-change diagram with affine `f`
is quasi-coherent: the direct image along the affine `f` is quasi-coherent by Tag 02KG, and
inverse image preserves quasi-coherence along an arbitrary morphism by Tag 01BG. -/
instance instIsQuasicoherentPullbackPushforward (d : BaseChangeDiagram.{u}) [IsAffineHom d.f] :
    ((Scheme.Modules.pullback d.g).obj
      ((Scheme.Modules.pushforward d.f).obj d.F)).IsQuasicoherent :=
  haveI := d.isQuasicoherent
  haveI := isQuasicoherent_pushforward_of_isAffineHom d.f d.F ‹_›
  inferInstance

/-- The target `f'_*(g')^*𝓕` of the base-change morphism of a base-change diagram with affine
`f` is quasi-coherent: the inverse image `𝓕' = (g')^*𝓕` is quasi-coherent by Tag 01BG, and
`f'` is affine because `f` is. -/
instance instIsQuasicoherentPushforwardPulledBack (d : BaseChangeDiagram.{u})
    [IsAffineHom d.f] :
    ((Scheme.Modules.pushforward d.f').obj d.pulledBack).IsQuasicoherent :=
  haveI := d.isQuasicoherent
  isQuasicoherent_pushforward_of_isAffineHom d.f' d.pulledBack inferInstance

/-- The base-change morphism `g^*f_*𝓕 ⟶ f'_*(g')^*𝓕` of a base-change diagram. This is the
library morphism `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` instantiated at
the diagram's commutative square, recorded as an abbreviation so that the morphism whose
invertibility is at stake in Tag 02KG has a name; it is not a further construction of a
base-change map. -/
abbrev diagramBaseChange (d : BaseChangeDiagram.{u}) :
    (Scheme.Modules.pullback d.g).obj ((Scheme.Modules.pushforward d.f).obj d.F) ⟶
      (Scheme.Modules.pushforward d.f').obj d.pulledBack :=
  (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans d.isPullback.w).app d.F

end Stacks.Modules

end
