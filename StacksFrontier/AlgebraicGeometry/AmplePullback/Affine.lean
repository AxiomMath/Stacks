module

public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness pulled back along an affine morphism

An invertible sheaf on a scheme is ample when the scheme is quasi-compact and every point lies in
an affine nonvanishing locus of a global section of some positive tensor power. Both conditions
survive pullback along a morphism `f : X ⟶ Y` that is **affine**, provided `X` itself is
quasi-compact: the witnessing section is pulled back, its nonvanishing locus is the preimage of
the original one, and the preimage of an affine open along an affine morphism is affine.

Specialized to a closed immersion this is [Stacks, Tag 01PU]: the restriction of an ample
invertible sheaf to a closed subscheme is ample. The source's proof is the same two observations —
a closed subset of a quasi-compact space is quasi-compact, and a closed subscheme of an affine
scheme is affine — and the affine-morphism statement is exactly the generality in which they are
available.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isAffineHom`: the pullback of an ample
  invertible sheaf along an affine morphism with quasi-compact source is ample.
* `AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isClosedImmersion`: **[Stacks, Tag 01PU]**,
  the restriction of an ample invertible sheaf to a closed subscheme is ample.

## Implementation notes

This strengthens `AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isIso` of
`StacksFrontier/AlgebraicGeometry/AmplePullback/Basic.lean`, whose proof it follows line for
line, in exactly two places: quasi-compactness of the source is a hypothesis instead of being
transported along a homeomorphism, and affineness of the preimage of the witnessing locus comes
from `AlgebraicGeometry.IsAffineOpen.preimage` instead of from
`AlgebraicGeometry.IsAffineOpen.preimage_of_isIso`. Everything else — the identification of the
pullback of a tensor power with the tensor power of the pullback
(`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`), the invariance of a nonvanishing
locus under an isomorphism of sheaves, and [Stacks, Tag 0H78] for the nonvanishing locus of a
pulled-back section — is reused unchanged.

An affine morphism is not the same generality as the immersion of [Stacks, Tag 0B3E]: a closed
immersion is affine and an open immersion is not, while conversely an affine morphism need not be
an immersion. Neither statement implies the other, and this is the one a closed subscheme needs.

For the closed-immersion corollary quasi-compactness of the source is automatic: a closed
immersion is quasi-compact, so `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`
applies to the quasi-compact target supplied by ampleness.

The invertibility of the pullback is an instance binder, as in `Basic.lean`: it is
`Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback` of [Stacks, Tag 0B8L] and is
not found by instance search. This is harmless, `AlgebraicGeometry.SheafOfModules.IsInvertible`
being `Prop`-valued.

## References

* [Stacks Project, Tag 01PU](https://stacks.math.columbia.edu/tag/01PU)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L)]

/-- The pullback of an ample invertible sheaf of modules along an affine morphism whose source is
quasi-compact is ample. Each witnessing section is pulled back and carried across
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`, which leaves its nonvanishing locus the
preimage of the original one, and the preimage of an affine open along an affine morphism is
affine. -/
public theorem isAmple_pullback_of_isAffineHom [IsAffineHom f] [CompactSpace X]
    (h : IsAmple Y L) : IsAmple X ((Scheme.Modules.pullback f).obj L) := by
  refine ⟨‹CompactSpace X›, fun x => ?_⟩
  obtain ⟨n, hn, s, hxs, haff⟩ := h.exists_affine_nonvanishingLocus (f.base x)
  have key : Stacks.SheafOfModules.nonvanishingOpen
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          ((Scheme.Modules.pullback f).obj L) (n : ℤ))
        (SheafOfModules.sectionsMap (pullbackTensorPowerIso f L n).hom
          (Stacks.SheafOfModules.modulePullbackSection f.toLRSHom _ s)) =
      f ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
        (tensorPower Y.toRingedSpace.presheaf
          (structureSheafRing Y.toRingedSpace).property L (n : ℤ)) s :=
    (TopologicalSpace.Opens.ext (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap
      X.toRingedSpace (pullbackTensorPowerIso f L n) _)).trans
        (Stacks.SheafOfModules.preimage_nonvanishingOpen f _ s).symm
  exact ⟨n, hn, _, key.ge hxs, key ▸ haff.preimage f⟩

/-- **Stacks Project, Tag 01PU.** The restriction of an ample invertible sheaf of modules to a
closed subscheme is ample. The closed immersion is affine, and its source is quasi-compact
because its target is. -/
@[stacks 01PU,
  ega "II 4.5.14" "necessity",
  ega "II 4.5.13" "necessity",
  ega "III 2.6.2.3" "special case",
  ega "III 5.2.5" "Ampleness of L'_0 = L/JL"]
public theorem isAmple_pullback_of_isClosedImmersion [IsClosedImmersion f] (h : IsAmple Y L) :
    IsAmple X ((Scheme.Modules.pullback f).obj L) :=
  have : CompactSpace Y := h.compactSpace
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  isAmple_pullback_of_isAffineHom f L h

end AlgebraicGeometry.Scheme.Modules

end
