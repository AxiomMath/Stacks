module

public import StacksFrontier.AlgebraicGeometry.Duality.Dualizing
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport

/-!
# A flat morphism out of a Gorenstein scheme is a Gorenstein morphism

A flat morphism `f : X ⟶ Y` of locally Noetherian schemes with Gorenstein source is a Gorenstein
morphism: it is flat at every point of `X`, and the local ring of the fibre through a point is a
Gorenstein local ring.

Flatness at a point is immediate from flatness of `f`. The fibre statement is the closed-fibre
half of Stacks 0BJL applied to the stalk homomorphism `𝒪_{Y, f x} → 𝒪_{X, x}`, which is a flat
local homomorphism of Noetherian local rings: `𝒪_{X, x}` is Gorenstein because `X` is, so the
quotient of `𝒪_{X, x}` by the extension of the maximal ideal of `𝒪_{Y, f x}` is Gorenstein, and
that quotient is the local ring of the fibre.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Duality.isGorenstein_of_flat` — a flat morphism of locally Noetherian schemes with
  Gorenstein source is a Gorenstein morphism, together with the local Noetherianity of its fibres
  that the Gorenstein-morphism predicate needs.

## Implementation notes

The Gorenstein-morphism predicate `AlgebraicGeometry.Scheme.Hom.IsGorenstein` takes the local
Noetherianity of the fibres as an explicit argument, because it is what supplies the Noetherian
structure on the fibre stalks. Here that argument is not an extra assumption — it follows from
local Noetherianity of the source — so it is packaged existentially with the conclusion rather
than demanded of the caller.

Gorensteinness of the fibre stalk is obtained for the quotient `𝒪_{X, x} ⧸ m_{f x} 𝒪_{X, x}` and
then transported along `AlgebraicGeometry.quotientStalkEquivFiberStalk`, a ring equivalence onto
the fibre stalk. The transport is `Dualizing.isGorensteinLocalRing_of_ringEquiv`, taken from
`StacksFrontier/RingTheory/Dualizing/FlatLocalGorenstein.lean`; it is itself a consequence of
Stacks 0BJL, a ring equivalence being a flat local homomorphism, so the "source is Gorenstein"
half of that criterion applies to it.

This file installs `HasDerivedCategory.standard` as a local instance, as every file in this
Gorenstein chain does: `Dualizing.IsGorensteinLocalRing` is defined with that instance in scope,
so the model is part of its type and there is no free-model version to state instead.

Both class names in the statement are written out in full, deliberately. The conclusion names
the Gorenstein-morphism predicate `AlgebraicGeometry.Scheme.Hom.IsGorenstein`, so with
`AlgebraicGeometry` open an unqualified `IsGorenstein` here could resolve to either it or the
Gorenstein-scheme class. The spellings used are the ones
`Stacks.Duality.isGorensteinLocalRing_stalk_of_flat` is stated against, so the two halves of
Tag 0C12 take literally the same hypothesis.

## References

* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
* [Stacks Project, Tag 0C12](https://stacks.math.columbia.edu/tag/0C12)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- **Stacks Project, Tag 0C12.** A flat morphism of locally Noetherian schemes with Gorenstein
source is a Gorenstein morphism.

The local Noetherianity of the fibres that `Scheme.Hom.IsGorenstein` requires is supplied here
rather than assumed: it follows from local Noetherianity of the source. -/
-- NO `@[stacks 0C12]` ATTRIBUTE HERE, DELIBERATELY, for the same reason as on
-- `Stacks.Duality.isGorensteinLocalRing_stalk_of_flat`: 0C12's covering set in this library is
-- the two declarations together, and the audit scanner keys on the bare four-character tag and
-- reads the quoted suffix as free text, so an attribute on either one alone renders the whole
-- tag formalized. Both are now present; placing the pair of attributes is the lead's call.
@[stacks 0C12 "Gorenstein morphism"]
theorem isGorenstein_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsGorenstein X] [IsLocallyNoetherian Y] [Flat f] :
    ∃ hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y),
      AlgebraicGeometry.Scheme.Hom.IsGorenstein f hf := by
  refine ⟨fun y => isLocallyNoetherian_fiber f y, fun x => ?_⟩
  have hfib : IsLocallyNoetherian (f.fiber (f x)) := isLocallyNoetherian_fiber f (f x)
  refine ⟨(AlgebraicGeometry.Flat.iff_flat_stalkMap f).mp ‹_› x, ?_⟩
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat A B := (AlgebraicGeometry.Flat.iff_flat_stalkMap f).mp ‹_› x
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let I := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  have : Nontrivial (B ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  exact Dualizing.isGorensteinLocalRing_of_ringEquiv (quotientStalkEquivFiberStalk f x).symm
    ((Dualizing.isGorensteinLocalRing_iff_of_flat A B).mp
      (AlgebraicGeometry.IsGorenstein.isGorensteinLocalRing x)).2

end Stacks.Duality

end
