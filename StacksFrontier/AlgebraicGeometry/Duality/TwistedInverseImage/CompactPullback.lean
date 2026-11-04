module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-!
# The twisted inverse image from a compact pullback

Let `f : X ⟶ Y` be a morphism of schemes and suppose derived direct image preserves
quasi-coherence of cohomology, so that it restricts to a functor
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. The Stacks proof of [Stacks, Tag 0A9E] obtains the twisted
inverse image `f^×` as the right adjoint of that restriction from Brown representability
([Stacks, Tag 0A8G]), and the hypothesis of Brown representability that is not about `D_QCoh`
alone is that `Rf_*` commutes with direct sums ([Stacks, Tag 08DZ]). The source deduces that from
derived pullback: `Lf^*` is left adjoint to `Rf_*` and carries a compact generator of
`D_QCoh(𝒪_Y)` to a compact object of `D_QCoh(𝒪_X)` ([Stacks, Tag 09UA]), and a right adjoint
whose left adjoint preserves the compactness of a generator commutes with direct sums.

This file carries out that deduction, so that Tag 08DZ no longer has to be proved separately. Of
the three inputs that
`isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactGenerator` asks for — Tags 08D5, 08DZ
and 09IS — the middle one is replaced here by the derived
pullback–pushforward adjunction together with compactness of the pullback of a generator, which
is how the source produces it.

## Main results

Both live in the namespace `Stacks.Duality.DerivedPushforward`.

* `preservesCoproducts_quasiCoherentDerivedPushforward_of_compactPullback` — [Stacks, Tag 08DZ]
  from a left adjoint preserving the compactness of a generator.
* `isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactPullback` — [Stacks, Tag 0A9E] with
  Tags 08D5, 09IS and the derived pullback–pushforward adjunction as its hypotheses, and Tag
  08DZ discharged.

## Implementation notes

The left adjoint is a hypothesis rather than `Lf^*` itself. Taking the adjunction as an argument
keeps the statement exactly as strong as the source's and makes the input explicit.

The statements of this file are at the locally small model of
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the only model at which
`D_QCoh(𝒪_X)` has the direct sums that Brown representability needs.

**The adjunction is now available at that model, and the hypothesis is dischargeable.**
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction` and its relatives were
  restated at a free
`[HasDerivedCategory]` binder, so for an arbitrary morphism `f` of schemes

  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⊣
    Stacks.Duality.derivedPushforward f`

elaborates with no instance binder written, the right-hand side being this development's own
`Rf_*`; the two spellings of pushforward agree by `rfl`. Its restriction to
`Stacks.Duality.quasiCoherentDerivedCategory` is
`Stacks.Duality.quasiCoherentDerivedAdjunction` of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`, whose one
mathematical input is that `Lf^*` preserves quasi-coherence of cohomology — the `Lf^*` analogue
of the `hpush` hypothesis in `Duality/QuasiCoherentPushforwardAdjoint.lean`. So the version of
the second statement below with `L` and `adj` replaced by that functor and that adjunction is
`isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactDerivedPullback` of that same file, and
the results here are kept at a general `L` only because the source states them that way.

Additivity of the left adjoint is not assumed: it follows from additivity of `Rf_*`, which is
`isTriangulated_quasiCoherentDerivedPushforward` read through
`CategoryTheory.Adjunction.left_adjoint_additive`. Compatibility of the left adjoint
with the shift is assumed, since it is a structure rather than a property.

No `@[stacks]` attribute is attached: Tags 08D5, 08DZ, 09IS and 0A9E are all still open, and the
hypotheses of the results below are exactly what is missing.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality.DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {L : Stacks.Duality.quasiCoherentDerivedCategory Y ⥤
    Stacks.Duality.quasiCoherentDerivedCategory X} [L.CommShift ℤ]

/-- **[Stacks, Tag 08DZ] from a compact pullback.** Suppose derived direct image preserves
quasi-coherence of cohomology, let `L` be a left adjoint of the restricted derived direct image
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` compatible with the shift, and let `E` be a compact weak
generator of `D_QCoh(𝒪_Y)` whose image `L E` is compact. Then `Rf_*` commutes with direct sums.

In the source `L` is derived pullback `Lf^*`, `E` is the compact generator of [Stacks, Tag 09IS]
and compactness of `L E` is [Stacks, Tag 09UA]. -/
theorem preservesCoproducts_quasiCoherentDerivedPushforward_of_compactPullback
    (adj : L ⊣ Stacks.Duality.quasiCoherentDerivedPushforward f hpush)
    (E : Stacks.Duality.quasiCoherentDerivedCategory Y) [IsCompactObject.{u} E]
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hLE : IsCompactObject.{u} (L.obj E)) :
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush) := by
  have : L.Additive := adj.left_adjoint_additive
  exact Pretriangulated.preservesCoproducts_of_isCompactObject_map adj E hE inferInstance hLE

/-- **The Stacks proof of [Stacks, Tag 0A9E], with [Stacks, Tag 08DZ] discharged.** Let
`f : X ⟶ Y` be a morphism of schemes. Suppose

* derived direct image preserves quasi-coherence of cohomology ([Stacks, Tag 08D5], the argument
  `hpush`);
* the restricted derived direct image has a left adjoint `L` compatible with the shift — derived
  pullback `Lf^*`, by [Stacks, Tag 079W];
* `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_Y)` each have a compact weak generator ([Stacks, Tag 09IS]);
* `L` carries the generator of `D_QCoh(𝒪_Y)` to a compact object ([Stacks, Tag 09UA]).

Then the restricted derived direct image has a right adjoint — the twisted inverse image `f^×`.

Compared with `isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactGenerator` this
replaces the hypothesis that `Rf_*` commutes with direct sums ([Stacks, Tag 08DZ]) by the
adjunction and the compactness of the pullback from which the source derives it. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactPullback
    (adj : L ⊣ Stacks.Duality.quasiCoherentDerivedPushforward f hpush)
    (sourceGenerator : Stacks.Duality.quasiCoherentDerivedCategory X)
    [IsCompactObject.{u} sourceGenerator]
    (hsourceGenerator : (ObjectProperty.singleton sourceGenerator).IsWeakTriangulatedGenerator)
    (targetGenerator : Stacks.Duality.quasiCoherentDerivedCategory Y)
    [IsCompactObject.{u} targetGenerator]
    (htargetGenerator : (ObjectProperty.singleton targetGenerator).IsWeakTriangulatedGenerator)
    (hpullback : IsCompactObject.{u} (L.obj targetGenerator)) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  have := preservesCoproducts_quasiCoherentDerivedPushforward_of_compactPullback f hpush adj
    targetGenerator htargetGenerator hpullback
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactGenerator f hpush sourceGenerator
    hsourceGenerator

end Stacks.Duality.DerivedPushforward

end
