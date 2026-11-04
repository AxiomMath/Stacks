module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Blowing up a scheme, base changed to the local ring at a point

Fix a scheme `Y` and a point `y` of `Y`. The canonical morphism `Y.fromSpecStalk y`,
`Spec 𝒪_{Y, y} ⟶ Y`, is flat, so blowing up commutes with base change along it
([Stacks, Tag 0805]): for a quasi-coherent ideal sheaf `M` on `Y` the square

```
blowUp (M.comap (Y.fromSpecStalk y)) ⟶ blowUp M
                 ↓                        ↓
          Spec 𝒪_{Y, y}            ⟶      Y
```

is cartesian. This module collects the consequences of that square which transport local
information at `y` back to `Y`, as the proof of [Stacks, Tag 0AHH] needs: the local statement
[Stacks, Tag 0AGT] concerns a two-dimensional regular local ring, and the lemmas below are what
carry its conclusions from `Spec 𝒪_{Y, y}` to `Y`.

The point is that `Y.fromSpecStalk y` is not merely flat but also a preimmersion, and both
properties are stable under base change; a flat preimmersion induces isomorphisms on local
rings, so the projection `q` of the square above is an isomorphism on every local ring. Colengths
of inverse-image ideal sheaves are therefore unchanged by `q`, and the whole fibre of
`blowUpToBase M` over `y` lies in the image of `q`, so nothing over `y` is missed.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_isPullback_blowUpToBase_comap_fromSpecStalk`:
  the cartesian square itself, [Stacks, Tag 0805] applied to `Y.fromSpecStalk y`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.flat_and_isPreimmersion_of_isPullback` and
  `Stacks.ResolutionOfSurfaces.CartierDescent.isIso_stalkMap_of_isPullback`: the projection of
  such a square is a flat preimmersion, hence an isomorphism on every local ring.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_comap_of_isIso_stalkMap`:
  a morphism which is an isomorphism on the local ring at a point preserves the colength of an
  ideal sheaf there.
* `Stacks.ResolutionOfSurfaces.CartierDescent.fibre_subset_range_of_isPullback`: the fibre of
  `blowUpToBase M` over `y` is contained in the image of the projection.
* `Stacks.ResolutionOfSurfaces.CartierDescent.comap_exceptionalIdeal_of_isPullback`: the
  exceptional ideal sheaf of the blowup over `Spec 𝒪_{Y, y}` is the inverse image of the
  exceptional ideal sheaf of the blowup of `Y`.

## Implementation notes

The square is stated in the argument order produced by
`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`, namely
`IsPullback (blowUpToBase (M.comap (Y.fromSpecStalk y))) q (Y.fromSpecStalk y) (blowUpToBase M)`;
so in `IsPullback p q f g` the leg `f` is the flat morphism `Y.fromSpecStalk y` and the leg being
base changed to `q` is that one. All the downstream lemmas take a square of exactly this shape as
a hypothesis, rather than the existential, so that a caller may `obtain` the square once and feed
the same `sq` to each of them.

`flat_and_isPreimmersion_of_isPullback` returns a conjunction rather than two instances because
the two properties of `q` are never available as instances: `q` is an arbitrary morphism carrying
the square as a hypothesis. A caller wanting the stalk isomorphism should use
`isIso_stalkMap_of_isPullback`, which does the `haveI` dance internally.

`length_stalk_quotient_comap_of_isIso_stalkMap` is stated for an arbitrary morphism and an
arbitrary hypothesis `IsIso (q.stalkMap z)`, with no reference to the blowup: that is all the
proof uses, and stating it this way lets it be applied at a point of the blowup over
`Spec 𝒪_{Y, y}` without rediscovering the square. The ideal-theoretic input is
`AlgebraicGeometry.IdealSheafData.stalk_comap`, which identifies the stalk of an inverse image
with the `Ideal.map` of the stalk along the map of local rings;
`Module.quotient_length_eq_of_ringEquiv` then transports the length of the quotient across the
ring isomorphism.

`comap_exceptionalIdeal_of_isPullback` cannot be stated for an abstract vertex `W`: both sides
are ideal sheaves on the source of `q`, and the right-hand side forces that source to be
`blowUp (M.comap (Y.fromSpecStalk y))`. Its proof is `Scheme.IdealSheafData.comap_comp` twice,
unfolding `AlgebraicGeometry.exceptionalIdeal M` to `M.comap (blowUpToBase M)`, and then the
commutativity `sq.w` of the square.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-! ### The cartesian square -/

/-- **Blowing up commutes with base change to the local ring at a point.** For a scheme `Y`, a
point `y` of `Y` and a quasi-coherent ideal sheaf `M` on `Y`, the blowup of `Spec 𝒪_{Y, y}` in
the inverse image of `M` sits in a cartesian square over the blowup of `Y` in `M`.

This is [Stacks, Tag 0805] applied to the flat morphism `Y.fromSpecStalk y`; it is the
flat-base-change input to [Stacks, Tag 0AHH]. -/
public theorem exists_isPullback_blowUpToBase_comap_fromSpecStalk {Y : Scheme.{u}} (y : Y)
    (M : Y.IdealSheafData) :
    ∃ q : AlgebraicGeometry.blowUp (M.comap (Y.fromSpecStalk y)) ⟶ AlgebraicGeometry.blowUp M,
      CategoryTheory.IsPullback
        (AlgebraicGeometry.blowUpToBase (M.comap (Y.fromSpecStalk y))) q
        (Y.fromSpecStalk y) (AlgebraicGeometry.blowUpToBase M) := by
  have : Flat (Y.fromSpecStalk y) := AlgebraicGeometry.flat_fromSpecStalk Y y
  exact AlgebraicGeometry.exists_isPullback_blowUpToBase_comap (Y.fromSpecStalk y) M

section Projection

variable {Y : Scheme.{u}} (y : Y) {W : Scheme.{u}} {M : Y.IdealSheafData}
  {q : W ⟶ AlgebraicGeometry.blowUp M} {p : W ⟶ Spec (Y.presheaf.stalk y)}

/-! ### The projection is a flat preimmersion -/

/-- **The projection of the square of
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_isPullback_blowUpToBase_comap_fromSpecStalk`
is a flat preimmersion.** Indeed `Y.fromSpecStalk y` is flat and a preimmersion, and both
properties are stable under base change. -/
public theorem flat_and_isPreimmersion_of_isPullback
    (sq : CategoryTheory.IsPullback p q (Y.fromSpecStalk y)
      (AlgebraicGeometry.blowUpToBase M)) :
    Flat q ∧ IsPreimmersion q :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
      (AlgebraicGeometry.flat_fromSpecStalk Y y),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance⟩

/-- **The projection of the square of
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_isPullback_blowUpToBase_comap_fromSpecStalk`
induces an isomorphism on every local ring.** It is a flat preimmersion by
`Stacks.ResolutionOfSurfaces.CartierDescent.flat_and_isPreimmersion_of_isPullback`, and a flat
preimmersion is an isomorphism on local rings. -/
public theorem isIso_stalkMap_of_isPullback
    (sq : CategoryTheory.IsPullback p q (Y.fromSpecStalk y)
      (AlgebraicGeometry.blowUpToBase M)) (z : W) :
    IsIso (q.stalkMap z) := by
  obtain ⟨hflat, hpre⟩ := flat_and_isPreimmersion_of_isPullback y sq
  exact AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion q z

/-! ### The fibre over the chosen point -/

/-- **The fibre of the blowup morphism over `y` is contained in the image of the projection.**
The closed point of `Spec 𝒪_{Y, y}` is sent to `y` by `Y.fromSpecStalk y`, so for every point of
`blowUp M` above `y` the cartesian square produces a point of `W` above it. -/
public theorem fibre_subset_range_of_isPullback
    (sq : CategoryTheory.IsPullback p q (Y.fromSpecStalk y)
      (AlgebraicGeometry.blowUpToBase M)) :
    (AlgebraicGeometry.blowUpToBase M).base ⁻¹' {y} ⊆ Set.range q.base := by
  intro z hz
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback sq
    (IsLocalRing.closedPoint (Y.presheaf.stalk y)) z
    (Scheme.fromSpecStalk_closedPoint.trans hz.symm)
  exact ⟨w, hw⟩

end Projection

/-! ### Colengths are preserved -/

/-- **A morphism which is an isomorphism on the local ring at a point preserves the colength of
an ideal sheaf there.** The stalk of the inverse image `K.comap q` at `z` is the image of the
stalk of `K` at `q z` under the map of local rings, and a ring isomorphism carries the quotient
by an ideal to the quotient by its image, preserving length. -/
public theorem length_stalk_quotient_comap_of_isIso_stalkMap {W X : Scheme.{u}} (q : W ⟶ X)
    (K : X.IdealSheafData) (z : W) (hz : IsIso (q.stalkMap z)) :
    Module.length (W.presheaf.stalk z)
        (W.presheaf.stalk z ⧸ AlgebraicGeometry.IdealSheafData.stalk (K.comap q) z) =
      Module.length (X.presheaf.stalk (q.base z))
        (X.presheaf.stalk (q.base z) ⧸ AlgebraicGeometry.IdealSheafData.stalk K (q.base z)) := by
  have := hz
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap]
  exact (Module.quotient_length_eq_of_ringEquiv
    (asIso (q.stalkMap z)).commRingCatIsoToRingEquiv _).symm

/-! ### The exceptional ideal sheaf -/

/-- **The exceptional ideal sheaf of the blowup over `Spec 𝒪_{Y, y}` is the inverse image of the
exceptional ideal sheaf of the blowup of `Y`.** Both are inverse images of `M` along the two
composites around the cartesian square, which agree. -/
public theorem comap_exceptionalIdeal_of_isPullback {Y : Scheme.{u}} (y : Y)
    {M : Y.IdealSheafData}
    (q : AlgebraicGeometry.blowUp (M.comap (Y.fromSpecStalk y)) ⟶ AlgebraicGeometry.blowUp M)
    (sq : CategoryTheory.IsPullback
      (AlgebraicGeometry.blowUpToBase (M.comap (Y.fromSpecStalk y))) q
      (Y.fromSpecStalk y) (AlgebraicGeometry.blowUpToBase M)) :
    (AlgebraicGeometry.exceptionalIdeal M).comap q =
      AlgebraicGeometry.exceptionalIdeal (M.comap (Y.fromSpecStalk y)) := by
  change (M.comap (AlgebraicGeometry.blowUpToBase M)).comap q =
    (M.comap (Y.fromSpecStalk y)).comap
      (AlgebraicGeometry.blowUpToBase (M.comap (Y.fromSpecStalk y)))
  simp only [← Scheme.IdealSheafData.comap_comp, sq.w]

end Stacks.ResolutionOfSurfaces.CartierDescent

end
