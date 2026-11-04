module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# The centre of the blowup at a point, read on the local ring

Fix a scheme `Y` and a closed point `y` of `Y`. Blowing up `Y` at the reduced closed subscheme
supported at `y` means blowing up the ideal sheaf
`Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩`. The local statement of [Stacks, Tag 0AGT] that
the globalisation step of [Stacks, Tag 0AHH] consumes is instead about the blowup of
`Spec 𝒪_{Y, y}` at its closed point, and the library states that blowup — in
`AlgebraicGeometry.isRegular_blowUp_maximalIdeal` — as the blowup of
`Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
(IsLocalRing.maximalIdeal A))` for a local ring `A`.

This file is the one line of dictionary between the two: the inverse image of the reduced closed
point along `Y.fromSpecStalk y : Spec 𝒪_{Y, y} ⟶ Y` is exactly that centre, for
`A := 𝒪_{Y, y}`. Composed with the cartesian square of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/EmbeddedResolution/CartierDescent/StalkBaseChange.lean`, this is what lets the local theorem be applied to the
stalk and its conclusions carried back to `Y`.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.comap_vanishingIdeal_fromSpecStalk`: the inverse
  image of the ideal sheaf of a reduced closed point along the canonical morphism from the
  spectrum of its local ring is the ideal sheaf cut out by the maximal ideal of that local ring.
* `Stacks.ResolutionOfSurfaces.CartierDescent.comap_vanishingIdeal_fromSpecStalk_of`: the same
  statement with the local ring spelled `CommRingCat.of ↥(Y.presheaf.stalk y)`, which is the
  shape produced by instantiating a theorem about a bare ring `A : Type u` — such as
  `AlgebraicGeometry.isRegular_blowUp_maximalIdeal` — at the stalk.

## Implementation notes

The proof is a composition of two results already in the tree:
`AlgebraicGeometry.vanishingIdeal_singleton_comap_fromSpecStalk` rewrites the inverse image as
the kernel ideal sheaf of `Spec.map (Y.residue y)`, and `AlgebraicGeometry.Scheme.ker_SpecMap`
computes the kernel ideal sheaf of a morphism of affine schemes as `ofIdealTop` of the transport
of the ring-theoretic kernel along `Scheme.ΓSpecIso`. What remains is
`RingHom.ker (Y.residue y).hom = IsLocalRing.maximalIdeal (Y.presheaf.stalk y)`, which is
`IsLocalRing.ker_residue` — `AlgebraicGeometry.Scheme.residue` is by definition
`CommRingCat.ofHom (IsLocalRing.residue _)`, so no bridging is needed. Note that the stalk of an
ideal sheaf does not enter: `AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton`
identifies the stalk at `y`, whereas what is wanted here is the ideal of the inverse image on the
affine open `⊤` of `Spec 𝒪_{Y, y}`, and the kernel route reaches that directly.

`comap_vanishingIdeal_fromSpecStalk_of` holds by `CommRingCat.of_carrier`, which is a `rfl`
lemma, so the second statement is the first one up to definitional unfolding; it is recorded
separately only because the elaborated right-hand side differs syntactically and `rw` therefore
distinguishes them.

The companion fact that the support of `Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩` is `{y}`
is not restated here: it is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal` at the closed set `⟨{y}, hy⟩`
(or `Stacks.AffineClosedUnion.support_vanishingIdeal` for the `TopologicalSpace.Closeds`-level
form), neither of which needs the closed set to be a point.

## References

* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-- **The inverse image of a reduced closed point in its own local ring is the closed point.**
For a closed point `y` of a scheme `Y`, the inverse image along `Y.fromSpecStalk y` of the ideal
sheaf of the reduced closed subscheme supported at `y` is the ideal sheaf on `Spec 𝒪_{Y, y}` cut
out by the maximal ideal of `𝒪_{Y, y}`; that is, the centre of the blowup of `Spec 𝒪_{Y, y}` at
its closed point. -/
public theorem comap_vanishingIdeal_fromSpecStalk {Y : Scheme.{u}} (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap (Y.fromSpecStalk y) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))) := by
  rw [vanishingIdeal_singleton_comap_fromSpecStalk y hy, Scheme.ker_SpecMap]
  exact congrArg (fun I ↦ Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom I))
    (IsLocalRing.ker_residue (R := ↥(Y.presheaf.stalk y)))

/-- **The inverse image of a reduced closed point in its own local ring is the closed point**,
stated with the local ring spelled as `CommRingCat.of ↥(Y.presheaf.stalk y)`. This is the form
matching a theorem about a bare local ring `A : Type u`, such as
`AlgebraicGeometry.isRegular_blowUp_maximalIdeal`, instantiated at `A := ↥(Y.presheaf.stalk y)`. -/
public theorem comap_vanishingIdeal_fromSpecStalk_of {Y : Scheme.{u}} (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap (Y.fromSpecStalk y) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of ↥(Y.presheaf.stalk y))).inv.hom
          (IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y))) :=
  comap_vanishingIdeal_fromSpecStalk y hy

end Stacks.ResolutionOfSurfaces.CartierDescent

end
