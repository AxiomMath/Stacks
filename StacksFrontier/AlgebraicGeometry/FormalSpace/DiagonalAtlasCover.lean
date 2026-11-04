module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsFromAlgebraicSpace
import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The atlas cover of a relative product over a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S` with an atlas `Xᵢ ⟶ X` as in Definition 0AIM. The proof of **Stacks 0AIP** — the
diagonal of `X` is representable — covers the relative product `U ×_X V` of two scheme-valued
points of `X` by the sheaves `(U ×_X Xᵢ) ×_{Xᵢ} (V ×_X Xᵢ)` and argues that each of them is a
scheme. This file proves the weaker assertion which is available in this library
unconditionally: each of them is an *algebraic space* over `S`.

Nothing here proves Stacks 0AIP, and no declaration below carries that tag; see the
implementation notes for what is missing.

## Main results

* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_sheafifiedYoneda_obj`: the sheaf
  represented by an object of the site is an algebraic space over `S` in the value universe
  `Type (u + 1)` in which a formal algebraic space lives.
* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_pullback_snd_pullback_snd`: one step of
  the proof of **Stacks 0AIP**. For `Xᵢ ⟶ X` a morphism from an affine formal algebraic space
  which is representable by algebraic spaces, and `A ⟶ X`, `C ⟶ X` two morphisms whose sources
  are algebraic spaces over `S`, the sheaf `(A ×_X Xᵢ) ×_{Xᵢ} (C ×_X Xᵢ)` is an algebraic space
  over `S`.

## Implementation notes

The source's step is stronger: `(U ×_X Xᵢ) ×_{Xᵢ} (V ×_X Xᵢ)` is a *scheme*, by Stacks 0AIG
applied to `Xᵢ ⟶ X` (étale, hence locally quasi-finite, hence representable by schemes, so that
`U ×_X Xᵢ` is a scheme) followed by Stacks 0AI8 for the diagonal of `Xᵢ`. Neither step is
available here as stated. This library's Stacks 0AIG,
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isAffineFormalAlgebraicSpace`, asks
its affine formal algebraic space to be the sheafified universe lift of a sheaf of `Type u`,
whereas an atlas member of `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` is a sheaf of
`Type (u + 1)`; and this library's Stacks 0AI8,
`AlgebraicGeometry.FormalSpace.diagonal_isClosedImmersion`, concludes only about base changes
along *represented* sheaves, whereas `U ×_X Xᵢ` is here only an algebraic space.

What replaces them is Stacks 03XY twice, around the unconditional affine case of Stacks 0AIQ:
`A ×_X Xᵢ` is an algebraic space because `Xᵢ ⟶ X` is representable by algebraic spaces, the
projection `A ×_X Xᵢ ⟶ Xᵢ` is representable by algebraic spaces by Stacks 0AIQ for an affine
formal algebraic space target, and one more application of Stacks 03XY gives the fibre product
over `Xᵢ`. The conclusion is correspondingly weaker — an algebraic space, not a scheme — and
that is all this step needs to be for the route sketched below.

This does **not** suffice for Stacks 0AIP, and the gap is not in this step. The source assembles
the cover into an algebraic space by the bootstrap theorem Stacks 04S6 and then descends to a
scheme by Stacks 03XX. The bootstrap is not the obstruction: Stacks 0BGQ and 0BGR
(`AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas` and
`…_of_relativelyRepresentable_surjective_etale`) are unconditional in this library and accept an
étale atlas with no hypothesis on the diagonal, and the diagonal of `A ×_X C` is in any case
representable for free, that sheaf being a subsheaf of the representable `A ×_S C` because
`diag X` is a split monomorphism.

The obstruction is the *size of the atlas*. Every algebraic-space criterion in this library —
Stacks 0BGQ and 0BGR above, Stacks 02WQ
(`AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit`) and Stacks 04SK
(`AlgebraicGeometry.isAlgebraicSpace_of_isCovering`) — consumes a *single* atlas object or
algebraic space, so the cover has to be replaced by its coproduct, and a coproduct of algebraic
spaces is available only under a bound on the index type by the cofinality of the site's size
cutoff (`AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit`, which asks `#I <
B.cutoff.ord.cof` for `I : Type u`, or
`AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le`). The atlas of
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` is indexed by an arbitrary type of
`Type (u + 1)` and carries no such bound. Replacing it, for a fixed pair of scheme-valued
points, by a jointly surjective subfamily indexed below the cutoff is the missing input.

The value universe is *not* a further obstruction, contrary to what the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal` suggest. A fibre product of two
sheaves with `u`-small sections has `u`-small sections, and a sheafified representable has
`u`-small sections, so `A ×_X C` descends to `Type u`, where Stacks 03XX
(`AlgebraicGeometry.Space.isRepresentable_of_locallyQuasiFinite_separated`) lives; likewise an
affine formal algebraic space has `u`-small sections by its set-theoretic condition, which is
what the hypothesis of Stacks 0AIG asks for. Both smallness facts are already proved in this
library, as `small_sheaf_pullback`, `small_sheafifiedYoneda` and `small_of_setTheoreticCondition`
of `StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/FiniteTypeClassification.lean`, but all
three are `private` there and so are not usable from here without promoting them.

## References

* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIQ](https://stacks.math.columbia.edu/tag/0AIQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf represented by an object of the big fppf site of `S` is an algebraic space over
`S` in the value universe `Type (u + 1)` in which a formal algebraic space lives. The big fppf
site is subcanonical, so the sheafified Yoneda presheaf of an object agrees with its
universe-lifted Yoneda presheaf. -/
theorem isAlgebraicSpaceULift_sheafifiedYoneda_obj (a : BigFppfOver B S hS) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a).obj := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let e := Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso (e.app a)).symm
    (Space.isAlgebraicSpaceULift_uliftYoneda B S hS a)

/-- One step of the proof of **Stacks 0AIP**. Let `fi : Xᵢ ⟶ X` be a morphism of fppf sheaves
on the big fppf site of `S` which is representable by algebraic spaces and whose source is an
affine formal algebraic space, and let `α : A ⟶ X` and `γ : C ⟶ X` be two morphisms whose
sources are algebraic spaces over `S`. Then the fibre product `(A ×_X Xᵢ) ×_{Xᵢ} (C ×_X Xᵢ)`
is an algebraic space over `S`.

Taking `A` and `C` to be sheaves represented by objects of the site and `fi` to be a member of
an atlas as in Definition 0AIM, this is the assertion that the cover of `A ×_X C` used in the
proof of Stacks 0AIP has algebraic spaces for its members. The source gets schemes there; see
the implementation notes of this file for why that is not available here, and for what else
Stacks 0AIP needs beyond this step. -/
theorem isAlgebraicSpaceULift_pullback_snd_pullback_snd
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hXi : IsAffineFormalAlgebraicSpace B S hS Xi)
    (hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    {A C : FppfSheaf B S hS} (α : A ⟶ X) (γ : C ⟶ X)
    (hA : Space.IsAlgebraicSpaceULift.{u + 1} B S hS A.obj)
    (hC : Space.IsAlgebraicSpaceULift.{u + 1} B S hS C.obj) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd α.hom fi.hom) (pullback.snd γ.hom fi.hom)) := by
  have hAi : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback α.hom fi.hom) :=
    Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS fi.hom α.hom hfi hA
  have hCi : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback γ.hom fi.hom) :=
    Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS fi.hom γ.hom hfi hC
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.snd γ.hom fi.hom) :=
    isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift_of_isAffineFormal B S hS
      (X := ⟨pullback γ.hom fi.hom, hCi.isSheaf⟩)
      (ObjectProperty.homMk (pullback.snd γ.hom fi.hom)) hCi hXi
  exact Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS
    (pullback.snd γ.hom fi.hom) (pullback.snd α.hom fi.hom) hrep hAi

end AlgebraicGeometry.FormalSpace

end
