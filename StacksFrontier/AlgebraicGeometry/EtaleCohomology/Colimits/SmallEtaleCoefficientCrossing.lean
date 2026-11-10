module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetsToAbelianBaseChangeBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentation

/-!
# The coefficient crossing of the degree-zero hypothesis of Stacks 09YQ

The degree-zero hypothesis `H0` of `isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic`
(in the namespace `Stacks.EtaleCohomology.SmallEtaleLimitCohomology`) is about **abelian**
sheaves, `AddCommGrpCat.{u + 1}`, on Mathlib's small étale sites; what the library has in degree
zero, `Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object`, is about
sheaves of **sets**, `Type (u + 1)`. This file carries the inverse image across that change of
coefficients, and identifies the sections of the two inverse images.

The comparison itself is not new and is not re-stated here:
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare` and its invertibility
`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare` are public and stated for an
arbitrary continuous functor of sites and an arbitrary coefficient functor, and they instantiate
**directly** at `Stacks.EtaleCohomology.smallEtaleBaseChange f` for a morphism `f : Y ⟶ X` of
schemes, between `AlgebraicGeometry.Scheme.smallEtaleTopology X` and
`AlgebraicGeometry.Scheme.smallEtaleTopology Y`, with the coefficient functor
`CategoryTheory.forget AddCommGrpCat.{u + 1}`. The two inputs that are not plain typeclass
inference are `Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange`,
which is public and stated exactly for base change of small étale sites, and
`CategoryTheory.GrothendieckTopology.PreservesSheafification` for the forgetful functor; both are
found by inference at these sites. In particular nothing has to be made public and nothing has to
be re-proved. The `private` instantiations in the tree — `bigSitePullbackForget` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer` and
`pullbackForgetAt` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetsToAbelianBaseChangeBridge` —
are local abbreviations for readability in their own files, and not the only access to the
instantiation.

What this file adds is the two things that were missing: the comparison **named as an
isomorphism** at these sites, in the vocabulary
`Stacks.EtaleCohomology.etaleAbelianInverseImage` / `Stacks.EtaleCohomology.smallEtaleInverseImage`
that the colimit development uses, and the resulting identification **on sections**, which is the
form in which a statement about sections of a sheaf of sets over an étale object can consume it.

## Main definitions

* `Stacks.EtaleCohomology.etaleForgetInverseImageIso` — **the coefficient crossing**: composing
  with the forgetful functor of abelian groups commutes with étale inverse image, on Mathlib's
  small étale sites.
* `Stacks.EtaleCohomology.etaleForgetInverseImageSections` — the induced bijection on sections
  over an object of the small étale site of the source.

## Main results

* `Stacks.EtaleCohomology.etaleForgetInverseImageIso_hom` — the crossing is the comparison
  `Stacks.EtaleCohomology.coefficientPullbackTwoSquare` and nothing else.

## Implementation notes

**The direction of the comparison** is read off `CategoryTheory.TwoSquare`, which is
`T ⋙ R ⟶ L ⋙ B` for a square with sides `T`, `L`, `R`, `B`. For
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare` the top side is the change of coefficients
on the site of the target of `f`, the right side is the inverse image of sheaves of sets and the
left side is the inverse image of abelian sheaves, so the transformation goes from "forget the
group structure, then take the set-valued inverse image" to "take the abelian inverse image, then
forget the group structure". That is the direction of `etaleForgetInverseImageIso`.

**Why the isomorphism is not `asIso` of the comparison with the readable type ascribed directly.**
`Stacks.EtaleCohomology.smallEtaleInverseImage` is a `def`, not an `abbrev`. With the readable
type as the expected type, the `IsIso` instance problem that `CategoryTheory.asIso` raises is
posed with the two functors of the composite in that spelling, and
`isIso_coefficientPullbackTwoSquare` no longer matches it: the unfolding of
`smallEtaleInverseImage` that the match needs is not available at the transparency instance
search uses, and the result is `failed to synthesize instance IsIso …`. Elaborating the comparison
against `_ ≅ _` first and converting afterwards costs nothing.

**What the crossing does *not* give.** It carries the inverse image, hence the *sources*
of the legs of a colimit presentation and the *data* of a system. It does **not** carry the
universal property, and no declaration here claims otherwise. The clause that fails is the
factorisation clause and the quantifier that fails is the one over the target:
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation.existsUnique_desc`
quantifies over abelian sheaves `H` on the small étale site of the limit, while
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.SheafSystem.IsColimitPresentation`
— the predicate that
`Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object` consumes, and
consumes in full, through
`Stacks.EtaleCohomology.QcSeparatedColimit.objectSections_surjective_and_separated` — quantifies
over sheaves of **sets** `H` and asks for a map `G ⟶ H` there. Composition with the forgetful
functor has no left adjoint in this tree, so a map out of the underlying sheaf of sets of the
presenting sheaf is the transpose of nothing abelian; and a compatible family of maps of sheaves
of sets into the underlying sheaf of sets of an abelian `H` need not be additive, so the failure
is not repaired by restricting the quantifier to targets in the image of
`CategoryTheory.sheafCompose`.

What *is* true, and is the extra input such a transfer would need, is that for the index of the
dévissage of [Stacks, Tag 09YQ] — a nonempty directed preorder `I` with `UnivLE.{v, u + 1}` —
composition with the forgetful functor **does** preserve colimits of shape `I` at these sites:
every hypothesis of `CategoryTheory.preservesColimitsOfShape_sheafCompose` is satisfied by
`sheafCompose (smallEtaleTopology Y) (forget AddCommGrpCat.{u + 1})` there. Two things keep it from
closing the gap. First, the abelian universal property becomes an honest
`CategoryTheory.Limits.IsColimit` only after passing to the Karoubi envelope —
the diagram `i ↦ f_i^{-1}F_i` is not a functor, which is why the predicate exists at all — by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimit_systemKaroubiCocone`, and nothing
lifts `CategoryTheory.sheafCompose` to the Karoubi envelopes or transports colimit preservation
there. Second, there is no set-valued counterpart of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCompatibleFamily`, of `IsColimitPresentation`
or of `isColimitPresentation_of_isColimit` to receive the result.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]

/-- **Composing with the forgetful functor of abelian groups commutes with étale inverse image.**
For a morphism `f : Y ⟶ X` of schemes, the comparison

`(forget) ∘ f^{-1} ≅ f^{-1} ∘ (forget)`

of the two composites of an inverse image on Mathlib's small étale sites with the change of
coefficients from `AddCommGrpCat.{u + 1}` to `Type (u + 1)`: forgetting the group structure on the
site of `X` and then taking the inverse image of sheaves of sets agrees with taking the inverse
image of abelian sheaves and then forgetting the group structure on the site of `Y`.

This is `Stacks.EtaleCohomology.coefficientPullbackTwoSquare` at these sites, invertible by
`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`; both are public and general, and the
instantiation needs nothing beyond them. Taking `f` to be
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi c i`, the projection of a limit cone of
schemes to a level, gives the comparison that the degree-zero hypothesis of [Stacks, Tag 09YQ]
asks for.

Nothing about the morphism is assumed: `f` is an arbitrary morphism of schemes, and the comparison
is invertible because the forgetful functor preserves the left Kan extension along base change of
étale schemes — base change is representably flat, so the categories indexing the extension are
filtered — and the sheafification of the small étale topology. -/
public def etaleForgetInverseImageIso :
    sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u + 1}) ⋙
        smallEtaleInverseImage.{u, 0} f ≅
      etaleAbelianInverseImage.{u, u + 1} f ⋙
        sheafCompose (smallEtaleTopology Y) (forget AddCommGrpCat.{u + 1}) :=
  (asIso (coefficientPullbackTwoSquare (smallEtaleBaseChange f) (smallEtaleTopology X)
    (smallEtaleTopology Y) (forget AddCommGrpCat.{u + 1})) : _ ≅ _)

omit [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}] in
/-- **The coefficient crossing is the existing comparison and nothing else**: the forward direction
of `Stacks.EtaleCohomology.etaleForgetInverseImageIso` is the natural transformation underlying
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, so everything proved about that comparison
— that it is the mate of the identity comparison of direct images, and that its components are
the Kan-extension description `Stacks.EtaleCohomology.coefficientPullbackComparison` — applies to
it unchanged. -/
public theorem etaleForgetInverseImageIso_hom :
    (etaleForgetInverseImageIso f).hom =
      (coefficientPullbackTwoSquare (smallEtaleBaseChange f) (smallEtaleTopology X)
        (smallEtaleTopology Y) (forget AddCommGrpCat.{u + 1})) :=
  rfl

/-- **The sections of the two inverse images agree.** For an abelian sheaf `F` on Mathlib's small
étale site of `X` and an object `V` of the small étale site of `Y`, the sections over `V` of the
inverse image along `f` of the underlying sheaf of sets of `F` are the underlying set of the
sections over `V` of the inverse image of `F` as an abelian sheaf.

This is `Stacks.EtaleCohomology.etaleForgetInverseImageIso` evaluated at `F` and read on sections
over `V`. It is the form in which a statement about sections of a sheaf of sets over an étale
object — such as
`Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object` — can consume
the crossing. -/
public def etaleForgetInverseImageSections
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (V : Y.Etale) :
    ((smallEtaleInverseImage.{u, 0} f).obj
          ((sheafCompose (smallEtaleTopology X)
            (forget AddCommGrpCat.{u + 1})).obj F)).obj.obj (op V) ≃
      (forget AddCommGrpCat.{u + 1}).obj
        (((etaleAbelianInverseImage.{u, u + 1} f).obj F).obj.obj (op V)) :=
  (((sheafSections (smallEtaleTopology Y) (Type (u + 1))).obj (op V)).mapIso
    ((etaleForgetInverseImageIso f).app F)).toEquiv

end Stacks.EtaleCohomology

end
