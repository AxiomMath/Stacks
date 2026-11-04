module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableCancellation
import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Maps from an algebraic space to a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S` with `X` an algebraic space over `S` and `Y` a formal
algebraic space over `S`. **Stacks 0AIQ** says that `f` is representable by algebraic spaces.

The only thing the formal algebraic space hypothesis on the target is used for is the
representability of its absolute diagonal, **Stacks 0AIP**, which this library carries for an
*affine* formal algebraic space only (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal`). That representability is
therefore the hypothesis `h0AIP` below, in the shape
`AlgebraicGeometry.FormalSpace.HasRepresentableRelativeProducts` in which the rest of this
development already records it, and nothing else about `Y` is assumed.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift`:
  **Stacks 0AIQ**, with the representability assertion of **Stacks 0AIP** for the target as a
  hypothesis.
* `…isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift_of_isAffineFormal`:
  **Stacks 0AIQ** unconditionally when the target is an affine formal algebraic space, which is
  the case in which this library has Stacks 0AIP.
* `…isRepresentableByAlgebraicSpacesULift_of_hasRepresentableRelativeProducts`: the one input,
  that a scheme-valued point of a sheaf with representable relative products is representable
  by algebraic spaces.

## Implementation notes

The source argues through a chart: a scheme-valued point `Z ⟶ Y` is pulled back along a
surjective étale scheme atlas `U ⟶ X`, the resulting `U ×_Y Z` is a scheme by Stacks 0AIP, the
map `U ×_Y Z ⟶ X ×_Y Z` is representable surjective étale by Spaces, Lemma 02WL, and Bootstrap,
Theorem 04S6 assembles `X ×_Y Z` into an algebraic space. The bootstrap theorem is available
here only in the two forms of
`StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FinalBootstrap`, both of which
carry condition (3) of Stacks 04S6 as a hypothesis, so that route would make the statement
conditional on a second missing input.

It is not needed. Stacks 0AIP says exactly that every morphism to `Y` out of a sheaf represented
by an object of the site is relatively representable, so a scheme-valued point of `Y` is
representable by algebraic spaces — every one of its represented base changes is a represented
sheaf, hence an algebraic space by Stacks 025Z. The fibre product of an algebraic space with the
source of a morphism representable by algebraic spaces is an algebraic space by **Stacks 03XY**,
which is `AlgebraicGeometry.Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift`, and
that fibre product is the base change of `f` along the point. No chart, no bootstrap and no
descent of `U ×_Y Z` to a scheme appear.

Stacks 0AIP is stated in this library for the sheafified Yoneda embedding, and concludes
representability by objects of the site, whereas representability by algebraic spaces is tested
against universe-lifted Yoneda presheaves of the site. The two are bridged by
`FormalSpace.isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable` together
with `CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`, the chosen big fppf topology being
subcanonical; the comparison isomorphism at the object of the site is composed away as a base
change along an isomorphism.

The algebraic space condition on the source is
`AlgebraicGeometry.Space.IsAlgebraicSpaceULift` in the value universe `Type (u + 1)` in which a
formal algebraic space lives. Nothing is weakened by that: the condition on a universe lift of a
presheaf of `Type u` is the condition on the presheaf itself, by
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff`.

## References

* [Stacks Project, Tag 02WL](https://stacks.math.columbia.edu/tag/02WL)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIQ](https://stacks.math.columbia.edu/tag/0AIQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme-valued point of an fppf sheaf with representable relative products is
representable by algebraic spaces.

Representable relative products say that the point is relatively representable once it is
transported into the sheaf category along the comparison isomorphism between the sheafified
Yoneda embedding and the Yoneda embedding into sheaves; the underlying morphism of presheaves
is then representable by algebraic spaces, and it differs from the given point by composition
with an isomorphism, which is a base change. -/
theorem isRepresentableByAlgebraicSpacesULift_of_hasRepresentableRelativeProducts
    {Y : FppfSheaf B S hS} (h0AIP : HasRepresentableRelativeProducts B S hS Y)
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS ξ := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let e := Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)
  let ξ₀ : (GrothendieckTopology.uliftYoneda.{u + 1} (BigFppfOver.topology B S hS)).obj U ⟶ Y :=
    ObjectProperty.homMk ξ
  have h := isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable B S hS
    ((e.app U).hom ≫ ξ₀) (h0AIP ((e.app U).hom ≫ ξ₀))
  let i := (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso (e.app U)
  exact Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS i.inv ξ (i.hom ≫ ξ)
    (𝟙 Y.obj) (IsPullback.of_horiz_isIso
      ⟨(i.inv_hom_id_assoc ξ).trans (Category.comp_id ξ).symm⟩) h

/-- **Stacks 0AIQ**, with the representability assertion of **Stacks 0AIP** for the target as a
hypothesis. A morphism of fppf sheaves on the big fppf site of `S` whose source is an algebraic
space over `S` and whose target has representable relative products is representable by
algebraic spaces.

The base change of the morphism along a scheme-valued point of the target is the fibre product
of the source with the point, and the point is representable by algebraic spaces, so Stacks
03XY applies. -/
theorem isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj)
    (h0AIP : HasRepresentableRelativeProducts B S hS Y) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := fun U ξ =>
  Space.isAlgebraicSpaceULift_of_iso B S hS (pullbackSymmetry f.hom ξ)
    (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS ξ f.hom
      (isRepresentableByAlgebraicSpacesULift_of_hasRepresentableRelativeProducts B S hS h0AIP
        U ξ) hX)

/-- **Stacks 0AIQ** when the target is an affine formal algebraic space. A morphism of fppf
sheaves from an algebraic space over `S` to an affine formal algebraic space over `S` is
representable by algebraic spaces, the relative products of the target being representable by
**Stacks 0AI8**. -/
@[stacks 0AIQ "for a target which is an affine formal algebraic space, that being the case in \
which this library has Stacks 0AIP"]
theorem isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift_of_isAffineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift B S hS f hX
    (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hY)

end AlgebraicGeometry.FormalSpace

end
