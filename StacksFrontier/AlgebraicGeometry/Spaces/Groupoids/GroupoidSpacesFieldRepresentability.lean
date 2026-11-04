module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroFieldOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSpacesDerealizationProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules

/-!
# The object and arrow spaces of a groupoid over a field are representable

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealization` turns a groupoid in algebraic spaces
into a groupoid scheme, asking only that its object and arrow spaces be representable. This file
supplies both representabilities for a groupoid whose object space is the presheaf of an object
of the site with field-valued spectrum — the situation of **Stacks 06FF** and of the groupoid of
a flat field-valued presentation of an algebraic stack.

For the object space there is nothing to do: the presheaf is isomorphic to a representable one.
For the arrow space the input is **Stacks 06LZ** at condition (2), in the form
`AlgebraicGeometry.Space.isRepresentable_of_isLocallyOfFiniteType_over_field_of_base`: the
source map of the groupoid, composed with the identification of the object space, is a morphism
of the arrow space to the presheaf of the spectrum of a field, and it is locally of finite type;
with the dimension of the arrow space zero that tag makes the arrow space a scheme.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isRepresentable_objects`: the object space is
  representable as soon as it is identified with the presheaf of an object of the site.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.nonempty_points_arrows`: the arrow space has a
  point as soon as the object space does — the identity arrow at it (**Stacks 06K5**).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isRepresentable_arrows`: **the arrow space is
  representable** when the object space is the presheaf of a field spectrum of the site, the
  source is locally of finite type and the arrow space has dimension zero.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isRepresentable_arrows_of_dimension_le_zero`: the
  same from `dim ≤ 0`, which is the unconditional form **Stacks 06FF** and **Stacks 0ACA**
  deliver, the missing point of the arrow space being the identity arrow.

## Implementation notes

The hypothesis on the dimension is the one **Stacks 06FF** produces, so it is stated on the
arrow *space* and not on the arrow scheme; this is the representability counterpart of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces`'s
`isLocallyArtinian_derealization_arrows_of_dimension_le_zero`, which reads the same hypothesis on
the de-realized arrow scheme. Both go through the source map composed with the identification of
the object space, and the local-finite-type hypothesis is
transferred across that composition by invariance of the every-étale-chart condition of
**Stacks 03MJ** under isomorphism.

## References

* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 06FF](https://stacks.math.columbia.edu/tag/06FF)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- **The object space of a groupoid in algebraic spaces identified with the presheaf of an
object of the site is representable.** -/
theorem isRepresentable_objects {K : BigFppfOver C S hS} (e : G.objects.obj ≅ yoneda.obj K) :
    G.objects.obj.IsRepresentable :=
  isRepresentable_of_natIso (yoneda.obj K) e.symm

/-- **The arrow space of a groupoid in algebraic spaces has a point as soon as its object space
does**: the unit of **Stacks 06K5** carries a point of the object space to the identity arrow
at it. -/
theorem nonempty_points_arrows (hne : Nonempty (Space.points C S hS G.objects.obj)) :
    Nonempty (Space.points C S hS G.arrows.obj) :=
  ⟨Space.pointsMap C S hS G.objects.obj (identityArrow G).hom hne.some⟩

/-- **The arrow space of a groupoid in algebraic spaces over a field is representable.** Let the
object space of `G` be identified with the presheaf of an object `K` of the site whose
underlying scheme is the spectrum of a field, let the source of `G` be locally of finite type
and let the arrow space have dimension zero. Then the arrow space is a scheme.

This is **Stacks 06LZ** at condition (2): the source, read through the identification of the
object space, is a morphism of the arrow space to the presheaf of the field spectrum which is
locally of finite type, so
`AlgebraicGeometry.Space.isRepresentable_of_isLocallyOfFiniteType_over_field_of_base` applies. -/
theorem isRepresentable_arrows (hZ : C.Contains (⊤_ Scheme.{u}))
    {K : BigFppfOver C S hS} (e : G.objects.obj ≅ yoneda.obj K)
    {k : Type u} [Field k]
    (eK : (BigFppfOver.toScheme C S hS).obj K ≅ Spec (.of k))
    (hsrc : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (hdim : Space.dimension C S hS G.arrows.obj G.arrows.property = 0) :
    G.arrows.obj.IsRepresentable := by
  let : MorphismProperty.RespectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS
          (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf C S hS _
  exact Space.isRepresentable_of_isLocallyOfFiniteType_over_field_of_base C S hS hZ
    G.arrows.property eK (m := G.source.hom ≫ e.hom)
    (MorphismProperty.RespectsIso.postcomp _ e.hom _ hsrc) hdim

/-- **The arrow space of a groupoid in algebraic spaces over a field is representable**, from the
inequality `dim ≤ 0`.

That inequality is the unconditional form of zero-dimensionality — the dimension of
**Stacks 04N6** is a supremum in `WithBot ℕ∞`, so the empty space has dimension `⊥` — and it is
what **Stacks 06FF** and **Stacks 0ACA** deliver. The point that promotes it to an equality is
the identity arrow at a point of the object space. -/
theorem isRepresentable_arrows_of_dimension_le_zero (hZ : C.Contains (⊤_ Scheme.{u}))
    {K : BigFppfOver C S hS} (e : G.objects.obj ≅ yoneda.obj K)
    {k : Type u} [Field k]
    (eK : (BigFppfOver.toScheme C S hS).obj K ≅ Spec (.of k))
    (hsrc : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (hdim : Space.dimension C S hS G.arrows.obj G.arrows.property ≤ 0)
    (hne : Nonempty (Space.points C S hS G.objects.obj)) :
    G.arrows.obj.IsRepresentable :=
  isRepresentable_arrows G hZ e eK hsrc
    (Space.dimension_eq_zero_of_dimension_le_zero C S hS G.arrows.property hdim
      (nonempty_points_arrows G hne))

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
