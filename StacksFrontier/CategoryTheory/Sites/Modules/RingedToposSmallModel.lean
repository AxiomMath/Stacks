module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom

/-!
# The equi-universe small model of a ringed topos

A ringed topos in the sense of Stacks 01D3 is an `AlgebraicGeometry.RingedTopos.{v, u, w}`: a
site with objects in `Type u` and morphisms in `Type v`, carrying a sheaf of commutative rings
with sections in `Type w`.  Much of the ringed-topos machinery — Stacks 06YY, 05VD, 07A4, and
the localization of Stacks 04IF — is stated for a `RingedTopos.{w, w, w}`, where the three
universes agree, and is therefore unavailable for the sites of algebraic geometry, whose objects
lie one universe above their morphisms and their sections.

Whenever the underlying site is *essentially small* at the universe `w` of the sections, that
gap closes: the site has a model whose objects and morphisms both lie in `Type w`, and
transporting the topology and the structure sheaf along the comparison with that model produces
a `RingedTopos.{w, w, w}` together with a comparison which is an *equivalence* of ringed topoi,
its structure map being the unit isomorphism of Mathlib's equivalence of sheaf categories.

This file builds that model once, at free universes.

## Main definitions

* `AlgebraicGeometry.RingedTopos.smallModelTopology`: the topology transported to a small model
  of the site, namely the topology induced by the comparison.
* `AlgebraicGeometry.RingedTopos.smallModelStructureSheaf`: the structure sheaf transported to
  the model, the restriction of the given one along the comparison.
* `AlgebraicGeometry.RingedTopos.smallModel`: **the model**, a `RingedTopos.{w, w, w}`.
* `AlgebraicGeometry.RingedTopos.smallModelStructureIso`: the identification of the structure
  sheaf with the restriction, back along the comparison, of the structure sheaf of the model.
* `AlgebraicGeometry.RingedTopos.toSmallModelHom` and
  `AlgebraicGeometry.RingedTopos.fromSmallModelHom`: the comparison, as morphisms of ringed
  topoi in the two directions.

## Main results

* `AlgebraicGeometry.RingedTopos.isIso_toSmallModelHom_fSharp`: the structure map of the
  comparison is an isomorphism, so the comparison is an equivalence of ringed topoi and not
  merely a morphism.

## Implementation notes

**The model is presented by the topology and the structure sheaf, not by the packed ringed
topos.**  `AlgebraicGeometry.RingedTopos.smallModel` takes a topology and a sheaf of commutative
rings on it rather than a `RingedTopos`, so that at a concrete site every instance is demanded at
the site's own spelling of its topology.  Taking a `RingedTopos` would force the instances to be
demanded at the projection `X.J`, which does not reduce at instance transparency, and every
`HasSheafify`, `WEqualsLocallyBijective` and `HasSheafCompose` instance of the model would have
to be restated there.  The two comparison morphisms are the exception: a morphism of ringed topoi
needs a `RingedTopos` on each side, so they take the packed ringed topos, and their continuity
fields are supplied as explicit `inferInstanceAs` at the unprojected spelling.

**The structure map of the comparison is the unit of Mathlib's equivalence of sheaf
categories.**  `CategoryTheory.Equivalence.sheafCongr` for the comparison and the induced
topology has restriction along the inverse of the comparison as its functor and restriction along
the comparison as its inverse, and both coincide *on the nose* with the
`CategoryTheory.Functor.sheafPushforwardContinuous` spellings that
`AlgebraicGeometry.RingedToposSiteHom` is stated with.  So the unit isomorphism of that
equivalence, evaluated at the structure sheaf, already has the type of the structure map; no
bridge is needed and invertibility is `CategoryTheory.Iso.isIso_hom`.

**Why the limits of the structured-arrow categories are declared here.**  The restriction
functors along the two comparisons are equivalences only once the comma categories indexing the
right Kan extensions have the relevant limits, and Mathlib asks for those as instances.  They
hold because the comma categories are essentially small at `w`: the model is small and the site
is locally small at `w`, both consequences of essential smallness.  Stated at an arbitrary
complete category they serve for sheaves of sets, of abelian groups and of commutative rings
alike.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace AlgebraicGeometry.RingedTopos

section Site

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]

/-- The comma categories indexing the right Kan extension along the comparison of a site with a
small model of it have all limits of a complete category whose morphisms lie in the universe of
the model: they are essentially small there, the model being small and the site locally small. -/
instance hasLimitsOfShape_structuredArrow_equivSmallModel_inverse_op (W : Cᵒᵖ)
    (A : Type u') [Category.{w} A] [HasLimits A] :
    HasLimitsOfShape (StructuredArrow W (equivSmallModel.{w} C).inverse.op) A :=
  have : EssentiallySmall.{w}
      (StructuredArrow W (equivSmallModel.{w} C).inverse.op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The same for the comparison in the other direction.  Together with the previous instance this
is what makes the two restriction functors between the sheaves of a site and the sheaves of its
small model equivalences. -/
instance hasLimitsOfShape_structuredArrow_equivSmallModel_functor_op
    (W : (SmallModel.{w} C)ᵒᵖ) (A : Type u') [Category.{w} A] [HasLimits A] :
    HasLimitsOfShape (StructuredArrow W (equivSmallModel.{w} C).functor.op) A :=
  have : EssentiallySmall.{w}
      (StructuredArrow W (equivSmallModel.{w} C).functor.op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The topology of a site transported to a small model of it: the topology induced on the model
by the comparison, which is the finest one making the comparison continuous and for which the
comparison is a dense subsite inclusion in both directions. -/
noncomputable abbrev smallModelTopology (J : GrothendieckTopology C) :
    GrothendieckTopology (SmallModel.{w} C) :=
  (equivSmallModel.{w} C).inverse.inducedTopology J

end Site

section Model

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{w})

/-- The structure sheaf of the model: the restriction, along the comparison of the site with its
small model, of a sheaf of commutative rings on the site.

This is named, rather than written out inside `AlgebraicGeometry.RingedTopos.smallModel`, so
that statements about sheaves of modules on the model can be made without going through the
structure projection `(smallModel J O).O`: that projection does not unfold at instance
transparency, and a statement phrased with it forces every `HasSheafify`,
`WEqualsLocallyBijective` and `HasSheafCompose` instance to be restated at the projected
spelling of the topology. -/
noncomputable abbrev smallModelStructureSheaf :
    Sheaf (smallModelTopology.{w} J) CommRingCat.{w} :=
  ((equivSmallModel.{w} C).inverse.sheafPushforwardContinuous CommRingCat.{w}
    (smallModelTopology.{w} J) J).obj O

/-- **The equi-universe model of the ringed topos presented by a site and a sheaf of commutative
rings on it.**  Its site is a small model of the given site, with the transported topology, and
its structure sheaf is the restriction of the given one along the comparison.

Its three universes all equal the universe `w` of the sections, which is the universe shape at
which the ringed-topos machinery of Stacks 06YY, 05VD, 07A4 and 04IF is available. -/
noncomputable def smallModel : RingedTopos.{w, w, w} where
  C := SmallModel.{w} C
  J := smallModelTopology.{w} J
  O := smallModelStructureSheaf.{w} J O

/-- The site of the model is a small model of the given site. -/
@[simp]
theorem smallModel_C : (smallModel.{w} J O).C = SmallModel.{w} C := rfl

/-- The topology of the model is the transported topology. -/
@[simp]
theorem smallModel_J : (smallModel.{w} J O).J = smallModelTopology.{w} J := rfl

/-- The structure sheaf of the model is the restriction of the given sheaf of commutative
rings. -/
@[simp]
theorem smallModel_O : (smallModel.{w} J O).O = smallModelStructureSheaf.{w} J O := rfl

/-- **The identification of a sheaf of commutative rings on a site with the restriction, back
along the comparison with a small model, of its restriction to that model.**

This is the unit isomorphism of Mathlib's equivalence of sheaf categories
`CategoryTheory.Equivalence.sheafCongr` for the comparison and the induced topology, evaluated
at the sheaf; the two restriction functors of that equivalence are, on the nose, the two
`CategoryTheory.Functor.sheafPushforwardContinuous` functors appearing here. -/
noncomputable def smallModelStructureIso :
    O ≅ ((equivSmallModel.{w} C).functor.sheafPushforwardContinuous CommRingCat.{w} J
      (smallModelTopology.{w} J)).obj (smallModelStructureSheaf.{w} J O) :=
  (Equivalence.sheafCongr J (smallModelTopology.{w} J) (equivSmallModel.{w} C)
    CommRingCat.{w}).unitIso.app O

end Model

section Hom

variable (X : RingedTopos.{v, u, w}) [EssentiallySmall.{w} X.C]

/-- **The comparison of the equi-universe model with the ringed topos it models, as a morphism of
ringed topoi `(model) ⟶ X`.**  Its underlying continuous functor is the comparison of the site of
`X` with its small model, and its structure map is
`AlgebraicGeometry.RingedTopos.smallModelStructureIso`, hence an isomorphism. -/
noncomputable def toSmallModelHom :
    RingedToposSiteHom (smallModel.{w} X.J X.O) X where
  u := (equivSmallModel.{w} X.C).functor
  isContinuous := inferInstanceAs ((equivSmallModel.{w} X.C).functor.IsContinuous
    X.J (smallModelTopology.{w} X.J))
  fSharp := (smallModelStructureIso.{w} X.J X.O).hom

/-- The underlying functor of `toSmallModelHom` is the comparison functor of the small model. -/
@[simp]
theorem toSmallModelHom_u :
    (toSmallModelHom.{w} X).u = (equivSmallModel.{w} X.C).functor := rfl

/-- The structure map of `toSmallModelHom` is `smallModelStructureIso`. -/
@[simp]
theorem toSmallModelHom_fSharp :
    (toSmallModelHom.{w} X).fSharp = (smallModelStructureIso.{w} X.J X.O).hom := rfl

/-- **The comparison is an equivalence of ringed topoi, not merely a morphism**: its structure
map is an isomorphism, being the component of the unit isomorphism of an equivalence of sheaf
categories. -/
theorem isIso_toSmallModelHom_fSharp : IsIso (toSmallModelHom.{w} X).fSharp :=
  (smallModelStructureIso.{w} X.J X.O).isIso_hom

/-- **The comparison in the other direction, as a morphism of ringed topoi `X ⟶ (model)`.**  Its
underlying continuous functor is the comparison read from the model to the site, and its
structure map is the *identity*: the structure sheaf of the model is by definition the
restriction of the structure sheaf of `X` along that functor, so the two sides of the structure
map are the same sheaf. -/
noncomputable def fromSmallModelHom :
    RingedToposSiteHom X (smallModel.{w} X.J X.O) where
  u := (equivSmallModel.{w} X.C).inverse
  isContinuous := inferInstanceAs ((equivSmallModel.{w} X.C).inverse.IsContinuous
    (smallModelTopology.{w} X.J) X.J)
  fSharp := 𝟙 _

/-- The underlying functor of `fromSmallModelHom` is the inverse comparison functor of the small
model. -/
@[simp]
theorem fromSmallModelHom_u :
    (fromSmallModelHom.{w} X).u = (equivSmallModel.{w} X.C).inverse := rfl

/-- The structure map of `fromSmallModelHom` is the identity of the structure sheaf of the
model. -/
@[simp]
theorem fromSmallModelHom_fSharp :
    (fromSmallModelHom.{w} X).fSharp = 𝟙 (smallModelStructureSheaf.{w} X.J X.O) := rfl

end Hom

end AlgebraicGeometry.RingedTopos

end
