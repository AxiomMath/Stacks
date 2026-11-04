module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import Mathlib.CategoryTheory.Sites.Equivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A `Type u`-presented model of the small étale ringed topos

The small étale site of a scheme `S : Scheme.{u}` has its objects in `Type (u + 1)` and its
morphisms in `Type u`, so `AlgebraicGeometry.SmallEtale.ringedTopos` is an
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`: a ringed topos whose *section* universe lies
strictly below its *object* universe.  That is the one universe shape in which the ringed-topos
machinery of this development is unavailable.  Stacks 06YY, 05VD and 07A4 are all proved for
`AlgebraicGeometry.RingedTopos.{u, u, u}`, or — for the first of them — at free universes with
the sections at the `max` of the two site universes; a ringed topos with objects in `Type (u+1)`
and sections in `Type u` satisfies neither constraint.

The small étale site is nevertheless *essentially small* at `u`
(`AlgebraicGeometry.SmallEtale.essentiallySmall`), so it is equivalent to a genuinely
small category `SmallModel.{u} (SmallEtale B S hS) : Type u`.  Transporting the étale topology
and the structure sheaf along that equivalence produces a ringed topos
`AlgebraicGeometry.SmallEtale.smallModelRingedTopos : RingedTopos.{u, u, u}` whose topos of
sheaves and whose sheaves of modules are equivalent to those of `(S_étale, 𝒪)`, and which does
lie in the universe shape the Stacks 06YY / 05VD / 07A4 chain is stated at.

That transport is not special to the small étale site, and it is not carried out here: it is
`AlgebraicGeometry.RingedTopos.smallModel` and its comparison morphisms, built at free universes
for an arbitrary site which is essentially small at the universe of its structure sheaf's
sections.  **Everything in this file is that construction instantiated at the small étale site
of `S`**, which is essentially small at `u` by
`AlgebraicGeometry.SmallEtale.essentiallySmall`; what the file adds is the comparison of the
model with the small Zariski site of `S`, which is particular to this site.

This file therefore names:

* the comparison `(model) ⟶ (S_étale, 𝒪)`, whose underlying functor is the comparison of the
  small étale site with its small model and whose structure map is an *isomorphism*, so it is an
  equivalence of ringed topoi and not merely a morphism;
* the morphism `ε_model : (model) ⟶ (S_Zar, 𝒪_S)`, the composite of the morphism `ε` of
  Stacks 08H7 with that comparison.  Its underlying functor is a *morphism of sites* in the
  sense of Stacks 00X1, which the étale presentation of `ε` cannot be: `ε`'s own underlying
  functor goes between categories in two different universes, and
  `CategoryTheory.Functor.IsMorphismOfSites` is available only for small categories in a single
  universe.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallModelEquiv`: the comparison of the small étale site with a
  small model of it in `Type u`.
* `AlgebraicGeometry.SmallEtale.smallModelTopology`: the étale topology transported to the small
  model, namely the topology induced by the comparison.
* `AlgebraicGeometry.SmallEtale.smallModelRingedTopos`: **the model**, a
  `RingedTopos.{u, u, u}`, with structure sheaf the restriction of the structure sheaf of the
  small étale site along the comparison.
* `AlgebraicGeometry.SmallEtale.toEtaleStructureIso`: the identification of the structure sheaf
  of the small étale site with the restriction, back along the comparison, of the structure
  sheaf of the model.
* `AlgebraicGeometry.SmallEtale.smallModelStructureSheaf`: the structure sheaf of the model,
  named so that statements about it avoid the structure projection.
* `AlgebraicGeometry.SmallEtale.toEtaleHom`: the comparison as a morphism of ringed topoi
  `(model) ⟶ (S_étale, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.fromEtaleHom`: the comparison in the other direction, as a
  morphism of ringed topoi `(S_étale, 𝒪) ⟶ (model)`, whose structure map is the identity.
* `AlgebraicGeometry.SmallEtale.opensToSmallModel`: the inclusion of the small Zariski site of
  `S` into the model.
* `AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom`: **`ε` read on the model**, the morphism
  of ringed topoi `(model) ⟶ (S_Zar, 𝒪_S)`.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_toEtaleHom_fSharp`: the structure map of the comparison is
  an isomorphism, so the comparison is an equivalence of ringed topoi.
* `AlgebraicGeometry.SmallEtale.isMorphismOfSites_opensToSmallModel`: the inclusion of the small
  Zariski site into the model is a morphism of sites, by Stacks 00X5 — it is continuous and
  representably flat, being the composite of the continuous representably flat inclusion of the
  small Zariski site into the small étale site with an equivalence.
* `AlgebraicGeometry.SmallEtale.isMorphismOfSites_toZariskiSmallModelHom_u`: the same statement
  about the functor underlying `ε_model`, which is what the Stacks 06YY and 08H5 chain consumes.

## Implementation notes

**Every instance the model needs is found by instance search, and that is the whole point of
the construction.**  The model site is a `SmallCategory` in `Type u`, so Mathlib's
unconditional instances supply `HasSheafify _ (Type u)`, `HasSheafify _ AddCommGrpCat.{u}`,
`GrothendieckTopology.WEqualsLocallyBijective _ AddCommGrpCat.{u}` and the four
`HasSheafCompose` instances with no argument at all; on the small étale site each of these had
to be proved separately from essential smallness
(`AlgebraicGeometry.SmallEtale.hasWeakSheafify_smallEtale`,
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_smallEtale`,
`AlgebraicGeometry.SmallEtale.hasSheafify_smallType`).
No instance is declared here for that reason.

**The structure map of the comparison is the unit of Mathlib's equivalence of sheaf
categories**, and that is where the content of
`AlgebraicGeometry.SmallEtale.toEtaleStructureIso` sits: see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel`.  Here it is only instantiated.

**Essential smallness is passed to the generic comparison explicitly.**
`AlgebraicGeometry.RingedTopos.toSmallModelHom` and
`AlgebraicGeometry.RingedTopos.fromSmallModelHom` take the ringed topos packed, since a morphism
of ringed topoi needs one on each side, so they ask for `EssentiallySmall.{u}` of the projection
`(ringedTopos B S hS).C`.  That projection does not reduce at instance transparency, so the
search fails even though `AlgebraicGeometry.SmallEtale.essentiallySmall` is exactly the
instance wanted; it is therefore handed over positionally.  The same projections *do* reduce at
default transparency, which is why `toEtaleHom_u`, `fromEtaleHom_u` and
`toZariskiSmallModelHom_u` are all `rfl`.

## References

* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The model site -/

/-- The comparison of the small étale site of `S` with a small model of it in `Type u`.

The small étale site is essentially small at `u` by
`AlgebraicGeometry.SmallEtale.essentiallySmall`; this is Mathlib's canonical equivalence with the
`Type u` model that essential smallness provides. -/
public noncomputable abbrev smallModelEquiv :
    SmallEtale B S hS ≌ SmallModel.{u} (SmallEtale B S hS) :=
  equivSmallModel.{u} (SmallEtale B S hS)

/-- The small étale topology of `S`, transported to the small model of the small étale site:
the topology induced on the model by the comparison, which is the finest one making the
comparison continuous and for which the comparison is a dense subsite inclusion in both
directions. -/
public noncomputable abbrev smallModelTopology :
    GrothendieckTopology (SmallModel.{u} (SmallEtale B S hS)) :=
  RingedTopos.smallModelTopology (topology B S hS)

/-- The structure sheaf of the model: the restriction, along the comparison, of the structure
sheaf `T ↦ Γ(T, 𝒪_T)` of the small étale site of `S`.

This is named, rather than written out inside
`AlgebraicGeometry.SmallEtale.smallModelRingedTopos`, so that statements about sheaves of
modules on the model can be made without going through the structure projection
`(smallModelRingedTopos B S hS).O`: that projection does not unfold at instance transparency,
and a statement phrased with it forces every `HasSheafify`, `WEqualsLocallyBijective` and
`HasSheafCompose` instance to be restated at the projected spelling of the topology. -/
public noncomputable abbrev smallModelStructureSheaf :
    Sheaf (smallModelTopology B S hS) CommRingCat.{u} :=
  RingedTopos.smallModelStructureSheaf (topology B S hS) (commRingStructureSheaf B S hS)

/-- **The `Type u`-presented model of the small étale ringed topos of `S`.**  Its site is the
small model of the small étale site, with the transported topology, and its structure sheaf is
the restriction of the structure sheaf `T ↦ Γ(T, 𝒪_T)` of the small étale site along the
comparison.

Unlike `AlgebraicGeometry.SmallEtale.ringedTopos`, which is a `RingedTopos.{u, u + 1, u}`, this
is a `RingedTopos.{u, u, u}`: the universe shape at which Stacks 06YY, 05VD and 07A4 are
available. -/
public noncomputable def smallModelRingedTopos : RingedTopos.{u, u, u} :=
  RingedTopos.smallModel (topology B S hS) (commRingStructureSheaf B S hS)

/-- The site of the model is the small model of the small étale site. -/
@[simp]
public theorem smallModelRingedTopos_C :
    (smallModelRingedTopos B S hS).C = SmallModel.{u} (SmallEtale B S hS) := rfl

/-- The topology of the model is the transported étale topology. -/
@[simp]
public theorem smallModelRingedTopos_J :
    (smallModelRingedTopos B S hS).J = smallModelTopology B S hS := rfl

/-- The structure sheaf of the model is the restriction of the structure sheaf of the small
étale site. -/
@[simp]
public theorem smallModelRingedTopos_O :
    (smallModelRingedTopos B S hS).O = smallModelStructureSheaf B S hS := rfl

/-- The structure sheaf of the model has, as its underlying presheaf, the structure presheaf of
the small étale site read through the comparison: its sections over an object `V` of the model
are the global functions on the object of the small étale site that `V` names. -/
@[simp]
public theorem smallModelRingedTopos_O_obj :
    (smallModelRingedTopos B S hS).O.obj =
      (smallModelEquiv B S hS).inverse.op ⋙ (ringedTopos B S hS).O.obj := rfl

/-! ### The comparison with the small étale ringed topos -/

/-- **The identification of the structure sheaf of the small étale site with the restriction,
back along the comparison, of the structure sheaf of the model.**

This is the unit isomorphism of Mathlib's equivalence of sheaf categories
`CategoryTheory.Equivalence.sheafCongr` for the comparison and the induced topology, evaluated
at the structure sheaf; the two restriction functors of that equivalence are, on the nose, the
two `CategoryTheory.Functor.sheafPushforwardContinuous` functors appearing here. -/
public noncomputable def toEtaleStructureIso :
    (ringedTopos B S hS).O ≅
      (((smallModelEquiv B S hS).functor).sheafPushforwardContinuous CommRingCat.{u}
        (topology B S hS) (smallModelTopology B S hS)).obj
          (smallModelRingedTopos B S hS).O :=
  RingedTopos.smallModelStructureIso (topology B S hS) (commRingStructureSheaf B S hS)

/-- **The comparison of the model with the small étale ringed topos, as a morphism of ringed
topoi `(model) ⟶ (S_étale, 𝒪)`.**  Its underlying continuous functor is the comparison of the
small étale site with its small model, and its structure map is
`AlgebraicGeometry.SmallEtale.toEtaleStructureIso`. -/
public noncomputable def toEtaleHom :
    RingedToposSiteHom (smallModelRingedTopos B S hS) (ringedTopos B S hS) :=
  @RingedTopos.toSmallModelHom (ringedTopos B S hS) (essentiallySmall B S hS)

@[simp]
public theorem toEtaleHom_u :
    (toEtaleHom B S hS).u = (smallModelEquiv B S hS).functor := rfl

@[simp]
public theorem toEtaleHom_fSharp :
    (toEtaleHom B S hS).fSharp = (toEtaleStructureIso B S hS).hom := rfl

/-- **The comparison is an equivalence of ringed topoi, not merely a morphism**: its structure
map is an isomorphism, being the component of the unit isomorphism of an equivalence of sheaf
categories. -/
public theorem isIso_toEtaleHom_fSharp : IsIso (toEtaleHom B S hS).fSharp :=
  (toEtaleStructureIso B S hS).isIso_hom

/-- **The comparison in the other direction, as a morphism of ringed topoi
`(S_étale, 𝒪) ⟶ (model)`.**  Its underlying continuous functor is the comparison read from the
model to the small étale site, and its structure map is the *identity*: the structure sheaf of
the model is by definition the restriction of the structure sheaf of the small étale site along
that functor, so the two sides of the structure map are the same sheaf.

This is the morphism whose pushforward of sheaves of modules is restriction to the model, the
transport functor `Mod(𝒪) ⥤ Mod(𝒪_model)`.  Unlike the pullback of sheaves of modules, which is
available only when the two ringed topoi have their section universe equal to their object
universe, the pushforward is available with all four site universes free — which is why the
transport is taken in this direction. -/
public noncomputable def fromEtaleHom :
    RingedToposSiteHom (ringedTopos B S hS) (smallModelRingedTopos B S hS) :=
  @RingedTopos.fromSmallModelHom (ringedTopos B S hS) (essentiallySmall B S hS)

@[simp]
public theorem fromEtaleHom_u :
    (fromEtaleHom B S hS).u = (smallModelEquiv B S hS).inverse := rfl

@[simp]
public theorem fromEtaleHom_fSharp :
    (fromEtaleHom B S hS).fSharp = 𝟙 (smallModelStructureSheaf B S hS) := rfl

/-! ### `ε` read on the model -/

/-- The inclusion of the small Zariski site of `S` into the model of the small étale site: the
inclusion into the small étale site, followed by the comparison with the model. -/
public noncomputable abbrev opensToSmallModel :
    S.Opens ⥤ SmallModel.{u} (SmallEtale B S hS) :=
  opensToSmallEtale B S hS ⋙ (smallModelEquiv B S hS).functor

/-- The inclusion of the small Zariski site of `S` into the model is continuous: the inclusion
into the small étale site is continuous by
`AlgebraicGeometry.SmallEtale.isContinuous_opensToSmallEtale`, and the comparison with the model
is continuous for the induced topology. -/
public instance isContinuous_opensToSmallModel :
    (opensToSmallModel B S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (smallModelTopology B S hS) :=
  Functor.isContinuous_comp (opensToSmallEtale B S hS) (smallModelEquiv B S hS).functor
    (Opens.grothendieckTopology ↥S) (topology B S hS) (smallModelTopology B S hS)

/-- **Stacks 00X5 for the inclusion of the small Zariski site into the model.**  The inclusion
is a morphism of sites in the sense of Stacks 00X1: it is continuous, and it is representably
flat, being the composite of the representably flat inclusion of the small Zariski site into the
small étale site (`AlgebraicGeometry.SmallEtale.representablyFlat_opensToSmallEtale`) with an
equivalence.

This is the statement that `ε`'s own presentation cannot support: `ε` is presented by a functor
`S.Opens ⥤ SmallEtale B S hS` whose target lives in `Type (u + 1)`, and
`CategoryTheory.Functor.IsMorphismOfSites` is stated only for small categories in a single
universe. -/
public theorem isMorphismOfSites_opensToSmallModel :
    (opensToSmallModel B S hS).IsMorphismOfSites
      (Opens.grothendieckTopology ↥S) (smallModelTopology B S hS) :=
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

/-- **`ε` read on the model**: the morphism of ringed topoi
`(model) ⟶ (S_Zar, 𝒪_S)` obtained by composing the morphism `ε` of Stacks 08H7 with the
comparison of the model with the small étale ringed topos.

Both source and target are `RingedTopos.{u, u, u}`, so every statement of the Stacks 06YY,
05VD and 07A4 chain applies to this morphism; `ε` itself, whose source is a
`RingedTopos.{u, u + 1, u}`, is outside the universe shape those statements are made at. -/
public noncomputable def toZariskiSmallModelHom :
    RingedToposSiteHom (smallModelRingedTopos B S hS) S.zariskiRingedTopos :=
  (toZariskiRingedToposHom B S hS).comp (toEtaleHom B S hS)

/-- The functor underlying `ε` read on the model is the inclusion of the small Zariski site of
`S` into the model. -/
@[simp]
public theorem toZariskiSmallModelHom_u :
    (toZariskiSmallModelHom B S hS).u = opensToSmallModel B S hS := rfl

/-- **`ε` read on the model is presented by a morphism of sites.**  This is the hypothesis
`hmos` that every statement of the Stacks 06YY, 0G6R, 05VD and 08H5 chain carries, so it is
recorded here at the spelling in which those statements demand it. -/
public theorem isMorphismOfSites_toZariskiSmallModelHom_u :
    ((toZariskiSmallModelHom B S hS).u).IsMorphismOfSites
      S.zariskiRingedTopos.J (smallModelRingedTopos B S hS).J :=
  isMorphismOfSites_opensToSmallModel B S hS

/-- The morphism of topoi underlying `ε` read on the model, which exists because the underlying
functor is a morphism of sites (Stacks 00XC). -/
@[sga "4 VII 4.2.2"]
public noncomputable def toZariskiSmallModelToposHom :
    MorphismOfTopoi (smallModelRingedTopos B S hS).Topos S.zariskiRingedTopos.Topos :=
  (toZariskiSmallModelHom B S hS).toToposHom (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)

end AlgebraicGeometry.SmallEtale

end
