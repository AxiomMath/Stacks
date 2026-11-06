module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafSiteTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

/-!
# The two sheaves of the lifting problem at one universe

Let `X ⊆ X'` be a closed subspace of an algebraic space over a scheme `S` in a big fppf site,
let `q : Y ⟶ Bb` be a morphism of algebraic spaces and let `a : X ⟶ Y` be a morphism over `Bb`.
`AlgebraicGeometry.Space.liftActionSheafTransport` puts the acting sheaf of [Stacks Project,
Tag 061D] on the small étale site of `X'`, where the sheaf of lifts
`AlgebraicGeometry.Space.liftsSubfunctor` lives, and
`AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquiv` identifies their sections
over a chart presented by a chart presentation.  The two are still not comparable as a group
acting on a set in the sense of `PseudoTorsor`, for two reasons that have nothing to do with the
geometry:

* the acting sheaf is a sheaf of `𝒪_X`-modules at module universe `u + 1` — a section over an
  étale chart is a morphism of modules on a slice of the small étale site, whose objects are in
  `Type (u + 1)` (see `AlgebraicGeometry.Space.smallEtaleInternalHom`) — so its sections are in
  `Type (u + 1)`, while the sheaf of lifts is a subfunctor of a presheaf of `Type u`;
* `PseudoTorsor` takes a `SheafOfGroups`, that is a *multiplicatively* written group on each set
  of sections, whereas the acting sheaf's sections are abelian groups.

This file removes both obstacles.  The universes are aligned **upwards**: the sheaf of lifts is
composed with `CategoryTheory.uliftFunctor` to land in `Type (u + 1)`, which costs nothing
because a universe lift neither creates nor destroys amalgamations
(`CategoryTheory.Presieve.isSheaf_comp_uliftFunctor`).

Aligning downwards is not available, for two independent reasons.  First, the module universe
`u + 1` of the acting sheaf is forced by its own definition:
`AlgebraicGeometry.Space.smallEtaleInternalHom` of two `𝒪_X`-modules at module universe `m`
lands at module universe `max (u + 1) m`, because a section over an étale chart is a morphism of
modules on a slice of the small étale site and so a family indexed by the objects of that slice.
Second, and decisively, the equivalence of topoi the transport is taken along,
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening`, does not exist at `Type u`: it
is `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, whose `IsEquivalence` instance asks for
limits of shape `CategoryTheory.StructuredArrow X (thickeningChartBaseChange …).op` in the value
category, and those shapes have objects in `Type (u + 1)`, so `Type u` does not have them.  The
same equivalence instantiated at `Type u` was elaborated and reports exactly that failure of
instance synthesis.  Lowering would therefore mean first replacing the small étale site by a
`u`-small model of it — the site is essentially small,
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall` — and rebuilding the internal hom, the
transport and the chart-level identification over that model, which is new mathematics rather
than bookkeeping.

## Main definitions

* `AlgebraicGeometry.Space.liftActionSheafOfGroups`: **the acting sheaf of [Stacks Project,
  Tag 061D], as a sheaf of groups on the small étale site of `X'`** — the shape in which
  `PseudoTorsor` takes the group that acts.  Its presheaf is the transported acting sheaf on the
  nose, so every statement about the transport applies to it verbatim.
* `AlgebraicGeometry.Space.liftsSubfunctorULift`: **the sheaf of lifts of [Stacks Project,
  Tag 061D] as a sheaf of `Type (u + 1)`**, the universe of the acting sheaf's sections.
* `AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquivULift`: the bijection of
  `AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquiv` between the two, at the
  common universe and with the acting side read as a group of sections.

## Main results

* `AlgebraicGeometry.Space.liftActionSheafTransport_map_add`: **the restriction maps of the
  transported acting sheaf are additive**, which is what makes the transport a sheaf of groups.
* `AlgebraicGeometry.Space.liftActionSheafTransport_mul_eq_add` and
  `AlgebraicGeometry.Space.liftActionSheafTransport_one_eq_zero`: the group law of
  `AlgebraicGeometry.Space.liftActionSheafOfGroups` is the addition of the acting sheaf's
  sections, written multiplicatively.
* `AlgebraicGeometry.Space.liftActionSheafOfGroups_presheaf`: the presheaf of sections of the
  acting sheaf of groups is the transported acting sheaf, by `rfl`.
* `AlgebraicGeometry.Space.liftsSubfunctorULift_map_up` and
  `AlgebraicGeometry.Space.liftsSubfunctorULift_down_map`: the restriction maps of the lifted
  sheaf of lifts are those of the sheaf of lifts, in both directions of the lift — the
  restriction compatibility of the universe lift itself —
  `AlgebraicGeometry.Space.liftsSubfunctorULiftEquiv_naturality` being the same statement as a
  commuting square of the sections bijections.

## Implementation notes

The group structure is the multiplicative reading of the additive structure of the acting
sheaf's sections, through `Multiplicative`, exactly as
`Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf` reads an abelian sheaf as a sheaf of
groups.  It is recorded on the transported sheaf's sections rather than on a new presheaf, so
`AlgebraicGeometry.Space.liftActionSheafOfGroups_presheaf` holds by `rfl` and nothing proved
about the transport has to be restated.

`SheafOfGroups` quantifies its group structure and its multiplicativity over objects of the
*opposite* site, so both are stated here in that spelling as well
(`AlgebraicGeometry.Space.liftActionSheafTransport_addCommGroup_op`,
`AlgebraicGeometry.Space.liftActionSheafTransport_group_op`,
`AlgebraicGeometry.Space.liftActionSheafTransport_map_mul_op`): the existing instance
`AlgebraicGeometry.Space.liftActionSheafTransport_addCommGroup` is keyed at `Opposite.op U'`, so
instance search does not find it for a section over a variable object of the opposite site even
though the two are definitionally equal.  Each field of
`AlgebraicGeometry.Space.liftActionSheafOfGroups` is then one of these declarations applied
verbatim, which is what makes the structure affordable: assembling it with the fields written
out in place is a deterministic 200,000-heartbeat `whnf` timeout, while every one of the pieces
is free on its own.

**Additivity of the transport's restriction maps is cheap.**  The *statement* elaborates
cheaply; what exceeds the budget is the term-mode proof `map_add φ.hom θ η`, because
unifying an application of `Functor.map` of a `Type`-valued functor with an application of
`FunLike.coe` drives `whnf` through the transport and the forgetful functor.  Rewriting with
`AlgebraicGeometry.Space.liftActionSheafTransport_map_apply` first — which is `rfl`
and matches syntactically — puts all three occurrences in the `FunLike` spelling before
`map_add` is applied, and the lemma then checks in seconds.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 061D]'s two sheaves are registered
on `AlgebraicGeometry.Space.liftsSubfunctor` and `AlgebraicGeometry.Space.liftActionSheaf`;
aligning the universes of the two and reading the acting one multiplicatively asserts no tag.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

/-! ### The acting sheaf as a sheaf of groups -/

/-- **The restriction maps of the transported acting sheaf are additive.**

The transported sheaf's sections over an étale chart of `X'` are the sections of the acting
sheaf of [Stacks Project, Tag 061D] over the base-changed chart of `X`
(`AlgebraicGeometry.Space.liftActionSheafTransport_obj`), hence an abelian group, and its
restriction maps are the maps underlying morphisms of abelian groups
(`AlgebraicGeometry.Space.liftActionSheafTransport_map_apply`). -/
theorem liftActionSheafTransport_map_add (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (θ η : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    (liftActionSheafTransport C S hS Z hG q a).obj.map m.op (θ + η) =
      (liftActionSheafTransport C S hS Z hG q a).obj.map m.op θ +
        (liftActionSheafTransport C S hS Z hG q a).obj.map m.op η := by
  rw [liftActionSheafTransport_map_apply, liftActionSheafTransport_map_apply,
    liftActionSheafTransport_map_apply]
  exact map_add _ θ η

/-- The sections of the transported acting sheaf over an object of the *opposite* small étale
site of `X'` are an abelian group.  This is
`AlgebraicGeometry.Space.liftActionSheafTransport_addCommGroup`, whose statement is keyed at
`Opposite.op U'` and is therefore not found by instance search at a variable object of the
opposite site, even though the two spellings are definitionally equal. -/
instance liftActionSheafTransport_addCommGroup_op (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (U : (SmallEtale C S hS X'.1)ᵒᵖ) :
    AddCommGroup ((liftActionSheafTransport C S hS Z hG q a).obj.obj U) :=
  inferInstanceAs (AddCommGroup
    ((liftActionSheafTransport C S hS Z hG q a).obj.obj (op U.unop)))

/-- **The sections of the transported acting sheaf form a group, written multiplicatively**:
the abelian group of
`AlgebraicGeometry.Space.liftActionSheafTransport_addCommGroup_op`, read through
`Multiplicative`, which is the form `SheafOfGroups` asks for. -/
instance liftActionSheafTransport_group_op (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (U : (SmallEtale C S hS X'.1)ᵒᵖ) :
    Group ((liftActionSheafTransport C S hS Z hG q a).obj.obj U) :=
  inferInstanceAs (Group (Multiplicative
    ((liftActionSheafTransport C S hS Z hG q a).obj.obj U)))

/-- The multiplication of
`AlgebraicGeometry.Space.liftActionSheafTransport_group_op` is the addition of the sections of
the acting sheaf. -/
theorem liftActionSheafTransport_mul_eq_add (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U : (SmallEtale C S hS X'.1)ᵒᵖ}
    (θ η : (liftActionSheafTransport C S hS Z hG q a).obj.obj U) :
    θ * η = θ + η :=
  rfl

/-- The unit of `AlgebraicGeometry.Space.liftActionSheafTransport_group_op` is the zero section
of the acting sheaf. -/
theorem liftActionSheafTransport_one_eq_zero (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (U : (SmallEtale C S hS X'.1)ᵒᵖ) :
    (1 : (liftActionSheafTransport C S hS Z hG q a).obj.obj U) = 0 :=
  rfl

/-- `AlgebraicGeometry.Space.liftActionSheafTransport_map_add` at an arbitrary morphism of the
opposite small étale site of `X'`, the spelling in which `SheafOfGroups` quantifies. -/
theorem liftActionSheafTransport_map_add_op (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U V : (SmallEtale C S hS X'.1)ᵒᵖ} (f : U ⟶ V)
    (θ η : (liftActionSheafTransport C S hS Z hG q a).obj.obj U) :
    (liftActionSheafTransport C S hS Z hG q a).obj.map f (θ + η) =
      (liftActionSheafTransport C S hS Z hG q a).obj.map f θ +
        (liftActionSheafTransport C S hS Z hG q a).obj.map f η :=
  liftActionSheafTransport_map_add C S hS Z hG q a f.unop θ η

/-- **The restriction maps of the transported acting sheaf are group homomorphisms** for
`AlgebraicGeometry.Space.liftActionSheafTransport_group_op`: this is
`AlgebraicGeometry.Space.liftActionSheafTransport_map_add_op` written multiplicatively. -/
theorem liftActionSheafTransport_map_mul_op (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U V : (SmallEtale C S hS X'.1)ᵒᵖ} (f : U ⟶ V)
    (θ η : (liftActionSheafTransport C S hS Z hG q a).obj.obj U) :
    (liftActionSheafTransport C S hS Z hG q a).obj.map f (θ * η) =
      (liftActionSheafTransport C S hS Z hG q a).obj.map f θ *
        (liftActionSheafTransport C S hS Z hG q a).obj.map f η :=
  liftActionSheafTransport_map_add_op C S hS Z hG q a f θ η

/-- **The acting sheaf of [Stacks Project, Tag 061D] as a sheaf of groups on the small étale
site of the ambient space `X'`**, which is the shape in which `PseudoTorsor` takes the sheaf of
groups that acts.

The underlying presheaf is `AlgebraicGeometry.Space.liftActionSheafTransport` itself, so no new
presheaf of sections is introduced; the group law is
`AlgebraicGeometry.Space.liftActionSheafTransport_group_op`, the addition of the acting sheaf's
sections written multiplicatively, and that the restriction maps are group homomorphisms is
`AlgebraicGeometry.Space.liftActionSheafTransport_map_mul_op`. -/
def liftActionSheafOfGroups (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    SheafOfGroups.{u + 1} (SmallEtale.topology C S hS X'.1) where
  presheaf := (liftActionSheafTransport C S hS Z hG q a).obj
  isSheaf := (liftActionSheafTransport C S hS Z hG q a).property
  group U := liftActionSheafTransport_group_op C S hS Z hG q a U
  map_mul {_ _} f θ η := liftActionSheafTransport_map_mul_op C S hS Z hG q a f θ η

/-- The presheaf underlying `AlgebraicGeometry.Space.liftActionSheafOfGroups` is the transported
acting sheaf, on the nose. -/
theorem liftActionSheafOfGroups_presheaf (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    (liftActionSheafOfGroups C S hS Z hG q a).presheaf =
      (liftActionSheafTransport C S hS Z hG q a).obj :=
  rfl

/-! ### The sheaf of lifts at the universe of the acting sheaf -/

/-- **The sheaf of lifts of [Stacks Project, Tag 061D] as a sheaf of `Type (u + 1)`**, the
universe in which the acting sheaf's sections live.

Composing with `CategoryTheory.uliftFunctor` changes neither the sheaf condition nor the
restriction maps: a universe lift is a bijection on each set of sections compatible with
restriction, so compatible families and their amalgamations correspond
(`CategoryTheory.Presieve.isSheaf_comp_uliftFunctor`). -/
def liftsSubfunctorULift (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) :
    Sheaf (SmallEtale.topology C S hS X'.1) (Type (u + 1)) :=
  ⟨(liftsSubfunctor C S hS p q a).toFunctor ⋙ uliftFunctor.{u + 1, u},
    (isSheaf_iff_isSheaf_of_type _ _).2
      (Presieve.isSheaf_comp_uliftFunctor _
        ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_liftsSubfunctor C S hS p q a)))⟩

/-- The sections of `AlgebraicGeometry.Space.liftsSubfunctorULift` over an étale chart of `X'`
are the universe lift of the sections of the sheaf of lifts. -/
theorem liftsSubfunctorULift_obj (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) (U' : SmallEtale C S hS X'.1) :
    (liftsSubfunctorULift C S hS p q a).obj.obj (op U') =
      ULift.{u + 1} ((liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :=
  rfl

/-- **The restriction maps of `AlgebraicGeometry.Space.liftsSubfunctorULift` are those of the
sheaf of lifts**, read on a lifted section. -/
theorem liftsSubfunctorULift_map_up (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    (liftsSubfunctorULift C S hS p q a).obj.map m.op (ULift.up β) =
      ULift.up ((liftsSubfunctor C S hS p q a).toFunctor.map m.op β) :=
  rfl

/-- **The restriction maps of `AlgebraicGeometry.Space.liftsSubfunctorULift` are those of the
sheaf of lifts**, read on an arbitrary section through the inverse of the lift. -/
theorem liftsSubfunctorULift_down_map (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (β : (liftsSubfunctorULift C S hS p q a).obj.obj (op U')) :
    ((liftsSubfunctorULift C S hS p q a).obj.map m.op β).down =
      (liftsSubfunctor C S hS p q a).toFunctor.map m.op β.down :=
  rfl

/-- The sections of `AlgebraicGeometry.Space.liftsSubfunctorULift` over an étale chart of `X'`
are in bijection with the lifts over that chart. -/
def liftsSubfunctorULiftEquiv (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) (U' : SmallEtale C S hS X'.1) :
    (liftsSubfunctorULift C S hS p q a).obj.obj (op U') ≃
      (liftsSubfunctor C S hS p q a).toFunctor.obj (op U') :=
  Equiv.ulift

/-- **The universe lift of the sheaf of lifts is compatible with restriction**: the bijections
of `AlgebraicGeometry.Space.liftsSubfunctorULiftEquiv` form a commuting square with the
restriction maps of the two presheaves. -/
theorem liftsSubfunctorULiftEquiv_naturality (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (β : (liftsSubfunctorULift C S hS p q a).obj.obj (op U')) :
    liftsSubfunctorULiftEquiv C S hS p q a V'
        ((liftsSubfunctorULift C S hS p q a).obj.map m.op β) =
      (liftsSubfunctor C S hS p q a).toFunctor.map m.op
        (liftsSubfunctorULiftEquiv C S hS p q a U' β) :=
  rfl

/-! ### The two sheaves compared at a chart presentation -/

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')

/-- **The sections of the acting sheaf of groups over `U'` are the sections of the sheaf of
lifts over `U'`**, granted that the two charts of `q` of a presentation at `U'` are étale: this
is `AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquiv` with both sides in the
shape `PseudoTorsor` takes them — the acting side as the sections of a sheaf of groups, the
lifts side at the universe of those sections. -/
def transportLiftsEquivULift (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (liftActionSheafOfGroups C S hS Z hG q a).presheaf.obj (op U') ≃
      (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U') :=
  (P.transportLiftsEquiv C S hS hG hw hv).trans Equiv.ulift.symm

/-- The bijection of
`AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquivULift` is the action of the
acting sheaf's sections on the presented lift. -/
theorem transportLiftsEquivULift_apply (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (θ : (liftActionSheafOfGroups C S hS Z hG q a).presheaf.obj (op U')) :
    P.transportLiftsEquivULift C S hS hG hw hv θ =
      ULift.up (P.translateTransportSection C S hS hG hw hv θ) :=
  rfl

/-- **The sections of the acting sheaf of groups act simply transitively on the sections of the
lifted sheaf of lifts over `U'`**, granted that the two charts of `q` of a presentation at `U'`
are étale: every section of the lifted sheaf of lifts is the translate of the presented lift by
a unique section of the acting sheaf of groups.  This is the simple transitivity of
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_bijective` with both
sides at the universe of the acting sheaf's sections. -/
theorem existsUnique_translateTransportSection_up_eq (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (β : (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U')) :
    ∃! θ : (liftActionSheafOfGroups C S hS Z hG q a).presheaf.obj (op U'),
      ULift.up (P.translateTransportSection C S hS hG hw hv θ) = β :=
  ⟨(P.transportLiftsEquivULift C S hS hG hw hv).symm β,
    (P.transportLiftsEquivULift C S hS hG hw hv).apply_symm_apply β,
    fun _ hθ => (P.transportLiftsEquivULift C S hS hG hw hv).injective
      (hθ.trans ((P.transportLiftsEquivULift C S hS hG hw hv).apply_symm_apply β).symm)⟩

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
