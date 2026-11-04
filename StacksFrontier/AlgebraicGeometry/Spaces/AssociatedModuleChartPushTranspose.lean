module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushSelfChart

/-!
# The associated-module comparison at the identity chart, read on Zariski sections

Let `B` be a big fppf site containing a scheme `S` and let `V` be an object of the big fppf
category over `S`.  `AlgebraicGeometry.Space.associatedModuleChartPushSelfChartIso` recovers a
quasi-coherent `𝒪`-module on the small étale site of `yoneda.obj V` from its Zariski chart
restriction at the identity chart, and
`AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` does the same for a
sheaf of ideals read as a submodule of `𝒪_V`.

Both are built from the **inverse of the counit** of the associated-module adjunction of
Stacks 03DX, so neither describes its own values; that is what the "What is not proved" sections
of `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiDefiningIdeal.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean` record as missing.

**This file supplies the description that is wanted, and it never computes the
counit-inverse.**  A morphism out of an associated module `𝓝^a` is determined by its transpose
along the associated-module adjunction — its composite with the unit `𝓝 ⟶ (𝓝^a)|_{Zar}` — and
that transpose is a morphism of modules on the small *Zariski* site, where both sides have
sections.  The transposes of the two comparisons are computed here, and the answer is that
nothing of the counit survives: the counit's own transpose is the identity, by the right triangle
identity of the adjunction.  For the comparison of a sheaf of ideals the transpose is the
canonical sections map, the comparison of scalars
`AlgebraicGeometry.Space.chartSectionsRingHom`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_eqToHom_comp_counit` and
  `CategoryTheory.Adjunction.unit_comp_map_eqToIso_trans_hom`: **for any adjunction, the transpose
  of the counit read over an equality of objects is the transport of that equality.**  This is
  where the counit-inverse disappears.
* `CategoryTheory.Adjunction.hom_ext_of_unit_comp_map`: **two morphisms out of a left adjoint
  with the same transpose are equal** — what puts a comparison of two morphisms out of `𝓝^a`
  onto the sections of `𝓝`.
* `unit_comp_restrictModule_map_associatedModuleRestrictModuleIso_hom` (in the namespace
  `AlgebraicGeometry.SmallEtale`): the transpose of the counit isomorphism of Stacks 03DX (2) is
  the identity.
* `unit_comp_restrictModule_map_associatedModuleChartPushSelfChartIso_hom` (in the namespace
  `AlgebraicGeometry.Space`, written without the prefix so that it fits): **the transpose of the
  comparison at the identity chart is the transport of
  `AlgebraicGeometry.Space.chartPush_selfChart`** — that is, the comparison does nothing that the
  equality of Zariski modules it is built over does not already do.
* `unit_comp_restrictModule_map_associatedModuleChartZariskiIdealSheafSelfChartIso_hom` (same
  namespace): **the transpose of the comparison for a sheaf of ideals is the canonical sections
  map** `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush`, up to that transport, and
  `associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_comp_eqToHom` is the same with
  the transport cancelled off the right.
* `associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_val_app_apply` (same namespace):
  **the same statement on a section** — the inclusion-compatibility on sections.  A regular
  function `r` on a Zariski open `W` of the representing scheme, lying in the ideal of sections
  there, goes to `AlgebraicGeometry.Space.chartSectionsRingHom` of `r`.  That is a *ring*
  homomorphism defined on all of `Γ(A, W)`, so the comparison it describes is compatible with
  the inclusions of both sheaves of ideals into both structure sheaves — which is what the
  inclusion-compatibility asserts.

## Route

The hom-set bijection of an adjunction is `CategoryTheory.Adjunction.homEquiv`, which is
*definitionally* `f ↦ unit ≫ G.map f`; so every statement here is phrased with
`unit ≫ restrictModule.map` written out rather than through `homEquiv`, and the inputs are
`CategoryTheory.Adjunction.unit_comp_map_eq_iff`,
`CategoryTheory.Adjunction.homEquiv_naturality_left` and `CategoryTheory.eqToHom_map`.

Each geometric comparison is read in two steps: first it is identified, **as an isomorphism**,
with the composite it is defined as — that is `associatedModuleChartPushSelfChartIso_eq` and
`associatedModuleChartZariskiIdealSheafSelfChartIso_eq`, both in the namespace
`AlgebraicGeometry.Space` and both holding by `rfl` — and then the transpose of that composite is
computed by the generic lemmas.  The sections statement is read off
`AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush_hom_val_app_apply`.

## Implementation notes

**The step that decides whether this file elaborates.**  The comparison is *defined* as
`eqToIso … ≪≫ counit`, so the equation identifying it with that composite holds by `rfl`.  Asking
instead for the corresponding equation between the `hom` **components** — the same statement with
`.hom` applied to both sides — exhausts the heartbeat budget, and so does any proof that asks the
elaborator to recognise `(associatedModuleChartPushSelfChartIso …).hom` as a composite while
unifying against a lemma.  The isomorphism-level `rfl`, and the identification of
`AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso` with the counit at the same
geometric data, are together checked in under a second, while the component-level `rfl` does not
fit in 400 000 heartbeats.  The reason is the one recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPushSelfChart.lean`: projecting `hom` out of the
composite drives the elaborator into a weak-head normalisation of the chart comparison, a
four-layer composite of equivalences of sites, and that is the computation
`AlgebraicGeometry.Space.chartPush_selfChart` exists in order not to do.  So the comparison is
moved by `congrArg` **as an isomorphism**, and `hom` is applied only afterwards, inside the
generic lemmas, where the categories are variables.

For the same reason the lemmas the file rests on are proved for an **arbitrary adjunction**, not
for the associated-module adjunction of a particular scheme: a statement about the latter has to
be instantiated by ascribing geometric modules to its categories, whereas with the generic
statements every argument is fixed by unification against a goal that is already elaborated.
Three further measurements of the same shape, which is why even the formalities here are stated
generically.  The statements of all three geometric transpose lemmas elaborate in a fraction of a
second, and so does each single generic step applied to them; what does *not* fit in the budget
is a `congrArg` whose abstracted variable is a morphism of the Zariski modules, performed at the
geometric data — because `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush` is stated
at `SheafOfModules.{u} (chartScheme A).ringCatSheaf` while the adjunction's source category is
`AlgebraicGeometry.Scheme.Modules (chartScheme A)`, and the two spellings have to be reconciled
once per such abstraction.  Hence
`CategoryTheory.Adjunction.unit_comp_map_hom_of_eq_mapIso_trans_eqToIso_trans`, which composes
the two steps generically, and `CategoryTheory.comp_eqToHom_symm_of_eq_comp_eqToHom`, which does
the `eqToHom` cancellation generically.

No declaration here carries a `stacks` tag.  The transpose of the associated-module comparison is
a step of the arrow identification of Stacks 05ZB and of part (2) of Stacks 04G2, not an
assertion of either.

## What is not proved

**The same transpose written at the `definingIdealOfHom` spelling of the Zariski sheaf of
ideals.**  `AlgebraicGeometry.Space.representedSmallEtaleRestrictionDefiningIdealSheafIso` is
`AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` of the defining
ideal sheaf, read backwards and composed with the `eqToIso` of the equality of submodules
`AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_eq_definingIdealOfHom`; so its
transpose *is* the statement above instantiated at
`AlgebraicGeometry.Space.definingIdealSheaf` of the closed subspace, carried across that
equality.  **The mathematics of that version is settled**: with the generic
lemma `adj.unit.app X ≫ G.map Θ.inv = eqToHom d ≫ t` for
`Θ = j.symm ≪≫ eqToIso (congrArg F.obj d).symm` and
`t` the transpose of `j` — which is `CategoryTheory.Adjunction.homEquiv_naturality_left` after
`CategoryTheory.eqToHom_map`, three lines — the whole statement elaborates and the proof goes
through **at 4 000 000 heartbeats**, and the naming equation identifying the comparison with that
composite holds by `rfl` and is cheap.  What does not fit the 200 000 of this development is the
defeq that matches the generic conclusion against the goal, and its profile is the same
as everywhere else here: `CategoryStruct.comp` unfolded 145 251 times, with
`AlgebraicGeometry.Space.selfChart`, `CategoryTheory.Over.iteratedSliceEquiv`,
`AlgebraicGeometry.SmallEtale.opensToSmallEtale` and
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` beneath it — the normalisation of the
objects of the two small étale sites.

**None** of the following four remedies brings it inside the budget: writing every
argument of the generic lemma out, including the transpose `t`; stating the whole geometric
instance at `AlgebraicGeometry.BigFppfOver.toScheme` of `V` instead of
`AlgebraicGeometry.Space.chartScheme` of the identity chart, which is the spelling
`representedSmallEtaleRestrictionDefiningIdealSheafIso` itself is stated at; ascribing
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` to
`(CategoryTheory.SheafOfModules.unit (chartScheme (selfChart …)).ringCatSheaf).Submodule`, so
that its `toSheafOfModules` is taken at the same ambient module as the equality of submodules
takes it (the two spellings of that ambient are the mismatch the cost comes from); and
`attribute [local irreducible]` on the four site constructions above.  So this is a genuine
instance of the elaboration wall, not an open mathematical question, and the right route for a
consumer is to use the statements of this file at
`AlgebraicGeometry.Space.definingIdealSheaf` — where they are already unconditional — and to
move to `definingIdealOfHom` by the equality of submodules, which, being an equality, is
compatible with everything.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), part (2), whose counit
  isomorphism the comparisons are built from.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the
  associated-module functor and its adjunction.
* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the arrow identification
  this step feeds.
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), part (2), whose cognate
  input this is.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- **The transpose of the counit read over an equality of objects.**  If an object `X` of the
source category is *equal* to `G.obj Y`, then the morphism `F.obj X ⟶ Y` which transports along
that equality and then applies the counit has the transport itself as its transpose.

This is `CategoryTheory.Adjunction.unit_comp_map_eq_iff` together with
`CategoryTheory.eqToHom_map`.  It is the statement that makes a comparison built as the *inverse*
of a counit describable: the inverse is never computed, because what a consumer of such a
comparison needs is the transpose of its forward direction, and that is the right triangle
identity. -/
theorem unit_comp_map_eqToHom_comp_counit (adj : F ⊣ G) {X : C} {Y : D} (e : X = G.obj Y) :
    adj.unit.app X ≫ G.map (eqToHom (congrArg F.obj e) ≫ adj.counit.app Y) = eqToHom e :=
  (adj.unit_comp_map_eq_iff (eqToHom (congrArg F.obj e) ≫ adj.counit.app Y) (eqToHom e)).2
    (congrArg (fun t => t ≫ adj.counit.app Y) (eqToHom_map F e).symm)

/-- **The transpose of a counit isomorphism read over an equality of objects.**  The preceding
statement for an isomorphism `i` whose forward direction is the counit, preceded by the transport
of an equality `X = G.obj Y`.

This is the shape in which the comparisons of the small étale site are *defined*, so it is the
form a consumer meets them in.  `i` is left arbitrary with its forward direction named by a
hypothesis, rather than taken to be `CategoryTheory.asIso` of the counit, so that the geometric
instance supplies that identification separately — see the implementation notes. -/
theorem unit_comp_map_eqToIso_trans_hom (adj : F ⊣ G) {X : C} {Y : D} (e : X = G.obj Y)
    (i : F.obj (G.obj Y) ≅ Y) (hi : i.hom = adj.counit.app Y) :
    adj.unit.app X ≫ G.map (eqToIso (congrArg F.obj e) ≪≫ i).hom = eqToHom e :=
  (congrArg (fun t => adj.unit.app X ≫ G.map t)
      (congrArg (fun t => eqToHom (congrArg F.obj e) ≫ t) hi)).trans
    (adj.unit_comp_map_eqToHom_comp_counit e)

/-- **The transpose of an isomorphism which is known to be a counit over an equality of
objects.**  `CategoryTheory.Adjunction.unit_comp_map_eqToIso_trans_hom` with the composite named
by a hypothesis rather than written out.

This is the form the geometric instances use, and taking `Θ` with a hypothesis is the point: the
`congrArg` that replaces `Θ` by the composite is then performed **here**, where the two
categories are variables, instead of at the geometric instantiation, where it drives the
elaborator into a normalisation of the objects of a small étale site.  See the implementation
notes. -/
theorem unit_comp_map_hom_of_eq_eqToIso_trans (adj : F ⊣ G) {X : C} {Y : D} (e : X = G.obj Y)
    (i : F.obj (G.obj Y) ≅ Y) (hi : i.hom = adj.counit.app Y) (Θ : F.obj X ≅ Y)
    (hΘ : Θ = eqToIso (congrArg F.obj e) ≪≫ i) :
    adj.unit.app X ≫ G.map Θ.hom = eqToHom e :=
  hΘ ▸ adj.unit_comp_map_eqToIso_trans_hom e i hi

/-- **The transpose of an isomorphism which is known to factor through the left adjoint of an
isomorphism of the source category.**
`CategoryTheory.Adjunction.homEquiv_naturality_left`, with the hom-set bijection written out and
the composite named by a hypothesis rather than written out, for the same reason as the preceding
statement. -/
theorem unit_comp_map_hom_of_eq_mapIso_trans (adj : F ⊣ G) {X X' : C} {Y : D} (κ : X ≅ X')
    (j : F.obj X' ≅ Y) (Θ : F.obj X ≅ Y) (hΘ : Θ = F.mapIso κ ≪≫ j) :
    adj.unit.app X ≫ G.map Θ.hom = κ.hom ≫ (adj.unit.app X' ≫ G.map j.hom) :=
  hΘ ▸ adj.homEquiv_naturality_left κ.hom j.hom

/-- **The transpose of an isomorphism which factors through the left adjoint of an isomorphism
of the source category followed by a counit over an equality of objects.**  The composite of the
two preceding statements: the transpose is `κ.hom` followed by the transport of the equality.

This is the whole of what the geometric instance for a sheaf of ideals needs, and it is stated
generically for the reason recorded in the implementation notes — every `congrArg` carrying a
named comparison to the composite it is defined as is performed here, where the two categories
are variables. -/
theorem unit_comp_map_hom_of_eq_mapIso_trans_eqToIso_trans (adj : F ⊣ G) {X X' : C} {Y : D}
    (κ : X ≅ X') (e : X' = G.obj Y) (i : F.obj (G.obj Y) ≅ Y) (hi : i.hom = adj.counit.app Y)
    (j : F.obj X' ≅ Y) (hj : j = eqToIso (congrArg F.obj e) ≪≫ i) (Θ : F.obj X ≅ Y)
    (hΘ : Θ = F.mapIso κ ≪≫ j) :
    adj.unit.app X ≫ G.map Θ.hom = κ.hom ≫ eqToHom e :=
  (adj.unit_comp_map_hom_of_eq_mapIso_trans κ j Θ hΘ).trans
    (congrArg (fun t => κ.hom ≫ t) (adj.unit_comp_map_hom_of_eq_eqToIso_trans e i hi j hj))

/-- **Two morphisms out of a left adjoint applied to one object, with the same transpose, are
equal.**

This is injectivity of `CategoryTheory.Adjunction.homEquiv`, whose forward direction is
*definitionally* `f ↦ unit ≫ G.map f`.  It is what puts a comparison of two morphisms out of an
associated module onto the sections of the module it is associated to. -/
theorem hom_ext_of_unit_comp_map (adj : F ⊣ G) {X : C} {Y : D} {f g : F.obj X ⟶ Y}
    (h : adj.unit.app X ≫ G.map f = adj.unit.app X ≫ G.map g) : f = g :=
  (adj.homEquiv X Y).injective h

end CategoryTheory.Adjunction

namespace CategoryTheory

universe v₃ u₃

/-- **Cancelling a transport off the right of a morphism.**  If `f` is `g` followed by the
transport of an equality `e`, then `f` followed by the transport of `e.symm` is `g`.

A formality, stated separately because the two morphisms the geometric instances below feed it
live in two definitionally equal but differently written spellings of one category of sheaves of
modules, and doing the `eqToHom` arithmetic there rather than here is what puts it over the
heartbeat budget. -/
theorem comp_eqToHom_symm_of_eq_comp_eqToHom {C : Type u₃} [Category.{v₃} C] {X Y Z : C}
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Z = Y) (h : f = g ≫ eqToHom e) :
    f ≫ eqToHom e.symm = g :=
  (congrArg (fun t => t ≫ eqToHom e.symm) h).trans
    ((Category.assoc g (eqToHom e) (eqToHom e.symm)).trans
      ((congrArg (fun t => g ≫ t) ((eqToHom_trans e e.symm).trans (eqToHom_refl Z _))).trans
        (Category.comp_id g)))

end CategoryTheory


namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The counit isomorphism of Stacks 03DX (2) is the counit**, by `rfl`:
`AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso` is `CategoryTheory.asIso` of the
counit of `AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`. -/
theorem associatedModuleRestrictModuleIso_hom
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    (associatedModuleRestrictModuleIso B S hS G hG).hom =
      (associatedModuleAdjunction B S hS).counit.app G :=
  rfl

/-- **The transpose of the counit isomorphism of the associated-module adjunction is the
identity.**  For a quasi-coherent `𝒪`-module `G` on the small étale site of a scheme, the unit of
the adjunction at the Zariski restriction of `G`, followed by the restriction of
`AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso`, is the identity.

This is the right triangle identity of
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`, and it is the reason a comparison
assembled from the *inverse* of that counit still has a description on Zariski sections. -/
theorem unit_comp_restrictModule_map_associatedModuleRestrictModuleIso_hom
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    (associatedModuleAdjunction B S hS).unit.app ((restrictModule B S hS).obj G) ≫
        (restrictModule B S hS).map (associatedModuleRestrictModuleIso B S hS G hG).hom =
      CategoryStruct.id ((restrictModule B S hS).obj G) :=
  (associatedModuleAdjunction B S hS).right_triangle_components G

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)

/-! ### The comparison at the identity chart -/

/-- **The comparison at the identity chart is the counit read over
`AlgebraicGeometry.Space.chartPush_selfChart`**, by `rfl`: that is how
`AlgebraicGeometry.Space.associatedModuleChartPushSelfChartIso` is defined.

Stated as an equality of *isomorphisms*, which is what makes it cheap; see the implementation
notes for why the corresponding equality of `hom` components is not. -/
theorem associatedModuleChartPushSelfChartIso_eq
    (M : SheafOfModules.{u} (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩))
    (hM : M.IsQuasicoherentOnSite) :
    associatedModuleChartPushSelfChartIso B S hS V M hM =
      eqToIso (congrArg
          (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              (chartScheme (selfChart B S hS V))
              (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                (selfChart B S hS V)).left.property).obj
          (chartPush_selfChart B S hS V M)) ≪≫
        _root_.AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso
          (associatedBigEtaleSite B) (chartScheme (selfChart B S hS V))
          (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V)).left.property
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M)
          (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse B S hS V M hM) :=
  rfl

/-- **The transpose of the comparison at the identity chart.**  For a quasi-coherent `𝒪`-module
`M` on the small étale site of a representable algebraic space, the unit of the associated-module
adjunction at the Zariski chart restriction of `M`, followed by the restriction of
`AlgebraicGeometry.Space.associatedModuleChartPushSelfChartIso`, is the transport `eqToHom` of
`AlgebraicGeometry.Space.chartPush_selfChart`.

So the comparison — which is built from the *inverse* of the counit of the associated-module
adjunction, and has no description of its own values — does, after transposition, nothing beyond
that equality of Zariski modules: the chart restriction at the identity chart *is* the Zariski
restriction of the module read on the representing scheme's small étale site. -/
theorem unit_comp_restrictModule_map_associatedModuleChartPushSelfChartIso_hom
    (M : SheafOfModules.{u} (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩))
    (hM : M.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
            (chartScheme (selfChart B S hS V))
            (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
              (selfChart B S hS V)).left.property).unit.app
          (chartPush B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ M
            (selfChart B S hS V)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme (selfChart B S hS V))
            (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
              (selfChart B S hS V)).left.property).map
          (associatedModuleChartPushSelfChartIso B S hS V M hM).hom =
      eqToHom (chartPush_selfChart B S hS V M) :=
  CategoryTheory.Adjunction.unit_comp_map_hom_of_eq_eqToIso_trans
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property)
    (chartPush_selfChart B S hS V M)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso
      (associatedBigEtaleSite B) (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M)
      (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse B S hS V M hM))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso_hom
      (associatedBigEtaleSite B) (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M)
      (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse B S hS V M hM))
    (associatedModuleChartPushSelfChartIso B S hS V M hM)
    (associatedModuleChartPushSelfChartIso_eq B S hS V M hM)

/-! ### Comparing a sheaf of ideals with the associated module of its Zariski restriction -/

/-- **The comparison for a sheaf of ideals is the associated module of the Zariski comparison
followed by the comparison at the identity chart**, by `rfl`: that is how
`AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` is defined.

Like `AlgebraicGeometry.Space.associatedModuleChartPushSelfChartIso_eq` this is an equality of
*isomorphisms*; see the implementation notes.  The associated-module functor is written here at
the chart's own scheme `AlgebraicGeometry.Space.chartScheme` rather than at
`AlgebraicGeometry.BigFppfOver.toScheme` of `V`, which is the spelling the definition uses: the
two are definitionally equal, and this is the spelling the lemmas below are stated at. -/
theorem associatedModuleChartZariskiIdealSheafSelfChartIso_eq
    (N : (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite) :
    associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            (chartScheme (selfChart B S hS V))
            (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
              (selfChart B S hS V)).left.property).mapIso
          (chartZariskiIdealSheafIsoChartPush B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V)) ≪≫
        associatedModuleChartPushSelfChartIso B S hS V N.toSheafOfModules hN :=
  rfl

/-- **The transpose of the comparison of a sheaf of ideals with the associated module of its
Zariski restriction is the canonical sections map.**  For a sheaf of ideals `N ⊆ 𝒪` on the small
étale site of a representable algebraic space, quasi-coherent on the site, the unit of the
associated-module adjunction at the Zariski restriction of `N`, followed by the restriction of
`AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso`, is
`AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush` — the comparison of scalars
`AlgebraicGeometry.Space.chartSectionsRingHom` read on sections — followed by the transport of
`AlgebraicGeometry.Space.chartPush_selfChart`.

This is the inclusion-compatibility that the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiDefiningIdeal.lean` names as absent, in
the form in which it is usable: the comparison is built from the inverse of a counit and cannot
describe its own values, but a morphism out of an associated module is determined by its
transpose, and the transpose is a morphism of modules on the small Zariski site given on sections
by a *ring* isomorphism.  Being a ring map it is compatible with the inclusions of both sheaves
of ideals into both structure sheaves, which is what the inclusion-compatibility asserts. -/
theorem unit_comp_restrictModule_map_associatedModuleChartZariskiIdealSheafSelfChartIso_hom
    (N : (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
            (chartScheme (selfChart B S hS V))
            (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
              (selfChart B S hS V)).left.property).unit.app
          (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
            (selfChart B S hS V)).toSheafOfModules ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme (selfChart B S hS V))
            (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
              (selfChart B S hS V)).left.property).map
          (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN).hom =
      (chartZariskiIdealSheafIsoChartPush B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V)).hom ≫
        eqToHom (chartPush_selfChart B S hS V N.toSheafOfModules) :=
  CategoryTheory.Adjunction.unit_comp_map_hom_of_eq_mapIso_trans_eqToIso_trans
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property)
    (chartZariskiIdealSheafIsoChartPush B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V))
    (chartPush_selfChart B S hS V N.toSheafOfModules)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso
      (associatedBigEtaleSite B) (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj N.toSheafOfModules)
      (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse B S hS V
        N.toSheafOfModules hN))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso_hom
      (associatedBigEtaleSite B) (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj N.toSheafOfModules)
      (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse B S hS V
        N.toSheafOfModules hN))
    (associatedModuleChartPushSelfChartIso B S hS V N.toSheafOfModules hN)
    (associatedModuleChartPushSelfChartIso_eq B S hS V N.toSheafOfModules hN)
    (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN)
    (associatedModuleChartZariskiIdealSheafSelfChartIso_eq B S hS V N hN)

/-- **The transpose of the comparison, read back at the chart restriction, is exactly the
canonical sections map.**  The preceding statement with the transport of
`AlgebraicGeometry.Space.chartPush_selfChart` cancelled off the right, so that the target is the
chart restriction `AlgebraicGeometry.Space.chartPush` in the spelling whose sections over a
Zariski open are the sections of the sheaf of ideals over the étale chart which that open cuts
out. -/
theorem associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_comp_eqToHom
    (N : (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite) :
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
              (chartScheme (selfChart B S hS V))
              (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                (selfChart B S hS V)).left.property).unit.app
            (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
              (selfChart B S hS V)).toSheafOfModules ≫
          (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              (chartScheme (selfChart B S hS V))
              (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                (selfChart B S hS V)).left.property).map
            (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN).hom) ≫
        eqToHom (chartPush_selfChart B S hS V N.toSheafOfModules).symm =
      (chartZariskiIdealSheafIsoChartPush B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V)).hom :=
  CategoryTheory.comp_eqToHom_symm_of_eq_comp_eqToHom _
    (chartZariskiIdealSheafIsoChartPush B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V)).hom
    (chartPush_selfChart B S hS V N.toSheafOfModules)
    (unit_comp_restrictModule_map_associatedModuleChartZariskiIdealSheafSelfChartIso_hom
      B S hS V N hN)

/-- **The inclusion-compatibility on sections.**  A regular function `r` on a Zariski open `W` of
the representing scheme, lying in the ideal of sections there of the Zariski restriction of a
quasi-coherent sheaf of ideals `N`, is carried by the transpose of
`AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` to
`AlgebraicGeometry.Space.chartSectionsRingHom` of `r` — the comparison of scalars of the chart,
which is the section of `N` over the étale chart which `W` cuts out that `r` corresponds to by
`AlgebraicGeometry.Space.mem_chartZariskiIdealSheaf_iff`.

This is the sections description that the comparison itself does not have, and it is compatible
with the inclusions into the two structure sheaves because
`AlgebraicGeometry.Space.chartSectionsRingHom` is a ring homomorphism defined on all of
`Γ(A, W)`: the statement is an equation between the *underlying regular functions*, the `.1` of
each side being taken in the sections of the structure sheaf. -/
theorem associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_val_app_apply
    (N : (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite)
    (W : (chartScheme (selfChart B S hS V)).Opens)
    (r : (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
      (selfChart B S hS V)).toSheafOfModules.val.obj (op W)) :
    (((((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
                  (associatedBigEtaleSite B) (chartScheme (selfChart B S hS V))
                  (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                    (selfChart B S hS V)).left.property).unit.app
                (chartZariskiIdealSheaf B S hS
                  ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
                  (selfChart B S hS V)).toSheafOfModules ≫
              (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  (chartScheme (selfChart B S hS V))
                  (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
                    (selfChart B S hS V)).left.property).map
                (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN).hom) ≫
            eqToHom (chartPush_selfChart B S hS V N.toSheafOfModules).symm).val.app (op W)) r).1 =
      chartSectionsRingHom B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V) W r.1 :=
  (congrArg (fun m => ((m.val.app (op W)) r).1)
      (associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_comp_eqToHom
        B S hS V N hN)).trans
    (chartZariskiIdealSheafIsoChartPush_hom_val_app_apply B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V) W r)

end AlgebraicGeometry.Space

end
