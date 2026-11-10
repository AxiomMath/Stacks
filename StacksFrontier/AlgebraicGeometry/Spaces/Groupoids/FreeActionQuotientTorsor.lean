module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotientChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelationSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TwistedLineQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCoproduct

/-!
# The chart of a free-action quotient is a torsor in the spaces-étale site of the quotient

Let a group `G` act freely on an object `V` of a big fppf site over a scheme `S`. The chart
`h_V ⟶ V/G` is an object of the spaces-étale site of the quotient, by
`AlgebraicGeometry.Space.freeActionQuotientChart`. This file assembles, inside that site, the
data `CategoryTheory.IsTorsorObject` asks for: the action of `G` by automorphisms of the
chart, the kernel pair of the chart with its `G` copies of the chart, and the two freeness
inputs.

The geometric content comes from one square,
`AlgebraicGeometry.Space.isPullback_freeActionQuotientMap`, which exhibits the kernel pair of
the chart as the disjoint union of one copy of `V` per group element — a square of presheaves
on the big fppf site, which has to be moved into the small site — together with the
factorization of a one-point source through a single summand of that union.

## Main definitions

* `AlgebraicGeometry.Space.freeActionChartMap` is the automorphism of the chart attached to a
  group element, and `AlgebraicGeometry.Space.freeActionChartAut` the resulting action of `G`
  by automorphisms of the chart in the spaces-étale site of the quotient.
* `AlgebraicGeometry.Space.freeActionRelationChart` is the kernel pair of the chart as an
  object of that site, with `AlgebraicGeometry.Space.freeActionRelationFst` and
  `AlgebraicGeometry.Space.freeActionRelationSnd` its two projections, and
  `AlgebraicGeometry.Space.freeActionChartSummand` the copy of the chart inside it indexed by
  a group element.

## Main results

* `AlgebraicGeometry.Space.siteActionRelationInclusion_comp_target`: the target map of the
  graph relation restricted to the summand indexed by `g` is the automorphism of the site
  realizing `g`, in the site rather than on underlying schemes.
* `AlgebraicGeometry.Space.siteActionHom_comp_freeActionQuotientMap`: **the chart is invariant
  under the action**, which is what makes the action an action on the chart as an object over
  the quotient.
* `AlgebraicGeometry.Space.isPullback_freeActionRelationChart`: **the kernel pair of the chart
  over the final object of the small site**.
* `AlgebraicGeometry.Space.summandSieve_mem_freeActionRelationChart`: **the `G` copies of the
  chart inside the kernel pair are disjoint as the topology sees it** — every morphism into
  the kernel pair factors through one of them locally on its source.
* `AlgebraicGeometry.Space.eq_one_of_comp_freeActionChartAut` and
  `AlgebraicGeometry.Space.nonempty_points_of_bot_notMem_topology`: the action is free on the
  morphisms out of an object with a point, and the objects the empty sieve does not cover have
  a point.
* `AlgebraicGeometry.Space.isTorsorObject_freeActionChartAut`: **the chart `h_V ⟶ V/G` is a
  `G`-torsor over the final object of the spaces-étale site of the quotient**, which is the
  hypothesis [Stacks, Tag 0727] makes about the pair `(W_p, U_p)`.

## Implementation notes

The automorphism of `V` realizing a group element is
`AlgebraicGeometry.Space.siteActionHom`, the preimage of the acting automorphism under the
fully faithful inclusion of the site into the schemes over `S`. Its multiplicativity is
proved here by faithfulness of that inclusion from
`AlgebraicGeometry.Space.post_map_siteActionHom`; note that `CategoryTheory.Aut` multiplies by
`CategoryTheory.Iso.trans` in the opposite order
(`CategoryTheory.Aut_mul_def`), so composing the morphism of `g` with the morphism of `h`
gives the morphism of `h * g`.

Invariance of the chart is deduced from the kernel-pair square rather than from
`AlgebraicGeometry.Space.siteActionHom_comp_actionProjection`, which says the same thing for
`AlgebraicGeometry.Space.actionProjection`: that morphism and
`AlgebraicGeometry.Space.freeActionQuotientMap` are two unbridged presentations of the chart,
the first as the composite of the Yoneda comparison with the map to the quotient sheaf and the
second as `AlgebraicGeometry.Space.quotientMap` of the graph relation, and the kernel-pair
route needs no bridge.

Moving the kernel-pair square into the small site is three applications of
`CategoryTheory.IsPullback.of_map_of_faithful`, along the full subcategory of algebraic spaces
inside presheaves, the forgetful functor of the slice over the quotient, and the inclusion of
the small site into that slice; each is faithful and reflects fibre products.

Local disjointness of the copies needs no extension of
`AlgebraicGeometry.Space.SpacesEtale.ofArrows_mem_topology_of_isColimit_cofan` from binary to
`G`-indexed coproducts. Covering sieves of the spaces-étale site are characterized pointwise
by `AlgebraicGeometry.Space.SpacesEtale.mem_topology_iff_sievePointwiseCover`; a point is a
field-valued point, whose source has one point and therefore factors through a single summand
by `AlgebraicGeometry.Space.exists_sigmaι_factorization_actionRelationScheme`; and the arrow
of the sieve realizing it is the fibre product of the given morphism with that summand, taken
inside the small site, whose points lift by [Stacks, Tag 03H4].

## References

* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- Two morphisms of the spaces-étale site are equal when their underlying morphisms of
presheaves are. -/
private theorem spacesEtale_hom_ext {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} {A A' : SpacesEtale B S hS X} {f f' : A ⟶ A'}
    (h : f.hom.left.hom = f'.hom.left.hom) : f = f' :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ h))

variable (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))

/-! ### The automorphism of the site realizing a group element -/

omit [Small.{u, v} G] [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The automorphism of the site realizing the identity is the identity. -/
theorem siteActionHom_one : siteActionHom G B hS V a 1 = 𝟙 V :=
  (Over.post (X := B.obj hS) B.inclusion).map_injective <| by
    rw [post_map_siteActionHom, map_one, CategoryTheory.Functor.map_id]
    rfl

omit [Small.{u, v} G] [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The automorphisms of the site realizing two group elements compose to the automorphism
realizing their product, in the order `CategoryTheory.Aut` multiplies in. -/
theorem siteActionHom_comp (g h : G) :
    siteActionHom G B hS V a g ≫ siteActionHom G B hS V a h =
      siteActionHom G B hS V a (h * g) :=
  (Over.post (X := B.obj hS) B.inclusion).map_injective <| by
    rw [CategoryTheory.Functor.map_comp, post_map_siteActionHom, post_map_siteActionHom,
      post_map_siteActionHom, map_mul, Aut.mul_asIso]
    rfl

variable (hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The target map of the graph relation of a group action, restricted to the summand indexed
by `g`, is the automorphism of the site realizing `g`.** This is
`AlgebraicGeometry.Space.toScheme_map_siteActionRelationInclusion_comp_target` read inside the
site, which faithfulness of the functor to schemes allows. -/
theorem siteActionRelationInclusion_comp_target (g : G) :
    siteActionRelationInclusion G B hS V hR g ≫ siteActionRelationTarget G B hS V hR a =
      siteActionHom G B hS V a g :=
  (BigFppfOver.toScheme B S hS).map_injective <|
    (toScheme_map_siteActionRelationInclusion_comp_target G B hS V hR a g).trans
      (congrArg Over.Hom.left (post_map_siteActionHom G B hS V a g)).symm

/-! ### The action of the group on the chart -/

variable (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a)

/-- **The chart of the quotient by a free action is invariant under the action.** The kernel
pair of the chart is the disjoint union of one copy of `V` per group element, so the two
projections become equal after the chart; restricted to the summand indexed by `g` the first
projection is the identity and the second is the automorphism realizing `g`. -/
theorem siteActionHom_comp_freeActionQuotientMap (g : G) :
    yoneda.map (siteActionHom G B hS V a g) ≫ freeActionQuotientMap G B S hS V a ha =
      freeActionQuotientMap G B S hS V a ha := by
  have hR := contains_actionRelationScheme_of_actsFreely G B S hS V a ha
  have hw := (isPullback_freeActionQuotientMap G B S hS V a ha).w
  have h := congrArg
    (fun k => yoneda.map (siteActionRelationInclusion G B hS V hR g) ≫ k) hw
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    siteActionRelationInclusion_comp_target G B S hS V a hR g,
    siteActionRelationInclusion_comp_source G B hS V hR g, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  exact h

/-- The automorphism of the chart `h_V ⟶ V/G` attached to a group element: the automorphism of
`V` realizing it, which is a morphism over the quotient because the chart is invariant. -/
def freeActionChartMap (g : G) :
    freeActionQuotientChart G B S hS V a ha ⟶ freeActionQuotientChart G B S hS V a ha :=
  ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (yoneda.map (siteActionHom G B hS V a g)) :
      siteObjectSpace B S hS V ⟶ siteObjectSpace B S hS V)
    (ObjectProperty.hom_ext _ (siteActionHom_comp_freeActionQuotientMap G B S hS V a ha g)))

/-- The underlying morphism of presheaves of the automorphism of the chart attached to `g` is
the image under the Yoneda embedding of the automorphism of `V` realizing `g`. -/
@[simp]
theorem freeActionChartMap_hom (g : G) :
    ((freeActionChartMap G B S hS V a ha g).hom.left).hom =
      yoneda.map (siteActionHom G B hS V a g) :=
  rfl

/-- The automorphism of the chart attached to the identity is the identity. -/
theorem freeActionChartMap_one : freeActionChartMap G B S hS V a ha 1 = 𝟙 _ :=
  spacesEtale_hom_ext (by
    rw [freeActionChartMap_hom, siteActionHom_one, CategoryTheory.Functor.map_id]
    rfl)

/-- The automorphisms of the chart attached to two group elements compose to the automorphism
attached to their product, in the order `CategoryTheory.Aut` multiplies in. -/
theorem freeActionChartMap_comp (g h : G) :
    freeActionChartMap G B S hS V a ha g ≫ freeActionChartMap G B S hS V a ha h =
      freeActionChartMap G B S hS V a ha (h * g) :=
  spacesEtale_hom_ext (by
    change yoneda.map (siteActionHom G B hS V a g) ≫
      yoneda.map (siteActionHom G B hS V a h) = _
    rw [← CategoryTheory.Functor.map_comp, siteActionHom_comp]
    rfl)

/-- **The action of `G` by automorphisms of the chart `h_V ⟶ V/G` inside the spaces-étale site
of the quotient.** This is the datum of which [Stacks, Tag 0727] asks that the chart be a
torsor. -/
def freeActionChartAut : G →* Aut (freeActionQuotientChart G B S hS V a ha) where
  toFun g :=
    Aut.of
      { hom := freeActionChartMap G B S hS V a ha g
        inv := freeActionChartMap G B S hS V a ha g⁻¹
        hom_inv_id := by
          rw [freeActionChartMap_comp, inv_mul_cancel, freeActionChartMap_one]
        inv_hom_id := by
          rw [freeActionChartMap_comp, mul_inv_cancel, freeActionChartMap_one] }
  map_one' := Aut.ext (Iso.ext (freeActionChartMap_one G B S hS V a ha))
  map_mul' g h := Aut.ext (Iso.ext (freeActionChartMap_comp G B S hS V a ha h g).symm)

/-- The automorphism of the chart attached to `g` by `freeActionChartAut` has underlying
morphism `freeActionChartMap g`. -/
@[simp]
theorem freeActionChartAut_hom (g : G) :
    (freeActionChartAut G B S hS V a ha g).asIso.hom = freeActionChartMap G B S hS V a ha g :=
  rfl

/-! ### The kernel pair of the chart, inside the small site of the quotient -/

/-- The relation scheme of a free action — the disjoint union of one copy of `V` per group
element — as an algebraic space over `S`. -/
def freeActionRelationSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (siteActionRelationScheme G B hS V
      (contains_actionRelationScheme_of_actsFreely G B S hS V a ha)),
    isAlgebraicSpace_yoneda B S hS _⟩

/-- The target map of the graph relation, as a morphism of algebraic spaces over `S`: the
first projection of the kernel pair of the chart. -/
def freeActionRelationSpaceFst :
    freeActionRelationSpace G B S hS V a ha ⟶ siteObjectSpace B S hS V :=
  ObjectProperty.homMk (yoneda.map (siteActionRelationTarget G B hS V
    (contains_actionRelationScheme_of_actsFreely G B S hS V a ha) a))

/-- The source map of the graph relation, as a morphism of algebraic spaces over `S`: the
second projection of the kernel pair of the chart. -/
def freeActionRelationSpaceSnd :
    freeActionRelationSpace G B S hS V a ha ⟶ siteObjectSpace B S hS V :=
  ObjectProperty.homMk (yoneda.map (siteActionRelationSource G B hS V
    (contains_actionRelationScheme_of_actsFreely G B S hS V a ha)))

/-- **The graph relation of a free action is the kernel pair of the chart**, as a square of
algebraic spaces over `S` rather than of presheaves. -/
theorem isPullback_freeActionRelationSpace :
    IsPullback (freeActionRelationSpaceFst G B S hS V a ha)
      (freeActionRelationSpaceSnd G B S hS V a ha)
      (freeActionQuotientSpaceMap G B S hS V a ha)
      (freeActionQuotientSpaceMap G B S hS V a ha) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    (isPullback_freeActionQuotientMap G B S hS V a ha)

/-- The second projection of the kernel pair of the chart is étale: it is a base change of
the chart, which is étale. -/
theorem isEtale_freeActionRelationSpaceSnd :
    IsEtale B S hS (freeActionRelationSpaceSnd G B S hS V a ha).hom :=
  isEtale_of_isPullback B S hS _ _ _ _
    (isPullback_freeActionRelationSpace G B S hS V a ha)
    (isEtale_freeActionQuotientMap G B S hS V a ha)

/-- **The graph relation of a free action, as an object of the spaces-étale site of the
quotient**: it is étale over the quotient because it is étale over the chart, which is étale
over the quotient. -/
def freeActionRelationChart : SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha) :=
  ⟨Over.mk (freeActionRelationSpaceSnd G B S hS V a ha ≫
      freeActionQuotientSpaceMap G B S hS V a ha),
    isEtale_comp B S hS (isEtale_freeActionRelationSpaceSnd G B S hS V a ha)
      (isEtale_freeActionQuotientMap G B S hS V a ha)⟩

/-- The first projection of the kernel pair of the chart, as a morphism of the spaces-étale
site of the quotient. -/
def freeActionRelationFst :
    freeActionRelationChart G B S hS V a ha ⟶ freeActionQuotientChart G B S hS V a ha :=
  ObjectProperty.homMk (Over.homMk (freeActionRelationSpaceFst G B S hS V a ha)
    (isPullback_freeActionRelationSpace G B S hS V a ha).w)

/-- The second projection of the kernel pair of the chart, as a morphism of the spaces-étale
site of the quotient. -/
def freeActionRelationSnd :
    freeActionRelationChart G B S hS V a ha ⟶ freeActionQuotientChart G B S hS V a ha :=
  ObjectProperty.homMk (Over.homMk (freeActionRelationSpaceSnd G B S hS V a ha) rfl)

/-- **The kernel pair of the chart `h_V ⟶ V/G`, inside the spaces-étale site of the
quotient.** The chart's morphism to the final object of that site is its structure morphism
to the quotient, so this is the square of
`AlgebraicGeometry.Space.isPullback_freeActionRelationSpace` reflected through the inclusion
of the site into the slice over the quotient and the forgetful functor of that slice, both of
which are faithful and reflect fibre products. -/
theorem isPullback_freeActionRelationChart :
    IsPullback (freeActionRelationFst G B S hS V a ha)
      (freeActionRelationSnd G B S hS V a ha)
      (SpacesEtale.toFinal B S hS (freeActionQuotientChart G B S hS V a ha))
      (SpacesEtale.toFinal B S hS (freeActionQuotientChart G B S hS V a ha)) :=
  IsPullback.of_map_of_faithful
    (SpacesEtale.inclusion B S hS (actionQuotientSpace G B S hS V a ha))
    (IsPullback.of_map_of_faithful (Over.forget (actionQuotientSpace G B S hS V a ha))
      (isPullback_freeActionRelationSpace G B S hS V a ha))

/-! ### The copies of the chart inside the kernel pair, and their local disjointness -/

section Summand

omit [Group G] [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The summand inclusion of the relation scheme, read under the inclusion of the site into
the schemes over `S`, is the summand inclusion of the coproduct. -/
theorem post_map_siteActionRelationInclusion (g : G) :
    (Over.post (X := B.obj hS) B.inclusion).map
        (siteActionRelationInclusion G B hS V hR g) =
      Sigma.ι (fun _ : G ↦ underlyingOver B hS V) g :=
  Over.OverMorphism.ext rfl

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **Every point of the relation scheme of a group action lies in one summand.** A point is
a section over a field spectrum, whose source has exactly one point, so it factors through
the copy of `V` indexed by a single group element — which on points says the summand
inclusions are jointly surjective. -/
theorem exists_pointsMap_siteActionRelationInclusion_eq
    (r : points B S hS (yoneda.obj (siteActionRelationScheme G B hS V hR))) :
    ∃ (g : G) (y : points B S hS (yoneda.obj V)),
      pointsMap B S hS (yoneda.obj V)
        (yoneda.map (siteActionRelationInclusion G B hS V hR g)) y = r := by
  classical
  obtain ⟨q, rfl⟩ := Quot.exists_rep r
  obtain ⟨g, w, hw⟩ := exists_sigmaι_factorization_actionRelationScheme
    (underlyingOver B hS V) G
    (inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier) : Type u)))
    (IsLocalRing.closedPoint q.carrier)
    ((Over.post (X := B.obj hS) B.inclusion).map
      (q.value : q.siteObject ⟶ siteActionRelationScheme G B hS V hR))
  set w' := (Over.post (X := B.obj hS) B.inclusion).preimage w with hw'def
  have hwmap : (Over.post (X := B.obj hS) B.inclusion).map w' = w :=
    (Over.post (X := B.obj hS) B.inclusion).map_preimage w
  have hvalue : w' ≫ siteActionRelationInclusion G B hS V hR g = q.value :=
    (Over.post (X := B.obj hS) B.inclusion).map_injective (by
      rw [CategoryTheory.Functor.map_comp, hwmap,
        post_map_siteActionRelationInclusion G B S hS V hR g]
      exact hw.symm)
  refine ⟨g, (⟨q.carrier, q.contained, q.toBase, w'⟩ :
    FieldValuedPoint B S hS (yoneda.obj V)).class B S hS _, ?_⟩
  rw [pointsMap_class]
  exact congrArg (Quot.mk _) (congrArg
    (fun v ↦ (⟨q.carrier, q.contained, q.toBase, v⟩ :
      FieldValuedPoint B S hS (yoneda.obj (siteActionRelationScheme G B hS V hR)))) hvalue)

end Summand

/-- The copy of the chart inside the kernel pair indexed by a group element: the summand of
the relation scheme indexed by it, which lies over the quotient because the source map of the
relation is the identity on that summand. -/
def freeActionChartSummand (g : G) :
    freeActionQuotientChart G B S hS V a ha ⟶ freeActionRelationChart G B S hS V a ha :=
  ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (yoneda.map (siteActionRelationInclusion G B hS V
        (contains_actionRelationScheme_of_actsFreely G B S hS V a ha) g)) :
      siteObjectSpace B S hS V ⟶ freeActionRelationSpace G B S hS V a ha)
    (ObjectProperty.hom_ext _ (by
      change yoneda.map (siteActionRelationInclusion G B hS V _ g) ≫
        yoneda.map (siteActionRelationSource G B hS V _) ≫
          freeActionQuotientMap G B S hS V a ha = _
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
        siteActionRelationInclusion_comp_source, CategoryTheory.Functor.map_id,
        Category.id_comp]
      rfl)))

/-- The underlying morphism of presheaves of the copy of the chart indexed by `g` is the image
under the Yoneda embedding of the inclusion of the summand of the relation scheme indexed by
`g`. -/
@[simp]
theorem freeActionChartSummand_hom (g : G) :
    ((freeActionChartSummand G B S hS V a ha g).hom.left).hom =
      yoneda.map (siteActionRelationInclusion G B hS V
        (contains_actionRelationScheme_of_actsFreely G B S hS V a ha) g) :=
  rfl

/-- Each copy of the chart inside the kernel pair splits the second projection: the source
map of the relation is the identity on every summand. -/
theorem freeActionChartSummand_comp_snd (g : G) :
    freeActionChartSummand G B S hS V a ha g ≫ freeActionRelationSnd G B S hS V a ha =
      𝟙 _ :=
  spacesEtale_hom_ext (by
    change yoneda.map (siteActionRelationInclusion G B hS V _ g) ≫
      yoneda.map (siteActionRelationSource G B hS V _) = _
    rw [← CategoryTheory.Functor.map_comp, siteActionRelationInclusion_comp_source,
      CategoryTheory.Functor.map_id]
    rfl)

/-- On the copy of the chart indexed by `g` the first projection of the kernel pair is the
automorphism of the chart attached to `g`: the target map of the relation restricted to that
summand is the automorphism realizing `g`. -/
theorem freeActionChartSummand_comp_fst (g : G) :
    freeActionChartSummand G B S hS V a ha g ≫ freeActionRelationFst G B S hS V a ha =
      freeActionChartMap G B S hS V a ha g :=
  spacesEtale_hom_ext (by
    change yoneda.map (siteActionRelationInclusion G B hS V _ g) ≫
      yoneda.map (siteActionRelationTarget G B hS V _ a) = _
    rw [← CategoryTheory.Functor.map_comp, siteActionRelationInclusion_comp_target]
    rfl)

/-- **The copies of the chart inside the kernel pair are disjoint as the topology sees it**:
every morphism into the kernel pair factors through one of them locally on its source.

This is the one condition of `CategoryTheory.translationSieve_mem_of_isPullback` with content.
Pointwise it is the factorization of a field-valued point of the relation scheme through a
single summand, and the member of the sieve realizing it is the fibre product, inside the
small site, of the given morphism with that summand. -/
theorem summandSieve_mem_freeActionRelationChart
    {A : SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha)}
    (d : A ⟶ freeActionRelationChart G B S hS V a ha) :
    summandSieve (freeActionChartSummand G B S hS V a ha) d ∈
      SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha) A := by
  classical
  rw [SpacesEtale.mem_topology_iff_sievePointwiseCover]
  intro x
  obtain ⟨g, y, hy⟩ := exists_pointsMap_siteActionRelationInclusion_eq G B S hS V
    (contains_actionRelationScheme_of_actsFreely G B S hS V a ha)
    (pointsMap B S hS
      ((SpacesEtale.toSpaces B S hS (actionQuotientSpace G B S hS V a ha)).obj A).1
      ((SpacesEtale.toSpaces B S hS (actionQuotientSpace G B S hS V a ha)).map d).hom x)
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS
    ((IsPullback.of_hasPullback d (freeActionChartSummand G B S hS V a ha g)).map
      (SpacesEtale.toSpaces B S hS (actionQuotientSpace G B S hS V a ha))) x y hy.symm
  exact ⟨Limits.pullback d (freeActionChartSummand G B S hS V a ha g),
    Limits.pullback.fst d (freeActionChartSummand G B S hS V a ha g),
    ⟨g, Limits.pullback.snd d (freeActionChartSummand G B S hS V a ha g),
      Limits.pullback.condition⟩, w, hw⟩

/-! ### Freeness of the action against the objects with a point -/

/-- The automorphism of the chart attached to `g`, as a morphism of algebraic spaces, is the
image under the Yoneda embedding of the automorphism of `V` realizing `g`. -/
@[simp]
theorem toSpaces_map_freeActionChartMap (g : G) :
    ((SpacesEtale.toSpaces B S hS (actionQuotientSpace G B S hS V a ha)).map
        (freeActionChartMap G B S hS V a ha g)).hom =
      yoneda.map (siteActionHom G B hS V a g) :=
  rfl

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **An object of the spaces-étale site that the empty sieve does not cover has a point.**
This is the contrapositive of `AlgebraicGeometry.Space.SpacesEtale.bot_mem_topology`: the
empty family is jointly surjective over an object with no points. -/
theorem nonempty_points_of_bot_notMem_topology (X : AlgebraicSpaces B S hS)
    (A : SpacesEtale B S hS X) (h : (⊥ : Sieve A) ∉ SpacesEtale.topology B S hS X A) :
    Nonempty (points B S hS ((SpacesEtale.toSpaces B S hS X).obj A).obj) := by
  by_contra hne
  exact h (SpacesEtale.bot_mem_topology B S hS X A (not_nonempty_iff.1 hne))

/-- **The action of `G` on the chart is free on the morphisms out of an object with a
point.** A point of the source is a section over a field spectrum in the site, and the
morphism to the chart carries it to a morphism from that spectrum to `V` which the group
element fixes; the spectrum of a field has a point, so freeness of the action in the sense of
[Stacks, Tag 071S] applies. -/
theorem eq_one_of_comp_freeActionChartAut
    {A : SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha)}
    (hA : Nonempty (points B S hS
      ((SpacesEtale.toSpaces B S hS (actionQuotientSpace G B S hS V a ha)).obj A).obj))
    (φ : A ⟶ freeActionQuotientChart G B S hS V a ha) (g : G)
    (hg : φ ≫ (freeActionChartAut G B S hS V a ha g).asIso.hom = φ) :
    g = 1 := by
  classical
  obtain ⟨x⟩ := hA
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hval := congrArg (fun k : A ⟶ freeActionQuotientChart G B S hS V a ha ↦
    (((SpacesEtale.toSpaces B S hS (actionQuotientSpace G B S hS V a ha)).map k).hom).app
      (Opposite.op p.siteObject) p.value) hg
  set m : p.siteObject ⟶ V := (((SpacesEtale.toSpaces B S hS
    (actionQuotientSpace G B S hS V a ha)).map φ).hom).app (Opposite.op p.siteObject) p.value
    with hmdef
  have hfix : m ≫ siteActionHom G B hS V a g = m := by
    rw [hmdef]
    exact hval
  have key : (Over.post (X := B.obj hS) B.inclusion).map
        (m ≫ siteActionHom G B hS V a g) =
      (Over.post (X := B.obj hS) B.inclusion).map m := congrArg _ hfix
  rw [CategoryTheory.Functor.map_comp, post_map_siteActionHom] at key
  have h1 : ((1 : Aut (underlyingOver B hS V))).asIso.hom = 𝟙 (underlyingOver B hS V) := rfl
  refine ha ((Over.post (X := B.obj hS) B.inclusion).obj p.siteObject)
    ⟨IsLocalRing.closedPoint p.carrier⟩
    ((Over.post (X := B.obj hS) B.inclusion).map m) g 1 ?_
  rw [map_one, h1, Category.comp_id]
  exact key

/-! ### The chart is a torsor over the final object -/

/-- **The chart `h_V ⟶ V/G` of the quotient by a free action is a `G`-torsor over the final
object of the spaces-étale site of the quotient.**

This is the hypothesis [Stacks, Tag 0727] makes about the pair `(W_p, U_p)`, for the quotient
of an object of a big fppf site by a free action of an abstract group. The three conditions
are `AlgebraicGeometry.Space.splittingSieve_mem_freeActionQuotientChart`, the kernel-pair
presentation `AlgebraicGeometry.Space.isPullback_freeActionRelationChart` together with
`AlgebraicGeometry.Space.summandSieve_mem_freeActionRelationChart`, and
`AlgebraicGeometry.Space.eq_one_of_comp_freeActionChartAut` against the objects with a point.

The base of the kernel pair is the final object of the site, which receives exactly one
morphism from every object by `AlgebraicGeometry.Space.SpacesEtale.final_unique`; that is the
subterminality `CategoryTheory.isTorsorObject_of_isPullback` asks for. -/
theorem isTorsorObject_freeActionChartAut :
    IsTorsorObject (freeActionChartAut G B S hS V a ha)
      (SpacesEtale.topology B S hS (actionQuotientSpace G B S hS V a ha)) := by
  have htest : ∀ A : SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha),
      (⊥ : Sieve A) ∉ SpacesEtale.topology B S hS
          (actionQuotientSpace G B S hS V a ha) A →
      ∃ A' : SpacesEtale B S hS (actionQuotientSpace G B S hS V a ha),
        Nonempty (points B S hS ((SpacesEtale.toSpaces B S hS
          (actionQuotientSpace G B S hS V a ha)).obj A').obj) ∧ Nonempty (A' ⟶ A) :=
    fun A hbot ↦ ⟨A, nonempty_points_of_bot_notMem_topology B S hS
      (actionQuotientSpace G B S hS V a ha) A hbot, ⟨𝟙 A⟩⟩
  exact isTorsorObject_of_isPullback
    (fun _ _ _ ↦ Subsingleton.elim _ _)
    (isPullback_freeActionRelationChart G B S hS V a ha).flip
    (freeActionChartSummand G B S hS V a ha)
    (freeActionChartSummand_comp_snd G B S hS V a ha)
    (freeActionChartSummand_comp_fst G B S hS V a ha)
    (fun _ d ↦ summandSieve_mem_freeActionRelationChart G B S hS V a ha d)
    (splittingSieve_mem_freeActionQuotientChart G B S hS V a ha)
    (fun _ hA φ g hg ↦ eq_one_of_comp_freeActionChartAut G B S hS V a ha hA φ g hg)
    htest

end AlgebraicGeometry.Space

end
