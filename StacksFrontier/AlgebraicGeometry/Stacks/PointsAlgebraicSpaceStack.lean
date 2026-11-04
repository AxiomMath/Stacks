module

public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPointSetInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinChart

/-!
# The point space of the stack of an algebraic space, and its open substacks

Let `F` be an algebraic space over `S` and let `S_F = algebraicSpaceStack F` be the algebraic
stack of **Stacks 03YS** that it determines. Two things are proved here.

The first is the **identification of point spaces**: the canonical map on points of the
tautological chart `F ⟶ S_F` is a homeomorphism from the topology of **Stacks 03BX** on the
points of `F` to the topology of **Stacks 04XL** on the points of `S_F`. The map is
`AlgebraicGeometry.Stack.spacePointMap` at the identity based functor, and it is already known
to be bijective (`AlgebraicGeometry.Stack.spacePointMap_id_bijective`) and continuous
(**Stacks 04XL**, clause (1)); what this file adds is that it is **open**, with no hypothesis at
all on `F`.

The second is the **converse of `exists_openSubstack_algebraicSpaceStack_of_isOpenImmersion`**:
every open substack of `S_F` arises from an open subspace of `F`. That direction is what makes
the stack-level rendering of a conclusion of the form "after replacing `F` by an open subspace"
equivalent to the source's; see
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingQuasiFiniteEtale.lean`.

## Main results

* `AlgebraicGeometry.Stack.isOpenMap_spacePointMap_id`: the canonical map on points of the
  tautological chart of an algebraic space is an open map. No hypotheses.
* `AlgebraicGeometry.Stack.isHomeomorph_spacePointMap_id` and
  `AlgebraicGeometry.Stack.pointsHomeomorphSpace`: it is a homeomorphism, and that
  homeomorphism as a bundled `Homeomorph`.
* `AlgebraicGeometry.Stack.OpenSubstack.mem_openSubspaceOfPoints_pointSet_iff`: a section of `F`
  lies in the subspace of **Stacks 03BZ** cut out by the inverse image of the point set of an
  open substack `Y` of `S_F` exactly when the object of `S_F` it names is an object of `Y`.
* `AlgebraicGeometry.Stack.exists_isOpenSubspace_property_eq_essImage`: every open substack of
  `S_F` is the essential image of the 1-morphism induced by an open subspace of `F`, and its
  point set is the image of that subspace's point set.

## How the openness is proved

It is not an instance of the openness clause of **Stacks 04XL**
(`AlgebraicGeometry.Stack.isOpenMap_spacePointMap`), which asks the chart to be flat and locally
of finite presentation on each of its represented base changes — that route needs the chart's
smoothness and hence an algebraic-space hypothesis on `F`. Instead the proof reads the definition
of the topology as a supremum of coinduced topologies: by
`AlgebraicGeometry.Stack.isOpen_pointTopology_iff` it is enough to see that the image of an open
set has open preimage along *every* chart of `S_F`, and every chart factors on points through the
tautological one, because a based functor between categories of elements of set-valued presheaves
is a morphism of presheaves
(`AlgebraicGeometry.Stack.spacePointMap_presheafMapOfBasedFunctor`,
`AlgebraicGeometry.Stack.spacePointMap_comp`). The tautological chart is injective on points, so
the preimage of the image of an open set along it is that set again, and what is left is
continuity of the map on points of a morphism of algebraic spaces.

This is the mirror at the tautological chart of
`AlgebraicGeometry.Stack.isOpenMap_spacePointMap_representing`, which proves the same thing for
the chart of a representing equivalence of an arbitrary category fibred in groupoids.

## How the converse is proved

Let `Y` be an open substack of `S_F`. Its point set `|Y|` is open
(`AlgebraicGeometry.Stack.OpenSubstack.isOpen_pointSet`), so its inverse image along the
tautological chart is an open set of points of `F`, and the subspace of **Stacks 03BZ** it cuts
out, `AlgebraicGeometry.Space.openSubspaceOfPoints`, is an open subspace `V ⊆ F`
(`AlgebraicGeometry.Stack.isOpenSubspace_openSubspaceOfPoints_spacePointMap_preimage`).

That `V` is the right one is read off the locus of **Stacks 04YM**. A section of `F` lies in `V`
exactly when the object it names lies in `AlgebraicGeometry.Stack.pointsWithin S_F |Y|`, by
`AlgebraicGeometry.Stack.mem_openSubspaceOfPoints_spacePointMap_preimage_iff`, and that locus
**is** `Y` — this is the injectivity half of **Stacks 06FJ** in the form in which it is formalized,
`AlgebraicGeometry.Stack.OpenSubstack.pointsWithin_pointSet_le` together with its converse
`AlgebraicGeometry.Stack.OpenSubstack.pointsWithin_pointSet_ge`. So membership of `V` and
membership of `Y` agree section by section, and the essential image of the induced 1-morphism
`S_V ⟶ S_F` is `Y`: one direction is that an object of `S_F` lying in `Y` is literally the image
of an object of `S_V`, the other that `Y` is closed under isomorphism
(`AlgebraicGeometry.Stack.OpenSubstack.strictlyFull`).

The point-set clause is where the identification of point spaces is used: the point set of
`openSubspaceOfPoints` is the set it was cut out by (**Stacks 03BZ**, part (1),
`AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`), which here is the inverse image
of `|Y|`, and the tautological chart is surjective on points, so the image of that inverse image
is `|Y|` again.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The point space of the stack of an algebraic space -/

/-- **The canonical map on points of the tautological chart of an algebraic space is open.** The
map `|F| → |S_F|` of **Stacks 04XL** attached to the identity based functor on the category of
elements of `F` is an open map from the topology of **Stacks 03BX** to the topology of
Stacks 04XL.

No hypothesis on `F` is needed. This is not the openness clause of Stacks 04XL, which asks the
chart to be flat and locally of finite presentation on its represented base changes; it is read
off the definition of the topology as a supremum of coinduced topologies, every chart factoring
on points through the tautological one. -/
theorem isOpenMap_spacePointMap_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    @IsOpenMap _ _ (Space.pointTopology B S hS F)
      (pointTopology B S hS (fibredCategory B S hS F))
      (spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val)) := by
  intro V hV
  refine (isOpen_pointTopology_iff B S hS (fibredCategory B S hS F) _).2 fun c => ?_
  have hfac : spacePointMap B S hS c.1.1 (fibredCategory B S hS F) c.2 =
      spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val) ∘
      Space.pointsMap B S hS c.1.1 (presheafMapOfBasedFunctor c.2) := by
    funext p
    have hcomp := congrFun (spacePointMap_comp B S hS c.1.1 (fibredCategory B S hS c.1.1)
      (fibredCategory B S hS F) (BasedFunctor.id (fibredCategory B S hS c.1.1).val) c.2) p
    rw [BasedFunctor.id_comp] at hcomp
    rw [Function.comp_apply, spacePointMap_presheafMapOfBasedFunctor]
    exact hcomp
  rw [hfac, Set.preimage_comp,
    Set.preimage_image_eq V (spacePointMap_id_bijective B S hS F).injective]
  have hc := Space.continuous_pointsMap B S hS (presheafMapOfBasedFunctor c.2)
  rw [continuous_def] at hc
  exact hc V hV

/-- **The point space of the stack of an algebraic space is the point space of that space.** The
canonical map on points of the tautological chart is a homeomorphism from the topology of
**Stacks 03BX** on `|F|` to the topology of **Stacks 04XL** on `|S_F|`.

Bijectivity is `AlgebraicGeometry.Stack.spacePointMap_id_bijective`, continuity is clause (1) of
Stacks 04XL, and openness is `AlgebraicGeometry.Stack.isOpenMap_spacePointMap_id`. Only
continuity uses that `F` is an algebraic space. -/
theorem isHomeomorph_spacePointMap_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    @IsHomeomorph _ _ (Space.pointTopology B S hS F)
      (pointTopology B S hS (fibredCategory B S hS F))
      (spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val)) :=
  @IsHomeomorph.mk _ _ (Space.pointTopology B S hS F)
    (pointTopology B S hS (fibredCategory B S hS F)) _
    (continuous_spacePointMap B S hS F hF (fibredCategory B S hS F) _)
    (isOpenMap_spacePointMap_id B S hS F)
    (spacePointMap_id_bijective B S hS F)

/-- **The identification of `|F|` with `|S_F|`**, as a bundled homeomorphism from the point space
of **Stacks 03BX** of an algebraic space `F` over `S` to the point space of **Stacks 04XL** of the
algebraic stack of **Stacks 03YS** that `F` determines.

This is the mirror at an algebraic space of
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, which identifies the point space of the stack of
a scheme of the site with the underlying topological space of that scheme. -/
noncomputable def pointsHomeomorphSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    letI := Space.pointTopology B S hS F
    letI := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS F hF).val
    @Homeomorph (Space.points B S hS F)
      (AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS F hF)) _ _ :=
  letI := Space.pointTopology B S hS F
  letI := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS F hF).val
  (isHomeomorph_spacePointMap_id B S hS F hF).homeomorph _

/-! ### Every open substack of the stack of an algebraic space comes from an open subspace -/

/-- **An open substack of `S_F`, read on `F`.** A section `s` of `F` over an object `A` of the
site lies in the subspace of **Stacks 03BZ** cut out by the inverse image along the tautological
chart of the point set of an open substack `Y` of `S_F` exactly when the object `(A, s)` of `S_F`
is an object of `Y`.

Both directions are the identification of the locus of **Stacks 04YM** on a chart,
`AlgebraicGeometry.Stack.mem_openSubspaceOfPoints_spacePointMap_preimage_iff`, composed with the
injectivity half of **Stacks 06FJ** in the form in which it is formalized: an open substack *is* the
locus of its own point set,
`AlgebraicGeometry.Stack.OpenSubstack.pointsWithin_pointSet_le` and
`AlgebraicGeometry.Stack.OpenSubstack.pointsWithin_pointSet_ge`. -/
theorem OpenSubstack.mem_openSubspaceOfPoints_pointSet_iff
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (Y : OpenSubstack (algebraicSpaceStack.{u, w} B S hS F hF))
    (A : BigFppfOver B S hS) (s : F.obj (Opposite.op A)) :
    s ∈ (Space.openSubspaceOfPoints B S hS F
          (spacePointMap B S hS F (algebraicSpaceStack.{u, w} B S hS F hF).val
            (BasedFunctor.id (fibredCategory B S hS F).val) ⁻¹'
            Y.pointSet B S hS)).obj (Opposite.op A) ↔
      Y.property ⟨A, Discrete.mk s⟩ := by
  rw [mem_openSubspaceOfPoints_spacePointMap_preimage_iff B S hS F
    (Y.pointSet B S hS) (BasedFunctor.id (fibredCategory B S hS F).val) s]
  exact ⟨fun h => Y.pointsWithin_pointSet_le B S hS _ h,
    fun h => Y.pointsWithin_pointSet_ge B S hS _ h⟩

/-- **Every open substack of the stack of an algebraic space arises from an open subspace of that
space.** For `F` an algebraic space over `S` and `Y` an open substack of the algebraic stack
`S_F` of **Stacks 03YS** there is an open subspace `V ⊆ F` in the sense of **Stacks 02YU**,
part (2), such that

* the objects of `Y` are exactly the essential image of the 1-morphism `S_V ⟶ S_F` of
  **Stacks 0458** induced by the inclusion of `V`, and
* the point set of `Y` is the image of the point set of `V` under the identification of `|F|`
  with `|S_F|`.

This is the converse of
`AlgebraicGeometry.Stack.exists_openSubstack_algebraicSpaceStack_of_isOpenImmersion`, which turns
an open subspace of `F` into an open substack of `S_F` with exactly that first property. The two
together say that the open substacks of `S_F` are precisely the open subspaces of `F`, which is
what a conclusion phrased as "after replacing `F` by an open subspace" needs if it is to be read
as a statement about an open substack of `S_F`. The subspace is the one of **Stacks 03BZ** cut
out by the inverse image of `|Y|`, and the point-set clause uses that the tautological chart is
surjective on points. -/
theorem exists_isOpenSubspace_property_eq_essImage
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (Y : OpenSubstack (algebraicSpaceStack.{u, w} B S hS F hF)) :
    ∃ (V : Subfunctor F) (hV : Space.IsOpenSubspace B S hS V),
      Y.property = (CatFiberedInGroupoids.homFunctor
          (algebraicSpaceStackMap.{u, w} B S hS hV.1 hF V.ι).hom).essImage ∧
        Y.pointSet B S hS =
          spacePointMap B S hS F (algebraicSpaceStack.{u, w} B S hS F hF).val
              (BasedFunctor.id (fibredCategory B S hS F).val) ''
            Set.range (Space.pointsMap B S hS V.toFunctor V.ι) := by
  refine ⟨Space.openSubspaceOfPoints B S hS F
      (spacePointMap B S hS F (algebraicSpaceStack.{u, w} B S hS F hF).val
        (BasedFunctor.id (fibredCategory B S hS F).val) ⁻¹' Y.pointSet B S hS),
    isOpenSubspace_openSubspaceOfPoints_spacePointMap_preimage B S hS F hF
      (Y.pointSet B S hS) (BasedFunctor.id (fibredCategory B S hS F).val)
      (OpenSubstack.isOpen_pointSet B S hS Y), ?_, ?_⟩
  · refine funext fun x => propext ⟨fun hx => ?_, fun hx => ?_⟩
    · refine ⟨⟨x.base, Discrete.mk ⟨x.fiber.as,
        (Y.mem_openSubspaceOfPoints_pointSet_iff B S hS x.base x.fiber.as).2 hx⟩⟩, ⟨eqToIso ?_⟩⟩
      exact associatedMap_obj B S hS _ _
    · obtain ⟨y, ⟨e⟩⟩ := hx
      refine Y.strictlyFull.of_iso e ?_
      exact (Y.mem_openSubspaceOfPoints_pointSet_iff B S hS y.base y.fiber.as.1).1 y.fiber.as.2
  · rw [Space.range_pointsMap_ι_openSubspaceOfPoints,
      Set.image_preimage_eq _ (spacePointMap_id_bijective B S hS F).surjective]

end AlgebraicGeometry.Stack

end
