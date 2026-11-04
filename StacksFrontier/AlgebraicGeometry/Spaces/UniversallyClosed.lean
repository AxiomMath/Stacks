module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Closed, universally closed and proper morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *closed* when the map it induces on
points is a closed map, *universally closed* when its base change along every morphism from
an algebraic space is closed, and *proper* when it is separated, of finite type and
universally closed.

The two comparisons of closed maps on points proved here make the two formal properties of
universal closedness — a universally closed morphism is closed, and universal closedness is
stable under base change — immediate. Both rest on one fact about the point topology, proved
here: the map on points induced by an isomorphism of presheaves is a bijection with continuous
inverse, hence a closed map. So the map on points of a morphism which factors as an
isomorphism followed by a morphism with closed map on points has closed map on points itself,
and each of the two comparisons is an instance of that: for closedness the isomorphism is the
inverse of the second projection of the base change along the identity, and for base change it
is the pasting isomorphism `W ×_Z (Z ×_Y X) ≅ W ×_Y X`.

## Main definitions

* `AlgebraicGeometry.Space.IsClosedMorphism`: closed morphisms (Stacks 03HI, part (1)).
* `AlgebraicGeometry.Space.UniversallyClosed`: universally closed morphisms (Stacks 03HI,
  part (2)).
* `AlgebraicGeometry.Space.IsProper`: proper morphisms (Stacks 03ZM).

## Main results

* `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_isIso`: the map on points induced by an
  isomorphism of presheaves on the big fppf site of `S` is a closed map.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_comp_isIso`: a morphism which becomes one
  with closed map on points after precomposition with an isomorphism has closed map on points.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_pullback_fst_id`: if the base change of
  `f` along the identity of its target has closed map on points, so does `f`. With Tag 03HI
  this says that a universally closed morphism of algebraic spaces is closed.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_pullback_fst_pullback_fst`: if the base
  change of `f : X ⟶ Y` along `w ≫ g` has closed map on points, then the base change along
  `w` of the base change along `g` does. With Tag 03HI this says that universal closedness of
  a morphism of algebraic spaces is stable under base change.
* `AlgebraicGeometry.Space.IsClosedMorphism.comp`: a composition of closed morphisms is
  closed.
* `AlgebraicGeometry.Space.IsProper.isSeparated`,
  `AlgebraicGeometry.Space.IsProper.isFiniteType` and
  `AlgebraicGeometry.Space.IsProper.universallyClosed` are the three conjuncts of properness,
  and `AlgebraicGeometry.Space.IsProper.mk'` assembles them.

## Implementation notes

The point set is `AlgebraicGeometry.Space.points` of Stacks 03BU and the induced map is
`AlgebraicGeometry.Space.pointsMap`. The topology is
`AlgebraicGeometry.Space.pointTopology`, the topology detected by scheme-valued points; it
is the one constructed in `StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology` rather than
a topology chosen from the existence statement of Stacks 03BX, so that nothing here rests
on a `Classical.choose`. All three clauses of Stacks 03BX hold for it, and
`AlgebraicGeometry.Space.PointTopologyFamily.topology_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique` shows that *any* family of
topologies satisfying those clauses assigns this topology to every algebraic space.

The base changes in the universal condition are the presheaf fibre products of Stacks 02X2;
algebraicity of the fibre product is not needed to state the condition, because
`AlgebraicGeometry.Space.pointTopology` is defined for an arbitrary presheaf. Algebraicity
of the covering object `Z` *is* part of the condition and is therefore a hypothesis of the
quantifier, as in the source.

As elsewhere in this directory the predicates are stated for arbitrary morphisms of
presheaves on the big fppf site of `S`, algebraicity of the source and target being imposed
by clients; and they are abbreviations, so that a client may use the constituent conditions
without a conversion lemma.

`AlgebraicGeometry.Space.pointTopology` is a `def`, not an instance. The definitions supply
it with `letI`; the four comparison results that follow them install it as a local instance
instead, so that `IsClosedMap` and `Continuous` elaborate without explicit topology
arguments.

None of the four results needs any presheaf to be an algebraic space, because the point
topology is constructed for an arbitrary presheaf on the big fppf site. Algebraicity enters
only in the quantifier of universal closedness, which tests the base changes by *algebraic*
spaces over the target, and so is supplied by the client at the point of use: the first
comparison is applied to the instance of that quantifier at the identity of the target, and
the second to its instance at the composite `w ≫ g`.

The comparisons are stated about `AlgebraicGeometry.Space.pointsMap` and `IsClosedMap` rather
than about `AlgebraicGeometry.Space.IsClosedMorphism`, so that they apply to any formulation
of Tag 03HI: closedness of a morphism of algebraic spaces is this closed-map condition,
whatever algebraicity hypotheses the predicate carries alongside it.

## References

* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Closed, universally closed and proper morphisms -/

section Defs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of algebraic spaces over `S` is *closed* when the map it induces on points is a
closed map for the topology detected by scheme-valued points. -/
@[stacks 03HI "closed"]
abbrev IsClosedMorphism (f : F ⟶ G) : Prop :=
  letI := pointTopology B S hS F
  letI := pointTopology B S hS G
  IsClosedMap (pointsMap B S hS F f)

/-- A morphism of algebraic spaces over `S` is *universally closed* when its base change along
every morphism to its target from an algebraic space over `S` is closed. -/
@[stacks 03HI "universally closed"]
abbrev UniversallyClosed (f : F ⟶ G) : Prop :=
  ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
    ∀ g : Z ⟶ G, IsClosedMorphism B S hS (pullback.fst g f)

/-- A morphism of algebraic spaces over `S` is *proper* when it is separated, of finite type and
universally closed. -/
@[stacks 03ZM]
abbrev IsProper (f : F ⟶ G) : Prop :=
  IsSeparated B S hS f ∧ IsFiniteType B S hS f ∧ UniversallyClosed B S hS f

end Defs

/-! ### Closedness on points of a base change -/

section Comparisons

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on points induced by an isomorphism of presheaves on the big fppf site of `S` is
a closed map: it is a bijection whose inverse is the map on points of the inverse morphism,
so the image of a set under it is the preimage of that set under a continuous map. -/
theorem isClosedMap_pointsMap_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ G) [IsIso e] : IsClosedMap (pointsMap B S hS F e) :=
  .of_inverse (continuous_pointsMap B S hS (inv e))
    (fun y ↦ by simpa using (congrFun (pointsMap_comp B S hS G (inv e) e) y).symm)
    (fun x ↦ by simpa using (congrFun (pointsMap_comp B S hS F e (inv e)) x).symm)

/-- If a morphism of presheaves on the big fppf site of `S` becomes, after precomposition
with an isomorphism, a morphism whose map on points is closed, then its own map on points is
closed. -/
theorem isClosedMap_pointsMap_of_comp_isIso {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ F') [IsIso e] {g : F' ⟶ G} {f : F ⟶ G} (hfg : e ≫ g = f)
    (hg : IsClosedMap (pointsMap B S hS F' g)) :
    IsClosedMap (pointsMap B S hS F f) := by
  subst hfg
  rw [pointsMap_comp]
  exact IsClosedMap.comp hg (isClosedMap_pointsMap_of_isIso B S hS e)

/-- If the base change of `f : X ⟶ Y` along the identity of `Y` has closed map on points, then
so does `f`: the second projection of that base change is an isomorphism which identifies its
first projection with `f`.

Applied to the instance at the identity of `Y` of the quantifier defining universal
closedness, this says that a universally closed morphism of algebraic spaces is closed. -/
theorem isClosedMap_pointsMap_of_pullback_fst_id {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)
    (h : IsClosedMap (pointsMap B S hS (pullback (𝟙 Y) f) (pullback.fst (𝟙 Y) f))) :
    IsClosedMap (pointsMap B S hS X f) := by
  refine isClosedMap_pointsMap_of_comp_isIso B S hS (inv (pullback.snd (𝟙 Y) f)) ?_ h
  have hc : pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f := by
    simpa using pullback.condition (f := 𝟙 Y) (g := f)
  rw [hc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- If the base change of `f : X ⟶ Y` along a composite `w ≫ g` has closed map on points, then
so does the base change along `w` of the base change along `g`: the pasting isomorphism
`W ×_Z (Z ×_Y X) ≅ W ×_Y X` identifies the two first projections to `W`.

Applied to the instance at `w ≫ g` of the quantifier defining universal closedness, this
says that universal closedness of a morphism of algebraic spaces is stable under base
change. -/
theorem isClosedMap_pointsMap_pullback_fst_pullback_fst
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y) (w : W ⟶ Z)
    (h : IsClosedMap (pointsMap B S hS (pullback (w ≫ g) f) (pullback.fst (w ≫ g) f))) :
    IsClosedMap (pointsMap B S hS (pullback w (pullback.fst g f))
      (pullback.fst w (pullback.fst g f))) :=
  isClosedMap_pointsMap_of_comp_isIso B S hS (pullbackRightPullbackFstIso g f w).hom
    (pullbackRightPullbackFstIso_hom_fst g f w) h

end Comparisons

/-! ### Composition of closed morphisms, and the conjuncts of properness -/

section Permanence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A composition of closed morphisms of algebraic spaces is closed: the map on points of a
composition is the composition of the maps on points. -/
theorem IsClosedMorphism.comp {f : F ⟶ G} {g : G ⟶ H} (hg : IsClosedMorphism B S hS g)
    (hf : IsClosedMorphism B S hS f) :
    IsClosedMorphism B S hS (f ≫ g) := by
  intro W hW
  rw [pointsMap_comp, Set.image_comp]
  exact hg _ (hf _ hW)

/-- A proper morphism of algebraic spaces is separated. -/
theorem IsProper.isSeparated {f : F ⟶ G} (h : IsProper B S hS f) : IsSeparated B S hS f := h.1

/-- A proper morphism of algebraic spaces is of finite type. -/
theorem IsProper.isFiniteType {f : F ⟶ G} (h : IsProper B S hS f) :
    IsFiniteType B S hS f := h.2.1

/-- A proper morphism of algebraic spaces is universally closed. -/
theorem IsProper.universallyClosed {f : F ⟶ G} (h : IsProper B S hS f) :
    UniversallyClosed B S hS f := h.2.2

/-- Properness of a morphism of algebraic spaces follows from its three conjuncts. -/
theorem IsProper.mk' {f : F ⟶ G} (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (huc : UniversallyClosed B S hS f) : IsProper B S hS f :=
  ⟨hsep, hft, huc⟩

end Permanence

end AlgebraicGeometry.Space

end
