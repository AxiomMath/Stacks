module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteGroupQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientPresentationKernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# The schematic locus of the quotient by a free action of a finite group

Let `S` be a scheme, let `V` be an object of a big fppf site over `S` and let a finite group
`G` act freely on `V` over `S`. The graph relation of the action is the disjoint union of one
copy of `V` for each element of `G`, so its source map is a finite coproduct of copies of the
identity and is therefore finite locally free; being the kernel pair of the quotient map
`h_V ⟶ V/G`, it makes that map finite locally free after every representable base change.
Together with its surjectivity this is the input of Stacks 0BA1, and the conclusion is that a
point of `V/G` lies in the schematic locus exactly when the whole fibre above it is covered by
the point set of some open immersion into `h_V` out of an affine object of the site.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFree_sigmaDesc`: a morphism out of a finite coproduct of
  schemes is finite locally free when each of its restrictions to a summand is.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_actionRelationSource`: the source map of the
  graph relation of an action of a finite group is finite locally free.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_quotientMap`: the quotient map of an
  étale equivalence relation with finite locally free source map is finite locally free after
  every representable base change.
* `AlgebraicGeometry.Space.isPullback_freeActionQuotientMap`: the disjoint union of one copy
  of `V` for each element of `G` is the fibre product `h_V ×_{V/G} h_V`.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_freeActionQuotientMap` and
  `AlgebraicGeometry.Space.surjective_presheaf_freeActionQuotientMap`: the chart `h_V ⟶ V/G`
  of a free action of a finite group is finite locally free and surjective after every
  representable base change.
* `AlgebraicGeometry.Space.mem_schematicLocus_actionQuotient_iff`: **Stacks 0B87** for an
  action on an object of the site, condition (2) in the form in which Tag 0BA1 is formalized.

## Implementation notes

Finite local freeness of the source map is read through
`AlgebraicGeometry.Space.property_left_of_sigmaDesc`, which reduces a property of a morphism
out of a coproduct of copies of `V` indexed by `G` to the same property of the descent of its
restrictions over a shrunken index type; each restriction of the source map is the identity.
That the finite coproduct itself is finite locally free is finiteness
(`AlgebraicGeometry.isFinite_sigmaDesc`) together with flatness and local finite presentation,
which are Zariski local on the source.

The quotient map is handled by `AlgebraicGeometry.Space.presheaf_of_isKernelPair`, which
transports a base-change stable, fppf local property of morphisms of schemes from the source
map of the relation to the quotient map. Finite local freeness is fppf local on the base
because it is fpqc local on the base, by
`Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc`.
Locality is genuinely needed: the comparison from the disjoint union of the copies of `V` to
the kernel pair is only an isomorphism after sheafification, since a point of the kernel pair
is concentrated in a single group element only locally on the base.

Finiteness of `G` is used only for the source map: for an infinite group the relation scheme is
an infinite disjoint union, whose projection is étale but not finite, and 0BA1 does not apply.

The tag itself — a free action of a finite group on an *arbitrary* algebraic space over `S`,
with the quotient of Tag 071S — is
`AlgebraicGeometry.Space.mem_schematicLocus_orbitQuotient_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionSpaceSchematicLocus`, which is why
the attribute below is qualified. There the relation is the kernel pair of an étale chart
rather than the graph of the action, and the fibre product of the space with the chart over
the quotient is the disjoint union of one copy of the chart for each group element.

## References

* [Stacks Project, Tag 0B87](https://stacks.math.columbia.edu/tag/0B87)
* [Stacks Project, Tag 0BA1](https://stacks.math.columbia.edu/tag/0BA1)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Groupoids

universe u v

namespace Stacks.Morphisms

/-- Being finite locally free is fppf local on the base, the fppf coverings being fpqc
coverings. -/
instance isFiniteLocallyFree_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- The identity of a scheme is finite locally free. -/
theorem isFiniteLocallyFree_id (X : Scheme.{u}) : IsFiniteLocallyFree (𝟙 X) := by
  rw [isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A morphism out of a finite coproduct of schemes is finite locally free when each of its
restrictions to a summand is: finiteness is `AlgebraicGeometry.isFinite_sigmaDesc`, and
flatness and local finite presentation are Zariski local on the source. -/
theorem isFiniteLocallyFree_sigmaDesc {ι : Type v} [Finite ι] [Small.{u} ι]
    {Y : ι → Scheme.{u}} {T : Scheme.{u}} (f : ∀ i, Y i ⟶ T)
    (hf : ∀ i, IsFiniteLocallyFree (f i)) :
    IsFiniteLocallyFree (Sigma.desc f) := by
  have h (i : ι) :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation (f i)).1 (hf i)
  have _ : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have _ : IsZariskiLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have _ : ∀ i, _root_.AlgebraicGeometry.IsFinite (f i) := fun i => (h i).1
  rw [isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
  exact ⟨inferInstance, IsZariskiLocalAtSource.sigmaDesc fun i => (h i).2.1,
    IsZariskiLocalAtSource.sigmaDesc fun i => (h i).2.2⟩

end Stacks.Morphisms

namespace AlgebraicGeometry.Space

open Stacks.Morphisms

/-- **The source map of the graph relation of an action of a finite group is finite locally
free.** The relation scheme is the disjoint union of one copy of the scheme acted on for each
group element, and the source map is the identity on each copy. -/
theorem isFiniteLocallyFree_actionRelationSource {S : Scheme.{u}} (U : Over S) (G : Type v)
    [Group G] [Finite G] [Small.{u} G] :
    IsFiniteLocallyFree (actionRelationSource U G).left := by
  have _ : Finite (Shrink.{u} G) := Finite.of_equiv G (equivShrink.{u} G)
  have _ : MorphismProperty.RespectsIso (@IsFiniteLocallyFree.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine property_left_of_sigmaDesc (@IsFiniteLocallyFree.{u}) G
    (actionRelationSource U G) ?_
  refine isFiniteLocallyFree_sigmaDesc _ fun i => ?_
  have h : (Sigma.ι (fun _ : G => U) ((equivShrink.{u} G).symm i) ≫
      actionRelationSource U G).left = 𝟙 U.left := by
    rw [show Sigma.ι (fun _ : G => U) ((equivShrink.{u} G).symm i) ≫
      actionRelationSource U G = 𝟙 U from by simp [actionRelationSource]]
    rfl
  rw [h]
  exact isFiniteLocallyFree_id U.left

/-- **The target map of the graph relation of an action of a finite group is finite locally
free.** The relation scheme is the disjoint union of one copy of the scheme acted on for each
group element, and the target map acts on the copy indexed by `g` by the automorphism `a g`,
which is an isomorphism and so finite locally free. -/
theorem isFiniteLocallyFree_actionRelationTarget {S : Scheme.{u}} (U : Over S) (G : Type v)
    [Group G] [Finite G] [Small.{u} G] (a : G →* Aut U) :
    IsFiniteLocallyFree (actionRelationTarget U G a).left := by
  have _ : Finite (Shrink.{u} G) := Finite.of_equiv G (equivShrink.{u} G)
  have _ : MorphismProperty.RespectsIso (@IsFiniteLocallyFree.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine property_left_of_sigmaDesc (@IsFiniteLocallyFree.{u}) G
    (actionRelationTarget U G a) ?_
  refine isFiniteLocallyFree_sigmaDesc _ fun i => ?_
  have h : (Sigma.ι (fun _ : G => U) ((equivShrink.{u} G).symm i) ≫
      actionRelationTarget U G a).left = (a ((equivShrink.{u} G).symm i)).asIso.hom.left := by
    rw [show Sigma.ι (fun _ : G => U) ((equivShrink.{u} G).symm i) ≫
      actionRelationTarget U G a = (a ((equivShrink.{u} G).symm i)).asIso.hom from by
        simp [actionRelationTarget]]
  have _ : IsIso (a ((equivShrink.{u} G).symm i)).asIso.hom.left :=
    ((Over.forget S).mapIso (a ((equivShrink.{u} G).symm i)).asIso).isIso_hom
  rw [h]
  simpa using MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree.{u})
    (a ((equivShrink.{u} G).symm i)).asIso.hom.left (𝟙 U.left) (isFiniteLocallyFree_id U.left)

section Quotient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {R U : BigFppfOver B S hS} (s t : R ⟶ U)

/-- **The quotient map of a relation is a surjection of fppf sheaves.** It is the projection
onto the quotient sheaf read through the functor of points of the scheme presenting it. -/
theorem isLocallySurjective_quotientMap :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (quotientMap B S hS s t) := by
  have hfull : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have hfaith : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  rw [show quotientMap B S hS s t = quotientChart (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) U (relation B S hS s t) from
    yonedaEquiv_symm_app_toQuotientSheaf _ _ _ _]
  exact isLocallySurjective_quotientChart _ _ _ _

/-- **The quotient map of an étale equivalence relation whose source map is finite locally
free is finite locally free after every representable base change.** Its kernel pair is the
relation, and finite local freeness is stable under base change and fppf local on the base. -/
theorem isFiniteLocallyFree_presheaf_quotientMap
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hs : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s)) :
    (MorphismProperty.inverseImage (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (quotientMap B S hS s t) :=
  presheaf_of_isKernelPair B S hS (quotientMap B S hS s t) (@IsFiniteLocallyFree.{u})
    (quotientMap_isPullback B S hS s t)
    (isLocallySurjective_quotientMap B S hS s t)
    (relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t
      (isAlgebraicSpace_quotient_unconditional B S hS s t)) hs

end Quotient

section FreeFiniteAction

variable (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u})
  (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The relation scheme of a free action satisfies the size cutoff of the site, freeness on
the points being condition (*) of Tag 02Z2. -/
theorem contains_actionRelationScheme_of_actsFreely
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) :
    B.Contains (actionRelationScheme (underlyingOver B hS V) G).left :=
  contains_actionRelationScheme G B hS V a
    ((actsFreelyOnNonemptyPoints_iff (underlyingOver B hS V) G a).1 ha)

/-- The canonical chart `h_V ⟶ V/G` of the quotient of `V` by a free action of `G`: the
quotient map of the graph relation of the action, read inside the site. -/
noncomputable def freeActionQuotientMap
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) :
    yoneda.obj V ⟶ actionQuotient G B hS V a :=
  quotientMap B S hS
    (siteActionRelationSource G B hS V
      (contains_actionRelationScheme_of_actsFreely G B S hS V a ha))
    (siteActionRelationTarget G B hS V
      (contains_actionRelationScheme_of_actsFreely G B S hS V a ha) a)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The graph relation of a free action is an étale equivalence relation inside the site. -/
theorem isEtaleEquivalenceRelation_relation_of_actsFreely
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) :
    IsEtaleEquivalenceRelation (relation B S hS
      (siteActionRelationSource G B hS V
        (contains_actionRelationScheme_of_actsFreely G B S hS V a ha))
      (siteActionRelationTarget G B hS V
        (contains_actionRelationScheme_of_actsFreely G B S hS V a ha) a)) :=
  actionRelation_isEtaleEquivalenceRelation (underlyingOver B hS V) G a
    ((actsFreelyOnNonemptyPoints_iff (underlyingOver B hS V) G a).1 ha)

/-- **The disjoint union of one copy of `V` for each element of `G` is the fibre product
`h_V ×_{V/G} h_V`.** The target and source maps of the graph relation are its two projections,
so the quotient map of a free action is a pseudo-torsor under the constant group `G` split by
`V` itself. -/
theorem isPullback_freeActionQuotientMap
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) :
    IsPullback
      (yoneda.map (siteActionRelationTarget G B hS V
        (contains_actionRelationScheme_of_actsFreely G B S hS V a ha) a))
      (yoneda.map (siteActionRelationSource G B hS V
        (contains_actionRelationScheme_of_actsFreely G B S hS V a ha)))
      (freeActionQuotientMap G B S hS V a ha) (freeActionQuotientMap G B S hS V a ha) :=
  have _ := isEtaleEquivalenceRelation_relation_of_actsFreely G B S hS V a ha
  quotientMap_isPullback B S hS _ _

/-- **The quotient map of a free action of a finite group is finite locally free after every
representable base change.** Its kernel pair is the disjoint union of one copy of `V` for each
element of `G`, whose projection is a finite coproduct of copies of the identity. -/
theorem isFiniteLocallyFree_presheaf_freeActionQuotientMap [Finite G]
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) :
    (MorphismProperty.inverseImage (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (freeActionQuotientMap G B S hS V a ha) :=
  have _ := isEtaleEquivalenceRelation_relation_of_actsFreely G B S hS V a ha
  isFiniteLocallyFree_presheaf_quotientMap B S hS _ _
    (isFiniteLocallyFree_actionRelationSource (underlyingOver B hS V) G)

/-- **The quotient map of a free action is surjective after every representable base change.**
The source map of the graph relation is split by the summand indexed by the identity. -/
theorem surjective_presheaf_freeActionQuotientMap
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (freeActionQuotientMap G B S hS V a ha) :=
  have _ := isEtaleEquivalenceRelation_relation_of_actsFreely G B S hS V a ha
  quotientMap_surjective_unconditional B S hS _ _

/-- **Stacks 0B87.** Let a finite group `G` act freely on an object `V` of a big fppf site over
a scheme `S` and let `y` be a point of the quotient `V/G`. Then `y` lies in the schematic locus
of `V/G` if and only if there is an affine object `U` of the site and an open immersion
`i : h_U ⟶ h_V` whose point set contains every point of `h_V` above `y`.

The quotient map is surjective and finite locally free after every representable base change,
so this is Stacks 0BA1 for it, read on the chart `h_V ⟶ V/G` bundled as a morphism of
algebraic spaces over `S`. -/
@[stacks 0B87 "for a free action of a finite group on an object of the big fppf site over `S` \
in place of an action on an arbitrary algebraic space, the quotient being the quotient sheaf \
of the graph relation of the action as in the library's form of Tag 071S, freeness being read on \
the points over the test schemes with nonempty underlying space, and the affine open of \
condition (2) being presented as in the library's form of Tag 0BA1, by an open immersion into \
the functor of points of the scheme acted on out of an affine object of the site"]
theorem mem_schematicLocus_actionQuotient_iff [Finite G]
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a)
    (y : points B S hS (actionQuotient G B hS V a)) :
    y ∈ Set.range (pointsMap B S hS
        (schematicLocus B S hS (actionQuotient G B hS V a)).toFunctor
        (schematicLocus B S hS (actionQuotient G B hS V a)).ι) ↔
      ∃ (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ yoneda.obj V),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧ IsOpenImmersion B S hS i ∧
        ∀ x : points B S hS (yoneda.obj V),
          pointsMap B S hS (yoneda.obj V) (freeActionQuotientMap G B S hS V a ha) x = y →
            x ∈ Set.range (pointsMap B S hS (yoneda.obj U) i) :=
  mem_range_pointsMap_schematicLocus_iff_exists_isAffine_isOpenImmersion B S hS
    (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (Y := ⟨actionQuotient G B hS V a,
      isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints G B hS V a ha⟩)
    (ObjectProperty.homMk (freeActionQuotientMap G B S hS V a ha))
    (surjective_presheaf_freeActionQuotientMap G B S hS V a ha)
    (isFiniteLocallyFree_presheaf_freeActionQuotientMap G B S hS V a ha) y

end FreeFiniteAction

end AlgebraicGeometry.Space

end
