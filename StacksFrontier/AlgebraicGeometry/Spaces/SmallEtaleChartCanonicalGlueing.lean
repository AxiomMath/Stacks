module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleToposCoherence

/-!
# The canonical chartwise glueing datum of a sheaf on an algebraic space

Stacks 03LS describes a sheaf `F` on the small étale site of an algebraic space `X` by the family
of its restrictions `F_U` to the étale scheme charts `U` of `X`, together with the comparison
isomorphisms `c_f : f^{-1}F_U ≅ F_V` for the morphisms `f : V ⟶ U` of charts, *subject to the
cocycle condition* `c_g ∘ g^{-1}c_f = c_{g ≫ f}`.

`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueing` defines the category
`AlgebraicGeometry.Space.ChartGlueingData` in which that datum lives, and records that the
cocycle condition for the canonical datum of a sheaf was missing: it is stated through
`AlgebraicGeometry.Space.chartInverseImageComp`, which is an
`CategoryTheory.Adjunction.leftAdjointUniq`, so it is the adjoint mate of an associativity
statement about `AlgebraicGeometry.Space.smallToposMorphism_comp`.  That associativity is now
available as `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc`, and this file
discharges the cocycle with it and assembles the canonical chartwise datum into a functor.

## Main definitions

* `AlgebraicGeometry.Space.canonicalChartGlueingData`: the chartwise glueing datum of a sheaf of
  sets on the small étale site of `X` — its restrictions to the charts, the comparison
  isomorphisms of `AlgebraicGeometry.Space.chartRestrictionComp`, and the cocycle condition.
* `AlgebraicGeometry.Space.chartGlueingFunctor`: the canonical functor from sheaves on the small
  étale site of `X` to chartwise glueing data.

## Main results

* `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc_inv`: the pentagon of
  Stacks 03G2, part (3), on inverse images, rearranged so that the two comparison isomorphisms
  read in the direction a cocycle condition uses them.
* `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_cocycle`: the same identity for
  three composable morphisms of algebraic spaces whose pairwise composites are *named* by further
  morphisms and equalities, which is the shape the chart constructions present.
* `AlgebraicGeometry.Space.chartRestrictionComp_cocycle`: **the cocycle condition for the
  restrictions of a sheaf to the étale scheme charts of `X`**, the condition Stacks 03LS imposes
  on its data.
* `AlgebraicGeometry.Space.chartGlueingFunctor_faithful`: the canonical functor is faithful.

## Implementation notes

The cocycle condition is derived from the pentagon in three steps, because the chart comparisons
do not present their composites in the shape the pentagon states them.

First, `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc_inv` rearranges the
pentagon.  The pentagon is a statement about the *forward* comparison isomorphisms
`(f ≫ g)^{-1} ≅ g^{-1} ⋙ f^{-1}`, whereas a cocycle condition composes their inverses; the
rearrangement is three cancellations.

Second, `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_cocycle` restates it with
each of the three composites `f ≫ a`, `g ≫ (f ≫ a)` and `g ≫ f` replaced by a morphism of its
own together with an equality, and with the comparison isomorphisms transported along those
equalities.  This is what the chart constructions need: `chartMap f ≫ chartToSpace U` is not
`chartToSpace V` but is *equal* to it (`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`), and
likewise `chartMap g ≫ chartMap f` is equal to `chartMap (g ≫ f)`
(`AlgebraicGeometry.Space.chartMap_comp`), so the `CategoryTheory.eqToIso` in the definitions of
`AlgebraicGeometry.Space.chartRestrictionComp` and
`AlgebraicGeometry.Space.chartInverseImageComp` has to be carried through.  The restatement is
proved by substituting the three equalities, which returns the previous lemma.  The fourth
equality `em` is then redundant — it is forced by the other three — but it is taken as a
hypothesis rather than derived, because what the chart instance supplies for it is
`chartMap_comp_chartToSpace (g ≫ f)` and not a composite of the other three proofs; proof
irrelevance makes the two interchangeable inside `CategoryTheory.eqToHom`.

Third, `AlgebraicGeometry.Space.chartRestrictionComp_cocycle` instantiates it at the chart data.

What is *not* proved here is that `AlgebraicGeometry.Space.chartGlueingFunctor` is an
equivalence — that is
`AlgebraicGeometry.Space.chartGlueingFunctor_isEquivalence` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueingEquivalence`.  Faithfulness is proved
here, by reduction to Stacks 0GWK through the comparison
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso`, which needs nothing beyond the
object-level dictionary between charts and slices.  Fullness and essential surjectivity do not
reduce that way, and the obstruction has a single source, recorded here precisely.

Any functor between `AlgebraicGeometry.Space.ChartGlueingData` and the slice-indexed
`CategoryTheory.SiteGlueing.GlueingData` must carry one cocycle condition to the other, so it
needs `AlgebraicGeometry.Space.chartRestrictionComp` and
`AlgebraicGeometry.Space.chartInverseImageComp` to correspond, through
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso` and
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso`, to
`CategoryTheory.Sheaf.pushforwardOverMapIso` and
`CategoryTheory.GrothendieckTopology.overMapPullbackComp`.  Both of the latter are
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` isomorphisms on the nose, and both of
the former are built out of `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso`
(Stacks 03LQ, written `θ` below) and
`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage` (Stacks 03G2, part (3)).  So
everything reduces to one statement about those two, for étale morphisms `k` and `l` of
algebraic spaces — the *bridge*:

```
(smallToposMorphism_comp_inverseImage k l).hom ≫ whiskerRight θ_l _ ≫ whiskerLeft _ θ_k
  = θ_(k ≫ l)
```

It is stated with no comparison isomorphism on the restriction side at all, because that side is
*strict*: `AlgebraicGeometry.Space.smallEtalePostcomp_comp` is an equality of functors, and
restriction along the two postcompositions therefore composes to restriction along the composite
with nothing inserted.  In that form the statement typechecks.

What makes the bridge reachable — and what the two files upstream, and an earlier pass of this
one, wrongly took to be absent — is that its two sides are left adjoints of *the same* functor:
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward` is
`restriction along postcomposition ⊣ (smallToposMorphism h).pushforward`, with the same right
adjoint as `(smallToposMorphism h).adj`.  So `CategoryTheory.Adjunction.leftAdjointUniq` and
`CategoryTheory.Adjunction.leftAdjointUniq_trans` apply, and the bridge splits into four
statements — not three, as an earlier pass of this file recorded; the fourth was missed.  All
four are now proved, and so is the bridge,
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_comp` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionComp`:

* that `CategoryTheory.Adjunction.leftAdjointUniq` is compatible with
  `CategoryTheory.Adjunction.comp` — the comparison of two composite left adjoints is the
  horizontal composite of the two comparisons.  This is general, and it already existed:
  `CategoryTheory.Adjunction.leftAdjointUniq_comp`;
* that transporting the right adjoints of two adjunctions along one and the same isomorphism
  leaves `CategoryTheory.Adjunction.leftAdjointUniq` unchanged.  Also general, and now proved:
  `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_congr`.  Together with the previous
  item it gives the hexagon
  `CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker`, from which the bridge is
  formal: `AlgebraicGeometry.Space.smallToposMorphism_inverseImageUniq_comp`;
* **the content**: that the composite of the two restriction adjunctions, with its right
  adjoint transported along `AlgebraicGeometry.Space.smallToposMorphism_comp`, *equals* the
  restriction adjunction of the composite.  It says the direct-image composition comparison of
  Stacks 03G2, part (3), is the comparison that strictness of the Stacks 03LP restriction tower
  already supplies.  Being an equality of two adjunctions with the same left and the same right
  adjoint, it is a unit identity, and it is now proved, as
  `AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward_comp`, by transporting
  `AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompSheafComp` — the same statement on
  the spaces-étale topoi — along the comparison equivalences of Stacks 03G1.  That transport is
  not formal, because postcomposition composes strictly on the small étale sites
  (`AlgebraicGeometry.Space.smallEtalePostcomp_comp`) but not on the spaces-étale ones, where
  `AlgebraicGeometry.Space.spacesEtalePostcompComp` is a `CategoryTheory.Over.mapComp`; the
  absorption of that `Over.mapComp` is
  `AlgebraicGeometry.Space.whiskerRight_spacesEtalePostcompSheafComp_inv`, the one equation it
  leaves is
  `AlgebraicGeometry.Space.inverseCompIso_smallEtalePostcompComparisonSquare_comp`, and the
  calculus that carries them the rest of the way is
  `CategoryTheory.conjugateEquiv_transport_comp_ofNatIsoLeft`;
* the step the earlier pass missed, now proved as
  `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_eq_uniq`: that
  `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso`, the comparison Stacks 03LQ
  supplies and the one out of which
  `AlgebraicGeometry.Space.chartRestriction_overPullbackIso` and
  `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso` are built, *is* the canonical
  comparison `AlgebraicGeometry.Space.smallToposMorphism_inverseImageUniq` of the two left
  adjoints.  Without it the hexagon proves the bridge for the canonical comparison and says
  nothing about the one the chart dictionary uses.  It was the hypothesis `hθ` of
  `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_comp`, and it is again a
  transport statement: both comparisons are assembled from the same spaces-étale data, the one
  by the chain of `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage` and
  the other by `CategoryTheory.Adjunction.leftAdjointUniq` of two transported adjunctions.
  Conjugation by the equivalences only whiskers a comparison
  (`CategoryTheory.leftAdjointUniq_transport`), and the pair of retypings
  `CategoryTheory.Adjunction.ofNatIsoLeft` and `CategoryTheory.Adjunction.ofNatIsoRight` by
  which `AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward` presents its adjoints
  are both identities — the one on the right because it cancels an equivalence against its own
  unit, the one on the left because the Stacks 03G1 square for postcomposition is strict
  (`AlgebraicGeometry.Space.smallEtalePostcompComparisonSquare_eq_refl`).

So the bridge is available, with no hypothesis.  The step it was wanted for, and which is not
carried out here, is the *compatibility* of the chart-to-slice dictionary with the composition
isomorphisms, that is, that
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso` and
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso` carry
`AlgebraicGeometry.Space.chartRestrictionComp` and
`AlgebraicGeometry.Space.chartInverseImageComp` to `CategoryTheory.Sheaf.pushforwardOverMapIso`
and `CategoryTheory.GrothendieckTopology.overMapPullbackComp`.  Those are the two squares which
turn a chartwise datum, or a morphism of chartwise data, into the slice-indexed form of
Stacks 0GWK, and they are
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp` and
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso_comp` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence`.  With them, fullness
and essential surjectivity follow from `CategoryTheory.SiteGlueing.canonicalEquivalence` the way
faithfulness already does here, and the equivalence of Stacks 03LS is
`AlgebraicGeometry.Space.chartGlueingEquivalence` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueingEquivalence`.

## References

* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The pentagon in the orientation a cocycle condition uses -/

/-- The pentagon of Stacks 03G2, part (3), on inverse images
(`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc`), rearranged: the
comparison isomorphisms are composed in the direction `g^{-1}f^{-1} ≅ (f ≫ g)^{-1}`, which is
the direction in which a cocycle condition uses them. -/
theorem smallToposMorphism_comp_inverseImage_assoc_inv {Y₀ Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}
    (g : Y₀ ⟶ Y₁) (f : Y₁ ⟶ Y₂) (a : Y₂ ⟶ Y₃) :
    Functor.whiskerRight (smallToposMorphism_comp_inverseImage B S hS f a).inv
        ((smallToposMorphism B S hS g).inverseImage) ≫
      (smallToposMorphism_comp_inverseImage B S hS g (f ≫ a)).inv =
    Functor.whiskerLeft ((smallToposMorphism B S hS a).inverseImage)
        (smallToposMorphism_comp_inverseImage B S hS g f).inv ≫
      (smallToposMorphism_comp_inverseImage B S hS (g ≫ f) a).inv ≫
      eqToHom (congrArg (fun k : Y₀ ⟶ Y₃ => (smallToposMorphism B S hS k).inverseImage)
        (Category.assoc g f a)) := by
  have pent := smallToposMorphism_comp_inverseImage_assoc B S hS g f a
  have hassoc : (Functor.associator ((smallToposMorphism B S hS a).inverseImage)
      ((smallToposMorphism B S hS f).inverseImage)
      ((smallToposMorphism B S hS g).inverseImage)).hom = 𝟙 _ := rfl
  rw [hassoc, Category.id_comp] at pent
  have step : Functor.whiskerRight (smallToposMorphism_comp_inverseImage B S hS f a).hom
        ((smallToposMorphism B S hS g).inverseImage) ≫
      Functor.whiskerLeft ((smallToposMorphism B S hS a).inverseImage)
          (smallToposMorphism_comp_inverseImage B S hS g f).inv ≫
        (smallToposMorphism_comp_inverseImage B S hS (g ≫ f) a).inv =
      (smallToposMorphism_comp_inverseImage B S hS g (f ≫ a)).inv ≫
        eqToHom (congrArg (fun k : Y₀ ⟶ Y₃ => (smallToposMorphism B S hS k).inverseImage)
          (Category.assoc g f a).symm) := by
    rw [← pent, Iso.inv_hom_id_assoc]
  rw [← Functor.isoWhiskerRight_inv, Iso.inv_comp_eq, Functor.isoWhiskerRight_hom]
  slice_rhs 1 3 => rw [step]
  simp

/-- `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc_inv` with each composite
of two of the three morphisms named by a morphism of its own and an equality, and the comparison
isomorphisms transported along those equalities.

This is the shape the chart constructions present: the composite of a morphism of charts with the
structure morphism of the target chart is *equal* to the structure morphism of the source chart,
not literally it, and likewise for the represented morphisms of two composable morphisms of
charts. -/
theorem smallToposMorphism_comp_inverseImage_cocycle {Y₀ Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}
    (g : Y₀ ⟶ Y₁) (f : Y₁ ⟶ Y₂) (a : Y₂ ⟶ Y₃) (b : Y₁ ⟶ Y₃) (c : Y₀ ⟶ Y₃) (m : Y₀ ⟶ Y₂)
    (ea : f ≫ a = b) (eb : g ≫ b = c) (ec : g ≫ f = m) (em : m ≫ a = c) :
    Functor.whiskerRight ((smallToposMorphism_comp_inverseImage B S hS f a).inv ≫
          eqToHom (congrArg (fun k : Y₁ ⟶ Y₃ => (smallToposMorphism B S hS k).inverseImage) ea))
        ((smallToposMorphism B S hS g).inverseImage) ≫
      ((smallToposMorphism_comp_inverseImage B S hS g b).inv ≫
        eqToHom (congrArg (fun k : Y₀ ⟶ Y₃ => (smallToposMorphism B S hS k).inverseImage) eb)) =
    Functor.whiskerLeft ((smallToposMorphism B S hS a).inverseImage)
        ((smallToposMorphism_comp_inverseImage B S hS g f).inv ≫
          eqToHom (congrArg (fun k : Y₀ ⟶ Y₂ => (smallToposMorphism B S hS k).inverseImage) ec)) ≫
      ((smallToposMorphism_comp_inverseImage B S hS m a).inv ≫
        eqToHom (congrArg (fun k : Y₀ ⟶ Y₃ => (smallToposMorphism B S hS k).inverseImage) em)) := by
  subst ea
  subst eb
  subst ec
  simpa using smallToposMorphism_comp_inverseImage_assoc_inv B S hS g f a

/-! ### The cocycle condition for the restrictions of a sheaf to the charts -/

variable (X : AlgebraicSpaces B S hS)

/-- **The cocycle condition of Stacks 03LS for the restrictions of a sheaf to the étale scheme
charts of `X`**: restricting to a chart `U`, then to a chart `V` over it, then to a chart `W` over
that, is the same whether the last two steps are taken one at a time or the two morphisms of
charts are composed first.

This is `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_cocycle` at the represented
morphisms of the charts, where the three equalities of morphisms of algebraic spaces are
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace` twice and
`AlgebraicGeometry.Space.chartMap_comp`. -/
@[stacks 03LS "the cocycle condition for the chartwise restrictions"]
theorem chartRestrictionComp_cocycle {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    Functor.whiskerRight (chartRestrictionComp B S hS X f).hom
        (chartInverseImage B S hS X g) ≫ (chartRestrictionComp B S hS X g).hom =
    Functor.whiskerLeft (chartRestriction B S hS X U)
        (chartInverseImageComp B S hS X f g).hom ≫
      (chartRestrictionComp B S hS X (g ≫ f)).hom := by
  simp only [chartRestrictionComp, chartInverseImageComp, chartRestriction, chartInverseImage,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  exact smallToposMorphism_comp_inverseImage_cocycle B S hS (chartMap B S hS X g)
    (chartMap B S hS X f) (chartToSpace B S hS X U) (chartToSpace B S hS X V)
    (chartToSpace B S hS X W) (chartMap B S hS X (g ≫ f))
    (chartMap_comp_chartToSpace B S hS X f) (chartMap_comp_chartToSpace B S hS X g)
    (chartMap_comp B S hS X f g) (chartMap_comp_chartToSpace B S hS X (g ≫ f))

/-! ### The canonical chartwise glueing datum -/

/-- **The canonical chartwise glueing datum of a sheaf** (Stacks 03LS): the restrictions of a
sheaf of sets on the small étale site of `X` to the étale scheme charts of `X`, with the
comparison isomorphisms of `AlgebraicGeometry.Space.chartRestrictionComp` and the cocycle
condition `AlgebraicGeometry.Space.chartRestrictionComp_cocycle`. -/
noncomputable def canonicalChartGlueingData
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) : ChartGlueingData B S hS X where
  sheaf U := (chartRestriction B S hS X U).obj F
  transition f := (chartRestrictionComp B S hS X f).app F
  transition_comp f g := NatTrans.congr_app (chartRestrictionComp_cocycle B S hS X f g) F

/-- **The canonical chartwise description of sheaves on an algebraic space** (Stacks 03LS), as a
functor: a sheaf of sets on the small étale site of `X` goes to the family of its restrictions to
the étale scheme charts of `X`, and a morphism of sheaves to the family of its restrictions, which
is compatible with the comparison isomorphisms by naturality of
`AlgebraicGeometry.Space.chartRestrictionComp`. -/
noncomputable def chartGlueingFunctor :
    Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⥤ ChartGlueingData B S hS X where
  obj F := canonicalChartGlueingData B S hS X F
  map {_F _G} ψ :=
    { app := fun U => (chartRestriction B S hS X U).map ψ
      w := fun f => (chartRestrictionComp B S hS X f).hom.naturality ψ }
  map_id F := ChartGlueingData.hom_ext B S hS X fun U => (chartRestriction B S hS X U).map_id F
  map_comp ψ ψ' :=
    ChartGlueingData.hom_ext B S hS X fun U => (chartRestriction B S hS X U).map_comp ψ ψ'

/-- The canonical chartwise description sends a sheaf to the family of its restrictions to the
charts, by `rfl`. -/
theorem chartGlueingFunctor_obj_sheaf (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (U : SmallEtale B S hS X.1) :
    ((chartGlueingFunctor B S hS X).obj F).sheaf U = (chartRestriction B S hS X U).obj F := rfl

/-- On morphisms the canonical chartwise description is restriction to the charts, by `rfl`. -/
theorem chartGlueingFunctor_map_app
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (ψ : F ⟶ G)
    (U : SmallEtale B S hS X.1) :
    ((chartGlueingFunctor B S hS X).map ψ).app U = (chartRestriction B S hS X U).map ψ := rfl

/-- **The canonical chartwise description of Stacks 03LS is faithful**: a morphism of sheaves on
the small étale site of `X` is determined by its restrictions to the étale scheme charts of `X`.

This is faithfulness of the slice-indexed glueing functor of Stacks 0GWK, which needs only the
object-level dictionary between charts and slices: restriction to a chart is restriction to the
slice followed by an equivalence
(`AlgebraicGeometry.Space.chartRestriction_overPullbackIso`), and an equivalence is faithful. -/
instance chartGlueingFunctor_faithful : (chartGlueingFunctor B S hS X).Faithful where
  map_injective := by
    intro F G ψ ψ' h
    have hU : ∀ U : SmallEtale B S hS X.1,
        ((SmallEtale.topology B S hS X.1).overPullback (Type (u + 1)) U).map ψ =
          ((SmallEtale.topology B S hS X.1).overPullback (Type (u + 1)) U).map ψ' := by
      intro U
      have h1 : (chartRestriction B S hS X U).map ψ = (chartRestriction B S hS X U).map ψ' :=
        congrArg (fun α : (chartGlueingFunctor B S hS X).obj F ⟶
          (chartGlueingFunctor B S hS X).obj G => ChartGlueingData.Hom.app α U) h
      set r := chartRestriction_overPullbackIso B S hS X U with hr
      have h2 : ((SmallEtale.topology B S hS X.1).overPullback (Type (u + 1)) U ⋙
            (chartSliceSheafEquiv B S hS X U).functor).map ψ =
          ((SmallEtale.topology B S hS X.1).overPullback (Type (u + 1)) U ⋙
            (chartSliceSheafEquiv B S hS X U).functor).map ψ' :=
        haveI : IsIso (r.hom.app F) := inferInstance
        (cancel_epi (r.hom.app F)).mp
          (by rw [← r.hom.naturality ψ, h1, r.hom.naturality ψ'])
      simp only [Functor.comp_map] at h2
      exact (chartSliceSheafEquiv B S hS X U).functor.map_injective h2
    exact (SiteGlueing.canonicalFunctor (SmallEtale.topology B S hS X.1)).map_injective
      (SiteGlueing.GlueingData.hom_ext hU)

end AlgebraicGeometry.Space

end
