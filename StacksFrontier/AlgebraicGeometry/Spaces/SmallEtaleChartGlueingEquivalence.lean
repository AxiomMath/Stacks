module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence

/-!
# The chartwise description of sheaves is the slice-indexed one

Stacks 03LS describes a sheaf on the small étale site of an algebraic space `X` by a family of
sheaves on the small étale sites of the étale scheme charts of `X` with comparison isomorphisms
satisfying a cocycle condition; Stacks 0GWK does the same with the slices `X_étale/U`.  The two
dictionary squares — `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp` for a
morphism of charts and `AlgebraicGeometry.Space.chartRestriction_overPullbackIso_comp` for the
structure morphism of a chart — say that the object-by-object dictionary of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure` is compatible with the
composition isomorphisms on both sides.  This file turns them into an *equivalence* between
slice-indexed and chartwise glueing data, identifies the canonical chartwise description with the
canonical slice-indexed one read through it, and so **proves the equivalence of categories of
Stacks 03LS**.

## Main definitions

* `AlgebraicGeometry.Space.sliceToChartGlueingData` and
  `AlgebraicGeometry.Space.sliceToChartFunctor`: the slice-indexed glueing datum of Stacks 0GWK,
  read chartwise.  Its cocycle condition is the dictionary square for a morphism of charts.
* `AlgebraicGeometry.Space.chartToSliceGlueingData`: a chartwise glueing datum read on the
  slices, the quasi-inverse construction.
* `AlgebraicGeometry.Space.chartGlueingEquivalence`: **Stacks 03LS**, the equivalence between
  sheaves of sets on the small étale site of `X` and chartwise glueing data.

## Main results

* `AlgebraicGeometry.Space.sliceToChartFunctor_faithful`,
  `AlgebraicGeometry.Space.sliceToChartFunctor_full` and
  `AlgebraicGeometry.Space.sliceToChartFunctor_essSurj`: the chartwise reading of slice-indexed
  glueing data is an equivalence — fully faithful because the comparison equivalence of
  Stacks 04M0 is, chart by chart, and essentially surjective by the quasi-inverse construction
  above.
* `AlgebraicGeometry.Space.chartGlueingFunctorIso`: the canonical chartwise description of
  Stacks 03LS is the canonical slice-indexed description of Stacks 0GWK read chartwise.  This is
  the dictionary square for the structure morphism of a chart.
* `AlgebraicGeometry.Space.chartGlueingFunctor_full` and
  `AlgebraicGeometry.Space.chartGlueingFunctor_isEquivalence`: the canonical chartwise
  description is full and, with `AlgebraicGeometry.Space.chartGlueingFunctor_faithful` and the
  essential surjectivity above, an equivalence.

## Implementation notes

Every proof here is one rearrangement of a five-fold composite, and every rearrangement is done
in an abstract lemma applied with each morphism given positionally
(`CategoryTheory.comp_bridge_rearrange_cocycle`, `CategoryTheory.comp_naturality_rearrange`,
`CategoryTheory.comp_cancel_rearrange`).  This is forced, and the reason is recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence`: the concrete terms
spell one and the same object both as `F.obj (G.obj T)` and as `(G ⋙ F).obj T`, so the goals are
not type-correct at `implicit` transparency, `CategoryTheory.Category.assoc` has no key to match
and `simp` declines them.  On abstract objects there is nothing to mismatch, and an explicit
application checks only definitional equality.

The quasi-inverse direction needs no mate of the dictionary square.  A chartwise datum is carried
to the slices object by object by the quasi-inverse of the comparison equivalence of Stacks 04M0,
and its transition isomorphisms are the *preimages*, under that fully faithful comparison, of the
dictionary comparison followed by the counits
(`AlgebraicGeometry.Space.chartToSliceTransitionIso`).  So its cocycle condition is an identity
between morphisms of sheaves on a chart, and there the square proved upstream applies directly,
with its two comparisons inverted: that is `CategoryTheory.cocycle_transport`, whose twelve
morphisms and twelve identities are exactly the rearrangement this performs.  The comparison back
to the datum one started from is then the counit chart by chart, and its compatibility with the
transitions is the cancellation `CategoryTheory.comp_sandwich_cancel`.

## References

* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

/-- The rearrangement that turns a naturality square, a dictionary square and a cocycle
condition into the cocycle condition of a transported glueing datum.  Stated abstractly, and with
the first composite given as a morphism of its own, so that an application checks only
definitional equality. -/
theorem comp_bridge_rearrange_cocycle {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ Bo P Q : C}
    (a₀ : A₀ ⟶ A₂) (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) {c₁ : A₁ ⟶ Bo}
    {b₁ : Bo ⟶ A₃} (p : A₀ ⟶ P) (q : P ⟶ Q) (e : Q ⟶ Bo) (w : Q ⟶ A₄) (ha₀ : a₀ = a ≫ b)
    (hnat : b ≫ c = c₁ ≫ b₁) (hbr : a ≫ c₁ = p ≫ q ≫ e) (hcps : e ≫ b₁ ≫ d = w) :
    a₀ ≫ c ≫ d = p ≫ q ≫ w := by
  rw [ha₀, Category.assoc, reassoc_of% hnat, reassoc_of% hbr, hcps]

/-- The rearrangement that turns a naturality square and a compatibility identity into the
compatibility of a transported morphism of glueing data. -/
theorem comp_naturality_rearrange {C : Type*} [Category C] {A₀ A₁ A₂ A₃ Bo T : C} (a : A₀ ⟶ A₁)
    (c : A₁ ⟶ A₂) (d : A₂ ⟶ A₃) {c₁ : A₀ ⟶ Bo} {b₁ : Bo ⟶ A₂} (d' : Bo ⟶ T) (z : T ⟶ A₃)
    (hnat : a ≫ c = c₁ ≫ b₁) (hmix : b₁ ≫ d = d' ≫ z) :
    a ≫ c ≫ d = (c₁ ≫ d') ≫ z := by
  rw [← Category.assoc a, hnat, Category.assoc, hmix, Category.assoc]

/-- The rearrangement that recovers a compatibility identity from its image under a dictionary:
the naturality square moves the dictionary comparison across, and what is left is the identity
one already has. -/
theorem comp_cancel_rearrange {C : Type*} [Category C] {A₀ A₁ A₂ A₃ Bo T : C} (a : A₀ ⟶ A₁)
    (c : A₁ ⟶ A₂) (d : A₂ ⟶ A₃) (c₁ : A₀ ⟶ Bo) (b₁ : Bo ⟶ A₂) (d' : Bo ⟶ T) (z : T ⟶ A₃)
    (hnat : a ≫ c = c₁ ≫ b₁) (hw : a ≫ c ≫ d = (c₁ ≫ d') ≫ z) :
    c₁ ≫ b₁ ≫ d = c₁ ≫ d' ≫ z := by
  rw [← Category.assoc, ← hnat, Category.assoc, hw, Category.assoc]

/-- The rearrangement that proves the cocycle condition of a glueing datum transported *against*
a dictionary: the dictionary square, read with the comparisons inverted, together with the
cocycle condition of the datum one started from and the naturality of the two composition
comparisons.

All twelve morphisms are given positionally and every invertibility is supplied as an explicit
retraction, so that an application checks only definitional equality: the concrete terms spell
one object both as `F.obj (G.obj T)` and as `(G ⋙ F).obj T`, which defeats `rw` and `simp` on
the goal itself. -/
theorem cocycle_transport {C : Type*} [Category C]
    {A₁ A₂ A₃ A₄ A₅ A₆ A₇ M₀ M₁ N Sw Z : C} (m : M₀ ⟶ M₁) (h : M₀ ⟶ N) (εg : M₁ ⟶ Z)
    (εgf : N ⟶ Z) (c₁ : A₁ ⟶ M₀) (c₁inv : M₀ ⟶ A₁) (pgεf : A₁ ⟶ A₂) (qgV : A₂ ⟶ M₁)
    (qgVinv : M₁ ⟶ A₂) (pgcV : A₂ ⟶ A₃) (pgcVinv : A₃ ⟶ A₂) (tg : A₃ ⟶ Sw) (cWinv : Sw ⟶ Z)
    (pga : A₁ ⟶ A₆) (a : A₆ ⟶ A₁) (pgPfcU : A₆ ⟶ A₇) (pgtf : A₇ ⟶ A₃) (p : A₇ ⟶ A₅)
    (tgf : A₅ ⟶ Sw) (p' : A₆ ⟶ A₄) (pgfcU : A₄ ⟶ A₅) (q : A₄ ⟶ N) (qinv : N ⟶ A₄) (e : N ⟶ M₀)
    (hc₁ : c₁inv ≫ c₁ = 𝟙 M₀) (hnat : pgεf ≫ qgV = c₁ ≫ m)
    (hεg : εg = qgVinv ≫ pgcV ≫ tg ≫ cWinv) (hqgV : qgV ≫ qgVinv = 𝟙 A₂)
    (hpgεf : pgεf = pga ≫ pgPfcU ≫ pgtf ≫ pgcVinv) (hcV : pgcVinv ≫ pgcV = 𝟙 A₃)
    (hcoc : pgtf ≫ tg = p ≫ tgf) (hnatCIC : pgPfcU ≫ p = p' ≫ pgfcU)
    (hsq : a ≫ c₁ = p' ≫ q ≫ e) (hpga : pga ≫ a = 𝟙 A₁) (heh : e ≫ h = 𝟙 N)
    (hq : q ≫ qinv = 𝟙 A₄) (hεgf : εgf = qinv ≫ pgfcU ≫ tgf ≫ cWinv) :
    m ≫ εg = h ≫ εgf := by
  have hc : pga ≫ p' ≫ q ≫ e = c₁ := by
    rw [← hsq, ← Category.assoc, hpga, Category.id_comp]
  have key : pga ≫ p' = c₁ ≫ h ≫ qinv := by
    rw [← hc]
    simp only [Category.assoc]
    rw [← Category.assoc e, heh, Category.id_comp, hq, Category.comp_id]
  have main : c₁ ≫ m ≫ εg = c₁ ≫ h ≫ εgf := by
    rw [← reassoc_of% hnat, hεg, reassoc_of% hqgV, hpgεf]
    simp only [Category.assoc]
    rw [reassoc_of% hcV, reassoc_of% hcoc, reassoc_of% hnatCIC, reassoc_of% key, hεgf]
  simpa [reassoc_of% hc₁] using c₁inv ≫= main

/-- Two equal morphisms, composed with identities on either side, agree.  Stated abstractly
because the two sides of the concrete statement spell their endpoints differently — once through
the glueing datum of a sheaf and once through the restriction of that sheaf — so
`CategoryTheory.Category.comp_id` has no key to match. -/
theorem comp_id_eq_id_comp {C : Type*} [Category C] {A Bo : C} (x y : A ⟶ Bo) (h : x = y) :
    x ≫ 𝟙 Bo = 𝟙 A ≫ y := by rw [Category.comp_id, Category.id_comp, h]

/-- The same with the identity on the left given as a morphism known to be one. -/
theorem id_comp_eq_comp_id {C : Type*} [Category C] {A Bo : C} (e : A ⟶ A) (x y : A ⟶ Bo)
    (he : e = 𝟙 A) (h : x = y) : e ≫ x = y ≫ 𝟙 Bo := by
  rw [he, Category.id_comp, Category.comp_id, h]

/-- A composite sandwiched between a comparison isomorphism and its inverse is the composite.
Stated abstractly, with the two inverses given positionally, for the same reason as the other
rearrangements here. -/
theorem comp_sandwich_cancel {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ : C} (x : A₀ ⟶ A₁)
    (xinv : A₁ ⟶ A₀) (y : A₀ ⟶ A₂) (z : A₂ ⟶ A₃) (winv : A₃ ⟶ A₄) (w : A₄ ⟶ A₃)
    (hx : x ≫ xinv = 𝟙 A₀) (hw : winv ≫ w = 𝟙 A₃) :
    (x ≫ xinv ≫ y ≫ z ≫ winv) ≫ w = y ≫ z := by
  rw [← Category.assoc x, hx, Category.id_comp]
  simp only [Category.assoc]
  rw [hw, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Slice-indexed glueing data read chartwise -/

/-- The transition isomorphism of the chartwise reading of a slice-indexed glueing datum: the
chart-to-slice dictionary followed by the datum's own comparison isomorphism, read through the
comparison equivalence of Stacks 04M0. -/
def sliceToChartTransition (D : SiteGlueing.GlueingData.{u + 1} (SmallEtale.topology B S hS X.1))
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartInverseImage B S hS X f).obj
        ((chartSliceSheafEquiv B S hS X U).functor.obj (D.sheaf U)) ≅
      (chartSliceSheafEquiv B S hS X V).functor.obj (D.sheaf V) :=
  (chartInverseImage_overMapPullbackIso B S hS X f).app (D.sheaf U) ≪≫
    (chartSliceSheafEquiv B S hS X V).functor.mapIso (D.iso f)

/-- **A slice-indexed glueing datum read chartwise.**  The sheaves on the slices `X_étale/U` of
a glueing datum of Stacks 0GWK, read as sheaves on the small étale sites of the charts through
the comparison equivalence of Stacks 04M0, form a chartwise glueing datum in the sense of
Stacks 03LS.  The cocycle condition is the dictionary square
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp` together with the datum's
own cocycle condition. -/
def sliceToChartGlueingData
    (D : SiteGlueing.GlueingData.{u + 1} (SmallEtale.topology B S hS X.1)) :
    ChartGlueingData B S hS X where
  sheaf U := (chartSliceSheafEquiv B S hS X U).functor.obj (D.sheaf U)
  transition f := sliceToChartTransition B S hS X D f
  transition_comp {W V U} f g := by
    have key : (((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app
          (D.sheaf U)) ≫
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) g).map (D.iso f).hom ≫
          (D.iso g).hom) = (D.iso (g ≫ f)).hom := by
      rw [D.comp f g]
      simp
    have hcps : (chartSliceSheafEquiv B S hS X W).functor.map
            (((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app
              (D.sheaf U)) ≫
          (chartSliceSheafEquiv B S hS X W).functor.map
            (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) g).map
              (D.iso f).hom) ≫
            (chartSliceSheafEquiv B S hS X W).functor.map (D.iso g).hom =
        (chartSliceSheafEquiv B S hS X W).functor.map (D.iso (g ≫ f)).hom := by
      rw [← Functor.map_comp, ← Functor.map_comp, key]
    exact comp_bridge_rearrange_cocycle
      ((chartInverseImage B S hS X g).map (sliceToChartTransition B S hS X D f).hom)
      ((chartInverseImage B S hS X g).map
        ((chartInverseImage_overMapPullbackIso B S hS X f).hom.app (D.sheaf U)))
      ((chartInverseImage B S hS X g).map
        ((chartSliceSheafEquiv B S hS X V).functor.map (D.iso f).hom))
      ((chartInverseImage_overMapPullbackIso B S hS X g).hom.app (D.sheaf V))
      ((chartSliceSheafEquiv B S hS X W).functor.map (D.iso g).hom)
      ((chartInverseImageComp B S hS X f g).hom.app
        ((chartSliceSheafEquiv B S hS X U).functor.obj (D.sheaf U)))
      ((chartInverseImage_overMapPullbackIso B S hS X (g ≫ f)).hom.app (D.sheaf U))
      ((chartSliceSheafEquiv B S hS X W).functor.map
        (((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app
          (D.sheaf U)))
      ((chartSliceSheafEquiv B S hS X W).functor.map (D.iso (g ≫ f)).hom)
      ((chartInverseImage B S hS X g).map_comp _ _)
      ((chartInverseImage_overMapPullbackIso B S hS X g).hom.naturality (D.iso f).hom)
      (chartInverseImage_overMapPullbackIso_comp B S hS X f g (D.sheaf U)) hcps

/-- **The slice-indexed description of Stacks 0GWK, read chartwise**, as a functor to the
chartwise glueing data of Stacks 03LS. -/
def sliceToChartFunctor :
    SiteGlueing.GlueingData.{u + 1} (SmallEtale.topology B S hS X.1) ⥤
      ChartGlueingData B S hS X where
  obj D := sliceToChartGlueingData B S hS X D
  map {D E} α :=
    { app := fun U => (chartSliceSheafEquiv B S hS X U).functor.map (α.app U)
      w := fun {V U} f => by
        have hmix : (chartSliceSheafEquiv B S hS X V).functor.map
                (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).map
                  (α.app U)) ≫
              (chartSliceSheafEquiv B S hS X V).functor.map (E.iso f).hom =
            (chartSliceSheafEquiv B S hS X V).functor.map (D.iso f).hom ≫
              (chartSliceSheafEquiv B S hS X V).functor.map (α.app V) := by
          rw [← Functor.map_comp, ← Functor.map_comp, α.w f]
        exact comp_naturality_rearrange
          ((chartInverseImage B S hS X f).map
            ((chartSliceSheafEquiv B S hS X U).functor.map (α.app U)))
          ((chartInverseImage_overMapPullbackIso B S hS X f).hom.app (E.sheaf U))
          ((chartSliceSheafEquiv B S hS X V).functor.map (E.iso f).hom)
          ((chartSliceSheafEquiv B S hS X V).functor.map (D.iso f).hom)
          ((chartSliceSheafEquiv B S hS X V).functor.map (α.app V))
          ((chartInverseImage_overMapPullbackIso B S hS X f).hom.naturality (α.app U)) hmix }
  map_id D :=
    ChartGlueingData.hom_ext B S hS X fun U =>
      (chartSliceSheafEquiv B S hS X U).functor.map_id (D.sheaf U)
  map_comp α β :=
    ChartGlueingData.hom_ext B S hS X fun U =>
      (chartSliceSheafEquiv B S hS X U).functor.map_comp (α.app U) (β.app U)

/-- The chartwise reading of a slice-indexed glueing datum carries the sheaf on a slice to the
sheaf on the chart, by `rfl`. -/
theorem sliceToChartFunctor_obj_sheaf
    (D : SiteGlueing.GlueingData.{u + 1} (SmallEtale.topology B S hS X.1))
    (U : SmallEtale B S hS X.1) :
    ((sliceToChartFunctor B S hS X).obj D).sheaf U =
      (chartSliceSheafEquiv B S hS X U).functor.obj (D.sheaf U) := rfl

/-- On morphisms, the chartwise reading of a slice-indexed glueing datum is the comparison
equivalence of Stacks 04M0 chart by chart, by `rfl`. -/
theorem sliceToChartFunctor_map_app
    {D E : SiteGlueing.GlueingData.{u + 1} (SmallEtale.topology B S hS X.1)} (α : D ⟶ E)
    (U : SmallEtale B S hS X.1) :
    ((sliceToChartFunctor B S hS X).map α).app U =
      (chartSliceSheafEquiv B S hS X U).functor.map (α.app U) := rfl

/-! ### Full faithfulness -/

/-- **The chartwise reading of slice-indexed glueing data is faithful**: a morphism of
slice-indexed data is determined by its components, and the comparison equivalence of Stacks 04M0
is faithful at every chart. -/
instance sliceToChartFunctor_faithful : (sliceToChartFunctor B S hS X).Faithful where
  map_injective {D E} {_ _} h :=
    SiteGlueing.GlueingData.hom_ext fun U =>
      (chartSliceSheafEquiv B S hS X U).functor.map_injective
        (congrArg (fun γ : (sliceToChartFunctor B S hS X).obj D ⟶
          (sliceToChartFunctor B S hS X).obj E => ChartGlueingData.Hom.app γ U) h)

/-- **The chartwise reading of slice-indexed glueing data is full.**  A chartwise morphism is a
morphism of each chart sheaf, so it comes from a morphism of each slice sheaf because the
comparison equivalence of Stacks 04M0 is full; that family is compatible with the slice-side
comparison isomorphisms because the dictionary comparison is an isomorphism and natural, so the
chartwise compatibility can be moved across it. -/
instance sliceToChartFunctor_full : (sliceToChartFunctor B S hS X).Full where
  map_surjective {D E} γ := by
    choose ap hap using fun U : SmallEtale B S hS X.1 =>
      (chartSliceSheafEquiv B S hS X U).functor.map_surjective (γ.app U)
    refine ⟨{ app := ap, w := fun {V U} f => ?_ }, ChartGlueingData.hom_ext B S hS X hap⟩
    refine (chartSliceSheafEquiv B S hS X V).functor.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    refine (cancel_epi ((chartInverseImage_overMapPullbackIso B S hS X f).hom.app
      (D.sheaf U))).mp ?_
    refine comp_cancel_rearrange ((chartInverseImage B S hS X f).map (γ.app U))
      ((chartInverseImage_overMapPullbackIso B S hS X f).hom.app (E.sheaf U))
      ((chartSliceSheafEquiv B S hS X V).functor.map (E.iso f).hom)
      ((chartInverseImage_overMapPullbackIso B S hS X f).hom.app (D.sheaf U))
      ((chartSliceSheafEquiv B S hS X V).functor.map
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).map (ap U)))
      ((chartSliceSheafEquiv B S hS X V).functor.map (D.iso f).hom)
      ((chartSliceSheafEquiv B S hS X V).functor.map (ap V)) ?_ ?_
    · rw [← hap U]
      exact (chartInverseImage_overMapPullbackIso B S hS X f).hom.naturality (ap U)
    · rw [hap V]
      exact γ.w f

/-! ### The canonical chartwise description is the canonical slice-indexed one -/

/-- The comparison of the canonical chartwise glueing datum of a sheaf with the chartwise reading
of its canonical slice-indexed glueing datum: restriction to a chart is restriction to the slice,
and the comparison isomorphisms correspond by the dictionary square for the structure morphism of
a chart. -/
def chartGlueingFunctorHom (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (chartGlueingFunctor B S hS X).obj F ⟶
      (sliceToChartFunctor B S hS X).obj
        ((SiteGlueing.canonicalFunctor (SmallEtale.topology B S hS X.1)).obj F) where
  app U := (chartRestriction_overPullbackIso B S hS X U).hom.app F
  w f := chartRestriction_overPullbackIso_comp B S hS X f F

/-- The comparison `AlgebraicGeometry.Space.chartGlueingFunctorHom` is an isomorphism, since each
of its components is. -/
instance isIso_chartGlueingFunctorHom
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    IsIso (chartGlueingFunctorHom B S hS X F) :=
  ChartGlueingData.isIso_of_isIso_app B S hS X _ fun U =>
    inferInstanceAs (IsIso ((chartRestriction_overPullbackIso B S hS X U).app F).hom)

/-- **The canonical chartwise description of Stacks 03LS is the canonical slice-indexed
description of Stacks 0GWK, read chartwise.**  Its component at a sheaf is
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso`, and the compatibility with the
comparison isomorphisms is the dictionary square for the structure morphism of a chart. -/
def chartGlueingFunctorIso :
    chartGlueingFunctor B S hS X ≅
      SiteGlueing.canonicalFunctor (SmallEtale.topology B S hS X.1) ⋙
        sliceToChartFunctor B S hS X :=
  NatIso.ofComponents (fun F => asIso (chartGlueingFunctorHom B S hS X F)) fun {_ _} ψ =>
    ChartGlueingData.hom_ext B S hS X fun U =>
      (chartRestriction_overPullbackIso B S hS X U).hom.naturality ψ

/-- **The canonical chartwise description of Stacks 03LS is full.**  With
`AlgebraicGeometry.Space.chartGlueingFunctor_faithful` it is fully faithful: it is the canonical
slice-indexed description of Stacks 0GWK, which is an equivalence, followed by the fully faithful
chartwise reading. -/
instance chartGlueingFunctor_full : (chartGlueingFunctor B S hS X).Full :=
  Functor.Full.of_iso (chartGlueingFunctorIso B S hS X).symm

/-! ### Chartwise glueing data read on the slices -/

/-- The sheaf on the slice `X_étale/U` attached to a chartwise glueing datum, by the
quasi-inverse of the comparison equivalence of Stacks 04M0. -/
def chartToSliceSheaf (D : ChartGlueingData B S hS X) (U : SmallEtale B S hS X.1) :
    Sheaf ((SmallEtale.topology B S hS X.1).over U) (Type (u + 1)) :=
  (chartSliceSheafEquiv B S hS X U).inverse.obj (D.sheaf U)

/-- The transition isomorphism of a chartwise glueing datum, transported to the slice sheaves and
read back on the charts: the chart-to-slice dictionary, the counits of the comparison equivalence
of Stacks 04M0 at the two charts, and the datum's own transition. -/
def chartToSliceTransitionIso (D : ChartGlueingData B S hS X) {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) :
    (chartSliceSheafEquiv B S hS X V).functor.obj
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj
          (chartToSliceSheaf B S hS X D U)) ≅
      (chartSliceSheafEquiv B S hS X V).functor.obj (chartToSliceSheaf B S hS X D V) :=
  ((chartInverseImage_overMapPullbackIso B S hS X f).app
      (chartToSliceSheaf B S hS X D U)).symm ≪≫
    (chartInverseImage B S hS X f).mapIso
      ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)) ≪≫
      D.transition f ≪≫ ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).symm

/-- The transition isomorphism of the slice-indexed reading of a chartwise glueing datum: the
preimage of `AlgebraicGeometry.Space.chartToSliceTransitionIso` under the comparison equivalence
of Stacks 04M0, which is fully faithful. -/
def chartToSliceTransition (D : ChartGlueingData B S hS X) {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) :
    ((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj
        (chartToSliceSheaf B S hS X D U) ≅ chartToSliceSheaf B S hS X D V :=
  (chartSliceSheafEquiv B S hS X V).functor.preimageIso (chartToSliceTransitionIso B S hS X D f)

/-- The comparison equivalence of Stacks 04M0 carries
`AlgebraicGeometry.Space.chartToSliceTransition` back to
`AlgebraicGeometry.Space.chartToSliceTransitionIso`. -/
theorem map_chartToSliceTransition_hom (D : ChartGlueingData B S hS X)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartSliceSheafEquiv B S hS X V).functor.map (chartToSliceTransition B S hS X D f).hom =
      (chartToSliceTransitionIso B S hS X D f).hom := by
  rw [chartToSliceTransition, Functor.preimageIso_hom, Functor.map_preimage]

/-- **A chartwise glueing datum read on the slices.**  The cocycle condition is the dictionary
square `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp` read with its
comparisons inverted, together with the chartwise cocycle condition and the naturality of the two
composition comparisons. -/
def chartToSliceGlueingData (D : ChartGlueingData B S hS X) :
    SiteGlueing.GlueingData.{u + 1} (SmallEtale.topology B S hS X.1) where
  sheaf U := chartToSliceSheaf B S hS X D U
  iso f := chartToSliceTransition B S hS X D f
  comp {W V U} f g := by
    have hnat : (chartInverseImage B S hS X g).map (chartToSliceTransitionIso B S hS X D f).hom ≫
          ((chartInverseImage_overMapPullbackIso B S hS X g).app
            (chartToSliceSheaf B S hS X D V)).hom =
        ((chartInverseImage_overMapPullbackIso B S hS X g).app
            (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj
              (chartToSliceSheaf B S hS X D U))).hom ≫
          (chartSliceSheafEquiv B S hS X W).functor.map
            (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) g).map
              (chartToSliceTransition B S hS X D f).hom) := by
      rw [← map_chartToSliceTransition_hom B S hS X D f]
      exact (chartInverseImage_overMapPullbackIso B S hS X g).hom.naturality
        (chartToSliceTransition B S hS X D f).hom
    have hpgεf : (chartInverseImage B S hS X g).map
          (chartToSliceTransitionIso B S hS X D f).hom =
        (chartInverseImage B S hS X g).map
            (((chartInverseImage_overMapPullbackIso B S hS X f).app
              (chartToSliceSheaf B S hS X D U)).inv) ≫
          (chartInverseImage B S hS X g).map ((chartInverseImage B S hS X f).map
              ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom) ≫
            (chartInverseImage B S hS X g).map (D.transition f).hom ≫
              (chartInverseImage B S hS X g).map
                ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).inv := by
      simp only [← Functor.map_comp]
      rfl
    have hcV : (chartInverseImage B S hS X g).map
          ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).inv ≫
        (chartInverseImage B S hS X g).map
          ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).hom = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id, (chartInverseImage B S hS X g).map_id]
    have hpga : (chartInverseImage B S hS X g).map
          (((chartInverseImage_overMapPullbackIso B S hS X f).app
            (chartToSliceSheaf B S hS X D U)).inv) ≫
        (chartInverseImage B S hS X g).map
          (((chartInverseImage_overMapPullbackIso B S hS X f).app
            (chartToSliceSheaf B S hS X D U)).hom) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id, (chartInverseImage B S hS X g).map_id]
    have heh : (chartSliceSheafEquiv B S hS X W).functor.map
          ((((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).app
            (chartToSliceSheaf B S hS X D U)).inv) ≫
        (chartSliceSheafEquiv B S hS X W).functor.map
          ((((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).app
            (chartToSliceSheaf B S hS X D U)).hom) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id, (chartSliceSheafEquiv B S hS X W).functor.map_id]
    have hεg : (chartSliceSheafEquiv B S hS X W).functor.map
          (chartToSliceTransition B S hS X D g).hom =
        ((chartInverseImage_overMapPullbackIso B S hS X g).app
            (chartToSliceSheaf B S hS X D V)).inv ≫
          (chartInverseImage B S hS X g).map
            ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).hom ≫
            (D.transition g).hom ≫
              ((chartSliceSheafEquiv B S hS X W).counitIso.app (D.sheaf W)).inv :=
      map_chartToSliceTransition_hom B S hS X D g
    have hεgf : (chartSliceSheafEquiv B S hS X W).functor.map
          (chartToSliceTransition B S hS X D (g ≫ f)).hom =
        ((chartInverseImage_overMapPullbackIso B S hS X (g ≫ f)).app
            (chartToSliceSheaf B S hS X D U)).inv ≫
          (chartInverseImage B S hS X (g ≫ f)).map
            ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom ≫
            (D.transition (g ≫ f)).hom ≫
              ((chartSliceSheafEquiv B S hS X W).counitIso.app (D.sheaf W)).inv :=
      map_chartToSliceTransition_hom B S hS X D (g ≫ f)
    refine (chartSliceSheafEquiv B S hS X W).functor.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact cocycle_transport
      ((chartSliceSheafEquiv B S hS X W).functor.map
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) g).map
          (chartToSliceTransition B S hS X D f).hom))
      ((chartSliceSheafEquiv B S hS X W).functor.map
        ((((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).app
          (chartToSliceSheaf B S hS X D U)).hom))
      ((chartSliceSheafEquiv B S hS X W).functor.map
        (chartToSliceTransition B S hS X D g).hom)
      ((chartSliceSheafEquiv B S hS X W).functor.map
        (chartToSliceTransition B S hS X D (g ≫ f)).hom)
      (((chartInverseImage_overMapPullbackIso B S hS X g).app
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj
          (chartToSliceSheaf B S hS X D U))).hom)
      (((chartInverseImage_overMapPullbackIso B S hS X g).app
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj
          (chartToSliceSheaf B S hS X D U))).inv)
      ((chartInverseImage B S hS X g).map (chartToSliceTransitionIso B S hS X D f).hom)
      (((chartInverseImage_overMapPullbackIso B S hS X g).app
        (chartToSliceSheaf B S hS X D V)).hom)
      (((chartInverseImage_overMapPullbackIso B S hS X g).app
        (chartToSliceSheaf B S hS X D V)).inv)
      ((chartInverseImage B S hS X g).map
        ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).hom)
      ((chartInverseImage B S hS X g).map
        ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).inv)
      ((D.transition g).hom)
      (((chartSliceSheafEquiv B S hS X W).counitIso.app (D.sheaf W)).inv)
      ((chartInverseImage B S hS X g).map
        (((chartInverseImage_overMapPullbackIso B S hS X f).app
          (chartToSliceSheaf B S hS X D U)).inv))
      ((chartInverseImage B S hS X g).map
        (((chartInverseImage_overMapPullbackIso B S hS X f).app
          (chartToSliceSheaf B S hS X D U)).hom))
      ((chartInverseImage B S hS X g).map ((chartInverseImage B S hS X f).map
        ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom))
      ((chartInverseImage B S hS X g).map (D.transition f).hom)
      ((chartInverseImageComp B S hS X f g).hom.app (D.sheaf U))
      ((D.transition (g ≫ f)).hom)
      ((chartInverseImageComp B S hS X f g).hom.app
        ((chartSliceSheafEquiv B S hS X U).functor.obj (chartToSliceSheaf B S hS X D U)))
      ((chartInverseImage B S hS X (g ≫ f)).map
        ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom)
      (((chartInverseImage_overMapPullbackIso B S hS X (g ≫ f)).app
        (chartToSliceSheaf B S hS X D U)).hom)
      (((chartInverseImage_overMapPullbackIso B S hS X (g ≫ f)).app
        (chartToSliceSheaf B S hS X D U)).inv)
      ((chartSliceSheafEquiv B S hS X W).functor.map
        ((((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).app
          (chartToSliceSheaf B S hS X D U)).inv))
      (Iso.inv_hom_id _) hnat hεg (Iso.hom_inv_id _) hpgεf hcV (D.transition_comp f g)
      ((chartInverseImageComp B S hS X f g).hom.naturality
        ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom)
      (chartInverseImage_overMapPullbackIso_comp B S hS X f g
        (chartToSliceSheaf B S hS X D U))
      hpga heh (Iso.hom_inv_id _) hεgf

/-- The comparison from the chartwise reading of the slice-indexed reading of a chartwise glueing
datum back to the datum: the counit of the comparison equivalence of Stacks 04M0 at every
chart. -/
def sliceToChartOfChartToSliceHom (D : ChartGlueingData B S hS X) :
    (sliceToChartFunctor B S hS X).obj (chartToSliceGlueingData B S hS X D) ⟶ D where
  app U := ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom
  w {V U} f := by
    have h1 : ((((sliceToChartFunctor B S hS X).obj
          (chartToSliceGlueingData B S hS X D)).transition f).hom) =
        ((chartInverseImage_overMapPullbackIso B S hS X f).app
            (chartToSliceSheaf B S hS X D U)).hom ≫
          (chartSliceSheafEquiv B S hS X V).functor.map
            (chartToSliceTransition B S hS X D f).hom := rfl
    rw [h1, map_chartToSliceTransition_hom B S hS X D f,
      show (chartToSliceTransitionIso B S hS X D f).hom =
        ((chartInverseImage_overMapPullbackIso B S hS X f).app
            (chartToSliceSheaf B S hS X D U)).inv ≫
          (chartInverseImage B S hS X f).map
            ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom ≫
            (D.transition f).hom ≫
              ((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).inv from rfl]
    exact (comp_sandwich_cancel
      (((chartInverseImage_overMapPullbackIso B S hS X f).app
        (chartToSliceSheaf B S hS X D U)).hom)
      (((chartInverseImage_overMapPullbackIso B S hS X f).app
        (chartToSliceSheaf B S hS X D U)).inv)
      ((chartInverseImage B S hS X f).map
        ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom)
      ((D.transition f).hom)
      (((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).inv)
      (((chartSliceSheafEquiv B S hS X V).counitIso.app (D.sheaf V)).hom)
      (Iso.hom_inv_id _) (Iso.inv_hom_id _)).symm

/-- The comparison `AlgebraicGeometry.Space.sliceToChartOfChartToSliceHom` is an isomorphism,
since each of its components is. -/
instance isIso_sliceToChartOfChartToSliceHom (D : ChartGlueingData B S hS X) :
    IsIso (sliceToChartOfChartToSliceHom B S hS X D) :=
  ChartGlueingData.isIso_of_isIso_app B S hS X _ fun U =>
    inferInstanceAs (IsIso ((chartSliceSheafEquiv B S hS X U).counitIso.app (D.sheaf U)).hom)

/-- **The chartwise reading of slice-indexed glueing data is essentially surjective**: every
chartwise glueing datum is the chartwise reading of its own slice-indexed reading. -/
instance sliceToChartFunctor_essSurj : (sliceToChartFunctor B S hS X).EssSurj where
  mem_essImage D :=
    ⟨chartToSliceGlueingData B S hS X D, ⟨asIso (sliceToChartOfChartToSliceHom B S hS X D)⟩⟩

/-- The chartwise reading of slice-indexed glueing data is an equivalence of categories. -/
instance sliceToChartFunctor_isEquivalence : (sliceToChartFunctor B S hS X).IsEquivalence where

/-- The canonical chartwise description of sheaves on the small étale site of `X` is an
equivalence of categories. -/
instance chartGlueingFunctor_isEquivalence : (chartGlueingFunctor B S hS X).IsEquivalence :=
  Functor.isEquivalence_of_iso (chartGlueingFunctorIso B S hS X).symm

/-- **Stacks 03LS.**  A sheaf of sets on the small étale site of an algebraic space `X` is the
same thing as a family of sheaves `F_U` on the small étale sites of the étale scheme charts `U`
of `X`, together with isomorphisms `c_f : f^{-1}F_U ≅ F_V` for the morphisms `f : V ⟶ U` of
charts satisfying the cocycle condition `c_g ∘ g^{-1}c_f = c_{g ≫ f}` — an *equivalence of
categories*, given by sending a sheaf to the family of its restrictions to the charts.

The proof is the one the source gives: the chartwise inverse image is restriction along
postcomposition (Stacks 03LQ, through Stacks 03LP), so the chartwise data are the slice-indexed
data of Stacks 0GWK read through the comparison equivalence of Stacks 04M0
(`AlgebraicGeometry.Space.sliceToChartFunctor`, an equivalence), and the chartwise description is
the slice-indexed one read through it
(`AlgebraicGeometry.Space.chartGlueingFunctorIso`). -/
@[stacks 03LS]
def chartGlueingEquivalence :
    Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ≌ ChartGlueingData B S hS X :=
  (chartGlueingFunctor B S hS X).asEquivalence

/-- The equivalence of Stacks 03LS is the canonical chartwise description: it sends a sheaf to
the family of its restrictions to the étale scheme charts, by `rfl`. -/
theorem chartGlueingEquivalence_functor :
    (chartGlueingEquivalence B S hS X).functor = chartGlueingFunctor B S hS X := rfl

/-- **Stacks 03LS with its restriction comparison.**  The equivalence of Stacks 03LS together
with the identification of the chart sheaves of the datum it attaches to a sheaf with the
restrictions of that sheaf to the charts, natural in the sheaf and compatible with the comparison
isomorphisms `AlgebraicGeometry.Space.chartRestrictionComp`.

The comparison is the identity: the equivalence *is* the canonical chartwise description
`AlgebraicGeometry.Space.chartGlueingFunctor`, whose datum carries exactly those restrictions. -/
def chartGlueingEquivalenceRestriction :
    { e : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ≌ ChartGlueingData B S hS X //
      ∃ η : ∀ (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
        (U : SmallEtale B S hS X.1),
        (e.functor.obj F).sheaf U ≅ (chartRestriction B S hS X U).obj F,
      (∀ (F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) (a : F ⟶ G)
        (U : SmallEtale B S hS X.1),
        (e.functor.map a).app U ≫ (η G U).hom =
          (η F U).hom ≫ (chartRestriction B S hS X U).map a) ∧
      (∀ (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
        {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
        (chartInverseImage B S hS X f).map (η F U).hom ≫
            (chartRestrictionComp B S hS X f).hom.app F =
          ((e.functor.obj F).transition f).hom ≫ (η F V).hom) } :=
  ⟨chartGlueingEquivalence B S hS X, fun _ _ => Iso.refl _,
    fun _ _ a U => comp_id_eq_id_comp _ _ (chartGlueingFunctor_map_app B S hS X a U),
    fun _ {_ _} f => id_comp_eq_comp_id _ _ _ ((chartInverseImage B S hS X f).map_id _) rfl⟩

end AlgebraicGeometry.Space

end
