module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibreFullFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationCoordinates
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDiagonalUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.CategoryTheory.Sites.Stackification.RawLocalEquality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart of the weighted quotient stack

Let `k` be a commutative ring, `p` a natural number, `U = Spec k[x_0, x_1, …]` with the action
of `𝐆_m` in which `x_i` has weight `p^i`, and `[U/𝐆_m]` the quotient stack of **Stacks 06RE**.
This file reads `[U/𝐆_m]` as an object of the 2-category of algebraic stacks over `Spec ℤ`,
through its small model, and describes it through the chart `U ⟶ [U/𝐆_m]`: its objects are
fppf locally chart objects, its vertical isomorphisms between chart objects are units, and the
isomorphism presheaf of two chart objects is a presheaf of units.

## Main definitions

* `AlgebraicGeometry.PPowerWeighted.weightedQuotientStack`: `[U/𝐆_m]` as an algebraic stack, and
  `AlgebraicGeometry.PPowerWeighted.weightedQuotientPresentation` its presentation by the action
  groupoid.
* `AlgebraicGeometry.PPowerWeighted.chart`: the chart `U ⟶ [U/𝐆_m]`.
* `AlgebraicGeometry.PPowerWeighted.chartVerticalEquiv`: the vertical isomorphisms between the
  chart objects of two `W`-points `h`, `h'` of `U` are the units `γ` of `Γ(W)` with
  `γ • h = h'`.
* `AlgebraicGeometry.PPowerWeighted.chartIsomEquiv`: the sections over `f : V ⟶ W` of the
  isomorphism presheaf of the chart objects of `h` and `h'` are the units `γ` of `Γ(V)` with
  `γ • (f ≫ h) = f ≫ h'`.

## Main results

* `AlgebraicGeometry.PPowerWeighted.isRepresentableByAlgebraicSpaces_chart`,
  `AlgebraicGeometry.PPowerWeighted.hasRelativeProperty_smooth_chart`,
  `AlgebraicGeometry.PPowerWeighted.hasRelativeProperty_surjective_chart`,
  `AlgebraicGeometry.PPowerWeighted.isSurjective_chart` and
  `AlgebraicGeometry.PPowerWeighted.isSmooth_chart`: the chart is a smooth surjective
  1-morphism representable by algebraic spaces.
* `AlgebraicGeometry.PPowerWeighted.exists_chart_isHomLift`: every object of `[U/𝐆_m]` is fppf
  locally the target of a morphism from a chart object (Stacks 044X, part (1)).
* `AlgebraicGeometry.PPowerWeighted.chartVerticalEquiv_comp`,
  `AlgebraicGeometry.PPowerWeighted.chartVerticalEquiv_id` and
  `AlgebraicGeometry.PPowerWeighted.chartMap_comp_chartVerticalEquiv_symm`: composition is
  multiplication of units, the identity is `1`, and restriction along `g : V ⟶ W` is
  restriction of units.
* `AlgebraicGeometry.PPowerWeighted.chartIsomEquiv_naturality`: the identification of the
  isomorphism presheaf is natural.

## Implementation notes

A chart object is, by definition, the image of a point of the object space of the action
groupoid under the canonical map from the pointwise groupoid fibration to the quotient stack,
followed by `CategoryTheory.ShrinkHoms.functor`. Vertical morphisms between such images are the
arrows of the evaluated groupoid by Stacks 044X, part (2)
(`AlgebraicGeometry.Stack.fullyFaithful_pointwiseToQuotientStackFiber`), and these are units by
`AlgebraicGeometry.PPowerWeighted.arrowsEquiv`. Composition in the evaluated groupoid is the
composition morphism of the action groupoid, which multiplies the `𝐆_m`-coordinates
(`AlgebraicGeometry.PPowerWeighted.arrowsEquiv_compose_fst`), read through the heterogeneous
equality `comp_eq` of `AlgebraicGeometry.Space.ActionGroupoidConstruction`.

The isomorphism presheaf is read through the comparison
`AlgebraicGeometry.PPowerWeighted.chartPullbackIso` of the chosen pullback of a chart object with
the chart object of the restricted point; naturality is then the restriction compatibility of the
vertical isomorphisms together with the cartesian property of the images under the chart of the
morphisms of the slice.

The convention for units is that of the arrows of the action groupoid: the arrow `(γ, h)` has
source `h` and target `γ • h`, so the vertical isomorphism `a(h) ⟶ a(h')` of `γ` exists when
`γ • h = h'`.

## References

* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.PPowerWeighted

/-- The base `Spec ℤ` of the site. -/
local macro "𝒵" : term => `(Spec (CommRingCat.of (ULift ℤ)))

variable (𝒞 : BigFppfSite.{u}) (k : Type u) [CommRing k] (p : ℕ)
  (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))

/-- **Stacks 06RE.** The quotient stack `[U/𝐆_m]` of the weighted action, as an object of the
2-category of algebraic stacks over `Spec ℤ` (Stacks 03YP): the small model
`AlgebraicGeometry.Stack.smallQuotientStack` of the quotient stack of the action groupoid, which
is smooth. -/
noncomputable def weightedQuotientStack :
    Stack.AlgebraicStacks.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  Stack.smallQuotientStack.{u, w} (actionGroupoidOverBase 𝒞 k p hU)
    (isSmooth_actionGroupoidOverBase 𝒞 k p hU)

/-- The presentation (Stacks 04TI) of `AlgebraicGeometry.PPowerWeighted.weightedQuotientStack` by
the action groupoid `𝐆_m × U ⇉ U`. -/
noncomputable def weightedQuotientPresentation :
    Stack.GroupoidPresentation 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val :=
  Stack.smallQuotientStackPresentation.{u, w} (actionGroupoidOverBase 𝒞 k p hU)
    (isSmooth_actionGroupoidOverBase 𝒞 k p hU)

/-- The presenting groupoid of the weighted quotient stack is the action groupoid. -/
theorem weightedQuotientPresentation_groupoid :
    (weightedQuotientPresentation.{u, w} 𝒞 k p hU).groupoid = actionGroupoidOverBase 𝒞 k p hU :=
  rfl

/-- The quotient stack of the presenting groupoid is the quotient stack `[U/𝐆_m]` of
`AlgebraicGeometry.PPowerWeighted.quotientStack`. -/
theorem quotientStack_weightedQuotientPresentation :
    Stack.quotientStack (weightedQuotientPresentation.{u, w} 𝒞 k p hU).groupoid =
      quotientStack 𝒞 k p hU :=
  rfl

/-- The presenting equivalence of the weighted quotient stack, from the quotient stack of the
action groupoid to its small model. -/
noncomputable def presentingFunctor :
    Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU) ⥤ᵇ
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val :=
  (weightedQuotientPresentation.{u, w} 𝒞 k p hU).basedFunctor

/-- The presenting functor is an equivalence of categories. -/
noncomputable instance isEquivalence_presentingFunctor :
    (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.IsEquivalence :=
  (weightedQuotientPresentation.{u, w} 𝒞 k p hU).isEquivalence_basedFunctor

/-- The presenting functor is `CategoryTheory.ShrinkHoms.functor`. -/
theorem presentingFunctor_toFunctor :
    (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor =
      ShrinkHoms.functor (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj :=
  rfl

/-- The chart as a functor over the site: the presentation 1-morphism
`AlgebraicGeometry.Stack.schemePresentationHom` of the scheme `U` through
`AlgebraicGeometry.PPowerWeighted.objectsIso`, followed by the presenting equivalence. -/
noncomputable def chartBased :
    (Stack.schemeFibredCategory 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (totalSiteObject 𝒞 k hU)).val ⥤ᵇ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val :=
  BasedFunctor.comp
    (Stack.schemePresentationHom (G := actionGroupoidOverBase 𝒞 k p hU) (objectsIso 𝒞 k p hU).hom)
    (presentingFunctor.{u, w} 𝒞 k p hU)

/-- **The chart `U ⟶ [U/𝐆_m]`**, as a 1-morphism of algebraic stacks: a `W`-point `h` of `U`
goes to the image in the quotient stack of the point of the object space of the action groupoid
named by `h`. -/
noncomputable def chart :
    Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (totalSiteObject 𝒞 k hU) ⟶
      weightedQuotientStack.{u, w} 𝒞 k p hU :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (chartBased.{u, w} 𝒞 k p hU))

/-- **The chart is representable by algebraic spaces**: the projection of Stacks 044R is, by
Stacks 04WZ, and representability is invariant under the presenting equivalence (Stacks 0457). -/
theorem isRepresentableByAlgebraicSpaces_chart :
    Stack.IsRepresentableByAlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (chart.{u, w} 𝒞 k p hU).hom.hom :=
  (Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_target 𝒞 𝒵
    (Space.contains_specULiftZ 𝒞)
    (𝒳 := Stack.schemeFibredCategory 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (totalSiteObject 𝒞 k hU))
    (𝒴 := (weightedQuotientStack.{u, w} 𝒞 k p hU).val)
    (𝒴' := CatFiberedInGroupoids.mk (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU))
      (Stack.isFiberedInGroupoids_quotientStack _))
    (chart.{u, w} 𝒞 k p hU).hom.hom
    (Stack.schemePresentationHom (G := actionGroupoidOverBase 𝒞 k p hU) (objectsIso 𝒞 k p hU).hom)
    (presentingFunctor.{u, w} 𝒞 k p hU) (Iso.refl _)).2
    (Stack.isRepresentableByAlgebraicSpaces_schemePresentationHom _
      (Stack.representable_quotientStackProjectionHom _))

/-- The action groupoid has a presentation in the sense of
`AlgebraicGeometry.Stack.QuotientAtlas.Presentation`, from Stacks 04WZ. -/
theorem quotientAtlasPresentation_exists :
    Nonempty (Stack.QuotientAtlas.Presentation (actionGroupoidOverBase 𝒞 k p hU)) :=
  ⟨Stack.QuotientAtlas.presentationOfRepresentable _
    (Stack.representable_quotientStackProjectionHom _)⟩

/-- The relative property of the chart at a property of morphisms of algebraic spaces which the
isomorphisms and the source of the action groupoid have. -/
theorem relativeProperty_chart
    (P : MorphismProperty (AlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))]
    [P.IsStableUnderComposition]
    (hα : P (ObjectProperty.homMk (objectsIso 𝒞 k p hU).hom :
      schemeSpace (totalSiteObject 𝒞 k hU) ⟶
        (actionGroupoidOverBase 𝒞 k p hU).objects))
    (hsource : P (actionGroupoidOverBase 𝒞 k p hU).source) :
    Stack.HasRelativeProperty.{u, u, u + 1, u} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) P
      (chart.{u, w} 𝒞 k p hU).hom (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU) :=
  Stack.relativeProperty_of_equivalences_symm 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) P
    (𝒳 := Stack.schemeFibredCategory 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (totalSiteObject 𝒞 k hU))
    (𝒴 := (weightedQuotientStack.{u, w} 𝒞 k p hU).val)
    (𝒳' := Stack.schemeFibredCategory 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (totalSiteObject 𝒞 k hU))
    (𝒴' := CatFiberedInGroupoids.mk (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU))
      (Stack.isFiberedInGroupoids_quotientStack _))
    (Stack.schemePresentationHom (G := actionGroupoidOverBase 𝒞 k p hU) (objectsIso 𝒞 k p hU).hom)
    (chart.{u, w} 𝒞 k p hU).hom.hom (BasedFunctor.id _) (presentingFunctor.{u, w} 𝒞 k p hU)
    (Iso.refl _)
    (Stack.relativeProperty_schemePresentationHom.{u, u} P
      (quotientAtlasPresentation_exists 𝒞 k p hU).some _ hα hsource)

/-- **The chart is smooth**, in the relative sense of Stacks 03YK: the source map of the action
groupoid is smooth, and `AlgebraicGeometry.PPowerWeighted.objectsIso` is an isomorphism. -/
theorem hasRelativeProperty_smooth_chart :
    Stack.HasRelativeProperty.{u, u, u + 1, u} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Space.smoothMorphismProperty 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
      (chart.{u, w} 𝒞 k p hU).hom (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU) :=
  relativeProperty_chart 𝒞 k p hU _
    (show Space.IsSmooth 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (objectsIso 𝒞 k p hU).hom from
      @Space.isSmooth_of_isIso 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (isAlgebraicSpace_yoneda 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _)
        (actionGroupoidOverBase 𝒞 k p hU).objects.property (objectsIso 𝒞 k p hU).hom
        (Iso.isIso_hom _))
    (isSmooth_actionGroupoidOverBase 𝒞 k p hU).source

/-- **The chart is surjective**, in the relative sense of Stacks 03YK. -/
theorem hasRelativeProperty_surjective_chart :
    Stack.HasRelativeProperty.{u, u, u + 1, u} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Space.surjectiveMorphismProperty 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
      (chart.{u, w} 𝒞 k p hU).hom (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU) :=
  relativeProperty_chart 𝒞 k p hU _
    (Space.isSurjective_of_isIso 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (objectsIso 𝒞 k p hU).hom)
    (Stack.QuotientAtlas.isSurjective_source _)

/-- **The chart is surjective on points** (Stacks 04ZS), by Stacks 04XI. -/
theorem isSurjective_chart :
    Stack.IsSurjective 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (chart.{u, w} 𝒞 k p hU) :=
  (Stack.pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} 𝒞 𝒵
    (Space.contains_specULiftZ 𝒞) _
    (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU)).2
    (hasRelativeProperty_surjective_chart 𝒞 k p hU)

/-- **The chart is a smooth 1-morphism of algebraic stacks** (Stacks 075U). -/
theorem isSmooth_chart :
    Stack.AlgebraicStacks.IsSmooth 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (chart.{u, w} 𝒞 k p hU) :=
  Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} 𝒞 𝒵
    (Space.contains_specULiftZ 𝒞)
    (fun _ _ k => Space.IsSmooth 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) k)
    (weightedQuotientStack.{u, w} 𝒞 k p hU).property _
    (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU)
    (hasRelativeProperty_smooth_chart 𝒞 k p hU)

section Shrink

variable {𝒞 k hU}

/-- `AlgebraicGeometry.PPowerWeighted.objectsIso` read on a point of the object space. -/
theorem objectsIso_hom_inv_apply {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (x : (actionGroupoid 𝒞 k p hU).objects.obj.obj (op W)) :
    (objectsIso 𝒞 k p hU).hom.app (op W) ((objectsIso 𝒞 k p hU).inv.app (op W) x) = x := by
  simp

/-- A morphism of the weighted quotient stack lies over `f` exactly when its image in the quotient
stack of the action groupoid does. -/
theorem isHomLift_iff_shrink {R T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (f : R ⟶ T)
    {x y : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (θ : x ⟶ y) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift f θ ↔
      (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).p.IsHomLift f
        ((ShrinkHoms.inverse (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj).map θ) :=
  ⟨fun h => have := h; Functor.isHomLift_map_of_comp_eq
      (G := ShrinkHoms.inverse (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj)
      (q := (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).p)
      (p := (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p) rfl f θ,
    fun h => Functor.isHomLift_of_isHomLift_map_of_comp_eq
      (G := ShrinkHoms.inverse (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj)
      (q := (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).p)
      (p := (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p) rfl f θ h⟩

/-- A morphism of the quotient stack of the action groupoid lying over `f` stays over `f` in the
weighted quotient stack. -/
private theorem isHomLift_shrink_functor_map {R T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (f : R ⟶ T) {x y : (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj} (m : x ⟶ y)
    (hm : (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).p.IsHomLift f m) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift f
      ((ShrinkHoms.functor (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj).map m) :=
  (isHomLift_iff_shrink.{u, w} p f _).2
    ((congrArg ((Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).p.IsHomLift f)
      (Equiv.symm_apply_apply (equivShrink _) m)).mpr hm)

end Shrink

/-! ### Local essential surjectivity of the chart -/

/-- **Every object of the weighted quotient stack is fppf locally a chart object.** For an object
`ξ` over `T` there is a covering sieve of `T` such that for every `g : V ⟶ T` in it there are a
`V`-point `h` of `U` and a morphism from the chart object of `h` to `ξ` lying over `g`. This is
part (1) of Stacks 044X: `[U/𝐆_m]` is the stackification of the pointwise groupoid fibration. -/
theorem exists_chart_isHomLift (T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.Fiber T) :
    ∃ R ∈ BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) T,
      ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ ⦃g : V ⟶ T⦄, R.arrows g →
        ∃ (h : V ⟶ totalSiteObject 𝒞 k hU)
          (φ : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h) ⟶ ξ.1),
          (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ := by
  let ξ' : (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).p.Fiber T := ⟨ξ.1, ξ.2⟩
  obtain ⟨R, hR, hess⟩ := Stack.essImage_toQuotientStack (actionGroupoidOverBase 𝒞 k p hU) T ξ'
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨⟨⟨b, x⟩, hz⟩, ⟨e⟩⟩ := hess hg
  obtain rfl : b = V := hz
  obtain ⟨h, rfl⟩ : ∃ h : b ⟶ totalSiteObject 𝒞 k hU, (objectsIso 𝒞 k p hU).hom.app (op b) h = x :=
    ⟨(objectsIso 𝒞 k p hU).inv.app (op b) x, objectsIso_hom_inv_apply p x⟩
  have hψ : (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).p.IsHomLift g
      (e.hom.1 ≫ Functor.IsPreFibered.pullbackMap ξ'.2 g) :=
    Functor.isHomLift_comp_of_isHomLift_id _ _ _ g e.hom.2 inferInstance
  exact ⟨h, _, isHomLift_shrink_functor_map.{u, w} p g _ hψ⟩

section CoGrothendieckFibre

variable {𝒮 : Type*} [Category 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{w, u}}

-- The fibres of the Grothendieck construction of `G.toPseudofunctor'` are those of `G` only after
-- unfolding `Functor.toPseudofunctor'`; without it the simp lemmas below do not see the
-- `eqToHom`s of `G` in the fibre components.
attribute [local implicit_reducible] Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc Pseudofunctor.CoGrothendieck.ι in
/-- **Restriction commutes with the inclusions of the fibres** in the Grothendieck construction
of a presheaf of categories `F`: for `g : V ⟶ W`, morphisms `a ⟶ g^* b` and `a' ⟶ g^* b'` given
by equalities, and `r : b ⟶ b'`, the two composites `a ⟶ b'` agree when the morphism `a ⟶ a'` of
the fibre over `V` is `g^* r` read through the two equalities. -/
theorem coGrothendieck_restriction_comp_ι (G : 𝒮ᵒᵖ ⥤ Cat.{w, u}) {V W : 𝒮} (g : V ⟶ W)
    {a a' : G.obj (op V)} {b b' : G.obj (op W)} (ea : a = (G.map g.op).toFunctor.obj b)
    (ea' : a' = (G.map g.op).toFunctor.obj b') (r : b ⟶ b') (r' : a ⟶ a')
    (hr : r' = eqToHom ea ≫ (G.map g.op).toFunctor.map r ≫ eqToHom ea'.symm) :
    (⟨g, eqToHom ea⟩ : (Pseudofunctor.CoGrothendieck.ι G.toPseudofunctor' V).obj a ⟶
        (Pseudofunctor.CoGrothendieck.ι G.toPseudofunctor' W).obj b) ≫
        (Pseudofunctor.CoGrothendieck.ι G.toPseudofunctor' W).map r =
      (Pseudofunctor.CoGrothendieck.ι G.toPseudofunctor' V).map r' ≫
        (⟨g, eqToHom ea'⟩ : (Pseudofunctor.CoGrothendieck.ι G.toPseudofunctor' V).obj a' ⟶
          (Pseudofunctor.CoGrothendieck.ι G.toPseudofunctor' W).obj b') := by
  subst ea ea' hr
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _
    ((Category.comp_id g).trans (Category.id_comp g).symm) ?_
  rw [PresheafOfCategories.comp_fiber, PresheafOfCategories.comp_fiber]
  dsimp only [Pseudofunctor.CoGrothendieck.ι_map_base, Pseudofunctor.CoGrothendieck.ι_map_fiber,
    Pseudofunctor.CoGrothendieck.ι_obj_fiber, Pseudofunctor.CoGrothendieck.ι_obj_base,
    Functor.toPseudofunctor'_obj, Functor.toPseudofunctor'_map, Functor.toPseudofunctor'_mapId,
    Functor.toPseudofunctor'_mapComp]
  simp [eqToHom_map]

end CoGrothendieckFibre

/-! ### Vertical morphisms between chart objects -/

section Vertical

variable {𝒞 k hU}

/-- The point of the object space of the action groupoid named by a `W`-point `h` of `U`. -/
noncomputable abbrev groupoidPoint {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.Evaluation (op W) :=
  (objectsIso 𝒞 k p hU).hom.app (op W) h

/-- An arrow whose source is the point named by `h` has second coordinate `h`. -/
theorem arrowsEquiv_snd_of_source {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (r : (actionGroupoid 𝒞 k p hU).arrows.obj.obj (op W)) (h : W ⟶ totalSiteObject 𝒞 k hU)
    (hr : (actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.source.app (op W) r =
      groupoidPoint p h) :
    (arrowsEquiv 𝒞 k p hU W r).2 = h := by
  have hr' : (actionGroupoid 𝒞 k p hU).source.hom.app (op W) r =
      (objectsIso 𝒞 k p hU).hom.app (op W) h := hr
  rw [← objectsIso_inv_source, hr']
  simp

/-- An arrow whose target is the point named by `h'` carries its second coordinate to `h'`. -/
theorem actMap_of_target {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (r : (actionGroupoid 𝒞 k p hU).arrows.obj.obj (op W)) (h' : W ⟶ totalSiteObject 𝒞 k hU)
    (hr : (actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.target.app (op W) r =
      groupoidPoint p h') :
    actMap p (arrowsEquiv 𝒞 k p hU W r).1 (arrowsEquiv 𝒞 k p hU W r).2 = h' := by
  have hr' : (actionGroupoid 𝒞 k p hU).target.hom.app (op W) r =
      (objectsIso 𝒞 k p hU).hom.app (op W) h' := hr
  rw [← objectsIso_inv_target, hr']
  simp

/-- The source of the arrow `(γ, h)` is the point named by `h`. -/
theorem source_arrowsEquiv_symm {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.source.app (op W)
        ((arrowsEquiv 𝒞 k p hU W).symm (γ, h)) = groupoidPoint p h := by
  have e := objectsIso_inv_source 𝒞 k p hU W ((arrowsEquiv 𝒞 k p hU W).symm (γ, h))
  rw [Equiv.apply_symm_apply] at e
  exact (objectsIso_hom_inv_apply p _).symm.trans
    (congrArg ((objectsIso 𝒞 k p hU).hom.app (op W)) e)

/-- The target of the arrow `(γ, h)` is the point named by `γ • h`. -/
theorem target_arrowsEquiv_symm {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.target.app (op W)
        ((arrowsEquiv 𝒞 k p hU W).symm (γ, h)) = groupoidPoint p (actMap p γ h) := by
  have e := objectsIso_inv_target 𝒞 k p hU W ((arrowsEquiv 𝒞 k p hU W).symm (γ, h))
  rw [Equiv.apply_symm_apply] at e
  exact (objectsIso_hom_inv_apply p _).symm.trans
    (congrArg ((objectsIso 𝒞 k p hU).hom.app (op W)) e)

/-- **Arrows of the evaluated action groupoid between two points of `U` are units.** An arrow
from the point named by `h` to the point named by `h'` is a unit `γ` of `Γ(W)` with
`γ • h = h'`: the arrow `(γ, h)` of `AlgebraicGeometry.PPowerWeighted.arrowsEquiv` has source `h`
and target `γ • h`. -/
noncomputable def groupoidArrowEquiv {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h h' : W ⟶ totalSiteObject 𝒞 k hU) :
    (groupoidPoint p h ⟶ groupoidPoint p h') ≃
      {γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ //
        actMap p γ h = h'} where
  toFun r :=
    ⟨(arrowsEquiv 𝒞 k p hU W
      ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv
        (op W) _ _ r).1).1, by
      have h2 := arrowsEquiv_snd_of_source p _ h
        ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv
          (op W) _ _ r).2.1
      have h3 := actMap_of_target p _ h'
        ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv
          (op W) _ _ r).2.2
      rwa [h2] at h3⟩
  invFun γ := ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv
      (op W) _ _).symm
    ⟨(arrowsEquiv 𝒞 k p hU W).symm (γ.1, h), source_arrowsEquiv_symm p γ.1 h,
      (target_arrowsEquiv_symm p γ.1 h).trans (congrArg (groupoidPoint p) γ.2)⟩
  left_inv r := by
    apply ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv
      (op W) _ _).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply (arrowsEquiv 𝒞 k p hU W).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext rfl (arrowsEquiv_snd_of_source p _ h
        ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv
          (op W) _ _ r).2.1).symm
  right_inv γ := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

/-- The point named by `g ≫ h` is the restriction along `g` of the point named by `h`. -/
theorem groupoidPoint_comp {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (objectsIso 𝒞 k p hU).hom.app (op V) (g ≫ h) =
      (actionGroupoid 𝒞 k p hU).objects.obj.map g.op ((objectsIso 𝒞 k p hU).hom.app (op W) h) := by
  rw [← NatTrans.naturality_apply]
  rfl

/-- The object of the weighted quotient stack which the chart attaches to a `W`-point `h` of
`U`. -/
noncomputable abbrev chartObj {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj :=
  (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h)

/-- The image under the chart of the morphism `Over.homMk g : g ≫ h ⟶ h` of the slice. -/
noncomputable abbrev chartMap {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (h : W ⟶ totalSiteObject 𝒞 k hU) :
    chartObj.{u, w} p (g ≫ h) ⟶ chartObj.{u, w} p h :=
  (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.map (Over.homMk g : Over.mk (g ≫ h) ⟶ Over.mk h)

/-- The vertical morphism of chart objects induced by an arrow of the evaluated groupoid. -/
noncomputable def chartArrow {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h') :
    chartObj.{u, w} p h ⟶ chartObj.{u, w} p h' :=
  (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map
    ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map r).1

/-- The vertical morphism induced by an arrow lies over the identity. -/
theorem isHomLift_chartArrow {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h') :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W)
      (chartArrow.{u, w} p r) := by
  exact isHomLift_shrink_functor_map.{u, w} p (𝟙 W) _
    ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map r).2

/-- **Vertical morphisms of chart objects are arrows of the evaluated groupoid** (Stacks 044X,
part (2), through the small model). -/
noncomputable def chartVerticalArrowEquiv {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h h' : W ⟶ totalSiteObject 𝒞 k hU) :
    {θ : chartObj.{u, w} p h ⟶ chartObj.{u, w} p h' //
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ} ≃
      (groupoidPoint p h ⟶ groupoidPoint p h') where
  toFun θ := (Stack.fullyFaithful_pointwiseToQuotientStackFiber
      (actionGroupoidOverBase 𝒞 k p hU) W).some.preimage
    ⟨(ShrinkHoms.inverse (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj).map θ.1,
      (isHomLift_iff_shrink.{u, w} p (𝟙 W) θ.1).1 θ.2⟩
  invFun r := ⟨chartArrow.{u, w} p r, isHomLift_chartArrow.{u, w} p r⟩
  left_inv θ := by
    apply Subtype.ext
    have e := congrArg Subtype.val ((Stack.fullyFaithful_pointwiseToQuotientStackFiber
      (actionGroupoidOverBase 𝒞 k p hU) W).some.map_preimage
      ⟨(ShrinkHoms.inverse (Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU)).obj).map θ.1,
        (isHomLift_iff_shrink.{u, w} p (𝟙 W) θ.1).1 θ.2⟩)
    exact (congrArg (ShrinkHoms.functor _).map e).trans (Equiv.apply_symm_apply _ _)
  right_inv r := by
    apply (Stack.fullyFaithful_pointwiseToQuotientStackFiber
      (actionGroupoidOverBase 𝒞 k p hU) W).some.map_injective
    refine ((Stack.fullyFaithful_pointwiseToQuotientStackFiber
      (actionGroupoidOverBase 𝒞 k p hU) W).some.map_preimage _).trans ?_
    apply Functor.Fiber.hom_ext
    exact Equiv.symm_apply_apply _ _

variable (𝒞 k hU) in
/-- The presheaf of groupoids of points of the action groupoid, read in `Cat`. -/
noncomputable abbrev pointsFunctor :=
  Stack.evaluationGroupoidFunctor (actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors ⋙
    Grpd.forgetToCat

variable (𝒞 k hU) in
/-- The pseudofunctor of groupoids of points, whose Grothendieck construction is the pointwise
groupoid fibration. -/
noncomputable abbrev pointsPseudofunctor :=
  (pointsFunctor 𝒞 k p hU).toPseudofunctor'

variable (𝒞 k hU) in
/-- The arrow of the arrow space underlying a morphism of the groupoid of points. -/
noncomputable def arrowF {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {x y : (pointsFunctor 𝒞 k p hU).obj (op W)} (φ : x ⟶ y) :
    (actionGroupoidOverBase 𝒞 k p hU).arrows.obj.obj (op W) :=
  ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv (op W) x y φ).1

variable (𝒞 k hU) in
/-- A morphism of the groupoid of points is determined by its arrow. -/
theorem arrowF_injective {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {x y : (pointsFunctor 𝒞 k p hU).obj (op W)} {φ ψ : x ⟶ y}
    (h : arrowF 𝒞 k p hU φ = arrowF 𝒞 k p hU ψ) : φ = ψ :=
  ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv (op W) x y).injective
    (Subtype.ext h)

variable (𝒞 k hU) in
/-- Transporting the target does not change the arrow. -/
theorem arrowF_comp_eqToHom {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {x y y' : (pointsFunctor 𝒞 k p hU).obj (op W)} (φ : x ⟶ y) (hy : y = y') :
    arrowF 𝒞 k p hU (φ ≫ eqToHom hy) = arrowF 𝒞 k p hU φ := by
  cases hy
  simp

variable (𝒞 k hU) in
/-- Transporting the source does not change the arrow. -/
theorem arrowF_eqToHom_comp {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {x x' y : (pointsFunctor 𝒞 k p hU).obj (op W)} (hx : x' = x) (φ : x ⟶ y) :
    arrowF 𝒞 k p hU (eqToHom hx ≫ φ) = arrowF 𝒞 k p hU φ := by
  cases hx
  simp

variable (𝒞 k hU) in
/-- The restriction of a morphism of the groupoid of points has the restricted arrow. -/
theorem arrowF_map {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    {x y : (pointsFunctor 𝒞 k p hU).obj (op W)} (φ : x ⟶ y) :
    arrowF 𝒞 k p hU (((pointsFunctor 𝒞 k p hU).map g.op).toFunctor.map φ) =
      (actionGroupoidOverBase 𝒞 k p hU).arrows.obj.map g.op (arrowF 𝒞 k p hU φ) :=
  Deformation.evaluationMap_map_arrow _ g.op φ

/-- The point of the groupoid of points named by `h`. -/
noncomputable abbrev pointF {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) : (pointsFunctor 𝒞 k p hU).obj (op W) :=
  groupoidPoint p h

/-- `AlgebraicGeometry.PPowerWeighted.groupoidPoint_comp` in the groupoid of points. -/
theorem pointF_comp {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    pointF p (g ≫ h) = ((pointsFunctor 𝒞 k p hU).map g.op).toFunctor.obj (pointF p h) :=
  groupoidPoint_comp p g h

/-- The morphism of the pointwise groupoid fibration underlying the image under the chart of
`Over.homMk g`: it lies over `g`, and its component in the fibre is an identity. -/
noncomputable def pointwiseRestrictionF {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (Pseudofunctor.CoGrothendieck.ι (pointsPseudofunctor 𝒞 k p hU) V).obj (pointF p (g ≫ h)) ⟶
      (Pseudofunctor.CoGrothendieck.ι (pointsPseudofunctor 𝒞 k p hU) W).obj (pointF p h) :=
  ⟨g, eqToHom (groupoidPoint_comp p g h)⟩

/-- Restriction commutes with the arrows of the pointwise groupoid fibration. -/
theorem pointwiseRestrictionF_comp_ι {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h h' : W ⟶ totalSiteObject 𝒞 k hU}
    (r : pointF p h ⟶ pointF p h') (r' : pointF p (g ≫ h) ⟶ pointF p (g ≫ h'))
    (hr : arrowF 𝒞 k p hU r' =
      (actionGroupoidOverBase 𝒞 k p hU).arrows.obj.map g.op (arrowF 𝒞 k p hU r)) :
    pointwiseRestrictionF p g h ≫ (Pseudofunctor.CoGrothendieck.ι _ W).map r =
      (Pseudofunctor.CoGrothendieck.ι _ V).map r' ≫ pointwiseRestrictionF p g h' := by
  refine coGrothendieck_restriction_comp_ι (pointsFunctor 𝒞 k p hU) g (pointF_comp p g h)
    (pointF_comp p g h') r r' (arrowF_injective 𝒞 k p hU ?_)
  rwa [arrowF_eqToHom_comp, arrowF_comp_eqToHom, arrowF_map]

/-- The restriction along `g : V ⟶ W` of an arrow of the evaluated groupoid between the points
named by `h` and `h'`: an arrow between the points named by `g ≫ h` and `g ≫ h'`. -/
noncomputable def restrictArrow {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : pointF p h ⟶ pointF p h') :
    pointF p (g ≫ h) ⟶ pointF p (g ≫ h') :=
  eqToHom (pointF_comp p g h) ≫ ((pointsFunctor 𝒞 k p hU).map g.op).toFunctor.map r ≫
    eqToHom (pointF_comp p g h').symm

/-- The restriction of an arrow along `g` has the arrow restricted along `g`. -/
theorem arrowF_restrictArrow {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : pointF p h ⟶ pointF p h') :
    arrowF 𝒞 k p hU (restrictArrow p g r) =
      (actionGroupoidOverBase 𝒞 k p hU).arrows.obj.map g.op (arrowF 𝒞 k p hU r) := by
  rw [restrictArrow, arrowF_eqToHom_comp, arrowF_comp_eqToHom, arrowF_map]

/-- The image under the chart of `Over.homMk g`, in the pointwise groupoid fibration. -/
theorem chartMap_eq {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (h : W ⟶ totalSiteObject 𝒞 k hU) :
    chartMap.{u, w} p g h = (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map
      ((Stack.pointwiseToQuotientStack _).map (pointwiseRestrictionF p g h)) :=
  rfl

/-- `AlgebraicGeometry.PPowerWeighted.chartArrow`, in the pointwise groupoid fibration. -/
theorem chartArrow_eq {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h') :
    chartArrow.{u, w} p r = (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map
      ((Stack.pointwiseToQuotientStack _).map
        ((Pseudofunctor.CoGrothendieck.ι (pointsPseudofunctor 𝒞 k p hU) W).map r)) :=
  rfl

/-- **Restriction of vertical morphisms of chart objects.** The image under the chart of
`Over.homMk g : g ≫ h ⟶ h` intertwines the vertical morphism induced by an arrow `r` and the one
induced by its restriction along `g`. -/
theorem chartMap_comp_chartArrow {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h') :
    chartMap.{u, w} p g h ≫ chartArrow.{u, w} p r =
      chartArrow.{u, w} p (restrictArrow p g r) ≫ chartMap.{u, w} p g h' := by
  have key := congrArg (fun m => (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map
    ((Stack.pointwiseToQuotientStack _).map m))
    (pointwiseRestrictionF_comp_ι p g r (restrictArrow p g r) (arrowF_restrictArrow p g r))
  refine ((presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map_comp _ _).symm.trans ?_
  refine (congrArg (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map
    ((Stack.pointwiseToQuotientStack _).map_comp _ _).symm).trans ?_
  refine key.trans ?_
  refine (congrArg (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map
    ((Stack.pointwiseToQuotientStack _).map_comp _ _)).trans ?_
  exact (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map_comp _ _

/-- The unit of an arrow is the first coordinate of its arrow. -/
theorem groupoidArrowEquiv_apply_val {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h') :
    (groupoidArrowEquiv p h h' r).1 = (arrowsEquiv 𝒞 k p hU W (arrowF 𝒞 k p hU r)).1 :=
  rfl

/-- The unit of the restriction of an arrow is the restriction of its unit. -/
theorem groupoidArrowEquiv_restrictArrow {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h h' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h') :
    (groupoidArrowEquiv p (g ≫ h) (g ≫ h') (restrictArrow p g r)).1 =
      Units.map (restrict g).toMonoidHom (groupoidArrowEquiv p h h' r).1 :=
  (groupoidArrowEquiv_apply_val p (restrictArrow p g r)).trans
    ((congrArg (fun a => (arrowsEquiv 𝒞 k p hU V a).1) (arrowF_restrictArrow p g r)).trans
      (congrArg Prod.fst (arrowsEquiv_naturality 𝒞 k p hU g (arrowF 𝒞 k p hU r))))

/-- **Vertical isomorphisms of chart objects are units.** For `W`-points `h` and `h'` of `U`,
morphisms `a(h) ⟶ a(h')` of the weighted quotient stack lying over the identity of `W` are the
units `γ` of `Γ(W)` with `γ • h = h'`. The convention is that of the arrows of the action
groupoid: the arrow `(γ, h)` has source `h` and target `γ • h`
(`AlgebraicGeometry.PPowerWeighted.objectsIso_inv_source`,
`AlgebraicGeometry.PPowerWeighted.objectsIso_inv_target`). -/
noncomputable def chartVerticalEquiv {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h h' : W ⟶ totalSiteObject 𝒞 k hU) :
    {θ : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h) ⟶
        (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h') //
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ} ≃
      {γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ //
        actMap p γ h = h'} :=
  (chartVerticalArrowEquiv.{u, w} p h h').trans (groupoidArrowEquiv p h h')

/-- The unit of a vertical isomorphism is the unit of the arrow inducing it. -/
theorem chartVerticalEquiv_apply {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU}
    (θ : {θ : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h) ⟶
        (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h') //
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ}) :
    chartVerticalEquiv.{u, w} p h h' θ =
      groupoidArrowEquiv p h h' (chartVerticalArrowEquiv.{u, w} p h h' θ) :=
  rfl

/-- The vertical isomorphism of a unit `γ` is the one induced by the arrow `(γ, h)`. -/
theorem chartVerticalEquiv_symm_apply {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU}
    (γ : {γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ //
        actMap p γ h = h'}) :
    ((chartVerticalEquiv.{u, w} p h h').symm γ).1 =
      chartArrow.{u, w} p ((groupoidArrowEquiv p h h').symm γ) :=
  rfl

/-- **Restriction of vertical isomorphisms of chart objects.** For `g : V ⟶ W`, the image under
the chart of `Over.homMk g : g ≫ h ⟶ h` intertwines the vertical isomorphism of a unit `γ` of
`Γ(W)` and that of its restriction `γ|_V` to `V`. -/
theorem chartMap_comp_chartVerticalEquiv_symm
    {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    {h h' : W ⟶ totalSiteObject 𝒞 k hU}
    (γ : {γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ //
        actMap p γ h = h'}) :
    (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.map
        (Over.homMk g : Over.mk (g ≫ h) ⟶ Over.mk h) ≫
        ((chartVerticalEquiv.{u, w} p h h').symm γ).1 =
      ((chartVerticalEquiv.{u, w} p (g ≫ h) (g ≫ h')).symm
          ⟨Units.map (restrict g).toMonoidHom γ.1, by rw [← comp_actMap, γ.2]⟩).1 ≫
        (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.map
          (Over.homMk g : Over.mk (g ≫ h') ⟶ Over.mk h') := by
  have hr : restrictArrow p g ((groupoidArrowEquiv p h h').symm γ) =
      (groupoidArrowEquiv p (g ≫ h) (g ≫ h')).symm
        ⟨Units.map (restrict g).toMonoidHom γ.1, by rw [← comp_actMap, γ.2]⟩ := by
    apply (groupoidArrowEquiv p (g ≫ h) (g ≫ h')).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [groupoidArrowEquiv_restrictArrow, Equiv.apply_symm_apply]
  rw [chartVerticalEquiv_symm_apply, chartVerticalEquiv_symm_apply, ← hr]
  exact chartMap_comp_chartArrow.{u, w} p g _

end Vertical

/-! ### The isomorphism presheaf of two chart objects -/

section Isom

variable {𝒞 k hU}

/-- The weighted quotient stack is fibred in groupoids over the site. -/
theorem isFiberedInGroupoids_weightedQuotientStack :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsFiberedInGroupoids :=
  (weightedQuotientStack.{u, w} 𝒞 k p hU).val.isFiberedInGroupoids

/-- The weighted quotient stack is a fibred category over the site. -/
theorem isFibered_weightedQuotientStack :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsFibered :=
  (isFiberedInGroupoids_weightedQuotientStack.{u, w} p).isFibered

/-- The weighted quotient stack is a fibred category over the site. -/
instance instIsFiberedWeightedQuotientStack :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsFibered :=
  isFibered_weightedQuotientStack.{u, w} p

/-- The chart object of a `W`-point `h` of `U`, as an object of the fibre over `W`. -/
noncomputable abbrev chartFiber {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.Fiber W :=
  ⟨(chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h),
    (chart.{u, w} 𝒞 k p hU).hom.hom.w_obj (Over.mk h)⟩

/-- The image under the chart of a morphism `Over.mk h₁ ⟶ Over.mk h` of the slice over `U`
whose underlying morphism is `g`. -/
noncomputable abbrev chartHom {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h₁ : V ⟶ totalSiteObject 𝒞 k hU} {h : W ⟶ totalSiteObject 𝒞 k hU}
    (e : g ≫ h = h₁) : chartObj.{u, w} p h₁ ⟶ chartObj.{u, w} p h :=
  (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.map (Over.homMk g e : Over.mk h₁ ⟶ Over.mk h)

/-- The image under the chart of a morphism over `g` lies over `g`. -/
instance isHomLift_chartHom {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h₁ : V ⟶ totalSiteObject 𝒞 k hU} {h : W ⟶ totalSiteObject 𝒞 k hU}
    (e : g ≫ h = h₁) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g (chartHom.{u, w} p g e) := by
  have : (Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (totalSiteObject 𝒞 k hU)).val.val.p.IsHomLift g
      (Over.homMk g e : Over.mk h₁ ⟶ Over.mk h) :=
    Functor.IsHomLift.map (p := (Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (totalSiteObject 𝒞 k hU)).val.val.p) (Over.homMk g e : Over.mk h₁ ⟶ Over.mk h)
  exact BasedFunctor.preserves_isHomLift (chart.{u, w} 𝒞 k p hU).hom.hom g _

/-- The image under the chart of a morphism over `g` is strongly cartesian over `g`. -/
instance isStronglyCartesian_chartHom {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {h₁ : V ⟶ totalSiteObject 𝒞 k hU} {h : W ⟶ totalSiteObject 𝒞 k hU}
    (e : g ≫ h = h₁) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsStronglyCartesian g
      (chartHom.{u, w} p g e) :=
  (isFiberedInGroupoids_weightedQuotientStack.{u, w} p).isStronglyCartesian_homLift _ _

/-- The images under the chart of composable morphisms of the slice compose. -/
theorem chartHom_comp {V₁ V₂ W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g₁ : V₁ ⟶ V₂) (g₂ : V₂ ⟶ W) (g : V₁ ⟶ W) (hg : g₁ ≫ g₂ = g)
    {h₁ : V₁ ⟶ totalSiteObject 𝒞 k hU} {h₂ : V₂ ⟶ totalSiteObject 𝒞 k hU}
    {h : W ⟶ totalSiteObject 𝒞 k hU} (e₁ : g₁ ≫ h₂ = h₁) (e₂ : g₂ ≫ h = h₂) (e : g ≫ h = h₁) :
    chartHom.{u, w} p g₁ e₁ ≫ chartHom.{u, w} p g₂ e₂ = chartHom.{u, w} p g e := by
  refine ((chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.map_comp _ _).symm.trans ?_
  exact congrArg (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.map (Over.OverMorphism.ext hg)

/-- The comparison, in the fibre over `V`, between the chosen pullback of the chart object of
`h` along `f : V ⟶ W` and the chart object of `f ≫ h`: both are cartesian over `f`. -/
noncomputable def chartPullbackIso {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) (f : V ⟶ W) :
    Functor.pullbackFiber (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p (chartFiber.{u, w} p h)
        f ≅ chartFiber.{u, w} p (f ≫ h) :=
  let φ : (Functor.pullbackFiber (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
      (chartFiber.{u, w} p h) f).1 ⟶ chartObj.{u, w} p h :=
    Functor.IsPreFibered.pullbackMap (chartFiber.{u, w} p h).2 f
  let ψ : chartObj.{u, w} p (f ≫ h) ⟶ chartObj.{u, w} p h := chartHom.{u, w} p f rfl
  have hφ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsCartesian f φ :=
    Functor.IsPreFibered.pullbackMap.IsCartesian _ _
  have hψ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsCartesian f ψ :=
    inferInstanceAs ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsCartesian f
      (chartHom.{u, w} p f (rfl : f ≫ h = f ≫ h)))
  Functor.fiberIsoOfCartesian
    (z := Functor.pullbackFiber (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
      (chartFiber.{u, w} p h) f) (z' := chartFiber.{u, w} p (f ≫ h)) f φ ψ hφ hψ

/-- The defining factorisation of `AlgebraicGeometry.PPowerWeighted.chartPullbackIso`. -/
theorem chartPullbackIso_hom_fac {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) (f : V ⟶ W) :
    Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h f).hom ≫
        chartHom.{u, w} p f (rfl : f ≫ h = f ≫ h) =
      Functor.IsPreFibered.pullbackMap (chartFiber.{u, w} p h).2 f :=
  Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The defining factorisation of the inverse of
`AlgebraicGeometry.PPowerWeighted.chartPullbackIso`. -/
theorem chartPullbackIso_inv_fac {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) (f : V ⟶ W) :
    Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h f).inv ≫
        Functor.IsPreFibered.pullbackMap (chartFiber.{u, w} p h).2 f =
      chartHom.{u, w} p f (rfl : f ≫ h = f ≫ h) :=
  Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- **A vertical morphism of chart objects is pinned down by its restriction.** If a vertical
morphism `θ₁` between the chart objects of `k₁` and `k₁'` is intertwined with the vertical
morphism `θ` of a unit `γ` by the images under the chart of two morphisms over `g`, then `θ₁` is
the vertical morphism of the restriction `γ|_V`. -/
theorem chartVerticalEquiv_eq_of_comp {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) {m m' : W ⟶ totalSiteObject 𝒞 k hU} {m₁ m₁' : V ⟶ totalSiteObject 𝒞 k hU}
    (e : g ≫ m = m₁) (e' : g ≫ m' = m₁')
    (θ : {θ : chartObj.{u, w} p m ⟶ chartObj.{u, w} p m' //
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ})
    (θ₁ : {θ : chartObj.{u, w} p m₁ ⟶ chartObj.{u, w} p m₁' //
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 V) θ})
    (hθ : chartHom.{u, w} p g e ≫ θ.1 = θ₁.1 ≫ chartHom.{u, w} p g e') :
    (chartVerticalEquiv.{u, w} p m₁ m₁' θ₁).1 =
      Units.map (restrict g).toMonoidHom (chartVerticalEquiv.{u, w} p m m' θ).1 := by
  subst e e'
  have hr := chartMap_comp_chartVerticalEquiv_symm.{u, w} p g (chartVerticalEquiv.{u, w} p m m' θ)
  rw [Equiv.symm_apply_apply] at hr
  set θ' := (chartVerticalEquiv.{u, w} p (g ≫ m) (g ≫ m')).symm
    ⟨Units.map (restrict g).toMonoidHom (chartVerticalEquiv.{u, w} p m m' θ).1,
      by rw [← comp_actMap, (chartVerticalEquiv.{u, w} p m m' θ).2]⟩ with hθ'
  have h1 : θ₁ = θ' := by
    have := θ₁.2
    have := θ'.2
    apply Subtype.ext
    exact Functor.IsCartesian.ext (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p g
      (chartHom.{u, w} p g (rfl : g ≫ m' = g ≫ m')) θ₁.1 θ'.1 (hθ.symm.trans hr)
  rw [h1, hθ', Equiv.apply_symm_apply]

/-- **The isomorphism presheaf of two chart objects, on the slice.** For `W`-points `h`, `h'` of
`U` and `f : V ⟶ W`, the sections over `f` of the isomorphism presheaf
`Isom(a(h), a(h'))` of Stacks 02ZB are the units `γ` of `Γ(V)` with `γ • (f ≫ h) = f ≫ h'`.
A section, an isomorphism between the chosen pullbacks of `a(h)` and `a(h')` along `f`, is read
through the comparisons `AlgebraicGeometry.PPowerWeighted.chartPullbackIso` with the chart objects
of `f ≫ h` and `f ≫ h'`, and then through
`AlgebraicGeometry.PPowerWeighted.chartVerticalEquiv`. -/
noncomputable def chartIsomEquiv {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h h' : W ⟶ totalSiteObject 𝒞 k hU) (f : V ⟶ W) :
    ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf (chartFiber.{u, w} p h)
        (chartFiber.{u, w} p h')).obj (op (Over.mk f)) ≃
      {γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ //
        actMap p γ (f ≫ h) = f ≫ h'} where
  toFun s := chartVerticalEquiv.{u, w} p (f ≫ h) (f ≫ h')
    ((chartPullbackIso.{u, w} p h f).inv ≫ s.1 ≫ (chartPullbackIso.{u, w} p h' f).hom)
  invFun γ := ⟨(chartPullbackIso.{u, w} p h f).hom ≫
      (show chartFiber.{u, w} p (f ≫ h) ⟶ chartFiber.{u, w} p (f ≫ h') from
        (chartVerticalEquiv.{u, w} p (f ≫ h) (f ≫ h')).symm γ) ≫
      (chartPullbackIso.{u, w} p h' f).inv,
    ((isFiberedInGroupoids_weightedQuotientStack.{u, w} p).fiber_isGroupoid V).all_isIso
      _⟩
  left_inv s := by
    apply Subtype.ext
    change (chartPullbackIso.{u, w} p h f).hom ≫
      (show chartFiber.{u, w} p (f ≫ h) ⟶ chartFiber.{u, w} p (f ≫ h') from
        (chartVerticalEquiv.{u, w} p (f ≫ h) (f ≫ h')).symm
          (chartVerticalEquiv.{u, w} p (f ≫ h) (f ≫ h')
            ((chartPullbackIso.{u, w} p h f).inv ≫ s.1 ≫ (chartPullbackIso.{u, w} p h' f).hom))) ≫
      (chartPullbackIso.{u, w} p h' f).inv = s.1
    rw [Equiv.symm_apply_apply]
    simp
  right_inv γ := by
    change chartVerticalEquiv.{u, w} p (f ≫ h) (f ≫ h')
      ((chartPullbackIso.{u, w} p h f).inv ≫ ((chartPullbackIso.{u, w} p h f).hom ≫
        (show chartFiber.{u, w} p (f ≫ h) ⟶ chartFiber.{u, w} p (f ≫ h') from
          (chartVerticalEquiv.{u, w} p (f ≫ h) (f ≫ h')).symm γ) ≫
        (chartPullbackIso.{u, w} p h' f).inv) ≫ (chartPullbackIso.{u, w} p h' f).hom) = γ
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Equiv.apply_symm_apply _ _

omit [CommRing k] in
/-- A morphism over `f` followed by a morphism over an identity lies over `f`. -/
theorem isHomLift_comp_of_isHomLift_id_right {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳]
    (q : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b c : 𝒳} (π : a ⟶ b) (ε : b ⟶ c) (f : R ⟶ S)
    (hπ : q.IsHomLift f π) (hε : q.IsHomLift (𝟙 S) ε) : q.IsHomLift f (π ≫ ε) :=
  have := hπ
  have := hε
  IsHomLift.comp_lift_id_right' q f π S ε

omit [CommRing k] in
/-- Pasting three commutative squares. -/
theorem comp_conj_eq_conj_comp {C : Type*} [Category C] {X₁ X₂ P₁ P₂ Q₁ Q₂ Y₁ Y₂ : C}
    (c : X₁ ⟶ X₂) (a : X₂ ⟶ P₂) (m : P₂ ⟶ Q₂) (b : Q₂ ⟶ Y₂) (a' : X₁ ⟶ P₁) (m' : P₁ ⟶ Q₁)
    (b' : Q₁ ⟶ Y₁) (c' : Y₁ ⟶ Y₂) (mx : P₁ ⟶ P₂) (my : Q₁ ⟶ Q₂) (h₁ : c ≫ a = a' ≫ mx)
    (h₂ : m' ≫ my = mx ≫ m) (h₃ : b' ≫ c' = my ≫ b) :
    c ≫ a ≫ m ≫ b = (a' ≫ m' ≫ b') ≫ c' := by
  rw [← Category.assoc c a, h₁, Category.assoc, ← Category.assoc mx, ← h₂, Category.assoc,
    Category.assoc, Category.assoc, h₃]

omit [CommRing k] in
/-- `CategoryTheory.Functor.IsStronglyCartesian.ext` with its instance arguments explicit. -/
theorem isStronglyCartesian_ext' {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳] (q : 𝒳 ⥤ 𝒮)
    {R S R' : 𝒮} {a b a' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (hφ : q.IsStronglyCartesian f φ)
    (g : R' ⟶ R) (ψ ψ' : a' ⟶ a) (hψ : q.IsHomLift g ψ) (hψ' : q.IsHomLift g ψ')
    (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' :=
  have := hφ
  have := hψ
  have := hψ'
  Functor.IsStronglyCartesian.ext q f φ g h

/-- `AlgebraicGeometry.PPowerWeighted.chartPullbackIso` is natural in the object of the slice:
it intertwines the images under the chart and the restriction maps of the chosen pullbacks. -/
theorem chartHom_comp_chartPullbackIso_inv {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) {a a' : Over W} (q : a' ⟶ a)
    (e : q.left ≫ a.hom ≫ h = a'.hom ≫ h) :
    chartHom.{u, w} p q.left e ≫
        Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a.hom).inv =
      Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a'.hom).inv ≫
        Functor.pullbackFiberMap (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
          (chartFiber.{u, w} p h) q := by
  have : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsStronglyCartesian a.hom
      (Functor.IsPreFibered.pullbackMap (chartFiber.{u, w} p h).2 a.hom) :=
    (isFiberedInGroupoids_weightedQuotientStack.{u, w} p).isStronglyCartesian_homLift
      _ _
  have hq : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift q.left
      (Functor.pullbackFiberMap (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
        (chartFiber.{u, w} p h) q) := inferInstance
  have hl : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift q.left
      (chartHom.{u, w} p q.left e ≫
        Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a.hom).inv) :=
    isHomLift_comp_of_isHomLift_id_right _ _ _ q.left (isHomLift_chartHom.{u, w} p q.left e)
      (chartPullbackIso.{u, w} p h a.hom).inv.2
  have hr : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift q.left
      (Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a'.hom).inv ≫
        Functor.pullbackFiberMap (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
          (chartFiber.{u, w} p h) q) :=
    Functor.isHomLift_comp_of_isHomLift_id _ _ _ q.left
      (chartPullbackIso.{u, w} p h a'.hom).inv.2 hq
  refine isStronglyCartesian_ext' (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p a.hom
    (Functor.IsPreFibered.pullbackMap (chartFiber.{u, w} p h).2 a.hom) this q.left _ _ hl hr ?_
  have h1 := Functor.pullbackFiberMap_fac (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
    (chartFiber.{u, w} p h) q
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (chartHom.{u, w} p q.left e ≫ ·)
    (chartPullbackIso_inv_fac.{u, w} p h a.hom)).trans ?_
  refine (chartHom_comp.{u, w} p q.left a.hom a'.hom (Over.w q) e rfl rfl).trans ?_
  refine ((Category.assoc _ _ _).trans ?_).symm
  refine (congrArg (Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a'.hom).inv ≫ ·)
    h1).trans ?_
  exact chartPullbackIso_inv_fac.{u, w} p h a'.hom

/-- `AlgebraicGeometry.PPowerWeighted.chartHom_comp_chartPullbackIso_inv`, for the forward
comparison. -/
theorem chartPullbackIso_hom_comp_chartHom {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) {a a' : Over W} (q : a' ⟶ a)
    (e : q.left ≫ a.hom ≫ h = a'.hom ≫ h) :
    Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a'.hom).hom ≫
        chartHom.{u, w} p (h₁ := a'.hom ≫ h) (h := a.hom ≫ h) q.left e =
      Functor.pullbackFiberMap (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
          (chartFiber.{u, w} p h) q ≫
        Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a.hom).hom := by
  have hl := Functor.isHomLift_comp_of_isHomLift_id
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
    (Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a'.hom).hom)
    (chartHom.{u, w} p (h₁ := a'.hom ≫ h) (h := a.hom ≫ h) q.left e) q.left
    (chartPullbackIso.{u, w} p h a'.hom).hom.2
    (isHomLift_chartHom.{u, w} p (h₁ := a'.hom ≫ h) (h := a.hom ≫ h) q.left e)
  have hr := isHomLift_comp_of_isHomLift_id_right
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
    (Functor.pullbackFiberMap (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
      (chartFiber.{u, w} p h) q)
    (Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a.hom).hom) q.left
    (Functor.pullbackFiberMap_isHomLift _ _ q) (chartPullbackIso.{u, w} p h a.hom).hom.2
  refine isStronglyCartesian_ext' (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p a.hom
    (chartHom.{u, w} p (h₁ := a.hom ≫ h) (h := h) a.hom rfl) inferInstance q.left _ _ hl hr ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (Functor.Fiber.fiberInclusion.map (chartPullbackIso.{u, w} p h a'.hom).hom ≫ ·)
    (chartHom_comp.{u, w} p q.left a.hom a'.hom (Over.w q) e rfl rfl)).trans ?_
  refine (chartPullbackIso_hom_fac.{u, w} p h a'.hom).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (Functor.pullbackFiberMap (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p
    (chartFiber.{u, w} p h) q ≫ ·) (chartPullbackIso_hom_fac.{u, w} p h a.hom)).trans ?_
  exact Functor.pullbackFiberMap_fac _ _ q

/-- The unit attached to a section of the isomorphism presheaf. -/
theorem chartIsomEquiv_apply {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h h' : W ⟶ totalSiteObject 𝒞 k hU) (f : V ⟶ W)
    (s : ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf (chartFiber.{u, w} p h)
        (chartFiber.{u, w} p h')).obj (op (Over.mk f))) :
    chartIsomEquiv.{u, w} p h h' f s = chartVerticalEquiv.{u, w} p (f ≫ h) (f ≫ h')
      ((chartPullbackIso.{u, w} p h f).inv ≫ s.1 ≫ (chartPullbackIso.{u, w} p h' f).hom) :=
  rfl

/-- **Naturality of `AlgebraicGeometry.PPowerWeighted.chartIsomEquiv` in `f`.** Restricting a
section of `Isom(a(h), a(h'))` from `f : V ⟶ W` to `g ≫ f` for `g : V' ⟶ V` restricts the unit it
corresponds to along `g`. -/
theorem chartIsomEquiv_naturality {V V' W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h h' : W ⟶ totalSiteObject 𝒞 k hU) (f : V ⟶ W) (g : V' ⟶ V)
    (s : ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf (chartFiber.{u, w} p h)
        (chartFiber.{u, w} p h')).obj (op (Over.mk f))) :
    (chartIsomEquiv.{u, w} p h h' (g ≫ f)
        (((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.isomPresheaf (chartFiber.{u, w} p h)
          (chartFiber.{u, w} p h')).map (Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f).op s)).1 =
      Units.map (restrict g).toMonoidHom (chartIsomEquiv.{u, w} p h h' f s).1 := by
  rw [chartIsomEquiv_apply, chartIsomEquiv_apply]
  refine chartVerticalEquiv_eq_of_comp.{u, w} p g (Category.assoc g f h).symm
    (Category.assoc g f h').symm _ _ ?_
  exact comp_conj_eq_conj_comp _ _ _ _ _ _ _ _ _ _
    (chartHom_comp_chartPullbackIso_inv.{u, w} p h
      (Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f) _)
    (Functor.fiberInclusion_map_morRestrict_comp_pullbackFiberMap _ _ _ _ s.1)
    (chartPullbackIso_hom_comp_chartHom.{u, w} p h'
      (Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f) _)

end Isom

/-! ### Composition in the action groupoid -/

section Composition

open scoped TensorProduct CategoryTheory.MonObj

variable {𝒞}

attribute [local instance] Space.multiplicativeGroupULiftSiteObjectGrpObj in
/-- **The identification of the points of `𝐆_m` with units is multiplicative.** -/
@[ega "II 8.3.9" "The group law on Hom(Z"]
theorem gmUnitsEquiv_mul (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (m₁ m₂ : (gmPoints 𝒞).obj (op W)) :
    gmUnitsEquiv W (m₁ * m₂) = gmUnitsEquiv W m₁ * gmUnitsEquiv W m₂ := by
  apply Units.ext
  rw [Units.val_mul, gmUnitsEquiv_val, gmUnitsEquiv_val, gmUnitsEquiv_val]
  have hmul : gmHom (m₁ * m₂) = CartesianMonoidalCategory.lift (gmHom m₁) (gmHom m₂) ≫
      MonObj.mul := rfl
  rw [hmul, Over.comp_left]
  have w : (gmHom m₁).left ≫ Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ)
      (LaurentPolynomial (ULift.{u} ℤ)))) = (gmHom m₂).left ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)))) :=
    (Over.w (gmHom m₁)).trans (Over.w (gmHom m₂)).symm
  have hl : (CartesianMonoidalCategory.lift (gmHom m₁) (gmHom m₂)).left ≫
      (MonObj.mul (X := (Space.toSchemeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
        (Space.multiplicativeGroupULiftSiteObject 𝒞))).left =
      pullback.lift (gmHom m₁).left (gmHom m₂).left w ≫
        (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
          (LaurentPolynomial (ULift.{u} ℤ))).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom (ULift.{u} ℤ)
          (LaurentPolynomial (ULift.{u} ℤ))).toRingHom) := rfl
  have e := specRingHom_comp_specMap (pullback.lift (gmHom m₁).left (gmHom m₂).left w ≫
        (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
          (LaurentPolynomial (ULift.{u} ℤ))).hom)
    (CommRingCat.ofHom (Bialgebra.comulAlgHom (ULift.{u} ℤ)
          (LaurentPolynomial (ULift.{u} ℤ))).toRingHom)
  have key := (congrArg specRingHom (hl.trans (Category.assoc _ _ _).symm)).trans e
  refine (congrArg (fun φ => (CommRingCat.Hom.hom φ) (LaurentPolynomial.T 1)) key).trans ?_
  have hc : (Bialgebra.comulAlgHom (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)))
      (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T 1 :=
    LaurentPolynomial.comul_T 1
  refine (congrArg (specRingHom (pullback.lift (gmHom m₁).left (gmHom m₂).left w ≫
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
        (LaurentPolynomial (ULift.{u} ℤ))).hom)).hom hc).trans ?_
  exact specRingHom_lift_pullbackSpecIso_hom_tmul _ _ w _ _

omit [CommRing k] in
/-- Pullbacks along heterogeneously equal morphisms agree. -/
theorem pullback_eq_of_heq {D : Type*} [Category D] [HasPullbacks D] {X X' Y Y' Z Z' : D}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} (hX : X = X') (hY : Y = Y')
    (hZ : Z = Z') (hf : f ≍ f') (hg : g ≍ g') : pullback f g = pullback f' g' := by
  subst hX hY hZ
  cases hf
  cases hg
  rfl

omit [CommRing k] in
/-- The first projections of pullbacks along heterogeneously equal morphisms agree. -/
theorem eqToHom_comp_pullback_fst_of_heq {D : Type*} [Category D] [HasPullbacks D]
    {X X' Y Y' Z Z' : D} {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') (hf : f ≍ f') (hg : g ≍ g') :
    eqToHom (pullback_eq_of_heq hX hY hZ hf hg) ≫ pullback.fst f' g' =
      pullback.fst f g ≫ eqToHom hX := by
  subst hX hY hZ
  cases hf
  cases hg
  simp

omit [CommRing k] in
/-- The second projections of pullbacks along heterogeneously equal morphisms agree. -/
theorem eqToHom_comp_pullback_snd_of_heq {D : Type*} [Category D] [HasPullbacks D]
    {X X' Y Y' Z Z' : D} {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') (hf : f ≍ f') (hg : g ≍ g') :
    eqToHom (pullback_eq_of_heq hX hY hZ hf hg) ≫ pullback.snd f' g' =
      pullback.snd f g ≫ eqToHom hY := by
  subst hX hY hZ
  cases hf
  cases hg
  simp

variable (𝒞) in
open MonoidalCategory in
/-- The domain of the composition of the action groupoid is the fibre product of `snd` and of
the action. -/
theorem compositionDomain_eq (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    (AlgebraicSpaces.fiberProduct 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (actionGroupoid 𝒞 k p hU).source (actionGroupoid 𝒞 k p hU).target).obj =
      (letI := spaceOverModObj 𝒞 k p hU;
        pullback (CartesianMonoidalCategory.snd (groupOver 𝒞) (spaceOver 𝒞 k hU)).left
          (ModObj.smul (M := groupOver 𝒞) (X := spaceOver 𝒞 k hU)).left) :=
  let := spaceOverModObj 𝒞 k p hU
  pullback_eq_of_heq (actionGroupoid_arrows_obj 𝒞 k p hU) (actionGroupoid_arrows_obj 𝒞 k p hU)
    (actionGroupoid_objects_obj 𝒞 k p hU) (actionGroupoidConstruction 𝒞 k p hU).source_eq
    (actionGroupoidConstruction 𝒞 k p hU).target_eq

variable (𝒞) in
/-- **Stacks 0444**, the composition of the action groupoid, as an equation. -/
theorem actionGroupoid_comp_hom (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    (actionGroupoid 𝒞 k p hU).comp.hom = eqToHom (compositionDomain_eq 𝒞 (k := k) p hU) ≫
      (letI := spaceOverModObj 𝒞 k p hU;
        (actionGroupoidConstruction 𝒞 k p hU).compositionDomainIso.hom ≫
          (Stacks.Groupoids.ActionGroupoid.composition (groupOver 𝒞) (spaceOver 𝒞 k hU)).left) ≫
      eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU).symm :=
  let := spaceOverModObj 𝒞 k p hU
  (conj_eqToHom_iff_heq _ _ (compositionDomain_eq 𝒞 (k := k) p hU)
    (actionGroupoid_arrows_obj 𝒞 k p hU)).2 (actionGroupoidConstruction 𝒞 k p hU).comp_eq

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks in a slice of presheaves on the big fppf site is deep
/-- Pullbacks in a slice of presheaves on the big fppf site (instance search times out without
this shortcut). -/
local instance hasPullbacks_over_GerbeStratificationChart {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} (B : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    HasPullbacks (Over B) := inferInstance

local instance (priority := high) hasPullback_over_GerbeStratificationChart
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {X Y Z : Over B} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (𝒞) in
open MonoidalCategory CartesianMonoidalCategory in
/-- **Composition in the action groupoid multiplies the units, on morphisms from a representable
presheaf.** -/
theorem comp_hom_comp_gmCoord (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))
    (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (Y : yoneda.obj W ⟶ (AlgebraicSpaces.fiberProduct 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (actionGroupoid 𝒞 k p hU).source (actionGroupoid 𝒞 k p hU).target).obj) :
    Y ≫ (actionGroupoid 𝒞 k p hU).comp.hom ≫ eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
        pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd =
      (Y ≫ pullback.fst _ _ ≫ eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
        pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd) *
      (Y ≫ pullback.snd _ _ ≫ eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
        pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd) := by
  let := spaceOverModObj 𝒞 k p hU
  let T : Over (baseAlgebraicSpace 𝒞).obj :=
    Over.mk ((isTerminalBaseAlgebraicSpace 𝒞).from (yoneda.obj W))
  let tO : T ⟶ pullback (snd (groupOver 𝒞) (spaceOver 𝒞 k hU))
      (ModObj.smul (M := groupOver 𝒞) (X := spaceOver 𝒞 k hU)) :=
    Over.homMk (Y ≫ eqToHom (compositionDomain_eq 𝒞 (k := k) p hU) ≫
      (actionGroupoidConstruction 𝒞 k p hU).compositionDomainIso.hom)
      ((isTerminalBaseAlgebraicSpace 𝒞).hom_ext _ _)
  have eL : Y ≫ (actionGroupoid 𝒞 k p hU).comp.hom ≫
      eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
        pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd =
      overProdFstHomMulEquiv _ (gmPoints 𝒞) T
        (tO ≫ Stacks.Groupoids.ActionGroupoid.composition (groupOver 𝒞) (spaceOver 𝒞 k hU) ≫
          fst (groupOver 𝒞) (spaceOver 𝒞 k hU)) := by
    rw [actionGroupoid_comp_hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl
  have eM : overProdFstHomMulEquiv _ (gmPoints 𝒞) T
        (tO ≫ Stacks.Groupoids.ActionGroupoid.composition (groupOver 𝒞) (spaceOver 𝒞 k hU) ≫
          fst (groupOver 𝒞) (spaceOver 𝒞 k hU)) =
      overProdFstHomMulEquiv _ (gmPoints 𝒞) T (tO ≫ pullback.fst _ _ ≫
          fst (groupOver 𝒞) (spaceOver 𝒞 k hU)) *
        overProdFstHomMulEquiv _ (gmPoints 𝒞) T (tO ≫ pullback.snd _ _ ≫
          fst (groupOver 𝒞) (spaceOver 𝒞 k hU)) := by
    rw [Stacks.Groupoids.ActionGroupoid.composition_fst, ← Category.assoc, comp_lift,
      ← Hom.mul_def, map_mul]
  have e1 : overProdFstHomMulEquiv _ (gmPoints 𝒞) T (tO ≫ pullback.fst _ _ ≫
      fst (groupOver 𝒞) (spaceOver 𝒞 k hU)) = Y ≫ pullback.fst _ _ ≫
        eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
          pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd := by
    have hfst := (actionGroupoidConstruction 𝒞 k p hU).compositionDomainIso_fst
    have hl : tO.left ≫ (pullback.fst (snd (groupOver 𝒞) (spaceOver 𝒞 k hU))
        (ModObj.smul (M := groupOver 𝒞) (X := spaceOver 𝒞 k hU))).left =
        Y ≫ pullback.fst _ _ ≫ eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) := by
      change (Y ≫ eqToHom (compositionDomain_eq 𝒞 (k := k) p hU) ≫
        (actionGroupoidConstruction 𝒞 k p hU).compositionDomainIso.hom) ≫ _ = _
      rw [Category.assoc, Category.assoc, hfst]
      exact congrArg (Y ≫ ·) (eqToHom_comp_pullback_fst_of_heq (actionGroupoid_arrows_obj 𝒞 k p hU)
        (actionGroupoid_arrows_obj 𝒞 k p hU) (actionGroupoid_objects_obj 𝒞 k p hU)
        (actionGroupoidConstruction 𝒞 k p hU).source_eq
        (actionGroupoidConstruction 𝒞 k p hU).target_eq)
    rw [overProdFstHomMulEquiv_apply, Over.comp_left, Over.comp_left, ← Category.assoc tO.left, hl]
    simp only [Category.assoc]
    rfl
  have e2 : overProdFstHomMulEquiv _ (gmPoints 𝒞) T (tO ≫ pullback.snd _ _ ≫
      fst (groupOver 𝒞) (spaceOver 𝒞 k hU)) = Y ≫ pullback.snd _ _ ≫
        eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
          pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd := by
    have hsnd := (actionGroupoidConstruction 𝒞 k p hU).compositionDomainIso_snd
    have hl : tO.left ≫ (pullback.snd (snd (groupOver 𝒞) (spaceOver 𝒞 k hU))
        (ModObj.smul (M := groupOver 𝒞) (X := spaceOver 𝒞 k hU))).left =
        Y ≫ pullback.snd _ _ ≫ eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) := by
      change (Y ≫ eqToHom (compositionDomain_eq 𝒞 (k := k) p hU) ≫
        (actionGroupoidConstruction 𝒞 k p hU).compositionDomainIso.hom) ≫ _ = _
      rw [Category.assoc, Category.assoc, hsnd]
      exact congrArg (Y ≫ ·) (eqToHom_comp_pullback_snd_of_heq (actionGroupoid_arrows_obj 𝒞 k p hU)
        (actionGroupoid_arrows_obj 𝒞 k p hU) (actionGroupoid_objects_obj 𝒞 k p hU)
        (actionGroupoidConstruction 𝒞 k p hU).source_eq
        (actionGroupoidConstruction 𝒞 k p hU).target_eq)
    rw [overProdFstHomMulEquiv_apply, Over.comp_left, Over.comp_left, ← Category.assoc tO.left, hl]
    simp only [Category.assoc]
    rfl
  rw [eL, eM, e1, e2]

variable (𝒞) in
/-- **The composite of the arrows `(γ', h')` and `(γ, h)` of the action groupoid is `γ' * γ`.** -/
theorem arrowsEquiv_compose_fst (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))
    (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (a' a : (actionGroupoid 𝒞 k p hU).arrows.obj.obj (op W))
    (hcomp : (actionGroupoid 𝒞 k p hU).toGroupoidInFunctors.source.app (op W) a' =
      (actionGroupoid 𝒞 k p hU).toGroupoidInFunctors.target.app (op W) a) :
    (arrowsEquiv 𝒞 k p hU W
        ((actionGroupoid 𝒞 k p hU).toGroupoidInFunctors.compose (op W) a' a hcomp)).1 =
      (arrowsEquiv 𝒞 k p hU W a').1 * (arrowsEquiv 𝒞 k p hU W a).1 := by
  let z := (composableToPullback (actionGroupoid 𝒞 k p hU).source.hom
    (actionGroupoid 𝒞 k p hU).target.hom).app (op W) ⟨(a', a), hcomp⟩
  let Y : yoneda.obj W ⟶ (AlgebraicSpaces.fiberProduct 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (actionGroupoid 𝒞 k p hU).source (actionGroupoid 𝒞 k p hU).target).obj := yonedaEquiv.symm z
  have hz : yonedaEquiv Y = z := yonedaEquiv.apply_symm_apply z
  have hY' : yonedaEquiv (Y ≫ pullback.fst _ _) = a' :=
    (congrArg ((pullback.fst (actionGroupoid 𝒞 k p hU).source.hom
      (actionGroupoid 𝒞 k p hU).target.hom).app (op W)) hz).trans
      (congrArg (fun (m : Deformation.composableArrows _ _ (actionGroupoid 𝒞 k p hU).source.hom
          (actionGroupoid 𝒞 k p hU).target.hom ⟶ (actionGroupoid 𝒞 k p hU).arrows.obj) =>
          m.app (op W) ⟨(a', a), hcomp⟩)
        (pullback.lift_fst _ _ _))
  have hY : yonedaEquiv (Y ≫ pullback.snd _ _) = a :=
    (congrArg ((pullback.snd (actionGroupoid 𝒞 k p hU).source.hom
      (actionGroupoid 𝒞 k p hU).target.hom).app (op W)) hz).trans
      (congrArg (fun (m : Deformation.composableArrows _ _ (actionGroupoid 𝒞 k p hU).source.hom
          (actionGroupoid 𝒞 k p hU).target.hom ⟶ (actionGroupoid 𝒞 k p hU).arrows.obj) =>
          m.app (op W) ⟨(a', a), hcomp⟩)
        (pullback.lift_snd _ _ _))
  have hc : yonedaEquiv (Y ≫ (actionGroupoid 𝒞 k p hU).comp.hom) =
      (actionGroupoid 𝒞 k p hU).toGroupoidInFunctors.compose (op W) a' a hcomp :=
    congrArg ((actionGroupoid 𝒞 k p hU).comp.hom.app (op W)) hz
  have key := (congrArg (yonedaHomMulEquiv (Space.pointsOnSite 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Space.multiplicativeGroupULiftSiteObject 𝒞)
      (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞)) W)
    (comp_hom_comp_gmCoord 𝒞 (k := k) p hU W Y)).trans (map_mul _ _ _)
  refine (congrArg Prod.fst (arrowsEquiv_apply 𝒞 k p hU W _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Prod.fst (arrowsEquiv_apply 𝒞 k p hU W _)).symm
    (congrArg Prod.fst (arrowsEquiv_apply 𝒞 k p hU W _)).symm)
  refine Eq.trans ?_ (gmUnitsEquiv_mul W _ _)
  refine congrArg (gmUnitsEquiv W) ?_
  rw [← hc, ← hY', ← hY]
  exact key

variable {k hU}

/-- **Composition of arrows of the evaluated action groupoid multiplies units**: the composite of
an arrow `h ⟶ h'` with unit `γ` and an arrow `h' ⟶ h''` with unit `γ'` has unit `γ' * γ`. -/
theorem groupoidArrowEquiv_comp {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' h'' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h')
    (r' : groupoidPoint p h' ⟶ groupoidPoint p h'') :
    (groupoidArrowEquiv p h h'' (r ≫ r')).1 =
      (groupoidArrowEquiv p h' h'' r').1 * (groupoidArrowEquiv p h h' r).1 := by
  refine (groupoidArrowEquiv_apply_val p (r ≫ r')).trans ?_
  refine (congrArg (fun a => (arrowsEquiv 𝒞 k p hU W a).1)
    ((actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors.evaluationArrowEquiv_comp
      (op W) r r')).trans ?_
  exact arrowsEquiv_compose_fst 𝒞 (k := k) p hU W _ _ _

/-- The unit of an identity arrow is `1`. -/
theorem groupoidArrowEquiv_id {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (groupoidArrowEquiv p h h (𝟙 (groupoidPoint p h))).1 = 1 := by
  have e := groupoidArrowEquiv_comp p (𝟙 (groupoidPoint p h)) (𝟙 (groupoidPoint p h))
  rw [Category.id_comp] at e
  exact mul_eq_left.mp e.symm

/-- `AlgebraicGeometry.PPowerWeighted.chartArrow` preserves composition. -/
theorem chartArrow_comp {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' h'' : W ⟶ totalSiteObject 𝒞 k hU} (r : groupoidPoint p h ⟶ groupoidPoint p h')
    (r' : groupoidPoint p h' ⟶ groupoidPoint p h'') :
    chartArrow.{u, w} p (r ≫ r') = chartArrow.{u, w} p r ≫ chartArrow.{u, w} p r' := by
  have e : ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map
      (r ≫ r')).1 =
      ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map r).1 ≫
        ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map r').1 :=
    congrArg Subtype.val
      ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map_comp r r')
  exact (congrArg (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map e).trans
    ((presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map_comp _ _)

/-- `AlgebraicGeometry.PPowerWeighted.chartArrow` preserves identities. -/
theorem chartArrow_id {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    chartArrow.{u, w} p (𝟙 (groupoidPoint p h)) = 𝟙 _ := by
  have e : ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map
      (𝟙 (groupoidPoint p h))).1 = 𝟙 _ :=
    congrArg Subtype.val
      ((Stack.pointwiseToQuotientStackFiber (actionGroupoidOverBase 𝒞 k p hU) W).map_id _)
  exact (congrArg (presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map e).trans
    ((presentingFunctor.{u, w} 𝒞 k p hU).toFunctor.map_id _)

/-- **Composition of vertical isomorphisms of chart objects.** The composite of the vertical
isomorphism `a(h) ⟶ a(h')` of a unit `γ` and the vertical isomorphism `a(h') ⟶ a(h'')` of a unit
`γ'` is the vertical isomorphism of `γ' * γ`. -/
theorem chartVerticalEquiv_comp {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' h'' : W ⟶ totalSiteObject 𝒞 k hU}
    (θ : {θ : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h) ⟶
        (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h') //
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ})
    (θ' : {θ : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h') ⟶
        (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h'') //
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ}) :
    (chartVerticalEquiv.{u, w} p h h''
        ⟨θ.1 ≫ θ'.1, Functor.isHomLift_comp_of_isHomLift_id _ _ _ _ θ.2 (by
          simpa using θ'.2)⟩).1 =
      (chartVerticalEquiv.{u, w} p h' h'' θ').1 * (chartVerticalEquiv.{u, w} p h h' θ).1 := by
  have hθ := (chartVerticalArrowEquiv.{u, w} p h h').symm_apply_apply θ
  have hθ' := (chartVerticalArrowEquiv.{u, w} p h' h'').symm_apply_apply θ'
  have key : (⟨θ.1 ≫ θ'.1, Functor.isHomLift_comp_of_isHomLift_id _ _ _ _ θ.2 (by
      simpa using θ'.2)⟩ : {θ : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h) ⟶
        (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h'') //
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ}) =
      (chartVerticalArrowEquiv.{u, w} p h h'').symm
        (chartVerticalArrowEquiv.{u, w} p h h' θ ≫ chartVerticalArrowEquiv.{u, w} p h' h'' θ') := by
    apply Subtype.ext
    refine Eq.trans ?_ (chartArrow_comp p _ _).symm
    exact congrArg₂ (· ≫ ·) (congrArg Subtype.val hθ).symm (congrArg Subtype.val hθ').symm
  rw [chartVerticalEquiv_apply, key, Equiv.apply_symm_apply]
  exact groupoidArrowEquiv_comp p _ _

/-- **The identity of a chart object corresponds to the unit `1`.** -/
theorem chartVerticalEquiv_id {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (chartVerticalEquiv.{u, w} p h h ⟨𝟙 _, IsHomLift.id (BasedFunctor.w_obj _ _)⟩).1 = 1 := by
  have key : (⟨𝟙 _, IsHomLift.id (BasedFunctor.w_obj _ _)⟩ :
      {θ : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h) ⟶
        (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.obj (Over.mk h) //
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ}) =
      (chartVerticalArrowEquiv.{u, w} p h h).symm (𝟙 _) :=
    Subtype.ext (chartArrow_id.{u, w} p h).symm
  rw [chartVerticalEquiv_apply, key, Equiv.apply_symm_apply]
  exact groupoidArrowEquiv_id p h

end Composition

end AlgebraicGeometry.PPowerWeighted

end
