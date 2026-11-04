module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartReducedSubschemeInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartReducedSubschemeRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinChart
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningReduction
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRetarget

/-!
# Substacks cut out by invariant subschemes of a smooth chart

Let `a : U ⟶ 𝒳` be a smooth 1-morphism, representable by algebraic spaces, from the algebraic
stack of a scheme `U` of the big fppf site of `S` to an algebraic stack `𝒳`. This file descends
subschemes of `U` which are invariant under the relation `U ×_𝒳 U` to substacks of `𝒳`, in the
generality needed to build the strata of a quotient stack.

## Restricted charts

The common core is `AlgebraicGeometry.Stack.restrictedChart`. Let `P` be a property of the
objects of `𝒳`, closed under isomorphism and cutting out an algebraic stack, and let `i : V ⟶ U`
be a monomorphism of the site such that `a(h)` has `P` exactly when `h : W ⟶ U` factors through
`i`. Then `a` restricts to a 1-morphism from `V` to the full subcategory on `P`, sending `k` to
`a(k ≫ i)`, whose base changes are those of `a`
(`AlgebraicGeometry.Stack.nonempty_equivalenceOver_restrictedChart_baseChange`): it is
representable by algebraic spaces, smooth and surjective when `a` is, its image on points is the
image of `V`, and the substack is reduced when `V` is.

## The closed case

For a subscheme `Z` of `U` which is invariant in the sense of
`AlgebraicGeometry.Stack.IsChartInvariantSubscheme` — membership of `Z` is transported along
every pair of morphisms to `U` whose images under `a` are joined by a morphism over the identity —
the property `AlgebraicGeometry.Stack.invariantSubschemeProperty` (every lift to `U` of a base
change of `x` factors through `Z`) is tested on one lift, is fppf local, and has chart subfunctor
the functor of points of `Z`. For `Z` a closed subscheme it cuts out a closed substack by the
closed case of **Stacks 0507**, and `Z` is a smooth surjective chart of it. The reduced induced
closed subscheme of the chart on a closed set of points is invariant
(`AlgebraicGeometry.Stack.isChartInvariantSubscheme_chartReducedSubscheme`), so this generalizes
the construction of **Stacks 0509** in
`StacksFrontier/AlgebraicGeometry/Stacks/ReducedClosedSubstackExistence.lean`.

## The open case

For an open subscheme `j : D ⟶ U` whose image `Ω` in `|𝒳|` is saturated, `|a|⁻¹ Ω = |D|`, the
set `Ω` is open (`AlgebraicGeometry.Stack.isOpen_of_preimage_chartPointMap_eq`, from openness of
smooth morphisms on points), and `a` restricts to a smooth surjective chart
`AlgebraicGeometry.Stack.openRestrictedChart` of the open substack on `Ω` of **Stacks 06FJ**.

## Open and closed

For an open substack `O` of `𝒳` and a closed substack `Q` of `O`, the objects of `𝒳` lying in
`O` and there in `Q` form a locally closed substack of `𝒳`
(`AlgebraicGeometry.Stack.isLocallyClosedSubstack_openClosedProperty`), equivalent over the site
to `Q`, hence reduced when `Q` is, with the image of the points of `Q` as point set.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restricting a chart to a monomorphism into its scheme -/

section RestrictedChart

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (P : ObjectProperty 𝒳.val.val.obj)
  (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) (i : V ⟶ U)
  (hmem : ∀ (W : BigFppfOver B S hS) (h : W ⟶ U),
    P (a.hom.hom.toFunctor.obj (Over.mk h)) ↔ ∃ g : W ⟶ V, g ≫ i = h)

include hmem in
/-- The image under `a` of the composite of a morphism `k : W ⟶ V` with `i` has the property. -/
theorem prop_obj_overMap_of_forall_iff (k : Over V) :
    P (a.hom.hom.toFunctor.obj ((Over.map i).obj k)) :=
  (hmem k.left (k.hom ≫ i)).2 ⟨k.hom, rfl⟩

/-- **The restriction of a chart to a monomorphism.** If `a(h)` has `P` exactly when `h` factors
through `i : V ⟶ U`, the chart `a` restricts to a 1-morphism from the algebraic stack of `V` to
the full subcategory on `P`: a morphism `k : W ⟶ V` goes to `a(k ≫ i)`. -/
def restrictedChart :
    schemeStack.{u, w} B S hS V ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := ObjectProperty.lift _
        (CatFiberedInGroupoids.homFunctor (schemeStackMap.{u, w} B S hS i).hom ⋙
          a.hom.hom.toFunctor)
        (prop_obj_overMap_of_forall_iff B S hS a P i hmem)
      w := by
        have hw : a.hom.hom.toFunctor ⋙ 𝒳.val.val.p =
            (schemeStack.{u, w} B S hS U).val.val.p :=
          a.hom.hom.w
        exact (congrArg (fun G => CatFiberedInGroupoids.homFunctor
          (schemeStackMap.{u, w} B S hS i).hom ⋙ G) hw).trans
            (schemeStackMap.{u, w} B S hS i).hom.hom.w })

/-- The restricted chart sends `k : W ⟶ V` to `a(k ≫ i)`. -/
@[simp]
theorem restrictedChart_obj (k : Over V) :
    ((restrictedChart B S hS a P hP i hmem).hom.hom.toFunctor.obj k).obj =
      a.hom.hom.toFunctor.obj (Over.mk (k.hom ≫ i)) :=
  rfl

/-- The restricted chart followed by the inclusion of the substack has the map on points of the
composite of `i` with `a`. -/
theorem pointsMap_restrictedChart_comp :
    AlgebraicStacks.pointsMap B S hS
        (restrictedChart B S hS a P hP i hmem ≫ fullSubcategoryInclusion 𝒳 P hP) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS i ≫ a) := by
  funext q
  induction q using Quotient.inductionOn with
  | h q => rfl

/-- **The base change of a restricted chart is the base change of the chart.** Along a
scheme-valued point `y` of the substack with values in `T`, the base change of
`AlgebraicGeometry.Stack.restrictedChart` is equivalent, over the big fppf site of `T`, to the
base change of `a` along the composite of `y` with the inclusion of the substack.

The inclusion of the substack is fully faithful, so the target of the 2-fibre product can be
changed to `𝒳` (`CategoryTheory.TwoFibreProductOver.mapBaseFstEquivalenceOver`); then the
factor `V` can be replaced by `U`, because `i` is a monomorphism and every lift to `U` of an
object of the substack factors through `i`. -/
theorem nonempty_equivalenceOver_restrictedChart_baseChange [P.IsClosedUnderIsomorphisms]
    (hi : Mono i) (T : BigFppfOver B S hS)
    (y : BigFppfOver B T.left.1 T.left.2 ⥤ (fullSubcategoryBased 𝒳 P).obj)
    (hy : y ⋙ (fullSubcategoryBased 𝒳 P).p = Over.map T.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom)
        (schemeStack.{u, w} B S hS V).val.val.p (fullSubcategoryBased 𝒳 P).p y
        (CatFiberedInGroupoids.homFunctor (restrictedChart B S hS a P hP i hmem).hom))
      (TwoFibreProductOver.fst (Over.map T.hom) (schemeStack.{u, w} B S hS U).val.val.p
        𝒳.val.val.p (y ⋙ P.ι) (CatFiberedInGroupoids.homFunctor a.hom))) := by
  let ιF := CatFiberedInGroupoids.homFunctor (schemeStackMap.{u, w} B S hS i).hom
  have hA : ιF ⋙ (schemeStack.{u, w} B S hS U).val.val.p =
      (schemeStack.{u, w} B S hS V).val.val.p :=
    (schemeStackMap.{u, w} B S hS i).hom.hom.w
  have hfull := full_homFunctor_schemeStackMap.{u, w} B S hS i hi
  have hfaith := faithful_homFunctor_schemeStackMap.{u, w} B S hS i
  have hw : a.hom.hom.toFunctor ⋙ 𝒳.val.val.p = (schemeStack.{u, w} B S hS U).val.val.p :=
    a.hom.hom.w
  have hlift : ∀ Q : TwoFibreProductOver (Over.map T.hom)
      (schemeStack.{u, w} B S hS U).val.val.p 𝒳.val.val.p (y ⋙ P.ι) a.hom.hom.toFunctor,
      ∃ (x' : (schemeStack.{u, w} B S hS V).val.val.obj)
      (_ : (schemeStack.{u, w} B S hS V).val.val.p.obj x' =
        (schemeStack.{u, w} B S hS U).val.val.p.obj Q.y) (e : Q.y ≅ ιF.obj x'),
      (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift
        (𝟙 ((schemeStack.{u, w} B S hS U).val.val.p.obj Q.y)) e.hom := by
    intro Q
    have hPy : P (a.hom.hom.toFunctor.obj (Over.mk Q.y.hom)) :=
      P.prop_of_iso Q.iso (y.obj Q.x).property
    obtain ⟨g, hg⟩ := (hmem _ Q.y.hom).1 hPy
    refine ⟨Over.mk g, rfl, Over.isoMk (Iso.refl _) ?_, ?_⟩
    · show 𝟙 _ ≫ (g ≫ i) = Q.y.hom
      rw [Category.id_comp]
      exact hg
    · exact IsHomLift.of_fac' _ _ _ rfl rfl rfl
  have hK := TwoFibreProductOver.isEquivalence_precomposeSnd_of_full_of_faithful
    (pT := Over.map T.hom) (pℬ := 𝒳.val.val.p)
    (G := y ⋙ P.ι) (F := a.hom.hom.toFunctor)
    (a := ιF) (overMap_isFiberedInGroupoids T.hom)
    (schemeStack.{u, w} B S hS U).val.property hA hfull hfaith hw hlift
  have h₁ := fst_isFiberedInGroupoids_overMap T.hom
    (schemeStack.{u, w} B S hS V).val.val.p 𝒳.val.val.p (y ⋙ P.ι)
    (ιF ⋙ a.hom.hom.toFunctor)
    (schemeStack.{u, w} B S hS V).val.property
    𝒳.val.property hy ((congrArg (fun G => ιF ⋙ G) hw).trans hA)
  have h₂ := fst_isFiberedInGroupoids_overMap T.hom (schemeStack.{u, w} B S hS U).val.val.p
    𝒳.val.val.p (y ⋙ P.ι) a.hom.hom.toFunctor (schemeStack.{u, w} B S hS U).val.property
    𝒳.val.property hy hw
  obtain ⟨E₂⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁ h₂
    (TwoFibreProductOver.precomposeSnd (pT := Over.map T.hom) (pℬ := 𝒳.val.val.p)
      (y ⋙ P.ι) a.hom.hom.toFunctor ιF hA)
    (TwoFibreProductOver.precomposeSnd_comp_fst _ _ _ _) hK
  exact ⟨(TwoFibreProductOver.mapBaseFstEquivalenceOver (b := P.ι) rfl).trans E₂⟩

variable (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)

include hrep in
/-- **A restricted chart is representable by algebraic spaces**: its base changes are those of
`a` (`AlgebraicGeometry.Stack.nonempty_equivalenceOver_restrictedChart_baseChange`). -/
theorem isRepresentableByAlgebraicSpaces_restrictedChart [P.IsClosedUnderIsomorphisms]
    (hi : Mono i) :
    IsRepresentableByAlgebraicSpaces B S hS (restrictedChart B S hS a P hP i hmem).hom.hom := by
  intro T _ _ y hy
  obtain ⟨E⟩ := nonempty_equivalenceOver_restrictedChart_baseChange B S hS a P hP i hmem hi T y hy
  obtain ⟨F, hF, ⟨e⟩⟩ := hrep T (y ⋙ P.ι) hy
  exact ⟨F, hF, ⟨E.trans e⟩⟩

include hrep in
/-- **A restricted chart inherits the relative properties of the chart** which are stable under
base change and fppf local on the target: its base changes are those of `a`. -/
theorem hasRelativeProperty_restrictedChart [P.IsClosedUnderIsomorphisms] (hi : Mono i)
    (Q : MorphismProperty (AlgebraicSpaces B S hS))
    [Q.IsStableUnderBaseChange] [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (hQ : HasRelativeProperty.{u, u, u + 1, u} B S hS Q a.hom hrep) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS Q (restrictedChart B S hS a P hP i hmem).hom
      (isRepresentableByAlgebraicSpaces_restrictedChart B S hS a P hP i hmem hrep hi) := by
  intro T y hy F hF ⟨e⟩
  obtain ⟨E⟩ := nonempty_equivalenceOver_restrictedChart_baseChange B S hS a P hP i hmem hi T y hy
  exact hQ T (y ⋙ P.ι) hy F hF ⟨E.symm.trans e⟩

variable (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
    (Space.smoothMorphismProperty B S hS) a.hom hrep)
  (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
    (Space.surjectiveMorphismProperty B S hS) a.hom hrep)

include hsmooth hsurj in
/-- **A restricted chart of a smooth surjective chart is smooth and surjective.** -/
theorem isSmooth_and_isSurjective_restrictedChart [P.IsClosedUnderIsomorphisms] (hi : Mono i) :
    AlgebraicStacks.IsSmooth B S hS (restrictedChart B S hS a P hP i hmem) ∧
      IsSurjective B S hS (restrictedChart B S hS a P hP i hmem) := by
  have hcrep := isRepresentableByAlgebraicSpaces_restrictedChart B S hS a P hP i hmem hrep hi
  refine ⟨?_, ?_⟩
  · exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) hP _ hcrep
      (hasRelativeProperty_restrictedChart B S hS a P hP i hmem hrep hi _ hsmooth)
  · exact (pointsMap_surjective_iff_isRelativelySurjective B S hS _ hcrep).2
      (hasRelativeProperty_restrictedChart B S hS a P hP i hmem hrep hi _ hsurj)

include hmem hsmooth hsurj in
/-- **The substack has as points the image of `V`.** The restricted chart is surjective on
points, and its composite with the inclusion has the map on points of the composite of `i` with
`a`. -/
theorem range_pointsMap_of_restrictedChart [P.IsClosedUnderIsomorphisms] (hi : Mono i) :
    Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) =
      AlgebraicStacks.chartPointMap B S hS U 𝒳 a ''
        Set.range ((BigFppfOver.toScheme B S hS).map i).base := by
  have hcs := (isSmooth_and_isSurjective_restrictedChart B S hS a P hP i hmem hrep hsmooth hsurj
    hi).2
  have h1 : Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) =
      Set.range (AlgebraicStacks.pointsMap B S hS
        (restrictedChart B S hS a P hP i hmem ≫ fullSubcategoryInclusion 𝒳 P hP)) := by
    rw [AlgebraicStacks.pointsMap_comp, Set.range_comp, hcs.range_eq, Set.image_univ]
  have h3 : Set.range (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS i ≫ a)) =
      Set.range (AlgebraicStacks.chartPointMap B S hS _ 𝒳
        (schemeStackMap.{u, w} B S hS i ≫ a)) := by
    let _ := pointTopology B S hS (schemeFibredCategory B S hS V)
    show _ = Set.range (AlgebraicStacks.pointsMap B S hS _ ∘ _)
    rw [Set.range_comp, (pointsHomeomorphScheme B S hS _).symm.surjective.range_eq,
      Set.image_univ]
  rw [h1, pointsMap_restrictedChart_comp, h3, chartPointMap_schemeStackMap_comp, Set.range_comp]

include hmem hsmooth hsurj in
/-- **The substack is reduced when `V` is**: the restricted chart is a smooth surjective chart
of it by the scheme `V`. -/
theorem isReducedStack_of_restrictedChart [P.IsClosedUnderIsomorphisms] (hi : Mono i)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj V)] :
    IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) := by
  obtain ⟨hsm, hs⟩ := isSmooth_and_isSurjective_restrictedChart B S hS a P hP i hmem hrep
    hsmooth hsurj hi
  exact ⟨_, restrictedChart B S hS a P hP i hmem, hs, hsm, inferInstance⟩

end RestrictedChart

/-! ### Membership of an immersed subscheme is fppf local -/

/-- **Membership of a morphism of the site in an immersed subscheme of its target is local for the
fppf topology.** -/
theorem mem_subschemePoints_of_sieve {U : BigFppfOver B S hS}
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) {W : BigFppfOver B S hS} (h : W ⟶ U)
    (hh : (Space.subschemePoints B S hS Z).sieveOfSection (U := op W) h ∈
      BigFppfOver.topology B S hS W) :
    h ∈ (Space.subschemePoints B S hS Z).obj (op W) :=
  Space.mem_subschemePoints_of_sieveOfSection B S hS (Space.subschemeι B S hS Z hZ) (Iso.refl _)
    (Category.id_comp _) h hh

/-! ### The property cut out by an invariant subscheme of a chart -/

section Invariant

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))

/-- A subscheme `Z` of the scheme of a chart `a : U ⟶ 𝒳` is *invariant* when membership of `Z`
is transported along every pair of morphisms `h, h' : W ⟶ U` whose images under `a` are joined
by a morphism of `𝒳` over the identity of `W`: if `h` factors through `Z`, so does `h'`. This is
invariance under the relation `U ×_𝒳 U`. -/
def IsChartInvariantSubscheme : Prop :=
  ∀ ⦃W : BigFppfOver B S hS⦄ (h h' : W ⟶ U)
    (θ : a.hom.hom.toFunctor.obj (Over.mk h) ⟶ a.hom.hom.toFunctor.obj (Over.mk h')),
    𝒳.val.val.p.IsHomLift (𝟙 W) θ →
    h ∈ (Space.subschemePoints B S hS Z).obj (op W) →
    h' ∈ (Space.subschemePoints B S hS Z).obj (op W)

/-- The property of an object `x` of `𝒳` that every lift of `x` to the chart `a : U ⟶ 𝒳`, after
an arbitrary base change, factors through the subscheme `Z` of `U`. -/
def invariantSubschemeProperty : ObjectProperty 𝒳.val.val.obj := fun x =>
  ∀ (W : BigFppfOver B S hS) (h : W ⟶ U), (a.hom.hom.toFunctor.obj (Over.mk h) ⟶ x) →
    h ∈ (Space.subschemePoints B S hS Z).obj (op W)

/-- The property is inherited along morphisms of `𝒳`. -/
theorem invariantSubschemeProperty_of_hom {x y : 𝒳.val.val.obj} (φ : x ⟶ y)
    (hy : invariantSubschemeProperty B S hS a Z y) :
    invariantSubschemeProperty B S hS a Z x :=
  fun W h ψ => hy W h (ψ ≫ φ)

/-- The property is closed under isomorphism, being inherited along morphisms. -/
instance : (invariantSubschemeProperty B S hS a Z).IsClosedUnderIsomorphisms :=
  ⟨fun e hx => invariantSubschemeProperty_of_hom B S hS a Z e.inv hx⟩

/-- **The reduced induced closed subscheme of a smooth chart on a closed set of points is
invariant**, by `AlgebraicGeometry.Stack.mem_chartReducedSubscheme_of_hom`. -/
theorem isChartInvariantSubscheme_chartReducedSubscheme
    (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      a.hom hrep)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    IsChartInvariantSubscheme B S hS a (chartReducedSubscheme B S hS 𝒳 U a T hT) :=
  fun _ h h' θ hθ hh => mem_chartReducedSubscheme_of_hom B S hS a hrep hsmooth T hT h h' θ hθ hh

/-- The image under a chart of the restriction `Over.mk (g ≫ h) ⟶ Over.mk h` lies over `g`. -/
private theorem isHomLift_map_overHomMk (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    {W W' : BigFppfOver B S hS} (g : W ⟶ W') (h : W' ⟶ U) :
    𝒳.val.val.p.IsHomLift g
      (a.hom.hom.toFunctor.map (Over.homMk g rfl : Over.mk (g ≫ h) ⟶ Over.mk h)) :=
  have hw : a.hom.hom.toFunctor ⋙ 𝒳.val.val.p = Over.forget U := a.hom.hom.w
  PresheafOfCategories.isHomLift_map_of_comp hw g _ (IsHomLift.of_fac' _ _ _ rfl rfl (by simp))

/-- A morphism out of the image under a chart of `h : W ⟶ U` lies over some `j : W ⟶ W'`. -/
private theorem exists_isHomLift_of_hom (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    {W W' : BigFppfOver B S hS} (h : W ⟶ U) {x : 𝒳.val.val.obj}
    (ψ : a.hom.hom.toFunctor.obj (Over.mk h) ⟶ x) (hx : 𝒳.val.val.p.obj x = W') :
    ∃ j : W ⟶ W', 𝒳.val.val.p.IsHomLift j ψ :=
  have hdom : 𝒳.val.val.p.obj (a.hom.hom.toFunctor.obj (Over.mk h)) = W :=
    Functor.congr_obj a.hom.hom.w (Over.mk h)
  ⟨eqToHom hdom.symm ≫ 𝒳.val.val.p.map ψ ≫ eqToHom hx, by infer_instance⟩

variable {a Z}

/-- **The property is tested on one lift.** If `χ : a(h₁) ⟶ x` lies over the identity of the base
`W'` of `x`, then `x` has the property exactly when `h₁ : W' ⟶ U` factors through `Z`: any other
lift of a base change of `x` is joined to the corresponding base change of `h₁` by a morphism over
the identity, and invariance of `Z` transports membership along it. -/
theorem invariantSubschemeProperty_iff (hinv : IsChartInvariantSubscheme B S hS a Z)
    {W' : BigFppfOver B S hS} {x : 𝒳.val.val.obj}
    (h₁ : W' ⟶ U) (χ : a.hom.hom.toFunctor.obj (Over.mk h₁) ⟶ x)
    (hχ : 𝒳.val.val.p.IsHomLift (𝟙 W') χ) :
    invariantSubschemeProperty B S hS a Z x ↔
      h₁ ∈ (Space.subschemePoints B S hS Z).obj (op W') := by
  refine ⟨fun hx => hx W' h₁ χ, fun hh W h ψ => ?_⟩
  have hcod : 𝒳.val.val.p.obj x = W' := IsHomLift.codomain_eq 𝒳.val.val.p (𝟙 W') χ
  obtain ⟨j, hψ⟩ := exists_isHomLift_of_hom B S hS a h ψ hcod
  have hm' : 𝒳.val.val.p.IsHomLift j
      (a.hom.hom.toFunctor.map (Over.homMk j rfl : Over.mk (j ≫ h₁) ⟶ Over.mk h₁) ≫ χ) := by
    have := isHomLift_map_overHomMk B S hS a j h₁
    have := hχ
    infer_instance
  obtain ⟨θ, hθ, -⟩ := exists_isHomLift_id_comp_eq B S hS 𝒳.val.property j _ ψ hm' hψ
  exact hinv (j ≫ h₁) h θ hθ ((Space.subschemePoints B S hS _).map j.op hh)

/-- **The property is local on the big fppf site** for an immersed subscheme: a lift of a base
change of `y` to the chart restricts, over the members of a covering sieve, to lifts of objects
with the property, and membership of an immersed subscheme is fppf local. -/
theorem invariantSubschemeProperty_of_sieve (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow)
    {U' : BigFppfOver B S hS}
    (y : 𝒳.val.val.p.Fiber U') {R : Sieve U'} (hR : R ∈ BigFppfOver.topology B S hS U')
    (hRy : ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ U'), R k →
      k ∈ (objSubfunctor (fun φ hb => invariantSubschemeProperty_of_hom B S hS a Z φ hb)
        y).obj (op V)) :
    invariantSubschemeProperty B S hS a Z y.1 := by
  intro W h ψ
  obtain ⟨j, hψ⟩ := exists_isHomLift_of_hom B S hS a h ψ y.2
  apply mem_subschemePoints_of_sieve B S hS Z hZ h
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable j hR)
  intro W₂ g hg
  obtain ⟨ζ, α, hα, hζ⟩ := hRy (g ≫ j) hg
  show g ≫ h ∈ _
  refine hζ W₂ (g ≫ h) ?_
  have hc : 𝒳.val.val.p.IsStronglyCartesian (g ≫ j) α :=
    𝒳.val.property.isStronglyCartesian_homLift _ α
  have hcomp : 𝒳.val.val.p.IsHomLift (g ≫ j)
      (a.hom.hom.toFunctor.map (Over.homMk g rfl : Over.mk (g ≫ h) ⟶ Over.mk h) ≫ ψ) := by
    have := isHomLift_map_overHomMk B S hS a g h
    have := hψ
    infer_instance
  exact Functor.IsStronglyCartesian.map 𝒳.val.val.p (g ≫ j) α (Category.id_comp _).symm
    (a.hom.hom.toFunctor.map (Over.homMk g rfl : Over.mk (g ≫ h) ⟶ Over.mk h) ≫ ψ)

/-- **The chart subfunctor of the property along `a` is the functor of points of `Z`**, by
`AlgebraicGeometry.Stack.invariantSubschemeProperty_iff` at the identity. -/
theorem chartSubfunctor_invariantSubschemeProperty (hinv : IsChartInvariantSubscheme B S hS a Z) :
    chartSubfunctor (fun φ hb => invariantSubschemeProperty_of_hom B S hS a Z φ hb) a =
      Space.subschemePoints B S hS Z := by
  ext T' s
  exact invariantSubschemeProperty_iff B S hS hinv s (𝟙 _)
    (IsHomLift.id (Functor.congr_obj a.hom.hom.w _))

/-- The image under `a` of `h : W ⟶ U` has the property exactly when `h` factors through the
inclusion of the immersed subscheme `Z`. -/
theorem invariantSubschemeProperty_obj_iff (hinv : IsChartInvariantSubscheme B S hS a Z)
    (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow) (W : BigFppfOver B S hS) (h : W ⟶ U) :
    invariantSubschemeProperty B S hS a Z (a.hom.hom.toFunctor.obj (Over.mk h)) ↔
      ∃ g : W ⟶ Space.subschemeObject B S hS Z hZ, g ≫ Space.subschemeι B S hS Z hZ = h := by
  rw [invariantSubschemeProperty_iff B S hS hinv h (𝟙 _)
      (IsHomLift.id (Functor.congr_obj a.hom.hom.w _)),
    Space.subschemePoints_eq_range B S hS (Space.subschemeι B S hS Z hZ) (Iso.refl _)
      (Category.id_comp _)]
  rfl

/-- **An invariant closed subscheme of a smooth surjective chart cuts out a closed substack.**
The property is fppf local (`AlgebraicGeometry.Stack.invariantSubschemeProperty_of_sieve`) and
its chart subfunctor along `a` is the functor of points of `Z`
(`AlgebraicGeometry.Stack.chartSubfunctor_invariantSubschemeProperty`), a closed subspace of `U`;
`AlgebraicGeometry.Stack.isClosedSubstack_of_isClosedSubspace_chartSubfunctor` (the closed case
of **Stacks 0507**) concludes. -/
theorem isClosedSubstack_invariantSubschemeProperty (hinv : IsChartInvariantSubscheme B S hS a Z)
    (hZ : _root_.AlgebraicGeometry.IsClosedImmersion Z.arrow)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      a.hom hrep)
    (hsurj : IsSurjective B S hS a) :
    IsClosedSubstack 𝒳 (invariantSubschemeProperty B S hS a Z) := by
  have hZi : _root_.AlgebraicGeometry.IsImmersion Z.arrow := inferInstance
  refine isClosedSubstack_of_isClosedSubspace_chartSubfunctor
    (fun φ hb => invariantSubschemeProperty_of_hom B S hS a Z φ hb)
    (fun U' y R hR hRy => invariantSubschemeProperty_of_sieve B S hS hZi y hR hRy)
    (J := PUnit.{1}) (fun _ => a) (fun _ => ?_) ?_ (fun _ => ?_)
  · exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep hsmooth
  · ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_range, exists_const, true_iff]
    exact hsurj x
  · rw [chartSubfunctor_invariantSubschemeProperty B S hS hinv,
      Space.subschemePoints_eq_range B S hS (Space.subschemeι B S hS Z hZi) (Iso.refl _)
        (Category.id_comp _)]
    exact Space.isClosedSubspace_range_yoneda_map B S hS _ hZ

variable (hinv : IsChartInvariantSubscheme B S hS a Z)
  (hZ : _root_.AlgebraicGeometry.IsImmersion Z.arrow)
  (hP : IsAlgebraicStack.{u, w} B S hS
    (fullSubcategoryBased 𝒳 (invariantSubschemeProperty B S hS a Z)))

/-- The inclusion of an immersed subscheme of an object of the site is a monomorphism of the
site. -/
theorem mono_subschemeι : Mono (Space.subschemeι B S hS Z hZ) :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (Space.mono_toScheme_map_of_presentation B S hS _ (Iso.refl _) (Category.id_comp _))

/-- **The chart of the substack cut out by an invariant subscheme.** The subscheme `Z` of the
chart, mapped to the substack: a morphism `k : W ⟶ Z` goes to the image under `a` of its
composite with the inclusion `Z ⟶ U`. -/
def invariantSubschemeChart :
    schemeStack.{u, w} B S hS (Space.subschemeObject B S hS Z hZ) ⟶
      fullSubcategoryAlgebraicStack 𝒳 (invariantSubschemeProperty B S hS a Z) hP :=
  restrictedChart B S hS a _ hP (Space.subschemeι B S hS Z hZ)
    (invariantSubschemeProperty_obj_iff B S hS hinv hZ)

/-- **The base change of the chart of the substack is the base change of `a`.** -/
theorem nonempty_equivalenceOver_invariantSubschemeChart_baseChange (T : BigFppfOver B S hS)
    (y : BigFppfOver B T.left.1 T.left.2 ⥤
      (fullSubcategoryBased 𝒳 (invariantSubschemeProperty B S hS a Z)).obj)
    (hy : y ⋙ (fullSubcategoryBased 𝒳 (invariantSubschemeProperty B S hS a Z)).p =
      Over.map T.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom)
        (schemeStack.{u, w} B S hS (Space.subschemeObject B S hS Z hZ)).val.val.p
        (fullSubcategoryBased 𝒳 (invariantSubschemeProperty B S hS a Z)).p y
        (CatFiberedInGroupoids.homFunctor (invariantSubschemeChart B S hS hinv hZ hP).hom))
      (TwoFibreProductOver.fst (Over.map T.hom) (schemeStack.{u, w} B S hS U).val.val.p
        𝒳.val.val.p (y ⋙ (invariantSubschemeProperty B S hS a Z).ι)
        (CatFiberedInGroupoids.homFunctor a.hom))) :=
  nonempty_equivalenceOver_restrictedChart_baseChange B S hS a _ hP _ _
    (mono_subschemeι B S hS hZ) T y hy

variable (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
  (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
    a.hom hrep)
  (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
    a.hom hrep)

include hrep in
/-- The chart of the substack is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_invariantSubschemeChart :
    IsRepresentableByAlgebraicSpaces B S hS (invariantSubschemeChart B S hS hinv hZ hP).hom.hom :=
  isRepresentableByAlgebraicSpaces_restrictedChart B S hS a _ hP _ _ hrep
    (mono_subschemeι B S hS hZ)

include hsmooth hsurj in
/-- **The chart of the substack is smooth and surjective.** -/
theorem isSmooth_and_isSurjective_invariantSubschemeChart :
    AlgebraicStacks.IsSmooth B S hS (invariantSubschemeChart B S hS hinv hZ hP) ∧
      IsSurjective B S hS (invariantSubschemeChart B S hS hinv hZ hP) :=
  isSmooth_and_isSurjective_restrictedChart B S hS a _ hP _ _ hrep hsmooth hsurj
    (mono_subschemeι B S hS hZ)

include hinv hZ hsmooth hsurj in
/-- **The substack has as points the image of the points of `Z`** under the map on points of the
chart. -/
theorem range_pointsMap_invariantSubschemeProperty :
    Set.range (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 (invariantSubschemeProperty B S hS a Z) hP)) =
      AlgebraicStacks.chartPointMap B S hS U 𝒳 a '' Set.range Z.arrow.base :=
  range_pointsMap_of_restrictedChart B S hS a _ hP _
    (invariantSubschemeProperty_obj_iff B S hS hinv hZ) hrep hsmooth hsurj
    (mono_subschemeι B S hS hZ)

include hinv hZ hsmooth hsurj in
/-- **The substack is reduced when `Z` is.** -/
theorem isReducedStack_invariantSubschemeProperty [IsReduced (Z : Scheme.{u})] :
    IsReducedStack B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (invariantSubschemeProperty B S hS a Z) hP) :=
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj (Space.subschemeObject B S hS Z hZ)) :=
    inferInstanceAs (IsReduced (Z : Scheme.{u}))
  isReducedStack_of_restrictedChart B S hS a _ hP _
    (invariantSubschemeProperty_obj_iff B S hS hinv hZ) hrep hsmooth hsurj
    (mono_subschemeι B S hS hZ)

end Invariant

/-! ### Restricting a chart to a saturated open subscheme -/

section OpenRestriction

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U D : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (j : D ⟶ U)
  (Ω : Set (AlgebraicStacks.points B S hS 𝒳))

/-- **The image of `h : W ⟶ U` under a chart lies over `Ω` exactly when `h` maps `W` into the part
of `U` lying over `Ω`.** A field-valued point mapping to `a(h)` is, up to the equivalence of
**Stacks 04XF**, the image of a point of `W`. -/
theorem pointsWithin_obj_iff_range_subset {W : BigFppfOver B S hS} (h : W ⟶ U) :
    pointsWithin 𝒳 Ω (a.hom.hom.toFunctor.obj (Over.mk h)) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map h).base ⊆
        AlgebraicStacks.chartPointMap B S hS U 𝒳 a ⁻¹' Ω := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS W)
  set F := schemeStackMap.{u, w} B S hS h ≫ a
  have key : pointsWithin 𝒳 Ω (a.hom.hom.toFunctor.obj (Over.mk h)) ↔
      ∀ z, AlgebraicStacks.pointsMap B S hS F z ∈ Ω := by
    constructor
    · intro hx z
      induction z using Quotient.inductionOn with
      | h q =>
        exact hx _ (a.hom.hom.toFunctor.map
          (Over.homMk q.obj.hom rfl : (Over.map h).obj q.obj ⟶ Over.mk h))
    · intro hz
      have h0 : pointsWithin (schemeStack.{u, w} B S hS W)
          (Stack.pointsMap B S hS _ (schemeStack.{u, w} B S hS W).val.property 𝒳.val.property
            F.hom.hom ⁻¹' Ω) (Over.mk (𝟙 W)) :=
        fun q _ => hz _
      exact pointsWithin_of_hom 𝒳 Ω (a.hom.hom.toFunctor.map
        (Over.homMk (𝟙 W) (by simp) : Over.mk h ⟶ (Over.map h).obj (Over.mk (𝟙 W))))
        (pointsWithin_obj_of_pointsWithin_preimage B S hS F.hom.hom Ω h0)
  rw [key]
  have hc := chartPointMap_schemeStackMap_comp B S hS 𝒳 U W a h
  constructor
  · rintro hz _ ⟨w, rfl⟩
    have h1 := hz ((pointsHomeomorphScheme B S hS W).symm w)
    show AlgebraicStacks.chartPointMap B S hS U 𝒳 a
      (((BigFppfOver.toScheme B S hS).map h).base w) ∈ Ω
    rw [← Function.comp_apply (f := AlgebraicStacks.chartPointMap B S hS U 𝒳 a), ← hc]
    exact h1
  · intro hr z
    have h1 := hr ⟨pointsHomeomorphScheme B S hS W z, rfl⟩
    rw [Set.mem_preimage, ← Function.comp_apply (f := AlgebraicStacks.chartPointMap B S hS U 𝒳 a),
      ← hc] at h1
    change AlgebraicStacks.pointsMap B S hS F
      ((pointsHomeomorphScheme B S hS W).symm (pointsHomeomorphScheme B S hS W z)) ∈ Ω at h1
    rwa [Homeomorph.symm_apply_apply] at h1

/-- **The image of a saturated open subscheme of a smooth surjective chart is open.** If the part
of `U` lying over `Ω` is the open subscheme `D`, then `Ω` is its image, and smooth 1-morphisms
are open on points. -/
theorem isOpen_of_preimage_chartPointMap_eq (hsm : AlgebraicStacks.IsSmooth B S hS a)
    (hsurj : IsSurjective B S hS a)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hΩ : AlgebraicStacks.chartPointMap B S hS U 𝒳 a ⁻¹' Ω =
      Set.range ((BigFppfOver.toScheme B S hS).map j).base) :
    @IsOpen _ (pointTopology B S hS 𝒳.val) Ω := by
  let _ := pointTopology B S hS 𝒳.val
  rw [← Set.image_preimage_eq Ω (AlgebraicStacks.surjective_chartPointMap B S hS U 𝒳 a hsurj),
    hΩ]
  exact AlgebraicStacks.isOpenMap_chartPointMap B S hS U 𝒳 a hsm _
    ((BigFppfOver.toScheme B S hS).map j).isOpenEmbedding.isOpen_range

variable (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hΩ : AlgebraicStacks.chartPointMap B S hS U 𝒳 a ⁻¹' Ω =
    Set.range ((BigFppfOver.toScheme B S hS).map j).base)

include hj hΩ in
/-- The image under `a` of `h : W ⟶ U` lies over `Ω` exactly when `h` factors through the
saturated open subscheme `D`. -/
theorem pointsWithin_obj_iff_exists_comp (W : BigFppfOver B S hS) (h : W ⟶ U) :
    pointsWithin 𝒳 Ω (a.hom.hom.toFunctor.obj (Over.mk h)) ↔ ∃ g : W ⟶ D, g ≫ j = h := by
  rw [pointsWithin_obj_iff_range_subset B S hS a Ω h, hΩ]
  refine ⟨Space.exists_factorization_of_isOpenImmersion j hj h, ?_⟩
  rintro ⟨g, rfl⟩
  rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

include hj in
/-- An open immersion of the site is a monomorphism of the site. -/
theorem mono_of_isOpenImmersion_toScheme_map : Mono j :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

variable (hΩo : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω)

/-- **The restriction of a chart to a saturated open subscheme.** If the part of `U` lying over a
set `Ω` of points of `𝒳` is the open subscheme `D`, the chart `a` restricts to a 1-morphism from
the algebraic stack of `D` to the open substack of `𝒳` on `Ω` (**Stacks 06FJ**), sending
`k : W ⟶ D` to `a(k ≫ j)`. -/
def openRestrictedChart :
    schemeStack.{u, w} B S hS D ⟶ fullSubcategoryAlgebraicStack 𝒳
      (pointsWithinOpenSubstack B S hS 𝒳 Ω hΩo).property
      (pointsWithinOpenSubstack B S hS 𝒳 Ω hΩo).isAlgebraic :=
  restrictedChart B S hS a (pointsWithin 𝒳 Ω) _ j
    (pointsWithin_obj_iff_exists_comp B S hS a j Ω hj hΩ)

/-- The restricted chart sends `k : W ⟶ D` to `a(k ≫ j)`. -/
@[simp]
theorem openRestrictedChart_obj (k : Over D) :
    ((openRestrictedChart B S hS a j Ω hj hΩ hΩo).hom.hom.toFunctor.obj k).obj =
      a.hom.hom.toFunctor.obj (Over.mk (k.hom ≫ j)) :=
  rfl

variable (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
  (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
    a.hom hrep)
  (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
    a.hom hrep)

include hrep in
/-- The restriction of a chart to a saturated open subscheme is representable by algebraic
spaces. -/
theorem isRepresentableByAlgebraicSpaces_openRestrictedChart :
    IsRepresentableByAlgebraicSpaces B S hS
      (openRestrictedChart B S hS a j Ω hj hΩ hΩo).hom.hom :=
  have : (pointsWithin 𝒳 Ω).IsClosedUnderIsomorphisms :=
    ⟨fun e hx => pointsWithin_of_hom 𝒳 Ω e.inv hx⟩
  isRepresentableByAlgebraicSpaces_restrictedChart B S hS a _ _ _ _ hrep
    (mono_of_isOpenImmersion_toScheme_map B S hS j hj)

include hsmooth hsurj in
/-- **The restriction of a smooth surjective chart to a saturated open subscheme is smooth and
surjective.** -/
theorem isSmooth_and_isSurjective_openRestrictedChart :
    AlgebraicStacks.IsSmooth B S hS (openRestrictedChart B S hS a j Ω hj hΩ hΩo) ∧
      IsSurjective B S hS (openRestrictedChart B S hS a j Ω hj hΩ hΩo) :=
  have : (pointsWithin 𝒳 Ω).IsClosedUnderIsomorphisms :=
    ⟨fun e hx => pointsWithin_of_hom 𝒳 Ω e.inv hx⟩
  isSmooth_and_isSurjective_restrictedChart B S hS a _ _ _ _ hrep hsmooth hsurj
    (mono_of_isOpenImmersion_toScheme_map B S hS j hj)

end OpenRestriction

/-! ### A closed substack of an open substack -/

section OpenClosed

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} (O : OpenSubstack 𝒳)
  (Q : ObjectProperty (fullSubcategoryAlgebraicStack 𝒳 O.property O.isAlgebraic).val.val.obj)

/-- The property of an object of `𝒳` of lying in the open substack `O` and, there, in the
substack of `O` cut out by `Q`. -/
def openClosedProperty : ObjectProperty 𝒳.val.val.obj := fun x =>
  ∃ hx : O.property x, Q ⟨x, hx⟩

variable (hQ : IsAlgebraicStack.{u, w} B S hS
    (fullSubcategoryBased (fullSubcategoryAlgebraicStack 𝒳 O.property O.isAlgebraic) Q))
  (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (openClosedProperty O Q)))

/-- The comparison 1-morphism from the iterated full subcategory to the full subcategory of `𝒳`
on `AlgebraicGeometry.Stack.openClosedProperty`: it forgets nothing but regroups the two
membership proofs. -/
def openClosedComparison :
    fullSubcategoryAlgebraicStack (fullSubcategoryAlgebraicStack 𝒳 O.property O.isAlgebraic)
        Q hQ ⟶
      fullSubcategoryAlgebraicStack 𝒳 (openClosedProperty O Q) hP :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := ObjectProperty.lift _ (Q.ι ⋙ O.property.ι)
        (fun y => ⟨y.obj.property, y.property⟩)
      w := rfl })

/-- The comparison followed by the inclusion into `𝒳` is the inclusion of `Q` into `O` followed by
the inclusion of `O`. -/
theorem openClosedComparison_comp :
    openClosedComparison O Q hQ hP ≫ fullSubcategoryInclusion 𝒳 (openClosedProperty O Q) hP =
      fullSubcategoryInclusion _ Q hQ ≫ O.inclusion :=
  rfl

/-- The underlying functor of the comparison is an equivalence of categories: it is fully
faithful, both sides having the morphisms of `𝒳`, and surjective on objects. -/
theorem isEquivalence_openClosedComparison :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (openClosedComparison O Q hQ hP).hom) := by
  have hfaith : (CatFiberedInGroupoids.homFunctor (openClosedComparison O Q hQ hP).hom).Faithful :=
    ⟨fun {_ _} f g hfg => ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
      (congrArg (fun k => k.hom) hfg))⟩
  have hfull : (CatFiberedInGroupoids.homFunctor (openClosedComparison O Q hQ hP).hom).Full :=
    ⟨fun {_ _} f => ⟨ObjectProperty.homMk (ObjectProperty.homMk f.hom), rfl⟩⟩
  have hess : (CatFiberedInGroupoids.homFunctor (openClosedComparison O Q hQ hP).hom).EssSurj :=
    ⟨fun x => ⟨⟨⟨x.obj, x.property.1⟩, x.property.2⟩, ⟨Iso.refl _⟩⟩⟩
  exact Functor.IsEquivalence.mk

/-- The comparison is surjective on points: it is surjective on objects. -/
theorem isSurjective_openClosedComparison :
    IsSurjective B S hS (openClosedComparison O Q hQ hP) := by
  intro z
  induction z using Quotient.inductionOn with
  | h q =>
    exact ⟨Quotient.mk _
      { carrier := q.carrier
        base := q.base
        isSpec := q.isSpec
        obj := ⟨⟨q.obj.obj, q.obj.property.1⟩, q.obj.property.2⟩
        «over» := q.over }, rfl⟩

include hQ hP in
/-- **The substack on `AlgebraicGeometry.Stack.openClosedProperty` is equivalent over the site to
the iterated full subcategory**: the comparison has underlying functor an equivalence, and a
quasi-inverse over the site with vertical unit and counit is supplied by **Stacks 003Z**. -/
theorem nonempty_equivalence_openClosedProperty :
    Nonempty (BasedCategory.Equivalence
      (fullSubcategoryBased (fullSubcategoryAlgebraicStack 𝒳 O.property O.isAlgebraic) Q)
      (fullSubcategoryBased 𝒳 (openClosedProperty O Q))) := by
  obtain ⟨G, hG, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (fullSubcategoryAlgebraicStack _ Q hQ).val.val.p
    (fullSubcategoryAlgebraicStack 𝒳 (openClosedProperty O Q) hP).val.val.p
    (fullSubcategoryAlgebraicStack _ Q hQ).val.property
    (fullSubcategoryAlgebraicStack 𝒳 (openClosedProperty O Q) hP).val.property
    (openClosedComparison O Q hQ hP).hom.hom.toFunctor (openClosedComparison O Q hQ hP).hom.hom.w
    (isEquivalence_openClosedComparison O Q hQ hP)
  exact ⟨{ functor := (openClosedComparison O Q hQ hP).hom.hom
           inverse := ⟨G, hG⟩
           unitIso := BasedNatIso.mkNatIso η hη
           counitIso := BasedNatIso.mkNatIso ε hε }⟩

/-- **The substack on `AlgebraicGeometry.Stack.openClosedProperty` is reduced when the substack
of `O` cut out by `Q` is.** -/
theorem isReducedStack_openClosedProperty
    (hred : IsReducedStack B S hS
      (fullSubcategoryAlgebraicStack (fullSubcategoryAlgebraicStack 𝒳 O.property O.isAlgebraic)
        Q hQ)) :
    IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 (openClosedProperty O Q) hP) :=
  isReducedStack_of_isEquivalence_stackMorphism (openClosedComparison O Q hQ hP)
    (isEquivalence_openClosedComparison O Q hQ hP) (isSurjective_openClosedComparison O Q hQ hP)
    hred

/-- **The points of the substack on `AlgebraicGeometry.Stack.openClosedProperty`** are the images
in `|𝒳|` of the points of the substack of `O` cut out by `Q`. -/
theorem range_pointsMap_openClosedProperty :
    Set.range (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 (openClosedProperty O Q) hP)) =
      AlgebraicStacks.pointsMap B S hS O.inclusion ''
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion _ Q hQ)) := by
  rw [← Set.range_comp, ← AlgebraicStacks.pointsMap_comp, ← openClosedComparison_comp O Q hQ hP,
    AlgebraicStacks.pointsMap_comp, Set.range_comp,
    (isSurjective_openClosedComparison O Q hQ hP).range_eq, Set.image_univ]

/-- **A closed substack of an open substack is a locally closed substack.** The composite of the
inclusion of `Q` into `O` with the inclusion of `O` is an immersion (**Stacks 0502**), and its
essential image, which cuts out a locally closed substack by **Stacks 0506**, is
`AlgebraicGeometry.Stack.openClosedProperty`. -/
theorem isLocallyClosedSubstack_openClosedProperty
    (hQc : IsClosedSubstack (fullSubcategoryAlgebraicStack 𝒳 O.property O.isAlgebraic) Q) :
    IsLocallyClosedSubstack 𝒳 (openClosedProperty O Q) := by
  obtain ⟨hQiso, hQa, hQci⟩ := hQc
  have := O.strictlyFull
  have := hQiso
  set i := fullSubcategoryInclusion _ Q hQa ≫ O.inclusion
  have hi : AlgebraicStacks.IsImmersion B S hS i :=
    AlgebraicStacks.isImmersion_comp B S hS _ _
      (AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS _ hQci)
      ⟨O.isOpenImmersion.1, fun U y hy F hF he =>
        Space.isImmersion_of_isOpenImmersion B S hS (O.isOpenImmersion.2 U y hy F hF he)⟩
  have heq : openClosedProperty O Q = (CatFiberedInGroupoids.homFunctor i.hom).essImage := by
    ext x
    constructor
    · rintro ⟨hx, hq⟩
      exact ⟨⟨⟨x, hx⟩, hq⟩, ⟨Iso.refl _⟩⟩
    · rintro ⟨y, ⟨e⟩⟩
      exact ⟨O.property.prop_of_iso e y.obj.property,
        Q.prop_of_iso (ObjectProperty.isoMk _ e) y.property⟩
  rw [heq]
  exact AlgebraicStacks.isLocallyClosedSubstack_essImage i hi

end OpenClosed

end AlgebraicGeometry.Stack

end
