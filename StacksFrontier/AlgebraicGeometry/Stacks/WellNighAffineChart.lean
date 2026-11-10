module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationLift
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow

/-!
# Charts of well-nigh affine algebraic stacks

A well-nigh affine algebraic stack `𝒳` (Stacks 0DUL) has, by definition, a surjective, flat,
finite and finitely presented 1-morphism `x : U ⟶ 𝒳` from an affine scheme `U`, and by
(1) ⟹ (2) of Stacks 0DUM the self-intersection `R = U ×_𝒳 U` is an affine scheme with finite
locally free projections `s, t : R ⟶ U`, and `𝒳 = [U/R]`. The proof of Stacks 0DUP uses this
presentation through two of its consequences, which hold *for the chart `x` itself*:

* the two composites `R ⟶ U ⟶ 𝒳` through `s` and through `t` are isomorphic, objectwise over
  the site; and
* an `R`-invariant morphism `U ⟶ W` to an algebraic space descends to a 1-morphism `𝒳 ⟶ W`
  restricting to it along `x` (Stacks 0DUH).

`AlgebraicGeometry.Stack.WellNighAffineChart` packages the chart, the groupoid and these two
facts; `AlgebraicGeometry.Stack.nonempty_wellNighAffineChart` produces one from well-nigh
affineness. It is the statement of (1) ⟹ (2) of Stacks 0DUM
(`AlgebraicGeometry.Stack.hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine`)
with the chart retained, which that existential statement forgets, and the proof is that one
with the comparison of Stacks 04T4 (5) between the canonical morphism and the chart kept.

## Main definitions

* `AlgebraicGeometry.Stack.WellNighAffineChart`: the chart data.

## Main results

* `AlgebraicGeometry.Stack.nonempty_wellNighAffineChart`: a well-nigh affine algebraic stack has
  such a chart.

## References

* [Stacks Project, Tag 0DUL](https://stacks.math.columbia.edu/tag/0DUL)
* [Stacks Project, Tag 0DUM](https://stacks.math.columbia.edu/tag/0DUM)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w v t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A chart of a well-nigh affine algebraic stack together with its affine finite locally
free relation.** The chart `x : U ⟶ 𝒳` from an affine object of the site is surjective, flat,
finite and of finite presentation; `s, t : V ⟶ U` are finite locally free morphisms of affine
objects of the site carrying a groupoid structure on their sections, the two composites
`V ⟶ U ⟶ 𝒳` are isomorphic over the site at every object, and every morphism `U ⟶ W` to an
algebraic space identifying `s` and `t` descends along `x`. -/
structure WellNighAffineChart (𝒳 : AlgebraicStacks.{u, w} B S hS) where
  /-- The affine object of the site carrying the chart. -/
  U : BigFppfOver B S hS
  /-- The object `U` is an affine scheme. -/
  isAffine_U : IsAffine ((BigFppfOver.toScheme B S hS).obj U)
  /-- The affine object of the site representing the self-intersection. -/
  V : BigFppfOver B S hS
  /-- The object `V` is an affine scheme. -/
  isAffine_V : IsAffine ((BigFppfOver.toScheme B S hS).obj V)
  /-- The source of the relation. -/
  s : V ⟶ U
  /-- The target of the relation. -/
  t : V ⟶ U
  /-- The composition law on composable pairs of sections. -/
  c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s) (yoneda.map t) ⟶
    yoneda.obj V
  /-- At every object `T` of the site, `s`, `t` and `c` form a groupoid on sections over `T`. -/
  pointwise : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
    ((yoneda.map t).app T) fun p => c.app T p)
  /-- The source `s` is finite locally free. -/
  isFiniteLocallyFree_s :
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s)
  /-- The target `t` is finite locally free. -/
  isFiniteLocallyFree_t :
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t)
  /-- The chart. -/
  chart : schemeStack.{u, w} B S hS U ⟶ 𝒳
  /-- The chart is surjective. -/
  isSurjective_chart : IsSurjective B S hS chart
  /-- The chart is flat. -/
  isFlat_chart : AlgebraicStacks.IsFlat B S hS chart
  /-- The chart is finite. -/
  isFinite_chart : AlgebraicStacks.IsFinite B S hS chart
  /-- The chart is of finite presentation. -/
  isRelativelyFinitePresentation_chart :
    AlgebraicStacks.IsRelativelyFinitePresentation B S hS chart
  /-- The two composites `V ⟶ U ⟶ 𝒳` are isomorphic over the site at every object. -/
  vertical : ∀ r : (schemeFibredCategory B S hS V).val.obj,
    ∃ φ : chart.hom.hom.obj ((schemeFibredCategoryMap B S hS s).hom.obj r) ⟶
        chart.hom.hom.obj ((schemeFibredCategoryMap B S hS t).hom.obj r),
      𝒳.val.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS V).val.p.obj r)) φ
  /-- A morphism to an algebraic space identifying `s` and `t` descends along the chart. -/
  descend : ∀ (W : AlgebraicSpaces B S hS) (φ : yoneda.obj U ⟶ W.obj),
    yoneda.map s ≫ φ = yoneda.map t ≫ φ →
      ∃ g : 𝒳.val.val ⥤ᵇ (fibredCategory B S hS W.obj).val,
        BasedFunctor.comp chart.hom.hom g =
          BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS φ).1.hom

variable {B S hS}

/-- A 1-morphism into the category fibred in sets of a presheaf takes the two ends of a vertical
morphism to the same object. -/
theorem obj_eq_of_isHomLift_id_fibredCategory {𝒵 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D : 𝒵 ⥤ᵇ (fibredCategory B S hS W).val)
    {a b : 𝒵.obj} (φ : a ⟶ b) {T : BigFppfOver B S hS} (hφ : 𝒵.p.IsHomLift (𝟙 T) φ) :
    D.obj a = D.obj b :=
  congrArg Subtype.val
    ((PresheafOfCategories.isDiscrete_fiber_discreteProjection W T).eq_of_hom
    (X := ⟨D.obj a, (Functor.congr_obj D.w a).trans (IsHomLift.domain_eq 𝒵.p (𝟙 T) φ)⟩)
    (Y := ⟨D.obj b, (Functor.congr_obj D.w b).trans (IsHomLift.codomain_eq 𝒵.p (𝟙 T) φ)⟩)
    ⟨D.toFunctor.map φ, Functor.isHomLift_map_of_comp_eq D.w (𝟙 T) φ⟩)

variable (B S hS)

/-- **A well-nigh affine algebraic stack has a chart with an affine finite locally free
relation.** This is (1) ⟹ (2) of Stacks 0DUM with the chart retained: the relation is the
self-intersection of the chart that Stacks 0DUL provides, and the two properties of the chart
are read off the canonical morphism of Stacks 04T4 (4) and (5), an equivalence by Stacks 04WY,
through its comparison with the chart. -/
theorem nonempty_wellNighAffineChart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) : Nonempty (WellNighAffineChart.{u, w} B S hS 𝒳) := by
  classical
  obtain ⟨U, hU, f, hsurj, hflat, hfin, hrfp⟩ := h𝒳
  obtain ⟨hrep, hfinR⟩ := hfin
  obtain ⟨-, hfp⟩ := hrfp
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS U
  let F : 𝒰 ⟶ 𝒳.val := f.hom
  let Uₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let eU : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (Uₛ.obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS 𝒰 𝒳.val F.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  let R₀ : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR₀' : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom).val.p
      (presheafOfCategories (R₀.obj ⋙ typeToCat)).p := eR₀
  have hfinP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.finiteMorphismProperty B S hS) F hrep := hfinR
  have hflatP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) F hrep :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) (schemeStack.{u, w} B S hS U).property
      𝒳.property F hrep).1 hflat
  have hlfpP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) F hrep :=
    fun V y hy G hG he => (hfp V y hy G hG he).1
  have hsurjP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) F hrep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hrep).1 hsurj
  have ht₀ : Space.IsFinite B S hS (SelfIntersection.relationTarget eU eR₀').hom :=
    SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ R₀ eU eR₀'
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨V, p, i, hV, -, hpb⟩ := ht₀ U hU (𝟙 _)
  have hi : IsIso i := hpb.flip.isIso_snd_of_isIso
  let Rₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom).val.p
      (presheafOfCategories (Rₛ.obj ⋙ typeToCat)).p :=
    eR₀'.trans (PresheafOfCategories.equivalenceOverOfIso (asIso i).symm)
  obtain ⟨E⟩ := SelfIntersection.nonempty_isEquivalenceOver_canonicalMap eU eR 𝒳.property
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      hlfpP T y hy G hG he⟩)
  let P := SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property
  have hsF := SelfIntersection.prop_relationSource B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  have htF := SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨hsFl, htFl⟩ := SelfIntersection.isFlat_relationSource_and_relationTarget
    B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR hrep hflatP
  obtain ⟨hsL, htL⟩ :=
    SelfIntersection.isLocallyOfFinitePresentation_relationSource_and_relationTarget
      B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR hrep hlfpP
  obtain ⟨s, t, c', hG', hs, ht, -⟩ := exists_representedGroupoid_eq_ofComposable B S hS
    (SelfIntersection.relationSourceMap eU eR) (SelfIntersection.relationTargetMap eU eR)
    (SelfIntersection.compositionLaw eU eR (SelfIntersection.isFiberedInSetoids_source eU))
    (SelfIntersection.nonempty_pointwiseGroupoid eU eR
      (SelfIntersection.isFiberedInSetoids_source eU))
  -- the source and target of the groupoid of the presentation are `s` and `t`
  have hsG : P.groupoid.source.hom = yoneda.map s := hs.symm
  have htG : P.groupoid.target.hom = yoneda.map t := ht.symm
  have hflf : ∀ (g : V ⟶ U) (m : yoneda.obj V ⟶ yoneda.obj U), yoneda.map g = m →
      Space.IsFinite B S hS m → Space.IsFlat B S hS m →
      Space.IsLocallyOfFinitePresentation B S hS m →
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map g) := by
    rintro g m rfl
    exact isFiniteLocallyFree_of_yonedaMap B S hS g
  -- lifting of the identity along the inverse of the comparison to the chart
  have hv : ∀ z : (schemeFibredCategory B S hS U).val.obj,
      𝒳.val.val.p.IsHomLift (𝟙 z.left) (P.extends_f.1.inv.app z) := fun z => by
    have : 𝒳.val.val.p.IsHomLift (𝟙 z.left) (P.extends_f.1.app z).hom := P.extends_f.2 z
    exact IsHomLift.lift_id_inv 𝒳.val.val.p z.left (P.extends_f.1.app z)
  -- the projection to the quotient stack takes `eqToHom` to a lift of the identity
  have hqe : ∀ {x y : (fibredCategory B S hS P.groupoid.objects.obj).val.obj} (h : x = y) {T},
      (fibredCategory B S hS P.groupoid.objects.obj).val.p.obj x = T →
      (Stack.quotientStack P.groupoid).p.IsHomLift (𝟙 T)
        ((Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h)) :=
    fun h _ hT => by
      have := IsHomLift.eqToHom_domain_lift_id
        (p := (fibredCategory B S hS P.groupoid.objects.obj).val.p) h hT
      exact Functor.isHomLift_map_of_comp_eq (Stack.quotientStackProjection P.groupoid).w _ _
  refine ⟨{
    U := U
    isAffine_U := hU
    V := V
    isAffine_V := hV
    s := s
    t := t
    c := c'
    pointwise := hG'
    isFiniteLocallyFree_s := ?_
    isFiniteLocallyFree_t := ?_
    chart := f
    isSurjective_chart := hsurj
    isFlat_chart := hflat
    isFinite_chart := ⟨hrep, hfinR⟩
    isRelativelyFinitePresentation_chart := ⟨hrep, hfp⟩
    vertical := ?_
    descend := ?_ }⟩
  · exact hflf s _ hs hsF hsFl hsL
  · exact hflf t _ ht htF htFl htL
  · -- the vertical isomorphisms, read off the canonical 2-morphism of Stacks 044S
    intro r
    let a : (fibredCategory B S hS P.groupoid.arrows.obj).val.obj :=
      ⟨r.left, Discrete.mk r.hom⟩
    have h₁ : P.sourcePresentation.hom.functor.obj
        ((schemeFibredCategoryMap B S hS s).hom.obj r) =
        (associatedMap B S hS P.groupoid.source.hom).1.hom.obj a := by
      rw [hsG]
      rfl
    have h₂ : (associatedMap B S hS P.groupoid.target.hom).1.hom.obj a =
        P.sourcePresentation.hom.functor.obj
          ((schemeFibredCategoryMap B S hS t).hom.obj r) := by
      rw [htG]
      rfl
    refine ⟨P.extends_f.1.inv.app _ ≫
      P.canonicalMap.toFunctor.map ((Stack.quotientStackProjection P.groupoid).toFunctor.map
          (eqToHom h₁) ≫
        (quotientStackTwoArrow P.groupoid).app a ≫
        (Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h₂)) ≫
      P.extends_f.1.hom.app _, ?_⟩
    let z₁ := (schemeFibredCategoryMap B S hS s).hom.obj r
    let z₂ := (schemeFibredCategoryMap B S hS t).hom.obj r
    have hv₃ : 𝒳.val.val.p.IsHomLift (𝟙 r.left) (P.extends_f.1.hom.app z₂) := P.extends_f.2 z₂
    have hq₂ : (Stack.quotientStack P.groupoid).p.IsHomLift (𝟙 r.left)
        ((quotientStackTwoArrow P.groupoid).app a) :=
      (quotientStackTwoArrow P.groupoid).isHomLift' a
    have hq : (Stack.quotientStack P.groupoid).p.IsHomLift (𝟙 r.left)
        ((Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h₁) ≫
          (quotientStackTwoArrow P.groupoid).app a ≫
          (Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h₂)) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ (Stack.quotientStack P.groupoid).p r.left _ _ _ _ _
        (hqe h₁ rfl)
        (@IsHomLift.comp_of_lift_id _ _ _ _ (Stack.quotientStack P.groupoid).p r.left _ _ _ _ _
          hq₂ (hqe h₂ rfl))
    have hc : 𝒳.val.val.p.IsHomLift (𝟙 r.left) (P.canonicalMap.toFunctor.map
        ((Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h₁) ≫
          (quotientStackTwoArrow P.groupoid).app a ≫
          (Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h₂))) :=
      Functor.isHomLift_map_of_comp_eq P.canonicalMap.w (𝟙 r.left) _
    change 𝒳.val.val.p.IsHomLift (𝟙 r.left) _
    exact @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p r.left _ _ _ _ _ (hv z₁)
      (@IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p r.left _ _ _ _ _ hc hv₃)
  · -- descent along the canonical morphism, an equivalence by Stacks 04WY, and Stacks 0DUH
    intro W φ hφ
    let φ' : P.groupoid.objects ⟶ W := ObjectProperty.homMk φ
    have hφ' : P.groupoid.target ≫ φ' = P.groupoid.source ≫ φ' := by
      apply ObjectProperty.hom_ext
      change P.groupoid.target.hom ≫ φ = P.groupoid.source.hom ≫ φ
      rw [hsG, htG]
      exact hφ.symm
    let D := quotientStackOfInvariant P.groupoid φ' hφ'
    refine ⟨BasedFunctor.comp ⟨E.inv, E.inv_over⟩ D, ?_⟩
    have : (fibredCategory B S hS W.obj).val.p.IsFiberedInSets :=
      inferInstanceAs (PresheafOfCategories.discreteProjection W.obj).IsFiberedInSets
    refine BasedCategory.BasedFunctor.ext' ?_
    refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _
      (BasedFunctor.comp f.hom.hom (BasedFunctor.comp ⟨E.inv, E.inv_over⟩ D)).w
      (BasedFunctor.comp (sliceElementsComparison B S hS U)
        (associatedMap B S hS φ).1.hom).w (fun z => ?_)
    have hproj := congrArg
      (fun L : (fibredCategory B S hS P.groupoid.objects.obj).val ⥤ᵇ
          (fibredCategory B S hS W.obj).val => L.obj (P.sourcePresentation.hom.functor.obj z))
      (quotientStackProjection_comp_quotientStackOfInvariant P.groupoid φ' hφ')
    refine Eq.trans ?_ hproj
    let y := (Stack.quotientStackProjection P.groupoid).toFunctor.obj
      (P.sourcePresentation.hom.functor.obj z)
    have h₁ : (Stack.quotientStack P.groupoid).p.IsHomLift (𝟙 z.left)
        (E.inv.map (P.extends_f.1.inv.app z)) :=
      Functor.isHomLift_map_of_comp_eq E.inv_over (𝟙 z.left) _
    have hx : (Stack.quotientStack P.groupoid).p.obj
        ((P.canonicalMap.toFunctor ⋙ E.inv).obj y) = z.left := by
      change ((P.canonicalMap.toFunctor ⋙ E.inv) ⋙ (Stack.quotientStack P.groupoid).p).obj y = _
      rw [Functor.assoc, E.inv_over, P.canonicalMap.w]
      rfl
    have h₂ : (Stack.quotientStack P.groupoid).p.IsHomLift (𝟙 z.left) (E.unitIso.app y).hom :=
      (congrArg (fun T => (Stack.quotientStack P.groupoid).p.IsHomLift (𝟙 T)
        (E.unitIso.app y).hom) hx).mp (E.unit_vertical y)
    exact obj_eq_of_isHomLift_id_fibredCategory D
      (E.inv.map (P.extends_f.1.inv.app z) ≫ (E.unitIso.app y).hom) (T := z.left)
      (@IsHomLift.comp_of_lift_id _ _ _ _ (Stack.quotientStack P.groupoid).p z.left _ _ _ _ _
        h₁ h₂)

end AlgebraicGeometry.Stack

end
