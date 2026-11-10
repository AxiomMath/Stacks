module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineChart
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpacesOfFppfCover

/-!
# A well-nigh affine chart with a prescribed relation (proof of Stacks 0DUQ)

Let `x : 𝒮_U ⟶ 𝒳` be a surjective, flat, finite and finitely presented 1-morphism from an affine
object of the site, and let `V` be an affine object of the site representing the self-intersection
`R = 𝒮_U ×_𝒳 𝒮_U`, with source and target `s, t : V ⟶ U`. Then `(U, V, s, t, x)` is a
`AlgebraicGeometry.Stack.WellNighAffineChart` of `𝒳`, whose composition law is the composition
law of the self-intersection (Stacks 04T4 (3)) read through the representation. This is the
construction in the proof of Stacks 0DUM, with the chart and the representing object of its
self-intersection kept: the proof of Stacks 0DUQ needs the moduli space of Stacks 0DUP built from
the groupoid `(U, R, s, t, c)` of a chart of its own choosing, and from the groupoid
`(U', R', s', t', c')` of the base-changed chart.

Along the way: two 1-morphisms from `𝒳` to an algebraic space which agree on the chart are equal
(the injectivity half of Stacks 0DUH, transported along the equivalence `[U/R] ≃ 𝒳` of
Stacks 04WY), and the chart is locally essentially surjective on fibres.

## Main results

* `AlgebraicGeometry.Stack.WellNighAffineChart.ofRepresentation`: the chart.
* `AlgebraicGeometry.Stack.WellNighAffineChart.ofRepresentation_c_app`: its composition law.
* `AlgebraicGeometry.Stack.WellNighAffineChart.eq_of_chart_comp_eq`: uniqueness of descents.
* `AlgebraicGeometry.Stack.WellNighAffineChart.locallyEssSurjOnFibers_chart`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace WellNighAffineChart

/-- A composable pair for `(yoneda.map s, yoneda.map t)` is a composable pair for `(σ, τ)` when
`yoneda.map s = σ` and `yoneda.map t = τ`. -/
theorem composable_of_eq {U V : BigFppfOver B S hS} {σ τ : yoneda.obj V ⟶ yoneda.obj U}
    {s t : V ⟶ U} (hs : yoneda.map s = σ) (ht : yoneda.map t = τ) {T : (BigFppfOver B S hS)ᵒᵖ}
    (q : (Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s)
      (yoneda.map t)).obj T) : σ.app T q.1.1 = τ.app T q.1.2 := by
  subst hs ht
  exact q.2

/-- A composition law on composable pairs for `(σ, τ)` with pointwise groupoid laws transports
along equalities `yoneda.map s = σ`, `yoneda.map t = τ` to one for `(yoneda.map s, yoneda.map t)`,
with the same values. -/
theorem exists_composition_transport {U V : BigFppfOver B S hS}
    (σ τ : yoneda.obj V ⟶ yoneda.obj U)
    (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) σ τ ⟶ yoneda.obj V)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (σ.app T) (τ.app T) fun p => c.app T p))
    (s t : V ⟶ U) (hs : yoneda.map s = σ) (ht : yoneda.map t = τ) :
    ∃ (c' : Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s)
        (yoneda.map t) ⟶ yoneda.obj V)
      (_ : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
        ((yoneda.map t).app T) fun p => c'.app T p)),
      ∀ T (q : (Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s)
          (yoneda.map t)).obj T),
        c'.app T q = c.app T ⟨q.1, composable_of_eq hs ht q⟩ := by
  subst hs ht
  exact ⟨c, hG, fun _ _ => rfl⟩

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (hsurj : IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f)
  (hfin : AlgebraicStacks.IsFinite B S hS f)
  (hrfp : AlgebraicStacks.IsRelativelyFinitePresentation B S hS f)
  {V : BigFppfOver B S hS}
  (eR : StacksRepresentableCFG.EquivalenceOver (ChartBaseChange.rel f).val.p
    (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
  (s t : V ⟶ U)
  (hs : yoneda.map s = SelfIntersection.relationSourceMap
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
  (ht : yoneda.map t = SelfIntersection.relationTargetMap
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)

/-- A chart is relatively surjective, flat and locally of finite presentation. -/
private theorem hasRelativeProperty_of_chart (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hfin : AlgebraicStacks.IsFinite B S hS f)
    (hrfp : AlgebraicStacks.IsRelativelyFinitePresentation B S hS f) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) f.hom hfin.1 ∧
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) f.hom hfin.1 ∧
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) f.hom hfin.1 :=
  ⟨(pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hfin.1).1 hsurj,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) (schemeStack.{u, w} B S hS U).property
      𝒳.property f.hom hfin.1).1 hflat,
    fun V y hy G hG he => (hrfp.2 V y hy G hG he).1⟩

include hsurj hflat hfin hrfp in
/-- **A chart is locally essentially surjective on fibres.** -/
theorem locallyEssSurjOnFibers_chart :
    Functor.LocallyEssSurjOnFibers 𝒳.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (BigFppfOver.topology B S hS) := by
  obtain ⟨hsurjP, hflatP, hlfpP⟩ := hasRelativeProperty_of_chart f hsurj hflat hfin hrfp
  exact
    AlgebraicStacks.locallyEssSurjOnFibers_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    B S hS (schemeStack.{u, w} B S hS U).val
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) f.hom
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      hlfpP T y hy G hG he⟩)

include hsurj hflat hfin hrfp hs ht in
/-- **The properties of a chart with a prescribed representation of its self-intersection.**
The source and target are finite locally free; the two composites `V ⟶ U ⟶ 𝒳` are isomorphic
over the site at every object; every morphism from `U` to an algebraic space identifying `s` and
`t` descends along the chart; and two 1-morphisms from `𝒳` to an algebraic space which agree on
the chart are equal. -/
theorem ofRepresentation_props :
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) ∧
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t) ∧
    (∀ r : (schemeFibredCategory B S hS V).val.obj,
      ∃ φ : f.hom.hom.obj ((schemeFibredCategoryMap B S hS s).hom.obj r) ⟶
          f.hom.hom.obj ((schemeFibredCategoryMap B S hS t).hom.obj r),
        𝒳.val.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS V).val.p.obj r)) φ) ∧
    (∀ (W : AlgebraicSpaces B S hS) (φ : yoneda.obj U ⟶ W.obj),
      yoneda.map s ≫ φ = yoneda.map t ≫ φ →
        ∃ g : 𝒳.val.val ⥤ᵇ (fibredCategory B S hS W.obj).val,
          BasedFunctor.comp f.hom.hom g =
            BasedFunctor.comp (sliceElementsComparison B S hS U)
              (associatedMap B S hS φ).1.hom) ∧
    (∀ (W : AlgebraicSpaces B S hS) (D₁ D₂ : 𝒳.val.val ⥤ᵇ (fibredCategory B S hS W.obj).val),
      BasedFunctor.comp f.hom.hom D₁ = BasedFunctor.comp f.hom.hom D₂ → D₁ = D₂) := by
  classical
  obtain ⟨hrep, hfinR⟩ := hfin
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    (schemeStack.{u, w} B S hS U).val
  let F : 𝒰 ⟶ 𝒳.val := f.hom
  let Uₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let Rₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let eU : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (Uₛ.obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  let eR' : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom).val.p
      (presheafOfCategories (Rₛ.obj ⋙ typeToCat)).p := eR
  have hfinP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.finiteMorphismProperty B S hS) F hrep := hfinR
  obtain ⟨hsurjP, hflatP, hlfpP⟩ := hasRelativeProperty_of_chart f hsurj hflat ⟨hrep, hfinR⟩ hrfp
  obtain ⟨E⟩ := SelfIntersection.nonempty_isEquivalenceOver_canonicalMap eU eR' 𝒳.property
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      hlfpP T y hy G hG he⟩)
  let P := SelfIntersection.selfIntersectionPresentation eU eR' 𝒳.property
  have hsF := SelfIntersection.prop_relationSource B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR'
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  have htF := SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR'
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨hsFl, htFl⟩ := SelfIntersection.isFlat_relationSource_and_relationTarget
    B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR' hrep hflatP
  obtain ⟨hsL, htL⟩ :=
    SelfIntersection.isLocallyOfFinitePresentation_relationSource_and_relationTarget
      B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR' hrep hlfpP
  have hsG : P.groupoid.source.hom = yoneda.map s := hs.symm
  have htG : P.groupoid.target.hom = yoneda.map t := ht.symm
  have hset : ∀ W : AlgebraicSpaces B S hS,
      (fibredCategory B S hS W.obj).val.p.IsFiberedInSets := fun W =>
    inferInstanceAs (PresheafOfCategories.discreteProjection W.obj).IsFiberedInSets
  have hinv : ∀ z, 𝒳.val.val.p.IsHomLift (𝟙 z.left) (P.extends_f.1.inv.app z) := fun z => by
    have : 𝒳.val.val.p.IsHomLift (𝟙 z.left) (P.extends_f.1.app z).hom := P.extends_f.2 z
    exact IsHomLift.lift_id_inv 𝒳.val.val.p z.left (P.extends_f.1.app z)
  have hfl : ∀ (m : V ⟶ U) (g : yoneda.obj V ⟶ yoneda.obj U), yoneda.map m = g →
      Space.IsFinite B S hS g → Space.IsFlat B S hS g →
      Space.IsLocallyOfFinitePresentation B S hS g →
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map m) := by
    rintro m g rfl
    exact isFiniteLocallyFree_of_yonedaMap B S hS m
  refine ⟨hfl s _ hs hsF hsFl hsL, hfl t _ ht htF htFl htL, ?_, ?_, ?_⟩
  · -- the vertical isomorphisms, read off the canonical 2-morphism of Stacks 044S
    intro r
    let a : (fibredCategory B S hS P.groupoid.arrows.obj).val.obj :=
      ⟨r.left, Discrete.mk r.hom⟩
    have h₁ : P.sourcePresentation.hom.functor.obj
        ((schemeFibredCategoryMap B S hS s).hom.obj r) =
        (associatedMap B S hS P.groupoid.source.hom).1.hom.obj a := by
      rw [hsG]; rfl
    have h₂ : (associatedMap B S hS P.groupoid.target.hom).1.hom.obj a =
        P.sourcePresentation.hom.functor.obj
          ((schemeFibredCategoryMap B S hS t).hom.obj r) := by
      rw [htG]; rfl
    refine ⟨P.extends_f.1.inv.app _ ≫
      P.canonicalMap.toFunctor.map ((Stack.quotientStackProjection P.groupoid).toFunctor.map
          (eqToHom h₁) ≫
        (quotientStackTwoArrow P.groupoid).app a ≫
        (Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h₂)) ≫
      P.extends_f.1.hom.app _, ?_⟩
    let z₁ := (schemeFibredCategoryMap B S hS s).hom.obj r
    let z₂ := (schemeFibredCategoryMap B S hS t).hom.obj r
    have hv₁ := hinv z₁
    have hv₃ : 𝒳.val.val.p.IsHomLift (𝟙 r.left) (P.extends_f.1.hom.app z₂) := P.extends_f.2 z₂
    have hqe : ∀ {a b : (fibredCategory B S hS P.groupoid.objects.obj).val.obj} (h : a = b),
        (fibredCategory B S hS P.groupoid.objects.obj).val.p.obj a = r.left →
        (Stack.quotientStack P.groupoid).p.IsHomLift (𝟙 r.left)
          ((Stack.quotientStackProjection P.groupoid).toFunctor.map (eqToHom h)) := fun h hr =>
      have := IsHomLift.eqToHom_domain_lift_id
        (p := (fibredCategory B S hS P.groupoid.objects.obj).val.p) h (R := r.left) hr
      Functor.isHomLift_map_of_comp_eq (Stack.quotientStackProjection P.groupoid).w (𝟙 r.left)
        (eqToHom h)
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
    exact @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p r.left _ _ _ _ _ hv₁
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
    have := hset W
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
    have hv := hinv z
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
  · -- uniqueness: Stacks 0DUH on `[U/R]`, transported along the canonical equivalence
    intro W D₁ D₂ hD
    have := hset W
    have hL : BasedFunctor.comp P.canonicalMap D₁ = BasedFunctor.comp P.canonicalMap D₂ := by
      refine restriction_injective P.groupoid _ _ ?_
      refine BasedCategory.BasedFunctor.ext' ?_
      refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _
        (BasedFunctor.comp (Stack.quotientStackProjection P.groupoid)
          (BasedFunctor.comp P.canonicalMap D₁)).w
        (BasedFunctor.comp (Stack.quotientStackProjection P.groupoid)
          (BasedFunctor.comp P.canonicalMap D₂)).w (fun z => ?_)
      obtain ⟨T, ⟨a⟩⟩ := z
      let o : 𝒰.val.obj := Over.mk a
      have e : ∀ D : 𝒳.val.val ⥤ᵇ (fibredCategory B S hS W.obj).val,
          D.obj (P.canonicalMap.toFunctor.obj
            ((Stack.quotientStackProjection P.groupoid).toFunctor.obj
              (P.sourcePresentation.hom.functor.obj o))) = D.obj (f.hom.hom.obj o) := fun D =>
        obj_eq_of_isHomLift_id_fibredCategory D (P.extends_f.1.hom.app o) (P.extends_f.2 o)
      exact (e D₁).trans ((congrArg (fun L => L.obj o) hD).trans (e D₂).symm)
    refine BasedCategory.BasedFunctor.ext' ?_
    refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _ D₁.w D₂.w (fun a => ?_)
    have e : ∀ D : 𝒳.val.val ⥤ᵇ (fibredCategory B S hS W.obj).val,
        D.obj (P.canonicalMap.toFunctor.obj (E.inv.obj a)) = D.obj a := fun D =>
      obj_eq_of_isHomLift_id_fibredCategory D (E.counitIso.hom.app a) (E.counit_vertical a)
    exact (e D₁).symm.trans ((congrArg (fun L => L.obj (E.inv.obj a)) hL).trans (e D₂))

/-- The source of the self-intersection, on representing presheaves. -/
noncomputable def relSourceMap : yoneda.obj V ⟶ yoneda.obj U :=
  SelfIntersection.relationSourceMap
    (𝒰 := (schemeStack.{u, w} B S hS U).val) (𝒳 := 𝒳.val) (f := f.hom.hom)
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR

/-- The target of the self-intersection, on representing presheaves. -/
noncomputable def relTargetMap : yoneda.obj V ⟶ yoneda.obj U :=
  SelfIntersection.relationTargetMap
    (𝒰 := (schemeStack.{u, w} B S hS U).val) (𝒳 := 𝒳.val) (f := f.hom.hom)
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR

/-- The composition law of the self-intersection (Stacks 04T4 (3)), on representing presheaves. -/
noncomputable def relCompositionLaw :
    Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (relSourceMap f eR)
      (relTargetMap f eR) ⟶ yoneda.obj V :=
  SelfIntersection.compositionLaw
    (𝒰 := (schemeStack.{u, w} B S hS U).val) (𝒳 := 𝒳.val) (f := f.hom.hom)
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
    (SelfIntersection.isFiberedInSetoids_source (𝒰 := (schemeStack.{u, w} B S hS U).val)
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (PresheafOfCategories.sliceElementsEquivalenceOver U))

/-- For every object `T`, the source map, target map and composition law of the
self-intersection, evaluated at `T`, form a groupoid. -/
theorem relCompositionLaw_pointwise : ∀ T, Nonempty (Deformation.PointwiseGroupoid
    ((relSourceMap f eR).app T) ((relTargetMap f eR).app T)
      fun p => (relCompositionLaw f eR).app T p) :=
  SelfIntersection.nonempty_pointwiseGroupoid
    (𝒰 := (schemeStack.{u, w} B S hS U).val) (𝒳 := 𝒳.val) (f := f.hom.hom)
    (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
    (SelfIntersection.isFiberedInSetoids_source (𝒰 := (schemeStack.{u, w} B S hS U).val)
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (PresheafOfCategories.sliceElementsEquivalenceOver U))

include hsurj hflat hfin hrfp hs ht in
/-- **The well-nigh affine chart `(U, V, s, t, x)`** attached to a chart `x` and an affine
representing object `V` of its self-intersection, with the composition law of the
self-intersection. -/
noncomputable def ofRepresentation (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    WellNighAffineChart.{u, w} B S hS 𝒳 where
  U := U
  isAffine_U := hU
  V := V
  isAffine_V := hV
  s := s
  t := t
  c := (exists_composition_transport _ _ (relCompositionLaw f eR)
    (relCompositionLaw_pointwise f eR) s t hs ht).choose
  pointwise := (exists_composition_transport _ _ (relCompositionLaw f eR)
    (relCompositionLaw_pointwise f eR) s t hs ht).choose_spec.choose
  isFiniteLocallyFree_s := (ofRepresentation_props f hsurj hflat hfin hrfp eR s t hs ht).1
  isFiniteLocallyFree_t := (ofRepresentation_props f hsurj hflat hfin hrfp eR s t hs ht).2.1
  chart := f
  isSurjective_chart := hsurj
  isFlat_chart := hflat
  isFinite_chart := hfin
  isRelativelyFinitePresentation_chart := hrfp
  vertical := (ofRepresentation_props f hsurj hflat hfin hrfp eR s t hs ht).2.2.1
  descend := (ofRepresentation_props f hsurj hflat hfin hrfp eR s t hs ht).2.2.2.1

/-- The composition law of `ofRepresentation` is that of the self-intersection. -/
theorem ofRepresentation_c_app (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (T : (BigFppfOver B S hS)ᵒᵖ)
    (q : (Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s)
      (yoneda.map t)).obj T) :
    (ofRepresentation f hsurj hflat hfin hrfp eR s t hs ht hU hV).c.app T q =
      (relCompositionLaw f eR).app T ⟨q.1, composable_of_eq hs ht q⟩ :=
  (exists_composition_transport _ _ (relCompositionLaw f eR)
    (relCompositionLaw_pointwise f eR) s t hs ht).choose_spec.choose_spec T q

include hsurj hflat hfin hrfp hs ht in
/-- **Two 1-morphisms from `𝒳` to an algebraic space which agree on the chart are equal.** -/
theorem eq_of_chart_comp_eq (W : AlgebraicSpaces B S hS)
    (D₁ D₂ : 𝒳.val.val ⥤ᵇ (fibredCategory B S hS W.obj).val)
    (hD : BasedFunctor.comp f.hom.hom D₁ = BasedFunctor.comp f.hom.hom D₂) : D₁ = D₂ :=
  (ofRepresentation_props f hsurj hflat hfin hrfp eR s t hs ht).2.2.2.2 W D₁ D₂ hD

end WellNighAffineChart

end AlgebraicGeometry.Stack

end
