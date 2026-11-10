module

public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionPresentation
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionQuotientMap
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful

/-!
# Full faithfulness of the canonical morphism of a self-intersection presentation

Let `S` be a scheme contained in a big fppf site, let `𝒰` and `𝒳` be categories fibred in groupoids
over the big fppf site of `S`, let `f : 𝒰 ⟶ 𝒳` be a 1-morphism, and let `eU`, `eR` present `𝒰` and
its self-intersection by algebraic spaces, so that the presentation datum
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation` is available. This file
proves that the canonical morphism `f_can : [U/R] ⟶ 𝒳` of that datum is fully faithful.

## Main results

All names are in the namespace `AlgebraicGeometry.Stack.SelfIntersection`.

* `nonempty_fullyFaithful_canonicalMap`: the canonical morphism of the presentation datum is fully
  faithful.
* `full_toStackOfPointwiseGroupoid` and `faithful_toStackOfPointwiseGroupoid`: the 1-morphism from
  the pointwise groupoid fibration of the self-intersection groupoid to `𝒳` is fully faithful.
* `isIso_morPresheafMap_toStackUliftOfPointwise`: the map of morphism presheaves induced by that
  1-morphism is an isomorphism of presheaves.
* `isLocallyBijective_morPresheafMap_toStackUliftOfPointwise`: that map is locally injective and
  locally surjective.
* `nonempty_fullyFaithful_canonicalMap_of_fiber`: the canonical morphism is fully faithful if it
  is full and faithful on every fibre.
* `nonempty_fullyFaithful_canonicalMap_of_morPresheafMap`: the canonical morphism is fully
  faithful if the map of morphism presheaves induced by the 1-morphism from the pointwise groupoid
  fibration is locally injective and locally surjective.

## Implementation notes

`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` requires the source and the target to
share one morphism universe, while the quotient prestack has morphism universe `u + 1` and `𝒳` has
morphism universe `u`. The presheaf-level statements are therefore made for
`AlgebraicGeometry.Stack.SelfIntersection.toStackUliftOfPointwise`, whose target is the universe
lift of `𝒳`, and carried down to `𝒳` along `CategoryTheory.BasedCategory.uliftDown`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰.val ⥤ᵇ 𝒳.val}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- If for every test object `T` of the big fppf site the functor induced on the fibres over `T`
by the canonical morphism of the presentation datum is full and faithful, then that canonical
morphism is fully faithful. The fibrewise full faithfulness is a hypothesis. -/
theorem nonempty_fullyFaithful_canonicalMap_of_fiber
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val)
    (hfib : ∀ T : BigFppfOver B S hS,
      (Functor.Fiber.mapOfComp
          (Stack.quotientStack (selfIntersectionGroupoid eU eR (isFiberedInSetoids_source eU))).p
          𝒳.val.p
          (canonicalMapToStack eU eR (isFiberedInSetoids_source eU) h𝒳).toFunctor
          (canonicalMapToStack eU eR (isFiberedInSetoids_source eU) h𝒳).w T).Full ∧
      (Functor.Fiber.mapOfComp
          (Stack.quotientStack (selfIntersectionGroupoid eU eR (isFiberedInSetoids_source eU))).p
          𝒳.val.p
          (canonicalMapToStack eU eR (isFiberedInSetoids_source eU) h𝒳).toFunctor
          (canonicalMapToStack eU eR (isFiberedInSetoids_source eU) h𝒳).w T).Faithful) :
    Nonempty ((selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor.FullyFaithful) := by
  obtain ⟨hfull, hfaith⟩ :=
    (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
      (Stack.quotientStack (selfIntersectionGroupoid eU eR (isFiberedInSetoids_source eU))).p
      𝒳.val.p
      (Stack.isFiberedInGroupoids_quotientStack _) 𝒳.isFiberedInGroupoids _
      (canonicalMapToStack eU eR (isFiberedInSetoids_source eU) h𝒳).w).2 hfib
  have h1 : (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor.Full := hfull
  have h2 : (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor.Faithful := hfaith
  exact ⟨Functor.FullyFaithful.ofFullyFaithful
    (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor⟩

/-- The 1-morphism from the quotient prestack of the self-intersection groupoid to the universe
lift of `𝒳` is a 1-morphism of fibred categories over the big fppf site. -/
theorem isFibredOneMorphism_toStackUliftOfPointwise (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.IsFibredOneMorphism
      (stackUlift 𝒳).p (toStackUliftOfPointwise eU eR hsetU) :=
  (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val
    𝒳.isFiberedInGroupoids).isFibredOneMorphism (toStackUliftOfPointwise_comp eU eR hsetU)

/-- The extension of the 1-morphism to the universe lift of `𝒳` along the stackification is a
1-morphism of fibred categories over the big fppf site. -/
theorem isFibredOneMorphism_canonicalMapUlift (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    (Stack.quotientStack (selfIntersectionGroupoid eU eR hsetU)).p.IsFibredOneMorphism
      (stackUlift 𝒳).p (canonicalMapUlift eU eR hsetU h𝒳) :=
  (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val
    𝒳.isFiberedInGroupoids).isFibredOneMorphism (canonicalMapUlift_comp_eq eU eR hsetU h𝒳)

/-- The structure functor of the quotient prestack of a self-intersection groupoid is fibred. -/
private theorem isFibered_quotientPrestack_p (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.IsFibered :=
  (Stack.isFiberedInGroupoids_quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).isFibered

/-- The structure functor of the universe lift of `𝒳` is fibred. -/
private theorem isFibered_stackUlift_p : (stackUlift 𝒳).p.IsFibered :=
  (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibered

/-- If the 1-morphism from the pointwise groupoid fibration of the self-intersection groupoid to
the universe lift of `𝒳` induces locally injective and locally surjective maps of morphism
presheaves, then the canonical morphism of the presentation datum is fully faithful. The local
injectivity and local surjectivity, for objects of the fibres of the quotient prestack, are a
hypothesis. -/
theorem nonempty_fullyFaithful_canonicalMap_of_morPresheafMap
    (hsetU : 𝒰.val.p.IsFiberedInSetoids) (h𝒳 : IsAlgebraicStack B S hS 𝒳.val)
    (hmor : haveI : (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.IsFibered :=
        (Stack.isFiberedInGroupoids_quotientPrestack
          (selfIntersectionGroupoid eU eR hsetU)).isFibered
      haveI : (stackUlift 𝒳).p.IsFibered :=
        (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibered
      ∀ (T : BigFppfOver B S hS)
        (x y : (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.Fiber T),
        Presheaf.IsLocallyInjective ((BigFppfOver.topology B S hS).over T)
            ((isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU).morPresheafMap x y) ∧
          Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over T)
            ((isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU).morPresheafMap x y)) :
    Nonempty ((selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor.FullyFaithful) := by
  have hpfib := isFibered_quotientPrestack_p eU eR hsetU
  have hp'fib : (Stack.quotientStack (selfIntersectionGroupoid eU eR hsetU)).p.IsFibered :=
    (Stack.isFiberedInGroupoids_quotientStack (selfIntersectionGroupoid eU eR hsetU)).isFibered
  have hqfib := isFibered_stackUlift_p (𝒳 := 𝒳)
  have hG := Stack.isFibredOneMorphism_toQuotientStack (selfIntersectionGroupoid eU eR hsetU)
  have hH := isFibredOneMorphism_canonicalMapUlift eU eR hsetU h𝒳
  have hFmor := Functor.Stackification.isLocallyBijective_morPresheafMap_of_natIso
    hG hH (BigFppfOver.topology B S hS)
    (isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU)
    (unitCanonicalMapUlift eU eR hsetU h𝒳)
    (isHomLift_unitCanonicalMapUlift_app eU eR hsetU h𝒳) hmor
  have hfull : (canonicalMapUlift eU eR hsetU h𝒳).Full :=
    Functor.Stackification.full_of_extension hG hH (BigFppfOver.topology B S hS)
      (Stack.isLocallyBijective_toQuotientStack (selfIntersectionGroupoid eU eR hsetU))
      (Stack.essImage_toQuotientStack (selfIntersectionGroupoid eU eR hsetU)) hFmor
      (fun T x y => (Stack.isStack_quotientStack
        (selfIntersectionGroupoid eU eR hsetU)).isMorSheaf T x y)
      (fun T x y => (isStack_stackUlift h𝒳).isMorSheaf T x y)
  have hfaith : (canonicalMapUlift eU eR hsetU h𝒳).Faithful :=
    Functor.Stackification.faithful_of_extension hG hH (BigFppfOver.topology B S hS)
      (Stack.isLocallyBijective_toQuotientStack (selfIntersectionGroupoid eU eR hsetU))
      (Stack.essImage_toQuotientStack (selfIntersectionGroupoid eU eR hsetU)) hFmor
      (fun T x y => (Stack.isStack_quotientStack
        (selfIntersectionGroupoid eU eR hsetU)).isMorSheaf T x y)
      (fun T x y => (isStack_stackUlift h𝒳).isMorSheaf T x y)
  have hdfaith : (BasedCategory.uliftDown 𝒳.val :
      (stackUlift 𝒳).obj ⥤ 𝒳.val.obj).Faithful :=
    ⟨fun {_ _} _ _ h => congrArg (BasedCategory.uliftUp 𝒳.val).map h⟩
  have hdfull : (BasedCategory.uliftDown 𝒳.val :
      (stackUlift 𝒳).obj ⥤ 𝒳.val.obj).Full :=
    ⟨fun {_ _} ψ => ⟨(BasedCategory.uliftUp 𝒳.val).map ψ, rfl⟩⟩
  have h1 : (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor.Full :=
    inferInstanceAs ((canonicalMapUlift eU eR hsetU h𝒳 ⋙ BasedCategory.uliftDown 𝒳.val).Full)
  have h2 : (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor.Faithful :=
    inferInstanceAs ((canonicalMapUlift eU eR hsetU h𝒳 ⋙ BasedCategory.uliftDown 𝒳.val).Faithful)
  exact ⟨Functor.FullyFaithful.ofFullyFaithful
    (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor⟩

/-- The morphism of the site that a morphism between the chosen representatives of two sections
of the object space lies over: its projection, composed with the identifications of the bases of
the representatives with the objects the sections are taken at. -/
noncomputable def targetHomBase {W V : BigFppfOver B S hS}
    (a : U.obj.obj (op W)) (b : U.obj.obj (op V))
    (φ : f.toFunctor.obj (representingObj eU a) ⟶ f.toFunctor.obj (representingObj eU b)) :
    W ⟶ V :=
  eqToHom (fObj_over (f := f) eU a).symm ≫ 𝒳.val.p.map φ ≫ eqToHom (fObj_over (f := f) eU b)

/-- A morphism between the chosen representatives lies over the morphism of the site
`AlgebraicGeometry.Stack.SelfIntersection.targetHomBase` attaches to it. -/
theorem isHomLift_targetHomBase {W V : BigFppfOver B S hS}
    (a : U.obj.obj (op W)) (b : U.obj.obj (op V))
    (φ : f.toFunctor.obj (representingObj eU a) ⟶ f.toFunctor.obj (representingObj eU b)) :
    𝒳.val.p.IsHomLift (targetHomBase eU a b φ) φ :=
  CategoryTheory.IsHomLift.of_fac' 𝒳.val.p _ φ
    (fObj_over (f := f) eU a) (fObj_over (f := f) eU b) (by simp [targetHomBase])

/-- Two morphisms of the pointwise groupoid fibration with the same image in `𝒳` have the same
base morphism. -/
theorem base_eq_of_toStackOfPointwiseGroupoidMap_eq (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u u' : X ⟶ Y)
    (h : toStackOfPointwiseGroupoidMap eU eR hsetU u =
      toStackOfPointwiseGroupoidMap eU eR hsetU u') : u.base = u'.base := by
  have h1 := isHomLift_toStackOfPointwiseGroupoidMap eU eR hsetU u
  have h2 := isHomLift_toStackOfPointwiseGroupoidMap eU eR hsetU u'
  rw [h] at h1
  have := h1
  have := h2
  exact (CategoryTheory.IsHomLift.fac 𝒳.val.p u.base
      (toStackOfPointwiseGroupoidMap eU eR hsetU u')).trans
    (CategoryTheory.IsHomLift.fac 𝒳.val.p u'.base
      (toStackOfPointwiseGroupoidMap eU eR hsetU u')).symm

/-- Two morphisms of the pointwise groupoid fibration with the same base morphism and the same
image in `𝒳` are equal. -/
theorem toStackOfPointwiseGroupoidMap_injective_of_base_eq (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u u' : X ⟶ Y) (hb : u.base = u'.base)
    (h : toStackOfPointwiseGroupoidMap eU eR hsetU u =
      toStackOfPointwiseGroupoidMap eU eR hsetU u') : u = u' := by
  obtain ⟨bu, φu⟩ := u
  obtain ⟨bu', φu'⟩ := u'
  simp only at hb
  subst hb
  have hc := isStronglyCartesian_fRestrict (f := f) eU bu Y.fiber
  have hvert : ∀ φ : X.fiber ⟶ U.obj.map bu.op Y.fiber,
      𝒳.val.p.IsHomLift (𝟙 X.base)
        (fiberHomIso eU X.fiber (U.obj.map bu.op Y.fiber)
          (pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φ⟩)).inv := by
    intro φ
    exact @CategoryTheory.IsHomLift.lift_id_inv _ _ _ _ 𝒳.val.p _ _ _ _
      (pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φ⟩).2
  have key : (fiberHomIso eU X.fiber (U.obj.map bu.op Y.fiber)
        (pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu⟩)).inv =
      (fiberHomIso eU X.fiber (U.obj.map bu.op Y.fiber)
        (pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu'⟩)).inv := by
    have := hvert φu
    have := hvert φu'
    exact CategoryTheory.Functor.IsStronglyCartesian.ext 𝒳.val.p bu
      (fRestrict (f := f) eU bu Y.fiber) (𝟙 X.base) h
  have hhom : Functor.Fiber.fiberInclusion.map
        (pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu⟩) =
      Functor.Fiber.fiberInclusion.map
        (pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu'⟩) := by
    rw [← fiberHomIso_hom eU X.fiber (U.obj.map bu.op Y.fiber), ← fiberHomIso_hom eU X.fiber
      (U.obj.map bu.op Y.fiber)]
    exact (Iso.inv_eq_inv _ _).1 key
  have hθ : pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu⟩ =
      pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu'⟩ :=
    Functor.Fiber.hom_ext hhom
  have hsec : pointwiseSection eU eR hsetU (X := X) (Y := Y) ⟨bu, φu⟩ =
      pointwiseSection eU eR hsetU (X := X) (Y := Y) ⟨bu, φu'⟩ := by
    rw [← arrowOfFiberHom_pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu⟩,
      ← arrowOfFiberHom_pointwiseFiberHom eU eR hsetU (X := X) (Y := Y) ⟨bu, φu'⟩, hθ]
  have : φu = φu' :=
    ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
      (op X.base) X.fiber (U.obj.map bu.op Y.fiber)).injective (Subtype.ext hsec)
  rw [this]

/-- **The 1-morphism from the pointwise groupoid fibration to `𝒳` is faithful.** -/
theorem faithful_toStackOfPointwiseGroupoid (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor.Faithful where
  map_injective {_ _} u u' h :=
    toStackOfPointwiseGroupoidMap_injective_of_base_eq eU eR hsetU u u'
      (base_eq_of_toStackOfPointwiseGroupoidMap_eq eU eR hsetU u u' h) h

/-- Every morphism of `𝒳` between the images of two objects of the pointwise groupoid fibration
is the image of a morphism of that fibration. -/
theorem exists_pointwiseHom_of_targetHom (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj}
    (φ : f.toFunctor.obj (representingObj eU X.fiber) ⟶
      f.toFunctor.obj (representingObj eU Y.fiber)) :
    ∃ u : X ⟶ Y, toStackOfPointwiseGroupoidMap eU eR hsetU u = φ := by
  set bs : X.base ⟶ Y.base := targetHomBase eU X.fiber Y.fiber φ with hbs
  have hφ : 𝒳.val.p.IsHomLift bs φ := isHomLift_targetHomBase eU X.fiber Y.fiber φ
  set c : U.obj.obj (op X.base) := U.obj.map bs.op Y.fiber with hc
  have hcart : 𝒳.val.p.IsStronglyCartesian bs (fRestrict (f := f) eU bs Y.fiber) :=
    isStronglyCartesian_fRestrict (f := f) eU bs Y.fiber
  set α : f.toFunctor.obj (representingObj eU X.fiber) ⟶
      f.toFunctor.obj (representingObj eU c) :=
    CategoryTheory.Functor.IsStronglyCartesian.map 𝒳.val.p bs
      (fRestrict (f := f) eU bs Y.fiber) (Category.id_comp bs).symm φ with hα
  have hfac : α ≫ fRestrict (f := f) eU bs Y.fiber = φ :=
    CategoryTheory.Functor.IsStronglyCartesian.fac 𝒳.val.p bs
      (fRestrict (f := f) eU bs Y.fiber) (Category.id_comp bs).symm φ
  have hαlift : 𝒳.val.p.IsHomLift (𝟙 X.base) α :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift 𝒳.val.p bs
      (fRestrict (f := f) eU bs Y.fiber) (Category.id_comp bs).symm φ
  set αfib : (Functor.Fiber.mk (fObj_over (f := f) eU X.fiber) : 𝒳.val.p.Fiber X.base) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU c) := ⟨α, hαlift⟩ with hαfib
  have := isGroupoid_targetFiber (𝒳 := 𝒳) X.base
  have : IsIso αfib := IsGroupoid.all_isIso αfib
  set θ := CategoryTheory.inv αfib with hθdef
  have hinv : (fiberHomIso eU X.fiber c θ).inv = α :=
    congrArg Functor.Fiber.fiberInclusion.map (IsIso.inv_inv (f := αfib))
  set r : R.obj.obj (op X.base) := arrowOfFiberHom eU eR X.fiber c θ with hr
  have hsrc : (relationSourceMap eU eR).app (op X.base) r = X.fiber :=
    relationSourceMap_arrowOfFiberHom eU eR X.fiber c θ
  have htgt : (relationTargetMap eU eR).app (op X.base) r = c :=
    relationTargetMap_arrowOfFiberHom eU eR X.fiber c θ
  set g : (show (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.Evaluation
        (op X.base) from X.fiber) ⟶ c :=
    ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
      (op X.base) X.fiber c).symm ⟨r, hsrc, htgt⟩ with hg
  refine ⟨⟨bs, g⟩, ?_⟩
  have hsec : arrowOfFiberHom eU eR X.fiber c θ =
      pointwiseSection eU eR hsetU (X := X) (Y := Y) ⟨bs, g⟩ :=
    (congrArg Subtype.val (Equiv.apply_symm_apply
      ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
        (op X.base) X.fiber c) ⟨r, hsrc, htgt⟩)).symm
  rw [toStackOfPointwiseGroupoidMap_eq eU eR hsetU (X := X) (Y := Y) ⟨bs, g⟩ c θ hsec
    (representingObjRestrict eU bs Y.fiber) (isHomLift_representingObjRestrict eU bs Y.fiber),
    hinv]
  exact hfac

/-- **The 1-morphism from the pointwise groupoid fibration to `𝒳` is full.** -/
theorem full_toStackOfPointwiseGroupoid (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor.Full where
  map_surjective {_ _} φ := exists_pointwiseHom_of_targetHom eU eR hsetU φ

/-- The universe lift `CategoryTheory.BasedCategory.uliftUp` of `𝒳` is faithful. -/
theorem faithful_uliftUp :
    (BasedCategory.uliftUp 𝒳.val : 𝒳.val.obj ⥤ (stackUlift 𝒳).obj).Faithful :=
  ⟨fun {_ _} _ _ h =>
    congrArg (BasedCategory.uliftDown 𝒳.val : (stackUlift 𝒳).obj ⥤ 𝒳.val.obj).map h⟩

/-- The universe lift `CategoryTheory.BasedCategory.uliftUp` of `𝒳` is full. -/
theorem full_uliftUp :
    (BasedCategory.uliftUp 𝒳.val : 𝒳.val.obj ⥤ (stackUlift 𝒳).obj).Full :=
  ⟨fun {_ _} ψ =>
    ⟨(BasedCategory.uliftDown 𝒳.val : (stackUlift 𝒳).obj ⥤ 𝒳.val.obj).map ψ, rfl⟩⟩

/-- **The 1-morphism from the pointwise groupoid fibration to the universe lift of `𝒳` is
faithful.** -/
theorem faithful_toStackUliftOfPointwise (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (toStackUliftOfPointwise eU eR hsetU).Faithful := by
  have := faithful_toStackOfPointwiseGroupoid eU eR hsetU
  have := faithful_uliftUp (𝒳 := 𝒳)
  change ((Stack.quotientPrestackEquivalence (selfIntersectionGroupoid eU eR hsetU)).inverse ⋙
    (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor ⋙
    BasedCategory.uliftUp 𝒳.val).Faithful
  infer_instance

/-- **The 1-morphism from the pointwise groupoid fibration to the universe lift of `𝒳` is
full.** -/
theorem full_toStackUliftOfPointwise (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (toStackUliftOfPointwise eU eR hsetU).Full := by
  have := full_toStackOfPointwiseGroupoid eU eR hsetU
  have := full_uliftUp (𝒳 := 𝒳)
  change ((Stack.quotientPrestackEquivalence (selfIntersectionGroupoid eU eR hsetU)).inverse ⋙
    (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor ⋙
    BasedCategory.uliftUp 𝒳.val).Full
  infer_instance

/-- Over every test object `T`, the map of morphism presheaves induced by the 1-morphism from the
pointwise groupoid fibration to the universe lift of `𝒳`, between any two objects of the fibre of
the quotient prestack over `T`, is an isomorphism of presheaves. -/
theorem isIso_morPresheafMap_toStackUliftOfPointwise (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    haveI : (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.IsFibered :=
        (Stack.isFiberedInGroupoids_quotientPrestack
          (selfIntersectionGroupoid eU eR hsetU)).isFibered
    haveI : (stackUlift 𝒳).p.IsFibered :=
        (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibered
      ∀ (T : BigFppfOver B S hS)
        (x y : (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.Fiber T),
        IsIso ((isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU).morPresheafMap x y) := by
  have := isFibered_quotientPrestack_p eU eR hsetU
  have := isFibered_stackUlift_p (𝒳 := 𝒳)
  have := full_toStackUliftOfPointwise eU eR hsetU
  have := faithful_toStackUliftOfPointwise eU eR hsetU
  intro T x y
  exact Comma.isIso_morPresheafMap_of_fullyFaithful
    (isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU) x y

/-- Over every test object `T`, the map of morphism presheaves induced by the 1-morphism from the
pointwise groupoid fibration to the universe lift of `𝒳`, between any two objects of the fibre of
the quotient prestack over `T`, is locally injective and locally surjective for the fppf
topology. -/
theorem isLocallyBijective_morPresheafMap_toStackUliftOfPointwise
    (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    haveI : (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.IsFibered :=
        (Stack.isFiberedInGroupoids_quotientPrestack
          (selfIntersectionGroupoid eU eR hsetU)).isFibered
    haveI : (stackUlift 𝒳).p.IsFibered :=
        (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibered
      ∀ (T : BigFppfOver B S hS)
        (x y : (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.Fiber T),
        Presheaf.IsLocallyInjective ((BigFppfOver.topology B S hS).over T)
            ((isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU).morPresheafMap x y) ∧
          Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over T)
            ((isFibredOneMorphism_toStackUliftOfPointwise eU eR hsetU).morPresheafMap x y) := by
  have := isFibered_quotientPrestack_p eU eR hsetU
  have := isFibered_stackUlift_p (𝒳 := 𝒳)
  intro T x y
  have := isIso_morPresheafMap_toStackUliftOfPointwise eU eR hsetU T x y
  exact ⟨inferInstance, inferInstance⟩

/-- The canonical morphism `f_can : [U/R] ⟶ 𝒳` of the presentation datum
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation` is fully faithful. -/
@[stacks 04T4 "part (6): full faithfulness"]
theorem nonempty_fullyFaithful_canonicalMap (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Nonempty ((selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor.FullyFaithful) :=
  nonempty_fullyFaithful_canonicalMap_of_morPresheafMap eU eR (isFiberedInSetoids_source eU) h𝒳
    (isLocallyBijective_morPresheafMap_toStackUliftOfPointwise eU eR
      (isFiberedInSetoids_source eU))

end AlgebraicGeometry.Stack.SelfIntersection

end
