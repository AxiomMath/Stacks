module

public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts

/-!
# A flat presentation of an algebraic stack is an equivalence

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, and let
`f : 𝒰 ⟶ 𝒳` be a 1-morphism out of a category fibred in groupoids represented by an algebraic
space `U`, whose self-intersection `𝒰 ×_𝒳 𝒰` is represented by an algebraic space `R`. These data
give a groupoid in algebraic spaces `R ⇉ U` and a canonical 1-morphism `f_can : [U/R] ⟶ 𝒳` out
of its quotient stack. If `f` is surjective, flat and locally of finite presentation, then `f_can`
is an equivalence.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.exists_fppfLocalFiberPreimage`: every object of a
  fibre of `𝒳` becomes isomorphic to one coming from `𝒰` along a single covering morphism of the
  big fppf site.
* `AlgebraicGeometry.Stack.SelfIntersection.locallyEssSurjOnFibers_canonicalMap`: the canonical
  1-morphism of the presentation datum is locally essentially surjective on fibres.
* `AlgebraicGeometry.Stack.SelfIntersection.nonempty_isEquivalenceOver_canonicalMap`: the
  canonical 1-morphism is an equivalence over the big fppf site.

## References

* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰 ⟶ 𝒳}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism into an algebraic stack whose source is representable by an
algebraic space, and suppose every algebraic space representing a base change of `f` along a
scheme-valued point of `𝒳` has surjective, flat and locally finitely presented structural
morphism. Then for every object `y` of the fibre of `𝒳` over a test object `V` there is a single
morphism `r : W ⟶ V` generating a covering sieve of the fppf topology such that `r^* y` is the
image of an object of the fibre of `𝒰` over `W`. -/
theorem exists_fppfLocalFiberPreimage
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hU : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hCover : ∀ (T : BigFppfOver B S hS)
        (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.obj)
        (_hy : y ⋙ 𝒳.val.p = Over.map T.hom)
        (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B T.left.1 T.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map T.hom) 𝒰.val.p 𝒳.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        let a := algebraicSpaceMap B S hS T
          ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)
        (Space.IsSurjective B S hS a.hom ∧ Space.IsFlat B S hS a.hom ∧
          Space.IsLocallyOfFinitePresentation B S hS a.hom)) :
    (letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ (V : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber V),
      ∃ (W : BigFppfOver B S hS) (r : W ⟶ V),
        Sieve.generate (Presieve.singleton r) ∈ BigFppfOver.topology B S hS V ∧
        ∃ z : 𝒰.val.p.Fiber W,
          Nonempty ((Fiber.mapOfComp 𝒰.val.p 𝒳.val.p
            (CatFiberedInGroupoids.homFunctor f)
            (CatFiberedInGroupoids.homFunctor_comp_p f) W).obj z ≅
              pullbackFiber 𝒳.val.p y r)) := by
  classical
  have hf_repr : IsRepresentableByAlgebraicSpaces B S hS f.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS h𝒳 hU f
  let pY := 𝒳.val.p
  let pU := 𝒰.val.p
  have : pY.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let G := CatFiberedInGroupoids.homFunctor f
  let J := BigFppfOver.topology B S hS
  let JY := pY.inheritedTopology J
  have hInherited : Functor.IsInheritedTopology pY J JY :=
    Functor.isInheritedTopology_inheritedTopology pY J
  intro V y
  rcases y with ⟨y, rfl⟩
  obtain ⟨x, a, ha⟩ := exists_fppfLocalLift B S hS f hf_repr hCover y
  let RY := Sieve.generate (Presieve.singleton a)
  have hRY : RY ∈ JY y := ha
  have hR : RY.functorPushforward pY ∈ J (pY.obj y) := by
    simpa [pY] using (Functor.IsInheritedTopology.mem_iff_functorPushforward
      𝒳.isFiberedInGroupoids hInherited RY).mp hRY
  have hR_eq : RY.functorPushforward pY = Sieve.generate (Presieve.singleton (pY.map a)) := by
    dsimp [RY]
    rw [← Sieve.generate_map_eq_functorPushforward]
    simp
  let hGbase := CatFiberedInGroupoids.homFunctor_comp_p f
  have hx : pU.obj x = pY.obj (G.obj x) := (Functor.congr_obj hGbase x).symm
  let z : pU.Fiber (pY.obj (G.obj x)) := Fiber.mk hx
  let yY : pY.Fiber (pY.obj y) := Fiber.mk rfl
  have haLift : pY.IsHomLift (pY.map a) a := Functor.IsHomLift.map (p := pY) a
  have haCart : pY.IsStronglyCartesian (pY.map a) a :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (pY.map a) a
  let e := Functor.fiberIsoOfCartesian (p := pY) (a := y)
    (z := pullbackFiber pY yY (pY.map a))
    (z' := (Fiber.mapOfComp pU pY G hGbase _).obj z)
    (pY.map a) (IsPreFibered.pullbackMap yY.2 (pY.map a)) a
    (IsPreFibered.pullbackMap.IsCartesian yY.2 (pY.map a))
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian pY (pY.map a) a)
  exact ⟨pY.obj (G.obj x), pY.map a, hR_eq ▸ hR, z, ⟨e.symm⟩⟩

/-- The canonical 1-morphism of the presentation datum `selfIntersectionPresentation eU eR h𝒳`
is locally essentially surjective on fibres, given that every object of a fibre of `𝒳` lifts to
`𝒰` after base change along a single covering morphism of the site. -/
theorem locallyEssSurjOnFibers_canonicalMap
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hloc : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (V : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber V),
        ∃ (W : BigFppfOver B S hS) (r : W ⟶ V),
          Sieve.generate (Presieve.singleton r) ∈ BigFppfOver.topology B S hS V ∧
          ∃ z : 𝒰.val.p.Fiber W,
            Nonempty ((Fiber.mapOfComp 𝒰.val.p 𝒳.val.p
              (CatFiberedInGroupoids.homFunctor f)
              (CatFiberedInGroupoids.homFunctor_comp_p f) W).obj z ≅
                pullbackFiber 𝒳.val.p y r)) :
    Functor.LocallyEssSurjOnFibers 𝒳.isFiberedInGroupoids.isFibered
      (selfIntersectionPresentation eU eR h𝒳).canonicalMap.w
      (BigFppfOver.topology B S hS) := by
  classical
  let P := selfIntersectionPresentation eU eR h𝒳
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hFmor := 𝒳.isFiberedInGroupoids.isFibredOneMorphism P.canonicalMap.w
  let pU := 𝒰.val.p
  let pX := 𝒳.val.p
  let pQ := (Stack.quotientStack P.groupoid).p
  let pObj := (Stack.fibredCategory B S hS P.groupoid.objects.obj).val.p
  let proj := Stack.quotientStackProjection P.groupoid
  let hSP := P.sourcePresentation.hom.w
  let hProj := proj.w
  let FF := P.canonicalMap.toFunctor
  have hF : pU.IsFibredOneMorphism pX (CatFiberedInGroupoids.homFunctor f) :=
    𝒳.isFiberedInGroupoids.isFibredOneMorphism (CatFiberedInGroupoids.homFunctor_comp_p f)
  intro V y
  obtain ⟨W, r, hr, z, ⟨eX⟩⟩ := hloc V y
  refine ⟨Sieve.generate (Presieve.singleton r), hr, ?_⟩
  rintro V' g ⟨W', k, r', hr', hk'⟩
  cases hr'
  have : pU.IsFibered := 𝒰.isFiberedInGroupoids.isFibered
  let zV := pullbackFiber pU z k
  let hSPobj := congrArg (fun G => G.obj zV.1) hSP
  let zObj : pObj.Fiber V' := Fiber.mk (hSPobj.trans zV.2)
  let hProjobj := congrArg (fun G => G.obj zObj.1) hProj
  let zQ : pQ.Fiber V' := Fiber.mk (hProjobj.trans zObj.2)
  let zH := (Fiber.mapOfComp pQ pX FF hFmor.comp_eq V').obj zQ
  let zF := (Functor.fiberFunctorOfCompEq
    (CatFiberedInGroupoids.homFunctor_comp_p f) V').obj zV
  let α := P.extends_f.1.app zV.1
  have : pX.IsHomLift (𝟙 (pU.obj zV.1)) α.hom := P.extends_f.2 zV.1
  have hα : pX.IsHomLift (𝟙 V') α.hom := by
    have hcomp : pX.IsHomLift
        (eqToHom zV.2.symm ≫ 𝟙 (pU.obj zV.1) ≫ eqToHom zV.2) α.hom := inferInstance
    simpa using hcomp
  let eExt : zH ≅ zF := Fiber.isoMk (p := pX) α hα
  let eBase := pullbackFiberIso eX k ≪≫ pullbackFiberCompIso y r k
  let eLift := (hF.mapPullbackFiberIso z k).symm ≪≫ eBase
  refine ⟨zQ, ⟨?_⟩⟩
  simpa [zQ, zObj, zH, zF, hk'] using (eExt ≪≫ eLift)

/-- Let `𝒳` be an algebraic stack over `S`, let `f : 𝒰 ⟶ 𝒳` be a 1-morphism whose
source is represented by an algebraic space `U` and whose self-intersection is represented by an
algebraic space `R`, and suppose that every algebraic space representing a base change of `f`
along a scheme-valued point of `𝒳` has surjective, flat and locally finitely presented structural
morphism. Then the canonical 1-morphism `f_can : [U/R] ⟶ 𝒳` of the presentation datum
`selfIntersectionPresentation eU eR h𝒳` is an equivalence over the big fppf site of `S`. -/
@[stacks 04WY "flat_presentation_equivalence"]
theorem nonempty_isEquivalenceOver_canonicalMap
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hCover : ∀ (T : BigFppfOver B S hS)
        (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.obj)
        (_hy : y ⋙ 𝒳.val.p = Over.map T.hom)
        (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B T.left.1 T.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map T.hom) 𝒰.val.p 𝒳.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        let a := algebraicSpaceMap B S hS T
          ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)
        (Space.IsSurjective B S hS a.hom ∧ Space.IsFlat B S hS a.hom ∧
          Space.IsLocallyOfFinitePresentation B S hS a.hom)) :
    Nonempty (Functor.IsEquivalenceOver
      (Stack.quotientStack (selfIntersectionPresentation eU eR h𝒳).groupoid).p
      𝒳.val.p
      (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor) := by
  classical
  let P := selfIntersectionPresentation eU eR h𝒳
  let J := BigFppfOver.topology B S hS
  have hFF : P.canonicalMap.toFunctor.FullyFaithful :=
    Classical.choice (nonempty_fullyFaithful_canonicalMap eU eR h𝒳)
  obtain ⟨h𝒳fiber, h𝒳stack, -, -⟩ := id h𝒳
  have : 𝒳.val.p.IsFibered := h𝒳fiber.isFibered
  have hFbase : P.canonicalMap.toFunctor ⋙ 𝒳.val.p =
      (Stack.quotientStack P.groupoid).p := P.canonicalMap.w
  have hFmor : (Stack.quotientStack P.groupoid).p.IsFibredOneMorphism
      𝒳.val.p P.canonicalMap.toFunctor := h𝒳fiber.isFibredOneMorphism hFbase
  have := hFF.full
  have := hFF.faithful
  have hLoc := locallyEssSurjOnFibers_canonicalMap eU eR h𝒳
    (exists_fppfLocalFiberPreimage h𝒳 ⟨U.obj, U.property, ⟨eU⟩⟩ hCover)
  have hess : ∀ V : BigFppfOver B S hS,
      (Fiber.mapOfComp (Stack.quotientStack P.groupoid).p 𝒳.val.p
        P.canonicalMap.toFunctor hFmor.comp_eq V).EssSurj := by
    intro V
    refine ⟨fun y => ?_⟩
    obtain ⟨RS, hRS, hRSess⟩ := hLoc V y
    exact Functor.exists_iso_of_locally_essImage hFmor
      (Stack.isStack_quotientStack P.groupoid).hasEffectiveDescent
      (h𝒳stack.1.isMorSheaf V) y hRS hRSess
  exact ⟨Functor.isEquivalenceOver_of_exists_vertical_iso hFbase
    (Functor.exists_vertical_iso_of_fiber_essSurj hFbase hess)⟩

end AlgebraicGeometry.Stack.SelfIntersection

end
