module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSliceFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitenessFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor

/-!
# The isomorphism sheaves of an algebraic stack are locally of finite type

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site, let `T` be an object of the
site and let `x`, `y` be two objects of the fibre of `𝒳` over `T`. The isomorphism sheaf
`Isom(x, y)` is an algebraic space over `T`, and its structural morphism to `T` is locally of
finite type.

## Main definitions

* `AlgebraicGeometry.Stack.liftedIsomPresheafIso`: the isomorphism sheaves of two objects of a
  fibre agree, after a universe lift, with those of their images under a fully faithful
  1-morphism of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_isomPresheaf_of_presentation`: the isomorphism
  sheaves of an algebraic stack have every fpqc-local étale-chart property that the arrow fibres
  of a presentation have.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_isomPresheaf`: the structural morphism of the
  isomorphism sheaf `Isom(x, y)` of two objects of an algebraic stack is locally of finite type.

## References

* [Stacks Project, Tag 041S](https://stacks.math.columbia.edu/tag/041S)
* [Stacks Project, Tag 0462](https://stacks.math.columbia.edu/tag/0462)
* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044W](https://stacks.math.columbia.edu/tag/044W)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe u w

/-! ### The isomorphism sheaves along a fully faithful 1-morphism, with a universe lift -/

section MorPresheafUlift

universe u₁ u₂ u₃ u₄ vb v v' v₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞]

/-- The morphism presheaf of two objects of a fibre of a category fibred in groupoids is
isomorphic to their isomorphism presheaf. -/
noncomputable def morPresheafIsoIsomPresheaf {𝒟 : Type u₄} [Category.{v₄} 𝒟]
    (q : 𝒟 ⥤ 𝒞) [q.IsFibered] (hq : q.IsFiberedInGroupoids) {U : 𝒞} (x y : q.Fiber U) :
    q.morPresheaf x y ≅ q.isomPresheaf x y := by
  have htop : q.isomSubpresheaf x y = ⊤ := by
    refine le_antisymm le_top fun V f _ => ?_
    have _ := hq.fiber_isGroupoid V.unop.left
    change IsIso f
    infer_instance
  have _ := (q.isomSubpresheaf x y).eq_top_iff_isIso.1 htop
  exact (asIso (q.isomSubpresheaf x y).ι).symm

variable {𝒳 : Type u₂} [Category.{v} 𝒳] {𝒮 : Type u₃} [Category.{max v v'} 𝒮]
  {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} [p.IsFibered] [r.IsFibered]

/-- The map of morphism presheaves induced by a 1-morphism of fibred categories `F`, from the
universe lift of the morphism presheaf of `a` and `b` to the morphism presheaf of their images. -/
noncomputable def liftedMorPresheafMap (hF : p.IsFibredOneMorphism r F)
    {U : 𝒞} (a b : p.Fiber U) :
    p.morPresheaf a b ⋙ uliftFunctor.{v'} ⟶
      r.morPresheaf ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a)
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj b) where
  app g := ↾fun m => (hF.mapPullbackFiberIso a g.unop.hom).hom ≫
    (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).map m.down ≫
    (hF.mapPullbackFiberIso b g.unop.hom).inv
  naturality := by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    exact hF.morRestrict_mapPullbackFiberIso_conj a b h m.down

/-- The map `liftedMorPresheafMap` of morphism presheaves of a fully faithful 1-morphism is an
isomorphism. -/
theorem isIso_liftedMorPresheafMap (hF : p.IsFibredOneMorphism r F)
    [F.Full] [F.Faithful] {U : 𝒞} (a b : p.Fiber U) :
    IsIso (liftedMorPresheafMap.{_, _, _, _, _, v'} hF a b) := by
  have happ : ∀ g, IsIso ((liftedMorPresheafMap.{_, _, _, _, _, v'} hF a b).app g) := by
    intro g
    rw [isIso_iff_bijective]
    have hfull : (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).Full :=
      Functor.Fiber.full_mapOfComp hF.comp_eq g.unop.left
    have hfaith : (Functor.fiberFunctorOfCompEq hF.comp_eq g.unop.left).Faithful :=
      Functor.Fiber.faithful_mapOfComp hF.comp_eq g.unop.left
    constructor
    · intro m m' hmm
      exact ULift.ext (hfaith.map_injective ((cancel_mono _).1 ((cancel_epi _).1 hmm)))
    · intro n
      obtain ⟨m, hm⟩ := hfull.map_surjective
        ((hF.mapPullbackFiberIso a g.unop.hom).inv ≫ n ≫
          (hF.mapPullbackFiberIso b g.unop.hom).hom)
      refine ⟨ULift.up m, ?_⟩
      show (hF.mapPullbackFiberIso a g.unop.hom).hom ≫ _ ≫ _ = n
      rw [hm]
      simp
  exact NatIso.isIso_of_isIso_app _

/-- **The isomorphism sheaves of two objects of a fibre agree with those of their images** under
a fully faithful 1-morphism of categories fibred in groupoids, after a universe lift. -/
noncomputable def liftedIsomPresheafIso (hF : p.IsFibredOneMorphism r F)
    [F.Full] [F.Faithful] (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    {U : 𝒞} (a b : p.Fiber U) :
    p.isomPresheaf a b ⋙ uliftFunctor.{v'} ≅
      r.isomPresheaf ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a)
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj b) :=
  have _ := isIso_liftedMorPresheafMap.{_, _, _, _, _, v'} hF a b
  Functor.isoWhiskerRight (morPresheafIsoIsomPresheaf p hp a b).symm uliftFunctor ≪≫
    asIso (liftedMorPresheafMap.{_, _, _, _, _, v'} hF a b) ≪≫
      morPresheafIsoIsomPresheaf r hr _ _

end MorPresheafUlift

/-! ### Descent of local finite type along an fppf covering of the base -/

/-- A property respecting isomorphisms that holds for the second projection of a pullback square
holds for the canonical second projection of the pullback. -/
private theorem pullback_snd_of_isPullback {C : Type*} [Category C] (P : MorphismProperty C)
    [P.RespectsIso] {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {fst : W ⟶ X}
    {snd : W ⟶ Y} (h : IsPullback fst snd f g) (hs : P snd) : P (pullback.snd f g) := by
  rw [← h.isoPullback_hom_snd] at hs
  exact (P.cancel_left_of_respectsIso _ _).mp hs

/-- **An étale-chart property of the structural morphism of an algebraic space descends along an
fppf covering of the base.** Let `Q` be local on the target for the fpqc topology when read on
étale charts, and let `k i : V i ⟶ Z` be an fppf covering of a terminal object `Z`. If the base
change of `F ⟶ yoneda Z` along each `yoneda (V i) ⟶ yoneda Z` has `Q` on every étale chart, then
so does the structural morphism of `F`. -/
theorem holdsOnEveryEtaleChart_terminal_of_fppfFamily
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        Space.HoldsOnEveryEtaleChart B S hS Q f.hom)
      (Space.Topology.precoverage.{u, u + 1} .fpqc B S hS)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {Idx : Type (u + 1)} (V : Idx → BigFppfOver B S hS)
    (Z : BigFppfOver B S hS) (hZ : IsTerminal Z) (k : ∀ i, V i ⟶ Z)
    (hcov : Space.IsFppfCovering B S hS (fun i => yoneda.obj (V i)) (fun i => yoneda.map (k i)))
    (hloc : ∀ i, Space.HoldsOnEveryEtaleChart B S hS Q
      (pullback.snd ((hZ.isTerminalObj yoneda Z).from F) (yoneda.map (k i)))) :
    Space.HoldsOnEveryEtaleChart B S hS Q (terminal.from F) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ f => Space.HoldsOnEveryEtaleChart B S hS Q f.hom
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩
  let X : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let f : X ⟶ Y := ObjectProperty.homMk ((hZ.isTerminalObj yoneda Z).from F)
  let Vi : Idx → AlgebraicSpaces B S hS :=
    fun i => ⟨yoneda.obj (V i), isAlgebraicSpace_yoneda B S hS (V i)⟩
  let g : ∀ i, Vi i ⟶ Y := fun i => ObjectProperty.homMk (yoneda.map (k i))
  have hR : Presieve.ofArrows Vi g ∈
      (Space.Topology.precoverage.{u, u + 1} .fpqc B S hS).coverings Y :=
    ⟨Idx, Vi, g, rfl, Y.property, (fun i => (Vi i).property),
      Space.isFpqcCovering_of_isFppfCovering B S hS _ _ hcov⟩
  have _ : P.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso B S hS _
  have hPf : P f := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR ?_
    rintro A q _ ⟨i⟩
    exact pullback_snd_of_isPullback P (AlgebraicSpaces.isPullback_fiberProduct B S hS f (g i))
      (hloc i)
  exact Space.holdsOnEveryEtaleChart_of_isTerminal B S hS
    (hZ.isTerminalObj yoneda Z) terminalIsTerminal _ _ hPf

/-! ### Étale-chart properties of isomorphism sheaves from a presentation -/

/-- **An étale-chart property of an isomorphism sheaf, local on the target for the fpqc topology,
may be checked fppf-locally on the test object.** If over the members `f : V ⟶ T` of a covering
sieve the restriction of `Isom(x, y)` is isomorphic to a presheaf whose structural morphism over
`V` has `Q` on every étale chart, then the structural morphism of `Isom(x, y)` over `T` has `Q` on
every étale chart. -/
theorem holdsOnEveryEtaleChart_isomPresheaf_of_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (Q : MorphismProperty Scheme.{u})
    [∀ T : BigFppfOver B S hS, MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B T.left.1 T.left.2⦄ (f : F ⟶ G) =>
        Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q f.hom)
      (Space.Topology.precoverage.{u, u + 1} .fpqc B T.left.1 T.left.2)]
    (T : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ x y : 𝒳.val.p.Fiber T,
      (∃ R ∈ BigFppfOver.topology B S hS T,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f →
          ∃ F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u,
            Space.HoldsOnEveryEtaleChart B V.left.1 V.left.2 Q (terminal.from F) ∧
              Nonempty (F ≅ (Over.iteratedSliceBackward V).op ⋙ (Over.map f).op ⋙
                𝒳.val.p.isomPresheaf x y)) →
      Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q
        (terminal.from ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf x y)) := by
  classical
  let _ : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨_hFib, _hStack, hDiag, _hAtlas⟩ := id h𝒳
  intro x y ⟨Rsieve, hRsieve, hlocal⟩
  obtain ⟨Fisom, hFisom, ⟨eIsom⟩⟩ :=
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp hDiag T x y
  set I := (Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf x y with hIdef
  have hI : IsAlgebraicSpace B T.left.1 T.left.2 I :=
    isAlgebraicSpace_of_iso B T.left.1 T.left.2
      (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso eIsom).symm hFisom
  obtain ⟨Idx, Wv, m, hmem, hflat, hlfp, hsurj⟩ := exists_family_of_mem_topology B S hS hRsieve
  let Z : BigFppfOver B T.left.1 T.left.2 := Over.mk (𝟙 (B.obj T.left.2))
  let Vi : Idx → BigFppfOver B T.left.1 T.left.2 := fun i => Over.mk (m i)
  let k : ∀ i, Vi i ⟶ Z := fun i => Over.homMk (m i)
  refine holdsOnEveryEtaleChart_terminal_of_fppfFamily B T.left.1 T.left.2 Q hI Vi Z
    Over.mkIdTerminal k
    (Space.isFppfCovering_yoneda_map B T.left.1 T.left.2 Vi k hflat hlfp
      hsurj) ?_
  intro i
  have hsq := OverShriek.isPullback_relocalizeRestrictCounit (m i) I
    (fun W => OverShriek.subsingleton_yoneda_obj_mkId W)
    ((Over.mkIdTerminal.isTerminalObj yoneda Z).from I) (yoneda.map (k i))
  let P : MorphismProperty ((BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u) :=
    fun _ _ q => Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q q
  have _ : P.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B T.left.1 T.left.2 Q
  refine pullback_snd_of_isPullback P hsq
    ((Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B (Wv i).1 T.left.1
    (Wv i).2 T.left.2 (m i) _ _).2 ?_)
  obtain ⟨Fi, hFiQ, ⟨eLocal⟩⟩ := hlocal (hmem i)
  let Vi' : BigFppfOver B S hS := Over.mk (m i ≫ T.hom)
  let gi : Vi' ⟶ T := Over.homMk (m i)
  let eFi : (OverShriek.relocalizeRestrict (m i)).obj I ≅ Fi :=
    OverShriek.relocalizeRestrictIteratedSliceIso gi (𝒳.val.p.isomPresheaf x y) ≪≫ eLocal.symm
  exact Space.holdsOnEveryEtaleChart_of_isTerminal B (Wv i).1 (Wv i).2 terminalIsTerminal
    (Over.mkIdTerminal.isTerminalObj yoneda _) _ _
    ((Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B (Wv i).1 (Wv i).2 Q eFi).mpr hFiQ)

/-- **The isomorphism sheaf of two objects of an algebraic stack has every étale-chart property,
local on the target for the fpqc topology, that the arrow fibres of a presentation have.** Let
`𝒳` be an algebraic stack presented by a groupoid `G`, `eQ : [U/R] ≃ 𝒳`, and let `Q` be a property
of morphisms of schemes, local on the target for the fpqc topology when read on étale charts, such
that the presheaf of arrows from `x'` to `y'` has `Q` on every étale chart for all points `x'`,
`y'` of the object space over a common test object which are equal whenever `x = y`. Then the
structural morphism of `Isom(x, y)`, read over `T`, has `Q` on every étale chart. -/
theorem holdsOnEveryEtaleChart_isomPresheaf_of_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    {Z₀ : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Z₀)
    (eQ : StacksRepresentableCFG.EquivalenceOver (quotientStack G).p 𝒳.val.p)
    (Q : MorphismProperty Scheme.{u})
    [∀ T : BigFppfOver B S hS, MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B T.left.1 T.left.2⦄ (f : F ⟶ G) =>
        Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q f.hom)
      (Space.Topology.precoverage.{u, u + 1} .fpqc B T.left.1 T.left.2)]
    (T : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ x y : 𝒳.val.p.Fiber T,
      (∀ (V : BigFppfOver B S hS) (x' y' : G.objects.obj.obj (Opposite.op V)),
        (x = y → x' = y') →
          Space.HoldsOnEveryEtaleChart B S hS Q
            (pullback.fst (prod.lift (yonedaEquiv.symm y') (yonedaEquiv.symm x'))
              (prod.lift G.target.hom G.source.hom))) →
      Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q
        (terminal.from ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf x y)) := by
  classical
  let _ : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  intro x y hQ
  have hLift : 𝒳.val.p.IsFibredOneMorphism (quotientStack G).p eQ.inv.functor :=
    { comp_eq := eQ.inv.w
      map_isStronglyCartesian := by
        intro A A' g a b k hk
        exact eQ.toEquivalence.symm.isStronglyCartesian_map_functor
          (quotientStack G).p eQ.inv.w g k hk }
  let _ : eQ.inv.functor.Full := eQ.toEquivalence.fullyFaithfulInverse.full
  let _ : eQ.inv.functor.Faithful := eQ.toEquivalence.fullyFaithfulInverse.faithful
  let lift := Functor.fiberFunctorOfCompEq hLift.comp_eq T
  let eC : 𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u + 1, u} ≅
      (quotientStack G).p.isomPresheaf (lift.obj x) (lift.obj y) :=
    liftedIsomPresheafIso hLift 𝒳.isFiberedInGroupoids
      (isFiberedInGroupoids_quotientStack G) x y
  obtain ⟨Rsieve, hRsieve, hlocal⟩ :=
    isomPresheaf_locallyHoldsOnEveryEtaleChart B S hS G Q T (lift.obj x) (lift.obj y)
      (fun V x' y' hxy => hQ V x' y' (fun h => hxy (by rw [h])))
  refine holdsOnEveryEtaleChart_isomPresheaf_of_local B S hS 𝒳 h𝒳 Q T x y
    ⟨Rsieve, hRsieve, fun V f hf => ?_⟩
  obtain ⟨Fi, -, hFiQ, ⟨ei⟩⟩ := hlocal hf
  let L := (Over.iteratedSliceBackward V).op ⋙ (Over.map f).op
  exact ⟨Fi, hFiQ, ⟨((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}).preimageIso
    (ei ≪≫ (Functor.isoWhiskerLeft L eC).symm)⟩⟩

/-! ### Local finite type of the isomorphism sheaves -/

/-- Let `𝒳` be an algebraic stack over `S`, let `T` be an object of the big fppf site of `S` and
let `x`, `y` be two objects of the fibre of `𝒳` over `T`. Then the structural morphism of the
isomorphism sheaf `Isom(x, y)`, read over `T`, is locally of finite type. -/
@[stacks 04XR]
theorem isLocallyOfFiniteType_isomPresheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (T : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ x y : 𝒳.val.p.Fiber T,
      Space.IsLocallyOfFiniteType B T.left.1 T.left.2
        (terminal.from ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf x y)) := by
  classical
  let _ : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨_hFib, _hStack, _hDiag, hAtlas⟩ := id h𝒳
  obtain ⟨U, fU, hfU, hprop⟩ := hAtlas
  intro x y
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS U
  let Uspace : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let eU : StacksRepresentableCFG.EquivalenceOver 𝒰.val.p
      (presheafOfCategories (Uspace.obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  let Fmor : 𝒰 ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom fU
  have hFmor : IsRepresentableByAlgebraicSpaces B S hS Fmor.hom := hfU
  obtain ⟨Rsp, hRsp, hER⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS 𝒰 𝒳 Fmor.hom h𝒳
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  let Rspace : AlgebraicSpaces B S hS := ⟨Rsp, hRsp⟩
  obtain ⟨eR⟩ : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳 Fmor.hom).val.p
      (presheafOfCategories (Rspace.obj ⋙ typeToCat)).p) := hER
  have hsmoothRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) Fmor hFmor :=
    fun V z hz F' hF' hE => (hprop V z hz F' hF' hE).2
  have hsourceLft : Space.IsLocallyOfFiniteType B S hS
      (SelfIntersection.selfIntersectionPresentation eU eR h𝒳).groupoid.source.hom :=
    Space.isLocallyOfFiniteType_of_isSmooth B S hS
      (SelfIntersection.isSmooth_selfIntersectionPresentation_source eU eR hFmor hsmoothRel h𝒳)
  obtain ⟨eQ, _heQ⟩ := SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
    eU eR h𝒳 hsmoothRel (fun V z hz F' hF' hE => (hprop V z hz F' hF' hE).1)
  exact holdsOnEveryEtaleChart_isomPresheaf_of_presentation B S hS 𝒳 h𝒳 _ eQ _ T x y
    (fun V x' y' _ => Space.isLocallyOfFiniteType_arrowFiber_fst B S hS _ hsourceLft V x' y')

end AlgebraicGeometry.Stack

end
