module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.DottedArrowsClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaAutomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme

/-!
# A reduced algebraic stack with quasi-compact inertia has a dense open substack with flat,
locally finitely presented inertia

Let `𝒳` be a reduced algebraic stack over a scheme `S` of a big fppf site whose inertia
projection `I_𝒳 ⟶ 𝒳` is quasi-compact. This file proves that there is a dense open substack
`𝒰 ⊆ 𝒳` whose inertia projection `I_𝒰 ⟶ 𝒰` is flat and locally of finite presentation. By
**Stacks 06QJ** such a `𝒰` is a gerbe, as asserted in **Stacks 06RC**.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_pullback_yonedaMap`: a property of
  morphisms of algebraic spaces which is local on the target for the fppf topology descends along
  a flat, locally finitely presented, surjective morphism of the site.
* `AlgebraicGeometry.Stack.exists_dense_openSubstack_isFlat_isLocallyOfFinitePresentation_inertia`:
  the dense open substack with flat, locally finitely presented inertia.

## References

* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
* [Stacks Project, Tag 06QS](https://stacks.math.columbia.edu/tag/06QS)
* [Stacks Project, Tag 06RC](https://stacks.math.columbia.edu/tag/06RC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property local on the target for the fppf topology descends along one flat, locally
finitely presented, surjective morphism of the site.** Let `Q` be a property of morphisms of
schemes whose every-étale-chart condition is local on the target for the fppf topology of
algebraic spaces over `S`. If a morphism `f : F ⟶ h_Z` from an algebraic space has `Q` after base
change along `h_m : h_{T₀} ⟶ h_Z` for a morphism `m` of the site whose underlying morphism of
schemes is flat, locally of finite presentation and surjective, then `f` has `Q`. -/
theorem holdsOnEveryEtaleChart_of_pullback_yonedaMap (Q : MorphismProperty Scheme.{u})
    [(Stack.spaceProperty B S hS (fun _ _ h => HoldsOnEveryEtaleChart B S hS Q h)).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, u} B S hS)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T₀ Z : BigFppfOver B S hS} (f : F ⟶ yoneda.obj Z) (m : T₀ ⟶ Z)
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map m))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map m))
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map m))
    (h : HoldsOnEveryEtaleChart B S hS Q (pullback.snd f (yoneda.map m))) :
    HoldsOnEveryEtaleChart B S hS Q f := by
  let P := Stack.spaceProperty B S hS (fun _ _ h => HoldsOnEveryEtaleChart B S hS Q h)
  let X : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩
  let Y₀ : AlgebraicSpaces B S hS := ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩
  let fA : X ⟶ Y := ObjectProperty.homMk f
  let gA : Y₀ ⟶ Y := ObjectProperty.homMk (yoneda.map m)
  have hcov : Topology.IsCovering .fppf B S hS (fun _ : PUnit.{u + 1} => Y₀.obj)
      (fun _ => gA.hom) := by
    refine ⟨Y.property, fun _ => Y₀.property, ?_⟩
    refine ⟨Y.property, fun _ => Y₀.property, fun _ => ?_, fun _ => ?_, ?_⟩
    · exact (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
        Flat.isEtaleLocalOnSourceAndTarget m).2 hflat
    · exact (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget m).2 hlfp
    · have hs : Function.Surjective (pointsMap B S hS (yoneda.obj T₀) (yoneda.map m)) :=
        (surjective_yonedaMap_iff_surjective_pointsMap B S hS m).1
          ((presheaf_yoneda_map_iff B S hS
            (inferInstance : MorphismProperty.IsStableUnderBaseChange
              (@Surjective.{u} : MorphismProperty Scheme.{u})) m).2 hsurj)
      exact Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨PUnit.unit, hs y⟩
  have hR : Presieve.ofArrows (fun _ : PUnit.{u + 1} => Y₀) (fun _ => gA) ∈
      (Topology.fppf.precoverage.{u, u} B S hS) Y :=
    ⟨PUnit.{u + 1}, fun _ => Y₀, fun _ => gA, rfl, hcov⟩
  change P fA
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hR ?_
  intro U g _ hg
  cases hg
  have hsq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback fA gA)
  change HoldsOnEveryEtaleChart B S hS Q (pullback.snd fA gA).hom
  rw [← hsq.isoPullback_hom_snd]
  let PU : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => HoldsOnEveryEtaleChart B S hS Q g
  have _ : PU.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS Q
  exact (PU.cancel_left_of_respectsIso hsq.isoPullback.hom _).2 h

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An automorphism space pulled back along a morphism into an open of the base inherits the
properties the automorphism space has over that open.** Let `x` be an object of `𝒳` over `U` and
let `W` be an open subspace of `U` (read on the site of `U`) over which the automorphism space
`Isom_𝒳(x, x) ⟶ U` has an étale-chart property `Q` stable under base change. If `m : x' ⟶ x` is a
cartesian morphism over `e : V ⟶ U` and `e` lands in `W`, then `Isom_𝒳(x', x') ⟶ V` has `Q`. -/
theorem holdsOnEveryEtaleChart_isomSpace_of_mem (Q : MorphismProperty Scheme.{u})
    (hQ : IsEtaleLocalOnSourceAndTarget Q) [Q.IsStableUnderBaseChange]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    {U V : BigFppfOver B S hS} (x : 𝒳.val.p.Fiber U)
    (W : Subfunctor (yoneda.obj (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2)))
    (hWsp : IsAlgebraicSpace B U.left.1 U.left.2 W.toFunctor)
    (hW : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
        (pullback.snd (OverShriek.toYonedaMkId (isomSpace B S hS 𝒳 U x x)) W.ι))
    (e : V ⟶ U)
    (he : (Over.homMk e.left : (Over.mk e.left : Over U.left) ⟶ Over.mk (𝟙 U.left)) ∈
      W.obj (Opposite.op (Over.mk e.left)))
    {x' : 𝒳.val.p.Fiber V} (m : x'.1 ⟶ x.1) (hm : 𝒳.val.p.IsStronglyCartesian e m) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B V.left.1 V.left.2 Q
      (terminal.from (isomSpace B S hS 𝒳 V x' x')) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let I := isomSpace B S hS 𝒳 U x x
  have hI : IsAlgebraicSpace B U.left.1 U.left.2 I := isAlgebraicSpace_isomSpace B S hS 𝒳 h𝒳 U x x
  let π : I ⟶ yoneda.obj (Over.mk (𝟙 U.left)) := OverShriek.toYonedaMkId I
  let k : (Over.mk e.left : Over U.left) ⟶ Over.mk (𝟙 U.left) := Over.homMk e.left
  refine (holdsOnEveryEtaleChart_isomSpace_iff_pullbackSnd B S hS Q 𝒳 e m hm
    (fun W => OverShriek.subsingleton_yoneda_obj_mkId W) π (yoneda.map k)).2 ?_
  let τ₀ : yoneda.obj (Over.mk e.left : Over U.left) ⟶ W.toFunctor := yonedaEquiv.symm ⟨k, he⟩
  have hτ : τ₀ ≫ W.ι = yoneda.map k := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    simp only [τ₀, yonedaEquiv_yoneda_map]
    rfl
  rw [← hτ]
  have hbig := IsPullback.of_hasPullback π (τ₀ ≫ W.ι)
  have hright := IsPullback.of_hasPullback π W.ι
  have hleft := IsPullback.of_right' hbig hright
  have hsnd : Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q (pullback.snd π W.ι) := hW
  have := Space.holdsOnEveryEtaleChart_isStableUnderBaseChange B U.left.1 U.left.2 Q hQ
  have hy := isAlgebraicSpace_yoneda B U.left.1 U.left.2
  let Wa : AlgebraicSpaces B U.left.1 U.left.2 := ⟨W.toFunctor, hWsp⟩
  let Ya : AlgebraicSpaces B U.left.1 U.left.2 := ⟨yoneda.obj (Over.mk e.left : Over U.left), hy _⟩
  let P₁ : AlgebraicSpaces B U.left.1 U.left.2 :=
    ⟨pullback π W.ι, isAlgebraicSpace_pullback B U.left.1 U.left.2 π W.ι hI hWsp (hy _)⟩
  let P₂ : AlgebraicSpaces B U.left.1 U.left.2 :=
    ⟨pullback π (τ₀ ≫ W.ι), isAlgebraicSpace_pullback B U.left.1 U.left.2 π _ hI (hy _) (hy _)⟩
  let sA : P₁ ⟶ Wa := ObjectProperty.homMk (pullback.snd π W.ι)
  let tA : Ya ⟶ Wa := ObjectProperty.homMk τ₀
  let lA : P₂ ⟶ P₁ := ObjectProperty.homMk (hright.lift (pullback.fst π (τ₀ ≫ W.ι))
    (pullback.snd π (τ₀ ≫ W.ι) ≫ τ₀) (by rw [hbig.w, Category.assoc]))
  let s'A : P₂ ⟶ Ya := ObjectProperty.homMk (pullback.snd π (τ₀ ≫ W.ι))
  have hsqA : IsPullback lA s'A sA tA :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hleft.w) hleft
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B U.left.1 U.left.2⦄ (k : F ⟶ G) =>
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q k.hom) hsqA hsnd

/-- The base changes of a smooth surjective 1-morphism of algebraic stacks from an algebraic
space are surjective, flat and locally of finite presentation. -/
theorem relative_surjective_flat_lfp_of_isSmooth {𝒲 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒲 ⟶ 𝒴) (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hSurj : IsSurjective B S hS g) (hSm : AlgebraicStacks.IsSmooth B S hS g) :
    ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.val.obj)
      (_hyv : yv ⋙ 𝒴.val.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.val.p 𝒴.val.val.p yv
          (CatFiberedInGroupoids.homFunctor g.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h) := by
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hlfpLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  intro U y hy F hF he
  exact ⟨(pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hg).1
      hSurj U y hy F hF he,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒲.property 𝒴.property
      g.hom hg).1 (AlgebraicStacks.isFlat_of_isSmooth B S hS g hSm) U y hy F hF he,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒲.property 𝒴.property g.hom hg).1
        ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
          𝒲.property 𝒴.property g.hom).1
          (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS g hSm))
        U y hy F hF he⟩

/-- **The automorphism spaces of an open image substack, from the chart.** Let `f : U ⟶ 𝒳` be a
smooth surjective 1-morphism from the stack of a scheme `U`, let `x₀` be its value at the terminal
object, and let `W` be an open subspace of `U` over which `Isom_𝒳(x₀, x₀)` has an étale-chart
property `Q` which is stable under base change and local on the target for the fppf topology.
Then every object of the open substack covered by `W ⟶ U ⟶ 𝒳` has automorphism space with `Q`. -/
theorem holdsOnEveryEtaleChart_isomSpace_openImageSubstack (Q : MorphismProperty Scheme.{u})
    (hQ : IsEtaleLocalOnSourceAndTarget Q) [Q.IsStableUnderBaseChange]
    (hQloc : ∀ (T : BigFppfOver B S hS), (spaceProperty B T.left.1 T.left.2
      (fun _ _ h => Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q h)).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B T.left.1 T.left.2))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {U : BigFppfOver B S hS}
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (W : Subfunctor (yoneda.obj (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2)))
    (hWo : Space.IsOpenSubspace B U.left.1 U.left.2 W)
    (hWsp : IsAlgebraicSpace B U.left.1 U.left.2 W.toFunctor)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
    (hyf : y = Over.iteratedSliceBackward U ⋙ CatFiberedInGroupoids.homFunctor f.hom)
    (hW : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
        (pullback.snd (OverShriek.toYonedaMkId (isomSpace B S hS 𝒳.val U
          (Functor.sliceValue 𝒳.val.val.p U y hy) (Functor.sliceValue 𝒳.val.val.p U y hy))) W.ι))
    (hg : AlgebraicStacks.IsSmooth B S hS
      (schemeStackMap.{u, w} B S hS (Space.openSiteObjectHom B S hS U
        (Space.opensOfOpenSubspace B U.left.1 U.left.2 _ W hWo)) ≫ f))
    (T : BigFppfOver B S hS)
    (η : (openImageSubstack B S hS _ hg).toAlgebraicStack.val.val.p.Fiber T) :
    letI : (openImageSubstack B S hS _ hg).toAlgebraicStack.val.val.p.IsFibered :=
      (openImageSubstack B S hS _ hg).toAlgebraicStack.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q
      (terminal.from (isomSpace B S hS (openImageSubstack B S hS _ hg).toAlgebraicStack.val T
        η η)) := by
  subst hyf
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let 𝒰 := openImageSubstack B S hS _ hg
  let : 𝒰.toAlgebraicStack.val.val.p.IsFibered :=
    𝒰.toAlgebraicStack.val.isFiberedInGroupoids.isFibered
  let p := 𝒳.val.val.p
  let Wo := Space.opensOfOpenSubspace B U.left.1 U.left.2 _ W hWo
  let W' := Space.openSiteObject B S hS U Wo
  let ι := Space.openSiteObjectHom B S hS U Wo
  let g : schemeStack.{u, w} B S hS W' ⟶ 𝒳 := schemeStackMap.{u, w} B S hS ι ≫ f
  let b := openImageFactorization B S hS g hg
  have hbsm : AlgebraicStacks.IsSmooth B S hS b :=
    isSmooth_openImageFactorization B S hS g hg
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W')
  have hbsurj : IsSurjective B S hS b := isSurjective_openImageFactorization B S hS g hg
  have hbrep : IsRepresentableByAlgebraicSpaces B S hS b.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒰.toAlgebraicStack.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W') b.hom
  obtain ⟨T', m, hmflat, hmlfp, hmsurj, z, φ, hφ⟩ :=
    exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS b.hom hbrep
      (relative_surjective_flat_lfp_of_isSmooth B S hS b hbrep hbsurj hbsm) T η
  refine (holdsOnEveryEtaleChart_isomSpace_fullSubcategory_iff B S hS Q 𝒳 𝒰.property
    𝒰.isAlgebraic T η).2 ?_
  let η' : p.Fiber T := ⟨η.1.obj, η.2⟩
  let F := isomSpace B S hS 𝒳.val T η' η'
  have hF : IsAlgebraicSpace B T.left.1 T.left.2 F :=
    isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property T η' η'
  let V : BigFppfOver B S hS := Over.mk (m ≫ T.hom)
  let k : V ⟶ T := Over.homMk m rfl
  have hφ' : p.IsHomLift k φ.hom :=
    Functor.isHomLift_map_of_comp_eq (p := 𝒰.toAlgebraicStack.val.val.p)
      (fullSubcategoryInclusion 𝒳 𝒰.property 𝒰.isAlgebraic).hom.hom.w k φ
  let x' : p.Fiber V := ⟨((CatFiberedInGroupoids.homFunctor b.hom).obj z).obj,
    IsHomLift.domain_eq p k φ.hom⟩
  have hmη : p.IsStronglyCartesian k φ.hom :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift k φ.hom
  let T₀ : BigFppfOver B T.left.1 T.left.2 := Over.mk m
  let m₀ : T₀ ⟶ Over.mk (𝟙 T.left) := Over.homMk m
  have := hQloc T
  have hdesc : Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q
      (OverShriek.toYonedaMkId F) := by
    refine Space.holdsOnEveryEtaleChart_of_pullback_yonedaMap B T.left.1 T.left.2 Q hF
      (OverShriek.toYonedaMkId F) m₀ hmflat hmlfp hmsurj ?_
    refine (holdsOnEveryEtaleChart_isomSpace_iff_pullbackSnd B S hS Q 𝒳.val (x := η') (x' := x')
      k φ.hom hmη
      (fun W => OverShriek.subsingleton_yoneda_obj_mkId W) (OverShriek.toYonedaMkId F)
      (yoneda.map m₀)).1 ?_
    let A := (Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left))
    have hzA : (z.hom ≫ ι).left ≫ A.left.hom = z.left.hom := by
      dsimp [A, Over.iteratedSliceBackward]
      rw [Category.id_comp, Category.assoc, Over.w ι, Over.w z.hom]
    let μ₀ : z.left ⟶ A.left := Over.homMk (z.hom ≫ ι).left hzA
    let μ : (Over.map ι).obj z ⟶ A := Over.homMk μ₀ (by
      apply Over.OverMorphism.ext
      dsimp [μ₀, A, Over.iteratedSliceBackward]
      rfl)
    let m₁ : x'.1 ⟶ (Functor.sliceValue p U _ hy).1 :=
      (CatFiberedInGroupoids.homFunctor f.hom).map μ
    have hμ : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift μ₀ μ :=
      IsHomLift.map (p := (schemeStack.{u, w} B S hS U).val.val.p) μ
    have hm₁ : p.IsHomLift μ₀ m₁ :=
      Functor.isHomLift_map_of_comp_eq (p := (schemeStack.{u, w} B S hS U).val.val.p)
        f.hom.hom.w μ₀ μ
    have h₁ : V = z.left :=
      x'.2.symm.trans (Functor.congr_obj f.hom.hom.w ((Over.map ι).obj z))
    have h₂ : A.left = U := (IsHomLift.codomain_eq p μ₀ m₁).symm.trans
      (Functor.sliceValue p U _ hy).2
    let e₁ : V ⟶ U := eqToHom h₁ ≫ μ₀ ≫ eqToHom h₂
    have he₁ : p.IsHomLift e₁ m₁ := by
      simp only [e₁]
      infer_instance
    have hm₁c : p.IsStronglyCartesian e₁ m₁ :=
      𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift e₁ m₁
    refine holdsOnEveryEtaleChart_isomSpace_of_mem B S hS Q hQ 𝒳.val 𝒳.property
      (Functor.sliceValue p U _ hy) W hWsp hW e₁ ?_ m₁ hm₁c
    refine (Space.mem_iff_of_isOpenSubspace B U.left.1 U.left.2 _ W hWo _).2 fun t => ?_
    have hι : ∀ t', ((BigFppfOver.toScheme B S hS).map ι) t' ∈ Wo := by
      intro t'
      rw [Space.map_openSiteObjectHom]
      exact t'.2
    have hμl : μ₀.left = z.hom.left ≫ ι.left := rfl
    change (B.inclusion.map e₁.left) t ∈ Wo
    simp only [e₁, Over.comp_left, Functor.map_comp, hμl,
      Scheme.Hom.comp_apply]
    exact hι _
  exact Space.holdsOnEveryEtaleChart_of_isTerminal B T.left.1 T.left.2
    (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _ hdesc

attribute [local instance] Space.pointTopology in
/-- **A reduced algebraic stack whose automorphism spaces are quasi-compact has a dense open
substack with flat, locally finitely presented inertia.** Here quasi-compactness is assumed of
the automorphism spaces at the scheme-valued points. -/
theorem exists_dense_openSubstack_isFlat_isLocallyOfFinitePresentation_inertia_of_isomSpace
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (hred : IsReducedStack B S hS 𝒳)
    (hqc : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
        (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
        Space.IsQuasiCompact B U.left.1 U.left.2
          (terminal.from (isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
            (Functor.sliceValue 𝒳.val.val.p U y hy)))) :
    ∃ 𝒰 : OpenSubstack 𝒳, @Dense _ (pointTopology B S hS 𝒳.val) (𝒰.pointSet B S hS) ∧
      AlgebraicStacks.IsFlat B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒰.toAlgebraicStack) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒰.toAlgebraicStack) := by
  obtain ⟨U, f, hfsurj, hfsm, hUred⟩ := hred
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let p := 𝒳.val.val.p
  let y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj :=
    Over.iteratedSliceBackward U ⋙ CatFiberedInGroupoids.homFunctor f.hom
  have hy : y ⋙ p = Over.map U.hom := by
    calc
      _ = Over.iteratedSliceBackward U ⋙ (CatFiberedInGroupoids.homFunctor f.hom ⋙ p) :=
        Functor.assoc _ _ _
      _ = Over.iteratedSliceBackward U ⋙ (schemeStack.{u, w} B S hS U).val.val.p :=
        congrArg (fun F => Over.iteratedSliceBackward U ⋙ F) f.hom.hom.w
      _ = Over.map U.hom := Over.iteratedSliceBackward_forget U
  let x₀ := Functor.sliceValue p U y hy
  let G := isomSpace B S hS 𝒳.val U x₀ x₀
  have hG : IsAlgebraicSpace B U.left.1 U.left.2 G :=
    isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property U x₀ x₀
  let π : G ⟶ yoneda.obj (Over.mk (𝟙 U.left)) := OverShriek.toYonedaMkId G
  have hπ : Space.IsFiniteType B U.left.1 U.left.2 π := by
    refine ⟨Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2 terminalIsTerminal
      (Over.mkIdTerminal.isTerminalObj yoneda _) _ _
      (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳.val 𝒳.property U x₀ x₀), ?_⟩
    have hisoU : (Space.quasiCompactPresheafProperty B U.left.1 U.left.2).RespectsIso :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    let t : ⊤_ _ ≅ yoneda.obj (Over.mk (𝟙 U.left)) :=
      terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal.isTerminalObj yoneda _)
    rw [show π = terminal.from G ≫ t.hom from
      (Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _]
    exact (MorphismProperty.cancel_right_of_respectsIso
      (Space.quasiCompactPresheafProperty B U.left.1 U.left.2) _ t.hom).2 (hqc U y hy)
  have : IsReduced ((BigFppfOver.toScheme B U.left.1 U.left.2).obj (Over.mk (𝟙 U.left))) :=
    hUred
  obtain ⟨W, hWd, hWflat, hWlfp, -, -⟩ :=
    Space.exists_dense_open_genericFlatness_of_isScheme B U.left.1 U.left.2 hG
      (Over.mk (𝟙 U.left)) π hπ (Space.unitModule B U.left.1 U.left.2 hG)
      (Space.isQuasicoherentOnCharts_unitModule B U.left.1 U.left.2 hG)
      (Space.isFiniteTypeOnCharts_unitModule B U.left.1 U.left.2 hG)
  have hWo : Space.IsOpenSubspace B U.left.1 U.left.2 W := hWd.1
  let Wo := Space.opensOfOpenSubspace B U.left.1 U.left.2 _ W hWo
  let ι := Space.openSiteObjectHom B S hS U Wo
  have hιsm : Smooth ((BigFppfOver.toScheme B S hS).map ι) := by
    rw [Space.map_openSiteObjectHom]
    exact inferInstanceAs (Smooth Wo.ι)
  have hg : AlgebraicStacks.IsSmooth B S hS (schemeStackMap.{u, w} B S hS ι ≫ f) :=
    AlgebraicStacks.isSmooth_comp B S hS _ f (isSmooth_schemeStackMap.{u, w} B S hS ι hιsm) hfsm
  refine ⟨openImageSubstack B S hS _ hg, ?_, ?_, ?_⟩
  · let := pointTopology B S hS 𝒳.val
    let := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
    rw [openImageSubstack_pointSet, AlgebraicStacks.pointsMap_comp, Set.range_comp]
    have hWo_dense : Dense (Wo : Set ((BigFppfOver.toScheme B U.left.1 U.left.2).obj
        (Over.mk (𝟙 U.left)))) := by
      change Dense (Space.pointsToScheme B U.left.1 U.left.2 (Over.mk (𝟙 U.left)) ''
        Set.range (Space.pointsMap B U.left.1 U.left.2 W.toFunctor W.ι))
      exact DenseRange.dense_image
        (Space.schemePointsHomeomorph B U.left.1 U.left.2
          (Over.mk (𝟙 U.left))).surjective.denseRange
        (Space.schemePointsHomeomorph B U.left.1 U.left.2 (Over.mk (𝟙 U.left))).continuous hWd.2
    have hι : DenseRange ((BigFppfOver.toScheme B S hS).map ι).base := by
      rw [Space.map_openSiteObjectHom]
      change Dense (Set.range Wo.ι)
      rw [Scheme.Opens.range_ι]
      exact hWo_dense
    exact DenseRange.dense_image hfsurj.denseRange
      (continuous_pointsMap B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom)
      (dense_range_pointsMap_schemeStackMap.{u, w} B S hS ι hι)
  · exact (isFlat_inertiaProjection_iff_isomSpace B S hS _).2 fun T η =>
      holdsOnEveryEtaleChart_isomSpace_openImageSubstack B S hS (@Flat.{u})
        Flat.isEtaleLocalOnSourceAndTarget
        (fun T => Space.isFlat_isLocalAtTarget_fppf B T.left.1 T.left.2) 𝒳 f W hWo hWd.1.1 y hy
        rfl hWflat hg T η
  · exact (isLocallyOfFinitePresentation_inertiaProjection_iff_isomSpace B S hS _).2
      fun T η => holdsOnEveryEtaleChart_isomSpace_openImageSubstack B S hS
        (@LocallyOfFinitePresentation.{u}) LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
        (fun T => Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B T.left.1 T.left.2)
        𝒳 f W hWo hWd.1.1 y hy rfl hWlfp hg T η

/-- **A reduced algebraic stack with quasi-compact inertia has a dense open substack with flat,
locally finitely presented inertia.** There is an open substack `𝒰` of `𝒳`, dense in `|𝒳|`,
whose inertia projection `I_𝒰 ⟶ 𝒰` is flat and locally of finite presentation. -/
theorem exists_dense_openSubstack_isFlat_isLocallyOfFinitePresentation_inertia
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (hred : IsReducedStack B S hS 𝒳)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    ∃ 𝒰 : OpenSubstack 𝒳, @Dense _ (pointTopology B S hS 𝒳.val) (𝒰.pointSet B S hS) ∧
      AlgebraicStacks.IsFlat B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒰.toAlgebraicStack) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒰.toAlgebraicStack) :=
  exists_dense_openSubstack_isFlat_isLocallyOfFinitePresentation_inertia_of_isomSpace B S hS 𝒳 hred
    (isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection B S hS 𝒳 hqc)

end AlgebraicGeometry.Stack

end
