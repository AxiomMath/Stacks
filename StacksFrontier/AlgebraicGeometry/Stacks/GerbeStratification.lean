module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeInertiaCharacterization
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsLocallyQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiCompactInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningReduction
public import StacksFrontier.Topology.WellOrderedStratification

/-!
# Stratifications of an algebraic stack by gerbes (Stacks 06RF)

**Stacks 06RF**: let `𝒳` be an algebraic stack over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is
quasi-compact. Then there are a well-ordered index set `I` and for every `i ∈ I` a reduced locally
closed substack `𝒰ᵢ ⊆ 𝒳` such that

1. each `𝒰ᵢ` is a gerbe,
2. `|𝒳| = ⋃ᵢ |𝒰ᵢ|`,
3. `Tᵢ = |𝒳| \ ⋃_{i' < i} |𝒰ᵢ'|` is closed in `|𝒳|` for every `i`, and
4. `|𝒰ᵢ|` is open in `Tᵢ`;

moreover either (a) `|𝒰ᵢ| ⊆ Tᵢ` is dense, or (b) `𝒰ᵢ` is quasi-compact, and in case (a), with
`𝒰ᵢ` chosen as large as possible, the stratification is canonical.

## The proof

For a nonempty closed set `T ⊆ |𝒳|` let `𝒳'` be the reduced closed substack with `|𝒳'| = T`
(Stacks 0509). Its automorphism spaces are those of `𝒳`, so they are quasi-compact, and Stacks
06RC gives a dense open substack of `𝒳'` which is a gerbe. In case (a) the stratum over `T` is the
union of all open substacks of `𝒳'` which are gerbes (a gerbe, `isGerbe_iUnion`), in case (b) a
nonempty quasi-compact open substack of the dense one (Stacks 04Y9); either is carried to a reduced
locally closed substack of `𝒳` by the immersion `𝒳' ⟶ 𝒳` (Stacks 0506,
`exists_locallyClosedSubstack_of_isImmersion`). The transfinite recursion is
`TopologicalSpace.exists_wellOrdered_stratification`, and the canonicity of case (a) is
`TopologicalSpace.stratification_unique`.

Stacks 06RC, and so this theorem, rests on Stacks 06QJ (2) `⟹` (1), proved from the bootstrap
theorem Stacks 04S6 part (3).

## Main results

* `AlgebraicGeometry.Stack.exists_gerbe_stratification`: Stacks 06RF, with the stratifications
  (a), whose strata are as large as possible, and (b).
* `AlgebraicGeometry.Stack.exists_gerbe_stratification_unique`: the stratification (a) is
  canonical.
* `AlgebraicGeometry.Stack.isReducedStack_openSubstack`: an open substack of a reduced algebraic
  stack is reduced.
* `AlgebraicGeometry.Stack.isGerbe_iUnion`, `AlgebraicGeometry.Stack.isGerbe_openSubstack_of_le`:
  unions of open gerbes, and open substacks of gerbes, are gerbes.

## References

* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 04Y9](https://stacks.math.columbia.edu/tag/04Y9)
* [Stacks Project, Tag 05UQ](https://stacks.math.columbia.edu/tag/05UQ)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
* [Stacks Project, Tag 06RC](https://stacks.math.columbia.edu/tag/06RC)
* [Stacks Project, Tag 06RF](https://stacks.math.columbia.edu/tag/06RF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open substack of a reduced algebraic stack is reduced.** Let `f : V ⟶ 𝒳` be a smooth
surjective atlas by a reduced scheme. The open subscheme of `V` lying over the points of an open
substack `𝒪` is reduced, and its composite with `f` is smooth with image `|𝒪|`; so its
factorization through `𝒪` (`AlgebraicGeometry.Stack.openImageFactorization`) is a reduced smooth
surjective atlas of `𝒪`. -/
theorem isReducedStack_openSubstack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hred : IsReducedStack B S hS 𝒳) (𝒪 : OpenSubstack 𝒳) :
    IsReducedStack B S hS 𝒪.toAlgebraicStack := by
  obtain ⟨V, f, hfs, hfsm, hVred⟩ := hred
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS (schemeFibredCategory B S hS V)
  let e := pointsHomeomorphScheme B S hS V
  let A := AlgebraicStacks.pointsMap B S hS f ⁻¹' 𝒪.pointSet B S hS
  have hA : IsOpen A := (OpenSubstack.isOpen_pointSet B S hS 𝒪).preimage
    (continuous_pointsMap B S hS (schemeStack.{u, w} B S hS V).val 𝒳.val f.hom.hom)
  let Wo : ((BigFppfOver.toScheme B S hS).obj V).Opens :=
    ⟨e.symm ⁻¹' A, hA.preimage e.symm.continuous⟩
  let ι := Space.openSiteObjectHom B S hS V Wo
  have hιsm : Smooth ((BigFppfOver.toScheme B S hS).map ι) := by
    have h : Smooth Wo.ι := inferInstance
    rw [Space.map_openSiteObjectHom]
    exact h
  have hg : AlgebraicStacks.IsSmooth B S hS (schemeStackMap.{u, w} B S hS ι ≫ f) :=
    AlgebraicStacks.isSmooth_comp B S hS _ f (isSmooth_schemeStackMap.{u, w} B S hS ι hιsm) hfsm
  -- The image of the restricted atlas is `|𝒪|`.
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ι ≫ f)) =
      𝒪.pointSet B S hS := by
    let := pointTopology B S hS (schemeFibredCategory B S hS (Space.openSiteObject B S hS V Wo))
    have hfun : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ι) =
        e.symm ∘ (((BigFppfOver.toScheme B S hS).map ι).base ∘
          (pointsHomeomorphScheme B S hS (Space.openSiteObject B S hS V Wo))) := by
      refine funext fun z => e.injective ?_
      rw [Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
      exact pointsHomeomorphScheme_naturality B S hS ι z
    have hι : Set.range (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ι)) =
        A := by
      rw [hfun, Set.range_comp, Set.range_comp,
        (pointsHomeomorphScheme B S hS (Space.openSiteObject B S hS V Wo)).surjective.range_eq,
        Set.image_univ, Space.map_openSiteObjectHom]
      show e.symm '' Set.range Wo.ι = A
      rw [Scheme.Opens.range_ι]
      exact e.symm.image_preimage A
    rw [AlgebraicStacks.pointsMap_comp, Set.range_comp, hι]
    exact Set.image_preimage_eq _ hfs
  have hO : 𝒪 = openImageSubstack B S hS _ hg := by
    refine (OpenSubstack.ofIsOpen_pointSet B S hS 𝒪).symm.trans ?_
    unfold openImageSubstack
    congr 1
    exact hrange.symm
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι) := by
    have h : AlgebraicGeometry.IsOpenImmersion Wo.ι := inferInstance
    rw [Space.map_openSiteObjectHom]
    exact h
  rw [hO]
  exact ⟨_, openImageFactorization B S hS _ hg, isSurjective_openImageFactorization B S hS _ hg,
    isSmooth_openImageFactorization B S hS _ hg
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _),
    isReduced_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map ι)⟩

/-- **Being a gerbe travels along an equivalence over the site.** -/
theorem AlgebraicStacks.isGerbe_of_equivalenceOver {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳'.val.val.p 𝒳.val.val.p)
    (h : AlgebraicStacks.IsGerbe B S hS 𝒳) : AlgebraicStacks.IsGerbe B S hS 𝒳' := by
  obtain ⟨𝒴, h𝒴, g, hg⟩ := h
  let F : 𝒳'.val.val ⥤ᵇ 𝒴.val.val := BasedFunctor.comp ⟨e.hom.functor, e.hom.w⟩ g.hom.hom
  refine ⟨𝒴, h𝒴, Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom F), ?_⟩
  show CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) 𝒴.val.val.p
    (e.hom.functor ⋙ CatFiberedInGroupoids.homFunctor g.hom)
  refine CategoryTheory.IsGerbeOver.comp ?_ hg
  exact (congrArg (fun q => CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) q
    e.hom.functor) g.hom.hom.w).mpr
      (CategoryTheory.IsGerbeOver.of_equivalenceOver 𝒳.val.isFiberedInGroupoids e)

/-- **The locally closed substack cut out by an immersion from a reduced gerbe.** If
`j : 𝒲 ⟶ 𝒳` is an immersion and `𝒲` is reduced and a gerbe, the essential image of `j` is a
reduced locally closed substack of `𝒳` which is a gerbe, with the same points as `𝒲`, and
quasi-compact when `𝒲` is (Stacks 0506). -/
theorem exists_locallyClosedSubstack_of_isImmersion {𝒲 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (j : 𝒲 ⟶ 𝒳) (hj : AlgebraicStacks.IsImmersion B S hS j)
    (hred : IsReducedStack B S hS 𝒲) (hg : AlgebraicStacks.IsGerbe B S hS 𝒲) :
    ∃ (Q : ObjectProperty 𝒳.val.val.obj)
      (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q)),
      IsLocallyClosedSubstack 𝒳 Q ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
          Set.range (AlgebraicStacks.pointsMap B S hS j) ∧
        (IsQuasiCompactStack.{u, w} B S hS 𝒲.val 𝒲.property →
          IsQuasiCompactStack.{u, w} B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val
            (fullSubcategoryAlgebraicStack 𝒳 Q hQ).property) := by
  obtain ⟨Q, ⟨hQlc, hQ, f, hfe, ⟨α⟩⟩, -⟩ :=
    AlgebraicStacks.existsUnique_locallyClosedSubstack_of_isImmersion j hj
  have hfs : IsSurjective B S hS f := isSurjective_of_isEquivalenceFunctor B S hS f hfe
  obtain ⟨eo⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒲.val.isFiberedInGroupoids (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) f.hom.hom.w hfe
  have hpts : AlgebraicStacks.pointsMap B S hS (f ≫ fullSubcategoryInclusion 𝒳 Q hQ) =
      AlgebraicStacks.pointsMap B S hS j :=
    Stack.pointsMap_eq_of_basedNatTrans B S hS _ _ _ α.hom.hom.hom
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
      Set.range (AlgebraicStacks.pointsMap B S hS j) := by
    rw [← hpts, AlgebraicStacks.pointsMap_comp, Set.range_comp, hfs.range_eq, Set.image_univ]
  refine ⟨Q, hQ, hQlc, isReducedStack_of_isEquivalence_stackMorphism f hfe hfs hred,
    AlgebraicStacks.isGerbe_of_equivalenceOver B S hS eo.symm hg, hrange, fun hqc => ?_⟩
  let := pointTopology B S hS 𝒲.val
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val
  have : CompactSpace _ := hqc
  exact ⟨by
    rw [← hfs.range_eq]
    exact isCompact_range (continuous_pointsMap B S hS 𝒲.val _ f.hom.hom)⟩

/-- A stack is a gerbe once every property `Q` (flat, locally of finite presentation) holding on
all automorphism spaces of a family of gerbes holds on all of its own (Stacks 06QJ). -/
private theorem isGerbe_of_forall_holdsOnEveryEtaleChart_isomSpace
    {𝒴 : AlgebraicStacks.{u, w} B S hS} {J : Type*} (𝒲 : J → AlgebraicStacks.{u, w} B S hS)
    (hg : ∀ j, AlgebraicStacks.IsGerbe B S hS (𝒲 j))
    [𝒴.val.val.p.IsFibered] [∀ j, (𝒲 j).val.val.p.IsFibered]
    (key : ∀ (Q : MorphismProperty Scheme.{u})
      [∀ T : BigFppfOver B S hS, MorphismProperty.IsLocalAtTarget
        (fun ⦃F G : AlgebraicSpaces B T.left.1 T.left.2⦄ (f : F ⟶ G) =>
          Space.HoldsOnEveryEtaleChart B T.left.1 T.left.2 Q f.hom)
        (Space.Topology.precoverage.{u, u + 1} .fpqc B T.left.1 T.left.2)],
      (∀ j (U : BigFppfOver B S hS) (x : (𝒲 j).val.val.p.Fiber U),
        Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
          (terminal.from (isomSpace B S hS (𝒲 j).val U x x))) →
      ∀ (U : BigFppfOver B S hS) (x : 𝒴.val.val.p.Fiber U),
        Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
          (terminal.from (isomSpace B S hS 𝒴.val U x x))) :
    AlgebraicStacks.IsGerbe B S hS 𝒴 := by
  have hflat := fun j =>
    AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbe
      B S hS _ (hg j)
  refine AlgebraicStacks.isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection
    B S hS _ ((isFlat_inertiaProjection_iff_isomSpace B S hS _).2 ?_)
    ((isLocallyOfFinitePresentation_inertiaProjection_iff_isomSpace B S hS _).2 ?_)
  · exact key _ fun j => (isFlat_inertiaProjection_iff_isomSpace B S hS _).1 (hflat j).1
  · exact key _ fun j =>
      (isLocallyOfFinitePresentation_inertiaProjection_iff_isomSpace B S hS _).1 (hflat j).2

/-- **An open substack of a gerbe is a gerbe**: its automorphism
spaces are those of the larger open substack, which are flat and locally of finite presentation
(Stacks 06QJ, (1) `⟹` (2)), so its inertia is flat and locally of finite presentation and it is a
gerbe (Stacks 06QJ, (2) `⟹` (1)). -/
theorem isGerbe_openSubstack_of_le
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (𝒰 𝒱 : OpenSubstack 𝒳)
    (h : 𝒱.property ≤ 𝒰.property) (hg : AlgebraicStacks.IsGerbe B S hS 𝒰.toAlgebraicStack) :
    AlgebraicStacks.IsGerbe B S hS 𝒱.toAlgebraicStack := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let : 𝒱.toAlgebraicStack.val.val.p.IsFibered :=
    𝒱.toAlgebraicStack.val.isFiberedInGroupoids.isFibered
  let : 𝒰.toAlgebraicStack.val.val.p.IsFibered :=
    𝒰.toAlgebraicStack.val.isFiberedInGroupoids.isFibered
  refine isGerbe_of_forall_holdsOnEveryEtaleChart_isomSpace B S hS (fun _ : Unit =>
    𝒰.toAlgebraicStack) (fun _ => hg) fun Q _ hQ U x => ?_
  -- The automorphism space of an object of `𝒱` is that of the same object in `𝒰`.
  let x' : 𝒰.toAlgebraicStack.val.val.p.Fiber U := ⟨⟨x.1.obj, h _ x.1.property⟩, x.2⟩
  obtain ⟨e₁⟩ := nonempty_isomSpace_iso_of_fullyFaithful B S hS 𝒱.inclusion U x
  obtain ⟨e₂⟩ := nonempty_isomSpace_iso_of_fullyFaithful B S hS 𝒰.inclusion U x'
  exact (Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B U.left.1 U.left.2 _
    (e₁ ≪≫ e₂.symm)).2 (hQ () U x')

/-- **A union of open substacks which are gerbes is a gerbe**.
The automorphism space of an object `x` of `⋃ᵢ 𝒲ᵢ` over `T` is, over the members of a covering
sieve of `T` (Stacks 05UQ), the automorphism space of a restriction of `x` lying in some `𝒲ᵢ`,
which is flat and locally of finite presentation (Stacks 06QJ, (1) `⟹` (2)); these properties
descend (`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_isomPresheaf_of_local`), and the union
is a gerbe by Stacks 06QJ, (2) `⟹` (1). -/
theorem isGerbe_iUnion
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {J : Type*} (𝒲 : J → OpenSubstack 𝒳)
    (hg : ∀ j, AlgebraicStacks.IsGerbe B S hS (𝒲 j).toAlgebraicStack) :
    AlgebraicStacks.IsGerbe B S hS (OpenSubstack.iUnion 𝒲).toAlgebraicStack := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let 𝒰 := OpenSubstack.iUnion 𝒲
  let : 𝒰.toAlgebraicStack.val.val.p.IsFibered :=
    𝒰.toAlgebraicStack.val.isFiberedInGroupoids.isFibered
  let : ∀ j, (𝒲 j).toAlgebraicStack.val.val.p.IsFibered := fun j =>
    (𝒲 j).toAlgebraicStack.val.isFiberedInGroupoids.isFibered
  -- The automorphism spaces of objects of `𝒳` lying in `⋃ᵢ 𝒲ᵢ` have `Q`.
  refine isGerbe_of_forall_holdsOnEveryEtaleChart_isomSpace B S hS (fun j => (𝒲 j).toAlgebraicStack)
    hg fun Q _ hQ U x => ?_
  let x𝒳 : 𝒳.val.val.p.Fiber U := ⟨x.1.obj, x.2⟩
  obtain ⟨e₁⟩ := nonempty_isomSpace_iso_of_fullyFaithful B S hS 𝒰.inclusion U x
  refine (Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B U.left.1 U.left.2 Q e₁).2 ?_
  obtain ⟨R, hR, hRmem⟩ := (OpenSubstack.isUnion_iUnion 𝒲).2 U x𝒳 x.1.property
  refine holdsOnEveryEtaleChart_isomPresheaf_of_local B S hS 𝒳.val 𝒳.property Q U x𝒳 x𝒳
    ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨j, hj⟩ := hRmem f hf
  let x' : (𝒲 j).toAlgebraicStack.val.val.p.Fiber V :=
    ⟨⟨(Functor.pullbackFiber 𝒳.val.val.p x𝒳 f).1, hj⟩,
      (Functor.pullbackFiber 𝒳.val.val.p x𝒳 f).2⟩
  obtain ⟨e₂⟩ := nonempty_isomSpace_iso_of_fullyFaithful B S hS (𝒲 j).inclusion V x'
  exact ⟨_, hQ j V x', ⟨e₂ ≪≫ Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op
    (isomPresheafPullbackCompIso 𝒳.val.val.p x𝒳 x𝒳 f)⟩⟩

/-- **The largest gerbe in a closed set of points.** For a set `T` of points of `𝒳`, the points of
`𝒳` lying in an open substack, which is a gerbe, of a reduced closed substack of `𝒳` with point
set `T`. By Stacks 0509 there is exactly one such reduced closed substack when `T` is closed, and
this is the image of the union of its open substacks which are gerbes: the open substack "as large
as possible" of the proof of Stacks 06RF, which makes the stratification canonical. -/
def maximalGerbePointSet (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) : Set (AlgebraicStacks.points B S hS 𝒳) :=
  {x | ∃ (P : ObjectProperty 𝒳.val.val.obj)
      (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)),
      IsClosedSubstack 𝒳 P ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) = T ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) ∧
        ∃ 𝒲 : OpenSubstack (fullSubcategoryAlgebraicStack 𝒳 P hP),
          AlgebraicStacks.IsGerbe B S hS 𝒲.toAlgebraicStack ∧
            x ∈ AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP) ''
              𝒲.pointSet B S hS}

/-- The largest gerbe in a set of points lies in that set. -/
theorem maximalGerbePointSet_subset (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) : maximalGerbePointSet B S hS 𝒳 T ⊆ T := by
  rintro x ⟨P, hP, -, hT, -, 𝒲, -, y, -, rfl⟩
  exact hT ▸ ⟨y, rfl⟩

/-- An open substack `𝒲` of a reduced stack `𝒳'` which is a gerbe is carried by an immersion
`i : 𝒳' ⟶ 𝒳` to a reduced locally closed substack of `𝒳` which is a gerbe, with points
`i '' |𝒲|`, and quasi-compact when `𝒲` is. -/
theorem exists_locallyClosedSubstack_of_isGerbe_openSubstack
    {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒳' ⟶ 𝒳)
    (hi : AlgebraicStacks.IsImmersion B S hS i) (hred : IsReducedStack B S hS 𝒳')
    (𝒲 : OpenSubstack 𝒳') (hg : AlgebraicStacks.IsGerbe B S hS 𝒲.toAlgebraicStack) :
    ∃ (Q : ObjectProperty 𝒳.val.val.obj)
      (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q)),
      IsLocallyClosedSubstack 𝒳 Q ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
          AlgebraicStacks.pointsMap B S hS i '' 𝒲.pointSet B S hS ∧
        (IsQuasiCompactStack.{u, w} B S hS 𝒲.toAlgebraicStack.val
            𝒲.toAlgebraicStack.property →
          IsQuasiCompactStack.{u, w} B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val
            (fullSubcategoryAlgebraicStack 𝒳 Q hQ).property) := by
  have hj : AlgebraicStacks.IsImmersion B S hS (𝒲.inclusion ≫ i) :=
    AlgebraicStacks.isImmersion_comp B S hS _ _
      (AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS _ 𝒲.isOpenImmersion) hi
  obtain ⟨Q, hQ, hlc, hr, hgQ, hrQ, hqcQ⟩ := exists_locallyClosedSubstack_of_isImmersion B S hS
    _ hj (isReducedStack_openSubstack B S hS 𝒳' hred 𝒲) hg
  refine ⟨Q, hQ, hlc, hr, hgQ, ?_, hqcQ⟩
  rw [hrQ, AlgebraicStacks.pointsMap_comp, Set.range_comp]

/-- A nonempty open substack `𝒰` of an algebraic stack which is a gerbe contains a nonempty
quasi-compact open substack, which is a gerbe (Stacks 04Y9). -/
theorem exists_openSubstack_isGerbe_isQuasiCompact (𝒳' : AlgebraicStacks.{u, w} B S hS)
    (𝒰 : OpenSubstack 𝒳') (hger : AlgebraicStacks.IsGerbe B S hS 𝒰.toAlgebraicStack)
    (hne : (𝒰.pointSet B S hS).Nonempty) :
    ∃ 𝒱 : OpenSubstack 𝒳', AlgebraicStacks.IsGerbe B S hS 𝒱.toAlgebraicStack ∧
      (𝒱.pointSet B S hS).Nonempty ∧
      IsQuasiCompactStack.{u, w} B S hS 𝒱.toAlgebraicStack.val 𝒱.toAlgebraicStack.property := by
  let := pointTopology B S hS 𝒳'.val
  obtain ⟨y', hy'⟩ := hne
  obtain ⟨V, ⟨hVo, hVc, hy'V⟩, hVsub⟩ :=
    (hasBasis_nhds_isOpen_isCompact B S hS 𝒳'.val 𝒳'.property y').mem_iff.1
      ((OpenSubstack.isOpen_pointSet B S hS 𝒰).mem_nhds hy')
  let 𝒱 := OpenSubstack.ofIsOpen B S hS V hVo
  have hVpts : 𝒱.pointSet B S hS = V := OpenSubstack.pointSet_ofIsOpen V hVo
  have hle : 𝒱.property ≤ 𝒰.property :=
    OpenSubstack.property_le_of_pointSet_subset B S hS (hVpts.symm ▸ hVsub)
  refine ⟨𝒱, isGerbe_openSubstack_of_le B S hS 𝒰 𝒱 hle hger, ⟨y', hVpts.symm ▸ hy'V⟩, ?_⟩
  let := pointTopology B S hS 𝒱.toAlgebraicStack.val
  have hembV := AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS 𝒱.inclusion
    (AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS _ 𝒱.isOpenImmersion)
  refine ⟨?_⟩
  rw [hembV.isCompact_iff, Set.image_univ]
  show IsCompact (𝒱.pointSet B S hS)
  rw [hVpts]
  exact hVc

/-- The points of `𝒳` carried by the open substacks which are gerbes of the reduced closed
substack with points `T` form the largest gerbe in `T`. -/
theorem image_iUnion_isGerbe_eq_maximalGerbePointSet (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) (hPc : IsClosedSubstack 𝒳 P)
    (hrange : Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) = T)
    (hred : IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP)) :
    AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP) ''
        (OpenSubstack.iUnion fun j : {𝒲 : OpenSubstack (fullSubcategoryAlgebraicStack 𝒳 P hP) //
          AlgebraicStacks.IsGerbe B S hS 𝒲.toAlgebraicStack} => j.1).pointSet B S hS =
      maximalGerbePointSet B S hS 𝒳 T := by
  rw [OpenSubstack.pointSet_iUnion]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact ⟨P, hP, hPc, hrange, hred, j.1, j.2, y, hj, rfl⟩
  · rintro ⟨P', hP', hP'c, hP'r, hP'red, 𝒲', hg', hx⟩
    obtain rfl : P' = P := (existsUnique_reducedClosedSubstack B S hS 𝒳 T hT).unique
      ⟨hP'c, fun _ => hP'r, fun _ => hP'red⟩ ⟨hPc, fun _ => hrange, fun _ => hred⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, Set.mem_iUnion.2 ⟨⟨𝒲', hg'⟩, hy⟩, rfl⟩

/-- **The strata over a closed set of points.** Let `𝒳` be an algebraic stack over `S` whose
automorphism spaces are quasi-compact, and `T ⊆ |𝒳|` a nonempty closed set. There is a reduced
locally closed substack of `𝒳` which is a gerbe, whose points form a subset of `T` open in `T` and
(a) dense in `T`; and there is one whose points form a nonempty subset of `T` open in `T` and which
is (b) quasi-compact.

Both are cut out of the reduced closed substack `𝒳'` with `|𝒳'| = T` (Stacks 0509): (a) by the
dense open gerbe of Stacks 06RC, (b) by a nonempty quasi-compact open of it (Stacks 04Y9). -/
theorem exists_gerbe_strata
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
        (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
        Space.IsQuasiCompact B U.left.1 U.left.2
          (terminal.from (isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
            (Functor.sliceValue 𝒳.val.val.p U y hy))))
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) (hTne : T.Nonempty) :
    (∃ (Q : ObjectProperty 𝒳.val.val.obj)
      (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q)),
      IsLocallyClosedSubstack 𝒳 Q ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) ⊆ T ∧
        (∃ O, @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧
          Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
            T ∩ O) ∧
        T ⊆ @closure _ (pointTopology B S hS 𝒳.val)
          (Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ))) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
          maximalGerbePointSet B S hS 𝒳 T) ∧
    (∃ (Q : ObjectProperty 𝒳.val.val.obj)
      (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q)),
      IsLocallyClosedSubstack 𝒳 Q ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) ⊆ T ∧
        (∃ O, @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧
          Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
            T ∩ O) ∧
        (Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ))).Nonempty ∧
        IsQuasiCompactStack.{u, w} B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val
          (fullSubcategoryAlgebraicStack 𝒳 Q hQ).property) := by
  let := pointTopology B S hS 𝒳.val
  obtain ⟨P, ⟨⟨hPiso, hP, hPimm⟩, hpts, hPred⟩, -⟩ :=
    existsUnique_reducedClosedSubstack B S hS 𝒳 T hT
  let 𝒳' := fullSubcategoryAlgebraicStack 𝒳 P hP
  let := pointTopology B S hS 𝒳'.val
  let i := fullSubcategoryInclusion 𝒳 P hP
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS i) = T := hpts hP
  have hi : AlgebraicStacks.IsImmersion B S hS i :=
    AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS i hPimm
  have hemb := AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS i hi
  have hred' : IsReducedStack B S hS 𝒳' := hPred hP
  obtain ⟨𝒰, hdense, hger⟩ := exists_dense_openSubstack_isGerbe_of_isomSpace B S hS
    𝒳' hred' (isQuasiCompact_isomSpace_of_fullyFaithful B S hS i hqc)
  -- Images of open sets of `|𝒳'|` are open in `T`.
  have himage : ∀ V : Set (AlgebraicStacks.points B S hS 𝒳'), IsOpen V →
      ∃ O, IsOpen O ∧ AlgebraicStacks.pointsMap B S hS i '' V = T ∩ O := by
    intro V hV
    obtain ⟨O, hO, rfl⟩ := hemb.isInducing.isOpen_iff.1 hV
    exact ⟨O, hO, by rw [Set.image_preimage_eq_range_inter, hrange]⟩
  constructor
  · -- (a): the union of all open substacks of `𝒳'` which are gerbes.
    let 𝒲 : {𝒲 : OpenSubstack 𝒳' // AlgebraicStacks.IsGerbe B S hS 𝒲.toAlgebraicStack} →
        OpenSubstack 𝒳' := fun j => j.1
    obtain ⟨Q, hQ, hlc, hr, hgQ, hrQ, -⟩ :=
      exists_locallyClosedSubstack_of_isGerbe_openSubstack B S hS i hi hred'
        (OpenSubstack.iUnion 𝒲) (isGerbe_iUnion B S hS 𝒲 fun j => j.2)
    obtain ⟨O, hO, hOeq⟩ := himage _ (OpenSubstack.isOpen_pointSet B S hS (OpenSubstack.iUnion 𝒲))
    have hle : 𝒰.pointSet B S hS ⊆ (OpenSubstack.iUnion 𝒲).pointSet B S hS := by
      rw [OpenSubstack.pointSet_iUnion]
      exact Set.subset_iUnion (fun j => (𝒲 j).pointSet B S hS) ⟨𝒰, hger⟩
    refine ⟨Q, hQ, hlc, hr, hgQ, hrQ.subset.trans ((Set.image_subset_range _ _).trans
      hrange.subset), ⟨O, hO, hrQ.trans hOeq⟩, ?_, ?_⟩
    · rw [hrQ, ← hrange, ← Set.image_univ, ← hdense.closure_eq]
      exact (image_closure_subset_closure_image
        (continuous_pointsMap B S hS 𝒳'.val 𝒳.val i.hom.hom)).trans
          (closure_mono (Set.image_mono hle))
    · exact hrQ.trans (image_iUnion_isGerbe_eq_maximalGerbePointSet B S hS 𝒳 T hT hP
        ⟨hPiso, hP, hPimm⟩ hrange hred')
  · -- (b): a nonempty quasi-compact open of the dense open gerbe.
    rw [← hrange] at hTne
    obtain ⟨_, y, -⟩ := hTne
    obtain ⟨𝒱, hg𝒱, hne𝒱, hqc𝒱⟩ :=
      exists_openSubstack_isGerbe_isQuasiCompact B S hS 𝒳' 𝒰 hger (hdense.nonempty_iff.2 ⟨y⟩)
    obtain ⟨Q, hQ, hlc, hr, hgQ, hrQ, hqcQ⟩ :=
      exists_locallyClosedSubstack_of_isGerbe_openSubstack B S hS i hi hred' 𝒱 hg𝒱
    obtain ⟨O, hO, hOeq⟩ := himage _ (OpenSubstack.isOpen_pointSet B S hS 𝒱)
    exact ⟨Q, hQ, hlc, hr, hgQ, hrQ.subset.trans ((Set.image_subset_range _ _).trans
      hrange.subset), ⟨O, hO, hrQ.trans hOeq⟩, hrQ ▸ hne𝒱.image _, hqcQ hqc𝒱⟩

/-- **Assembling the strata into a well-ordered stratification.** If every nonempty closed set
`T` of points of `𝒳` carries a reduced locally closed substack which is a gerbe, whose points form
a nonempty subset of `T` open in `T` and which has a further property `E T`, then there is a
well-ordered stratification of `|𝒳|` by such substacks (`TopologicalSpace`
`.exists_wellOrdered_stratification`). -/
theorem exists_gerbe_stratification_of_strata (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (E : Set (AlgebraicStacks.points B S hS 𝒳) → (Q : ObjectProperty 𝒳.val.val.obj) →
      IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q) → Prop)
    (h : ∀ T : Set (AlgebraicStacks.points B S hS 𝒳),
      @IsClosed _ (pointTopology B S hS 𝒳.val) T → T.Nonempty →
      ∃ (Q : ObjectProperty 𝒳.val.val.obj)
        (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q)),
        IsLocallyClosedSubstack 𝒳 Q ∧
          IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
          AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
          Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) ⊆ T ∧
          (∃ O, @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧
            Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
              T ∩ O) ∧
          (Set.range (AlgebraicStacks.pointsMap B S hS
            (fullSubcategoryInclusion 𝒳 Q hQ))).Nonempty ∧
          E T Q hQ) :
    ∃ (I : Type (u + 2)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (Q : I → ObjectProperty 𝒳.val.val.obj)
      (hQ : ∀ i, IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (Q i))),
      (∀ i, IsLocallyClosedSubstack 𝒳 (Q i) ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i)) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i))) ∧
      (⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 (Q i) (hQ i)))) = Set.univ ∧
      (∀ i, @IsClosed _ (pointTopology B S hS 𝒳.val) (Set.univ \ ⋃ (j : I) (_ : j < i),
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Q j) (hQ j))))) ∧
      (∀ i, ∃ O, @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Q i) (hQ i))) =
          (Set.univ \ ⋃ (j : I) (_ : j < i), Set.range (AlgebraicStacks.pointsMap B S hS
            (fullSubcategoryInclusion 𝒳 (Q j) (hQ j)))) ∩ O) ∧
      (∀ i, E (Set.univ \ ⋃ (j : I) (_ : j < i), Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 (Q j) (hQ j)))) (Q i) (hQ i)) := by
  classical
  let := pointTopology B S hS 𝒳.val
  choose Qf hQf hprop using h
  let f : Set (AlgebraicStacks.points B S hS 𝒳) → Set (AlgebraicStacks.points B S hS 𝒳) :=
    fun T => if hT : IsClosed T ∧ T.Nonempty then
      Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 (Qf T hT.1 hT.2) (hQf T hT.1 hT.2))) else ∅
  have hf : ∀ T (hT : IsClosed T) (hne : T.Nonempty), f T = Set.range
      (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Qf T hT hne)
        (hQf T hT hne))) := fun T hT hne => dite_eq_left ⟨hT, hne⟩
  have hsub : ∀ T, f T ⊆ T := by
    intro T
    by_cases hT : IsClosed T ∧ T.Nonempty
    · rw [hf T hT.1 hT.2]
      exact (hprop T hT.1 hT.2).2.2.2.1
    · simp only [f, dite_eq_right hT, Set.empty_subset]
  have hopen : ∀ T, IsClosed T → ∃ O, IsOpen O ∧ f T = T ∩ O := by
    intro T hT
    rcases T.eq_empty_or_nonempty with hne | hne
    · exact ⟨∅, isOpen_empty, by
        rw [hne, Set.empty_inter]
        exact Set.subset_empty_iff.1 (hne ▸ hsub ∅)⟩
    · rw [hf T hT hne]
      exact (hprop T hT hne).2.2.2.2.1
  have hne : ∀ T, IsClosed T → T.Nonempty → (f T).Nonempty := by
    intro T hT hT'
    rw [hf T hT hT']
    exact (hprop T hT hT').2.2.2.2.2.1
  obtain ⟨I, _, _, Ts, hTs, hTc, hTne, hcov⟩ :=
    TopologicalSpace.exists_wellOrdered_stratification f hsub hopen hne
  have hfi : ∀ i, f (Ts i) = Set.range (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 (Qf (Ts i) (hTc i) (hTne i)) (hQf (Ts i) (hTc i) (hTne i)))) :=
    fun i => hf _ (hTc i) (hTne i)
  have hTs' : ∀ i, Ts i = Set.univ \ ⋃ (j : I) (_ : j < i), Set.range
      (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Qf (Ts j) (hTc j) (hTne j))
        (hQf (Ts j) (hTc j) (hTne j)))) := by
    intro i
    rw [hTs i]
    simp only [hfi]
  refine ⟨I, inferInstance, inferInstance, fun i => Qf (Ts i) (hTc i) (hTne i),
    fun i => hQf (Ts i) (hTc i) (hTne i), fun i => ⟨(hprop _ _ _).1, (hprop _ _ _).2.1,
      (hprop _ _ _).2.2.1⟩, ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [← hcov]
    simp only [hfi]
  · rw [← hTs' i]
    exact hTc i
  · rw [← hTs' i]
    exact (hprop _ _ _).2.2.2.2.1
  · rw [← hTs' i]
    exact (hprop _ _ _).2.2.2.2.2.2

/-- **Stacks 06RF, the stratifications (a) and (b).** Let `𝒳` be an algebraic stack over `S`
whose inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact. Then there are a well-ordered index set
`I` and for every `i ∈ I` a reduced locally closed substack `𝒰ᵢ ⊆ 𝒳` such that

1. each `𝒰ᵢ` is a gerbe,
2. `|𝒳| = ⋃ᵢ |𝒰ᵢ|`,
3. `Tᵢ = |𝒳| \ ⋃_{i' < i} |𝒰ᵢ'|` is closed in `|𝒳|`, and
4. `|𝒰ᵢ|` is open in `Tᵢ`,

and this can be arranged so that (a) `|𝒰ᵢ|` is dense in `Tᵢ` for every `i`, with `𝒰ᵢ` chosen as
large as possible: `|𝒰ᵢ|` is the set of points of `Tᵢ` lying in an open substack, which is a
gerbe, of the reduced closed substack with points `Tᵢ` (`maximalGerbePointSet`); and also so that
(b) every `𝒰ᵢ` is quasi-compact. Here `|𝒰ᵢ|` is the image of the points of `𝒰ᵢ` in `|𝒳|`. The
stratification of case (a) is canonical: `exists_gerbe_stratification_unique`. -/
@[stacks 06RF "existence of the stratification, arranged as in (a), with strata as large as \
possible, and as in (b)"]
theorem exists_gerbe_stratification
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    (∃ (I : Type (u + 2)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (Q : I → ObjectProperty 𝒳.val.val.obj)
      (hQ : ∀ i, IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (Q i))),
      (∀ i, IsLocallyClosedSubstack 𝒳 (Q i) ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i)) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i))) ∧
      (⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 (Q i) (hQ i)))) = Set.univ ∧
      (∀ i, @IsClosed _ (pointTopology B S hS 𝒳.val) (Set.univ \ ⋃ (j : I) (_ : j < i),
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Q j) (hQ j))))) ∧
      (∀ i, ∃ O, @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Q i) (hQ i))) =
          (Set.univ \ ⋃ (j : I) (_ : j < i), Set.range (AlgebraicStacks.pointsMap B S hS
            (fullSubcategoryInclusion 𝒳 (Q j) (hQ j)))) ∩ O) ∧
      (∀ i, (Set.univ \ ⋃ (j : I) (_ : j < i), Set.range (AlgebraicStacks.pointsMap B S hS
          (fullSubcategoryInclusion 𝒳 (Q j) (hQ j)))) ⊆
        @closure _ (pointTopology B S hS 𝒳.val) (Set.range (AlgebraicStacks.pointsMap B S hS
          (fullSubcategoryInclusion 𝒳 (Q i) (hQ i)))) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Q i) (hQ i))) =
          maximalGerbePointSet B S hS 𝒳 (Set.univ \ ⋃ (j : I) (_ : j < i),
            Set.range (AlgebraicStacks.pointsMap B S hS
              (fullSubcategoryInclusion 𝒳 (Q j) (hQ j)))))) ∧
    (∃ (I : Type (u + 2)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (Q : I → ObjectProperty 𝒳.val.val.obj)
      (hQ : ∀ i, IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (Q i))),
      (∀ i, IsLocallyClosedSubstack 𝒳 (Q i) ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i)) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i))) ∧
      (⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 (Q i) (hQ i)))) = Set.univ ∧
      (∀ i, @IsClosed _ (pointTopology B S hS 𝒳.val) (Set.univ \ ⋃ (j : I) (_ : j < i),
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Q j) (hQ j))))) ∧
      (∀ i, ∃ O, @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 (Q i) (hQ i))) =
          (Set.univ \ ⋃ (j : I) (_ : j < i), Set.range (AlgebraicStacks.pointsMap B S hS
            (fullSubcategoryInclusion 𝒳 (Q j) (hQ j)))) ∩ O) ∧
      (∀ i, IsQuasiCompactStack.{u, w} B S hS (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i)).val
        (fullSubcategoryAlgebraicStack 𝒳 (Q i) (hQ i)).property)) := by
  let := pointTopology B S hS 𝒳.val
  have hqc' := isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection B S hS 𝒳 hqc
  constructor
  · refine exists_gerbe_stratification_of_strata B S hS 𝒳
      (fun T Q hQ => T ⊆ closure (Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 Q hQ))) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
          maximalGerbePointSet B S hS 𝒳 T) fun T hT hTne => ?_
    obtain ⟨Q, hQ, hlc, hr, hg, hsub, hopen, hdense, hmax⟩ :=
      (exists_gerbe_strata B S hS 𝒳 hqc' T hT hTne).1
    exact ⟨Q, hQ, hlc, hr, hg, hsub, hopen, closure_nonempty_iff.1 (hTne.mono hdense), hdense,
      hmax⟩
  · exact exists_gerbe_stratification_of_strata B S hS 𝒳
      (fun _ Q hQ => IsQuasiCompactStack.{u, w} B S hS
        (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val
        (fullSubcategoryAlgebraicStack 𝒳 Q hQ).property) fun T hT hTne =>
      (exists_gerbe_strata B S hS 𝒳 hqc' T hT hTne).2

/-- **Stacks 06RF, the canonical stratification (a).** A stratification of `|𝒳|` as in Stacks
06RF whose strata are chosen as large as possible is unique: if two well-ordered families of
nonempty sets of points `Wᵢ` cover `|𝒳|` and each `Wᵢ` is the largest gerbe
(`maximalGerbePointSet`) in `Tᵢ = |𝒳| \ ⋃_{j < i} Wⱼ`, then the index sets are order-isomorphic
with the same sets. -/
@[stacks 06RF "canonicity of the stratification (a) with strata as large as possible"]
theorem exists_gerbe_stratification_unique (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {I : Type*} [LinearOrder I] [WellFoundedLT I] (W : I → Set (AlgebraicStacks.points B S hS 𝒳))
    (hW : ∀ i, W i = maximalGerbePointSet B S hS 𝒳 (Set.univ \ ⋃ (j : I) (_ : j < i), W j))
    (hWne : ∀ i, (W i).Nonempty) (hWcov : (⋃ i, W i) = Set.univ)
    {I' : Type*} [LinearOrder I'] [WellFoundedLT I']
    (W' : I' → Set (AlgebraicStacks.points B S hS 𝒳))
    (hW' : ∀ i, W' i = maximalGerbePointSet B S hS 𝒳 (Set.univ \ ⋃ (j : I') (_ : j < i), W' j))
    (hW'ne : ∀ i, (W' i).Nonempty) (hW'cov : (⋃ i, W' i) = Set.univ) :
    ∃ e : I ≃o I', ∀ i, W' (e i) = W i := by
  let f := maximalGerbePointSet B S hS 𝒳
  let T : I → Set (AlgebraicStacks.points B S hS 𝒳) := fun i =>
    Set.univ \ ⋃ (j : I) (_ : j < i), W j
  let T' : I' → Set (AlgebraicStacks.points B S hS 𝒳) := fun i =>
    Set.univ \ ⋃ (j : I') (_ : j < i), W' j
  have hfT : ∀ i, f (T i) = W i := fun i => (hW i).symm
  have hfT' : ∀ i, f (T' i) = W' i := fun i => (hW' i).symm
  let := pointTopology B S hS 𝒳.val
  obtain ⟨e, he⟩ :=
    TopologicalSpace.stratification_unique f (maximalGerbePointSet_subset B S hS 𝒳) T
      (fun i => by simp only [T, hfT]) (fun i => by simpa only [hfT] using hWne i)
      (by simpa only [hfT] using hWcov) T' (fun i => by simp only [T', hfT'])
      (fun i => by simpa only [hfT'] using hW'ne i) (by simpa only [hfT'] using hW'cov)
  exact ⟨e, fun i => by rw [← hfT' (e i), he i, hfT]⟩

end AlgebraicGeometry.Stack

end
