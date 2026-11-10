module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.SchemeGeneric
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageDiscreteValuationPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperImageAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed

/-!
# Stacks 0CQM over an affine Noetherian base, given a proper surjective scheme cover

Let `V` be an affine Noetherian scheme of the big fppf site of `S`, let `f : 𝒳 ⟶ V` be a
separated 1-morphism of finite type of algebraic stacks over `S`, and let `h : 𝒰 ⟶ 𝒳` be of
finite type with dense image, such that `h` and `f` satisfy the hypothesis of **Stacks 0CQM**.
Suppose given a scheme `X'` of the site and a surjective 1-morphism `p : X' ⟶ 𝒳` which is
universally closed and satisfies the existence part of the valuative criterion, with `p ≫ f`
2-isomorphic to the 1-morphism induced by a separated morphism `X' ⟶ V` of finite type. Then `f`
is proper. This is the last two paragraphs of the proof of Stacks 0CQM, with Chow's lemma
replaced by the given cover.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_schemeStackMap`: a universally
  closed morphism of the site induces a universally closed 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_denseTestExistence_of_schemeCover`: the
  statement above.

## Implementation notes

The source replaces `X` by the scheme-theoretic image of `W = X ×_𝒳 𝒰 ⟶ X`. Here `W` is a
2-fibre product of algebraic stacks, so an affine smooth presentation `W₀ ⟶ W` is chosen first
(it exists because `W` is quasi-compact, being of finite type over the quasi-compact scheme
`X'`), and `Z ⊂ X'` is the scheme-theoretic image of the morphism of schemes `W₀ ⟶ X'`
underlying the composite. The hypothesis of Stacks 0CQM for `h`, `f` transfers to the induced
1-morphisms `W₀ ⟶ Z`, `Z ⟶ V` by
`AlgebraicGeometry.Stack.ValuativeCriterion.denseTestExistence_of_lift`, because `Z ⟶ X' ⟶ 𝒳`
satisfies the existence part of the valuative criterion (**Stacks 0CLP**, **Stacks 0CLM**); this
is the claim of the source's proof, including its appeal to **Stacks 0ARH**. Properness of
`Z ⟶ V` then follows from condition (4) of **Stacks 0208**, which is all the source's appeal to
Limits of Spaces, Lemma 0CMD uses here: the generic points of `Z` lie in the image of `W₀` because
`W₀ ⟶ Z` is quasi-compact and dominant. Finally `Z ⟶ 𝒳` is surjective, its image being closed and
containing the dense image of `h`, and **Stacks 0CQK** gives properness of `f`.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
* [Stacks Project, Tag 0CQK](https://stacks.math.columbia.edu/tag/0CQK)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of schemes underlying a 1-morphism of represented algebraic stacks which is
locally of finite type is itself locally of finite type. -/
alias locallyOfFiniteType_toScheme_map_schemeMapOfFunctor :=
  locallyOfFiniteType_schemeMapOfFunctor

namespace AlgebraicStacks

/-- **A universally closed morphism of the site induces a universally closed 1-morphism of
algebraic stacks.** The Yoneda image of the morphism is universally closed, so the induced
1-morphism is universally closed relatively to algebraic spaces, which is universal closedness on
points by **Stacks 0512**, the 1-morphism being representable by algebraic spaces. -/
theorem universallyClosed_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map g)) :
    UniversallyClosed B S hS (schemeStackMap.{u, w} B S hS g) := by
  have _ : (Space.universallyClosedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hrel := hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS
    (Space.universallyClosedProperty B S hS) g (Space.universallyClosed_yoneda_map B S hS g hg)
  exact (representable_universallyClosed_iff_closedMap_baseChange B S hS
    (schemeStackMap.{u, w} B S hS g)
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)).1 hrel

/-- **Stacks 0CQM over an affine Noetherian base, given a proper surjective scheme cover.** Let
`V` be an affine locally Noetherian scheme of the site, `f : 𝒳 ⟶ V` separated and of finite type,
and `h : 𝒰 ⟶ 𝒳` of finite type with dense image such that `h`, `f` satisfy the hypothesis of
Stacks 0CQM. If `p : X' ⟶ 𝒳` is a surjective, universally closed 1-morphism from a scheme of the
site satisfying the existence part of the valuative criterion, and `p ≫ f` is 2-isomorphic to the
1-morphism induced by a separated quasi-compact morphism `φ : X' ⟶ V` locally of finite type,
then `f` is proper. -/
theorem isProper_of_denseTestExistence_of_schemeCover
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ schemeStack.{u, w} B S hS V) (h : 𝒰 ⟶ 𝒳)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : letI := Stack.pointTopology B S hS 𝒳.val
      Dense (Set.range (AlgebraicStacks.pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DenseTestExistence B S hS h f)
    {X' : BigFppfOver B S hS} (p : schemeStack.{u, w} B S hS X' ⟶ 𝒳)
    (hpuc : UniversallyClosed B S hS p) (hpex : ValuativeCriterion.Existence B S hS p)
    (hps : Stack.IsSurjective B S hS p) (φ : X' ⟶ V)
    (hφsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map φ))
    (hφlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map φ))
    (hφqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map φ))
    (eφ : p ≫ f ≅ schemeStackMap.{u, w} B S hS φ) :
    IsProper B S hS f := by
  classical
  let T := BigFppfOver.toScheme B S hS
  have _ := hV
  have _ := hVN
  have _ := hφsep
  have _ := hφlft
  have _ := hφqc
  -- the base change of `h` along `p`, and an affine smooth presentation of it
  let P := twoFibreProductSquareAlgebraicStacks B S hS p h
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p h
  have hPft : IsFiniteType B S hS P.fst := isFiniteType_baseChange B S hS h p P hP hh
  have hX'c : CompactSpace (T.obj X') := QuasiCompact.compactSpace_of_compactSpace (T.map φ)
  have hX'qc := isQuasiCompactStack_schemeStack.{u, w} B S hS X'
    (Space.isQuasiCompactSpace_yoneda B S hS X' hX'c)
  have hPqc := isQuasiCompactStack_of_isQuasiCompactMorphism B S hS P.fst hPft.2 hX'qc
  obtain ⟨W, hW, c, hcsurj, hcsm⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS P.pt).1 hPqc
  let c' : schemeStack.{u, w} B S hS W ⟶ P.pt := c
  have _ : IsAffine (T.obj W) := hW
  have hidlft : Space.IsLocallyOfFiniteType B S hS (𝟙 (yoneda.obj W)) := by
    simpa using (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (𝟙 W)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have hclft : AlgebraicStacks.IsLocallyOfFiniteType B S hS c' :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h ↦ Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (schemeStack.{u, w} B S hS W).property P.pt.property c'.hom).2
      (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
        (fun _ _ h ↦ Space.IsLocallyOfFiniteType B S hS h) c'.hom
        (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
        (PresheafOfCategories.sliceElementsEquivalenceOver W) hcsm hidlft)
  -- the morphism of schemes `W ⟶ X'`
  let ψ₀ : W ⟶ X' := schemeMapOfFunctor B S hS (c' ≫ P.fst).hom.hom
  have _ : LocallyOfFiniteType (T.map ψ₀) :=
    locallyOfFiniteType_toScheme_map_schemeMapOfFunctor B S hS (c' ≫ P.fst)
      (isLocallyOfFiniteType_comp B S hS c' P.fst hclft hPft.1)
  have _ : QuasiCompact (T.map ψ₀) := by
    have : QuasiCompact (T.map ψ₀ ≫ T.map φ) := inferInstance
    exact QuasiCompact.of_comp (T.map ψ₀) (T.map φ)
  -- the scheme-theoretic image `Z` of `W ⟶ X'`
  let g := T.map ψ₀
  have hZsize : B.Contains g.image :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact g.imageι) X'.left.property
  let Zobj : BigFppfOver B S hS :=
    Over.mk ((⟨g.imageι⟩ : B.obj hZsize ⟶ X'.left) ≫ X'.hom)
  let ι : Zobj ⟶ X' := Over.homMk (⟨g.imageι⟩ : Zobj.left ⟶ X'.left) rfl
  let ψ' : W ⟶ Zobj := Over.homMk (⟨g.toImage⟩ : W.left ⟶ Zobj.left) (by
    apply B.inclusion.map_injective
    change g.toImage ≫ g.imageι ≫ B.inclusion.map X'.hom = B.inclusion.map W.hom
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    have h1 := congrArg B.inclusion.map (Over.w ψ₀)
    rwa [B.inclusion.map_comp] at h1)
  have hψ'ι : ψ' ≫ ι = ψ₀ :=
    Over.OverMorphism.ext (B.inclusion.map_injective (Scheme.Hom.toImage_imageι g))
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion (T.map ι) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion g.imageι)
  have _ : IsDominant (T.map ψ') := inferInstanceAs (IsDominant g.toImage)
  have _ : QuasiCompact (T.map ψ') := inferInstanceAs (QuasiCompact g.toImage)
  have _ : LocallyOfFiniteType (T.map ψ') := by
    have : LocallyOfFiniteType (T.map ψ' ≫ T.map ι) := by
      rw [← T.map_comp, hψ'ι]
      infer_instance
    exact LocallyOfFiniteType.of_comp (f := T.map ψ') (g := T.map ι) this
  -- the 1-morphism `Z ⟶ 𝒳`
  let pZ := schemeStackMap.{u, w} B S hS ι ≫ p
  have hιst : IsClosedImmersion B S hS (schemeStackMap.{u, w} B S hS ι) :=
    isClosedImmersion_schemeStackMap.{u, w} B S hS ι inferInstance
  have hpZuc : UniversallyClosed B S hS pZ :=
    universallyClosed_comp B S hS _ _ (universallyClosed_of_isClosedImmersion B S hS _ hιst) hpuc
  have hpZex : ValuativeCriterion.Existence B S hS pZ :=
    valuativeCriterionExistence_comp B S hS _ _
      (valuativeCriterionExistence_of_isClosedImmersion B S hS _ hιst) hpex
  -- the hypothesis of Stacks 0CQM for `W ⟶ Z` and `Z ⟶ V`
  let eψ₀ : c' ≫ P.fst ≅ schemeStackMap.{u, w} B S hS ψ₀ := schemeStackMapIso B S hS (c' ≫ P.fst)
  let σ : schemeStackMap.{u, w} B S hS ψ' ≫ pZ ≅ (c' ≫ P.snd) ≫ h :=
    (α_ _ _ _).symm ≪≫
      whiskerRightIso (eqToIso ((schemeStackMap_comp B S hS ψ' ι).trans
        (congrArg (schemeStackMap.{u, w} B S hS) hψ'ι))) p ≪≫
      whiskerRightIso eψ₀.symm p ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso c' P.iso ≪≫ (α_ _ _ _).symm
  let τ : schemeStackMap.{u, w} B S hS (ι ≫ φ) ≅ pZ ≫ f :=
    eqToIso (schemeStackMap_comp B S hS ι φ).symm ≪≫
      whiskerLeftIso (schemeStackMap.{u, w} B S hS ι) eφ.symm ≪≫ (α_ _ _ _).symm
  have hE : ValuativeCriterion.DenseTestExistence B S hS (schemeStackMap.{u, w} B S hS ψ')
      (schemeStackMap.{u, w} B S hS (ι ≫ φ)) :=
    ValuativeCriterion.denseTestExistence_of_lift B S hS (c' ≫ P.snd) pZ σ τ
      (fun _ F G ↦ subsingleton_hom₂_schemeFibredCategory B S hS F G) hpZex hlift
  -- `Z ⟶ V` is proper, by condition (4) of Stacks 0208
  have hZV : _root_.AlgebraicGeometry.IsProper (T.map (ι ≫ φ)) := by
    have _ : LocallyOfFiniteType (T.map ι) :=
      ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType (T.map ι)).mp inferInstance).2
    have _ : LocallyOfFiniteType (T.map (ι ≫ φ)) := by
      rw [T.map_comp]; infer_instance
    have _ : QuasiCompact (T.map (ι ≫ φ)) := by
      rw [T.map_comp]; infer_instance
    have hZsep : _root_.AlgebraicGeometry.IsSeparated (T.map (ι ≫ φ)) := by
      rw [T.map_comp]; infer_instance
    have huniq := ((_root_.AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType
      (T.map (ι ≫ φ))).out 1 4).mp hZsep
    refine isProper_of_genericDiscreteValuativeCriterion (T.map (ι ≫ φ)) ?_
    intro η hη A hA hAK i₂ sq
    exact ⟨nonempty_liftStruct_of_denseTestExistence B S hS ψ' (ι ≫ φ)
        (IsDominant.denseRange (f := T.map ψ')) hE η hη A hA hAK i₂ sq,
      huniq η hη A hA hAK i₂ sq⟩
  -- `Z ⟶ 𝒳` is surjective
  have hpZsurj : Stack.IsSurjective B S hS pZ := by
    let := Stack.pointTopology B S hS 𝒳.val
    let := Stack.pointTopology B S hS (schemeStack.{u, w} B S hS Zobj).val
    have hcl : _root_.IsClosed (Set.range (AlgebraicStacks.pointsMap B S hS pZ)) := by
      have := isClosed_of_universallyClosed B S hS pZ hpZuc Set.univ isClosed_univ
      rwa [Set.image_univ] at this
    have hsub : Set.range (AlgebraicStacks.pointsMap B S hS h) ⊆
        Set.range (AlgebraicStacks.pointsMap B S hS pZ) := by
      rintro _ ⟨u₀, rfl⟩
      obtain ⟨x', hx'⟩ := hps (AlgebraicStacks.pointsMap B S hS h u₀)
      obtain ⟨pt, hpt₁, -⟩ :=
        exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP x' u₀ hx'
      obtain ⟨wpt, hwpt⟩ := hcsurj pt
      refine ⟨AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ψ') wpt, ?_⟩
      have e1 : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ψ₀) =
          AlgebraicStacks.pointsMap B S hS (c' ≫ P.fst) :=
        pointsMap_eq_of_hom₂ B S hS eψ₀.inv
      calc AlgebraicStacks.pointsMap B S hS pZ
            (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ψ') wpt)
          = AlgebraicStacks.pointsMap B S hS p
              (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ψ₀) wpt) := by
            rw [← hψ'ι, ← schemeStackMap_comp, pointsMap_comp, pointsMap_comp]
            rfl
        _ = AlgebraicStacks.pointsMap B S hS p
              (AlgebraicStacks.pointsMap B S hS (c' ≫ P.fst) wpt) := by rw [e1]
        _ = AlgebraicStacks.pointsMap B S hS p x' := by
            rw [pointsMap_comp, Function.comp_apply, hwpt]
            exact congrArg _ hpt₁
        _ = AlgebraicStacks.pointsMap B S hS h u₀ := hx'
    intro x
    have hx : x ∈ closure (Set.range (AlgebraicStacks.pointsMap B S hS h)) := by
      rw [hdense.closure_eq]
      trivial
    exact closure_minimal hsub hcl hx
  -- Stacks 0CQK
  have hUC : UniversallyClosed B S hS (pZ ≫ f) :=
    universallyClosed_of_iso B S hS τ
      (universallyClosed_schemeStackMap B S hS (ι ≫ φ) inferInstance)
  exact isProper_of_surjective_universallyClosed_comp B S hS pZ f hUC hpZsurj hsep hf

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
