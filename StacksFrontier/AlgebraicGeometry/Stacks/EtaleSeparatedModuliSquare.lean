module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineEtaleModuliSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSeparatedChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleGroupoidQuotientGlue
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpenQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.GlueDataOverBaseSite
public import StacksFrontier.AlgebraicGeometry.Size.Basic

/-!
# An étale separated stabilizer-preserving morphism to a well-nigh affine stack (Stacks 0DUS)

Let `h : 𝒳' ⟶ 𝒳` be an étale, separated morphism of algebraic stacks inducing isomorphisms on
automorphism groups, with `𝒳` well-nigh affine. Then there is a cartesian square
```
𝒳' ⟶ 𝒳
↓     ↓
M' ⟶ M
```
with `M' ⟶ M` a separated étale morphism of schemes and `𝒳 ⟶ M` the moduli space of
Stacks 0DUP.

The proof follows the source. Choose a chart `x : U ⟶ 𝒳` with `U` affine and `R = U ×_𝒳 U`
represented by the affine `V`. The base change `W = 𝒳' ×_𝒳 U` is a scheme, separated and étale
over `U` (Stacks 0DU9, 0DU7, 0418), and its relation `R' = W ×_𝒳' W` is represented by
`V ×_{s, U} W`, finite locally free over `W`. The morphism of groupoid schemes
`(W, R') ⟶ (U, R)` has cartesian source, target and stabilizer squares. Covering `W` by
`R'`-invariant affine opens `Q i` (Stacks 07S0, 03JE), the invariant spectra `N i` are étale over
`M = Spec C` with `Q i = N i ×_M U` (Stacks 0DT9); they glue along the images of the overlaps to a
scheme `Y` (Stacks 01JA, 01JB) with `W = Y ×_M U`, étale over `M`, and separated over `M` since
`W ⟶ Y` is a universally closed surjection and `W ⟶ M` is separated (Stacks 09MQ). The invariant
morphism `W ⟶ Y` descends to `𝒳' ⟶ Y` (Stacks 0DUH), and the square of stacks is cartesian by
the argument of Stacks 0DUQ
(`AlgebraicGeometry.Stack.ChartBaseChange.nonempty_isTwoFibreProduct_moduliSquare`).

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.exists_relation'_representation_general`: the relation
  of a base-changed chart is represented by `V ×_{s, U} W`, for any `W`.
* `AlgebraicGeometry.Stack.exists_isTwoFibreProduct_moduliSpace_of_isEtale_of_isSeparated`:
  **Stacks 0DUS**.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U W : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)

/-- A pullback square of representable presheaves gives a commuting square of site morphisms. -/
private theorem comp_eq_of_isPullback_yoneda {P X Y Z : BigFppfOver B S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map d)) :
    a ≫ c = b ≫ d :=
  yoneda.map_injective ((yoneda.map_comp _ _).trans (h.w.trans (yoneda.map_comp _ _).symm))

/-- **The relation of the base-changed chart is represented by an object of the site** for an
arbitrary (not necessarily affine) `W`: the fibre product `V ×_{s, U} W`, whose source and target
are finite locally free when those of `R` are. -/
theorem exists_relation'_representation_general {V : BigFppfOver B S hS}
    (eR : StacksRepresentableCFG.EquivalenceOver (rel x).val.p
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
    (hsF : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (htF : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t))
    (fU : W ⟶ U)
    (hfU : yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK)) :
    ∃ (V' : BigFppfOver B S hS)
      (eR' : StacksRepresentableCFG.EquivalenceOver (rel' h x eK).val.p
        (presheafOfCategories (yoneda.obj V' ⋙ typeToCat)).p)
      (s' t' : V' ⟶ W) (fV : V' ⟶ V),
      yoneda.map s' = SelfIntersection.relationSourceMap
        (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩)
        (PresheafOfCategories.sliceElementsEquivalenceOver W) eR' ∧
      yoneda.map t' = SelfIntersection.relationTargetMap
        (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩)
        (PresheafOfCategories.sliceElementsEquivalenceOver W) eR' ∧
      yoneda.map fV = representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
        (relationMap h x eK) ∧
      IsPullback (yoneda.map fV) (yoneda.map s') (yoneda.map s) (yoneda.map fU) ∧
      IsPullback (yoneda.map fV) (yoneda.map t') (yoneda.map t) (yoneda.map fU) ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s') ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t') := by
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let eW := PresheafOfCategories.sliceElementsEquivalenceOver W
  -- the relation `R'` is represented by an algebraic space (Stacks 04T4 (1))
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (schemeStack.{u, w} B S hS W).val 𝒳'.val (chart' h x eK).hom 𝒳'.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  -- the source square for that representation identifies it with `V ×_{s, U} W`
  have hpb₀ := isPullback_relationSource (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (R₀' := ⟨F, hF⟩) h x eK eU eW eR eF
  rw [← hs, ← hfU] at hpb₀
  have hyP : IsPullback (yoneda.map (pullback.fst s fU)) (yoneda.map (pullback.snd s fU))
      (yoneda.map s) (yoneda.map fU) := (IsPullback.of_hasPullback s fU).map yoneda
  let i : F ≅ yoneda.obj (pullback s fU) := hpb₀.isoIsPullback _ _ hyP
  let eR' : StacksRepresentableCFG.EquivalenceOver (rel' h x eK).val.p
      (presheafOfCategories (yoneda.obj (pullback s fU) ⋙ typeToCat)).p :=
    eF.trans (PresheafOfCategories.equivalenceOverOfIso i)
  -- the two squares for the new representation
  have hsq := isPullback_relationSource (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (R₀' := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) h x eK eU eW eR eR'
  have htq := isPullback_relationTarget (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (R₀' := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) h x eK eU eW eR eR'
  rw [← hs, ← hfU] at hsq
  rw [← ht, ← hfU] at htq
  obtain ⟨s', hs'⟩ : ∃ s' : pullback s fU ⟶ W, yoneda.map s' =
      SelfIntersection.relationSourceMap
        (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (R := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) eW eR' :=
    ⟨_, yoneda.map_preimage _⟩
  obtain ⟨t', ht'⟩ : ∃ t' : pullback s fU ⟶ W, yoneda.map t' =
      SelfIntersection.relationTargetMap
        (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (R := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) eW eR' :=
    ⟨_, yoneda.map_preimage _⟩
  obtain ⟨fV, hfV⟩ : ∃ fV : pullback s fU ⟶ V, yoneda.map fV =
      representingMap B S hS _ _ (yoneda.obj (pullback s fU)) (yoneda.obj V) eR' eR
        (relationMap h x eK) :=
    ⟨_, yoneda.map_preimage _⟩
  rw [← hs', ← hfV] at hsq
  rw [← ht', ← hfV] at htq
  exact ⟨pullback s fU, eR', s', t', fV, hs', ht', hfV, hsq, htq,
    isFiniteLocallyFree_of_isPullback (isPullback_toScheme_of_isPullback_yoneda hsq) hsF,
    isFiniteLocallyFree_of_isPullback (isPullback_toScheme_of_isPullback_yoneda htq) htF⟩

end ChartBaseChange

section Main

variable (B S hS)

open GroupoidScheme.InvariantCoverGlue in
/-- **Stacks 0DUS.** Let `h : 𝒳' ⟶ 𝒳` be a morphism of algebraic stacks. Assume `𝒳` is well-nigh
affine, `h` is étale, `h` is separated, and `h` induces isomorphisms on automorphism groups
(Stacks 0DTW). Then there exists a cartesian diagram
```
𝒳' ⟶ 𝒳
↓     ↓
M' ⟶ M
```
where `M' ⟶ M` is a separated étale morphism of schemes and `𝒳 ⟶ M` is the moduli space
constructed in Stacks 0DUP: a uniform categorical moduli space in affine schemes, separated,
quasi-compact and a universal homeomorphism. -/
@[stacks 0DUS]
theorem exists_isTwoFibreProduct_moduliSpace_of_isEtale_of_isSeparated
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳)
    (he : IsEtale B S hS h) (hsep : AlgebraicStacks.IsSeparated B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q) :
    ∃ (M M' : BigFppfOver B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj M) (isAlgebraicSpace_yoneda B S hS M))
      (f' : 𝒳' ⟶
        algebraicSpaceStack.{u, w} B S hS (yoneda.obj M') (isAlgebraicSpace_yoneda B S hS M'))
      (g : M' ⟶ M) (hcomm : f'.hom ≫ (associatedMap B S hS (yoneda.map g)).1 = h.hom ≫ f.hom),
      Etale ((BigFppfOver.toScheme B S hS).map g) ∧
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g) ∧
      Nonempty (Bicategory.IsTwoFibreProduct
        (ChartBaseChange.moduliSquare h g f.hom f'.hom hcomm)) ∧
      (IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj)
          ⟨yoneda.obj M, isAlgebraicSpace_yoneda B S hS M⟩ f.hom ∧
        AlgebraicStacks.IsSeparated B S hS f ∧ IsQuasiCompactMorphism.{u, w} B S hS f ∧
          UniversalHomeomorphism B S hS f) := by
  classical
  have h𝒳₀ := h𝒳
  -- `h` is unramified (Stacks 0CIW), faithful and representable by algebraic spaces (Stacks 0DU9,
  -- 0DU7), and bijective on automorphism groups
  have hu := isUnramified_of_isEtale B S hS he
  obtain ⟨Ein⟩ :=
    inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt B S hS h hu hauto
  have := Ein.isEquivalence
  have hhf := faithful_homFunctor_of_isDM B S hS h hu.1 hauto
  have hAut : ∀ a : 𝒳'.val.val.obj, Function.Surjective (automorphismGroupMap B S hS h a) :=
    fun a => (Functor.bijective_verticalAutMap 𝒳'.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor h.hom) (CatFiberedInGroupoids.homFunctor_comp_p h.hom)
        a).2
  -- a chart `x : U ⟶ 𝒳` and an affine representing object `V` of `R = U ×_𝒳 U`
  obtain ⟨U, hU, x, hsurj, hflat, hfin, hrfp⟩ := h𝒳
  obtain ⟨V, hV, ⟨eR⟩⟩ := ChartBaseChange.exists_isAffine_representation_rel x hU hfin
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  obtain ⟨s, hs⟩ : ∃ s : V ⟶ U, yoneda.map s = SelfIntersection.relationSourceMap
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) eU eR :=
    ⟨_, yoneda.map_preimage _⟩
  obtain ⟨t, ht⟩ : ∃ t : V ⟶ U, yoneda.map t = SelfIntersection.relationTargetMap
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) eU eR :=
    ⟨_, yoneda.map_preimage _⟩
  let K := WellNighAffineChart.ofRepresentation x hsurj hflat hfin hrfp eR s t hs ht hU hV
  -- the base change `W = 𝒳' ×_𝒳 U` is a scheme, separated and étale over `U`
  obtain ⟨W, eK, fU, hfU, hfUet, hfUsep⟩ :=
    ChartBaseChange.exists_etale_isSeparated_chartBaseChange h x he hsep hauto
  let k : schemeStack.{u, w} B S hS W ⟶ (chartBaseChangeSquare h x).pt :=
    Bicategory.InducedBicategory.mkHom (ChartBaseChange.comparison h x eK)
  have hk : (CatFiberedInGroupoids.homFunctor k.hom).IsEquivalence :=
    eK.toEquivalence.isEquivalence_functor
  obtain ⟨hsurj', hflat', hfin', hrfp'⟩ :=
    chartBaseChange_properties h x k hk hsurj hflat hfin hrfp
  let x' : schemeStack.{u, w} B S hS W ⟶ 𝒳' := k ≫ (chartBaseChangeSquare h x).fst
  let eW := PresheafOfCategories.sliceElementsEquivalenceOver W
  -- `R' = W ×_{𝒳'} W` is represented by `V' = V ×_{s, U} W`
  obtain ⟨V', eR', s', t', fV, hs', ht', hfV, hsq, htq, hs'F, ht'F⟩ :=
    ChartBaseChange.exists_relation'_representation_general h x eK eR s t hs ht
      K.isFiniteLocallyFree_s K.isFiniteLocallyFree_t fU hfU
  obtain ⟨c', hG', hc'⟩ := WellNighAffineChart.exists_composition_transport _ _
    (WellNighAffineChart.relCompositionLaw x' eR')
    (WellNighAffineChart.relCompositionLaw_pointwise x' eR') s' t' hs' ht'
  have hset : (schemeStack.{u, w} B S hS U).val.val.p.IsFiberedInSetoids :=
    SelfIntersection.isFiberedInSetoids_source
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) eU
  have hset' : (schemeStack.{u, w} B S hS W).val.val.p.IsFiberedInSetoids :=
    SelfIntersection.isFiberedInSetoids_source
      (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩) eW
  -- the morphism of groupoid schemes `(W, R', s', t', c') ⟶ (U, R, s, t, c)`
  have hsV : fV ≫ s = s' ≫ fU := ChartBaseChange.comp_eq_of_isPullback_yoneda hsq
  have htV : fV ≫ t = t' ≫ fU := ChartBaseChange.comp_eq_of_isPullback_yoneda htq
  have hrepV : ∀ {X : BigFppfOver B S hS} (z : X ⟶ V'),
      (representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
        (ChartBaseChange.relationMap h x eK)).app (op X) z = z ≫ fV :=
    fun {X} z => (congrArg (fun m => m.app (op X) z) hfV).symm
  have hc : ∀ (X : BigFppfOver B S hS) (a b : X ⟶ V') (hab : a ≫ s' = b ≫ t'),
      Space.representedComp s' t' c' a b hab ≫ fV =
        Space.representedComp s t K.c (a ≫ fV) (b ≫ fV)
          (Space.comp_fV_composable s t s' t' fU fV hsV htV hab) := by
    intro X a b hab
    have e₁ := hc' (op X) ⟨(a, b), hab⟩
    have e₂ := WellNighAffineChart.ofRepresentation_c_app x hsurj hflat hfin hrfp eR s t hs ht
      hU hV (op X) ⟨(a ≫ fV, b ≫ fV), Space.comp_fV_composable s t s' t' fU fV hsV htV hab⟩
    have e₃ := ChartBaseChange.relationMap_compositionLaw h x eK
      (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (R₀' := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) eU eW eR eR' hset hset'
      (W := X) ⟨(a, b), WellNighAffineChart.composable_of_eq hs' ht' ⟨(a, b), hab⟩⟩
    refine (hrepV _).symm.trans ((congrArg (fun z => (representingMap B S hS _ _ (yoneda.obj V')
      (yoneda.obj V) eR' eR (ChartBaseChange.relationMap h x eK)).app (op X) z) e₁).trans
        (e₃.trans ?_))
    refine Eq.trans ?_ e₂.symm
    exact congrArg (fun z => (WellNighAffineChart.relCompositionLaw x eR).app (op X) z)
      (Subtype.ext (Prod.ext (hrepV a) (hrepV b)))
  let G' : Stacks.Groupoids.GroupoidScheme S := Space.representedGroupoidScheme s' t' c' hG'
  let F : Stacks.Groupoids.GroupoidScheme.Hom G' K.groupoidScheme :=
    Space.representedGroupoidSchemeHom s t K.c K.pointwise s' t' c' hG' fU fV hsV htV hc
  have : Stacks.Morphisms.IsFiniteLocallyFree G'.source.left := hs'F
  have : Stacks.Morphisms.IsFiniteLocallyFree G'.target.left := ht'F
  have : Etale F.mapObjects.left := hfUet
  have : _root_.AlgebraicGeometry.IsSeparated F.mapObjects.left := hfUsep
  -- the source, target and stabilizer conditions of Stacks 0DT9
  have hsource : IsPullback F.mapArrows.left G'.source.left
      K.groupoidScheme.source.left F.mapObjects.left :=
    ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda hsq
  have htarget : IsPullback F.mapArrows.left G'.target.left
      K.groupoidScheme.target.left F.mapObjects.left :=
    ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda htq
  have hstabsite : ∀ (X : BigFppfOver B S hS) (v : X ⟶ V'), v ≫ (fV ≫ t) = v ≫ (fV ≫ s) →
      v ≫ t' = v ≫ s' := by
    intro X v hv
    have hv' : (SelfIntersection.relationTargetMap
          (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) eU eR).app (op X)
          ((representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
            (ChartBaseChange.relationMap h x eK)).app (op X) v) =
        (SelfIntersection.relationSourceMap
          (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) eU eR).app (op X)
          ((representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
            (ChartBaseChange.relationMap h x eK)).app (op X) v) := by
      rw [hrepV v, ← ht, ← hs]
      exact (Category.assoc _ _ _).trans (hv.trans (Category.assoc _ _ _).symm)
    have e := ChartBaseChange.relationTarget_eq_relationSource h x eK
      (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (R₀' := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) eU eW eR eR' hAut X v hv'
    rwa [← ht', ← hs'] at e
  have hstabO : ∀ (T : Over S) (r : T ⟶ G'.arrows),
      r ≫ F.mapArrows ≫ K.groupoidScheme.target = r ≫ F.mapArrows ≫ K.groupoidScheme.source →
        r ≫ G'.target = r ≫ G'.source := fun T r hr => by
    have hr' : r ≫ (Space.siteToOver B hS).map (fV ≫ t) =
        r ≫ (Space.siteToOver B hS).map (fV ≫ s) :=
      (congrArg (r ≫ ·) ((Space.siteToOver B hS).map_comp _ _)).trans
        (hr.trans (congrArg (r ≫ ·) ((Space.siteToOver B hS).map_comp _ _)).symm)
    exact Space.comp_eq_of_forall_site B hS (fV ≫ t) (fV ≫ s) t' s' hstabsite r hr'
  have hsrc : ∀ {T : Scheme.{u}} (r : T ⟶ G'.arrows.left),
      (r ≫ F.mapArrows.left) ≫ K.groupoidScheme.source.left =
        (r ≫ F.mapArrows.left) ≫ K.groupoidScheme.target.left →
      r ≫ G'.source.left = r ≫ G'.target.left := by
    intro T r hr
    have e := hstabO (Over.mk (r ≫ G'.arrows.hom)) (Over.homMk r rfl) (by
      ext
      simpa only [Over.comp_left, Over.homMk_left, Category.assoc] using hr.symm)
    simpa only [Over.comp_left, Over.homMk_left] using (congrArg CommaMorphism.left e).symm
  -- a cover of `W` by `R'`-invariant affine opens (Stacks 07S0, 03JE)
  let I := {Q : G'.objects.left.affineOpens // Stacks.Groupoids.IsInvariantOpen G' Q.1}
  let Q : I → G'.objects.left.Opens := fun i => i.1.1
  have hQ : ∀ i, Stacks.Groupoids.IsInvariantOpen G' (Q i) := fun i => i.2
  have hQa : ∀ i, IsAffineOpen (Q i) := fun i => i.1.2
  have hcov : ∀ w, ∃ i, w ∈ Q i := fun w => by
    obtain ⟨Q₀, hQ₀, hQ₀a, hw⟩ :=
      GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_of_etale G' F.mapObjects.left w
    exact ⟨⟨⟨Q₀, hQ₀a⟩, hQ₀⟩, hw⟩
  -- the glued scheme `Y`, étale and separated over `M`, with `W = Y ×_M U`
  let D : Scheme.GlueDataOverBase ((BigFppfOver.toScheme B S hS).obj K.moduliObject) :=
    glueData G' Q hQ hQa F hsource htarget hsrc
  have hJ : Cardinal.mk D.J < B.cutoff :=
    lt_of_le_of_lt ((Cardinal.mk_subtype_le _).trans
      (Scheme.mk_affineOpens_le_size G'.objects.left)) W.left.2
  let Y := D.siteObj hJ W.left.2 (size_pieceSpec_le G' Q hQ hQa)
  let gM : Y ⟶ K.moduliObject := D.siteToBase hJ W.left.2 (size_pieceSpec_le G' Q hQ hQa)
  have hgM : (BigFppfOver.toScheme B S hS).map gM = D.toBase := rfl
  have hpbS := isPullback_gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov
  let qO : (Space.siteToOver B hS).obj W ⟶ (Space.siteToOver B hS).obj Y :=
    Over.homMk (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov) (by
      have e : gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov ≫
          (glueData G' Q hQ hQa F hsource htarget hsrc).toBase ≫
            GroupoidScheme.invariantSpectrumToBase K.groupoidScheme = G'.objects.hom := by
        rw [← Category.assoc, hpbS.w, Category.assoc,
          GroupoidScheme.objectsToInvariantSpectrum_comp_invariantSpectrumToBase]
        exact Over.w F.mapObjects
      exact e)
  let q' : W ⟶ Y := (Space.siteToOver B hS).preimage qO
  have hq'S : (BigFppfOver.toScheme B S hS).map q' =
      gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov :=
    congrArg Over.Hom.left ((Space.siteToOver B hS).map_preimage qO)
  have hpb' : IsPullback ((BigFppfOver.toScheme B S hS).map fU)
      ((BigFppfOver.toScheme B S hS).map q')
      ((BigFppfOver.toScheme B S hS).map K.quotientMap) ((BigFppfOver.toScheme B S hS).map gM) :=
    ChartBaseChange.isPullback_of_eq hpbS.flip rfl hq'S K.toScheme_map_quotientMap hgM
  have hH2 := ChartBaseChange.isPullback_yoneda_of_isPullback_toScheme hpb'
  have hgEt : Etale ((BigFppfOver.toScheme B S hS).map gM) :=
    etale_toBase G' Q hQ hQa F hsource htarget hsrc
  have hgSep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map gM) :=
    isSeparated_toBase G' Q hQ hQa F hsource htarget hsrc hcov
  -- the invariant morphism `W ⟶ Y` descends to `f' : 𝒳' ⟶ Y` (Stacks 0DUH)
  have hinv : yoneda.map s' ≫ yoneda.map q' = yoneda.map t' ≫ yoneda.map q' := by
    rw [← yoneda.map_comp, ← yoneda.map_comp]
    congr 1
    apply (Space.siteToOver B hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage]
    exact Over.OverMorphism.ext (source_comp_gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov)
  obtain ⟨g', hg'⟩ := (WellNighAffineChart.ofRepresentation_props x' hsurj' hflat' hfin' hrfp'
    eR' s' t' hs' ht').2.2.2.1 ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩
    (yoneda.map q') hinv
  let f' : 𝒳' ⟶
      algebraicSpaceStack.{u, w} B S hS (yoneda.obj Y) (isAlgebraicSpace_yoneda B S hS Y) :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom g')
  -- the square commutes and is cartesian (the argument of Stacks 0DUQ)
  have hq := K.chart_comp_moduliMap
  have hx := WellNighAffineChart.locallyEssSurjOnFibers_chart x hsurj hflat hfin hrfp
  have hx' := WellNighAffineChart.locallyEssSurjOnFibers_chart x' hsurj' hflat' hfin' hrfp'
  have hw : fU ≫ K.quotientMap = q' ≫ gM := ChartBaseChange.comp_eq_of_isPullback_yoneda hH2
  have hcomm := ChartBaseChange.moduliSquare_comm h x eK gM K.moduliMap.hom f'.hom fU hfU
    K.quotientMap q' hq hg' hw (fun D₁ D₂ hD =>
      WellNighAffineChart.eq_of_chart_comp_eq x' hsurj' hflat' hfin' hrfp' eR' s' t' hs' ht'
        ⟨yoneda.obj K.moduliObject, isAlgebraicSpace_yoneda B S hS _⟩ D₁ D₂ hD)
  exact ⟨K.moduliObject, Y, K.moduliMap, f', gM, hcomm, hgEt, hgSep,
    ChartBaseChange.nonempty_isTwoFibreProduct_moduliSquare h x eK (gM := gM)
      (f := K.moduliMap.hom) (f' := f'.hom) (hcomm := hcomm) fU
      hfU K.quotientMap q' hq hg' hH2 hx hx' hhf
      (ChartBaseChange.exists_preimage_of_relation h x eK gM f'.hom fU hfU K.quotientMap q' hg'
        hH2 eR eR' s t s' t' fV hs ht hs' ht' hfV hsq htq),
    ⟨K.isUniformCategoricalModuliSpaceIn_moduliMap, K.isSeparated_moduliMap h𝒳₀,
      K.isQuasiCompactMorphism_moduliMap, K.universalHomeomorphism_moduliMap⟩⟩

end Main

end AlgebraicGeometry.Stack

end
