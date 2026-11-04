module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeFullness
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRepresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineChartOfRepresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentedGroupoidSchemeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SiteToOverEqualizerTest
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.PullbackCriterion
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleInvariantRingMapAssembly

/-!
# An étale stabilizer-preserving morphism of well-nigh affine stacks (Stacks 0DUQ)

Let `h : 𝒳' ⟶ 𝒳` be an étale morphism of well-nigh affine algebraic stacks inducing isomorphisms
on automorphism groups. Then the square
```
𝒳' ⟶ 𝒳
↓     ↓
M' ⟶ M
```
of the moduli spaces of Stacks 0DUP is cartesian, with `M' ⟶ M` étale.

The proof follows the source. `h` is representable by algebraic spaces (Stacks 0DU9, 0DU7). For a
chart `x : U ⟶ 𝒳` with affine relation `R = U ×_𝒳 U` represented by `V`, the base change
`U' = 𝒳' ×_𝒳 U` is affine (Stacks 0DUN) and its relation `R'` is represented by `V ×_{s, U} U'`.
The pair `(U' ⟶ U, R' ⟶ R)` is a morphism of groupoid schemes whose source, target and stabilizer
squares are cartesian; Stacks 0DT9 makes `M' = Spec C' ⟶ M = Spec C` étale with
`U' = M' ×_M U`, and the square of stacks is then cartesian
(`AlgebraicGeometry.Stack.ChartBaseChange.nonempty_isTwoFibreProduct_moduliSquare`).

## Main results

* `exists_isTwoFibreProduct_moduliSpace_of_isEtale_of_inducesIsomorphismAt`:
  **Stacks 0DUQ**.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

/-- Transport of a cartesian square along equalities of its four sides. -/
theorem isPullback_of_eq {C : Type*} [Category C] {P X Y Z : C} {a a' : P ⟶ X} {b b' : P ⟶ Y}
    {c c' : X ⟶ Z} {d d' : Y ⟶ Z} (h : IsPullback a b c d) (ha : a' = a) (hb : b' = b)
    (hc : c' = c) (hd : d' = d) : IsPullback a' b' c' d' := by
  subst ha hb hc hd
  exact h

/-- A cartesian square of the underlying schemes of objects of the site is a cartesian square of
schemes over `S`. -/
theorem isPullback_siteToOver_of_isPullback_toScheme {P X Y Z : BigFppfOver B S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map d)) :
    IsPullback ((Space.siteToOver B hS).map a) ((Space.siteToOver B hS).map b)
      ((Space.siteToOver B hS).map c) ((Space.siteToOver B hS).map d) := by
  have hw : (Space.siteToOver B hS).map a ≫ (Space.siteToOver B hS).map c =
      (Space.siteToOver B hS).map b ≫ (Space.siteToOver B hS).map d :=
    Over.OverMorphism.ext h.w
  exact IsPullback.of_map (Over.forget S) hw h

/-- A cartesian square of the underlying schemes of objects of the site is a cartesian square of
represented presheaves. -/
theorem isPullback_yoneda_of_isPullback_toScheme {P X Y Z : BigFppfOver B S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map d)) :
    IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map d) := by
  have hO := isPullback_siteToOver_of_isPullback_toScheme h
  have hw : a ≫ c = b ≫ d := (Space.siteToOver B hS).map_injective
    (((Space.siteToOver B hS).map_comp _ _).trans
      (hO.w.trans ((Space.siteToOver B hS).map_comp _ _).symm))
  exact (IsPullback.of_map (Space.siteToOver B hS) hw hO).map yoneda

/-- A cartesian square of represented presheaves commutes on the underlying morphisms. -/
private theorem comp_eq_of_isPullback_yoneda {P X Y Z : BigFppfOver B S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map d)) :
    a ≫ c = b ≫ d :=
  yoneda.map_injective (by simpa only [Functor.map_comp] using h.w)

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}

/-- **The self-intersection of a finite chart from an affine object is represented by an affine
object of the site.** -/
theorem exists_isAffine_representation_rel (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hfin : AlgebraicStacks.IsFinite B S hS x) :
    ∃ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver (rel x).val.p
        (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) := by
  obtain ⟨hrep, hfinR⟩ := hfin
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    (schemeStack.{u, w} B S hS U).val
  let F : 𝒰 ⟶ 𝒳.val := x.hom
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
  have ht₀ : Space.IsFinite B S hS (SelfIntersection.relationTarget eU eR₀').hom :=
    SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ R₀ eU eR₀'
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨V, p, i, hV, -, hpb⟩ := ht₀ U hU (𝟙 _)
  have hi : IsIso i := hpb.flip.isIso_snd_of_isIso
  exact ⟨V, hV, ⟨eR₀'.trans (PresheafOfCategories.equivalenceOverOfIso (asIso i).symm)⟩⟩

/-- An object `(z.left, φ z.hom)` of the category attached to a presheaf, for `z` over `U` with
`z.left = T` naming the section `a`, is `(T, φ a)`. -/
theorem fibredCategory_mk_eq_of_section {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Over U)
    {T : BigFppfOver B S hS} (hz : z.left = T) (a : T ⟶ U) (ha : eqToHom hz.symm ≫ z.hom = a)
    (φ : yoneda.obj U ⟶ G) :
    (⟨z.left, Discrete.mk (φ.app (op z.left) z.hom)⟩ : (fibredCategory B S hS G).val.obj) =
      ⟨T, Discrete.mk (φ.app (op T) a)⟩ := by
  obtain ⟨zl, ⟨⟨⟩⟩, zh⟩ := z
  change zl = T at hz
  subst hz
  change eqToHom rfl ≫ zh = a at ha
  rw [eqToHom_refl, Category.id_comp] at ha
  subst ha
  rfl

section Comm

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U W : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)
  {M M' : BigFppfOver B S hS} (gM : M' ⟶ M)
  (f : 𝒳.val ⟶ fibredCategory B S hS (yoneda.obj M))
  (f' : 𝒳'.val ⟶ fibredCategory B S hS (yoneda.obj M'))

/-- **The square of moduli maps commutes**, when it does on the charts and the 1-morphisms out
of `𝒳'` to `M` are determined by their restriction to the chart `x'`. -/
theorem moduliSquare_comm (fU : W ⟶ U)
    (hfU : yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK))
    (q : U ⟶ M) (q' : W ⟶ M')
    (hq : BasedFunctor.comp x.hom.hom f.hom = BasedFunctor.comp (sliceElementsComparison B S hS U)
      (associatedMap B S hS (yoneda.map q)).1.hom)
    (hq' : BasedFunctor.comp (chart' h x eK).hom f'.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS W)
        (associatedMap B S hS (yoneda.map q')).1.hom)
    (hw : fU ≫ q = q' ≫ gM)
    (huniq : ∀ D₁ D₂ : 𝒳'.val.val ⥤ᵇ (fibredCategory B S hS (yoneda.obj M)).val,
      BasedFunctor.comp (chart' h x eK).hom D₁ = BasedFunctor.comp (chart' h x eK).hom D₂ →
        D₁ = D₂) :
    f' ≫ (associatedMap B S hS (yoneda.map gM)).1 = h.hom ≫ f := by
  have hset : (fibredCategory B S hS (yoneda.obj M)).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection (yoneda.obj M)).IsFiberedInSets
  let K := eK.hom.functor
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let eW := PresheafOfCategories.sliceElementsEquivalenceOver W
  apply Bicategory.InducedBicategory.hom_ext
  apply huniq
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _
    (BasedFunctor.comp (chart' h x eK).hom
      (f' ≫ (associatedMap B S hS (yoneda.map gM)).1).hom).w
    (BasedFunctor.comp (chart' h x eK).hom (h.hom ≫ f).hom).w (fun o => ?_)
  -- the left side, through `x' ≫ f' = q'`
  have e₁ : f'.hom.obj ((chart' h x eK).hom.obj o) =
      ⟨o.left, Discrete.mk ((yoneda.map q').app (op o.left) o.hom)⟩ :=
    (congrArg (fun L => L.obj o) hq').trans (comp_sliceElementsComparison_obj _ o)
  have eL : (associatedMap B S hS (yoneda.map gM)).1.hom.obj
      (f'.hom.obj ((chart' h x eK).hom.obj o)) =
      ⟨o.left, Discrete.mk ((yoneda.map gM).app (op o.left)
        ((yoneda.map q').app (op o.left) o.hom))⟩ :=
    (congrArg (associatedMap B S hS (yoneda.map gM)).1.hom.obj e₁).trans
      (associatedMap_obj B S hS _ _)
  -- the right side, through the comparison `h ∘ x' ≅ x ∘ f` and `x ≫ f = q`
  have e₂ : f.hom.obj (h.hom.hom.obj ((chart' h x eK).hom.obj o)) =
      f.hom.obj (x.hom.hom.obj ((chartMap h x eK).hom.obj o)) :=
    obj_eq_of_isHomLift_id_fibredCategory f.hom ((chartIso h x eK).hom.app o)
      (isHomLift_chartIso h x eK o)
  have e₃ : f.hom.obj (x.hom.hom.obj ((chartMap h x eK).hom.obj o)) =
      ⟨((chartMap h x eK).hom.obj o).left, Discrete.mk ((yoneda.map q).app
        (op ((chartMap h x eK).hom.obj o).left) ((chartMap h x eK).hom.obj o).hom)⟩ :=
    (congrArg (fun L => L.obj ((chartMap h x eK).hom.obj o)) hq).trans
      (comp_sliceElementsComparison_obj _ _)
  have hz : ((chartMap h x eK).hom.obj o).left = o.left :=
    (K.obj o).hy.trans (comparison_base h x eK o)
  have hsec : eqToHom hz.symm ≫ ((chartMap h x eK).hom.obj o).hom = o.hom ≫ fU := by
    have e := representingMap_app_sectionOfObj eW eU (chartMap h x eK) o rfl
    have e' := (congrArg (fun m => m.app (op o.left)
      (PresheafOfCategories.sectionOfObj eW o rfl)) hfU).trans e
    have a₁ := sectionOfObj_sliceElementsEquivalenceOver' ((chartMap h x eK).hom.obj o) hz
    have a₂ : PresheafOfCategories.sectionOfObj eW o rfl = o.hom :=
      (sectionOfObj_sliceElementsEquivalenceOver' o rfl).trans (by simp)
    exact a₁.symm.trans (e'.symm.trans
      (congrArg (fun y => (yoneda.map fU).app (op o.left) y) a₂))
  have e₄ := fibredCategory_mk_eq_of_section (G := yoneda.obj M) _ hz _ hsec (yoneda.map q)
  have e₅ : (⟨o.left, Discrete.mk ((yoneda.map q).app (op o.left) (o.hom ≫ fU))⟩ :
      (fibredCategory B S hS (yoneda.obj M)).val.obj) =
      ⟨o.left, Discrete.mk ((yoneda.map gM).app (op o.left)
        ((yoneda.map q').app (op o.left) o.hom))⟩ := by
    congr 2
    exact (Category.assoc _ _ _).trans ((congrArg (o.hom ≫ ·) hw).trans
      (Category.assoc _ _ _).symm)
  exact eL.trans (e₅.symm.trans (e₄.symm.trans (e₃.symm.trans e₂.symm)))

end Comm

end ChartBaseChange

section Main

variable (B S hS)

/-- **Stacks 0DUQ.** Let `h : 𝒳' ⟶ 𝒳` be a morphism of algebraic stacks. Assume `𝒳'` and `𝒳` are
well-nigh affine, `h` is étale, and `h` induces isomorphisms on automorphism groups (Stacks 0DTW).
Then there exists a cartesian diagram
```
𝒳' ⟶ 𝒳
↓     ↓
M' ⟶ M
```
where `M' ⟶ M` is étale and the vertical arrows are moduli spaces as constructed in Stacks 0DUP:
uniform categorical moduli spaces in affine schemes, separated, quasi-compact and universal
homeomorphisms. -/
@[stacks 0DUQ]
theorem exists_isTwoFibreProduct_moduliSpace_of_isEtale_of_inducesIsomorphismAt
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) (h𝒳' : IsWellNighAffine.{u, w} B S hS 𝒳')
    (he : IsEtale B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q) :
    ∃ (M M' : BigFppfOver B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj M) (isAlgebraicSpace_yoneda B S hS M))
      (f' : 𝒳' ⟶
        algebraicSpaceStack.{u, w} B S hS (yoneda.obj M') (isAlgebraicSpace_yoneda B S hS M'))
      (g : M' ⟶ M) (hcomm : f'.hom ≫ (associatedMap B S hS (yoneda.map g)).1 = h.hom ≫ f.hom),
      Etale ((BigFppfOver.toScheme B S hS).map g) ∧
      Nonempty (Bicategory.IsTwoFibreProduct
        (ChartBaseChange.moduliSquare h g f.hom f'.hom hcomm)) ∧
      (IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj)
          (schemeSpace M) f.hom ∧
        AlgebraicStacks.IsSeparated B S hS f ∧ IsQuasiCompactMorphism.{u, w} B S hS f ∧
          UniversalHomeomorphism B S hS f) ∧
      (IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj)
          (schemeSpace M') f'.hom ∧
        AlgebraicStacks.IsSeparated B S hS f' ∧ IsQuasiCompactMorphism.{u, w} B S hS f' ∧
          UniversalHomeomorphism B S hS f') := by
  classical
  have h𝒳₀ := h𝒳
  -- `h` is unramified (Stacks 0CIW), faithful and representable by algebraic spaces (Stacks 0DU9,
  -- 0DU7), and bijective on automorphism groups
  have hu := isUnramified_of_isEtale B S hS he
  have hhf := faithful_homFunctor_of_isDM B S hS h hu.1 hauto
  have hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom :=
    AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful B S hS h hhf
  obtain ⟨Ein⟩ :=
    inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt B S hS h hu hauto
  have := Ein.isEquivalence
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
  -- the base change `U' = 𝒳' ×_𝒳 U` is affine (Stacks 0DUN), with chart `x' : U' ⟶ 𝒳'`
  obtain ⟨W, hW, ⟨eK⟩⟩ := exists_isAffine_equivalenceOver_chartBaseChange h x hrep h𝒳' hfin
  let k : schemeStack.{u, w} B S hS W ⟶ (chartBaseChangeSquare h x).pt :=
    Bicategory.InducedBicategory.mkHom (ChartBaseChange.comparison h x eK)
  have hk : (CatFiberedInGroupoids.homFunctor k.hom).IsEquivalence :=
    eK.toEquivalence.isEquivalence_functor
  obtain ⟨hsurj', hflat', hfin', hrfp'⟩ :=
    chartBaseChange_properties h x k hk hsurj hflat hfin hrfp
  let x' : schemeStack.{u, w} B S hS W ⟶ 𝒳' := k ≫ (chartBaseChangeSquare h x).fst
  let eW := PresheafOfCategories.sliceElementsEquivalenceOver W
  obtain ⟨fU, hfU⟩ : ∃ fU : W ⟶ U, yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W)
      (yoneda.obj U) eW eU (ChartBaseChange.chartMap h x eK) := ⟨_, yoneda.map_preimage _⟩
  -- `R' = U' ×_{𝒳'} U'` is represented by the affine `V' = V ×_{s, U} U'`
  obtain ⟨V', eR', s', t', fV, hs', ht', hfV, hsq, htq, hV', -, -⟩ :=
    ChartBaseChange.exists_relation'_representation h x eK eR s t hs ht K.isFiniteLocallyFree_s
      K.isFiniteLocallyFree_t hW fU hfU
  let K' := WellNighAffineChart.ofRepresentation x' hsurj' hflat' hfin' hrfp' eR' s' t' hs' ht'
    hW hV'
  have hset : (schemeStack.{u, w} B S hS U).val.val.p.IsFiberedInSetoids :=
    SelfIntersection.isFiberedInSetoids_source
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) eU
  have hset' : (schemeStack.{u, w} B S hS W).val.val.p.IsFiberedInSetoids :=
    SelfIntersection.isFiberedInSetoids_source
      (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩) eW
  -- the morphism of groupoid schemes `(U', R', s', t', c') ⟶ (U, R, s, t, c)`
  have hsV : fV ≫ s = s' ≫ fU := ChartBaseChange.comp_eq_of_isPullback_yoneda hsq
  have htV : fV ≫ t = t' ≫ fU := ChartBaseChange.comp_eq_of_isPullback_yoneda htq
  have hrepV : ∀ {X : BigFppfOver B S hS} (z : X ⟶ V'),
      (representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
        (ChartBaseChange.relationMap h x eK)).app (op X) z = z ≫ fV :=
    fun {X} z => (congrArg (fun m => m.app (op X) z) hfV).symm
  have hc : ∀ (X : BigFppfOver B S hS) (a b : X ⟶ V') (hab : a ≫ s' = b ≫ t'),
      Space.representedComp s' t' K'.c a b hab ≫ fV =
        Space.representedComp s t K.c (a ≫ fV) (b ≫ fV)
          (Space.comp_fV_composable s t s' t' fU fV hsV htV hab) := by
    intro X a b hab
    have e₁ := WellNighAffineChart.ofRepresentation_c_app x' hsurj' hflat' hfin' hrfp' eR' s' t'
      hs' ht' hW hV' (op X) ⟨(a, b), hab⟩
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
  let F : Stacks.Groupoids.GroupoidScheme.Hom K'.groupoidScheme K.groupoidScheme :=
    Space.representedGroupoidSchemeHom s t K.c K.pointwise s' t' K'.c K'.pointwise fU fV hsV htV hc
  -- the three cartesian squares of Stacks 0DT9
  have hsource : IsPullback F.mapArrows.left K'.groupoidScheme.source.left
      K.groupoidScheme.source.left F.mapObjects.left :=
    ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda hsq
  have htarget : IsPullback F.mapArrows.left K'.groupoidScheme.target.left
      K.groupoidScheme.target.left F.mapObjects.left :=
    ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda htq
  have hsourceO : IsPullback F.mapArrows K'.groupoidScheme.source K.groupoidScheme.source
      F.mapObjects :=
    ChartBaseChange.isPullback_siteToOver_of_isPullback_toScheme hsource
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
  have hstab := isPullback_stabilizerMap_left_of_isPullback_source F hsourceO
    (fun T r hr => by
      have hr' : r ≫ (Space.siteToOver B hS).map (fV ≫ t) =
          r ≫ (Space.siteToOver B hS).map (fV ≫ s) :=
        (congrArg (r ≫ ·) ((Space.siteToOver B hS).map_comp _ _)).trans
          (hr.trans (congrArg (r ≫ ·) ((Space.siteToOver B hS).map_comp _ _)).symm)
      exact Space.comp_eq_of_forall_site B hS (fV ≫ t) (fV ≫ s) t' s' hstabsite r hr')
  have : Etale F.mapObjects.left :=
    ChartBaseChange.etale_toScheme_map_of_chartMap h x eK hrep he fU hfU
  -- Stacks 0DT9: `C ⟶ C'` is étale and `U' = M' ×_M U`
  have hEt := AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap F hsource htarget hstab
  have hpb := AlgebraicGeometry.GroupoidScheme.isPullback_mapObjects F hsource htarget hstab
  have hover : Spec.map (CommRingCat.ofHom (AlgebraicGeometry.GroupoidScheme.invariantRingMap F)) ≫
      AlgebraicGeometry.GroupoidScheme.invariantSpectrumToBase K.groupoidScheme =
        AlgebraicGeometry.GroupoidScheme.invariantSpectrumToBase K'.groupoidScheme := by
    apply AlgebraicGeometry.GroupoidScheme.ext_of_comp_objectsToInvariantSpectrum
      K'.groupoidScheme
    rw [← Category.assoc, ← hpb.w, Category.assoc,
      AlgebraicGeometry.GroupoidScheme.objectsToInvariantSpectrum_comp_invariantSpectrumToBase,
      AlgebraicGeometry.GroupoidScheme.objectsToInvariantSpectrum_comp_invariantSpectrumToBase]
    exact Over.w F.mapObjects
  let gO : Over.mk (AlgebraicGeometry.GroupoidScheme.invariantSpectrumToBase K'.groupoidScheme) ⟶
      Over.mk (AlgebraicGeometry.GroupoidScheme.invariantSpectrumToBase K.groupoidScheme) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (AlgebraicGeometry.GroupoidScheme.invariantRingMap F)))
      hover
  let gM : K'.moduliObject ⟶ K.moduliObject := (Space.siteToOver B hS).preimage gO
  have hgM : (BigFppfOver.toScheme B S hS).map gM =
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.GroupoidScheme.invariantRingMap F)) :=
    congrArg Over.Hom.left
      ((Space.siteToOver B hS).map_preimage (X := K'.moduliObject) (Y := K.moduliObject) gO)
  have hpb' : IsPullback ((BigFppfOver.toScheme B S hS).map fU)
      ((BigFppfOver.toScheme B S hS).map K'.quotientMap)
      ((BigFppfOver.toScheme B S hS).map K.quotientMap) ((BigFppfOver.toScheme B S hS).map gM) :=
    ChartBaseChange.isPullback_of_eq hpb rfl K'.toScheme_map_quotientMap
      K.toScheme_map_quotientMap hgM
  have hH2 := ChartBaseChange.isPullback_yoneda_of_isPullback_toScheme hpb'
  have hgEt : Etale ((BigFppfOver.toScheme B S hS).map gM) := by
    rw [hgM]
    exact HasRingHomProperty.Spec_iff.mpr hEt
  -- the moduli maps, their restrictions to the charts, and the cartesian square
  have hq := K.chart_comp_moduliMap
  have hq' := K'.chart_comp_moduliMap
  have hx := WellNighAffineChart.locallyEssSurjOnFibers_chart x hsurj hflat hfin hrfp
  have hx' := WellNighAffineChart.locallyEssSurjOnFibers_chart x' hsurj' hflat' hfin' hrfp'
  have hw : fU ≫ K.quotientMap = K'.quotientMap ≫ gM :=
    ChartBaseChange.comp_eq_of_isPullback_yoneda hH2
  have hcomm := ChartBaseChange.moduliSquare_comm h x eK gM K.moduliMap.hom K'.moduliMap.hom fU hfU
    K.quotientMap K'.quotientMap hq hq' hw (fun D₁ D₂ hD =>
      WellNighAffineChart.eq_of_chart_comp_eq x' hsurj' hflat' hfin' hrfp' eR' s' t' hs' ht'
        ⟨yoneda.obj K.moduliObject, isAlgebraicSpace_yoneda B S hS _⟩ D₁ D₂ hD)
  have hH3 := fun T w₁ w₂ hw α hα =>
    ChartBaseChange.exists_preimage_of_relation h x eK gM K'.moduliMap.hom fU
    hfU K.quotientMap K'.quotientMap hq' hH2 eR eR' s t s' t' fV hs ht hs' ht' hfV hsq htq T w₁
    w₂ hw α hα
  exact ⟨K.moduliObject, K'.moduliObject, K.moduliMap, K'.moduliMap, gM, hcomm, hgEt,
    ChartBaseChange.nonempty_isTwoFibreProduct_moduliSquare h x eK (gM := gM)
      (f := K.moduliMap.hom) (f' := K'.moduliMap.hom) (hcomm := hcomm) fU
      hfU K.quotientMap K'.quotientMap hq hq' hH2 hx hx' hhf hH3,
    ⟨K.isUniformCategoricalModuliSpaceIn_moduliMap, K.isSeparated_moduliMap h𝒳₀,
      K.isQuasiCompactMorphism_moduliMap, K.universalHomeomorphism_moduliMap⟩,
    ⟨K'.isUniformCategoricalModuliSpaceIn_moduliMap, K'.isSeparated_moduliMap h𝒳',
      K'.isQuasiCompactMorphism_moduliMap, K'.universalHomeomorphism_moduliMap⟩⟩

end Main

end AlgebraicGeometry.Stack

end
