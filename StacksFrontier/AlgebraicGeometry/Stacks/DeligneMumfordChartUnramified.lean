module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordEtaleCoverAssembly
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# The two projections of an étale chart of `W ×_𝒳 W` are jointly unramified

Let `𝒳` be an algebraic stack over `S` which is DM over `S` (Stacks 050D), `b : W ⟶ 𝒳` a
1-morphism from a scheme of the site, and `c : E ⟶ W ×_𝒳 W` an étale 1-morphism from a scheme of
the site whose composites with the two projections are induced by morphisms `s, t : E ⟶ W` of the
site. Then the morphism of schemes `(s, t) : E ⟶ W ×_S W` is unramified.

This is the input the étale slices of the proof of Stacks 06N3 are cut with. The argument: by
Stacks 050H, part (4), the comparison `W ×_𝒳 W ⟶ W ×_S W` is unramified, since the structure
morphism of `𝒳` is DM; `c` is étale, hence unramified; so `W ×_𝒳 W`'s chart `E ⟶ W ×_S W` is
unramified in the sense of Stacks 04XB. The 2-fibre product `W ×_S W` of represented stacks is
represented by the product `W ⨯ W` of the site
(`AlgebraicGeometry.Stack.isEquivalence_schemeStackProdFunctor`), and the composite is
2-isomorphic to the 1-morphism induced by `(s, t)`, because 2-cells into the stack represented
by `S` are unique. Stacks 0457 and the bridge of Stacks 04XB then give unramifiedness of the
morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.unramified_of_isUnramified_yonedaMap`: the scheme-level bridge.
* `AlgebraicGeometry.Stack.unramified_of_hasRelativeProperty_schemeFibredCategoryMap`.
* `AlgebraicGeometry.Stack.unramified_prodLift_of_isDMOver`.
* `AlgebraicGeometry.Stack.unramifiedAt_pullbackLift_of_isDMOver`: the same with the product
  taken over `Spec ℤ` in the category of schemes, the shape the slice lemma
  `Stacks.AlgebraicGeometry.exists_etale_slice_of_unramified_pair` consumes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Unramifiedness of a morphism of representable algebraic spaces is unramifiedness of the
morphism of schemes.** The chart condition of Stacks 03ZH, tested at the identity charts. -/
theorem unramified_of_isUnramified_yonedaMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : IsUnramified B S hS (yoneda.map g)) :
    Unramified ((BigFppfOver.toScheme B S hS).map g) :=
  hg U V (yoneda.map (𝟙 U)) (yoneda.map (𝟙 V)) g
    ((presheaf_yoneda_map_etale_iff B S hS (𝟙 U)).2
      (by simpa using inferInstanceAs (Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj U)))))
    ((presheaf_yoneda_map_etale_iff B S hS (𝟙 V)).2
      (by simpa using inferInstanceAs (Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj V)))))
    (by simp)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Unramifiedness of morphisms of algebraic spaces is local at the target for the fppf
precoverage. -/
private theorem isLocalAtTarget_unramified_fppf :
    (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
  (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
    (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)

/-- **A morphism of the site inducing an unramified 1-morphism is unramified**: the bridge of
Stacks 04XB at unramifiedness. -/
theorem unramified_of_hasRelativeProperty_schemeFibredCategoryMap {U V : BigFppfOver B S hS}
    (g : U ⟶ V)
    (h : haveI : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
        Space.isUnramified_isStableUnderBaseChange B S hS
      haveI : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
        (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
          (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.unramifiedMorphismProperty B S hS)
        (schemeFibredCategoryMap B S hS g)
        (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)) :
    Unramified ((BigFppfOver.toScheme B S hS).map g) := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have := isLocalAtTarget_unramified_fppf B S hS
  have h' := (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.unramifiedMorphismProperty B S hS) (schemeFibredCategoryMap B S hS g)
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)
    (yoneda.obj U) (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_yoneda B S hS V)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver V)).1 h
  change Space.IsUnramified B S hS _ at h'
  rw [representingMap_schemeFibredCategoryMap] at h'
  exact Space.unramified_of_isUnramified_yonedaMap B S hS g h'

/-- **2-cells into a represented category are unique**: its structure functor, the forgetful
functor of a slice, is faithful and the components of a 2-cell are vertical. -/
theorem twoCell_ext_schemeFibredCategory
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} {V : BigFppfOver B S hS}
    {f g : 𝒜 ⟶ schemeFibredCategory B S hS V} (α β : f ⟶ g) : α = β := by
  have : (schemeFibredCategory B S hS V).val.p.Faithful := inferInstanceAs (Over.forget V).Faithful
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ ?_)
  ext a
  refine (schemeFibredCategory B S hS V).val.p.map_injective ?_
  rw [IsHomLift.fac' (schemeFibredCategory B S hS V).val.p (𝟙 (𝒜.val.p.obj a))
      (α.hom.toNatTrans.app a),
    IsHomLift.fac' (schemeFibredCategory B S hS V).val.p (𝟙 (𝒜.val.p.obj a))
      (β.hom.toNatTrans.app a)]

/-- The represented product `W ⨯ W` of the site as the 2-fibre product of `W` with itself over
the stack represented by `S`, along any 1-morphism equal to the structure morphism of `W`: an
equivalence whose two projections are the 1-morphisms induced by the two projections of the
product. -/
theorem exists_schemeStackProd_equivalence (W : BigFppfOver B S hS)
    (k : schemeStack.{u, w} B S hS W ⟶ schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))
    (hk : structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS W) = k) :
    ∃ e : schemeStack.{u, w} B S hS (W ⨯ W) ⟶ twoFibreProductAlgebraicStack B S hS k k,
      e.hom.hom.toFunctor.IsEquivalence ∧
      e.hom ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          k.hom k.hom).fst = schemeFibredCategoryMap B S hS prod.fst ∧
      e.hom ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          k.hom k.hom).snd = schemeFibredCategoryMap B S hS prod.snd := by
  subst hk
  exact ⟨schemeStackProdHom.{u, w} B S hS W W,
    isEquivalence_schemeStackProdFunctor.{u, w} B S hS W W, rfl, rfl⟩

/-- **The two projections of an étale chart of `W ×_𝒳 W` are jointly unramified.** Let `𝒳` be
DM over `S`, `b : W ⟶ 𝒳` a 1-morphism from a scheme of the site, and `c : E ⟶ W ×_𝒳 W` an étale
1-morphism from a scheme of the site whose composites with the two projections are induced by
`s, t : E ⟶ W`. Then `(s, t) : E ⟶ W ×_S W` is an unramified morphism of schemes. -/
theorem unramified_prodLift_of_isDMOver (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsDMOver.{u, w} B S hS 𝒳) {W E : BigFppfOver B S hS}
    (b : schemeFibredCategory B S hS W ⟶ 𝒳.val)
    (c : schemeFibredCategory B S hS E ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).pt)
    (hc : IsRelativelyEtale B S hS c) (s t : E ⟶ W)
    (es : schemeFibredCategoryMap B S hS s ≅
      c ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).fst)
    (et : schemeFibredCategoryMap B S hS t ≅
      c ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).snd) :
    Unramified ((BigFppfOver.toScheme B S hS).map (prod.lift s t)) := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have := isLocalAtTarget_unramified_fppf B S hS
  let Q₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b
  let b' : schemeStack.{u, w} B S hS W ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom b
  let h := structureMorphism.{u, w} B S hS 𝒳
  let cmp := comparison B S hS b' b' h
  have hcmprep := isRepresentableByAlgebraicSpaces_comparison B S hS b' b' h
  have hcmpU := isUnramified_comparison B S hS b' b' h h𝒳
  have hcU := hasRelativeProperty_unramified_of_isRelativelyEtale B S hS hc hc.1
  let ψ := c ≫ cmp.hom
  have hψrep : IsRepresentableByAlgebraicSpaces B S hS ψ.hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS c cmp.hom hc.1 hcmprep
  have hψU : HasRelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) ψ hψrep :=
    hasRelativeProperty_comp B S hS (Space.unramifiedMorphismProperty B S hS) c cmp.hom hc.1
      hcmprep hcU hcmpU
  obtain ⟨e, he, hefst, hesnd⟩ := exists_schemeStackProd_equivalence.{u, w} B S hS W (b' ≫ h)
    (comp_structureMorphism B S hS b').symm
  let Tsq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (b' ≫ h).hom (b' ≫ h).hom
  have hTsq : Bicategory.IsTwoFibreProduct Tsq :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hfst : Q₀.fst = cmp.hom ≫ Tsq.fst := rfl
  have hsnd : Q₀.snd = cmp.hom ≫ Tsq.snd := rfl
  let isoQ : Q₀.fst ≫ (b' ≫ h).hom ≅ Q₀.snd ≫ (b' ≫ h).hom :=
    (Bicategory.associator Q₀.fst b h.hom).symm ≪≫ Bicategory.whiskerRightIso Q₀.iso h.hom ≪≫
      Bicategory.associator Q₀.snd b h.hom
  let Sq : Bicategory.TwoCommSq (b' ≫ h).hom (b' ≫ h).hom :=
    { pt := schemeFibredCategory B S hS E
      fst := schemeFibredCategoryMap B S hS s
      snd := schemeFibredCategoryMap B S hS t
      iso := Bicategory.whiskerRightIso es _ ≪≫ Bicategory.associator c Q₀.fst _ ≪≫
        Bicategory.whiskerLeftIso c isoQ ≪≫ (Bicategory.associator c Q₀.snd _).symm ≪≫
        Bicategory.whiskerRightIso et.symm _ }
  let L₁ : Bicategory.TwoCommSq.PreHom Sq Tsq :=
    { hom := ψ
      isoFst := es ≪≫ Bicategory.whiskerLeftIso c (eqToIso hfst) ≪≫
        (Bicategory.associator c cmp.hom Tsq.fst).symm
      isoSnd := et ≪≫ Bicategory.whiskerLeftIso c (eqToIso hsnd) ≪≫
        (Bicategory.associator c cmp.hom Tsq.snd).symm
      compat := twoCell_ext_schemeFibredCategory B S hS _ _ }
  have h₁ : schemeFibredCategoryMap B S hS s =
      schemeFibredCategoryMap B S hS (prod.lift s t) ≫ e.hom ≫ Tsq.fst := by
    rw [hefst, ← schemeFibredCategoryMap_comp, prod.lift_fst]
  have h₂ : schemeFibredCategoryMap B S hS t =
      schemeFibredCategoryMap B S hS (prod.lift s t) ≫ e.hom ≫ Tsq.snd := by
    rw [hesnd, ← schemeFibredCategoryMap_comp, prod.lift_snd]
  let L₂ : Bicategory.TwoCommSq.PreHom Sq Tsq :=
    { hom := schemeFibredCategoryMap B S hS (prod.lift s t) ≫ e.hom
      isoFst := eqToIso h₁ ≪≫ (Bicategory.associator _ _ _).symm
      isoSnd := eqToIso h₂ ≪≫ (Bicategory.associator _ _ _).symm
      compat := twoCell_ext_schemeFibredCategory B S hS _ _ }
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hTsq L₁ L₂
  have : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS E).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 (schemeFibredCategory B S hS E).val.obj))
  have := he
  exact unramified_of_hasRelativeProperty_schemeFibredCategoryMap B S hS _
    (hasRelativeProperty_of_equivalences B S hS (Space.unramifiedMorphismProperty B S hS)
      (schemeFibredCategoryMap B S hS (prod.lift s t)) ψ
      (BasedFunctor.id (schemeFibredCategory B S hS E).val) e.hom.hom
      (twoIsoHomIso B S hS θ) hψrep
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _) hψU)

/-- **The form the étale slices are cut with.** Under the hypotheses of
`AlgebraicGeometry.Stack.unramified_prodLift_of_isDMOver`, the morphism of schemes
`(s, t) : E ⟶ W ×_{Spec ℤ} W` is unramified at every point. It is `(s, t) : E ⟶ W ×_S W`
followed by the base change `W ×_S W ⟶ W ×_{Spec ℤ} W` of the diagonal of `S`, an immersion. -/
theorem unramifiedAt_pullbackLift_of_isDMOver (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsDMOver.{u, w} B S hS 𝒳) {W E : BigFppfOver B S hS}
    (b : schemeFibredCategory B S hS W ⟶ 𝒳.val)
    (c : schemeFibredCategory B S hS E ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).pt)
    (hc : IsRelativelyEtale B S hS c) (s t : E ⟶ W)
    (es : schemeFibredCategoryMap B S hS s ≅
      c ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).fst)
    (et : schemeFibredCategoryMap B S hS t ≅
      c ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).snd)
    (x : (BigFppfOver.toScheme B S hS).obj E) :
    UnramifiedAt (pullback.lift ((BigFppfOver.toScheme B S hS).map s)
        ((BigFppfOver.toScheme B S hS).map t) (terminal.hom_ext _ _) :
      (BigFppfOver.toScheme B S hS).obj E ⟶
        pullback (terminal.from ((BigFppfOver.toScheme B S hS).obj W))
          (terminal.from ((BigFppfOver.toScheme B S hS).obj W))) x := by
  let F := BigFppfOver.toScheme B S hS
  have hunr : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [FormallyUnramified f],
      Unramified f := fun f _ _ =>
    (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).2 ⟨inferInstance, inferInstance⟩
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hPB : IsPullback (prod.fst : W ⨯ W ⟶ W) prod.snd (terminal.from W) (terminal.from W) :=
    IsPullback.of_hasBinaryProduct' W W
  have hPB' := hPB.map F
  let ρ := F.map (terminal.from W)
  let i := terminal.from (F.obj (⊤_ BigFppfOver B S hS))
  let j : pullback ρ ρ ⟶ pullback (ρ ≫ i) (ρ ≫ i) :=
    pullback.map ρ ρ (ρ ≫ i) (ρ ≫ i) (𝟙 _) (𝟙 _) i (by simp) (by simp)
  have hj : _root_.AlgebraicGeometry.IsImmersion j :=
    MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback ρ ρ i)
      (inferInstanceAs (_root_.AlgebraicGeometry.IsImmersion (pullback.diagonal i)))
  have hρi : ρ ≫ i = terminal.from (F.obj W) := terminal.hom_ext _ _
  have hfac : (pullback.lift (F.map s) (F.map t) (terminal.hom_ext _ _) :
        F.obj E ⟶ pullback (terminal.from (F.obj W)) (terminal.from (F.obj W))) =
      F.map (prod.lift s t) ≫ hPB'.isoPullback.hom ≫ j ≫ (pullback.congrHom hρi hρi).hom := by
    apply pullback.hom_ext
    · simp only [pullback.congrHom_hom, Category.assoc, pullback.map_fst, Category.comp_id,
        IsPullback.isoPullback_hom_fst, ← F.map_comp, limit.lift_π, BinaryFan.mk_pt,
        BinaryFan.mk_fst, ρ, i, j]
      exact pullback.lift_fst _ _ _
    · simp only [pullback.congrHom_hom, Category.assoc, pullback.map_snd, Category.comp_id,
        IsPullback.isoPullback_hom_snd, ← F.map_comp, limit.lift_π, BinaryFan.mk_pt,
        BinaryFan.mk_snd, ρ, i, j]
      exact pullback.lift_snd _ _ _
  have h₁ := unramified_prodLift_of_isDMOver B S hS 𝒳 h𝒳 b c hc s t es et
  have h₂ : Unramified hPB'.isoPullback.hom := hunr _
  have h₃ : Unramified j := hunr _
  have h₄ : Unramified (pullback.congrHom hρi hρi).hom := hunr _
  rw [hfac]
  exact (MorphismProperty.comp_mem _ _ _ h₁
    (MorphismProperty.comp_mem _ _ _ h₂ (MorphismProperty.comp_mem _ _ _ h₃ h₄))).unramifiedAt x

end AlgebraicGeometry.Stack

end
