module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickeningCriteria

/-!
# Models of a morphism of algebraic spaces of finite presentation over a ring of finite type

Let `f : U ⟶ X` be a morphism of algebraic spaces of finite presentation over `Spec A`. Then
there are a finite subset `k ⊆ A`, with `A₀ = ℤ[k] ⊆ A`, and a morphism `f₀ : U₀ ⟶ X₀` of
algebraic spaces of finite presentation over `Spec A₀` whose base change along
`Spec A ⟶ Spec A₀` is `f`; if `f` is flat, `f₀` can be chosen flat.

## Main results

* `AlgebraicGeometry.Space.exists_relationHom_of_isFinitePresentation`: compatible affine étale
  presentations of `U` and `X`.
* `AlgebraicGeometry.Space.exists_finiteType_model_hom`: the model `f₀`.

## Implementation notes

As for `AlgebraicGeometry.Space.exists_stageModel`, the model is built from presentations and
the Noetherian approximation of schemes, not from Stacks 07SK, whose statement in this library
bounds the size of the index category. Affine étale presentations `(W_U, R_U)` of `U` and
`(W_X, R_X)` of `X` with maps `a : W_U ⟶ W_X`, `b : R_U ⟶ R_X` presenting `f` are schemes and
morphisms of finite presentation over `Spec A`; they descend to a stage together with the
identities between them (Stacks 01ZM), and `a` descends to a flat morphism if it is flat
(Stacks 04AI). The quotients of the descended relations are `U₀` and `X₀`, and the descended `a`
induces `f₀`.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u


namespace AlgebraicGeometry

/-! ### Models of a morphism of relations -/

section HomModel

/-- Two composites of morphisms of models agree after the base change as soon as the
morphisms they model compose to the same morphism. -/
theorem map_comp_eq_of_isModel {C E : Type*} [Category* C] [Category* E] (G : C ⥤ E)
    {RU₀ WU₀ RX₀ WX₀ : C} {RU WU RX WX : E} (sU₀ : RU₀ ⟶ WU₀) (a₀ : WU₀ ⟶ WX₀)
    (b₀ : RU₀ ⟶ RX₀) (sX₀ : RX₀ ⟶ WX₀) {sU : RU ⟶ WU} {a : WU ⟶ WX} {b : RU ⟶ RX}
    {sX : RX ⟶ WX} (eRU : G.obj RU₀ ≅ RU) (eWU : G.obj WU₀ ≅ WU) (eRX : G.obj RX₀ ≅ RX)
    (eWX : G.obj WX₀ ≅ WX) (hs : G.map sU₀ ≫ eWU.hom = eRU.hom ≫ sU)
    (ha : G.map a₀ ≫ eWX.hom = eWU.hom ≫ a) (hb : G.map b₀ ≫ eRX.hom = eRU.hom ≫ b)
    (hsX : G.map sX₀ ≫ eWX.hom = eRX.hom ≫ sX) (h : b ≫ sX = sU ≫ a) :
    G.map (b₀ ≫ sX₀) = G.map (sU₀ ≫ a₀) := by
  rw [← cancel_mono eWX.hom, G.map_comp, G.map_comp, Category.assoc, Category.assoc, hsX, ha,
    ← Category.assoc, hb, ← Category.assoc, hs, Category.assoc, Category.assoc, h]

/-- A property of morphisms of schemes invariant under isomorphism holds for a morphism of
models after the base change as soon as it holds for the morphism it models. -/
theorem prop_map_left_of_isModel (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {T T' : Scheme.{u}} (π : T' ⟶ T) {WU₀ WX₀ : Over T} {WU WX : Over T'} (a₀ : WU₀ ⟶ WX₀)
    {a : WU ⟶ WX} (eWU : (Over.pullback π).obj WU₀ ≅ WU) (eWX : (Over.pullback π).obj WX₀ ≅ WX)
    (ha : (Over.pullback π).map a₀ ≫ eWX.hom = eWU.hom ≫ a) (h : P a.left) :
    P ((Over.pullback π).map a₀).left := by
  have h' : (Over.pullback π).map a₀ = eWU.hom ≫ a ≫ eWX.inv := by
    rw [← reassoc_of% ha, Iso.hom_inv_id, Category.comp_id]
  have : IsIso eWU.hom.left := (Over.forget _).map_isIso eWU.hom
  have : IsIso eWX.inv.left := (Over.forget _).map_isIso eWX.inv
  rw [h', Over.comp_left, Over.comp_left]
  exact (P.cancel_left_of_respectsIso _ _).2 ((P.cancel_right_of_respectsIso _ _).2 h)

/-- A functor preserves a commuting square. -/
private theorem map_comp_eq_map_comp {C E : Type*} [Category* C] [Category* E] (G : C ⥤ E)
    {X Y Z W : C} {x : X ⟶ Y} {y : Y ⟶ W} {z : X ⟶ Z} {w : Z ⟶ W}
    (h : G.map (x ≫ y) = G.map (z ≫ w)) : G.map x ≫ G.map y = G.map z ≫ G.map w := by
  rwa [G.map_comp, G.map_comp] at h

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The étale groupoid properties of a model of a relation persist under restriction. -/
theorem RelationModel.etaleGroupoid_restrict {W R : Over c.pt} {s t : R ⟶ W}
    (M : RelationModel c s t)
    (h : Etale M.s₀.left ∧ Etale M.t₀.left ∧ Mono (prod.lift M.s₀ M.t₀).left ∧
      IsAffineHom M.W₀.hom ∧ IsGroupoidRelation M.s₀ M.t₀) {k : I} (a : k ⟶ M.stage) :
    Etale (M.restrict a).s₀.left ∧ Etale (M.restrict a).t₀.left ∧
      Mono (prod.lift (M.restrict a).s₀ (M.restrict a).t₀).left ∧
      IsAffineHom (M.restrict a).W₀.hom ∧
      IsGroupoidRelation (M.restrict a).s₀ (M.restrict a).t₀ :=
  ⟨M.etale_restrict_s₀ a h.1, M.etale_restrict_t₀ a h.2.1,
    M.prop_prodLift_restrict (MorphismProperty.monomorphisms Scheme.{u}) h.2.2.1 a,
    M.prop_W₀_restrict @IsAffineHom h.2.2.2.1 a, M.isGroupoidRelation_restrict h.2.2.2.2 a⟩

/-- **Stacks 01ZM, 07RP, 01ZN and 04AI for a morphism of relations.** Let `s_U, t_U : R_U ⟶ W_U`
and `s_X, t_X : R_X ⟶ W_X` be étale groupoid relations of schemes of finite presentation over
the limit, as in `AlgebraicGeometry.RelationModel.exists_etaleEquivalenceRelation`, and let
`a : W_U ⟶ W_X`, `b : R_U ⟶ R_X` be a morphism of relations. Then both relations, `a` and `b`
have models over a common stage which again form a morphism of étale groupoid relations, and
the model of `a` is flat if `a` is. -/
theorem RelationModel.exists_hom_etaleEquivalenceRelation (hc : IsLimit c)
    {WU RU WX RX : Over c.pt} (sU tU : RU ⟶ WU) (sX tX : RX ⟶ WX) (a : WU ⟶ WX)
    (b : RU ⟶ RX) (hbs : b ≫ sX = sU ≫ a) (hbt : b ≫ tX = tU ≫ a)
    (hWU : FinitePresentation WU.hom) (hRU : FinitePresentation RU.hom)
    (hWX : FinitePresentation WX.hom) (hRX : FinitePresentation RX.hom)
    [Etale sU.left] [Etale tU.left] [Mono (prod.lift sU tU).left] [IsAffineHom WU.hom]
    [Etale sX.left] [Etale tX.left] [Mono (prod.lift sX tX).left] [IsAffineHom WX.hom]
    (hgU : IsGroupoidRelation sU tU) (hgX : IsGroupoidRelation sX tX) :
    ∃ (k : I) (WU₀ RU₀ WX₀ RX₀ : Over (D.obj k)) (sU₀ tU₀ : RU₀ ⟶ WU₀) (sX₀ tX₀ : RX₀ ⟶ WX₀)
      (a₀ : WU₀ ⟶ WX₀) (b₀ : RU₀ ⟶ RX₀) (eWU : (Over.pullback (c.π.app k)).obj WU₀ ≅ WU)
      (eRU : (Over.pullback (c.π.app k)).obj RU₀ ≅ RU)
      (eWX : (Over.pullback (c.π.app k)).obj WX₀ ≅ WX)
      (eRX : (Over.pullback (c.π.app k)).obj RX₀ ≅ RX),
      FinitePresentation WU₀.hom ∧ FinitePresentation RU₀.hom ∧
      FinitePresentation WX₀.hom ∧ FinitePresentation RX₀.hom ∧
      (Over.pullback (c.π.app k)).map sU₀ ≫ eWU.hom = eRU.hom ≫ sU ∧
      (Over.pullback (c.π.app k)).map tU₀ ≫ eWU.hom = eRU.hom ≫ tU ∧
      (Over.pullback (c.π.app k)).map sX₀ ≫ eWX.hom = eRX.hom ≫ sX ∧
      (Over.pullback (c.π.app k)).map tX₀ ≫ eWX.hom = eRX.hom ≫ tX ∧
      (Over.pullback (c.π.app k)).map a₀ ≫ eWX.hom = eWU.hom ≫ a ∧
      b₀ ≫ sX₀ = sU₀ ≫ a₀ ∧ b₀ ≫ tX₀ = tU₀ ≫ a₀ ∧
      (Etale sU₀.left ∧ Etale tU₀.left ∧ Mono (prod.lift sU₀ tU₀).left ∧
        IsAffineHom WU₀.hom ∧ IsGroupoidRelation sU₀ tU₀) ∧
      (Etale sX₀.left ∧ Etale tX₀.left ∧ Mono (prod.lift sX₀ tX₀).left ∧
        IsAffineHom WX₀.hom ∧ IsGroupoidRelation sX₀ tX₀) ∧
      (Flat a.left → Flat a₀.left) := by
  obtain ⟨MU, hU₁, hU₂, hU₃, hU₄, hU₅, -, -⟩ :=
    RelationModel.exists_etaleEquivalenceRelation hc sU tU hWU hRU hgU
  obtain ⟨MX, hX₁, hX₂, hX₃, hX₄, hX₅, -, -⟩ :=
    RelationModel.exists_etaleEquivalenceRelation hc sX tX hWX hRX hgX
  -- a common stage
  let MU₁ := MU.restrict (IsCofiltered.minToLeft MU.stage MX.stage)
  let MX₁ := MX.restrict (IsCofiltered.minToRight MU.stage MX.stage)
  -- descend `a`
  obtain ⟨k₁, γ₁, a₁, ha₁⟩ := RelationModel.exists_hom_model hc MU₁.W₀ MX₁.W₀
    MU₁.finitePresentation_W₀ MX₁.finitePresentation_W₀ MU₁.eW MX₁.eW a
  let MU₂ := MU₁.restrict γ₁
  let MX₂ := MX₁.restrict γ₁
  replace ha₁ : (Over.pullback (c.π.app k₁)).map a₁ ≫ MX₂.eW.hom = MU₂.eW.hom ≫ a := ha₁
  -- descend `b`
  obtain ⟨k₂, γ₂, b₂, hb₂⟩ := RelationModel.exists_hom_model hc MU₂.R₀ MX₂.R₀
    MU₂.finitePresentation_R₀ MX₂.finitePresentation_R₀ MU₂.eR MX₂.eR b
  let MU₃ := MU₂.restrict γ₂
  let MX₃ := MX₂.restrict γ₂
  replace hb₂ : (Over.pullback (c.π.app k₂)).map b₂ ≫ MX₃.eR.hom = MU₃.eR.hom ≫ b := hb₂
  let a₂ : MU₃.W₀ ⟶ MX₃.W₀ := (Over.pullback (D.map γ₂)).map a₁
  have ha₂ : (Over.pullback (c.π.app k₂)).map a₂ ≫ MX₃.eW.hom = MU₃.eW.hom ≫ a :=
    RelationModel.isModel_restrict γ₂ MU₂.eW MX₂.eW ha₁
  -- the identities of a morphism of relations, eventually
  have e₁ := map_comp_eq_of_isModel (Over.pullback (c.π.app k₂)) MU₃.s₀ a₂ b₂ MX₃.s₀
    MU₃.eR MU₃.eW MX₃.eR MX₃.eW MU₃.hs ha₂ hb₂ MX₃.hs hbs
  have e₂ := map_comp_eq_of_isModel (Over.pullback (c.π.app k₂)) MU₃.t₀ a₂ b₂ MX₃.t₀
    MU₃.eR MU₃.eW MX₃.eR MX₃.eW MU₃.ht ha₂ hb₂ MX₃.ht hbt
  have hRU₃ : FinitePresentation MU₃.R₀.hom := MU₃.finitePresentation_R₀
  have hWX₃ : FinitePresentation MX₃.W₀.hom := MX₃.finitePresentation_W₀
  obtain ⟨k₃, γ₃, h₃⟩ := (RelationModel.eventuallyBelow_map_eq hc hRU₃ hWX₃ e₁).and
    (RelationModel.eventuallyBelow_map_eq hc hRU₃ hWX₃ e₂)
  obtain ⟨f₁, f₂⟩ := h₃ (𝟙 k₃)
  rw [Category.id_comp] at f₁ f₂
  let MU₄ := MU₃.restrict γ₃
  let MX₄ := MX₃.restrict γ₃
  let a₃ : MU₄.W₀ ⟶ MX₄.W₀ := (Over.pullback (D.map γ₃)).map a₂
  let b₃ : MU₄.R₀ ⟶ MX₄.R₀ := (Over.pullback (D.map γ₃)).map b₂
  have ha₃ : (Over.pullback (c.π.app k₃)).map a₃ ≫ MX₄.eW.hom = MU₄.eW.hom ≫ a :=
    RelationModel.isModel_restrict γ₃ MU₃.eW MX₃.eW ha₂
  have f₁' : b₃ ≫ MX₄.s₀ = MU₄.s₀ ≫ a₃ := map_comp_eq_map_comp _ f₁
  have f₂' : b₃ ≫ MX₄.t₀ = MU₄.t₀ ≫ a₃ := map_comp_eq_map_comp _ f₂
  have : CompactSpace MU₄.W₀.left := RelationModel.compactSpace_W₀ MU₄
  have : CompactSpace MX₄.W₀.left := RelationModel.compactSpace_W₀ MX₄
  have : QuasiSeparatedSpace MU₄.W₀.left := RelationModel.quasiSeparatedSpace_W₀ MU₄
  have : QuasiSeparatedSpace MX₄.W₀.left := RelationModel.quasiSeparatedSpace_W₀ MX₄
  -- flatness of the model of `a`
  have : LocallyOfFinitePresentation a₃.left :=
    locallyOfFinitePresentation_left_of_finitePresentation _ MU₄.finitePresentation_W₀
      MX₄.finitePresentation_W₀
  obtain ⟨k₄, γ₄, hf₄⟩ : ∃ (k₄ : I) (γ₄ : k₄ ⟶ k₃),
      Flat a.left → Flat ((Over.pullback (D.map γ₄)).map a₃).left := by
    by_cases hfl : Flat a.left
    · have : MorphismProperty.RespectsIso @Flat :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      have : Flat ((Over.pullback (c.π.app k₃)).map a₃).left :=
        prop_map_left_of_isModel @Flat _ a₃ MU₄.eW MX₄.eW ha₃ hfl
      obtain ⟨k₄, γ₄, hf₄⟩ := exists_flat_baseChange_of_limitBaseChange D c k₃ MU₄.W₀ MX₄.W₀ a₃ hc
      exact ⟨k₄, γ₄, fun _ => hf₄⟩
    · exact ⟨k₃, 𝟙 _, fun h => absurd h hfl⟩
  let MU₅ := MU₄.restrict γ₄
  let MX₅ := MX₄.restrict γ₄
  have gU := MU₄.etaleGroupoid_restrict (MU₃.etaleGroupoid_restrict (MU₂.etaleGroupoid_restrict
    (MU₁.etaleGroupoid_restrict (MU.etaleGroupoid_restrict ⟨hU₁, hU₂, hU₃, hU₄, hU₅⟩ _) γ₁) γ₂)
    γ₃) γ₄
  have gX := MX₄.etaleGroupoid_restrict (MX₃.etaleGroupoid_restrict (MX₂.etaleGroupoid_restrict
    (MX₁.etaleGroupoid_restrict (MX.etaleGroupoid_restrict ⟨hX₁, hX₂, hX₃, hX₄, hX₅⟩ _) γ₁) γ₂)
    γ₃) γ₄
  refine ⟨k₄, MU₅.W₀, MU₅.R₀, MX₅.W₀, MX₅.R₀, MU₅.s₀, MU₅.t₀, MX₅.s₀, MX₅.t₀,
    (Over.pullback (D.map γ₄)).map a₃, (Over.pullback (D.map γ₄)).map b₃, MU₅.eW, MU₅.eR,
    MX₅.eW, MX₅.eR, MU₅.finitePresentation_W₀, MU₅.finitePresentation_R₀,
    MX₅.finitePresentation_W₀, MX₅.finitePresentation_R₀, MU₅.hs, MU₅.ht, MX₅.hs, MX₅.ht,
    RelationModel.isModel_restrict γ₄ MU₄.eW MX₄.eW ha₃, ?_, ?_, gU, gX, hf₄⟩
  · exact map_comp_eq_map_comp _ (congrArg _ f₁')
  · exact map_comp_eq_map_comp _ (congrArg _ f₂')

end HomModel

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X U : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}

/-! ### Compatible presentations -/

include B in
/-- **Compatible affine étale presentations of a morphism.** Let `f : U ⟶ X` be a morphism of
algebraic spaces of finite presentation over `Spec A`. There are surjective étale atlases
`c_X : W_X ⟶ X` and `c_U : W_U ⟶ U` with `W_X`, `W_U` affine, with kernel pairs `R_X`, `R_U`
represented by quasi-compact objects, and morphisms `a : W_U ⟶ W_X`, `b : R_U ⟶ R_X` over `f`. -/
theorem exists_relationHom_of_isFinitePresentation (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hU : IsAlgebraicSpace B (Spec (.of A)) hA U)
    (pX : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (pU : U ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hpX : IsFinitePresentation B (Spec (.of A)) hA pX)
    (hpU : IsFinitePresentation B (Spec (.of A)) hA pU) (f : U ⟶ X) :
    ∃ (WX RX WU RU : BigFppfOver B (Spec (.of A)) hA) (cX : yoneda.obj WX ⟶ X)
      (cU : yoneda.obj WU ⟶ U) (r₁ r₂ : RX ⟶ WX) (u₁ u₂ : RU ⟶ WU) (a : WU ⟶ WX) (b : RU ⟶ RX),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf cX ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf cX ∧
      IsPullback (yoneda.map r₁) (yoneda.map r₂) cX cX ∧
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj WX) ∧
      FinitePresentation (B.inclusion.map WX.hom) ∧
      CompactSpace ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj RX) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf cU ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf cU ∧
      IsPullback (yoneda.map u₁) (yoneda.map u₂) cU cU ∧
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj WU) ∧
      FinitePresentation (B.inclusion.map WU.hom) ∧
      CompactSpace ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj RU) ∧
      yoneda.map a ≫ cX = cU ≫ f ∧ b ≫ r₁ = u₁ ≫ a ∧ b ≫ r₂ = u₂ ≫ a := by
  have hZ := BigFppfSite.contains_terminal B
  obtain ⟨WX, RX, cX, r₁, r₂, hXs, hXe, hRX, hWX, hWXfp, hRXc, -, -⟩ :=
    exists_relation_of_isFinitePresentation B hX pX hpX
  let Q := BigFppfOver.toScheme B (Spec (.of A)) hA
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  have : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  have : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  have : P.IsStableUnderComposition :=
    let := AlgebraicGeometry.surjective_isStableUnderComposition.{u}
    MorphismProperty.IsStableUnderComposition.inverseImage Q
  have : E.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage Q
  have : P.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition P
  have : E.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition E
  -- the fibre product `U ×_X W_X` and an affine atlas of it
  have hT : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA hZ
      (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of A)) hA _ hZ
      ⟨_, inferInstanceAs (QuasiSeparatedSpace (Spec (.of A))),
        ⟨Functor.RepresentableBy.yoneda _⟩⟩
  have hXqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A)) hA hZ hX hT
    hpX.2.2
  have hUqc := isQuasiCompactSpace_of_isQuasiCompact_toBase B (Spec (.of A)) hA pU hpU.2.1
  have hWXqc : IsQuasiCompactSpace B (Spec (.of A)) hA (yoneda.obj WX) :=
    isQuasiCompactSpace_yoneda_obj B (Spec (.of A)) hA
      (have : IsAffine (Q.obj WX) := hWX; inferInstance)
  have hU' := isAlgebraicSpace_pullback B (Spec (.of A)) hA f cX hU
    (isAlgebraicSpace_yoneda B _ hA WX) hX
  have hU'qc := isQuasiCompactSpace_pullback B (Spec (.of A)) hA hZ f cX hU hX hUqc hWXqc hXqs
  obtain ⟨WU, c', hWU, hc's, hc'e⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B _ hA _ hU').1 hU'qc
  have hpb := IsPullback.of_hasPullback f cX
  let cU := c' ≫ pullback.fst f cX
  have hcUs : P.presheaf cU :=
    MorphismProperty.comp_mem _ _ _ hc's (P.presheaf.of_isPullback hpb.flip hXs)
  have hcUe : E.presheaf cU :=
    MorphismProperty.comp_mem _ _ _ (presheaf_etale_of_isEtale B (Spec (.of A)) hA hc'e)
      (E.presheaf.of_isPullback hpb.flip hXe)
  obtain ⟨RU, u₁, u₂, hRU, hWUfp, hRUc, -, -⟩ := exists_relation_of_chart B hU pU hpU cU hWU hcUe
  -- the morphisms of presentations
  let a : WU ⟶ WX := yoneda.preimage (c' ≫ pullback.snd f cX)
  have ha : yoneda.map a ≫ cX = cU ≫ f := by
    simp only [a, Functor.map_preimage, Category.assoc, cU, pullback.condition]
  have hw : yoneda.map (u₁ ≫ a) ≫ cX = yoneda.map (u₂ ≫ a) ≫ cX := by
    simp only [Functor.map_comp, Category.assoc, ha]
    simp only [← Category.assoc, hRU.w]
  let b : RU ⟶ RX := yoneda.preimage (hRX.lift _ _ hw)
  refine ⟨WX, RX, WU, RU, cX, cU, r₁, r₂, u₁, u₂, a, b, hXs, hXe, hRX, hWX, hWXfp, hRXc,
    hcUs, hcUe, hRU, hWU, hWUfp, hRUc, ha, ?_, ?_⟩
  · exact yoneda.map_injective (by simp [b])
  · exact yoneda.map_injective (by simp [b])

/-! ### Descending morphisms along an atlas -/

/-- **A morphism out of an algebraic space is defined on an atlas.** A morphism `h : W ⟶ G` to
an fppf sheaf which equalizes the kernel pair of a surjective étale atlas `φ : W ⟶ F` factors
through `φ`: the atlas is the coequalizer of its kernel pair (Stacks 0262, part (3)). -/
theorem exists_comp_eq_of_surjectiveEtale {S : Scheme.{u}} {hS : B.Contains S}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {V R : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ F) (s t : R ⟶ V) (hR : IsPullback (yoneda.map s) (yoneda.map t) φ φ)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (h : yoneda.obj V ⟶ G) (hh : yoneda.map s ≫ h = yoneda.map t ≫ h) :
    ∃ w : F ⟶ G, φ ≫ w = h := by
  obtain ⟨hRsh, hVsh, ⟨hcol⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS φ s t hR hF hsurj hetale
  let J := BigFppfOver.topology B S hS
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let VF : Sheaf J (Type u) := ⟨yoneda.obj V, hVsh⟩
  let GF : Sheaf J (Type u) := ⟨G, hG⟩
  let hf : VF ⟶ GF := ObjectProperty.homMk h
  have hw : (ObjectProperty.homMk (yoneda.map s) : RF ⟶ VF) ≫ hf =
      (ObjectProperty.homMk (yoneda.map t) : RF ⟶ VF) ≫ hf := Sheaf.hom_ext hh
  exact ⟨(hcol.desc (Cofork.ofπ hf hw)).hom,
    congrArg (fun k => k.hom) (hcol.fac (Cofork.ofπ hf hw) WalkingParallelPair.one)⟩

/-! ### Objects of the site over a stage -/

/-- A scheme of finite presentation over a stage of the Noetherian approximation of `Spec A`,
as an object of the big fppf site over that stage. -/
abbrev stageSiteObj (k : (Finset A)ᵒᵖ) (W₀ : Over ((specAdjoinFinsetDiagram A).obj k))
    (h : FinitePresentation W₀.hom) :
    BigFppfOver B ((specAdjoinFinsetDiagram A).obj k) (contains_specAdjoinFinsetDiagram_obj B k) :=
  BigFppfOver.mk B _ (contains_specAdjoinFinsetDiagram_obj B k)
    (@Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact _ _ _ W₀.hom
      (have := h.1; inferInstance) h.2.1 (contains_specAdjoinFinsetDiagram_obj B k)) W₀.hom

/-- A morphism of schemes of finite presentation over a stage, as a morphism of the site. -/
abbrev stageSiteHom (k : (Finset A)ᵒᵖ) {X₀ Y₀ : Over ((specAdjoinFinsetDiagram A).obj k)}
    (hX : FinitePresentation X₀.hom) (hY : FinitePresentation Y₀.hom) (f₀ : X₀ ⟶ Y₀) :
    stageSiteObj B k X₀ hX ⟶ stageSiteObj B k Y₀ hY :=
  (fullyFaithful_overPost_bigFppfInclusion B _ (contains_specAdjoinFinsetDiagram_obj B k)).preimage
    f₀

/-- The morphism of schemes underlying `stageSiteHom B k hX hY f₀` is `f₀`. -/
theorem map_stageSiteHom (k : (Finset A)ᵒᵖ) {X₀ Y₀ : Over ((specAdjoinFinsetDiagram A).obj k)}
    (hX : FinitePresentation X₀.hom) (hY : FinitePresentation Y₀.hom) (f₀ : X₀ ⟶ Y₀) :
    (Over.post B.inclusion).map (stageSiteHom B k hX hY f₀) = f₀ :=
  Functor.FullyFaithful.map_preimage _ _

include B in
/-- **The quotient of an étale groupoid relation over a stage.** An étale relation of schemes of
finite presentation over a stage `Spec A_k`, with `(s, t)` a monomorphism, `W` affine over the
stage and groupoid witnesses, has a quotient algebraic space of finite presentation over the
stage, with atlas `W ⟶ X₀` whose kernel pair is `(s, t)`. -/
theorem exists_quotient_of_stageRelation (k : (Finset A)ᵒᵖ)
    {W₀ R₀ : Over ((specAdjoinFinsetDiagram A).obj k)} (hW₀ : FinitePresentation W₀.hom)
    (hR₀ : FinitePresentation R₀.hom) (s₀ t₀ : R₀ ⟶ W₀)
    (h : Etale s₀.left ∧ Etale t₀.left ∧ Mono (prod.lift s₀ t₀).left ∧
      _root_.AlgebraicGeometry.IsAffineHom W₀.hom ∧
      IsGroupoidRelation s₀ t₀) :
    ∃ (X₀ : (BigFppfOver B ((specAdjoinFinsetDiagram A).obj k)
        (contains_specAdjoinFinsetDiagram_obj B k))ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B _ (contains_specAdjoinFinsetDiagram_obj B k) X₀)
      (q : yoneda.obj (stageSiteObj B k W₀ hW₀) ⟶ X₀)
      (y : X₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj (contains_specAdjoinFinsetDiagram_obj B k))))),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B _ (contains_specAdjoinFinsetDiagram_obj B k))).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B _ (contains_specAdjoinFinsetDiagram_obj B k))).presheaf q ∧
      IsPullback (yoneda.map (stageSiteHom B k hR₀ hW₀ s₀))
        (yoneda.map (stageSiteHom B k hR₀ hW₀ t₀)) q q ∧
      IsFinitePresentation B _ (contains_specAdjoinFinsetDiagram_obj B k) y ∧
      Stacks.Groupoids.IsEtaleEquivalenceRelation
        (prod.lift ((Over.post B.inclusion).map (stageSiteHom B k hR₀ hW₀ s₀))
          ((Over.post B.inclusion).map (stageSiteHom B k hR₀ hW₀ t₀))) := by
  obtain ⟨hMs, hMt, hMmono, hMaff, hMgrp⟩ := h
  have hZ := BigFppfSite.contains_terminal B
  let S₀ := (specAdjoinFinsetDiagram A).obj k
  have h₀ : B.Contains S₀ := contains_specAdjoinFinsetDiagram_obj B k
  have hS₀ : IsAffine S₀ := inferInstanceAs (IsAffine ((specAdjoinFinsetDiagram A).obj k))
  let Wo := stageSiteObj B k W₀ hW₀
  let Ro := stageSiteObj B k R₀ hR₀
  let G₀ := Over.post (X := B.obj h₀) B.inclusion
  have hG₀ : G₀.FullyFaithful := fullyFaithful_overPost_bigFppfInclusion B S₀ h₀
  let sR : Ro ⟶ Wo := stageSiteHom B k hR₀ hW₀ s₀
  let tR : Ro ⟶ Wo := stageSiteHom B k hR₀ hW₀ t₀
  have hsR : G₀.map sR = s₀ := map_stageSiteHom B k hR₀ hW₀ s₀
  have htR : G₀.map tR = t₀ := map_stageSiteHom B k hR₀ hW₀ t₀
  have hgrpo : IsGroupoidRelation sR tR :=
    IsGroupoidRelation.of_map hG₀ (by rw [hsR, htR]; exact hMgrp)
  obtain ⟨refl, symm, comp, hr₁, hr₂, hσ₁, hσ₂, hc₁, hc₂⟩ := hgrpo
  have hjm : JointlyMono₂ (G₀.map sR) (G₀.map tR) := by
    have : Mono (prod.lift s₀ t₀) := Over.mono_of_mono_left _
    rw [hsR, htR]
    exact AlgebraicGeometry.jointlyMono₂_of_mono_prodLift _ _ this
  have hsE : Etale ((BigFppfOver.toScheme B S₀ h₀).map sR) := by
    change Etale (G₀.map sR).left
    rwa [hsR]
  have htE : Etale ((BigFppfOver.toScheme B S₀ h₀).map tR) := by
    change Etale (G₀.map tR).left
    rwa [htR]
  have hWoAff : IsAffine ((BigFppfOver.toScheme B S₀ h₀).obj Wo) := by
    have := hMaff
    have : IsAffine W₀.left := isAffine_of_isAffineHom W₀.hom
    exact this
  let T := yoneda.obj (Over.mk (𝟙 (B.obj h₀)) : BigFppfOver B S₀ h₀)
  have hT : IsAlgebraicSpace B S₀ h₀ T := isAlgebraicSpace_yoneda B S₀ h₀ _
  have hTqc : IsQuasiCompactSpace B S₀ h₀ T :=
    isQuasiCompactSpace_yoneda_obj B S₀ h₀ (inferInstanceAs (CompactSpace S₀))
  have hTqs : IsAbsolutelyQuasiSeparated B S₀ h₀ hZ T :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S₀ h₀ _ hZ
      ⟨_, inferInstanceAs (QuasiSeparatedSpace S₀), ⟨Functor.RepresentableBy.yoneda _⟩⟩
  let wo : yoneda.obj Wo ⟶ T :=
    yoneda.map (Over.homMk Wo.hom (Category.comp_id _) : Wo ⟶ Over.mk (𝟙 (B.obj h₀)))
  have hwo : yoneda.map sR ≫ wo = yoneda.map tR ≫ wo :=
    (isTerminal_yoneda_obj_base B S₀ h₀).hom_ext _ _
  have hwoFp : IsFinitePresentation B S₀ h₀ wo :=
    isFinitePresentation_yoneda_map B S₀ h₀ _ hW₀
  have hR₀c : CompactSpace R₀.left :=
    have : QuasiCompact R₀.hom := hR₀.2.1
    QuasiCompact.compactSpace_of_compactSpace R₀.hom
  have hRoqc : IsQuasiCompactSpace B S₀ h₀ (yoneda.obj Ro) :=
    isQuasiCompactSpace_yoneda_obj B S₀ h₀ hR₀c
  obtain ⟨X₀, hX₀, q, y, hqs, hqe, hqk, -, hyfp⟩ :=
    exists_isFinitePresentation_quotient_of_witnesses B S₀ h₀ hZ hT hTqc hTqs hWoAff sR tR hsE htE
      hjm refl hr₁ hr₂ symm hσ₁ hσ₂ comp hc₁ hc₂ wo hwo hwoFp hRoqc
  exact ⟨X₀, hX₀, q, y, hqs, hqe, hqk, hyfp,
    isEtaleEquivalenceRelation_relation_of_witnesses B S₀ h₀ sR tR hsE htE hjm refl hr₁ hr₂ symm
      hσ₁ hσ₂ comp hc₁ hc₂⟩

/-! ### The model of a morphism -/

include B in
/-- The pullback of a site morphism along a morphism of bases, compared through the base change
of the underlying morphism of schemes. -/
theorem overPost_pullback_map_comp {S₀ : Scheme.{u}} (h₀ : B.Contains S₀) (g : B.obj hA ⟶ B.obj h₀)
    {π : B.inclusion.obj (B.obj hA) ⟶ B.inclusion.obj (B.obj h₀)} (hg : B.inclusion.map g = π)
    {Ro Wo : BigFppfOver B S₀ h₀} (m : Ro ⟶ Wo) {R W : Over (B.inclusion.obj (B.obj hA))}
    (n : R ⟶ W) (eR : (Over.pullback π).obj ((Over.post B.inclusion).obj Ro) ≅ R)
    (eW : (Over.pullback π).obj ((Over.post B.inclusion).obj Wo) ≅ W)
    (h : (Over.pullback π).map ((Over.post B.inclusion).map m) ≫ eW.hom = eR.hom ≫ n) :
    (Over.post B.inclusion).map ((Over.pullback g).map m) ≫
        ((Over.postPullbackIso B.inclusion g ≪≫
          Functor.isoWhiskerLeft (Over.post B.inclusion) (Over.pullbackCongr hg)).app Wo ≪≫
          eW).hom =
      ((Over.postPullbackIso B.inclusion g ≪≫
          Functor.isoWhiskerLeft (Over.post B.inclusion) (Over.pullbackCongr hg)).app Ro ≪≫
          eR).hom ≫ n := by
  let Θ := Over.postPullbackIso B.inclusion g ≪≫
    Functor.isoWhiskerLeft (Over.post B.inclusion) (Over.pullbackCongr hg)
  have h' : (Over.post B.inclusion).map ((Over.pullback g).map m) ≫ Θ.hom.app Wo =
      Θ.hom.app Ro ≫ (Over.pullback π).map ((Over.post B.inclusion).map m) := Θ.hom.naturality m
  rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, Iso.app_hom, ← Category.assoc, h',
    Category.assoc, h, ← Category.assoc]

/-- The kernel pair of an étale relation with a monic pairing on a scheme of finite
presentation, with quasi-compact source, is of finite presentation. -/
theorem finitePresentation_of_relation {T : Scheme.{u}} [QuasiSeparatedSpace T] {W R : Over T}
    (s t : R ⟶ W) (hW : FinitePresentation W.hom) [CompactSpace R.left] [Etale s.left]
    [Mono (prod.lift s t).left] : FinitePresentation R.hom := by
  have hRw : R.hom = s.left ≫ W.hom := (Over.w s).symm
  have hRw' : R.hom = (prod.lift s t).left ≫ (W ⨯ W).hom := (Over.w (prod.lift s t)).symm
  have : LocallyOfFinitePresentation W.hom := hW.1
  have : QuasiSeparated (W ⨯ W).hom := (finitePresentation_prod_hom hW hW).2.2
  refine ⟨?_, inferInstance, ?_⟩
  · rw [hRw]; infer_instance
  · rw [hRw']; infer_instance

/-- The relation of an étale chart of an algebraic space over `Spec A` with affine source of
finite presentation and quasi-compact kernel pair is an étale groupoid relation of schemes of
finite presentation. -/
private theorem relation_data_of_chart
    (F : Over (B.obj hA) ⥤ Over (specAdjoinFinsetCone A).pt) (hF : F = Over.post B.inclusion)
    {W R : BigFppfOver B (Spec (.of A)) hA}
    {Y : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (c : yoneda.obj W ⟶ Y) (r₁ r₂ : R ⟶ W)
    (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) c c)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf c)
    (hW : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj W))
    (hWfp : FinitePresentation (B.inclusion.map W.hom))
    (hRc : CompactSpace ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj R)) :
    Etale (F.map r₁).left ∧ Etale (F.map r₂).left ∧ Mono (prod.lift (F.map r₁) (F.map r₂)).left ∧
      _root_.AlgebraicGeometry.IsAffineHom (F.obj W).hom ∧ FinitePresentation (F.obj R).hom ∧
      IsGroupoidRelation (F.map r₁) (F.map r₂) := by
  subst hF
  set F : Over (B.obj hA) ⥤ Over (specAdjoinFinsetCone A).pt := Over.post B.inclusion
  have : PreservesFiniteProducts F := preservesFiniteProducts_overPost_bigFppfInclusion B _ hA
  have hEq : IsEquivalenceRelation (F.map r₁) (F.map r₂) :=
    isEquivalenceRelation_of_isPullback B _ hA c r₁ r₂ hR
  have : Etale (F.map r₁).left := he.property c (yoneda.map r₂) r₁ hR.flip
  have : Etale (F.map r₂).left := he.property c (yoneda.map r₁) r₂ hR
  have : Mono (prod.lift (F.map r₁) (F.map r₂)) :=
    mono_prodLift_of_jointlyMono₂ hEq.nonempty_equivalenceRelation.some.toJointlyMono₂
  have : Mono (prod.lift (F.map r₁) (F.map r₂)).left := inferInstance
  have : IsAffine (specAdjoinFinsetCone A).pt := inferInstanceAs (IsAffine (Spec (.of A)))
  have : IsAffine (F.obj W).left := hW
  have : _root_.AlgebraicGeometry.IsAffineHom (F.obj W).hom := inferInstance
  have : CompactSpace (F.obj R).left := hRc
  have : QuasiSeparatedSpace (specAdjoinFinsetCone A).pt :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of A)))
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    finitePresentation_of_relation (F.map r₁) (F.map r₂) (W := F.obj W) hWfp,
    IsGroupoidRelation.of_isEquivalenceRelation hEq⟩

include B in
/-- **A model of a morphism of algebraic spaces of finite presentation.** Let `f : U ⟶ X` be a
morphism of algebraic spaces of finite presentation over `Spec A`. For some finite subset
`k ⊆ A` there is a morphism `f₀ : U₀ ⟶ X₀` of algebraic spaces of finite presentation over
`Spec ℤ[k]` whose restriction along `Spec A ⟶ Spec ℤ[k]` is `f`, and which is flat if `f` is. -/
theorem exists_stageModel_hom (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hU : IsAlgebraicSpace B (Spec (.of A)) hA U)
    (pX : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (pU : U ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hpX : IsFinitePresentation B (Spec (.of A)) hA pX)
    (hpU : IsFinitePresentation B (Spec (.of A)) hA pU) (f : U ⟶ X) :
    ∃ (i : (Finset A)ᵒᵖ) (X₀ U₀ : (BigFppfOver B ((specAdjoinFinsetDiagram A).obj i)
        (contains_specAdjoinFinsetDiagram_obj B i))ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B _ (contains_specAdjoinFinsetDiagram_obj B i) X₀)
      (_ : IsAlgebraicSpace B _ (contains_specAdjoinFinsetDiagram_obj B i) U₀)
      (pX₀ : X₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj (contains_specAdjoinFinsetDiagram_obj B i)))))
      (pU₀ : U₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj (contains_specAdjoinFinsetDiagram_obj B i)))))
      (f₀ : U₀ ⟶ X₀),
      IsFinitePresentation B _ _ pX₀ ∧ IsFinitePresentation B _ _ pU₀ ∧
      (IsFlat B (Spec (.of A)) hA f → IsFlat B _ _ f₀) ∧
      ∀ (g : B.obj hA ⟶ B.obj (contains_specAdjoinFinsetDiagram_obj B i)),
        B.inclusion.map g = (specAdjoinFinsetCone A).π.app i →
        ∃ (eU : U ≅ (OverShriek.relocalizeRestrict g).obj U₀)
          (eX : X ≅ (OverShriek.relocalizeRestrict g).obj X₀),
          eU.hom ≫ (OverShriek.relocalizeRestrict g).map f₀ = f ≫ eX.hom := by
  classical
  obtain ⟨WX, RX, WU, RU, cX, cU, r₁, r₂, u₁, u₂, a, b, hXs, hXe, hRX, hWX, hWXfp, hRXc,
    hUs, hUe, hRU, hWU, hWUfp, hRUc, ha, hb₁, hb₂⟩ :=
    exists_relationHom_of_isFinitePresentation B hX hU pX pU hpX hpU f
  let F : Over (B.obj hA) ⥤ Over (specAdjoinFinsetCone A).pt := Over.post B.inclusion
  have hFF : F.FullyFaithful := fullyFaithful_overPost_bigFppfInclusion B _ hA
  have hc : IsLimit (specAdjoinFinsetCone A) := isLimit_specAdjoinFinsetCone A
  -- the relations, read as schemes over `Spec A`
  obtain ⟨e₁X, e₂X, mX, aX, hRXfp, hgX⟩ :=
    relation_data_of_chart B F rfl cX r₁ r₂ hRX hXe hWX hWXfp hRXc
  obtain ⟨e₁U, e₂U, mU, aU, hRUfp, hgU⟩ :=
    relation_data_of_chart B F rfl cU u₁ u₂ hRU hUe hWU hWUfp hRUc
  have hbs : F.map b ≫ F.map r₁ = F.map u₁ ≫ F.map a := by
    exact map_comp_eq_map_comp _ (congrArg _ hb₁)
  have hbt : F.map b ≫ F.map r₂ = F.map u₂ ≫ F.map a := by
    exact map_comp_eq_map_comp _ (congrArg _ hb₂)
  obtain ⟨k, WU₀, RU₀, WX₀, RX₀, sU₀, tU₀, sX₀, tX₀, a₀, b₀, eWU, eRU, eWX, eRX, hWU₀, hRU₀, hWX₀,
    hRX₀, hsU, htU, hsX, htX, ha₀, hbs₀, hbt₀, gU, gX, hfl⟩ :=
    RelationModel.exists_hom_etaleEquivalenceRelation hc (F.map u₁) (F.map u₂) (F.map r₁) (F.map r₂)
      (F.map a) (F.map b) hbs hbt hWUfp hRUfp
      hWXfp hRXfp
      hgU hgX
  -- the quotients over the stage
  have h₀ : B.Contains ((specAdjoinFinsetDiagram A).obj k) :=
    contains_specAdjoinFinsetDiagram_obj B k
  obtain ⟨X₀, hX₀, qX, yX, hqXs, hqXe, hqXk, hyX, hrelX⟩ :=
    exists_quotient_of_stageRelation B k hWX₀ hRX₀ sX₀ tX₀ gX
  obtain ⟨U₀, hU₀, qU, yU, hqUs, hqUe, hqUk, hyU, hrelU⟩ :=
    exists_quotient_of_stageRelation B k hWU₀ hRU₀ sU₀ tU₀ gU
  let G₀ := Over.post (X := B.obj h₀) B.inclusion
  have hG₀ : G₀.FullyFaithful := fullyFaithful_overPost_bigFppfInclusion B _ h₀
  let aR := stageSiteHom B k hWU₀ hWX₀ a₀
  let bR := stageSiteHom B k hRU₀ hRX₀ b₀
  have hbsR : bR ≫ stageSiteHom B k hRX₀ hWX₀ sX₀ = stageSiteHom B k hRU₀ hWU₀ sU₀ ≫ aR :=
    hG₀.map_injective (by simp only [Functor.map_comp, G₀, bR, aR, map_stageSiteHom]; exact hbs₀)
  have hbtR : bR ≫ stageSiteHom B k hRX₀ hWX₀ tX₀ = stageSiteHom B k hRU₀ hWU₀ tU₀ ≫ aR :=
    hG₀.map_injective (by simp only [Functor.map_comp, G₀, bR, aR, map_stageSiteHom]; exact hbt₀)
  -- the model of `f`
  have hqa : yoneda.map (stageSiteHom B k hRU₀ hWU₀ sU₀) ≫ (yoneda.map aR ≫ qX) =
      yoneda.map (stageSiteHom B k hRU₀ hWU₀ tU₀) ≫ (yoneda.map aR ≫ qX) := by
    rw [← Category.assoc, ← Functor.map_comp, ← hbsR, ← Category.assoc, ← Functor.map_comp,
      ← hbtR, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hqXk.w]
  obtain ⟨f₀, hf₀⟩ := exists_comp_eq_of_surjectiveEtale B hU₀ hX₀.isSheaf qU _ _ hqUk hqUs
    hqUe _ hqa
  refine ⟨k, X₀, U₀, hX₀, hU₀, yX, yU, f₀, hyX, hyU, fun hf => ?_, fun g hg => ?_⟩
  · -- flatness
    have hfa : Flat (F.map a).left := hf WU WX cU cX a hUe hXe ha
    refine (holdsOnEveryEtaleChart_iff_surjectiveChart B _ h₀ _
      AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hU₀ hX₀ f₀).2
      ⟨_, _, qU, qX, aR, hqUe, hqXe, hqUs, hf₀.symm, ?_⟩
    change Flat (G₀.map aR).left
    rw [map_stageSiteHom]
    exact hfl hfa
  · -- the restriction of the model is `f`
    let Θ := Over.postPullbackIso B.inclusion g ≪≫ Functor.isoWhiskerLeft G₀ (Over.pullbackCongr hg)
    let ξ := fun (Wo : BigFppfOver B _ h₀) {W : BigFppfOver B (Spec (.of A)) hA}
      (e : (Over.pullback ((specAdjoinFinsetCone A).π.app k)).obj (G₀.obj Wo) ≅ F.obj W) =>
      hFF.preimageIso (Θ.app Wo ≪≫ e)
    have hξ : ∀ {Ro Wo : BigFppfOver B _ h₀} (m : Ro ⟶ Wo) {R W : BigFppfOver B (Spec (.of A)) hA}
        (n : R ⟶ W) (eR : (Over.pullback ((specAdjoinFinsetCone A).π.app k)).obj (G₀.obj Ro) ≅
          F.obj R)
        (eW : (Over.pullback ((specAdjoinFinsetCone A).π.app k)).obj (G₀.obj Wo) ≅ F.obj W),
        (Over.pullback ((specAdjoinFinsetCone A).π.app k)).map (G₀.map m) ≫ eW.hom =
          eR.hom ≫ F.map n →
        (Over.pullback g).map m ≫ (ξ Wo eW).hom = (ξ Ro eR).hom ≫ n := by
      intro Ro Wo m R W n eR eW h
      refine hFF.map_injective ?_
      rw [F.map_comp, F.map_comp]
      simp only [ξ, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
      exact overPost_pullback_map_comp B h₀ g hg m (F.map n) eR eW h
    have mapX : ∀ m₀, G₀.map (stageSiteHom B k hRX₀ hWX₀ m₀) = m₀ := map_stageSiteHom B k _ _
    have mapU : ∀ m₀, G₀.map (stageSiteHom B k hRU₀ hWU₀ m₀) = m₀ := map_stageSiteHom B k _ _
    let oWX := stageSiteObj B k WX₀ hWX₀
    let oRX := stageSiteObj B k RX₀ hRX₀
    let oWU := stageSiteObj B k WU₀ hWU₀
    let oRU := stageSiteObj B k RU₀ hRU₀
    obtain ⟨eX, heX⟩ := exists_iso_relocalizeRestrict_of_quotient B hX cX r₁ r₂ hXs hXe hRX h₀
      (stageSiteHom B k hRX₀ hWX₀ sX₀) (stageSiteHom B k hRX₀ hWX₀ tX₀) hrelX hX₀ qX hqXs hqXe
      hqXk g (ξ oWX eWX) (ξ oRX eRX)
      (hξ (stageSiteHom B k hRX₀ hWX₀ sX₀) r₁ eRX eWX (by rw [mapX]; exact hsX))
      (hξ (stageSiteHom B k hRX₀ hWX₀ tX₀) r₂ eRX eWX (by rw [mapX]; exact htX))
    obtain ⟨eU, heU⟩ := exists_iso_relocalizeRestrict_of_quotient B hU cU u₁ u₂ hUs hUe hRU h₀
      (stageSiteHom B k hRU₀ hWU₀ sU₀) (stageSiteHom B k hRU₀ hWU₀ tU₀) hrelU hU₀ qU hqUs hqUe
      hqUk g (ξ oWU eWU) (ξ oRU eRU)
      (hξ (stageSiteHom B k hRU₀ hWU₀ sU₀) u₁ eRU eWU (by rw [mapU]; exact hsU))
      (hξ (stageSiteHom B k hRU₀ hWU₀ tU₀) u₂ eRU eWU (by rw [mapU]; exact htU))
    have hφa : (Over.pullback g).map aR ≫ (ξ oWX eWX).hom = (ξ oWU eWU).hom ≫ a :=
      hξ aR a eWU eWX (by rw [map_stageSiteHom]; exact ha₀)
    have hφa' : (ξ oWU eWU).inv ≫ (Over.pullback g).map aR = a ≫ (ξ oWX eWX).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, hφa]
    refine ⟨eU, eX, eq_of_comp_eq_of_surjectiveEtale B (Spec (.of A)) hA hU
      (isAlgebraicSpace_relocalizeRestrict B (Spec (.of A)) _ hA h₀ g X₀ hX₀).isSheaf cU hUs hUe
      ?_⟩
    rw [reassoc_of% heU, ← Functor.map_comp, hf₀, Functor.map_comp,
      ← reassoc_of% (OverShriek.restrictYonedaIso_naturality g aR), ← Functor.map_comp_assoc,
      hφa', Functor.map_comp, Category.assoc, ← heX, ← Category.assoc, ha, Category.assoc]

include B in
/-- **A model of a morphism over a ring of finite type over `ℤ`.** Let `f : U ⟶ X` be a
morphism of algebraic spaces of finite presentation over `Spec A`. There are a ring `A₀` of
finite type over `ℤ` with a map `A₀ → A` and a morphism `f₀ : U₀ ⟶ X₀` of algebraic spaces of
finite presentation over `Spec A₀`, flat if `f` is flat, whose base change along
`Spec A ⟶ Spec A₀` is `f`. -/
theorem exists_finiteType_model_hom (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hU : IsAlgebraicSpace B (Spec (.of A)) hA U)
    (pX : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (pU : U ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hpX : IsFinitePresentation B (Spec (.of A)) hA pX)
    (hpU : IsFinitePresentation B (Spec (.of A)) hA pU) (f : U ⟶ X) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra A₀ A) (_ : Algebra.FiniteType ℤ A₀)
      (hA₀ : B.Contains (Spec (.of A₀))) (X₀ U₀ : (BigFppfOver B (Spec (.of A₀)) hA₀)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (Spec (.of A₀)) hA₀ X₀)
      (_ : IsAlgebraicSpace B (Spec (.of A₀)) hA₀ U₀)
      (pX₀ : X₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA₀))))
      (pU₀ : U₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA₀)))) (f₀ : U₀ ⟶ X₀),
      IsFinitePresentation B (Spec (.of A₀)) hA₀ pX₀ ∧
      IsFinitePresentation B (Spec (.of A₀)) hA₀ pU₀ ∧
      (IsFlat B (Spec (.of A)) hA f → IsFlat B (Spec (.of A₀)) hA₀ f₀) ∧
      ∀ (g : B.obj hA ⟶ B.obj hA₀),
        B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) →
        ∃ (eU : U ≅ (OverShriek.relocalizeRestrict g).obj U₀)
          (eX : X ≅ (OverShriek.relocalizeRestrict g).obj X₀),
          eU.hom ≫ (OverShriek.relocalizeRestrict g).map f₀ = f ≫ eX.hom := by
  obtain ⟨i, X₀, U₀, hX₀, hU₀, pX₀, pU₀, f₀, h₁, h₂, h₃, h₄⟩ :=
    exists_stageModel_hom B hX hU pX pU hpX hpU f
  exact ⟨Algebra.adjoin ℤ (i.unop : Set A), inferInstance, inferInstance,
    finiteType_adjoinFinset_int A i.unop, contains_specAdjoinFinsetDiagram_obj B i, X₀, U₀, hX₀,
    hU₀, pX₀, pU₀, f₀, h₁, h₂, h₃, h₄⟩

end AlgebraicGeometry.Space
