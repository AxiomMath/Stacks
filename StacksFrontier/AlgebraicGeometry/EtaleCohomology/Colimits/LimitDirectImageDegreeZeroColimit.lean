module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageConeShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleAffineSectionsColimit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelCocyclePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelLegPinning
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelTransitionCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLocalizedVanishing

/-!
# Stacks 0EYM in degree zero, in adjoint form

Let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes over a nonempty directed
set with affine transition morphisms, `g_i : X_i ⟶ S_i` a morphism of the first into the second
with every `g_i` quasi-compact and quasi-separated, `X = lim X_i`, `S = lim S_i`, and
`g : X ⟶ S` the limit morphism. Let `(F_i)` be a system of abelian sheaves on the `X_i` and
`𝓕 = colim f_i^{-1}F_i`, presented by maps `ι_i : f_i^{-1}F_i ⟶ 𝓕`, with transposes
`x_i : F_i ⟶ f_{i, *}𝓕`.

This file proves the degree-zero case of [Stacks, Tag 0EYM], `g_* 𝓕 = colim h_i^{-1} g_{i, *}F_i`,
in its adjoint form: for every abelian sheaf `𝒢` on `S` and every family
`σ_i : g_{i, *}F_i ⟶ h_{i, *}𝒢` compatible with the transition maps of the direct images, there is
a unique `χ : g_* 𝓕 ⟶ 𝒢` with `h_{i, *}χ ∘ π_i = σ_i`, where
`π_i = g_{i, *}x_i` followed by the identification `g_{i, *}f_{i, *} ≅ h_{i, *}g_*` of the
projection square (`Stacks.EtaleCohomology.LimitDirectImage.projectionTranspose`).

The proof is the source's. At a level `i` the sheaf `g_{i, *}f_{i, *}𝓕` is, over an affine `V`
étale over `S_i`, the group `𝓕(V ×_{S_i} X)`, and since `V ×_{S_i} X_i` is quasi-compact and
quasi-separated (here the hypotheses on the `g_i` enter) this is the filtered colimit over
`i' ≥ i` of the `F_{i'}(V ×_{S_i} X_{i'})` by [Stacks, Tag 09YQ] in degree zero, read on sections
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.qcqsSections_isColimit`). Hence a map out of
`g_{i, *}f_{i, *}𝓕` is the same as a compatible family of maps out of the
`g_{i, *}f_{i'i, *}F_{i'}` (`Stacks.EtaleCohomology.existsUnique_desc_of_affineSections`). The
family `σ` provides such a family, giving `ρ_i : h_{i, *}g_* 𝓕 ⟶ h_{i, *}𝒢`; the `ρ_i` are
compatible, and so, by the colimit half of [Stacks, Tag 0EYN] on `S` in adjoint form
(`Stacks.EtaleCohomology.AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange`), they are
the `h_{i, *}χ` of a unique `χ`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.legTranspose_compat` — the transposed legs of a
  presented system are compatible with its transition maps.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.existsUnique_levelDescent` — the factorisation at
  a level.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.existsUnique_directImage_desc` — **the
  degree-zero colimit assertion, in adjoint form.**

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology Stacks.EtaleCohomology.LimitDirectImage

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

section Legs

variable {I : Type v} [Preorder I] {DX : Iᵒᵖ ⥤ Scheme.{max u v}} {cX : Cone DX}
  (E : PresentedSystem (c := cX) IsColimitPresentation)

/-- **The transposed legs** `x_i : F_i ⟶ f_{i, *}𝓕` of a presented system: the transposes of the
presentation maps `ι_i : f_i^{-1}F_i ⟶ 𝓕` under the inverse-image/direct-image adjunctions. -/
abbrev legTranspose (i : Iᵒᵖ) :
    E.sys.obj i ⟶ (smallEtalePushforward (cX.π.app i) AddCommGrpCat.{max u v + 1}).obj E.sheaf :=
  systemDirLeg cX E.sys E.sheaf (transportLeg E.sys E.sheaf E.ι) i

/-- **The transposed legs of a presented system are compatible with its transition maps.** -/
theorem legTranspose_compat {i j : Iᵒᵖ} (a : i ⟶ j) :
    legTranspose E j =
      E.sys.mapTranspose a ≫
        (systemPushforward DX AddCommGrpCat.{max u v + 1} a).map (legTranspose E i) ≫
          (coneProjectionComp AddCommGrpCat.{max u v + 1} cX a).hom.app E.sheaf :=
  systemDirLeg_compat cX E.sys E.sheaf (transportLeg E.sys E.sheaf E.ι)
    (fun a => (isCompatibleFamily_iff E.sys E.sheaf E.ι).mp E.pres.compatible a) a

end Legs

section Sections

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{max u v}}

/-- **The transposed transition map on sections is the transpose of the transition map on
sections**, read through the comparison of the two inverse images. -/
theorem mapTranspose_hom_app (F : EtaleSheafSystem D AddCommGrpCat.{max u v + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) (Z : (D.obj j).Etale) :
    (F.mapTranspose a).hom.app (op Z) =
      etaleTransposeSection.{max u v + 1, max u v} (D.map a) (systemTransitionMap F a) Z := by
  have h1 : F.map a = (inverseImageIsoPullbackAb (D.map a)).hom.app (F.obj j) ≫
      systemTransitionMap F a := by
    rw [systemTransitionMap_eq, Iso.hom_inv_id_app_assoc]
  have h2 := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp (smallEtaleAdjunctionAb (D.map a))
    (etaleAbelianInverseImageDirectImageAdj.{max u v, max u v + 1} (D.map a))
    (systemTransitionMap F a)
  exact congrArg (fun z : F.obj j ⟶ (smallEtalePushforwardAb (D.map a)).obj (F.obj i) =>
    z.hom.app (op Z)) ((congrArg ((smallEtaleAdjunctionAb (D.map a)).homEquiv _ _) h1).trans h2)

variable {cX : Cone D} (E : PresentedSystem (c := cX) IsColimitPresentation)
  (i₀ : I) (W : (D.obj (op i₀)).Etale)

/-- **The shifted transposed leg on sections over `W` is the leg on sections of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.qcqsSectionsLeg`.** -/
theorem shiftLeg_legTranspose_hom_app (k : (GeIndex i₀)ᵒᵖ) :
    (shiftLeg (c := cX) (legTranspose E) (geIndexToBase i₀ k)).hom.app (op W) =
      qcqsSectionsLeg D cX E i₀ W k :=
  congrArg₂ (· ≫ ·)
    (systemDirLeg_transportLeg_hom_app cX E.sys E.sheaf E.ι _ _)
    (smallEtalePushforwardComp'_hom_app_hom_app _ _ _ _ _ E.sheaf (op W))

/-- **The shifted transition map on sections over `W` is the transition on sections of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.qcqsSectionsTransition`.** -/
theorem shiftTransition_hom_app {j k : (GeIndex i₀)ᵒᵖ} (b : k ⟶ j) :
    (shiftTransition AddCommGrpCat.{max u v + 1} E.sys.mapTranspose ((geIndexOpFunctor i₀).map b)
        (geIndexToBase i₀ j) (geIndexToBase i₀ k) (Subsingleton.elim _ _)).hom.app (op W) =
      qcqsSectionsTransition D cX E i₀ W b :=
  congrArg₂ (· ≫ ·) (mapTranspose_hom_app E.sys _ _)
    (smallEtalePushforwardComp'_hom_app_hom_app _ _ _ _ _ _ (op W))

end Sections

section Level

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {DX DS : Iᵒᵖ ⥤ Scheme.{max u v}} (γ : DX ⟶ DS) {cX : Cone DX} (hcX : IsLimit cX)
  (cS : Cone DS) (hcS : IsLimit cS)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)]
  (E : PresentedSystem (c := cX) IsColimitPresentation)
  {𝒢 : Sheaf (smallEtaleTopology cS.pt) AddCommGrpCat.{max u v + 1}}

/-- The compatibility of a family of maps out of the direct images `g_{i, *}F_i` with their
transposed transition maps `Stacks.EtaleCohomology.LimitDirectImage.directTransition`. -/
def IsDirectImageFamily
    (σ : ∀ i : Iᵒᵖ, directImage γ AddCommGrpCat.{max u v + 1} E.sys i ⟶
      (smallEtalePushforward (cS.π.app i) AddCommGrpCat.{max u v + 1}).obj 𝒢) : Prop :=
  ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    σ j = directTransition γ AddCommGrpCat.{max u v + 1} E.sys a ≫
      (systemPushforward DS AddCommGrpCat.{max u v + 1} a).map (σ i) ≫
        (coneProjectionComp AddCommGrpCat.{max u v + 1} cS a).hom.app 𝒢

/-- The transposed cocone maps `π_i : g_{i, *}F_i ⟶ h_{i, *}g_* 𝓕` of a presented system. -/
abbrev legProjection :=
  projectionTranspose γ AddCommGrpCat.{max u v + 1} cX cS hcS E.sys (legTranspose E)

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)] in
/-- The transposed cocone maps form an `IsDirectImageFamily`. -/
theorem isDirectImageFamily_legProjection :
    IsDirectImageFamily γ cS E (legProjection γ cS hcS E) :=
  fun a => projectionTranspose_compat γ AddCommGrpCat.{max u v + 1} cX cS hcS E.sys
    (legTranspose E) (fun a => legTranspose_compat E a) a

variable {σ : ∀ i : Iᵒᵖ, directImage γ AddCommGrpCat.{max u v + 1} E.sys i ⟶
  (smallEtalePushforward (cS.π.app i) AddCommGrpCat.{max u v + 1}).obj 𝒢}

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)] in
/-- The quasi-compactness and quasi-separatedness of the base change to `X_{i₀}` of an affine
étale `S_{i₀}`-scheme, which is where the hypotheses on the `g_i` enter. -/
theorem qcqs_baseChange_affineEtale (i₀ : I) (V : (DS.obj (op i₀)).AffineEtale) :
    CompactSpace ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)).left ∧
      QuasiSeparatedSpace
        ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)).left := by
  have : CompactSpace
      ↥((𝟭 Scheme.{max u v}).obj ((AffineEtale.Spec (DS.obj (op i₀))).obj V).left) :=
    inferInstanceAs (CompactSpace (Spec _))
  have : QuasiSeparatedSpace
      ↥((𝟭 Scheme.{max u v}).obj ((AffineEtale.Spec (DS.obj (op i₀))).obj V).left) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec _))
  have : QuasiCompact (γ.app (op i₀)) := inferInstance
  have : QuasiSeparated (γ.app (op i₀)) := inferInstance
  have : QuasiCompact (pullback.fst ((AffineEtale.Spec _).obj V).hom (γ.app (op i₀))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback ((AffineEtale.Spec _).obj V).hom (γ.app (op i₀))).flip
      inferInstance
  have : QuasiSeparated (pullback.fst ((AffineEtale.Spec _).obj V).hom (γ.app (op i₀))) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback ((AffineEtale.Spec _).obj V).hom (γ.app (op i₀))).flip
      inferInstance
  have h₁ := QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst ((AffineEtale.Spec _).obj V).hom (γ.app (op i₀)))
  have h₂ := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst ((AffineEtale.Spec _).obj V).hom (γ.app (op i₀)))
  exact ⟨h₁, h₂⟩

include hcX in
/-- **The factorisation at a level**, through the filtered colimit of sections of
[Stacks, Tag 09YQ] over the base changes of affine étale `S_{i₀}`-schemes to the
quasi-compact quasi-separated `X_{i₀}`. -/
theorem existsUnique_levelMap (hσ : IsDirectImageFamily γ cS E σ) (i₀ : I) :
    ∃! σ' : (smallEtalePushforward (γ.app (op i₀)) AddCommGrpCat.{max u v + 1}).obj
        ((smallEtalePushforward (cX.π.app (op i₀)) AddCommGrpCat.{max u v + 1}).obj E.sheaf) ⟶
        (smallEtalePushforward (cS.π.app (op i₀)) AddCommGrpCat.{max u v + 1}).obj 𝒢,
      ∀ k : (GeIndex i₀)ᵒᵖ,
        (smallEtalePushforward (γ.app (op i₀)) AddCommGrpCat.{max u v + 1}).map
            (shiftLeg (c := cX) (legTranspose E) (geIndexToBase i₀ k)) ≫ σ' =
          (transitionSquareIso γ AddCommGrpCat.{max u v + 1} (geIndexToBase i₀ k)).hom.app
              (E.sys.obj ((geIndexOpFunctor i₀).obj k)) ≫
            shiftLeg (c := cS) σ (geIndexToBase i₀ k) := by
  have hcol := fun V : (DS.obj (op i₀)).AffineEtale =>
    have : Etale ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)).hom :=
      ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)).prop
    have := (qcqs_baseChange_affineEtale γ i₀ V).1
    have := (qcqs_baseChange_affineEtale γ i₀ V).2
    qcqsSections_isColimit DX cX E i₀
      ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)) hcX
  refine existsUnique_desc_of_affineSections (X := DS.obj (op i₀)) (J := (GeIndex i₀)ᵒᵖ)
    (fun {j k} b => (smallEtalePushforward (γ.app (op i₀)) AddCommGrpCat.{max u v + 1}).map
      (shiftTransition AddCommGrpCat.{max u v + 1} E.sys.mapTranspose ((geIndexOpFunctor i₀).map b)
        (geIndexToBase i₀ j) (geIndexToBase i₀ k) (Subsingleton.elim _ _)))
    _ ?_ ?_ ?_ ?_ _ ?_
  · intro j j'
    obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) j.unop.1 j'.unop.1
    exact ⟨op ⟨m, j.unop.2.trans h₁⟩, (homOfLE (show j.unop ≤ ⟨m, j.unop.2.trans h₁⟩ from h₁)).op,
      (homOfLE (show j'.unop ≤ ⟨m, j.unop.2.trans h₁⟩ from h₂)).op, trivial⟩
  · intro j k b
    refine ((smallEtalePushforward (γ.app (op i₀)) AddCommGrpCat.{max u v + 1}).map_comp _
      _).symm.trans (congrArg (smallEtalePushforward (γ.app (op i₀))
        AddCommGrpCat.{max u v + 1}).map ?_)
    exact shiftTransition_comp_shiftLeg E.sys.mapTranspose (legTranspose E)
      (fun a => legTranspose_compat E a)
      _ _ _ _
  · intro V x
    obtain ⟨k, t, ht⟩ := (hcol V).1 x
    exact ⟨k, t, (ConcreteCategory.congr_hom (shiftLeg_legTranspose_hom_app E i₀ _ k) t).trans ht⟩
  · intro V k t ht
    obtain ⟨k', b, hb⟩ := (hcol V).2 k t
      ((ConcreteCategory.congr_hom (shiftLeg_legTranspose_hom_app E i₀ _ k) t).symm.trans ht)
    exact ⟨k', b, (ConcreteCategory.congr_hom (shiftTransition_hom_app E i₀ _ b) t).trans hb⟩
  · intro j k b
    have h₁ := shiftTransition_transitionSquareIso γ AddCommGrpCat.{max u v + 1} E.sys
      ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ j) (geIndexToBase i₀ k)
      (Subsingleton.elim _ _)
    have h₂ := shiftTransition_comp_shiftLeg (c := cS)
      (directTransition γ AddCommGrpCat.{max u v + 1} E.sys) σ hσ
      ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ j) (geIndexToBase i₀ k)
      (Subsingleton.elim _ _)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ shiftLeg (c := cS) σ
      (geIndexToBase i₀ k)) h₁).trans ((Category.assoc _ _ _).trans (congrArg
        ((transitionSquareIso γ AddCommGrpCat.{max u v + 1} (geIndexToBase i₀ j)).hom.app
          (E.sys.obj ((geIndexOpFunctor i₀).obj j)) ≫ ·) h₂)))

include hcX in
/-- **The factorisation at a level, read on `S`.** For a compatible family `σ_i` there is a unique
`ρ : h_{i₀, *}g_* 𝓕 ⟶ h_{i₀, *}𝒢` such that, for every transition `a : i ⟶ i₀`, the shifted
transposed cocone map from `i` followed by `ρ` is the shifted `σ_i`. -/
theorem existsUnique_levelDescent (hσ : IsDirectImageFamily γ cS E σ) (i₀ : I) :
    ∃! ρ : (smallEtalePushforward (cS.π.app (op i₀)) AddCommGrpCat.{max u v + 1}).obj
        ((smallEtalePushforward (limitMorphism γ cX cS hcS) AddCommGrpCat.{max u v + 1}).obj
          E.sheaf) ⟶
        (smallEtalePushforward (cS.π.app (op i₀)) AddCommGrpCat.{max u v + 1}).obj 𝒢,
      ∀ {m : Iᵒᵖ} (a : m ⟶ op i₀),
        shiftLeg (c := cS) (legProjection γ cS hcS E) a ≫ ρ = shiftLeg (c := cS) σ a := by
  obtain ⟨σ', hσ', hu⟩ := existsUnique_levelMap γ hcX cS E hσ i₀
  have key : ∀ k : (GeIndex i₀)ᵒᵖ,
      (smallEtalePushforward (γ.app (op i₀)) AddCommGrpCat.{max u v + 1}).map
          (shiftLeg (c := cX) (legTranspose E) (geIndexToBase i₀ k)) ≫
        (projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)).hom.app E.sheaf =
      (transitionSquareIso γ AddCommGrpCat.{max u v + 1} (geIndexToBase i₀ k)).hom.app
          (E.sys.obj ((geIndexOpFunctor i₀).obj k)) ≫
        shiftLeg (c := cS) (legProjection γ cS hcS E) (geIndexToBase i₀ k) :=
    fun k => shiftLeg_projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS E.sys
      (legTranspose E) _
  refine ⟨(projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)).inv.app E.sheaf ≫
    σ', fun {m} a => ?_, fun z hz => ?_⟩
  · have hall : ∀ k : (GeIndex i₀)ᵒᵖ,
        shiftLeg (c := cS) (legProjection γ cS hcS E) (geIndexToBase i₀ k) ≫
            (projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)).inv.app
              E.sheaf ≫ σ' =
          shiftLeg (c := cS) σ (geIndexToBase i₀ k) := by
      intro k
      refine (cancel_epi ((transitionSquareIso γ AddCommGrpCat.{max u v + 1}
        (geIndexToBase i₀ k)).hom.app (E.sys.obj ((geIndexOpFunctor i₀).obj k)))).mp ?_
      calc _ = ((transitionSquareIso γ AddCommGrpCat.{max u v + 1} (geIndexToBase i₀ k)).hom.app
              (E.sys.obj ((geIndexOpFunctor i₀).obj k)) ≫
            shiftLeg (c := cS) (legProjection γ cS hcS E) (geIndexToBase i₀ k)) ≫
            (projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)).inv.app
              E.sheaf ≫ σ' := (Category.assoc _ _ _).symm
        _ = ((smallEtalePushforward (γ.app (op i₀)) AddCommGrpCat.{max u v + 1}).map
              (shiftLeg (c := cX) (legTranspose E) (geIndexToBase i₀ k)) ≫
            (projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)).hom.app
              E.sheaf) ≫
            (projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)).inv.app
              E.sheaf ≫ σ' := by rw [key k]
        _ = (smallEtalePushforward (γ.app (op i₀)) AddCommGrpCat.{max u v + 1}).map
              (shiftLeg (c := cX) (legTranspose E) (geIndexToBase i₀ k)) ≫ σ' := by
          rw [Category.assoc, Iso.hom_inv_id_app_assoc]
        _ = _ := hσ' k
    exact hall (op ⟨m.unop, leOfHom a.unop⟩)
  · have h : (projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)).hom.app
        E.sheaf ≫ z = σ' :=
      hu _ fun k => by rw [reassoc_of% (key k), hz]
    rw [← h]
    exact (Iso.inv_hom_id_app_assoc
      (projectionSquareIso γ AddCommGrpCat.{max u v + 1} cX cS hcS (op i₀)) E.sheaf z).symm

include hcX in
/-- **[Stacks, Tag 0EYM] in degree zero, in adjoint form.** Let `X = lim X_i` and `S = lim S_i`
with affine transition morphisms over a nonempty directed set, `g_i : X_i ⟶ S_i` quasi-compact and
quasi-separated with limit `g : X ⟶ S`, and `E` a presented system `𝓕 = colim f_i^{-1}F_i`. Then
for every abelian sheaf `𝒢` on `S` and every family `σ_i : g_{i, *}F_i ⟶ h_{i, *}𝒢` compatible
with the transition maps of the direct images, there is a unique `χ : g_* 𝓕 ⟶ 𝒢` with
`h_{i, *}χ ∘ π_i = σ_i`, `π_i` being the transposed cocone maps. -/
theorem existsUnique_directImage_desc [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    (hσ : IsDirectImageFamily γ cS E σ) :
    ∃! χ : (smallEtalePushforward (limitMorphism γ cX cS hcS) AddCommGrpCat.{max u v + 1}).obj
        E.sheaf ⟶ 𝒢,
      ∀ i : Iᵒᵖ, legProjection γ cS hcS E i ≫
        (smallEtalePushforward (cS.π.app i) AddCommGrpCat.{max u v + 1}).map χ = σ i := by
  choose ρ hρ hρu using fun i₀ : I => existsUnique_levelDescent γ hcX cS hcS E hσ i₀
  have hπ : IsDirectImageFamily γ cS E (legProjection γ cS hcS E) :=
    isDirectImageFamily_legProjection γ cS hcS E
  have hcompat : IsDirectImageCompatible cS
      ((smallEtalePushforward (limitMorphism γ cX cS hcS) AddCommGrpCat.{max u v + 1}).obj E.sheaf)
      𝒢 (fun i => ρ i.unop) := by
    intro i j a
    refine (hρu j.unop _ (fun {m} a'' => ?_)).symm
    obtain ⟨n, h₁, h₂⟩ := directed_of (· ≤ ·) m.unop i.unop
    have s₁ := shiftTransition_comp_shiftLeg (c := cS)
      (directTransition γ AddCommGrpCat.{max u v + 1} E.sys) (legProjection γ cS hcS E) hπ
      (homOfLE h₁).op a'' ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _)
    have s₂ := shiftTransition_comp_shiftLeg (c := cS)
      (directTransition γ AddCommGrpCat.{max u v + 1} E.sys) σ hσ
      (homOfLE h₁).op a'' ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _)
    have c₁ := shiftLeg_cancel (c := cS) (homOfLE h₂).op a ((homOfLE h₂).op ≫ a) rfl
      (legProjection γ cS hcS E (op n)) (σ (op n)) (ρ i.unop)
      (by
        have h := hρ i.unop (homOfLE h₂).op
        simp only [shiftLeg, Category.assoc] at h
        exact h)
    rw [← s₁, ← s₂]
    exact (Category.assoc _ _ _).trans (congrArg (shiftTransition AddCommGrpCat.{max u v + 1}
      (directTransition γ AddCommGrpCat.{max u v + 1} E.sys) (homOfLE h₁).op a''
        ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _) ≫ ·) ((Category.assoc _ _ _).trans c₁))
  have hsmall : Small.{max u v} ↥(Set.range DS.obj ∪ {cS.pt} : Set Scheme.{max u v}) := by
    have : Small.{max u v} ↥(Set.range DS.obj) := small_range _
    infer_instance
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small
    (Set.range DS.obj ∪ {cS.pt} : Set Scheme.{max u v})
  obtain ⟨χ, hχ, hχu⟩ := AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange DS cS B
    (fun i => hB _ (Or.inl ⟨i, rfl⟩)) (hB _ (Or.inr rfl)) hcS
    ((smallEtalePushforward (limitMorphism γ cX cS hcS) AddCommGrpCat.{max u v + 1}).obj E.sheaf)
    𝒢 (fun i => ρ i.unop) hcompat
  refine ⟨χ, fun i => ?_, fun χ' hχ' => hχu χ' fun i => ?_⟩
  · refine (congrArg (legProjection γ cS hcS E i ≫ ·) (hχ i)).trans ?_
    refine (congrArg (· ≫ ρ i.unop) (hπ (𝟙 i))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (directTransition γ AddCommGrpCat.{max u v + 1} E.sys (𝟙 i) ≫ ·)
      (hρ i.unop (𝟙 i))).trans (hσ (𝟙 i)).symm
  · refine hρu i.unop _ fun {m} a => ?_
    change shiftLeg (c := cS) (legProjection γ cS hcS E) a ≫
        (smallEtalePushforward (cS.π.app (op i.unop)) AddCommGrpCat.{max u v + 1}).map χ' =
      shiftLeg (c := cS) σ a
    have hn := (coneProjectionComp AddCommGrpCat.{max u v + 1} cS a).hom.naturality χ'
    dsimp only [Functor.comp_map] at hn
    simp only [shiftLeg, Category.assoc]
    rw [← hn, ← Functor.map_comp_assoc, hχ' m]

end Level

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
