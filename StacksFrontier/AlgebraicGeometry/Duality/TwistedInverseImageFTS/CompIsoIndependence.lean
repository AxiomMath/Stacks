module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.PseudoFunctor

/-!
# Independence of the composition isomorphism of upper shriek functors

For morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` of `FTS_S` over a Noetherian base, the isomorphism
`(f ≫ g)^! ≅ f^! ∘ g^!` on `D⁺_QCoh` of [Stacks, Tag 0ATX] can be computed through any
compactification `R ⊇ Q ⊇ X` of `X` over any compactification `Ȳ` of `g`, and changing the
compactifications of `f`, `g` and `f ≫ g` conjugates it by the isomorphisms of
[Stacks, Tag 0AA0].

## Main results

* `Stacks.Duality.upperShriekPlusIso_trans`: the isomorphisms of [Stacks, Tag 0AA0] compose.
* `Stacks.Duality.NestedCompactification.upperShriekCompIso_eq_compIsoVia`: the composition
  isomorphism through an arbitrary nested compactification.
* `Stacks.Duality.NestedCompactification.upperShriekCompIso_eq_conj`: the dependence on the
  compactifications.

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

section DominatingIdentities

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S] {X Y : FTS S}
  (f : X ⟶ Y)

/-- `α` of the identity morphism of a compactification is the identity. -/
theorem upperShriekCompactificationIso_id (c : CompactificationOf (Over.mk f.left)) :
    upperShriekCompactificationIso f c c (𝟙 c.space) (Category.id_comp _)
      (IsPullback.id_vert c.immersion) = Iso.refl _ := by
  have h := upperShriekCompactificationIso_trans f c c c (𝟙 c.space) (𝟙 c.space)
    (Category.id_comp _) (Category.id_comp _) (IsPullback.id_vert c.immersion)
    (IsPullback.id_vert c.immersion) (by simp) (by simpa using IsPullback.id_vert c.immersion)
  rw [upperShriekCompactificationIso_congr f (Category.id_comp (𝟙 c.space)) _ _
    (Category.id_comp _) (IsPullback.id_vert c.immersion)] at h
  ext1
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom] at h'
  rw [← cancel_epi (upperShriekCompactificationIso f c c (𝟙 c.space) (Category.id_comp _)
      (IsPullback.id_vert c.immersion)).hom]
  simpa using h'.symm

/-- The isomorphism of [Stacks, Tag 0AA0] between the upper shriek functors of a compactification
and itself is the identity. -/
theorem upperShriekPlusIso_refl (c : CompactificationOf (Over.mk f.left)) :
    DominatingCompactification.upperShriekPlusIso f c c = Iso.refl _ := by
  rw [upperShriekPlusIso_eq_of_span f c c c (𝟙 c.space) (𝟙 c.space) (Category.id_comp _)
    (Category.id_comp _) (IsPullback.id_vert c.immersion) (IsPullback.id_vert c.immersion)]
  simp

/-- For a morphism `g : X̄₁ ⟶ X̄₂` of compactifications with `g⁻¹(X) = X`, the isomorphism of
[Stacks, Tag 0AA0] is `α_g`. -/
theorem upperShriekPlusIso_eq_upperShriekCompactificationIso
    (c₁ c₂ : CompactificationOf (Over.mk f.left)) (g : c₁.space ⟶ c₂.space) [IsProper g]
    (hg : g ≫ c₂.toBase = c₁.toBase) (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion) :
    DominatingCompactification.upperShriekPlusIso f c₁ c₂ =
      upperShriekCompactificationIso f c₁ c₂ g hg sq := by
  rw [upperShriekPlusIso_eq_of_span f c₁ c₁ c₂ (𝟙 c₁.space) g (Category.id_comp _) hg
    (IsPullback.id_vert c₁.immersion) sq, upperShriekCompactificationIso_id]
  simp

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma isProper_comp_of {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (ha : IsProper a)
    (hb : IsProper b) : IsProper (a ≫ b) :=
  MorphismProperty.comp_mem @IsProper _ _ ha hb

private lemma upperShriekPlusIso_trans_of_span (W c₁ c₂ c₃ : CompactificationOf (Over.mk f.left))
    (u₁ : W.space ⟶ c₁.space) (u₂ : W.space ⟶ c₂.space) (u₃ : W.space ⟶ c₃.space)
    (i₁ : IsProper u₁) (i₂ : IsProper u₂) (i₃ : IsProper u₃)
    (hu₁ : u₁ ≫ c₁.toBase = W.toBase) (hu₂ : u₂ ≫ c₂.toBase = W.toBase)
    (hu₃ : u₃ ≫ c₃.toBase = W.toBase)
    (sq₁ : IsPullback W.immersion (𝟙 X.left) u₁ c₁.immersion)
    (sq₂ : IsPullback W.immersion (𝟙 X.left) u₂ c₂.immersion)
    (sq₃ : IsPullback W.immersion (𝟙 X.left) u₃ c₃.immersion) :
    DominatingCompactification.upperShriekPlusIso f c₁ c₂ ≪≫
        DominatingCompactification.upperShriekPlusIso f c₂ c₃ =
      DominatingCompactification.upperShriekPlusIso f c₁ c₃ := by
  rw [upperShriekPlusIso_eq_of_span f W c₁ c₂ u₁ u₂ hu₁ hu₂ sq₁ sq₂,
    upperShriekPlusIso_eq_of_span f W c₂ c₃ u₂ u₃ hu₂ hu₃ sq₂ sq₃,
    upperShriekPlusIso_eq_of_span f W c₁ c₃ u₁ u₃ hu₁ hu₃ sq₁ sq₃]
  simp

/-- **Transitivity of the isomorphisms of [Stacks, Tag 0AA0]**: `f^!_{c₁} ≅ f^!_{c₂} ≅ f^!_{c₃}`
is `f^!_{c₁} ≅ f^!_{c₃}`. -/
theorem upperShriekPlusIso_trans (c₁ c₂ c₃ : CompactificationOf (Over.mk f.left)) :
    DominatingCompactification.upperShriekPlusIso f c₁ c₂ ≪≫
        DominatingCompactification.upperShriekPlusIso f c₂ c₃ =
      DominatingCompactification.upperShriekPlusIso f c₁ c₃ := by
  have p₁ := (DominatingCompactification.isPullback_fst f
    (DominatingCompactification.compactification f c₁ c₂) c₃).paste_vert
    (DominatingCompactification.isPullback_fst f c₁ c₂)
  have p₂ := (DominatingCompactification.isPullback_fst f
    (DominatingCompactification.compactification f c₁ c₂) c₃).paste_vert
    (DominatingCompactification.isPullback_snd f c₁ c₂)
  simp only [Category.comp_id] at p₁ p₂
  exact upperShriekPlusIso_trans_of_span f (DominatingCompactification.compactification f
    (DominatingCompactification.compactification f c₁ c₂) c₃) c₁ c₂ c₃ _ _
    (DominatingCompactification.snd f _ c₃)
    (isProper_comp_of _ _ (inferInstance : IsProper (DominatingCompactification.fst f _ c₃))
      (inferInstance : IsProper (DominatingCompactification.fst f c₁ c₂)))
    (isProper_comp_of _ _ (inferInstance : IsProper (DominatingCompactification.fst f _ c₃))
      (inferInstance : IsProper (DominatingCompactification.snd f c₁ c₂)))
    (inferInstance : IsProper (DominatingCompactification.snd f _ c₃))
    (Category.assoc _ _ _)
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (DominatingCompactification.fst_comp_toBase f c₁ c₂).symm))
    (DominatingCompactification.fst_comp_toBase f _ c₃).symm p₁ p₂
    (DominatingCompactification.isPullback_snd f _ c₃)

/-- The isomorphisms of [Stacks, Tag 0AA0] in the two directions are inverse. -/
theorem upperShriekPlusIso_symm (c₁ c₂ : CompactificationOf (Over.mk f.left)) :
    (DominatingCompactification.upperShriekPlusIso f c₁ c₂).symm =
      DominatingCompactification.upperShriekPlusIso f c₂ c₁ := by
  have h := upperShriekPlusIso_trans f c₁ c₂ c₁
  rw [upperShriekPlusIso_refl] at h
  rw [← Iso.symm_self_id_assoc (DominatingCompactification.upperShriekPlusIso f c₁ c₂)
    (DominatingCompactification.upperShriekPlusIso f c₂ c₁), h, Iso.trans_refl]

end DominatingIdentities

end Stacks.Duality

namespace Stacks.Duality.NestedCompactification

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y Z : FTS S} {f : X ⟶ Y}
  {g : Y ⟶ Z}

section MapQ

variable {cg₁ cg₂ : CompactificationOf (Over.mk g.left)} (N₁ : NestedCompactification f g cg₁)
  (N₂ : NestedCompactification f g cg₂) {ψ : cg₁.space ⟶ cg₂.space}
  (sqψ : IsPullback cg₁.immersion (𝟙 Y.left) ψ cg₂.immersion)
  (φ : N₁.R ⟶ N₂.R) (hφ : φ ≫ N₂.r = N₁.r ≫ ψ)

/-- The restriction `Q₁ ⟶ Q₂` of a morphism `R₁ ⟶ R₂` of nested compactifications over
`Ȳ₁ ⟶ Ȳ₂`. -/
noncomputable def mapQ : N₁.Q ⟶ N₂.Q :=
  N₂.isPullback.lift (N₁.v ≫ φ) N₁.rQ (by
    rw [Category.assoc, hφ, ← Category.assoc, N₁.isPullback.w, Category.assoc, sqψ.w]
    simp)

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The restriction `Q₁ ⟶ Q₂` composed with `Q₂ ⟶ R₂` is `Q₁ ⟶ R₁ ⟶ R₂`. -/
@[reassoc (attr := simp)]
theorem mapQ_v : mapQ N₁ N₂ sqψ φ hφ ≫ N₂.v = N₁.v ≫ φ := IsPullback.lift_fst _ _ _ _

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The restriction `Q₁ ⟶ Q₂` lies over the identity of `Y`. -/
@[reassoc (attr := simp)]
theorem mapQ_rQ : mapQ N₁ N₂ sqψ φ hφ ≫ N₂.rQ = N₁.rQ := IsPullback.lift_snd _ _ _ _

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The restriction of a morphism of nested compactifications is cartesian over `X`. -/
theorem isPullback_mapQ (sqφ : IsPullback N₁.u (𝟙 X.left) φ N₂.u) :
    IsPullback N₁.uQ (𝟙 X.left) (mapQ N₁ N₂ sqψ φ hφ) N₂.uQ := by
  have sqF : IsPullback N₁.v (mapQ N₁ N₂ sqψ φ hφ) φ N₂.v := by
    refine IsPullback.of_bot ?_ (mapQ_v N₁ N₂ sqψ φ hφ).symm N₂.isPullback
    rw [mapQ_rQ, hφ]
    simpa using N₁.isPullback.paste_vert sqψ
  refine IsPullback.of_right ?_ ?_ sqF
  · rw [N₁.uQ_v, N₂.uQ_v]; exact sqφ
  · apply N₂.isPullback.hom_ext
    · simp only [Category.assoc, mapQ_v]
      rw [← Category.assoc, N₁.uQ_v, N₂.uQ_v]
      simpa using sqφ.w
    · simp [N₁.uQ_rQ, N₂.uQ_rQ]

end MapQ

section Dominate

variable {cg₁ cg₂ : CompactificationOf (Over.mk g.left)} (N₁ : NestedCompactification f g cg₁)
  (N₂ : NestedCompactification f g cg₂) {ψ : cg₁.space ⟶ cg₂.space}
  (sqψ : IsPullback cg₁.immersion (𝟙 Y.left) ψ cg₂.immersion)

omit [CompactSpace S] [QuasiSeparatedSpace S] in
include sqψ in
/-- The square `X ⟶ R₁ ⟶ Ȳ₁ ⟶ Ȳ₂` and `X ⟶ R₂ ⟶ Ȳ₂` commutes. -/
theorem dominate_comm : N₁.u ≫ N₁.r ≫ ψ = 𝟙 X.left ≫ N₂.u ≫ N₂.r := by
  rw [reassoc_of% N₁.u_r, N₂.u_r, Category.id_comp, sqψ.w]
  simp

/-- The graph `X ⟶ R₁ ×_{Ȳ₂} R₂`. -/
noncomputable abbrev dominateGraph : X.left ⟶ pullback (N₁.r ≫ ψ) N₂.r :=
  GraphClosure.graph (N₁.r ≫ ψ) N₂.r N₁.u N₂.u (𝟙 X.left) (dominate_comm N₁ N₂ sqψ)

/-- The graph `X ⟶ R₁ ×_{Ȳ₂} R₂` is quasi-compact. -/
theorem quasiCompact_dominateGraph : QuasiCompact (dominateGraph N₁ N₂ sqψ) := by
  have : QuasiCompact (dominateGraph N₁ N₂ sqψ ≫ pullback.fst (N₁.r ≫ ψ) N₂.r) := by
    rw [GraphClosure.graph_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst (N₁.r ≫ ψ) N₂.r)

/-- The graph `X ⟶ R₁ ×_{Ȳ₂} R₂` is an open immersion into the closure of its image. -/
instance : IsOpenImmersion (dominateGraph N₁ N₂ sqψ).toImage := by
  have := quasiCompact_dominateGraph N₁ N₂ sqψ
  have : IsImmersion (dominateGraph N₁ N₂ sqψ) := GraphClosure.isImmersion_graph _ _ _ _ _ _
  infer_instance

/-- The projection of the closure of the graph to `R₁`. -/
noncomputable abbrev dominateFst : (dominateGraph N₁ N₂ sqψ).image ⟶ N₁.R :=
  GraphClosure.closureFst (N₁.r ≫ ψ) N₂.r N₁.u N₂.u (𝟙 X.left) (dominate_comm N₁ N₂ sqψ)

/-- The projection of the closure of the graph to `R₂`. -/
noncomputable abbrev dominateSnd : (dominateGraph N₁ N₂ sqψ).image ⟶ N₂.R :=
  GraphClosure.closureSnd (N₁.r ≫ ψ) N₂.r N₁.u N₂.u (𝟙 X.left) (dominate_comm N₁ N₂ sqψ)

/-- The projection of the closure of the graph to `R₁` is proper. -/
instance : IsProper (dominateFst N₁ N₂ sqψ) := by
  dsimp [dominateFst, GraphClosure.closureFst]; infer_instance

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The composite `X ⟶ R ⟶ R₁ ⟶ Ȳ₁` is `X ⟶ Y ⟶ Ȳ₁`. -/
theorem dominate_u_r : (dominateGraph N₁ N₂ sqψ).toImage ≫ dominateFst N₁ N₂ sqψ ≫ N₁.r =
    f.left ≫ cg₁.immersion :=
  (GraphClosure.toImage_closureFst_assoc _ _ _ _ _ _ _).trans N₁.u_r

/-- **A nested compactification dominating two others**: for nested compactifications `R₁`
over `Ȳ₁` and `R₂` over `Ȳ₂` and a morphism `ψ : Ȳ₁ ⟶ Ȳ₂` of compactifications of `Y`, the
closure of `X` in `R₁ ×_{Ȳ₂} R₂`, as a nested compactification over `Ȳ₁`. -/
noncomputable def dominate : NestedCompactification f g cg₁ where
  R := (dominateGraph N₁ N₂ sqψ).image
  r := dominateFst N₁ N₂ sqψ ≫ N₁.r
  u := (dominateGraph N₁ N₂ sqψ).toImage
  u_r := dominate_u_r N₁ N₂ sqψ
  Q := pullback (dominateFst N₁ N₂ sqψ ≫ N₁.r) cg₁.immersion
  v := pullback.fst _ _
  rQ := pullback.snd _ _
  isPullback := IsPullback.of_hasPullback _ _
  uQ := pullback.lift _ _ (dominate_u_r N₁ N₂ sqψ)
  uQ_v := pullback.lift_fst _ _ _
  uQ_rQ := pullback.lift_snd _ _ _

/-- The scheme of the dominating nested compactification is the closure of the graph. -/
@[simp] theorem dominate_R : (dominate N₁ N₂ sqψ).R = (dominateGraph N₁ N₂ sqψ).image := rfl
/-- The morphism to `Ȳ₁` of the dominating nested compactification is `R ⟶ R₁ ⟶ Ȳ₁`. -/
@[simp] theorem dominate_r : (dominate N₁ N₂ sqψ).r = dominateFst N₁ N₂ sqψ ≫ N₁.r := rfl
/-- The immersion of `X` into the dominating nested compactification is the graph. -/
@[simp] theorem dominate_u : (dominate N₁ N₂ sqψ).u = (dominateGraph N₁ N₂ sqψ).toImage := rfl

/-- The projection `R ⟶ R₁` lies over the identity of `Ȳ₁`. -/
theorem dominateFst_r : dominateFst N₁ N₂ sqψ ≫ N₁.r = (dominate N₁ N₂ sqψ).r ≫ 𝟙 _ :=
  (Category.comp_id _).symm

/-- The projection `R ⟶ R₂` lies over `ψ : Ȳ₁ ⟶ Ȳ₂`. -/
theorem dominateSnd_r : dominateSnd N₁ N₂ sqψ ≫ N₂.r = (dominate N₁ N₂ sqψ).r ≫ ψ := by
  simp [dominateSnd, dominateFst, GraphClosure.closureFst, GraphClosure.closureSnd,
    pullback.condition]

/-- The projection `R ⟶ R₁` is cartesian over `X`. -/
theorem isPullback_dominateFst :
    IsPullback (dominate N₁ N₂ sqψ).u (𝟙 X.left) (dominateFst N₁ N₂ sqψ) N₁.u :=
  have := quasiCompact_dominateGraph N₁ N₂ sqψ
  isPullback_id_of_preimage_opensRange_eq _ _ _ (GraphClosure.toImage_closureFst _ _ _ _ _ _)
    (GraphClosure.preimage_closureFst _ _ _ _ _ _)

/-- The projection `R ⟶ R₂` is cartesian over `X`. -/
theorem isPullback_dominateSnd (hψ : ψ ≫ cg₂.toBase = cg₁.toBase) :
    IsPullback (dominate N₁ N₂ sqψ).u (𝟙 X.left) (dominateSnd N₁ N₂ sqψ) N₂.u :=
  have := quasiCompact_dominateGraph N₁ N₂ sqψ
  have : IsSeparated ψ := by
    have : IsSeparated (ψ ≫ cg₂.toBase) := by rw [hψ]; infer_instance
    exact IsSeparated.of_comp ψ cg₂.toBase
  isPullback_id_of_preimage_opensRange_eq _ _ _
    ((GraphClosure.toImage_closureSnd _ _ _ _ _ _).trans (Category.id_comp _))
    (GraphClosure.preimage_closureSnd _ _ _ _ _ _)

end Dominate

section OfComp

variable (f g) (cg : CompactificationOf (Over.mk g.left))
  (cfg : CompactificationOf (Over.mk (f ≫ g).left))

/-- The compactification `P ⊇ Q ⊇ X` of `Stacks.Duality.CompCompactification` as a nested
compactification over `Ȳ`. -/
noncomputable def ofCompCompactification : NestedCompactification f g cg where
  R := CompCompactification.space f g cg cfg
  r := CompCompactification.proj f g cg cfg
  u := CompCompactification.ι f g cg cfg
  u_r := CompCompactification.ι_proj f g cg cfg
  Q := CompCompactification.restrictSpace f g cg cfg
  v := pullback.fst _ _
  rQ := pullback.snd _ _
  isPullback := IsPullback.of_hasPullback _ _
  uQ := CompCompactification.restrictι f g cg cfg
  uQ_v := pullback.lift_fst _ _ _
  uQ_rQ := pullback.lift_snd _ _ _

/-- The comparison `(f ≫ g)^! ⟶ f^! ∘ g^!` of `Stacks.Duality.CompCompactification` is the
comparison of the nested compactification `P ⊇ Q ⊇ X`. -/
theorem upperShriekCompHom_app_eq_compHom (K : quasiCoherentDerivedCategory Z.left) :
    (CompCompactification.upperShriekCompHom f g cg cfg).app K =
      (ofCompCompactification f g cg cfg).compHom.app K := by
  rw [CompCompactification.upperShriekCompHom_app_eq, compHom_app]
  rfl

end OfComp

section Plus

variable [IsNoetherian S] {cg : CompactificationOf (Over.mk g.left)}
  (N : NestedCompactification f g cg)

/-- The comparison `Stacks.Duality.NestedCompactification.compHom` is an isomorphism on
bounded-below objects. -/
theorem isIso_compHom_app (K : quasiCoherentDerivedCategory Z.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) : IsIso (N.compHom.app K) := by
  have := isIso_rightAdjointBaseChange_app_of_isOpenImmersion N.v N.rQ N.r cg.immersion
    N.isPullback _ (isBoundedBelow_twistedInverseImage_obj cg.toBase K hK)
  rw [compHom_app]
  have : IsIso ((openBaseChange N.v N.rQ N.r cg.immersion N.isPullback).app
      ((twistedInverseImage cg.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
        K)) := by
    unfold openBaseChange; assumption
  infer_instance

/-- **The composition isomorphism `(f ≫ g)^! ≅ f^! ∘ g^!` on `D⁺_QCoh` at a nested
compactification** (the proof of [Stacks, Tag 0ATX]): the comparison
`Stacks.Duality.NestedCompactification.compHom` is invertible on bounded-below objects by
[Stacks, Tag 0A9P]. -/
noncomputable def compPlusIso :
    upperShriekPlus (f ≫ g) N.compFG ≅ upperShriekPlus g cg ⋙ upperShriekPlus f N.compF :=
  upperShriekPlusCompIsoOfNatTrans N.compHom N.isIso_compHom_app

/-- The underlying morphism of the composition isomorphism at `K` is the comparison
`Stacks.Duality.NestedCompactification.compHom` at `K`. -/
@[simp]
theorem compPlusIso_hom_app_hom (K : quasiCoherentDerivedCategoryPlusOfModel Z.left) :
    (N.compPlusIso.hom.app K).hom = N.compHom.app K.obj :=
  rfl

end Plus

section NaturalityPlus

variable [IsNoetherian S] {cg₁ cg₂ : CompactificationOf (Over.mk g.left)}
  (N₁ : NestedCompactification f g cg₁) (N₂ : NestedCompactification f g cg₂)
  {ψ : cg₁.space ⟶ cg₂.space} (hψ : ψ ≫ cg₂.toBase = cg₁.toBase)
  (sqψ : IsPullback cg₁.immersion (𝟙 Y.left) ψ cg₂.immersion)
  (φ : N₁.R ⟶ N₂.R) (hφ : φ ≫ N₂.r = N₁.r ≫ ψ)
  (sqφ : IsPullback N₁.u (𝟙 X.left) φ N₂.u)

/-- **Naturality of the composition isomorphism of nested compactifications** on `D⁺_QCoh`. -/
theorem compPlusIso_naturality :
    haveI := isProper_of_comp_toBase (f ≫ g) (c₁ := N₁.compFG) (c₂ := N₂.compFG) φ
      (hφfg N₁ N₂ ψ hψ φ hφ)
    haveI := isProper_of_comp_toBase f (c₁ := N₁.compF) (c₂ := N₂.compF) (mapQ N₁ N₂ sqψ φ hφ)
      (mapQ_rQ N₁ N₂ sqψ φ hφ)
    haveI := isProper_of_comp_toBase g (c₁ := cg₁) (c₂ := cg₂) ψ hψ
    upperShriekCompactificationIso (f ≫ g) N₁.compFG N₂.compFG φ (hφfg N₁ N₂ ψ hψ φ hφ) sqφ ≪≫
        N₂.compPlusIso =
      N₁.compPlusIso ≪≫
        Functor.isoWhiskerLeft (upperShriekPlus g cg₁)
          (upperShriekCompactificationIso f N₁.compF N₂.compF (mapQ N₁ N₂ sqψ φ hφ)
            (mapQ_rQ N₁ N₂ sqψ φ hφ) (isPullback_mapQ N₁ N₂ sqψ φ hφ sqφ)) ≪≫
        Functor.isoWhiskerRight (upperShriekCompactificationIso g cg₁ cg₂ ψ hψ sqψ)
          (upperShriekPlus f N₂.compF) := by
  refine Iso.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  exact compHom_naturality N₁ N₂ ψ hψ sqψ φ hφ sqφ (mapQ N₁ N₂ sqψ φ hφ)
    (mapQ_v N₁ N₂ sqψ φ hφ) (mapQ_rQ N₁ N₂ sqψ φ hφ) (isPullback_mapQ N₁ N₂ sqψ φ hφ sqφ) K.obj

end NaturalityPlus

section Independence

variable [IsNoetherian S] (cf : CompactificationOf (Over.mk f.left))
  (cg : CompactificationOf (Over.mk g.left)) (cfg : CompactificationOf (Over.mk (f ≫ g).left))

/-- The composite `(f ≫ g)^!_{cfg} ≅ (f ≫ g)^!_R ≅ f^!_Q ∘ g^!_{Ȳ} ≅ f^!_{cf} ∘ g^!_{cg}` attached
to a nested compactification `R ⊇ Q ⊇ X` over a compactification `Ȳ` of `g`. -/
noncomputable abbrev compIsoVia {c : CompactificationOf (Over.mk g.left)}
    (N : NestedCompactification f g c) :
    upperShriekPlus (f ≫ g) cfg ≅ upperShriekPlus g cg ⋙ upperShriekPlus f cf :=
  DominatingCompactification.upperShriekPlusIso (f ≫ g) cfg N.compFG ≪≫ N.compPlusIso ≪≫
    Functor.isoWhiskerLeft (upperShriekPlus g c)
      (DominatingCompactification.upperShriekPlusIso f N.compF cf) ≪≫
    Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso g c cg)
      (upperShriekPlus f cf)

/-- `Stacks.Duality.upperShriekCompIso` is computed through the nested compactification
`P ⊇ Q ⊇ X`. -/
theorem upperShriekCompIso_eq_compIsoVia_ofCompCompactification :
    upperShriekCompIso f g cf cg cfg =
      compIsoVia cf cg cfg (ofCompCompactification f g cg cfg) := by
  rw [compIsoVia, upperShriekPlusIso_refl, Functor.isoWhiskerRight_refl, Iso.trans_refl]
  refine Iso.ext (NatTrans.ext (funext fun K => ObjectProperty.hom_ext _ ?_))
  simp only [upperShriekCompIso, Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom]
  congr 1
  congr 1
  exact upperShriekCompHom_app_eq_compHom f g cg cfg K.obj

/-- The composite through a nested compactification does not change along a morphism of nested
compactifications. -/
theorem compIsoVia_eq_of_hom {c₁ c₂ : CompactificationOf (Over.mk g.left)}
    (N₁ : NestedCompactification f g c₁) (N₂ : NestedCompactification f g c₂)
    {ψ : c₁.space ⟶ c₂.space} (hψ : ψ ≫ c₂.toBase = c₁.toBase)
    (sqψ : IsPullback c₁.immersion (𝟙 Y.left) ψ c₂.immersion)
    (φ : N₁.R ⟶ N₂.R) (hφ : φ ≫ N₂.r = N₁.r ≫ ψ) (sqφ : IsPullback N₁.u (𝟙 X.left) φ N₂.u) :
    compIsoVia cf cg cfg N₁ = compIsoVia cf cg cfg N₂ := by
  have h := compPlusIso_naturality N₁ N₂ hψ sqψ φ hφ sqφ
  have := isProper_of_comp_toBase (f ≫ g) (c₁ := N₁.compFG) (c₂ := N₂.compFG) φ
    (hφfg N₁ N₂ ψ hψ φ hφ)
  have := isProper_of_comp_toBase f (c₁ := N₁.compF) (c₂ := N₂.compF)
    (mapQ N₁ N₂ sqψ φ hφ) (mapQ_rQ N₁ N₂ sqψ φ hφ)
  have := isProper_of_comp_toBase g (c₁ := c₁) (c₂ := c₂) ψ hψ
  simp only [compIsoVia]
  rw [← upperShriekPlusIso_trans (f ≫ g) cfg N₁.compFG N₂.compFG,
    upperShriekPlusIso_eq_upperShriekCompactificationIso (f ≫ g) N₁.compFG N₂.compFG φ
      (hφfg N₁ N₂ ψ hψ φ hφ) sqφ, Iso.trans_assoc, reassoc_of% h,
    ← upperShriekPlusIso_trans f N₁.compF N₂.compF cf,
    upperShriekPlusIso_eq_upperShriekCompactificationIso f N₁.compF N₂.compF
      (mapQ N₁ N₂ sqψ φ hφ) (mapQ_rQ N₁ N₂ sqψ φ hφ) (isPullback_mapQ N₁ N₂ sqψ φ hφ sqφ),
    ← upperShriekPlusIso_trans g c₁ c₂ cg,
    upperShriekPlusIso_eq_upperShriekCompactificationIso g c₁ c₂ ψ hψ sqψ,
    Functor.isoWhiskerLeft_trans, Functor.isoWhiskerRight_trans]
  simp only [Iso.trans_assoc]
  rw [← Functor.isoWhiskerLeft_trans_isoWhiskerRight_assoc
    (upperShriekCompactificationIso g c₁ c₂ ψ hψ sqψ)
    (DominatingCompactification.upperShriekPlusIso f N₂.compF cf)]

/-- **The composite through a nested compactification is independent of the nested
compactification** (the independence in [Stacks, Tag 0ATX]): any two nested compactifications,
over any two compactifications of `g`, give the same isomorphism
`(f ≫ g)^!_{cfg} ≅ f^!_{cf} ∘ g^!_{cg}`. -/
theorem compIsoVia_eq {c₁ c₂ : CompactificationOf (Over.mk g.left)}
    (N₁ : NestedCompactification f g c₁) (N₂ : NestedCompactification f g c₂) :
    compIsoVia cf cg cfg N₁ = compIsoVia cf cg cfg N₂ := by
  let D := DominatingCompactification.compactification g c₁ c₂
  let ND := ofCompCompactification f g D cfg
  have hfst : DominatingCompactification.fst g c₁ c₂ ≫ c₁.toBase = D.toBase := rfl
  have hsnd : DominatingCompactification.snd g c₁ c₂ ≫ c₂.toBase = D.toBase :=
    (DominatingCompactification.fst_comp_toBase g c₁ c₂).symm
  have s₁ := DominatingCompactification.isPullback_fst g c₁ c₂
  have s₂ := DominatingCompactification.isPullback_snd g c₁ c₂
  have key : ∀ {c : CompactificationOf (Over.mk g.left)} (N : NestedCompactification f g c)
      {ψ : D.space ⟶ c.space} (hψ : ψ ≫ c.toBase = D.toBase)
      (s : IsPullback D.immersion (𝟙 Y.left) ψ c.immersion),
      compIsoVia cf cg cfg ND = compIsoVia cf cg cfg N := fun {_} N {_} hψ s =>
    (compIsoVia_eq_of_hom cf cg cfg (dominate ND N s) ND (Category.id_comp _)
      (IsPullback.id_vert _) (dominateFst ND N s) (dominateFst_r ND N s)
      (isPullback_dominateFst ND N s)).symm.trans
      (compIsoVia_eq_of_hom cf cg cfg (dominate ND N s) N hψ s (dominateSnd ND N s)
        (dominateSnd_r ND N s) (isPullback_dominateSnd ND N s hψ))
  exact (key N₁ hfst s₁).symm.trans (key N₂ hsnd s₂)

/-- **`Stacks.Duality.upperShriekCompIso` through any nested compactification**: for every
compactification `Ȳ` of `g` and every nested compactification `R ⊇ Q ⊇ X` over it,
`(f ≫ g)^!_{cfg} ≅ f^!_{cf} ∘ g^!_{cg}` is `(f ≫ g)^!_{cfg} ≅ (f ≫ g)^!_R`, the comparison of
the nested compactification, and `f^!_Q ≅ f^!_{cf}`, `g^!_{Ȳ} ≅ g^!_{cg}`. -/
theorem upperShriekCompIso_eq_compIsoVia {c : CompactificationOf (Over.mk g.left)}
    (N : NestedCompactification f g c) :
    upperShriekCompIso f g cf cg cfg = compIsoVia cf cg cfg N :=
  (upperShriekCompIso_eq_compIsoVia_ofCompCompactification cf cg cfg).trans
    (compIsoVia_eq cf cg cfg _ N)

/-- **The composition isomorphisms for two choices of compactifications differ by the
isomorphisms of [Stacks, Tag 0AA0]**: `(f ≫ g)^! ≅ f^! ∘ g^!` at `cf'`, `cg'`, `cfg'` is the one at
`cf`, `cg`, `cfg` conjugated by `(f ≫ g)^!_{cfg'} ≅ (f ≫ g)^!_{cfg}`, `f^!_{cf} ≅ f^!_{cf'}` and
`g^!_{cg} ≅ g^!_{cg'}`. -/
theorem upperShriekCompIso_eq_conj (cf' : CompactificationOf (Over.mk f.left))
    (cg' : CompactificationOf (Over.mk g.left))
    (cfg' : CompactificationOf (Over.mk (f ≫ g).left)) :
    upperShriekCompIso f g cf' cg' cfg' =
      DominatingCompactification.upperShriekPlusIso (f ≫ g) cfg' cfg ≪≫
        upperShriekCompIso f g cf cg cfg ≪≫
        Functor.isoWhiskerLeft (upperShriekPlus g cg)
          (DominatingCompactification.upperShriekPlusIso f cf cf') ≪≫
        Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso g cg cg')
          (upperShriekPlus f cf') := by
  rw [upperShriekCompIso_eq_compIsoVia cf' cg' cfg' (ofCompCompactification f g cg cfg),
    upperShriekCompIso_eq_compIsoVia cf cg cfg (ofCompCompactification f g cg cfg)]
  simp only [compIsoVia, Iso.trans_assoc]
  rw [← Iso.trans_assoc (DominatingCompactification.upperShriekPlusIso (f ≫ g) cfg' cfg),
    upperShriekPlusIso_trans, upperShriekPlusIso_refl, Functor.isoWhiskerRight_refl,
    Iso.refl_trans, ← Functor.isoWhiskerLeft_trans_assoc, upperShriekPlusIso_trans]

end Independence

end Stacks.Duality.NestedCompactification

end
