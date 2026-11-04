module

public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AtlasDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleStageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts

/-!
# Systems of glued étale quotients

Let `U_k` be a system of quasi-separated algebraic spaces, `V_k` a system of quasi-compact
objects of the big fppf site, `j_k : Y_k ⟶ V_k` open immersions and `y_k : Y_k ⟶ U_k` étale
morphisms, with `Y_k = Y_l ×_{V_l} V_k` and `Y_k = Y_l ×_{U_l} U_k` along the transition
morphisms. The quotients `X_k = V_k / R_k` of `V_k` by the glued relations
`R_k = V_k ⊔_{Y_k} (Y_k ×_{U_k} Y_k)` (`AlgebraicGeometry.Space.GluedEtaleDatum`) form a system of
algebraic spaces with étale atlases `V_k`, whose kernel pairs `R_k` are cartesian over the
transition morphisms of the atlases: this is the displayed square (Stacks 07SV) of the proof of
absolute Noetherian approximation, which makes the transition morphisms of the `X_k` affine as
soon as those of the `V_k` are (Stacks 07S3 and 03WG).

## Main definitions

* `AlgebraicGeometry.Space.GluedEtaleSystem`: the data above.
* `AlgebraicGeometry.Space.GluedEtaleSystem.atlasFamily`: the quotients with their atlases.

## Main results

* `AlgebraicGeometry.Space.GluedEtaleSystem.hcart`: the kernel pairs are cartesian over the
  transition morphisms of the atlases.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SV](https://stacks.math.columbia.edu/tag/07SV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A system of data for glued étale quotients, cartesian over the transition morphisms. -/
structure GluedEtaleSystem (K : Type u) [Category.{u} K] where
  /-- The algebraic spaces. -/
  U : K ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Each `U_k` is an algebraic space. -/
  isAlgebraicSpace_U (k : K) : IsAlgebraicSpace B S hS (U.obj k)
  /-- Each `U_k` is absolutely quasi-separated. -/
  isAbsolutelyQuasiSeparated_U (k : K) :
    IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) (U.obj k)
  /-- The schemes to be glued. -/
  V : K ⥤ BigFppfOver B S hS
  /-- Their open subschemes. -/
  Y : K ⥤ BigFppfOver B S hS
  /-- The open immersions. -/
  j : Y ⟶ V
  /-- Each `j_k` is an open immersion of schemes. -/
  isOpenImmersion_j (k : K) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j.app k))
  /-- The étale morphisms to the algebraic spaces. -/
  y : Y ⋙ yoneda ⟶ U
  /-- Each `y_k` is étale. -/
  isEtale_y (k : K) : IsEtale B S hS (y.app k)
  /-- `Y_k = Y_l ×_{V_l} V_k` along each transition morphism. -/
  isPullback_j {k l : K} (e : k ⟶ l) : IsPullback (Y.map e) (j.app k) (j.app l) (V.map e)
  /-- `Y_k = Y_l ×_{U_l} U_k` along each transition morphism. -/
  isPullback_y {k l : K} (e : k ⟶ l) :
    IsPullback (yoneda.map (Y.map e)) (y.app k) (y.app l) (U.map e)
  /-- Each `V_k` is quasi-compact. -/
  compactSpace_V (k : K) : CompactSpace ((BigFppfOver.toScheme B S hS).obj (V.obj k))
  /-- Each `Y_k` is quasi-compact. -/
  compactSpace_Y (k : K) : CompactSpace ((BigFppfOver.toScheme B S hS).obj (Y.obj k))

namespace GluedEtaleSystem

variable {B S hS} {K : Type u} [Category.{u} K] (G : GluedEtaleSystem B S hS K)

local notation "𝕋" => BigFppfOver.toScheme B S hS

/-- Each étale morphism `y_k : Y_k ⟶ U_k` is relatively representable. -/
theorem relativelyRepresentable_y (k : K) : yoneda.relativelyRepresentable (G.y.app k) :=
  (G.isAlgebraicSpace_U k).diagonal_representable.of_diag (G.y.app k)

/-- The fibre product `Y_k ×_{U_k} Y_k`. -/
noncomputable abbrev Q (k : K) : BigFppfOver B S hS :=
  (G.relativelyRepresentable_y k).pullback (G.y.app k)

/-- The first projection of `Y_k ×_{U_k} Y_k`. -/
noncomputable abbrev p₁ (k : K) : G.Q k ⟶ G.Y.obj k :=
  (G.relativelyRepresentable_y k).fst' (G.y.app k)

/-- The second projection of `Y_k ×_{U_k} Y_k`. -/
noncomputable abbrev p₂ (k : K) : G.Q k ⟶ G.Y.obj k :=
  (G.relativelyRepresentable_y k).snd (G.y.app k)

/-- The projections `p₁` and `p₂` exhibit `Q k` as the fibre product `Y_k ×_{U_k} Y_k`. -/
theorem isPullback_Q (k : K) :
    IsPullback (yoneda.map (G.p₁ k)) (yoneda.map (G.p₂ k)) (G.y.app k) (G.y.app k) :=
  (G.relativelyRepresentable_y k).isPullback' (G.y.app k)

/-- The fibre product `Y_k ×_{U_k} Y_k` is quasi-compact. -/
theorem compactSpace_Q (k : K) : CompactSpace ((𝕋).obj (G.Q k)) := by
  have := G.compactSpace_Y k
  obtain ⟨W, hW, ⟨e⟩⟩ := (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback B S hS
    (BigFppfSite.contains_terminal B) _ (G.isAlgebraicSpace_U k)).mp
    (G.isAbsolutelyQuasiSeparated_U k) _ _ (G.y.app k) (G.y.app k) inferInstance inferInstance
  let e' : W ≅ G.Q k := Yoneda.fullyFaithful.preimageIso (e ≪≫ (G.isPullback_Q k).isoPullback.symm)
  exact Function.Surjective.compactSpace ((𝕋).map e'.hom).continuous
    (fun x => ⟨((𝕋).map e'.inv).base x, by
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, e'.inv_hom_id, CategoryTheory.Functor.map_id]
      rfl⟩)

/-- Each `j_k` is an open immersion of schemes. -/
instance isOpenImmersion_j_app (k : K) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((𝕋).map (G.j.app k)) :=
  G.isOpenImmersion_j k

/-- Each `V_k` is quasi-compact. -/
instance compactSpace_V_obj (k : K) : CompactSpace ((𝕋).obj (G.V.obj k)) := G.compactSpace_V k

/-- The glueing datum at a stage. -/
noncomputable abbrev datum (k : K) : GluedEtaleDatum B S hS where
  U := G.U.obj k
  isAlgebraicSpace_U := G.isAlgebraicSpace_U k
  V := G.V.obj k
  Y := G.Y.obj k
  j := G.j.app k
  isOpenImmersion_j := G.isOpenImmersion_j k
  y := G.y.app k
  isEtale_y := G.isEtale_y k
  Q := G.Q k
  p₁ := G.p₁ k
  p₂ := G.p₂ k
  isPullback_Q := G.isPullback_Q k
  compactSpace_V := G.compactSpace_V k
  compactSpace_Q := G.compactSpace_Q k

/-- The transition morphisms of the fibre products `Y_k ×_{U_k} Y_k`. -/
noncomputable def qmap {k l : K} (e : k ⟶ l) : G.Q k ⟶ G.Q l :=
  yoneda.preimage ((G.isPullback_Q l).lift (yoneda.map (G.p₁ k ≫ G.Y.map e))
    (yoneda.map (G.p₂ k ≫ G.Y.map e)) (by
      simp only [Functor.map_comp, Category.assoc, (G.isPullback_y e).w]
      rw [← Category.assoc, ← Category.assoc, (G.isPullback_Q k).w]))

/-- The transition morphism `qmap e` is compatible with the first projections. -/
@[reassoc (attr := simp)]
theorem qmap_p₁ {k l : K} (e : k ⟶ l) : G.qmap e ≫ G.p₁ l = G.p₁ k ≫ G.Y.map e :=
  yoneda.map_injective (by simp [qmap])

/-- The transition morphism `qmap e` is compatible with the second projections. -/
@[reassoc (attr := simp)]
theorem qmap_p₂ {k l : K} (e : k ⟶ l) : G.qmap e ≫ G.p₂ l = G.p₂ k ≫ G.Y.map e :=
  yoneda.map_injective (by simp [qmap])

/-- Two morphisms to `Y_k ×_{U_k} Y_k` agreeing after both projections are equal. -/
theorem Q_hom_ext (k : K) {T : BigFppfOver B S hS} {x y : T ⟶ G.Q k}
    (h₁ : x ≫ G.p₁ k = y ≫ G.p₁ k) (h₂ : x ≫ G.p₂ k = y ≫ G.p₂ k) : x = y :=
  (G.datum k).Q_hom_ext x y h₁ h₂

/-- The diagonals `Y_k ⟶ Y_k ×_{U_k} Y_k` commute with the transition morphisms. -/
theorem d_qmap {k l : K} (e : k ⟶ l) :
    (G.datum k).d ≫ G.qmap e = G.Y.map e ≫ (G.datum l).d := by
  have h₁ : (G.datum k).d ≫ G.p₁ k = 𝟙 _ := (G.datum k).d_p₁
  have h₂ : (G.datum k).d ≫ G.p₂ k = 𝟙 _ := (G.datum k).d_p₂
  have h₁' : (G.datum l).d ≫ G.p₁ l = 𝟙 _ := (G.datum l).d_p₁
  have h₂' : (G.datum l).d ≫ G.p₂ l = 𝟙 _ := (G.datum l).d_p₂
  refine G.Q_hom_ext l ?_ ?_
  · rw [Category.assoc, qmap_p₁, ← Category.assoc, h₁, Category.id_comp, Category.assoc, h₁',
      Category.comp_id]
  · rw [Category.assoc, qmap_p₂, ← Category.assoc, h₂, Category.id_comp, Category.assoc, h₂',
      Category.comp_id]

/-- Naturality of the open immersions `j_k` on underlying schemes. -/
theorem j_naturality {k l : K} (e : k ⟶ l) :
    (𝕋).map (G.j.app k) ≫ (𝕋).map (G.V.map e) = (𝕋).map (G.Y.map e) ≫ (𝕋).map (G.j.app l) := by
  rw [← Functor.map_comp, ← Functor.map_comp, G.j.naturality]

/-- The transition morphism of the glued schemes. -/
noncomputable def rmap₀ {k l : K} (e : k ⟶ l) :
    (G.datum k).relationScheme ⟶ (G.datum l).relationScheme :=
  (G.datum k).isPushout.desc ((𝕋).map (G.V.map e) ≫ (G.datum l).a)
    ((𝕋).map (G.qmap e) ≫ (G.datum l).b) (by
      rw [← Category.assoc, G.j_naturality e, Category.assoc, (G.datum l).isPushout.w,
        ← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp, G.d_qmap])

/-- The transition morphism `rmap₀ e` restricted to the component `V_k`. -/
theorem a_rmap₀ {k l : K} (e : k ⟶ l) :
    (G.datum k).a ≫ G.rmap₀ e = (𝕋).map (G.V.map e) ≫ (G.datum l).a :=
  (G.datum k).isPushout.inl_desc _ _ _

/-- The transition morphism `rmap₀ e` restricted to the component `Y_k ×_{U_k} Y_k`. -/
theorem b_rmap₀ {k l : K} (e : k ⟶ l) :
    (G.datum k).b ≫ G.rmap₀ e = (𝕋).map (G.qmap e) ≫ (G.datum l).b :=
  (G.datum k).isPushout.inr_desc _ _ _

/-- `rmap₀ e` commutes with any pair of projections of the glued relations that restrict to the
identity on `V` and to `j ∘ p` on `Q`, for projections `p` compatible with `qmap e`. -/
private theorem rmap₀_comp_proj {k l : K} (e : k ⟶ l) (p : ∀ k, G.Q k ⟶ G.Y.obj k)
    (hp : G.qmap e ≫ p l = p k ≫ G.Y.map e)
    (s : ∀ k, (G.datum k).relationScheme ⟶ (𝕋).obj (G.V.obj k))
    (ha : ∀ k, (G.datum k).a ≫ s k = 𝟙 _)
    (hb : ∀ k, (G.datum k).b ≫ s k = (𝕋).map (p k) ≫ (𝕋).map (G.j.app k)) :
    G.rmap₀ e ≫ s l = s k ≫ (𝕋).map (G.V.map e) := by
  refine (G.datum k).isPushout.hom_ext ?_ ?_
  · rw [← Category.assoc, a_rmap₀, Category.assoc, ha, Category.comp_id, ← Category.assoc, ha,
      Category.id_comp]
  · rw [← Category.assoc, b_rmap₀, Category.assoc, hb, reassoc_of% hb (k := k), ← Category.assoc,
      ← (𝕋).map_comp, hp, (𝕋).map_comp, Category.assoc]
    exact congrArg ((𝕋).map (p k) ≫ ·) (G.j_naturality e).symm

/-- The transition morphisms of the glued schemes commute with the first projections. -/
theorem rmap₀_src₀ {k l : K} (e : k ⟶ l) :
    G.rmap₀ e ≫ (G.datum l).src₀ = (G.datum k).src₀ ≫ (𝕋).map (G.V.map e) :=
  G.rmap₀_comp_proj e G.p₁ (G.qmap_p₁ e) (fun k => (G.datum k).src₀)
    (fun _ => GluedRelation.a_src _ _) fun _ => GluedRelation.b_src _ _

/-- The transition morphisms of the glued schemes commute with the second projections. -/
theorem rmap₀_tgt₀ {k l : K} (e : k ⟶ l) :
    G.rmap₀ e ≫ (G.datum l).tgt₀ = (G.datum k).tgt₀ ≫ (𝕋).map (G.V.map e) :=
  G.rmap₀_comp_proj e G.p₂ (G.qmap_p₂ e) (fun k => (G.datum k).tgt₀)
    (fun _ => GluedRelation.a_tgt _ _) fun _ => GluedRelation.b_tgt _ _

/-- Each glued scheme `R_k` is quasi-compact. -/
instance compactSpace_relationScheme (k : K) : CompactSpace (G.datum k).relationScheme :=
  (G.datum k).compactSpace_relationScheme

/-- The first projection `R_k ⟶ V_k` is locally of finite type. -/
instance locallyOfFiniteType_src₀ (k : K) : LocallyOfFiniteType (G.datum k).src₀ :=
  (G.datum k).locallyOfFiniteType_src₀

/-- The system of glued relations. -/
noncomputable abbrev R : K ⥤ BigFppfOver B S hS where
  obj k := (G.datum k).relation
  map {k l} e := siteObjectOfLocallyOfFiniteType.lift (G.V.obj l) (G.datum l).src₀ (G.rmap₀ e) (by
    change (G.datum k).src₀ ≫ (G.V.obj k).hom.hom = _
    rw [← Category.assoc, G.rmap₀_src₀, Category.assoc]
    exact congrArg ((G.datum k).src₀ ≫ ·)
      (congrArg (fun f => f.hom) (Over.w (G.V.map e))).symm)
  map_id k := (𝕋).map_injective (by
    change G.rmap₀ (𝟙 k) = (𝕋).map (𝟙 (G.datum k).relation)
    rw [CategoryTheory.Functor.map_id]
    have hq : G.qmap (𝟙 k) = 𝟙 _ := G.Q_hom_ext k (by simp) (by simp)
    refine (G.datum k).isPushout.hom_ext ?_ ?_
    · rw [a_rmap₀, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · rw [b_rmap₀, hq, CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
  map_comp {k l m} e f := (𝕋).map_injective (by
    change G.rmap₀ (e ≫ f) = G.rmap₀ e ≫ G.rmap₀ f
    have hq : G.qmap (e ≫ f) = G.qmap e ≫ G.qmap f := G.Q_hom_ext m (by simp) (by simp)
    refine (G.datum k).isPushout.hom_ext ?_ ?_
    · rw [a_rmap₀, ← Category.assoc, a_rmap₀, Category.assoc, a_rmap₀, ← Category.assoc,
        ← (𝕋).map_comp, ← G.V.map_comp]
    · rw [b_rmap₀, ← Category.assoc, b_rmap₀, Category.assoc, b_rmap₀, ← Category.assoc,
        ← (𝕋).map_comp, hq])

/-- On underlying schemes, the transition morphisms of `R` are the morphisms `rmap₀ e`. -/
@[simp]
theorem toScheme_map_R_map {k l : K} (e : k ⟶ l) : (𝕋).map (G.R.map e) = G.rmap₀ e := rfl

/-- The first projections of the glued relations. -/
noncomputable def src : G.R ⟶ G.V where
  app k := (G.datum k).src
  naturality _ _ e := (𝕋).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact G.rmap₀_src₀ e)

/-- The second projections of the glued relations. -/
noncomputable def tgt : G.R ⟶ G.V where
  app k := (G.datum k).tgt
  naturality _ _ e := (𝕋).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact G.rmap₀_tgt₀ e)

/-- **The kernel pairs are cartesian over the transition morphisms of the atlases**
(Stacks 07SV). -/
theorem hcart {k l : K} (e : k ⟶ l) :
    IsPullback (G.R.map e) (G.src.app k) (G.src.app l) (G.V.map e) := by
  refine isPullback_of_isPullback_toScheme ?_
  have hQs : IsPullback (G.qmap e) (G.p₁ k) (G.p₁ l) (G.Y.map e) := by
    refine IsPullback.of_map yoneda (G.qmap_p₁ e) ?_
    refine IsPullback.of_right ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, qmap_p₁])
      (G.isPullback_Q l).flip
    have h := (G.isPullback_Q k).flip.paste_horiz (G.isPullback_y e)
    have hn : yoneda.map (G.Y.map e) ≫ G.y.app l = G.y.app k ≫ G.U.map e := G.y.naturality e
    rw [← Functor.map_comp, qmap_p₂, Functor.map_comp, hn]
    exact h
  have hQ := hQs.map (𝕋)
  exact isPullback_gluedRelationSource_of_isPullback ((G.isPullback_j e).map (𝕋)) hQ
    (G.datum k).hd₁ (by rw [← Functor.map_comp, ← Functor.map_comp, G.d_qmap])
    (G.datum k).isPushout (G.datum l).isPushout (GluedRelation.a_src (G.datum k).hd₁ _)
    (GluedRelation.b_src (G.datum k).hd₁ _) (GluedRelation.a_src (G.datum l).hd₁ _)
    (GluedRelation.b_src (G.datum l).hd₁ _) (G.a_rmap₀ e) (G.b_rmap₀ e)

/-- **The glued quotients with their atlases.** -/
@[reducible]
noncomputable def atlasFamily : AtlasFamily B S hS K where
  V := G.V
  R := G.R
  s := G.src
  t := G.tgt
  X k := (G.datum k).quotient
  isAlgebraicSpace k := (G.datum k).isAlgebraicSpace_quotient
  v k := (G.datum k).quotientMap
  surjective k := (G.datum k).surjective_quotientMap
  etale k := (G.datum k).etale_quotientMap
  isPullback k := (G.datum k).isPullback_quotientMap

/-- **The transition morphisms of the glued quotients are affine** as soon as those of the
atlases are (Stacks 07S3 and 03WG). -/
theorem isAffineHom_atlasFamily_map {k l : K} (e : k ⟶ l)
    (he : _root_.AlgebraicGeometry.IsAffineHom ((𝕋).map (G.V.map e))) :
    IsAffineHom B S hS (G.atlasFamily.diagram.map e) :=
  G.atlasFamily.isAffineHom_diagram_map G.hcart e he

end GluedEtaleSystem

end AlgebraicGeometry.Space

end
