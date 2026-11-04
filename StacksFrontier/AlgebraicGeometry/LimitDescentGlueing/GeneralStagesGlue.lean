module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesIsoAlt
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesTransport

/-!
# Glueing models over arbitrary stages: the induction for Stacks Tag 0EY1

Let `S = lim Sᵢ` be a directed inverse limit of schemes with affine transition morphisms, **with
no finiteness hypothesis whatsoever on the stages `Sᵢ`**.  This file runs the glueing induction of
the essential-surjectivity half of Stacks Tag 0EY1 over the predicate
`AlgebraicGeometry.LimitDescent.HasQcqsModel'`: a quasi-separated scheme over `S` covered by
finitely many quasi-compact opens each of which has a quasi-compact, quasi-separated model locally
of finite presentation over a stage has such a model itself.

## Main results

* `AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_finite_cover`: the induction.
* `AlgebraicGeometry.LimitDescent.hasQcqsModel'_of_sup`: its step, glueing two pieces.

## Implementation notes

This is the argument of `StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing` — whose
`exists_common_models`, `exists_glue_data`, `hasModel_of_isEmpty`, `hasModel_of_sup` and
`hasModel_of_finite_cover` are `private` and are therefore re-derived rather than reused — with
two changes, and no others.

First, the predicate is `AlgebraicGeometry.LimitDescent.HasQcqsModel'` and not
`AlgebraicGeometry.LimitDescent.HasModel`, so every piece of data that was recorded there as
`AlgebraicGeometry.FinitePresentation` of a morphism over a stage is recorded here as
quasi-compactness and quasi-separatedness of its *source* together with the morphism being
locally of finite presentation.  Over a quasi-separated stage the two coincide, by
`AlgebraicGeometry.finitePresentation_of_compactSpace`, and over an arbitrary stage they are
incomparable; the source states the tag in the second form.  Stability of the second form under
the base changes the induction performs is
`AlgebraicGeometry.LimitDescent.compactSpace_quasiSeparatedSpace_of_isPullback`, which uses only
that the *transition* morphisms are affine.  This is what replaces quasi-compactness of the
stages, and it is also why the glued model is quasi-compact: the two pieces are, and
`AlgebraicGeometry.quasiSeparatedSpace_of_sup` makes the glueing quasi-separated.

Second, the two descents of the intersection of two pieces are identified at a later stage by
`AlgebraicGeometry.LimitDescent.exists_iso_of_isPullback_of_isPullback_of_small` and not by
`AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`, which assumes the stages quasi-compact
and quasi-separated.  That replacement is the reason the index is a directed preorder with
`Small.{u}` rather than a cofiltered category at the universe of the schemes: the fullness and
faithfulness halves of Tag 0EY1 which it is assembled from are available only at that shape.
The results of `StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing` that the induction
*does* consume — transport of a model along a transition, and Tag 01Z4 (1) relative to a model —
are therefore used through their index-universe-free forms in
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStagesTransport`, with the index
instantiated at `Iᵒᵖ`.

Stages are kept as objects of `Iᵒᵖ` throughout, which is where the transport results deliver
them; the single point at which the preorder is needed is the appeal to the iso-descent, and
there the translation is `Opposite.unop` in one direction and `CategoryTheory.homOfLE` composed
with `Opposite.op` in the other.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)

Tags covered: none.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.LimitDescent

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [Small.{u} I]
  (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] (c : Cone D)

/-! ### Two pieces over a common stage -/

/-- Base change along a transition map of a morphism, locally of finite presentation, out of a
quasi-compact quasi-separated scheme. -/
private lemma compactSpace_quasiSeparatedSpace_pullback_fst
    {S S' Z : Scheme.{u}} (t : S' ⟶ S) [IsAffineHom t] (q : Z ⟶ S) (hcZ : CompactSpace Z)
    (hsZ : QuasiSeparatedSpace Z) (hl : LocallyOfFinitePresentation q) :
    CompactSpace ↥(pullback t q) ∧ QuasiSeparatedSpace ↥(pullback t q) ∧
      LocallyOfFinitePresentation (pullback.fst t q) :=
  have h := (IsPullback.of_hasPullback t q).flip
  ⟨(compactSpace_quasiSeparatedSpace_of_isPullback h inferInstance hcZ hsZ).1,
    (compactSpace_quasiSeparatedSpace_of_isPullback h inferInstance hcZ hsZ).2,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h hl⟩

/-- A quasi-compact open of the source of a morphism with a quasi-compact quasi-separated model is
cut out, at every stage far enough along, by a quasi-compact open of the model. -/
private lemma exists_qcqs_model_open (hc : IsLimit c) {X : Scheme.{u}} (g : X ⟶ c.pt)
    (hm : HasQcqsModel' D c g) (U : X.Opens) (hU : IsCompact U.1) :
    ∃ m : Iᵒᵖ, ∀ n : Iᵒᵖ, (n ⟶ m) → ∃ (Z : Scheme.{u}) (q : Z ⟶ D.obj n) (h : X ⟶ Z)
      (V : Z.Opens), CompactSpace Z ∧ QuasiSeparatedSpace Z ∧ LocallyOfFinitePresentation q ∧
        IsPullback h g q (c.π.app n) ∧ IsCompact V.1 ∧ h ⁻¹ᵁ V = U := by
  have : InitiallySmall.{u} Iᵒᵖ := CategoryTheory.initiallySmall_of_small_of_locallySmall _
  obtain ⟨i, Y, p, g', hcY, hsY, hlp, hpb⟩ := hm
  obtain ⟨m, a, g1, V1, hpb1, -, hV1c, hV1e⟩ :=
    exists_isOpen_model_of_initiallySmall D c hc p g g' hpb U hU
  obtain ⟨hc1, hs1, hl1⟩ :=
    compactSpace_quasiSeparatedSpace_pullback_fst (D.map a) p hcY hsY hlp
  refine ⟨m, fun n t => ?_⟩
  obtain ⟨h2, V2, -, hpb2, hV2c, hV2e, -⟩ :=
    exists_isPullback_transport_open D c t _ g g1 hpb1 V1 hV1c U hV1e
  obtain ⟨hc2, hs2, hl2⟩ :=
    compactSpace_quasiSeparatedSpace_pullback_fst (D.map t) _ hc1 hs1 hl1
  exact ⟨_, _, h2, V2, hc2, hs2, hl2, hpb2, hV2c, hV2e⟩

private lemma preimage_inf_left_ι {X : Scheme.{u}} (A B : X.Opens) :
    A.ι ⁻¹ᵁ (A ⊓ B : X.Opens) = A.ι ⁻¹ᵁ B := by
  rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

private lemma preimage_inf_right_ι {X : Scheme.{u}} (A B : X.Opens) :
    B.ι ⁻¹ᵁ (A ⊓ B : X.Opens) = B.ι ⁻¹ᵁ A := by
  rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]

/-- Two quasi-compact opens with quasi-compact quasi-separated models have models over a
*common* stage, each carrying a quasi-compact open which cuts out their intersection. -/
private lemma exists_common_qcqs_models (hc : IsLimit c) {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (f : X ⟶ c.pt)
    {A B : X.Opens} (hA : IsCompact A.1) (hB : IsCompact B.1)
    (hAm : HasQcqsModel' D c (A.ι ≫ f)) (hBm : HasQcqsModel' D c (B.ι ≫ f)) :
    ∃ (m : Iᵒᵖ) (ZA ZB : Scheme.{u}) (qA : ZA ⟶ D.obj m) (qB : ZB ⟶ D.obj m)
      (hA' : A.toScheme ⟶ ZA) (hB' : B.toScheme ⟶ ZB) (VA : ZA.Opens) (VB : ZB.Opens),
      CompactSpace ZA ∧ QuasiSeparatedSpace ZA ∧ LocallyOfFinitePresentation qA ∧
        CompactSpace ZB ∧ QuasiSeparatedSpace ZB ∧ LocallyOfFinitePresentation qB ∧
        IsPullback hA' (A.ι ≫ f) qA (c.π.app m) ∧ IsPullback hB' (B.ι ≫ f) qB (c.π.app m) ∧
        IsCompact VA.1 ∧ IsCompact VB.1 ∧
        hA' ⁻¹ᵁ VA = A.ι ⁻¹ᵁ B ∧ hB' ⁻¹ᵁ VB = B.ι ⁻¹ᵁ A := by
  have hABc : IsCompact ((A ⊓ B : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact hA.inter_of_isOpen hB A.isOpen B.isOpen
  obtain ⟨mA, hmA⟩ := exists_qcqs_model_open D c hc (A.ι ≫ f) hAm (A.ι ⁻¹ᵁ B)
    (preimage_inf_left_ι A B ▸ isCompact_preimage_ι inf_le_left hABc)
  obtain ⟨mB, hmB⟩ := exists_qcqs_model_open D c hc (B.ι ≫ f) hBm (B.ι ⁻¹ᵁ A)
    (preimage_inf_right_ι A B ▸ isCompact_preimage_ι inf_le_right hABc)
  obtain ⟨ZA, qA, hA', VA, hcA, hsA, hlA, hpbA, hVAc, hVAe⟩ :=
    hmA _ (IsCofiltered.minToLeft mA mB)
  obtain ⟨ZB, qB, hB', VB, hcB, hsB, hlB, hpbB, hVBc, hVBe⟩ :=
    hmB _ (IsCofiltered.minToRight mA mB)
  exact ⟨_, ZA, ZB, qA, qB, hA', hB', VA, VB, hcA, hsA, hlA, hcB, hsB, hlB, hpbA, hpbB,
    hVAc, hVBc, hVAe, hVBe⟩

/-! ### The glue datum -/

/-- If a quasi-compact open of the model pulls back to `W` inside `U`, then `W` is the pullback of
that open along the model map. -/
private lemma exists_isPullback_homOfLE_ι {X Z : Scheme.{u}} {W U : X.Opens} (hWU : W ≤ U)
    (h : U.toScheme ⟶ Z) (V : Z.Opens) (hV : h ⁻¹ᵁ V = U.ι ⁻¹ᵁ W) :
    ∃ w : W.toScheme ⟶ V.toScheme, IsPullback w (X.homOfLE hWU) V.ι h := by
  have hrng : Set.range (X.homOfLE hWU ≫ h).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    show _ ∈ (V : Set Z)
    have : (X.homOfLE hWU ≫ h) ⁻¹ᵁ V = ⊤ := by
      rw [Scheme.Hom.comp_preimage, hV, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι,
        Scheme.Opens.ι_preimage_self]
    exact this.ge (Set.mem_univ y)
  refine ⟨IsOpenImmersion.lift V.ι _ hrng, IsOpenImmersion.isPullback _ _ _ _
    (IsOpenImmersion.lift_fac _ _ hrng).symm ?_⟩
  rw [Scheme.Opens.opensRange_ι, hV, Scheme.opensRange_homOfLE]

/-- Two maps into a base change `pullback a q` agree when they agree after both projections; this
is the bookkeeping for comparing a transported model with the comparison isomorphism. -/
private lemma comp_ι_eq_of_fst_snd {S S' Z T X' Y : Scheme.{u}} {a : S' ⟶ S} {q : Z ⟶ S}
    {V : Z.Opens} {V₃ : (pullback a q).Opens} {θ : Y ⟶ V₃.toScheme} {ρ : V₃.toScheme ⟶ V.toScheme}
    {g : T ⟶ Y} {r : Y ⟶ V.toScheme} {p : Y ⟶ S'} {w : T ⟶ V.toScheme} {k : X' ⟶ pullback a q}
    {h : X' ⟶ Z} {j : T ⟶ X'} (hθ₁ : θ ≫ V₃.ι ≫ pullback.fst a q = p) (hθ₂ : θ ≫ ρ = r)
    (hρ : V₃.ι ≫ pullback.snd a q = ρ ≫ V.ι) (hg : g ≫ r = w) (hk : k ≫ pullback.snd a q = h)
    (hj : j ≫ h = w ≫ V.ι) (hfst : g ≫ p = j ≫ k ≫ pullback.fst a q) :
    (g ≫ θ) ≫ V₃.ι = j ≫ k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hθ₁, hfst]
  · simp only [Category.assoc, hρ]
    rw [← Category.assoc θ ρ, hθ₂, ← Category.assoc g r, hg, hk, hj]

/-- **The glue datum for two quasi-compact opens with quasi-compact quasi-separated models.**  At
one stage, the two opens have models carrying quasi-compact opens cutting out their intersection,
together with an isomorphism between those two opens over the stage which is compatible with the
two presentations of the intersection. -/
private lemma exists_qcqs_glue_data (hc : IsLimit c) {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (f : X ⟶ c.pt)
    {A B : X.Opens} (hA : IsCompact A.1) (hB : IsCompact B.1)
    (hAm : HasQcqsModel' D c (A.ι ≫ f)) (hBm : HasQcqsModel' D c (B.ι ≫ f)) :
    ∃ (m : Iᵒᵖ) (ZA ZB : Scheme.{u}) (qA : ZA ⟶ D.obj m) (qB : ZB ⟶ D.obj m)
      (hA' : A.toScheme ⟶ ZA) (hB' : B.toScheme ⟶ ZB) (VA : ZA.Opens) (VB : ZB.Opens)
      (φ : VA.toScheme ≅ VB.toScheme) (wA : (A ⊓ B : X.Opens).toScheme ⟶ VA.toScheme),
      CompactSpace ZA ∧ QuasiSeparatedSpace ZA ∧ LocallyOfFinitePresentation qA ∧
        CompactSpace ZB ∧ QuasiSeparatedSpace ZB ∧ LocallyOfFinitePresentation qB ∧
        IsPullback hA' (A.ι ≫ f) qA (c.π.app m) ∧ IsPullback hB' (B.ι ≫ f) qB (c.π.app m) ∧
        hA' ⁻¹ᵁ VA = A.ι ⁻¹ᵁ B ∧ hB' ⁻¹ᵁ VB = B.ι ⁻¹ᵁ A ∧ IsCompact VA.1 ∧
        φ.hom ≫ VB.ι ≫ qB = VA.ι ≫ qA ∧
        wA ≫ VA.ι = X.homOfLE inf_le_left ≫ hA' ∧
        wA ≫ φ.hom ≫ VB.ι = X.homOfLE inf_le_right ≫ hB' := by
  obtain ⟨m, ZA, ZB, qA, qB, hA', hB', VA, VB, hcA, hsA, hlA, hcB, hsB, hlB, hmA, hmB,
    hVAc, hVBc, hVAe, hVBe⟩ := exists_common_qcqs_models D c hc f hA hB hAm hBm
  -- the two presentations of `A ⊓ B` inside the two models
  obtain ⟨wA0, hwA0⟩ := exists_isPullback_homOfLE_ι (inf_le_left : A ⊓ B ≤ A) hA' VA
    (hVAe.trans (preimage_inf_left_ι A B).symm)
  obtain ⟨wB0, hwB0⟩ := exists_isPullback_homOfLE_ι (inf_le_right : A ⊓ B ≤ B) hB' VB
    (hVBe.trans (preimage_inf_right_ι A B).symm)
  have hmodA : IsPullback wA0 ((A ⊓ B : X.Opens).ι ≫ f) (VA.ι ≫ qA) (c.π.app m) := by
    have h := hwA0.paste_vert hmA
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have hmodB : IsPullback wB0 ((A ⊓ B : X.Opens).ι ≫ f) (VB.ι ≫ qB) (c.π.app m) := by
    have h := hwB0.paste_vert hmB
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  obtain ⟨hcVA, hsVA, hlVA⟩ :=
    compactSpace_quasiSeparatedSpace_locallyOfFinitePresentation_ι_comp qA hlA VA hVAc
  obtain ⟨hcVB, hsVB, hlVB⟩ :=
    compactSpace_quasiSeparatedSpace_locallyOfFinitePresentation_ι_comp qB hlB VB hVBc
  obtain ⟨m', him, YA'', YB'', pA'', pB'', rA, rB, gA'', gB'', φ', -, -, -, -, -, -,
    hrA, hrB, hgA'', hgB'', hφ'p, hφ'c, hgArA, hgBrB⟩ :=
    exists_iso_of_isPullback_of_isPullback_of_small D c hc m.unop hcVA hsVA hcVB hsVB hlVA hlVB
      hmodA hmodB
  set e : Opposite.op m' ⟶ m := (homOfLE him).op with he
  obtain ⟨hA3, VA3, ρA, hmA3, hVA3c, hVA3e, hA3s, hρAw, hρA⟩ :=
    exists_isPullback_transport_open D c e qA (A.ι ≫ f) hA' hmA VA hVAc (A.ι ⁻¹ᵁ B) hVAe
  obtain ⟨hB3, VB3, ρB, hmB3, hVB3c, hVB3e, hB3s, hρBw, hρB⟩ :=
    exists_isPullback_transport_open D c e qB (B.ι ≫ f) hB' hmB VB hVBc (B.ι ⁻¹ᵁ A) hVBe
  set θA := hrA.isoIsPullback _ _ hρA with hθA
  set θB := hrB.isoIsPullback _ _ hρB with hθB
  have hθAs : θA.hom ≫ VA3.ι ≫ pullback.fst (D.map e) qA = pA'' :=
    hrA.isoIsPullback_hom_snd _ _ hρA
  have hθBs : θB.hom ≫ VB3.ι ≫ pullback.fst (D.map e) qB = pB'' :=
    hrB.isoIsPullback_hom_snd _ _ hρB
  have hθAf : θA.hom ≫ ρA = rA := hrA.isoIsPullback_hom_fst _ _ hρA
  have hθBf : θB.hom ≫ ρB = rB := hrB.isoIsPullback_hom_fst _ _ hρB
  have keyA := comp_ι_eq_of_fst_snd hθAs hθAf hρAw hgArA hA3s hwA0.w.symm
    (by rw [hgA''.w, hmA3.w]; simp only [← Category.assoc, Scheme.homOfLE_ι])
  have keyB := comp_ι_eq_of_fst_snd hθBs hθBf hρBw hgBrB hB3s hwB0.w.symm
    (by rw [hgB''.w, hmB3.w]; simp only [← Category.assoc, Scheme.homOfLE_ι])
  obtain ⟨hcA3, hsA3, hlA3⟩ :=
    compactSpace_quasiSeparatedSpace_pullback_fst (D.map e) qA hcA hsA hlA
  obtain ⟨hcB3, hsB3, hlB3⟩ :=
    compactSpace_quasiSeparatedSpace_pullback_fst (D.map e) qB hcB hsB hlB
  refine ⟨Opposite.op m', _, _, pullback.fst (D.map e) qA, pullback.fst (D.map e) qB, hA3, hB3,
    VA3, VB3, θA.symm ≪≫ φ' ≪≫ θB, gA'' ≫ θA.hom, hcA3, hsA3, hlA3, hcB3, hsB3, hlB3,
    hmA3, hmB3, hVA3e, hVB3e, hVA3c, ?_, keyA, ?_⟩
  · rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [hθBs, hφ'p, ← hθAs, Iso.inv_hom_id_assoc]
  · rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc gA'' φ'.hom (θB.hom ≫ VB3.ι), hφ'c,
      ← Category.assoc gB'' θB.hom VB3.ι, keyB]

/-! ### The glueing step -/

omit [IsDirected I (· ≤ ·)] [Small.{u} I] [∀ {a b : Iᵒᵖ} (t : a ⟶ b), IsAffineHom (D.map t)] in
/-- A morphism out of an empty scheme has a quasi-compact quasi-separated model over a stage: the
empty open subscheme of that stage.  No finiteness of the stage is used — the empty scheme is
quasi-compact and quasi-separated whatever the stage is. -/
private lemma hasQcqsModel'_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (f : X ⟶ c.pt) :
    HasQcqsModel' D c f := by
  let i₀ : Iᵒᵖ := Opposite.op (Classical.arbitrary I)
  have hXi : IsInitial X := isInitialOfIsEmpty
  have hEe : IsEmpty (⊥ : (D.obj i₀).Opens).toScheme :=
    inferInstanceAs (IsEmpty (∅ : Set (D.obj i₀)))
  exact ⟨i₀, (⊥ : (D.obj i₀).Opens).toScheme, (⊥ : (D.obj i₀).Opens).ι, hXi.to _,
    inferInstance, inferInstance, inferInstance, IsPullback.of_iso_pullback ⟨hXi.hom_ext _ _⟩
      (hXi.uniqueUpToIso (isInitialOfIsEmpty.ofIso (asIso (pullback.fst _ _)).symm))
      (hXi.hom_ext _ _) (hXi.hom_ext _ _)⟩

/-- **The glueing step of the essential surjectivity of Stacks Tag 0EY1 over arbitrary stages.**
If `X` is covered by two quasi-compact opens each of which has a quasi-compact, quasi-separated
model locally of finite presentation over a stage, then `X` itself has one: glue the two models
along the isomorphism of
`AlgebraicGeometry.LimitDescent.exists_iso_of_isPullback_of_isPullback_of_small` between the two
descents of the intersection. -/
private lemma hasQcqsModel'_of_sup (hc : IsLimit c) {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (f : X ⟶ c.pt)
    {A B : X.Opens} (hAB : A ⊔ B = ⊤) (hA : IsCompact A.1) (hB : IsCompact B.1)
    (hAm : HasQcqsModel' D c (A.ι ≫ f)) (hBm : HasQcqsModel' D c (B.ι ≫ f)) :
    HasQcqsModel' D c f := by
  obtain ⟨m, ZA, ZB, qA, qB, hA', hB', VA, VB, φ, wA, hcA, hsA, hlA, hcB, hsB, hlB, hmA, hmB,
    hVAe, hVBe, hVAc, hφq, hwA, hwB⟩ := exists_qcqs_glue_data D c hc f hA hB hAm hBm
  have hd : VA.ι ≫ qA = (φ.hom ≫ VB.ι) ≫ qB := by rw [Category.assoc]; exact hφq.symm
  have hjAq : pushout.inl VA.ι (φ.hom ≫ VB.ι) ≫ pushout.desc qA qB hd = qA :=
    pushout.inl_desc _ _ _
  have hjBq : pushout.inr VA.ι (φ.hom ≫ VB.ι) ≫ pushout.desc qA qB hd = qB :=
    pushout.inr_desc _ _ _
  have hpo : VA.ι ≫ pushout.inl VA.ι (φ.hom ≫ VB.ι) =
      φ.hom ≫ VB.ι ≫ pushout.inr VA.ι (φ.hom ≫ VB.ι) := by
    rw [← Category.assoc]; exact pushout.condition
  have hcov := opensRange_pushout_inl_sup_inr VA.ι (φ.hom ≫ VB.ι)
  have hint := opensRange_pushout_inl_inf_inr VA.ι (φ.hom ≫ VB.ι)
  obtain ⟨g, hg, -, -⟩ := isPullback_of_glueData (c.π.app m) f hAB hmA hmB hVAe hVBe φ
    (pushout.desc qA qB hd) _ _ hjAq hjBq hpo hcov hint wA hwA hwB
  have : CompactSpace VA.toScheme := isCompact_iff_compactSpace.1 hVAc
  have hzls : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have hCS : CompactSpace ↥(pushout VA.ι (φ.hom ≫ VB.ι)) := by
    rw [← isCompact_univ_iff, ← TopologicalSpace.Opens.coe_top, ← hcov,
      TopologicalSpace.Opens.coe_sup]
    exact (isCompact_range (pushout.inl VA.ι (φ.hom ≫ VB.ι)).continuous).union
      (isCompact_range (pushout.inr VA.ι (φ.hom ≫ VB.ι)).continuous)
  have hqs : ∀ {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
      (j : Y ⟶ pushout VA.ι (φ.hom ≫ VB.ι)) [IsOpenImmersion j], IsQuasiSeparated (Set.range j) :=
    fun j _ => by
      have h := (j.isOpenEmbedding.isQuasiSeparated_iff (s := Set.univ)).mp isQuasiSeparated_univ
      rwa [Set.image_univ] at h
  have hQS : QuasiSeparatedSpace ↥(pushout VA.ι (φ.hom ≫ VB.ι)) := by
    refine quasiSeparatedSpace_of_sup hcov ?_ ?_ ?_
    · exact hqs (pushout.inl VA.ι (φ.hom ≫ VB.ι))
    · exact hqs (pushout.inr VA.ι (φ.hom ≫ VB.ι))
    · rw [hint]
      exact isCompact_range (VA.ι ≫ pushout.inl VA.ι (φ.hom ≫ VB.ι)).continuous
  -- local finite presentation of the glued map on the open piece `j`
  have hloc : ∀ {Y : Scheme.{u}} (j : Y ⟶ pushout VA.ι (φ.hom ≫ VB.ι)) [IsOpenImmersion j]
      {q : Y ⟶ D.obj m}, j ≫ pushout.desc qA qB hd = q → LocallyOfFinitePresentation q →
      LocallyOfFinitePresentation (j.opensRange.ι ≫ pushout.desc qA qB hd) :=
    fun j _ _ hj hq => by
      rw [← IsOpenImmersion.isoOfRangeEq_inv_fac j (Scheme.Opens.ι _)
        (congrArg TopologicalSpace.Opens.carrier j.opensRange.opensRange_ι.symm),
        Category.assoc, hj]
      exact MorphismProperty.comp_mem _ _ _ inferInstance hq
  refine ⟨m, _, pushout.desc qA qB hd, g, hCS, hQS, ?_, hg⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun b : Bool => cond b (pushout.inl VA.ι (φ.hom ≫ VB.ι)).opensRange
      (pushout.inr VA.ι (φ.hom ≫ VB.ι)).opensRange) (by rw [iSup_bool_eq]; exact hcov) ?_
  rintro (_ | _)
  · exact hloc _ hjBq hlB
  · exact hloc _ hjAq hlA

/-! ### Induction over a finite cover -/

/-- **The glueing induction of the essential surjectivity of Stacks Tag 0EY1 over arbitrary
stages.**  If `X` is covered by finitely many quasi-compact opens each of which has a
quasi-compact, quasi-separated model locally of finite presentation over a stage, then `X` has
one.  The induction glues two pieces at a time, which is why the quasi-compactness of the
intersections is available at every step. -/
public lemma hasQcqsModel'_of_finite_cover (hc : IsLimit c) {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (f : X ⟶ c.pt) {J : Type u} [Finite J] (U : J → X.Opens)
    (hU : IsOpenCover U)
    (hUc : ∀ k, IsCompact (U k).1) (hUm : ∀ k, HasQcqsModel' D c ((U k).ι ≫ f)) :
    HasQcqsModel' D c f := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have key : ∀ T : Finset J, IsCompact ((⨆ k ∈ T, U k : X.Opens) : Set X) ∧
      HasQcqsModel' D c ((⨆ k ∈ T, U k : X.Opens).ι ≫ f) := by
    intro T
    induction T using Finset.induction with
    | empty =>
      have hbot : (⨆ k ∈ (∅ : Finset J), U k : X.Opens) = ⊥ := by simp
      rw [hbot]
      refine ⟨by rw [TopologicalSpace.Opens.coe_bot]; exact isCompact_empty, ?_⟩
      have : IsEmpty (⊥ : X.Opens).toScheme := inferInstanceAs (IsEmpty (∅ : Set X))
      exact hasQcqsModel'_of_isEmpty D c _
    | insert k T hk ih =>
      obtain ⟨hWc, hWm⟩ := ih
      have hins : (⨆ l ∈ insert k T, U l : X.Opens) = U k ⊔ ⨆ l ∈ T, U l := by
        apply TopologicalSpace.Opens.ext
        simp
      rw [hins]
      refine ⟨by rw [TopologicalSpace.Opens.coe_sup]; exact (hUc k).union hWc, ?_⟩
      set W' : X.Opens := U k ⊔ ⨆ l ∈ T, U l with hW'
      have : QuasiSeparatedSpace W'.toScheme :=
        QuasiSeparatedSpace.of_isOpenEmbedding W'.ι.isOpenEmbedding
      have hsup : (W'.ι ⁻¹ᵁ U k) ⊔ (W'.ι ⁻¹ᵁ (⨆ l ∈ T, U l : X.Opens)) = ⊤ := by
        rw [← Scheme.Hom.preimage_sup, ← hW', Scheme.Opens.ι_preimage_self]
      have hres : ∀ {V : X.Opens} (h : V ≤ W'), HasQcqsModel' D c (V.ι ≫ f) →
          HasQcqsModel' D c ((W'.ι ⁻¹ᵁ V).ι ≫ W'.ι ≫ f) := fun {V} h hm => by
        refine HasQcqsModel'.of_iso D c (isoOfImageEq (W'.ι ⁻¹ᵁ V) V (image_preimage_ι h)).symm ?_
          hm
        have h1 : (isoOfImageEq (W'.ι ⁻¹ᵁ V) V (image_preimage_ι h)).inv ≫ V.ι =
            (W'.ι ⁻¹ᵁ V).ι ≫ W'.ι := by
          rw [← isoOfImageEq_hom (W'.ι ⁻¹ᵁ V) V (image_preimage_ι h), Iso.inv_hom_id_assoc]
        rw [Iso.symm_hom, ← Category.assoc, h1, Category.assoc]
      refine hasQcqsModel'_of_sup D c hc (W'.ι ≫ f) hsup
        (isCompact_preimage_ι le_sup_left (hUc k))
        (isCompact_preimage_ι le_sup_right hWc) ?_ ?_
      · exact hres le_sup_left (hUm k)
      · exact hres le_sup_right hWm
  have htop : (⨆ k ∈ (Finset.univ : Finset J), U k : X.Opens) = ⊤ := by
    have : (⨆ k ∈ (Finset.univ : Finset J), U k : X.Opens) = ⨆ k, U k := by simp
    rw [this]
    exact hU
  have h := (key Finset.univ).2
  rw [htop] at h
  refine HasQcqsModel'.of_iso D c (X.topIso).symm ?_ h
  rw [Iso.symm_hom, ← Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry.LimitDescent
