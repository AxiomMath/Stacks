module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected

/-!
# Locally constant maps on a limit of schemes come from a stage

Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms and let `X = lim D`. A locally constant map `X → M` into a set comes from a locally
constant map on some stage, and two locally constant maps on a stage which agree on `X` already
agree on a later stage. That is, `LC(lim D, M) = colim LC(D i, M)`.

A locally constant map on the quasi-compact space `X` takes finitely many values, on the members of
a finite partition of `X` into clopen, hence quasi-compact open, subsets. Each of those is the
preimage of a quasi-compact open of some stage (Stacks 01Z4 (1),
`AlgebraicGeometry.exists_preimage_eq`), and their pairwise disjointness and the fact that they
cover are both equalities of preimages of quasi-compact opens, which hold at a later stage
(Stacks 01Z4 (2), `AlgebraicGeometry.exists_map_preimage_eq_map_preimage`).

## Main results

* `AlgebraicGeometry.exists_locallyConstant_comap_eq_of_isLimit` — every locally constant map on
  the limit comes from a stage.
* `AlgebraicGeometry.exists_locallyConstant_comap_map_eq_of_isLimit` — two locally constant maps
  on a stage which agree on the limit agree on a later stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

/-- A quasi-compact open of a stage whose preimage in a cofiltered limit is empty has empty
preimage at some later stage. -/
private theorem exists_forall_notMem_preimage_of_preimage_eq_bot [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    (hc : IsLimit c) {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (h : c.π.app i ⁻¹ᵁ U = ⊥) : ∃ (j : I) (f : j ⟶ i), ∀ y, y ∉ D.map f ⁻¹ᵁ U := by
  obtain ⟨j, f, hj⟩ := exists_map_preimage_eq_map_preimage D c hc hU
    (isCompact_empty.of_isClosed_subset isClosed_empty (by simp))
    (h.trans (Scheme.Hom.preimage_bot _).symm)
  refine ⟨j, f, fun y hy => ?_⟩
  rw [hj, Scheme.Hom.preimage_bot] at hy
  exact hy

include hc in
/-- Two locally constant maps on a stage of a cofiltered limit of quasi-compact schemes with
affine transition morphisms which agree after pulling back to the limit agree after pulling back
to a later stage. -/
theorem exists_locallyConstant_comap_map_eq_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    {M : Type w} {i : I} (t t' : LocallyConstant (D.obj i) M)
    (h : t.comap (c.π.app i).base.hom = t'.comap (c.π.app i).base.hom) :
    ∃ (j : I) (f : j ⟶ i), t.comap (D.map f).base.hom = t'.comap (D.map f).base.hom := by
  classical
  have hloc : IsLocallyConstant fun y => (t y, t' y) :=
    t.isLocallyConstant.prodMk t'.isLocallyConstant
  let E : (D.obj i).Opens :=
    ⟨{y | t y ≠ t' y}, hloc {p : M × M | p.1 ≠ p.2}⟩
  have hEc : IsCompact (E : Set (D.obj i)) :=
    (isOpen_compl_iff.mp (hloc {p : M × M | p.1 ≠ p.2}ᶜ)).isCompact
  have hE : c.π.app i ⁻¹ᵁ E = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    exact (hx : t _ ≠ t' _) (congrArg (fun s : LocallyConstant c.pt M => s x) h)
  obtain ⟨j, f, hj⟩ := exists_forall_notMem_preimage_of_preimage_eq_bot D c hc hEc hE
  exact ⟨j, f, LocallyConstant.ext fun y => by_contra (hj y)⟩

include hc in
/-- Every locally constant map on a cofiltered limit of quasi-compact quasi-separated schemes with
affine transition morphisms is pulled back from a locally constant map on some stage. -/
theorem exists_locallyConstant_comap_eq_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {M : Type w} (s : LocallyConstant c.pt M) :
    ∃ (i : I) (t : LocallyConstant (D.obj i) M), t.comap (c.π.app i).base.hom = s := by
  classical
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let R := s.range_finite.toFinset
  have hR : ∀ x, s x ∈ R := by simp [R]
  -- the fibres of `s`, as quasi-compact opens of the limit
  let C : M → c.pt.Opens := fun m => ⟨{x | s x = m}, s.isLocallyConstant.isOpen_fiber m⟩
  have hC : ∀ m, IsCompact (C m : Set c.pt) := fun m =>
    (s.isLocallyConstant.isClosed_fiber m).isCompact
  choose i V hV hVi using fun m => exists_preimage_eq D c hc (C m) (hC m)
  obtain ⟨i₀, hi₀⟩ := IsCofiltered.inf_objs_exists (R.image i)
  have hf : ∀ m : R, Nonempty (i₀ ⟶ i m) := fun m => hi₀ (Finset.mem_image_of_mem i m.2)
  let f : ∀ m : R, i₀ ⟶ i m := fun m => (hf m).some
  let V₀ : R → (D.obj i₀).Opens := fun m => D.map (f m) ⁻¹ᵁ V m
  have hV₀c : ∀ m, IsCompact (V₀ m : Set (D.obj i₀)) := fun m =>
    QuasiCompact.isCompact_preimage (f := D.map (f m)) _ (V m).2 (hV m)
  have hV₀ : ∀ m, c.π.app i₀ ⁻¹ᵁ V₀ m = C m := fun m => by
    rw [← hVi m, ← c.w (f m)]
    rfl
  -- the pairwise intersections and the union, as quasi-compact opens of the stage `i₀`
  let UA : (D.obj i₀).Opens := ⨆ p : {p : R × R // p.1 ≠ p.2}, V₀ p.1.1 ⊓ V₀ p.1.2
  let UB : (D.obj i₀).Opens := ⨆ m : R, V₀ m
  have hUAc : IsCompact (UA : Set (D.obj i₀)) := by
    simp only [UA, TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_inf]
    exact isCompact_iUnion fun p =>
      QuasiSeparatedSpace.inter_isCompact _ _ (V₀ p.1.1).2 (hV₀c _) (V₀ p.1.2).2 (hV₀c _)
  have hUA : c.π.app i₀ ⁻¹ᵁ UA = ⊥ := by
    rw [Scheme.Hom.preimage_iSup]
    refine eq_bot_iff.2 (iSup_le fun p => ?_)
    rw [Scheme.Hom.preimage_inf, hV₀, hV₀]
    intro x ⟨hx₁, hx₂⟩
    exact p.2 (Subtype.ext ((hx₁ : s x = _).symm.trans hx₂))
  have hUB : c.π.app i₀ ⁻¹ᵁ UB = c.π.app i₀ ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_iSup]
    refine eq_top_iff.2 fun x _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨s x, hR x⟩, ?_⟩
    rw [hV₀]
    rfl
  obtain ⟨j₁, f₁, hj₁⟩ := exists_forall_notMem_preimage_of_preimage_eq_bot D c hc hUAc hUA
  obtain ⟨j₂, f₂, hj₂⟩ := exists_map_preimage_eq_map_preimage D c hc
    (by simp only [UB, TopologicalSpace.Opens.coe_iSup]; exact isCompact_iUnion hV₀c)
    isCompact_univ hUB
  obtain ⟨k, g₁, g₂, hg⟩ := IsCofiltered.cospan f₁ f₂
  let φ := g₁ ≫ f₁
  let W : R → (D.obj k).Opens := fun m => D.map φ ⁻¹ᵁ V₀ m
  have hW : ∀ {j : I} (g : k ⟶ j) (f : j ⟶ i₀), g ≫ f = φ → ∀ m y,
      y ∈ W m ↔ D.map g y ∈ D.map f ⁻¹ᵁ V₀ m := fun g f e m y => by
    change D.map φ y ∈ V₀ m ↔ _
    rw [← e, D.map_comp]
    exact Iff.rfl
  have hdisj : ∀ (m m' : R) (y : D.obj k), y ∈ W m → y ∈ W m' → m = m' := by
    intro m m' y hm hm'
    by_contra hne
    refine hj₁ (D.map g₁ y) ?_
    rw [Scheme.Hom.preimage_iSup, TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨(m, m'), hne⟩, (hW g₁ f₁ rfl _ _).1 hm, (hW g₁ f₁ rfl _ _).1 hm'⟩
  have hcov : ∀ y : D.obj k, ∃ m : R, y ∈ W m := by
    intro y
    have hy : D.map g₂ y ∈ D.map f₂ ⁻¹ᵁ UB := by
      rw [hj₂]
      trivial
    rw [Scheme.Hom.preimage_iSup, TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨m, hm⟩ := hy
    exact ⟨m, (hW g₂ f₂ hg.symm _ _).2 hm⟩
  choose μ hμ using hcov
  refine ⟨k, ⟨fun y => (μ y).1, ?_⟩, ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun y => ⟨W (μ y), (W (μ y)).2, hμ y,
      fun y' hy' => ?_⟩
    rw [hdisj _ _ y' (hμ y') hy']
  · ext x
    change (μ (c.π.app k x)).1 = s x
    have hx : c.π.app k x ∈ W ⟨s x, hR x⟩ := by
      change x ∈ (c.π.app k ≫ D.map φ) ⁻¹ᵁ V₀ _
      rw [c.w, hV₀]
      rfl
    rw [hdisj _ _ _ (hμ _) hx]

/-! ### Base change of a limit over a base -/

section BaseChange

variable {S W : Scheme.{u}} (w : W ⟶ S) (t : ∀ i, D.obj i ⟶ S)
  (ht : ∀ {i j : I} (φ : i ⟶ j), D.map φ ≫ t j = t i)

/-- The base change `i ↦ W ×_S D i` of a diagram over `S` along `w : W ⟶ S`. -/
abbrev overBaseChangeDiagram : I ⥤ Scheme.{u} where
  obj i := pullback w (t i)
  map {i j} φ := pullback.lift (f := w) (g := t j) (pullback.fst w (t i))
    (pullback.snd w (t i) ≫ D.map φ) (by rw [Category.assoc, ht φ, pullback.condition])
  map_id i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, D.map_id, Category.comp_id, Category.id_comp]
  map_comp φ ψ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        D.map_comp, Category.assoc]

/-- The transition maps of the base change diagram commute with the first projections to `W`. -/
theorem overBaseChangeDiagram_map_fst {i j : I} (φ : i ⟶ j) :
    (overBaseChangeDiagram D w t ht).map φ ≫ pullback.fst w (t j) = pullback.fst w (t i) :=
  pullback.lift_fst _ _ _

/-- The transition maps of the base change diagram lie over the transition maps of `D`. -/
theorem overBaseChangeDiagram_map_snd {i j : I} (φ : i ⟶ j) :
    (overBaseChangeDiagram D w t ht).map φ ≫ pullback.snd w (t j) =
      pullback.snd w (t i) ≫ D.map φ :=
  pullback.lift_snd _ _ _

/-- The second projections `W ×_S D i ⟶ D i`. -/
def overBaseChangeDiagramSnd : overBaseChangeDiagram D w t ht ⟶ D where
  app i := pullback.snd w (t i)
  naturality _i _j φ := overBaseChangeDiagram_map_snd D w t ht φ

variable {D} (f : c.pt ⟶ S) (hf : ∀ i, c.π.app i ≫ t i = f)

/-- The projections of the base change of a cone are compatible with the transition maps. -/
theorem overBaseChangeCone_naturality {i j : I} (φ : i ⟶ j) :
    pullback.lift (f := w) (g := t i) (pullback.fst w f) (pullback.snd w f ≫ c.π.app i)
        (by rw [Category.assoc, hf i, pullback.condition]) ≫
      (overBaseChangeDiagram D w t ht).map φ =
    pullback.lift (f := w) (g := t j) (pullback.fst w f) (pullback.snd w f ≫ c.π.app j)
        (by rw [Category.assoc, hf j, pullback.condition]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, overBaseChangeDiagram_map_fst, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, overBaseChangeDiagram_map_snd, pullback.lift_snd_assoc, pullback.lift_snd,
      Category.assoc, Cone.w]

/-- The base change `W ×_S c.pt` of a cone over a diagram over `S`, along `w : W ⟶ S`. -/
abbrev overBaseChangeCone : Cone (overBaseChangeDiagram D w t ht) where
  pt := pullback w f
  π :=
    { app i := pullback.lift (f := w) (g := t i) (pullback.fst w f)
        (pullback.snd w f ≫ c.π.app i) (by rw [Category.assoc, hf i, pullback.condition])
      naturality i j φ :=
        (Category.id_comp _).trans (overBaseChangeCone_naturality c w t ht f hf φ).symm }

/-- The legs of the base change cone commute with the first projections to `W`. -/
theorem overBaseChangeCone_π_app_fst (i : I) :
    (overBaseChangeCone c w t ht f hf).π.app i ≫ pullback.fst w (t i) = pullback.fst w f :=
  pullback.lift_fst _ _ _

/-- The legs of the base change cone lie over the legs of `c`. -/
theorem overBaseChangeCone_π_app_snd (i : I) :
    (overBaseChangeCone c w t ht f hf).π.app i ≫ pullback.snd w (t i) =
      pullback.snd w f ≫ c.π.app i :=
  pullback.lift_snd _ _ _

/-- The base change of a cone, mapped to the original cone by the second projection. -/
def overBaseChangeConeHom :
    (Cone.postcompose (overBaseChangeDiagramSnd D w t ht)).obj (overBaseChangeCone c w t ht f hf) ⟶
      c where
  hom := pullback.snd w f
  w i := (overBaseChangeCone_π_app_snd c w t ht f hf i).symm

/-- The base change square of a stage. -/
theorem isPullback_overBaseChangeCone (i : I) :
    IsPullback ((overBaseChangeCone c w t ht f hf).π.app i) (pullback.snd w f)
      (pullback.snd w (t i)) (c.π.app i) := by
  refine IsPullback.of_right ?_ (overBaseChangeCone_π_app_snd c w t ht f hf i)
    (IsPullback.of_hasPullback w (t i))
  rw [overBaseChangeCone_π_app_fst, hf i]
  exact IsPullback.of_hasPullback w f

include hc in
/-- **The base change of a limit along a morphism to the base is a limit.** -/
def isLimitOverBaseChangeCone [IsCofiltered I] : IsLimit (overBaseChangeCone c w t ht f hf) :=
  have : IsConnected I := IsCofiltered.isConnected I
  isLimitOfIsPullbackOfIsConnected (overBaseChangeDiagramSnd D w t ht) _ c
    (overBaseChangeConeHom c w t ht f hf) (isPullback_overBaseChangeCone c w t ht f hf) hc

/-- The transition morphisms of the base changed diagram are affine when those of the diagram
are. -/
instance overBaseChangeDiagram_isAffineHom [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {i j : I}
    (φ : i ⟶ j) : IsAffineHom ((overBaseChangeDiagram D w t ht).map φ) := by
  have h : IsPullback ((overBaseChangeDiagram D w t ht).map φ) (pullback.snd w (t i))
      (pullback.snd w (t j)) (D.map φ) := by
    refine IsPullback.of_right ?_ (overBaseChangeDiagram_map_snd D w t ht φ)
      (IsPullback.of_hasPullback w (t j))
    rw [overBaseChangeDiagram_map_fst, ht φ]
    exact IsPullback.of_hasPullback w (t i)
  exact MorphismProperty.of_isPullback h.flip inferInstance

end BaseChange

end AlgebraicGeometry

end
