module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationIntegralComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.Dominating
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The dominating compactification of two compactifications

Let `φ : X ⟶ S` be a quasi-compact morphism and let `c₁`, `c₂` be compactifications of `X` over
`S`, with ambient schemes `X̄₁`, `X̄₂`.  The scheme-theoretic image `P` of
`(j₁, j₂) : X ⟶ X̄₁ ×_S X̄₂` is a compactification of `X` over `S` dominating both, with
projections `q_i : P ⟶ X̄_i` ([Stacks, Tag 0ATU]). Then

* each square `X = q_i⁻¹(X)` is cartesian: a point of `P` lying over the image of `X` in `X̄_i`
  lies on the image of `X` in `P`;
* when `S = Spec k` for a field `k` and `X̄₁`, `X̄₂` have dimension at most one, each `q_i` is
  finite.

## Main results

* `AlgebraicGeometry.CompactificationOf.immersion_dominatingFstMap`,
  `AlgebraicGeometry.CompactificationOf.dominatingFstMap_toBase` and their `Snd` forms: the
  projections `q_i` of the dominating compactification
  `AlgebraicGeometry.CompactificationOf.dominating` are compatible with the immersions and the
  structure morphisms.
* `AlgebraicGeometry.CompactificationOf.preimage_range_subset_of_comp_eq`: a point of `P` over
  the image of `X` lies on the image of `X`.
* `AlgebraicGeometry.CompactificationOf.isFinite_dominatingFstMap` and `..._dominatingSndMap`.

## References

* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 01RH](https://stacks.math.columbia.edu/tag/01RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Topology.Dimension

variable {X : Type*} [TopologicalSpace X]

/-- **The boundary of an open set in dimension at most one.**  In a Noetherian sober `T0` space
of Krull dimension at most one, the boundary `closure U ∖ U` of an open set `U` is a finite set
of closed points. -/
theorem closure_diff_finite_and_isClosed_singleton [T0Space X] [NoetherianSpace X]
    [QuasiSober X] (hdim : topologicalKrullDim X ≤ 1) {U : Set X} (hU : IsOpen U) :
    (closure U \ U).Finite ∧ ∀ x ∈ closure U \ U, IsClosed ({x} : Set X) := by
  have hT : IsClosed (closure U \ U) := isClosed_closure.sdiff hU
  have hTc : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ closure U \ U := by
    intro C hC hCT
    obtain ⟨o, ho, ⟨x, hx⟩, hoC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
    have hxU : x ∈ closure U := (hCT (hoC hx)).1
    obtain ⟨y, hyo, hyU⟩ := mem_closure_iff.1 hxU o ho hx
    exact (hCT (hoC hyo)).2 hyU
  exact ⟨finite_of_not_irreducibleComponent_subset hdim hT hTc,
    fun x hx ↦ isClosed_singleton_of_not_irreducibleComponent_subset hdim hT hTc hx⟩

end Stacks.Topology.Dimension

namespace AlgebraicGeometry

namespace CompactificationOf

variable {S X : Scheme.{u}} {φ : X ⟶ S} [QuasiCompact φ] (c₁ c₂ : CompactificationOf (Over.mk φ))

/-- The morphism `dominatingLift c₁ c₂ : X ⟶ X̄₁ ×_S X̄₂` is an immersion. -/
instance : IsImmersion (dominatingLift c₁ c₂) := by
  have : IsImmersion (dominatingLift c₁ c₂ ≫ pullback.fst c₁.toBase c₂.toBase) := by
    rw [pullback.lift_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst c₁.toBase c₂.toBase)

/-- The morphism `dominatingLift c₁ c₂ : X ⟶ X̄₁ ×_S X̄₂` is quasi-compact. -/
instance : QuasiCompact (dominatingLift c₁ c₂) := by
  have : QuasiCompact (dominatingLift c₁ c₂ ≫ pullback.fst c₁.toBase c₂.toBase) := by
    rw [pullback.lift_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst c₁.toBase c₂.toBase)

/-- The first projection of the dominating compactification is compatible with the immersions
of `X`. -/
@[reassoc (attr := simp)]
lemma immersion_dominatingFstMap :
    (dominating c₁ c₂).immersion ≫ CompactificationOf.Hom.map (dominatingFst c₁ c₂) =
      c₁.immersion := by
  change (dominatingLift c₁ c₂).toImage ≫ (dominatingLift c₁ c₂).imageι ≫
    pullback.fst _ _ = c₁.immersion
  rw [Scheme.Hom.toImage_imageι_assoc, pullback.lift_fst]

/-- The second projection of the dominating compactification is compatible with the immersions
of `X`. -/
@[reassoc (attr := simp)]
lemma immersion_dominatingSndMap :
    (dominating c₁ c₂).immersion ≫ CompactificationOf.Hom.map (dominatingSnd c₁ c₂) =
      c₂.immersion := by
  change (dominatingLift c₁ c₂).toImage ≫ (dominatingLift c₁ c₂).imageι ≫
    pullback.snd _ _ = c₂.immersion
  rw [Scheme.Hom.toImage_imageι_assoc, pullback.lift_snd]

/-- The first projection of the dominating compactification is compatible with the structure
morphisms to `S`. -/
lemma dominatingFstMap_toBase :
    CompactificationOf.Hom.map (dominatingFst c₁ c₂) ≫ c₁.toBase = (dominating c₁ c₂).toBase :=
  rfl

/-- The first projection of the dominating compactification is proper. -/
instance : IsProper (CompactificationOf.Hom.map (dominatingFst c₁ c₂)) :=
  inferInstanceAs (IsProper (dominatingFstMap c₁ c₂))

/-- The second projection of the dominating compactification is proper. -/
instance : IsProper (CompactificationOf.Hom.map (dominatingSnd c₁ c₂)) :=
  inferInstanceAs (IsProper (dominatingSndMap c₁ c₂))

/-- The second projection of the dominating compactification is compatible with the structure
morphisms to `S`. -/
lemma dominatingSndMap_toBase :
    CompactificationOf.Hom.map (dominatingSnd c₁ c₂) ≫ c₂.toBase =
      (dominating c₁ c₂).toBase := by
  change ((dominatingLift c₁ c₂).imageι ≫ pullback.snd _ _) ≫ c₂.toBase =
    ((dominatingLift c₁ c₂).imageι ≫ pullback.fst _ _) ≫ c₁.toBase
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- **A point of `P` over the image of `X` in `X̄` lies on the image of `X` in `P`**, for a
morphism `q : P ⟶ X̄` of compactifications out of the dominating one. -/
theorem preimage_range_subset_of_comp_eq (c : CompactificationOf (Over.mk φ))
    (q : (dominating c₁ c₂).space ⟶ c.space) (hq : (dominating c₁ c₂).immersion ≫ q = c.immersion)
    (hqb : q ≫ c.toBase = (dominating c₁ c₂).toBase) :
    q.base ⁻¹' Set.range c.immersion.base ⊆ Set.range (dominating c₁ c₂).immersion.base := by
  let P := dominating c₁ c₂
  let m := P.immersion
  let V : P.space.Opens := q ⁻¹ᵁ c.immersion.opensRange
  have hVr : Set.range (V.ι ≫ q).base ⊆ Set.range c.immersion.base := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨y, hy⟩ := v.2
    exact ⟨y, by rwa [Scheme.Hom.comp_apply]⟩
  let r : V.toScheme ⟶ X := IsOpenImmersion.lift c.immersion (V.ι ≫ q) hVr
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ m.opensRange
  have hW : IsSchemeTheoreticallyDominant W.ι :=
    isSchemeTheoreticallyDense_toImage (dominatingLift c₁ c₂) (Or.inl inferInstance) V
  have hWr : Set.range (W.ι ≫ V.ι).base ⊆ Set.range m.base := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := w.2
    exact ⟨y, by rwa [Scheme.Hom.comp_apply]⟩
  let s : W.toScheme ⟶ X := IsOpenImmersion.lift m (W.ι ≫ V.ι) hWr
  have hs : s ≫ m = W.ι ≫ V.ι := IsOpenImmersion.lift_fac _ _ _
  have hWs : W.ι ≫ r = s := by
    rw [← cancel_mono c.immersion, Category.assoc, IsOpenImmersion.lift_fac, ← hq,
      ← Category.assoc s, hs, Category.assoc]
  have : IsSeparated (Over.mk P.toBase).hom := (P.property.2).toIsSeparated
  have heq := eq_of_isSchemeTheoreticallyDominant_ι (S := S)
    (X := Over.mk (V.ι ≫ P.toBase)) (Y := Over.mk P.toBase)
    (Over.homMk V.ι rfl) (Over.homMk (r ≫ m) (by
      change (r ≫ P.immersion) ≫ P.toBase = V.ι ≫ P.toBase
      have h1 : P.immersion ≫ P.toBase = φ := CompactificationOf.immersion_toBase P
      have h2 : c.immersion ≫ c.toBase = φ := CompactificationOf.immersion_toBase c
      have h3 : r ≫ c.immersion = V.ι ≫ q := IsOpenImmersion.lift_fac _ _ _
      calc (r ≫ P.immersion) ≫ P.toBase = r ≫ φ := by rw [Category.assoc, h1]
        _ = (r ≫ c.immersion) ≫ c.toBase := by rw [Category.assoc, h2]
        _ = V.ι ≫ P.toBase := by rw [h3, Category.assoc, hqb]))
    W (by simp [← Category.assoc, hWs, hs])
  intro p hp
  have hpV : p ∈ (V : Set P.space) := hp
  have h1 := congrArg (fun f => f.left.base ⟨p, hpV⟩) heq
  simp only [Over.homMk_left] at h1
  exact ⟨r.base ⟨p, hpV⟩, (h1.symm : (r ≫ m).base ⟨p, hpV⟩ = p)⟩

/-- The image of `X` is dense in the dominating compactification. -/
theorem denseRange_dominating_immersion : DenseRange (dominating c₁ c₂).immersion.base :=
  (isDominant_toImage (dominatingLift c₁ c₂) (Or.inl inferInstance)).denseRange

/-- A projection out of the dominating compactification maps it into the closure of `X`. -/
theorem mem_closure_range_of_comp_eq (c : CompactificationOf (Over.mk φ))
    (q : (dominating c₁ c₂).space ⟶ c.space) (hq : (dominating c₁ c₂).immersion ≫ q = c.immersion)
    (p : (dominating c₁ c₂).space) : q.base p ∈ closure (Set.range c.immersion.base) := by
  have h := mem_closure_image q.base.hom.continuous.continuousAt
    ((denseRange_dominating_immersion c₁ c₂).closure_range ▸ Set.mem_univ p :
      p ∈ closure (Set.range (dominating c₁ c₂).immersion.base))
  rwa [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hq] at h

end CompactificationOf

section Fibres

/-- **The points of `Y₁ ×_k Y₂` over a closed point and a point are finitely many**, for `Y₁`
locally of finite type over a field `k`. -/
theorem finite_setOf_pullback_fst_snd_eq {k : Type u} [Field k] {Y₁ Y₂ : Scheme.{u}}
    (a₁ : Y₁ ⟶ Spec (.of k)) (a₂ : Y₂ ⟶ Spec (.of k)) [LocallyOfFiniteType a₁] {y : Y₁}
    (hy : IsClosed ({y} : Set Y₁)) (z : Y₂) :
    {p : (pullback a₁ a₂ : Scheme.{u}) |
      pullback.fst a₁ a₂ p = y ∧ pullback.snd a₁ a₂ p = z}.Finite := by
  have : JacobsonSpace Y₁ := LocallyOfFiniteType.jacobsonSpace a₁
  let b := Y₁.fromSpecResidueField y
  have : IsClosedImmersion b := isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsFinite (b ≫ a₁) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have e₁ : (b ≫ a₁) ≫ 𝟙 _ = b ≫ a₁ := Category.comp_id _
  have e₂ : a₂ ≫ 𝟙 _ = 𝟙 _ ≫ a₂ := by simp
  let ℓ := pullback.map (b ≫ a₁) a₂ a₁ a₂ b (𝟙 _) (𝟙 _) e₁ e₂
  have hrange := Scheme.Pullback.range_map (b ≫ a₁) a₂ a₁ a₂ b (𝟙 _) (𝟙 _) e₁ e₂
  have hsnd : ℓ ≫ pullback.snd a₁ a₂ = pullback.snd (b ≫ a₁) a₂ := by
    simp [ℓ]
  refine (((pullback.snd (b ≫ a₁) a₂).finite_preimage_singleton z).image ℓ.base).subset ?_
  rintro p ⟨hp₁, hp₂⟩
  have hp : p ∈ Set.range ℓ.base := by
    rw [hrange]
    refine ⟨?_, ?_⟩
    · change pullback.fst a₁ a₂ p ∈ Set.range b.base
      rw [Scheme.range_fromSpecResidueField, hp₁]
      rfl
    · exact ⟨pullback.snd a₁ a₂ p, rfl⟩
  obtain ⟨w, rfl⟩ := hp
  refine ⟨w, ?_, rfl⟩
  change (pullback.snd (b ≫ a₁) a₂).base w = z
  rw [← hsnd, Scheme.Hom.comp_apply, hp₂]

end Fibres

namespace CompactificationOf

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} {φ : X ⟶ Spec (.of k)} [QuasiCompact φ]
  (c₁ c₂ : CompactificationOf (Over.mk φ))

omit [QuasiCompact φ] in
/-- The ambient scheme of a compactification over a field is a Noetherian space. -/
theorem noetherianSpace_space (c : CompactificationOf (Over.mk φ)) : NoetherianSpace c.space := by
  have : IsLocallyNoetherian c.space := LocallyOfFiniteType.isLocallyNoetherian c.toBase
  have : CompactSpace c.space := QuasiCompact.compactSpace_of_compactSpace c.toBase
  have : IsNoetherian c.space := ⟨⟩
  infer_instance

omit [QuasiCompact φ] in
/-- **The boundary of `X` in a compactification of dimension at most one** is a finite set of
closed points. -/
theorem boundary_finite_and_isClosed (c : CompactificationOf (Over.mk φ))
    (hc : topologicalKrullDim c.space ≤ 1) :
    (closure (Set.range c.immersion.base) \ Set.range c.immersion.base).Finite ∧
      ∀ y ∈ closure (Set.range c.immersion.base) \ Set.range c.immersion.base,
        IsClosed ({y} : Set c.space) := by
  have := noetherianSpace_space c
  exact Stacks.Topology.Dimension.closure_diff_finite_and_isClosed_singleton hc
    c.immersion.isOpenEmbedding.isOpen_range

/-- A point of `P` off the image of `X` maps off the image of `X` under each projection, to a
boundary point. -/
theorem mem_boundary_of_not_mem_range (c : CompactificationOf (Over.mk φ))
    (q : (dominating c₁ c₂).space ⟶ c.space) (hq : (dominating c₁ c₂).immersion ≫ q = c.immersion)
    (hqb : q ≫ c.toBase = (dominating c₁ c₂).toBase) (p : (dominating c₁ c₂).space)
    (hp : p ∉ Set.range (dominating c₁ c₂).immersion.base) :
    q.base p ∈ closure (Set.range c.immersion.base) \ Set.range c.immersion.base :=
  ⟨mem_closure_range_of_comp_eq c₁ c₂ c q hq p,
    fun h ↦ hp (preimage_range_subset_of_comp_eq c₁ c₂ c q hq hqb h)⟩

/-- The fibres of a projection `q : P ⟶ X̄` out of the dominating compactification are finite
when `X̄` and `X̄'` have dimension at most one, given finiteness of the fibres of `(q, q')`
over closed points of `X̄`. -/
private theorem finite_preimage_singleton_of_comp_eq (c c' : CompactificationOf (Over.mk φ))
    (q : (dominating c₁ c₂).space ⟶ c.space) (q' : (dominating c₁ c₂).space ⟶ c'.space)
    (hq : (dominating c₁ c₂).immersion ≫ q = c.immersion)
    (hqb : q ≫ c.toBase = (dominating c₁ c₂).toBase)
    (hq' : (dominating c₁ c₂).immersion ≫ q' = c'.immersion)
    (hqb' : q' ≫ c'.toBase = (dominating c₁ c₂).toBase)
    (hc : topologicalKrullDim c.space ≤ 1) (hc' : topologicalKrullDim c'.space ≤ 1)
    (hfin : ∀ y, IsClosed ({y} : Set c.space) → ∀ z,
      {p | q.base p = y ∧ q'.base p = z}.Finite) (y : c.space) :
    (q.base ⁻¹' {y}).Finite := by
  by_cases hy : y ∈ Set.range c.immersion.base
  · refine Set.Subsingleton.finite ?_
    intro p hp p' hp'
    obtain ⟨x, rfl⟩ := preimage_range_subset_of_comp_eq c₁ c₂ c q hq hqb
      (show _ ∈ _ from (hp : _ = y) ▸ hy)
    obtain ⟨x', rfl⟩ := preimage_range_subset_of_comp_eq c₁ c₂ c q hq hqb
      (show _ ∈ _ from (hp' : _ = y) ▸ hy)
    have e : c.immersion.base x = c.immersion.base x' := by
      rw [← hq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact (hp : _ = y).trans (hp' : _ = y).symm
    rw [c.immersion.isOpenEmbedding.injective e]
  · have hoff : ∀ p, q.base p = y → p ∉ Set.range (dominating c₁ c₂).immersion.base := by
      rintro p hp ⟨x, rfl⟩
      refine hy ⟨x, ?_⟩
      rw [← hp, ← Scheme.Hom.comp_apply, hq]
    rcases Set.eq_empty_or_nonempty (q.base ⁻¹' {y}) with he | ⟨p, hp⟩
    · exact he ▸ Set.finite_empty
    have hyB := mem_boundary_of_not_mem_range c₁ c₂ c q hq hqb p (hoff p hp)
    rw [(hp : _ = y)] at hyB
    refine ((boundary_finite_and_isClosed c' hc').1.biUnion fun z _ ↦
      hfin y ((boundary_finite_and_isClosed c hc).2 y hyB) z).subset ?_
    intro p' hp'
    have hz := mem_boundary_of_not_mem_range c₁ c₂ c' q' hq' hqb' p' (hoff p' hp')
    simp only [Set.mem_iUnion]
    exact ⟨_, hz, hp', rfl⟩

/-- **The fibres of `q₁ : P ⟶ X̄₁` are finite** when `X̄₁` and `X̄₂` have dimension at most
one. -/
theorem finite_dominatingFstMap_preimage (h₁ : topologicalKrullDim c₁.space ≤ 1)
    (h₂ : topologicalKrullDim c₂.space ≤ 1) (y : c₁.space) :
    ((CompactificationOf.Hom.map (dominatingFst c₁ c₂)).base ⁻¹' {y}).Finite :=
  finite_preimage_singleton_of_comp_eq c₁ c₂ c₁ c₂ _ _ (immersion_dominatingFstMap c₁ c₂)
    (dominatingFstMap_toBase c₁ c₂) (immersion_dominatingSndMap c₁ c₂)
    (dominatingSndMap_toBase c₁ c₂) h₁ h₂
    (fun _ hy z ↦ (finite_setOf_pullback_fst_snd_eq c₁.toBase c₂.toBase hy z).preimage
      (dominatingLift c₁ c₂).imageι.isClosedEmbedding.injective.injOn |>.subset fun _ h ↦ h) y

/-- The points of `Y₁ ×_k Y₂` over a point and a closed point are finitely many, for `Y₂`
locally of finite type over a field. -/
theorem finite_setOf_pullback_snd_fst_eq {Y₁ Y₂ : Scheme.{u}}
    (a₁ : Y₁ ⟶ Spec (.of k)) (a₂ : Y₂ ⟶ Spec (.of k)) [LocallyOfFiniteType a₂] {z : Y₂}
    (hz : IsClosed ({z} : Set Y₂)) (y : Y₁) :
    {p : (pullback a₁ a₂ : Scheme.{u}) |
      pullback.snd a₁ a₂ p = z ∧ pullback.fst a₁ a₂ p = y}.Finite := by
  let e := pullbackSymmetry a₁ a₂
  refine ((finite_setOf_pullback_fst_snd_eq a₂ a₁ hz y).image e.inv.base).subset ?_
  rintro p ⟨hp₁, hp₂⟩
  refine ⟨e.hom.base p, ⟨?_, ?_⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst, hp₁]
  · rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd, hp₂]
  · rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl

/-- **The fibres of `q₂ : P ⟶ X̄₂` are finite** when `X̄₁` and `X̄₂` have dimension at most
one. -/
theorem finite_dominatingSndMap_preimage (h₁ : topologicalKrullDim c₁.space ≤ 1)
    (h₂ : topologicalKrullDim c₂.space ≤ 1) (y : c₂.space) :
    ((CompactificationOf.Hom.map (dominatingSnd c₁ c₂)).base ⁻¹' {y}).Finite :=
  finite_preimage_singleton_of_comp_eq c₁ c₂ c₂ c₁ _ _ (immersion_dominatingSndMap c₁ c₂)
    (dominatingSndMap_toBase c₁ c₂) (immersion_dominatingFstMap c₁ c₂)
    (dominatingFstMap_toBase c₁ c₂) h₂ h₁
    (fun _ hy z ↦ (finite_setOf_pullback_snd_fst_eq c₁.toBase c₂.toBase hy z).preimage
      (dominatingLift c₁ c₂).imageι.isClosedEmbedding.injective.injOn |>.subset fun _ h ↦ h) y

/-- **`q₁ : P ⟶ X̄₁` is finite** when `X̄₁` and `X̄₂` have dimension at most one. -/
theorem isFinite_dominatingFstMap (h₁ : topologicalKrullDim c₁.space ≤ 1)
    (h₂ : topologicalKrullDim c₂.space ≤ 1) :
    IsFinite (CompactificationOf.Hom.map (dominatingFst c₁ c₂)) := by
  have : LocallyQuasiFinite (CompactificationOf.Hom.map (dominatingFst c₁ c₂)) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_dominatingFstMap_preimage c₁ c₂ h₁ h₂)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **`q₂ : P ⟶ X̄₂` is finite** when `X̄₁` and `X̄₂` have dimension at most one. -/
theorem isFinite_dominatingSndMap (h₁ : topologicalKrullDim c₁.space ≤ 1)
    (h₂ : topologicalKrullDim c₂.space ≤ 1) :
    IsFinite (CompactificationOf.Hom.map (dominatingSnd c₁ c₂)) := by
  have : LocallyQuasiFinite (CompactificationOf.Hom.map (dominatingSnd c₁ c₂)) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_dominatingSndMap_preimage c₁ c₂ h₁ h₂)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Field

end CompactificationOf

end AlgebraicGeometry

end
