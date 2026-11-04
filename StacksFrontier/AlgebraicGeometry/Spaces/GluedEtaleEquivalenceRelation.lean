module

public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleRelationTransition

/-!
# The glued étale equivalence relation of an elementary distinguished square

Let `j : Y ⟶ V` be an open immersion of schemes and let `p₁, p₂ : Q ⇉ Y` be an étale
equivalence relation on `Y` with an open diagonal `d : Y ⟶ Q`; in the application `Q` is the
fibre product `Y ×_U Y` over an algebraic space `U` receiving an étale morphism from `Y`.
Glueing `V` to `Q` along `Y` gives a scheme `R` with two morphisms `s, t : R ⟶ V`, the identity
on the chart `V` and `j ∘ p₁`, resp. `j ∘ p₂`, on the chart `Q`. This file proves that
`s, t : R ⇉ V` is an étale equivalence relation on `V`, as asserted without proof in the proof
of absolute Noetherian approximation.

## Main definitions

* `AlgebraicGeometry.GluedRelation.src`, `AlgebraicGeometry.GluedRelation.tgt`: the two
  projections of the glued relation.

## Main results

* `AlgebraicGeometry.GluedRelation.isPullback_src`: the chart `Q` is the inverse image of `Y`
  under the first projection.
* `AlgebraicGeometry.GluedRelation.hom_ext_of_isPushout`: the two projections are jointly monic.
* `AlgebraicGeometry.GluedRelation.exists_symm`, `AlgebraicGeometry.GluedRelation.exists_trans`:
  symmetry and transitivity.
* `AlgebraicGeometry.GluedRelation.src_of_isZariskiLocalAtSource`: a property local on the source
  which holds on both charts holds for the projections; in particular they are étale.
* `AlgebraicGeometry.GluedRelation.exists_lift_of_locally_lift`: morphisms into a jointly monic
  pair which lift locally lift globally.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u


namespace AlgebraicGeometry.GluedRelation
/-- **Morphisms into a jointly monic pair glue.** If `s, t : R ⇉ V` are jointly monic for test
morphisms from all schemes, and a pair of morphisms `f₁, f₂ : T ⇉ V` lifts to `R` locally on
`T`, then it lifts to `R`. -/
theorem exists_lift_of_locally_lift {R V T : Scheme.{u}} (s t : R ⟶ V)
    (hm : ∀ {Z : Scheme.{u}} (x y : Z ⟶ R), x ≫ s = y ≫ s → x ≫ t = y ≫ t → x = y)
    (f₁ f₂ : T ⟶ V)
    (H : ∀ τ : T, ∃ O : T.Opens, τ ∈ O ∧
      ∃ g : O.toScheme ⟶ R, g ≫ s = O.ι ≫ f₁ ∧ g ≫ t = O.ι ≫ f₂) :
    ∃ g : T ⟶ R, g ≫ s = f₁ ∧ g ≫ t = f₂ := by
  choose O hO g hg₁ hg₂ using H
  let 𝒰 : T.OpenCover :=
    { I₀ := T
      X i := O i
      f i := (O i).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨x, by simpa using hO x⟩, inferInstance⟩ }
  have hcompat : ∀ i k, pullback.fst (𝒰.f i) (𝒰.f k) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f k) ≫ g k :=
    fun i k => hm _ _
      (by rw [Category.assoc, Category.assoc, hg₁, hg₁, ← Category.assoc, ← Category.assoc,
        pullback.condition])
      (by rw [Category.assoc, Category.assoc, hg₂, hg₂, ← Category.assoc, ← Category.assoc,
        pullback.condition])
  refine ⟨𝒰.glueMorphisms g hcompat, 𝒰.hom_ext _ _ fun i => ?_, 𝒰.hom_ext _ _ fun i => ?_⟩
  · rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact hg₁ i
  · rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact hg₂ i

variable {V Y Q R : Scheme.{u}} {j : Y ⟶ V} [IsOpenImmersion j] {p₁ p₂ : Q ⟶ Y} {d : Y ⟶ Q}
  [IsOpenImmersion d] (hd₁ : d ≫ p₁ = 𝟙 Y) (hd₂ : d ≫ p₂ = 𝟙 Y) {a : V ⟶ R} {b : Q ⟶ R}
  (hR : IsPushout j d a b)

include hd₁ in
/-- The first projection of the glued relation. -/
noncomputable def src : R ⟶ V :=
  hR.desc (𝟙 V) (p₁ ≫ j) (by rw [Category.comp_id, ← Category.assoc, hd₁, Category.id_comp])

include hd₂ in
/-- The second projection of the glued relation. -/
noncomputable def tgt : R ⟶ V :=
  hR.desc (𝟙 V) (p₂ ≫ j) (by rw [Category.comp_id, ← Category.assoc, hd₂, Category.id_comp])

omit [IsOpenImmersion j] [IsOpenImmersion d] in
/-- The first projection restricted to the chart `V` is the identity of `V`. -/
@[reassoc (attr := simp)]
theorem a_src : a ≫ src hd₁ hR = 𝟙 V := hR.inl_desc _ _ _

omit [IsOpenImmersion j] [IsOpenImmersion d] in
/-- The first projection restricted to the chart `Q` is `j ∘ p₁`. -/
@[reassoc (attr := simp)]
theorem b_src : b ≫ src hd₁ hR = p₁ ≫ j := hR.inr_desc _ _ _

omit [IsOpenImmersion j] [IsOpenImmersion d] in
/-- The second projection restricted to the chart `V` is the identity of `V`. -/
@[reassoc (attr := simp)]
theorem a_tgt : a ≫ tgt hd₂ hR = 𝟙 V := hR.inl_desc _ _ _

omit [IsOpenImmersion j] [IsOpenImmersion d] in
/-- The second projection restricted to the chart `Q` is `j ∘ p₂`. -/
@[reassoc (attr := simp)]
theorem b_tgt : b ≫ tgt hd₂ hR = p₂ ≫ j := hR.inr_desc _ _ _

include hR in
/-- The chart `a : V ⟶ R` is an open immersion. -/
theorem isOpenImmersion_a : IsOpenImmersion a := isOpenImmersion_inl_of_isPushout hR

include hR in
/-- The chart `b : Q ⟶ R` is an open immersion. -/
theorem isOpenImmersion_b : IsOpenImmersion b := isOpenImmersion_inr_of_isPushout hR

include hR in
/-- Every point of `R` lies in the image of `a` or in the image of `b`. -/
theorem mem_range_a_or_b (x : R) : x ∈ Set.range a.base ∨ x ∈ Set.range b.base :=
  exists_eq_of_isPushout_of_isOpenImmersion hR x

include hd₁ in
/-- A point of the glued relation lies on the chart `Q` exactly when its first projection lies
in `Y`. -/
theorem mem_range_b_iff_src (x : R) :
    x ∈ Set.range b.base ↔ (src hd₁ hR).base x ∈ Set.range j.base := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨p₁.base q, by rw [← Scheme.Hom.comp_apply, ← b_src hd₁ hR, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    rcases mem_range_a_or_b hR x with ⟨v, rfl⟩ | hb
    · refine ⟨d.base y, ?_⟩
      have h1 : (src hd₁ hR).base (a.base v) = v := by
        rw [← Scheme.Hom.comp_apply, a_src]
        rfl
      have hv : v = j.base y := by rw [← h1, hy]
      rw [hv, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hR.w]
    · exact hb

include hd₂ in
/-- A point of the glued relation lies on the chart `Q` exactly when its second projection
lies in `Y`. -/
theorem mem_range_b_iff_tgt (x : R) :
    x ∈ Set.range b.base ↔ (tgt hd₂ hR).base x ∈ Set.range j.base :=
  mem_range_b_iff_src hd₂ hR x

/-- **The chart `Q` is the inverse image of `Y` under the first projection.** -/
theorem isPullback_src : IsPullback b p₁ (src hd₁ hR) j := by
  have := isOpenImmersion_b hR
  have hrange : ∀ {T : Scheme.{u}} (x : T ⟶ R) (y : T ⟶ Y), x ≫ src hd₁ hR = y ≫ j →
      Set.range x.base ⊆ Set.range b.base := fun x y h => by
    rintro _ ⟨τ, rfl⟩
    rw [mem_range_b_iff_src hd₁ hR, ← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  refine IsPullback.of_isLimit' ⟨b_src hd₁ hR⟩ (PullbackCone.IsLimit.mk _
    (fun s => IsOpenImmersion.lift b s.fst (hrange _ _ s.condition))
    (fun s => IsOpenImmersion.lift_fac _ _ _) (fun s => ?_) (fun s m hm₁ _ => ?_))
  · have hl := IsOpenImmersion.lift_fac b s.fst (hrange _ _ s.condition)
    rw [← cancel_mono j, Category.assoc, ← b_src hd₁ hR, ← Category.assoc, hl, s.condition]
  · have hl := IsOpenImmersion.lift_fac b s.fst (hrange _ _ s.condition)
    rw [← cancel_mono b, hl]
    exact hm₁

/-- **The chart `Q` is the inverse image of `Y` under the second projection.** -/
theorem isPullback_tgt : IsPullback b p₂ (tgt hd₂ hR) j :=
  isPullback_src hd₂ hR

omit [IsOpenImmersion d] in
/-- A morphism into a scheme, restricted to the inverse image of the range of an open
immersion, lands in that range. -/
theorem range_restrict_subset {T X Z : Scheme.{u}} (x : T ⟶ Z) (f : X ⟶ Z) [IsOpenImmersion f]
    (O : T.Opens) (hO : O ≤ x ⁻¹ᵁ f.opensRange) :
    Set.range (O.ι ≫ x).base ⊆ Set.range f.base := by
  rintro _ ⟨o, rfl⟩
  have hmem : O.ι.base o ∈ (O : Set T) := by
    rw [← Scheme.Opens.range_ι O]
    exact ⟨o, rfl⟩
  have h : x.base (O.ι.base o) ∈ f.opensRange := hO hmem
  rw [Scheme.Hom.comp_apply]
  simpa [Scheme.Hom.coe_opensRange] using h

/-- Two morphisms into `Z` whose values at a point lie in the range of an open immersion `f`
factor through `f` on a common open neighbourhood of that point. -/
private theorem exists_opens_lift_of_mem_range {T X Z : Scheme.{u}} (x y : T ⟶ Z) (f : X ⟶ Z)
    [IsOpenImmersion f] (τ : T) (hx : x.base τ ∈ Set.range f.base)
    (hy : y.base τ ∈ Set.range f.base) :
    ∃ O : T.Opens, τ ∈ O ∧ ∃ x' y' : O.toScheme ⟶ X, x' ≫ f = O.ι ≫ x ∧ y' ≫ f = O.ι ≫ y :=
  ⟨x ⁻¹ᵁ f.opensRange ⊓ y ⁻¹ᵁ f.opensRange,
    ⟨by simpa [Scheme.Hom.coe_opensRange] using hx, by simpa [Scheme.Hom.coe_opensRange] using hy⟩,
    _, _, IsOpenImmersion.lift_fac f _ (range_restrict_subset x f _ inf_le_left),
    IsOpenImmersion.lift_fac f _ (range_restrict_subset y f _ inf_le_right)⟩

/-- Cancelling the monomorphism `j` turns equal composites with the charts' projections into
equal composites with `p` and `p'`. -/
private theorem comp_eq_comp_of_comp_chart_eq {T Y V Q R : Scheme.{u}} (j : Y ⟶ V)
    [Mono j] (b : Q ⟶ R) (s s' : R ⟶ V) (p p' : Q ⟶ Y) (hs : b ≫ s = p ≫ j)
    (hs' : b ≫ s' = p' ≫ j) (x y : T ⟶ Q) (h : (x ≫ b) ≫ s = (y ≫ b) ≫ s') :
    x ≫ p = y ≫ p' := by
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← hs, ← hs', ← Category.assoc,
    ← Category.assoc]
  exact h

/-- **The two projections of the glued relation are jointly monic**, for test morphisms from
arbitrary schemes, as soon as the two projections of `Q` are. -/
theorem hom_ext_of_isPushout
    (hQ : ∀ {T : Scheme.{u}} (x y : T ⟶ Q), x ≫ p₁ = y ≫ p₁ → x ≫ p₂ = y ≫ p₂ → x = y)
    {T : Scheme.{u}} {x y : T ⟶ R} (hs : x ≫ src hd₁ hR = y ≫ src hd₁ hR)
    (ht : x ≫ tgt hd₂ hR = y ≫ tgt hd₂ hR) : x = y := by
  have := isOpenImmersion_a hR
  have := isOpenImmersion_b hR
  have hsrc : ∀ τ, (src hd₁ hR).base (x.base τ) = (src hd₁ hR).base (y.base τ) := fun τ => by
    rw [← Scheme.Hom.comp_apply, hs, Scheme.Hom.comp_apply]
  refine Scheme.hom_ext_of_forall x y fun τ => ?_
  by_cases hx : x.base τ ∈ Set.range b.base
  · have hy : y.base τ ∈ Set.range b.base := by
      rw [mem_range_b_iff_src hd₁ hR] at hx ⊢
      rwa [← hsrc]
    obtain ⟨O, hO, x', y', hx', hy'⟩ := exists_opens_lift_of_mem_range x y b τ hx hy
    refine ⟨O, hO, ?_⟩
    rw [← hx', ← hy']
    congr 1
    exact hQ _ _
      (comp_eq_comp_of_comp_chart_eq j b _ _ _ _ (b_src hd₁ hR) (b_src hd₁ hR) _ _
        (by rw [hx', hy', Category.assoc, Category.assoc, hs]))
      (comp_eq_comp_of_comp_chart_eq j b _ _ _ _ (b_tgt hd₂ hR) (b_tgt hd₂ hR) _ _
        (by rw [hx', hy', Category.assoc, Category.assoc, ht]))
  · have hy : y.base τ ∉ Set.range b.base := fun hy => hx (by
      rw [mem_range_b_iff_src hd₁ hR] at hy ⊢
      rwa [hsrc])
    have hxa := (mem_range_a_or_b hR (x.base τ)).resolve_right hx
    have hya := (mem_range_a_or_b hR (y.base τ)).resolve_right hy
    obtain ⟨O, hO, x', y', hx', hy'⟩ := exists_opens_lift_of_mem_range x y a τ hxa hya
    refine ⟨O, hO, ?_⟩
    rw [← hx', ← hy']
    congr 1
    rw [← Category.comp_id x', ← Category.comp_id y', ← a_src hd₁ hR, ← Category.assoc,
      ← Category.assoc, hx', hy', Category.assoc, Category.assoc, hs]

omit [IsOpenImmersion j] [IsOpenImmersion d] in
/-- **The glued relation is symmetric**, as soon as `Q` is. -/
theorem exists_symm
    (hQ : ∀ {T : Scheme.{u}} (x y : T ⟶ Q), x ≫ p₁ = y ≫ p₁ → x ≫ p₂ = y ≫ p₂ → x = y)
    (σ : Q ⟶ Q) (hσ₁ : σ ≫ p₁ = p₂) (hσ₂ : σ ≫ p₂ = p₁) :
    ∃ σR : R ⟶ R, σR ≫ src hd₁ hR = tgt hd₂ hR ∧ σR ≫ tgt hd₂ hR = src hd₁ hR := by
  have hdσ : d ≫ σ = d := hQ _ _ (by rw [Category.assoc, hσ₁, hd₁, hd₂])
    (by rw [Category.assoc, hσ₂, hd₁, hd₂])
  refine ⟨hR.desc a (σ ≫ b) (by rw [hR.w, ← Category.assoc, hdσ]), hR.hom_ext ?_ ?_,
    hR.hom_ext ?_ ?_⟩
  · rw [hR.inl_desc_assoc, a_src, a_tgt]
  · rw [hR.inr_desc_assoc, Category.assoc, b_src, b_tgt, ← Category.assoc, hσ₁]
  · rw [hR.inl_desc_assoc, a_src, a_tgt]
  · rw [hR.inr_desc_assoc, Category.assoc, b_src, b_tgt, ← Category.assoc, hσ₂]

/-- **The glued relation is transitive**, as soon as `Q` is. -/
theorem exists_trans
    (hQ : ∀ {T : Scheme.{u}} (x y : T ⟶ Q), x ≫ p₁ = y ≫ p₁ → x ≫ p₂ = y ≫ p₂ → x = y)
    (hQt : ∀ {T : Scheme.{u}} (x y : T ⟶ Q), x ≫ p₂ = y ≫ p₁ →
      ∃ z : T ⟶ Q, z ≫ p₁ = x ≫ p₁ ∧ z ≫ p₂ = y ≫ p₂) :
    ∃ τR : pullback (tgt hd₂ hR) (src hd₁ hR) ⟶ R,
      τR ≫ src hd₁ hR = pullback.fst _ _ ≫ src hd₁ hR ∧
        τR ≫ tgt hd₂ hR = pullback.snd _ _ ≫ tgt hd₂ hR := by
  have := isOpenImmersion_a hR
  have := isOpenImmersion_b hR
  let x := pullback.fst (tgt hd₂ hR) (src hd₁ hR)
  let y := pullback.snd (tgt hd₂ hR) (src hd₁ hR)
  have hxy : x ≫ tgt hd₂ hR = y ≫ src hd₁ hR := pullback.condition
  have hchart : ∀ {T : Scheme.{u}} (z : T ⟶ R) (z' : T ⟶ V), z' ≫ a = z →
      z ≫ src hd₁ hR = z ≫ tgt hd₂ hR := fun z z' h => by
    rw [← h, Category.assoc, Category.assoc, a_src, a_tgt]
  refine exists_lift_of_locally_lift _ _
    (fun u v h₁ h₂ => hom_ext_of_isPushout hd₁ hd₂ hR hQ h₁ h₂) _ _
    fun τ => ?_
  by_cases hx : x.base τ ∈ Set.range b.base
  · by_cases hy : y.base τ ∈ Set.range b.base
    · obtain ⟨O, hO, x', y', hx', hy'⟩ := exists_opens_lift_of_mem_range x y b τ hx hy
      obtain ⟨z, hz₁, hz₂⟩ := hQt x' y'
        (comp_eq_comp_of_comp_chart_eq j b _ _ _ _ (b_tgt hd₂ hR) (b_src hd₁ hR) _ _
          (by rw [hx', hy', Category.assoc, Category.assoc, hxy]))
      refine ⟨O, hO, z ≫ b, ?_, ?_⟩
      · rw [Category.assoc, b_src, ← Category.assoc, hz₁, Category.assoc, ← b_src hd₁ hR,
          ← Category.assoc, hx', Category.assoc]
      · rw [Category.assoc, b_tgt, ← Category.assoc, hz₂, Category.assoc, ← b_tgt hd₂ hR,
          ← Category.assoc, hy', Category.assoc]
    · have hya := (mem_range_a_or_b hR (y.base τ)).resolve_right hy
      obtain ⟨O, hO, y', -, hy', -⟩ := exists_opens_lift_of_mem_range y y a τ hya hya
      refine ⟨O, hO, O.ι ≫ x, by rw [Category.assoc], ?_⟩
      calc (O.ι ≫ x) ≫ tgt hd₂ hR = O.ι ≫ y ≫ src hd₁ hR := by rw [Category.assoc, hxy]
        _ = O.ι ≫ y ≫ tgt hd₂ hR := by
          rw [← Category.assoc, ← Category.assoc, hchart _ y' hy']
  · have hxa := (mem_range_a_or_b hR (x.base τ)).resolve_right hx
    obtain ⟨O, hO, x', -, hx', -⟩ := exists_opens_lift_of_mem_range x x a τ hxa hxa
    refine ⟨O, hO, O.ι ≫ y, ?_, by rw [Category.assoc]⟩
    calc (O.ι ≫ y) ≫ src hd₁ hR = O.ι ≫ x ≫ tgt hd₂ hR := by rw [Category.assoc, hxy]
      _ = O.ι ≫ x ≫ src hd₁ hR := by
        rw [← Category.assoc, ← Category.assoc, (hchart _ x' hx').symm]

/-- The open cover of the glued relation by its two charts. -/
noncomputable def openCover : R.OpenCover where
  I₀ := Bool
  X i := if i then V else Q
  f i := match i with
    | true => a
    | false => b
  mem₀ := by
    have := isOpenImmersion_a hR
    have := isOpenImmersion_b hR
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ by cases i <;> dsimp <;> infer_instance⟩
    rcases mem_range_a_or_b hR x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨true, y, rfl⟩
    · exact ⟨false, y, rfl⟩

/-- A property local at the source holds for the first projection of the glued relation if it
holds for the identity of `V` and for `j ∘ p₁`. -/
theorem src_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h₁ : P (𝟙 V)) (h₂ : P (p₁ ≫ j)) : P (src hd₁ hR) :=
  IsZariskiLocalAtSource.of_openCover (openCover hR) fun i => by
    cases i
    · show P (b ≫ src hd₁ hR)
      rwa [b_src]
    · show P (a ≫ src hd₁ hR)
      rwa [a_src]

/-- A property local at the source holds for the second projection of the glued relation if it
holds for the identity of `V` and for `j ∘ p₂`. -/
theorem tgt_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (h₁ : P (𝟙 V)) (h₂ : P (p₂ ≫ j)) : P (tgt hd₂ hR) :=
  src_of_isZariskiLocalAtSource hd₂ hR P h₁ h₂

include hR in
/-- If the underlying spaces of `V` and `Q` are compact, then so is the underlying space of `R`. -/
theorem compactSpace [CompactSpace V] [CompactSpace Q] : CompactSpace R := by
  have hcov : (Set.univ : Set R) = Set.range a.base ∪ Set.range b.base := by
    ext x
    simpa using mem_range_a_or_b hR x
  refine ⟨?_⟩
  rw [hcov]
  exact (isCompact_range a.continuous).union (isCompact_range b.continuous)

end AlgebraicGeometry.GluedRelation

end
