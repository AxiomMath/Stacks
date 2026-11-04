module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleRelationTransition

/-!
# Extending an equivalence relation on an open subscheme by the diagonal

Let `j : W ⟶ V` be an open immersion of schemes and let `p₁, p₂ : Q ⟶ W` be an equivalence
relation on `W` whose reflexivity section `δ : W ⟶ Q` is an open immersion. Glueing `V` to `Q`
along `W`, which sits in `V` by `j` and in `Q` by `δ`, gives a scheme `R` with two morphisms
`t, s : R ⟶ V`: the identity on the chart `V`, and `p₁ ≫ j`, resp. `p₂ ≫ j`, on the chart `Q`.
The pair `t, s` is an equivalence relation on `V`: the relation `Q` over `W`, and the trivial
relation elsewhere. It is étale as soon as `p₁` and `p₂` are.

This is the relation `R_i` on `V_i` of the proof of absolute Noetherian approximation for
algebraic spaces, Stacks 07SU, where `Q = W_i ×_{U_i} W_i` is the kernel pair of an étale
morphism `W_i ⟶ U_i` to an algebraic space.

## Main definitions

* `AlgebraicGeometry.RelationExtension.target` and `AlgebraicGeometry.RelationExtension.source`:
  the two morphisms `pushout j δ ⟶ V`.

## Main results

* `AlgebraicGeometry.RelationExtension.equivalenceRelation`: the pair `target, source` is an
  equivalence relation on `V`, and `AlgebraicGeometry.RelationExtension.isEquivalenceRelation`
  its propositional form.
* `AlgebraicGeometry.RelationExtension.etale_target` and
  `AlgebraicGeometry.RelationExtension.etale_source`: the two morphisms are étale when `p₁` and
  `p₂` are.

## Implementation notes

The four properties of an equivalence relation are checked chart by chart. Joint monicity needs
no covering at all: two morphisms into `R` which factor through charts and have the same two
components are equal, by a case distinction on the charts, the mixed case using that a point of
`Q` with equal components lies on the diagonal. Symmetry is glued from the identity of `V` and
the symmetry of `Q`. Transitivity is constructed locally on the source, where both factors lie in
charts, and the local pieces are glued along an open cover of the source; they agree on the
overlaps by joint monicity, which is
`AlgebraicGeometry.RelationExtension.exists_lift_of_locally`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelationExtension

/-- **Glueing local solutions of a jointly monic pair.** Let `t, s : Z ⟶ V` be jointly monic and
let `a, b : Y ⟶ V`. If every point of `Y` has an open neighbourhood `U` with a morphism
`U ⟶ Z` whose two components are the restrictions of `a` and `b`, then there is a morphism
`Y ⟶ Z` with components `a` and `b`. The local morphisms agree on overlaps by joint monicity, so
they glue. -/
theorem exists_lift_of_locally {Y Z V : Scheme.{u}} (t s : Z ⟶ V) [JointlyMono₂ t s]
    (a b : Y ⟶ V)
    (H : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      ∃ τ : U.toScheme ⟶ Z, τ ≫ t = U.ι ≫ a ∧ τ ≫ s = U.ι ≫ b) :
    ∃ τ : Y ⟶ Z, τ ≫ t = a ∧ τ ≫ s = b := by
  choose U hyU τ hτt hτs using H
  let 𝒰 : Y.OpenCover :=
    { I₀ := Y
      X y := U y
      f y := (U y).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun y ↦ ⟨y, by simpa using hyU y⟩, inferInstance⟩ }
  have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ τ x = pullback.snd _ _ ≫ τ y := by
    intro x y
    apply JointlyMono₂.right_cancellation (p₁ := t) (p₂ := s)
    · simp only [Category.assoc, hτt]
      show pullback.fst (U x).ι (U y).ι ≫ (U x).ι ≫ a =
        pullback.snd (U x).ι (U y).ι ≫ (U y).ι ≫ a
      rw [pullback.condition_assoc]
    · simp only [Category.assoc, hτs]
      show pullback.fst (U x).ι (U y).ι ≫ (U x).ι ≫ b =
        pullback.snd (U x).ι (U y).ι ≫ (U y).ι ≫ b
      rw [pullback.condition_assoc]
  refine ⟨𝒰.glueMorphisms τ hcompat, ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun y ↦ ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact hτt y
  · refine 𝒰.hom_ext _ _ fun y ↦ ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact hτs y

variable {V W Q : Scheme.{u}} (j : W ⟶ V) [IsOpenImmersion j] (p₁ p₂ : Q ⟶ W)
  (δ : W ⟶ Q) [IsOpenImmersion δ]

/-- The *target* map of the extended relation: the identity on the chart `V` and `p₁ ≫ j` on
the chart `Q`. -/
noncomputable def target (hδ₁ : δ ≫ p₁ = 𝟙 W) : pushout j δ ⟶ V :=
  pushout.desc (𝟙 V) (p₁ ≫ j) (by rw [Category.comp_id, ← Category.assoc, hδ₁, Category.id_comp])

/-- The *source* map of the extended relation: the identity on the chart `V` and `p₂ ≫ j` on
the chart `Q`. -/
noncomputable def source (hδ₂ : δ ≫ p₂ = 𝟙 W) : pushout j δ ⟶ V :=
  pushout.desc (𝟙 V) (p₂ ≫ j) (by rw [Category.comp_id, ← Category.assoc, hδ₂, Category.id_comp])

variable {j p₁ p₂ δ}

/-- The target map restricts to the identity on the chart `V`. -/
@[reassoc (attr := simp)]
theorem inl_target (hδ₁ : δ ≫ p₁ = 𝟙 W) : pushout.inl j δ ≫ target j p₁ δ hδ₁ = 𝟙 V :=
  pushout.inl_desc _ _ _

/-- The target map restricts to `p₁ ≫ j` on the chart `Q`. -/
@[reassoc (attr := simp)]
theorem inr_target (hδ₁ : δ ≫ p₁ = 𝟙 W) : pushout.inr j δ ≫ target j p₁ δ hδ₁ = p₁ ≫ j :=
  pushout.inr_desc _ _ _

/-- The source map restricts to the identity on the chart `V`. -/
@[reassoc (attr := simp)]
theorem inl_source (hδ₂ : δ ≫ p₂ = 𝟙 W) : pushout.inl j δ ≫ source j p₂ δ hδ₂ = 𝟙 V :=
  pushout.inl_desc _ _ _

/-- The source map restricts to `p₂ ≫ j` on the chart `Q`. -/
@[reassoc (attr := simp)]
theorem inr_source (hδ₂ : δ ≫ p₂ = 𝟙 W) : pushout.inr j δ ≫ source j p₂ δ hδ₂ = p₂ ≫ j :=
  pushout.inr_desc _ _ _

/-- The chart `V` of the glueing is an open immersion. -/
instance isOpenImmersion_inl : IsOpenImmersion (pushout.inl j δ) :=
  isOpenImmersion_inl_of_isPushout (IsPushout.of_hasPushout j δ)

/-- The chart `Q` of the glueing is an open immersion. -/
instance isOpenImmersion_inr : IsOpenImmersion (pushout.inr j δ) :=
  isOpenImmersion_inr_of_isPushout (IsPushout.of_hasPushout j δ)

omit [IsOpenImmersion δ] in
/-- A point of `Q` with equal components lies on the diagonal. -/
theorem eq_comp_δ_of_comp_eq (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W)
    (hδ₂ : δ ≫ p₂ = 𝟙 W) {T : Scheme.{u}} (q : T ⟶ Q) (h : q ≫ p₁ = q ≫ p₂) :
    q = q ≫ p₁ ≫ δ := by
  apply hQ.right_cancellation
  · rw [Category.assoc, Category.assoc, hδ₁, Category.comp_id]
  · rw [Category.assoc, Category.assoc, hδ₂, Category.comp_id, h]

/-- **Joint monicity, chart by chart.** Two morphisms into the glueing, each factoring through
one of the two charts, with the same target and source components, are equal. -/
theorem eq_of_factor (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W) (hδ₂ : δ ≫ p₂ = 𝟙 W)
    {T : Scheme.{u}} (φ ψ : T ⟶ pushout j δ)
    (hφ : (∃ x, φ = x ≫ pushout.inl j δ) ∨ (∃ q, φ = q ≫ pushout.inr j δ))
    (hψ : (∃ x, ψ = x ≫ pushout.inl j δ) ∨ (∃ q, ψ = q ≫ pushout.inr j δ))
    (ht : φ ≫ target j p₁ δ hδ₁ = ψ ≫ target j p₁ δ hδ₁)
    (hs : φ ≫ source j p₂ δ hδ₂ = ψ ≫ source j p₂ δ hδ₂) : φ = ψ := by
  -- the mixed case: a point of `V` and a point of `Q` with the same components
  have mixed : ∀ (x : T ⟶ V) (q : T ⟶ Q),
      x ≫ pushout.inl j δ ≫ target j p₁ δ hδ₁ = q ≫ pushout.inr j δ ≫ target j p₁ δ hδ₁ →
      x ≫ pushout.inl j δ ≫ source j p₂ δ hδ₂ = q ≫ pushout.inr j δ ≫ source j p₂ δ hδ₂ →
      x ≫ pushout.inl j δ = q ≫ pushout.inr j δ := by
    intro x q h₁ h₂
    simp only [inl_target, inr_target, inl_source, inr_source, Category.comp_id] at h₁ h₂
    have hq : q ≫ p₁ = q ≫ p₂ := by
      apply (cancel_mono j).mp
      rw [Category.assoc, Category.assoc, ← h₁, ← h₂]
    rw [eq_comp_δ_of_comp_eq hQ hδ₁ hδ₂ q hq, Category.assoc, Category.assoc,
      ← pushout.condition, ← Category.assoc, ← Category.assoc, Category.assoc q, ← h₁]
  rcases hφ with ⟨x, rfl⟩ | ⟨q, rfl⟩ <;> rcases hψ with ⟨x', rfl⟩ | ⟨q', rfl⟩
  · simp only [Category.assoc, inl_target, Category.comp_id] at ht
    rw [ht]
  · exact mixed x q' (by simpa only [Category.assoc] using ht)
      (by simpa only [Category.assoc] using hs)
  · exact (mixed x' q (by simpa only [Category.assoc] using ht.symm)
      (by simpa only [Category.assoc] using hs.symm)).symm
  · simp only [Category.assoc, inr_target, inr_source] at ht hs
    have h₁ : q ≫ p₁ = q' ≫ p₁ := (cancel_mono j).mp (by simpa only [Category.assoc] using ht)
    have h₂ : q ≫ p₂ = q' ≫ p₂ := (cancel_mono j).mp (by simpa only [Category.assoc] using hs)
    rw [hQ.right_cancellation q q' h₁ h₂]

/-- Every point of a scheme mapping to the glueing has an open neighbourhood on which the map
factors through one of the two charts. -/
theorem exists_factor {T : Scheme.{u}} (f : T ⟶ pushout j δ) (y : T) :
    ∃ U : T.Opens, y ∈ U ∧
      ((∃ x : U.toScheme ⟶ V, U.ι ≫ f = x ≫ pushout.inl j δ) ∨
        (∃ q : U.toScheme ⟶ Q, U.ι ≫ f = q ≫ pushout.inr j δ)) := by
  have key : ∀ {X : Scheme.{u}} (g : X ⟶ pushout j δ) [IsOpenImmersion g], (∃ v, g v = f y) →
      ∃ U : T.Opens, y ∈ U ∧ ∃ x : U.toScheme ⟶ X, U.ι ≫ f = x ≫ g := by
    rintro X g _ ⟨v, hv⟩
    have H : Set.range ((f ⁻¹ᵁ g.opensRange).ι ≫ f) ⊆ Set.range g := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    exact ⟨f ⁻¹ᵁ g.opensRange, ⟨v, hv⟩, IsOpenImmersion.lift _ _ H,
      (IsOpenImmersion.lift_fac _ _ H).symm⟩
  rcases exists_eq_of_isPushout_of_isOpenImmersion (IsPushout.of_hasPushout j δ) (f y) with
    hy | hy
  · obtain ⟨U, hyU, h⟩ := key _ hy
    exact ⟨U, hyU, Or.inl h⟩
  · obtain ⟨U, hyU, h⟩ := key _ hy
    exact ⟨U, hyU, Or.inr h⟩

/-- Restricting a chart factorization to a smaller open. -/
theorem factor_restrict {T : Scheme.{u}} (f : T ⟶ pushout j δ) {U U' : T.Opens} (hle : U' ≤ U)
    (h : (∃ x : U.toScheme ⟶ V, U.ι ≫ f = x ≫ pushout.inl j δ) ∨
      (∃ q : U.toScheme ⟶ Q, U.ι ≫ f = q ≫ pushout.inr j δ)) :
    (∃ x : U'.toScheme ⟶ V, U'.ι ≫ f = x ≫ pushout.inl j δ) ∨
      (∃ q : U'.toScheme ⟶ Q, U'.ι ≫ f = q ≫ pushout.inr j δ) := by
  rcases h with ⟨x, hx⟩ | ⟨q, hq⟩
  · exact Or.inl ⟨T.homOfLE hle ≫ x, by rw [← T.homOfLE_ι hle, Category.assoc, hx, Category.assoc]⟩
  · exact Or.inr ⟨T.homOfLE hle ≫ q, by rw [← T.homOfLE_ι hle, Category.assoc, hq, Category.assoc]⟩

/-- **The extended relation is jointly monic.** -/
theorem jointlyMono₂ (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W) (hδ₂ : δ ≫ p₂ = 𝟙 W) :
    JointlyMono₂ (target j p₁ δ hδ₁) (source j p₂ δ hδ₂) where
  right_cancellation T f g ht hs := by
    refine Scheme.hom_ext_of_forall f g fun y ↦ ?_
    obtain ⟨U, hyU, hU⟩ := exists_factor f y
    obtain ⟨U', hyU', hU'⟩ := exists_factor g y
    refine ⟨U ⊓ U', ⟨hyU, hyU'⟩, ?_⟩
    refine eq_of_factor hQ hδ₁ hδ₂ _ _ ?_ ?_ ?_ ?_
    · exact factor_restrict f inf_le_left hU
    · exact factor_restrict g inf_le_right hU'
    · rw [Category.assoc, ht, Category.assoc]
    · rw [Category.assoc, hs, Category.assoc]

omit [IsOpenImmersion δ] in
/-- The symmetry of `Q` fixes the diagonal. -/
theorem δ_comp_symm (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W) (hδ₂ : δ ≫ p₂ = 𝟙 W)
    (σ : Q ⟶ Q) (hσ₁ : σ ≫ p₁ = p₂) (hσ₂ : σ ≫ p₂ = p₁) : δ ≫ σ = δ := by
  apply hQ.right_cancellation
  · rw [Category.assoc, hσ₁, hδ₂, hδ₁]
  · rw [Category.assoc, hσ₂, hδ₁, hδ₂]

/-- The symmetry of the extended relation: the identity on the chart `V` and the symmetry of `Q`
on the chart `Q`. -/
noncomputable def symm (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W) (hδ₂ : δ ≫ p₂ = 𝟙 W)
    (σ : Q ⟶ Q) (hσ₁ : σ ≫ p₁ = p₂) (hσ₂ : σ ≫ p₂ = p₁) : pushout j δ ⟶ pushout j δ :=
  pushout.desc (pushout.inl j δ) (σ ≫ pushout.inr j δ) (by
    rw [pushout.condition, ← Category.assoc, δ_comp_symm hQ hδ₁ hδ₂ σ hσ₁ hσ₂])

/-- The symmetry followed by the target map is the source map. -/
theorem symm_target (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W) (hδ₂ : δ ≫ p₂ = 𝟙 W)
    (σ : Q ⟶ Q) (hσ₁ : σ ≫ p₁ = p₂) (hσ₂ : σ ≫ p₂ = p₁) :
    symm hQ hδ₁ hδ₂ σ hσ₁ hσ₂ ≫ target j p₁ δ hδ₁ = source j p₂ δ hδ₂ := by
  refine pushout.hom_ext ?_ ?_
  · rw [symm, pushout.inl_desc_assoc, inl_target, inl_source]
  · rw [symm, pushout.inr_desc_assoc, Category.assoc, inr_target, inr_source,
      ← Category.assoc, hσ₁]

/-- The symmetry followed by the source map is the target map. -/
theorem symm_source (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W) (hδ₂ : δ ≫ p₂ = 𝟙 W)
    (σ : Q ⟶ Q) (hσ₁ : σ ≫ p₁ = p₂) (hσ₂ : σ ≫ p₂ = p₁) :
    symm hQ hδ₁ hδ₂ σ hσ₁ hσ₂ ≫ source j p₂ δ hδ₂ = target j p₁ δ hδ₁ := by
  refine pushout.hom_ext ?_ ?_
  · rw [symm, pushout.inl_desc_assoc, inl_target, inl_source]
  · rw [symm, pushout.inr_desc_assoc, Category.assoc, inr_target, inr_source,
      ← Category.assoc, hσ₂]

/-- **Transitivity of the extended relation**, for an arbitrary scheme of composable pairs:
given `α, β : Y ⟶ R` with `α ≫ source = β ≫ target`, there is `τ : Y ⟶ R` with target
`α ≫ target` and source `β ≫ source`. -/
theorem exists_trans (hQ : JointlyMono₂ p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W) (hδ₂ : δ ≫ p₂ = 𝟙 W)
    (hQt : ∀ {T : Scheme.{u}} (q₁ q₂ : T ⟶ Q), q₁ ≫ p₂ = q₂ ≫ p₁ →
      ∃ q : T ⟶ Q, q ≫ p₁ = q₁ ≫ p₁ ∧ q ≫ p₂ = q₂ ≫ p₂)
    {Y : Scheme.{u}} (α β : Y ⟶ pushout j δ)
    (h : α ≫ source j p₂ δ hδ₂ = β ≫ target j p₁ δ hδ₁) :
    ∃ τ : Y ⟶ pushout j δ,
      τ ≫ target j p₁ δ hδ₁ = α ≫ target j p₁ δ hδ₁ ∧
        τ ≫ source j p₂ δ hδ₂ = β ≫ source j p₂ δ hδ₂ := by
  have := jointlyMono₂ (j := j) hQ hδ₁ hδ₂
  refine exists_lift_of_locally _ _ _ _ fun y ↦ ?_
  obtain ⟨U, hyU, hU⟩ := exists_factor α y
  obtain ⟨U', hyU', hU'⟩ := exists_factor β y
  refine ⟨U ⊓ U', ⟨hyU, hyU'⟩, ?_⟩
  have hU₀ := factor_restrict α (inf_le_left : U ⊓ U' ≤ U) hU
  have hU₀' := factor_restrict β (inf_le_right : U ⊓ U' ≤ U') hU'
  set O := U ⊓ U'
  have hO : O.ι ≫ α ≫ source j p₂ δ hδ₂ = O.ι ≫ β ≫ target j p₁ δ hδ₁ := by rw [h]
  -- a morphism factoring through the chart `V` has equal target and source components
  have inl_comp : ∀ (γ : Y ⟶ pushout j δ) (x : O.toScheme ⟶ V), O.ι ≫ γ = x ≫ pushout.inl j δ →
      O.ι ≫ γ ≫ target j p₁ δ hδ₁ = x ∧ O.ι ≫ γ ≫ source j p₂ δ hδ₂ = x := fun γ x hx ↦ by
    rw [← Category.assoc, hx, ← Category.assoc O.ι, hx]
    simp
  rcases hU₀ with ⟨x, hx⟩ | ⟨q₁, hq₁⟩
  · -- the first factor lies in the chart `V`: take the second factor
    obtain ⟨e1, e2⟩ := inl_comp α x hx
    refine ⟨O.ι ≫ β, ?_, by rw [Category.assoc]⟩
    rw [Category.assoc, ← hO, e2, e1]
  rcases hU₀' with ⟨x, hx⟩ | ⟨q₂, hq₂⟩
  · -- the second factor lies in the chart `V`: take the first factor
    obtain ⟨e1, e2⟩ := inl_comp β x hx
    refine ⟨O.ι ≫ α, by rw [Category.assoc], ?_⟩
    rw [Category.assoc, hO, e1, e2]
  -- both factors lie in the chart `Q`: compose in `Q`
  have hq : q₁ ≫ p₂ = q₂ ≫ p₁ := by
    apply (cancel_mono j).mp
    have := hO
    rw [← Category.assoc, hq₁, ← Category.assoc O.ι, hq₂] at this
    simpa only [Category.assoc, inr_source, inr_target] using this
  obtain ⟨q, hq₁p, hq₂p⟩ := hQt q₁ q₂ hq
  refine ⟨q ≫ pushout.inr j δ, ?_, ?_⟩
  · rw [← Category.assoc, hq₁]
    simp only [Category.assoc, inr_target, ← reassoc_of% hq₁p]
  · rw [← Category.assoc, hq₂]
    simp only [Category.assoc, inr_source, ← reassoc_of% hq₂p]

/-- **The extended relation is an equivalence relation.** If `p₁, p₂ : Q ⟶ W` is an
equivalence relation whose reflexivity section is the open immersion `δ`, then the two maps
`target, source : pushout j δ ⟶ V`, the identity on `V` and `p₁ ≫ j`, `p₂ ≫ j` on `Q`, form an
equivalence relation on `V`. -/
noncomputable def equivalenceRelation (hQ : EquivalenceRelation p₁ p₂) (hδ₁ : δ ≫ p₁ = 𝟙 W)
    (hδ₂ : δ ≫ p₂ = 𝟙 W) :
    EquivalenceRelation (target j p₁ δ hδ₁) (source j p₂ δ hδ₂) :=
  haveI hmono := jointlyMono₂ (j := j) hQ.toJointlyMono₂ hδ₁ hδ₂
  have hQt : ∀ {T : Scheme.{u}} (q₁ q₂ : T ⟶ Q), q₁ ≫ p₂ = q₂ ≫ p₁ →
      ∃ q : T ⟶ Q, q ≫ p₁ = q₁ ≫ p₁ ∧ q ≫ p₂ = q₂ ≫ p₂ := by
    intro T q₁ q₂ h
    let ℓ : T ⟶ hQ.c.pt := PullbackCone.IsLimit.lift hQ.isLimit q₁ q₂ h
    refine ⟨ℓ ≫ hQ.t, ?_, ?_⟩
    · rw [Category.assoc, hQ.transitivity₁, ← Category.assoc,
        PullbackCone.IsLimit.lift_fst]
    · rw [Category.assoc, hQ.transitivity₂, ← Category.assoc,
        PullbackCone.IsLimit.lift_snd]
  have hex := fun {Y : Scheme.{u}} (α β : Y ⟶ pushout j δ) h ↦
    exists_trans (j := j) hQ.toJointlyMono₂ hδ₁ hδ₂ hQt α β h
  { right_cancellation := hmono.right_cancellation
    r := pushout.inl j δ
    s := symm hQ.toJointlyMono₂ hδ₁ hδ₂ hQ.s hQ.symmetry₁ hQ.symmetry₂
    symmetry₁ := symm_target hQ.toJointlyMono₂ hδ₁ hδ₂ hQ.s hQ.symmetry₁ hQ.symmetry₂
    symmetry₂ := symm_source hQ.toJointlyMono₂ hδ₁ hδ₂ hQ.s hQ.symmetry₁ hQ.symmetry₂
    c := pullback.cone (source j p₂ δ hδ₂) (target j p₁ δ hδ₁)
    isLimit := pullback.isLimit _ _
    t := (hex (pullback.fst _ _) (pullback.snd _ _) pullback.condition).choose
    transitivity₁ :=
      (hex (pullback.fst _ _) (pullback.snd _ _) pullback.condition).choose_spec.1
    transitivity₂ :=
      (hex (pullback.fst _ _) (pullback.snd _ _) pullback.condition).choose_spec.2 }

/-- **The extended relation is an equivalence relation**, propositionally. -/
theorem isEquivalenceRelation [hQ : IsEquivalenceRelation p₁ p₂] (hδ₁ : δ ≫ p₁ = 𝟙 W)
    (hδ₂ : δ ≫ p₂ = 𝟙 W) :
    IsEquivalenceRelation (target j p₁ δ hδ₁) (source j p₂ δ hδ₂) :=
  (equivalenceRelation hQ.nonempty_equivalenceRelation.some hδ₁ hδ₂).isEquivalenceRelation

/-- The two charts of the glueing cover it. -/
theorem iSup_opensRange_eq_top :
    (pushout.inl j δ).opensRange ⊔ (pushout.inr j δ).opensRange = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union, SetLike.mem_coe,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  rcases exists_eq_of_isPushout_of_isOpenImmersion (IsPushout.of_hasPushout j δ) x with
    ⟨v, hv⟩ | ⟨q, hq⟩
  · exact Or.inl ⟨v, hv⟩
  · exact Or.inr ⟨q, hq⟩

/-- A property of morphisms local on the source holds for a morphism out of the glueing as soon
as it holds on the two charts. -/
theorem of_charts (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] {Z : Scheme.{u}}
    (f : pushout j δ ⟶ Z) (hl : P (pushout.inl j δ ≫ f)) (hr : P (pushout.inr j δ ≫ f)) :
    P f := by
  have key : ∀ {X : Scheme.{u}} (g : X ⟶ pushout j δ) [IsOpenImmersion g], P (g ≫ f) →
      P (g.opensRange.ι ≫ f) := by
    intro X g _ hg
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac g g.opensRange.ι (by simp), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact hg
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun b : Bool ↦ if b then (pushout.inl j δ).opensRange else (pushout.inr j δ).opensRange)
    ?_ fun b ↦ ?_
  · rw [← iSup_opensRange_eq_top (j := j) (δ := δ), iSup_bool_eq]
    rfl
  · cases b
    · exact key _ hr
    · exact key _ hl

/-- **The target map is étale** when `p₁` is. -/
theorem etale_target [Etale p₁] (hδ₁ : δ ≫ p₁ = 𝟙 W) : Etale (target j p₁ δ hδ₁) :=
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  of_charts @Etale _ (by rw [inl_target]; infer_instance) (by rw [inr_target]; infer_instance)

/-- **The source map is étale** when `p₂` is. -/
theorem etale_source [Etale p₂] (hδ₂ : δ ≫ p₂ = 𝟙 W) : Etale (source j p₂ δ hδ₂) :=
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  of_charts @Etale _ (by rw [inl_source]; infer_instance) (by rw [inr_source]; infer_instance)

end AlgebraicGeometry.RelationExtension

end
