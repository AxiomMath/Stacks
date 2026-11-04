module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleRelationTransition

/-!
# Glueing an étale equivalence relation to the identity relation

Let `j : W ⟶ V` be an open immersion of schemes, and let `(t₀, s₀) : P ⟶ W` be an étale
equivalence relation on `W` with diagonal `δ : W ⟶ P`, so that `δ ≫ s₀ = 𝟙 W` and
`δ ≫ t₀ = 𝟙 W`. Since `δ` is a section of an étale morphism it is an open immersion
(`AlgebraicGeometry.isOpenImmersion_of_section_of_etale`), and one may glue `V` and `P` along
`W`: this is a pushout square

```
W  --δ-->  P
|          |
j          b
v          v
V  --a-->  R
```

The morphisms `s, t : R ⟶ V` which are the identity on the chart `V` and `s₀ ≫ j`, resp.
`t₀ ≫ j`, on the chart `P` form an étale equivalence relation `(t, s)` on `V`: it is the trivial
relation away from `W`, and the given one on `W`.

This is the construction made in the proof of absolute Noetherian approximation for
quasi-compact and quasi-separated algebraic spaces (Stacks 07SU): there `W = W_i` is an open
subscheme of `V = V_i`, `P = W_i ×_{U_i} W_i` with its two projections and the diagonal, and the
glued scheme is the scheme `R_i` of the proof, of which the source asserts that `(t_i, s_i)` is
an étale equivalence relation on `V_i`.

All verifications are local on `R` (and on `R ×_{s, V, t} R`), which is covered by the two
charts `V` and `P`: reflexivity is witnessed by `a`; symmetry is glued from the identity of `V`
and the symmetry of `P`; joint monicity and transitivity are checked on the opens of a source
scheme where the relevant morphisms factor through one of the two charts, the local composites
being glued using joint monicity.

## Main definitions

* `AlgebraicGeometry.gluedRelationMap`: the morphism `pushout j δ ⟶ V` which is the identity
  on `V` and `q ≫ j` on `P`, for a retraction `q` of `δ`.

## Main results

* `AlgebraicGeometry.exists_lift_of_jointlyMono₂_of_forall`: lifting along a jointly monic pair
  of morphisms of schemes is local on the source.
* `AlgebraicGeometry.IsZariskiLocalAtSource.of_isPushout`: a property local on the source holds
  for a morphism out of a glueing of two schemes along a common open as soon as it holds on the
  two charts.
* `AlgebraicGeometry.compactSpace_of_isPushout`: such a glueing of two quasi-compact schemes is
  quasi-compact.
* `AlgebraicGeometry.etale_of_isPushout`: the maps `s` and `t` are étale.
* `AlgebraicGeometry.quasiCompact_of_isPushout`: the maps `s` and `t` are quasi-compact when `j`
  and `s₀`, resp. `t₀`, are. (When `V` is quasi-separated and `R` is quasi-compact this is also
  supplied by Mathlib's instance `AlgebraicGeometry.quasiCompact_of_compactSpace`.)
* `AlgebraicGeometry.jointlyMono₂_of_isPushout`: the pair `(t, s)` is jointly monic.
* `AlgebraicGeometry.isEquivalenceRelation_of_isPushout`: the pair `(t, s)` is an equivalence
  relation on `V`.
* `AlgebraicGeometry.etale_and_isEquivalenceRelation_of_isPushout`: the two previous facts
  together: `(t, s)` is an étale equivalence relation on `V`.
* `AlgebraicGeometry.isEquivalenceRelation_gluedRelationMap`: the same for the chosen glueing
  `pushout j δ`, together with the instances `CompactSpace`, `LocallyOfFiniteType` over the
  terminal scheme, and étaleness and quasi-compactness of `AlgebraicGeometry.gluedRelationMap`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Lifting a pair of morphisms along a jointly monic pair of morphisms of schemes is local on
the source: if `x₁ : T ⟶ V₁` and `x₂ : T ⟶ V₂` lift through `p₁ : R ⟶ V₁` and `p₂ : R ⟶ V₂` on
a neighbourhood of every point of `T`, then they lift globally. The local lifts glue because they
agree on overlaps by joint monicity. -/
theorem exists_lift_of_jointlyMono₂_of_forall {R V₁ V₂ T : Scheme.{u}} (p₁ : R ⟶ V₁)
    (p₂ : R ⟶ V₂) [JointlyMono₂ p₁ p₂] (x₁ : T ⟶ V₁) (x₂ : T ⟶ V₂)
    (H : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧
      ∃ f : U.toScheme ⟶ R, f ≫ p₁ = U.ι ≫ x₁ ∧ f ≫ p₂ = U.ι ≫ x₂) :
    ∃ f : T ⟶ R, f ≫ p₁ = x₁ ∧ f ≫ p₂ = x₂ := by
  choose U hxU f hf₁ hf₂ using H
  let 𝒰 : T.OpenCover :=
    { I₀ := T, X x := U x, f x := (U x).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  have hglue : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x =
      pullback.snd (𝒰.f x) (𝒰.f y) ≫ f y := by
    intro x y
    refine JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ ?_ ?_
    · simpa only [Category.assoc, hf₁] using pullback.condition_assoc x₁
    · simpa only [Category.assoc, hf₂] using pullback.condition_assoc x₂
  exact ⟨𝒰.glueMorphisms f hglue, 𝒰.hom_ext _ _ fun x ↦ by rw [𝒰.ι_glueMorphisms_assoc, hf₁],
    𝒰.hom_ext _ _ fun x ↦ by rw [𝒰.ι_glueMorphisms_assoc, hf₂]⟩

/-- A morphism into the target of an open immersion `a` lifts through `a` on every open of its
source which it maps into the image of `a`. -/
private lemma exists_comp_eq_ι_comp {A R T : Scheme.{u}} (a : A ⟶ R) [IsOpenImmersion a]
    (φ : T ⟶ R) (U : T.Opens) (hU : U ≤ φ ⁻¹ᵁ a.opensRange) :
    ∃ u : U.toScheme ⟶ A, u ≫ a = U.ι ≫ φ := by
  refine ⟨IsOpenImmersion.lift a (U.ι ≫ φ) ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨y, rfl⟩
  exact hU y.2

section Pushout

variable {X Y W R : Scheme.{u}} {f : W ⟶ X} {g : W ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion g]
  {a : X ⟶ R} {b : Y ⟶ R}

/-- A property of morphisms of schemes which is local on the source holds for a morphism out of
the glueing of two schemes along a common open as soon as it holds on the two charts. -/
theorem IsZariskiLocalAtSource.of_isPushout {Q : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource Q] (h : IsPushout f g a b) {Z : Scheme.{u}} {φ : R ⟶ Z}
    (ha : Q (a ≫ φ)) (hb : Q (b ≫ φ)) : Q φ := by
  have := isOpenImmersion_inl_of_isPushout h
  have := isOpenImmersion_inr_of_isPushout h
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun i : Bool ↦ bif i then a.opensRange else b.opensRange) ?_ ?_
  · refine top_unique fun x _ ↦ ?_
    rw [iSup_bool_eq]
    rcases exists_eq_of_isPushout_of_isOpenImmersion h x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  · rintro (_ | _)
    · simpa only [cond_false, ← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc,
        Q.cancel_left_of_respectsIso] using hb
    · simpa only [cond_true, ← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc,
        Q.cancel_left_of_respectsIso] using ha

/-- The glueing of two quasi-compact schemes along a common open is quasi-compact. -/
theorem compactSpace_of_isPushout (h : IsPushout f g a b) [CompactSpace X] [CompactSpace Y] :
    CompactSpace R := by
  rw [← isCompact_univ_iff]
  convert (isCompact_range a.continuous).union (isCompact_range b.continuous)
  exact (Set.eq_univ_of_forall fun x ↦ exists_eq_of_isPushout_of_isOpenImmersion h x).symm

end Pushout

section GluedRelation

variable {V W P R : Scheme.{u}} {j : W ⟶ V} {s₀ t₀ : P ⟶ W} {δ : W ⟶ P}
  {a : V ⟶ R} {b : P ⟶ R}

/-- The glueing of `V` and `P` along the open immersions `j : W ⟶ V` and `δ : W ⟶ P`, mapped to
`V` by the identity on `V` and by `q ≫ j` on `P` for an étale retraction `q` of `δ`, is étale over
`V`. -/
theorem etale_of_isPushout [IsOpenImmersion j] [IsOpenImmersion δ] {q : P ⟶ W} [Etale q]
    (hR : IsPushout j δ a b) {s : R ⟶ V} (hsa : a ≫ s = 𝟙 V) (hsb : b ≫ s = q ≫ j) :
    Etale s := by
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  exact IsZariskiLocalAtSource.of_isPushout hR (by rw [hsa]; infer_instance)
    (by rw [hsb]; infer_instance)

/-- The glueing of `V` and `P` along the open immersions `j : W ⟶ V` and `δ : W ⟶ P`, mapped to
`V` by the identity on `V` and by `q ≫ j` on `P`, is quasi-compact over `V` as soon as `j` and `q`
are: the inverse image of a quasi-compact open `K` of `V` is the union of `K` in the first chart
and of `q⁻¹(j⁻¹(K))` in the second. -/
theorem quasiCompact_of_isPushout [IsOpenImmersion j] [IsOpenImmersion δ] [QuasiCompact j]
    {q : P ⟶ W} [QuasiCompact q] (hR : IsPushout j δ a b) {s : R ⟶ V} (hsa : a ≫ s = 𝟙 V)
    (hsb : b ≫ s = q ≫ j) : QuasiCompact s := by
  have ha : ∀ y, s (a y) = y := fun y ↦ by rw [← Scheme.Hom.comp_apply, hsa]; rfl
  have hb : ∀ z, s (b z) = j (q z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, hsb, Scheme.Hom.comp_apply]
  refine ⟨fun K hK hc ↦ ?_⟩
  have hpre : s ⁻¹' K = a '' K ∪ b '' (q ⁻¹' (j ⁻¹' K)) := by
    ext x
    refine ⟨fun hx ↦ ?_, ?_⟩
    · rcases exists_eq_of_isPushout_of_isOpenImmersion hR x with ⟨y, rfl⟩ | ⟨z, rfl⟩
      · exact Or.inl ⟨y, by simpa [ha] using hx, rfl⟩
      · exact Or.inr ⟨z, by simpa [hb] using hx, rfl⟩
    · rintro (⟨y, hy, rfl⟩ | ⟨z, hz, rfl⟩)
      · simpa [Set.mem_preimage, ha] using hy
      · simpa [Set.mem_preimage, hb] using hz
  rw [hpre]
  exact (hc.image a.continuous).union
    ((QuasiCompact.isCompact_preimage (f := q) _ (hK.preimage j.continuous)
      (QuasiCompact.isCompact_preimage (f := j) K hK hc)).image b.continuous)

/-- If `(t₀, s₀)` is a jointly monic pair on `W` with common section `δ`, then the pair
`(t, s)` obtained by glueing it with the identity relation of `V` along `W` is jointly monic. -/
theorem jointlyMono₂_of_isPushout [IsOpenImmersion j] [IsOpenImmersion δ] [JointlyMono₂ t₀ s₀]
    (hδs : δ ≫ s₀ = 𝟙 W) (hδt : δ ≫ t₀ = 𝟙 W) (hR : IsPushout j δ a b) {s t : R ⟶ V}
    (hsa : a ≫ s = 𝟙 V) (hsb : b ≫ s = s₀ ≫ j) (hta : a ≫ t = 𝟙 V) (htb : b ≫ t = t₀ ≫ j) :
    JointlyMono₂ t s := by
  have := isOpenImmersion_inl_of_isPushout hR
  have := isOpenImmersion_inr_of_isPushout hR
  -- A point of the first chart and a point of the second chart with the same image under
  -- `t` and `s` are equal.
  have key : ∀ {U : Scheme.{u}} (u : U ⟶ V) (v : U ⟶ P),
      u = v ≫ t₀ ≫ j → u = v ≫ s₀ ≫ j → u ≫ a = v ≫ b := by
    intro U u v hut hus
    have hst : v ≫ s₀ = v ≫ t₀ := by
      rw [← cancel_mono j, Category.assoc, Category.assoc, ← hut, ← hus]
    have hv : v = (v ≫ t₀) ≫ δ :=
      JointlyMono₂.right_cancellation (p₁ := t₀) (p₂ := s₀) _ _
        (by rw [Category.assoc, Category.assoc, hδt, Category.comp_id])
        (by rw [Category.assoc, Category.assoc, hδs, Category.comp_id, hst])
    rw [hv, Category.assoc, ← hR.w, hut]
    simp only [Category.assoc]
  refine ⟨fun T φ ψ h₁ h₂ ↦ Scheme.hom_ext_of_forall _ _ fun x ↦ ?_⟩
  have hU : ∀ (φ ψ : T ⟶ R) (r : R ⟶ V) (U : T.Opens), φ ≫ r = ψ ≫ r →
      U.ι ≫ φ ≫ r = U.ι ≫ ψ ≫ r := fun _ _ _ _ h ↦ by rw [h]
  -- The mixed case: `φ x` lies in the first chart and `ψ x` in the second.
  have mixed : ∀ φ ψ : T ⟶ R, φ ≫ t = ψ ≫ t → φ ≫ s = ψ ≫ s → φ x ∈ a.opensRange →
      ψ x ∈ b.opensRange → ∃ U : T.Opens, x ∈ U ∧ U.ι ≫ φ = U.ι ≫ ψ := by
    intro φ ψ h₁ h₂ hφ hψ
    let U := φ ⁻¹ᵁ a.opensRange ⊓ ψ ⁻¹ᵁ b.opensRange
    refine ⟨U, ⟨hφ, hψ⟩, ?_⟩
    obtain ⟨u, hu⟩ := exists_comp_eq_ι_comp a φ U inf_le_left
    obtain ⟨v, hv⟩ := exists_comp_eq_ι_comp b ψ U inf_le_right
    have e₁ := hU φ ψ t U h₁
    have e₂ := hU φ ψ s U h₂
    rw [← Category.assoc, ← hu, ← Category.assoc, ← hv, Category.assoc, Category.assoc, hta,
      htb, Category.comp_id] at e₁
    rw [← Category.assoc, ← hu, ← Category.assoc, ← hv, Category.assoc, Category.assoc, hsa,
      hsb, Category.comp_id] at e₂
    rw [← hu, ← hv]
    exact key u v e₁ e₂
  rcases exists_eq_of_isPushout_of_isOpenImmersion hR (φ x) with hφ | hφ <;>
    rcases exists_eq_of_isPushout_of_isOpenImmersion hR (ψ x) with hψ | hψ
  · refine ⟨φ ⁻¹ᵁ a.opensRange ⊓ ψ ⁻¹ᵁ a.opensRange, ⟨hφ, hψ⟩, ?_⟩
    obtain ⟨u, hu⟩ := exists_comp_eq_ι_comp a φ _ inf_le_left
    obtain ⟨u', hu'⟩ := exists_comp_eq_ι_comp a ψ _ inf_le_right
    rw [← hu, ← hu']
    congr 1
    have := hU φ ψ t (φ ⁻¹ᵁ a.opensRange ⊓ ψ ⁻¹ᵁ a.opensRange) h₁
    rwa [← Category.assoc, ← hu, ← Category.assoc, ← hu', Category.assoc, Category.assoc, hta,
      Category.comp_id, Category.comp_id] at this
  · exact mixed φ ψ h₁ h₂ hφ hψ
  · obtain ⟨U, hx, hU⟩ := mixed ψ φ h₁.symm h₂.symm hψ hφ
    exact ⟨U, hx, hU.symm⟩
  · refine ⟨φ ⁻¹ᵁ b.opensRange ⊓ ψ ⁻¹ᵁ b.opensRange, ⟨hφ, hψ⟩, ?_⟩
    obtain ⟨v, hv⟩ := exists_comp_eq_ι_comp b φ _ inf_le_left
    obtain ⟨v', hv'⟩ := exists_comp_eq_ι_comp b ψ _ inf_le_right
    have e₁ := hU φ ψ t (φ ⁻¹ᵁ b.opensRange ⊓ ψ ⁻¹ᵁ b.opensRange) h₁
    have e₂ := hU φ ψ s (φ ⁻¹ᵁ b.opensRange ⊓ ψ ⁻¹ᵁ b.opensRange) h₂
    rw [← Category.assoc, ← hv, ← Category.assoc, ← hv', Category.assoc, Category.assoc, htb,
      ← Category.assoc, ← Category.assoc, cancel_mono] at e₁
    rw [← Category.assoc, ← hv, ← Category.assoc, ← hv', Category.assoc, Category.assoc, hsb,
      ← Category.assoc, ← Category.assoc, cancel_mono] at e₂
    rw [← hv, ← hv', JointlyMono₂.right_cancellation (p₁ := t₀) (p₂ := s₀) v v' e₁ e₂]

/-- **The glued étale equivalence relation of the proof of Stacks 07SU.** Let `j : W ⟶ V` be an
open immersion, let `(t₀, s₀) : P ⟶ W` be an étale equivalence relation on `W` with diagonal
`δ`, and let `R` be the glueing of `V` and `P` along `W`, that is a pushout of `j` and `δ`. Then
the morphisms `s, t : R ⟶ V` which are the identity on `V` and `s₀ ≫ j`, resp. `t₀ ≫ j`, on `P`
form an equivalence relation `(t, s)` on `V`. -/
theorem isEquivalenceRelation_of_isPushout [IsOpenImmersion j] [Etale s₀]
    [IsEquivalenceRelation t₀ s₀] (hδs : δ ≫ s₀ = 𝟙 W) (hδt : δ ≫ t₀ = 𝟙 W)
    (hR : IsPushout j δ a b) {s t : R ⟶ V} (hsa : a ≫ s = 𝟙 V) (hsb : b ≫ s = s₀ ≫ j)
    (hta : a ≫ t = 𝟙 V) (htb : b ≫ t = t₀ ≫ j) :
    IsEquivalenceRelation t s := by
  have : IsOpenImmersion δ := isOpenImmersion_of_section_of_etale s₀ δ hδs
  have := isOpenImmersion_inl_of_isPushout hR
  have := isOpenImmersion_inr_of_isPushout hR
  obtain ⟨e⟩ := ‹IsEquivalenceRelation t₀ s₀›.nonempty_equivalenceRelation
  have : JointlyMono₂ t₀ s₀ := e.toJointlyMono₂
  have hm : JointlyMono₂ t s := jointlyMono₂_of_isPushout hδs hδt hR hsa hsb hta htb
  -- The symmetry of `P` fixes the diagonal, so it glues with the identity of `V`.
  have hδσ : δ ≫ e.s = δ :=
    JointlyMono₂.right_cancellation (p₁ := t₀) (p₂ := s₀) _ _
      (by rw [Category.assoc, e.symmetry₁, hδs, hδt])
      (by rw [Category.assoc, e.symmetry₂, hδs, hδt])
  let σ : R ⟶ R := hR.desc a (e.s ≫ b) (by rw [← Category.assoc, hδσ, hR.w])
  have hσt : σ ≫ t = s := hR.hom_ext (by simp [σ, hta, hsa])
    (by simp only [σ, IsPushout.inr_desc_assoc, Category.assoc, htb, hsb, e.symmetry₁_assoc])
  have hσs : σ ≫ s = t := hR.hom_ext (by simp [σ, hta, hsa])
    (by simp only [σ, IsPushout.inr_desc_assoc, Category.assoc, htb, hsb, e.symmetry₂_assoc])
  -- Transitivity is glued from local composites on `R ×_{s, V, t} R`.
  obtain ⟨τ, hτt, hτs⟩ := exists_lift_of_jointlyMono₂_of_forall t s
    (pullback.fst s t ≫ t) (pullback.snd s t ≫ s) fun x ↦ by
      have hc := pullback.condition (f := s) (g := t)
      rcases exists_eq_of_isPushout_of_isOpenImmersion hR (pullback.fst s t x) with hF | hF
      · -- The first factor lies in the chart `V`: the composite is the second factor.
        let U := pullback.fst s t ⁻¹ᵁ a.opensRange
        obtain ⟨u, hu⟩ := exists_comp_eq_ι_comp a (pullback.fst s t) U le_rfl
        refine ⟨U, hF, U.ι ≫ pullback.snd s t, ?_, Category.assoc _ _ _⟩
        rw [Category.assoc, ← hc, ← Category.assoc, ← Category.assoc, ← hu, Category.assoc,
          Category.assoc, hsa, hta]
      rcases exists_eq_of_isPushout_of_isOpenImmersion hR (pullback.snd s t x) with hG | hG
      · -- The second factor lies in the chart `V`: the composite is the first factor.
        let U := pullback.snd s t ⁻¹ᵁ a.opensRange
        obtain ⟨u, hu⟩ := exists_comp_eq_ι_comp a (pullback.snd s t) U le_rfl
        refine ⟨U, hG, U.ι ≫ pullback.fst s t, Category.assoc _ _ _, ?_⟩
        rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc, ← hu, Category.assoc,
          Category.assoc, hta, hsa]
      -- Both factors lie in the chart `P`: use the transitivity of `P`.
      let U := pullback.fst s t ⁻¹ᵁ b.opensRange ⊓ pullback.snd s t ⁻¹ᵁ b.opensRange
      obtain ⟨v₁, hv₁⟩ := exists_comp_eq_ι_comp b (pullback.fst s t) U inf_le_left
      obtain ⟨v₂, hv₂⟩ := exists_comp_eq_ι_comp b (pullback.snd s t) U inf_le_right
      have hv : v₁ ≫ s₀ = v₂ ≫ t₀ := by
        rw [← cancel_mono j, Category.assoc, Category.assoc, ← hsb, ← htb, ← Category.assoc,
          ← Category.assoc, hv₁, hv₂, Category.assoc, Category.assoc, hc]
      let l := PullbackCone.IsLimit.lift e.isLimit v₁ v₂ hv
      refine ⟨U, ⟨hF, hG⟩, l ≫ e.t ≫ b, ?_, ?_⟩
      · rw [Category.assoc, Category.assoc, htb, e.transitivity₁_assoc,
          PullbackCone.IsLimit.lift_fst_assoc, ← htb, ← Category.assoc, hv₁, Category.assoc]
      · rw [Category.assoc, Category.assoc, hsb, e.transitivity₂_assoc,
          PullbackCone.IsLimit.lift_snd_assoc, ← hsb, ← Category.assoc, hv₂, Category.assoc]
  exact EquivalenceRelation.isEquivalenceRelation
    { toJointlyMono₂ := hm
      r := a
      reflexivity₁ := hta
      reflexivity₂ := hsa
      s := σ
      symmetry₁ := hσt
      symmetry₂ := hσs
      c := PullbackCone.mk _ _ (pullback.condition (f := s) (g := t))
      isLimit := pullbackIsPullback s t
      t := τ
      transitivity₁ := hτt
      transitivity₂ := hτs }

/-- **The glued étale equivalence relation of the proof of Stacks 07SU**, with all its
conclusions: in the situation of `AlgebraicGeometry.isEquivalenceRelation_of_isPushout`, with
`s₀` and `t₀` étale, the maps `s` and `t` are étale and `(t, s)` is an equivalence relation on
`V`. -/
theorem etale_and_isEquivalenceRelation_of_isPushout [IsOpenImmersion j] [Etale s₀] [Etale t₀]
    [IsEquivalenceRelation t₀ s₀] (hδs : δ ≫ s₀ = 𝟙 W) (hδt : δ ≫ t₀ = 𝟙 W)
    (hR : IsPushout j δ a b) {s t : R ⟶ V} (hsa : a ≫ s = 𝟙 V) (hsb : b ≫ s = s₀ ≫ j)
    (hta : a ≫ t = 𝟙 V) (htb : b ≫ t = t₀ ≫ j) :
    Etale s ∧ Etale t ∧ IsEquivalenceRelation t s := by
  have : IsOpenImmersion δ := isOpenImmersion_of_section_of_etale s₀ δ hδs
  exact ⟨etale_of_isPushout hR hsa hsb, etale_of_isPushout hR hta htb,
    isEquivalenceRelation_of_isPushout hδs hδt hR hsa hsb hta htb⟩

end GluedRelation

section Construction

variable {V W P : Scheme.{u}} (j : W ⟶ V) [IsOpenImmersion j] (δ : W ⟶ P) [IsOpenImmersion δ]

/-- For open immersions `j : W ⟶ V` and `δ : W ⟶ P` and a retraction `q` of `δ`, the morphism
from the glueing `pushout j δ` of `V` and `P` along `W` to `V` which is the identity on `V` and
`q ≫ j` on `P`. For `q` the source and the target of an étale equivalence relation on `W` with
diagonal `δ` these are the source and the target of the glued relation of the proof of
Stacks 07SU. -/
noncomputable def gluedRelationMap (q : P ⟶ W) (hq : δ ≫ q = 𝟙 W) : pushout j δ ⟶ V :=
  pushout.desc (𝟙 V) (q ≫ j) (by rw [Category.comp_id, ← Category.assoc, hq, Category.id_comp])

/-- The map `AlgebraicGeometry.gluedRelationMap` is the identity on the chart `V`. -/
@[reassoc (attr := simp)]
lemma inl_gluedRelationMap (q : P ⟶ W) (hq : δ ≫ q = 𝟙 W) :
    pushout.inl j δ ≫ gluedRelationMap j δ q hq = 𝟙 V :=
  pushout.inl_desc _ _ _

/-- The map `AlgebraicGeometry.gluedRelationMap` is `q ≫ j` on the chart `P`. -/
@[reassoc (attr := simp)]
lemma inr_gluedRelationMap (q : P ⟶ W) (hq : δ ≫ q = 𝟙 W) :
    pushout.inr j δ ≫ gluedRelationMap j δ q hq = q ≫ j :=
  pushout.inr_desc _ _ _

/-- The map `AlgebraicGeometry.gluedRelationMap` is étale when the retraction `q` is. -/
instance etale_gluedRelationMap (q : P ⟶ W) (hq : δ ≫ q = 𝟙 W) [Etale q] :
    Etale (gluedRelationMap j δ q hq) :=
  etale_of_isPushout (IsPushout.of_hasPushout j δ) (inl_gluedRelationMap j δ q hq)
    (inr_gluedRelationMap j δ q hq)

/-- The map `AlgebraicGeometry.gluedRelationMap` is quasi-compact when `j` and `q` are. -/
instance quasiCompact_gluedRelationMap (q : P ⟶ W) (hq : δ ≫ q = 𝟙 W) [QuasiCompact j]
    [QuasiCompact q] : QuasiCompact (gluedRelationMap j δ q hq) :=
  quasiCompact_of_isPushout (IsPushout.of_hasPushout j δ) (inl_gluedRelationMap j δ q hq)
    (inr_gluedRelationMap j δ q hq)

/-- **The glued étale equivalence relation of the proof of Stacks 07SU**, for the chosen glueing
`pushout j δ`: if `(t₀, s₀)` is an étale equivalence relation on `W` with diagonal `δ`, then the
glued maps `gluedRelationMap j δ t₀ _` and `gluedRelationMap j δ s₀ _` form an étale
equivalence relation on `V`. -/
theorem isEquivalenceRelation_gluedRelationMap {s₀ t₀ : P ⟶ W} [Etale s₀]
    [IsEquivalenceRelation t₀ s₀] (hδs : δ ≫ s₀ = 𝟙 W) (hδt : δ ≫ t₀ = 𝟙 W) :
    IsEquivalenceRelation (gluedRelationMap j δ t₀ hδt) (gluedRelationMap j δ s₀ hδs) :=
  isEquivalenceRelation_of_isPushout hδs hδt (IsPushout.of_hasPushout j δ)
    (inl_gluedRelationMap ..) (inr_gluedRelationMap ..) (inl_gluedRelationMap ..)
    (inr_gluedRelationMap ..)

/-- The glueing of two quasi-compact schemes along a common open is quasi-compact. -/
instance compactSpace_pushout_of_isOpenImmersion [CompactSpace V] [CompactSpace P] :
    CompactSpace ↥(pushout j δ) :=
  compactSpace_of_isPushout (IsPushout.of_hasPushout j δ)

/-- The glueing of two schemes locally of finite type (over the terminal scheme `Spec ℤ`) along
a common open is locally of finite type. -/
instance locallyOfFiniteType_terminal_from_pushout [LocallyOfFiniteType (terminal.from V)]
    [LocallyOfFiniteType (terminal.from P)] :
    LocallyOfFiniteType (terminal.from (pushout j δ)) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
      (Q := RingHom.FiniteType)
  exact IsZariskiLocalAtSource.of_isPushout (IsPushout.of_hasPushout j δ)
    (by rw [terminal.comp_from]; infer_instance) (by rw [terminal.comp_from]; infer_instance)

end Construction

end AlgebraicGeometry

end
