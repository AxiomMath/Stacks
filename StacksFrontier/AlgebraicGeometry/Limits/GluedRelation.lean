module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleRelationTransition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relation obtained by glueing the diagonal of a scheme to a relation on an open subscheme

Let `V` be a scheme, `ι : W ⟶ V` an open subscheme, and `p₁, p₂ : Q ⟶ W` an equivalence relation
on `W` (jointly monic, symmetric and transitive on points) with a diagonal `δ : W ⟶ Q` which is an
open immersion. Glueing `V` to `Q` along `W` gives a scheme `R = V ⊔_W Q` with two maps
`R ⟶ V`, the identity on `V` and `pᵢ` followed by `ι` on `Q`. This file shows that these two maps
form an equivalence relation on `V`, read on `T`-valued points, which is étale when `p₁` and `p₂`
are.

## Main definitions

* `AlgebraicGeometry.GluedRelation.fst` and `AlgebraicGeometry.GluedRelation.snd`: the two maps.

## Main results

* `AlgebraicGeometry.GluedRelation.hom_ext`: the two maps are jointly monic.
* `AlgebraicGeometry.GluedRelation.exists_symm` and
  `AlgebraicGeometry.GluedRelation.exists_trans`: symmetry and transitivity on points.
* `AlgebraicGeometry.GluedRelation.etale_fst` and `AlgebraicGeometry.GluedRelation.etale_snd`:
  the two maps are étale when `p₁` and `p₂` are.
* `AlgebraicGeometry.GluedRelation.isEquivalenceRelation`: the two maps form an internal
  equivalence relation of schemes.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- **A jointly monic pair which is an equivalence relation on points is an internal equivalence
relation**, in a category with pullbacks: reflexivity, symmetry and transitivity are read off the
relation on points at the identity of `X`, of `R` and of the pullback `R ×_X R`. -/
@[sga "4 IV 9.8.2" "9.8.2 b)"]
theorem isEquivalenceRelation_of_equivalence {C : Type*} [Category* C] [HasPullbacks C]
    {R X : C} (p₁ p₂ : R ⟶ X)
    (hmono : ∀ {T : C} (a b : T ⟶ R), a ≫ p₁ = b ≫ p₁ → a ≫ p₂ = b ≫ p₂ → a = b)
    (heq : ∀ T : C, _root_.Equivalence (fun x y : T ⟶ X => ∃ r : T ⟶ R, r ≫ p₁ = x ∧ r ≫ p₂ = y)) :
    IsEquivalenceRelation p₁ p₂ := by
  obtain ⟨r, hr₁, hr₂⟩ := (heq X).refl (𝟙 X)
  obtain ⟨σ, hσ₁, hσ₂⟩ := (heq R).symm ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
  obtain ⟨τ, hτ₁, hτ₂⟩ := (heq (pullback p₂ p₁)).trans
    ⟨pullback.fst p₂ p₁, rfl, pullback.condition⟩ ⟨pullback.snd p₂ p₁, rfl, rfl⟩
  exact EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := fun _ a b h₁ h₂ => hmono a b h₁ h₂
      r := r
      reflexivity₁ := hr₁
      reflexivity₂ := hr₂
      s := σ
      symmetry₁ := hσ₁
      symmetry₂ := hσ₂
      c := pullback.cone p₂ p₁
      isLimit := pullback.isLimit p₂ p₁
      t := τ
      transitivity₁ := hτ₁
      transitivity₂ := hτ₂ }

end CategoryTheory

namespace AlgebraicGeometry.GluedRelation

variable {V W Q : Scheme.{u}} (ι : W ⟶ V) [IsOpenImmersion ι] (δ : W ⟶ Q) [IsOpenImmersion δ]
  (p₁ p₂ : Q ⟶ W) (h₁ : δ ≫ p₁ = 𝟙 W) (h₂ : δ ≫ p₂ = 𝟙 W)

/-- The first map of the glued relation: the identity on `V` and `p₁` followed by `ι` on `Q`. -/
noncomputable def fst : pushout ι δ ⟶ V :=
  pushout.desc (𝟙 V) (p₁ ≫ ι) (by rw [Category.comp_id, reassoc_of% h₁])

/-- The second map of the glued relation: the identity on `V` and `p₂` followed by `ι` on `Q`. -/
noncomputable def snd : pushout ι δ ⟶ V :=
  pushout.desc (𝟙 V) (p₂ ≫ ι) (by rw [Category.comp_id, reassoc_of% h₂])

/-- The first map of the glued relation restricts to the identity on `V`. -/
@[reassoc (attr := simp)]
theorem inl_fst : pushout.inl ι δ ≫ fst ι δ p₁ h₁ = 𝟙 V := pushout.inl_desc _ _ _

/-- The first map of the glued relation restricts to `p₁ ≫ ι` on `Q`. -/
@[reassoc (attr := simp)]
theorem inr_fst : pushout.inr ι δ ≫ fst ι δ p₁ h₁ = p₁ ≫ ι := pushout.inr_desc _ _ _

/-- The second map of the glued relation restricts to the identity on `V`. -/
@[reassoc (attr := simp)]
theorem inl_snd : pushout.inl ι δ ≫ snd ι δ p₂ h₂ = 𝟙 V := pushout.inl_desc _ _ _

/-- The second map of the glued relation restricts to `p₂ ≫ ι` on `Q`. -/
@[reassoc (attr := simp)]
theorem inr_snd : pushout.inr ι δ ≫ snd ι δ p₂ h₂ = p₂ ≫ ι := pushout.inr_desc _ _ _

/-- The inclusion of `V` into the glued scheme is an open immersion. -/
instance : IsOpenImmersion (pushout.inl ι δ) :=
  isOpenImmersion_inl_of_isPushout (IsPushout.of_hasPushout ι δ)

/-- The inclusion of `Q` into the glued scheme is an open immersion. -/
instance : IsOpenImmersion (pushout.inr ι δ) :=
  isOpenImmersion_inr_of_isPushout (IsPushout.of_hasPushout ι δ)

/-- Every point of the glued scheme lies on one of the two charts. -/
theorem mem_range_inl_or_inr (z : (pushout ι δ : Scheme.{u})) :
    z ∈ Set.range (pushout.inl ι δ) ∨ z ∈ Set.range (pushout.inr ι δ) :=
  exists_eq_of_isPushout_of_isOpenImmersion (IsPushout.of_hasPushout ι δ) z

/-- A point on both charts comes from the overlap `W`. -/
theorem exists_of_inl_eq_inr {v : V} {q : Q} (h : pushout.inl ι δ v = pushout.inr ι δ q) :
    ∃ w : W, ι w = v ∧ δ w = q := by
  have hpb := isPullback_of_isPushout_of_isOpenImmersion (IsPushout.of_hasPushout ι δ)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback v q h
  refine ⟨hpb.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_snd, hz₂]

/-- A morphism into the glued scheme which lands on the first chart has equal composites with
the two maps of the relation. -/
theorem fst_eq_snd_of_range_subset {T : Scheme.{u}} (r : T ⟶ pushout ι δ)
    (hr : Set.range r ⊆ Set.range (pushout.inl ι δ)) :
    r ≫ fst ι δ p₁ h₁ = r ≫ snd ι δ p₂ h₂ := by
  rw [← IsOpenImmersion.lift_fac (pushout.inl ι δ) r hr, Category.assoc, Category.assoc,
    inl_fst, inl_snd]

/-- A morphism whose points over an open `U` all land in the range of an open immersion `c`
factors over `U` through `c`. -/
private theorem exists_comp_eq_of_forall_mem {X Y Z : Scheme.{u}} (c : X ⟶ Z) [IsOpenImmersion c]
    (r : Y ⟶ Z) (U : Y.Opens) (hU : ∀ y ∈ U, r y ∈ c.opensRange) :
    ∃ a : U.toScheme ⟶ X, U.ι ≫ r = a ≫ c :=
  ⟨IsOpenImmersion.lift c _ (by rintro _ ⟨y, rfl⟩; exact hU _ y.2),
    (IsOpenImmersion.lift_fac _ _ _).symm⟩

variable {p₁ p₂ h₁ h₂}

/-- **The two maps of the glued relation are jointly monic**, provided `p₁` and `p₂` are. -/
theorem hom_ext
    (hQ : ∀ {T : Scheme.{u}} (σ τ : T ⟶ Q), σ ≫ p₁ = τ ≫ p₁ → σ ≫ p₂ = τ ≫ p₂ → σ = τ)
    {T : Scheme.{u}} (r₁ r₂ : T ⟶ pushout ι δ)
    (e₁ : r₁ ≫ fst ι δ p₁ h₁ = r₂ ≫ fst ι δ p₁ h₁)
    (e₂ : r₁ ≫ snd ι δ p₂ h₂ = r₂ ≫ snd ι δ p₂ h₂) : r₁ = r₂ := by
  classical
  let A := (pushout.inl ι δ).opensRange
  let Bq := (pushout.inr ι δ).opensRange
  have glue : ∀ {C : Scheme.{u}} (c : C ⟶ pushout ι δ) [IsOpenImmersion c],
      (∀ {U : T.Opens} (a b : U.toScheme ⟶ C), U.ι ≫ r₁ = a ≫ c → U.ι ≫ r₂ = b ≫ c → a = b) →
      ∀ x, r₁ x ∈ c.opensRange → r₂ x ∈ c.opensRange →
        ∃ U : T.Opens, x ∈ U ∧ U.ι ≫ r₁ = U.ι ≫ r₂ := by
    intro C c _ H x hx₁ hx₂
    let U := r₁ ⁻¹ᵁ c.opensRange ⊓ r₂ ⁻¹ᵁ c.opensRange
    obtain ⟨a, ha⟩ := exists_comp_eq_of_forall_mem c r₁ U fun y hy => hy.1
    obtain ⟨b, hb⟩ := exists_comp_eq_of_forall_mem c r₂ U fun y hy => hy.2
    exact ⟨U, ⟨hx₁, hx₂⟩, by rw [ha, hb, H a b ha hb]⟩
  have caseA := glue (pushout.inl ι δ) fun {U} a b ha hb => by
    have k : (U.ι ≫ r₁) ≫ fst ι δ p₁ h₁ = (U.ι ≫ r₂) ≫ fst ι δ p₁ h₁ := by
      rw [Category.assoc, Category.assoc, e₁]
    simpa only [ha, hb, Category.assoc, inl_fst, Category.comp_id] using k
  have caseB := glue (pushout.inr ι δ) fun {U} a b ha hb => by
    have k : (U.ι ≫ r₁) ≫ fst ι δ p₁ h₁ = (U.ι ≫ r₂) ≫ fst ι δ p₁ h₁ := by
      rw [Category.assoc, Category.assoc, e₁]
    have l : (U.ι ≫ r₁) ≫ snd ι δ p₂ h₂ = (U.ι ≫ r₂) ≫ snd ι δ p₂ h₂ := by
      rw [Category.assoc, Category.assoc, e₂]
    simp only [ha, hb, Category.assoc, inr_fst, inr_snd] at k l
    exact hQ _ _ ((cancel_mono ι).1 (by simpa using k)) ((cancel_mono ι).1 (by simpa using l))
  have mixed : ∀ (s₁ s₂ : T ⟶ pushout ι δ), s₁ ≫ fst ι δ p₁ h₁ = s₂ ≫ fst ι δ p₁ h₁ →
      ∀ x, s₁ x ∈ A → s₂ x ∈ Bq → s₁ x ∈ Bq := by
    intro s₁ s₂ e x ⟨v, hv⟩ ⟨q, hq⟩
    have h : (s₁ ≫ fst ι δ p₁ h₁) x = (s₂ ≫ fst ι δ p₁ h₁) x := by rw [e]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hv, ← hq, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, inl_fst, inr_fst] at h
    change v = ι (p₁ q) at h
    refine ⟨δ (p₁ q), ?_⟩
    rw [← hv, h, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pushout.condition]
    rfl
  refine Scheme.hom_ext_of_forall r₁ r₂ fun x => ?_
  by_cases hA₁ : r₁ x ∈ A <;> by_cases hA₂ : r₂ x ∈ A
  · exact caseA x hA₁ hA₂
  · have hB₂ : r₂ x ∈ Bq := (mem_range_inl_or_inr ι δ (r₂ x)).resolve_left hA₂
    exact caseB x (mixed r₁ r₂ e₁ x hA₁ hB₂) hB₂
  · have hB₁ : r₁ x ∈ Bq := (mem_range_inl_or_inr ι δ (r₁ x)).resolve_left hA₁
    exact caseB x hB₁ (mixed r₂ r₁ e₁.symm x hA₂ hB₁)
  · exact caseB x ((mem_range_inl_or_inr ι δ (r₁ x)).resolve_left hA₁)
      ((mem_range_inl_or_inr ι δ (r₂ x)).resolve_left hA₂)

/-- **Points of the glued relation exist as soon as they exist locally.** The two maps being
jointly monic, local witnesses agree on overlaps and glue. -/
theorem exists_of_forall_exists
    (hQ : ∀ {T : Scheme.{u}} (σ τ : T ⟶ Q), σ ≫ p₁ = τ ≫ p₁ → σ ≫ p₂ = τ ≫ p₂ → σ = τ)
    {T : Scheme.{u}} (x y : T ⟶ V)
    (H : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ r : U.toScheme ⟶ pushout ι δ,
      r ≫ fst ι δ p₁ h₁ = U.ι ≫ x ∧ r ≫ snd ι δ p₂ h₂ = U.ι ≫ y) :
    ∃ r : T ⟶ pushout ι δ, r ≫ fst ι δ p₁ h₁ = x ∧ r ≫ snd ι δ p₂ h₂ = y := by
  choose U hU r hr₁ hr₂ using H
  let 𝒰 : T.OpenCover := {
    I₀ := T, X i := U i, f i := (U i).ι,
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun t ↦ ⟨t, by simpa using hU t⟩, inferInstance⟩ }
  have hcompat : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ r a = pullback.snd _ _ ≫ r b := by
    intro a b
    apply hom_ext ι δ hQ
    · rw [Category.assoc, Category.assoc, hr₁, hr₁, ← Category.assoc, ← Category.assoc,
        pullback.condition]
    · rw [Category.assoc, Category.assoc, hr₂, hr₂, ← Category.assoc, ← Category.assoc,
        pullback.condition]
  refine ⟨𝒰.glueMorphisms r hcompat, ?_, ?_⟩ <;> refine 𝒰.hom_ext _ _ fun a => ?_ <;>
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms] <;> first | exact hr₁ _ | exact hr₂ _

/-- A morphism into the glued scheme factors, near any point, through one of the two charts. -/
theorem exists_open_factor {T : Scheme.{u}} (r : T ⟶ pushout ι δ) (t : T) :
    ∃ U : T.Opens, t ∈ U ∧
      ((∃ v : U.toScheme ⟶ V, U.ι ≫ r = v ≫ pushout.inl ι δ) ∨
        (∃ q : U.toScheme ⟶ Q, U.ι ≫ r = q ≫ pushout.inr ι δ)) := by
  rcases mem_range_inl_or_inr ι δ (r t) with h | h
  · exact ⟨_, h, Or.inl
      (exists_comp_eq_of_forall_mem (pushout.inl ι δ) r
        (r ⁻¹ᵁ (pushout.inl ι δ).opensRange) fun y hy => hy)⟩
  · exact ⟨_, h, Or.inr
      (exists_comp_eq_of_forall_mem (pushout.inr ι δ) r
        (r ⁻¹ᵁ (pushout.inr ι δ).opensRange) fun y hy => hy)⟩

/-- **The glued relation is an equivalence relation on points**, provided `p₁, p₂` is one and is
jointly monic. -/
theorem equivalence
    (hQ : ∀ {T : Scheme.{u}} (σ τ : T ⟶ Q), σ ≫ p₁ = τ ≫ p₁ → σ ≫ p₂ = τ ≫ p₂ → σ = τ)
    (hQe : ∀ T : Scheme.{u},
      Equivalence (fun x y : T ⟶ W => ∃ q : T ⟶ Q, q ≫ p₁ = x ∧ q ≫ p₂ = y))
    (T : Scheme.{u}) :
    Equivalence (fun x y : T ⟶ V => ∃ r : T ⟶ pushout ι δ,
      r ≫ fst ι δ p₁ h₁ = x ∧ r ≫ snd ι δ p₂ h₂ = y) := by
  have cl₁ : ∀ {U : Scheme.{u}} (v : U ⟶ V), (v ≫ pushout.inl ι δ) ≫ fst ι δ p₁ h₁ = v := by
    intro U v; rw [Category.assoc, inl_fst, Category.comp_id]
  have cl₂ : ∀ {U : Scheme.{u}} (v : U ⟶ V), (v ≫ pushout.inl ι δ) ≫ snd ι δ p₂ h₂ = v := by
    intro U v; rw [Category.assoc, inl_snd, Category.comp_id]
  have cr₁ : ∀ {U : Scheme.{u}} (q : U ⟶ Q),
      (q ≫ pushout.inr ι δ) ≫ fst ι δ p₁ h₁ = q ≫ p₁ ≫ ι := by
    intro U q; rw [Category.assoc, inr_fst]
  have cr₂ : ∀ {U : Scheme.{u}} (q : U ⟶ Q),
      (q ≫ pushout.inr ι δ) ≫ snd ι δ p₂ h₂ = q ≫ p₂ ≫ ι := by
    intro U q; rw [Category.assoc, inr_snd]
  have res : ∀ {U : Scheme.{u}} (i : U ⟶ T) {r : T ⟶ pushout ι δ} {x : T ⟶ V}
      {m : pushout ι δ ⟶ V} (_ : r ≫ m = x), (i ≫ r) ≫ m = i ≫ x := by
    intro U i r x m h; rw [Category.assoc, h]
  constructor
  · intro x
    exact ⟨x ≫ pushout.inl ι δ, cl₁ x, cl₂ x⟩
  · rintro x y ⟨r, hr₁, hr₂⟩
    refine exists_of_forall_exists ι δ hQ y x fun t => ?_
    obtain ⟨U, htU, hU | hU⟩ := exists_open_factor ι δ r t
    · obtain ⟨v, hv⟩ := hU
      have ex : U.ι ≫ x = v := by rw [← res U.ι hr₁, hv, cl₁]
      have ey : U.ι ≫ y = v := by rw [← res U.ι hr₂, hv, cl₂]
      refine ⟨U, htU, v ≫ pushout.inl ι δ, ?_, ?_⟩
      · rw [cl₁, ey]
      · rw [cl₂, ex]
    · obtain ⟨q, hq⟩ := hU
      obtain ⟨q', hq'₁, hq'₂⟩ := (hQe _).symm ⟨q, rfl, rfl⟩
      have ex : U.ι ≫ x = q ≫ p₁ ≫ ι := by rw [← res U.ι hr₁, hq, cr₁]
      have ey : U.ι ≫ y = q ≫ p₂ ≫ ι := by rw [← res U.ι hr₂, hq, cr₂]
      refine ⟨U, htU, q' ≫ pushout.inr ι δ, ?_, ?_⟩
      · rw [cr₁, ey, ← Category.assoc, hq'₁, Category.assoc]
      · rw [cr₂, ex, ← Category.assoc, hq'₂, Category.assoc]
  · rintro x y z ⟨r₁, hr₁₁, hr₁₂⟩ ⟨r₂, hr₂₁, hr₂₂⟩
    refine exists_of_forall_exists ι δ hQ x z fun t => ?_
    obtain ⟨U₁, htU₁, hU₁⟩ := exists_open_factor ι δ r₁ t
    obtain ⟨U₂, htU₂, hU₂⟩ := exists_open_factor ι δ r₂ t
    let U := U₁ ⊓ U₂
    have hU1 : U ≤ U₁ := inf_le_left
    have hU2 : U ≤ U₂ := inf_le_right
    let i₁ := T.homOfLE hU1
    let i₂ := T.homOfLE hU2
    have hι₁ : U.ι = i₁ ≫ U₁.ι := (Scheme.homOfLE_ι _ _).symm
    have hι₂ : U.ι = i₂ ≫ U₂.ι := (Scheme.homOfLE_ι _ _).symm
    refine ⟨U, ⟨htU₁, htU₂⟩, ?_⟩
    rcases hU₁ with ⟨v, hv⟩ | ⟨q₁, hq₁⟩
    · have hv' : U.ι ≫ r₁ = (i₁ ≫ v) ≫ pushout.inl ι δ := by
        rw [hι₁, Category.assoc, hv, Category.assoc]
      have ex : U.ι ≫ x = i₁ ≫ v := by rw [← res U.ι hr₁₁, hv', cl₁]
      have ey : U.ι ≫ y = i₁ ≫ v := by rw [← res U.ι hr₁₂, hv', cl₂]
      refine ⟨U.ι ≫ r₂, ?_, res U.ι hr₂₂⟩
      rw [res U.ι hr₂₁, ey, ex]
    rcases hU₂ with ⟨v, hv⟩ | ⟨q₂, hq₂⟩
    · have hv' : U.ι ≫ r₂ = (i₂ ≫ v) ≫ pushout.inl ι δ := by
        rw [hι₂, Category.assoc, hv, Category.assoc]
      have ey : U.ι ≫ y = i₂ ≫ v := by rw [← res U.ι hr₂₁, hv', cl₁]
      have ez : U.ι ≫ z = i₂ ≫ v := by rw [← res U.ι hr₂₂, hv', cl₂]
      refine ⟨U.ι ≫ r₁, res U.ι hr₁₁, ?_⟩
      rw [res U.ι hr₁₂, ey, ez]
    · let a := i₁ ≫ q₁
      let b := i₂ ≫ q₂
      have ha : U.ι ≫ r₁ = a ≫ pushout.inr ι δ := by
        rw [hι₁, Category.assoc, hq₁, Category.assoc]
      have hb : U.ι ≫ r₂ = b ≫ pushout.inr ι δ := by
        rw [hι₂, Category.assoc, hq₂, Category.assoc]
      have ex : U.ι ≫ x = a ≫ p₁ ≫ ι := by rw [← res U.ι hr₁₁, ha, cr₁]
      have ey₁ : U.ι ≫ y = a ≫ p₂ ≫ ι := by rw [← res U.ι hr₁₂, ha, cr₂]
      have ey₂ : U.ι ≫ y = b ≫ p₁ ≫ ι := by rw [← res U.ι hr₂₁, hb, cr₁]
      have ez : U.ι ≫ z = b ≫ p₂ ≫ ι := by rw [← res U.ι hr₂₂, hb, cr₂]
      have hab : a ≫ p₂ = b ≫ p₁ := by
        rw [← cancel_mono ι]
        simpa only [Category.assoc] using ey₁.symm.trans ey₂
      obtain ⟨c, hc₁, hc₂⟩ := (hQe _).trans ⟨a, rfl, hab⟩ ⟨b, rfl, rfl⟩
      refine ⟨c ≫ pushout.inr ι δ, ?_, ?_⟩
      · rw [cr₁, ex, ← Category.assoc, hc₁, Category.assoc]
      · rw [cr₂, ez, ← Category.assoc, hc₂, Category.assoc]

/-- The two charts cover the glued scheme. -/
theorem iSup_opensRange : (pushout.inl ι δ).opensRange ⊔ (pushout.inr ι δ).opensRange = ⊤ :=
  top_unique fun z _ => mem_range_inl_or_inr ι δ z

/-- A property local at the source holds for a morphism out of the glued scheme as soon as it
holds on the two charts. -/
theorem of_inl_inr (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] {Y : Scheme.{u}}
    (f : pushout ι δ ⟶ Y) (hl : P (pushout.inl ι δ ≫ f)) (hr : P (pushout.inr ι δ ≫ f)) :
    P f := by
  have key : ∀ {X : Scheme.{u}} (j : X ⟶ pushout ι δ) [IsOpenImmersion j], P (j ≫ f) →
      P (j.opensRange.ι ≫ f) := fun j _ h => by
    rwa [← j.isoOpensRange_hom_ι, Category.assoc, P.cancel_left_of_respectsIso] at h
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := P)
    (fun b : Bool => if b then (pushout.inl ι δ).opensRange else (pushout.inr ι δ).opensRange)
    ?_ fun b => ?_
  · rw [iSup_bool_eq]
    exact iSup_opensRange ι δ
  · cases b
    · exact key _ hr
    · exact key _ hl

/-- The first map of the glued relation is étale when `p₁` is. -/
theorem etale_fst [Etale p₁] : Etale (fst ι δ p₁ h₁) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  of_inl_inr ι δ @Etale _ (by rw [inl_fst]; infer_instance) (by rw [inr_fst]; infer_instance)

/-- The second map of the glued relation is étale when `p₂` is. -/
theorem etale_snd [Etale p₂] : Etale (snd ι δ p₂ h₂) :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  of_inl_inr ι δ @Etale _ (by rw [inl_snd]; infer_instance) (by rw [inr_snd]; infer_instance)

/-- **The glued relation is an internal equivalence relation of schemes**, with the second map as
the target and the first as the source (the convention of the relation of a pair `s, t`). -/
theorem isEquivalenceRelation
    (hQ : ∀ {T : Scheme.{u}} (σ τ : T ⟶ Q), σ ≫ p₁ = τ ≫ p₁ → σ ≫ p₂ = τ ≫ p₂ → σ = τ)
    (hQe : ∀ T : Scheme.{u},
      Equivalence (fun x y : T ⟶ W => ∃ q : T ⟶ Q, q ≫ p₁ = x ∧ q ≫ p₂ = y)) :
    IsEquivalenceRelation (snd ι δ p₂ h₂) (fst ι δ p₁ h₁) := by
  refine CategoryTheory.isEquivalenceRelation_of_equivalence _ _
    (fun a b e₂ e₁ => hom_ext ι δ hQ a b e₁ e₂) fun T => ?_
  have h := equivalence ι δ (h₁ := h₁) (h₂ := h₂) hQ hQe T
  constructor
  · intro x
    obtain ⟨r, h₁, h₂⟩ := h.refl x
    exact ⟨r, h₂, h₁⟩
  · rintro x y ⟨r, h₁, h₂⟩
    obtain ⟨r', h₁', h₂'⟩ := h.symm ⟨r, h₂, h₁⟩
    exact ⟨r', h₂', h₁'⟩
  · rintro x y z ⟨r, h₁, h₂⟩ ⟨r', h₁', h₂'⟩
    obtain ⟨r'', h₁'', h₂''⟩ := h.trans ⟨r', h₂', h₁'⟩ ⟨r, h₂, h₁⟩
    exact ⟨r'', h₂'', h₁''⟩

end AlgebraicGeometry.GluedRelation

end
