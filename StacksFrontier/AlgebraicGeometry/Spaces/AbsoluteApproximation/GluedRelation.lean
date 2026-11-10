module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Stage

/-!
# The relation glued from the diagonal and an étale equivalence relation on an open

In the problem step of the proof of Stacks 07SU one is given, at every stage `i`, a scheme
`V_i`, an open subscheme `W_i ⊆ V_i` and the étale equivalence relation
`W_i ×_{U_i} W_i ⇉ W_i`, and one forms the scheme `R_i` by glueing `V_i` and
`W_i ×_{U_i} W_i` along `W_i`, the second inclusion being the diagonal. The two projections of
`W_i ×_{U_i} W_i` extend to étale morphisms `s_i, t_i : R_i ⟶ V_i`, and the proof asserts that
`(t_i, s_i)` is an étale equivalence relation on `V_i` and that the source squares of the system
`(R_i)` are cartesian. This file proves both, for an arbitrary scheme `V`, open immersion
`ι : W ⟶ V` and internal equivalence relation `p₁, p₂ : P ⟶ W` with étale projections.

## Main definitions

* `AlgebraicGeometry.gluedRelationProj`: the morphism `V ∪_W P ⟶ V` which is the identity on
  `V` and `p ≫ ι` on `P`, for a projection `p : P ⟶ W` split by the glueing map `d : W ⟶ P`.
* `AlgebraicGeometry.gluedRelationProjNatTrans`: the same morphism, stage by stage, as a natural
  transformation out of `AlgebraicGeometry.gluePairFunctor`.

## Main results

* `CategoryTheory.isEquivalenceRelation_of_forall`: a jointly monic pair is an internal
  equivalence relation when the induced relation on generalized points is reflexive, symmetric
  and transitive.
* `AlgebraicGeometry.Scheme.exists_lift_of_forall`: lifting a pair of morphisms through a
  jointly monic pair is local on the source.
* `AlgebraicGeometry.preimage_opensRange_gluedRelationProj`: the second piece `P` of the glueing
  is the inverse image of `W` under either projection.
* `AlgebraicGeometry.etale_gluedRelationProj`: the projections are étale.
* `AlgebraicGeometry.isEquivalenceRelation_gluedRelationProj`: the two projections form an
  internal equivalence relation on `V`.
* `AlgebraicGeometry.isPullback_gluedRelationProjNatTrans`: for a system of such data whose
  squares on `ι` and on `p₂` are cartesian, the squares of the glued relations on the second
  projection are cartesian.

## Implementation notes

The equivalence relation is checked on generalized points `T ⟶ V`. A point of the glued scheme
lies in `P` exactly when its image under either projection lies in `W`
(`AlgebraicGeometry.preimage_opensRange_gluedRelationProj`), so a point `r : T ⟶ V ∪_W P` is,
over the open of `T` where the common value `r ≫ s = r' ≫ t` lands in `W`, a point of `P`, and
over the open where `r` lands in `V`, a point of the diagonal. Symmetry and transitivity are
therefore read off from those of `P` and of equality on two opens covering `T`, and the local
solutions are glued by `AlgebraicGeometry.Scheme.exists_lift_of_forall`, which only needs joint
monicity of the two projections. The cartesian squares are checked on the open cover of the glued
scheme by its two pieces, through Mathlib's `AlgebraicGeometry.Scheme.isPullback_of_openCover`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace CategoryTheory

variable {C : Type*} [Category* C]

/-- **An internal equivalence relation recognised on generalized points.** A jointly monic pair
`p₁, p₂ : R ⟶ X` is an internal equivalence relation as soon as the relation it induces on the
`T`-valued points of `X` is reflexive, symmetric and transitive, for every `T`. -/
theorem isEquivalenceRelation_of_forall {R X : C} (p₁ p₂ : R ⟶ X) [HasPullback p₂ p₁]
    (hmono : JointlyMono₂ p₁ p₂) (hrefl : ∃ r : X ⟶ R, r ≫ p₁ = 𝟙 X ∧ r ≫ p₂ = 𝟙 X)
    (hsymm : ∀ {T : C} (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ p₁ = r ≫ p₂ ∧ r' ≫ p₂ = r ≫ p₁)
    (htrans : ∀ {T : C} (r r' : T ⟶ R), r ≫ p₂ = r' ≫ p₁ →
      ∃ r'' : T ⟶ R, r'' ≫ p₁ = r ≫ p₁ ∧ r'' ≫ p₂ = r' ≫ p₂) :
    IsEquivalenceRelation p₁ p₂ := by
  obtain ⟨r, hr₁, hr₂⟩ := hrefl
  obtain ⟨s, hs₁, hs₂⟩ := hsymm (𝟙 R)
  obtain ⟨t, ht₁, ht₂⟩ := htrans (pullback.fst p₂ p₁) (pullback.snd p₂ p₁) pullback.condition
  exact EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := hmono.right_cancellation
      r := r
      reflexivity₁ := hr₁
      reflexivity₂ := hr₂
      s := s
      symmetry₁ := by simpa using hs₁
      symmetry₂ := by simpa using hs₂
      c := pullback.cone p₂ p₁
      isLimit := pullback.isLimit p₂ p₁
      t := t
      transitivity₁ := by simpa using ht₁
      transitivity₂ := by simpa using ht₂ }

namespace IsEquivalenceRelation

variable {R X : C} {p₁ p₂ : R ⟶ X} [h : IsEquivalenceRelation p₁ p₂]

include h in
/-- The two maps of an internal equivalence relation are jointly monic. -/
theorem jointlyMono₂ : JointlyMono₂ p₁ p₂ :=
  ⟨h.nonempty_equivalenceRelation.some.right_cancellation⟩

include h in
/-- Symmetry of an internal equivalence relation on generalized points. -/
theorem exists_symm {T : C} (r : T ⟶ R) :
    ∃ r' : T ⟶ R, r' ≫ p₁ = r ≫ p₂ ∧ r' ≫ p₂ = r ≫ p₁ := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  exact ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁], by rw [Category.assoc, e.symmetry₂]⟩

include h in
/-- Transitivity of an internal equivalence relation on generalized points. -/
theorem exists_trans {T : C} (r r' : T ⟶ R) (hrr' : r ≫ p₂ = r' ≫ p₁) :
    ∃ r'' : T ⟶ R, r'' ≫ p₁ = r ≫ p₁ ∧ r'' ≫ p₂ = r' ≫ p₂ := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  refine ⟨PullbackCone.IsLimit.lift e.isLimit r r' hrr' ≫ e.t, ?_, ?_⟩
  · rw [Category.assoc, e.transitivity₁, ← Category.assoc, PullbackCone.IsLimit.lift_fst]
  · rw [Category.assoc, e.transitivity₂, ← Category.assoc, PullbackCone.IsLimit.lift_snd]

end IsEquivalenceRelation

end CategoryTheory

namespace AlgebraicGeometry

/-- **Lifting through a jointly monic pair is local on the source.** If `a, b : R ⟶ V` are
jointly monic and every point of `T` has an open neighbourhood over which `(x, y)` lifts through
`(a, b)`, then `(x, y)` lifts through `(a, b)` on all of `T`: the local lifts agree on overlaps
by joint monicity and glue. -/
theorem Scheme.exists_lift_of_forall {T R V : Scheme.{u}} (a b : R ⟶ V) [JointlyMono₂ a b]
    (x y : T ⟶ V)
    (H : ∀ τ : T, ∃ U : T.Opens, τ ∈ U ∧
      ∃ r : (U : Scheme.{u}) ⟶ R, r ≫ a = U.ι ≫ x ∧ r ≫ b = U.ι ≫ y) :
    ∃ r : T ⟶ R, r ≫ a = x ∧ r ≫ b = y := by
  choose U hxU r hra hrb using H
  let 𝒰 : T.OpenCover := {
    I₀ := T, X i := (U i), f i := (U i).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ r i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ r j := by
    intro i j
    apply JointlyMono₂.right_cancellation (p₁ := a) (p₂ := b)
    · simp only [Category.assoc, hra]
      exact pullback.condition_assoc (f := 𝒰.f i) (g := 𝒰.f j) x
    · simp only [Category.assoc, hrb]
      exact pullback.condition_assoc (f := 𝒰.f i) (g := 𝒰.f j) y
  refine ⟨𝒰.glueMorphisms r hcompat, 𝒰.hom_ext _ _ fun τ ↦ ?_, 𝒰.hom_ext _ _ fun τ ↦ ?_⟩ <;>
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
  exacts [hra τ, hrb τ]

section Glued

variable {W V P : Scheme.{u}} (ι : W ⟶ V) [IsOpenImmersion ι] (d : W ⟶ P) [IsOpenImmersion d]

/-- **The projection of the glued relation.** For a morphism `p : P ⟶ W` split by the glueing
map `d : W ⟶ P`, the morphism from `V` glued to `P` along `W` to `V` which is the identity on `V`
and `p ≫ ι` on `P`. -/
noncomputable def gluedRelationProj (p : P ⟶ W) (hp : d ≫ p = 𝟙 W) :
    Scheme.gluePair ι d ⟶ V :=
  Scheme.gluePairDesc ι d (𝟙 V) (p ≫ ι) (by rw [reassoc_of% hp, Category.comp_id])

variable (p : P ⟶ W) (hp : d ≫ p = 𝟙 W)

/-- The projection of the glued relation is the identity on the piece `V`. -/
@[reassoc (attr := simp)]
lemma gluePairInl_gluedRelationProj :
    Scheme.gluePairInl ι d ≫ gluedRelationProj ι d p hp = 𝟙 V :=
  Scheme.gluePairInl_desc _ _ _ _ _

/-- The projection of the glued relation is `p ≫ ι` on the piece `P`. -/
@[reassoc (attr := simp)]
lemma gluePairInr_gluedRelationProj :
    Scheme.gluePairInr ι d ≫ gluedRelationProj ι d p hp = p ≫ ι :=
  Scheme.gluePairInr_desc _ _ _ _ _

/-- **The second piece of the glued relation is the inverse image of `W` under a projection.**
A point of `V` lies over `W` exactly when it is identified with a point of `P` in the glueing. -/
lemma preimage_opensRange_gluedRelationProj :
    gluedRelationProj ι d p hp ⁻¹ᵁ ι.opensRange = (Scheme.gluePairInr ι d).opensRange := by
  ext z
  simp only [Scheme.Hom.mem_preimage, SetLike.mem_coe, Scheme.Hom.coe_opensRange, Set.mem_range]
  obtain ⟨v, rfl⟩ | ⟨q, rfl⟩ := Scheme.gluePair_jointly_surjective ι d z
  · rw [← Scheme.Hom.comp_apply, gluePairInl_gluedRelationProj]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨d w, ((Scheme.gluePairInl_eq_gluePairInr_iff ι d).mpr ⟨w, rfl, rfl⟩).symm⟩
    · rintro ⟨q, hq⟩
      obtain ⟨w, hw, -⟩ := (Scheme.gluePairInl_eq_gluePairInr_iff ι d).mp hq.symm
      exact ⟨w, by simpa using hw⟩
  · rw [← Scheme.Hom.comp_apply, gluePairInr_gluedRelationProj, Scheme.Hom.comp_apply]
    exact ⟨fun _ ↦ ⟨q, rfl⟩, fun _ ↦ ⟨p q, rfl⟩⟩

/-- **The projections of the glued relation are étale**, being the identity on `V` and the étale
morphism `p ≫ ι` on `P`. -/
lemma etale_gluedRelationProj [Etale p] : Etale (gluedRelationProj ι d p hp) := by
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun b : Bool ↦ cond b (Scheme.gluePairInl ι d).opensRange
      (Scheme.gluePairInr ι d).opensRange) ?_ fun b ↦ ?_
  · exact iSup_bool_eq.trans (Scheme.gluePair_opensRange_sup ι d)
  · cases b
    · rw [Bool.cond_false, ← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc,
        gluePairInr_gluedRelationProj]
      infer_instance
    · rw [Bool.cond_true, ← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc,
        gluePairInl_gluedRelationProj, Category.comp_id]
      infer_instance

/-- Over the open where a point of the glued relation projects into `W`, it is a point of `P`. -/
lemma exists_gluePairInr_of_forall_mem {T : Scheme.{u}} (r : T ⟶ Scheme.gluePair ι d)
    (U : T.Opens) (hU : U ≤ (r ≫ gluedRelationProj ι d p hp) ⁻¹ᵁ ι.opensRange) :
    ∃ b : (U : Scheme.{u}) ⟶ P, b ≫ Scheme.gluePairInr ι d = U.ι ≫ r := by
  refine ⟨IsOpenImmersion.lift (Scheme.gluePairInr ι d) (U.ι ≫ r) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨u, rfl⟩
  have hu : r u.1 ∈ gluedRelationProj ι d p hp ⁻¹ᵁ ι.opensRange := hU u.2
  rw [preimage_opensRange_gluedRelationProj] at hu
  exact hu

/-- Near a point of `T` at which a point of the glued relation does not project into `W`, it is a
point of the diagonal piece `V`. -/
lemma exists_gluePairInl_of_not_mem {T : Scheme.{u}} (r : T ⟶ Scheme.gluePair ι d) (τ : T)
    (hτ : τ ∉ (r ≫ gluedRelationProj ι d p hp) ⁻¹ᵁ ι.opensRange) :
    ∃ U : T.Opens, τ ∈ U ∧
      ∃ v : (U : Scheme.{u}) ⟶ V, v ≫ Scheme.gluePairInl ι d = U.ι ≫ r := by
  refine ⟨r ⁻¹ᵁ (Scheme.gluePairInl ι d).opensRange, ?_, ?_⟩
  · obtain ⟨v, hv⟩ | ⟨q, hq⟩ := Scheme.gluePair_jointly_surjective ι d (r τ)
    · exact ⟨v, hv⟩
    · refine absurd ?_ hτ
      change r τ ∈ gluedRelationProj ι d p hp ⁻¹ᵁ ι.opensRange
      rw [preimage_opensRange_gluedRelationProj]
      exact ⟨q, hq⟩
  · exact ⟨IsOpenImmersion.lift (Scheme.gluePairInl ι d) (_ ≫ r) (by
      rintro _ ⟨u, rfl⟩
      exact u.2), IsOpenImmersion.lift_fac _ _ _⟩

/-- A point of the diagonal piece `V` of the glued relation projects to itself. -/
private lemma comp_gluedRelationProj_of_comp_gluePairInl {T U : Scheme.{u}} {v : U ⟶ V}
    {f : U ⟶ T} {r : T ⟶ Scheme.gluePair ι d} {p : P ⟶ W} (hp : d ≫ p = 𝟙 W)
    (h : v ≫ Scheme.gluePairInl ι d = f ≫ r) :
    f ≫ r ≫ gluedRelationProj ι d p hp = v := by
  rw [← Category.assoc, ← h, Category.assoc, gluePairInl_gluedRelationProj, Category.comp_id]

/-- If `a` is a point of the second piece `P` of the glued relation `r` and `c ≫ p = a ≫ p'`,
then `c ≫ p ≫ ι` is the projection of `r` along `p'`. -/
private lemma comp_comp_eq_comp_gluedRelationProj {T U : Scheme.{u}} {a c : U ⟶ P}
    {p p' : P ⟶ W} (hp' : d ≫ p' = 𝟙 W) (hc : c ≫ p = a ≫ p') {f : U ⟶ T}
    {r : T ⟶ Scheme.gluePair ι d} (h : a ≫ Scheme.gluePairInr ι d = f ≫ r) :
    c ≫ p ≫ ι = f ≫ r ≫ gluedRelationProj ι d p' hp' := by
  rw [reassoc_of% hc, ← gluePairInr_gluedRelationProj ι d p' hp', ← Category.assoc, h,
    Category.assoc]

variable (p₁ p₂ : P ⟶ W) (hd₁ : d ≫ p₁ = 𝟙 W) (hd₂ : d ≫ p₂ = 𝟙 W)

/-- The two projections of the glued relation agree after a morphism out of `V` as soon as `p₁`
and `p₂` do. -/
lemma gluedRelationProj_comp_eq {Z : Scheme.{u}} (q : V ⟶ Z) (h : p₁ ≫ ι ≫ q = p₂ ≫ ι ≫ q) :
    gluedRelationProj ι d p₁ hd₁ ≫ q = gluedRelationProj ι d p₂ hd₂ ≫ q := by
  refine Scheme.gluePair_hom_ext _ _ ?_ ?_
  · rw [gluePairInl_gluedRelationProj_assoc, gluePairInl_gluedRelationProj_assoc]
  · rw [gluePairInr_gluedRelationProj_assoc, gluePairInr_gluedRelationProj_assoc, h]

/-- **The projections of the glued relation are jointly monic** when `p₁, p₂` are. -/
lemma jointlyMono₂_gluedRelationProj [JointlyMono₂ p₁ p₂] :
    JointlyMono₂ (gluedRelationProj ι d p₁ hd₁) (gluedRelationProj ι d p₂ hd₂) := by
  refine ⟨fun {T} f g h₁ h₂ ↦ Scheme.hom_ext_of_forall _ _ fun τ ↦ ?_⟩
  by_cases hτ : τ ∈ (f ≫ gluedRelationProj ι d p₁ hd₁) ⁻¹ᵁ ι.opensRange
  · let U := (f ≫ gluedRelationProj ι d p₁ hd₁) ⁻¹ᵁ ι.opensRange
    obtain ⟨a, ha⟩ := exists_gluePairInr_of_forall_mem ι d p₁ hd₁ f U le_rfl
    obtain ⟨b, hb⟩ := exists_gluePairInr_of_forall_mem ι d p₁ hd₁ g U (by rw [← h₁])
    refine ⟨U, hτ, ?_⟩
    rw [← ha, ← hb]
    congr 1
    apply JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂)
    · rw [← cancel_mono ι, Category.assoc, Category.assoc,
        comp_comp_eq_comp_gluedRelationProj ι d hd₁ rfl ha,
        comp_comp_eq_comp_gluedRelationProj ι d hd₁ rfl hb, h₁]
    · rw [← cancel_mono ι, Category.assoc, Category.assoc,
        comp_comp_eq_comp_gluedRelationProj ι d hd₂ rfl ha,
        comp_comp_eq_comp_gluedRelationProj ι d hd₂ rfl hb, h₂]
  · obtain ⟨U₁, hU₁, a, ha⟩ := exists_gluePairInl_of_not_mem ι d p₁ hd₁ f τ hτ
    obtain ⟨U₂, hU₂, b, hb⟩ := exists_gluePairInl_of_not_mem ι d p₁ hd₁ g τ (by rwa [← h₁])
    refine ⟨U₁ ⊓ U₂, ⟨hU₁, hU₂⟩, ?_⟩
    have ea : (U₁ ⊓ U₂).ι ≫ f = (T.homOfLE inf_le_left ≫ a) ≫ Scheme.gluePairInl ι d := by
      rw [Category.assoc, ha, Scheme.homOfLE_ι_assoc]
    have eb : (U₁ ⊓ U₂).ι ≫ g = (T.homOfLE inf_le_right ≫ b) ≫ Scheme.gluePairInl ι d := by
      rw [Category.assoc, hb, Scheme.homOfLE_ι_assoc]
    rw [ea, eb]
    congr 1
    have := congrArg ((U₁ ⊓ U₂).ι ≫ ·) h₁
    rw [← Category.assoc, ← Category.assoc, ea, eb] at this
    simpa using this

/-- **The glued relation is an internal equivalence relation on `V`.** -/
theorem isEquivalenceRelation_gluedRelationProj [IsEquivalenceRelation p₁ p₂] :
    IsEquivalenceRelation (gluedRelationProj ι d p₁ hd₁) (gluedRelationProj ι d p₂ hd₂) := by
  have hJ : JointlyMono₂ p₁ p₂ := IsEquivalenceRelation.jointlyMono₂
  have hJ' := jointlyMono₂_gluedRelationProj ι d p₁ p₂ hd₁ hd₂
  set t := gluedRelationProj ι d p₁ hd₁
  set s := gluedRelationProj ι d p₂ hd₂
  refine isEquivalenceRelation_of_forall t s hJ' ⟨Scheme.gluePairInl ι d, by simp [t],
    by simp [s]⟩ (fun {T} r ↦ ?_) (fun {T} r r' hrr' ↦ ?_)
  · refine Scheme.exists_lift_of_forall t s _ _ fun τ ↦ ?_
    by_cases hτ : τ ∈ (r ≫ s) ⁻¹ᵁ ι.opensRange
    · let U := (r ≫ s) ⁻¹ᵁ ι.opensRange
      obtain ⟨b, hb⟩ := exists_gluePairInr_of_forall_mem ι d p₂ hd₂ r U le_rfl
      obtain ⟨b', hb'₁, hb'₂⟩ := IsEquivalenceRelation.exists_symm (p₁ := p₁) (p₂ := p₂) b
      refine ⟨U, hτ, b' ≫ Scheme.gluePairInr ι d, ?_, ?_⟩
      · rw [Category.assoc, gluePairInr_gluedRelationProj]
        exact comp_comp_eq_comp_gluedRelationProj ι d hd₂ hb'₁ hb
      · rw [Category.assoc, gluePairInr_gluedRelationProj]
        exact comp_comp_eq_comp_gluedRelationProj ι d hd₁ hb'₂ hb
    · obtain ⟨U, hU, v, hv⟩ := exists_gluePairInl_of_not_mem ι d p₂ hd₂ r τ hτ
      have ht' := comp_gluedRelationProj_of_comp_gluePairInl ι d hd₁ hv
      have hs' := comp_gluedRelationProj_of_comp_gluePairInl ι d hd₂ hv
      refine ⟨U, hU, U.ι ≫ r, ?_, ?_⟩ <;> rw [Category.assoc, ht', hs']
  · refine Scheme.exists_lift_of_forall t s _ _ fun τ ↦ ?_
    by_cases hτ : τ ∈ (r ≫ s) ⁻¹ᵁ ι.opensRange
    · let U := (r ≫ s) ⁻¹ᵁ ι.opensRange
      obtain ⟨b, hb⟩ := exists_gluePairInr_of_forall_mem ι d p₂ hd₂ r U le_rfl
      obtain ⟨b', hb'⟩ := exists_gluePairInr_of_forall_mem ι d p₁ hd₁ r' U
        (by rw [← hrr'])
      have hbb' : b ≫ p₂ = b' ≫ p₁ := by
        rw [← cancel_mono ι, Category.assoc, Category.assoc,
          comp_comp_eq_comp_gluedRelationProj ι d hd₂ rfl hb,
          comp_comp_eq_comp_gluedRelationProj ι d hd₁ rfl hb', hrr']
      obtain ⟨b'', hb''₁, hb''₂⟩ :=
        IsEquivalenceRelation.exists_trans (p₁ := p₁) (p₂ := p₂) b b' hbb'
      refine ⟨U, hτ, b'' ≫ Scheme.gluePairInr ι d, ?_, ?_⟩
      · rw [Category.assoc, gluePairInr_gluedRelationProj]
        exact comp_comp_eq_comp_gluedRelationProj ι d hd₁ hb''₁ hb
      · rw [Category.assoc, gluePairInr_gluedRelationProj]
        exact comp_comp_eq_comp_gluedRelationProj ι d hd₂ hb''₂ hb'
    · obtain ⟨U₁, hU₁, v, hv⟩ := exists_gluePairInl_of_not_mem ι d p₂ hd₂ r τ hτ
      obtain ⟨U₂, hU₂, v', hv'⟩ := exists_gluePairInl_of_not_mem ι d p₁ hd₁ r' τ
        (by rwa [← hrr'])
      refine ⟨U₁ ⊓ U₂, ⟨hU₁, hU₂⟩, (U₁ ⊓ U₂).ι ≫ r, rfl, ?_⟩
      have e₁ : (U₁ ⊓ U₂).ι ≫ r ≫ s = (U₁ ⊓ U₂).ι ≫ r' ≫ t := by rw [hrr']
      have ht' := comp_gluedRelationProj_of_comp_gluePairInl ι d hd₁ hv'
      have hs' := comp_gluedRelationProj_of_comp_gluePairInl ι d hd₂ hv'
      have e₂ : (U₁ ⊓ U₂).ι ≫ r' ≫ t = (U₁ ⊓ U₂).ι ≫ r' ≫ s := by
        rw [← Scheme.homOfLE_ι_assoc T (inf_le_right : U₁ ⊓ U₂ ≤ U₂), ht',
          ← Scheme.homOfLE_ι_assoc T (inf_le_right : U₁ ⊓ U₂ ≤ U₂), hs']
      rw [Category.assoc, e₁, e₂]

/-- **The projection of the glued relation commutes with maps of glueings.** -/
lemma gluePairMap_gluedRelationProj {W' V' P' : Scheme.{u}} (ι' : W' ⟶ V') [IsOpenImmersion ι']
    (d' : W' ⟶ P') [IsOpenImmersion d'] (p' : P' ⟶ W') (hp' : d' ≫ p' = 𝟙 W')
    (w : W ⟶ W') (x : V ⟶ V') (y : P ⟶ P') (hx : ι ≫ x = w ≫ ι') (hy : d ≫ y = w ≫ d')
    (hpy : p ≫ w = y ≫ p') :
    Scheme.gluePairMap w x y hx hy ≫ gluedRelationProj ι' d' p' hp' =
      gluedRelationProj ι d p hp ≫ x := by
  refine Scheme.gluePair_hom_ext _ _ ?_ ?_
  · rw [Scheme.gluePairInl_gluePairMap_assoc, gluePairInl_gluedRelationProj,
      gluePairInl_gluedRelationProj_assoc, Category.comp_id]
  · rw [Scheme.gluePairInr_gluePairMap_assoc, gluePairInr_gluedRelationProj,
      gluePairInr_gluedRelationProj_assoc, hx, ← reassoc_of% hpy]

end Glued

section Functor

variable {J : Type w} [Category.{v} J] {Dw Dv Dp : J ⥤ Scheme.{u}} (ι : Dw ⟶ Dv) (d : Dw ⟶ Dp)
  [∀ j, IsOpenImmersion (ι.app j)] [∀ j, IsOpenImmersion (d.app j)]

/-- **The projection of the glued relations, as a natural transformation.** For a natural
transformation `p : Dp ⟶ Dw` split by `d`, the projections `gluedRelationProj` at the stages form
a natural transformation from the diagram of glued stages to `Dv`. -/
noncomputable def gluedRelationProjNatTrans (p : Dp ⟶ Dw) (hp : d ≫ p = 𝟙 Dw) :
    gluePairFunctor ι d ⟶ Dv where
  app j := gluedRelationProj (ι.app j) (d.app j) (p.app j) (by
    rw [← NatTrans.comp_app, hp, NatTrans.id_app])
  naturality {j k} u :=
    gluePairMap_gluedRelationProj (ι.app j) (d.app j) (p.app j) _ (ι.app k) (d.app k) (p.app k) _
      (Dw.map u) (Dv.map u) (Dp.map u) (ι.naturality u).symm (d.naturality u).symm
      (p.naturality u).symm

variable (p : Dp ⟶ Dw) (hp : d ≫ p = 𝟙 Dw)

/-- The component of `gluedRelationProjNatTrans` at a stage `j` is the projection
`gluedRelationProj` of the glued relation at `j`. -/
@[simp]
lemma gluedRelationProjNatTrans_app (j : J) :
    (gluedRelationProjNatTrans ι d p hp).app j = gluedRelationProj (ι.app j) (d.app j) (p.app j)
      (by rw [← NatTrans.comp_app, hp, NatTrans.id_app]) := rfl

/-- At every stage, `gluedRelationProjNatTrans` is the identity on the piece `Dv`. -/
@[reassoc (attr := simp)]
lemma gluePairFunctorInl_app_gluedRelationProjNatTrans_app (j : J) :
    (gluePairFunctorInl ι d).app j ≫ (gluedRelationProjNatTrans ι d p hp).app j = 𝟙 _ :=
  gluePairInl_gluedRelationProj _ _ _ (by rw [← NatTrans.comp_app, hp, NatTrans.id_app])

/-- At every stage `j`, `gluedRelationProjNatTrans` is `p.app j ≫ ι.app j` on the piece `Dp`. -/
@[reassoc (attr := simp)]
lemma gluePairFunctorInr_app_gluedRelationProjNatTrans_app (j : J) :
    (gluePairFunctorInr ι d).app j ≫ (gluedRelationProjNatTrans ι d p hp).app j =
      p.app j ≫ ι.app j :=
  gluePairInr_gluedRelationProj _ _ _ (by rw [← NatTrans.comp_app, hp, NatTrans.id_app])

include hp in
omit [∀ j, IsOpenImmersion (d.app j)] in
/-- In a cartesian square on a projection `p` with a section `d`, the square on the section is
cartesian too. -/
lemma isPullback_section_of_isPullback ⦃j k : J⦄ (u : j ⟶ k)
    (h : IsPullback (Dp.map u) (p.app j) (p.app k) (Dw.map u)) :
    IsPullback (Dw.map u) (d.app j) (d.app k) (Dp.map u) := by
  have hs : ∀ i, d.app i ≫ p.app i = 𝟙 _ := fun i ↦ by
    rw [← NatTrans.comp_app, hp, NatTrans.id_app]
  refine IsPullback.of_bot ?_ (d.naturality u) h
  rw [hs, hs]
  exact IsPullback.of_id_snd

/-- **Checking a cartesian square on an open cover of its upper right corner.** If the upper right
corner `X` is covered by open immersions `𝒰.f i` and, for each of them, a cartesian square with
`fWX` exhibits a piece `Wi i` of `W` whose square over `fYZ` is cartesian, the square is
cartesian. -/
lemma _root_.AlgebraicGeometry.Scheme.isPullback_of_openCover_of_isPullback
    {W X Y Z : Scheme.{u}} (fWX : W ⟶ X) (fWY : W ⟶ Y) (fXZ : X ⟶ Z) (fYZ : Y ⟶ Z)
    (𝒰 : X.OpenCover) (Wi : 𝒰.I₀ → Scheme.{u}) (a : ∀ i, Wi i ⟶ W) (b : ∀ i, Wi i ⟶ 𝒰.X i)
    (ha : ∀ i, IsPullback (a i) (b i) fWX (𝒰.f i))
    (H : ∀ i, IsPullback (b i) (a i ≫ fWY) (𝒰.f i ≫ fXZ) fYZ) :
    IsPullback fWX fWY fXZ fYZ := by
  refine Scheme.isPullback_of_openCover fWX fWY fXZ fYZ 𝒰 fun i ↦ ?_
  refine (H i).of_iso ((ha i).isoPullback) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact ((ha i).isoPullback_hom_snd).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change a i ≫ fWY = (ha i).isoPullback.hom ≫ pullback.fst _ _ ≫ fWY
    rw [IsPullback.isoPullback_hom_fst_assoc]
  · simp
  · simp

variable (hι : ∀ ⦃j k : J⦄ (u : j ⟶ k), IsPullback (Dw.map u) (ι.app j) (ι.app k) (Dv.map u))
  (hpb : ∀ ⦃j k : J⦄ (u : j ⟶ k), IsPullback (Dp.map u) (p.app j) (p.app k) (Dw.map u))

include hι hpb in
/-- **The source squares of the glued relations are cartesian.** If the squares of `ι` and of the
projection `p` are cartesian, so are the squares of the glued relations over the projection
`gluedRelationProjNatTrans`: at the diagonal piece the square is the identity square of `Dv`,
and at the second piece it is the composite of the squares of `p` and of `ι`. -/
theorem isPullback_gluedRelationProjNatTrans ⦃j k : J⦄ (u : j ⟶ k) :
    IsPullback ((gluePairFunctor ι d).map u) ((gluedRelationProjNatTrans ι d p hp).app j)
      ((gluedRelationProjNatTrans ι d p hp).app k) (Dv.map u) := by
  have hα : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dv.map u ⁻¹ᵁ (ι.app k).opensRange = (ι.app j).opensRange :=
    fun _ _ u ↦ preimage_opensRange_of_isPullback (hι u).flip
  have hβ : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dp.map u ⁻¹ᵁ (d.app k).opensRange = (d.app j).opensRange :=
    fun _ _ u ↦ preimage_opensRange_of_isPullback
      (isPullback_section_of_isPullback d p hp u (hpb u)).flip
  let 𝒰 : ((gluePairFunctor ι d).obj k).OpenCover :=
    Scheme.Cover.mkOfCovers WalkingPair
      (fun b ↦ (Scheme.gluePairDiagram (ι.app k) (d.app k)).obj (some b))
      (fun b ↦ colimit.ι (Scheme.gluePairDiagram (ι.app k) (d.app k)) (some b))
      (fun x ↦ by
        obtain ⟨y, hy⟩ | ⟨y, hy⟩ := Scheme.gluePair_jointly_surjective (ι.app k) (d.app k) x
        · exact ⟨.left, y, hy⟩
        · exact ⟨.right, y, hy⟩)
      (fun b ↦ by
        cases b
        · exact inferInstanceAs (IsOpenImmersion (Scheme.gluePairInl (ι.app k) (d.app k)))
        · exact inferInstanceAs (IsOpenImmersion (Scheme.gluePairInr (ι.app k) (d.app k))))
  refine Scheme.isPullback_of_openCover_of_isPullback _ _ _ _ 𝒰
    (fun b ↦ (Scheme.gluePairDiagram (ι.app j) (d.app j)).obj (some b))
    (fun b ↦ colimit.ι (Scheme.gluePairDiagram (ι.app j) (d.app j)) (some b))
    (fun b ↦ b.casesOn (Dv.map u) (Dp.map u)) (fun b ↦ ?_) (fun b ↦ ?_)
  · cases b
    · exact (isPullback_gluePairFunctorInl_app ι d hβ u).flip
    · exact (isPullback_gluePairFunctorInr_app ι d hα u).flip
  · cases b
    · change IsPullback (Dv.map u) (Scheme.gluePairInl (ι.app j) (d.app j) ≫ _)
        (Scheme.gluePairInl (ι.app k) (d.app k) ≫ _) (Dv.map u)
      rw [gluedRelationProjNatTrans_app, gluedRelationProjNatTrans_app,
        gluePairInl_gluedRelationProj, gluePairInl_gluedRelationProj]
      exact IsPullback.of_id_snd
    · change IsPullback (Dp.map u) (Scheme.gluePairInr (ι.app j) (d.app j) ≫ _)
        (Scheme.gluePairInr (ι.app k) (d.app k) ≫ _) (Dv.map u)
      rw [gluedRelationProjNatTrans_app, gluedRelationProjNatTrans_app,
        gluePairInr_gluedRelationProj, gluePairInr_gluedRelationProj]
      exact (hpb u).paste_vert (hι u)

end Functor

end AlgebraicGeometry
