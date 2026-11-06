module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedQuotientKernelPair

/-!
# Morphisms related by every stage relation have the same image in `X`

This is the converse of `AlgebraicGeometry.Space.ElementaryChart.StageMap.exists_lift_of_eq`:
let an elementary chart `f : V ⟶ X` with open part `U ⊆ X` and inverse image `W ⊆ V` map
compatibly to the stages `E_i` of a directed system of extended relations
(`AlgebraicGeometry.Space.OpenKernelPairExtension`), with transition morphisms
(`AlgebraicGeometry.Space.OpenKernelPairExtension.Transition`), in such a way that `W` is the
inverse image of every `W_i`, and that morphisms into `V` and into `U` are determined by their
images in the stages beyond any given one. Then two morphisms `a, b : Y ⟶ V` whose images in
every stage are related by the relation `R_i` have the same image in `X`.

This is the inclusion `lim R_i ⊆ V ×_X V` of the proof of absolute Noetherian approximation,
Stacks 07SU: "`R` is the union of `W ×_U W` and `V` glued along `W`".

## Main definitions

* `AlgebraicGeometry.Space.ElementaryChart.StageSystem`: the stages, their compatible maps
  from the chart, and the transition morphisms.

## Main results

* `AlgebraicGeometry.Space.mem_range_snd_of_isPullback`: in a cartesian square of schemes, a point
  whose image lies in the image of the opposite side lies in the image of the near side.
* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.isPullback_inl` and
  `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.isPullback_inr`: the two charts of a
  glued relation are the inverse images of the charts of the next one.
* `AlgebraicGeometry.Space.ElementaryChart.StageSystem.eq_of_forall_exists_lift`: the converse.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "F" => BigFppfOver.toScheme B S hS

/-- In a cartesian square of schemes, a point of one side whose image lies in the image of the
opposite side lies in the image of the side between them. -/
theorem mem_range_snd_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) (hy : g y ∈ Set.range f) :
    y ∈ Set.range snd := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨z, -, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
  refine ⟨h.isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz₂]

namespace OpenKernelPairExtension

variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W V' W' : BigFppfOver B S hS}
  {E : OpenKernelPairExtension B S hS X V W} {E' : OpenKernelPairExtension B S hS X' V' W'}

/-- Morphisms into the glued relation are determined by their two components. -/
theorem hom_ext_R {Z : BigFppfOver B S hS} (x y : Z ⟶ E.R) (h₁ : x ≫ E.t = y ≫ E.t)
    (h₂ : x ≫ E.s = y ≫ E.s) : x = y := by
  have : JointlyMono₂ E.targetScheme E.sourceScheme :=
    RelationExtension.jointlyMono₂ (j := (F).map E.j)
      (equivalenceRelation_kernel B S hS E.isPullback).toJointlyMono₂ E.map_δ_q₁ E.map_δ_q₂
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  exact JointlyMono₂.right_cancellation (p₁ := E.targetScheme) (p₂ := E.sourceScheme)
    ((F).map x) ((F).map y) (by exact congrArg (fun g ↦ (F).map g) h₁)
    (by exact congrArg (fun g ↦ (F).map g) h₂)

/-- The diagonal chart of a glued relation is an open immersion of schemes. -/
instance isOpenImmersion_map_inl : AlgebraicGeometry.IsOpenImmersion ((F).map E.inl) :=
  RelationExtension.isOpenImmersion_inl

/-- The kernel pair chart of a glued relation is an open immersion of schemes. -/
instance isOpenImmersion_map_inr : AlgebraicGeometry.IsOpenImmersion ((F).map E.inr) :=
  RelationExtension.isOpenImmersion_inr

namespace Transition

variable (T : Transition E E')

/-- The diagonal chart of a glued relation is the inverse image of the diagonal chart of the
next one. -/
theorem isPullback_inl : IsPullback ((F).map T.v) ((F).map E.inl) ((F).map E'.inl)
    ((F).map T.r) := by
  have h : IsPullback ((F).map T.v) (pushout.inl ((F).map E.j) ((F).map E.δ))
      (pushout.inl ((F).map E'.j) ((F).map E'.δ)) T.rScheme := by
    refine IsPullback.of_bot ?_ T.inl_rScheme.symm T.isPullback_rScheme_sourceScheme
    rw [RelationExtension.inl_source, RelationExtension.inl_source]
    exact IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
  exact h

/-- The kernel pair chart of a glued relation is the inverse image of the kernel pair chart of
the next one. -/
theorem isPullback_inr : IsPullback ((F).map T.q) ((F).map E.inr) ((F).map E'.inr)
    ((F).map T.r) := by
  have h : IsPullback ((F).map T.q) (pushout.inr ((F).map E.j) ((F).map E.δ))
      (pushout.inr ((F).map E'.j) ((F).map E'.δ)) T.rScheme := by
    refine IsPullback.of_bot ?_ T.inr_rScheme.symm T.isPullback_rScheme_sourceScheme
    rw [RelationExtension.inr_source, RelationExtension.inr_source]
    exact T.isPullback_q_q₂.paste_vert T.isPullback_map_j
  exact h

end Transition

end OpenKernelPairExtension


namespace ElementaryChart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
  (C : ElementaryChart X V)

/-- **A directed system of stages for an elementary chart.** Extended relations `E i` on stages
`V_i ⊇ W_i ⟶ U_i`, with compatible maps from `V ⊇ W ⟶ U` and transition morphisms for
`i ≤ i'`, such that `W` is the inverse image of every `W_i` and such that morphisms into `V` and
into `U` are determined by their images in the stages beyond any given one. -/
structure StageSystem (I : Type u) [Preorder I] where
  /-- The open part of the target at a stage. -/
  Ui : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The ambient object at a stage. -/
  Vi : I → BigFppfOver B S hS
  /-- The chart at a stage. -/
  Wi : I → BigFppfOver B S hS
  /-- The extended relation at a stage. -/
  E : ∀ i, OpenKernelPairExtension B S hS (Ui i) (Vi i) (Wi i)
  /-- The maps from the chart. -/
  M : ∀ i, C.StageMap (E i)
  /-- The transition morphisms. -/
  T : ∀ {i i' : I}, i ≤ i' → OpenKernelPairExtension.Transition (E i') (E i)
  /-- The maps from the chart commute with the transition morphisms on ambient objects. -/
  comm_v : ∀ {i i' : I} (h : i ≤ i'), (M i').v ≫ (T h).v = (M i).v
  /-- The maps from the chart commute with the transition morphisms on charts. -/
  comm_w : ∀ {i i' : I} (h : i ≤ i'), (M i').w ≫ (T h).k = (M i).w
  /-- The maps from the chart commute with the transition morphisms on open parts. -/
  comm_u : ∀ {i i' : I} (h : i ≤ i'), (M i').u ≫ (T h).u = (M i).u
  /-- The chart `W` is the inverse image of the chart at every stage. -/
  isPullback_w : ∀ i, IsPullback (M i).w C.j (E i).j (M i).v
  /-- Morphisms into `V` agreeing at every stage beyond a given one are equal. -/
  hom_ext_V : ∀ (i₀ : I) {Y : BigFppfOver B S hS} (x y : Y ⟶ V),
    (∀ i, i₀ ≤ i → x ≫ (M i).v = y ≫ (M i).v) → x = y
  /-- Morphisms into `U` agreeing at every stage beyond a given one are equal. -/
  hom_ext_U : ∀ (i₀ : I) {Y : BigFppfOver B S hS} (x y : yoneda.obj Y ⟶ C.U.toFunctor),
    (∀ i, i₀ ≤ i → x ≫ (M i).u = y ≫ (M i).u) → x = y

namespace StageSystem

variable {C} {I : Type u} [Preorder I] (D : C.StageSystem I)

/-- Morphisms from the presheaf represented by an object of the site to an fppf sheaf are equal
when they agree on an open cover. -/
theorem hom_ext_of_locally (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {Y : BigFppfOver B S hS} (x y : yoneda.obj Y ⟶ X)
    (H : ∀ z : (F).obj Y, ∃ O : ((F).obj Y).Opens, z ∈ O ∧
      yoneda.map (openIncl B S hS Y O) ≫ x = yoneda.map (openIncl B S hS Y O) ≫ y) :
    x = y := by
  choose O hzO hO using H
  have hcov := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
    (fun z ↦ openIncl B S hS Y (O z)) (fun z ↦ by
      change AlgebraicGeometry.IsOpenImmersion (O z).ι
      infer_instance) (fun z ↦ ⟨z, by
      change z ∈ Set.range (O z).ι
      rw [Scheme.Opens.range_ι]
      exact hzO z⟩)
  have hsh := (isSheaf_iff_isSheaf_of_type _ X).mp hX
  apply yonedaEquiv.injective
  refine (hsh _ hcov).isSeparatedFor.ext fun Z g hg ↦ ?_
  obtain ⟨W', k, g', hg', rfl⟩ := hg
  cases hg' with
  | mk z =>
    have h := congrArg yonedaEquiv (hO z)
    rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality] at h
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h]

/-- The lifts at two stages are related by the transition morphism. -/
theorem lift_comp_r {i i' : I} (h : i ≤ i') {Y : BigFppfOver B S hS} (a b : Y ⟶ V)
    (ρ : Y ⟶ (D.E i).R) (hρt : ρ ≫ (D.E i).t = a ≫ (D.M i).v)
    (hρs : ρ ≫ (D.E i).s = b ≫ (D.M i).v)
    (ρ' : Y ⟶ (D.E i').R) (hρt' : ρ' ≫ (D.E i').t = a ≫ (D.M i').v)
    (hρs' : ρ' ≫ (D.E i').s = b ≫ (D.M i').v) :
    ρ' ≫ (D.T h).r = ρ :=
  OpenKernelPairExtension.hom_ext_R _ _
    (by rw [Category.assoc, (D.T h).r_t, ← Category.assoc, hρt', Category.assoc, D.comm_v, hρt])
    (by rw [Category.assoc, (D.T h).r_s, ← Category.assoc, hρs', Category.assoc, D.comm_v, hρs])

/-- **Morphisms related by every stage relation have the same image in `X`.** -/
theorem eq_of_forall_exists_lift [Nonempty I] [IsDirected I (· ≤ ·)]
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {Y : BigFppfOver B S hS} (a b : Y ⟶ V)
    (H : ∀ i, ∃ ρ : Y ⟶ (D.E i).R, ρ ≫ (D.E i).t = a ≫ (D.M i).v ∧
      ρ ≫ (D.E i).s = b ≫ (D.M i).v) :
    yoneda.map a ≫ C.f = yoneda.map b ≫ C.f := by
  choose ρ hρt hρs using H
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hρr (i : I) (hi : i₀ ≤ i) : (F).map (ρ i) ≫ (F).map (D.T hi).r = (F).map (ρ i₀) := by
    rw [← (F).map_comp, D.lift_comp_r hi a b (ρ i₀) (hρt i₀) (hρs i₀) (ρ i) (hρt i) (hρs i)]
  refine hom_ext_of_locally hX _ _ fun z ↦ ?_
  have hcov : ∀ x : (F).obj (D.E i₀).R, x ∈ Set.range ((F).map (D.E i₀).inl) ∨
      x ∈ Set.range ((F).map (D.E i₀).inr) := fun x ↦
    exists_eq_of_isPushout_of_isOpenImmersion (D.E i₀).isPushout_map x
  rcases hcov ((F).map (ρ i₀) z) with hz | hz
  · -- the diagonal chart: `a` and `b` agree near `z`
    set O : ((F).obj Y).Opens := (F).map (ρ i₀) ⁻¹ᵁ ((F).map (D.E i₀).inl).opensRange
    refine ⟨O, hz, ?_⟩
    have hab : openIncl B S hS Y O ≫ a = openIncl B S hS Y O ≫ b := by
      refine D.hom_ext_V i₀ _ _ fun i hi ↦ ?_
      have hrange : Set.range ((F).map (openIncl B S hS Y O) ≫ (F).map (ρ i)) ⊆
          Set.range ((F).map (D.E i).inl) := by
        rintro _ ⟨w, rfl⟩
        refine mem_range_snd_of_isPullback (D.T hi).isPullback_inl _ ?_
        rw [← Scheme.Hom.comp_apply, Category.assoc, hρr i hi]
        exact w.2
      set d := IsOpenImmersion.lift _ _ hrange
      have hd : d ≫ (F).map (D.E i).inl = (F).map (openIncl B S hS Y O) ≫ (F).map (ρ i) :=
        IsOpenImmersion.lift_fac _ _ hrange
      have k : ∀ (c : Y ⟶ V) (g : (D.E i).R ⟶ D.Vi i), ρ i ≫ g = c ≫ (D.M i).v →
          (D.E i).inl ≫ g = 𝟙 _ → (F).map (openIncl B S hS Y O ≫ c ≫ (D.M i).v) = d := by
        intro c g hg hinl
        rw [← hg, (F).map_comp, (F).map_comp, ← Category.assoc, ← hd, Category.assoc,
          ← (F).map_comp, hinl, (F).map_id, Category.comp_id]
      have := BigFppfOver.map_toScheme_injective B S hS
        ((k a _ (hρt i) (D.E i).inl_t).trans (k b _ (hρs i) (D.E i).inl_s).symm)
      simpa only [Category.assoc] using this
    rw [← Category.assoc, ← Category.assoc, ← yoneda.map_comp, hab, yoneda.map_comp,
      Category.assoc]
  · -- the kernel pair chart: `a` and `b` factor through `W` with the same image in `U`
    set O : ((F).obj Y).Opens := (F).map (ρ i₀) ⁻¹ᵁ ((F).map (D.E i₀).inr).opensRange
    refine ⟨O, hz, ?_⟩
    let O' := openObj B S hS Y O
    let ιO : O' ⟶ Y := openIncl B S hS Y O
    have hrange (i : I) (hi : i₀ ≤ i) : Set.range ((F).map ιO ≫ (F).map (ρ i)) ⊆
        Set.range ((F).map (D.E i).inr) := by
      rintro _ ⟨w, rfl⟩
      refine mem_range_snd_of_isPullback (D.T hi).isPullback_inr _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, hρr i hi]
      exact w.2
    -- the lift to the kernel pair chart at every stage beyond `i₀`, as a morphism of the site
    have hstrQ (i : I) (hi : i₀ ≤ i) :
        IsOpenImmersion.lift _ _ (hrange i hi) ≫ str B S hS (D.E i).Q = str B S hS O' := by
      rw [← map_comp_str B S hS (D.E i).inr, ← Category.assoc, IsOpenImmersion.lift_fac,
        Category.assoc, map_comp_str, map_comp_str]
    let e (i : I) (hi : i₀ ≤ i) : O' ⟶ (D.E i).Q := homOfScheme _ (hstrQ i hi)
    have he (i : I) (hi : i₀ ≤ i) : e i hi ≫ (D.E i).inr = ιO ≫ ρ i :=
      BigFppfOver.map_toScheme_injective B S hS (by
        change (F).map (e i hi ≫ (D.E i).inr) = (F).map (ιO ≫ ρ i)
        rw [(F).map_comp, (F).map_comp]
        exact IsOpenImmersion.lift_fac _ _ (hrange i hi))
    have hea (i : I) (hi : i₀ ≤ i) : e i hi ≫ (D.E i).q₁ ≫ (D.E i).j = ιO ≫ a ≫ (D.M i).v := by
      rw [← (D.E i).inr_t, ← Category.assoc, he i hi, Category.assoc, hρt]
    have heb (i : I) (hi : i₀ ≤ i) : e i hi ≫ (D.E i).q₂ ≫ (D.E i).j = ιO ≫ b ≫ (D.M i).v := by
      rw [← (D.E i).inr_s, ← Category.assoc, he i hi, Category.assoc, hρs]
    -- `a` and `b` factor through `W`
    have hsq := D.isPullback_w i₀
    let a'' : O' ⟶ C.W := hsq.lift (e i₀ le_rfl ≫ (D.E i₀).q₁) (ιO ≫ a) (by
      rw [Category.assoc, hea i₀ le_rfl, ← Category.assoc])
    let b'' : O' ⟶ C.W := hsq.lift (e i₀ le_rfl ≫ (D.E i₀).q₂) (ιO ≫ b) (by
      rw [Category.assoc, heb i₀ le_rfl, ← Category.assoc])
    have ha'' : a'' ≫ C.j = ιO ≫ a := hsq.lift_snd _ _ _
    have hb'' : b'' ≫ C.j = ιO ≫ b := hsq.lift_snd _ _ _
    -- at every stage beyond `i₀`, the two points of `W_i` are those of the kernel pair chart
    have hmono (i : I) : Mono (D.E i).j :=
      (F).mono_of_mono_map (inferInstance : Mono ((F).map (D.E i).j))
    have hwa (i : I) (hi : i₀ ≤ i) : a'' ≫ (D.M i).w = e i hi ≫ (D.E i).q₁ := by
      rw [← cancel_mono (D.E i).j, Category.assoc, (D.M i).comm_j, ← Category.assoc, ha'',
        Category.assoc, Category.assoc, hea i hi]
    have hwb (i : I) (hi : i₀ ≤ i) : b'' ≫ (D.M i).w = e i hi ≫ (D.E i).q₂ := by
      rw [← cancel_mono (D.E i).j, Category.assoc, (D.M i).comm_j, ← Category.assoc, hb'',
        Category.assoc, Category.assoc, heb i hi]
    have hpU : yoneda.map a'' ≫ C.p = yoneda.map b'' ≫ C.p := by
      refine D.hom_ext_U i₀ _ _ fun i hi ↦ ?_
      rw [Category.assoc, Category.assoc, ← (D.M i).comm_p, ← Category.assoc, ← Category.assoc,
        ← yoneda.map_comp, ← yoneda.map_comp, hwa i hi, hwb i hi, yoneda.map_comp,
        yoneda.map_comp, Category.assoc, Category.assoc, (D.E i).isPullback.w]
    change yoneda.map ιO ≫ yoneda.map a ≫ C.f = yoneda.map ιO ≫ yoneda.map b ≫ C.f
    rw [← Category.assoc, ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, ← ha'',
      ← hb'', yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
      C.isPullback_W.w, ← Category.assoc, ← Category.assoc, hpU]

end StageSystem

end ElementaryChart

end AlgebraicGeometry.Space

end
