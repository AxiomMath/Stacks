module

public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairOpenExtension

/-!
# Transition morphisms of extended kernel-pair relations

Let `E` and `E'` be two extended kernel-pair relations
(`AlgebraicGeometry.Space.OpenKernelPairExtension`): open immersions `W ⟶ V`, `W' ⟶ V'`,
morphisms `p : W ⟶ X`, `p' : W' ⟶ X'` with represented kernel pairs `Q`, `Q'`, and the glued
relations `R = V ⊔_W Q`, `R' = V' ⊔_{W'} Q'`. Given `v : V ⟶ V'`, `k : W ⟶ W'` and
`u : X ⟶ X'` such that `W` is the inverse image of `W'` in `V` and `W = W' ×_{X'} X`, the
relations are related by a morphism `r : R ⟶ R'` over `v`, and the squares formed by `r`, `v`
and either of the two morphisms `R ⟶ V`, `R' ⟶ V'` are cartesian.

This is the transition morphism of the relations `R_i` of the proof of absolute Noetherian
approximation, Stacks 07SU, with the cartesian square displayed there as Stacks 07SV.

## Main definitions

* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition`: the data `v`, `k`, `u` and the
  two cartesian squares.
* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.q` and
  `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.r`: the induced morphisms of the
  kernel pairs and of the glued relations.

## Main results

* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.isPullback_q_q₂`: the kernel pair
  of `p` is the base change of the kernel pair of `p'` along `k`, read on either projection.
* `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.isPullback_rScheme_sourceScheme`
  and
  `AlgebraicGeometry.Space.OpenKernelPairExtension.Transition.isPullback_rScheme_targetScheme`:
  the displayed square of Stacks 07SV, for the source and for the target morphism.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SV](https://stacks.math.columbia.edu/tag/07SV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "F" => BigFppfOver.toScheme B S hS

namespace OpenKernelPairExtension

variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W V' W' : BigFppfOver B S hS}
  (E : OpenKernelPairExtension B S hS X V W) (E' : OpenKernelPairExtension B S hS X' V' W')

/-- A *transition* from `E` to `E'`: morphisms `v : V ⟶ V'`, `k : W ⟶ W'` and `u : X ⟶ X'`
such that `W` is the inverse image of `W'` in `V` and `W = W' ×_{X'} X`. -/
structure Transition where
  /-- The morphism of the ambient objects. -/
  v : V ⟶ V'
  /-- The morphism of the charts. -/
  k : W ⟶ W'
  /-- The morphism of the targets. -/
  u : X ⟶ X'
  isPullback_j : IsPullback k E.j E'.j v
  isPullback_p : IsPullback (yoneda.map k) E.p E'.p u

namespace Transition

variable {E E'} (T : Transition E E')

/-- The two composites `Q ⟶ W ⟶ W'` agree after composing with `p' : W' ⟶ X'`. -/
theorem yoneda_q_comm :
    yoneda.map (E.q₁ ≫ T.k) ≫ E'.p = yoneda.map (E.q₂ ≫ T.k) ≫ E'.p := by
  rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, T.isPullback_p.w,
    ← Category.assoc, ← Category.assoc, E.isPullback.w]

/-- The induced morphism of the kernel pairs `Q = W ×_X W ⟶ Q' = W' ×_{X'} W'`. -/
noncomputable def q : E.Q ⟶ E'.Q :=
  kernelPairLift B S hS E'.isPullback (E.q₁ ≫ T.k) (E.q₂ ≫ T.k) T.yoneda_q_comm

/-- The morphism `q` commutes with the first projections of the kernel pairs. -/
@[reassoc (attr := simp)]
theorem q_q₁ : T.q ≫ E'.q₁ = E.q₁ ≫ T.k := kernelPairLift_fst _ _ _ _ _ _ _

/-- The morphism `q` commutes with the second projections of the kernel pairs. -/
@[reassoc (attr := simp)]
theorem q_q₂ : T.q ≫ E'.q₂ = E.q₂ ≫ T.k := kernelPairLift_snd _ _ _ _ _ _ _

/-- The morphism `q` commutes with the diagonals `W ⟶ Q` and `W' ⟶ Q'`. -/
theorem δ_q : E.δ ≫ T.q = T.k ≫ E'.δ :=
  kernelPair_hom_ext B S hS E'.isPullback _ _ (by simp) (by simp)

/-- The kernel pair of `p` is the base change of the kernel pair of `p'` along `k`, read on the
second projection, as presheaves. -/
theorem isPullback_yoneda_q_q₂ :
    IsPullback (yoneda.map T.q) (yoneda.map E.q₂) (yoneda.map E'.q₂) (yoneda.map T.k) := by
  have houter : IsPullback (yoneda.map E.q₁ ≫ yoneda.map T.k) (yoneda.map E.q₂) E'.p
      (E.p ≫ T.u) :=
    E.isPullback.paste_horiz T.isPullback_p
  have houter' : IsPullback (yoneda.map T.q ≫ yoneda.map E'.q₁) (yoneda.map E.q₂) E'.p
      (yoneda.map T.k ≫ E'.p) := by
    rw [← yoneda.map_comp, q_q₁, yoneda.map_comp, T.isPullback_p.w]
    exact houter
  exact IsPullback.of_right houter' (by rw [← yoneda.map_comp, ← yoneda.map_comp, q_q₂])
    E'.isPullback

/-- The kernel pair of `p` is the base change of the kernel pair of `p'` along `k`, read on the
first projection, as presheaves. -/
theorem isPullback_yoneda_q_q₁ :
    IsPullback (yoneda.map T.q) (yoneda.map E.q₁) (yoneda.map E'.q₁) (yoneda.map T.k) := by
  have houter : IsPullback (yoneda.map E.q₂ ≫ yoneda.map T.k) (yoneda.map E.q₁) E'.p
      (E.p ≫ T.u) :=
    E.isPullback.flip.paste_horiz T.isPullback_p
  have houter' : IsPullback (yoneda.map T.q ≫ yoneda.map E'.q₂) (yoneda.map E.q₁) E'.p
      (yoneda.map T.k ≫ E'.p) := by
    rw [← yoneda.map_comp, q_q₂, yoneda.map_comp, T.isPullback_p.w]
    exact houter
  exact IsPullback.of_right houter' (by rw [← yoneda.map_comp, ← yoneda.map_comp, q_q₁])
    E'.isPullback.flip

/-- A cartesian square of representable presheaves is a cartesian square of schemes. -/
theorem isPullback_map_of_isPullback_yoneda {P₁ P₂ P₃ P₄ : BigFppfOver B S hS}
    {a : P₁ ⟶ P₂} {b : P₁ ⟶ P₃} {c : P₂ ⟶ P₄} {d : P₃ ⟶ P₄}
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map d)) :
    IsPullback ((F).map a) ((F).map b) ((F).map c) ((F).map d) :=
  (IsPullback.of_map yoneda (yoneda.map_injective (by
    rw [yoneda.map_comp, yoneda.map_comp]; exact h.w)) h).map F

/-- The kernel pair of `p` is the base change of the kernel pair of `p'` along `k`, read on the
second projection, as schemes. -/
theorem isPullback_q_q₂ :
    IsPullback ((F).map T.q) ((F).map E.q₂) ((F).map E'.q₂) ((F).map T.k) :=
  isPullback_map_of_isPullback_yoneda T.isPullback_yoneda_q_q₂

/-- The kernel pair of `p` is the base change of the kernel pair of `p'` along `k`, read on the
first projection, as schemes. -/
theorem isPullback_q_q₁ :
    IsPullback ((F).map T.q) ((F).map E.q₁) ((F).map E'.q₁) ((F).map T.k) :=
  isPullback_map_of_isPullback_yoneda T.isPullback_yoneda_q_q₁

/-- The chart `W` is the inverse image of `W'` under `v : V ⟶ V'`, as schemes. -/
theorem isPullback_map_j : IsPullback ((F).map T.k) ((F).map E.j) ((F).map E'.j) ((F).map T.v) :=
  T.isPullback_j.map F

/-- The morphism of glued schemes `V ⊔_W Q ⟶ V' ⊔_{W'} Q'`. -/
noncomputable def rScheme : E.glued ⟶ E'.glued :=
  pushout.desc ((F).map T.v ≫ pushout.inl ((F).map E'.j) ((F).map E'.δ))
    ((F).map T.q ≫ pushout.inr ((F).map E'.j) ((F).map E'.δ)) (by
    rw [← Category.assoc, ← (F).map_comp, ← T.isPullback_j.w, (F).map_comp,
      Category.assoc, pushout.condition, ← Category.assoc, ← Category.assoc,
      ← (F).map_comp, ← (F).map_comp, T.δ_q])

/-- The restriction of `rScheme` to `V` is `v` followed by the inclusion `V' ⟶ V' ⊔_{W'} Q'`. -/
@[reassoc (attr := simp)]
theorem inl_rScheme : pushout.inl ((F).map E.j) ((F).map E.δ) ≫ T.rScheme =
    (F).map T.v ≫ pushout.inl ((F).map E'.j) ((F).map E'.δ) :=
  pushout.inl_desc _ _ _

/-- The restriction of `rScheme` to `Q` is `q` followed by the inclusion `Q' ⟶ V' ⊔_{W'} Q'`. -/
@[reassoc (attr := simp)]
theorem inr_rScheme : pushout.inr ((F).map E.j) ((F).map E.δ) ≫ T.rScheme =
    (F).map T.q ≫ pushout.inr ((F).map E'.j) ((F).map E'.δ) :=
  pushout.inr_desc _ _ _

/-- The morphism `rScheme` lies over `v` with respect to the target morphisms. -/
theorem rScheme_targetScheme : T.rScheme ≫ E'.targetScheme = E.targetScheme ≫ (F).map T.v := by
  refine pushout.hom_ext ?_ ?_
  · rw [← Category.assoc, T.inl_rScheme, Category.assoc, RelationExtension.inl_target,
      Category.comp_id, ← Category.assoc, RelationExtension.inl_target, Category.id_comp]
  · rw [← Category.assoc, T.inr_rScheme, Category.assoc, RelationExtension.inr_target]
    conv_rhs => rw [← Category.assoc, RelationExtension.inr_target]
    rw [← (F).map_comp, ← (F).map_comp, ← (F).map_comp, ← (F).map_comp]
    exact congrArg (fun a ↦ (F).map a) (by
      rw [← Category.assoc, T.q_q₁, Category.assoc, Category.assoc, T.isPullback_j.w])

/-- The morphism `rScheme` lies over `v` with respect to the source morphisms. -/
theorem rScheme_sourceScheme : T.rScheme ≫ E'.sourceScheme = E.sourceScheme ≫ (F).map T.v := by
  refine pushout.hom_ext ?_ ?_
  · rw [← Category.assoc, T.inl_rScheme, Category.assoc, RelationExtension.inl_source,
      Category.comp_id, ← Category.assoc, RelationExtension.inl_source, Category.id_comp]
  · rw [← Category.assoc, T.inr_rScheme, Category.assoc, RelationExtension.inr_source]
    conv_rhs => rw [← Category.assoc, RelationExtension.inr_source]
    rw [← (F).map_comp, ← (F).map_comp, ← (F).map_comp, ← (F).map_comp]
    exact congrArg (fun a ↦ (F).map a) (by
      rw [← Category.assoc, T.q_q₂, Category.assoc, Category.assoc, T.isPullback_j.w])

/-- The morphism of glued relations, as a morphism of the site. -/
noncomputable def r : E.R ⟶ E'.R :=
  BigFppfOver.homMk B S hS E'.contains_glued _ T.rScheme (by
    change T.rScheme ≫ E'.targetScheme ≫ str B S hS V' = E.targetScheme ≫ str B S hS V
    rw [← Category.assoc, rScheme_targetScheme, Category.assoc, map_comp_str])

/-- The underlying morphism of schemes of `r` is `rScheme`. -/
theorem map_r : (F).map T.r = T.rScheme := rfl

/-- **Stacks 07SV, for the source morphism.** The square formed by `r`, the two source
morphisms `R ⟶ V`, `R' ⟶ V'` and `v` is cartesian, as a square of schemes. -/
theorem isPullback_rScheme_sourceScheme :
    IsPullback T.rScheme E.sourceScheme E'.sourceScheme ((F).map T.v) :=
  isPullback_gluedRelationSource_of_isPullback T.isPullback_map_j T.isPullback_q_q₂
    E.map_δ_q₂ (by rw [← (F).map_comp, ← (F).map_comp, T.δ_q])
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (RelationExtension.inl_source _) (RelationExtension.inr_source _)
    (RelationExtension.inl_source _) (RelationExtension.inr_source _)
    T.inl_rScheme T.inr_rScheme

/-- **Stacks 07SV, for the target morphism.** The square formed by `r`, the two target
morphisms `R ⟶ V`, `R' ⟶ V'` and `v` is cartesian, as a square of schemes. -/
theorem isPullback_rScheme_targetScheme :
    IsPullback T.rScheme E.targetScheme E'.targetScheme ((F).map T.v) :=
  isPullback_gluedRelationSource_of_isPullback T.isPullback_map_j T.isPullback_q_q₁
    E.map_δ_q₁ (by rw [← (F).map_comp, ← (F).map_comp, T.δ_q])
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (RelationExtension.inl_target _) (RelationExtension.inr_target _)
    (RelationExtension.inl_target _) (RelationExtension.inr_target _)
    T.inl_rScheme T.inr_rScheme

end Transition

end OpenKernelPairExtension

end AlgebraicGeometry.Space

end
