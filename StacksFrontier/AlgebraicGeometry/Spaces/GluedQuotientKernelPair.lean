module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartKernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairOpenExtensionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover

/-!
# The kernel pair of an elementary chart, read on the stages of an approximation

Let `f : V ⟶ X` be an étale chart which is an isomorphism off an open subspace `U ⊆ X`, with
inverse image `W ⊆ V` (an `AlgebraicGeometry.Space.ElementaryChart`). Suppose `V`, `W` and `U`
map to the stages `V_i`, `W_i`, `U_i` of an approximation, with `W_i ⊆ V_i` open and
`W_i ⟶ U_i` étale, compatibly, and let `R_i = V_i ⊔_{W_i} (W_i ×_{U_i} W_i)` be the extended
relations (`AlgebraicGeometry.Space.OpenKernelPairExtension`).

This file proves that two morphisms `a, b : Y ⟶ V` with the same image in `X` have images in
every `V_i` which are related by `R_i`: locally on `Y` they are either equal, and related by the
diagonal chart of `R_i`, or both factor through `W` with the same image in `U`, and are related by
the chart `W_i ×_{U_i} W_i` of `R_i`. This is the inclusion `V ×_X V ⊆ lim R_i` of the proof of
absolute Noetherian approximation, Stacks 07SU.

## Main definitions

* `AlgebraicGeometry.Space.homOfScheme`: a morphism of the site from a morphism of the
  underlying schemes commuting with the structure morphisms.
* `AlgebraicGeometry.Space.ElementaryChart.StageMap`: the compatible maps of `V`, `W`, `U` to
  the data of an extended relation.

## Main results

* `AlgebraicGeometry.Space.ElementaryChart.StageMap.exists_lift_of_eq`: two morphisms with the
  same image in `X` are related by the extended relation of the stage.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "F" => BigFppfOver.toScheme B S hS

/-- A morphism of the site from a morphism of the underlying schemes which commutes with the
structure morphisms to `S`. -/
noncomputable def homOfScheme {Y Z : BigFppfOver B S hS} (g : (F).obj Y ⟶ (F).obj Z)
    (hg : g ≫ str B S hS Z = str B S hS Y) : Y ⟶ Z :=
  Over.homMk (ObjectProperty.homMk g) (by apply ObjectProperty.hom_ext; exact hg)

/-- The underlying morphism of schemes of `homOfScheme g hg` is `g`. -/
theorem map_homOfScheme {Y Z : BigFppfOver B S hS} (g : (F).obj Y ⟶ (F).obj Z)
    (hg : g ≫ str B S hS Z = str B S hS Y) : (F).map (homOfScheme g hg) = g := rfl

namespace ElementaryChart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
  (C : ElementaryChart X V)

/-- **Compatible maps of an elementary chart to the data of an extended relation.** Morphisms
`V ⟶ V'`, `W ⟶ W'` and `U ⟶ X'` to the data of an extended relation `E` on `V'`, compatible with
the open immersions and with the morphisms to `U` and `X'`. -/
structure StageMap {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V' W' : BigFppfOver B S hS}
    (E : OpenKernelPairExtension B S hS X' V' W') where
  /-- The map of the ambient objects. -/
  v : V ⟶ V'
  /-- The map of the charts. -/
  w : C.W ⟶ W'
  /-- The map of the open parts of the targets. -/
  u : C.U.toFunctor ⟶ X'
  comm_j : w ≫ E.j = C.j ≫ v
  comm_p : yoneda.map w ≫ E.p = C.p ≫ u

namespace StageMap

variable {C} {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V' W' : BigFppfOver B S hS}
  {E : OpenKernelPairExtension B S hS X' V' W'} (M : C.StageMap E)

/-- **Two morphisms with the same image in `X` are related by the extended relation.** -/
theorem exists_lift_of_eq {Y : BigFppfOver B S hS} (a b : Y ⟶ V)
    (h : yoneda.map a ≫ C.f = yoneda.map b ≫ C.f) :
    ∃ ρ : Y ⟶ E.R, ρ ≫ E.t = a ≫ M.v ∧ ρ ≫ E.s = b ≫ M.v := by
  have : JointlyMono₂ E.targetScheme E.sourceScheme :=
    RelationExtension.jointlyMono₂ (j := (F).map E.j)
      (equivalenceRelation_kernel B S hS E.isPullback).toJointlyMono₂ E.map_δ_q₁ E.map_δ_q₂
  obtain ⟨ρs, hρt, hρs⟩ := RelationExtension.exists_lift_of_locally E.targetScheme
    E.sourceScheme ((F).map a ≫ (F).map M.v) ((F).map b ≫ (F).map M.v) (fun y ↦ by
      obtain ⟨O, hyO, hO⟩ := C.exists_eq_or_factor a b h y
      refine ⟨O, hyO, ?_⟩
      rcases hO with heq | ⟨a', b', ha', hb'⟩
      · refine ⟨O.ι ≫ (F).map a ≫ (F).map M.v ≫ pushout.inl _ _, ?_, ?_⟩
        · simp only [Category.assoc, RelationExtension.inl_target, Category.comp_id]
        · rw [Category.assoc, Category.assoc, Category.assoc, RelationExtension.inl_source,
            Category.comp_id, ← Category.assoc, heq, Category.assoc]
      · let O' := openObj B S hS Y O
        let ιO : O' ⟶ Y := openIncl B S hS Y O
        have hsa : (a' : (F).obj O' ⟶ (F).obj C.W) ≫ str B S hS C.W = str B S hS O' := by
          change a' ≫ str B S hS C.W = O.ι ≫ str B S hS Y
          rw [← map_comp_str B S hS C.j, ← Category.assoc, ha', Category.assoc, map_comp_str]
        have hsb : (b' : (F).obj O' ⟶ (F).obj C.W) ≫ str B S hS C.W = str B S hS O' := by
          change b' ≫ str B S hS C.W = O.ι ≫ str B S hS Y
          rw [← map_comp_str B S hS C.j, ← Category.assoc, hb', Category.assoc, map_comp_str]
        let a'' : O' ⟶ C.W := homOfScheme _ hsa
        let b'' : O' ⟶ C.W := homOfScheme _ hsb
        have ha'' : a'' ≫ C.j = ιO ≫ a :=
          BigFppfOver.map_toScheme_injective B S hS (by exact ha')
        have hb'' : b'' ≫ C.j = ιO ≫ b :=
          BigFppfOver.map_toScheme_injective B S hS (by exact hb')
        have hpU : yoneda.map a'' ≫ C.p = yoneda.map b'' ≫ C.p := by
          rw [← cancel_mono C.U.ι, Category.assoc, Category.assoc, ← C.isPullback_W.w,
            ← Category.assoc, ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, ha'',
            hb'', yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, h]
        have hpE : yoneda.map (a'' ≫ M.w) ≫ E.p = yoneda.map (b'' ≫ M.w) ≫ E.p := by
          rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, M.comm_p,
            ← Category.assoc, ← Category.assoc, hpU]
        let q : O' ⟶ E.Q := kernelPairLift B S hS E.isPullback _ _ hpE
        have hq₁ : (F).map q ≫ (F).map E.q₁ = (F).map a'' ≫ (F).map M.w := by
          rw [← (F).map_comp, kernelPairLift_fst, (F).map_comp]
        have hq₂ : (F).map q ≫ (F).map E.q₂ = (F).map b'' ≫ (F).map M.w := by
          rw [← (F).map_comp, kernelPairLift_snd, (F).map_comp]
        have hjv : (F).map M.w ≫ (F).map E.j = (F).map C.j ≫ (F).map M.v := by
          rw [← (F).map_comp, M.comm_j, (F).map_comp]
        have e₁ : (F).map a'' ≫ (F).map C.j = (F).map ιO ≫ (F).map a := by
          rw [← (F).map_comp, ha'', (F).map_comp]
        have e₂ : (F).map b'' ≫ (F).map C.j = (F).map ιO ≫ (F).map b := by
          rw [← (F).map_comp, hb'', (F).map_comp]
        have k₁ : ((F).map q ≫ pushout.inr _ _) ≫ E.targetScheme =
            (F).map ιO ≫ (F).map a ≫ (F).map M.v := by
          rw [Category.assoc, RelationExtension.inr_target, ← Category.assoc, hq₁,
            Category.assoc, hjv, ← Category.assoc, e₁, Category.assoc]
        have k₂ : ((F).map q ≫ pushout.inr _ _) ≫ E.sourceScheme =
            (F).map ιO ≫ (F).map b ≫ (F).map M.v := by
          rw [Category.assoc, RelationExtension.inr_source, ← Category.assoc, hq₂,
            Category.assoc, hjv, ← Category.assoc, e₂, Category.assoc]
        exact ⟨(F).map q ≫ pushout.inr _ _, k₁, k₂⟩)
  have hw : ρs ≫ E.targetScheme ≫ str B S hS V' = str B S hS Y := by
    rw [← Category.assoc, hρt, Category.assoc, map_comp_str, map_comp_str]
  refine ⟨BigFppfOver.homMk B S hS E.contains_glued _ ρs hw, ?_, ?_⟩
  · exact BigFppfOver.map_toScheme_injective B S hS (by exact hρt)
  · exact BigFppfOver.map_toScheme_injective B S hS (by exact hρs)

end StageMap

end ElementaryChart

end AlgebraicGeometry.Space

end
