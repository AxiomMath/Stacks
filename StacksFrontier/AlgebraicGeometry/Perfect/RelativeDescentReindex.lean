module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineSections
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentSituationIso

/-!
# Reindexing a relative descent situation at a later stage

Let `D` be a relative descent situation in the sense of Stacks 0DI6, with inverse system `Sᵢ`,
limit `S`, fixed stage `0` and `X₀ ⟶ S₀`. For a stage `i ≥ 0` the morphism `Xᵢ ⟶ Sᵢ` is again
flat and of finite presentation, so `D.reindex i`, the same inverse system with fixed stage `i`
and `Xᵢ` in place of `X₀`, is a relative descent situation. Its stages `Xᵢ ×_{Sᵢ} Sₖ` and its
limit `Xᵢ ×_{Sᵢ} S` are `Xₖ` and `X`.

For objects `K`, `L` of `D(𝒪_{Xᵢ})`, `AlgebraicGeometry.RelativeDescentSituation.HomDescentAt`
is the statement that `colim_{k ≥ i} Hom_{D(𝒪_{Xₖ})}(Lf_{ki}^*K, Lf_{ki}^*L) ⟶
Hom_{D(𝒪_X)}(Lfᵢ^*K, Lfᵢ^*L)` is bijective, read in the stages of `D` itself; this is the
morphism set of the colimit category of Stacks 0DI8 between two objects living at stage `i`. It is
the conclusion of Stacks 0DI7 for `D.reindex i`.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.reindex`: the situation with fixed stage `i`.
* `AlgebraicGeometry.RelativeDescentSituation.HomDescentAt`: descent of derived morphism sets
  between objects at stage `i`, along the stages `k ≥ i` of `D`.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.homDescentAt_iff_reindex`: `HomDescentAt` at
  stage `i` is the conclusion of Stacks 0DI7 for `D.reindex i`.
* `AlgebraicGeometry.RelativeDescentSituation.reindex_X₀_hom`: the structure morphism of the
  fixed stage of `D.reindex i` is `Xᵢ ⟶ Sᵢ`, so relative perfectness at the fixed stage of
  `D.reindex i` is relative perfectness at stage `i` of `D`.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedPullback

variable {X Y Z : Scheme.{u}}

/-- The map on derived morphism sets attached to a factorisation depends on its first factor
only through its value. -/
theorem schemeFactorHom_congr {f f' : X ⟶ Y} (hf : f = f') (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k) (h' : f' ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    schemeFactorHom f g k h K L = schemeFactorHom f' g k h' K L := by
  subst hf
  rfl

/-- **The map on derived morphism sets attached to a factorisation whose first factor is an
isomorphism is bijective.** -/
theorem bijective_schemeFactorHom (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (f' : Y ⟶ X) (hff' : f ≫ f' = 𝟙 X) (hf'f : f' ≫ f = 𝟙 Y)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    Function.Bijective (schemeFactorHom f g k h K L) :=
  (Iso.homCongr ((schemeFactorIso f g k h).app K) ((schemeFactorIso f g k h).app L)).bijective.comp
    (bijective_derivedPullback_map f.toLRSHom.toShHom f'.toLRSHom.toShHom
      (congrArg (fun m : X ⟶ X ↦ m.toLRSHom.toShHom) hff')
      (congrArg (fun m : Y ⟶ Y ↦ m.toLRSHom.toShHom) hf'f) _ _)

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-- **The relative descent situation reindexed at a stage `i`.** The inverse system and its
limit are those of `D`, the fixed index is `i`, and the scheme over the fixed stage is
`Xᵢ ⟶ Sᵢ`, flat and of finite presentation as a base change of `X₀ ⟶ S₀`. -/
abbrev reindex (i : D.LaterIndex) : RelativeDescentSituation.{u, u} I where
  descent := { D.descent with base := i.1 }
  X₀ := Over.mk (D.structureMapAt i)
  flat := by
    have := D.flat
    exact (inferInstance : Flat (pullback.snd D.X₀.hom (D.baseMap i)))
  finitePresentation := by
    have := D.finitePresentation.locallyOfFinitePresentation
    have := D.finitePresentation.quasiCompact
    have := D.finitePresentation.quasiSeparated
    exact ⟨(inferInstance : LocallyOfFinitePresentation (pullback.snd D.X₀.hom (D.baseMap i))),
      (inferInstance : QuasiCompact (pullback.snd D.X₀.hom (D.baseMap i))),
      (inferInstance : QuasiSeparated (pullback.snd D.X₀.hom (D.baseMap i)))⟩

variable (i : D.LaterIndex)

/-- The fixed stage of `D.reindex i` is `Xᵢ`. -/
theorem reindex_X₀_left : (D.reindex i).X₀.left = D.schemeAt i :=
  rfl

/-- The structure morphism of the fixed stage of `D.reindex i` is `Xᵢ ⟶ Sᵢ`. -/
theorem reindex_X₀_hom : (D.reindex i).X₀.hom = D.structureMapAt i :=
  rfl

/-- The canonical derived-tensoring certificates of `Xᵢ ⟶ Sᵢ` are those on the inverse-image
ringed space of the structure morphism of the fixed stage of `D.reindex i`. -/
theorem canonicalStageCertificates_eq_reindex :
    D.canonicalStageCertificates i =
      RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
        (RingedSpace.inverseImage (D.descent.system.obj (op i.1)).toRingedSpace
          (D.reindex i).X₀.hom.base) :=
  rfl

/-- The stage of `D` attached to a stage `k ≥ i` of `D.reindex i`. -/
abbrev reindexLater (k : (D.reindex i).LaterIndex) : D.LaterIndex :=
  ⟨k.1, i.2.trans k.2⟩

/-- The transition morphism `f_{ki} : Xₖ ⟶ Xᵢ` of `D` for a stage `k ≥ i`. -/
abbrev reindexTransition (k : (D.reindex i).LaterIndex) :
    D.schemeAt (D.reindexLater i k) ⟶ D.schemeAt i :=
  D.transition (i := i) (j := D.reindexLater i k) k.2

/-! ### Descent of derived morphism sets between objects at a stage -/

variable (K L : DerivedCategory (SheafOfModules.{u}
  (structureSheafRing (D.schemeAt i).toRingedSpace)))

/-- The transition map `Hom(Lf_{ki}^*K, Lf_{ki}^*L) ⟶ Hom(Lf_{li}^*K, Lf_{li}^*L)` for
`i ≤ k ≤ l`, given by applying `Lf_{lk}^*`. -/
def homTransitionAt {k l : (D.reindex i).LaterIndex} (h : k.1 ≤ l.1)
    (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L) :
    (derivedPullback (D.reindexTransition i l).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i l).toLRSHom.toShHom).obj L :=
  Stacks.DerivedPullback.schemeFactorHom (D.transition (i := D.reindexLater i k)
    (j := D.reindexLater i l) h) (D.reindexTransition i k) (D.reindexTransition i l)
    (D.transition_comp_transition k.2 h) K L φ

/-- The comparison map `Hom(Lf_{ki}^*K, Lf_{ki}^*L) ⟶ Hom(Lfᵢ^*K, Lfᵢ^*L)`, given by applying
`Lfₖ^*`. -/
def homComparisonAt (k : (D.reindex i).LaterIndex)
    (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L) :
    (derivedPullback (D.projection i).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.projection i).toLRSHom.toShHom).obj L :=
  Stacks.DerivedPullback.schemeFactorHom (D.projection (D.reindexLater i k))
    (D.reindexTransition i k) (D.projection i) (D.projection_comp_transition k.2) K L φ

/-- **The morphism sets of the colimit category of Stacks 0DI8 between two objects at stage
`i`.** Every morphism `Lfᵢ^*K ⟶ Lfᵢ^*L` over the limit `X` comes from a stage `k ≥ i`, and two
morphisms at a stage `k ≥ i` with the same image over `X` agree at some later stage; that is,
`colim_{k ≥ i} Hom_{D(𝒪_{Xₖ})}(Lf_{ki}^*K, Lf_{ki}^*L) ⟶ Hom_{D(𝒪_X)}(Lfᵢ^*K, Lfᵢ^*L)` is
bijective. -/
def HomDescentAt : Prop :=
  (∀ ψ : (derivedPullback (D.projection i).toLRSHom.toShHom).obj K ⟶
        (derivedPullback (D.projection i).toLRSHom.toShHom).obj L,
      ∃ (k : (D.reindex i).LaterIndex)
        (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
          (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L),
        D.homComparisonAt i K L k φ = ψ) ∧
    ∀ (k : (D.reindex i).LaterIndex)
      (φ φ' : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
        (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L),
      D.homComparisonAt i K L k φ = D.homComparisonAt i K L k φ' →
        ∃ (l : (D.reindex i).LaterIndex) (h : k.1 ≤ l.1),
          D.homTransitionAt i K L h φ = D.homTransitionAt i K L h φ'

/-! ### The stages and the limit of the reindexed situation -/

section Stages

variable (k : (D.reindex i).LaterIndex)

/-- The square formed by `f_{ki} : Xₖ ⟶ Xᵢ`, the structure morphisms `Xₖ ⟶ Sₖ` and `Xᵢ ⟶ Sᵢ`,
and the transition morphism `Sₖ ⟶ Sᵢ` commutes. -/
theorem reindexTransition_comp_snd :
    D.reindexTransition i k ≫ pullback.snd D.X₀.hom (D.baseMap i) =
      pullback.snd D.X₀.hom (D.baseMap (D.reindexLater i k)) ≫ (D.reindex i).baseMap k :=
  pullback.lift_snd _ _ _

/-- The composite of the transition morphisms `Sₖ ⟶ Sᵢ` and `Sᵢ ⟶ S₀` is `Sₖ ⟶ S₀`. -/
theorem reindex_baseMap_comp_baseMap :
    (D.reindex i).baseMap k ≫ D.baseMap i = D.baseMap (D.reindexLater i k) :=
  (D.descent.system.map_comp _ _).symm.trans (congrArg D.descent.system.map (Subsingleton.elim _ _))

/-- The map `Xₖ ⟶ Xᵢ ×_{Sᵢ} Sₖ`. -/
def reindexStageHom : D.schemeAt (D.reindexLater i k) ⟶ (D.reindex i).schemeAt k :=
  pullback.lift (D.reindexTransition i k) (pullback.snd D.X₀.hom (D.baseMap (D.reindexLater i k)))
    (D.reindexTransition_comp_snd i k)

/-- The map `Xᵢ ×_{Sᵢ} Sₖ ⟶ Xₖ`. -/
def reindexStageInv : (D.reindex i).schemeAt k ⟶ D.schemeAt (D.reindexLater i k) :=
  pullback.lift ((D.reindex i).toFixedStage k ≫ D.toFixedStage i)
    (pullback.snd (D.reindex i).X₀.hom ((D.reindex i).baseMap k)) (by
      have hc : (D.reindex i).toFixedStage k ≫ pullback.snd D.X₀.hom (D.baseMap i) =
          pullback.snd (D.reindex i).X₀.hom ((D.reindex i).baseMap k) ≫
            (D.reindex i).baseMap k :=
        pullback.condition
      rw [Category.assoc, pullback.condition, ← Category.assoc, hc, Category.assoc,
        D.reindex_baseMap_comp_baseMap i k])

/-- The first component of `Xₖ ⟶ Xᵢ ×_{Sᵢ} Sₖ` is `f_{ki} : Xₖ ⟶ Xᵢ`. -/
theorem reindexStageHom_fst :
    D.reindexStageHom i k ≫ (D.reindex i).toFixedStage k = D.reindexTransition i k :=
  pullback.lift_fst _ _ _

/-- The second component of `Xₖ ⟶ Xᵢ ×_{Sᵢ} Sₖ` is the structure morphism `Xₖ ⟶ Sₖ`. -/
theorem reindexStageHom_snd :
    D.reindexStageHom i k ≫ pullback.snd (D.reindex i).X₀.hom ((D.reindex i).baseMap k) =
      pullback.snd D.X₀.hom (D.baseMap (D.reindexLater i k)) :=
  pullback.lift_snd _ _ _

/-- The composite of `Xᵢ ×_{Sᵢ} Sₖ ⟶ Xₖ` with `Xₖ ⟶ X₀` is the projection `Xᵢ ×_{Sᵢ} Sₖ ⟶ Xᵢ`
followed by `Xᵢ ⟶ X₀`. -/
theorem reindexStageInv_fst :
    D.reindexStageInv i k ≫ D.toFixedStage (D.reindexLater i k) =
      (D.reindex i).toFixedStage k ≫ D.toFixedStage i :=
  pullback.lift_fst _ _ _

/-- The composite of `Xᵢ ×_{Sᵢ} Sₖ ⟶ Xₖ` with `Xₖ ⟶ Sₖ` is the projection `Xᵢ ×_{Sᵢ} Sₖ ⟶ Sₖ`.
-/
theorem reindexStageInv_snd :
    D.reindexStageInv i k ≫ pullback.snd D.X₀.hom (D.baseMap (D.reindexLater i k)) =
      pullback.snd (D.reindex i).X₀.hom ((D.reindex i).baseMap k) :=
  pullback.lift_snd _ _ _

/-- The stage `Xₖ` of `D` is the stage `Xᵢ ×_{Sᵢ} Sₖ` of `D.reindex i`. -/
def reindexStageIso : D.schemeAt (D.reindexLater i k) ≅ (D.reindex i).schemeAt k where
  hom := D.reindexStageHom i k
  inv := D.reindexStageInv i k
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, D.reindexStageInv_fst, ← Category.assoc, D.reindexStageHom_fst,
        Category.id_comp]
      exact D.transition_comp_toFixedStage k.2
    · rw [Category.assoc, D.reindexStageInv_snd, D.reindexStageHom_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, D.reindexStageHom_fst, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, D.transition_comp_toFixedStage, D.reindexStageInv_fst]
      · rw [Category.assoc, D.reindexTransition_comp_snd, ← Category.assoc,
          D.reindexStageInv_snd]
        exact pullback.condition.symm
    · rw [Category.assoc, D.reindexStageHom_snd, D.reindexStageInv_snd, Category.id_comp]

/-- The forward morphism of `reindexStageIso` is `reindexStageHom`. -/
theorem reindexStageIso_hom : (D.reindexStageIso i k).hom = D.reindexStageHom i k :=
  rfl

/-- The isomorphism `Xₖ ≅ Xᵢ ×_{Sᵢ} Sₖ` followed by the projection to `Xᵢ` is `f_{ki}`. -/
theorem reindexStageIso_hom_comp_toFixedStage :
    (D.reindexStageIso i k).hom ≫ (D.reindex i).toFixedStage k = D.reindexTransition i k :=
  D.reindexStageHom_fst i k

end Stages

section Limit

/-- The map `X ⟶ Xᵢ ×_{Sᵢ} S`. -/
def reindexLimitHom : D.limitScheme ⟶ (D.reindex i).limitScheme :=
  pullback.lift (D.projection i)
    (pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)))
    (D.projection_comp_snd i)

/-- The map `Xᵢ ×_{Sᵢ} S ⟶ X`. -/
def reindexLimitInv : (D.reindex i).limitScheme ⟶ D.limitScheme :=
  pullback.lift ((D.reindex i).limitToFixedStage ≫ D.toFixedStage i)
    (pullback.snd (D.reindex i).X₀.hom (D.descent.limitCone.π.app (op i.1))) (by
      have hc : (D.reindex i).limitToFixedStage ≫ pullback.snd D.X₀.hom (D.baseMap i) =
          pullback.snd (D.reindex i).X₀.hom (D.descent.limitCone.π.app (op i.1)) ≫
            D.descent.limitCone.π.app (op i.1) :=
        pullback.condition
      rw [Category.assoc, pullback.condition, ← Category.assoc, hc, Category.assoc]
      exact congrArg (fun m => pullback.snd (D.reindex i).X₀.hom
        (D.descent.limitCone.π.app (op i.1)) ≫ m) (D.descent.limitCone.w (homOfLE i.2).op))

/-- The first component of `X ⟶ Xᵢ ×_{Sᵢ} S` is the projection `fᵢ : X ⟶ Xᵢ`. -/
theorem reindexLimitHom_fst :
    D.reindexLimitHom i ≫ (D.reindex i).limitToFixedStage = D.projection i :=
  pullback.lift_fst _ _ _

/-- The second component of `X ⟶ Xᵢ ×_{Sᵢ} S` is the structure morphism `X ⟶ S`. -/
theorem reindexLimitHom_snd :
    D.reindexLimitHom i ≫ pullback.snd (D.reindex i).X₀.hom
        (D.descent.limitCone.π.app (op i.1)) =
      pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) :=
  pullback.lift_snd _ _ _

/-- The composite of `Xᵢ ×_{Sᵢ} S ⟶ X` with `X ⟶ X₀` is the projection to `Xᵢ` followed by
`Xᵢ ⟶ X₀`. -/
theorem reindexLimitInv_fst :
    D.reindexLimitInv i ≫ D.limitToFixedStage =
      (D.reindex i).limitToFixedStage ≫ D.toFixedStage i :=
  pullback.lift_fst _ _ _

/-- The composite of `Xᵢ ×_{Sᵢ} S ⟶ X` with `X ⟶ S` is the projection `Xᵢ ×_{Sᵢ} S ⟶ S`. -/
theorem reindexLimitInv_snd :
    D.reindexLimitInv i ≫ pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) =
      pullback.snd (D.reindex i).X₀.hom (D.descent.limitCone.π.app (op i.1)) :=
  pullback.lift_snd _ _ _

/-- The limit `X` of `D` is the limit `Xᵢ ×_{Sᵢ} S` of `D.reindex i`. -/
def reindexLimitIso : D.limitScheme ≅ (D.reindex i).limitScheme where
  hom := D.reindexLimitHom i
  inv := D.reindexLimitInv i
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, D.reindexLimitInv_fst, ← Category.assoc, D.reindexLimitHom_fst,
        Category.id_comp]
      exact D.projection_comp_toFixedStage i
    · rw [Category.assoc, D.reindexLimitInv_snd, D.reindexLimitHom_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, D.reindexLimitHom_fst, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, D.projection_comp_toFixedStage, D.reindexLimitInv_fst]
      · rw [Category.assoc, D.projection_comp_snd, ← Category.assoc, D.reindexLimitInv_snd]
        exact pullback.condition.symm
    · rw [Category.assoc, D.reindexLimitHom_snd, D.reindexLimitInv_snd, Category.id_comp]

/-- The forward morphism of `reindexLimitIso` is `reindexLimitHom`. -/
theorem reindexLimitIso_hom : (D.reindexLimitIso i).hom = D.reindexLimitHom i :=
  rfl

/-- The isomorphism `X ≅ Xᵢ ×_{Sᵢ} S` followed by the projection to `Xᵢ` is `fᵢ : X ⟶ Xᵢ`. -/
theorem reindexLimitIso_hom_comp_limitToFixedStage :
    (D.reindexLimitIso i).hom ≫ (D.reindex i).limitToFixedStage = D.projection i :=
  D.reindexLimitHom_fst i

end Limit

/-- The isomorphisms `Xₖ ≅ Xᵢ ×_{Sᵢ} Sₖ` commute with the transition morphisms of `D` and of
`D.reindex i`. -/
theorem transition_comp_reindexStageIso {k l : (D.reindex i).LaterIndex} (h : k.1 ≤ l.1) :
    D.transition (i := D.reindexLater i k) (j := D.reindexLater i l) h ≫
        (D.reindexStageIso i k).hom =
      (D.reindexStageIso i l).hom ≫ (D.reindex i).transition h := by
  apply pullback.hom_ext
  · rw [D.reindexStageIso_hom, D.reindexStageIso_hom, Category.assoc, Category.assoc,
      D.reindexStageHom_fst, (D.reindex i).transition_comp_toFixedStage h, D.reindexStageHom_fst]
    exact D.transition_comp_transition k.2 h
  · rw [D.reindexStageIso_hom, D.reindexStageIso_hom, Category.assoc, Category.assoc,
      D.reindexStageHom_snd, (D.reindex i).transition_comp_snd h, ← Category.assoc,
      D.reindexStageHom_snd, D.transition_comp_snd]

/-- The isomorphisms `Xₖ ≅ Xᵢ ×_{Sᵢ} Sₖ` and `X ≅ Xᵢ ×_{Sᵢ} S` commute with the projections of
`D` and of `D.reindex i`. -/
theorem projection_comp_reindexStageIso (k : (D.reindex i).LaterIndex) :
    D.projection (D.reindexLater i k) ≫ (D.reindexStageIso i k).hom =
      (D.reindexLimitIso i).hom ≫ (D.reindex i).projection k := by
  apply pullback.hom_ext
  · rw [D.reindexStageIso_hom, D.reindexLimitIso_hom, Category.assoc, Category.assoc,
      D.reindexStageHom_fst, (D.reindex i).projection_comp_toFixedStage k, D.reindexLimitHom_fst]
    exact D.projection_comp_transition k.2
  · rw [D.reindexStageIso_hom, D.reindexLimitIso_hom, Category.assoc, Category.assoc,
      D.reindexStageHom_snd, (D.reindex i).projection_comp_snd k, ← Category.assoc,
      D.reindexLimitHom_snd, D.projection_comp_snd]

/-! ### `HomDescentAt` is Stacks 0DI7 for the reindexed situation -/

/-- Two ways of composing the maps on derived morphism sets attached to factorisations through
`Y` agree when the composites of the first two factors agree. -/
private theorem schemeFactorHom_comp_comp_eq {V W W' Y Z : Scheme.{u}} (p : V ⟶ W) (t : W ⟶ Y)
    (p' : V ⟶ W') (t' : W' ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (b' : W' ⟶ Z) (c : V ⟶ Z)
    (hb : t ≫ a = b) (hb' : t' ≫ a = b') (hpb : p ≫ b = c) (hpb' : p' ≫ b' = c)
    (hq : p ≫ t = p' ≫ t')
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback a.toLRSHom.toShHom).obj K ⟶ (derivedPullback a.toLRSHom.toShHom).obj L) :
    Stacks.DerivedPullback.schemeFactorHom p b c hpb K L
        (Stacks.DerivedPullback.schemeFactorHom t a b hb K L φ) =
      Stacks.DerivedPullback.schemeFactorHom p' b' c hpb' K L
        (Stacks.DerivedPullback.schemeFactorHom t' a b' hb' K L φ) := by
  rw [Stacks.DerivedPullback.schemeFactorHom_comp p t a b _ c hb rfl
      (by rw [Category.assoc, hb, hpb]) hpb,
    Stacks.DerivedPullback.schemeFactorHom_comp p' t' a b' _ c hb' rfl
      (by rw [Category.assoc, hb', hpb']) hpb']
  exact congrFun (Stacks.DerivedPullback.schemeFactorHom_congr hq _ _ _ _ K L) φ

/-- The bijections of derived morphism sets induced by `Xₖ ≅ Xᵢ ×_{Sᵢ} Sₖ` intertwine the
transition maps `homTransitionAt` of `D` with the transition maps `homTransition` of `D.reindex i`.
-/
theorem homTransition_reindexStageHom {k l : (D.reindex i).LaterIndex} (h : k.1 ≤ l.1)
    (φ : (derivedPullback ((D.reindex i).toFixedStage k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((D.reindex i).toFixedStage k).toLRSHom.toShHom).obj L) :
    D.homTransitionAt i K L h (Stacks.DerivedPullback.schemeFactorHom (D.reindexStageIso i k).hom
        ((D.reindex i).toFixedStage k) (D.reindexTransition i k)
        (D.reindexStageIso_hom_comp_toFixedStage i k) K L φ) =
      Stacks.DerivedPullback.schemeFactorHom (D.reindexStageIso i l).hom
        ((D.reindex i).toFixedStage l) (D.reindexTransition i l)
        (D.reindexStageIso_hom_comp_toFixedStage i l) K L
        ((D.reindex i).homTransition K L h φ) :=
  schemeFactorHom_comp_comp_eq _ _ _ _ _ _ _ _ _ _ _ _
    (D.transition_comp_reindexStageIso i h) K L φ

/-- The bijections of derived morphism sets induced by `Xₖ ≅ Xᵢ ×_{Sᵢ} Sₖ` and `X ≅ Xᵢ ×_{Sᵢ} S`
intertwine the comparison maps `homComparisonAt` of `D` with the comparison maps `homComparison`
of `D.reindex i`. -/
theorem homComparison_reindexStageHom (k : (D.reindex i).LaterIndex)
    (φ : (derivedPullback ((D.reindex i).toFixedStage k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback ((D.reindex i).toFixedStage k).toLRSHom.toShHom).obj L) :
    D.homComparisonAt i K L k (Stacks.DerivedPullback.schemeFactorHom (D.reindexStageIso i k).hom
        ((D.reindex i).toFixedStage k) (D.reindexTransition i k)
        (D.reindexStageIso_hom_comp_toFixedStage i k) K L φ) =
      Stacks.DerivedPullback.schemeFactorHom (D.reindexLimitIso i).hom
        (D.reindex i).limitToFixedStage (D.projection i)
        (D.reindexLimitIso_hom_comp_limitToFixedStage i) K L
        ((D.reindex i).homComparison K L k φ) :=
  schemeFactorHom_comp_comp_eq _ _ _ _ _ _ _ _ _ _ _ _
    (D.projection_comp_reindexStageIso i k) K L φ

/-- **`HomDescentAt` at stage `i` is the conclusion of Stacks 0DI7 for `D.reindex i`.** The
stages `Xₖ` of `D` are the stages of `D.reindex i` and the limit `X` its limit, compatibly with
the transition and projection morphisms, so the two systems of derived morphism sets and their
cocones are isomorphic. -/
theorem homDescentAt_iff_reindex :
    D.HomDescentAt i K L ↔ (D.reindex i).HomDescent K L :=
  (descent_transfer (fun k l : (D.reindex i).LaterIndex => k.1 ≤ l.1)
    (fun h => (D.reindex i).homTransition K L h) ((D.reindex i).homComparison K L)
    (fun h => D.homTransitionAt i K L h) (D.homComparisonAt i K L)
    (fun k => Stacks.DerivedPullback.schemeFactorHom (D.reindexStageIso i k).hom
      ((D.reindex i).toFixedStage k) (D.reindexTransition i k)
      (D.reindexStageIso_hom_comp_toFixedStage i k) K L)
    (Stacks.DerivedPullback.schemeFactorHom (D.reindexLimitIso i).hom
      (D.reindex i).limitToFixedStage (D.projection i)
      (D.reindexLimitIso_hom_comp_limitToFixedStage i) K L)
    (fun k => Stacks.DerivedPullback.bijective_schemeFactorHom _ _ _ _
      (D.reindexStageIso i k).inv (D.reindexStageIso i k).hom_inv_id
      (D.reindexStageIso i k).inv_hom_id K L)
    (Stacks.DerivedPullback.bijective_schemeFactorHom _ _ _ _
      (D.reindexLimitIso i).inv (D.reindexLimitIso i).hom_inv_id
      (D.reindexLimitIso i).inv_hom_id K L)
    (fun h φ => D.homTransition_reindexStageHom i K L h φ)
    (fun k φ => D.homComparison_reindexStageHom i K L k φ)).symm

/-- The conclusion of Stacks 0DI7 for `D.reindex i` gives `HomDescentAt` at stage `i`. -/
theorem homDescentAt_of_reindex (h : (D.reindex i).HomDescent K L) : D.HomDescentAt i K L :=
  (D.homDescentAt_iff_reindex i K L).2 h

end AlgebraicGeometry.RelativeDescentSituation

end
