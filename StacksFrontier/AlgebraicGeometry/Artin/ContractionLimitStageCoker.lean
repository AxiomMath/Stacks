module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageInputs

/-!
# The cokernels along the descended system

For the descended system `k ↦ V'_k ⟶ V_k` of a stage witness
(`AlgebraicGeometry.Artin.LimitStages`) this file proves `Coker(A → C) = colim Coker(A_k → C_k)` in
the form used by `AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom` (its `hcoker`
input): an element of `C_k^∧` whose image in `C^∧` comes from `A^∧` comes from `A_{k₁}^∧` at a
later stage `k₁`, uniformly in the element. This is the "more algebra arguments" step of the proof
of Stacks 0GI5 for the generators `b_j`: the functions on `V'_k` whose restrictions to `V'` come
from `A` form a finite `A_k`-module, and each of its finitely many generators comes from `A_{k₁}`
at a later stage since `Γ(V', 𝒪) = colim Γ(V'_k, 𝒪)` and `A = colim A_k`.

## Main results

* `AlgebraicGeometry.Artin.LimitStages.exists_stage_mem_range_stageAlpha`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

variable {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat} {k₀ : I}
  (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]
  (W : StageWitness c κ ξ w k₀) [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  {I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)}
  (hZI₀ : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k₀).obj x ∈
    ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj).zeroLocus
      (I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)))

omit hpt in
include hκ in
/-- **`Γ(V, 𝒪) = colim Γ(V_k, 𝒪)`, surjectivity**, below a given stage. -/
theorem exists_stage_appTop_eq_below (k : Over k₀)
    (a : Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) :
    ∃ (k' : Over k₀) (_ : k' ⟶ k) (t : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)),
      resL κ k' t = a := by
  obtain ⟨k₁, t, ht⟩ := exists_stage_appTop_eq hκ a
  refine ⟨IsCofiltered.min k₁ k, IsCofiltered.minToRight k₁ k,
    res D (IsCofiltered.minToLeft k₁ k) t, (resL_res _ t).trans ht⟩

omit [IsCofiltered I] hD hpt in
/-- Restricting along `V' ⟶ V'_k` the pullback to `V'_k` of a function `t` on `V_k` gives the
pullback to `V'` of the image of `t` in `Γ(V, 𝒪)`. -/
theorem globalSectionsRingHomSite_stageA_pullbackRingHom (k : Over k₀)
    (t : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) :
    globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k)
        (pullbackRingHom B _ (spaceHom _ (stageQ W k)) t) =
      pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w)) (resL κ k t) :=
  globalSectionsRingHomSite_pullbackRingHom (stageQ W k) (limitMap κ k) (limitP w)
    (stageA W k) (stageA_q W k) t

omit [IsCofiltered I] hD hpt in
/-- Restricting along a transition map `V'_{k'} ⟶ V'_k` the pullback to `V'_k` of a function `t`
on `V_k` gives the pullback to `V'_{k'}` of the restriction of `t` to `V_{k'}`. -/
theorem globalSectionsRingHomSite_stageHom_pullbackRingHom {k k' : Over k₀} (f : k' ⟶ k)
    (t : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) :
    globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W f) : stageSpace W k' ⟶ stageSpace W k)
        (pullbackRingHom B _ (spaceHom _ (stageQ W k)) t) =
      pullbackRingHom B _ (spaceHom _ (stageQ W k')) (res D f t) :=
  globalSectionsRingHomSite_pullbackRingHom (stageQ W k) (D.map f.left).hom (stageQ W k')
    (stageHom W f) (stageHom_q W f) t

/-- The `Γ(V_k, 𝒪)`-submodule of the functions on `V'_k` whose restriction to `V'` comes from
`Γ(V, 𝒪)`. -/
def liftableFunctions (k : Over k₀) :
    Submodule Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)
      (globalFunctionsOver (D.obj k.left).obj (spaceHom _ (stageQ W k))) where
  carrier := {c' | globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) c' ∈
    (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range}
  add_mem' {a b} ha hb := by
    have ha' : globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) a ∈
      (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range := ha
    have hb' : globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) b ∈
      (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range := hb
    exact (congrArg (· ∈ (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range)
      (map_add (globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k)) a b)).mpr
      (Subring.add_mem _ ha' hb')
  zero_mem' :=
    (congrArg (· ∈ (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range)
      (map_zero (globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k)))).mpr
      (Subring.zero_mem _)
  smul_mem' r m hm := by
    have hm' : globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) m ∈
      (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range := hm
    have e := (map_mul (globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k))
        (pullbackRingHom B (D.obj k.left).obj (spaceHom _ (stageQ W k)) r) m).trans
      (congrArg (· * globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) m)
        (globalSectionsRingHomSite_stageA_pullbackRingHom W k r))
    exact (congrArg (· ∈ (pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w))).range) e).mpr
      (Subring.mul_mem _ ⟨resL κ k r, rfl⟩ hm')

/-- Restricting global functions along a morphism of spaces that factors as `f ≫ g` is restriction
along `g` followed by restriction along `f`. -/
private theorem globalSectionsRingHomSite_homMk_eq_comp {X Y Z : AlgebraicSpaces B S hS}
    {f : X.1 ⟶ Y.1} {g : Y.1 ⟶ Z.1} {h : X.1 ⟶ Z.1} (hfg : f ≫ g = h)
    (m : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS Z.1 Z.2).O))) :
    globalSectionsRingHomSite B S hS (ObjectProperty.homMk h : X ⟶ Z) m =
      globalSectionsRingHomSite B S hS (ObjectProperty.homMk f : X ⟶ Y)
        (globalSectionsRingHomSite B S hS (ObjectProperty.homMk g : Y ⟶ Z) m) := by
  rw [← hfg, ← RingHom.comp_apply, ← globalSectionsRingHomSite_comp]
  rfl

omit [IsCofiltered I] hD hpt in
/-- Restriction of global functions along the transition maps of `k ↦ V'_k` is functorial: along
the transition map of `h ≫ f` it is restriction along that of `f` followed by that of `h`. -/
theorem globalSectionsRingHomSite_stageHom_comp {k k' k'' : Over k₀} (f : k' ⟶ k) (h : k'' ⟶ k')
    (m : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O))) :
    globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W (h ≫ f)) : stageSpace W k'' ⟶ stageSpace W k) m =
      globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W h) : stageSpace W k'' ⟶ stageSpace W k')
        (globalSectionsRingHomSite B S hS
          (ObjectProperty.homMk (stageHom W f) : stageSpace W k' ⟶ stageSpace W k) m) :=
  globalSectionsRingHomSite_homMk_eq_comp (stageHom_comp W f h) m

omit [IsCofiltered I] hD hpt in
/-- Restricting a function on `V'_k` to `V'` directly agrees with restricting it first to `V'_{k'}`
along a transition map and then to `V'`. -/
theorem globalSectionsRingHomSite_stageA_stageHom {k k' : Over k₀} (f : k' ⟶ k)
    (m : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O))) :
    globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k') : limitSpace w ⟶ stageSpace W k')
        (globalSectionsRingHomSite B S hS
          (ObjectProperty.homMk (stageHom W f) : stageSpace W k' ⟶ stageSpace W k) m) =
      globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) m :=
  (globalSectionsRingHomSite_homMk_eq_comp (stageA_stageHom W f) m).symm

omit hpt in
include hκ in
/-- **A liftable function comes from `A` at a later stage** (`Coker(A → C) = colim
Coker(A_k → C_k)`, using the injectivity of `colim Γ(V'_k, 𝒪) ⟶ Γ(V', 𝒪)`). -/
theorem exists_stage_mem_range_of_mem_liftableFunctions (k : Over k₀)
    {m : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O))}
    (hm : m ∈ liftableFunctions W k) :
    ∃ (k' : Over k₀) (f : k' ⟶ k), globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W f) : stageSpace W k' ⟶ stageSpace W k) m ∈
      (pullbackRingHom B _ (spaceHom _ (stageQ W k'))).range := by
  obtain ⟨a, ha⟩ : ∃ a, pullbackRingHom B κ.pt.obj (spaceHom κ.pt.obj (limitP w)) a =
      globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) m := hm
  obtain ⟨k₁, f₁, t, ht⟩ := exists_stage_appTop_eq_below hκ k a
  have hs : globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageA W k₁) : limitSpace w ⟶ stageSpace W k₁)
        (globalSectionsRingHomSite B S hS
          (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k) m -
          pullbackRingHom B _ (spaceHom _ (stageQ W k₁)) t) = 0 := by
    rw [map_sub, globalSectionsRingHomSite_stageA_stageHom,
      globalSectionsRingHomSite_stageA_pullbackRingHom, ht, ← ha, sub_self]
  obtain ⟨k₂, f₂, hf₂⟩ := exists_stage_restrict_eq_zero hκ W _ hs
  refine ⟨k₂, f₂ ≫ f₁, res D f₂ t, ?_⟩
  rw [map_sub, sub_eq_zero, globalSectionsRingHomSite_stageHom_pullbackRingHom] at hf₂
  rw [globalSectionsRingHomSite_stageHom_comp, ← hf₂]

end AlgebraicGeometry.Artin.LimitStages

end
