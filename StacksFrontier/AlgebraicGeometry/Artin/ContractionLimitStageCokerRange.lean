module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageCoker

/-!
# The cokernel input of the lifting argument

The `hcoker` input of `AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom` for the
descended system of a stage witness in the proof of Stacks 0GI5.

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

/-- If the images of generators of the liftable functions on `V'_k` come from `A_{k₁}`, so do the
images of all liftable functions. -/
theorem mem_range_of_mem_liftableFunctions_of_span {k k₁ : Over k₀} (f₁ : k₁ ⟶ k)
    (G : Set (globalFunctionsOver (D.obj k.left).obj (spaceHom _ (stageQ W k))))
    (hG : Submodule.span _ G = liftableFunctions W k)
    (hf₁ : ∀ m ∈ G, globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k) m ∈
        (pullbackRingHom B _ (spaceHom _ (stageQ W k₁))).range) :
    ∀ m ∈ liftableFunctions W k, globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k) m ∈
        (pullbackRingHom B _ (spaceHom _ (stageQ W k₁))).range := by
  rw [← hG]
  intro m hm
  let R := (pullbackRingHom B _ (spaceHom _ (stageQ W k₁))).range.comap
    (globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k))
  induction hm using Submodule.span_induction with
  | mem x hx => exact hf₁ x hx
  | zero => exact R.zero_mem
  | add x y _ _ hx hy => exact R.add_mem hx hy
  | smul r x _ hx =>
    have e := (RingHom.map_mul (globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k))
      (pullbackRingHom B (D.obj k.left).obj (spaceHom _ (stageQ W k)) r) x).trans
      (congrArg (· * (globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k)) x)
        (globalSectionsRingHomSite_stageHom_pullbackRingHom W f₁ r))
    exact (congrArg (· ∈ (pullbackRingHom B _ (spaceHom _ (stageQ W k₁))).range) e).mpr
      (Subring.mul_mem _ ⟨res D f₁ r, rfl⟩ hx)

include hκ in
/-- **The liftable functions come from `A_{k₁}` at a single later stage** (they form a finite
`Γ(V_k, 𝒪)`-module). -/
theorem exists_stage_forall_mem_liftableFunctions (k : Over k₀) :
    ∃ (k₁ : Over k₀) (f₁ : k₁ ⟶ k), ∀ m : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O)),
      m ∈ liftableFunctions W k → globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k) m ∈
        (pullbackRingHom B _ (spaceHom _ (stageQ W k₁))).range := by
  have := moduleFinite_globalFunctionsOver_of_isProper (D.obj k.left).obj
    (spaceHom _ (stageQ W k)) (isProper_stageQ W k)
  have := isNoetherian_of_isNoetherianRing_of_finite
    Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)
    (globalFunctionsOver (D.obj k.left).obj (spaceHom _ (stageQ W k)))
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian (liftableFunctions W k)
  obtain ⟨k₁, f₁, hf₁⟩ := exists_forall_finset (k := k)
    (fun (m : globalFunctionsOver (D.obj k.left).obj (spaceHom _ (stageQ W k))) {k'} (f : k' ⟶ k) =>
      globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W f) : stageSpace W k' ⟶ stageSpace W k) m ∈
      (pullbackRingHom B _ (spaceHom _ (stageQ W k'))).range)
    (fun m _ _ f h hm => by
      obtain ⟨t, ht⟩ := hm
      exact ⟨res D h t, ((globalSectionsRingHomSite_stageHom_pullbackRingHom W h t).symm.trans
        (congrArg _ ht)).trans (globalSectionsRingHomSite_stageHom_comp W f h m).symm⟩) G
    (fun m hm => exists_stage_mem_range_of_mem_liftableFunctions hκ W k
      (hG ▸ Submodule.subset_span hm))
  exact ⟨k₁, f₁, fun m hm => mem_range_of_mem_liftableFunctions_of_span W f₁ G hG hf₁ m hm⟩

include hZI₀ in
/-- If `c = α(x) + c'` in `C_k^∧` and the image of `c` in `C^∧` comes from `A^∧`, then `c'` is
liftable. -/
theorem mem_liftableFunctions_of_mem_range (k : Over k₀)
    (c : towerRing (stageIdeal I₀ k) (stageQ W k))
    (x : AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (c' : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O)))
    (hxc : c = alpha (stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k) x +
      towerOf (stageIdeal I₀ k) (stageQ W k) c')
    (hc : towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
          (stageA W k) (stageA_q W k) c ∈ Set.range (limitAlpha W hZI₀)) :
    c' ∈ liftableFunctions W k := by
  obtain ⟨Nl, -, hQl⟩ := limit_torsion W hZI₀
  obtain ⟨y, hy⟩ := hc
  have hTL := congrArg (fun φ => φ c') (towerRingMap_comp_towerOf (stageQ W k) (limitMap κ k)
    (stageIdeal_map_limit I₀ k).le (limitP w) (stageA W k) (stageA_q W k))
  have hAL := congrArg (fun φ => φ x) (limitAlpha_comp_completionRingHom W hZI₀ k)
  refine exists_pullbackRingHom_eq_of_towerOf_eq_alpha (limitP w) w.isProper_p
    (limit_hZI hZI₀) (limit_hqc (I₀ := I₀) (w := w)) (N := Nl) hQl (x := y - cresL I₀ κ k x) ?_
  have h1 : towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
      (stageA W k) (stageA_q W k) c = limitAlpha W hZI₀ (cresL I₀ κ k x) +
        towerOf (limitIdeal (κ := κ) I₀) (limitP w) (globalSectionsRingHomSite B S hS
          (ObjectProperty.homMk (stageA W k) : limitSpace w ⟶ stageSpace W k) c') := by
    refine ((congrArg (towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k)
      (limitP w) (stageA W k) (stageA_q W k)) hxc).trans (RingHom.map_add _ _ _)).trans ?_
    exact congrArg₂ (· + ·) hAL.symm hTL
  exact (eq_sub_of_add_eq' (hy.trans h1).symm).trans
    ((limitAlpha W hZI₀).map_sub y (cresL I₀ κ k x)).symm

/-- If `c = α(x) + c'` in `C_k^∧` and the image of `c'` on `V'_{k₁}` comes from `A_{k₁}`, then the
image of `c` in `C_{k₁}^∧` comes from `A_{k₁}^∧`. -/
theorem mem_range_stageAlpha_of_decomposition {k k₁ : Over k₀} (f₁ : k₁ ⟶ k)
    (c : towerRing (stageIdeal I₀ k) (stageQ W k))
    (x : AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (c' : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O)))
    (hxc : c = alpha (stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k) x +
      towerOf (stageIdeal I₀ k) (stageQ W k) c')
    (t : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤))
    (ht : pullbackRingHom B _ (spaceHom _ (stageQ W k₁)) t = globalSectionsRingHomSite B S hS
      (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k) c') :
    towerRingMap (D.map f₁.left).hom (stageIdeal_map_le I₀ f₁) (stageQ W k) (stageQ W k₁)
      (stageHom W f₁) (stageHom_q W f₁) c ∈ Set.range (stageAlpha W hZI₀ k₁) := by
  refine ⟨cres I₀ f₁ x + algebraMap _ _ t, ?_⟩
  have hTk := congrArg (fun φ => φ c') (towerRingMap_comp_towerOf (stageQ W k) (D.map f₁.left).hom
    (stageIdeal_map_le I₀ f₁) (stageQ W k₁) (stageHom W f₁) (stageHom_q W f₁))
  have hAk := congrArg (fun φ => φ x) (towerRingMap_comp_alpha (stageQ W k) (stage_hZI hZI₀ k)
      (stage_hqc W k) (D.map f₁.left).hom (stageIdeal_map_le I₀ f₁) (stageQ W k₁) (stageHom W f₁)
      (stageHom_q W f₁) (stage_hZI hZI₀ k₁) (stage_hqc W k₁))
  have hτ := alpha_algebraMap (stageQ W k₁) (stage_hZI hZI₀ k₁) (stage_hqc W k₁) t
  refine ((stageAlpha W hZI₀ k₁).map_add _ _).trans ((congrArg₂ (· + ·) hAk.symm
    (hτ.trans ((congrArg (towerOf (stageIdeal I₀ k₁) (stageQ W k₁)) ht).trans hTk.symm))).trans ?_)
  exact ((congrArg (towerRingMap (D.map f₁.left).hom (stageIdeal_map_le I₀ f₁) (stageQ W k)
    (stageQ W k₁) (stageHom W f₁) (stageHom_q W f₁)) hxc).trans (RingHom.map_add _ _ _)).symm

include hZI₀ in
/-- If the liftable functions on `V'_k` come from `A_{k₁}`, then every element of `C_k^∧` whose
image in `C^∧` comes from `A^∧` has image in `C_{k₁}^∧` coming from `A_{k₁}^∧`. -/
theorem mem_range_stageAlpha_of_forall {k k₁ : Over k₀} (f₁ : k₁ ⟶ k)
    (hall : ∀ m : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS (stageSpace W k).1 (stageSpace W k).2).O)),
      m ∈ liftableFunctions W k → globalSectionsRingHomSite B S hS
        (ObjectProperty.homMk (stageHom W f₁) : stageSpace W k₁ ⟶ stageSpace W k) m ∈
          (pullbackRingHom B _ (spaceHom _ (stageQ W k₁))).range)
    (c : towerRing (stageIdeal I₀ k) (stageQ W k))
    (hc : towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
      (stageA W k) (stageA_q W k) c ∈ Set.range (limitAlpha W hZI₀)) :
    towerRingMap (D.map f₁.left).hom (stageIdeal_map_le I₀ f₁) (stageQ W k) (stageQ W k₁)
      (stageHom W f₁) (stageHom_q W f₁) c ∈ Set.range (stageAlpha W hZI₀ k₁) := by
  obtain ⟨Nk, -, hQk⟩ := stage_torsion W hZI₀ k
  obtain ⟨x, c', hxc⟩ := exists_eq_alpha_add_towerOf (V := (D.obj k.left).obj)
    (I := stageIdeal I₀ k) (X := stageSpace W k) (Z := (W.baseChange k.hom).Z)
    (stageQ W k) (isProper_stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k) (N := Nk) hQk c
  obtain ⟨t, ht⟩ := hall c' (mem_liftableFunctions_of_mem_range W hZI₀ k c x c' hxc hc)
  exact mem_range_stageAlpha_of_decomposition W hZI₀ f₁ c x c' hxc t ht

include hκ hZI₀ in
/-- **`Coker(A → C) = colim Coker(A_k → C_k)`**, in the form used by the lifting argument (the
`hcoker` input of `AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom`). -/
theorem exists_stage_mem_range_stageAlpha (k : Over k₀) :
    ∃ (k₁ : Over k₀) (f₁ : k₁ ⟶ k), ∀ c : towerRing (stageIdeal I₀ k) (stageQ W k),
      towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
          (stageA W k) (stageA_q W k) c ∈ Set.range (limitAlpha W hZI₀) →
        towerRingMap (D.map f₁.left).hom (stageIdeal_map_le I₀ f₁) (stageQ W k) (stageQ W k₁)
          (stageHom W f₁) (stageHom_q W f₁) c ∈ Set.range (stageAlpha W hZI₀ k₁) :=
  (exists_stage_forall_mem_liftableFunctions hκ W k).elim fun k₁ ⟨f₁, hall⟩ =>
    ⟨k₁, f₁, mem_range_stageAlpha_of_forall W hZI₀ f₁ hall⟩

end AlgebraicGeometry.Artin.LimitStages

end
