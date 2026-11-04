module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageAdicness

/-!
# Adicness at a later stage

An ideal of definition of `B` generates an ideal of definition of `A_{k}^∧` at a later stage when
it does in `A^∧` (Nakayama and `A / I^{N+1} = colim A_k / I_k^{N+1}`), in the proof of Stacks 0GI5.

## Main results

* `AlgebraicGeometry.Artin.LimitStages.exists_stage_pow_le_map`: if `I^N A^∧ ⊆ J A^∧`, then
  `I_{k'}^N A_{k'}^∧ ⊆ J A_{k'}^∧` at a later stage `k'`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {k₀ : I}
  (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]
  [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  (I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤))

omit hpt in
/-- If `x` and `y` are approximated to order `M` by elements of `J A_{k'}^∧` at later stages
`k'`, then so is `x + y`. -/
theorem exists_stage_approx_add {Bt : Type u} [CommRing Bt] (k : Over k₀)
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (M : ℕ) {x y : AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)}
    (hx : ∃ (k' : Over k₀) (f : k' ⟶ k) (w : AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)),
      w ∈ J.map ((cres I₀ f).comp φ) ∧
        x - cresL I₀ κ k' w ∈ (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _
          (AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj
            κ.pt.obj, ⊤))))
    (hy : ∃ (k' : Over k₀) (f : k' ⟶ k) (w : AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)),
      w ∈ J.map ((cres I₀ f).comp φ) ∧
        y - cresL I₀ κ k' w ∈ (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _
          (AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj
            κ.pt.obj, ⊤)))) :
    ∃ (k' : Over k₀) (f : k' ⟶ k) (w : AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)),
      w ∈ J.map ((cres I₀ f).comp φ) ∧
        x + y - cresL I₀ κ k' w ∈ (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _
          (AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj
            κ.pt.obj, ⊤))) := by
  obtain ⟨k₁, f₁, w₁, hw₁, h₁⟩ := hx
  obtain ⟨k₂, f₂, w₂, hw₂, h₂⟩ := hy
  obtain ⟨m, e₁, e₂, he⟩ := exists_common_stage f₁ f₂
  refine ⟨m, e₁ ≫ f₁, cres I₀ e₁ w₁ + cres I₀ e₂ w₂, Ideal.add_mem _
    (mem_map_comp_cres I₀ φ J f₁ e₁ hw₁) (he ▸ mem_map_comp_cres I₀ φ J f₂ e₂ hw₂), ?_⟩
  rw [RingHom.map_add, cresL_cres, cresL_cres, show x + y - (cresL I₀ κ k₁ w₁ + cresL I₀ κ k₂ w₂) =
    (x - cresL I₀ κ k₁ w₁) + (y - cresL I₀ κ k₂ w₂) by ring]
  exact Ideal.add_mem _ h₁ h₂

include hκ in
/-- If `x` is approximated to order `M` by elements of `J A_{k'}^∧` at later stages `k'`, then so
is `a * x` for every `a ∈ A^∧`. -/
theorem exists_stage_approx_smul {Bt : Type u} [CommRing Bt] (k : Over k₀)
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (M : ℕ) (a : AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) {x : AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)}
    (hx : ∃ (k' : Over k₀) (f : k' ⟶ k) (w : AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)),
      w ∈ J.map ((cres I₀ f).comp φ) ∧
        x - cresL I₀ κ k' w ∈ (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _
          (AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj
            κ.pt.obj, ⊤)))) :
    ∃ (k' : Over k₀) (f : k' ⟶ k) (w : AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)),
      w ∈ J.map ((cres I₀ f).comp φ) ∧
        a * x - cresL I₀ κ k' w ∈ (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _
          (AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj
            κ.pt.obj, ⊤))) := by
  obtain ⟨k₁, f₁, w₁, hw₁, h₁⟩ := hx
  obtain ⟨a₀, ha₀⟩ := Ideal.exists_sub_algebraMap_mem_map_pow (limitIdeal (κ := κ) I₀) a M
  obtain ⟨k₂, f₂, t, ht⟩ := exists_stage_appTop_eq_below hκ k₁ a₀
  refine ⟨k₂, f₂ ≫ f₁, algebraMap _ _ t * cres I₀ f₂ w₁,
    Ideal.mul_mem_left _ _ (mem_map_comp_cres I₀ φ J f₁ f₂ hw₁), ?_⟩
  rw [RingHom.map_mul, cresL_cres, completionRingHom_algebraMap, ht,
    show a * x - algebraMap _ _ a₀ * cresL I₀ κ k₁ w₁ =
      a * (x - cresL I₀ κ k₁ w₁) + (a - algebraMap _ _ a₀) * cresL I₀ κ k₁ w₁ by ring]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_right _ _ ha₀)

include hκ in
/-- **An element of `J A^∧` is approximated to any order by elements of `J A_{k'}^∧`.** -/
theorem exists_stage_approx_mem_map {Bt : Type u} [CommRing Bt] (k : Over k₀)
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (M : ℕ) {z : AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)}
    (hz : z ∈ J.map ((cresL I₀ κ k).comp φ)) :
    ∃ (k' : Over k₀) (f : k' ⟶ k) (w : AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)),
      w ∈ J.map ((cres I₀ f).comp φ) ∧
        z - cresL I₀ κ k' w ∈ (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _
          (AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj
            κ.pt.obj, ⊤))) := by
  have hz' : z ∈ Submodule.span _ (⇑((cresL I₀ κ k).comp φ) '' (J : Set Bt)) := hz
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨k, 𝟙 k, cres I₀ (𝟙 k) (φ j), Ideal.mem_map_of_mem _ hj, ?_⟩
    rw [cresL_cres, RingHom.comp_apply, sub_self]
    exact Submodule.zero_mem _
  | zero =>
    refine ⟨k, 𝟙 k, 0, Submodule.zero_mem _, ?_⟩
    rw [RingHom.map_zero, sub_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact exists_stage_approx_add I₀ k φ J M hx hy
  | smul a x _ hx => exact exists_stage_approx_smul hκ I₀ k φ J M a hx

/-- If the image of `g` at the stage `k'` lies in `J A_{k'}^∧ + I_{k'}^{N+1} A_{k'}^∧`, then its
image at any later stage `k''` lies in `J A_{k''}^∧ + I_{k''}^{N+1} A_{k''}^∧`. -/
theorem algebraMap_res_mem_sup_of_le {Bt : Type u} [CommRing Bt] {k k' k'' : Over k₀}
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (N : ℕ) (g : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (f : k' ⟶ k) (h : k'' ⟶ k')
    (hP : algebraMap _ (AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)) (res D f g) ∈
      J.map ((cres I₀ f).comp φ) ⊔ (stageIdeal I₀ k' ^ (N + 1)).map (algebraMap _
        (AdicCompletion (stageIdeal I₀ k') Γ((BigFppfOver.toScheme B S hS).obj
          (D.obj k'.left).obj, ⊤)))) :
    algebraMap _ (AdicCompletion (stageIdeal I₀ k'')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k''.left).obj, ⊤)) (res D (h ≫ f) g) ∈
      J.map ((cres I₀ (h ≫ f)).comp φ) ⊔ (stageIdeal I₀ k'' ^ (N + 1)).map (algebraMap _
        (AdicCompletion (stageIdeal I₀ k'') Γ((BigFppfOver.toScheme B S hS).obj
          (D.obj k''.left).obj, ⊤))) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hP
  refine Submodule.mem_sup.2 ⟨cres I₀ h y, mem_map_comp_cres I₀ φ J f h hy, cres I₀ h z,
    cres_mem_map_pow I₀ h hz, ?_⟩
  rw [← RingHom.map_add, hyz, completionRingHom_algebraMap, res_res]

include hκ in
/-- An element `d` of `A_k^∧` whose image in `A^∧` lies in `I^{N+1} A^∧` lies in
`I_{k'}^{N+1} A_{k'}^∧` at a later stage. -/
theorem exists_stage_cres_mem_map_pow (k : Over k₀) (M : ℕ)
    (d : AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (hd : cresL I₀ κ k d ∈ (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _
      (AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))) :
    ∃ (k' : Over k₀) (f : k' ⟶ k), cres I₀ f d ∈ (stageIdeal I₀ k' ^ M).map (algebraMap _
      (AdicCompletion (stageIdeal I₀ k') Γ((BigFppfOver.toScheme B S hS).obj
        (D.obj k'.left).obj, ⊤))) := by
  obtain ⟨e, he⟩ := Ideal.exists_sub_algebraMap_mem_map_pow (stageIdeal I₀ k) d M
  have hce : algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) (resL κ k e) ∈
        (limitIdeal (κ := κ) I₀ ^ M).map (algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
          Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))) := by
    rw [← completionRingHom_algebraMap (resL κ k) (stageIdeal_map_limit I₀ k).le,
      show algebraMap _ _ e = d - (d - algebraMap _ _ e) by ring, RingHom.map_sub]
    exact Ideal.sub_mem _ hd (cresL_mem_map_pow I₀ κ k he)
  obtain ⟨k', f, hf⟩ := exists_stage_res_mem_pow hκ I₀ e
    (FormalSpace.mem_pow_of_algebraMap_mem_map_pow _ _ hce)
  refine ⟨k', f, ?_⟩
  rw [show d = (d - algebraMap _ _ e) + algebraMap _ _ e by ring, RingHom.map_add,
    completionRingHom_algebraMap]
  exact Ideal.add_mem _ (cres_mem_map_pow I₀ f he) (Ideal.mem_map_of_mem _ hf)

omit [IsCofiltered I] hD hpt in
/-- The image in `A^∧` of an element of `I_k^N` lies in `(I A^∧)^N`. -/
theorem algebraMap_resL_mem_map_pow {k : Over k₀} (N : ℕ)
    {g : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)}
    (hgN : g ∈ stageIdeal I₀ k ^ N) :
    algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) (resL κ k g) ∈
        ((limitIdeal (κ := κ) I₀).map (algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
          Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))) ^ N := by
  rw [← Ideal.map_pow, ← stageIdeal_map_resL I₀ k, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hgN)

omit [IsCofiltered I] hD hpt in
/-- The map `A_{k'}^∧ → A^∧` sends the difference of the image of `g ∈ A_k` and `w` to the
difference of the image of `g` in `A^∧` and the image of `w`. -/
theorem cresL_algebraMap_res_sub {k k' : Over k₀} (f : k' ⟶ k)
    (g : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (w : AdicCompletion (stageIdeal I₀ k') Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k'.left).obj, ⊤)) :
    cresL I₀ κ k' (algebraMap _ (AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)) (res D f g) - w) =
      algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
        Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) (resL κ k g) - cresL I₀ κ k' w :=
  ((cresL I₀ κ k').map_sub _ _).trans (congrArg (· - cresL I₀ κ k' w)
    ((completionRingHom_algebraMap (resL κ k') (stageIdeal_map_limit I₀ k').le (res D f g)).trans
      (congrArg (algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
        Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))) (resL_res f g))))

/-- If `w ∈ J A_{k₂}^∧` and the image of `g` minus `w` lies in `I_{k₃}^{N+1} A_{k₃}^∧` at a later
stage `k₃`, then the image of `g` at `k₃` lies in `J A_{k₃}^∧ + I_{k₃}^{N+1} A_{k₃}^∧`. -/
theorem algebraMap_res_mem_sup_of_cres_mem {Bt : Type u} [CommRing Bt] {k k₂ k₃ : Over k₀}
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (N : ℕ) (g : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (f₂ : k₂ ⟶ k) (f₃ : k₃ ⟶ k₂)
    {w : AdicCompletion (stageIdeal I₀ k₂) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k₂.left).obj, ⊤)}
    (hw : w ∈ J.map ((cres I₀ f₂).comp φ))
    (hf₃ : cres I₀ f₃ (algebraMap _ (AdicCompletion (stageIdeal I₀ k₂)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₂.left).obj, ⊤)) (res D f₂ g) - w) ∈
      (stageIdeal I₀ k₃ ^ (N + 1)).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k₃)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₃.left).obj, ⊤)))) :
    algebraMap _ (AdicCompletion (stageIdeal I₀ k₃)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₃.left).obj, ⊤)) (res D (f₃ ≫ f₂) g) ∈
      J.map ((cres I₀ (f₃ ≫ f₂)).comp φ) ⊔ (stageIdeal I₀ k₃ ^ (N + 1)).map (algebraMap _
        (AdicCompletion (stageIdeal I₀ k₃) Γ((BigFppfOver.toScheme B S hS).obj
          (D.obj k₃.left).obj, ⊤))) :=
  Submodule.mem_sup.2 ⟨cres I₀ f₃ w, mem_map_comp_cres I₀ φ J f₂ f₃ hw, _, hf₃,
    ((cres I₀ f₃).map_add _ _).symm.trans ((congrArg (cres I₀ f₃) (add_sub_cancel w _)).trans
      ((completionRingHom_algebraMap (res D f₃) (stageIdeal_map_le I₀ f₃) (res D f₂ g)).trans
        (congrArg (algebraMap _ (AdicCompletion (stageIdeal I₀ k₃)
          Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₃.left).obj, ⊤))) (res_res f₂ f₃ g))))⟩

include hκ in
/-- Each element of `I_k^N` lies in `J A_{k'}^∧ + I_{k'}^{N+1} A_{k'}^∧` at a later stage. -/
theorem exists_stage_algebraMap_res_mem_sup {Bt : Type u} [CommRing Bt] (k : Over k₀)
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (N : ℕ)
    (hlim : ((limitIdeal (κ := κ) I₀).map (algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))) ^ N ≤ J.map ((cresL I₀ κ k).comp φ))
    (g : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (hgN : g ∈ stageIdeal I₀ k ^ N) :
    ∃ (k' : Over k₀) (f : k' ⟶ k), algebraMap _ (AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)) (res D f g) ∈
      J.map ((cres I₀ f).comp φ) ⊔ (stageIdeal I₀ k' ^ (N + 1)).map (algebraMap _
        (AdicCompletion (stageIdeal I₀ k') Γ((BigFppfOver.toScheme B S hS).obj
          (D.obj k'.left).obj, ⊤))) := by
  obtain ⟨k₂, f₂, w, hw, hzw⟩ := exists_stage_approx_mem_map hκ I₀ k φ J (N + 1)
    (hlim (algebraMap_resL_mem_map_pow I₀ N hgN))
  obtain ⟨k₃, f₃, hf₃⟩ := exists_stage_cres_mem_map_pow hκ I₀ k₂ (N + 1) _
    ((congrArg (· ∈ (limitIdeal (κ := κ) I₀ ^ (N + 1)).map (algebraMap _ (AdicCompletion
      (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))))
      (cresL_algebraMap_res_sub I₀ f₂ g w)).mpr hzw)
  exact ⟨k₃, f₃ ≫ f₂, algebraMap_res_mem_sup_of_cres_mem I₀ φ J N g f₂ f₃ hw hf₃⟩

omit [IsCofiltered I] in
/-- **Nakayama at a stage**: if the images of generators of `I_k^N` lie in
`J A_{k₁}^∧ + I_{k₁}^{N+1} A_{k₁}^∧`, then `I_{k₁}^N A_{k₁}^∧ ⊆ J A_{k₁}^∧`. -/
theorem pow_le_map_of_forall_mem_sup {Bt : Type u} [CommRing Bt] {k k₁ : Over k₀}
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (N : ℕ) (f₁ : k₁ ⟶ k) (G : Finset Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (hG : Ideal.span (G : Set _) = stageIdeal I₀ k ^ N)
    (hf₁ : ∀ g ∈ G, algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤)) (res D f₁ g) ∈
      J.map ((cres I₀ f₁).comp φ) ⊔ (stageIdeal I₀ k₁ ^ (N + 1)).map (algebraMap _
        (AdicCompletion (stageIdeal I₀ k₁) Γ((BigFppfOver.toScheme B S hS).obj
          (D.obj k₁.left).obj, ⊤)))) :
    ((stageIdeal I₀ k₁).map (algebraMap _ (AdicCompletion
        (stageIdeal I₀ k₁) Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤)))) ^ N ≤
      J.map ((cres I₀ f₁).comp φ) := by
  have e1 : stageIdeal I₀ k₁ ^ N = (stageIdeal I₀ k ^ N).map (res D f₁) := by
    rw [Ideal.map_pow, stageIdeal_map]
  have e2 : ((stageIdeal I₀ k₁).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤)))) ^ N =
      Ideal.span ((fun g => algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
        Γ((BigFppfOver.toScheme B S hS).obj
          (D.obj k₁.left).obj, ⊤)) (res D f₁ g)) '' (G : Set _)) := by
    rw [← Ideal.map_pow, e1, ← hG, Ideal.map_span, Ideal.map_span, Set.image_image]
  have e3 : (stageIdeal I₀ k₁).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤))) •
        ((stageIdeal I₀ k₁).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
          Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤)))) ^ N =
      (stageIdeal I₀ k₁ ^ (N + 1)).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤))) := by
    rw [Ideal.smul_eq_mul, ← pow_succ', Ideal.map_pow]
  have hle : ((stageIdeal I₀ k₁).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤)))) ^ N ≤
      J.map ((cres I₀ f₁).comp φ) ⊔ (stageIdeal I₀ k₁).map (algebraMap _ (AdicCompletion
        (stageIdeal I₀ k₁) Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤))) •
        ((stageIdeal I₀ k₁).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k₁)
          Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₁.left).obj, ⊤)))) ^ N := by
    rw [e3, e2, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hf₁ g hg
  have := AdicCompletion.isAdicComplete_self (stageIdeal I₀ k₁)
    (stageIdeal I₀ k₁).fg_of_isNoetherianRing
  exact Submodule.le_of_le_smul_of_le_jacobson_bot
    (((stageIdeal I₀ k₁).fg_of_isNoetherianRing.map _).pow) (IsAdicComplete.le_jacobson_bot _) hle

include hκ in
/-- **Adicness descends to a stage**: if `I^N A^∧ ⊆ J A^∧` for the image `φ` in `A^∧` of
`φ_k : B → A_k^∧`, then `I_{k'}^N A_{k'}^∧ ⊆ J A_{k'}^∧` at a later stage. -/
theorem exists_stage_pow_le_map {Bt : Type u} [CommRing Bt] (k : Over k₀)
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj
      (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (N : ℕ)
    (hlim : ((limitIdeal (κ := κ) I₀).map (algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))) ^ N ≤ J.map ((cresL I₀ κ k).comp φ)) :
    ∃ (k' : Over k₀) (f : k' ⟶ k), ((stageIdeal I₀ k').map (algebraMap _ (AdicCompletion
        (stageIdeal I₀ k') Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)))) ^ N ≤
      J.map ((cres I₀ f).comp φ) := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (stageIdeal I₀ k ^ N) :
    (stageIdeal I₀ k ^ N).FG)
  obtain ⟨k₁, f₁, hf₁⟩ := exists_forall_finset (k := k)
    (fun (g : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) {k'} (f : k' ⟶ k) =>
      algebraMap _ (AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)) (res D f g) ∈
          J.map ((cres I₀ f).comp φ) ⊔ (stageIdeal I₀ k' ^ (N + 1)).map (algebraMap _
            (AdicCompletion (stageIdeal I₀ k') Γ((BigFppfOver.toScheme B S hS).obj
              (D.obj k'.left).obj, ⊤))))
    (fun g _ _ f h hP => algebraMap_res_mem_sup_of_le I₀ φ J N g f h hP) G
    (fun g hg => exists_stage_algebraMap_res_mem_sup hκ I₀ k φ J N hlim g
      (hG ▸ Submodule.subset_span hg))
  exact ⟨k₁, f₁, pow_le_map_of_forall_mem_sup I₀ φ J N f₁ G hG hf₁⟩

end AlgebraicGeometry.Artin.LimitStages

end
