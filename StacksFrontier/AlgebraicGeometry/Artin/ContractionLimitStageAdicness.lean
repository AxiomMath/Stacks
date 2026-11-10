module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageCoker

/-!
# Adicness descends to a stage

Let `V = lim V_k` be a cofiltered limit of affine Noetherian objects, with rings `A_k = Γ(V_k, 𝒪)`,
`A = Γ(V, 𝒪)` and ideals `I_k = I₀ A_k`, `I = I₀ A`. This file records how powers of these ideals
and their extensions to the adic completions `A_k^∧` and `A^∧` behave under the transition maps.
They feed `AlgebraicGeometry.Artin.LimitStages.exists_stage_pow_le_map`, which gives the adicness
of the formal component at a stage in the proof of Stacks 0GI5.

## Main results

* `exists_stage_res_mem_pow`: an element of `A_k` whose image in `A` lies in `I^m` already has
  image in `I_{k'}^m` at some later stage `k'`.
* `mem_map_comp_cres`: the transition map `A_{k'}^∧ → A_{k''}^∧` carries the extension of an ideal
  along `B → A_k^∧ → A_{k'}^∧` into its extension along `B → A_k^∧ → A_{k''}^∧`.
* `cres_mem_map_pow`, `cresL_mem_map_pow`: the maps `A_k^∧ → A_{k'}^∧` and `A_k^∧ → A^∧` carry
  `I_k^m A_k^∧` into `I_{k'}^m A_{k'}^∧` and `I^m A^∧` respectively.
* `exists_common_stage`: two stages below `k` have a common later stage over `k`.

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
include hκ in
/-- If the image of `e ∈ A_k` in `A` lies in `I^m`, then its image in `A_{k'}` lies in `I_{k'}^m`
for some later stage `k' ⟶ k`. -/
theorem exists_stage_res_mem_pow {k : Over k₀}
    (e : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) {m : ℕ}
    (he : resL κ k e ∈ limitIdeal (κ := κ) I₀ ^ m) :
    ∃ (k' : Over k₀) (f : k' ⟶ k), res D f e ∈ stageIdeal I₀ k' ^ m := by
  classical
  rw [← stageIdeal_map_resL I₀ k, ← Ideal.map_pow, Ideal.map, Submodule.mem_span_set'] at he
  obtain ⟨n, a, g, hsum⟩ := he
  obtain ⟨k₁, f₁, hf₁⟩ := exists_forall_finset (k := k)
    (fun (i : Fin n) {k'} (f : k' ⟶ k) =>
      ∃ t : Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤), resL κ k' t = a i)
    (fun i _ _ f h ⟨t, ht⟩ => ⟨res D h t, by
      rw [← ht, resL_res]⟩) Finset.univ
    (fun i _ => by
      obtain ⟨k', f, t, ht⟩ := exists_stage_appTop_eq_below hκ k (a i)
      exact ⟨k', f, t, ht⟩)
  choose t ht using fun i => hf₁ i (Finset.mem_univ i)
  choose y hy hyg using fun i => (g i).2
  have hzero : resL κ k₁ (res D f₁ e - ∑ i, t i * res D f₁ (y i)) = 0 := by
    rw [map_sub, map_sum, resL_res, ← hsum, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ht i, resL_res, smul_eq_mul, hyg i]
  obtain ⟨k₂, f₂, hf₂⟩ := exists_stage_appTop_eq_zero hκ _ hzero
  refine ⟨k₂, f₂ ≫ f₁, ?_⟩
  have h2 : res D f₂ (res D f₁ e) = res D f₂ (∑ i, t i * res D f₁ (y i)) := by
    rwa [map_sub, sub_eq_zero] at hf₂
  have h1 : res D (f₂ ≫ f₁) e = ∑ i, res D f₂ (t i) * res D (f₂ ≫ f₁) (y i) := by
    rw [← res_res, h2, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, res_res]
  rw [h1]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
  rw [← stageIdeal_map I₀ (f₂ ≫ f₁), ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (hy i)

omit [IsCofiltered I] hD in
/-- For `φ : B → A_k^∧`, an ideal `J ⊆ B` and stages `k'' ⟶ k' ⟶ k`, the transition map
`A_{k'}^∧ → A_{k''}^∧` sends `J A_{k'}^∧` into `J A_{k''}^∧`. -/
theorem mem_map_comp_cres {Bt : Type u} [CommRing Bt] {k k' k'' : Over k₀}
    (φ : Bt →+* AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (J : Ideal Bt) (f : k' ⟶ k) (h : k'' ⟶ k') {w} (hw : w ∈ J.map ((cres I₀ f).comp φ)) :
    cres I₀ h w ∈ J.map ((cres I₀ (h ≫ f)).comp φ) := by
  have h1 := Ideal.mem_map_of_mem (cres I₀ h) hw
  rwa [Ideal.map_map, ← RingHom.comp_assoc, cres_comp_cres] at h1

omit [IsCofiltered I] hD in
/-- For `k' ⟶ k`, the transition map `A_k^∧ → A_{k'}^∧` sends `I_k^m A_k^∧` into
`I_{k'}^m A_{k'}^∧`. -/
theorem cres_mem_map_pow {k k' : Over k₀} (f : k' ⟶ k) {m : ℕ} {x}
    (hx : x ∈ (stageIdeal I₀ k ^ m).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)))) :
    cres I₀ f x ∈ (stageIdeal I₀ k' ^ m).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k')
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤))) := by
  rw [Ideal.map_pow] at hx ⊢
  exact completionRingHom_mem_map_pow _ hx

omit [IsCofiltered I] hD in
/-- The map `A_k^∧ → A^∧` to the completion of the limit sends `I_k^m A_k^∧` into `I^m A^∧`. -/
theorem cresL_mem_map_pow (κ : Cone D) (k : Over k₀) {m : ℕ} {x}
    (hx : x ∈ (stageIdeal I₀ k ^ m).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)))) :
    cresL I₀ κ k x ∈ (limitIdeal (κ := κ) I₀ ^ m).map (algebraMap _ (AdicCompletion
      (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))) := by
  rw [Ideal.map_pow] at hx ⊢
  exact completionRingHom_mem_map_pow _ hx

/-- Two stages `f₁ : k₁ ⟶ k` and `f₂ : k₂ ⟶ k` admit a common later stage `m` with maps to `k₁`
and `k₂` whose composites to `k` agree. -/
theorem exists_common_stage {k k₁ k₂ : Over k₀} (f₁ : k₁ ⟶ k) (f₂ : k₂ ⟶ k) :
    ∃ (m : Over k₀) (e₁ : m ⟶ k₁) (e₂ : m ⟶ k₂), e₁ ≫ f₁ = e₂ ≫ f₂ := by
  obtain ⟨m', e, he⟩ := IsCofilteredOrEmpty.cone_maps (IsCofiltered.minToLeft k₁ k₂ ≫ f₁)
    (IsCofiltered.minToRight k₁ k₂ ≫ f₂)
  exact ⟨m', e ≫ IsCofiltered.minToLeft k₁ k₂, e ≫ IsCofiltered.minToRight k₁ k₂, by
    rw [Category.assoc, he, Category.assoc]⟩

end AlgebraicGeometry.Artin.LimitStages

end
