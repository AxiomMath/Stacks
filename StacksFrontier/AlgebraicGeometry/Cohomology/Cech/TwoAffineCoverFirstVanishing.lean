module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# First cohomology on the union of two affine opens

Let `U₀` and `U₁` be affine opens of a scheme whose intersection is affine, and let `ℱ` be a
quasi-coherent module. By [Stacks, Tag 01XD] the cohomology of `ℱ` over `U₀ ∪ U₁` is the Čech
cohomology of the covering `{U₀, U₁}`, and in degree one a Čech cocycle is determined by its value
on `U₀ ∩ U₁`, up to coboundaries. So `H¹(U₀ ∪ U₁, ℱ) = 0` as soon as every section of `ℱ` over
`U₀ ∩ U₁` is a difference of restrictions of sections over `U₁` and over `U₀`.

## Main results

* `Stacks.Cohomology.TwoCover.isZero_Hgroup_one_of_surjective`: the vanishing criterion above.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01ED](https://stacks.math.columbia.edu/tag/01ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf Stacks.Cohomology.Basis

universe u

namespace Stacks.Cohomology.TwoCover

variable {Y : Scheme.{u}} (U₀ U₁ : Y.Opens)

/-- The covering `{U₀, U₁}`, indexed by `ULift (Fin 2)`. -/
def pairCover : ULift.{u} (Fin 2) → Y.Opens := fun i => ![U₀, U₁] i.down

/-- The first index. -/
abbrev i₀ : ULift.{u} (Fin 2) := ⟨0⟩

/-- The second index. -/
abbrev i₁ : ULift.{u} (Fin 2) := ⟨1⟩

/-- The member of `pairCover U₀ U₁` at index `i₀` is `U₀`. -/
@[simp] theorem pairCover_i₀ : pairCover U₀ U₁ i₀ = U₀ := rfl

/-- The member of `pairCover U₀ U₁` at index `i₁` is `U₁`. -/
@[simp] theorem pairCover_i₁ : pairCover U₀ U₁ i₁ = U₁ := rfl

/-- Every index in `ULift (Fin 2)` is `i₀` or `i₁`. -/
theorem eq_i₀_or_eq_i₁ (i : ULift.{u} (Fin 2)) : i = i₀ ∨ i = i₁ := by
  obtain ⟨j⟩ := i
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The union of the members of `pairCover U₀ U₁` is `U₀ ⊔ U₁`. -/
theorem iSup_pairCover : U₀ ⊔ U₁ = ⨆ i, pairCover U₀ U₁ i := by
  refine le_antisymm (sup_le (le_iSup_of_le i₀ le_rfl) (le_iSup_of_le i₁ le_rfl)) ?_
  refine iSup_le fun i => ?_
  rcases eq_i₀_or_eq_i₁ i with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

/-- A finite intersection of members of `{U₀, U₁}` is `U₀`, `U₁` or `U₀ ∩ U₁`. -/
theorem iInf_pairCover {r : ℕ} (s : Fin (r + 1) → ULift.{u} (Fin 2)) :
    (⨅ k, pairCover U₀ U₁ (s k)) = U₀ ∨ (⨅ k, pairCover U₀ U₁ (s k)) = U₁ ∨
      (⨅ k, pairCover U₀ U₁ (s k)) = U₀ ⊓ U₁ := by
  by_cases h0 : ∃ k, s k = i₀
  · by_cases h1 : ∃ k, s k = i₁
    · obtain ⟨k₀, hk₀⟩ := h0
      obtain ⟨k₁, hk₁⟩ := h1
      refine Or.inr (Or.inr (le_antisymm (le_inf ?_ ?_) (le_iInf fun k => ?_)))
      · exact iInf_le_of_le k₀ (hk₀ ▸ le_rfl)
      · exact iInf_le_of_le k₁ (hk₁ ▸ le_rfl)
      · rcases eq_i₀_or_eq_i₁ (s k) with h | h <;> rw [h]
        · exact inf_le_left
        · exact inf_le_right
    · push Not at h1
      obtain ⟨k₀, hk₀⟩ := h0
      refine Or.inl (le_antisymm (iInf_le_of_le k₀ (hk₀ ▸ le_rfl))
        (le_iInf fun k => ?_))
      rcases eq_i₀_or_eq_i₁ (s k) with h | h
      · exact h ▸ le_rfl
      · exact absurd h (h1 k)
  · push Not at h0
    refine Or.inr (Or.inl (le_antisymm (iInf_le_of_le 0 ?_) (le_iInf fun k => ?_)))
    · rcases eq_i₀_or_eq_i₁ (s 0) with h | h
      · exact absurd h (h0 0)
      · exact h ▸ le_rfl
    · rcases eq_i₀_or_eq_i₁ (s k) with h | h
      · exact absurd h (h0 k)
      · exact h ▸ le_rfl

/-- If `U₀`, `U₁` and `U₀ ⊓ U₁` are affine, then every nonempty finite intersection of members
of `pairCover U₀ U₁` is affine. -/
theorem isAffineOpen_iInf_pairCover (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
    (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) {r : ℕ} (s : Fin (r + 1) → ULift.{u} (Fin 2)) :
    IsAffineOpen (⨅ k, pairCover U₀ U₁ (s k)) := by
  rcases iInf_pairCover U₀ U₁ s with h | h | h <;> rw [h]
  · exact h₀
  · exact h₁
  · exact h₀₁

/-- The tuple `(i, j)`. -/
abbrev tup (i j : ULift.{u} (Fin 2)) : Fin 2 → ULift.{u} (Fin 2) := ![i, j]

/-- Every map `Fin 2 → ULift (Fin 2)` is the tuple of its two values. -/
theorem eq_tup (x : Fin 2 → ULift.{u} (Fin 2)) : x = tup (x 0) (x 1) := by
  funext k
  fin_cases k <;> rfl

/-- The intersection of `pairCover U₀ U₁` along `tup i j` is the intersection of the members at
`i` and at `j`. -/
theorem inter_tup (i j : ULift.{u} (Fin 2)) :
    inter (pairCover U₀ U₁) (tup i j) = pairCover U₀ U₁ i ⊓ pairCover U₀ U₁ j := by
  rw [inter_eq_iInf]
  refine le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1)) (le_iInf fun k => ?_)
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

/-- The intersection of `pairCover U₀ U₁` along a one-element tuple `y` is the member at `y 0`. -/
theorem inter_one (y : Fin 1 → ULift.{u} (Fin 2)) :
    inter (pairCover U₀ U₁) y = pairCover U₀ U₁ (y 0) := by
  rw [inter_eq_iInf]
  refine le_antisymm (iInf_le _ 0) (le_iInf fun k => ?_)
  fin_cases k
  exact le_rfl

variable {U₀ U₁} (F : Y.Modules) [F.IsQuasicoherent]

/-- **`H¹(U₀ ∪ U₁, ℱ) = 0` when sections over `U₀ ∩ U₁` split.** If `U₀`, `U₁` and `U₀ ∩ U₁`
are affine and every section of the quasi-coherent module `ℱ` over `U₀ ∩ U₁` is the restriction
of a section over `U₁` minus the restriction of a section over `U₀`, then `H¹(U₀ ∪ U₁, ℱ) = 0`. -/
theorem isZero_Hgroup_one_of_surjective (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
    (h₀₁ : IsAffineOpen (U₀ ⊓ U₁))
    (hsurj : ∀ c : ToType ((abSections F).obj (op (U₀ ⊓ U₁))),
      ∃ (a : ToType ((abSections F).obj (op U₀))) (b : ToType ((abSections F).obj (op U₁))),
        c = res (abSections F) inf_le_right b - res (abSections F) inf_le_left a) :
    IsZero (Hgroup Y.ringCatSheaf (U₀ ⊔ U₁) 1 F) := by
  rw [Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology Y (U₀ ⊔ U₁)
    (pairCover U₀ U₁) (iSup_pairCover U₀ U₁)
    (fun r s => isAffineOpen_iInf_pairCover U₀ U₁ h₀ h₁ h₀₁ s) F 1]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
  intro s hs
  set V := U₀ ⊔ U₁
  set U := pairCover U₀ U₁
  have hU := iSup_pairCover U₀ U₁
  have hs' : md V U hU F s = 0 := hs
  have hinf : ∀ {m : ℕ} (y : Fin m → ULift.{u} (Fin 2)), U₀ ⊓ U₁ ≤ inter U y := fun y => by
    rw [inter_eq_iInf]
    refine le_iInf fun k => ?_
    rcases eq_i₀_or_eq_i₁ (y k) with h | h
    · exact h ▸ inf_le_left
    · exact h ▸ inf_le_right
  have h01 := hinf (tup i₀ i₁)
  obtain ⟨a, b, hab⟩ := hsurj (res (abSections F) h01 (mcomp V U hU F s (tup i₀ i₁)))
  let g : ∀ y : Fin 1 → ULift.{u} (Fin 2), ToType ((abSections F).obj (op (inter U y))) := fun y =>
    if hy : y 0 = i₀ then
      res (abSections F) ((inter_one U₀ U₁ y).le.trans (hy ▸ le_rfl)) a
    else
      res (abSections F) ((inter_one U₀ U₁ y).le.trans
        ((eq_i₀_or_eq_i₁ (y 0)).resolve_left hy ▸ le_rfl)) b
  refine ⟨mmk V U hU F g, ?_⟩
  show md V U hU F (mmk V U hU F g) = s
  have hcoc : ∀ (y : Fin 3 → ULift.{u} (Fin 2)) {W : Y.Opens} (hW : W ≤ inter U y),
      res (abSections F) (hW.trans (inter_le_reindex U y (Fin.succAbove 0)))
          (mcomp V U hU F s (y ∘ Fin.succAbove 0)) -
        res (abSections F) (hW.trans (inter_le_reindex U y (Fin.succAbove 1)))
          (mcomp V U hU F s (y ∘ Fin.succAbove 1)) +
        res (abSections F) (hW.trans (inter_le_reindex U y (Fin.succAbove 2)))
          (mcomp V U hU F s (y ∘ Fin.succAbove 2)) = 0 := by
    intro y W hW
    have h := sum_res_mcomp_eq_zero V U hU F s hs' y hW
    rw [Fin.sum_univ_three] at h
    simpa [sub_eq_add_neg] using h
  have hdiag : ∀ i : ULift.{u} (Fin 2), mcomp V U hU F s (tup i i) = 0 := by
    intro i
    have h := hcoc ![i, i, i] (W := inter U (tup i i)) (by
      rw [inter_eq_iInf, inter_eq_iInf]
      exact le_iInf fun k => iInf_le_of_le 0 (by fin_cases k <;> exact le_rfl))
    have e : ∀ a : Fin 3, (![i, i, i] : Fin 3 → ULift.{u} (Fin 2)) ∘ Fin.succAbove a =
        tup i i := fun a => by funext k; fin_cases a <;> fin_cases k <;> rfl
    rw [res_mcomp_congr V U hU F s (e 0) _ le_rfl, res_mcomp_congr V U hU F s (e 1) _ le_rfl,
      res_mcomp_congr V U hU F s (e 2) _ le_rfl, res_id, sub_self, zero_add] at h
    exact h
  have h10 := hinf (tup i₁ i₀)
  have hanti : res (abSections F) h10 (mcomp V U hU F s (tup i₁ i₀)) =
      -res (abSections F) h01 (mcomp V U hU F s (tup i₀ i₁)) := by
    have h := hcoc ![i₀, i₁, i₀] (hinf _)
    have e0 : (![i₀, i₁, i₀] : Fin 3 → ULift.{u} (Fin 2)) ∘ Fin.succAbove 0 = tup i₁ i₀ := by
      funext k; fin_cases k <;> rfl
    have e1 : (![i₀, i₁, i₀] : Fin 3 → ULift.{u} (Fin 2)) ∘ Fin.succAbove 1 = tup i₀ i₀ := by
      funext k; fin_cases k <;> rfl
    have e2 : (![i₀, i₁, i₀] : Fin 3 → ULift.{u} (Fin 2)) ∘ Fin.succAbove 2 = tup i₀ i₁ := by
      funext k; fin_cases k <;> rfl
    rw [res_mcomp_congr V U hU F s e0 _ h10, res_mcomp_congr V U hU F s e1 _ (hinf _),
      res_mcomp_congr V U hU F s e2 _ h01, hdiag, res_zero, sub_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hinj : ∀ {W W' : Y.Opens} (e : W = W'), Function.Injective (res (abSections F) e.ge) := by
    intro W W' e x y h
    have h' := congrArg (res (abSections F) e.le) h
    rwa [res_res, res_res, res_id, res_id] at h'
  have hne : (i₁ : ULift.{u} (Fin 2)) ≠ i₀ := by decide
  refine mcech_ext V U hU F _ _ fun x => ?_
  obtain ⟨c₀, c₁, rfl⟩ : ∃ c₀ c₁, x = tup c₀ c₁ := ⟨_, _, eq_tup x⟩
  rw [mcomp_md V U hU F (mmk V U hU F g) (tup c₀ c₁), Fin.sum_univ_two,
    mcomp_mmk V U hU F g, mcomp_mmk V U hU F g]
  have t0 : (tup c₀ c₁ ∘ Fin.succAbove 0) 0 = c₁ := rfl
  have t1 : (tup c₀ c₁ ∘ Fin.succAbove 1) 0 = c₀ := rfl
  rcases eq_i₀_or_eq_i₁ c₀ with rfl | rfl <;> rcases eq_i₀_or_eq_i₁ c₁ with rfl | rfl
  · simp only [g, dif_pos t0, dif_pos t1]
    rw [hdiag, res_res, res_res]
    simp only [pow_zero, pow_one, one_smul, neg_smul, Fin.val_zero, Fin.val_one]
    exact add_neg_cancel _
  · simp only [g, dif_neg (t0.trans_ne hne), dif_pos t1]
    rw [res_res, res_res]
    simp only [pow_zero, pow_one, one_smul, neg_smul, Fin.val_zero, Fin.val_one,
      ← sub_eq_add_neg]
    refine hinj (inter_tup U₀ U₁ i₀ i₁) ?_
    refine Eq.trans ?_ hab.symm
    rw [res_sub, res_res, res_res]
    rfl
  · simp only [g, dif_pos t0, dif_neg (t1.trans_ne hne)]
    rw [res_res, res_res]
    simp only [pow_zero, pow_one, one_smul, neg_smul, Fin.val_zero, Fin.val_one,
      ← sub_eq_add_neg]
    have e : inter U (tup i₁ i₀) = U₀ ⊓ U₁ := by
      rw [inter_tup]; exact inf_comm _ _
    refine hinj e ?_
    refine Eq.trans ?_ hanti.symm
    rw [hab, res_sub, res_res, res_res, neg_sub]
  · simp only [g, dif_neg (t0.trans_ne hne), dif_neg (t1.trans_ne hne)]
    rw [hdiag, res_res, res_res]
    simp only [pow_zero, pow_one, one_smul, neg_smul, Fin.val_zero, Fin.val_one]
    exact add_neg_cancel _

end Stacks.Cohomology.TwoCover

end
