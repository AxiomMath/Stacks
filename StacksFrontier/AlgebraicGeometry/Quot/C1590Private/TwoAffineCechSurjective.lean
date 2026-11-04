module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.TwoAffineCoverFirstVanishing

/-!
# Vanishing first cohomology on two affine opens splits sections over the intersection

Let `U₀`, `U₁` be affine opens of a scheme with affine intersection and `ℱ` a quasi-coherent
module. If `H¹(U₀ ∪ U₁, ℱ) = 0`, every section of `ℱ` over `U₀ ∩ U₁` is the restriction of a
section over `U₁` minus the restriction of a section over `U₀`. This is the converse of
`Stacks.Cohomology.TwoCover.isZero_Hgroup_one_of_surjective`, and is proved the same way: by
[Stacks, Tag 01XD] the cohomology is that of the Čech complex of `{U₀, U₁}`; a section `c` over
`U₀ ∩ U₁` is the value at `(U₀, U₁)` of the alternating `1`-cochain with values `c`, `-c` at
`(U₀, U₁)`, `(U₁, U₀)` and zero on the diagonal, which is a cocycle and hence a coboundary.

## Main results

* `AlgebraicGeometry.C1590Private.exists_sub_eq_of_isZero_Hgroup_one`: the statement above.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf Stacks.Cohomology.Basis
open Stacks.Cohomology.TwoCover

universe u

namespace AlgebraicGeometry.C1590Private

/-- The sign of the alternating `1`-cochain of a two-member cover: `1` at `(U₀, U₁)`, `-1` at
`(U₁, U₀)`, `0` on the diagonal. -/
def pairSign (i j : ULift.{u} (Fin 2)) : ℤ :=
  if i = i₀ ∧ j = i₁ then 1 else if i = i₁ ∧ j = i₀ then -1 else 0

/-- `pairSign i j` is nonzero only at `(U₀, U₁)` and `(U₁, U₀)`. -/
theorem pairSign_ne_zero {i j : ULift.{u} (Fin 2)} (h : pairSign i j ≠ 0) :
    (i = i₀ ∧ j = i₁) ∨ (i = i₁ ∧ j = i₀) := by
  unfold pairSign at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd rfl h

/-- The face signs of a `2`-simplex of the two-member cover cancel. -/
theorem sum_pairSign (x : Fin 3 → ULift.{u} (Fin 2)) :
    ∑ a : Fin 3, (-1 : ℤ) ^ (a : ℕ) *
      pairSign ((x ∘ a.succAbove) 0) ((x ∘ a.succAbove) 1) = 0 := by
  rw [Fin.sum_univ_three]
  simp only [Function.comp_apply]
  rcases eq_i₀_or_eq_i₁ (x 0) with h0 | h0 <;> rcases eq_i₀_or_eq_i₁ (x 1) with h1 | h1 <;>
    rcases eq_i₀_or_eq_i₁ (x 2) with h2 | h2 <;>
    simp [Fin.succAbove, h0, h1, h2, pairSign, Fin.lt_def]

variable {Y : Scheme.{u}} {U₀ U₁ : Y.Opens}

/-- The intersection of the members of the two-member cover indexed by a `1`-simplex `x` at which
`pairSign` is nonzero is contained in `U₀ ∩ U₁`. -/
theorem inter_le_of_pairSign_ne_zero (x : Fin 2 → ULift.{u} (Fin 2))
    (h : pairSign (x 0) (x 1) ≠ 0) : inter (pairCover U₀ U₁) x ≤ U₀ ⊓ U₁ := by
  rw [eq_tup x, inter_tup]
  rcases pairSign_ne_zero h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]; exact le_rfl
  · rw [h0, h1]; exact (inf_comm _ _).le

variable (F : Y.Modules) [F.IsQuasicoherent]

/-- **`H¹(U₀ ∪ U₁, ℱ) = 0` splits sections over `U₀ ∩ U₁`.** If `U₀`, `U₁` and `U₀ ∩ U₁` are
affine and `H¹(U₀ ∪ U₁, ℱ) = 0` for the quasi-coherent module `ℱ`, every section of `ℱ` over
`U₀ ∩ U₁` is the restriction of a section over `U₁` minus the restriction of a section over
`U₀`. -/
theorem exists_sub_eq_of_isZero_Hgroup_one (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
    (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) (hH : IsZero (Hgroup Y.ringCatSheaf (U₀ ⊔ U₁) 1 F))
    (c : ToType ((abSections F).obj (op (U₀ ⊓ U₁)))) :
    ∃ (a : ToType ((abSections F).obj (op U₀))) (b : ToType ((abSections F).obj (op U₁))),
      c = res (abSections F) inf_le_right b - res (abSections F) inf_le_left a := by
  classical
  rw [Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology Y (U₀ ⊔ U₁)
    (pairCover U₀ U₁) (iSup_pairCover U₀ U₁)
    (fun r s => isAffineOpen_iInf_pairCover U₀ U₁ h₀ h₁ h₀₁ s) F 1] at hH
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hH
  set V := U₀ ⊔ U₁
  set U := pairCover U₀ U₁
  have hU := iSup_pairCover U₀ U₁
  -- the alternating cochain of `c`
  let ψ : ∀ x : Fin 2 → ULift.{u} (Fin 2), ToType ((abSections F).obj (op (inter U x))) :=
    fun x => if h : inter U x ≤ U₀ ⊓ U₁ then pairSign (x 0) (x 1) • res (abSections F) h c
      else 0
  have hψ : ∀ (x : Fin 2 → ULift.{u} (Fin 2)) {W : Y.Opens} (hW : W ≤ inter U x)
      (hW' : W ≤ U₀ ⊓ U₁),
      res (abSections F) hW (ψ x) = pairSign (x 0) (x 1) • res (abSections F) hW' c := by
    intro x W hW hW'
    by_cases h : inter U x ≤ U₀ ⊓ U₁
    · simp only [ψ, dite_eq_left h, res_zsmul, res_res]
    · have h0 : pairSign (x 0) (x 1) = 0 :=
        by_contra fun hne => h (inter_le_of_pairSign_ne_zero x hne)
      simp only [ψ, dite_eq_right h, res_zero, h0, zero_smul]
  let s := mmk V U hU F ψ
  have hs : md V U hU F s = 0 := by
    refine mcech_ext V U hU F _ _ fun x => ?_
    rw [mcomp_md V U hU F s x, mcomp_zero V U hU F x]
    simp only [s, mcomp_mmk V U hU F ψ]
    by_cases hx : inter U x ≤ U₀ ⊓ U₁
    · have hterm : ∀ a : Fin 3, (-1 : ℤ) ^ (a : ℕ) •
          res (abSections F) (inter_le_reindex U x a.succAbove) (ψ (x ∘ a.succAbove)) =
          ((-1 : ℤ) ^ (a : ℕ) * pairSign ((x ∘ a.succAbove) 0) ((x ∘ a.succAbove) 1)) •
            res (abSections F) hx c := fun a => by
        rw [hψ _ _ hx, smul_smul]
      rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_smul, sum_pairSign, zero_smul]
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [show ψ _ = 0 by
        simp only [ψ, dite_eq_right fun h => hx ((inter_le_reindex U x a.succAbove).trans h)],
        res_zero, smul_zero]
  obtain ⟨g, hg⟩ := hH s hs
  have hg' : md V U hU F g = s := hg
  -- read the coboundary at `(U₀, U₁)`
  have h01 : inter U (tup i₀ i₁) = U₀ ⊓ U₁ := inter_tup U₀ U₁ i₀ i₁
  have hcomp := congrArg (fun t => mcomp V U hU F t (tup i₀ i₁)) hg'
  rw [mcomp_md V U hU F g (tup i₀ i₁), mcomp_mmk V U hU F ψ (tup i₀ i₁), Fin.sum_univ_two]
    at hcomp
  have hc : ψ (tup i₀ i₁) = res (abSections F) h01.le c := by
    simp only [ψ, dite_eq_left h01.le, pairSign]
    simp
  rw [hc] at hcomp
  have hA : U₀ ≤ inter U ![i₀] := (inter_one U₀ U₁ ![i₀]).ge
  have hB : U₁ ≤ inter U ![i₁] := (inter_one U₀ U₁ ![i₁]).ge
  refine ⟨res (abSections F) hA (mcomp V U hU F g ![i₀]),
    res (abSections F) hB (mcomp V U hU F g ![i₁]), ?_⟩
  have e0 : tup i₀ i₁ ∘ Fin.succAbove 0 = ![i₁] := by funext k; fin_cases k; rfl
  have e1 : tup i₀ i₁ ∘ Fin.succAbove 1 = ![i₀] := by funext k; fin_cases k; rfl
  have hcomp' := congrArg (res (abSections F) h01.ge) hcomp
  rw [res_res, res_id, res_add, res_zsmul, res_zsmul, res_res, res_res] at hcomp'
  rw [res_res, res_res, ← hcomp', res_mcomp_congr V U hU F g e0 _ (inf_le_right.trans hB),
    res_mcomp_congr V U hU F g e1 _ (inf_le_left.trans hA)]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, ← sub_eq_add_neg]

end AlgebraicGeometry.C1590Private
