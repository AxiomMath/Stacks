module

public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A degree bound for the cohomology of quasi-coherent modules over an open subscheme

[Stacks, Tag 071L] bounds the degrees in which the cohomology of *every* quasi-coherent module
on a quasi-compact quasi-separated scheme `X` vanishes, in terms of a covering of `X` by
quasi-compact opens with affine diagonal. This file proves the same bound over an open
subscheme: a covering of an open `W ⊆ X` by opens with affine diagonal bounds the degrees in which
the cohomology of every quasi-coherent module *over `W`* vanishes. Quasi-separatedness of `X` is
replaced by the quasi-compactness of the finite intersections of the members of the covering.

## Main results

* `AlgebraicGeometry.isZero_cohomology_of_cover_bound_of_iSup_eq`: the bound.
* `AlgebraicGeometry.isZero_cohomology_of_affine_cover_bound`: the bound for a covering by affine
  opens whose finite intersections come with affine coverings.
* `AlgebraicGeometry.isCompact_iSup_of_finite`: a finite union of quasi-compact opens is
  quasi-compact.
* `AlgebraicGeometry.isCompact_finsetInf_of_isQuasiSeparated`: a nonempty finite intersection of
  quasi-compact opens contained in a quasi-separated region is quasi-compact.

## References

* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.UniformVanishing

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A union of finitely many quasi-compact opens is quasi-compact. -/
theorem isCompact_iSup_of_finite {ι : Type*} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsCompact (U i : Set X)) : IsCompact ((⨆ i, U i : X.Opens) : Set X) := by
  simpa using isCompact_iUnion hU

/-- **A nonempty finite intersection of quasi-compact opens contained in a quasi-separated region
is quasi-compact.** -/
theorem isCompact_finsetInf_of_isQuasiSeparated {R : X.Opens}
    (hR : IsQuasiSeparated (R : Set X)) {ι : Type*} (U : ι → X.Opens)
    (hUc : ∀ i, IsCompact (U i : Set X)) (hUR : ∀ i, U i ≤ R)
    {s : Finset ι} (hs : s.Nonempty) : IsCompact ((s.inf U : X.Opens) : Set X) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hUc i
  | cons i s hi hs ih =>
      obtain ⟨j, hj⟩ := hs
      rw [Finset.inf_cons]
      exact hR _ _ (hUR i) (U i).2 (hUc i) ((Finset.inf_le hj).trans (hUR j))
        (s.inf U : X.Opens).2 ih

/-- The `Ext`-theoretic form of [Stacks, Tag 01XI] for an open subscheme, in every degree: over a
quasi-compact open in which the intersection of two affine opens is affine, the cohomology of a
quasi-coherent module vanishes in degrees at least the affine covering number. -/
@[ega "III 3.2.3" "more general"]
private theorem isZero_sheafCohomology_of_affineCoverNum_le
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent] (W : X.Opens) (hW : IsCompact (W : Set X))
    (hinf : ∀ A B : X.Opens, A ≤ W → B ≤ W → IsAffineOpen A → IsAffineOpen B →
      IsAffineOpen (A ⊓ B))
    (p : ℕ) (hp : X.affineCoverNum W ≤ p) :
    IsZero (Sheaf.H' F.toAbelianSheaf p W) := by
  cases p with
  | zero =>
      obtain rfl : W = ⊥ := Scheme.eq_bot_of_affineCoverNum_eq_zero W hW (by lia)
      exact isZero_sheafCohomology_bot F.toAbelianSheaf 0
  | succ m =>
      exact (isZero_cohomology_of_affineCoverNum_le_of_isCompact F W hW hinf (m + 1) hp).of_iso
        (hgroupIsoSheafCohomology F W m).symm

/-- **[Stacks, Tag 071L] over an open subscheme.** Let `X` be a scheme, let `W` be an open of `X`
covered by finitely many opens `U 1, …, U n` in each of which the intersection of two affine
opens is affine — for instance each `U i` separated, or affine — and suppose every nonempty
finite intersection `⋂_{i ∈ I} U i` is quasi-compact. If `d` dominates all the numbers
`|I| + t(⋂_{i ∈ I} U i) - 1`, where `t` is the affine covering number
`AlgebraicGeometry.Scheme.affineCoverNum`, then `H^p(W, F) = 0` for every `p ≥ d` and every
quasi-coherent `𝒪_X`-module `F`. -/
theorem isZero_cohomology_of_cover_bound_of_iSup_eq (F : X.Modules) [F.IsQuasicoherent] {n : ℕ}
    (U : Fin n → X.Opens) {W : X.Opens} (hcov : ⨆ i, U i = W)
    (hUinf : ∀ (i : Fin n) (A B : X.Opens), A ≤ U i → B ≤ U i → IsAffineOpen A →
      IsAffineOpen B → IsAffineOpen (A ⊓ B))
    (hUc : ∀ s : Finset (Fin n), s.Nonempty → IsCompact ((s.inf U : X.Opens) : Set X))
    (d : ℕ) (hd : ∀ s : Finset (Fin n), s.Nonempty →
      s.card + X.affineCoverNum (s.inf U) - 1 ≤ d)
    (p : ℕ) (hp : d ≤ p) :
    IsZero (Hgroup X.ringCatSheaf W p F) := by
  classical
  have hext : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  have hinf : ∀ s : Finset (Fin n), s.Nonempty → ∀ A B : X.Opens, A ≤ s.inf U → B ≤ s.inf U →
      IsAffineOpen A → IsAffineOpen B → IsAffineOpen (A ⊓ B) := by
    intro s hs A B hA hB hAaff hBaff
    obtain ⟨i, hi⟩ := hs
    exact hUinf i A B (hA.trans (Finset.inf_le hi)) (hB.trans (Finset.inf_le hi)) hAaff hBaff
  have hunion : (Finset.univ : Finset (Fin n)).sup U = W := (Finset.sup_univ_eq_iSup U).trans hcov
  have hH : IsZero (Sheaf.H' F.toAbelianSheaf p W) := hunion ▸
    isZero_sheafCohomology_finsetSup F.toAbelianSheaf Finset.univ U
      (fun s ↦ X.affineCoverNum (s.inf U)) d
      (fun s hs pp hpp ↦
        isZero_sheafCohomology_of_affineCoverNum_le F (s.inf U) (hUc s hs) (hinf s hs) pp hpp)
      (fun s _ hs ↦ hd s hs) p hp
  cases p with
  | zero =>
      have hUbot : ∀ i, U i = ⊥ := by
        intro i
        have hsingle := hd {i} ⟨i, by simp⟩
        simp only [Finset.card_singleton, Finset.inf_singleton] at hsingle
        exact Scheme.eq_bot_of_affineCoverNum_eq_zero (U i)
          (by simpa using hUc {i} ⟨i, by simp⟩) (by lia)
      obtain rfl : W = ⊥ := by rw [← hcov]; simp [hUbot]
      exact isZero_Hgroup_bot F 0
  | succ m => exact hH.of_iso (hgroupIsoSheafCohomology F W m)

/-- **[Stacks, Tag 071L] over an open subscheme, from affine coverings of the intersections.**
If the open `W` is covered by finitely many affine opens `V 1, …, V k` and every nonempty finite
intersection `⋂_{i ∈ I} V i` is covered by `c_I` affine opens with `|I| + c_I - 1 ≤ d`, then
`H^p(W, F) = 0` for every `p ≥ d` and every quasi-coherent `𝒪_X`-module `F`. -/
theorem isZero_cohomology_of_affine_cover_bound (F : X.Modules) [F.IsQuasicoherent]
    {W : X.Opens} (d : ℕ) {k : ℕ} (V : Fin k → X.Opens) (hVaff : ∀ i, IsAffineOpen (V i))
    (hVcov : ⨆ i, V i = W)
    (hVbd : ∀ s : Finset (Fin k), s.Nonempty → ∃ (c : ℕ) (A : Fin c → X.Opens),
      (∀ a, IsAffineOpen (A a)) ∧ (⨆ a, A a = s.inf V) ∧ s.card + c - 1 ≤ d)
    (p : ℕ) (hp : d ≤ p) :
    IsZero (Hgroup X.ringCatSheaf W p F) := by
  refine isZero_cohomology_of_cover_bound_of_iSup_eq F V hVcov
    (fun i A₁ A₂ hA₁ hA₂ hA₁aff hA₂aff ↦ ?_) (fun s hs ↦ ?_) d (fun s hs ↦ ?_) p hp
  · have : IsAffine (V i).toScheme := hVaff i
    exact isAffineOpen_inf_of_le (V i) hA₁aff hA₂aff hA₁ hA₂
  · obtain ⟨c, A, hAaff, hAcov, -⟩ := hVbd s hs
    exact hAcov ▸ isCompact_iSup_of_finite A fun a ↦ (hAaff a).isCompact
  · obtain ⟨c, A, hAaff, hAcov, hcard⟩ := hVbd s hs
    have := Scheme.affineCoverNum_le A hAaff hAcov
    lia

end AlgebraicGeometry
