module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.Fintype.Order
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# The Qcqs lemma for quasi-coherent modules

Let `X` be a scheme, let `M` be a quasi-coherent `𝒪_X`-module and let `S` be a **quasi-compact
and quasi-separated** open of `X`. For `a : Γ(X, S)` this file proves that the sections of `M`
over the basic open `X.basicOpen a` are the localization of `Γ(M, S)` away from `a`.

This is the module-valued analogue of `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`, the
*Qcqs lemma* for the structure sheaf, and it generalizes
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`, which is the
case of an affine `S`.

## Main results

* `exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated`: surjectivity up to a power of `a`. For
  `S` quasi-compact and quasi-separated, every `x : Γ(M, X.basicOpen a)` satisfies
  `a ^ n • x = y |_ X.basicOpen a` for some `n` and some `y : Γ(M, S)`.
* `exists_pow_smul_eq_of_res_eq_of_isCompact`: injectivity up to a power of `a`. For `S` merely
  quasi-compact, two sections of `M` over `S` agreeing on `X.basicOpen a` agree after
  multiplication by a power of `a`.
* `isLocalizedModule_restrictₗ_of_qcqs`: the main result, phrased as
  `IsLocalizedModule.Away a (restrictₗ M hVS)`.
* `exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact` and
  `exists_pow_smul_eq_of_res_basicOpen_eq_of_isCompact`: the module-valued analogues of Mathlib's
  `AlgebraicGeometry.exists_of_res_zero_of_qcqs` and
  `AlgebraicGeometry.exists_of_res_eq_of_qcqs`. Unlike Mathlib's, these need only
  quasi-compactness.

## Implementation notes

The statements below spell restriction of sections as `M.presheaf.map (homOfLE h).op` rather
than using the `x |_ V` notation, because the `≤` proofs occurring here are not the ones that
`restrict_tac` produces and the lemmas are consumed by `rw`. The intended reading of, say,
`exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated` is
`y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n • x`.

The module structure on `Γ(M, V)` over `Γ(X, U)` for `V ≤ U` is the one supplied by
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE`; as explained there it has to be
provided by hand, so it appears as a `letI` in the statement of the main result.

Unlike Mathlib's structure-sheaf proof, which runs an induction over compact opens
(`AlgebraicGeometry.compact_open_induction_on`), the argument here is a single finite-cover
argument: choose a finite affine cover `Vᵢ` of `S`, solve the problem on each `Vᵢ` with the
affine case `isLocalizedModule_restrictₗ`, make the exponents uniform, and glue. The pairwise
intersections `Vᵢ ⊓ Vⱼ` are quasi-compact because `S` is quasi-separated, which is exactly what
is needed to compare the local solutions via `exists_pow_smul_eq_of_res_eq_of_isCompact` (that
lemma needs quasi-compactness only).

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7) (the structure-sheaf
  statement; this file proves a module-valued generalisation of it)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.QcqsLocalization

variable {X : Scheme.{u}}

/-- The sheaf of abelian groups underlying an `𝒪_X`-module. -/
noncomputable def abSheaf (M : X.Modules) : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩

/-- Restriction of sections of an `𝒪_X`-module along `W ≤ V ≤ U` factors through `V`. -/
theorem map_map (M : X.Modules) {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (h₃ : W ≤ U)
    (z : Γ(M, U)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op z) =
      M.presheaf.map (homOfLE h₃).op z := by
  rw [← Functor.map_comp_apply]
  rfl

/-- Restriction of sections of the structure sheaf along `W ≤ V ≤ U` factors through `V`. -/
theorem presheaf_map_map {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (h₃ : W ≤ U) (z : Γ(X, U)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op z) =
      X.presheaf.map (homOfLE h₃).op z := by
  rw [← Functor.map_comp_apply]
  rfl

/-- If a section `r` of `𝒪_X` over `U` restricts to a unit over `V ≤ U`, then `r` acts
invertibly on the sections of any `𝒪_X`-module over `V`. -/
theorem isUnit_algebraMap_moduleEnd (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U))
    (hr : IsUnit (X.presheaf.map (homOfLE h).op r)) :
    letI := moduleOfLE M h
    IsUnit (algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, V)) r) := by
  let := moduleOfLE M h
  obtain ⟨v, hv⟩ := hr
  have key : ∀ (c : Γ(X, U)) (z : Γ(M, V)),
      (↑v⁻¹ : Γ(X, V)) • (c • z) = c • ((↑v⁻¹ : Γ(X, V)) • z) := by
    intro c z
    change (↑v⁻¹ : Γ(X, V)) • ((X.presheaf.map (homOfLE h).op c) • z) =
      (X.presheaf.map (homOfLE h).op c) • ((↑v⁻¹ : Γ(X, V)) • z)
    rw [smul_smul, smul_smul, mul_comm]
  refine ⟨⟨algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, V)) r,
    { toFun := fun z ↦ (↑v⁻¹ : Γ(X, V)) • z
      map_add' := fun z w ↦ smul_add _ _ _
      map_smul' := key }, ?_, ?_⟩, rfl⟩
  · refine LinearMap.ext fun z ↦ ?_
    change (X.presheaf.map (homOfLE h).op r) • ((↑v⁻¹ : Γ(X, V)) • z) = z
    rw [← hv, smul_smul, Units.mul_inv, one_smul]
  · refine LinearMap.ext fun z ↦ ?_
    change (↑v⁻¹ : Γ(X, V)) • ((X.presheaf.map (homOfLE h).op r) • z) = z
    rw [← hv, smul_smul, Units.inv_mul, one_smul]

/-- **Affine case, surjectivity.** For `U` an affine open, `f : Γ(X, U)` and `W = X.basicOpen f`,
every section of a quasi-coherent `M` over `W` becomes the restriction of a section over `U`
after multiplication by a power of `f`. -/
theorem exists_eq_pow_smul_of_isAffineOpen (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) {W : X.Opens} (hW : W = X.basicOpen f) (hWU : W ≤ U)
    (x : Γ(M, W)) :
    ∃ (n : ℕ) (y : Γ(M, U)), M.presheaf.map (homOfLE hWU).op y =
      (X.presheaf.map (homOfLE hWU).op f) ^ n • x := by
  let := moduleOfLE M hWU
  have := isLocalizedModule_restrictₗ M hU f hW hWU
  obtain ⟨n, y, e⟩ :=
    IsLocalizedModule.Away.surj (f := restrictₗ M hWU) (r := f) x
  refine ⟨n, y, ?_⟩
  have e' : X.presheaf.map (homOfLE hWU).op (f ^ n) • x =
      M.presheaf.map (homOfLE hWU).op y := e
  rw [← e', map_pow]

/-- **Affine case, injectivity.** For `U` an affine open, `f : Γ(X, U)` and `W = X.basicOpen f`,
two sections of a quasi-coherent `M` over `U` that agree over `W` agree after multiplication by
a power of `f`. -/
theorem exists_pow_smul_eq_of_res_eq_of_isAffineOpen (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) {W : X.Opens} (hW : W = X.basicOpen f)
    (hWU : W ≤ U) (z₁ z₂ : Γ(M, U))
    (H : M.presheaf.map (homOfLE hWU).op z₁ = M.presheaf.map (homOfLE hWU).op z₂) :
    ∃ n : ℕ, f ^ n • z₁ = f ^ n • z₂ := by
  let := moduleOfLE M hWU
  have := isLocalizedModule_restrictₗ M hU f hW hWU
  exact IsLocalizedModule.Away.exists_of_eq (f := restrictₗ M hWU) f H

/-- A quasi-compact open is the supremum of finitely many affine opens contained in it. -/
private theorem exists_finite_affine_cover {U : X.Opens} (hU : IsCompact U.1) :
    ∃ (s : Set X.affineOpens) (_ : Fintype s), (∀ i : s, (i : X.Opens) ≤ U) ∧
      U = iSup fun i : s ↦ (i : X.Opens) := by
  obtain ⟨s, hsfin, hcov⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace hcov : U = iSup fun i : s ↦ (i : X.Opens) := by ext1; simpa using hcov
  refine ⟨s, hsfin.fintype, fun i ↦ ?_, hcov⟩
  rw [hcov]; exact le_iSup (fun i : s ↦ (i : X.Opens)) i

/-- **Injectivity over a quasi-compact open.** Two sections of a quasi-coherent `M` over a
quasi-compact open `U` that agree over `W = X.basicOpen f` agree after multiplication by a power
of `f`. This is the module-valued analogue of
`AlgebraicGeometry.exists_of_res_eq_of_qcqs`; note that quasi-separatedness is not needed. -/
theorem exists_pow_smul_eq_of_res_eq_of_isCompact (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1) (f : Γ(X, U)) {W : X.Opens} (hW : W = X.basicOpen f)
    (hWU : W ≤ U) (z₁ z₂ : Γ(M, U))
    (H : M.presheaf.map (homOfLE hWU).op z₁ = M.presheaf.map (homOfLE hWU).op z₂) :
    ∃ n : ℕ, f ^ n • z₁ = f ^ n • z₂ := by
  subst hW
  obtain ⟨s, _, hle, hcov⟩ := exists_finite_affine_cover hU
  have hPV : ∀ i : s, (i : X.Opens) ⊓ X.basicOpen f ≤ (i : X.Opens) := fun _ ↦ inf_le_left
  have hPb : ∀ i : s, (i : X.Opens) ⊓ X.basicOpen f ≤ X.basicOpen f := fun _ ↦ inf_le_right
  have hPU : ∀ i : s, (i : X.Opens) ⊓ X.basicOpen f ≤ U := fun i ↦ inf_le_left.trans (hle i)
  have key : ∀ i : s, ∃ k : ℕ,
      (X.presheaf.map (homOfLE (hle i)).op f) ^ k •
          M.presheaf.map (homOfLE (hle i)).op z₁ =
        (X.presheaf.map (homOfLE (hle i)).op f) ^ k •
          M.presheaf.map (homOfLE (hle i)).op z₂ := by
    intro i
    refine exists_pow_smul_eq_of_res_eq_of_isAffineOpen M i.1.2
      (X.presheaf.map (homOfLE (hle i)).op f)
      ((X.basicOpen_res f (homOfLE (hle i)).op).symm) (hPV i) _ _ ?_
    rw [map_map M (hPV i) (hle i) (hPU i) z₁, map_map M (hPV i) (hle i) (hPU i) z₂,
      ← map_map M (hPb i) hWU (hPU i) z₁, ← map_map M (hPb i) hWU (hPU i) z₂, H]
  choose k hk using key
  obtain ⟨K, hK⟩ := Finite.exists_le k
  have hloc : ∀ i : s, M.presheaf.map (homOfLE (hle i)).op (f ^ K • z₁) =
      M.presheaf.map (homOfLE (hle i)).op (f ^ K • z₂) := by
    intro i
    rw [M.map_smul, M.map_smul, map_pow, ← Nat.sub_add_cancel (hK i), pow_add, mul_smul,
      mul_smul, hk i]
  refine ⟨K, ?_⟩
  subst hcov
  exact TopCat.Sheaf.eq_of_locally_eq (F := abSheaf M) (fun i : s ↦ (i : X.Opens)) _ _ hloc

/-- **Vanishing over a quasi-compact open.** A section of a quasi-coherent `M` over a
quasi-compact open `U` that vanishes over `W = X.basicOpen f` is annihilated by a power of `f`.
This is the module-valued analogue of `AlgebraicGeometry.exists_of_res_zero_of_qcqs`. -/
theorem exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1) (f : Γ(X, U)) {W : X.Opens} (hW : W = X.basicOpen f)
    (hWU : W ≤ U) (z : Γ(M, U)) (H : M.presheaf.map (homOfLE hWU).op z = 0) :
    ∃ n : ℕ, f ^ n • z = 0 := by
  have H' : M.presheaf.map (homOfLE hWU).op z = M.presheaf.map (homOfLE hWU).op 0 := by
    rw [map_zero]; exact H
  obtain ⟨n, e⟩ := exists_pow_smul_eq_of_res_eq_of_isCompact M hU f hW hWU z 0 H'
  exact ⟨n, by simpa using e⟩

/-- **Surjectivity over a quasi-compact and quasi-separated open.** For `U` quasi-compact and
quasi-separated and `f : Γ(X, U)`, every section of a quasi-coherent `M` over `X.basicOpen f`
becomes the restriction of a section over `U` after multiplication by a power of `f`. This is
the module-valued analogue of
`AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`. -/
theorem exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U))
    (x : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • x := by
  obtain ⟨s, _, hle, hcov⟩ := exists_finite_affine_cover hU
  have hsub : ∀ i : s, ((i : X.Opens) : Set X) ⊆ (U : Set X) :=
    fun i ↦ SetLike.coe_subset_coe.mpr (hle i)
  have hPV : ∀ i : s, (i : X.Opens) ⊓ X.basicOpen f ≤ (i : X.Opens) := fun _ ↦ inf_le_left
  have hPb : ∀ i : s, (i : X.Opens) ⊓ X.basicOpen f ≤ X.basicOpen f := fun _ ↦ inf_le_right
  have hPU : ∀ i : s, (i : X.Opens) ⊓ X.basicOpen f ≤ U := fun i ↦ inf_le_left.trans (hle i)
  -- Solve the problem on each member of the cover, using the affine case.
  have key : ∀ i : s, ∃ (n : ℕ) (y : Γ(M, (i : X.Opens))),
      M.presheaf.map (homOfLE (hPV i)).op y =
        (X.presheaf.map (homOfLE (hPU i)).op f) ^ n •
          M.presheaf.map (homOfLE (hPb i)).op x := by
    intro i
    obtain ⟨n, y, hy⟩ := exists_eq_pow_smul_of_isAffineOpen M i.1.2
      (X.presheaf.map (homOfLE (hle i)).op f)
      ((X.basicOpen_res f (homOfLE (hle i)).op).symm) (hPV i)
      (M.presheaf.map (homOfLE (hPb i)).op x)
    exact ⟨n, y, by rw [hy, presheaf_map_map (hPV i) (hle i) (hPU i) f]⟩
  choose n y hy using key
  -- Make the exponents uniform.
  obtain ⟨N, hN⟩ := Finite.exists_le n
  obtain ⟨w, hwdef⟩ : ∃ w : ∀ i : s, Γ(M, (i : X.Opens)), ∀ i : s,
      w i = (X.presheaf.map (homOfLE (hle i)).op f) ^ (N - n i) • y i := ⟨_, fun _ ↦ rfl⟩
  have hw : ∀ i : s, M.presheaf.map (homOfLE (hPV i)).op (w i) =
      (X.presheaf.map (homOfLE (hPU i)).op f) ^ N •
        M.presheaf.map (homOfLE (hPb i)).op x := by
    intro i
    rw [hwdef i, M.map_smul, map_pow, presheaf_map_map (hPV i) (hle i) (hPU i) f, hy i,
      smul_smul, ← pow_add, Nat.sub_add_cancel (hN i)]
  -- The common value of the `w i` on any open contained in `V i ⊓ X.basicOpen f`.
  have hres : ∀ (i : s) (R : X.Opens) (hRV : R ≤ (i : X.Opens)) (hRb : R ≤ X.basicOpen f)
      (hRU : R ≤ U), M.presheaf.map (homOfLE hRV).op (w i) =
        (X.presheaf.map (homOfLE hRU).op f) ^ N • M.presheaf.map (homOfLE hRb).op x := by
    intro i R hRV hRb hRU
    have hRP : R ≤ (i : X.Opens) ⊓ X.basicOpen f := le_inf hRV hRb
    rw [← map_map M hRP (hPV i) hRV (w i), hw i, M.map_smul, map_pow,
      presheaf_map_map hRP (hPU i) hRU f, map_map M hRP (hPb i) hRb x]
  -- Compare the `w i` on the pairwise intersections, which are quasi-compact.
  have hQi : ∀ i j : s, (i : X.Opens) ⊓ (j : X.Opens) ≤ (i : X.Opens) := fun _ _ ↦ inf_le_left
  have hQj : ∀ i j : s, (i : X.Opens) ⊓ (j : X.Opens) ≤ (j : X.Opens) := fun _ _ ↦ inf_le_right
  have hQU : ∀ i j : s, (i : X.Opens) ⊓ (j : X.Opens) ≤ U := fun i _ ↦ inf_le_left.trans (hle i)
  have hQc : ∀ i j : s, IsCompact (((i : X.Opens) ⊓ (j : X.Opens) : X.Opens) : Set X) := by
    intro i j
    rw [Opens.coe_inf]
    exact hU' _ _ (hsub i) (i : X.Opens).2 i.1.2.isCompact (hsub j) (j : X.Opens).2
      j.1.2.isCompact
  have hpair : ∀ i j : s, ∃ mij : ℕ,
      (X.presheaf.map (homOfLE (hQU i j)).op f) ^ mij •
          M.presheaf.map (homOfLE (hQi i j)).op (w i) =
        (X.presheaf.map (homOfLE (hQU i j)).op f) ^ mij •
          M.presheaf.map (homOfLE (hQj i j)).op (w j) := by
    intro i j
    have hRQ : ((i : X.Opens) ⊓ (j : X.Opens)) ⊓ X.basicOpen f ≤
        (i : X.Opens) ⊓ (j : X.Opens) := inf_le_left
    have hRb : ((i : X.Opens) ⊓ (j : X.Opens)) ⊓ X.basicOpen f ≤ X.basicOpen f := inf_le_right
    have hRVi : ((i : X.Opens) ⊓ (j : X.Opens)) ⊓ X.basicOpen f ≤ (i : X.Opens) :=
      hRQ.trans (hQi i j)
    have hRVj : ((i : X.Opens) ⊓ (j : X.Opens)) ⊓ X.basicOpen f ≤ (j : X.Opens) :=
      hRQ.trans (hQj i j)
    have hRU : ((i : X.Opens) ⊓ (j : X.Opens)) ⊓ X.basicOpen f ≤ U := hRQ.trans (hQU i j)
    refine exists_pow_smul_eq_of_res_eq_of_isCompact M (hQc i j)
      (X.presheaf.map (homOfLE (hQU i j)).op f)
      ((X.basicOpen_res f (homOfLE (hQU i j)).op).symm) hRQ _ _ ?_
    rw [map_map M hRQ (hQi i j) hRVi (w i), map_map M hRQ (hQj i j) hRVj (w j),
      hres i _ hRVi hRb hRU, hres j _ hRVj hRb hRU]
  choose mm hmm using hpair
  obtain ⟨m, hm⟩ := Finite.exists_le fun p : s × s ↦ mm p.1 p.2
  obtain ⟨v, hvdef⟩ : ∃ v : ∀ i : s, Γ(M, (i : X.Opens)), ∀ i : s,
      v i = (X.presheaf.map (homOfLE (hle i)).op f) ^ m • w i := ⟨_, fun _ ↦ rfl⟩
  have hv : ∀ (i : s) (R : X.Opens) (hRV : R ≤ (i : X.Opens)),
      M.presheaf.map (homOfLE hRV).op (v i) =
        (X.presheaf.map (homOfLE hRV).op (X.presheaf.map (homOfLE (hle i)).op f)) ^ m •
          M.presheaf.map (homOfLE hRV).op (w i) := by
    intro i R hRV
    rw [hvdef i, M.map_smul, map_pow]
  -- The `v i` are a compatible family, so they glue.
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf (fun i : s ↦ (i : X.Opens)) v := by
    intro i j
    change M.presheaf.map (homOfLE (hQi i j)).op (v i) =
      M.presheaf.map (homOfLE (hQj i j)).op (v j)
    rw [hv i _ (hQi i j), hv j _ (hQj i j),
      presheaf_map_map (hQi i j) (hle i) (hQU i j) f,
      presheaf_map_map (hQj i j) (hle j) (hQU i j) f,
      ← Nat.sub_add_cancel (hm (i, j)), pow_add, mul_smul, mul_smul, hmm i j]
  obtain ⟨gl, hgl, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := abSheaf M)
    (fun i : s ↦ (i : X.Opens)) U (fun i ↦ homOfLE (hle i)) (le_of_eq hcov) v hcompat
  refine ⟨m + N, gl, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (F := abSheaf M)
    (fun i : s ↦ (i : X.Opens) ⊓ X.basicOpen f) (X.basicOpen f)
    (fun i ↦ homOfLE (hPb i)) ?_ _ _ fun i ↦ ?_
  · intro p hp
    have hpU : p ∈ U := X.basicOpen_le f hp
    rw [hcov] at hpU
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hpU
    exact Opens.mem_iSup.mpr ⟨i, hi, hp⟩
  · change M.presheaf.map (homOfLE (hPb i)).op
        (M.presheaf.map (homOfLE (X.basicOpen_le f)).op gl) =
      M.presheaf.map (homOfLE (hPb i)).op
        ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ (m + N) • x)
    have hgl' : M.presheaf.map (homOfLE (hle i)).op gl = v i := hgl i
    rw [map_map M (hPb i) (X.basicOpen_le f) (hPU i) gl,
      ← map_map M (hPV i) (hle i) (hPU i) gl, hgl', hv i _ (hPV i),
      presheaf_map_map (hPV i) (hle i) (hPU i) f, hres i _ (hPV i) (hPb i) (hPU i),
      smul_smul, ← pow_add, M.map_smul, map_pow,
      presheaf_map_map (hPb i) (X.basicOpen_le f) (hPU i) f]

/-- **The Qcqs lemma for quasi-coherent modules.** Let `M` be a quasi-coherent `𝒪_X`-module, let
`S` be a quasi-compact and quasi-separated open of the scheme `X` and let `a : Γ(X, S)`. Then the
sections of `M` over `X.basicOpen a` are the localization of `Γ(M, S)` away from `a`.

This is the module-valued analogue of `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` and
generalizes the affine case
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`. -/
theorem isLocalizedModule_restrictₗ_of_qcqs (M : X.Modules) [M.IsQuasicoherent] {S : X.Opens}
    (hS : IsCompact S.1) (hS' : IsQuasiSeparated S.1) (a : Γ(X, S)) {V : X.Opens}
    (hV : V = X.basicOpen a) (hVS : V ≤ S) :
    letI := moduleOfLE M hVS
    IsLocalizedModule.Away a (restrictₗ M hVS) := by
  subst hV
  let := moduleOfLE M hVS
  have hunit : IsUnit (X.presheaf.map (homOfLE hVS).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  refine IsLocalizedModule.Away.mk (isUnit_algebraMap_moduleEnd M hVS a hunit) ?_ ?_
  · intro z
    obtain ⟨k, yy, e⟩ :=
      exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated M hS hS' a z
    refine ⟨k, yy, ?_⟩
    change X.presheaf.map (homOfLE hVS).op (a ^ k) • z = _
    rw [map_pow]
    exact e.symm
  · intro z₁ z₂ hz
    exact exists_pow_smul_eq_of_res_eq_of_isCompact M hS a rfl hVS z₁ z₂ hz

/-- Two sections of a quasi-coherent `M` over a quasi-compact open `S` that agree on
`X.basicOpen a` agree after multiplication by a power of `a`. This is the specialization of
`exists_pow_smul_eq_of_res_eq_of_isCompact` to `W = X.basicOpen a`, convenient for use
alongside `isLocalizedModule_restrictₗ_of_qcqs`. -/
theorem exists_pow_smul_eq_of_res_basicOpen_eq_of_isCompact (M : X.Modules)
    [M.IsQuasicoherent] {S : X.Opens} (hS : IsCompact S.1) (a : Γ(X, S)) (z₁ z₂ : Γ(M, S))
    (H : M.presheaf.map (homOfLE (X.basicOpen_le a)).op z₁ =
      M.presheaf.map (homOfLE (X.basicOpen_le a)).op z₂) :
    ∃ n : ℕ, a ^ n • z₁ = a ^ n • z₂ :=
  exists_pow_smul_eq_of_res_eq_of_isCompact M hS a rfl (X.basicOpen_le a) z₁ z₂ H

end Stacks.AlgebraicGeometry.QcqsLocalization

end
