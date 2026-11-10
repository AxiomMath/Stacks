module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Multiplicative

/-!
# A function on `X_a` is a global section divided by a power of `a` itself

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `a` a homogeneous element of the graded
section ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag 01CV. This file proves the
surjectivity half of Stacks Tag 01PW at arbitrary degree, in the case `𝓕 = 𝒪_X`: every function
`g` on `X_a` is the ratio `t / aᵐ` of a global section `t` of `L ^⊗ (N m)` by a **power of `a`
itself**, for some `m ≥ 1`. The denominators of the degree-zero localization
`Γ_*(X, L)₍a₎ = HomogeneousLocalization.Away (grading L) a` are by definition the powers of `a`.

## Main results

* `Stacks.SectionRingChartBijective.exists_ratio_powSec_of_affine_cover`: the ratio, against a
  finite affine cover by nonvanishing opens of homogeneous elements of one degree.
* `Stacks.SectionRingChartBijective.exists_ratio_powSec`: the ratio for `L` ample, at a
  homogeneous element of arbitrary positive degree, with denominator a power of
  `Stacks.SectionExtension.powSec L a N₀`, whose image in `Γ_*(X, L)` is `aᴺ⁰`
  (`Stacks.SectionRingChartMap.of_powSec_eq_pow`).

## Implementation notes

`Stacks.SectionExtension.exists_ratio_of_affine_cover` runs the same gluing argument but
concludes only that `g` is a ratio `t / σ` for *some* global section `σ` not vanishing on `X_a`.
Here the denominator is kept a power of `a`, and the power operation is
`Stacks.SectionExtension.powSec`, the one `Stacks.SectionRingChartMap.numMap` divides by, rather
than `Stacks.TensorPowerTrivialize.sectionPow`.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec resTop res_resTop resTop_eq_smul_of_le exists_resTop_eq_smul
  smul_resTop_injective nonvanishingOpen_inf_eq_basicOpen exists_forall_le map_res_res
  map_res_res_module nvOpen_eq exists_common_degree_affine_cover resTop_globalSection_powSec
  nvLocus_powSec_of_one_le)

universe u

namespace Stacks.SectionRingChartBijective

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- Raising the exponent of `x` in `xᵉ * y = z` to `k ≥ e` gives `xᵏ * y = xᵏ⁻ᵉ * z`. -/
private theorem pow_mul_eq_pow_sub_mul_of_le {R : Type*} [CommSemiring R] {x y z : R} {e k : ℕ}
    (h : x ^ e * y = z) (hk : e ≤ k) : x ^ k * y = x ^ (k - e) * z := by
  rw [← h, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **A function on `X_a` is a global section divided by a power of `a`, given an affine
cover.** Let `a` be a homogeneous element of degree `N` with `X_a = U`, let `c i` be a finite
family of homogeneous elements of the same degree `N` whose nonvanishing opens `V i` are affine
and cover `X`, and let `g` be a function on `U`. Then there are an exponent `m ≥ 1` and a
homogeneous element `t` of degree `N m` with `t|_U = g · aᵐ|_U`. -/
theorem exists_ratio_powSec_of_affine_cover {N : ℕ} (a : powSections L N)
    {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, nvOpen L (c i) = V i)
    (hcaff : ∀ i, IsAffineOpen (V i)) (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
    (g : Γ(X, U)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ t : powSections L (N * m),
      resTop U (globalSection X _ t)
        = g • resTop U (globalSection X _ (powSec L a m)) := by
  classical
  have hVle : ∀ i, V i ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) :=
    fun i ↦ le_of_eq (hV i).symm
  -- the ratio `f i = a / c i` over `V i = X_{c i}`
  choose f hf using fun i : ι ↦ exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ a) (hVle i)
  have hD : ∀ i, U ⊓ V i = X.basicOpen (f i) := fun i ↦ by
    rw [← hU]
    exact nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i)) (globalSection X _ a)
      (hVle i) (f i) (hf i)
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i ↦ by rw [← hD i]; exact inf_le_left
  have hDV : ∀ i, X.basicOpen (f i) ≤ V i := fun i ↦ X.basicOpen_le (f i)
  choose e z hz using fun i : ι ↦ AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen X
    (V i) (hcaff i) (f i) (X.presheaf.map (homOfLE (hDU i)).op g)
  obtain ⟨k, hk⟩ := exists_forall_le e
  obtain ⟨cn, hcn⟩ : ∃ cn : (i : ι) → Γ(X, V i), ∀ (i : ι) {S : X.Opens}
      (h : S ≤ X.basicOpen (f i)) (hSV : S ≤ V i) (hSU : S ≤ U),
      X.presheaf.map (homOfLE hSV).op (cn i)
        = X.presheaf.map (homOfLE hSV).op (f i) ^ k * X.presheaf.map (homOfLE hSU).op g := by
    refine ⟨fun i ↦ f i ^ (k - e i) * z i, fun i S h hSV hSU ↦ ?_⟩
    have h0 : X.presheaf.map (homOfLE (hDV i)).op (z i)
        = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ e i
          * X.presheaf.map (homOfLE (hDU i)).op g := hz i
    change X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i ^ (k - e i) * z i)
      = X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i) ^ k
          * X.presheaf.map (homOfLE (h.trans (hDU i))).op g
    rw [← map_res_res h (hDV i) (f i ^ (k - e i) * z i)]
    simp only [map_mul, map_pow, h0, map_res_res]
    exact (pow_mul_eq_pow_sub_mul_of_le rfl (hk i)).symm
  -- the ratio `w i j = c j / c i` on the overlap `V i ⊓ V j`
  choose w hw using fun (i j : ι) ↦ exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ (c j))
    ((inf_le_left : V i ⊓ V j ≤ V i).trans (hVle i))
  obtain ⟨fA, hfA⟩ : ∃ fA : (i j : ι) → Γ(X, V i ⊓ V j), ∀ i j,
      fA i j = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i) :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hfw : ∀ i j : ι, fA i j
      = X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j) * w i j := by
    intro i j
    rw [hfA]
    refine smul_resTop_injective (natTensorPow L N) (globalSection X _ (c i))
      ((inf_le_left : V i ⊓ V j ≤ V i).trans (hVle i)) ?_
    rw [← resTop_eq_smul_of_le (natTensorPow L N) (inf_le_left : V i ⊓ V j ≤ V i) (f i) (hf i),
      mul_smul, ← hw i j,
      ← resTop_eq_smul_of_le (natTensorPow L N) (inf_le_right : V i ⊓ V j ≤ V j) (f j) (hf j)]
  -- the overlaps are affine, by Stacks Tag 01PV
  have hAaff : ∀ i j : ι, IsAffineOpen (V i ⊓ V j) := fun i j ↦ by
    rw [← hV j]
    exact Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
      (natTensorPow L N) (globalSection X _ (c j)) (hcaff i)
  have hBA : ∀ i j : ι, X.basicOpen (fA i j) ≤ V i ⊓ V j := fun i j ↦ X.basicOpen_le _
  have hBD : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f i) := fun i j ↦ by
    rw [hfA, X.basicOpen_res]; exact inf_le_right
  have hBU : ∀ i j : ι, X.basicOpen (fA i j) ≤ U := fun i j ↦ (hBD i j).trans (hDU i)
  have hBD' : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f j) := fun i j ↦ by
    rw [← hD j]
    exact le_inf (hBU i j) ((hBA i j).trans inf_le_right)
  have hzero : ∀ i j : ι, X.presheaf.map (homOfLE (hBA i j)).op
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
        = 0 := by
    intro i j
    have hfib : X.presheaf.map (homOfLE ((hBD i j).trans (hDV i))).op (f i)
        = X.presheaf.map (homOfLE ((hBD' i j).trans (hDV j))).op (f j)
            * X.presheaf.map (homOfLE (hBA i j)).op (w i j) := by
      have h := congrArg (X.presheaf.map (homOfLE (hBA i j)).op)
        ((hfA i j).symm.trans (hfw i j))
      rwa [map_mul, map_res_res, map_res_res] at h
    have key : X.presheaf.map (homOfLE ((hBD i j).trans (hDV i))).op (cn i)
        = X.presheaf.map (homOfLE ((hBD' i j).trans (hDV j))).op (cn j)
            * X.presheaf.map (homOfLE (hBA i j)).op (w i j) ^ k := by
      rw [hcn i (hBD i j) ((hBD i j).trans (hDV i)) (hBU i j),
        hcn j (hBD' i j) ((hBD' i j).trans (hDV j)) (hBU i j), hfib]
      ring
    rw [map_sub, map_mul, map_pow, map_res_res, map_res_res, sub_eq_zero]
    exact key
  choose m hm using fun (i j : ι) ↦
    AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X
      (hAaff i j).isCompact
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
      (fA i j) (hzero i j)
  obtain ⟨q, hq⟩ := exists_forall_le fun p : ι × ι ↦ m p.1 p.2
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = k + (q + 1) := ⟨k + q, by omega⟩
  have hσ : ∀ i, resTop (V i) (globalSection X _ (powSec L a (K + 1)))
      = f i ^ (K + 1) • resTop (V i) (globalSection X _ (powSec L (c i) (K + 1))) := fun i ↦
    resTop_globalSection_powSec L (c i) a (f i) (hf i) (K + 1)
  have hβ : ∀ i j : ι, resTop (V i ⊓ V j) (globalSection X _ (powSec L (c j) (K + 1)))
      = w i j ^ (K + 1) • resTop (V i ⊓ V j)
          (globalSection X _ (powSec L (c i) (K + 1))) := fun i j ↦
    resTop_globalSection_powSec L (c i) (c j) (w i j) (hw i j) (K + 1)
  have hγA : ∀ i j : ι,
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i ^ (q + 1) * cn i)
      = X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j ^ (q + 1) * cn j)
          * w i j ^ (K + 1) := by
    intro i j
    have hkey : fA i j ^ (q + 1) *
        X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        = fA i j ^ (q + 1) *
          (X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k) :=
      sub_eq_zero.mp ((mul_sub _ _ _).symm.trans (by
        rw [pow_mul_eq_pow_sub_mul_of_le (hm i j) (Nat.le_succ_of_le (hq (i, j))), mul_zero]))
    rw [map_mul, map_pow, map_mul, map_pow, ← hfA i j, hkey, hfw i j, hK]
    ring
  have hγD : ∀ i, X.presheaf.map (homOfLE (hDV i)).op (f i ^ (q + 1) * cn i)
      = X.presheaf.map (homOfLE (hDU i)).op g *
          X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) := by
    intro i
    rw [map_mul, map_pow, hcn i le_rfl (hDV i) (hDU i), hK, pow_add]
    ring
  have hcompat0 : ∀ i j : ι,
      (natTensorPow L (N * (K + 1))).presheaf.map
          (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
          ((f i ^ (q + 1) * cn i) • resTop (V i) (globalSection X _ (powSec L (c i) (K + 1))))
        = (natTensorPow L (N * (K + 1))).presheaf.map
          (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
          ((f j ^ (q + 1) * cn j) • resTop (V j)
            (globalSection X _ (powSec L (c j) (K + 1)))) := by
    intro i j
    rw [Scheme.Modules.map_smul, res_resTop, Scheme.Modules.map_smul, res_resTop, hβ i j,
      smul_smul, hγA i j]
  have hcompat : TopCat.Presheaf.IsCompatible (natTensorPow L (N * (K + 1))).presheaf V
      (fun i ↦ (f i ^ (q + 1) * cn i) •
        resTop (V i) (globalSection X _ (powSec L (c i) (K + 1)))) := hcompat0
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(natTensorPow L (N * (K + 1))).presheaf, (natTensorPow L (N * (K + 1))).isSheaf⟩ :
      TopCat.Sheaf Ab X) V ⊤ (fun _ ↦ homOfLE le_top) hcover _ hcompat
  refine ⟨K + 1, Nat.le_add_left 1 K,
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
      (natTensorPow L (N * (K + 1)))).symm t, ?_⟩
  have htg : globalSection X (natTensorPow L (N * (K + 1)))
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
        (natTensorPow L (N * (K + 1)))).symm t) = t :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
      (natTensorPow L (N * (K + 1)))).apply_symm_apply t
  rw [htg]
  refine TopCat.Presheaf.IsSheaf.section_ext
    (natTensorPow L (N * (K + 1))).isSheaf (U := op U) fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hcover (TopologicalSpace.Opens.mem_top x))
  refine ⟨X.basicOpen (f i), hDU i, ?_, ?_⟩
  · rw [← hD i]; exact ⟨hx, hi⟩
  · have hti : resTop (V i) t = (f i ^ (q + 1) * cn i) •
        resTop (V i) (globalSection X _ (powSec L (c i) (K + 1))) := ht i
    rw [res_resTop, ← res_resTop t (hDV i), hti, Scheme.Modules.map_smul, res_resTop,
      Scheme.Modules.map_smul, res_resTop,
      resTop_eq_smul_of_le (natTensorPow L (N * (K + 1))) (hDV i) (f i ^ (K + 1)) (hσ i),
      map_pow, smul_smul, hγD i]

/-- **A function on `X_a` is a global section divided by a power of `a`, for `L` ample.** For `a`
homogeneous of positive degree `d` and `g` a function on the nonvanishing open `X_a`, there is an
exponent `m ≥ 1` and a homogeneous element `t` of degree `d N₀ m` with `t|_{X_a} = g · (a^{N₀})ᵐ`
over `X_a`. This is the surjectivity half of Stacks Tag 01PW at the degree of `a` in the case
`𝓕 = 𝒪_X`. -/
theorem exists_ratio_powSec (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d) (a : powSections L d)
    (g : Γ(X, nvOpen L a)) :
    ∃ N₀ m : ℕ, 1 ≤ N₀ ∧ 1 ≤ m ∧ ∃ t : powSections L (d * N₀ * m),
      resTop (nvOpen L a) (globalSection X _ t)
        = g • resTop (nvOpen L a)
            (globalSection X _ (powSec L (powSec L a N₀) m)) := by
  obtain ⟨N, -, F, c, hN1, hdvd, -, hcaff, hcover⟩ :=
    exists_common_degree_affine_cover L hL hd a
  obtain ⟨N₀, rfl⟩ := hdvd
  have hN₀ : 1 ≤ N₀ := Nat.pos_of_ne_zero (by rintro rfl; simp at hN1)
  have hnv : nvOpen L (powSec L a N₀) = nvOpen L a :=
    TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, coe_nvOpen, nvLocus_powSec_of_one_le L a N₀ hN₀])
  obtain ⟨m, hm, t, ht⟩ := exists_ratio_powSec_of_affine_cover L (powSec L a N₀) c
    (nvOpen L a) hnv (fun i ↦ nvOpen L (c i)) (fun _ ↦ rfl) hcaff hcover g
  exact ⟨N₀, m, hN₀, hm, t, ht⟩

end Monoidal

end Stacks.SectionRingChartBijective

end
