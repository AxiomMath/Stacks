module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Multiplicative
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# A function on `X_a` is a ratio with denominator a power of `a`, over a quasi-compact cover

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `a` a homogeneous element of degree `N`
of the graded section ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of [Stacks, Tag 01CV]. The
surjectivity half of [Stacks, Tag 01PW] says that every function on `X_a` is a ratio `t / aᵐ` of
a global section `t` of `L ^⊗ (N m)` by a power of `a` itself.

`Stacks.SectionRingChartBijective.exists_ratio_powSec_of_affine_cover` proves this against a
finite family `c i` of homogeneous elements of the same degree `N` whose nonvanishing opens
`X_{c i}` are **affine** and cover `X`. That hypothesis is what ampleness of `L` supplies, and it
is more than the gluing argument uses: the two places affineness enters are an extension of a
function from a basic open of `X_{c i}` to `X_{c i}`, which [Stacks, Tag 01P7] performs over any
quasi-compact quasi-separated open
(`AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`), and quasi-compactness
of the overlaps `X_{c i} ⊓ X_{c j}`, which is used only through `IsCompact`.

This file runs the same argument with the affineness of the `X_{c i}` replaced by exactly those
two consequences. The point of doing so is that a cover by **quasi-affine** nonvanishing opens is
then enough, and that is a hypothesis one can obtain by descent along an fpqc covering of a base
— see `StacksFrontier/AlgebraicGeometry/AmpleQuasiAffineCover/Basic.lean`, which turns such a cover
into ampleness and is the last step of `(2) ⟹ (1)` of [Stacks, Tag 0D2P].

## Main results

* `Stacks.SectionRingChartBijective.exists_ratio_powSec_of_compact_cover`: the gluing argument of
  [Stacks, Tag 01PW] with the denominator pinned to a power of `a`, over a finite cover of `X` by
  nonvanishing opens of homogeneous elements of one degree that are quasi-compact and
  quasi-separated and have quasi-compact pairwise intersections.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
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
  map_res_res_module nvOpen_eq resTop_globalSection_powSec nvLocus_powSec_of_one_le)

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

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The gluing argument of [Stacks, Tag 01PW] with the denominator pinned to a power of the
given homogeneous element, over a quasi-compact cover.** The hypotheses are a homogeneous element
`a` of degree `N` with `X_a = U`, a finite family `c i` of homogeneous elements of the same degree
`N` whose nonvanishing opens `V i` cover `X` and are quasi-compact and quasi-separated with
quasi-compact pairwise intersections, and a function `g` on `U`. The conclusion is an exponent
`m ≥ 1` and a homogeneous element `t` of degree `N m` with `t|_U = g · aᵐ|_U`.

This is `Stacks.SectionRingChartBijective.exists_ratio_powSec_of_affine_cover` with the
affineness of the `V i` weakened to the two consequences of it that the argument uses: the
extension of a function from a basic open of `V i` to `V i`, which is
`AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`, and quasi-compactness of
the overlaps, which
`AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` consumes as
`IsCompact`. Nothing else in the argument changes. -/
theorem exists_ratio_powSec_of_compact_cover {N : ℕ} (a : powSections L N)
    {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, nvOpen L (c i) = V i)
    (hVcpt : ∀ i, IsCompact ((V i : X.Opens) : Set X))
    (hVqs : ∀ i, IsQuasiSeparated ((V i : X.Opens) : Set X))
    (hVcap : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
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
  -- `U ⊓ V i` is the basic open of that ratio
  have hD : ∀ i, U ⊓ V i = X.basicOpen (f i) := fun i ↦ by
    rw [← hU]
    exact nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i)) (globalSection X _ a)
      (hVle i) (f i) (hf i)
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i ↦ by rw [← hD i]; exact inf_le_left
  have hDV : ∀ i, X.basicOpen (f i) ≤ V i := fun i ↦ X.basicOpen_le (f i)
  -- the local extension over the quasi-compact quasi-separated `V i`, with the exponent raised
  -- to a single `k`
  choose e z hz using fun i : ι ↦
    AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X
      (V i) (hVcpt i) (hVqs i) (f i) (X.presheaf.map (homOfLE (hDU i)).op g)
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
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hk i)]
  -- the ratio `w i j = c j / c i` on the overlap `V i ⊓ V j`
  choose w hw using fun (i j : ι) ↦ exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ (c j))
    ((inf_le_left : V i ⊓ V j ≤ V i).trans (hVle i))
  obtain ⟨fA, hfA⟩ : ∃ fA : (i j : ι) → Γ(X, V i ⊓ V j), ∀ i j,
      fA i j = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i) :=
    ⟨_, fun _ _ ↦ rfl⟩
  -- `f i = f j * w i j` on the overlap: both compute `a` against `c i`
  have hfw : ∀ i j : ι, fA i j
      = X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j) * w i j := by
    intro i j
    rw [hfA]
    refine smul_resTop_injective (natTensorPow L N) (globalSection X _ (c i))
      ((inf_le_left : V i ⊓ V j ≤ V i).trans (hVle i)) ?_
    rw [← resTop_eq_smul_of_le (natTensorPow L N) (inf_le_left : V i ⊓ V j ≤ V i) (f i) (hf i),
      mul_smul, ← hw i j,
      ← resTop_eq_smul_of_le (natTensorPow L N) (inf_le_right : V i ⊓ V j ≤ V j) (f j) (hf j)]
  -- the overlaps are quasi-compact, by hypothesis
  have hAcpt : ∀ i j : ι, IsCompact ((V i ⊓ V j : X.Opens) : Set X) := hVcap
  have hBA : ∀ i j : ι, X.basicOpen (fA i j) ≤ V i ⊓ V j := fun i j ↦ X.basicOpen_le _
  have hBD : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f i) := fun i j ↦ by
    rw [hfA, X.basicOpen_res]; exact inf_le_right
  have hBU : ∀ i j : ι, X.basicOpen (fA i j) ≤ U := fun i j ↦ (hBD i j).trans (hDU i)
  have hBD' : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f j) := fun i j ↦ by
    rw [← hD j]
    exact le_inf (hBU i j) ((hBA i j).trans inf_le_right)
  -- the two numerators agree where `a` does not vanish, so a power of `f i` kills the difference
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
      rw [map_mul, map_res_res, map_res_res] at h
      exact h
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
      (hAcpt i j)
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
      (fA i j) (hzero i j)
  obtain ⟨q, hq⟩ := exists_forall_le fun p : ι × ι ↦ m p.1 p.2
  have hm' : ∀ i j : ι, fA i j ^ (q + 1) *
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
        = 0 := by
    intro i j
    have hmq : m i j ≤ q := hq (i, j)
    have h : q + 1 = q + 1 - m i j + m i j := by omega
    rw [h, pow_add, mul_assoc, hm i j, mul_zero]
  -- the exponent of the answer: `K + 1 = k + (q + 1)`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = k + (q + 1) := ⟨k + q, by omega⟩
  -- the two power laws of the compatible family of generators `c i ^ (K + 1)`
  have hσ : ∀ i, resTop (V i) (globalSection X _ (powSec L a (K + 1)))
      = f i ^ (K + 1) • resTop (V i) (globalSection X _ (powSec L (c i) (K + 1))) := fun i ↦
    resTop_globalSection_powSec L (c i) a (f i) (hf i) (K + 1)
  have hβ : ∀ i j : ι, resTop (V i ⊓ V j) (globalSection X _ (powSec L (c j) (K + 1)))
      = w i j ^ (K + 1) • resTop (V i ⊓ V j)
          (globalSection X _ (powSec L (c i) (K + 1))) := fun i j ↦
    resTop_globalSection_powSec L (c i) (c j) (w i j) (hw i j) (K + 1)
  -- the numerators agree on the overlaps, by the annihilator and `f i = f j * w i j`
  have hγA : ∀ i j : ι,
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i ^ (q + 1) * cn i)
      = X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j ^ (q + 1) * cn j)
          * w i j ^ (K + 1) := by
    intro i j
    have hkey : fA i j ^ (q + 1) *
        X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        = fA i j ^ (q + 1) *
          (X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k) := by
      have h := hm' i j
      rw [mul_sub, sub_eq_zero] at h
      exact h
    rw [map_mul, map_pow, map_mul, map_pow, ← hfA i j, hkey, hfw i j, hK]
    ring
  -- and they compute `g` against the generator over `U ⊓ V i`
  have hγD : ∀ i, X.presheaf.map (homOfLE (hDV i)).op (f i ^ (q + 1) * cn i)
      = X.presheaf.map (homOfLE (hDU i)).op g *
          X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) := by
    intro i
    rw [map_mul, map_pow, hcn i le_rfl (hDV i) (hDU i), hK, pow_add]
    ring
  -- the local sections, and their compatibility
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
    (natTensorPow L (N * (K + 1))).isSheaf (U := op U) ?_
  intro x hx
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

end Monoidal

end Stacks.SectionRingChartBijective

end
