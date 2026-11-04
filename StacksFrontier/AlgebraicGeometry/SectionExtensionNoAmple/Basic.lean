module

public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Annihilator
public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Cover
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Stacks Tag 01PW for an arbitrary quasi-coherent module, with **no ampleness hypothesis**

`Stacks.ModuleSectionExtension.exists_tensorSection_of_isAmple` proves the surjectivity half of
Stacks Tag 01PW for an arbitrary quasi-coherent `F` **under the additional hypothesis that `L` is
ample**, and `Stacks.SectionExtension.isSectionRatio_of_isAmple` does the case `F = 𝒪_X` under the
same hypothesis. Neither applies to part (1) of [Stacks, Tag 0892]: there `L` is the pullback
`f^* M` and the ampleness of `f^* M` is part (2), which the source deduces *from* part (1), so
assuming it is circular.

This file removes the ampleness. What replaces it is the hypothesis

> `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`: every point of `X` lies in the
> nonvanishing locus `X_b` of *some* homogeneous element `b` of positive degree,

with **no affineness asked of `X_b`**, together with quasi-compactness and quasi-separatedness of
`X` — which are Tag 01PW's own hypotheses on the scheme. See the "What is and is not proved"
section for what separates this from the source statement.

## Where ampleness was used, and what replaces it

Ampleness entered the ample proof in exactly one place: through
`Stacks.SectionExtension.exists_common_degree_affine_cover`, to make the members of the cover
*affine*. Two steps of the gluing need that:

1. the **local extension** on a chart (`Stacks.ModuleSectionExtension.exists_pow_smul_eq_res`),
   which is a localization statement and genuinely needs an affine; and
2. the **annihilator** on the pairwise intersections
   (`Stacks.ModuleSectionExtension.exists_pow_smul_eq_of_res_eq`), which in the ample proof is
   applied on `X_{c i} ⊓ X_{c j}`, affine by [Stacks, Tag 01PV] precisely because the members are
   affine nonvanishing loci.

Both are repaired without ampleness, and differently:

* For 1, the chart is replaced by an **affine open inside** `X_{c i}` rather than `X_{c i}` itself
  (`Stacks.SectionExtensionNoAmple.exists_common_degree_affine_subcover`). Everything the gluing
  does on a chart is divide by the generator `c i`, and both
  `Stacks.SectionExtension.exists_resTop_eq_smul` and
  `Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen` are already stated for an arbitrary
  open inside the nonvanishing locus, so nothing else changes.
* For 2, the intersection of two such affine charts is no longer affine — only quasi-compact, by
  quasi-separatedness of `X` — so the affine annihilator is replaced by
  `Stacks.SectionExtensionNoAmple.exists_pow_smul_eq_of_res_eq_of_isCompact`, its quasi-compact
  form, proved in the sibling file from the affine one over a finite affine cover.

Those are the only two changes to the argument of
`Stacks.ModuleSectionExtension.exists_tensorSection_of_affine_cover`; the degree bookkeeping, the
multiplicativity of the ratio (`Stacks.TensorPowerTrivialize.resTop_sectionPow`), the products of
sections (`Stacks.SectionTensorFormula.tensorSection`) and the final gluing are reused verbatim.

## Main results

* `Stacks.SectionExtensionNoAmple.exists_tensorSection_of_quasiCompact_cover`: **the gluing
  argument**, stated against a finite family of affine opens inside the nonvanishing loci of
  homogeneous elements of one common degree, with quasi-compact pairwise intersections. No
  ampleness, no affineness of the nonvanishing loci.
* `Stacks.SectionExtensionNoAmple.exists_tensorSection_of_hasPointwiseNonvanishing`: **the
  deliverable, in the section-ring vocabulary.** For `X` quasi-compact and quasi-separated, `L`
  invertible with enough sections, and `F` quasi-coherent, a section of `F` over `X_a` extends,
  after tensoring with a tensor power of `L`, to a global section.
* `Stacks.SectionExtensionNoAmple.exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing`: the
  same in the `Stacks.Ample.tensorPowModule` vocabulary the consumers of the ample cluster are
  stated over, obtained through `Stacks.ModuleSectionExtension.tensorSection_eqToHom` exactly as
  `Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple` is.
* `Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_of_isAmple`: ampleness implies the
  hypothesis, so what is proved here subsumes the ample statement.

## What is and is not proved, and why no Stacks attribute is attached

The source statement of Tag 01PW assumes only that `X` is quasi-compact (and quasi-separated for
part (2)) and that `L` is invertible. `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` is
an **additional hypothesis**: an invertible module can have no nonzero global section in any
positive tensor power at all, and then the hypothesis fails while the source statement still holds.
Removing it is not a matter of bookkeeping — the charts of the source's proof are opens on which
`L` *itself* is trivialized, with no global section in sight, and this repository has compatible
generators of all the tensor powers over a chart only as the restrictions of the powers of **one
global section** (`Stacks.TensorPowerTrivialize.trivializationPow`,
`Stacks.TensorPowerTrivialize.resTop_sectionPow`, whose own module documentation records this as
the step that "a trivialization with an unnamed local generator cannot supply"). So the four labels
of Tag 01PW are not closed here and no attribute is attached; the three counts recorded in
`Stacks.ModuleSectionExtension.Basic` stand, with the second weakened from "`L` is assumed ample"
to "`L` is assumed to have enough sections".

What is gained is exactly what part (1) of [Stacks, Tag 0892] needs, and it is not a bookkeeping
gain: for `L = f^* M` with `M` ample on the base the hypothesis holds unconditionally, by
[Stacks, Tag 0H78] in the form `Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection`, while
ampleness of `f^* M` is unavailable on pain of circularity.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowerTrivialize (sectionPow powDeg)
open Stacks.SectionExtension (resTop res_resTop resTop_eq_smul_of_le exists_resTop_eq_smul
  smul_resTop_injective nonvanishingOpen_inf_eq_basicOpen exists_forall_le map_res_res
  map_res_res_module)
open Stacks.SectionTensorFormula (tensorSection map_tensorSection tensorSection_smul_left
  tensorSection_smul_right)

universe u

namespace Stacks.SectionExtensionNoAmple

/-! ### The gluing argument -/

section Glue

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The gluing argument of Stacks Tag 01PW for an arbitrary quasi-coherent `F`, with no
ampleness and no affine nonvanishing locus.**

The hypotheses are a finite family `c i` of homogeneous elements of one degree `N`, a finite family
of **affine opens `V i` contained in `X_{c i}`** covering `X` whose pairwise intersections are
quasi-compact, a further homogeneous element `a` of degree `N` with `X_a = U`, and a section `t` of
`F` over `U`. The conclusion is a global section of `F ⊗ L ^⊗ p` restricting on `U` to `t ⊗ σ|_U`,
for `σ` a global section of `L ^⊗ p` not vanishing on `U`.

This is `Stacks.ModuleSectionExtension.exists_tensorSection_of_affine_cover` with `X_{c i} = V i`
weakened to `V i ≤ X_{c i}` and with the affineness of the overlaps weakened to
quasi-compactness. The proof is the same, with its annihilator step taken from
`Stacks.SectionExtensionNoAmple.exists_pow_smul_eq_of_res_eq_of_isCompact` instead of from the
affine form; see the module documentation. -/
theorem exists_tensorSection_of_quasiCompact_cover (F : X.Modules) [F.IsQuasicoherent] {N : ℕ}
    (a : powSections L N) {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, V i ≤ nvOpen L (c i))
    (hcaff : ∀ i, IsAffineOpen (V i))
    (hqc : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
    (t : Γ(F, U)) :
    ∃ (p : ℕ) (σ : Γ(natTensorPow L p, ⊤)) (τ : Γ(F ⊗ natTensorPow L p, ⊤)), N ∣ p ∧
      U = nonvanishingOpen X (natTensorPow L p) σ ∧
        resTop U τ = tensorSection F (natTensorPow L p) t (resTop U σ) := by
  classical
  have hVle : ∀ i, V i ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) := hV
  -- the ratio `f i = a / c i` over `V i ⊆ X_{c i}`
  choose f hf using fun i : ι => exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ a) (hVle i)
  -- `U ⊓ V i` is the basic open of that ratio
  have hD : ∀ i, U ⊓ V i = X.basicOpen (f i) := fun i => by
    rw [← hU]
    exact nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i)) (globalSection X _ a)
      (hVle i) (f i) (hf i)
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i => by rw [← hD i]; exact inf_le_left
  have hDV : ∀ i, X.basicOpen (f i) ≤ V i := fun i => X.basicOpen_le (f i)
  -- the local extension over the affine `V i`, with the exponent raised to a single `k`
  choose e z hz using fun i : ι => Stacks.ModuleSectionExtension.exists_pow_smul_eq_res F
    (hcaff i) (f i) (F.presheaf.map (homOfLE (hDU i)).op t)
  obtain ⟨k, hk⟩ := exists_forall_le e
  obtain ⟨cn, hcn⟩ : ∃ cn : (i : ι) → Γ(F, V i), ∀ (i : ι) {S : X.Opens}
      (h : S ≤ X.basicOpen (f i)),
      F.presheaf.map (homOfLE (h.trans (hDV i))).op (cn i)
        = X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i) ^ k
          • F.presheaf.map (homOfLE (h.trans (hDU i))).op t := by
    refine ⟨fun i => f i ^ (k - e i) • z i, fun i S h => ?_⟩
    have h0 : F.presheaf.map (homOfLE (hDV i)).op (z i)
        = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ e i
          • F.presheaf.map (homOfLE (hDU i)).op t := (hz i).symm
    rw [← map_res_res_module h (hDV i) (f i ^ (k - e i) • z i)]
    simp only [Scheme.Modules.map_smul, map_pow, h0, map_res_res, map_res_res_module, smul_smul,
      ← pow_add]
    rw [Nat.sub_add_cancel (hk i)]
  -- the ratio `w i j = c j / c i` on the overlap `V i ⊓ V j`
  choose w hw using fun (i j : ι) => exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ (c j))
    ((inf_le_left : V i ⊓ V j ≤ V i).trans (hVle i))
  obtain ⟨fA, hfA⟩ : ∃ fA : (i j : ι) → Γ(X, V i ⊓ V j), ∀ i j,
      fA i j = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i) :=
    ⟨_, fun _ _ => rfl⟩
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
  have hBA : ∀ i j : ι, X.basicOpen (fA i j) ≤ V i ⊓ V j := fun i j => X.basicOpen_le _
  have hBD : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f i) := fun i j => by
    rw [hfA, X.basicOpen_res]; exact inf_le_right
  have hBU : ∀ i j : ι, X.basicOpen (fA i j) ≤ U := fun i j => (hBD i j).trans (hDU i)
  have hBD' : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f j) := fun i j => by
    rw [← hD j]
    exact le_inf (hBU i j) ((hBA i j).trans inf_le_right)
  -- the two numerators agree where `a` does not vanish, so a power of `f i` kills the difference
  have hzero : ∀ i j : ι,
      F.presheaf.map (homOfLE (X.basicOpen_le (fA i j))).op
          (F.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i))
        = F.presheaf.map (homOfLE (X.basicOpen_le (fA i j))).op
          (w i j ^ k • F.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j)) := by
    intro i j
    have hfib : X.presheaf.map (homOfLE ((hBD i j).trans (hDV i))).op (f i)
        = X.presheaf.map (homOfLE ((hBD' i j).trans (hDV j))).op (f j)
            * X.presheaf.map (homOfLE (hBA i j)).op (w i j) := by
      have h := congrArg (X.presheaf.map (homOfLE (hBA i j)).op)
        ((hfA i j).symm.trans (hfw i j))
      rw [map_mul, map_res_res, map_res_res] at h
      exact h
    rw [map_res_res_module, Scheme.Modules.map_smul, map_pow, map_res_res_module,
      hcn i (hBD i j), hcn j (hBD' i j), hfib, smul_smul, mul_pow]
    ring_nf
  choose m hm using fun (i j : ι) => exists_pow_smul_eq_of_res_eq_of_isCompact F (hqc i j) (fA i j)
    (F.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i))
    (w i j ^ k • F.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j))
    (hzero i j)
  obtain ⟨q, hq⟩ := exists_forall_le fun p : ι × ι => m p.1 p.2
  have hm' : ∀ i j : ι, fA i j ^ (q + 1) •
      (F.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i))
        = fA i j ^ (q + 1) • (w i j ^ k •
            F.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j)) := by
    intro i j
    have hmq : m i j ≤ q := hq (i, j)
    have h : q + 1 = q + 1 - m i j + m i j := by omega
    rw [h, pow_add, mul_smul, mul_smul, hm i j]
  -- the exponent of the answer: `K + 1 = k + (q + 1)`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = k + (q + 1) := ⟨k + q, by omega⟩
  have hK' : K + 1 = q + 1 + k := by omega
  -- the two power laws of the compatible family of generators `c i ^ (K + 1)`
  have hσ : ∀ i, resTop (V i) (globalSection X _ (sectionPow L a K))
      = f i ^ (K + 1) • resTop (V i) (globalSection X _ (sectionPow L (c i) K)) := fun i =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) a (f i) (hf i) K
  have hβ : ∀ i j : ι, resTop (V i ⊓ V j) (globalSection X _ (sectionPow L (c j) K))
      = w i j ^ (K + 1) • resTop (V i ⊓ V j)
          (globalSection X _ (sectionPow L (c i) K)) := fun i j =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) (c j) (w i j) (hw i j) K
  -- the numerators agree on the overlaps, by the annihilator and `f i = f j * w i j`
  have hγA : ∀ i j : ι,
      F.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i ^ (q + 1) • cn i)
      = w i j ^ (K + 1) •
          F.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j ^ (q + 1) • cn j) := by
    intro i j
    have hscal : fA i j ^ (q + 1) * w i j ^ k
        = w i j ^ (K + 1) *
          X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j) ^ (q + 1) := by
      rw [hfw i j, mul_pow, hK]
      ring
    simp only [Scheme.Modules.map_smul, map_pow]
    rw [← hfA i j, hm' i j, smul_smul, hscal, smul_smul]
  -- and they compute `t` against the generator over `U ⊓ V i`
  have hγD : ∀ i, F.presheaf.map (homOfLE (hDV i)).op (f i ^ (q + 1) • cn i)
      = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) •
          F.presheaf.map (homOfLE (hDU i)).op t := by
    intro i
    rw [Scheme.Modules.map_smul, map_pow, hcn i le_rfl, smul_smul, ← pow_add,
      ← hK']
  -- the local sections, and their compatibility
  have hcompat0 : ∀ i j : ι,
      (F ⊗ natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
          (tensorSection F (natTensorPow L (powDeg N K)) (f i ^ (q + 1) • cn i)
            (resTop (V i) (globalSection X _ (sectionPow L (c i) K))))
        = (F ⊗ natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
          (tensorSection F (natTensorPow L (powDeg N K)) (f j ^ (q + 1) • cn j)
            (resTop (V j) (globalSection X _ (sectionPow L (c j) K)))) := by
    intro i j
    rw [map_tensorSection, map_tensorSection, res_resTop, res_resTop, hβ i j,
      tensorSection_smul_right, ← tensorSection_smul_left, hγA i j]
  have hcompat : TopCat.Presheaf.IsCompatible (F ⊗ natTensorPow L (powDeg N K)).presheaf V
      (fun i => tensorSection F (natTensorPow L (powDeg N K)) (f i ^ (q + 1) • cn i)
        (resTop (V i) (globalSection X _ (sectionPow L (c i) K)))) := hcompat0
  obtain ⟨τ, hτ, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(F ⊗ natTensorPow L (powDeg N K)).presheaf,
      (F ⊗ natTensorPow L (powDeg N K)).isSheaf⟩ : TopCat.Sheaf Ab X) V ⊤
    (fun _ => homOfLE le_top) hcover _ hcompat
  refine ⟨powDeg N K, globalSection X _ (sectionPow L a K), τ,
    (Stacks.TensorPowerTrivialize.powDeg_eq N K) ▸ Dvd.intro _ rfl, ?_, ?_⟩
  · rw [← hU]
    exact (Stacks.TensorPowerTrivialize.nonvanishingOpen_sectionPow L a K).symm
  · refine TopCat.Presheaf.IsSheaf.section_ext
      (F ⊗ natTensorPow L (powDeg N K)).isSheaf (U := op U) ?_
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover (TopologicalSpace.Opens.mem_top x))
    refine ⟨X.basicOpen (f i), hDU i, ?_, ?_⟩
    · rw [← hD i]; exact ⟨hx, hi⟩
    · have hti : resTop (V i) τ = tensorSection F (natTensorPow L (powDeg N K))
          (f i ^ (q + 1) • cn i)
          (resTop (V i) (globalSection X _ (sectionPow L (c i) K))) := hτ i
      rw [res_resTop, ← res_resTop τ (hDV i), hti, map_tensorSection, res_resTop, hγD i,
        map_tensorSection, res_resTop,
        resTop_eq_smul_of_le (natTensorPow L (powDeg N K)) (hDV i) (f i ^ (K + 1)) (hσ i),
        map_pow, tensorSection_smul_right, ← tensorSection_smul_left]

end Glue

/-! ### The deliverable -/

section Deliverable

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **Ampleness implies the hypothesis of this file**, so what is proved here subsumes
`Stacks.ModuleSectionExtension.exists_tensorSection_of_isAmple`. This is
`Stacks.SectionExtension.exists_pos_affine_nvOpen` with its affineness clause forgotten. -/
theorem hasPointwiseNonvanishing_of_isAmple (hL : IsAmple X L) : HasPointwiseNonvanishing L :=
  fun x => by
    obtain ⟨d, b, hd, hxb, -⟩ := Stacks.SectionExtension.exists_pos_affine_nvOpen L hL x
    exact ⟨d, b, hd, hxb⟩

/-- **Stacks Tag 01PW for an arbitrary quasi-coherent `F`, with no ampleness, in the section-ring
vocabulary.** For `X` quasi-compact and quasi-separated, `L` invertible such that every point lies
in the nonvanishing locus of some homogeneous element of positive degree, `F` quasi-coherent, `a`
homogeneous of positive degree and `t` a section of `F` over `X_a`, there is a tensor power
`L ^⊗ p` carrying a global section `σ` which does not vanish on `X_a` and a global section `τ` of
`F ⊗ L ^⊗ p` with `τ|_{X_a} = t ⊗ σ|_{X_a}`.

This is the statement of `Stacks.ModuleSectionExtension.exists_tensorSection_of_isAmple` with
ampleness of `L` replaced by `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` and
quasi-separatedness of `X` added — Tag 01PW's own hypothesis, which ampleness happened to supply
through `Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`. -/
theorem exists_tensorSection_of_hasPointwiseNonvanishing [CompactSpace X]
    [QuasiSeparatedSpace X] (hpt : HasPointwiseNonvanishing L) (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 1 ≤ n) (a : powSections L n) (U : X.Opens)
    (hU : nvOpen L a = U) (t : Γ(F, U)) :
    ∃ (p : ℕ) (σ : Γ(natTensorPow L p, ⊤)) (τ : Γ(F ⊗ natTensorPow L p, ⊤)), n ∣ p ∧
      U = nonvanishingOpen X (natTensorPow L p) σ ∧
        resTop U τ = tensorSection F (natTensorPow L p) t (resTop U σ) := by
  obtain ⟨N, a', ι, hι, c, V, -, hdvd, ha, hVaff, hVle, hcover⟩ :=
    exists_common_degree_affine_subcover L ‹CompactSpace X› hpt hn a
  have : Finite ι := hι
  have hUeq : nvOpen L a' = U :=
    TopologicalSpace.Opens.ext (by rw [coe_nvOpen, ha, ← coe_nvOpen, hU])
  have hqc : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X) := by
    intro i j
    have h := QuasiSeparatedSpace.inter_isCompact (α := X) (V i : Set X) (V j : Set X)
      (V i).2 (hVaff i).isCompact (V j).2 (hVaff j).isCompact
    rwa [TopologicalSpace.Opens.coe_inf]
  obtain ⟨p, σ, τ, hNp, hloc, heq⟩ := exists_tensorSection_of_quasiCompact_cover L F a' c U hUeq
    V hVle hVaff hqc hcover t
  exact ⟨p, σ, τ, hdvd.trans hNp, hloc, heq⟩

/-- **Stacks Tag 01PW for an arbitrary quasi-coherent `F`, with no ampleness, in the
`Stacks.Ample.tensorPowModule` vocabulary.**

The same statement as
`Stacks.SectionExtensionNoAmple.exists_tensorSection_of_hasPointwiseNonvanishing`
with the tensor powers spelled as `Stacks.Ample.tensorPowModule` and the nonvanishing opens as
`Stacks.AmpleTheory.powNonvanishingOpen`, which is the vocabulary every consumer of the ample
cluster is stated over. The passage is the one of
`Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple`, verbatim:
`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow` is an *equality* of modules, so the
comparison is an `eqToIso`, transported on the locus by `Stacks.Ample.nonvanishingLocus_congr`, on
the restriction by `Stacks.SectionExtension.resTop_app` and on the product of sections by
`Stacks.ModuleSectionExtension.tensorSection_eqToHom`. -/
theorem exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing [CompactSpace X]
    [QuasiSeparatedSpace X] (hpt : HasPointwiseNonvanishing L) (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 1 ≤ n) (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
    (t : Γ(F, Stacks.AmpleTheory.powNonvanishingOpen X L n s)) :
    ∃ (p : ℕ) (σ : Γ(tensorPowModule X L (p : ℤ), ⊤))
      (τ : Γ(F ⊗ tensorPowModule X L (p : ℤ), ⊤)), n ∣ p ∧
      Stacks.AmpleTheory.powNonvanishingOpen X L n s =
          Stacks.AmpleTheory.powNonvanishingOpen X L p σ ∧
        resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) τ =
          tensorSection F (tensorPowModule X L (p : ℤ)) t
            (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ) := by
  obtain ⟨a, ha⟩ := exists_powSections_nvLocus_eq L n s
  obtain ⟨p, σ, τ, hdvd, hσ, heq⟩ := exists_tensorSection_of_hasPointwiseNonvanishing L hpt F hn a
    (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
    (TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, ha, Stacks.AmpleTheory.coe_powNonvanishingOpen])) t
  have hmod : (natTensorPow L p : X.Modules) = tensorPowModule X L (p : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L p
  refine ⟨p, (eqToIso (C := X.Modules) hmod).hom.app ⊤ σ,
    (eqToIso (C := X.Modules) (congrArg (fun P : X.Modules => F ⊗ P) hmod)).hom.app ⊤ τ,
    hdvd, ?_, ?_⟩
  · refine hσ.trans (TopologicalSpace.Opens.ext ?_)
    rw [coe_nonvanishingOpen, Stacks.AmpleTheory.coe_powNonvanishingOpen,
      nonvanishingLocus_congr (eqToIso (C := X.Modules) hmod) σ]
  · rw [Stacks.SectionExtension.resTop_app, heq,
      Stacks.ModuleSectionExtension.tensorSection_eqToHom,
      Stacks.SectionExtension.resTop_app]

end Deliverable

end Stacks.SectionExtensionNoAmple

end
