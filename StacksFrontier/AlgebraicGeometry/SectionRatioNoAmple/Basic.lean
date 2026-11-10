module

public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Cover
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Consumers
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic

/-!
# Section ratios without ampleness

Let `X` be a quasi-compact and quasi-separated scheme and `L` an invertible module on `X` such
that every point of `X` lies in the nonvanishing locus of a homogeneous element of positive degree
(`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`). Then every function on the
nonvanishing locus `X_s` of a global section `s` of a positive tensor power of `L` is a ratio
`t / σ` of two global sections of one tensor power of `L`, with `σ` nowhere vanishing on `X_s`.
This is the surjectivity half of [Stacks, Tag 01PW] for `𝓕 = 𝒪_X`, with ampleness of `L`
replaced by the existence of enough sections.

## Main results

* `Stacks.SectionRatioNoAmple.exists_ratio_of_quasiCompact_cover`: given a finite cover of `X` by
  affine opens `V i` contained in the nonvanishing loci of homogeneous elements `c i` of one
  degree, with quasi-compact pairwise intersections, every function on the nonvanishing locus of
  a homogeneous element of that degree is such a ratio.
* `Stacks.SectionRatioNoAmple.isSectionRatio_of_hasPointwiseNonvanishing`: for `X` quasi-compact
  and quasi-separated and `L` invertible with enough sections,
  `Stacks.SectionExtension.IsSectionRatio X L`.
* `Stacks.SectionRatioNoAmple.basicOpenIsPow_of_hasPointwiseNonvanishing` and
  `Stacks.SectionRatioNoAmple.basicOpenIsPowNonvanishing_of_hasPointwiseNonvanishing`: under the
  same hypotheses, every basic open of a nonvanishing locus `X_s` (of an affine one, in the
  second) is the nonvanishing locus of a global section of a positive tensor power of `L`.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
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
  IsSectionRatio nvOpen_eq exists_tensorPow_ratio)
open Stacks.SectionExtensionNoAmple (HasPointwiseNonvanishing
  exists_common_degree_affine_subcover)

universe u

namespace Stacks.SectionRatioNoAmple

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

/-- Let `a` and `c i` be homogeneous of one degree `N`, let `U = X_a`, and let `V i` be affine
opens with `V i ≤ X_{c i}` covering `X`, finitely many, with quasi-compact pairwise intersections.
Then every function `g` on `U` is the ratio `t / σ` of two global sections of one tensor power of
`L`, with `σ` nowhere vanishing on `U`. -/
theorem exists_ratio_of_quasiCompact_cover {N : ℕ} (a : powSections L N)
    {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, V i ≤ nvOpen L (c i))
    (hcaff : ∀ i, IsAffineOpen (V i))
    (hqc : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i) (g : Γ(X, U)) :
    ∃ (p : ℕ) (t σ : Γ(natTensorPow L p, ⊤)),
      U ≤ nonvanishingOpen X (natTensorPow L p) σ ∧ resTop U t = g • resTop U σ := by
  classical
  have hVle : ∀ i, V i ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) :=
    fun i => (nvOpen_eq L (c i)) ▸ hV i
  choose f hf using fun i : ι => exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ a) (hVle i)
  have hD : ∀ i, U ⊓ V i = X.basicOpen (f i) := fun i => by
    rw [← hU]
    exact nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i)) (globalSection X _ a)
      (hVle i) (f i) (hf i)
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i => by rw [← hD i]; exact inf_le_left
  have hDV : ∀ i, X.basicOpen (f i) ≤ V i := fun i => X.basicOpen_le (f i)
  choose e z hz using fun i : ι => AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen X
    (V i) (hcaff i) (f i) (X.presheaf.map (homOfLE (hDU i)).op g)
  obtain ⟨k, hk⟩ := exists_forall_le e
  obtain ⟨cn, hcn⟩ : ∃ cn : (i : ι) → Γ(X, V i), ∀ (i : ι) {S : X.Opens}
      (h : S ≤ X.basicOpen (f i)) (hSV : S ≤ V i) (hSU : S ≤ U),
      X.presheaf.map (homOfLE hSV).op (cn i)
        = X.presheaf.map (homOfLE hSV).op (f i) ^ k * X.presheaf.map (homOfLE hSU).op g := by
    refine ⟨fun i => f i ^ (k - e i) * z i, fun i S h hSV hSU => ?_⟩
    have h0 : X.presheaf.map (homOfLE (hDV i)).op (z i)
        = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ e i
          * X.presheaf.map (homOfLE (hDU i)).op g := hz i
    change X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i ^ (k - e i) * z i)
      = X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i) ^ k
          * X.presheaf.map (homOfLE (h.trans (hDU i))).op g
    rw [← map_res_res h (hDV i) (f i ^ (k - e i) * z i)]
    simp only [map_mul, map_pow, h0, map_res_res]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hk i)]
  choose w hw using fun (i j : ι) => exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ (c j))
    ((inf_le_left : V i ⊓ V j ≤ V i).trans (hVle i))
  obtain ⟨fA, hfA⟩ : ∃ fA : (i j : ι) → Γ(X, V i ⊓ V j), ∀ i j,
      fA i j = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i) :=
    ⟨_, fun _ _ => rfl⟩
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
    rwa [map_sub, map_mul, map_pow, map_res_res, map_res_res, sub_eq_zero]
  choose m hm using fun (i j : ι) =>
    AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X
      (hqc i j)
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
      (fA i j) (hzero i j)
  obtain ⟨q, hq⟩ := exists_forall_le fun p : ι × ι => m p.1 p.2
  have hm' : ∀ i j : ι, fA i j ^ (q + 1) *
      (X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i)
        - X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j) * w i j ^ k)
        = 0 := by
    intro i j
    rw [← Nat.sub_add_cancel ((hq (i, j)).trans (Nat.le_add_right q 1)), pow_add, mul_assoc,
      hm i j, mul_zero]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = k + (q + 1) := ⟨k + q, by omega⟩
  have hσ : ∀ i, resTop (V i) (globalSection X _ (sectionPow L a K))
      = f i ^ (K + 1) • resTop (V i) (globalSection X _ (sectionPow L (c i) K)) := fun i =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) a (f i) (hf i) K
  have hβ : ∀ i j : ι, resTop (V i ⊓ V j) (globalSection X _ (sectionPow L (c j) K))
      = w i j ^ (K + 1) • resTop (V i ⊓ V j)
          (globalSection X _ (sectionPow L (c i) K)) := fun i j =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) (c j) (w i j) (hw i j) K
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
      rwa [mul_sub, sub_eq_zero] at h
    rw [map_mul, map_pow, map_mul, map_pow, ← hfA i j, hkey, hfw i j, hK]
    ring
  have hγD : ∀ i, X.presheaf.map (homOfLE (hDV i)).op (f i ^ (q + 1) * cn i)
      = X.presheaf.map (homOfLE (hDU i)).op g *
          X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) := by
    intro i
    rw [map_mul, map_pow, hcn i le_rfl (hDV i) (hDU i), hK, pow_add]
    ring
  have hcompat0 : ∀ i j : ι,
      (natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
          ((f i ^ (q + 1) * cn i) • resTop (V i) (globalSection X _ (sectionPow L (c i) K)))
        = (natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
          ((f j ^ (q + 1) * cn j) • resTop (V j)
            (globalSection X _ (sectionPow L (c j) K))) := by
    intro i j
    rw [Scheme.Modules.map_smul, res_resTop, Scheme.Modules.map_smul, res_resTop, hβ i j,
      smul_smul, hγA i j]
  have hcompat : TopCat.Presheaf.IsCompatible (natTensorPow L (powDeg N K)).presheaf V
      (fun i => (f i ^ (q + 1) * cn i) •
        resTop (V i) (globalSection X _ (sectionPow L (c i) K))) := hcompat0
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(natTensorPow L (powDeg N K)).presheaf, (natTensorPow L (powDeg N K)).isSheaf⟩ :
      TopCat.Sheaf Ab X) V ⊤ (fun _ => homOfLE le_top) hcover _ hcompat
  refine ⟨powDeg N K, t, globalSection X _ (sectionPow L a K), ?_, ?_⟩
  · rw [← hU]
    exact (Stacks.TensorPowerTrivialize.nonvanishingOpen_sectionPow L a K).ge
  · refine TopCat.Presheaf.IsSheaf.section_ext
      (natTensorPow L (powDeg N K)).isSheaf (U := op U) fun x hx => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover (TopologicalSpace.Opens.mem_top x))
    refine ⟨X.basicOpen (f i), hDU i, ?_, ?_⟩
    · rw [← hD i]; exact ⟨hx, hi⟩
    · have hti : resTop (V i) t = (f i ^ (q + 1) * cn i) •
          resTop (V i) (globalSection X _ (sectionPow L (c i) K)) := ht i
      rw [res_resTop, ← res_resTop t (hDV i), hti, Scheme.Modules.map_smul, res_resTop,
        Scheme.Modules.map_smul, res_resTop,
        resTop_eq_smul_of_le (natTensorPow L (powDeg N K)) (hDV i) (f i ^ (K + 1)) (hσ i),
        map_pow, smul_smul, hγD i]

end Glue

/-! ### Section ratios and basic opens -/

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

/-- The surjectivity half of [Stacks, Tag 01PW] for `𝓕 = 𝒪_X`: for `X` quasi-compact and
quasi-separated and `L` invertible such that every point lies in the nonvanishing locus of some
homogeneous element of positive degree, every function on a nonvanishing locus `X_s` is the ratio
of two global sections of one tensor power of `L` whose denominator does not vanish on `X_s`. -/
theorem isSectionRatio_of_hasPointwiseNonvanishing [CompactSpace X] [QuasiSeparatedSpace X]
    (hpt : HasPointwiseNonvanishing L) : IsSectionRatio X L := by
  intro n hn s g
  obtain ⟨a₀, ha₀⟩ := exists_powSections_nvLocus_eq L n s
  obtain ⟨N, a, ι, _, c, V, -, -, ha, hVaff, hVle, hcover⟩ :=
    exists_common_degree_affine_subcover L ‹CompactSpace X› hpt hn a₀
  have hqc : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X) := fun i j => by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact (V i : Set X) (V j : Set X)
      (V i).2 (hVaff i).isCompact (V j).2 (hVaff j).isCompact
  obtain ⟨p, t, σ, hle, heq⟩ := exists_ratio_of_quasiCompact_cover L a c
    (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
    (TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, ha, ha₀, Stacks.AmpleTheory.coe_powNonvanishingOpen]))
    V hVle hVaff hqc hcover g
  exact ⟨p, exists_tensorPow_ratio L t σ g hle heq⟩

/-- For `L` invertible with enough sections on a quasi-compact quasi-separated `X`, every basic
open of a nonvanishing locus `X_s` is the nonvanishing locus of a global section of a positive
tensor power of `L`. -/
theorem basicOpenIsPow_of_hasPointwiseNonvanishing [CompactSpace X] [QuasiSeparatedSpace X]
    (hpt : HasPointwiseNonvanishing L) : Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow X L :=
  Stacks.SectionExtension.basicOpenIsPow_of_isSectionRatio X L
    (isSectionRatio_of_hasPointwiseNonvanishing L hpt)

/-- For `L` invertible with enough sections on a quasi-compact quasi-separated `X`, every basic
open of an affine nonvanishing locus `X_s` is the nonvanishing locus of a global section of a
positive tensor power of `L`. -/
theorem basicOpenIsPowNonvanishing_of_hasPointwiseNonvanishing [CompactSpace X]
    [QuasiSeparatedSpace X] (hpt : HasPointwiseNonvanishing L) :
    Stacks.AmplePullback.BasicOpenIsPowNonvanishing X L :=
  Stacks.SectionExtension.basicOpenIsPowNonvanishing_of_isSectionRatio X L
    (isSectionRatio_of_hasPointwiseNonvanishing L hpt)

end Deliverable

end Stacks.SectionRatioNoAmple

end
