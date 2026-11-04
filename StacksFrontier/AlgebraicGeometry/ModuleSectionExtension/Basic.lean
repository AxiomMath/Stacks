module

public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.Scheme

/-!
# Stacks Tag 01PW for an arbitrary quasi-coherent module, for an ample `L`

For `L` ample and `𝓕` quasi-coherent: for `σ` a global section of `L ^⊗ n` with `n ≥ 1` and `τ` a
section of `𝓕` over `X_σ`, there is an exponent `p` and a global section of `𝓕 ⊗ L ^⊗ p`
restricting on `X_σ` to `τ ⊗ σ'|`, where `σ'` is a global section of `L ^⊗ p` not vanishing on
`X_σ`. This is the surjectivity half of Stacks Tag 01PW, in the "after multiplication by a power"
form; the case `𝓕 = 𝒪_X` is `Stacks.SectionExtension.isSectionRatio_of_isAmple`.

## Main results

* `Stacks.ModuleSectionExtension.exists_sectionPow_tensorSection_family_of_affine_cover`: the
  statement for a finite family of sections over one common denominator, against a finite affine
  cover by nonvanishing loci of one common degree `N`, with the denominator named: it is the power
  `a ^ (K + 1)` of the given element.
* `Stacks.ModuleSectionExtension.exists_tensorSection_family_of_affine_cover`: the same with the
  denominator unnamed, of degree a positive multiple of `N`.
* `Stacks.ModuleSectionExtension.exists_tensorSection_of_affine_cover`: the single-section form.
* `Stacks.ModuleSectionExtension.exists_tensorSection_of_isAmple`: for `L` ample and `F`
  quasi-coherent, a section of `F` over `X_a` extends, after tensoring with a power of `L`, to a
  global section.
* `Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple`: the same in the
  `Stacks.Ample.tensorPowModule` vocabulary.
* `Stacks.ModuleSectionExtension.exists_tensorSection_family_of_isAmple` and
  `Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of_isAmple`: the family
  form, in the two vocabularies, with the exponent a multiple of the degree of the given section.
* `Stacks.ModuleSectionExtension.tensorSection_eqToHom`: transport of a product of sections along
  an equality of modules.

## No Stacks attribute is attached

The four labels of Stacks Tag 01PW are assertions about the canonical map
`Γ_*(X, 𝓕)_{(s)} → Γ(X_s, 𝓕)`: that it is injective for `X` quasi-compact, bijective for `X`
quasi-compact and quasi-separated, that it sends `a/sⁿ` to the function characterized by
multiplication by `sⁿ`, and that the induced ring map is an isomorphism. None of them is proved
here: the map is not defined in this file, `L` is assumed ample where Tag 01PW assumes only that
it is invertible, and only the surjectivity direction is produced, in the "after multiplication by
a power" form.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
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

namespace Stacks.ModuleSectionExtension

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

/-- **The gluing argument of Stacks Tag 01PW for a finite family, with one common denominator.**

The hypotheses are a finite family `c i` of homogeneous elements of one degree `N` whose
nonvanishing loci `V i` are affine and cover `X`, a further homogeneous element `a` of the same
degree with `X_a = U`, and a finite family `t l` of sections of `F` over `U`. The conclusion is a
**single** tensor power `L ^⊗ p`, a **single** global section `σ` of it not vanishing on `U`, and
one global section `τ l` of `F ⊗ L ^⊗ p` for each `l`, restricting on `U` to `t l ⊗ σ|_U`. Here
`p = powDeg N K = N (K + 1)` and `σ = a ^ (K + 1)`. -/
theorem exists_sectionPow_tensorSection_family_of_affine_cover (F : X.Modules)
    [F.IsQuasicoherent] {N : ℕ}
    (a : powSections L N) {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, nvOpen L (c i) = V i)
    (hcaff : ∀ i, IsAffineOpen (V i)) (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
    {κ : Type u} [Finite κ] (t : κ → Γ(F, U)) :
    ∃ (K : ℕ) (τ : κ → Γ(F ⊗ natTensorPow L (powDeg N K), ⊤)),
      U = nonvanishingOpen X (natTensorPow L (powDeg N K))
          (globalSection X _ (sectionPow L a K)) ∧
        ∀ l, resTop U (τ l) = tensorSection F (natTensorPow L (powDeg N K)) (t l)
          (resTop U (globalSection X _ (sectionPow L a K))) := by
  classical
  have hVle : ∀ i, V i ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) :=
    fun i => le_of_eq (hV i).symm
  -- the ratio `f i = a / c i` over `V i = X_{c i}`
  choose f hf using fun i : ι => exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ a) (hVle i)
  -- `U ⊓ V i` is the basic open of that ratio
  have hD : ∀ i, U ⊓ V i = X.basicOpen (f i) := fun i => by
    rw [← hU]
    exact nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i)) (globalSection X _ a)
      (hVle i) (f i) (hf i)
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i => by rw [← hD i]; exact inf_le_left
  have hDV : ∀ i, X.basicOpen (f i) ≤ V i := fun i => X.basicOpen_le (f i)
  -- the local extension over the affine `V i`, with one exponent `k`
  choose e z hz using fun il : ι × κ => exists_pow_smul_eq_res F (hcaff il.1) (f il.1)
    (F.presheaf.map (homOfLE (hDU il.1)).op (t il.2))
  obtain ⟨k, hk⟩ := exists_forall_le e
  obtain ⟨cn, hcn⟩ : ∃ cn : (i : ι) → κ → Γ(F, V i), ∀ (i : ι) (l : κ) {S : X.Opens}
      (_ : S ≤ X.basicOpen (f i)) (hSV : S ≤ V i) (hSU : S ≤ U),
      F.presheaf.map (homOfLE hSV).op (cn i l)
        = X.presheaf.map (homOfLE hSV).op (f i) ^ k
          • F.presheaf.map (homOfLE hSU).op (t l) := by
    refine ⟨fun i l => f i ^ (k - e (i, l)) • z (i, l), fun i l S h hSV hSU => ?_⟩
    have h0 : F.presheaf.map (homOfLE (hDV i)).op (z (i, l))
        = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ e (i, l)
          • F.presheaf.map (homOfLE (hDU i)).op (t l) := (hz (i, l)).symm
    show F.presheaf.map (homOfLE (h.trans (hDV i))).op (f i ^ (k - e (i, l)) • z (i, l))
      = X.presheaf.map (homOfLE (h.trans (hDV i))).op (f i) ^ k
          • F.presheaf.map (homOfLE (h.trans (hDU i))).op (t l)
    rw [← map_res_res_module h (hDV i) (f i ^ (k - e (i, l)) • z (i, l))]
    simp only [Scheme.Modules.map_smul, map_pow, h0, map_res_res, map_res_res_module, smul_smul,
      ← pow_add]
    rw [Nat.sub_add_cancel (hk (i, l))]
  -- the ratio `w i j = c j / c i` on the overlap `V i ⊓ V j`, independent of the family index
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
  -- the overlaps are affine, by Stacks Tag 01PV
  have hAaff : ∀ i j : ι, IsAffineOpen (V i ⊓ V j) := fun i j => by
    rw [← hV j]
    exact Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
      (natTensorPow L N) (globalSection X _ (c j)) (hcaff i)
  have hBA : ∀ i j : ι, X.basicOpen (fA i j) ≤ V i ⊓ V j := fun i j => X.basicOpen_le _
  have hBD : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f i) := fun i j => by
    rw [hfA, X.basicOpen_res]; exact inf_le_right
  have hBU : ∀ i j : ι, X.basicOpen (fA i j) ≤ U := fun i j => (hBD i j).trans (hDU i)
  have hBD' : ∀ i j : ι, X.basicOpen (fA i j) ≤ X.basicOpen (f j) := fun i j => by
    rw [← hD j]
    exact le_inf (hBU i j) ((hBA i j).trans inf_le_right)
  -- the two numerators agree where `a` does not vanish, so a power of `f i` kills the difference
  have hzero : ∀ (i j : ι) (l : κ),
      F.presheaf.map (homOfLE (X.basicOpen_le (fA i j))).op
          (F.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i l))
        = F.presheaf.map (homOfLE (X.basicOpen_le (fA i j))).op
          (w i j ^ k •
            F.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j l)) := by
    intro i j l
    have hfib : X.presheaf.map (homOfLE ((hBD i j).trans (hDV i))).op (f i)
        = X.presheaf.map (homOfLE ((hBD' i j).trans (hDV j))).op (f j)
            * X.presheaf.map (homOfLE (hBA i j)).op (w i j) := by
      have h := congrArg (X.presheaf.map (homOfLE (hBA i j)).op)
        ((hfA i j).symm.trans (hfw i j))
      rw [map_mul, map_res_res, map_res_res] at h
      exact h
    rw [map_res_res_module, Scheme.Modules.map_smul, map_pow, map_res_res_module,
      hcn i l (hBD i j) ((hBD i j).trans (hDV i)) (hBU i j),
      hcn j l (hBD' i j) ((hBD' i j).trans (hDV j)) (hBU i j), hfib, smul_smul, mul_pow]
    ring_nf
  -- the annihilator exponent
  choose m hm using fun (r : ι × ι × κ) => exists_pow_smul_eq_of_res_eq F
    (hAaff r.1 r.2.1) (fA r.1 r.2.1)
    (F.presheaf.map (homOfLE (inf_le_left : V r.1 ⊓ V r.2.1 ≤ V r.1)).op (cn r.1 r.2.2))
    (w r.1 r.2.1 ^ k •
      F.presheaf.map (homOfLE (inf_le_right : V r.1 ⊓ V r.2.1 ≤ V r.2.1)).op (cn r.2.1 r.2.2))
    (hzero r.1 r.2.1 r.2.2)
  obtain ⟨q, hq⟩ := exists_forall_le m
  have hm' : ∀ (i j : ι) (l : κ), fA i j ^ (q + 1) •
      (F.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (cn i l))
        = fA i j ^ (q + 1) • (w i j ^ k •
            F.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (cn j l)) := by
    intro i j l
    have hmq : m (i, j, l) ≤ q := hq (i, j, l)
    have h : q + 1 = q + 1 - m (i, j, l) + m (i, j, l) := by omega
    rw [h, pow_add, mul_smul, mul_smul, hm (i, j, l)]
  -- the exponent of the answer: `K + 1 = k + (q + 1)`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = k + (q + 1) := ⟨k + q, by omega⟩
  have hK' : K + 1 = q + 1 + k := by omega
  have hσ : ∀ i, resTop (V i) (globalSection X _ (sectionPow L a K))
      = f i ^ (K + 1) • resTop (V i) (globalSection X _ (sectionPow L (c i) K)) := fun i =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) a (f i) (hf i) K
  have hβ : ∀ i j : ι, resTop (V i ⊓ V j) (globalSection X _ (sectionPow L (c j) K))
      = w i j ^ (K + 1) • resTop (V i ⊓ V j)
          (globalSection X _ (sectionPow L (c i) K)) := fun i j =>
    Stacks.TensorPowerTrivialize.resTop_sectionPow L (c i) (c j) (w i j) (hw i j) K
  -- the numerators agree on the overlaps, by the annihilator and `f i = f j * w i j`
  have hγA : ∀ (i j : ι) (l : κ),
      F.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i ^ (q + 1) • cn i l)
      = w i j ^ (K + 1) •
          F.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
            (f j ^ (q + 1) • cn j l) := by
    intro i j l
    have hscal : fA i j ^ (q + 1) * w i j ^ k
        = w i j ^ (K + 1) *
          X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j) ^ (q + 1) := by
      rw [hfw i j, mul_pow, hK]
      ring
    simp only [Scheme.Modules.map_smul, map_pow]
    rw [← hfA i j, hm' i j l, smul_smul, hscal, smul_smul]
  -- and they compute `t l` against the generator over `U ⊓ V i`
  have hγD : ∀ (i : ι) (l : κ),
      F.presheaf.map (homOfLE (hDV i)).op (f i ^ (q + 1) • cn i l)
      = X.presheaf.map (homOfLE (hDV i)).op (f i) ^ (K + 1) •
          F.presheaf.map (homOfLE (hDU i)).op (t l) := by
    intro i l
    rw [Scheme.Modules.map_smul, map_pow, hcn i l le_rfl (hDV i) (hDU i), smul_smul, ← pow_add,
      ← hK']
  -- the local sections are compatible
  have hcompat0 : ∀ (i j : ι) (l : κ),
      (F ⊗ natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
          (tensorSection F (natTensorPow L (powDeg N K)) (f i ^ (q + 1) • cn i l)
            (resTop (V i) (globalSection X _ (sectionPow L (c i) K))))
        = (F ⊗ natTensorPow L (powDeg N K)).presheaf.map
          (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
          (tensorSection F (natTensorPow L (powDeg N K)) (f j ^ (q + 1) • cn j l)
            (resTop (V j) (globalSection X _ (sectionPow L (c j) K)))) := by
    intro i j l
    rw [map_tensorSection, map_tensorSection, res_resTop, res_resTop, hβ i j,
      tensorSection_smul_right, ← tensorSection_smul_left, hγA i j l]
  have hcompat : ∀ l : κ, TopCat.Presheaf.IsCompatible
      (F ⊗ natTensorPow L (powDeg N K)).presheaf V
      (fun i => tensorSection F (natTensorPow L (powDeg N K)) (f i ^ (q + 1) • cn i l)
        (resTop (V i) (globalSection X _ (sectionPow L (c i) K)))) :=
    fun l i j => hcompat0 i j l
  choose τ hτ using fun l : κ => (TopCat.Sheaf.existsUnique_gluing'
    (⟨(F ⊗ natTensorPow L (powDeg N K)).presheaf,
      (F ⊗ natTensorPow L (powDeg N K)).isSheaf⟩ : TopCat.Sheaf Ab X) V ⊤
    (fun _ => homOfLE le_top) hcover _ (hcompat l)).exists
  refine ⟨K, τ, ?_, fun l => ?_⟩
  · rw [← hU]
    exact (Stacks.TensorPowerTrivialize.nonvanishingOpen_sectionPow L a K).symm
  · refine TopCat.Presheaf.IsSheaf.section_ext
      (F ⊗ natTensorPow L (powDeg N K)).isSheaf (U := op U) ?_
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover (TopologicalSpace.Opens.mem_top x))
    refine ⟨X.basicOpen (f i), hDU i, ?_, ?_⟩
    · rw [← hD i]; exact ⟨hx, hi⟩
    · have hti : resTop (V i) (τ l) = tensorSection F (natTensorPow L (powDeg N K))
          (f i ^ (q + 1) • cn i l)
          (resTop (V i) (globalSection X _ (sectionPow L (c i) K))) := hτ l i
      rw [res_resTop, ← res_resTop (τ l) (hDV i), hti, map_tensorSection, res_resTop, hγD i l,
        map_tensorSection, res_resTop,
        resTop_eq_smul_of_le (natTensorPow L (powDeg N K)) (hDV i) (f i ^ (K + 1)) (hσ i),
        map_pow, tensorSection_smul_right, ← tensorSection_smul_left]

/-- **The gluing argument of Stacks Tag 01PW for a finite family, with one common denominator**,
with the denominator left unnamed: it is a power of `a`, of degree a positive multiple of `N`. -/
theorem exists_tensorSection_family_of_affine_cover (F : X.Modules) [F.IsQuasicoherent] {N : ℕ}
    (a : powSections L N) {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, nvOpen L (c i) = V i)
    (hcaff : ∀ i, IsAffineOpen (V i)) (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
    {κ : Type u} [Finite κ] (t : κ → Γ(F, U)) :
    ∃ (p : ℕ) (σ : Γ(natTensorPow L p, ⊤)) (τ : κ → Γ(F ⊗ natTensorPow L p, ⊤)),
      (∃ k : ℕ, p = N * (k + 1)) ∧
      U = nonvanishingOpen X (natTensorPow L p) σ ∧
        ∀ l, resTop U (τ l) = tensorSection F (natTensorPow L p) (t l) (resTop U σ) := by
  obtain ⟨K, τ, hσ, hτ⟩ := exists_sectionPow_tensorSection_family_of_affine_cover L F a c U hU V hV
    hcaff hcover t
  exact ⟨powDeg N K, globalSection X _ (sectionPow L a K), τ,
    ⟨K, Stacks.TensorPowerTrivialize.powDeg_eq N K⟩, hσ, hτ⟩

/-- **The gluing argument of Stacks Tag 01PW, for an arbitrary quasi-coherent `F`.**

The hypotheses are a finite family `c i` of homogeneous elements of one degree `N` whose
nonvanishing loci `V i` are affine and cover `X`, a further homogeneous element `a` of the same
degree with `X_a = U`, and a section `t` of `F` over `U`. The conclusion is a global section of
`F ⊗ L ^⊗ p` restricting on `U` to `t ⊗ σ|_U`, for `σ` a global section of `L ^⊗ p` not vanishing
on `U`. -/
theorem exists_tensorSection_of_affine_cover (F : X.Modules) [F.IsQuasicoherent] {N : ℕ}
    (a : powSections L N) {ι : Type u} [Finite ι] (c : ι → powSections L N)
    (U : X.Opens) (hU : nvOpen L a = U)
    (V : ι → X.Opens) (hV : ∀ i, nvOpen L (c i) = V i)
    (hcaff : ∀ i, IsAffineOpen (V i)) (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
    (t : Γ(F, U)) :
    ∃ (p : ℕ) (σ : Γ(natTensorPow L p, ⊤)) (τ : Γ(F ⊗ natTensorPow L p, ⊤)),
      U = nonvanishingOpen X (natTensorPow L p) σ ∧
        resTop U τ = tensorSection F (natTensorPow L p) t (resTop U σ) := by
  obtain ⟨p, σ, τ, -, hσ, hτ⟩ := exists_tensorSection_family_of_affine_cover L F a c U hU V hV
    hcaff hcover (κ := PUnit.{u + 1}) (fun _ => t)
  exact ⟨p, σ, τ PUnit.unit, hσ, hτ PUnit.unit⟩

end Glue

/-! ### The deliverable, from ampleness -/

section Ample

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

/-- **Stacks Tag 01PW for an arbitrary quasi-coherent `F`, in the section-ring vocabulary.**

For `L` ample, `F` quasi-coherent, `a` a homogeneous element of positive degree and `t` a section
of `F` over `X_a`, there is a tensor power `L ^⊗ p` carrying a global section `σ` which does not
vanish on `X_a` and a global section `τ` of `F ⊗ L ^⊗ p` with `τ|_{X_a} = t ⊗ σ|_{X_a}`. -/
theorem exists_tensorSection_of_isAmple (hL : IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
    {n : ℕ} (hn : 1 ≤ n) (a : powSections L n) (U : X.Opens) (hU : nvOpen L a = U)
    (t : Γ(F, U)) :
    ∃ (p : ℕ) (σ : Γ(natTensorPow L p, ⊤)) (τ : Γ(F ⊗ natTensorPow L p, ⊤)),
      U = nonvanishingOpen X (natTensorPow L p) σ ∧
        resTop U τ = tensorSection F (natTensorPow L p) t (resTop U σ) := by
  obtain ⟨N, a', F', c, -, -, ha, hcaff, hcover⟩ :=
    Stacks.SectionExtension.exists_common_degree_affine_cover L hL hn a
  have hUeq : nvOpen L a' = U := TopologicalSpace.Opens.ext (by
    rw [coe_nvOpen, ha, ← coe_nvOpen, hU])
  exact exists_tensorSection_of_affine_cover L F a' c U hUeq
    (fun i => nvOpen L (c i)) (fun _ => rfl) hcaff hcover t

/-- **Transport of a product of sections along an equality of modules.** For `hmod : M = M'` an
equality in `X.Modules`, the `eqToIso` comparison carries `m ⊗ n` to `m ⊗ (eqToIso hmod) n`. -/
theorem tensorSection_eqToHom (F : X.Modules) {M M' : X.Modules} (hmod : M = M') (U : X.Opens)
    (m : Γ(F, U)) (n : Γ(M, U)) :
    (eqToIso (C := X.Modules) (congrArg (fun P : X.Modules => F ⊗ P) hmod)).hom.app U
        (tensorSection F M m n)
      = tensorSection F M' m ((eqToIso (C := X.Modules) hmod).hom.app U n) := by
  subst hmod
  simp

/-- Transport of a family of extended sections from `natTensorPow L p` to `tensorPowModule X L p`,
along the equality of these modules. -/
private theorem exists_tensorPow_of_natTensorPow (F : X.Modules) {κ : Type u} (U : X.Opens)
    (p : ℕ) (σ : Γ(natTensorPow L p, ⊤)) (τ : κ → Γ(F ⊗ natTensorPow L p, ⊤))
    (t : κ → Γ(F, U)) (hσ : U = nonvanishingOpen X (natTensorPow L p) σ)
    (heq : ∀ l, resTop U (τ l) = tensorSection F (natTensorPow L p) (t l) (resTop U σ)) :
    ∃ (σ' : Γ(tensorPowModule X L (p : ℤ), ⊤))
      (τ' : κ → Γ(F ⊗ tensorPowModule X L (p : ℤ), ⊤)),
      U = Stacks.AmpleTheory.powNonvanishingOpen X L p σ' ∧
        ∀ l, resTop U (τ' l) = tensorSection F (tensorPowModule X L (p : ℤ)) (t l)
          (resTop U σ') := by
  have hmod : (natTensorPow L p : X.Modules) = tensorPowModule X L (p : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L p
  refine ⟨(eqToIso (C := X.Modules) hmod).hom.app ⊤ σ,
    fun l => (eqToIso (C := X.Modules) (congrArg (fun P : X.Modules => F ⊗ P) hmod)).hom.app ⊤
      (τ l), ?_, fun l => ?_⟩
  · refine hσ.trans (TopologicalSpace.Opens.ext ?_)
    rw [coe_nonvanishingOpen, Stacks.AmpleTheory.coe_powNonvanishingOpen,
      nonvanishingLocus_congr (eqToIso (C := X.Modules) hmod) σ]
  · rw [Stacks.SectionExtension.resTop_app, heq l, tensorSection_eqToHom,
      Stacks.SectionExtension.resTop_app]

/-- **Stacks Tag 01PW for an arbitrary quasi-coherent `F`, in the `tensorPowModule` vocabulary.**

The same statement as `Stacks.ModuleSectionExtension.exists_tensorSection_of_isAmple`, with the
tensor powers spelled as `Stacks.Ample.tensorPowModule` and the nonvanishing opens as
`Stacks.AmpleTheory.powNonvanishingOpen`. The conclusion gives `X_s = X_σ`, not merely
`X_s ≤ X_σ`. -/
theorem exists_tensorPow_tensorSection_of_isAmple (hL : IsAmple X L) (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 1 ≤ n) (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
    (t : Γ(F, Stacks.AmpleTheory.powNonvanishingOpen X L n s)) :
    ∃ (p : ℕ) (σ : Γ(tensorPowModule X L (p : ℤ), ⊤))
      (τ : Γ(F ⊗ tensorPowModule X L (p : ℤ), ⊤)),
      Stacks.AmpleTheory.powNonvanishingOpen X L n s =
          Stacks.AmpleTheory.powNonvanishingOpen X L p σ ∧
        resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) τ =
          tensorSection F (tensorPowModule X L (p : ℤ)) t
            (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ) := by
  obtain ⟨a, ha⟩ := exists_powSections_nvLocus_eq L n s
  obtain ⟨p, σ, τ, hσ, heq⟩ := exists_tensorSection_of_isAmple L hL F hn a
    (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
    (TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, ha, Stacks.AmpleTheory.coe_powNonvanishingOpen])) t
  obtain ⟨σ', τ', hσ', heq'⟩ := exists_tensorPow_of_natTensorPow L F _ p σ
    (fun _ : PUnit.{u + 1} => τ) (fun _ => t) hσ fun _ => heq
  exact ⟨p, σ', τ' PUnit.unit, hσ', heq' PUnit.unit⟩

/-- **Stacks Tag 01PW for a finite family over one common denominator, for an ample `L`**, in the
section-ring vocabulary, with the exponent a multiple of the degree of `a`. -/
theorem exists_tensorSection_family_of_isAmple (hL : IsAmple X L) (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 1 ≤ n) (a : powSections L n) (U : X.Opens)
    (hU : nvOpen L a = U) {κ : Type u} [Finite κ] (t : κ → Γ(F, U)) :
    ∃ (p : ℕ) (σ : Γ(natTensorPow L p, ⊤)) (τ : κ → Γ(F ⊗ natTensorPow L p, ⊤)),
      (∃ e : ℕ, 1 ≤ e ∧ p = n * e) ∧
      U = nonvanishingOpen X (natTensorPow L p) σ ∧
        ∀ l, resTop U (τ l) = tensorSection F (natTensorPow L p) (t l) (resTop U σ) := by
  obtain ⟨N, a', F', c, hN1, hdvd, ha, hcaff, hcover⟩ :=
    Stacks.SectionExtension.exists_common_degree_affine_cover L hL hn a
  obtain ⟨m, rfl⟩ := hdvd
  have hUeq : nvOpen L a' = U := TopologicalSpace.Opens.ext (by
    rw [coe_nvOpen, ha, ← coe_nvOpen, hU])
  obtain ⟨p, σ, τ, ⟨k, hk⟩, hσ, heq⟩ := exists_tensorSection_family_of_affine_cover L F a' c U
    hUeq (fun i => nvOpen L (c i)) (fun _ => rfl) hcaff hcover t
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hN1
  exact ⟨p, σ, τ, ⟨m * (k + 1), Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega)), by rw [hk]; ring⟩, hσ, heq⟩

/-- **Stacks Tag 01PW for a finite family over one common denominator, for an ample `L`**, in the
`Stacks.Ample.tensorPowModule` vocabulary, with the exponent a multiple of the degree of `s`: one
module `F ⊗ L ^⊗ (n e)` with `e ≥ 1`, one global section `σ` of it with `X_s = X_σ`, and a family
of global sections of `F ⊗ L ^⊗ (n e)` restricting to the products `t l ⊗ σ|_{X_s}`. -/
theorem exists_tensorPow_tensorSection_family_of_isAmple (hL : IsAmple X L) (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 1 ≤ n) (s : Γ(tensorPowModule X L (n : ℤ), ⊤))
    {κ : Type u} [Finite κ]
    (t : κ → Γ(F, Stacks.AmpleTheory.powNonvanishingOpen X L n s)) :
    ∃ (p : ℕ) (σ : Γ(tensorPowModule X L (p : ℤ), ⊤))
      (τ : κ → Γ(F ⊗ tensorPowModule X L (p : ℤ), ⊤)), (∃ e : ℕ, 1 ≤ e ∧ p = n * e) ∧
      Stacks.AmpleTheory.powNonvanishingOpen X L n s =
          Stacks.AmpleTheory.powNonvanishingOpen X L p σ ∧
        ∀ l, resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) (τ l) =
          tensorSection F (tensorPowModule X L (p : ℤ)) (t l)
            (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ) := by
  obtain ⟨a, ha⟩ := exists_powSections_nvLocus_eq L n s
  obtain ⟨p, σ, τ, hdvd, hσ, heq⟩ := exists_tensorSection_family_of_isAmple L hL F hn a
    (Stacks.AmpleTheory.powNonvanishingOpen X L n s)
    (TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, ha, Stacks.AmpleTheory.coe_powNonvanishingOpen])) t
  obtain ⟨σ', τ', hσ', heq'⟩ := exists_tensorPow_of_natTensorPow L F _ p σ τ t hσ heq
  exact ⟨p, σ', τ', hdvd, hσ', heq'⟩

end Ample

end Stacks.ModuleSectionExtension

end
