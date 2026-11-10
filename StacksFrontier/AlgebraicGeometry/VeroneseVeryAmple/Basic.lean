module

public import StacksFrontier.AlgebraicGeometry.ChartDictionary.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.EventualGeneration
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.VeryAmpleProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Proper
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseAwayClosure

/-!
# A Veronese subring generated in degree one makes the twist very ample

Let `k` be a field, `X` a proper scheme over `k` with `H⁰(X, 𝒪_X) = k`, and `ℒ` an ample
invertible `𝒪_X`-module with graded section ring `S = Γ_*(X, ℒ)`. If for some `d > 0` the
`S₀`-module `S_d` is spanned by finitely many elements `b₀, …, b_N` and the Veronese subring
`S^{(d)} = ⨁_n S_{nd}` is generated in degree one, then `ℒ^{⊗ d}` is very ample on `X` over `k`.

This is the closing sentence of the proof of [Stacks, Tag 0E8V] (and of [Stacks, Tag 0E8W]):
"`X = Proj(S)` … Thus `S^{(6)}` is generated in degree `1`. This means that `ℒ^{⊗ 6}` is very
ample". The argument is the coordinate one:

* the `b_j`, read as global sections of `ℒ^{⊗ d}`, have no common zero: a common zero would kill
  every product of elements of `S_d`, hence by Veronese generation all of `S_{nd}`, hence the
  `d`-th power of a section not vanishing there, which ampleness provides;
* they therefore define a morphism `p : X ⟶ ℙᴺ_k` pulling `𝒪(1)` back to `ℒ^{⊗ d}`
  (`Stacks.AmpleImmersionReduction.twistPullback`);
* each chart `X_{b_i}` is affine, being the preimage of `D₊(b_i)` under the isomorphism
  `X ≅ Proj S` of [Stacks, Tag 0C6J]; its ring of functions is `S_{(b_i)}`
  ([Stacks, Tag 01PW], `Stacks.SectionRingChartBijective.chartRingMap_bijective`), which Veronese
  generation makes the polynomials over `S₀ = k` in the ratios `b_j / b_i`
  (`Stacks.VeroneseAwayClosure.mem_closure`); so `p` is a closed immersion on every chart, hence an
  immersion (`Stacks.ChartDictionary.isImmersion_of_closure`);
* an immersion into `ℙᴺ_k` carrying `𝒪(1)` to `ℒ^{⊗ d}` is very ampleness in the sense of
  [Stacks, Tag 01VM] (`Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion`).

## Main results

* `Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_natTensorPow_of_span`: the statement, for the
  `d`-th tensor power in its recursive spelling.
* `Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_tensorPowModule_of_span`: the same for
  `Stacks.Ample.tensorPowModule X ℒ d`.

## References

* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 0E8W](https://stacks.math.columbia.edu/tag/0E8W)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HomogeneousLocalization
open Stacks.Ample
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen nvLocus grading)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.VeroneseVeryAmple

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

/-! ### The family of global sections -/

variable {d : ℕ} {N : ℕ} (b : Fin (N + 1) → powSections L d)

/-- **The family `b` read as global sections of `ℒ^{⊗ d}`.** -/
abbrev secFamily : Fin (N + 1) → Γ(natTensorPow L d, ⊤) := fun j => globalSection X _ (b j)

/-- The charts of the family are the nonvanishing opens of the homogeneous elements. -/
theorem nvCover_secFamily (j : Fin (N + 1)) :
    Stacks.ProjectiveFromSections.nvCover (secFamily L b) j = nvOpen L (b j) :=
  rfl

/-- **The two ratios agree.** The ratio `b_j / b_i` of the section-ring vocabulary is the
coordinate ratio of the family on its `i`-th chart: both are the unique function multiplying
`b_i` to `b_j` there. -/
theorem ratio_eq_ratio (i j : Fin (N + 1)) :
    Stacks.SectionRingChartMap.ratio L (b i) le_rfl (b j) =
      Stacks.ProjectiveFromSections.ratio (secFamily L b) i j := by
  refine Stacks.ProjectiveFromSections.eq_div _ _ ?_
  exact Stacks.SectionRingChartMap.ratio_smul_resTop L (b i) le_rfl (b j)

/-- **The chart ring map on the fraction `b_j / b_i`** is the coordinate ratio. -/
theorem chartRingMap_mk_one (i j : Fin (N + 1))
    (h : DirectSum.of (powSections L) d (b j) ∈ grading L (1 • d)) :
    Stacks.SectionRingChartMap.chartRingMap L (b i) le_rfl
        (Away.mk (grading L) (Stacks.ExternalGrading.of_mem_summand d (b i)) 1
          (DirectSum.of (powSections L) d (b j)) h) =
      Stacks.ProjectiveFromSections.ratio (secFamily L b) i j := by
  have hz : DirectSum.of (powSections L) d (b j) ∈ grading L (d * 1) := by simpa using h
  have hof : DirectSum.of (powSections L) (d * 1) (Stacks.SectionExtension.powSec L (b i) 1) =
      DirectSum.of (powSections L) d (b i) := by
    rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, pow_one]
  rw [Stacks.SectionRingChartMap.chartRingMap_mk,
    Stacks.SectionRingChartMap.chartFamily_apply,
    Stacks.SectionRingChartMap.numMapR_of_mul L _ _ 1 le_rfl _ hz,
    Stacks.SectionRingChartMap.numMapR_def,
    Stacks.SectionRingChartMap.ratioR_congr L (by omega : d * 1 = d) _ _ _ le_rfl hof,
    Stacks.SectionRingChartMap.ratioR_of, ratio_eq_ratio]

/-! ### The charts cover -/

variable {L b}

/-- **The `b_j` have no common zero.** If every `b_j` vanished at `x`, so would every element of
`S_d` (they span it), every product of elements of `S_d`, hence by Veronese generation every
element of every `S_{nd}`; but ampleness gives a homogeneous `t` of positive degree `m` not
vanishing at `x`, and `t^d ∈ S_{md}` does not vanish there either. -/
theorem exists_mem_nvOpen (hL : IsAmple X L) (hd : 0 < d)
    (hspan : (grading L d : Set (sectionRing L)) ⊆
      (Submodule.span (Stacks.Veronese.gradeZero (grading L))
        (Set.range fun j => DirectSum.of (powSections L) d (b j)) : Set (sectionRing L)))
    (hver : Stacks.Veronese.VeroneseGeneratedInDegOne (grading L) d) (x : X) :
    ∃ j, x ∈ nvOpen L (b j) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, t, hm, hxt, -⟩ := Stacks.SectionExtension.exists_pos_affine_nvOpen L hL x
  set I := Stacks.AmpleFiniteAvoidance.sectionsIdeal L ({x}ᶜ : Set X) with hI
  have hb : ∀ j, DirectSum.of (powSections L) d (b j) ∈ I := fun j =>
    Stacks.AmpleFiniteAvoidance.of_mem_sectionsIdeal_iff.mpr fun y hy hyx => by
      rw [Set.mem_singleton_iff] at hyx
      subst hyx
      exact hcon j (by rw [← SetLike.mem_coe, Stacks.AmpleFiniteAvoidance.coe_nvOpen]; exact hy)
  -- the span of the `b_j` lies in `I`
  have hspanI : ∀ z ∈ Submodule.span (Stacks.Veronese.gradeZero (grading L))
      (Set.range fun j => DirectSum.of (powSections L) d (b j)), z ∈ I := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw => obtain ⟨j, rfl⟩ := hw; exact hb j
    | zero => exact zero_mem _
    | add w w' _ _ hw hw' => exact add_mem hw hw'
    | smul c w _ hw => exact I.mul_mem_left (c : sectionRing L) hw
  have hSd : ∀ z ∈ grading L d, z ∈ I := fun z hz => hspanI z (hspan hz)
  -- products of `m ≥ 1` elements of `S_d` lie in `I`
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hprod : ∀ z ∈ Submodule.span (Stacks.Veronese.gradeZero (grading L))
      (Stacks.Veronese.degOneProducts (grading L) d (m' + 1)), z ∈ I := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, hg, rfl⟩ := hw
      rw [Fin.prod_univ_succ]
      exact I.mul_mem_right _ (hSd _ (hg 0))
    | zero => exact zero_mem _
    | add w w' _ _ hw hw' => exact add_mem hw hw'
    | smul c w _ hw => exact I.mul_mem_left (c : sectionRing L) hw
  -- the `d`-th power of `t`
  have hpow : DirectSum.of (powSections L) (m' + 1) t ^ d ∈ grading L ((m' + 1) * d) := by
    have h := SetLike.pow_mem_graded d (Stacks.ExternalGrading.of_mem_summand (m' + 1) t)
    rwa [smul_eq_mul, mul_comm] at h
  have hpowI : DirectSum.of (powSections L) (m' + 1) t ^ d ∈ I := by
    have h : (DirectSum.of (powSections L) (m' + 1) t ^ d : sectionRing L) ∈
        ((grading L ((m' + 1) * d) : AddSubgroup (sectionRing L)) : Set (sectionRing L)) := hpow
    rw [hver (m' + 1) (by omega)] at h
    exact hprod _ h
  rw [← Stacks.SectionRingChartMap.of_powSec_eq_pow,
    Stacks.AmpleFiniteAvoidance.of_mem_sectionsIdeal_iff] at hpowI
  have hx : x ∈ nvOpen L (Stacks.SectionExtension.powSec L t d) :=
    Stacks.SectionRingChartMap.le_nvOpen_powSec L t le_rfl d hd hxt
  rw [← SetLike.mem_coe, Stacks.AmpleFiniteAvoidance.coe_nvOpen] at hx
  exact hpowI hx rfl

/-! ### The functions on a chart -/

/-- **The functions on the chart `X_{b_i}` are generated by the base and the coordinate ratios.**
By [Stacks, Tag 01PW] every function on `X_{b_i}` is the image under the chart ring map of an
element of `S_{(b_i)}`, which by Veronese generation lies in the subring generated by `S₀` and the
fractions `b_j / b_i`; the chart ring map sends `S₀` to restrictions of global functions, which
come from the base, and `b_j / b_i` to the coordinate ratio. -/
theorem mem_closure_chart (hL : IsAmple X L) (hd : 0 < d)
    (hspan : (grading L d : Set (sectionRing L)) ⊆
      (Submodule.span (Stacks.Veronese.gradeZero (grading L))
        (Set.range fun j => DirectSum.of (powSections L) d (b j)) : Set (sectionRing L)))
    (hver : Stacks.Veronese.VeroneseGeneratedInDegOne (grading L) d)
    {S : Scheme.{u}} (f : X ⟶ S) (hsurj : Function.Surjective f.appTop)
    (i : Fin (N + 1)) (hle : nvOpen L (b i) ≤ f ⁻¹ᵁ ⊤) (y : Γ(X, nvOpen L (b i))) :
    y ∈ Subring.closure (Set.range (fun r => (f.appLE ⊤ (nvOpen L (b i)) hle).hom r) ∪
      Set.range (Stacks.ProjectiveFromSections.ratio (secFamily L b) i)) := by
  obtain ⟨z, rfl⟩ := (Stacks.SectionRingChartBijective.chartRingMap_bijective L hL hd (b i)).2 y
  have hz := Stacks.VeroneseAwayClosure.mem_closure (grading L)
    (Stacks.ExternalGrading.of_mem_summand d (b i))
    (fun j => DirectSum.of (powSections L) d (b j))
    (fun j => Stacks.ExternalGrading.of_mem_summand d (b j)) hspan hver z
  set T := Subring.closure (Set.range (fun r => (f.appLE ⊤ (nvOpen L (b i)) hle).hom r) ∪
      Set.range (Stacks.ProjectiveFromSections.ratio (secFamily L b) i)) with hT
  have key : Stacks.VeroneseAwayClosure.closureSubring (grading L)
      (Stacks.ExternalGrading.of_mem_summand d (b i))
      (fun j => DirectSum.of (powSections L) d (b j))
      (fun j => Stacks.ExternalGrading.of_mem_summand d (b j)) ≤
      T.comap (Stacks.SectionRingChartMap.chartRingMap L (b i) le_rfl) := by
    refine Subring.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
    · change Stacks.SectionRingChartMap.chartRingMap L (b i) le_rfl _ ∈ T
      rw [Stacks.SectionRingProjMorphism.ToSpecZero.chartRingMap_fromZero]
      obtain ⟨r, hr⟩ := hsurj (Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom L c)
      rw [← hr]
      exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    · change Stacks.SectionRingChartMap.chartRingMap L (b i) le_rfl _ ∈ T
      rw [chartRingMap_mk_one]
      exact Subring.subset_closure (Or.inr ⟨j, rfl⟩)
  exact key hz

/-! ### Very ampleness -/

variable (L b)

/-- **A Veronese subring generated in degree one makes the twist very ample.** Let `k` be a field,
`f : X ⟶ Spec k` proper with `H⁰(X, 𝒪_X) = k`, and `ℒ` ample. If `S_d` (`d > 0`) is spanned over
`S₀` by `b₀, …, b_N` and `S^{(d)}` is generated in degree one, then `ℒ^{⊗ d}` is very ample
relative to `f`, in the sense of [Stacks, Tag 01VM]. -/
theorem isRelativelyVeryAmple_natTensorPow_of_span (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hL : IsAmple X L) (hd : 0 < d)
    (hspan : (grading L d : Set (sectionRing L)) ⊆
      (Submodule.span (Stacks.Veronese.gradeZero (grading L))
        (Set.range fun j => DirectSum.of (powSections L) d (b j)) : Set (sectionRing L)))
    (hver : Stacks.Veronese.VeroneseGeneratedInDegOne (grading L) d) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (natTensorPow L d) := by
  have hs : Stacks.ProjectiveFromSections.GeneratesStalks (secFamily L b) :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _
      (exists_mem_nvOpen hL hd hspan hver)
  obtain ⟨p, hpf, hchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks
      (secFamily L b) hs f
  have hiso := Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper L hL f
  have haff : ∀ i, IsAffineOpen (Stacks.ProjectiveFromSections.nvCover (secFamily L b) i) := by
    intro i
    rw [nvCover_secFamily, ← Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen
      L hL (b i) hd]
    exact (Proj.isAffineOpen_basicOpen (grading L) _
      (Stacks.ExternalGrading.of_mem_summand d (b i)) hd).preimage_of_isIso _
  have hsurj : Function.Surjective f.appTop := by
    have hb := ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)
    intro y
    obtain ⟨r, hr⟩ := hb.2 y
    exact ⟨_, hr⟩
  have hle : ∀ i : Fin (N + 1),
      Stacks.ProjectiveFromSections.nvCover (secFamily L b) i ≤ f ⁻¹ᵁ ⊤ := fun _ => by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  have himm : IsImmersion p :=
    Stacks.ChartDictionary.isImmersion_of_closure (secFamily L b) hs p hpf hchart haff
      (fun _ => ⊤) (fun _ => isAffineOpen_top _) hle
      (fun i y => mem_closure_chart hL hd hspan hver f hsurj i (hle i) y)
  obtain ⟨e⟩ := Stacks.AmpleImmersionReduction.twistPullback f (natTensorPow L d) N
    (secFamily L b) hs p hpf hchart
  exact Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion N f _ p himm hpf e

/-- **`ℒ^{⊗ d}` in the `Stacks.Ample.tensorPowModule` spelling.** The two spellings of the `d`-th
power are equal (`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow`), and relative very
ampleness only sees the module through an isomorphism. -/
theorem isRelativelyVeryAmple_tensorPowModule_of_natTensorPow {S : Scheme.{u}} (f : X ⟶ S)
    (h : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (natTensorPow L d)) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)) := by
  have hmod : (natTensorPow L d : X.Modules) = tensorPowModule X L (d : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L d
  obtain ⟨E, hE, i, hi, hover, ⟨e⟩⟩ := h
  exact ⟨E, hE, i, hi, hover, ⟨eqToIso hmod.symm ≪≫ e⟩⟩

/-! ### A finite spanning family from finitely many homogeneous generators -/

/-- **`S_D` is spanned by finitely many elements** when `S` is generated over `S₀` by finitely many
homogeneous elements of positive degree: the monomials of total degree `D` in the generators are
finitely many, since every exponent is at most `D`, and they span `S_D`
(`Stacks.Veronese.mem_span_monomials`). They are listed as a family indexed by `Fin (N + 1)`,
padded by `0`. -/
theorem exists_span_of_generators {r : ℕ} (g : Fin r → sectionRing L) (deg : Fin r → ℕ)
    (hdeg1 : ∀ i, 1 ≤ deg i) (hg : ∀ i, g i ∈ grading L (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero (grading L)) (Set.range g) = ⊤) (D : ℕ) :
    ∃ (N : ℕ) (b : Fin (N + 1) → powSections L D),
      (grading L D : Set (sectionRing L)) ⊆
        (Submodule.span (Stacks.Veronese.gradeZero (grading L))
          (Set.range fun j => DirectSum.of (powSections L) D (b j)) : Set (sectionRing L)) := by
  classical
  set Mon : Set (sectionRing L) :=
    {x | ∃ e : Fin r → ℕ, (∑ i, e i * deg i = D) ∧ x = ∏ i, g i ^ e i} with hMon
  have hMonfin : Mon.Finite := by
    have hbox : (Set.pi Set.univ fun _ : Fin r => Set.Iic D).Finite :=
      Set.Finite.pi fun _ => Set.finite_Iic D
    refine (hbox.image fun e => ∏ i, g i ^ e i).subset ?_
    rintro _ ⟨e, he, rfl⟩
    refine ⟨e, fun i _ => ?_, rfl⟩
    have h1 : e i ≤ e i * deg i := Nat.le_mul_of_pos_right _ (hdeg1 i)
    have h2 : e i * deg i ≤ ∑ j, e j * deg j :=
      Finset.single_le_sum (f := fun j => e j * deg j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    exact (h1.trans h2).trans he.le
  have hMongr : ∀ x ∈ Mon, x ∈ grading L D := by
    rintro _ ⟨e, he, rfl⟩
    have h := SetLike.prod_mem_graded (grading L) (fun i => e i * deg i) (fun i => g i ^ e i)
      (F := (Finset.univ : Finset (Fin r)))
      fun i (_ : i ∈ Finset.univ) => Stacks.Veronese.pow_mem_grade (grading L) g deg hg i (e i)
    rwa [he] at h
  set P : Set (powSections L D) := {c | DirectSum.of (powSections L) D c ∈ Mon} with hP
  have hPfin : P.Finite :=
    hMonfin.preimage (DirectSum.of_injective (β := fun n => powSections L n) D).injOn
  obtain ⟨n, b₀, hb₀⟩ := hPfin.fin_embedding
  refine ⟨n, fun j => if h : (j : ℕ) < n then b₀ ⟨j, h⟩ else 0, ?_⟩
  refine (Stacks.Veronese.mem_span_monomials (grading L) g deg hg hgen D).trans ?_
  refine Submodule.span_mono ?_
  intro x hx
  obtain ⟨c, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp (hMongr x hx)
  have hc : c ∈ Set.range b₀ := by rw [hb₀]; exact hx
  obtain ⟨j, rfl⟩ := hc
  refine ⟨Fin.castSucc j, ?_⟩
  simp only [Fin.val_castSucc, j.isLt, dite_true]

/-- **A Veronese subring generated in degree one makes the twist very ample**, with the finite
spanning family produced from finitely many homogeneous generators of positive degree. Let `k` be
a field, `f : X ⟶ Spec k` proper with `H⁰(X, 𝒪_X) = k`, `ℒ` ample, and `S = Γ_*(X, ℒ)` generated
over `S₀` by finitely many homogeneous elements of positive degree. If `S^{(d)}` (`d > 0`) is
generated in degree one, then `ℒ^{⊗ d}` is very ample relative to `f`
([Stacks, Tag 01VM]).

This is the closing sentence of the proofs of [Stacks, Tag 0E8V] and [Stacks, Tag 0E8W]. -/
theorem isRelativelyVeryAmple_tensorPowModule_of_generators (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hL : IsAmple X L) {r : ℕ} (g : Fin r → sectionRing L) (deg : Fin r → ℕ)
    (hdeg1 : ∀ i, 1 ≤ deg i) (hg : ∀ i, g i ∈ grading L (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero (grading L)) (Set.range g) = ⊤)
    (hd : 0 < d) (hver : Stacks.Veronese.VeroneseGeneratedInDegOne (grading L) d) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)) := by
  obtain ⟨N, b, hspan⟩ := exists_span_of_generators L g deg hdeg1 hg hgen d
  exact isRelativelyVeryAmple_tensorPowModule_of_natTensorPow L f
    (isRelativelyVeryAmple_natTensorPow_of_span L b k f hL hd hspan hver)

end Stacks.VeroneseVeryAmple

end
