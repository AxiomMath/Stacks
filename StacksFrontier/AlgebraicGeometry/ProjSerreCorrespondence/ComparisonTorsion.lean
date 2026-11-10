module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleDegreeZeroFlat
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.Basic

/-!
# The kernel and the cokernel of `𝒨 n ⟶ Γ(X, M(n)~)` are irrelevant-power torsion

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring generated in degree one over `𝒮 0`, let
`X = Proj 𝒮`, and let `M = ⨁_{i ∈ ℤ} 𝒨 i` be a `ℤ`-graded `S`-module. Equation 01MR gives in
every degree a canonical map

`𝒨 n ⟶ Γ(X, M(n)~)`,

namely `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`. This file proves
that both the kernel and the cokernel of that map are torsion for the irrelevant ideal `𝒮₊`: a
homogeneous element whose section vanishes is annihilated by a power of `𝒮₊`, and a power of
`𝒮₊` carries any prescribed global section into the image.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.exists_pow_smul_eq_zero_of_degreeNToGlobalSections_eq_zero`: if the section attached to a
  homogeneous element vanishes then every degree-one element of `S` annihilates that element
  after raising it to a power.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.exists_irrelevant_pow_smul_eq_zero_of_degreeNToGlobalSections_eq_zero`: **the kernel is
  `𝒮₊`-power torsion** — over a Noetherian `S` generated in degree one, a power of the
  irrelevant ideal annihilates every homogeneous element of the kernel.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.degreeNToGlobalSections_eq_zero_of_forall_exists_pow_smul_eq_zero` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.degreeNToGlobalSections_eq_zero_of_irrelevant_pow_smul_eq_zero`: the converses, which need
  no Noetherian hypothesis.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.degreeNToGlobalSections_eq_zero_iff`: **the
  criterion**, that the section of a homogeneous element vanishes exactly when a power of the
  irrelevant ideal annihilates it.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.exists_pow_smul_eq_zero_of_forall_fiber_eq_zero`: a homogeneous element of `M` dying in every
  fiber over a standard open of positive degree is annihilated by a power of that element's
  defining scalar.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_fraction_of_shiftedSectionsComponent`:
  on the standard open of a degree-one element a global section of `M(n)~` is a single
  homogeneous fraction.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.exists_pow_smul_mem_range_degreeNToGlobalSections`: **the cokernel is killed by powers of the
  degree-one elements** — for every degree-one `f` some `f ^ k` carries a prescribed global
  section of `M(n)~` into the image of the comparison in degree `k + n`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.homogeneousScalarGlobalSections_eq_degreeNToGlobalSections_iff`: membership in the image of
  the comparison, read pointwise in the module fibers.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.exists_irrelevant_pow_smul_mem_range_degreeNToGlobalSections`: **the cokernel is
  `𝒮₊`-power torsion** — over a Noetherian `S` generated in degree one by finitely many
  elements, a power of the irrelevant ideal carries a prescribed global section into the image.

## Implementation notes

The map `degreeNToGlobalSections 𝒮 𝒨 n` is by construction the degree-zero global-sections map
of Tag 0AG1 applied to the shift `M(n) = shiftedGrading 𝒨 n`, under the identification
`M(n)₀ = 𝒨 n` of `Stacks.GradedModule.shiftedGrading_zero`; so all the degree bookkeeping below
runs in the shifted grading.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Equation 27.10.0.6, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (degreeNToGlobalSections degreeNToGlobalSections_apply shiftedSectionsComponent
    homogeneousScalarGlobalSections homogeneousScalarGlobalSections_apply)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
  (degreeZeroToGlobalSections degreeZeroToGlobalSections_basicOpen)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w t

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- A fraction `w / s` vanishes in a localization once some element of the submonoid kills `w`. -/
private theorem mk_eq_zero_of_smul_eq_zero {p : Submonoid S} {w : M} (u s : p)
    (hu : (u : S) • w = 0) : (LocalizedModule.mk w s : LocalizedModule p M) = 0 := by
  rw [← LocalizedModule.zero_mk (M := M) (1 : p), LocalizedModule.mk_eq]
  exact ⟨u, by simpa only [Submonoid.smul_def, one_smul, smul_zero] using hu⟩

/-- Graded scalar multiplication, with the resulting degree rewritten along an equality. -/
private theorem graded_smul_mem_of_eq {R N A B : Type*} [Semiring R] [AddCommMonoid N]
    [Module R N] [SetLike A R] [SetLike B N] (𝒜 : ℕ → A) (ℬ : ℤ → B) [SetLike.GradedSMul 𝒜 ℬ]
    {p : ℕ} {q r : ℤ} {a : R} (ha : a ∈ 𝒜 p) {m : N} (hm : m ∈ ℬ q) (h : (p : ℤ) + q = r) :
    a • m ∈ ℬ r :=
  h ▸ SetLike.GradedSMul.smul_mem ha hm

/-- **If the canonical section of `M(n)~` attached to a homogeneous element `m` of degree `n`
vanishes, then every degree-one element of `S` annihilates `m` after raising it to a power.** -/
theorem exists_pow_smul_eq_zero_of_degreeNToGlobalSections_eq_zero (i : ℤ) (m : 𝒨 i)
    (hm : degreeNToGlobalSections 𝒮 𝒨 i m = 0) {f : S} (hf : f ∈ 𝒮 1) :
    ∃ k : ℕ, f ^ k • (m : M) = 0 := by
  have hm0 : (m : M) ∈ shiftedGrading 𝒨 i 0 := by
    simpa only [shiftedGrading, zero_add] using m.2
  have hzero : degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 i) ⟨(m : M), hm0⟩ = 0 := hm
  have hfrac := degreeZeroToGlobalSections_basicOpen 𝒮 (shiftedGrading 𝒨 i) hf Nat.one_pos
    ⟨(m : M), hm0⟩
  rw [hzero, map_zero] at hfrac
  exact (Stacks.SheafOfModules.eq_zero_iff_exists_pow_smul_eq_zero 𝒮 (shiftedGrading 𝒨 i)
    _ 0 (m : M) rfl).mp (hfrac.symm.trans (map_zero _))

/-- **The kernel of the comparison is `𝒮₊`-power torsion.** Over a Noetherian graded ring
generated in degree one over `𝒮 0`, if the canonical section of `M(n)~` attached to a
homogeneous element `m` of degree `n` vanishes then some power of the irrelevant ideal
annihilates `m`. -/
theorem exists_irrelevant_pow_smul_eq_zero_of_degreeNToGlobalSections_eq_zero
    [IsNoetherianRing S] (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    (i : ℤ) (m : 𝒨 i) (hm : degreeNToGlobalSections 𝒮 𝒨 i m = 0) :
    ∃ N : ℕ, ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N, a • (m : M) = 0 := by
  have hrad : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤
      (Submodule.span S {(m : M)}).annihilator.radical := by
    rw [← span_degreeOne_eq_irrelevant 𝒮 hgen, Ideal.span_le]
    intro g hg
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_degreeNToGlobalSections_eq_zero 𝒮 𝒨 i m hm
      (SetLike.mem_coe.mp hg)
    exact ⟨k, (Submodule.mem_annihilator_span_singleton _ _).2 hk⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (Ideal.fg_of_isNoetherianRing _)
  exact ⟨N, fun a ha => (Submodule.mem_annihilator_span_singleton _ _).1 (hN ha)⟩

omit [Decomposition 𝒨] in
/-- **If every degree-one element of `S` annihilates `m` after raising it to a power, then the
canonical section of `M(n)~` attached to `m` vanishes.** -/
theorem degreeNToGlobalSections_eq_zero_of_forall_exists_pow_smul_eq_zero
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (i : ℤ) (m : 𝒨 i)
    (h : ∀ f ∈ 𝒮 1, ∃ k : ℕ, f ^ k • (m : M) = 0) :
    degreeNToGlobalSections 𝒮 𝒨 i m = 0 := by
  have hcover : ⨆ f : 𝒮 1, ProjectiveSpectrum.basicOpen 𝒮 (f : S) = ⊤ :=
    Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen
  apply (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 i) ⊤).injective
  apply Subtype.ext
  funext x
  have hxcover : x.1 ∈ ⨆ f : 𝒮 1, ProjectiveSpectrum.basicOpen 𝒮 (f : S) := by
    rw [hcover]; exact Set.mem_univ _
  obtain ⟨f, hxf⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  obtain ⟨k, hk⟩ := h (f : S) f.2
  exact (degreeNToGlobalSections_apply 𝒮 𝒨 i m x.1).trans <| mk_eq_zero_of_smul_eq_zero
    ⟨(f : S) ^ k, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hxf k⟩ 1 hk

omit [Decomposition 𝒨] in
/-- **If a power of the irrelevant ideal annihilates a homogeneous element `m`, then the
canonical section of `M(n)~` attached to `m` vanishes.** -/
theorem degreeNToGlobalSections_eq_zero_of_irrelevant_pow_smul_eq_zero
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (i : ℤ) (m : 𝒨 i) {N : ℕ}
    (hN : ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N, a • (m : M) = 0) :
    degreeNToGlobalSections 𝒮 𝒨 i m = 0 :=
  degreeNToGlobalSections_eq_zero_of_forall_exists_pow_smul_eq_zero 𝒮 𝒨 hgen i m
    fun _ hf => ⟨N, hN _ (Ideal.pow_mem_pow (mem_irrelevant_of_mem_of_pos 𝒮 hf Nat.one_pos) N)⟩

/-- **The criterion: over a Noetherian graded ring generated in degree one over `𝒮 0`, the
canonical section of `M(n)~` attached to a homogeneous element of degree `n` vanishes exactly
when some power of the irrelevant ideal annihilates that element.** Equivalently, the kernel of
the comparison `𝒨 n ⟶ Γ(Proj 𝒮, M(n)~)` of Equation 01MR is the `𝒮₊`-power torsion part. -/
theorem degreeNToGlobalSections_eq_zero_iff [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (i : ℤ) (m : 𝒨 i) :
    degreeNToGlobalSections 𝒮 𝒨 i m = 0 ↔
      ∃ N : ℕ, ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N, a • (m : M) = 0 :=
  ⟨exists_irrelevant_pow_smul_eq_zero_of_degreeNToGlobalSections_eq_zero 𝒮 𝒨 hgen i m,
    fun ⟨_, hN⟩ => degreeNToGlobalSections_eq_zero_of_irrelevant_pow_smul_eq_zero 𝒮 𝒨 hgen i m hN⟩

/-! ### The cokernel -/

/-- A power of a homogeneous element of degree one is homogeneous of degree the exponent. -/
theorem pow_mem_graded_of_mem_one {f : S} (hf : f ∈ 𝒮 1) (k : ℕ) : f ^ k ∈ 𝒮 k := by
  simpa using SetLike.pow_mem_graded k hf

/-- **A homogeneous element of `M` that dies in every fiber of `M̃` over a standard open `D₊(h)`
of a positive-degree homogeneous `h` is annihilated by a power of `h`.** -/
theorem exists_pow_smul_eq_zero_of_forall_fiber_eq_zero {d : ℕ} (hd : 0 < d) {h : S}
    (hh : h ∈ 𝒮 d) {p : ℤ} {w : M} (hw : w ∈ 𝒨 p)
    (hvanish : ∀ x : ProjectiveSpectrum.basicOpen 𝒮 h,
      ∃ u : x.1.asHomogeneousIdeal.toIdeal.primeCompl, (u : S) • w = 0) :
    ∃ c : ℕ, h ^ c • w = 0 := by
  have hw0 : w ∈ shiftedGrading 𝒨 p (0 • (d : ℤ)) := by
    simpa only [shiftedGrading, zero_smul, zero_add] using hw
  have hsec : degreeZeroToSection 𝒮 (shiftedGrading 𝒨 p) h
      (degreeZeroFraction 𝒮 (shiftedGrading 𝒨 p) hh 0 w hw0) = 0 := by
    refine Subtype.ext (funext fun x => ?_)
    obtain ⟨u, hu⟩ := hvanish x
    rw [degreeZeroToSection_fraction]
    exact mk_eq_zero_of_smul_eq_zero u _ hu
  have hzero : degreeZeroFraction 𝒮 (shiftedGrading 𝒨 p) hh 0 w hw0 = 0 :=
    degreeZeroToSection_injective 𝒮 (shiftedGrading 𝒨 p) hh hd
      (hsec.trans (map_zero _).symm)
  exact (Stacks.SheafOfModules.eq_zero_iff_exists_pow_smul_eq_zero 𝒮 (shiftedGrading 𝒨 p)
    _ 0 w rfl).mp hzero

/-- **On the standard open of a degree-one element `h`, a global section of `M(n)~` is the
fraction `v / h ^ l` of a homogeneous `v` of degree `l + n`.** -/
theorem exists_fraction_of_shiftedSectionsComponent {h : S} (hh : h ∈ 𝒮 1) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    ∃ (l : ℕ) (v : M), v ∈ 𝒨 ((l : ℤ) + n) ∧
      ∀ x : ProjectiveSpectrum.basicOpen 𝒮 h,
        ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1
            ⟨x.1, trivial⟩ =
          LocalizedModule.mk v
            ⟨h ^ l, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 l⟩ := by
  let ι : ProjectiveSpectrum.basicOpen 𝒮 h ⟶ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) :=
    homOfLE le_top
  obtain ⟨z, hz⟩ := degreeZeroToSection_surjective 𝒮 (shiftedGrading 𝒨 n) hh Nat.one_pos
    ((associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)).val.map ι.op s)
  obtain ⟨l, v, hv, hfrac⟩ := degreeZeroFraction_surjective 𝒮 (shiftedGrading 𝒨 n) hh z
  refine ⟨l, v, by simpa using hv, fun x => ?_⟩
  have h1 := associatedModuleSheaf_restrict_apply (𝒜 := 𝒮) (𝒨 := shiftedGrading 𝒨 n) ι s x
  refine h1.symm.trans ?_
  rw [← hz, ← hfrac]
  exact degreeZeroToSection_fraction 𝒮 (shiftedGrading 𝒨 n) hh l v hv x

/-- Two sections of `M(i + n)~` agree once the scalar multiple `a • s` has the fraction `m / 1`
as its value in every module fiber. -/
private theorem homogeneousScalarGlobalSections_eq_of_forall {M' τ' : Type*} [AddCommGroup M']
    [Module S M'] [SetLike τ' M'] [AddSubgroupClass τ' M'] (ℬ : ℤ → τ') [Decomposition ℬ]
    [SetLike.GradedSMul 𝒮 ℬ] (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : shiftedSectionsComponent 𝒮 ℬ n)
    (m : ℬ ((i : ℤ) + n))
    (hval : ∀ x : ProjectiveSpectrum.top 𝒮,
      (a : S) • (((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading ℬ n) ⊤).toFun s).1
          ⟨x, trivial⟩) =
        LocalizedModule.mk (m : M') (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) :
    homogeneousScalarGlobalSections 𝒮 ℬ i n a s =
      degreeNToGlobalSections 𝒮 ℬ ((i : ℤ) + n) m := by
  apply (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading ℬ ((i : ℤ) + n)) ⊤).injective
  apply Subtype.ext
  funext x
  change ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading ℬ ((i : ℤ) + n)) ⊤).toFun
      (homogeneousScalarGlobalSections 𝒮 ℬ i n a s)).1 x =
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading ℬ ((i : ℤ) + n)) ⊤).toFun
      (degreeNToGlobalSections 𝒮 ℬ ((i : ℤ) + n) m)).1 x
  rw [homogeneousScalarGlobalSections_apply, degreeNToGlobalSections_apply]
  exact hval x.1

/-- **The cokernel of the comparison is killed by powers of the degree-one elements.** Let `S` be
generated over `𝒮 0` by finitely many degree-one elements `g i`, and let `f` be any degree-one
element. Then for every global section `s` of `M(n)~` some power `f ^ k` carries `s` into the
image of `𝒨 (k + n) ⟶ Γ(Proj 𝒮, M(k + n)~)`. -/
theorem exists_pow_smul_mem_range_degreeNToGlobalSections
    {r : ℕ} (g : Fin r → S) (hg : ∀ i, g i ∈ 𝒮 1)
    (hcover : Algebra.adjoin (𝒮 0) (Set.range g) = ⊤)
    {f : S} (hf : f ∈ 𝒮 1) (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    ∃ (k : ℕ) (m : 𝒨 ((k : ℤ) + n)),
      homogeneousScalarGlobalSections 𝒮 𝒨 k n ⟨f ^ k, pow_mem_graded_of_mem_one 𝒮 hf k⟩ s
        = degreeNToGlobalSections 𝒮 𝒨 ((k : ℤ) + n) m := by
  classical
  have hcov : ⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' 𝒮 g (fun i => ⟨1, hg i⟩) hcover
  obtain ⟨j, m₀, hm₀, hm₀val⟩ := exists_fraction_of_shiftedSectionsComponent 𝒮 𝒨 hf n s
  choose l v hv hvval using fun i : Fin r =>
    exists_fraction_of_shiftedSectionsComponent 𝒮 𝒨 (hg i) n s
  have hwdeg : ∀ i : Fin r,
      f ^ j • v i - g i ^ l i • m₀ ∈ 𝒨 ((j : ℤ) + ((l i : ℤ) + n)) := by
    intro i
    refine sub_mem ?_ ?_
    · exact graded_smul_mem_of_eq 𝒮 𝒨 (pow_mem_graded_of_mem_one 𝒮 hf j) (hv i) rfl
    · exact graded_smul_mem_of_eq 𝒮 𝒨 (pow_mem_graded_of_mem_one 𝒮 (hg i) (l i)) hm₀ (by ring)
  have hkill : ∀ i : Fin r, ∃ t : ℕ,
      (f * g i) ^ t • (f ^ j • v i - g i ^ l i • m₀) = 0 := by
    intro i
    refine exists_pow_smul_eq_zero_of_forall_fiber_eq_zero 𝒮 𝒨 (d := 1 + 1) (by norm_num)
      (SetLike.mul_mem_graded hf (hg i)) (hwdeg i) (fun x => ?_)
    have hx : x.1 ∈ ProjectiveSpectrum.basicOpen 𝒮 f ⊓
        ProjectiveSpectrum.basicOpen 𝒮 (g i) := by
      rw [← ProjectiveSpectrum.basicOpen_mul]
      exact x.2
    obtain ⟨u, hu⟩ :=
      LocalizedModule.mk_eq.mp ((hm₀val ⟨x.1, hx.1⟩).symm.trans (hvval i ⟨x.1, hx.2⟩))
    have hu' : (u : S) • (g i ^ l i • m₀) = (u : S) • (f ^ j • v i) := by
      simpa only [Submonoid.smul_def] using hu
    exact ⟨u, by rw [smul_sub, hu', sub_self]⟩
  choose t ht using hkill
  set B := Finset.univ.sup t
  have hkey : ∀ i : Fin r,
      g i ^ t i • (f ^ B • (f ^ j • v i - g i ^ l i • m₀)) = 0 := by
    intro i
    have htB : t i ≤ B := Finset.le_sup (f := t) (Finset.mem_univ i)
    have hcoef : g i ^ t i * f ^ B = f ^ (B - t i) * (f ^ t i * g i ^ t i) := by
      rw [show f ^ B = f ^ (B - t i) * f ^ t i by rw [← pow_add, Nat.sub_add_cancel htB]]
      ring
    rw [smul_smul, hcoef, ← smul_smul, ← mul_pow, ht i, smul_zero]
  have hmmem : f ^ B • m₀ ∈ 𝒨 (((B + j : ℕ) : ℤ) + n) :=
    graded_smul_mem_of_eq 𝒮 𝒨 (pow_mem_graded_of_mem_one 𝒮 hf B) hm₀ (by push_cast; ring)
  refine ⟨B + j, ⟨f ^ B • m₀, hmmem⟩, ?_⟩
  refine homogeneousScalarGlobalSections_eq_of_forall 𝒮 𝒨 (B + j) n _ s _ fun x => ?_
  have hxcover : x ∈ ⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i) := by
    rw [hcov]; exact Set.mem_univ _
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  change f ^ (B + j) •
      (((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1 ⟨x, trivial⟩) =
      LocalizedModule.mk (f ^ B • m₀) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [show (((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1
      ⟨x, trivial⟩) = LocalizedModule.mk (v i)
        ⟨g i ^ l i, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hxi (l i)⟩ from
      hvval i ⟨x, hxi⟩, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨⟨g i ^ t i, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hxi (t i)⟩, ?_⟩
  have h := hkey i
  rw [show f ^ B • (f ^ j • v i - g i ^ l i • m₀) =
      f ^ (B + j) • v i - g i ^ l i • (f ^ B • m₀) from by
    rw [smul_sub, smul_smul, ← pow_add, smul_comm (f ^ B) (g i ^ l i) m₀],
    smul_sub, sub_eq_zero] at h
  simpa only [Submonoid.smul_def, Submonoid.coe_one, one_smul] using h

/-- **The image of the comparison, read pointwise.** A homogeneous scalar multiple of a global
section of `M(n)~` is the section attached to a homogeneous element `m` of `M` exactly when its
value in every module fiber is the fraction `m / 1`. -/
theorem homogeneousScalarGlobalSections_eq_degreeNToGlobalSections_iff (i : ℕ) (n : ℤ)
    (a : 𝒮 i) (s : shiftedSectionsComponent 𝒮 𝒨 n) (m : 𝒨 ((i : ℤ) + n)) :
    homogeneousScalarGlobalSections 𝒮 𝒨 i n a s =
        degreeNToGlobalSections 𝒮 𝒨 ((i : ℤ) + n) m ↔
      ∀ x : ProjectiveSpectrum.top 𝒮,
        (a : S) • (((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1
            ⟨x, trivial⟩) =
          LocalizedModule.mk (m : M) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
  refine ⟨fun heq x => ?_, fun hval => ?_⟩
  · rw [← homogeneousScalarGlobalSections_apply 𝒮 𝒨 i n a s ⟨x, trivial⟩,
      ← degreeNToGlobalSections_apply 𝒮 𝒨 ((i : ℤ) + n) m x, heq]
  · exact homogeneousScalarGlobalSections_eq_of_forall 𝒮 𝒨 i n a s m hval

/-- **The cokernel of the comparison is `𝒮₊`-power torsion.** Over a Noetherian graded ring
generated in degree one over `𝒮 0` by finitely many elements `g i`, for every global section `s`
of `M(n)~` some power of the irrelevant ideal carries `s` into the image of the comparison: every
homogeneous `a` lying in that power has `a • s` of the form `degreeNToGlobalSections ... m`. -/
theorem exists_irrelevant_pow_smul_mem_range_degreeNToGlobalSections [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {r : ℕ} (g : Fin r → S) (hg : ∀ i, g i ∈ 𝒮 1)
    (hcover : Algebra.adjoin (𝒮 0) (Set.range g) = ⊤)
    (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    ∃ N : ℕ, ∀ (i : ℕ) (a : 𝒮 i),
      (a : S) ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N →
        ∃ m : 𝒨 ((i : ℤ) + n),
          homogeneousScalarGlobalSections 𝒮 𝒨 i n a s
            = degreeNToGlobalSections 𝒮 𝒨 ((i : ℤ) + n) m := by
  classical
  set σs : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)), ModuleFiber (M := M) 𝒮 x.1 :=
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1
  set W : Set S := {b : S | ∃ (p : ℕ) (hb : b ∈ 𝒮 p) (m : 𝒨 ((p : ℤ) + n)),
    ∀ x : ProjectiveSpectrum.top 𝒮,
      b • σs ⟨x, trivial⟩ =
        LocalizedModule.mk (m : M) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)}
  have hspan : ∀ (i : ℕ) (a : S), a ∈ 𝒮 i → a ∈ Ideal.span W →
      ∃ m : 𝒨 ((i : ℤ) + n), ∀ x : ProjectiveSpectrum.top 𝒮,
        a • σs ⟨x, trivial⟩ =
          LocalizedModule.mk (m : M) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
    intro i a ha hmem
    obtain ⟨κ, c, w, hsum⟩ := Submodule.mem_span_set'.mp hmem
    have hterm : ∀ t : Fin κ, ∃ y : 𝒨 ((i : ℤ) + n), ∀ x : ProjectiveSpectrum.top 𝒮,
        GradedRing.proj 𝒮 i (c t * (w t : S)) • σs ⟨x, trivial⟩ =
          LocalizedModule.mk (y : M) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
      intro t
      obtain ⟨p, hb, m', hm'⟩ := (w t).2
      by_cases hle : p ≤ i
      · have hγ : GradedRing.proj 𝒮 (i - p) (c t) ∈ 𝒮 (i - p) := proj_mem 𝒮 (c t) (i - p)
        have hdeg : (((i - p : ℕ) : ℤ) + ((p : ℤ) + n)) = ((i : ℤ) + n) := by omega
        refine ⟨⟨GradedRing.proj 𝒮 (i - p) (c t) • (m' : M), ?_⟩, fun x => ?_⟩
        · exact graded_smul_mem_of_eq 𝒮 𝒨 hγ m'.2 hdeg
        · rw [proj_mul_eq 𝒮 (c t) ((w t : S)) p i hb hle, mul_smul, hm' x,
            LocalizedModule.smul'_mk]
      · exact ⟨0, fun x => by
          rw [proj_mul_eq_zero_of_lt 𝒮 (c t) ((w t : S)) p i hb (by omega), zero_smul,
            ZeroMemClass.coe_zero, LocalizedModule.zero_mk]⟩
    choose y hy using hterm
    refine ⟨∑ t, y t, fun x => ?_⟩
    have hproj : a = ∑ t, GradedRing.proj 𝒮 i (c t * (w t : S)) := by
      rw [← proj_eq_self_of_mem 𝒮 ha, ← hsum, map_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [smul_eq_mul]
    rw [hproj, Finset.sum_smul, Finset.sum_congr rfl fun t _ => hy t x,
      AddSubmonoidClass.coe_finsetSum]
    exact (map_sum (LocalizedModule.mkLinearMap
      x.asHomogeneousIdeal.toIdeal.primeCompl M) (fun t => ((y t : M))) Finset.univ).symm
  have hrad : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ (Ideal.span W).radical := by
    rw [← span_degreeOne_eq_irrelevant 𝒮 hgen, Ideal.span_le]
    intro h hh
    obtain ⟨k, m, hkm⟩ := exists_pow_smul_mem_range_degreeNToGlobalSections 𝒮 𝒨 g hg hcover
      (SetLike.mem_coe.mp hh) n s
    refine ⟨k, Ideal.subset_span ⟨k, pow_mem_graded_of_mem_one 𝒮 (SetLike.mem_coe.mp hh) k,
      m, ?_⟩⟩
    exact (homogeneousScalarGlobalSections_eq_degreeNToGlobalSections_iff 𝒮 𝒨 k n _ s m).mp hkm
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (Ideal.fg_of_isNoetherianRing _)
  refine ⟨N, fun i a ha => ?_⟩
  obtain ⟨m, hm⟩ := hspan i (a : S) a.2 (hN ha)
  exact ⟨m, (homogeneousScalarGlobalSections_eq_degreeNToGlobalSections_iff 𝒮 𝒨 i n a s m).mpr hm⟩

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
