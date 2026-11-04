module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenScalars

/-!
# Shifted global sections on `Proj` read as fractions on the degree-one charts

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded
`S`-module and `X = Proj 𝒮`. For `f ∈ 𝒮 1` the standard open `D₊(f)` is affine and
`Γ(D₊(f), M(n)~) = M(n)₍f₎`, so a global section `s` of `M(n)~` has, on each such chart, a single
fraction `m / f ^ a` with `m` homogeneous of degree `a + n`. This file sets up that calculus:
the chart fraction of a section, its behaviour under the canonical map from the homogeneous
elements and under the homogeneous scalar action, and the two statements that the charts give —
a section is determined by its chart fractions, and the chart fraction on `D₊(f g)` is computed
from the one on `D₊(f)`, or on `D₊(g)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.frac`: the fraction in `M(n)₍f₎`
  representing the restriction of a shifted global section to `D₊(f)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.moduleToFiber_coe_fracDeg`: the chart
  fraction evaluates in every fiber over `D₊(f)` to the value of the section.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.coe_eq_of_forall_moduleToFiber_eq`: two
  degree-zero fractions with the same values in all fibers over `D₊(f)` are equal.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.eq_zero_of_forall_coe_frac_eq_zero`: a
  section whose chart fractions all vanish is zero, for a family of degree-one elements spanning
  the irrelevant ideal.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_mk_coe_frac`: the chart fraction is a
  single fraction `m / f ^ a` with `m` homogeneous of degree `a + n`.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.coe_frac_degreeNToGlobalSections`: the chart
  fraction of the canonical section of a homogeneous element is that element over `1`.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.coe_frac_homogeneousScalarGlobalSections`: a
  homogeneous scalar multiplies the numerator of the chart fraction.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.coe_fracDeg_mul_left` and
  `coe_fracDeg_mul_right`: the chart fraction on `D₊(f g)` obtained from the one on `D₊(f)`,
  respectively on `D₊(g)`.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections_basicOpen)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegreeSections

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- The restriction of a shifted global section of `M(n)~` to the standard open `D₊(f)`. -/
def restrictBasicOpen (f : S) (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)).val.map (homOfLE le_top).op s

/-- The fraction in `M(n)₍f₎` representing the restriction of a shifted global section to the
standard open of a homogeneous element `f` of positive degree `d`. -/
def fracDeg {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    GradedModuleDegreeZeroLocalization 𝒮 (shiftedGrading 𝒨 n) f :=
  associatedModuleSheafStandardOpenEquiv 𝒮 (shiftedGrading 𝒨 n) hf hd
    (restrictBasicOpen 𝒮 𝒨 f n s)

/-- The fraction in `M(n)₍f₎` representing the restriction of a shifted global section to the
standard open of a degree-one element. -/
abbrev frac {f : S} (hf : f ∈ 𝒮 1) (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    GradedModuleDegreeZeroLocalization 𝒮 (shiftedGrading 𝒨 n) f :=
  fracDeg 𝒮 𝒨 hf Nat.one_pos n s

/-- **The chart fraction evaluates, in every fiber over `D₊(f)`, to the value of the section.** -/
theorem moduleToFiber_coe_fracDeg {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) (x : ProjectiveSpectrum.basicOpen 𝒮 f) :
    moduleToFiber (M := M) 𝒮 f x (fracDeg 𝒮 𝒨 hf hd n s : LocalizedModule.Away f M) =
      s.1 ⟨x.1, trivial⟩ :=
  congrFun (congrArg Subtype.val
    (degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒮 (shiftedGrading 𝒨 n) hf hd _)) x

/-- **Two degree-zero fractions with the same value in every fiber over `D₊(f)` are equal.** -/
theorem coe_eq_of_forall_moduleToFiber_eq {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (n : ℤ)
    (u v : GradedModuleDegreeZeroLocalization 𝒮 (shiftedGrading 𝒨 n) f)
    (h : ∀ x : ProjectiveSpectrum.basicOpen 𝒮 f,
      moduleToFiber (M := M) 𝒮 f x (u : LocalizedModule.Away f M) =
        moduleToFiber (M := M) 𝒮 f x (v : LocalizedModule.Away f M)) :
    (u : LocalizedModule.Away f M) = (v : LocalizedModule.Away f M) :=
  congrArg Subtype.val (degreeZeroToSection_injective 𝒮 (shiftedGrading 𝒨 n) hf hd
    (Subtype.ext (funext h)))

/-- A family of elements spanning the irrelevant ideal has standard opens covering `Proj 𝒮`. -/
theorem exists_mem_basicOpen {ι : Type*} (fam : ι → S)
    (hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal)
    (x : ProjectiveSpectrum.top 𝒮) : ∃ i, x ∈ ProjectiveSpectrum.basicOpen 𝒮 (fam i) := by
  by_contra! hc
  refine x.not_irrelevant_le (?_ : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ _)
  rw [← hspan, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact not_not.mp (hc i)

/-- **A shifted global section whose chart fraction vanishes on every chart is zero.** -/
theorem eq_zero_of_forall_coe_frac_eq_zero {ι : Type*} (fam : ι → S) (hfam : ∀ i, fam i ∈ 𝒮 1)
    (hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n)
    (h : ∀ i, (frac 𝒮 𝒨 (hfam i) n s : LocalizedModule.Away (fam i) M) = 0) : s = 0 := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨i, hi⟩ := exists_mem_basicOpen 𝒮 fam hspan x.1
  have hval := moduleToFiber_coe_fracDeg 𝒮 𝒨 (hfam i) Nat.one_pos n s ⟨x.1, hi⟩
  rw [h i, map_zero] at hval
  exact hval.symm

/-- **The chart fraction of a shifted global section is a single fraction `m / f ^ a`** with `m`
homogeneous of degree `a + n`. -/
theorem exists_mk_coe_frac {f : S} (hf : f ∈ 𝒮 1) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    ∃ (a : ℕ) (m : M), m ∈ 𝒨 ((a : ℤ) + n) ∧
      (frac 𝒮 𝒨 hf n s : LocalizedModule.Away f M) =
        LocalizedModule.mk m ⟨f ^ a, by exact ⟨a, rfl⟩⟩ :=
  Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction 𝒮 (shiftedGrading 𝒨 n) hf
    (frac 𝒮 𝒨 hf n s)

/-- **A fraction `m / f ^ a` with `m` homogeneous of degree `a + n` lies in `M(n)₍f₎`.** -/
theorem mk_mem_degreeZeroLocalization_shifted {f : S} (hf : f ∈ 𝒮 1) (n : ℤ) (a : ℕ) {m : M}
    (hm : m ∈ 𝒨 ((a : ℤ) + n)) :
    LocalizedModule.mk (S := Submonoid.powers f) m ⟨f ^ a, by exact ⟨a, rfl⟩⟩ ∈
      GradedModuleDegreeZeroLocalization 𝒮 (shiftedGrading 𝒨 n) f :=
  Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree 𝒮
    (shiftedGrading 𝒨 n) hf a m (by simpa only [Nat.mul_one] using hm)

/-- **The chart fraction of the canonical section of a homogeneous element** is that element over
`f ^ 0`. -/
theorem coe_frac_degreeNToGlobalSections {f : S} (hf : f ∈ 𝒮 1) (n : ℤ) (m : 𝒨 n) :
    (frac 𝒮 𝒨 hf n (degreeNToGlobalSections 𝒮 𝒨 n m) : LocalizedModule.Away f M) =
      LocalizedModule.mk (m : M) ⟨f ^ 0, by exact ⟨0, rfl⟩⟩ :=
  congrArg Subtype.val (degreeZeroToGlobalSections_basicOpen 𝒮 (shiftedGrading 𝒨 n) hf
    Nat.one_pos ⟨(m : M), by simpa only [shiftedGrading, zero_add] using m.2⟩)

/-- A homogeneous scalar of degree `e` maps degree `i` into any degree equal to `e + i`. -/
private theorem smul_mem_of_add_eq {R N A B : Type*} [SMul R N] [SetLike A R] [SetLike B N]
    (𝒜 : ℕ → A) (ℬ : ℤ → B) [SetLike.GradedSMul 𝒜 ℬ] {e : ℕ} {b : R} (hb : b ∈ 𝒜 e) {m : N}
    {i j : ℤ} (hm : m ∈ ℬ i) (h : (e : ℤ) + i = j) : b • m ∈ ℬ j :=
  h ▸ SetLike.GradedSMul.smul_mem hb hm

/-- **A homogeneous scalar multiplies the numerator of the chart fraction.** -/
theorem coe_frac_homogeneousScalarGlobalSections {f : S} (hf : f ∈ 𝒮 1) (n : ℤ) (e : ℕ)
    (b : 𝒮 e) (s : shiftedSectionsComponent 𝒮 𝒨 n) {a : ℕ} {m : M}
    (hm : m ∈ 𝒨 ((a : ℤ) + n))
    (hfrac : (frac 𝒮 𝒨 hf n s : LocalizedModule.Away f M) =
      LocalizedModule.mk m ⟨f ^ a, by exact ⟨a, rfl⟩⟩) :
    (frac 𝒮 𝒨 hf ((e : ℤ) + n) (homogeneousScalarGlobalSections 𝒮 𝒨 e n b s) :
        LocalizedModule.Away f M) =
      LocalizedModule.mk ((b : S) • m) ⟨f ^ a, by exact ⟨a, rfl⟩⟩ := by
  refine coe_eq_of_forall_moduleToFiber_eq 𝒮 𝒨 hf Nat.one_pos ((e : ℤ) + n) _
    ⟨_, mk_mem_degreeZeroLocalization_shifted 𝒮 𝒨 hf ((e : ℤ) + n) a
      (smul_mem_of_add_eq 𝒮 𝒨 b.2 hm (by ring))⟩ fun x => ?_
  rw [moduleToFiber_coe_fracDeg, show ((homogeneousScalarGlobalSections 𝒮 𝒨 e n b s) : _).1
    ⟨x.1, trivial⟩ = (b : S) • (s : _).1 ⟨x.1, trivial⟩ from
      homogeneousScalarGlobalSections_apply 𝒮 𝒨 e n b s ⟨x.1, trivial⟩,
    ← moduleToFiber_coe_fracDeg 𝒮 𝒨 hf Nat.one_pos n s x, hfrac]
  simp only [moduleToFiber_mk]
  rw [LocalizedModule.smul'_mk]

/-- A fraction over the powers of `f` vanishes exactly when a power of `f` kills its
numerator. -/
theorem mk_eq_zero_iff_exists_pow_smul {f : S} (m : M) (s : Submonoid.powers f) :
    LocalizedModule.mk (S := Submonoid.powers f) m s = 0 ↔ ∃ k : ℕ, f ^ k • m = 0 := by
  rw [show (0 : LocalizedModule.Away f M) = LocalizedModule.mk 0 1 from
    (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq]
  simp [Submonoid.smul_def, Submonoid.mem_powers_iff]

/-- **Two shifted global sections with the same chart fractions are equal.** -/
theorem eq_of_forall_coe_frac_eq {ι : Type*} (fam : ι → S) (hfam : ∀ i, fam i ∈ 𝒮 1)
    (hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal) (n : ℤ)
    (s t : shiftedSectionsComponent 𝒮 𝒨 n)
    (h : ∀ i, (frac 𝒮 𝒨 (hfam i) n s : LocalizedModule.Away (fam i) M) =
      (frac 𝒮 𝒨 (hfam i) n t : LocalizedModule.Away (fam i) M)) : s = t := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨i, hi⟩ := exists_mem_basicOpen 𝒮 fam hspan x.1
  have hs := moduleToFiber_coe_fracDeg 𝒮 𝒨 (hfam i) Nat.one_pos n s ⟨x.1, hi⟩
  have ht := moduleToFiber_coe_fracDeg 𝒮 𝒨 (hfam i) Nat.one_pos n t ⟨x.1, hi⟩
  rw [h i] at hs
  exact hs.symm.trans ht

/-- The chart fraction of the zero section is zero. -/
theorem coe_fracDeg_zero {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (n : ℤ) :
    (fracDeg 𝒮 𝒨 hf hd n 0 : LocalizedModule.Away f M) = 0 := by
  refine coe_eq_of_forall_moduleToFiber_eq 𝒮 𝒨 hf hd n _ 0 fun x => ?_
  rw [moduleToFiber_coe_fracDeg, ZeroMemClass.coe_zero, map_zero]
  rfl

/-- If a degree-one scalar `b` kills a section, then a power of `f` kills `b • m`, for `m` the
numerator of the chart fraction. -/
private theorem exists_pow_smul_smul_eq_zero {f b : S} (hf : f ∈ 𝒮 1) (hb : b ∈ 𝒮 1) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n)
    (hbs : homogeneousScalarGlobalSections 𝒮 𝒨 1 n ⟨b, hb⟩ s = 0)
    {a : ℕ} {m : M} (hm : m ∈ 𝒨 ((a : ℤ) + n))
    (hfrac : (frac 𝒮 𝒨 hf n s : LocalizedModule.Away f M) =
      LocalizedModule.mk m ⟨f ^ a, by exact ⟨a, rfl⟩⟩) :
    ∃ k : ℕ, f ^ k • (b • m) = 0 := by
  have h := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 hf n 1 ⟨b, hb⟩ s hm hfrac
  rw [hbs, coe_fracDeg_zero] at h
  exact (mk_eq_zero_iff_exists_pow_smul (f := f) (b • m) _).mp h.symm

/-- **A section killed by the very element defining a chart has vanishing fraction on that
chart.** -/
theorem coe_frac_eq_zero_of_smul_self_eq_zero {f : S} (hf : f ∈ 𝒮 1) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n)
    (hs : homogeneousScalarGlobalSections 𝒮 𝒨 1 n ⟨f, hf⟩ s = 0) :
    (frac 𝒮 𝒨 hf n s : LocalizedModule.Away f M) = 0 := by
  obtain ⟨a, m, hm, hfrac⟩ := exists_mk_coe_frac 𝒮 𝒨 hf n s
  obtain ⟨k, hk⟩ := exists_pow_smul_smul_eq_zero 𝒮 𝒨 hf hf n s hs hm hfrac
  rw [hfrac, mk_eq_zero_iff_exists_pow_smul]
  exact ⟨k + 1, by rwa [pow_succ, mul_smul]⟩

/-- The chart fraction on `D₊(p)`, for `p = h * c` of degree two, computed from the one on
`D₊(h)`. -/
private theorem coe_fracDeg_eq_of_eq_mul {p h c : S} (hh : h ∈ 𝒮 1) (hc : c ∈ 𝒮 1)
    (hp : p ∈ 𝒮 2) (hpc : p = h * c) (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) {a : ℕ}
    {m : M} (hm : m ∈ 𝒨 ((a : ℤ) + n))
    (hfrac : (frac 𝒮 𝒨 hh n s : LocalizedModule.Away h M) =
      LocalizedModule.mk m ⟨h ^ a, by exact ⟨a, rfl⟩⟩) :
    (fracDeg 𝒮 𝒨 hp two_pos n s : LocalizedModule.Away p M) =
      LocalizedModule.mk (c ^ a • m) ⟨p ^ a, by exact ⟨a, rfl⟩⟩ := by
  subst hpc
  have hcm : c ^ a • m ∈ shiftedGrading 𝒨 n ((a * 2 : ℕ) : ℤ) :=
    smul_mem_of_add_eq 𝒮 𝒨 (SetLike.pow_mem_graded a hc) hm (by simp; ring)
  refine coe_eq_of_forall_moduleToFiber_eq 𝒮 𝒨 hp two_pos n _
    ⟨_, Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree 𝒮
      (shiftedGrading 𝒨 n) hp a _ hcm⟩ fun x => ?_
  have hx : x.1 ∈ ProjectiveSpectrum.basicOpen 𝒮 h :=
    ProjectiveSpectrum.basicOpen_mul_le_left 𝒮 h c x.2
  rw [moduleToFiber_coe_fracDeg, ← moduleToFiber_coe_fracDeg 𝒮 𝒨 hh Nat.one_pos n s ⟨x.1, hx⟩,
    hfrac, moduleToFiber_mk, moduleToFiber_mk]
  refine (LocalizedModule.mk_eq).mpr ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul]
  rw [mul_pow, mul_smul]

/-- **The chart fraction on `D₊(f g)` computed from the one on `D₊(f)`.** -/
theorem coe_fracDeg_mul_left {f g : S} (hf : f ∈ 𝒮 1) (hg : g ∈ 𝒮 1) (hfg : f * g ∈ 𝒮 2)
    (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) {a : ℕ} {m : M} (hm : m ∈ 𝒨 ((a : ℤ) + n))
    (hfrac : (frac 𝒮 𝒨 hf n s : LocalizedModule.Away f M) =
      LocalizedModule.mk m ⟨f ^ a, by exact ⟨a, rfl⟩⟩) :
    (fracDeg 𝒮 𝒨 hfg two_pos n s : LocalizedModule.Away (f * g) M) =
      LocalizedModule.mk (g ^ a • m) ⟨(f * g) ^ a, by exact ⟨a, rfl⟩⟩ :=
  coe_fracDeg_eq_of_eq_mul 𝒮 𝒨 hf hg hfg rfl n s hm hfrac

/-- **The chart fraction on `D₊(f g)` computed from the one on `D₊(g)`.** -/
theorem coe_fracDeg_mul_right {f g : S} (hf : f ∈ 𝒮 1) (hg : g ∈ 𝒮 1) (hfg : f * g ∈ 𝒮 2)
    (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) {a : ℕ} {m : M} (hm : m ∈ 𝒨 ((a : ℤ) + n))
    (hfrac : (frac 𝒮 𝒨 hg n s : LocalizedModule.Away g M) =
      LocalizedModule.mk m ⟨g ^ a, by exact ⟨a, rfl⟩⟩) :
    (fracDeg 𝒮 𝒨 hfg two_pos n s : LocalizedModule.Away (f * g) M) =
      LocalizedModule.mk (f ^ a • m) ⟨(f * g) ^ a, by exact ⟨a, rfl⟩⟩ :=
  coe_fracDeg_eq_of_eq_mul 𝒮 𝒨 hg hf hfg (mul_comm f g) n s hm hfrac

/-- A power of a degree-one element, as a homogeneous element of the corresponding degree. -/
def powDegOne {g : S} (hg : g ∈ 𝒮 1) (l : ℕ) : 𝒮 l :=
  ⟨g ^ l, by simpa using SetLike.pow_mem_graded l hg⟩

/-- **The numerator of a chart fraction can be chosen killed by every homogeneous scalar that
kills the section**, for a finite family of degree-one scalars. -/
theorem exists_mk_coe_frac_smul_eq_zero {f : S} (hf : f ∈ 𝒮 1) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n)
    {ι : Type*} [Finite ι] (b : ι → S) (hb : ∀ j, b j ∈ 𝒮 1)
    (hbs : ∀ j, homogeneousScalarGlobalSections 𝒮 𝒨 1 n ⟨b j, hb j⟩ s = 0) :
    ∃ (a : ℕ) (m : M), m ∈ 𝒨 ((a : ℤ) + n) ∧ (∀ j, b j • m = 0) ∧
      (frac 𝒮 𝒨 hf n s : LocalizedModule.Away f M) =
        LocalizedModule.mk m ⟨f ^ a, by exact ⟨a, rfl⟩⟩ := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨a, m, hm, hfrac⟩ := exists_mk_coe_frac 𝒮 𝒨 hf n s
  have hex : ∀ j, ∃ c : ℕ, f ^ c • (b j • m) = 0 := by
    intro j
    exact exists_pow_smul_smul_eq_zero 𝒮 𝒨 hf (hb j) n s (hbs j) hm hfrac
  choose c hc using hex
  refine ⟨a + Finset.univ.sup c, f ^ Finset.univ.sup c • m, ?_, ?_, ?_⟩
  · exact smul_mem_of_add_eq 𝒮 𝒨 (SetLike.pow_mem_graded _ hf) hm (by simp; ring)
  · intro j
    rw [← Nat.sub_add_cancel (Finset.le_sup (f := c) (Finset.mem_univ j)), pow_add, mul_smul,
      smul_comm (b j), smul_comm (b j) (f ^ c j), hc j, smul_zero]
  · rw [hfrac]
    refine (LocalizedModule.mk_eq).mpr ⟨1, ?_⟩
    simp only [Submonoid.smul_def, one_smul]
    rw [← mul_smul, pow_add]

/-- **A section whose fraction vanishes on the chart of a degree-one element `g` is killed by a
power of `g`**, given a finite family of degree-one elements spanning the irrelevant ideal. -/
theorem exists_pow_smul_eq_zero_of_coe_frac_eq_zero {ι : Type*} [Finite ι] (fam : ι → S)
    (hfam : ∀ i, fam i ∈ 𝒮 1)
    (hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal)
    {g : S} (hg : g ∈ 𝒮 1) (n : ℤ) (t : shiftedSectionsComponent 𝒮 𝒨 n)
    (ht : (frac 𝒮 𝒨 hg n t : LocalizedModule.Away g M) = 0) :
    ∃ l : ℕ, homogeneousScalarGlobalSections 𝒮 𝒨 l n (powDegOne 𝒮 hg l) t = 0 := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ i : ι, ∃ p : ℕ × ℕ, ∀ l : ℕ, p.1 + p.2 ≤ l →
      (frac 𝒮 𝒨 (hfam i) ((l : ℤ) + n)
        (homogeneousScalarGlobalSections 𝒮 𝒨 l n (powDegOne 𝒮 hg l) t) :
          LocalizedModule.Away (fam i) M) = 0 := by
    intro i
    obtain ⟨a, w, hw, hfr⟩ := exists_mk_coe_frac 𝒮 𝒨 (hfam i) n t
    have hfg : fam i * g ∈ 𝒮 2 := SetLike.mul_mem_graded (hfam i) hg
    have h1 := coe_fracDeg_mul_left 𝒮 𝒨 (hfam i) hg hfg n t hw hfr
    have h2 := coe_fracDeg_mul_right 𝒮 𝒨 (hfam i) hg hfg n t
      (m := (0 : M)) (a := 0) (by simp)
      (by rw [ht]; exact (LocalizedModule.zero_mk _).symm)
    rw [h1] at h2
    have h3 : LocalizedModule.mk (S := Submonoid.powers (fam i * g)) (g ^ a • w)
        ⟨(fam i * g) ^ a, by exact ⟨a, rfl⟩⟩ = 0 := by
      rw [h2]
      simp
    obtain ⟨N, hN⟩ := (mk_eq_zero_iff_exists_pow_smul (f := fam i * g) (g ^ a • w) _).mp h3
    refine ⟨(N, a), fun l hl => ?_⟩
    have hfrl := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n l
      (powDegOne 𝒮 hg l) t hw hfr
    rw [hfrl, mk_eq_zero_iff_exists_pow_smul]
    refine ⟨N, ?_⟩
    show fam i ^ N • (g ^ l • w) = 0
    rw [show l = l - (N + a) + N + a by omega, pow_add, pow_add, mul_smul, mul_smul,
      smul_comm (fam i ^ N), ← mul_smul (fam i ^ N), ← mul_pow, hN, smul_zero]
  choose p hp using key
  refine ⟨Finset.univ.sup fun i => (p i).1 + (p i).2, ?_⟩
  refine eq_zero_of_forall_coe_frac_eq_zero 𝒮 𝒨 fam hfam hspan _ _ fun i => ?_
  exact hp i _ (Finset.le_sup (f := fun i => (p i).1 + (p i).2) (Finset.mem_univ i))

omit [Decomposition 𝒨] in
/-- The homogeneous scalar action is subtractive in the section. -/
theorem homogeneousScalarGlobalSections_sub (e : ℕ) (n : ℤ) (a : 𝒮 e)
    (s t : shiftedSectionsComponent 𝒮 𝒨 n) :
    homogeneousScalarGlobalSections 𝒮 𝒨 e n a (s - t) =
      homogeneousScalarGlobalSections 𝒮 𝒨 e n a s -
        homogeneousScalarGlobalSections 𝒮 𝒨 e n a t :=
  (AddMonoidHom.mk' (homogeneousScalarGlobalSections 𝒮 𝒨 e n a)
    (homogeneousScalarGlobalSections_add_right 𝒮 𝒨 e n a)).map_sub s t

/-- Chart fractions are subtractive. -/
theorem coe_fracDeg_sub {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (n : ℤ)
    (s t : shiftedSectionsComponent 𝒮 𝒨 n) :
    (fracDeg 𝒮 𝒨 hf hd n (s - t) : LocalizedModule.Away f M) =
      (fracDeg 𝒮 𝒨 hf hd n s : LocalizedModule.Away f M) -
        (fracDeg 𝒮 𝒨 hf hd n t : LocalizedModule.Away f M) := by
  refine coe_eq_of_forall_moduleToFiber_eq 𝒮 𝒨 hf hd n _
    (fracDeg 𝒮 𝒨 hf hd n s - fracDeg 𝒮 𝒨 hf hd n t) fun x => ?_
  rw [moduleToFiber_coe_fracDeg, Submodule.coe_sub, map_sub, moduleToFiber_coe_fracDeg,
    moduleToFiber_coe_fracDeg]
  rfl

/-- **A homogeneous scalar that kills a section kills every homogeneous multiple of it.** -/
theorem homogeneousScalarGlobalSections_smul_eq_zero {ι : Type*} (fam : ι → S)
    (hfam : ∀ i, fam i ∈ 𝒮 1)
    (hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal)
    (n : ℤ) (s : shiftedSectionsComponent 𝒮 𝒨 n) {b : S} (hb : b ∈ 𝒮 1)
    (hbs : homogeneousScalarGlobalSections 𝒮 𝒨 1 n ⟨b, hb⟩ s = 0)
    (e : ℕ) (c : 𝒮 e) :
    homogeneousScalarGlobalSections 𝒮 𝒨 1 ((e : ℤ) + n) ⟨b, hb⟩
      (homogeneousScalarGlobalSections 𝒮 𝒨 e n c s) = 0 := by
  refine eq_zero_of_forall_coe_frac_eq_zero 𝒮 𝒨 fam hfam hspan _ _ fun i => ?_
  obtain ⟨a, w, hw, hfr⟩ := exists_mk_coe_frac 𝒮 𝒨 (hfam i) n s
  have h1 := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n e c s hw hfr
  have h2 := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) ((e : ℤ) + n) 1 ⟨b, hb⟩ _
    (smul_mem_of_add_eq 𝒮 𝒨 c.2 hw (by ring)) h1
  obtain ⟨k, hk⟩ := exists_pow_smul_smul_eq_zero 𝒮 𝒨 (hfam i) hb n s hbs hw hfr
  rw [h2, mk_eq_zero_iff_exists_pow_smul]
  exact ⟨k, by rw [smul_comm b, smul_comm (fam i ^ k), hk, smul_zero]⟩

end Stacks.AlgebraicGeometry.ProjLargeDegreeSections

end
