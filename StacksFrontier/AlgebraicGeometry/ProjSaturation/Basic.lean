module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.RingTheory.GradedAlgebra.FinitelyGenerated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# When does a homogeneous element have vanishing twisted section?

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring generated in degree one over `𝒮 0`, and
let `b ∈ 𝒮 n`. The canonical global section `degreeSection 𝒮 n b` of `𝒪_{Proj 𝒮}(n)` vanishes
exactly when `b` is annihilated by one whole homogeneous component `𝒮 N`. When `S` is in
addition Noetherian this is an equivalence, so the kernel of

`S ⟶ ⨁_{n ≥ 0} Γ(Proj 𝒮, 𝒪(n))`

is the set of elements killed by some `𝒮 N` — the *saturation* of `0`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_eq_zero_of_degreeSection_eq_zero'`
  and `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_eq_zero_of_degreeSection_eq_zero`:
  if the section of `b` vanishes then each homogeneous element of positive degree — in
  particular each degree-one element — kills `b` after raising to a power.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.degreeSection_eq_zero_of_forall_exists_pow_mul_eq_zero`: conversely, a section killed on
  every chart of a cover by positive-degree standard opens vanishes.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_annihilating_degree_of_degreeSection_eq_zero`
  and `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_of_annihilating_degree`:
  the two implications.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff`: **the criterion**.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.degreeSection_eq_zero_iff_exists_irrelevant_pow_le_annihilator`: the criterion in the
  `𝒮₊`-power torsion form of the source.

## Implementation notes

The section attached to `b ∈ 𝒮 n` restricts, on the standard open `D₊(f)` of a degree-one
element `f`, to the degree-zero fraction `b / f ^ 0`, by
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_basicOpen`. So the
section vanishes on `D₊(f)` exactly when `b` dies in `LocalizedModule.Away f S`, i.e. when some
power of `f` kills `b`. That gives one implication directly, and the other from the covering of
`Proj 𝒮` by the `D₊(f)` with `f` of degree one
(`Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top`).

Turning "each degree-one `f` kills `b` eventually" into "one whole `𝒮 N` kills `b`" is where
Noetherianness enters: the degree-one elements generate the irrelevant ideal
(`generates_algebra_iff_generates_irrelevant`), that ideal is then contained in the radical of
the annihilator of `b`, and a finitely generated ideal inside a radical has a power inside the
ideal (`Ideal.exists_pow_le_of_le_radical_of_fg`). Finally every element of `𝒮 N` lies in the
`N`-th power of the irrelevant ideal, because `𝒮` is generated in degree one.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- When `S` is generated in degree one over `𝒮 0`, the degree-one elements generate the
irrelevant ideal. -/
theorem span_degreeOne_eq_irrelevant (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    Ideal.span (𝒮 1 : Set S) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal := by
  have hrange : Set.range (fun x : 𝒮 1 ↦ (x : S)) = (𝒮 1 : Set S) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hadj : Algebra.adjoin (𝒮 0) (Set.range (fun x : 𝒮 1 ↦ (x : S))) = ⊤ := by
    rwa [hrange]
  have hh := (generates_algebra_iff_generates_irrelevant 𝒮 (fun x : 𝒮 1 ↦ (x : S))
    (fun _ ↦ 1) (fun _ ↦ Nat.one_pos) (fun x ↦ x.2)).mp hadj
  rwa [hrange] at hh

/-- In a Noetherian graded ring generated in degree one, finitely many degree-one elements
generate the irrelevant ideal. -/
@[ega "II 2.7.6"]
theorem exists_finset_degreeOne_span_irrelevant [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    ∃ s : Finset S, (∀ x ∈ s, x ∈ 𝒮 1) ∧
      Ideal.span (s : Set S) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal := by
  classical
  have hspan1 := span_degreeOne_eq_irrelevant 𝒮 hgen
  obtain ⟨t, ht⟩ := Ideal.fg_of_isNoetherianRing (HomogeneousIdeal.irrelevant 𝒮).toIdeal
  have hsub : (t : Set S) ⊆ Submodule.span S (𝒮 1 : Set S) := by
    intro x hx
    change x ∈ Ideal.span (𝒮 1 : Set S)
    rw [hspan1, ← ht]
    exact Ideal.subset_span hx
  obtain ⟨s, hs, hts⟩ := Submodule.subset_span_finite_of_subset_span hsub
  refine ⟨s, hs, le_antisymm (Ideal.span_le.mpr fun x hx ↦
    mem_irrelevant_of_mem_of_pos 𝒮 (hs hx) Nat.one_pos) ?_⟩
  rwa [← ht, Ideal.span_le]

/-- In a graded ring generated in degree one, a homogeneous element of degree `n` lies in the
`n`-th power of the irrelevant ideal. -/
theorem mem_irrelevant_pow_of_mem (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    (n : ℕ) {x : S} (hx : x ∈ 𝒮 n) : x ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ n := by
  have hspan1 := span_degreeOne_eq_irrelevant 𝒮 hgen
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hxspan : x ∈ Ideal.span (𝒮 1 : Set S) := by
        rw [hspan1]
        exact mem_irrelevant_of_mem_of_pos 𝒮 hx (Nat.succ_pos n)
      obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hxspan
      rw [← proj_eq_self_of_mem 𝒮 hx, ← hsum, map_sum]
      simp only [smul_eq_mul]
      rw [pow_succ]
      refine Ideal.sum_mem _ fun i _ ↦ ?_
      rw [proj_mul_eq 𝒮 (c i) (g i : S) 1 (n + 1) (g i).property (by omega)]
      exact Ideal.mul_mem_mul (ih (proj_mem 𝒮 (c i) n))
        (mem_irrelevant_of_mem_of_pos 𝒮 (g i).property Nat.one_pos)

/-- A fraction over the powers of `f` vanishes exactly when a power of `f` kills its numerator.
The denominator is irrelevant. -/
private theorem mk_eq_zero_iff_exists_pow_mul (f m : S) (s : Submonoid.powers f) :
    LocalizedModule.mk m s = 0 ↔ ∃ k : ℕ, f ^ k * m = 0 := by
  rw [show (0 : LocalizedModule (Submonoid.powers f) S) =
    LocalizedModule.mk 0 1 from (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := u.2
    simp only [Submonoid.smul_def, one_smul, smul_eq_mul, mul_zero] at hu
    exact ⟨k, by rwa [show f ^ k = (u : S) from hk]⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨f ^ k, ⟨k, rfl⟩⟩, ?_⟩
    simpa only [Submonoid.smul_def, one_smul, smul_eq_mul, mul_zero] using hk

/-- The restriction of the twisted section of `b ∈ 𝒮 n` to `D₊(f)`, for `f` homogeneous of
positive degree, vanishes exactly when a power of `f` kills `b`. -/
private theorem degreeSection_map_basicOpen_eq_zero_iff {n : ℕ} (b : 𝒮 n) {f : S} {d : ℕ}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    (associatedModuleSheaf 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))).val.map
        (homOfLE le_top : ProjectiveSpectrum.basicOpen 𝒮 f ⟶
          (⊤ : Opens (ProjectiveSpectrum.top 𝒮))).op (degreeSection 𝒮 n b) = 0 ↔
      ∃ k : ℕ, f ^ k * (b : S) = 0 := by
  set M := twistGrading (S := S) 𝒮 (n : ℤ) with hM
  have hb0 : (b : S) ∈ M 0 := by
    simp [hM, integerGrading, homogeneousSubmodule]
  set e := associatedModuleSheafStandardOpenEquiv 𝒮 M hf hd
  have hfrac : e ((associatedModuleSheaf 𝒮 M).val.map (homOfLE le_top).op
      (degreeSection 𝒮 n b)) = degreeZeroFraction 𝒮 M hf 0 (b : S) (by simpa using hb0) :=
    degreeZeroToGlobalSections_basicOpen 𝒮 M hf hd ⟨(b : S), hb0⟩
  refine (map_eq_zero_iff e e.injective).symm.trans ?_
  rw [hfrac]
  constructor
  · intro h0
    have hval := congrArg Subtype.val h0
    simp only [degreeZeroFraction, ZeroMemClass.coe_zero] at hval
    exact (mk_eq_zero_iff_exists_pow_mul f (b : S) _).mp hval
  · intro hk
    apply Subtype.ext
    simp only [degreeZeroFraction, ZeroMemClass.coe_zero]
    exact (mk_eq_zero_iff_exists_pow_mul f (b : S) _).mpr hk

/-- **If the canonical section of `𝒪(n)` attached to `b ∈ 𝒮 n` vanishes, then every homogeneous
element of positive degree kills `b` after raising it to a power.** The section restricted to
`D₊(f)` is the degree-zero fraction `b / f ^ 0`, so its vanishing says that `b` dies in the
localization of `S` at `f`.

Nothing here asks the degree of `f` to be one, nor the twist `𝒪(n)` to be invertible: the
section is read on `D₊(f)` through the associated-module-sheaf description
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_basicOpen`, whose
only hypothesis on the degree of `f` is that it be positive. -/
theorem exists_pow_mul_eq_zero_of_degreeSection_eq_zero' {n : ℕ} (b : 𝒮 n)
    (hb : degreeSection 𝒮 n b = 0) {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    ∃ k : ℕ, f ^ k * (b : S) = 0 :=
  (degreeSection_map_basicOpen_eq_zero_iff 𝒮 b hf hd).mp <| by
    rw [hb]
    exact map_zero _

/-- **If the canonical section of `𝒪(n)` attached to `b ∈ 𝒮 n` vanishes, then every degree-one
element kills `b` after raising it to a power.** -/
theorem exists_pow_mul_eq_zero_of_degreeSection_eq_zero {n : ℕ} (b : 𝒮 n)
    (hb : degreeSection 𝒮 n b = 0) {f : S} (hf : f ∈ 𝒮 1) :
    ∃ k : ℕ, f ^ k * (b : S) = 0 :=
  exists_pow_mul_eq_zero_of_degreeSection_eq_zero' 𝒮 b hb hf Nat.one_pos

/-- If a power of the irrelevant ideal annihilates `b`, then so does each element of `𝒮 N`. -/
private theorem mul_eq_zero_of_irrelevant_pow_le_annihilator
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {N : ℕ} {b : S}
    (hpow : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N ≤
      (Submodule.span S ({b} : Set S)).annihilator) {y : S} (hy : y ∈ 𝒮 N) : y * b = 0 := by
  simpa [smul_eq_mul] using (Submodule.mem_annihilator_span_singleton b y).mp
    (hpow (mem_irrelevant_pow_of_mem 𝒮 hgen N hy))

/-- **In a Noetherian graded ring generated in degree one, a vanishing twisted section means that
a power of the irrelevant ideal annihilates the element** — that is, the element is
`𝒮₊`-power torsion. -/
theorem exists_irrelevant_pow_le_annihilator_of_degreeSection_eq_zero [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n)
    (hb : degreeSection 𝒮 n b = 0) :
    ∃ N : ℕ, (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N ≤
      (Submodule.span S ({(b : S)} : Set S)).annihilator := by
  classical
  set K := (Submodule.span S ({(b : S)} : Set S)).annihilator
  obtain ⟨s, hs1, hspan⟩ := exists_finset_degreeOne_span_irrelevant 𝒮 hgen
  have hJrad : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ K.radical := by
    rw [← hspan, Ideal.span_le]
    intro f hf
    obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_degreeSection_eq_zero 𝒮 b hb (hs1 f hf)
    rw [SetLike.mem_coe, Ideal.mem_radical_iff]
    exact ⟨k, (Submodule.mem_annihilator_span_singleton (b : S) (f ^ k)).mpr
      (by simpa [smul_eq_mul] using hk)⟩
  exact Ideal.exists_pow_le_of_le_radical_of_fg hJrad (Ideal.fg_of_isNoetherianRing _)

/-- **In a Noetherian graded ring generated in degree one, a vanishing twisted section means
annihilation by a whole homogeneous component.** -/
theorem exists_annihilating_degree_of_degreeSection_eq_zero [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n)
    (hb : degreeSection 𝒮 n b = 0) :
    ∃ N : ℕ, ∀ y : S, y ∈ 𝒮 N → y * (b : S) = 0 := by
  obtain ⟨N, hpow⟩ :=
    exists_irrelevant_pow_le_annihilator_of_degreeSection_eq_zero 𝒮 hgen b hb
  exact ⟨N, fun y hy ↦ mul_eq_zero_of_irrelevant_pow_le_annihilator 𝒮 hgen hpow hy⟩

/-- **A twisted section that dies on every chart of a cover vanishes.** If the standard opens of
a family of homogeneous elements of positive degree cover `Proj 𝒮`, and each member of the family
has a power killing `b`, then the twisted section of `b` is zero: on `D₊(g j)` the section is the
fraction `b / (g j) ^ 0`, and that fraction is zero exactly because some power of `g j` kills `b`.

No hypothesis on the grading beyond the cover, and no hypothesis relating the degree `n` of the
twist to the degrees of the `g j`. -/
theorem degreeSection_eq_zero_of_forall_exists_pow_mul_eq_zero {ι : Type*} (g : ι → S)
    (hg : ∀ j, ∃ d : ℕ, 0 < d ∧ g j ∈ 𝒮 d)
    (hcov : ⨆ j, ProjectiveSpectrum.basicOpen 𝒮 (g j) = ⊤)
    {n : ℕ} (b : 𝒮 n) (hkill : ∀ j, ∃ k : ℕ, g j ^ k * (b : S) = 0) :
    degreeSection 𝒮 n b = 0 := by
  classical
  set M := twistGrading (S := S) 𝒮 (n : ℤ)
  apply (associatedModuleSheafSectionsEquiv 𝒮 M ⊤).injective
  apply Subtype.ext
  funext x
  have hxcover : x.1 ∈ ⨆ j, ProjectiveSpectrum.basicOpen 𝒮 (g j) := by
    rw [hcov]
    exact Set.mem_univ _
  obtain ⟨j, hxf⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  obtain ⟨d, hd, hf⟩ := hg j
  let i : ProjectiveSpectrum.basicOpen 𝒮 (g j) ⟶ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) :=
    homOfLE le_top
  have hres0 : (associatedModuleSheaf 𝒮 M).val.map i.op (degreeSection 𝒮 n b) = 0 :=
    (degreeSection_map_basicOpen_eq_zero_iff 𝒮 b hf hd).mpr (hkill j)
  have hpoint := associatedModuleSheaf_restrict_apply (𝒜 := 𝒮) (𝒨 := M) i
    (degreeSection 𝒮 n b) (⟨x.1, hxf⟩ : ProjectiveSpectrum.basicOpen 𝒮 (g j))
  have hlocal0 : (associatedModuleSheafSectionsEquiv 𝒮 M
      (ProjectiveSpectrum.basicOpen 𝒮 (g j))
      ((associatedModuleSheaf 𝒮 M).val.map i.op (degreeSection 𝒮 n b))).1
      ⟨x.1, hxf⟩ = 0 := by
    rw [hres0]
    rfl
  exact hpoint.symm.trans hlocal0

/-- **If a whole homogeneous component kills `b`, the twisted section of `b` vanishes.** The
standard opens of the degree-one elements cover `Proj 𝒮`, and on `D₊(f)` the section is the
fraction `b / f ^ 0`, which is zero because `f ^ N` kills `b`. -/
theorem degreeSection_eq_zero_of_annihilating_degree
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n)
    (hkill : ∃ N : ℕ, ∀ y : S, y ∈ 𝒮 N → y * (b : S) = 0) :
    degreeSection 𝒮 n b = 0 := by
  obtain ⟨N, hN⟩ := hkill
  exact degreeSection_eq_zero_of_forall_exists_pow_mul_eq_zero 𝒮 (fun f : 𝒮 1 ↦ (f : S))
    (fun f ↦ ⟨1, Nat.one_pos, f.2⟩)
    (Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen) b
    fun f ↦ ⟨N, hN ((f : S) ^ N) (by simpa using SetLike.pow_mem_graded N f.2)⟩

/-- **The criterion: in a Noetherian graded ring generated in degree one over `𝒮 0`, the
canonical twisted section of a homogeneous element vanishes exactly when the element is
annihilated by one whole homogeneous component.** Equivalently, the kernel of
`S ⟶ ⨁_{n ≥ 0} Γ(Proj 𝒮, 𝒪(n))` is the set of elements some `𝒮 N` kills. -/
theorem degreeSection_eq_zero_iff [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n) :
    degreeSection 𝒮 n b = 0 ↔ ∃ N : ℕ, ∀ y : S, y ∈ 𝒮 N → y * (b : S) = 0 :=
  ⟨exists_annihilating_degree_of_degreeSection_eq_zero 𝒮 hgen b,
    degreeSection_eq_zero_of_annihilating_degree 𝒮 hgen b⟩

/-- **The same criterion in the `𝒮₊`-power torsion form of the source**: the twisted section of
a homogeneous element vanishes exactly when some power of the irrelevant ideal annihilates it. -/
theorem degreeSection_eq_zero_iff_exists_irrelevant_pow_le_annihilator [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n) :
    degreeSection 𝒮 n b = 0 ↔ ∃ N : ℕ, (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N ≤
      (Submodule.span S ({(b : S)} : Set S)).annihilator := by
  refine ⟨exists_irrelevant_pow_le_annihilator_of_degreeSection_eq_zero 𝒮 hgen b,
    fun ⟨N, hpow⟩ ↦ degreeSection_eq_zero_of_annihilating_degree 𝒮 hgen b
      ⟨N, fun _ hy ↦ mul_eq_zero_of_irrelevant_pow_le_annihilator 𝒮 hgen hpow hy⟩⟩

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
