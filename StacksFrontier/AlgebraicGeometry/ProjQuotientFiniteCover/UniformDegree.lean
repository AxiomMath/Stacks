module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjQuasiCompact
public import StacksFrontier.AlgebraicGeometry.ProjQuotientFiniteCover.GradedRing
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.UniformDegree

/-!
# A closed subscheme of `Proj` is the `Proj` of a quotient, with no hypothesis on the grading

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a graded ring whose projective spectrum is **quasi-compact** — which
is automatic for the chart of a quasi-compact relative `Proj` — and let `i : Z ⟶ Proj 𝒮` be a
closed immersion. This file proves that `Z` and `Proj (𝒮 / I)` cut out the same ideal sheaf of
`Proj 𝒮`, for `I` any homogeneous ideal whose underlying ideal is the Tag 0BXK ideal of
equations of `Z`, with **no** hypothesis of generation in degree one and **no** Noetherian
hypothesis.

## The one new input

`Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover` of the sibling
`GradedRing.lean` proves the same thing from a finite family of **degree-one** elements whose
standard opens cover `Proj 𝒮`, together with generation in degree one. What replaces both
hypotheses here is `exists_finite_uniform_degree_cover`: a quasi-compact `Proj 𝒮` has a finite
family of homogeneous elements of **one** positive degree `d` whose standard opens cover it. Over
a quasi-compact `Proj 𝒮` finitely many positive-degree elements cover
(`AlgebraicGeometry.Proj.compactSpace_iff`), and raising each to the power that makes its degree
the product of all the degrees changes neither its standard open
(`AlgebraicGeometry.Proj.basicOpen_pow`) nor the cover.

That is the device of Stacks Tag 0801's own proof, which takes `f_0, …, f_n ∈ A_+` and passes to
`d = lcm (deg f_i)`; the chart comparison at degree `d` is
`AlgebraicGeometry.ProjectiveSpectrum.Proj`
`.mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker_uniform` and
`exists_pow_mul_chartFraction_mem_ker_uniform` of
`StacksFrontier/AlgebraicGeometry/ProjSaturation/UniformDegree.lean`.

## Main results

* `Stacks.ProjQuotientFiniteCover.exists_finite_uniform_degree_cover`: the finite cover in one
  positive degree.
* `Stacks.ProjQuotientFiniteCover.exists_pow_mul_mem_idealOfClosedSubscheme_of_cover_uniform` and
  `app_awayMk_eq_zero_iff_of_cover_uniform`: the saturation step and the chart comparison, both
  directions, at a uniform positive degree.
* `Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover_uniform`: **the equality
  of ideal sheaves, from quasi-compactness alone.**
* `Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_saturation`: **the equality of
  ideal sheaves for an ideal that only becomes the ideal of equations after saturation.** This is
  the form a graded ideal generated in a single degree satisfies, since such an ideal is not
  saturated; the hypothesis is that it sits inside the ideal of equations and that on each chart
  of a covering family a numerator killed on `Z` has a power-of-the-chart-element multiple in it.

## References

* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.HomogeneousIdeal

universe u w

namespace Stacks.ProjQuotientFiniteCover

/-! ### A finite cover of a quasi-compact `Proj` in one positive degree -/

section Cover

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **A quasi-compact `Proj 𝒮` is covered by the standard opens of finitely many homogeneous
elements of one and the same positive degree.**

`AlgebraicGeometry.Proj.compactSpace_iff` gives a finite set of positive-degree homogeneous
elements whose standard opens cover. Replacing each `x` of degree `dd x` by `x ^ (d / dd x)`,
where `d` is the product of the degrees, makes every degree equal to `d` and leaves each standard
open unchanged, by `AlgebraicGeometry.Proj.basicOpen_pow`.

This is the finite family Stacks Tag 0801's proof produces with `d = lcm (deg f_i)`. -/
theorem exists_finite_uniform_degree_cover
    [CompactSpace (AlgebraicGeometry.Proj 𝒮)] :
    ∃ (d : ℕ) (_ : 0 < d) (ι : Type u) (_ : Fintype ι) (g : ι → S),
      (∀ j, g j ∈ 𝒮 d) ∧ (⨆ j, AlgebraicGeometry.Proj.basicOpen 𝒮 (g j)) = ⊤ := by
  classical
  obtain ⟨t, ht, hrad⟩ := (AlgebraicGeometry.Proj.compactSpace_iff 𝒮).mp inferInstance
  have htop : (⨆ x ∈ t, AlgebraicGeometry.Proj.basicOpen 𝒮 x) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_irrelevant_le_radical 𝒮 t hrad
  choose dd hddpos hddmem using fun j : {x : S // x ∈ t} => ht j.1 j.2
  set d : ℕ := ∏ j : {x : S // x ∈ t}, dd j with hddef
  have hdpos : 0 < d := Finset.prod_pos fun j _ => hddpos j
  have hdvd : ∀ j : {x : S // x ∈ t}, dd j ∣ d := fun j =>
    Finset.dvd_prod_of_mem dd (Finset.mem_univ j)
  have hepos : ∀ j : {x : S // x ∈ t}, 0 < d / dd j := fun j =>
    Nat.div_pos (Nat.le_of_dvd hdpos (hdvd j)) (hddpos j)
  have hmem : ∀ j : {x : S // x ∈ t}, ((j : S) ^ (d / dd j)) ∈ 𝒮 d := by
    intro j
    have hp := SetLike.pow_mem_graded (A := 𝒮) (d / dd j) (hddmem j)
    rwa [smul_eq_mul, Nat.div_mul_cancel (hdvd j)] at hp
  have hcov : (⨆ j : {x : S // x ∈ t},
      AlgebraicGeometry.Proj.basicOpen 𝒮 ((j : S) ^ (d / dd j))) = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp (htop.ge (Set.mem_univ z))
    obtain ⟨hxt, hxz⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxt⟩, ?_⟩
    rwa [AlgebraicGeometry.Proj.basicOpen_pow 𝒮 x _ (hepos ⟨x, hxt⟩)]
  exact ⟨d, hdpos, {x : S // x ∈ t}, inferInstance,
    fun j => (j : S) ^ (d / dd j), hmem, hcov⟩

/-! ### The chart comparison at a uniform positive degree -/

variable {d : ℕ}

/-- A power `f ^ j` of a degree-`d` element times a degree-`n • d` element has degree
`(j + n) • d`. -/
private theorem pow_mul_mem_graded {f a : S} (hf : f ∈ 𝒮 d) {n : ℕ} (ha : a ∈ 𝒮 (n • d))
    (j : ℕ) : f ^ j * a ∈ 𝒮 ((j + n) • d) := by
  rw [add_smul]
  exact SetLike.mul_mem_graded (SetLike.pow_mem_graded (A := 𝒮) j hf) ha

/-- **One exponent serves every chart, at a uniform positive degree.** If the chart function
`b / f ^ n` lies in the kernel of `i` over `D₊(f)`, and `g` is a finite family of degree-`d`
elements whose standard opens cover `Proj 𝒮`, then `f ^ N · b` lies in the ideal of equations of
`Z` for some `N`.

This is `Stacks.ProjQuotientFiniteCover.exists_pow_mul_mem_idealOfClosedSubscheme_of_cover` with
the degree-one hypotheses relaxed to a common positive degree: the maximum of the per-chart
exponents of `AlgebraicGeometry.ProjectiveSpectrum.Proj`
`.exists_pow_mul_chartFraction_mem_ker_uniform` works on all charts at once, and padding a chart
function by a further power of `f` keeps it in the kernel because the kernel is an ideal. -/
theorem exists_pow_mul_mem_idealOfClosedSubscheme_of_cover_uniform (hd : 0 < d)
    {ι : Type*} [Finite ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 d)
    (hcov : ⨆ j, AlgebraicGeometry.Proj.basicOpen 𝒮 (g j) = ⊤)
    {f : S} (hf : f ∈ 𝒮 d) {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.Proj 𝒮)
    [IsClosedImmersion i] (n : ℕ) (b : 𝒮 (n • d))
    (hb : chartFraction 𝒮 hf n b ∈ RingHom.ker (i.app (AlgebraicGeometry.Proj.basicOpen 𝒮 f)).hom) :
    ∃ N : ℕ, f ^ N * (b : S) ∈ idealOfClosedSubscheme 𝒮 i := by
  classical
  have := Fintype.ofFinite ι
  choose NN hNN using fun j : ι =>
    exists_pow_mul_chartFraction_mem_ker_uniform 𝒮 hd hf (hg j) i n b hb
  refine ⟨Finset.univ.sup NN,
    mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker_uniform 𝒮 hd g hg hcov i
      ⟨f ^ Finset.univ.sup NN * (b : S), pow_mul_mem_graded 𝒮 hf b.2 _⟩ fun j C hC => ?_⟩
  obtain ⟨M, hM⟩ := Nat.exists_eq_add_of_le
    (Finset.le_sup (f := NN) (Finset.mem_univ j))
  have hC' : (C : S) = f ^ Finset.univ.sup NN * (b : S) := hC
  have hum : f ^ M ∈ 𝒮 (M • d) := SetLike.pow_mem_graded (A := 𝒮) M hf
  have hvm := pow_mul_mem_graded 𝒮 hf b.2 (NN j)
  have hwm := pow_mul_mem_graded 𝒮 hf hvm M
  rw [chartFraction_eq_of_cross 𝒮 (hg j) (Finset.univ.sup NN + n) (M + (NN j + n)) C
      ⟨_, hwm⟩ (by rw [hC', hM]; ring),
    chartFraction_mul 𝒮 (hg j) M (NN j + n) ⟨f ^ M, hum⟩ ⟨_, hvm⟩ ⟨_, hwm⟩ rfl]
  exact Ideal.mul_mem_left _ _ (hNN j ⟨_, hvm⟩ rfl)

/-- **The chart comparison at a uniform positive degree, both directions.** For `f` of degree `d`,
a degree-zero fraction `a / f ^ n` with `a` homogeneous of degree `n · d` is carried to zero by
`i` over `D₊(f)` exactly when some `f ^ j · a` lies in the ideal of equations of `Z`.

This is `Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover` with generation in
degree one and the degree-one cover replaced by a cover in one positive degree `d`. -/
theorem app_awayMk_eq_zero_iff_of_cover_uniform (hd : 0 < d)
    {ι : Type*} [Finite ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 d)
    (hcov : ⨆ j, AlgebraicGeometry.Proj.basicOpen 𝒮 (g j) = ⊤)
    {f : S} (hf : f ∈ 𝒮 d) {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.Proj 𝒮)
    [IsClosedImmersion i] (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • d)) :
    (i.app (AlgebraicGeometry.Proj.basicOpen 𝒮 f)).hom
        ((AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n a ha)) = 0 ↔
      ∃ j : ℕ, f ^ j * a ∈ idealOfClosedSubscheme 𝒮 i := by
  refine ⟨fun h => exists_pow_mul_mem_idealOfClosedSubscheme_of_cover_uniform 𝒮 hd g hg hcov hf i n
    ⟨a, ha⟩ h, ?_⟩
  rintro ⟨j, hj⟩
  have hmem := pow_mul_mem_graded 𝒮 hf ha j
  have := algebraicGeometry_isInvertible_twistingSheaf_smul 𝒮
    (ratioLocus_eq_top_of_iSup_basicOpen_degree 𝒮 g hg hcov) (j + n)
  have h1 := chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme 𝒮 hf hd i
    (j + n) ⟨f ^ j * a, hmem⟩ hj
  rw [chartFraction_eq_of_cross 𝒮 hf (j + n) n ⟨f ^ j * a, hmem⟩ ⟨a, ha⟩
    (by change f ^ j * a * f ^ n = a * f ^ (j + n); ring)] at h1
  exact RingHom.mem_ker.mp h1

end Cover

/-! ### The equality of ideal sheaves -/

section Quotient

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **`Z` and `Proj (𝒮 / I)` cut out the same ideal sheaf of `Proj 𝒮`**, for `I` any homogeneous
ideal whose underlying ideal is the Tag 0BXK ideal of equations of `Z`, with no hypothesis on the
grading beyond quasi-compactness of `Proj 𝒮`.

This is `Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover` with its two
hypotheses — generation in degree one and a finite degree-one cover — replaced by the finite cover
in one positive degree that `exists_finite_uniform_degree_cover` extracts from
quasi-compactness. -/
theorem ker_eq_ker_projMap_quotientMk_of_cover_uniform
    [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.Proj 𝒮) [IsClosedImmersion i]
    (I : HomogeneousIdeal 𝒮)
    (hI : I.toIdeal = Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme 𝒮 i)
    (hψ : HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      (HomogeneousIdeal.irrelevant 𝒮).map (quotientMk I)) :
    i.ker = (AlgebraicGeometry.Proj.map (quotientMk I) hψ).ker := by
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map (quotientMk I) hψ) :=
    AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective hψ (surjective_quotientMk I)
  obtain ⟨d, hd, ι, hι, g, hg, hcov⟩ := exists_finite_uniform_degree_cover 𝒮
  let := hι
  have key : ∀ (k : ι) (z : Away 𝒮 (g k)),
      ((i.app (AlgebraicGeometry.Proj.basicOpen 𝒮 (g k))).hom
            ((AlgebraicGeometry.Proj.awayToSection 𝒮 (g k)).hom z) = 0 ↔
        ((AlgebraicGeometry.Proj.map (quotientMk I) hψ).app
              (AlgebraicGeometry.Proj.basicOpen 𝒮 (g k))).hom
            ((AlgebraicGeometry.Proj.awayToSection 𝒮 (g k)).hom z) = 0) := by
    intro k z
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (hg k) z
    have h2 := awayToSection_mem_ker_app_projMap_quotientMk_iff 𝒮 I hψ (hg k) hd n a ha
    rw [RingHom.mem_ker] at h2
    have hEx : (∃ j : ℕ, g k ^ j * a ∈ I.toIdeal) ↔ ∃ j : ℕ, g k ^ j * a ∈
        Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme 𝒮 i := by
      rw [hI]
    exact (app_awayMk_eq_zero_iff_of_cover_uniform 𝒮 hd g hg hcov (hg k) i n a ha).trans
      (h2.trans hEx).symm
  exact le_antisymm
    (ker_le_ker_of_app_awayMk 𝒮 i _ g (fun _ => d) hg (fun _ => hd) hcov
      fun k z => (key k z).1)
    (ker_le_ker_of_app_awayMk 𝒮 _ i g (fun _ => d) hg (fun _ => hd) hcov
      fun k z => (key k z).2)

/-! ### The equality of ideal sheaves for an ideal that is only saturation-equivalent -/

/-- **`Z` and `Proj (𝒮 / I)` cut out the same ideal sheaf of `Proj 𝒮` for an ideal `I` which is
contained in the ideal of equations and recovers it after saturation on each chart.**

`ker_eq_ker_projMap_quotientMk_of_cover_uniform` asks that `I` *be* the Tag 0BXK ideal of
equations of `Z`. A graded ideal generated in a single degree is almost never that ideal — it
agrees with it only up to saturation, since the ideal of equations is saturated and `ℱ𝒜` is not —
so what is asked here instead is exactly what the saturation supplies chart by chart: `I` lies
inside the ideal of equations, and over each member `D₊(f c)` of a family of standard opens
covering `Proj 𝒮` a homogeneous numerator whose fraction dies on `Z` already has some
power-of-`f c` multiple in `I`.

The covering family is arbitrary — its index type need not be finite and its degrees need not
agree — because it plays only the role of the charts on which the two ideal sheaves are compared,
which is all `ker_le_ker_of_app_awayMk` asks. The finite family of one positive degree that the
chart comparison `app_awayMk_eq_zero_iff_of_cover_uniform` needs is a different family, produced
from quasi-compactness by `exists_finite_uniform_degree_cover`; the two are reconciled by raising
each member `f c` of the given family to the power `d` and each member `g j` of the extracted
family to the power `e c`, which makes both homogeneous of the one degree `e c * d` and changes
no standard open (`AlgebraicGeometry.Proj.basicOpen_pow`). Raising `f c` to a power also costs
nothing on the right-hand sides, since `I` is an ideal: a multiple by `f c ^ k` is padded up to a
multiple by `f c ^ (d * k)` by multiplying by a further power. -/
theorem ker_eq_ker_projMap_quotientMk_of_saturation
    [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.Proj 𝒮) [IsClosedImmersion i]
    (I : HomogeneousIdeal 𝒮)
    (hle : I.toIdeal ≤
      Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme 𝒮 i)
    {κ : Type*} (e : κ → ℕ) (f : κ → S) (hf : ∀ c, f c ∈ 𝒮 (e c)) (he : ∀ c, 0 < e c)
    (hcov : ⨆ c, AlgebraicGeometry.Proj.basicOpen 𝒮 (f c) = ⊤)
    (hsat : ∀ (c : κ) (n : ℕ) (a : S), a ∈ 𝒮 (n • e c) →
      (∃ j : ℕ, f c ^ j * a ∈
        Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme 𝒮 i) →
      ∃ j : ℕ, f c ^ j * a ∈ I.toIdeal)
    (hψ : HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      (HomogeneousIdeal.irrelevant 𝒮).map (quotientMk I)) :
    i.ker = (AlgebraicGeometry.Proj.map (quotientMk I) hψ).ker := by
  classical
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map (quotientMk I) hψ) :=
    AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective hψ (surjective_quotientMk I)
  obtain ⟨d, hd, ι, hι, g, hg, hcovg⟩ := exists_finite_uniform_degree_cover 𝒮
  let := hι
  have hFmem : ∀ c, f c ^ d ∈ 𝒮 (e c * d) := by
    intro c
    have h := SetLike.pow_mem_graded (A := 𝒮) d (hf c)
    rwa [smul_eq_mul, Nat.mul_comm d (e c)] at h
  have hGmem : ∀ (c : κ) (j : ι), g j ^ e c ∈ 𝒮 (e c * d) := by
    intro c j
    have h := SetLike.pow_mem_graded (A := 𝒮) (e c) (hg j)
    rwa [smul_eq_mul] at h
  have hDpos : ∀ c, 0 < e c * d := fun c => Nat.mul_pos (he c) hd
  have hcovF : ⨆ c, AlgebraicGeometry.Proj.basicOpen 𝒮 (f c ^ d) = ⊤ := by
    have h : ∀ c, AlgebraicGeometry.Proj.basicOpen 𝒮 (f c ^ d) =
        AlgebraicGeometry.Proj.basicOpen 𝒮 (f c) :=
      fun c => AlgebraicGeometry.Proj.basicOpen_pow 𝒮 (f c) d hd
    simpa only [h] using hcov
  have hcovG : ∀ c : κ, ⨆ j, AlgebraicGeometry.Proj.basicOpen 𝒮 (g j ^ e c) = ⊤ := by
    intro c
    have h : ∀ j, AlgebraicGeometry.Proj.basicOpen 𝒮 (g j ^ e c) =
        AlgebraicGeometry.Proj.basicOpen 𝒮 (g j) :=
      fun j => AlgebraicGeometry.Proj.basicOpen_pow 𝒮 (g j) (e c) (he c)
    simpa only [h] using hcovg
  have key : ∀ (c : κ) (z : Away 𝒮 (f c ^ d)),
      ((i.app (AlgebraicGeometry.Proj.basicOpen 𝒮 (f c ^ d))).hom
            ((AlgebraicGeometry.Proj.awayToSection 𝒮 (f c ^ d)).hom z) = 0 ↔
        ((AlgebraicGeometry.Proj.map (quotientMk I) hψ).app
              (AlgebraicGeometry.Proj.basicOpen 𝒮 (f c ^ d))).hom
            ((AlgebraicGeometry.Proj.awayToSection 𝒮 (f c ^ d)).hom z) = 0) := by
    intro c z
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (hFmem c) z
    have h2 := awayToSection_mem_ker_app_projMap_quotientMk_iff 𝒮 I hψ (hFmem c) (hDpos c) n a ha
    rw [RingHom.mem_ker] at h2
    rw [app_awayMk_eq_zero_iff_of_cover_uniform 𝒮 (hDpos c) (fun j => g j ^ e c)
      (fun j => hGmem c j) (hcovG c) (hFmem c) i n a ha, h2]
    have hdeg : (n * d) • e c = n • (e c * d) := by
      simp only [smul_eq_mul]; ring
    have ha' : a ∈ 𝒮 ((n * d) • e c) := by rw [hdeg]; exact ha
    refine ⟨fun hex => ?_, fun ⟨j, hj⟩ => ⟨j, hle hj⟩⟩
    obtain ⟨j, hj⟩ := hex
    obtain ⟨k, hk⟩ := hsat c (n * d) a ha' ⟨d * j, by rw [pow_mul]; exact hj⟩
    refine ⟨k, ?_⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_left k hd)
    have heq : (f c ^ d) ^ k * a = f c ^ m * (f c ^ k * a) := by
      rw [← pow_mul, hm, pow_add]; ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hk
  exact le_antisymm
    (ker_le_ker_of_app_awayMk 𝒮 i _ (fun c => f c ^ d) (fun c => e c * d) hFmem hDpos hcovF
      fun c z => (key c z).1)
    (ker_le_ker_of_app_awayMk 𝒮 _ i (fun c => f c ^ d) (fun c => e c * d) hFmem hDpos hcovF
      fun c z => (key c z).2)

end Quotient

end Stacks.ProjQuotientFiniteCover

end
