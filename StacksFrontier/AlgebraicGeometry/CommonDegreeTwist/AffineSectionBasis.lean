module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.Basic
public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.TwistComparison
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# The affine nonvanishing opens of the divisible twists are a basis on an open of `Proj`

Let `S` be a graded ring, `X = Proj(S)` and `Y ⊆ X` an open admitting a finite cover by standard
opens `D₊(f_i)` with the `f_i` homogeneous of one common positive degree `d`. For `n ≥ 1` and
`f ∈ S_{nd}` the global section of `𝒪(nd)` attached to `f` restricts to a global section `s` of
`𝒪_Y(nd)`, and its nonvanishing locus is `D₊(f) ∩ Y`. Since the standard opens `D₊(f)` are a
basis for the topology of `X` and are affine, the affine opens so obtained are a basis for the
topology of `Y`.

## Main definitions

* `Stacks.AlgebraicGeometry.CommonDegreeTwist.restrictedTwist`: the twist `𝒪(c)` of `Proj(S)`
  pulled back to an open subscheme.
* `Stacks.AlgebraicGeometry.CommonDegreeTwist.restrictedDegreeSection`: the global section of
  `𝒪_Y(k)` attached to a homogeneous element of degree `k`.

## Main results

* `Stacks.AlgebraicGeometry.CommonDegreeTwist.nonvanishingLocus_restrictedDegreeSection`: the
  nonvanishing locus of that section is `D₊(f) ∩ Y`, in the spelling the ample theory uses. This
  is the form of **Stacks Tag 01MW (5)** on the open subscheme `Y` rather than on `Proj(S)`.
* `Stacks.AlgebraicGeometry.CommonDegreeTwist.isBasis_affineNonvanishing_restrictedTwist`:
  **Stacks Tag 01MW (7)**, the affine nonvanishing opens are a basis for the topology of `Y`.
* `Stacks.AlgebraicGeometry.CommonDegreeTwist.isBasis_nonvanishing_restrictedTwist`:
  **Stacks Tag 01MW (6)**, the same with the affineness requirement dropped.
* `Stacks.AlgebraicGeometry.CommonDegreeTwist.exists_degree_forall`: **Stacks Tag 01MW** as the
  source states it — a quasi-compact open admits *some* degree `d ≥ 1` for which all seven
  clauses hold at once.

## The route

Three inputs, all in the library.

* **Stacks Tag 01MV** on `Proj(S)`,
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.mem_nonvanishingLocus_degreeSection_iff`, which
  is stated at the ringed-space spelling of the nonvanishing locus,
  `Stacks.SheafOfModules.nonvanishingLocus`.
* **Stacks Tag 0H78** for a morphism of schemes,
  `Stacks.NonvanishingPullback.preimage_nonvanishingLocus`, at the scheme spelling
  `Stacks.Ample.nonvanishingLocus`, which is the one ampleness is written over.
* The standard opens: they form a basis (`AlgebraicGeometry.Proj.isBasis_basicOpen`), they are
  affine in positive degree (`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`), and
  `AlgebraicGeometry.Proj.basicOpen_pow` lets the degree of the defining element be raised to a
  multiple of `d` without changing the open.

The two spellings of the nonvanishing locus are reconciled once, in
`mem_nonvanishingLocus_sectionsOfTop_iff'`, for an arbitrary scheme: the only genuine difference
is the module structure on the stalk, and
`Stacks.NonvanishingPullback.mem_maximalSmul_iff` identifies the two.

## Implementation notes

Given a point `x` of `Y` and an open `V ∋ x` of `Y`, the source picks a standard open
`D₊(r) ⊆ Y.ι(V)` and a member `D₊(g)` of the cover containing `x`. Writing `p` for the degree-`i`
homogeneous component of `r` that does not vanish at `x`, the element `(pg)^d` is homogeneous of
degree `(d + i)d`, a multiple of `d`, and `D₊((pg)^d) = D₊(p) ∩ D₊(g) ⊆ D₊(r)`, so its preimage in
`Y` is an affine open between `x` and `V`.

The ambient scheme has to be supplied explicitly to `Stacks.Ample.nonvanishingLocus` at
`Proj(S)`: its type is `X.Modules` for an implicit scheme `X`, and recovering `X` from the type
of `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` is a higher-order unification
problem that elaboration does not solve.

## References

* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.CommonDegreeTwist

universe u w t

/-! ### The two spellings of the nonvanishing locus -/

/-- **The two spellings of the nonvanishing locus of Stacks Tag 01CY agree.**
`Stacks.Ample.nonvanishingLocus`, which the ample theory is written over, takes a global section
of a module on a scheme; `Stacks.SheafOfModules.nonvanishingLocus` takes a
restriction-compatible family of sections of a module on a ringed space. The germ of the section
is the same element in both, and the submodule `𝔪_x · M_x` is the same submodule by
`Stacks.NonvanishingPullback.mem_maximalSmul_iff`. -/
theorem mem_nonvanishingLocus_sectionsOfTop_iff' {X : Scheme.{u}} (M : X.Modules)
    (m : Γ(M, ⊤)) (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus M m ↔
      x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M
        (Stacks.SheafOfModules.sectionsOfTop M m) :=
  Iff.trans (not_congr (Stacks.NonvanishingPullback.mem_maximalSmul_iff M x _))
    (Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_iff
      (X := X.toRingedSpace) M m x).symm

section Proj

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Stacks Tag 01MV in the spelling the ample theory uses.** At a point of the invertible locus
`W_d` the global section of `𝒪(nd)` attached to a homogeneous element `f` of degree `nd` is
nonvanishing exactly on the standard open `D₊(f)`. -/
theorem mem_nonvanishingLocus_degreeSection_iff' (d n : ℕ) (f : 𝒮 (n * d))
    {x : ProjectiveSpectrum.top 𝒮} (hx : x ∈ whereInvertible 𝒮 d) :
    x ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒮)
        (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)) (degreeSection 𝒮 (n * d) f) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) :=
  (mem_nonvanishingLocus_sectionsOfTop_iff' (X := AlgebraicGeometry.Proj 𝒮)
      (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)) (degreeSection 𝒮 (n * d) f) x).trans
    (mem_nonvanishingLocus_degreeSection_iff 𝒮 d n f hx)

/-! ### The twists and their sections on an open subscheme -/

/-- The twist `𝒪(c)` of `Proj(S)`, pulled back to an open subscheme `Y`. -/
noncomputable abbrev restrictedTwist (Y : (AlgebraicGeometry.Proj 𝒮).Opens) (c : ℤ) :
    Y.toScheme.Modules :=
  (modulePullback Y.ι.toLRSHom.toShHom).obj (twistingSheaf 𝒮 c)

/-- The global section of `𝒪_Y(k)` attached to a homogeneous element of degree `k`: the global
section of `𝒪(k)` of Stacks Tag 01MP, pulled back along the open immersion. -/
noncomputable def restrictedDegreeSection (Y : (AlgebraicGeometry.Proj 𝒮).Opens) (k : ℕ)
    (f : 𝒮 k) : Γ(restrictedTwist 𝒮 Y (k : ℤ), ⊤) :=
  Stacks.NonvanishingPullback.pullbackGlobalSection Y.ι (twistingSheaf 𝒮 (k : ℤ))
    (degreeSection 𝒮 k f)

/-- **Stacks Tag 01MW (5) on the open subscheme.** For `Y` covered by standard opens of one
common degree `d` and `f` homogeneous of degree `nd`, the nonvanishing locus on `Y` of the
restricted global section of `𝒪(nd)` attached to `f` is `D₊(f) ∩ Y`. -/
theorem nonvanishingLocus_restrictedDegreeSection
    (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) (n : ℕ) (f : 𝒮 (n * C.degree)) :
    Stacks.Ample.nonvanishingLocus (restrictedTwist 𝒮 Y ((n * C.degree : ℕ) : ℤ))
        (restrictedDegreeSection 𝒮 Y (n * C.degree) f) =
      ((Y.ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) : Y.toScheme.Opens) :
        Set Y.toScheme) := by
  refine Eq.trans (Stacks.NonvanishingPullback.preimage_nonvanishingLocus Y.ι
    (twistingSheaf 𝒮 ((n * C.degree : ℕ) : ℤ)) (degreeSection 𝒮 (n * C.degree) f)).symm ?_
  refine Set.ext fun z => ?_
  exact mem_nonvanishingLocus_degreeSection_iff' 𝒮 C.degree n f
    (le_whereInvertible 𝒮 Y C z.2)

/-! ### Stacks Tag 01MW (6) and (7) -/

/-- A `d`-th power of a product of homogeneous elements of degrees `i` and `d` is homogeneous of
degree `(d + i)d`, a multiple of `d`. -/
private theorem pow_mem_graded_mul (d i : ℕ) {a : S} (ha : a ∈ 𝒮 (i + d)) :
    a ^ d ∈ 𝒮 ((d + i) * d) := by
  have h := SetLike.pow_mem_graded (A := 𝒮) d ha
  rwa [show d • (i + d) = (d + i) * d from by rw [smul_eq_mul]; ring] at h

/-- **Stacks Tag 01MW (7).** Let `Y` be an open of `Proj(S)` admitting a finite cover by standard
opens defined by homogeneous elements of one common positive degree `d`. Then the affine opens
among the nonvanishing loci `Y_s`, for `s` a global section of `𝒪_Y(nd)` with `n ≥ 1`, form a
basis for the topology of `Y`. -/
theorem isBasis_affineNonvanishing_restrictedTwist
    (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) :
    Opens.IsBasis {V : Y.toScheme.Opens | ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(restrictedTwist 𝒮 Y ((n * C.degree : ℕ) : ℤ), ⊤),
        IsAffineOpen V ∧ (V : Set Y.toScheme) =
          Stacks.Ample.nonvanishingLocus
            (restrictedTwist 𝒮 Y ((n * C.degree : ℕ) : ℤ)) s} := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hxV
  have hd : 0 < C.degree := C.degree_pos
  obtain ⟨D₀, hD₀, hxr, hrV⟩ :=
    Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒮)
      (show Y.ι.base x ∈ Y.ι ''ᵁ V from ⟨x, hxV, rfl⟩)
  obtain ⟨r, rfl⟩ := hD₀
  rw [AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj] at hxr
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxr
  have hxcov : Y.ι.base x ∈
      ⨆ g ∈ C.sections, AlgebraicGeometry.Proj.basicOpen 𝒮 g ⊓ Y := by
    rw [C.iSup_basicOpen_inf_eq]
    exact x.2
  obtain ⟨g, hgcov⟩ := Opens.mem_iSup.mp hxcov
  obtain ⟨hg, hxg⟩ := Opens.mem_iSup.mp hgcov
  have hpdeg : GradedRing.proj 𝒮 i r ∈ 𝒮 i := by
    rw [GradedRing.proj_apply]
    exact SetLike.coe_mem _
  have hq : GradedRing.proj 𝒮 i r * g ∈ 𝒮 (i + C.degree) :=
    SetLike.mul_mem_graded hpdeg (C.sections_mem g hg)
  have hh : (GradedRing.proj 𝒮 i r * g) ^ C.degree ∈ 𝒮 ((C.degree + i) * C.degree) :=
    pow_mem_graded_mul 𝒮 C.degree i hq
  have hDeq : AlgebraicGeometry.Proj.basicOpen 𝒮 ((GradedRing.proj 𝒮 i r * g) ^ C.degree) =
      AlgebraicGeometry.Proj.basicOpen 𝒮 (GradedRing.proj 𝒮 i r) ⊓
        AlgebraicGeometry.Proj.basicOpen 𝒮 g := by
    rw [AlgebraicGeometry.Proj.basicOpen_pow _ _ _ hd, AlgebraicGeometry.Proj.basicOpen_mul]
  have hxD : Y.ι.base x ∈
      AlgebraicGeometry.Proj.basicOpen 𝒮 ((GradedRing.proj 𝒮 i r * g) ^ C.degree) := by
    rw [hDeq]
    exact ⟨hxi, hxg.1⟩
  have hDr : AlgebraicGeometry.Proj.basicOpen 𝒮 ((GradedRing.proj 𝒮 i r * g) ^ C.degree) ≤
      AlgebraicGeometry.Proj.basicOpen 𝒮 r := by
    rw [hDeq]
    refine inf_le_left.trans ?_
    calc AlgebraicGeometry.Proj.basicOpen 𝒮 (GradedRing.proj 𝒮 i r)
        ≤ ⨆ j : ℕ, AlgebraicGeometry.Proj.basicOpen 𝒮 (GradedRing.proj 𝒮 j r) :=
          le_iSup (fun j : ℕ => AlgebraicGeometry.Proj.basicOpen 𝒮 (GradedRing.proj 𝒮 j r)) i
      _ = AlgebraicGeometry.Proj.basicOpen 𝒮 r :=
          (AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj 𝒮 r).symm
  have hDV : AlgebraicGeometry.Proj.basicOpen 𝒮 ((GradedRing.proj 𝒮 i r * g) ^ C.degree) ≤
      Y.ι ''ᵁ V := hDr.trans hrV
  have hDY : AlgebraicGeometry.Proj.basicOpen 𝒮 ((GradedRing.proj 𝒮 i r * g) ^ C.degree) ≤ Y :=
    hDV.trans ((Y.ι.image_le_opensRange V).trans (Scheme.Opens.opensRange_ι Y).le)
  have hWaff : IsAffineOpen
      (Y.ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 ((GradedRing.proj 𝒮 i r * g) ^ C.degree)) := by
    refine (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 _ hh
      (Nat.mul_pos (by omega) hd)).preimage_of_isOpenImmersion Y.ι ?_
    rw [Scheme.Opens.opensRange_ι]
    exact hDY
  have hWV : Y.ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮
      ((GradedRing.proj 𝒮 i r * g) ^ C.degree) ≤ V :=
    (Y.ι.preimage_mono hDV).trans (Y.ι.preimage_image_eq V).le
  refine ⟨Y.ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮
      ((GradedRing.proj 𝒮 i r * g) ^ C.degree),
    ⟨C.degree + i, by omega,
      restrictedDegreeSection 𝒮 Y ((C.degree + i) * C.degree) ⟨_, hh⟩, hWaff, ?_⟩,
    hxD, hWV⟩
  exact (nonvanishingLocus_restrictedDegreeSection 𝒮 Y C (C.degree + i) ⟨_, hh⟩).symm

/-- **Stacks Tag 01MW (6).** Let `Y` be an open of `Proj(S)` admitting a finite cover by standard
opens defined by homogeneous elements of one common positive degree `d`. Then the nonvanishing
loci `Y_s`, for `s` a global section of `𝒪_Y(nd)` with `n ≥ 1`, form a basis for the topology of
`Y`. Those among them that are affine already do, by
`isBasis_affineNonvanishing_restrictedTwist`. -/
theorem isBasis_nonvanishing_restrictedTwist
    (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) :
    Opens.IsBasis {V : Y.toScheme.Opens | ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(restrictedTwist 𝒮 Y ((n * C.degree : ℕ) : ℤ), ⊤),
        (V : Set Y.toScheme) =
          Stacks.Ample.nonvanishingLocus
            (restrictedTwist 𝒮 Y ((n * C.degree : ℕ) : ℤ)) s} := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hxV
  obtain ⟨W, ⟨n, hn, s, -, hWeq⟩, hxW, hWV⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affineNonvanishing_restrictedTwist 𝒮 Y C) hxV
  exact ⟨W, ⟨n, hn, s, hWeq⟩, hxW, hWV⟩

/-! ### Stacks Tag 01MW for a quasi-compact open -/

/-- **Stacks Tag 01MW.** Let `S` be a graded ring, `X = Proj(S)` and `Y ⊆ X` a quasi-compact
open subscheme; write `𝒪_Y(n)` for the restriction of `𝒪_X(n)` to `Y`. Then there is an integer
`d ≥ 1` such that

1. `Y` is contained in the open `W_d` of Tag 01MU;
2. `𝒪_Y(dn)` is invertible for every `n : ℤ`;
3. every multiplication map `𝒪_Y(nd) ⊗_{𝒪_Y} 𝒪_Y(m) ⟶ 𝒪_Y(nd + m)` of Equation 01MO is an
   isomorphism;
4. every comparison map `M̃|_Y ⊗_{𝒪_Y} 𝒪_Y(nd) ⟶ M(nd)~|_Y` of Equation 01MQ is an
   isomorphism, for every graded `S`-module `M`;
5. for `f ∈ S_{nd}` with image `s ∈ Γ(Y, 𝒪_Y(nd))` the nonvanishing locus `Y_s` is
   `D₊(f) ∩ Y`;
6. the opens `Y_s`, for `s ∈ Γ(Y, 𝒪_Y(nd))` with `n ≥ 1`, form a basis for the topology of `Y`;
7. so do those among them which are affine.

The degree is the common degree of a finite standard-open cover of `Y`, which quasi-compactness
produces: `AlgebraicGeometry.Proj.commonDegreeCover`. Each clause is then the corresponding
result about such a cover, so all seven hold for that one degree. -/
@[stacks 01MW "degree_exists"]
theorem exists_degree_forall (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (hY : IsCompact (Y : Set (AlgebraicGeometry.Proj 𝒮))) :
    ∃ d : ℕ, 1 ≤ d ∧
      Y ≤ whereInvertible 𝒮 d ∧
      (∀ n : ℤ, SheafOfModules.IsInvertible Y.toScheme.presheaf Y.toScheme.ringCatSheaf.2
        ((Scheme.Modules.pullback Y.ι).obj (twistingSheaf 𝒮 ((d : ℤ) * n)))) ∧
      (∀ n m : ℤ, IsIso ((Scheme.Modules.restrictFunctor Y.ι).map
        (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m))) ∧
      (∀ (M : Type u) [AddCommGroup M] [Module S M] (τ : Type t) [SetLike τ M]
        [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
        [SetLike.GradedSMul 𝒮 𝒨] (n : ℤ),
          IsIso ((Scheme.Modules.restrictFunctor Y.ι).map
            (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n)))) ∧
      (∀ (n : ℕ) (f : 𝒮 (n * d)),
        Stacks.Ample.nonvanishingLocus (restrictedTwist 𝒮 Y ((n * d : ℕ) : ℤ))
            (restrictedDegreeSection 𝒮 Y (n * d) f) =
          ((Y.ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) : Y.toScheme.Opens) :
            Set Y.toScheme)) ∧
      Opens.IsBasis {V : Y.toScheme.Opens | ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : Γ(restrictedTwist 𝒮 Y ((n * d : ℕ) : ℤ), ⊤),
          (V : Set Y.toScheme) =
            Stacks.Ample.nonvanishingLocus (restrictedTwist 𝒮 Y ((n * d : ℕ) : ℤ)) s} ∧
      Opens.IsBasis {V : Y.toScheme.Opens | ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : Γ(restrictedTwist 𝒮 Y ((n * d : ℕ) : ℤ), ⊤),
          IsAffineOpen V ∧ (V : Set Y.toScheme) =
            Stacks.Ample.nonvanishingLocus (restrictedTwist 𝒮 Y ((n * d : ℕ) : ℤ)) s} :=
  let C := AlgebraicGeometry.Proj.commonDegreeCover 𝒮 Y hY
  ⟨C.degree, C.degree_pos,
    le_whereInvertible 𝒮 Y C,
    isInvertible_restrict_twistingSheaf_mul_degree 𝒮 Y C,
    fun n m => isIso_restrict_twistMultiplication_mul_degree 𝒮 Y C n m,
    fun _ _ _ _ _ _ 𝒨 _ _ n => isIso_restrict_moduleTwistMap_mul_degree 𝒮 𝒨 Y C n,
    fun n f => nonvanishingLocus_restrictedDegreeSection 𝒮 Y C n f,
    isBasis_nonvanishing_restrictedTwist 𝒮 Y C,
    isBasis_affineNonvanishing_restrictedTwist 𝒮 Y C⟩

end Proj

end Stacks.AlgebraicGeometry.CommonDegreeTwist

end
