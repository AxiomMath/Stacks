module

public import StacksFrontier.AlgebraicGeometry.ProjQuotientChartIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Quotient
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Localization
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.IdealOfClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenCover
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-!
# A closed subscheme of `Proj 𝒮` is the `Proj` of the quotient, at an `AddSubgroup`-valued grading

`StacksFrontier/AlgebraicGeometry/ClosedSubschemeProjQuotient/Saturation.lean` proves that a closed
immersion `i : Z ⟶ Proj 𝒮` into a quasi-compact absolute `Proj` has the same kernel ideal sheaf
as the canonical morphism out of `Proj` of the quotient by its homogeneous ideal of equations —
but only for a `Submodule`-valued grading `𝒮 : ℕ → Submodule R S` with `[GradedAlgebra 𝒮]`,
because the quotient it uses, `Stacks.RingTheory.HomogeneousQuotient.quotientGrading`, is stated
there.

The charts of a *relative* `Proj` are graded by `AddSubgroup`:
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading` takes values in
`AddSubgroup (A.sectionRing U)`. The parallel `AddSubgroup`-valued graded quotient is
`Stacks.HomogeneousIdeal.quotientGrading`, and it is what
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionAmbientHom` — the chart of
`Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` — is built from. This file carries the statement across, by reproving
it rather than by transporting: **every input is already stated at an `AddSubgroupClass`-valued
grading**, and only the two assembly steps of `./Basic.lean` and of
`StacksFrontier/AlgebraicGeometry/ClosedSubschemeProjQuotient/Saturation.lean` were written at the
`Submodule`-valued one.

Nothing here is new mathematics. The one addition on top of `./Basic.lean` is that the
conclusion is stated for an *arbitrary* homogeneous ideal equal to the ideal of equations, rather
than for that ideal packaged with its own homogeneity proof: a consumer arrives with a
homogeneous ideal built for other reasons — for the relative `Proj`, the ideal of local sections
lying in a graded ideal of `𝒜` — and has to prove it *equal* to the ideal of equations, not
*be* it.

## Main results

* `Stacks.ProjChartKerQuotient.exists_equalDegree_finite_cover`: a quasi-compact `Proj 𝒮` is
  covered by finitely many standard opens of homogeneous elements of one common positive degree.
* `Stacks.ProjChartKerQuotient.app_awayMk_eq_zero_iff`: **the chart comparison** — the fraction
  `a / f ^ n` dies on `Z` exactly when some `f ^ k · a` is an equation for `Z`.
* `Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk`: **the identification** — `Z` and
  `Proj (𝒮 ⧸ I)` cut out the same ideal sheaf of `Proj 𝒮`, for any homogeneous ideal `I` whose
  underlying ideal is the ideal of equations of `Z`.

## Implementation notes

The ideal of equations has two `rfl`-equal spellings,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme` — the one the chart material
is stated for — and `Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme`, the
one carrying the degreewise membership criterion a consumer needs. The statements below use the
second, and `idealOfClosedSubscheme_eq` records that nothing is transported.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)

## Not done here

No `@[stacks]` attribute is attached. Tag 0801 is about a relative `Proj` over an arbitrary base;
what is below is its absolute case, already registered at
`Stacks.ClosedSubschemeProjQuotient.projQuotientIso`, restated at the grading the charts of a
relative `Proj` carry.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite HomogeneousLocalization
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.HomogeneousIdeal

namespace Stacks.ProjChartKerQuotient

universe u

variable {S σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ)
  [GradedRing 𝒮]

/-- The two `rfl`-equal spellings of the homogeneous ideal of equations of a closed subscheme of
`Proj 𝒮` agree: they are the same span of the same set of homogeneous elements. -/
theorem idealOfClosedSubscheme_eq {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    idealOfClosedSubscheme 𝒮 i =
      Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme 𝒮 i :=
  rfl

/-! ### The covering family -/

/-- **A quasi-compact `Proj 𝒮` is covered by finitely many standard opens of homogeneous elements
of one common positive degree.** This is
`AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover` at the open `⊤`, with the
covering family re-indexed by the `Finset` it produces. -/
theorem exists_equalDegree_finite_cover [CompactSpace (AlgebraicGeometry.Proj 𝒮)] :
    ∃ (D : ℕ) (t : Finset S), 0 < D ∧ (∀ g ∈ t, g ∈ 𝒮 D) ∧
      ⨆ j : {x : S // x ∈ t}, Proj.basicOpen 𝒮 (j : S) = ⊤ := by
  obtain ⟨D, hD, t, ht, hcov⟩ :=
    _root_.AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover 𝒮 ⊤
      (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  refine ⟨D, t, hD, ht, ?_⟩
  have hrw : ⨆ j : {x : S // x ∈ t}, Proj.basicOpen 𝒮 (j : S)
      = ⨆ g ∈ t, Proj.basicOpen 𝒮 g ⊓ (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) := by
    simp only [inf_top_eq]
    rw [iSup_subtype']
  rw [hrw, ← hcov]

/-! ### The chart comparison -/

/-- **The chart comparison.** Let `i : Z ⟶ Proj 𝒮` be a closed immersion, let `fam` be a finite
family of homogeneous elements of one positive degree `d` whose standard opens cover `Proj 𝒮`,
and let `f` be homogeneous of that same degree `d`. A degree-zero fraction `a / f ^ n` over
`D₊(f)`, with `a` homogeneous of degree `n · d`, is carried to zero by `i` exactly when some
`f ^ k · a` lies in the homogeneous ideal of equations of `Z`.

The forward implication is the saturation step and the backward one the vanishing of the twisted
section of `f ^ k · a` on `Z`. -/
theorem app_awayMk_eq_zero_iff {d : ℕ} (hd : 0 < d) {ι : Type*} [Finite ι] (fam : ι → S)
    (hfam : ∀ j, fam j ∈ 𝒮 d) (hcov : ⨆ j, Proj.basicOpen 𝒮 (fam j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] {f : S} (hf : f ∈ 𝒮 d)
    (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • d)) :
    (i.app (Proj.basicOpen 𝒮 f)).hom
        ((Proj.awayToSection 𝒮 f).hom (HomogeneousLocalization.Away.mk 𝒮 hf n a ha)) = 0 ↔
      ∃ k : ℕ, f ^ k * a ∈
        Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme 𝒮 i := by
  refine ⟨fun h => exists_pow_mul_mem_idealOfClosedSubscheme 𝒮 hd fam hfam hcov hf i n
    ⟨a, ha⟩ (RingHom.mem_ker.mpr h), ?_⟩
  rintro ⟨k, hk⟩
  have hmem : f ^ k * a ∈ 𝒮 ((k + n) • d) := by
    have hp := SetLike.mul_mem_graded (SetLike.pow_mem_graded (A := 𝒮) k hf) ha
    rwa [← add_smul] at hp
  have := algebraicGeometry_isInvertible_twistingSheaf_of_cover 𝒮 fam d hfam hcov (k + n)
  have h1 := chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme 𝒮 hf hd i
    (k + n) ⟨f ^ k * a, hmem⟩ hk
  rw [chartFraction_pow_mul_left 𝒮 hf k n ⟨a, ha⟩ ⟨f ^ k * a, hmem⟩ rfl] at h1
  exact RingHom.mem_ker.mp h1

/-! ### The identification -/

/-- The kernel of the quotient map of a graded ring by a homogeneous ideal is that ideal. -/
theorem mem_ker_quotientMk_iff (I : HomogeneousIdeal 𝒮) (a : S) :
    a ∈ RingHom.ker ((quotientMk I : 𝒮 →+*ᵍ quotientGrading I) : S →+* S ⧸ I.toIdeal) ↔
      a ∈ I.toIdeal := by
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- **`Z` and `Proj (𝒮 ⧸ I)` cut out the same ideal sheaf of `Proj 𝒮`**, for `I` any homogeneous
ideal whose underlying ideal is the ideal of equations of `Z` and `Proj 𝒮` quasi-compact.

This is the absolute case of Tag 0801 at an `AddSubgroup`-valued grading. The two kernel ideal
sheaves are compared on the standard opens of a finite cover by elements of one common positive
degree (`Stacks.ProjQuotientChartIdeal.ker_le_ker_of_app_awayMk`), where the chart comparison
above computes the one belonging to `Z` and
`Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff` with
`Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff` computes the other. -/
theorem ker_eq_ker_projMap_quotientMk [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] (I : HomogeneousIdeal 𝒮)
    (hI : I.toIdeal =
      Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme 𝒮 i)
    (hq : HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      (HomogeneousIdeal.irrelevant 𝒮).map (quotientMk I)) :
    i.ker = (Proj.map (quotientMk I) hq).ker := by
  have : IsClosedImmersion (Proj.map (quotientMk I) hq) :=
    AlgebraicGeometry.Proj.isClosedImmersion_map_quotientMk I
  obtain ⟨D, t, hD, ht, hcov⟩ := exists_equalDegree_finite_cover 𝒮
  have hfam : ∀ j : {x : S // x ∈ t}, (j : S) ∈ 𝒮 D := fun j => ht _ j.2
  have key : ∀ (k : {x : S // x ∈ t}) (z : Away 𝒮 (k : S)),
      (i.app (Proj.basicOpen 𝒮 (k : S))).hom ((Proj.awayToSection 𝒮 (k : S)).hom z) = 0 ↔
        ((Proj.map (quotientMk I) hq).app (Proj.basicOpen 𝒮 (k : S))).hom
          ((Proj.awayToSection 𝒮 (k : S)).hom z) = 0 := by
    intro k z
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (hfam k) z
    rw [app_awayMk_eq_zero_iff 𝒮 hD (fun j : {x : S // x ∈ t} => (j : S)) hfam hcov i
      (hfam k) n a ha, ← RingHom.mem_ker,
      Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff
        (quotientMk I) hq (hfam k) hD,
      Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff]
    exact exists_congr fun j =>
      by rw [mem_ker_quotientMk_iff 𝒮 I, hI]
  refine le_antisymm ?_ ?_ <;>
    refine Stacks.ProjQuotientChartIdeal.ker_le_ker_of_app_awayMk 𝒮 _ _
      (fun j : {x : S // x ∈ t} => (j : S)) (fun _ => D) hfam (fun _ => hD) hcov fun k z => ?_
  exacts [(key k z).1, (key k z).2]

end Stacks.ProjChartKerQuotient

end
