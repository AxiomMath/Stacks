module

public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Quotient
public import StacksFrontier.AlgebraicGeometry.ProjQuotientFiniteCover.Basic

/-!
# The closed subscheme and the quotient cut out the same ideal sheaf, at a graded ring

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a graded ring — a family `𝒮 : ℕ → σ` of additive subgroups with
`[GradedRing 𝒮]`, *not* a graded algebra over a base ring — generated in degree one over `𝒮 0`
and admitting a finite family of degree-one elements whose standard opens cover `Proj 𝒮`, and let
`i : Z ⟶ Proj 𝒮` be a closed immersion. This file proves that `Z` and `Proj (𝒮 / I)` cut out the
same ideal sheaf of `Proj 𝒮`, for `I` **any** homogeneous ideal whose underlying ideal is the Tag
0BXK ideal of equations of `Z`:

    i.ker = (Proj.map (quotientMk I) hψ).ker .

## Why this restatement exists

`Stacks.ProjQuotientFiniteCover.ker_eq_ker_ambientHom_of_cover` is the same assertion, but it
lives in a `variable` block `{R S : Type u} [Algebra R S] (𝒮 : ℕ → Submodule R S)
[GradedAlgebra 𝒮]`, because `Stacks.ClosedSubschemeProjQuotient.ambientHom` and the chain
reaching it are stated there. The graded ring that a relative `Proj` presents on a chart is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading`, which is
`ℕ → AddSubgroup (𝒜.sectionRing U)`: a `GradedRing`, with no base ring to be a `GradedAlgebra`
over, since the degree-zero piece of a `SheafGradedAlgebra` is an arbitrary quasi-coherent
module. So the chain is restated here.

Nothing is reproved. The only thing the `GradedAlgebra` hypothesis was buying is
`Stacks.ProjQuotientChartIdeal.ambientHom_eq_projMap`, which identifies the *glued* morphism
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` with Mathlib's
`AlgebraicGeometry.Proj.map`; stating the conclusion at `Proj.map` of
`Stacks.HomogeneousIdeal.quotientMk` from the start removes the need for it, and every remaining
input — `Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover`,
`Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff`,
`Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff`,
`Stacks.HomogeneousIdeal.quotientMk` and
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme` — is already stated at
`[GradedRing 𝒮]`.

The ideal is taken as an argument together with the equation `I.toIdeal = idealOfClosedSubscheme`
rather than being `Stacks.ClosedSubschemeProjQuotient.homogeneousIdealOfClosedSubscheme`, because
the consumer's ideal is `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionIdeal`, whose
equality with the ideal of equations is a theorem and not a definition; rewriting the ideal inside
the type `Proj (quotientGrading I)` is then not needed.

## Main results

* `Stacks.ProjQuotientFiniteCover.ker_le_ker_of_app_awayMk`: the locality step at a graded ring —
  two kernel ideal sheaves on `Proj 𝒮` are compared on the standard charts, against the
  homogeneous fractions.
* `Stacks.ProjQuotientFiniteCover.awayToSection_mem_ker_app_projMap_quotientMk_iff`: the chart
  kernel of `Proj (𝒮 / I) ⟶ Proj 𝒮` at a graded ring: `a / f ^ n` dies exactly when some
  `f ^ k · a` lies in `I`.
* `Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover`: **the equality of ideal
  sheaves.**

## References

* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme
open Stacks.HomogeneousIdeal

universe u

namespace Stacks.ProjQuotientFiniteCover

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### Locality on the standard charts -/

/-- A standard open `D₊(f)` of `Proj 𝒮`, for `f` homogeneous of positive degree, packaged as an
affine open. This is `Stacks.ProjQuotientSaturationKer.standardAffineChart` at a graded ring. -/
def standardAffineChart {m : ℕ} (f : S) (hf : f ∈ 𝒮 m) (hm : 0 < m) :
    (AlgebraicGeometry.Proj 𝒮).affineOpens :=
  ⟨AlgebraicGeometry.Proj.basicOpen 𝒮 f,
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 f hf hm⟩

/-- The underlying open of `standardAffineChart 𝒮 f hf hm` is `D₊(f)`. -/
@[simp]
theorem standardAffineChart_coe {m : ℕ} (f : S) (hf : f ∈ 𝒮 m) (hm : 0 < m) :
    (standardAffineChart 𝒮 f hf hm).1 = AlgebraicGeometry.Proj.basicOpen 𝒮 f := rfl

/-- **Comparing two kernel ideal sheaves on the standard charts, at a graded ring.** For
quasi-compact morphisms `p, q` to `Proj 𝒮` and homogeneous `f k` of positive degrees whose
standard opens cover `Proj 𝒮`, it is enough to compare the two maps on the degree-zero fractions
over each `D₊(f k)`.

This is `Stacks.ProjQuotientChartIdeal.ker_le_ker_of_app_awayMk` with the `GradedAlgebra`
hypothesis dropped; the proof is unchanged, since `AlgebraicGeometry.Scheme.Hom.ker_apply`,
`AlgebraicGeometry.Proj.isAffineOpen_basicOpen` and
`AlgebraicGeometry.Proj.basicOpenIsoAway` are all available at a graded ring. -/
theorem ker_le_ker_of_app_awayMk {Z W : Scheme.{u}} (p : Z ⟶ Proj 𝒮) (q : W ⟶ Proj 𝒮)
    [QuasiCompact p] [QuasiCompact q] {ι : Type*} (f : ι → S) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒮 (d k)) (hd : ∀ k, 0 < d k)
    (hcover : ⨆ k, Proj.basicOpen 𝒮 (f k) = ⊤)
    (H : ∀ (k : ι) (z : Away 𝒮 (f k)),
      (p.app (Proj.basicOpen 𝒮 (f k))).hom ((Proj.awayToSection 𝒮 (f k)).hom z) = 0 →
      (q.app (Proj.basicOpen 𝒮 (f k))).hom ((Proj.awayToSection 𝒮 (f k)).hom z) = 0) :
    p.ker ≤ q.ker := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun k => standardAffineChart 𝒮 (f k) (hf k) (hd k)) hcover fun k => ?_
  rw [Scheme.Hom.ker_apply p _, Scheme.Hom.ker_apply q _]
  have hiso := Stacks.ProjQuotientChartIdeal.isIso_awayToSection (hf k) (hd k)
  have hsurj : Function.Surjective (Proj.awayToSection 𝒮 (f k)).hom :=
    (ConcreteCategory.bijective_of_isIso (Proj.awayToSection 𝒮 (f k))).2
  intro x hx
  obtain ⟨z, rfl⟩ := hsurj x
  exact RingHom.mem_ker.2 (H k z (RingHom.mem_ker.1 hx))

/-! ### The chart kernel of the quotient -/

/-- **The chart kernel of `Proj (𝒮 / I) ⟶ Proj 𝒮`, at a graded ring.** For `f ∈ 𝒮 m` with
`m > 0`, the degree-zero fraction `a / f ^ n` over `D₊(f)` dies on `Proj (𝒮 / I)` exactly when
`f ^ k · a` lies in `I` for some `k`.

This is `Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_ambientHom_iff` with
`Stacks.ClosedSubschemeProjQuotient.ambientHom` replaced by Mathlib's
`AlgebraicGeometry.Proj.map` at the graded quotient map, which is what removes the
`GradedAlgebra` hypothesis: the identification of the two morphisms is no longer needed. -/
theorem awayToSection_mem_ker_app_projMap_quotientMk_iff (I : HomogeneousIdeal 𝒮)
    (hψ : HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      (HomogeneousIdeal.irrelevant 𝒮).map (quotientMk I))
    {m : ℕ} {f : S} (hf : f ∈ 𝒮 m) (hm : 0 < m) (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • m)) :
    (Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n a ha) ∈
        RingHom.ker ((Proj.map (quotientMk I) hψ).app (Proj.basicOpen 𝒮 f)).hom ↔
      ∃ k : ℕ, f ^ k * a ∈ I.toIdeal := by
  rw [Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff (quotientMk I) hψ hf hm,
    Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff]
  exact exists_congr fun k => Ideal.Quotient.eq_zero_iff_mem

/-! ### The equality of ideal sheaves -/

/-- **`Z` and `Proj (𝒮 / I)` cut out the same ideal sheaf of `Proj 𝒮`**, for a graded ring
generated in degree one admitting a finite family of degree-one elements whose standard opens
cover `Proj 𝒮`, and for `I` any homogeneous ideal whose underlying ideal is the Tag 0BXK ideal of
equations of `Z`. No Noetherian hypothesis, and no `GradedAlgebra` structure, is used.

Both inclusions come from one chart statement: over `D₊(g k)` a degree-zero fraction dies on `Z`
exactly when a power-of-`g k` multiple of its numerator is an equation for `Z`
(`Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover`), and exactly when that
numerator has such a multiple in `I`
(`Stacks.ProjQuotientFiniteCover.awayToSection_mem_ker_app_projMap_quotientMk_iff`); the two
right-hand sides agree by hypothesis. -/
theorem ker_eq_ker_projMap_quotientMk_of_cover
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {ι : Type*} [Finite ι] (g : ι → S) (hg : ∀ j, g j ∈ 𝒮 1)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i]
    (I : HomogeneousIdeal 𝒮) (hI : I.toIdeal = idealOfClosedSubscheme 𝒮 i)
    (hψ : HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      (HomogeneousIdeal.irrelevant 𝒮).map (quotientMk I)) :
    i.ker = (Proj.map (quotientMk I) hψ).ker := by
  have : IsClosedImmersion (Proj.map (quotientMk I) hψ) :=
    Proj.isClosedImmersion_map_of_surjective hψ (surjective_quotientMk I)
  have key : ∀ (k : ι) (z : Away 𝒮 (g k)),
      ((i.app (Proj.basicOpen 𝒮 (g k))).hom ((Proj.awayToSection 𝒮 (g k)).hom z) = 0 ↔
        ((Proj.map (quotientMk I) hψ).app (Proj.basicOpen 𝒮 (g k))).hom
          ((Proj.awayToSection 𝒮 (g k)).hom z) = 0) := by
    intro k z
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (hg k) z
    have h2 := awayToSection_mem_ker_app_projMap_quotientMk_iff 𝒮 I hψ (hg k) Nat.one_pos n a ha
    rw [RingHom.mem_ker] at h2
    have hEx : (∃ j : ℕ, g k ^ j * a ∈ I.toIdeal) ↔
        ∃ j : ℕ, g k ^ j * a ∈ idealOfClosedSubscheme 𝒮 i := by rw [hI]
    exact (app_awayMk_eq_zero_iff_of_cover 𝒮 hgen g hg hcov (hg k) i n a ha).trans
      (h2.trans hEx).symm
  exact le_antisymm
    (ker_le_ker_of_app_awayMk 𝒮 i _ g (fun _ => 1) hg (fun _ => Nat.one_pos) hcov
      fun k z => (key k z).1)
    (ker_le_ker_of_app_awayMk 𝒮 _ i g (fun _ => 1) hg (fun _ => Nat.one_pos) hcov
      fun k z => (key k z).2)

end Stacks.ProjQuotientFiniteCover

end
