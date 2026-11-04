module

public import StacksFrontier.AlgebraicGeometry.Segre.Morphism
public import StacksFrontier.AlgebraicGeometry.SectionDivision.Basic

/-!
# The ratio of two canonical sections of `𝒪(1)` is the homogeneous fraction `g / f`

Let `𝒮` be a nonnegatively graded ring and let `f, g ∈ 𝒮 1`. Each of them determines a global
section `f / 1`, `g / 1` of `𝒪_{Proj 𝒮}(1)` (`Stacks.ProjTwistSection.homogeneousSection`), and
`f / 1` is nonvanishing on the standard open `D₊(f)`
(`Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection`). Over `D₊(f)` there
are two notions of the ratio of the two sections:

* the sheaf-theoretic one, `Stacks.SheafOfModules.divBySection` of [Stacks, Tag 01N8] — the unique
  function on `D₊(f)` whose product with `f / 1` is `g / 1`;
* the algebraic one, the degree-zero homogeneous fraction `g / f` of
  `HomogeneousLocalization.Away 𝒮 f`, carried into `Γ(Proj 𝒮, D₊(f))` by
  `AlgebraicGeometry.Proj.awayToSection`.

They agree: this is `divBySection_homogeneousSection`. Consequently, over the integral model
`ℙⁿ_ℤ` the ring `Γ(ℙⁿ_ℤ, D₊(Xᵢ))` is generated as a ring by the `n + 1` sheaf-theoretic ratios
`X_a / Xᵢ`.

## Main results

* `Stacks.ProjTwistSection.divBySection_homogeneousSection`: **`(g / 1) / (f / 1) = g / f`** on
  `D₊(f)`, for `f, g ∈ 𝒮 1`.
* `Stacks.ProjectiveChart.subring_eq_top_of_ratio_mem` and
  `Stacks.ProjectiveChart.closure_range_ratio_eq_top`: **the `i`-th chart ring of `ℙⁿ_ℤ` is
  generated as a ring by the ratios `X_a / Xᵢ`**.
* `Stacks.ProjTwistSection.sectionsSubring_eq_top_of_divBySection_mem`: **`Γ(ℙⁿ_ℤ, D₊(Xᵢ))` is
  generated as a ring by the sheaf-theoretic ratios `X_a / Xᵢ`.**

## Implementation notes

Only degree one is treated: at `d = 1` the twist degree `1 * ((1 : ℕ) : ℤ)` and `((1 : ℕ) : ℤ)`
agree after evaluation, so no transport along `one_mul` is needed.

No `@[stacks ...]` attribute is attached. Tag 01N8 is the construction of the morphism to
projective space from generating sections; the ratio computation is a step inside its proof and of
the proof of Tag 01NE, and the generation statement over `ℙⁿ_ℤ` is a lemma of the Segre and
Tag 01WD arguments rather than the statement of any tag.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjTwistSection

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
    (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The ideal underlying a point of `ProjectiveSpectrum.top 𝒮` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- **On `D₊(f)` the ratio of the canonical sections of `𝒪(1)` attached to two degree-one
elements `g` and `f` is the homogeneous fraction `g / f`.** The sheaf-theoretic quotient of
[Stacks, Tag 01N8] and the degree-zero element `g / f` of `HomogeneousLocalization.Away 𝒮 f`,
transported by `AlgebraicGeometry.Proj.awayToSection`, are the same section of the structure
sheaf. -/
theorem divBySection_homogeneousSection
    [Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace).property (twistingModule 𝒮 1)]
    (f g : S) (hf : f ∈ 𝒮 1) (hg : g ∈ 𝒮 1) :
    Stacks.SheafOfModules.divBySection (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
        (twistingModule 𝒮 1) (homogeneousSection 𝒮 f hf)
        (basicOpen_le_nonvanishingOpen_homogeneousSection 𝒮 f hf)
        ((homogeneousSection 𝒮 g hg).eval (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
      = (AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom
          (HomogeneousLocalization.Away.isLocalizationElem hf hg) := by
  refine Stacks.SheafOfModules.divBySection_eq_of_smul_eq _ _ _ ?_
  apply Subtype.ext
  funext x
  show Localization.mk (g ^ 1)
        ⟨f ^ 1, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 1⟩ *
      Localization.mk f (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    = Localization.mk g (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

end Stacks.ProjTwistSection

namespace Stacks.ProjectiveChart

/-- The image of the degree-zero part of `ℤ[X₀, …, Xₙ]` in the `i`-th chart ring lies in every
subring of the chart ring. -/
theorem algebraMap_deg0_mem_subring {n : ℕ} (i : Fin (n + 1))
    (T : Subring (ChartRing (ULift.{u} ℤ) n i)) (r : Deg0 (ULift.{u} ℤ) n) :
    algebraMap (Deg0 (ULift.{u} ℤ) n) (ChartRing (ULift.{u} ℤ) n i) r ∈ T := by
  have hr : r = (((degreeZeroEquiv (ULift.{u} ℤ) n r).down : ℤ) : Deg0 (ULift.{u} ℤ) n) :=
    (degreeZeroEquiv (ULift.{u} ℤ) n).injective
      ((ULift.up_intCast _).symm.trans (map_intCast _ _).symm)
  rw [hr, map_intCast]
  exact intCast_mem T _

/-- A subring of the `i`-th chart ring of `ℙⁿ_ℤ` containing the `n + 1` ratios `X_a / Xᵢ` is the
whole ring. -/
theorem subring_eq_top_of_ratio_mem {n : ℕ} (i : Fin (n + 1))
    (T : Subring (ChartRing (ULift.{u} ℤ) n i))
    (h : ∀ a : Fin (n + 1), ratio (ULift.{u} ℤ) i a ∈ T) : T = ⊤ := by
  refine top_unique ?_
  rintro y -
  obtain ⟨p, rfl⟩ := chartHom_surjective (ULift.{u} ℤ) i y
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [show chartHom (ULift.{u} ℤ) i (MvPolynomial.C r)
          = algebraMap (Deg0 (ULift.{u} ℤ) n) (ChartRing (ULift.{u} ℤ) n i) r from
        MvPolynomial.aeval_C _ _]
      exact algebraMap_deg0_mem_subring i T r
  | add p q hp hq =>
      rw [map_add]
      exact T.add_mem hp hq
  | mul_X p j hp =>
      rw [map_mul, show chartHom (ULift.{u} ℤ) i (MvPolynomial.X j)
          = ratio (ULift.{u} ℤ) i (i.succAbove j) from MvPolynomial.aeval_X _ _]
      exact T.mul_mem hp (h (i.succAbove j))

/-- The ratios `X_a / Xᵢ` generate the `i`-th chart ring of `ℙⁿ_ℤ` as a ring. -/
theorem closure_range_ratio_eq_top {n : ℕ} (i : Fin (n + 1)) :
    Subring.closure (Set.range (ratio (ULift.{u} ℤ) i)) = ⊤ :=
  subring_eq_top_of_ratio_mem i _ fun a => Subring.subset_closure ⟨a, rfl⟩

end Stacks.ProjectiveChart

namespace Stacks.ProjTwistSection

open AlgebraicGeometry.Segre Stacks.ProjectiveChart

/-- The twisting module `𝒪(1)` on `Proj (coordinateGrading n)`, that is on `ℙⁿ_ℤ`, is
invertible. -/
local instance isInvertible_coordinateTwistingModule (n : ℕ) :
    Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).toRingedSpace).property
      (twistingModule (coordinateGrading.{u} n) 1) :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf _
    (adjoin_coordinateGrading_one_eq_top.{u} n) 1

/-- The ring isomorphism `(ℤ[X₀, …, Xₙ]_{(Xᵢ)})₀ ≃+* Γ(ℙⁿ_ℤ, D₊(Xᵢ))` induced by
`AlgebraicGeometry.Proj.basicOpenIsoAway`. -/
noncomputable def chartSectionsEquiv (n : ℕ) (i : Fin (n + 1)) :
    ChartRing (ULift.{u} ℤ) n i ≃+*
      Γ(AlgebraicGeometry.Proj (coordinateGrading.{u} n),
        AlgebraicGeometry.Proj.basicOpen (coordinateGrading.{u} n) (MvPolynomial.X i)) :=
  (AlgebraicGeometry.Proj.basicOpenIsoAway (coordinateGrading.{u} n) (MvPolynomial.X i)
    (X_mem_degree_one _ i) Nat.one_pos).commRingCatIsoToRingEquiv

/-- `chartSectionsEquiv n i` acts on elements as `AlgebraicGeometry.Proj.awayToSection`. -/
theorem chartSectionsEquiv_apply (n : ℕ) (i : Fin (n + 1)) (y : ChartRing (ULift.{u} ℤ) n i) :
    chartSectionsEquiv.{u} n i y
      = (AlgebraicGeometry.Proj.awayToSection (coordinateGrading.{u} n)
          (MvPolynomial.X i)).hom y := rfl

/-- **`Γ(ℙⁿ_ℤ, D₊(Xᵢ))` is generated as a ring by the `n + 1` sheaf-theoretic ratios
`X_a / Xᵢ`**, the quotients of [Stacks, Tag 01N8] of the canonical sections of `𝒪(1)` attached to
the homogeneous coordinates. -/
theorem sectionsSubring_eq_top_of_divBySection_mem (n : ℕ) (i : Fin (n + 1))
    (T : Subring Γ(AlgebraicGeometry.Proj (coordinateGrading.{u} n),
      AlgebraicGeometry.Proj.basicOpen (coordinateGrading.{u} n) (MvPolynomial.X i)))
    (h : ∀ a : Fin (n + 1),
      Stacks.SheafOfModules.divBySection
          (X := (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).toRingedSpace)
          (twistingModule (coordinateGrading.{u} n) 1)
          (homogeneousSection (coordinateGrading.{u} n) (MvPolynomial.X i)
            (X_mem_degree_one _ i))
          (basicOpen_le_nonvanishingOpen_homogeneousSection (coordinateGrading.{u} n)
            (MvPolynomial.X i) (X_mem_degree_one _ i))
          ((homogeneousSection (coordinateGrading.{u} n) (MvPolynomial.X a)
            (X_mem_degree_one _ a)).eval
              (op (ProjectiveSpectrum.basicOpen (coordinateGrading.{u} n)
                (MvPolynomial.X i)))) ∈ T) :
    T = ⊤ := by
  have hcomap : T.comap (chartSectionsEquiv.{u} n i).toRingHom = ⊤ := by
    refine subring_eq_top_of_ratio_mem i _ fun a => ?_
    show chartSectionsEquiv.{u} n i (ratio (ULift.{u} ℤ) i a) ∈ T
    rw [chartSectionsEquiv_apply, ratio,
      ← divBySection_homogeneousSection (coordinateGrading.{u} n) (MvPolynomial.X i)
        (MvPolynomial.X a) (X_mem_degree_one _ i) (X_mem_degree_one _ a)]
    exact h a
  refine top_unique fun y _ => ?_
  have hy : (chartSectionsEquiv.{u} n i).symm y
      ∈ T.comap (chartSectionsEquiv.{u} n i).toRingHom := hcomap.ge trivial
  simpa using hy

end Stacks.ProjTwistSection

end
