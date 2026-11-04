module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistGlobalMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedLocalMap

/-!
# Restriction between standard opens, for the punctured cone over a homogeneous spectrum

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, `π : L = Proj B ⟶ P` the cone of the
truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` and `U ⊆ L` the punctured cone. For `f`, `g`
homogeneous of positive degree with `D₊(g) ⊆ D₊(f)`, comparing the punctured degreewise inclusions
`Γ(D₊(f), 𝒪_P(m)) → (B[1/σ f · ψ f])₀` and `Γ(D₊(g), 𝒪_P(m)) → (B[1/σ g · ψ g])₀` of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeTwistPuncturedLocalMap.lean` across that
inclusion of opens needs the two statements proved here: that the charts of `U` are nested the
way the standard opens of `P` are, and that the comparison maps
`Stacks.Truncation.puncturedToLocalization` intertwine the degree-zero restriction map of `B` with
the restriction map of `A`.

This is the punctured analogue of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeTwistLocalRestriction.lean`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.basicOpen_sigmaMulPsi_le_of_basicOpen_le`: **the chart
  of `U` over `D₊(g)` is contained in the chart over `D₊(f)`**, both being the part of `U` lying
  over the respective standard open.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistAwayHom_degreeZeroRingMap`: **the
  punctured degreewise inclusion commutes with restriction between two standard opens**, read in
  the degree-zero localizations of the truncation algebra.
* `Stacks.Truncation.puncturedToLocalization_degreeZeroRingMap_le`: **the comparison maps
  `(B[1/σ f · ψ f])₀ → A[1/f]` commute with the restriction maps of degree-zero
  localizations**, the one of `B` attached to `D₊(σ g · ψ g) ⊆ D₊(σ f · ψ f)` on the source and
  the one of `A` attached to `D₊(g) ⊆ D₊(f)` on the target.

## Implementation notes

The nesting of the charts is read off `openUInL_inf_basicOpen`: each chart is `U ⊓ D₊(ψ ·)`, and
`ψ` carries the inclusion `D₊(g) ⊆ D₊(f)` to `D₊(ψ g) ⊆ D₊(ψ f)` by
`Stacks.AlgebraicGeometry.ProjConeTwist.basicOpen_psi_le`.

The restriction compatibility is the uniqueness part of the universal property of
`B[1/σ f · ψ f]`, exactly as in `Stacks.Truncation.awayToLocalization_degreeZeroRingMap`: both
composites are ring maps out of that localization, so `IsLocalization.ringHom_ext` reduces the
identity to the image of `B`, where each side is the structure map of `A[1/g]` applied to the
degree-forgetting image of the element. The only change from the nonnegative case is the element
inverted and the witness that it becomes a unit, which is
`Stacks.Truncation.comp_sigmaMulPsi_mul_awayFrac` and the fraction `1 / f ²`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.Truncation

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}

/-- The map `A[1/σ f · ψ f] → A[1/f]` forgetting the degree, which exists since `σ f · ψ f`
divides `f ²` after forgetting the degree. -/
private noncomputable def awayLiftForgetDegree (f : A) :
    Localization.Away (sigmaMulPsi 𝒜 f) →+* Localization.Away f :=
  Localization.awayLift ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜))
    (sigmaMulPsi 𝒜 f)
    (isUnit_iff_exists_inv.mpr ⟨awayFrac f 2 1, comp_sigmaMulPsi_mul_awayFrac 𝒜⟩)

/-- **The comparison maps `(B[1/σ f · ψ f])₀ → A[1/f]` commute with the restriction maps of
degree-zero localizations:** the one of `B` attached to `D₊(σ g · ψ g) ⊆ D₊(σ f · ψ f)` on the
source, the one of `A` attached to `D₊(g) ⊆ D₊(f)` on the target. This is the restriction
compatibility of the degreewise description of the functions on the punctured cone. -/
@[stacks 0EKG "the comparison maps (B[1/sigma f * psi f])_0 to A[1/f] commute with the \
restriction maps of degree-zero localizations, for a general inclusion D+(g) <= D+(f) of \
standard opens"]
theorem puncturedToLocalization_degreeZeroRingMap_le
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ e : ℕ, 0 < e ∧ g ∈ 𝒜 e)
    (hσψf : ∃ d : ℕ, 0 < d ∧ sigmaMulPsi 𝒜 f ∈ grading 𝒜 d)
    (hσψg : ∃ e : ℕ, 0 < e ∧ sigmaMulPsi 𝒜 g ∈ grading 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hσψfg : ProjectiveSpectrum.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 g) ≤
      ProjectiveSpectrum.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
    (z : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) :
    puncturedToLocalization 𝒜
        (ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (sigmaMulPsi 𝒜 f) (sigmaMulPsi 𝒜 g)
          hσψf hσψg hσψfg z) =
      ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg (puncturedToLocalization 𝒜 z) := by
  have hkey : (awayLiftForgetDegree 𝒜 g).comp
        (ProjectiveSpectrum.localizedRingMap (grading 𝒜) (sigmaMulPsi 𝒜 f) (sigmaMulPsi 𝒜 g)
          hσψf hσψg hσψfg).toRingHom =
      (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom.comp
        (awayLiftForgetDegree 𝒜 f) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (sigmaMulPsi 𝒜 f)) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [AlgHom.commutes, awayLiftForgetDegree, awayLiftForgetDegree, IsLocalization.Away.lift_eq,
      IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.comp_apply, AlgHom.commutes]
  have h := congrArg
    (fun φ : Localization.Away (sigmaMulPsi 𝒜 f) →+* Localization.Away g => φ z.val) hkey
  simpa only [puncturedToLocalization, awayLiftForgetDegree, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, ProjectiveSpectrum.val_degreeZeroRingMap,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h

end Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

open Stacks.Truncation

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}

/-- **The chart of `U` over `D₊(g)` is contained in the chart over `D₊(f)`** as soon as
`D₊(g) ⊆ D₊(f)`: each chart is the part `U ⊓ D₊(ψ ·)` of the punctured cone lying over the
standard open, and `ψ` carries the inclusion to one of standard opens of `L`. -/
@[stacks 0EKG "the chart of U over D+(g) is contained in the chart over D+(f), for the \
truncation cone and an inclusion D+(g) <= D+(f) of standard opens of P"]
theorem basicOpen_sigmaMulPsi_le_of_basicOpen_le {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    ProjectiveSpectrum.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 g) ≤
      ProjectiveSpectrum.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f) := by
  have h : AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 g) ≤
      AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f) := by
    rw [sigmaMulPsi, sigmaMulPsi, ← openUInL_inf_basicOpen 𝒜 f d hf hd,
      ← openUInL_inf_basicOpen 𝒜 g e hg he]
    exact inf_le_inf_left _ (basicOpen_psi_le 𝒜 hf hd hg he hfg)
  exact h

/-- **The punctured degreewise inclusion commutes with restriction between two standard opens,
read in the degree-zero localizations of the truncation algebra.** On the source the restriction
of a section of `𝒪_P(m)` is the map of localizations of the shifted regular module, on the target
it is the degree-zero restriction map of `B`, and the comparison maps to `A[1/g]` identify the
two. -/
@[stacks 0EKG "the punctured degreewise inclusion of the sections of O_P(m) into the degree-zero \
localization of the truncation algebra at sigma f * psi f commutes with restriction between two \
standard opens, for every integer m"]
theorem puncturedConeTwistAwayHom_degreeZeroRingMap (m : ℤ) {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 m).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    puncturedConeTwistAwayHom 𝒜 m e hg he
        (((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 m).val.map (homOfLE hfg).op).hom s) =
      ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (sigmaMulPsi 𝒜 f) (sigmaMulPsi 𝒜 g)
        ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩ ⟨e, he, sigmaMulPsi_mem_grading 𝒜 e hg⟩
        (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg)
        (puncturedConeTwistAwayHom 𝒜 m d hf hd s) := by
  refine puncturedToLocalization_injective 𝒜 e hg ?_
  have h1 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 e hg he m
    (((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 m).val.map (homOfLE hfg).op).hom s)
  have h2 := puncturedToLocalization_degreeZeroRingMap_le 𝒜 ⟨d, hd, hf⟩ ⟨e, he, hg⟩
    ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩ ⟨e, he, sigmaMulPsi_mem_grading 𝒜 e hg⟩ hfg
    (basicOpen_sigmaMulPsi_le_of_basicOpen_le 𝒜 hf hd hg he hfg)
    (puncturedConeTwistAwayHom 𝒜 m d hf hd s)
  have h3 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd m s
  have h4 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE
    𝒜 hf hd hg he hfg m s
  have h5 := ProjectiveSpectrum.localizedMap_eq_localizedRingMap 𝒜
    (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 m) f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m s :
      LocalizedModule.Away f A))
  exact ((h1.trans h4).trans h5).trans
    (h2.trans (congrArg (ProjectiveSpectrum.localizedRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg)
      h3)).symm

end Stacks.AlgebraicGeometry.ProjConeTwist

end
