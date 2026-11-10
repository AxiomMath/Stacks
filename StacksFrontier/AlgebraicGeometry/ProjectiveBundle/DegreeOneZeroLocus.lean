module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TwistSectionLocus
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen
public import StacksFrontier.AlgebraicGeometry.TwistRigidityDegreeOne.Basic

/-!
# The support of the zero scheme of a degree-one section of `𝒪(1)`

Let `𝒮` be a graded ring generated in degree one over `𝒮 0`. For `a ∈ 𝒮 1` the zero scheme of
the global section of `𝒪(1)` on `Proj 𝒮` attached to `a` has support the complement of the
standard open `D₊(a)`: on a standard chart `D₊(f)`, `f ∈ 𝒮 1`, it is cut out by the fraction
`a / f`, whose nonvanishing locus is `D₊(f) ⊓ D₊(a)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.support_zeroScheme_degreeSection_one`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The zero scheme of the section of `𝒪(1)` attached to `a ∈ 𝒮 1` is supported exactly off
`D₊(a)`.** -/
theorem support_zeroScheme_degreeSection_one
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (a : 𝒮 1) :
    letI := isInvertible_twistingSheafModule_one 𝒮 hgen
    ((AlgebraicGeometry.zeroScheme (AlgebraicGeometry.Proj 𝒮)
          (twistingSheafModule 𝒮 ((1 : ℕ) : ℤ)) (degreeSection 𝒮 1 a)).support :
        Set (AlgebraicGeometry.Proj 𝒮)) =
      ((AlgebraicGeometry.Proj.basicOpen 𝒮 (a : S) : Set (AlgebraicGeometry.Proj 𝒮)))ᶜ := by
  let := isInvertible_twistingSheafModule_one 𝒮 hgen
  ext x
  obtain ⟨f, hf⟩ :=
    Stacks.AlgebraicGeometry.TwistRigidityDegreeOne.exists_degreeOne_notMem_of_adjoin_eq_top
      (𝒜 := 𝒮) hgen x
  have hxf : x ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) := hf
  let U : (AlgebraicGeometry.Proj 𝒮).affineOpens :=
    ⟨AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S),
      AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 (f : S) f.2 Nat.one_pos⟩
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hxf,
    zeroScheme_degreeSection_one_ideal_basicOpen 𝒮 hgen f.2 a, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton]
  change x ∉ (AlgebraicGeometry.Proj 𝒮).basicOpen
      ((AlgebraicGeometry.Proj.awayToSection 𝒮 (f : S)).hom
        (HomogeneousLocalization.Away.mk 𝒮 f.2 1 (a : S) _)) ↔ _
  rw [Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk 𝒮 f.2 Nat.one_pos 1 (a : S)
    (by simp)]
  simp [hxf]

end AlgebraicGeometry.ProjectiveSpectrum.Proj
