module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The complement of the first affine chart of the relative projective line

The projective line `ℙ¹_ℤ` of `AlgebraicGeometry.projectiveLine` is glued from two copies of
`Spec ℤ[X]` along the punctured line `Spec ℤ[T, T⁻¹]`, the transition being inversion of the
coordinate. The two charts therefore overlap exactly where the coordinate is invertible, and so
the second chart adds to the first exactly one point: the origin of the second chart, which is
the point at infinity `Stacks.Chow.integralInfinitySection`. This file proves that, and then
transports it along the base change defining `ℙ¹_S`, where the first affine chart
`Stacks.Chow.affineChart` and the infinity section `Stacks.Chow.lineInfinitySection` are both
preimages under the projection `ℙ¹_S ⟶ ℙ¹_ℤ`, so that the complement of the one is the image of
the other.

The file also shows that the structure morphism `ℙ¹_S ⟶ S` has residue degree one at every point
in the image of a constant section.

## Main results

* `Stacks.Chow.compl_range_projectiveLineXChart` — the point at infinity is the only point of
  `ℙ¹_ℤ` off the first chart.
* `Stacks.Chow.compl_range_affineChart` — the image of the infinity section of `ℙ¹_S ⟶ S` is
  exactly the complement of the first affine chart of `ℙ¹_S`.
* `Stacks.Chow.compl_range_affineChart_eq_singleton` — over a one-point base that complement is
  a single point.
* `Stacks.Chow.residueDegree_eq_one_of_lineConstantSection` — the structure morphism of `ℙ¹_S`
  has residue degree one along a constant section.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The complement of the first chart of `ℙ¹_ℤ` -/

/-- A point of `Spec ℤ[X]` at which the coordinate does not vanish lies on the punctured
line. -/
theorem mem_range_puncturedChart_of_X_notMem
    {x : Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))}
    (hx : (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∉
      (x : PrimeSpectrum (Polynomial (ULift.{u} ℤ))).asIdeal) :
    x ∈ Set.range (projectiveLinePuncturedChart (ULift.{u} ℤ)).base := by
  show (x : PrimeSpectrum (Polynomial (ULift.{u} ℤ))) ∈
    Set.range (PrimeSpectrum.comap (Polynomial.toLaurent (R := ULift.{u} ℤ)))
  rw [show (Polynomial.toLaurent (R := ULift.{u} ℤ)) =
      algebraMap (Polynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ)) from rfl,
    PrimeSpectrum.localization_away_comap_range (LaurentPolynomial (ULift.{u} ℤ)) Polynomial.X]
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr hx

/-- The coordinate of the second chart vanishes at every point of `ℙ¹_ℤ` off the first chart. -/
theorem X_mem_of_notMem_range_projectiveLineXChart
    {x : Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))}
    (hx : (projectiveLineYChart (ULift.{u} ℤ)).base x ∉
      Set.range (projectiveLineXChart (ULift.{u} ℤ))) :
    (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∈
      (x : PrimeSpectrum (Polynomial (ULift.{u} ℤ))).asIdeal := by
  by_contra hXn
  obtain ⟨y, hy⟩ := mem_range_puncturedChart_of_X_notMem hXn
  refine hx ⟨(Spec.map (CommRingCat.ofHom
    (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)).base y, ?_⟩
  calc (projectiveLineXChart (ULift.{u} ℤ)).base
        ((Spec.map (CommRingCat.ofHom
          (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)).base y)
      = (Spec.map (CommRingCat.ofHom
          (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom) ≫
          projectiveLineXChart (ULift.{u} ℤ)).base y :=
        (Scheme.Hom.comp_apply _ _ y).symm
    _ = (projectiveLinePuncturedChart (ULift.{u} ℤ) ≫
          projectiveLineYChart (ULift.{u} ℤ)).base y := by
        rw [(isPullback_projectiveLineCharts' (ULift.{u} ℤ)).w]
    _ = (projectiveLineYChart (ULift.{u} ℤ)).base
          ((projectiveLinePuncturedChart (ULift.{u} ℤ)).base y) :=
        Scheme.Hom.comp_apply _ _ y
    _ = (projectiveLineYChart (ULift.{u} ℤ)).base x := by rw [hy]

/-- A point of `Spec ℤ[X]` at which the coordinate vanishes lies in the image of the origin
`Spec ℤ ⟶ Spec ℤ[X]`. -/
theorem mem_range_specMap_evalRingHom_zero_of_X_mem
    {x : Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))}
    (hx : (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∈
      (x : PrimeSpectrum (Polynomial (ULift.{u} ℤ))).asIdeal) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))) := by
  rw [range_specMap_evalRingHom_zero]
  have hker : RingHom.ker (Polynomial.evalRingHom (0 : ULift.{u} ℤ)) ≤
      (x : PrimeSpectrum (Polynomial (ULift.{u} ℤ))).asIdeal := by
    rw [Polynomial.ker_evalRingHom, Ideal.span_le, Set.singleton_subset_iff]
    simpa using hx
  exact fun a ha => hker ha

/-- The point at infinity is the only point of `ℙ¹_ℤ` off the first chart. -/
theorem compl_range_projectiveLineXChart :
    (Set.range (projectiveLineXChart (ULift.{u} ℤ)))ᶜ =
      Set.range (integralInfinitySection.{u}) := by
  refine Set.eq_of_subset_of_subset (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨x, rfl⟩ := Or.resolve_left (Set.eq_univ_iff_forall.mp
      (range_projectiveLineXChart_union_range_projectiveLineYChart (ULift.{u} ℤ)) p) hp
    rw [range_integralInfinitySection]
    exact ⟨x, mem_range_specMap_evalRingHom_zero_of_X_mem
      (X_mem_of_notMem_range_projectiveLineXChart hp), rfl⟩
  · exact Set.disjoint_left.mp
      disjoint_range_integralInfinitySection_projectiveLineXChart hp

/-! ### The complement of the first affine chart of `ℙ¹_S` -/

/-- The image of the infinity section is exactly the complement of the first affine chart of
`ℙ¹_S`. -/
theorem compl_range_affineChart (S : Scheme.{u}) :
    (Set.range (affineChart S))ᶜ = Set.range (lineInfinitySection S) := by
  rw [range_affineChart, ← Set.preimage_compl, compl_range_projectiveLineXChart,
    lineInfinitySection, range_lineConstantSection]

/-- Over a base with exactly one point the complement of the first affine chart is the single
point at infinity. -/
@[ega "II 7.4.14" "partial"]
theorem compl_range_affineChart_eq_singleton (S : Scheme.{u}) [Subsingleton S] [Nonempty S] :
    (Set.range (affineChart S))ᶜ = {(lineInfinitySection S).base (Classical.arbitrary S)} := by
  rw [compl_range_affineChart]
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨Classical.arbitrary S, rfl⟩, fun p hp => ?_⟩
  obtain ⟨s, rfl⟩ := hp
  exact congrArg _ (Subsingleton.elim s (Classical.arbitrary S))

/-! ### The residue degree of the structure morphism along a section -/

/-- The residue-field map of the structure morphism of `ℙ¹_S` at a point in the image of a
constant section is bijective. -/
theorem bijective_residueFieldMap_relativeProjectiveLine_of_lineConstantSection
    (S : Scheme.{u}) (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) (s : S) :
    Function.Bijective
      (((relativeProjectiveLine S ↘ S).residueFieldMap
        ((lineConstantSection S e).base s)).hom) := by
  have hcomp : Function.Bijective
      (((lineConstantSection S e ≫ (relativeProjectiveLine S ↘ S)).residueFieldMap s).hom) := by
    rw [lineConstantSection_comp S e, Scheme.residueFieldMap_id]
    exact Function.bijective_id
  have hsec : Function.Bijective (((lineConstantSection S e).residueFieldMap s).hom) :=
    bijective_residueFieldMap_of_isClosedImmersion (lineConstantSection S e) s
  rw [Scheme.residueFieldMap_comp] at hcomp
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hcomp.surjective (((lineConstantSection S e).residueFieldMap s).hom y)
  exact ⟨z, hsec.injective hz⟩

/-- The residue degree of the structure morphism of `ℙ¹_S` at a point in the image of a section
is one. -/
theorem residueDegree_eq_one_of_lineConstantSection (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) (s : S) :
    (relativeProjectiveLine S ↘ S).residueDegree ((lineConstantSection S e).base s) = 1 := by
  let _ := ((relativeProjectiveLine S ↘ S).residueFieldMap
    ((lineConstantSection S e).base s)).hom.toAlgebra
  show Module.finrank
    (S.residueField ((relativeProjectiveLine S ↘ S).base ((lineConstantSection S e).base s)))
    ((relativeProjectiveLine S).residueField ((lineConstantSection S e).base s)) = 1
  exact Module.finrank_of_bijective_algebraMap
    (bijective_residueFieldMap_relativeProjectiveLine_of_lineConstantSection S e s)

end Stacks.Chow

end
