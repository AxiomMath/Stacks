module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface

/-!
# The cubic surface is proper over the affine line

The surface `Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t * T₀ * T₁ * T₂ = 0` of Stacks 0D5E is `Proj` of
`A = k[t][T₀, T₁, T₂] ⧸ (F)`. The degree-zero part of `A` is `k[t]`: every class of degree zero
is the class of a constant, and evaluation at the point `(1 : -1 : 0)`, where `F` vanishes for
every `t`, recovers the constant. So the structure morphism `Y ⟶ A¹_k` is
`Proj A ⟶ Spec A₀` followed by an isomorphism, and it is proper because `A` is of finite type
over `A₀`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.bijective_cubicDegreeZero`: `k[t] → A₀` is bijective.
* `Stacks.Examples.CurveFamilyNotScheme.isProper_cubicSurfaceToLine`: `Y ⟶ A¹_k` is proper.
* `Stacks.Examples.CurveFamilyNotScheme.locallyOfFinitePresentation_cubicSurfaceToLine`:
  `Y ⟶ A¹_k` is locally of finite presentation.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Stacks.AlgebraicGeometry.ProjPolyChart
  Stacks.RingTheory.HomogeneousQuotient

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The homogeneous coordinate ring `k[t][T₀, T₁, T₂] ⧸ (F)` of the cubic surface. -/
abbrev cubicRing : Type u := MvPolynomial (Fin 3) (Polynomial k) ⧸ (cubicIdeal k).toIdeal

/-- The grading of the homogeneous coordinate ring of the cubic surface. -/
abbrev cubicGrading : ℕ → Submodule (Polynomial k) (cubicRing k) :=
  quotientGrading (polyGrading (Polynomial k) 2) (cubicIdeal k)

/-- The map `k[t] → A₀` through which the structure morphism of the cubic surface is defined. -/
abbrev cubicDegreeZero : Polynomial k →+* cubicGrading k 0 :=
  (GradedRing.projZeroRingHom' (cubicGrading k)).comp (algebraMap (Polynomial k) (cubicRing k))

/-- Evaluation of the homogeneous coordinate ring of the cubic surface at `(1 : -1 : 0)`, where
the cubic vanishes identically in `t`. -/
def cubicEvalPoint : cubicRing k →+* Polynomial k :=
  Ideal.Quotient.lift _ (aeval (![1, -1, 0] : Fin 3 → Polynomial k)).toRingHom <| by
    intro a ha
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [cubicEquation]
    norm_num

/-- Evaluating the class of a constant at `(1 : -1 : 0)` gives back the constant. -/
theorem cubicEvalPoint_algebraMap (a : Polynomial k) :
    cubicEvalPoint k (algebraMap (Polynomial k) (cubicRing k) a) = a := by
  rw [← Ideal.Quotient.mk_algebraMap]
  simp [cubicEvalPoint, MvPolynomial.algebraMap_eq]

/-- The class of a constant is homogeneous of degree zero. -/
theorem algebraMap_mem_cubicGrading_zero (a : Polynomial k) :
    algebraMap (Polynomial k) (cubicRing k) a ∈ cubicGrading k 0 :=
  (mem_quotientGrading_iff _ _).2
    ⟨MvPolynomial.C a, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ _), rfl⟩

/-- The value of `k[t] → A₀` at `a` is the class of the constant `a`. -/
theorem coe_cubicDegreeZero (a : Polynomial k) :
    (cubicDegreeZero k a : cubicRing k) = algebraMap (Polynomial k) (cubicRing k) a := by
  simp only [cubicDegreeZero, RingHom.coe_comp, Function.comp_apply,
    GradedRing.coe_projZeroRingHom'_apply]
  exact DirectSum.decompose_of_mem_same _ (algebraMap_mem_cubicGrading_zero k a)

/-- The map `k[t] → A₀` is bijective: the degree-zero part of the homogeneous coordinate ring of
the cubic surface is `k[t]`. -/
theorem bijective_cubicDegreeZero : Function.Bijective (cubicDegreeZero k) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h := congrArg (fun z : cubicGrading k 0 => cubicEvalPoint k (z : cubicRing k)) hab
    simp only [coe_cubicDegreeZero] at h
    rwa [cubicEvalPoint_algebraMap, cubicEvalPoint_algebraMap] at h
  · obtain ⟨p, hp, hpx⟩ := (mem_quotientGrading_iff _ _).mp x.2
    rw [mem_homogeneousSubmodule, ← totalDegree_zero_iff_isHomogeneous,
      totalDegree_eq_zero_iff_eq_C] at hp
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    rw [coe_cubicDegreeZero, ← hpx]
    conv_rhs => rw [hp]
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]

/-- `k[t] → A₀` as an isomorphism of commutative rings. -/
instance isIso_ofHom_cubicDegreeZero : IsIso (CommRingCat.ofHom (cubicDegreeZero k)) := by
  have h : CommRingCat.ofHom (cubicDegreeZero k) =
      (RingEquiv.ofBijective _ (bijective_cubicDegreeZero k)).toCommRingCatIso.hom :=
    CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  rw [h]
  infer_instance

/-- The homogeneous coordinate ring of the cubic surface is of finite type over its degree-zero
part. -/
instance : Algebra.FiniteType (cubicGrading k 0) (cubicRing k) := by
  rw [← RingHom.finiteType_algebraMap]
  refine RingHom.FiniteType.of_comp_finiteType (f := cubicDegreeZero k) ?_
  have h : (algebraMap (cubicGrading k 0) (cubicRing k)).comp (cubicDegreeZero k) =
      algebraMap (Polynomial k) (cubicRing k) :=
    RingHom.ext fun a => coe_cubicDegreeZero k a
  rw [h, RingHom.finiteType_algebraMap]
  infer_instance

/-- **The cubic surface is proper over the affine line.** -/
instance isProper_cubicSurfaceToLine : IsProper (cubicSurfaceToLine k) := by
  have h₁ : IsProper (Proj.toSpecZero (cubicGrading k)) := inferInstance
  have h₂ : IsProper (Spec.map (CommRingCat.ofHom (cubicDegreeZero k))) := inferInstance
  exact MorphismProperty.comp_mem _ _ _ h₁ h₂

/-- The cubic surface is locally of finite presentation over the affine line. -/
instance locallyOfFinitePresentation_cubicSurfaceToLine :
    LocallyOfFinitePresentation (cubicSurfaceToLine k) :=
  inferInstance

end Stacks.Examples.CurveFamilyNotScheme

end
