module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable

/-!
# Degree-zero homology of an odd degree-one extension

Let `A` be a nonnegatively graded differential graded algebra with differential `dA` and let `f`
be an element of degree zero. Adjoining a variable `T` of degree one with `dT = f` produces the
extension `A⟨T⟩` of the previous file, and the differential on the extension is determined by
`dA` together with the value `f`. Because the differential vanishes in degree zero, `f` is
automatically a cycle, and multiplication by it is well defined on degree-zero homology.

This file records the resulting right-exact sequence
`H₀(A) --·f--> H₀(A) --> H₀(A⟨T⟩) --> 0`: the first map is multiplication by `f`, the second is
induced by the canonical inclusion of `A` into `A⟨T⟩`, the image of the first is exactly the
kernel of the second, and the second is surjective.

## Main definitions

* `DividedPowers.TateResolution.degreeZeroHomology` — degree-zero cycles modulo the boundaries
  coming from degree one.
* `DividedPowers.TateResolution.mulOnDegreeZeroHomology` — multiplication by a degree-zero
  element on degree-zero homology.
* `DividedPowers.TateResolution.toExtensionOnDegreeZeroHomology` — the map on degree-zero
  homology induced by the canonical inclusion into the odd degree-one extension.

## Main results

* `DividedPowers.TateResolution.mulOnDegreeZeroHomology_mk` and
  `DividedPowers.TateResolution.toExtensionOnDegreeZeroHomology_mk` compute the two maps on a
  class represented by a degree-zero element.
* `DividedPowers.TateResolution.exact_degreeZeroHomology_oddVariableExtension` — the image of
  multiplication by `f` is the kernel of the map to the extension.
* `DividedPowers.TateResolution.surjective_degreeZeroHomology_oddVariableExtension` — the map to
  the extension is surjective.

## Implementation notes

Degree-zero homology is presented directly as a quotient of the degree-zero graded piece `𝒜 0`,
by the submodule of those degree-zero elements that are differentials of degree-one elements,
rather than as a graded piece of the ungraded homology of the previous file. In degree zero every
element of `𝒜 0` is a cycle, so no kernel has to be taken, and the two maps of the sequence are
then induced on quotients by multiplication and by the inclusion.

The differential `dExt` on the extension is not constructed here. It enters as a parameter
together with the two equations that pin it down on the two summands of `A⟨T⟩`: it restricts to
`dA` along the inclusion, and it sends the adjoined variable to `f`. Exactness needs both, while
surjectivity needs only the first.

## References

* [Stacks Project, Tag 0GZ6](https://stacks.math.columbia.edu/tag/0GZ6)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open OddVariableExtension

attribute [local implicit_reducible] TwistedModule

universe u v

/-- Degree-zero homology of a nonnegatively graded differential graded algebra: the degree-zero
graded piece modulo the differentials of degree-one elements. -/
public abbrev degreeZeroHomology {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) : Type v :=
  (𝒜 0) ⧸ Submodule.comap (𝒜 0).subtype
    (LinearMap.range (dA.comp (𝒜 1).subtype))

/-- Multiplication by a degree-zero element on degree-zero homology. -/
public noncomputable def mulOnDegreeZeroHomology
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (f : A) (hf : f ∈ 𝒜 0) :
    degreeZeroHomology 𝒜 dA →ₗ[R] degreeZeroHomology 𝒜 dA := by
  let m : 𝒜 0 →ₗ[R] 𝒜 0 :=
    ((LinearMap.mulLeft R f).comp (𝒜 0).subtype).codRestrict (𝒜 0)
    (fun x => by
      simpa using (SetLike.mul_mem_graded hf x.property))
  refine Submodule.mapQ _ _ m ?_
  intro x hx
  obtain ⟨b, hb⟩ := hx
  change dA (b : A) = (x : A) at hb
  change f * (x : A) ∈ LinearMap.range (dA.comp (𝒜 1).subtype)
  refine ⟨⟨f * (b : A), by simpa using
    (SetLike.mul_mem_graded hf b.property)⟩, ?_⟩
  change dA (f * (b : A)) = f * (x : A)
  rw [IsDifferentialGradedAlgebra.leibniz hf b.property,
    IsDifferentialGradedAlgebra.d_grade_zero hf, zero_mul, zero_add, pow_zero,
    one_smul, hb]

/-- The map on degree-zero homology induced by the canonical inclusion into the odd degree-one
extension. -/
public noncomputable def toExtensionOnDegreeZeroHomology
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) (dExt : OddVariableExtension 𝒜 1 →ₗ[R]
      OddVariableExtension 𝒜 1)
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) :
    degreeZeroHomology 𝒜 dA →ₗ[R]
      degreeZeroHomology (OddVariableExtension.grade 𝒜 1) dExt := by
  let i : 𝒜 0 →ₗ[R] OddVariableExtension.grade 𝒜 1 0 :=
    (((OddVariableExtension.inclusionAlgHom 𝒜 1).toLinearMap.comp
      (𝒜 0).subtype).codRestrict
      (OddVariableExtension.grade 𝒜 1 0)
      (fun x => OddVariableExtension.inclusion_mem_grade 𝒜 1 0 x.property))
  refine Submodule.mapQ _ _ i ?_
  intro x hx
  obtain ⟨b, hb⟩ := hx
  change dA (b : A) = (x : A) at hb
  change OddVariableExtension.inclusion 𝒜 1 (x : A) ∈
    LinearMap.range (dExt.comp (OddVariableExtension.grade 𝒜 1 1).subtype)
  refine ⟨⟨OddVariableExtension.inclusion 𝒜 1 (b : A),
    OddVariableExtension.inclusion_mem_grade 𝒜 1 1 b.property⟩, ?_⟩
  change dExt (OddVariableExtension.inclusion 𝒜 1 (b : A)) =
    OddVariableExtension.inclusion 𝒜 1 (x : A)
  rw [hdExt, hb]

/-- Multiplication by a degree-zero element, computed on the class of a degree-zero element. -/
@[simp]
public theorem mulOnDegreeZeroHomology_mk
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (f : A) (hf : f ∈ 𝒜 0) (x : 𝒜 0) :
    mulOnDegreeZeroHomology 𝒜 dA f hf (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f * (x : A), SetLike.mul_mem_graded hf x.property⟩ : 𝒜 0) := by
  simp only [mulOnDegreeZeroHomology, Submodule.mapQ_apply]
  congr 1

/-- The map induced by the canonical inclusion, computed on the class of a degree-zero
element. -/
@[simp]
public theorem toExtensionOnDegreeZeroHomology_mk
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (x : 𝒜 0) :
    toExtensionOnDegreeZeroHomology 𝒜 dA dExt hdExt
      (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨OddVariableExtension.inclusion 𝒜 1 (x : A),
          OddVariableExtension.inclusion_mem_grade 𝒜 1 0 x.property⟩ :
          OddVariableExtension.grade 𝒜 1 0) := by
  simp only [toExtensionOnDegreeZeroHomology, Submodule.mapQ_apply]
  congr 1

/-- A degree-zero element of the extension has no component along the adjoined variable, so it
is the image of its own coefficient. -/
private theorem degreeZero_eq_inclusion
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (x : OddVariableExtension 𝒜 1)
    (hx : x ∈ OddVariableExtension.grade 𝒜 1 0) :
    x = OddVariableExtension.inclusion 𝒜 1 x.fst := by
  have hs : (show A from x.snd) = 0 := (Submodule.mem_bot R).mp <| by
    simpa using ((OddVariableExtension.mem_grade_iff 𝒜 1 0 x).mp hx).2
  exact TrivSqZeroExt.ext rfl (congrArg (fun a : A => (show TwistedModule 𝒜 1 from a)) hs)

/-- The differential of a degree-one element of the extension, in coefficient coordinates. -/
private theorem differential_degreeOne
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (f : A)
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 1) =
      OddVariableExtension.inclusion 𝒜 1 f)
    {y : OddVariableExtension 𝒜 1}
    (hy : y ∈ OddVariableExtension.grade 𝒜 1 1) :
    dExt y = OddVariableExtension.inclusion 𝒜 1
      (dA y.fst + (show A from y.snd) * f) := by
  have hy' := (OddVariableExtension.mem_grade_iff 𝒜 1 1 y).mp hy
  have hrepr := OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator 𝒜 1 y
  have hzero : dA (show A from y.snd) = 0 :=
    IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := dA) hy'.2
  have hprod := IsDifferentialGradedAlgebra.leibniz
    (𝒜 := OddVariableExtension.grade 𝒜 1) (d := dExt)
    (OddVariableExtension.inclusion_mem_grade 𝒜 1 0
      (a := (show A from y.snd)) hy'.2)
    (OddVariableExtension.generator_mem_grade 𝒜 1)
  conv_lhs => rw [← hrepr]
  rw [map_add, hdExt, hprod, hdExt, hT]
  simp [hzero, OddVariableExtension.inclusion]

/-- Multiplication by the cycle followed by the inclusion into the degree-one
extension is right exact on degree-zero homology. -/
@[stacks 0GZ6 "degree_one"]
public theorem exact_degreeZeroHomology_oddVariableExtension
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (f : A) (hf_grade : f ∈ 𝒜 0)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 1) =
      OddVariableExtension.inclusion 𝒜 1 f) :
    LinearMap.range (mulOnDegreeZeroHomology 𝒜 dA f hf_grade) =
      LinearMap.ker (toExtensionOnDegreeZeroHomology 𝒜 dA dExt hdExt) := by
  have hcomm : ∀ a : 𝒜 0, f * (a : A) = (a : A) * f := fun a => by
    simpa using (IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜)
      (i := 0) (j := 0) hf_grade a.property)
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, mulOnDegreeZeroHomology_mk,
      toExtensionOnDegreeZeroHomology_mk]
    apply (Submodule.Quotient.mk_eq_zero _).2
    change OddVariableExtension.inclusion 𝒜 1 (f * (a : A)) ∈
      LinearMap.range (dExt.comp (OddVariableExtension.grade 𝒜 1 1).subtype)
    let y : OddVariableExtension 𝒜 1 := TrivSqZeroExt.inr
      (show TwistedModule 𝒜 1 from (a : A))
    have hy : y ∈ OddVariableExtension.grade 𝒜 1 1 := by
      simp [y, OddVariableExtension.inr_mem_grade
        (Aᵢ := 𝒜) (d := 1) (m := 0) (a := (a : A)) a.property]
    have hd : dExt y = OddVariableExtension.inclusion 𝒜 1 (f * (a : A)) := by
      rw [differential_degreeOne 𝒜 dA dExt f hdExt hT hy]
      apply congrArg (OddVariableExtension.inclusion 𝒜 1)
      rw [hcomm a]
      simp [y]
    exact ⟨⟨y, hy⟩, hd⟩
  · intro hq
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, toExtensionOnDegreeZeroHomology_mk] at hq
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp
      (show OddVariableExtension.inclusion 𝒜 1 (x : A) ∈
        LinearMap.range (dExt.comp (OddVariableExtension.grade 𝒜 1 1).subtype) from
        (Submodule.Quotient.mk_eq_zero _).1 (by simpa using hq))
    have hy' := (OddVariableExtension.mem_grade_iff 𝒜 1 1 y).mp y.property
    have heq : (x : A) = dA y.val.fst + (show A from y.val.snd) * f := by
      simpa [OddVariableExtension.inclusion, differential_degreeOne 𝒜 dA dExt f hdExt hT y.property]
        using (congrArg TrivSqZeroExt.fst hy).symm
    let b : 𝒜 0 := ⟨(show A from y.val.snd), hy'.2⟩
    refine ⟨Submodule.Quotient.mk b, ?_⟩
    rw [mulOnDegreeZeroHomology_mk]
    apply (Submodule.Quotient.eq _).2
    rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]
    change (f * (b : A) - (x : A)) ∈
      LinearMap.range (dA.comp (𝒜 1).subtype)
    refine ⟨⟨-y.val.fst, (𝒜 1).neg_mem hy'.1⟩, ?_⟩
    change dA (-y.val.fst) = f * (b : A) - (x : A)
    rw [map_neg, heq, ← hcomm b]
    abel

/-- The inclusion onto degree-zero homology of the extension is surjective. -/
@[stacks 0GZ6 "degree_one"]
public theorem surjective_degreeZeroHomology_oddVariableExtension
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (dA : A →ₗ[R] A)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) :
    Function.Surjective
      (toExtensionOnDegreeZeroHomology 𝒜 dA dExt hdExt) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  have hx := (OddVariableExtension.mem_grade_iff 𝒜 1 0 x).mp x.property
  refine ⟨Submodule.Quotient.mk ⟨x.1.fst, hx.1⟩, ?_⟩
  rw [Submodule.mkQ_apply, toExtensionOnDegreeZeroHomology_mk]
  exact congrArg _ (Subtype.ext (degreeZero_eq_inclusion 𝒜 x.1 x.property).symm)

end DividedPowers.TateResolution

end
