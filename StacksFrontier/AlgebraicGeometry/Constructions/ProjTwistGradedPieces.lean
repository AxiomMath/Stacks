module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.RingTheory.HomogeneousLocalization.GradedLocalizedModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# All the twists over a standard open are the graded pieces of one localization

Let `𝒜` be a graded ring and `f ∈ 𝒜 d` homogeneous. The sections of the sheaf associated to a
graded module `M` over the standard open `D₊(f)` are the *degree-zero* part `M₍f₎` of the
localization `M_f` ([Stacks, Tag 01M6], `associatedModuleSheafStandardOpenEquiv`), and the `n`-th
twist `𝒪(n)` is the sheaf associated to the ring shifted by `n` (`twistingSheaf`, part (1) of
[Stacks, Tag 01MN]). Combining the two, the sections of `𝒪(n)` over `D₊(f)` are the degree-zero
part of the localization of the *shifted* module, which by
`Stacks.GradedLocalization.gradedPiece_shift` is the degree-`n` part of the one unshifted
localization `S_f`.

So as `n` ranges over `ℤ`, the modules of sections of the twists over a fixed standard open are
the graded pieces of a single `S_f`, which `Stacks.GradedLocalization.isInternal_gradedPiece`
decomposes as their direct sum. This is the form in which the Čech computation of
`H^q(ℙⁿ_R, 𝒪(d))` uses them ([Stacks, Tag 01XT]): the Čech complex of the standard cover for all
the twists at once is the `ℤ`-graded Čech complex of the localizations of `R[T₀, …, Tₙ]`, and the
complex computing a single `𝒪(d)` is its degree-`d` summand.

## Main results

* `GradedModuleDegreeZeroLocalization_eq_gradedPiece_zero`: the degree-zero localization `M₍f₎`
  and the degree-zero graded piece of `M_f` have the same elements.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroLocalization_twistGrading_eq`: `M₍f₎` for
  the ring shifted by `n` is the degree-`n` graded piece of `S_f`.

## Implementation notes

The grading action `VAdd ℕ ℤ` of a non-negative ring degree on an integer module degree is a
file-local instance, here as in the imported files, since Mathlib does not want it globally. All
of them are `n +ᵥ i = n + i`, so `SetLike.GradedSMul 𝒜 𝒨` means the same thing in each.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public section

universe u v w t

open DirectSum

/-- The grading action used for a naturally graded ring acting on an integer-graded module. -/
local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- The degree-zero localization `M₍f₎` is contained in the degree-zero graded piece of
`M_f`. -/
theorem mem_gradedPiece_zero_of_mem_degreeZeroLocalization {f : S} {d : ℕ} (hf : f ∈ 𝒜 d)
    (y : LocalizedModule.Away (R := S) f M)
    (hy : y ∈ GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    y ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 f 0 := by
  let _ := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨d', n, hf', x, hx, rfl⟩ := hy
      exact Stacks.GradedLocalization.mk_mem_gradedPiece 𝒜 𝒨 hf' (by simpa using hx)
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy => exact Stacks.GradedLocalization.smul_mem_gradedPiece 𝒜 𝒨 hf 0 a hy

/-- The degree-zero graded piece of `M_f` is contained in the degree-zero localization
`M₍f₎`. -/
theorem mem_degreeZeroLocalization_of_mem_gradedPiece_zero {f : S}
    (y : LocalizedModule.Away (R := S) f M)
    (hy : y ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 f 0) :
    y ∈ GradedModuleDegreeZeroLocalization 𝒜 𝒨 f := by
  let _ := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
      obtain ⟨d', n, hf', x, hx, rfl⟩ := hy
      exact Submodule.subset_span ⟨d', n, hf', x, by simpa using hx, rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | neg y _ hy => exact neg_mem hy

/-- An element of `M_f` lies in the degree-zero localization `M₍f₎` if and only if it lies in
the degree-zero graded piece of `M_f`. -/
theorem mem_degreeZeroLocalization_iff_mem_gradedPiece_zero {f : S} {d : ℕ} (hf : f ∈ 𝒜 d)
    (y : LocalizedModule.Away (R := S) f M) :
    y ∈ GradedModuleDegreeZeroLocalization 𝒜 𝒨 f ↔
      y ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 f 0 :=
  ⟨mem_gradedPiece_zero_of_mem_degreeZeroLocalization 𝒜 𝒨 hf y,
    mem_degreeZeroLocalization_of_mem_gradedPiece_zero 𝒜 𝒨 y⟩

/-- The degree-zero localization `M₍f₎` and the degree-zero graded piece of `M_f` have the same
elements. -/
theorem GradedModuleDegreeZeroLocalization_eq_gradedPiece_zero {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) :
    {y : LocalizedModule.Away (R := S) f M | y ∈ GradedModuleDegreeZeroLocalization 𝒜 𝒨 f} =
      {y | y ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 f 0} :=
  Set.ext fun y => mem_degreeZeroLocalization_iff_mem_gradedPiece_zero 𝒜 𝒨 hf y

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

/-- The degree-zero localization of the ring shifted by `n`, which by part (1) of
[Stacks, Tag 01MN] together with [Stacks, Tag 01M6] is the module of sections of `𝒪(n)` over
`D₊(f)`, is the degree-`n` graded piece of the localization `S_f`. -/
@[ega "II 8.2.7" "partial", ega "II 8.2.9" "partial"]
theorem degreeZeroLocalization_twistGrading_eq {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℤ)
    (y : LocalizedModule.Away (R := S) f S) :
    y ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := S) 𝒜 n) f ↔
      y ∈ Stacks.GradedLocalization.gradedPiece 𝒜 (integerGrading (S := S) 𝒜) f n := by
  rw [mem_degreeZeroLocalization_iff_mem_gradedPiece_zero 𝒜 (twistGrading (S := S) 𝒜 n) hf y,
    Stacks.GradedLocalization.gradedPiece_shift 𝒜 (integerGrading (S := S) 𝒜) f n 0, zero_add]

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
