module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationChart

/-!
# Regression tests: the `R`-algebra structure on a homogeneous localization

`StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationChart` once declared its own
`Algebra R (HomogeneousLocalization 𝒜 x)`, built by `RingHom.toAlgebra`, beside the canonical
`HomogeneousLocalization.instAlgebra` of
`StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra`. Its scalar action was not
definitionally Mathlib's `HomogeneousLocalization.instSMul`, so in every importer Mathlib's
`Algebra.smul_def` failed to typecheck against the `•` that elaboration produces.

These examples, in a module importing the chart file, check that instance search finds the
canonical structure, that its action is `instSMul` at instance transparency, and that
`Algebra.smul_def` and `HomogeneousLocalization.val_smul` apply both as terms and through `rw`.
-/

open HomogeneousLocalization

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] (x : Submonoid A)

/-- Instance search finds the canonical structure. -/
example : (inferInstance : Algebra R (HomogeneousLocalization 𝒜 x)) = instAlgebra x := by
  with_reducible_and_instances rfl

/-- Its scalar action is Mathlib's numerator action, at instance transparency. -/
example : (instAlgebra (𝒜 := 𝒜) x).toSMul = instSMul x := by
  with_reducible_and_instances rfl

/-- Mathlib's `Algebra.smul_def`, as a term. -/
example (r : R) (z : HomogeneousLocalization 𝒜 x) :
    r • z = algebraMap R (HomogeneousLocalization 𝒜 x) r * z :=
  Algebra.smul_def r z

/-- Mathlib's `Algebra.smul_def`, through `rw`. -/
example (r : R) (z : HomogeneousLocalization 𝒜 x) :
    r • z = algebraMap R (HomogeneousLocalization 𝒜 x) r * z := by
  rw [Algebra.smul_def]

/-- Mathlib's `HomogeneousLocalization.val_smul` on the action of the synthesized algebra. -/
example (r : R) (z : HomogeneousLocalization 𝒜 x) :
    (@HSMul.hSMul R _ _ (@instHSMul R _ Algebra.toSMul) r z).val = r • z.val := by
  rw [val_smul]

/-- The structure map is the composite `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`. -/
example (r : R) :
    algebraMap R (HomogeneousLocalization 𝒜 x) r = fromZeroRingHom 𝒜 x (algebraMap R (𝒜 0) r) :=
  Stacks.Truncation.Chart.algebraMap_homogeneousLocalization 𝒜 x r
