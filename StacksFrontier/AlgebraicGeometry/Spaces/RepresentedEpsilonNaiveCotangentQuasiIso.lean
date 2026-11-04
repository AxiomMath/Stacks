module

public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonPullbackExact

/-!
# Reducing Stacks 0D0X to the two cohomology sheaves

The canonical map `α : ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` of Stacks 0D0X,
`AlgebraicGeometry.Space.representedEpsilonNaiveCotangentMap`, is a morphism of complexes which
vanish outside degrees `-1` and `0`: `NL_{X/Y}` has no other terms, and neither has
`NL_{X₀/Y₀}`, hence neither has its image under the additive functor `ε^*`.  So `α` is a
quasi-isomorphism as soon as it induces isomorphisms on the kernels and on the cokernels of the
two differentials (`CochainComplex.quasiIso_of_isZero_X_of_isIso_kernel_cokernel`).

## Main results

* `AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentMap_of_isIso`: the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- `ε^*NL_{X₀/Y₀}` has no terms outside degrees `-1` and `0`. -/
theorem isZero_representedEpsilonPullback_naiveCotangent_X (i : ℤ) (hneg : i ≠ -1)
    (hzero : i ≠ 0) :
    IsZero ((((representedEpsilonModulePullback B S hS U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (representedZariskiToposNaiveCotangentComplex B S hS φ)).X i) :=
  Functor.map_isZero _
    (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u, u, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J _ _ _ i hneg hzero)

/-- `NL_{X/Y}` has no terms outside degrees `-1` and `0`. -/
theorem isZero_representedSpaceNaiveCotangentComplex_X (i : ℤ) (hneg : i ≠ -1)
    (hzero : i ≠ 0) :
    IsZero ((representedSpaceNaiveCotangentComplex B S hS φ).X i) :=
  Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J _ _ _ i hneg hzero

/-- The category of sheaves of `𝒪_X`-modules with sections in `Type (u + 1)` is abelian, at the
universe the naive cotangent complex `NL_{X/Y}` lives in. -/
local instance abelianRepresentedSmallEtaleModules :
    Abelian (_root_.SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O)) :=
  SheafOfModules.instAbelian.{u + 1} _

/-- **Stacks 0D0X reduced to the two cohomology sheaves.**  The canonical map
`ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` is a quasi-isomorphism as soon as it induces isomorphisms on the
kernels and on the cokernels of the two differentials. -/
theorem quasiIso_representedEpsilonNaiveCotangentMap_of_isIso
    (hker : IsIso (kernel.map _ _ ((representedEpsilonNaiveCotangentMap B S hS φ).f (-1))
      ((representedEpsilonNaiveCotangentMap B S hS φ).f 0)
      ((representedEpsilonNaiveCotangentMap B S hS φ).comm (-1) 0).symm))
    (hcoker : IsIso (cokernel.map _ _ ((representedEpsilonNaiveCotangentMap B S hS φ).f (-1))
      ((representedEpsilonNaiveCotangentMap B S hS φ).f 0)
      ((representedEpsilonNaiveCotangentMap B S hS φ).comm (-1) 0).symm)) :
    QuasiIso (representedEpsilonNaiveCotangentMap B S hS φ) :=
  CochainComplex.quasiIso_of_isZero_X_of_isIso_kernel_cokernel _
    (isZero_representedEpsilonPullback_naiveCotangent_X B S hS φ)
    (isZero_representedSpaceNaiveCotangentComplex_X B S hS φ) hker hcoker

end AlgebraicGeometry.Space

end
