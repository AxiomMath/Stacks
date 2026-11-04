module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure morphism of `Proj` to the terminal scheme

Projective `n`-space over a scheme `S` is the base change `ℙⁿ_S = S ×_{Spec ℤ} ℙⁿ_ℤ`, realized
as a pullback over the terminal scheme. This file shows that for a graded ring `A` of finite type
over its degree-zero part `𝒜 0` with `Spec (𝒜 0)` terminal, the morphism from `Proj 𝒜` to the
terminal scheme is locally of finite type, and that for the total-degree grading of a polynomial
ring in finitely many variables over `ULift ℤ` the spectrum of the degree-zero part is terminal.

## Main definitions

* `Stacks.AlgebraicGeometry.DivisorCluster.homogeneousSubmoduleZeroRingEquiv`: the degree-zero
  part of the total-degree grading of a polynomial ring is isomorphic to the coefficient ring.
* `Stacks.AlgebraicGeometry.DivisorCluster.isTerminalSpecHomogeneousSubmoduleZero`: the spectrum
  of that degree-zero part over `ULift ℤ` is a terminal scheme.

## Main results

* `Stacks.AlgebraicGeometry.DivisorCluster.isIso_terminalFrom`: the morphism from a terminal
  object to the chosen terminal object is an isomorphism.
* `Stacks.AlgebraicGeometry.DivisorCluster.bijective_algebraMap_homogeneousSubmodule_zero`: the
  coefficient ring maps bijectively onto the degree-zero part of the total-degree grading.
* `Stacks.AlgebraicGeometry.DivisorCluster.locallyOfFiniteType_terminalFrom_proj`: for a graded
  ring that is of finite type over its degree-zero part and whose `Spec (𝒜 0)` is a terminal
  scheme, the structure morphism of `Proj 𝒜` to the terminal scheme is locally of finite type.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.DivisorCluster

universe u v

/-- The morphism from a terminal object to the chosen terminal object is invertible. -/
public theorem isIso_terminalFrom {C : Type*} [Category C] [HasTerminal C] {X : C}
    (hX : IsTerminal X) : IsIso (terminal.from X) := by
  have h : terminal.from X = (hX.uniqueUpToIso terminalIsTerminal).hom := terminal.hom_ext _ _
  rw [h]
  infer_instance

section Grading

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structure map of the coefficient ring into the degree-zero part of the total-degree
grading of a polynomial ring is bijective: a polynomial is homogeneous of degree zero exactly
when it is a constant. -/
public theorem bijective_algebraMap_homogeneousSubmodule_zero
    (ι : Type v) (R : Type u) [CommRing R] :
    Function.Bijective
      (algebraMap R (MvPolynomial.homogeneousSubmodule ι R 0)) := by
  refine ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩
  · have h : (MvPolynomial.C a : MvPolynomial ι R) = MvPolynomial.C b := by
      have h' := congrArg (fun y : MvPolynomial.homogeneousSubmodule ι R 0 ↦ (y : MvPolynomial ι R))
        hab
      simpa [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq] using h'
    exact MvPolynomial.C_injective ι R h
  · obtain ⟨y, hy⟩ : ∃ y, algebraMap R (MvPolynomial ι R) y = (x : MvPolynomial ι R) := by
      rw [← Submodule.mem_one, ← MvPolynomial.homogeneousSubmodule_zero]
      exact x.2
    exact ⟨y, Subtype.ext (by rw [SetLike.GradeZero.coe_algebraMap]; exact hy)⟩

/-- The degree-zero part of the total-degree grading of a polynomial ring is the coefficient
ring. -/
public noncomputable def homogeneousSubmoduleZeroRingEquiv (ι : Type v) (R : Type u) [CommRing R] :
    R ≃+* (MvPolynomial.homogeneousSubmodule ι R 0) :=
  RingEquiv.ofBijective _ (bijective_algebraMap_homogeneousSubmodule_zero ι R)

/-- The spectrum of the degree-zero part of the total-degree grading of a polynomial ring over
the canonical universe copy of the integers is a terminal scheme. -/
public noncomputable def isTerminalSpecHomogeneousSubmoduleZero (n : ℕ) :
    IsTerminal (Spec (CommRingCat.of
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0))) :=
  specULiftZIsTerminal.ofIso
    (Scheme.Spec.mapIso
      (homogeneousSubmoduleZeroRingEquiv (Fin (n + 1)) (ULift.{u} ℤ)).toCommRingCatIso.op).symm

section Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If a graded ring is of finite type over its degree-zero part and the spectrum of that
degree-zero part is a terminal scheme, then the morphism from `Proj` of the grading to the
chosen terminal scheme is locally of finite type. -/
@[ega "II 2.7.1" "partial"]
public theorem locallyOfFiniteType_terminalFrom_proj [Algebra.FiniteType (𝒜 0) A]
    (hT : IsTerminal (Spec (CommRingCat.of (𝒜 0)))) :
    LocallyOfFiniteType (terminal.from (Proj 𝒜)) := by
  have := isIso_terminalFrom hT
  have h : terminal.from (Proj 𝒜) =
      Proj.toSpecZero 𝒜 ≫ terminal.from (Spec (CommRingCat.of (𝒜 0))) :=
    terminal.hom_ext _ _
  rw [h]
  infer_instance

end Proj

end Grading

end Stacks.AlgebraicGeometry.DivisorCluster

end
