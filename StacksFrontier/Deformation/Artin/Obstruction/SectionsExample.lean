module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections

/-!
# The obstruction theory of the functor of sections of a flat module

Let `S = Spec Λ` with `Λ` Noetherian, let `W → S` be a morphism of schemes and let `𝓕` be a
quasi-coherent `𝒪_W`-module flat over `S`. Stacks 07YH considers
```
F : (Sch/S)_{fppf}^{opp} ⟶ Sets,   T/S ↦ H⁰(W_T, 𝓕_T)
```
and asserts that the category fibred in groupoids attached to `F` has an obstruction theory,
with

1. obstruction modules `𝒪_x(M) = H¹(W_A, 𝓕_A ⊗_A M)`, and
2. obstruction element `o_x(A') ∈ 𝒪_x(I)` the image of `x` under the boundary map
   `H⁰(W_A, 𝓕_A) → H¹(W_A, 𝓕_A ⊗_A I)` of the short exact sequence
   `0 → 𝓕_A ⊗_A I → 𝓕_{A'} → 𝓕_A → 0`.

The source explicitly omits two things: the construction of that short exact sequence, and the
explanation of why flatness of `𝓕` over `S` makes it exact. This file supplies both of the
omitted ingredients, and the mechanism behind condition (iii) of Stacks 07YG.

## Main results

* `Deformation.Artin.SectionsExample.baseChangeTensorEquiv`: the first term of the sequence,
  `𝓕_A ⊗_A M`, is the base change `𝓕 ⊗_Λ M`; this is how the sequence of clause (2) is
  obtained from the sequence `0 → I → A' → A → 0` of `Λ`-modules.
* `Deformation.Artin.SectionsExample.exact_lTensor_kernelSubmodule`: the sequence
  `0 → 𝓕 ⊗_Λ I → 𝓕 ⊗_Λ A' → 𝓕 ⊗_Λ A → 0` is short exact, because `𝓕` is flat over `Λ`.
  Exactness at the left is exactly where flatness is used; without it the first map need not
  be injective.
* `Deformation.Artin.SectionsExample.exists_lift_iff_delta_eq_zero`: for a short exact
  sequence of `𝒪_X`-modules on a scheme, a section of the quotient is in the image of the
  sections of the middle term exactly when its boundary in `H¹` of the subobject vanishes.
  This is the boundary map of clause (2) and the equivalence of condition (iii).
* `Deformation.Artin.SectionsExample.rightDerivedZeroIsoSections`: `H⁰(U, -)` is the functor
  of sections over `U`, so the degree-`0` term of the long exact sequence above is the
  source's `H⁰(W_T, 𝓕_T)`.

## Implementation notes

The short exact sequence of clause (2) lives on `W_{A'}`, whose underlying topological space
is that of `W_A`; the source's construction is the pushforward along that homeomorphism of
the sequence obtained by applying the quasi-coherent base-change functor
`G ↦ (W → S)^* G ⊗_{𝒪_W} 𝓕` to the sequence `0 → I → A' → A → 0` of `𝒪_S`-modules. The
exactness of that functor is the flatness hypothesis; on sections over an affine it is the
exactness recorded here, `exact_lTensor_kernelSubmodule`, and sheaf-theoretically it is
`Stacks.SheafOfModules.pullbackTensorFunctor_exact` (Stacks 0GMU).

The boundary map is the connecting morphism of the long exact cohomology sequence over an open
of a scheme, `Stacks.AmpleCohomologicalCriterion.sectionsDeltaFunctor`, which is the right
derived δ-functor of the sections functor; `rightDerivedZeroIsoSections` identifies its
degree-`0` part with sections, so that the statement of `exists_lift_iff_delta_eq_zero` is
about honest global sections of the three modules.

The flatness statement is phrased for a `Λ`-module `𝓕` rather than for a sheaf, which is the
level at which the source's omitted argument lives: the sequence of `Λ`-modules
`0 → I → A' → A → 0` is exact, and tensoring with a flat module preserves it. Only flatness
of `𝓕` over `Λ` is used, and no hypothesis on the square of `I` is needed for exactness; the
square-zero hypothesis of a deformation situation is what makes `I` an `A`-module, which is
what lets `𝓕 ⊗_Λ I` be read as `𝓕_A ⊗_A I`.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public section

universe u v w

namespace Deformation.Artin.SectionsExample

open CategoryTheory TensorProduct AlgebraicGeometry Opposite TopologicalSpace

/-! ### Clause (2): the short exact sequence and the role of flatness -/

section Flat

variable {Λ : Type u} [CommRing Λ] {A' A : Type w} [CommRing A'] [CommRing A]
  [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)

/-- The kernel `I = Ker(A' → A)` of a surjection of `Λ`-algebras, as a `Λ`-submodule
of `A'`. -/
abbrev kernelSubmodule : Submodule Λ A' :=
  Submodule.restrictScalars Λ (RingHom.ker (π : A' →+* A))

/-- The sequence of `Λ`-modules `0 → I → A' → A` is exact at `A'`. -/
theorem exact_kernelSubmodule_subtype :
    Function.Exact ⇑(kernelSubmodule π).subtype ⇑π.toLinearMap := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, (RingHom.mem_ker (f := (π : A' →+* A))).2 hx⟩, rfl⟩
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact (RingHom.mem_ker (f := (π : A' →+* A))).1 hz

variable (F : Type v) [AddCommGroup F] [Module Λ F]

/-- **Stacks 07YH, clause (2): the short exact sequence, and why flatness gives it.** For a
surjection `A' → A` of `Λ`-algebras with kernel `I` and a `Λ`-module `𝓕` flat over `Λ`, the
sequence
```
0 → 𝓕 ⊗_Λ I → 𝓕 ⊗_Λ A' → 𝓕 ⊗_Λ A → 0
```
is short exact: exact at the middle term and surjective on the right for any `𝓕`, and
injective on the left because `𝓕` is flat. Through `baseChangeTensorEquiv` the left-hand term
is the source's `𝓕_A ⊗_A I`, the middle term is `𝓕_{A'}` and the right-hand term is `𝓕_A`,
so this is the sequence of clause (2) of the source together with the explanation, omitted
there, of why flatness of `𝓕` over `S` makes it short exact. -/
theorem exact_lTensor_kernelSubmodule (hπ : Function.Surjective π) [Module.Flat Λ F] :
    Function.Injective ⇑(LinearMap.lTensor F (kernelSubmodule π).subtype) ∧
      Function.Exact ⇑(LinearMap.lTensor F (kernelSubmodule π).subtype)
        ⇑(LinearMap.lTensor F π.toLinearMap) ∧
      Function.Surjective ⇑(LinearMap.lTensor F π.toLinearMap) :=
  ⟨Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective,
    Module.Flat.lTensor_exact F (exact_kernelSubmodule_subtype π),
    LinearMap.lTensor_surjective F hπ⟩

/-- **Stacks 07YH, clause (2): `𝓕_A ⊗_A M = 𝓕 ⊗_Λ M`.** For an `A`-module `M`, the first term
`𝓕_A ⊗_A M` of the short exact sequence of clause (2), where `𝓕_A = A ⊗_Λ 𝓕` is the base
change of `𝓕`, is the base change `𝓕 ⊗_Λ M` of `𝓕` along `Λ → A` tensored with `M`. Taking
`M = I` the kernel of a deformation situation — an `A`-module because `I² = 0` — identifies
the left-hand term of `exact_lTensor_kernelSubmodule` with the source's `𝓕_A ⊗_A I`. -/
noncomputable def baseChangeTensorEquiv (M : Type w) [AddCommGroup M] [Module A M]
    [Module Λ M] [IsScalarTower Λ A M] :
    M ⊗[A] (A ⊗[Λ] F) ≃ₗ[A] M ⊗[Λ] F :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange Λ A A M F

end Flat

/-! ### Clause (2) and condition (iii): the boundary map and the lifting criterion -/

section Cohomology

open Stacks.AmpleCohomologicalCriterion Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (U : Opens X.carrier)

/-- **`H⁰(U, -)` is the functor of sections over `U`.** The degree-`0` term of the long exact
cohomology sequence of a scheme is the module of sections, so that the source's
`H⁰(W_T, 𝓕_T)` — the value of the functor `F` of Stacks 07YH — is the module of global
sections of `𝓕_T` on `W_T`. -/
noncomputable def rightDerivedZeroIsoSections :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived 0 ≅
      SheafOfModules.evaluation X.ringCatSheaf (op U) :=
  Functor.rightDerivedZeroIsoSelf _

/-- **Stacks 07YH, clause (2) and condition (iii): the boundary map and the lifting
criterion.** Let `0 → G₁ → G₂ → G₃ → 0` be a short exact sequence of `𝒪_X`-modules on a
scheme `X`. A section `s` of `G₃` over an open `U` is the image of a section of `G₂` if and
only if its image under the boundary map `H⁰(U, G₃) → H¹(U, G₁)` vanishes.

Applied to the sequence `0 → 𝓕_A ⊗_A I → 𝓕_{A'} → 𝓕_A → 0` of clause (2) and to the section
`x ∈ H⁰(W_A, 𝓕_A)`, this is exactly the statement that the obstruction element
`o_x(A') ∈ H¹(W_A, 𝓕_A ⊗_A I)` vanishes if and only if `x` lifts to a section of `𝓕_{A'}`,
that is condition (iii) of Stacks 07YG for the example. -/
theorem exists_lift_iff_delta_eq_zero
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (s : (((sectionsDeltaFunctor X U).functor 0).obj S.X₃ : Type u)) :
    (∃ t : (((sectionsDeltaFunctor X U).functor 0).obj S.X₂ : Type u),
        ConcreteCategory.hom (((sectionsDeltaFunctor X U).functor 0).map S.g) t = s) ↔
      ConcreteCategory.hom ((sectionsDeltaFunctor X U).δ hS 0) s = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simpa using congr(ConcreteCategory.hom $((sectionsDeltaFunctor X U).map_g_δ hS 0) t)
  · intro h
    exact ((ShortComplex.moduleCat_exact_iff _).1
      ((sectionsDeltaFunctor X U).scδ₁_exact hS 0)) s h

end Cohomology

end Deformation.Artin.SectionsExample
