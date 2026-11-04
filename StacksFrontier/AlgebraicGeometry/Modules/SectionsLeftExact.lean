module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Taking sections over an open is left exact on modules on a scheme

Let `X` be a scheme and let `U` be an open subset of `X`. Taking sections over `U` is a functor
from the abelian category `X.Modules` of `𝒪_X`-modules to modules over the ring `Γ(X, U)`, and
this functor is left exact: it preserves kernels, because a limit of sheaves of modules is
computed sectionwise. Nothing is claimed on the other side; a surjection of `𝒪_X`-modules need
not be surjective on sections, and the failure is what sheaf cohomology measures.

In elementary terms left exactness says two things. First, a monomorphism `ψ : ℰ ⟶ 𝒜` of
`𝒪_X`-modules is injective on sections over every open. Second, if `ℰ ⟶ 𝒜 ⟶ ℬ` is exact at `𝒜`
and `ℰ ⟶ 𝒜` is a monomorphism, then a section of `𝒜` over `U` which the second map kills is the
image of a section of `ℰ` over `U`: on sections over `U` the image of `ψ` is exactly the kernel
of the next map, which is the "image = kernel" form of exactness.

The two statements are read off from one categorical fact, that the evaluation functor
`CategoryTheory.SheafOfModules.evaluation X.ringCatSheaf (op U)` preserves finite limits — this
is `CategoryTheory.SheafOfModules.Finite.evaluationPreservesFiniteLimits` in Mathlib — through
the standard characterisation of left exact functors between abelian categories: a left exact
functor carries an exact `ℰ ⟶ 𝒜 ⟶ ℬ` with `ℰ ⟶ 𝒜` monomorphic to an exact sequence whose first
map is again monomorphic.

## Main results

* `Stacks.AlgebraicGeometry.Modules.mono_map_evaluation`: a monomorphism of sheaves of modules
  stays a monomorphism after evaluation at an open.
* `Stacks.AlgebraicGeometry.Modules.exact_map_evaluation`: **evaluation at an open is left
  exact**, in the form that it carries a short complex which is exact with monomorphic first map
  to a short complex of modules which is exact with monomorphic first map. This is the
  sectionwise description of the kernel of a morphism of sheaves of modules.
* `Stacks.AlgebraicGeometry.Modules.injective_app_of_mono`: **a monomorphism of `𝒪_X`-modules is
  injective on sections over every open.**
* `Stacks.AlgebraicGeometry.Modules.exists_app_eq_of_exact`: **exactness is detected on sections
  over every open**, in element form: a section killed by the second map of an exact short
  complex whose first map is a monomorphism is the image of a section of the first term.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` wrapper around
`CategoryTheory.SheafOfModules X.ringCatSheaf` carrying its own `Hom` and its own `Category`
instance, so an instance registered for `CategoryTheory.SheafOfModules X.ringCatSheaf` is not
found at the `Scheme.Modules` spelling. The categorical work is therefore done at the
`CategoryTheory.SheafOfModules` spelling, where Mathlib's preservation instances for
`evaluation` apply, and the two element-level statements are written at the `Scheme.Modules`
spelling, which is the one `Γ(-, U)` and `Scheme.Modules.Hom.app` are written at. The crossing
between the two spellings is a defeq unification inside the proofs, never an instance search.

`CategoryTheory.SheafOfModules.evaluation` is itself a `def` built as a composite of the
forgetful functor to presheaves of modules with evaluation on presheaves of modules, so its
additivity is not found by instance search either; `evaluationAdditive` registers it after
unfolding.

Applying a morphism to a section is `Scheme.Modules.Hom.app`, whose values are morphisms of
abelian groups, while evaluation lands in `ModuleCat (X.ringCatSheaf.obj.obj (op U))`. The
underlying functions agree definitionally, since the abelian group of sections is obtained from
the module of sections by a forgetful functor which does not change the carrier; so the element
forms are obtained from the `ModuleCat` statements with no transport.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- Evaluation of sheaves of modules on a scheme at an open is an additive functor. Mathlib
builds `CategoryTheory.SheafOfModules.evaluation` as a composite, so this is not found by
instance search. -/
noncomputable instance evaluationAdditive (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf U).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- **Evaluation at an open is left exact.** A short complex of sheaves of modules on a scheme
which is exact and whose first map is a monomorphism has exact sections over every open, again
with monomorphic first map. Equivalently: the kernel of a morphism of sheaves of modules is
computed sectionwise. -/
theorem exact_map_evaluation (U : X.Opens)
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)) (hS : S.Exact) (hf : Mono S.f) :
    (S.map (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U))).Exact ∧
      Mono ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).map S.f) := by
  have := hf
  exact ⟨hS.map_of_mono_of_preservesKernel _ hf inferInstance, inferInstance⟩

/-- A monomorphism of sheaves of modules on a scheme stays a monomorphism after evaluation at an
open, since evaluation preserves finite limits. -/
theorem mono_map_evaluation {E A : SheafOfModules.{u} X.ringCatSheaf} (ψ : E ⟶ A) (hψ : Mono ψ)
    (U : X.Opens) : Mono ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).map ψ) := by
  have := hψ
  infer_instance

/-- **A monomorphism of `𝒪_X`-modules is injective on sections over every open.** -/
theorem injective_app_of_mono {E A : X.Modules} (ψ : E ⟶ A) [Mono ψ] (U : X.Opens) :
    Function.Injective (fun t : Γ(E, U) => ψ.app U t) :=
  (ModuleCat.mono_iff_injective _).1
    (mono_map_evaluation (show (E : SheafOfModules.{u} X.ringCatSheaf) ⟶ A from ψ) ‹Mono ψ› U)

/-- **Exactness of a short complex of `𝒪_X`-modules is detected on sections over every open**, in
the "image = kernel" element form: if `ψ : ℰ ⟶ 𝒜` is a monomorphism and `ℰ ⟶ 𝒜 ⟶ ℬ` is exact at
`𝒜`, then a section of `𝒜` over `U` killed by `ℬ`'s map is the image of a section of `ℰ` over
`U`. -/
theorem exists_app_eq_of_exact {E A B : X.Modules} (ψ : E ⟶ A) (b : A ⟶ B) (w : ψ ≫ b = 0)
    (hex : (ShortComplex.mk ψ b w).Exact) [Mono ψ] (U : X.Opens) (u : Γ(A, U))
    (hu : b.app U u = 0) : ∃ t : Γ(E, U), ψ.app U t = u := by
  have hex' : (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) ψ b w).Exact := hex
  have hψ : Mono (C := SheafOfModules.{u} X.ringCatSheaf) ψ := ‹Mono ψ›
  have h := (exact_map_evaluation U _ hex' hψ).1
  rw [ShortComplex.moduleCat_exact_iff] at h
  exact h u hu

end Stacks.AlgebraicGeometry.Modules

end
