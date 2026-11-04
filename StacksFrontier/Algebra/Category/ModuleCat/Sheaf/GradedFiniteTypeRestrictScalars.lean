module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtPowLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleRestrictScalars

/-!
# Finite type of a graded module survives restriction of scalars along a locally surjective map

Let `φ : A ⟶ B` be a unital homomorphism of sheaves of graded algebras over a sheaf of rings `R`
on a site, and let `M` be a graded `B`-module. `SheafOfModules.GradedModule.restrictScalars`
reads `M` as a graded `A`-module: the homogeneous pieces are unchanged and a homogeneous section
of `A` acts through `φ`.

Generation by a finite family of homogeneous sections is *not* preserved by restriction of
scalars in general — the coefficients of a combination live in `B` and have to be brought back
to `A`. This file proves that they can be when **`φ` is degreewise locally surjective**: each of
the finitely many coefficients lifts on some covering sieve, the finitely many sieves have a
common refinement (`CategoryTheory.GrothendieckTopology.exists_mem_forall_fin`), and on it the
lifted coefficients witness the same combination because the action of `restrictScalars φ M` is
the action of `M` composed with `φ`.

## Main results

* `SheafOfModules.GradedModule.restrictScalars_smulSection`: the action of `restrictScalars φ M`
  in a fixed total degree is the action of `M` on the image of the coefficient.
* `SheafOfModules.GradedModule.Generates.restrictScalars`: **a generating family of `M` over `B`
  generates `restrictScalars φ M` over `A`**, for a degreewise locally surjective `φ`.
* `SheafOfModules.GradedModule.isFiniteType_restrictScalars`: **`restrictScalars φ M` is of
  finite type whenever `M` is.**

## Implementation notes

Local surjectivity is taken as `CategoryTheory.Presheaf.IsLocallySurjective` of the underlying
morphism of presheaves of abelian groups in each degree, which is the shape the producers in
this library have — for instance
`Stacks.Blowup.isLocallySurjective_reesGradedPullbackHom_app_of_isAffine`. It is an explicit
hypothesis rather than an instance argument, because the class routinely sits in context at one
spelling of the underlying presheaf while synthesis asks for another; the same decision is
recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtPowLocallySurjective`.

The two coverings — the one on which a section is a `B`-combination, and the one on which the
coefficients of that combination lift to `A` — are composed by
`CategoryTheory.GrothendieckTopology.transitive`, which is why
`SheafOfModules.GradedModule.Generates` is defined through an actual sieve rather than as a bare
existential.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t a m v u

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- **The action of `restrictScalars φ M` in a fixed total degree** is the action of `M` on the
image of the coefficient under `φ`. Both sides are the same term: the pieces of
`restrictScalars φ M` are those of `M` and its action is `M`'s precomposed with `φ`. -/
theorem restrictScalars_smulSection (φ : GradedAlgebra.UnitalHom A B)
    (M : GradedModule.{t, a, m} B) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (x : (M.piece d).val.obj U) (y : (A.piece (k - d)).val.obj U) :
    (restrictScalars φ M).smulSection k x y =
      M.smulSection k x ((φ.app (k - d)).val.app U y) :=
  rfl

/-- **A family generating `M` over `B` generates `restrictScalars φ M` over `A`**, when `φ` is
locally surjective in every degree.

A homogeneous section is, on a covering sieve, a `B`-combination of the family; on a further
covering sieve the finitely many coefficients of that combination lift along `φ`, and the lifts
witness the same combination over `A`. -/
theorem Generates.restrictScalars {φ : GradedAlgebra.UnitalHom A B}
    (hφ : ∀ n : ℤ, Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (φ.app n).val))
    {M : GradedModule.{t, a, m} B} {U : C} {q : ℕ} {d : Fin q → ℤ}
    {s : ∀ i, (M.piece (d i)).val.obj (op U)} (hs : M.Generates d s) :
    (restrictScalars φ M).Generates d s := by
  intro k V f₀ x
  refine J.transitive (hs k V f₀ x) _ ?_
  rintro W g ⟨c, hc⟩
  obtain ⟨T, hT, hTall⟩ := J.exists_mem_forall_fin
    (fun i => Presheaf.imageSieve
      ((PresheafOfModules.toPresheaf R.obj).map (φ.app (k - d i)).val) (c i))
    fun i => (hφ (k - d i)).imageSieve_mem (c i)
  refine J.superset_covering ?_ hT
  intro W' h hh
  choose b hb using hTall h hh
  refine ⟨b, ?_⟩
  have key : ∀ i, M.smulSection k ((M.piece (d i)).val.restrictₛₗ ((h ≫ g) ≫ f₀).op (s i))
        ((φ.app (k - d i)).val.app (op W') (b i)) =
      (M.piece k).val.restrictₛₗ h.op
        (M.smulSection k ((M.piece (d i)).val.restrictₛₗ (g ≫ f₀).op (s i)) (c i)) := by
    intro i
    rw [smulSection_restrictₛₗ, restrictₛₗ_restrictₛₗ, Category.assoc]
    exact congrArg (M.smulSection k ((M.piece (d i)).val.restrictₛₗ (h ≫ g ≫ f₀).op (s i)))
      (hb i)
  show ∑ i, M.smulSection k ((M.piece (d i)).val.restrictₛₗ ((h ≫ g) ≫ f₀).op (s i))
      ((φ.app (k - d i)).val.app (op W') (b i)) =
    (M.piece k).val.restrictₛₗ (h ≫ g).op x
  refine Eq.trans (Finset.sum_congr rfl fun i _ => key i) ?_
  rw [← map_sum, hc]
  exact restrictₛₗ_restrictₛₗ (M.piece k).val g h x

/-- **Finite type survives restriction of scalars along a degreewise locally surjective unital
homomorphism.** The covering family and the generators are the ones `M` already has; only the
coefficients change. -/
theorem isFiniteType_restrictScalars {φ : GradedAlgebra.UnitalHom A B}
    (hφ : ∀ n : ℤ, Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (φ.app n).val))
    (M : GradedModule.{t, a, m} B) [hM : M.IsFiniteType] :
    (restrictScalars φ M).IsFiniteType where
  exists_generators := by
    obtain ⟨I, U, hU, hgen⟩ := hM.exists_generators
    refine ⟨I, U, hU, fun i => ?_⟩
    obtain ⟨n, d, s, hs⟩ := hgen i
    exact ⟨n, d, s, Generates.restrictScalars hφ hs⟩

end SheafOfModules.GradedModule

end
