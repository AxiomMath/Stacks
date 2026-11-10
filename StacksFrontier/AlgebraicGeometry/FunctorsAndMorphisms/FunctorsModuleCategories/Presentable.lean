module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Finitely presented modules are categorically compact

A finitely presented module is a finitely presentable object of its module category, that is,
the functor it corepresents commutes with filtered colimits. This is proved first for finite
free modules, where it comes from the free/forget adjunction and finiteness of the index set,
then for an arbitrary finitely presented module by writing it as the cokernel of a map of
finite free modules, and finally in an arbitrary module universe by restricting scalars along
`A ≃+* ULift A`.

## Main results

* `ModuleCat.finiteFree_isFinitelyPresentable`: a finite free module is finitely presentable.
* `ModuleCat.finitePresentation_isFinitelyPresentable_sameUniverse`: a finitely presented module
  over a ring in its own universe is finitely presentable.
* `ModuleCat.finitePresentation_of_restrictScalarsEquivalence`: finite presentation transports
  along restriction of scalars by a ring isomorphism.
* `ModuleCat.finitePresentation_isFinitelyPresentable`: a finitely presented module is finitely
  presentable, with the ring and module universes independent.

## References

* [Stacks Project, Tag 0GNJ](https://stacks.math.columbia.edu/tag/0GNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ u₂ t

namespace ModuleCat

/-- A finite free module over a ring is a finitely presentable object of its module category. -/
public lemma finiteFree_isFinitelyPresentable (A : Type u) [Ring A] (n : ℕ) :
    IsFinitelyPresentable.{u} (ModuleCat.of A (Fin n → A)) := by
  have : Fact (Cardinal.aleph0 : Cardinal.{u}).IsRegular :=
    Cardinal.fact_isRegular_aleph0
  have : (forget (ModuleCat.{u} A)).IsCardinalAccessible
      (Cardinal.aleph0 : Cardinal.{u}) :=
    ⟨fun J _ _ => by
      have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
      exact PreservesFilteredColimitsOfSize.preserves_filtered_colimits
        (F := forget (ModuleCat.{u} A)) J⟩
  have : IsCardinalPresentable (ULift.{u} (Fin n))
      (Cardinal.aleph0 : Cardinal.{u}) := by
    rw [Types.isCardinalPresentable_iff]
    exact hasCardinalLT_of_finite _ _ le_rfl
  have : IsCardinalPresentable ((ModuleCat.free A).obj (ULift.{u} (Fin n)))
      (Cardinal.aleph0 : Cardinal.{u}) :=
    (ModuleCat.adj A).isCardinalPresentable_leftAdjoint_obj _ _
  have : IsCardinalPresentable (ModuleCat.of A (ULift.{u} (Fin n) →₀ A))
      (Cardinal.aleph0 : Cardinal.{u}) := by
    change IsCardinalPresentable ((ModuleCat.free A).obj (ULift.{u} (Fin n))) _
    infer_instance
  exact isCardinalPresentable_of_iso
    (((Finsupp.domLCongr (R := A) (M := A)
      (Equiv.ulift.{u} : ULift.{u} (Fin n) ≃ Fin n)).trans
      (Finsupp.linearEquivFunOnFinite A A (Fin n))).toModuleIso) _

/-- A finitely presented module over a ring in the same universe is finitely presentable:
it is the cokernel of a map of finite free modules, and a finite colimit of finitely
presentable objects is finitely presentable. -/
public lemma finitePresentation_isFinitelyPresentable_sameUniverse
    (A : Type u) [Ring A] (M : ModuleCat.{u} A) [Module.FinitePresentation A M] :
    IsFinitelyPresentable.{u} M := by
  have : Fact (Cardinal.aleph0 : Cardinal.{u}).IsRegular :=
    Cardinal.fact_isRegular_aleph0
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' A M
  let f' : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A (Fin n → A) :=
    ModuleCat.ofHom g
  let g' : ModuleCat.of A (Fin n → A) ⟶ M := ModuleCat.ofHom f
  have (k : WalkingParallelPair) :
      IsCardinalPresentable ((parallelPair f' 0).obj k)
        (Cardinal.aleph0 : Cardinal.{u}) := by
    cases k
    · simpa [parallelPair] using finiteFree_isFinitelyPresentable A m
    · simpa [parallelPair] using finiteFree_isFinitelyPresentable A n
  exact isCardinalPresentable_of_isColimit.{u} _
    (ModuleCat.isColimitCokernelCofork f' g' hgf hf) (Cardinal.aleph0 : Cardinal.{u})
    (hasCardinalLT_of_finite _ _ le_rfl)

/-- Restriction of scalars along the inverse of a ring isomorphism preserves finite
presentation. -/
public lemma finitePresentation_of_restrictScalarsEquivalence
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (e : R ≃+* S) (M : ModuleCat.{t} R)
    [Module.FinitePresentation R M] :
    Module.FinitePresentation S
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.functor.obj M) := by
  let M' := (ModuleCat.restrictScalars e.symm.toRingHom).obj M
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let (k : ℕ) : Module S (Fin k → R) := Module.compHom _ e.symm.toRingHom
  let φ (k : ℕ) : (Fin k → S) ≃ₗ[S] (Fin k → R) :=
    { toFun := fun x i => e.symm (x i)
      invFun := fun y i => e (y i)
      map_add' := fun x y => funext fun i => map_add e.symm _ _
      map_smul' := fun r x => funext fun i => map_mul e.symm _ _
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  let f' : (Fin n → S) →ₗ[S] M' :=
    { f with map_smul' := fun r x => f.map_smul (e.symm r) x } ∘ₗ φ n
  let g' : (Fin m → S) →ₗ[S] (Fin n → S) :=
    (φ n).symm ∘ₗ { g with map_smul' := fun r x => g.map_smul (e.symm r) x } ∘ₗ φ m
  have hf' : Function.Surjective f' := by
    intro x
    obtain ⟨y, hy⟩ := hf x
    exact ⟨(φ n).symm y, by change f ((φ n) ((φ n).symm y)) = x; simpa using hy⟩
  have hgf' : Function.Exact g' f' := by
    intro x
    change f (φ n x) = 0 ↔ ∃ y, (φ n).symm (g (φ m y)) = x
    rw [hgf]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(φ m).symm y, by simp [hy]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨φ m y, by simp⟩
  apply Module.finitePresentation_of_free_of_surjective f' hf'
  rw [LinearMap.exact_iff.mp hgf']
  exact Submodule.fg_range g'

/-- A finitely presented module is a finitely presentable object of its module category, with
the universe of the ring and the universe of the module independent. -/
public lemma finitePresentation_isFinitelyPresentable
    (A : Type u) [Ring A] (M : ModuleCat.{max u v} A)
    (hfp : Module.FinitePresentation A M) : IsFinitelyPresentable.{max u v} M := by
  let S := ULift.{max u v} A
  let e : A ≃+* S := ULift.ringEquiv.symm
  let E : ModuleCat.{max u v} S ≌ ModuleCat.{max u v} A :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have := hfp
  have : Module.FinitePresentation S (E.symm.functor.obj M) :=
    finitePresentation_of_restrictScalarsEquivalence e M
  have : Fact (Cardinal.aleph0 : Cardinal.{max u v}).IsRegular :=
    Cardinal.fact_isRegular_aleph0
  exact (isCardinalPresentable_iff_of_isEquivalence M Cardinal.aleph0 E.symm.functor).mp
    (finitePresentation_isFinitelyPresentable_sameUniverse S _)

end ModuleCat
