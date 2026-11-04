module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TotallySplit
public import StacksCore.Tactic.StacksAttribute

/-!
# A finite étale algebra over a field splits after a finite separable extension

Let `K` be a field and `A` a finite étale `K`-algebra of dimension `d`. Then there is a finite
separable extension `K'/K` over which `A` becomes totally split: `K' ⊗_K A ≅ K'^d` as
`K'`-algebras. Equivalently, `A` acquires exactly `d` pairwise distinct `K'`-points after that
extension; geometrically, a finite étale morphism of degree `d` to `Spec K` acquires `d`
pairwise distinct sections after a finite separable extension of `K`.

## Main results

* `Stacks.TotallySplit.exists_finiteSeparable_isFiniteSplit_tensorProduct`: a finite étale
  algebra over a field becomes totally split after a finite separable extension of that field.
* `Stacks.TotallySplit.nonempty_algEquiv_fun_of_isFiniteSplit`: when it does, the number of
  factors is the dimension of the algebra over the original field.
* `Stacks.TotallySplit.exists_injective_algHom_of_algEquiv_fun`: a totally split algebra with
  `d` factors has `d` pairwise distinct rational points.
* `Stacks.TotallySplit.exists_finiteSeparable_injective_algHom`: a finite étale algebra of
  dimension `d` over a field has `d` pairwise distinct rational points after a finite separable
  extension.

## References

* [Stacks Project, Tag 00U3](https://stacks.math.columbia.edu/tag/00U3)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.TotallySplit

/-- A finite étale algebra over a field becomes totally split after a finite separable extension
of that field. -/
theorem exists_finiteSeparable_isFiniteSplit_tensorProduct {K A : Type u} [Field K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (_ : Algebra.IsSeparable K K'), Algebra.IsFiniteSplit K' (K' ⊗[K] A) := by
  obtain ⟨T, _, _, hff, hfinT, hetT, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := K) (S := A)
      (n := Module.finrank K A) (by simp [Module.rankAtStalk_eq_finrank_of_free])
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K T).mp hetT
  have hT : Nontrivial T := by
    have h1 : Nontrivial (T ⊗[K] K) := inferInstance
    exact (TensorProduct.rid K T).toEquiv.symm.nontrivial
  have : Nonempty I := by
    by_contra h
    simp only [not_nonempty_iff] at h
    have : Subsingleton (∀ i, L i) := inferInstance
    exact (not_subsingleton T) e.toEquiv.subsingleton
  obtain ⟨i⟩ := ‹Nonempty I›
  let f : T →ₐ[K] L i := (Pi.evalAlgHom K _ i).comp e.toAlgHom
  algebraize [f.toRingHom]
  have : IsScalarTower K T (L i) := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  exact ⟨L i, inferInstance, inferInstance, (hL i).1, (hL i).2,
    Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange K T (L i) (L i) A)⟩

/-- The number of factors of a totally split base change is the dimension of the algebra over
the original field. -/
theorem nonempty_algEquiv_fun_of_isFiniteSplit {K K' A : Type u} [Field K] [Field K']
    [Algebra K K'] [CommRing A] [Algebra K A] [Module.Finite K A]
    [Algebra.IsFiniteSplit K' (K' ⊗[K] A)] :
    Nonempty ((K' ⊗[K] A) ≃ₐ[K'] (Fin (Module.finrank K A) → K')) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K' (K' ⊗[K] A)
  have h : n = Module.finrank K A := by
    have h1 : Module.finrank K' (K' ⊗[K] A) = Module.finrank K A := Module.finrank_baseChange
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi] at h1
    simpa using h1
  exact ⟨h ▸ e⟩

/-- An algebra isomorphic to `d` copies of the base field has `d` pairwise distinct rational
points. -/
theorem exists_injective_algHom_of_algEquiv_fun {K' R : Type u} [Field K'] [CommRing R]
    [Algebra K' R] (d : ℕ) (e : R ≃ₐ[K'] (Fin d → K')) :
    ∃ w : Fin d → (R →ₐ[K'] K'), Function.Injective w := by
  refine ⟨fun k ↦ (Pi.evalAlgHom K' _ k).comp e.toAlgHom, fun k l hkl ↦ ?_⟩
  by_contra hne
  have hall : ∀ x : R, e x k = e x l := fun x ↦
    congrArg (fun φ : R →ₐ[K'] K' ↦ φ x) hkl
  have h := hall (e.symm (Pi.single k 1))
  rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h
  exact one_ne_zero h

/-- A finite étale algebra of dimension `d` over a field has `d` pairwise distinct rational
points after a finite separable extension of that field. -/
theorem exists_finiteSeparable_injective_algHom {K A : Type u} [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (_ : Algebra.IsSeparable K K')
      (w : Fin (Module.finrank K A) → ((K' ⊗[K] A) →ₐ[K'] K')), Function.Injective w := by
  obtain ⟨K', _, _, _, _, hsplit⟩ :=
    exists_finiteSeparable_isFiniteSplit_tensorProduct (K := K) (A := A)
  obtain ⟨e⟩ := nonempty_algEquiv_fun_of_isFiniteSplit (K := K) (K' := K') (A := A)
  obtain ⟨w, hw⟩ := exists_injective_algHom_of_algEquiv_fun (Module.finrank K A) e
  exact ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, w, hw⟩

end Stacks.TotallySplit

end
