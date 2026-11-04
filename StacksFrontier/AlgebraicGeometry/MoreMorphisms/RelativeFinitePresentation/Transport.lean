module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.RingTheory.FinitePresentation.Relative

/-!
# Transport of relative finite presentation along equivalences

Relative finite presentation of a module is a property of its isomorphism class, and more
generally it transports along a ring isomorphism of the ambient algebra together with a
compatible additive isomorphism of the modules.

## Main results

* `Module.FinitePresentationRel.of_linearEquiv`: relative finite presentation transports along
  an `A`-linear equivalence of `A`-modules.
* `Module.FinitePresentationRel.of_semilinearEquiv`: relative finite presentation transports
  along an `R`-algebra equivalence `A ≃ₐ[R] B` together with an additive equivalence of the
  modules that is semilinear over it.

## Implementation notes

A witness for `Module.FinitePresentationRel R A M` is a surjection `α : R[x_1, …, x_n] → A`
together with finite presentation of `M` over `R[x_1, …, x_n]` through `α`. Both statements keep
the same `n`, composing `α` with the algebra equivalence in the semilinear case, and transport
the finite presentation with `LinearEquiv.finitePresentation_iff`.
-/

@[expose] public section

universe u

namespace Module.FinitePresentationRel

/-- Transport of relative finite presentation along a semilinear equivalence over an algebra
equivalence. -/
private theorem of_semilinearEquiv_aux {R A B M N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (eA : A ≃ₐ[R] B) (eM : M ≃+ N) (he : ∀ a m, eM (a • m) = eA a • eM m)
    (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R B N := by
  obtain ⟨n, α, hα, hfp⟩ := h
  let β : MvPolynomial (Fin n) R →ₐ[R] B := eA.toAlgHom.comp α
  refine ⟨n, β, eA.surjective.comp hα, ?_⟩
  let _ : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
  let _ : Module (MvPolynomial (Fin n) R) N := Module.compHom N β.toRingHom
  let e : M ≃ₗ[MvPolynomial (Fin n) R] N :=
    { eM with map_smul' := fun p m => he (α p) m }
  exact (LinearEquiv.finitePresentation_iff e).mp hfp

/-- Relative finite presentation transports along an `A`-linear equivalence. -/
theorem of_linearEquiv {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R A N :=
  of_semilinearEquiv_aux (AlgEquiv.refl) e.toAddEquiv e.map_smul h

/-- Relative finite presentation transports along an `R`-algebra equivalence of the ambient
algebras together with an additive equivalence of the modules that is semilinear over it. -/
theorem of_semilinearEquiv {R A B M N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (eA : A ≃ₐ[R] B) (eM : M ≃+ N) (he : ∀ a m, eM (a • m) = eA a • eM m)
    (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R B N :=
  of_semilinearEquiv_aux eA eM he h

end Module.FinitePresentationRel
