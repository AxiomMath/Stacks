module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Etale.Basic

/-!
# Weak étaleness is invariant under isomorphisms of algebras

A weakly étale algebra stays weakly étale when the algebra is replaced by an isomorphic one
(`Algebra.WeaklyEtale.of_equiv`), and, more generally, when both the base ring and the algebra
are replaced by isomorphic rings compatibly with the structure maps
(`Algebra.WeaklyEtale.of_ringEquiv`).

## References

* [Stacks Project, Tag 092B](https://stacks.math.columbia.edu/tag/092B)
-/

@[expose] public section

namespace Algebra.WeaklyEtale

/-- Weak étaleness transfers along an isomorphism of algebras. -/
theorem of_equiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [WeaklyEtale R A] (e : A ≃ₐ[R] B) : WeaklyEtale R B := by
  let m := (Algebra.TensorProduct.congr e e).toAlgHom
  have hcomm : (Algebra.TensorProduct.lmul' R (S := B)).comp m =
      e.toAlgHom.comp (Algebra.TensorProduct.lmul' R (S := A)) := by
    apply Algebra.TensorProduct.ext <;> ext a <;> simp [m]
  have hf : (e.toAlgHom.comp (Algebra.TensorProduct.lmul' R (S := A))).Flat :=
    RingHom.Flat.comp (WeaklyEtale.flat_lmul' R A) (.of_bijective e.bijective)
  rw [← hcomm] at hf
  exact ⟨.of_linearEquiv e.symm.toLinearEquiv,
    (RingHom.Flat.comp_iff_of_bijective_right (Algebra.TensorProduct.congr e e).bijective).mp hf⟩

/-- Weak étaleness transfers along isomorphisms of the base ring and of the algebra that are
compatible with the structure maps. -/
theorem of_ringEquiv {X Y X' Y' : Type*} [CommRing X] [CommRing Y] [CommRing X'] [CommRing Y']
    [Algebra X Y] [Algebra X' Y'] [WeaklyEtale X Y] (σ : X' ≃+* X) (ψ : Y' ≃+* Y)
    (h : ∀ x, ψ (algebraMap X' Y' x) = algebraMap X Y (σ x)) : WeaklyEtale X' Y' := by
  let : Algebra X' X := σ.toRingHom.toAlgebra
  let : Algebra X' Y := ((algebraMap X Y).comp σ.toRingHom).toAlgebra
  have : IsScalarTower X' X Y := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale X' X :=
    Algebra.Etale.of_equiv (AlgEquiv.ofRingEquiv (f := σ) fun _ => rfl)
  have : WeaklyEtale X' Y := WeaklyEtale.trans X' X Y
  exact of_equiv (AlgEquiv.ofRingEquiv (f := ψ.symm) fun x => ψ.symm_apply_eq.mpr (h x).symm)

end Algebra.WeaklyEtale
