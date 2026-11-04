module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.AffineChart
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerAlgebra
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Base change of the standard tamely ramified algebra

For a ring map `R → T`, `φ ∈ R` and `e : ℕ`, the localized standard tamely ramified algebra
`A[x]/(x^e - φ)_φ` ([Stacks, Tag 0EYF]) commutes with base change:
`T ⊗_R R[x]/(x^e - φ)_φ ≅ T[x]/(x^e - φ)_φ` as `T`-algebras.

## Main results

* `AlgebraicGeometry.Abhyankar.kummerAwayBaseChange`: the isomorphism.
* `AlgebraicGeometry.Abhyankar.kummerAwayPiBaseChange`: its version for finite products.

## References

* [Stacks Project, Tag 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

variable {R : Type u} [CommRing R] (φ : R) (e : ℕ) (T : Type u) [CommRing T] [Algebra R T]

/-- The map `R[x]/(x^e - φ) → T[x]/(x^e - φ)` induced by `R → T`. -/
def standardMap : standardTamelyRamifiedAlgebra R φ e →+*
    standardTamelyRamifiedAlgebra T (algebraMap R T φ) e :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (Polynomial.mapRingHom (algebraMap R T))) (by
    intro p hp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/-- `standardMap` sends the image of `r ∈ R` to the image of `algebraMap R T r`. -/
lemma standardMap_algebraMap (r : R) :
    standardMap φ e T (algebraMap R _ r) = algebraMap T _ (algebraMap R T r) := by
  rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq]
  show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk]
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
  rfl

/-- `standardMap` sends the class of `x` to the class of `x`. -/
lemma standardMap_root :
    standardMap φ e T (Ideal.Quotient.mk _ X) = Ideal.Quotient.mk _ X := by
  show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk]
  simp

/-- The map `R[x]/(x^e - φ)_φ → T[x]/(x^e - φ)_φ` induced by `R → T`. -/
def kummerAwayMap : Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ) →+*
    Localization.Away (algebraMap T (standardTamelyRamifiedAlgebra T (algebraMap R T φ) e)
      (algebraMap R T φ)) :=
  IsLocalization.Away.lift (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ)
    (g := (algebraMap _ (Localization.Away (algebraMap T
      (standardTamelyRamifiedAlgebra T (algebraMap R T φ) e) (algebraMap R T φ)))).comp
      (standardMap φ e T)) (by
      rw [RingHom.comp_apply, standardMap_algebraMap]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- On elements of `R[x]/(x^e - φ)`, `kummerAwayMap` is given by `standardMap`. -/
lemma kummerAwayMap_algebraMap (c : standardTamelyRamifiedAlgebra R φ e) :
    kummerAwayMap φ e T (algebraMap _ _ c) = algebraMap _ _ (standardMap φ e T c) :=
  IsLocalization.Away.lift_eq _ _ c

/-- The image of `root R φ e` in `R[x]/(x^e - φ)_φ` has `e`-th power `φ`. -/
lemma kummerAway_root_pow :
    (algebraMap _ (Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ))
      (root R φ e)) ^ e = algebraMap R _ φ := by
  rw [← map_pow, root_pow, ← IsScalarTower.algebraMap_apply]

/-- The element `1 ⊗ root R φ e` of `T ⊗_R R[x]/(x^e - φ)_φ` has `e`-th power the image of `φ`. -/
lemma one_tmul_root_pow : ((1 : T) ⊗ₜ[R] algebraMap _
      (Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ)) (root R φ e)) ^ e =
    algebraMap T _ (algebraMap R T φ) := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, kummerAway_root_pow,
    ← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R T (T ⊗[R] Localization.Away
      (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ))]

/-- The map `T[x]/(x^e - φ) → T ⊗_R R[x]/(x^e - φ)_φ`. -/
def standardInv : standardTamelyRamifiedAlgebra T (algebraMap R T φ) e →+*
    T ⊗[R] Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ) :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (algebraMap T _)
    ((1 : T) ⊗ₜ[R] algebraMap _ _ (root R φ e))) (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, coe_eval₂RingHom, eval₂_sub, eval₂_X_pow, eval₂_C, one_tmul_root_pow, sub_self,
        mul_zero])

/-- `standardInv` sends the image of `t ∈ T` to the image of `t`. -/
lemma standardInv_algebraMap (t : T) :
    standardInv φ e T (algebraMap T _ t) = algebraMap T _ t := by
  show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (Polynomial.C t)) = _
  rw [Ideal.Quotient.lift_mk]
  simp

/-- `standardInv` sends the class of `x` to `1 ⊗ root R φ e`. -/
lemma standardInv_root :
    standardInv φ e T (root T (algebraMap R T φ) e) =
      (1 : T) ⊗ₜ[R] algebraMap _ _ (root R φ e) := by
  show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk]
  simp

/-- The inverse map `T[x]/(x^e - φ)_φ → T ⊗_R R[x]/(x^e - φ)_φ`. -/
def kummerAwayInv : Localization.Away (algebraMap T
      (standardTamelyRamifiedAlgebra T (algebraMap R T φ) e) (algebraMap R T φ)) →+*
    T ⊗[R] Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ) :=
  IsLocalization.Away.lift (algebraMap T (standardTamelyRamifiedAlgebra T (algebraMap R T φ) e)
    (algebraMap R T φ)) (g := standardInv φ e T) (by
      rw [standardInv_algebraMap, ← IsScalarTower.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply R
          (standardTamelyRamifiedAlgebra R φ e)]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away
        (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ))
        (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ)).map
          (Algebra.TensorProduct.includeRight (R := R) (A := T)))

/-- On elements of `T[x]/(x^e - φ)`, `kummerAwayInv` is given by `standardInv`. -/
lemma kummerAwayInv_algebraMap (c : standardTamelyRamifiedAlgebra T (algebraMap R T φ) e) :
    kummerAwayInv φ e T (algebraMap _ _ c) = standardInv φ e T c :=
  IsLocalization.Away.lift_eq _ _ c

/-- **Base change of the standard tamely ramified algebra.** For an `R`-algebra `T`,
`T ⊗_R R[x]/(x^e - φ)_φ ≅ T[x]/(x^e - φ)_φ` as `T`-algebras. -/
def kummerAwayBaseChange :
    T ⊗[R] Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ e) φ) ≃ₐ[T]
      Localization.Away (algebraMap T (standardTamelyRamifiedAlgebra T (algebraMap R T φ) e)
        (algebraMap R T φ)) := by
  let CR := standardTamelyRamifiedAlgebra R φ e
  let CT := standardTamelyRamifiedAlgebra T (algebraMap R T φ) e
  let KR := Localization.Away (algebraMap R CR φ)
  let KT := Localization.Away (algebraMap T CT (algebraMap R T φ))
  let Fr : KR →ₐ[R] KT :=
    { kummerAwayMap φ e T with
      commutes' := fun r ↦ by
        change kummerAwayMap φ e T (algebraMap R KR r) = _
        rw [IsScalarTower.algebraMap_apply R CR KR, kummerAwayMap_algebraMap,
          standardMap_algebraMap]
        exact (IsScalarTower.algebraMap_apply T CT KT _).symm.trans
          (IsScalarTower.algebraMap_apply R T KT r).symm }
  let F : T ⊗[R] KR →ₐ[T] KT :=
    Algebra.TensorProduct.lift (Algebra.ofId T KT) Fr (fun _ _ ↦ Commute.all _ _)
  let G : KT →ₐ[T] T ⊗[R] KR :=
    { kummerAwayInv φ e T with
      commutes' := fun t ↦ by
        change kummerAwayInv φ e T (algebraMap T KT t) = _
        rw [IsScalarTower.algebraMap_apply T CT KT, kummerAwayInv_algebraMap,
          standardInv_algebraMap] }
  have hFr : ∀ k, F (1 ⊗ₜ k) = kummerAwayMap φ e T k := fun k ↦ by
    simp [F, Algebra.TensorProduct.lift_tmul, Fr]
  have hFG : F.comp G = AlgHom.id T KT := by
    apply AlgHom.coe_ringHom_injective
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap T CT (algebraMap R T φ)))
      (Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun t ↦ ?_) ?_))
    · change F (kummerAwayInv φ e T (algebraMap CT KT (Ideal.Quotient.mk _ (C t)))) =
        algebraMap CT KT (Ideal.Quotient.mk _ (C t))
      rw [kummerAwayInv_algebraMap]
      change F (standardInv φ e T (algebraMap T CT t)) = algebraMap CT KT (algebraMap T CT t)
      rw [standardInv_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply T CT KT]
    · change F (kummerAwayInv φ e T (algebraMap CT KT (root T (algebraMap R T φ) e))) =
        algebraMap CT KT (root T (algebraMap R T φ) e)
      rw [kummerAwayInv_algebraMap, standardInv_root, hFr, kummerAwayMap_algebraMap]
      exact congrArg _ (standardMap_root φ e T)
  have hGF : G.comp F = AlgHom.id T (T ⊗[R] KR) := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AlgHom.coe_ringHom_injective
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R CR φ))
        (Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun r ↦ ?_) ?_))
      · change G (F (1 ⊗ₜ algebraMap CR KR (algebraMap R CR r))) =
          1 ⊗ₜ algebraMap CR KR (algebraMap R CR r)
        rw [← IsScalarTower.algebraMap_apply R CR KR, ← Algebra.TensorProduct.algebraMap_apply',
          IsScalarTower.algebraMap_apply R T (T ⊗[R] KR), AlgHom.commutes, AlgHom.commutes]
      · change G (F (1 ⊗ₜ algebraMap CR KR (root R φ e))) = 1 ⊗ₜ algebraMap CR KR (root R φ e)
        rw [hFr, kummerAwayMap_algebraMap]
        change kummerAwayInv φ e T (algebraMap CT KT (standardMap φ e T (root R φ e))) = _
        rw [kummerAwayInv_algebraMap]
        exact (congrArg _ (standardMap_root φ e T)).trans (standardInv_root φ e T)
  exact AlgEquiv.ofAlgHom F G hFG hGF

/-- **Base change of a finite product of standard tamely ramified algebras.** -/
def kummerAwayPiBaseChange {n : ℕ} (e : Fin n → ℕ) :
    T ⊗[R] (∀ i, Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ (e i)) φ)) ≃ₐ[T]
      ∀ i, Localization.Away
        (algebraMap T (standardTamelyRamifiedAlgebra T (algebraMap R T φ) (e i))
          (algebraMap R T φ)) :=
  (Algebra.TensorProduct.piRight R T T _).trans
    (AlgEquiv.piCongrRight fun i ↦ kummerAwayBaseChange φ (e i) T)

end AlgebraicGeometry.Abhyankar
