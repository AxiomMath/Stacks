module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Tower
public import StacksFrontier.RingTheory.Different.Formula.LocalizedCompleteIntersection

/-!
# Base change of a localized complete intersection

Let `R → A` be a ring map, let `h, f_1, …, f_n` be polynomials in `n` variables over `R`, and
write `h_A, f_{A,1}, …, f_{A,n}` for their images over `A`. Then

`A ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n) ≅ A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …, f_{A,n})`

as `A`-algebras, compatibly with the maps from the polynomial rings. In particular the Jacobian
determinant `det(∂f_i/∂x_j)` is carried to `det(∂f_{A,i}/∂x_j)`.

## Main definitions

* `Stacks.Discriminant.localizedCompleteIntersectionMap`: the `R`-algebra map
  `R[x, 1/h]/(f) → A[x, 1/h_A]/(f_A)` induced by `R → A`.
* `Stacks.Discriminant.localizedCompleteIntersectionCongr`: the identification of the algebras
  attached to equal data.
* `Stacks.Discriminant.localizedCompleteIntersectionBaseChange`: the `A`-algebra isomorphism
  `A ⊗_R R[x, 1/h]/(f) ≅ A[x, 1/h_A]/(f_A)`.

## Main results

* `Stacks.Discriminant.localizedCompleteIntersectionBaseChange_tmul_algebraMap`: the isomorphism
  sends `1 ⊗ p` to the image of `p` over `A`.
* `Stacks.Discriminant.localizedCompleteIntersectionBaseChange_tmul_det`: it sends the Jacobian
  determinant to the Jacobian determinant.
* `Stacks.Discriminant.localizedCompleteIntersection_algHom_ext`: algebra maps out of
  `R[x, 1/h]/(f)` are determined by the images of the variables.
* `Stacks.Discriminant.localizedCompleteIntersectionMap_comp`: the induced maps are compatible
  with composition `R → A' → A`.
* `Stacks.Discriminant.isPushout_localizedCompleteIntersection`: the square formed by `R → A`
  and the two localized complete intersections is a pushout.

## Implementation notes

Both directions of the isomorphism are built from universal properties: of the tensor product,
of the quotient, of the localization away from an element and of the polynomial ring. The two
composites are identities because they fix the images of the variables.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Stacks.Discriminant

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
  (h : MvPolynomial (Fin n) R) (f : Fin n → MvPolynomial (Fin n) R)

local notation "B₀" => localizedCompleteIntersection R n h f
local notation "B₁" => localizedCompleteIntersection A n (MvPolynomial.map (algebraMap R A) h)
  (fun i ↦ MvPolynomial.map (algebraMap R A) (f i))

/-- The image in `A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …, f_{A,n})` of a polynomial over `A` is its
class in the quotient of the localization. -/
theorem algebraMap_localizedCompleteIntersection_apply {S : Type*} [CommRing S] {n : ℕ}
    (h : MvPolynomial (Fin n) S) (f : Fin n → MvPolynomial (Fin n) S) (p : MvPolynomial (Fin n) S) :
    algebraMap (MvPolynomial (Fin n) S) (localizedCompleteIntersection S n h f) p =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) S) (Localization.Away h) p) :=
  rfl

/-- Two algebra maps out of `S[x_1, …, x_n, 1/h]/(f_1, …, f_n)` agree as soon as they agree on
the images of the variables. -/
theorem localizedCompleteIntersection_algHom_ext {S T : Type*} [CommRing S] [Semiring T]
    [Algebra S T] {n : ℕ} {h : MvPolynomial (Fin n) S} {f : Fin n → MvPolynomial (Fin n) S}
    {φ ψ : localizedCompleteIntersection S n h f →ₐ[S] T}
    (H : ∀ i, φ (algebraMap (MvPolynomial (Fin n) S) _ (MvPolynomial.X i)) =
      ψ (algebraMap (MvPolynomial (Fin n) S) _ (MvPolynomial.X i))) :
    φ = ψ :=
  Ideal.Quotient.algHom_ext _ (IsLocalization.algHom_ext (Submonoid.powers h)
    (MvPolynomial.algHom_ext H))

/-- Equal data give isomorphic localized complete intersections. -/
noncomputable def localizedCompleteIntersectionCongr {S : Type*} [CommRing S] {n : ℕ}
    {h h' : MvPolynomial (Fin n) S} {f f' : Fin n → MvPolynomial (Fin n) S} (hh : h = h')
    (hf : f = f') :
    localizedCompleteIntersection S n h f ≃ₐ[S] localizedCompleteIntersection S n h' f' := by
  subst hh hf
  exact AlgEquiv.refl

/-- The identification of equal data is compatible with the maps from the polynomial ring. -/
@[simp]
theorem localizedCompleteIntersectionCongr_algebraMap {S : Type*} [CommRing S] {n : ℕ}
    {h h' : MvPolynomial (Fin n) S} {f f' : Fin n → MvPolynomial (Fin n) S} (hh : h = h')
    (hf : f = f') (p : MvPolynomial (Fin n) S) :
    localizedCompleteIntersectionCongr hh hf (algebraMap (MvPolynomial (Fin n) S) _ p) =
      algebraMap (MvPolynomial (Fin n) S) _ p := by
  subst hh hf
  rfl

/-- The image of `h` in `A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …, f_{A,n})` is a unit. -/
theorem isUnit_algebraMap_map_localizedCompleteIntersection :
    IsUnit (((IsScalarTower.toAlgHom R (MvPolynomial (Fin n) A) B₁).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId R A))) h) := by
  show IsUnit (algebraMap (MvPolynomial (Fin n) A) B₁ (MvPolynomial.map (algebraMap R A) h))
  rw [algebraMap_localizedCompleteIntersection_apply]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

/-- The `R`-algebra map `R[x_1, …, x_n, 1/h] → A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …, f_{A,n})`
induced by `R → A`. -/
noncomputable def localizedCompleteIntersectionAwayMap : Localization.Away h →ₐ[R] B₁ :=
  IsLocalization.Away.liftAlgHom h (isUnit_algebraMap_map_localizedCompleteIntersection R A n h f)

/-- The map induced on localizations sends a polynomial to the image of its base change. -/
theorem localizedCompleteIntersectionAwayMap_algebraMap (p : MvPolynomial (Fin n) R) :
    localizedCompleteIntersectionAwayMap R A n h f
        (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h) p) =
      algebraMap (MvPolynomial (Fin n) A) B₁ (MvPolynomial.map (algebraMap R A) p) :=
  IsLocalization.Away.lift_eq h (isUnit_algebraMap_map_localizedCompleteIntersection R A n h f) p

/-- The `R`-algebra map `R[x_1, …, x_n, 1/h]/(f_1, …, f_n) → A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …,
f_{A,n})` induced by `R → A`. -/
noncomputable def localizedCompleteIntersectionMap : B₀ →ₐ[R] B₁ :=
  Ideal.Quotient.liftₐ _ (localizedCompleteIntersectionAwayMap R A n h f) (by
    intro a ha
    refine (Ideal.span_le (I := RingHom.ker _)).mpr ?_ ha
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, localizedRelations]
    change localizedCompleteIntersectionAwayMap R A n h f _ = 0
    rw [localizedCompleteIntersectionAwayMap_algebraMap,
      algebraMap_localizedCompleteIntersection_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩))

/-- The induced map sends the image of a polynomial `p` to the image of `p` over `A`. -/
@[simp]
theorem localizedCompleteIntersectionMap_algebraMap (p : MvPolynomial (Fin n) R) :
    localizedCompleteIntersectionMap R A n h f (algebraMap (MvPolynomial (Fin n) R) B₀ p) =
      algebraMap (MvPolynomial (Fin n) A) B₁ (MvPolynomial.map (algebraMap R A) p) := by
  rw [algebraMap_localizedCompleteIntersection_apply]
  exact localizedCompleteIntersectionAwayMap_algebraMap R A n h f p

/-- The `A`-algebra map `A[x_1, …, x_n] → A ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n)` sending each
variable to `1 ⊗ x_i`. -/
noncomputable def localizedCompleteIntersectionInvPoly :
    MvPolynomial (Fin n) A →ₐ[A] A ⊗[R] B₀ :=
  MvPolynomial.aeval fun i ↦
    (1 : A) ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) B₀ (MvPolynomial.X i)

/-- The inverse map on polynomials sends the base change of `p` to `1 ⊗ p`. -/
theorem localizedCompleteIntersectionInvPoly_map (p : MvPolynomial (Fin n) R) :
    localizedCompleteIntersectionInvPoly R A n h f (MvPolynomial.map (algebraMap R A) p) =
      (1 : A) ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) B₀ p := by
  rw [localizedCompleteIntersectionInvPoly, MvPolynomial.aeval_map_algebraMap]
  show MvPolynomial.aeval _ p =
    (Algebra.TensorProduct.includeRight.comp (IsScalarTower.toAlgHom R _ B₀)) p
  congr 1
  exact MvPolynomial.algHom_ext fun i ↦ by simp

/-- The image of `h_A` in `A ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n)` is a unit. -/
theorem isUnit_localizedCompleteIntersectionInvPoly :
    IsUnit (localizedCompleteIntersectionInvPoly R A n h f
      (MvPolynomial.map (algebraMap R A) h)) := by
  rw [localizedCompleteIntersectionInvPoly_map, algebraMap_localizedCompleteIntersection_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit h).map (Ideal.Quotient.mk _)).map
    (Algebra.TensorProduct.includeRight (R := R) (A := A))

/-- The `A`-algebra map `A[x_1, …, x_n, 1/h_A] → A ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
noncomputable def localizedCompleteIntersectionInvAway :
    Localization.Away (MvPolynomial.map (algebraMap R A) h) →ₐ[A] A ⊗[R] B₀ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_localizedCompleteIntersectionInvPoly R A n h f)

/-- The inverse map on the localization restricts to the inverse map on polynomials. -/
theorem localizedCompleteIntersectionInvAway_algebraMap (p : MvPolynomial (Fin n) A) :
    localizedCompleteIntersectionInvAway R A n h f
        (algebraMap (MvPolynomial (Fin n) A) (Localization.Away
          (MvPolynomial.map (algebraMap R A) h)) p) =
      localizedCompleteIntersectionInvPoly R A n h f p :=
  IsLocalization.Away.lift_eq _ (isUnit_localizedCompleteIntersectionInvPoly R A n h f) p

/-- The `A`-algebra map `A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …, f_{A,n}) →
A ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n)`, inverse to the base change map. -/
noncomputable def localizedCompleteIntersectionInv : B₁ →ₐ[A] A ⊗[R] B₀ :=
  Ideal.Quotient.liftₐ _ (localizedCompleteIntersectionInvAway R A n h f) (by
    intro a ha
    refine (Ideal.span_le (I := RingHom.ker _)).mpr ?_ ha
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, localizedRelations]
    change localizedCompleteIntersectionInvAway R A n h f _ = 0
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (localizedRelations R n h f)))
        (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h) (f i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [localizedCompleteIntersectionInvAway_algebraMap, localizedCompleteIntersectionInvPoly_map,
      algebraMap_localizedCompleteIntersection_apply, h0, TensorProduct.tmul_zero])

/-- The inverse map restricts to the inverse map on polynomials. -/
theorem localizedCompleteIntersectionInv_algebraMap (p : MvPolynomial (Fin n) A) :
    localizedCompleteIntersectionInv R A n h f (algebraMap (MvPolynomial (Fin n) A) B₁ p) =
      localizedCompleteIntersectionInvPoly R A n h f p := by
  rw [algebraMap_localizedCompleteIntersection_apply]
  exact localizedCompleteIntersectionInvAway_algebraMap R A n h f p

/-- The `A`-algebra map `A ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n) →
A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …, f_{A,n})`. -/
noncomputable def localizedCompleteIntersectionTensorMap : A ⊗[R] B₀ →ₐ[A] B₁ :=
  Algebra.TensorProduct.lift (Algebra.ofId A B₁) (localizedCompleteIntersectionMap R A n h f)
    fun _ _ ↦ Commute.all _ _

/-- **Base change of a localized complete intersection.** For a ring map `R → A`,
`A ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n) ≅ A[x_1, …, x_n, 1/h_A]/(f_{A,1}, …, f_{A,n})` as
`A`-algebras, where `h_A` and `f_{A,i}` are the images of `h` and `f_i` over `A`. -/
noncomputable def localizedCompleteIntersectionBaseChange : A ⊗[R] B₀ ≃ₐ[A] B₁ :=
  AlgEquiv.ofAlgHom (localizedCompleteIntersectionTensorMap R A n h f)
    (localizedCompleteIntersectionInv R A n h f)
    (by
      refine localizedCompleteIntersection_algHom_ext fun i ↦ ?_
      change localizedCompleteIntersectionTensorMap R A n h f
        (localizedCompleteIntersectionInv R A n h f
          (algebraMap (MvPolynomial (Fin n) A) B₁ (MvPolynomial.X i))) =
        algebraMap (MvPolynomial (Fin n) A) B₁ (MvPolynomial.X i)
      rw [localizedCompleteIntersectionInv_algebraMap, localizedCompleteIntersectionInvPoly,
        MvPolynomial.aeval_X, localizedCompleteIntersectionTensorMap,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul,
        localizedCompleteIntersectionMap_algebraMap, MvPolynomial.map_X])
    (by
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
      refine localizedCompleteIntersection_algHom_ext fun i ↦ ?_
      change localizedCompleteIntersectionInv R A n h f
        (localizedCompleteIntersectionTensorMap R A n h f
          ((1 : A) ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) B₀ (MvPolynomial.X i))) =
        (1 : A) ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) B₀ (MvPolynomial.X i)
      rw [localizedCompleteIntersectionTensorMap, Algebra.TensorProduct.lift_tmul, map_one,
        one_mul, localizedCompleteIntersectionMap_algebraMap,
        localizedCompleteIntersectionInv_algebraMap, localizedCompleteIntersectionInvPoly_map])

/-- The base change isomorphism sends `a ⊗ x` to `a • x_A`, where `x_A` is the image of `x`. -/
@[simp]
theorem localizedCompleteIntersectionBaseChange_tmul (a : A) (b : B₀) :
    localizedCompleteIntersectionBaseChange R A n h f (a ⊗ₜ[R] b) =
      a • localizedCompleteIntersectionMap R A n h f b :=
  (Algebra.TensorProduct.lift_tmul (Algebra.ofId A B₁) (localizedCompleteIntersectionMap R A n h f)
    (fun _ _ ↦ Commute.all _ _) a b).trans (Algebra.smul_def a _).symm

/-- The base change isomorphism sends `1 ⊗ p` to the image of `p` over `A`. -/
@[simp]
theorem localizedCompleteIntersectionBaseChange_tmul_algebraMap (p : MvPolynomial (Fin n) R) :
    localizedCompleteIntersectionBaseChange R A n h f
        ((1 : A) ⊗ₜ[R] algebraMap (MvPolynomial (Fin n) R) B₀ p) =
      algebraMap (MvPolynomial (Fin n) A) B₁ (MvPolynomial.map (algebraMap R A) p) := by
  rw [localizedCompleteIntersectionBaseChange_tmul, one_smul,
    localizedCompleteIntersectionMap_algebraMap]

/-- The base change isomorphism sends the Jacobian determinant `det(∂f_i/∂x_j)` to the Jacobian
determinant `det(∂f_{A,i}/∂x_j)`. -/
theorem localizedCompleteIntersectionBaseChange_tmul_det :
    localizedCompleteIntersectionBaseChange R A n h f
        ((1 : A) ⊗ₜ[R] Matrix.det fun i j : Fin n ↦
          algebraMap (MvPolynomial (Fin n) R) B₀ (MvPolynomial.pderiv j (f i))) =
      Matrix.det fun i j : Fin n ↦ algebraMap (MvPolynomial (Fin n) A) B₁
        (MvPolynomial.pderiv j (MvPolynomial.map (algebraMap R A) (f i))) := by
  let g : B₀ →+* B₁ := (localizedCompleteIntersectionBaseChange R A n h f).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := A)).toRingHom
  have hg : ∀ x, localizedCompleteIntersectionBaseChange R A n h f ((1 : A) ⊗ₜ[R] x) = g x :=
    fun _ ↦ rfl
  rw [hg]
  refine (g.map_det (Matrix.of fun i j : Fin n ↦
    algebraMap (MvPolynomial (Fin n) R) B₀ (MvPolynomial.pderiv j (f i)))).trans ?_
  congr 1
  refine Matrix.ext fun i j ↦ ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ← hg,
    localizedCompleteIntersectionBaseChange_tmul_algebraMap, MvPolynomial.pderiv_map]

/-- The square formed by `R → A` and the localized complete intersections over `R` and over `A`
is a pushout. -/
theorem isPushout_localizedCompleteIntersection :
    letI : Algebra B₀ B₁ := (localizedCompleteIntersectionMap R A n h f).toRingHom.toAlgebra
    haveI : IsScalarTower R B₀ B₁ := IsScalarTower.of_algebraMap_eq fun r ↦
      ((localizedCompleteIntersectionMap R A n h f).commutes r).symm
    Algebra.IsPushout R A B₀ B₁ := by
  let : Algebra B₀ B₁ := (localizedCompleteIntersectionMap R A n h f).toRingHom.toAlgebra
  refine ⟨IsBaseChange.of_equiv
    ((localizedCompleteIntersectionBaseChange R A n h f).toLinearEquiv.restrictScalars A) ?_⟩
  intro b
  simp only [LinearEquiv.restrictScalars_apply, AlgEquiv.toLinearEquiv_apply,
    localizedCompleteIntersectionBaseChange_tmul, one_smul]
  rfl

/-- **Transitivity.** For ring maps `R → A' → A`, the map induced by `R → A` is the composite of
the maps induced by `R → A'` and `A' → A`, up to the identification of the data
`(h_{A'})_A = h_A` and `(f_{A',i})_A = f_{A,i}`. -/
theorem localizedCompleteIntersectionMap_comp (A' : Type*) [CommRing A'] [Algebra R A']
    [Algebra A' A] [IsScalarTower R A' A] :
    ((localizedCompleteIntersectionMap A' A n (MvPolynomial.map (algebraMap R A') h)
        (fun i ↦ MvPolynomial.map (algebraMap R A') (f i))).restrictScalars R).comp
        (localizedCompleteIntersectionMap R A' n h f) =
      ((localizedCompleteIntersectionCongr
        (by rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq])
        (funext fun i ↦ by rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq])).toAlgHom
          |>.restrictScalars R).comp
        (localizedCompleteIntersectionMap R A n h f) := by
  refine localizedCompleteIntersection_algHom_ext fun i ↦ ?_
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    localizedCompleteIntersectionMap_algebraMap, MvPolynomial.map_X]
  exact (localizedCompleteIntersectionCongr_algebraMap _ _ _).symm

end Stacks.Discriminant

end
