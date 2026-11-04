module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.RingTheory.TensorAlgebra.Localization

/-!
# Base change of symmetric powers

Let `A` be a commutative ring, `B` an `A`-algebra and `M` an `A`-module. This file proves that
the formation of symmetric powers commutes with base change:

`B ⊗[A] Symⁿ_A(M) ≃ₗ[B] Symⁿ_B(B ⊗[A] M)`.

## Main results

* `Submodule.baseChange_mul`, `Submodule.baseChange_one`, `Submodule.baseChange_pow`: base change
  of submodules of an algebra is multiplicative, hence commutes with taking powers.
* `SymPow.symAlgBaseChangeEquiv`: the base change isomorphism of symmetric algebras
  `B ⊗[A] Sym_A(M) ≃ₐ[B] Sym_B(B ⊗[A] M)`.
* `SymPow.baseChangeEquiv`: the base change isomorphism of the `n`-th symmetric powers.

The same comparison is also given in a second form, in `namespace SymmetricAlgebra`:

* `SymmetricAlgebra.symmetricPowerProj`: the projection `Sym_R(M) → Symⁿ_R(M)` coming from the
  graded decomposition `SymmetricAlgebra.gradedAlgebra`.
* `SymmetricAlgebra.symmetricAlgebraBaseChange`: a base-change comparison of symmetric algebras,
  chosen from `SymmetricAlgebra.exists_algEquiv_baseChange`, with
  `SymmetricAlgebra.symmetricAlgebraBaseChange_ι` its value on degree-one generators.
* `SymmetricAlgebra.symmetricPowerBaseChange`: the degreewise comparison
  `A ⊗_R Symⁿ_R(M) ≃ₗ[A] Symⁿ_A(A ⊗_R M)`, with
  `SymmetricAlgebra.symmetricPowerBaseChange_tmul_prod_ι` its value on products of degree-one
  generators.

## Implementation notes

`SymPow.symmetricPower n A M` is the `n`-th power of the submodule
`LinearMap.range (SymmetricAlgebra.ι A M)` of `SymmetricAlgebra A M`, so there are two things to
do.

First, the symmetric algebra commutes with base change, by a comparison of universal properties:
`Sym_A(M)` is the universal commutative `A`-algebra receiving a linear map from `M`, and
`B ⊗[A] -` is left adjoint to restriction of scalars along `A → B`. The two mutually inverse
algebra maps are built with `SymmetricAlgebra.lift` and `Algebra.TensorProduct.liftEquivRight`;
the latter needs `Sym_B(B ⊗[A] M)` to be an `A`-algebra, which is arranged by `Algebra.compHom`
as a local instance (it occurs in none of the statements below).

Second, the base change isomorphism must be seen to respect the grading. Since
`Submodule.baseChange` turns a product of submodules into the product of their base changes, the
image of `(SymPow.symmetricPower n A M).baseChange B` is determined by the degree-one case, where
it is a short span computation.

The remaining input is that the natural map `B ⊗[A] p → p.baseChange B` is injective when `p` is
a piece of a decomposition of the ambient module; this is Mathlib's
`DirectSum.toBaseChange_bijective`, applied to the graded decomposition of the symmetric algebra
(`SymmetricAlgebra.gradedAlgebra`). Some such input is indispensable: tensoring does not preserve
injections in general, and it is exactly the splitting provided by the grading that makes
`B ⊗[A] Symⁿ_A(M)` a submodule of `B ⊗[A] Sym_A(M)`.

The second form factors through `SymmetricAlgebra.symmetricAlgebraBaseChange` rather than
through `Submodule.baseChange_pow`, and its injectivity comes from the graded projection
`SymmetricAlgebra.symmetricPowerProj` splitting the inclusion of the degree-`n` piece.

The scalar actions of `SymPow.towerRestrict` are spelled out with `Algebra.toSMul`, because the
`SMul B (Sym_B(B ⊗[A] M))` found by elaboration is the one coming from `RingCon.Quotient` rather
than from the algebra structure, and instance search does not see through the difference.
-/

@[expose] public section

open scoped TensorProduct Pointwise

namespace Submodule

section BaseChangeMul

variable {R S : Type*} (A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [CommSemiring S] [Algebra R S] (p q : Submodule R S)

/-- Base change of submodules of an `R`-algebra turns a product of submodules into the product of
their base changes. -/
theorem baseChange_mul : (p * q).baseChange A = p.baseChange A * q.baseChange A := by
  have himg : TensorProduct.mk R A S 1 '' ((p : Set S) * (q : Set S)) =
      TensorProduct.mk R A S 1 '' (p : Set S) * TensorProduct.mk R A S 1 '' (q : Set S) :=
    Set.image_mul (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S)
  rw [mul_eq_span_mul_set, baseChange_span, baseChange_eq_span, map_coe, baseChange_eq_span,
    map_coe, span_mul_span, himg]

/-- Base change of submodules of an `R`-algebra sends the unit submodule to the unit
submodule. -/
@[simp]
theorem baseChange_one : (1 : Submodule R S).baseChange A = 1 := by
  rw [one_eq_span, baseChange_span, one_eq_span]
  simp [Algebra.TensorProduct.one_def]

/-- Base change of submodules of an `R`-algebra commutes with taking powers. -/
theorem baseChange_pow (n : ℕ) : (p ^ n).baseChange A = p.baseChange A ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, baseChange_mul, ih, pow_succ]

end BaseChangeMul

end Submodule

/-- `ι (a ⊗ m) = a • ι (1 ⊗ m)` in the symmetric algebra of a base change. -/
private theorem ι_tmul_eq_smul_ι_one_tmul {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {M : Type*} [AddCommGroup M] [Module R M] (a : A) (m : M) :
    SymmetricAlgebra.ι A (A ⊗[R] M) (a ⊗ₜ[R] m) =
      a • SymmetricAlgebra.ι A (A ⊗[R] M) (1 ⊗ₜ[R] m) := by
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

namespace SymPow

variable {A : Type*} [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
  (M : Type*) [AddCommGroup M] [Module A M]

/-- The `A`-algebra structure on `Sym_B(B ⊗[A] M)` obtained by restricting scalars along
`A → B`. -/
local instance algebraRestrict : Algebra A (SymmetricAlgebra B (B ⊗[A] M)) :=
  Algebra.compHom _ (algebraMap A B)

/-- `Sym_B(B ⊗[A] M)` is an `A`-`B`-scalar tower for `SymPow.algebraRestrict`. -/
local instance towerRestrict :
    @IsScalarTower A B (SymmetricAlgebra B (B ⊗[A] M)) Algebra.toSMul Algebra.toSMul
      Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The `A`-linear map `M → Sym_B(B ⊗[A] M)`, `m ↦ 1 ⊗ m`. -/
noncomputable def toSymBaseChange : M →ₗ[A] SymmetricAlgebra B (B ⊗[A] M) where
  toFun m := SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] m)
  map_add' x y := by rw [TensorProduct.tmul_add, map_add]
  map_smul' a x := by
    change SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] (a • x)) =
      algebraMap A B a • SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] x)
    rw [← map_smul]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

/-- `SymPow.toSymBaseChange B M m = ι (1 ⊗ m)`. -/
@[simp]
theorem toSymBaseChange_apply (m : M) :
    toSymBaseChange B M m = SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] m) := rfl

/-- The forward algebra map `B ⊗[A] Sym_A(M) → Sym_B(B ⊗[A] M)`. -/
noncomputable def symAlgBaseChangeHom :
    B ⊗[A] SymmetricAlgebra A M →ₐ[B] SymmetricAlgebra B (B ⊗[A] M) :=
  Algebra.TensorProduct.liftEquivRight A B (SymmetricAlgebra A M)
    (SymmetricAlgebra B (B ⊗[A] M)) (SymmetricAlgebra.lift (toSymBaseChange B M))

/-- The forward map sends `b ⊗ x` to `b` times the image of `x` under the lift of
`SymPow.toSymBaseChange`. -/
@[simp]
theorem symAlgBaseChangeHom_tmul (b : B) (x : SymmetricAlgebra A M) :
    symAlgBaseChangeHom B M (b ⊗ₜ[A] x) =
      algebraMap B (SymmetricAlgebra B (B ⊗[A] M)) b *
        SymmetricAlgebra.lift (toSymBaseChange B M) x := rfl

/-- The backward algebra map `Sym_B(B ⊗[A] M) → B ⊗[A] Sym_A(M)`. -/
noncomputable def symAlgBaseChangeInv :
    SymmetricAlgebra B (B ⊗[A] M) →ₐ[B] B ⊗[A] SymmetricAlgebra A M :=
  SymmetricAlgebra.lift (LinearMap.baseChange B (SymmetricAlgebra.ι A M))

/-- The backward map sends `ι x` to the base change of `ι` applied to `x`. -/
@[simp]
theorem symAlgBaseChangeInv_ι (x : B ⊗[A] M) :
    symAlgBaseChangeInv B M (SymmetricAlgebra.ι B (B ⊗[A] M) x) =
      LinearMap.baseChange B (SymmetricAlgebra.ι A M) x :=
  SymmetricAlgebra.lift_ι_apply _ x

/-- The backward map undoes the lift of `SymPow.toSymBaseChange`. This is the universal property
of `Sym_A(M)`: both sides are `A`-algebra maps agreeing on the image of `M`. -/
theorem symAlgBaseChangeInv_lift (x : SymmetricAlgebra A M) :
    symAlgBaseChangeInv B M (SymmetricAlgebra.lift (toSymBaseChange B M) x) = 1 ⊗ₜ[A] x := by
  have key : ((symAlgBaseChangeInv B M).restrictScalars A).comp
      (SymmetricAlgebra.lift (toSymBaseChange B M)) =
      (Algebra.TensorProduct.includeRight :
        SymmetricAlgebra A M →ₐ[A] B ⊗[A] SymmetricAlgebra A M) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    show symAlgBaseChangeInv B M (SymmetricAlgebra.lift (toSymBaseChange B M)
      (SymmetricAlgebra.ι A M m)) = 1 ⊗ₜ[A] SymmetricAlgebra.ι A M m
    rw [SymmetricAlgebra.lift_ι_apply, toSymBaseChange_apply, symAlgBaseChangeInv_ι,
      LinearMap.baseChange_tmul]
  exact DFunLike.congr_fun key x

/-- The base change isomorphism for symmetric algebras:
`B ⊗[A] Sym_A(M) ≃ₐ[B] Sym_B(B ⊗[A] M)`. -/
noncomputable def symAlgBaseChangeEquiv :
    B ⊗[A] SymmetricAlgebra A M ≃ₐ[B] SymmetricAlgebra B (B ⊗[A] M) :=
  AlgEquiv.ofAlgHom (symAlgBaseChangeHom B M) (symAlgBaseChangeInv B M)
    (by
      refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
      change symAlgBaseChangeHom B M (symAlgBaseChangeInv B M
        (SymmetricAlgebra.ι B (B ⊗[A] M) x)) = SymmetricAlgebra.ι B (B ⊗[A] M) x
      induction x with
      | zero => rw [map_zero, map_zero, map_zero]
      | tmul b m =>
          rw [symAlgBaseChangeInv_ι, LinearMap.baseChange_tmul, symAlgBaseChangeHom_tmul,
            SymmetricAlgebra.lift_ι_apply, toSymBaseChange_apply, ← Algebra.smul_def,
            ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy])
    (by
      refine Algebra.TensorProduct.ext' fun b x => ?_
      change symAlgBaseChangeInv B M (symAlgBaseChangeHom B M (b ⊗ₜ[A] x)) = b ⊗ₜ[A] x
      rw [symAlgBaseChangeHom_tmul, map_mul, AlgHom.commutes, symAlgBaseChangeInv_lift]
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul])

/-- The base change isomorphism of symmetric algebras agrees with
`SymPow.symAlgBaseChangeHom`. -/
@[simp]
theorem symAlgBaseChangeEquiv_apply (x : B ⊗[A] SymmetricAlgebra A M) :
    symAlgBaseChangeEquiv B M x = symAlgBaseChangeHom B M x := rfl

/-- The degree-one part of `Sym_B(B ⊗[A] M)` is spanned by the image of `M`. -/
theorem span_range_ι_one_tmul :
    Submodule.span B
        (Set.range fun m : M => SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] m)) =
      LinearMap.range (SymmetricAlgebra.ι B (B ⊗[A] M)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨m, rfl⟩
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨x, rfl⟩
    induction x with
    | zero => simp
    | tmul b m =>
        rw [ι_tmul_eq_smul_ι_one_tmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy

/-- The base change isomorphism of symmetric algebras carries the base change of the degree-one
part to the degree-one part. -/
theorem map_symAlgBaseChangeEquiv_baseChange_one :
    Submodule.map (symAlgBaseChangeEquiv B M).toAlgHom.toLinearMap
        ((LinearMap.range (SymmetricAlgebra.ι A M)).baseChange B) =
      LinearMap.range (SymmetricAlgebra.ι B (B ⊗[A] M)) := by
  have hr : LinearMap.range (SymmetricAlgebra.ι A M) =
      Submodule.span A (Set.range (SymmetricAlgebra.ι A M)) :=
    le_antisymm (fun _ ⟨m, hm⟩ => hm ▸ Submodule.subset_span ⟨m, rfl⟩)
      (Submodule.span_le.2 fun _ ⟨m, hm⟩ => hm ▸ LinearMap.mem_range_self _ m)
  have hset : (symAlgBaseChangeEquiv B M).toAlgHom.toLinearMap ''
        (TensorProduct.mk A B (SymmetricAlgebra A M) 1 ''
          Set.range (SymmetricAlgebra.ι A M)) =
      Set.range fun m : M => SymmetricAlgebra.ι B (B ⊗[A] M) (1 ⊗ₜ[A] m) := by
    rw [← Set.range_comp, ← Set.range_comp]
    refine congrArg Set.range (funext fun m => ?_)
    show symAlgBaseChangeEquiv B M (1 ⊗ₜ[A] SymmetricAlgebra.ι A M m) = _
    rw [symAlgBaseChangeEquiv_apply, symAlgBaseChangeHom_tmul, map_one, one_mul,
      SymmetricAlgebra.lift_ι_apply, toSymBaseChange_apply]
  rw [hr, Submodule.baseChange_span, Submodule.map_span, hset, span_range_ι_one_tmul]

/-- The base change isomorphism of symmetric algebras carries the base change of the degree-`n`
part to the degree-`n` part. -/
theorem map_symAlgBaseChangeEquiv_baseChange (n : ℕ) :
    Submodule.map (symAlgBaseChangeEquiv B M).toAlgHom.toLinearMap
        ((symmetricPower n A M).baseChange B) = symmetricPower n B (B ⊗[A] M) := by
  rw [symmetricPower, symmetricPower, Submodule.baseChange_pow, Submodule.map_pow,
    map_symAlgBaseChangeEquiv_baseChange_one]

/-- **Symmetric powers commute with base change.** For a commutative ring `A`, an `A`-algebra `B`
and an `A`-module `M`, `B ⊗[A] Symⁿ_A(M) ≃ₗ[B] Symⁿ_B(B ⊗[A] M)`. -/
noncomputable def baseChangeEquiv (n : ℕ) :
    B ⊗[A] symmetricPower n A M ≃ₗ[B] symmetricPower n B (B ⊗[A] M) :=
  (LinearEquiv.ofBijective ((symmetricPower n A M).toBaseChange B)
      (DirectSum.toBaseChange_bijective (fun k => symmetricPower k A M) n)).trans
    ((((symmetricPower n A M).baseChange B).equivMapOfInjective
        (symAlgBaseChangeEquiv B M).toAlgHom.toLinearMap
        (symAlgBaseChangeEquiv B M).injective).trans
      (LinearEquiv.ofEq _ _ (map_symAlgBaseChangeEquiv_baseChange B M n)))

/-- As an element of `Sym_B(B ⊗[A] M)`, the image of `b ⊗ x` under `SymPow.baseChangeEquiv` is
the image of `b ⊗ x` under `SymPow.symAlgBaseChangeHom`. -/
@[simp]
theorem baseChangeEquiv_tmul (n : ℕ) (b : B) (x : symmetricPower n A M) :
    (baseChangeEquiv B M n (b ⊗ₜ[A] x) : SymmetricAlgebra B (B ⊗[A] M)) =
      symAlgBaseChangeHom B M (b ⊗ₜ[A] (x : SymmetricAlgebra A M)) := rfl

end SymPow

namespace SymmetricAlgebra

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (M : Type*) [AddCommGroup M] [Module R M]

/-! ### The graded projection -/

/-- The projection of the symmetric algebra onto its degree-`n` piece, from the graded
decomposition `SymmetricAlgebra.gradedAlgebra`. -/
noncomputable def symmetricPowerProj (n : ℕ) :
    SymmetricAlgebra R M →ₗ[R] SymPow.symmetricPower n R M :=
  (DirectSum.component R ℕ (fun k : ℕ => SymPow.symmetricPower k R M) n).comp
    (DirectSum.decomposeLinearEquiv
      (fun k : ℕ => SymPow.symmetricPower k R M)).toLinearMap

/-- The projection is the identity on the degree-`n` piece. -/
theorem symmetricPowerProj_coe (n : ℕ) (x : SymPow.symmetricPower n R M) :
    symmetricPowerProj R M n (x : SymmetricAlgebra R M) = x :=
  Subtype.ext
    (DirectSum.decompose_of_mem_same (fun k : ℕ => SymPow.symmetricPower k R M) x.2)

/-- The degree-`n` piece is a split summand of the symmetric algebra. -/
theorem symmetricPowerProj_comp_subtype (n : ℕ) :
    (symmetricPowerProj R M n).comp (SymPow.symmetricPower n R M).subtype =
      LinearMap.id :=
  LinearMap.ext fun x => symmetricPowerProj_coe R M n x

/-! ### The base change of the symmetric algebra -/

/-- A base-change isomorphism for the symmetric algebra, `Sym_A(A ⊗_R M) ≃ₐ[A] A ⊗_R Sym_R(M)`,
sending `ι (1 ⊗ m)` to `1 ⊗ ι m`. -/
noncomputable def symmetricAlgebraBaseChange :
    SymmetricAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] SymmetricAlgebra R M :=
  (SymmetricAlgebra.exists_algEquiv_baseChange R A M).choose

/-- The specification of `symmetricAlgebraBaseChange` on degree-one generators. -/
theorem symmetricAlgebraBaseChange_ι (m : M) :
    symmetricAlgebraBaseChange R A M (ι A (A ⊗[R] M) (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ι R M m :=
  (SymmetricAlgebra.exists_algEquiv_baseChange R A M).choose_spec m

/-- The inverse of `symmetricAlgebraBaseChange` sends `1 ⊗ ι m` to `ι (1 ⊗ m)`. -/
theorem symmetricAlgebraBaseChange_symm_tmul_ι (m : M) :
    (symmetricAlgebraBaseChange R A M).symm (1 ⊗ₜ[R] ι R M m) =
      ι A (A ⊗[R] M) (1 ⊗ₜ[R] m) :=
  (AlgEquiv.symm_apply_eq _).2 (symmetricAlgebraBaseChange_ι R A M m).symm

/-- The base-change comparison carries the base change of the degree-one generator to the
degree-one generator of the base-changed module. -/
theorem symmetricAlgebraBaseChange_symm_baseChange_ι (z : A ⊗[R] M) :
    (symmetricAlgebraBaseChange R A M).symm
        (LinearMap.baseChange A (ι R M) z) = ι A (A ⊗[R] M) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  | tmul a m =>
      rw [LinearMap.baseChange_tmul, TensorProduct.tmul_eq_smul_one_tmul, map_smul,
        symmetricAlgebraBaseChange_symm_tmul_ι, ← ι_tmul_eq_smul_ι_one_tmul]

/-- The base-change comparison carries `1 ⊗ (ι m₁ ⋯ ι mₙ)` to `ι (1 ⊗ m₁) ⋯ ι (1 ⊗ mₙ)`. -/
theorem symmetricAlgebraBaseChange_symm_one_tmul_prod_ι (n : ℕ) (s : Fin n → M) :
    (symmetricAlgebraBaseChange R A M).symm
        (1 ⊗ₜ[R] ∏ i : Fin n, ι R M (s i)) =
      ∏ i : Fin n, ι A (A ⊗[R] M) (1 ⊗ₜ[R] s i) := by
  have h : (1 : A) ⊗ₜ[R] (∏ i : Fin n, ι R M (s i)) =
      ∏ i : Fin n, ((1 : A) ⊗ₜ[R] ι R M (s i) : A ⊗[R] SymmetricAlgebra R M) :=
    map_prod (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := SymmetricAlgebra R M))
      _ _
  rw [h, map_prod]
  exact Finset.prod_congr rfl fun i _ => symmetricAlgebraBaseChange_symm_tmul_ι R A M (s i)

/-! ### The degreewise comparison -/

/-- The canonical map from `A ⊗_R Symⁿ_R(M)` into `A ⊗_R Sym_R(M)`. -/
noncomputable def symmetricPowerBaseChangeIncl (n : ℕ) :
    A ⊗[R] SymPow.symmetricPower n R M →ₗ[A] A ⊗[R] SymmetricAlgebra R M :=
  LinearMap.baseChange A (SymPow.symmetricPower n R M).subtype

/-- `symmetricPowerBaseChangeIncl` sends `a ⊗ x` to `a ⊗ x`, with `x` viewed in `Sym_R(M)`. -/
theorem symmetricPowerBaseChangeIncl_tmul (n : ℕ) (a : A)
    (x : SymPow.symmetricPower n R M) :
    symmetricPowerBaseChangeIncl R A M n (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] (x : SymmetricAlgebra R M) := rfl

/-- The inclusion is injective, because the graded projection splits it and a split
monomorphism stays one after base change. -/
theorem injective_symmetricPowerBaseChangeIncl (n : ℕ) :
    Function.Injective (symmetricPowerBaseChangeIncl R A M n) := by
  have h : (LinearMap.baseChange A (symmetricPowerProj R M n)).comp
      (symmetricPowerBaseChangeIncl R A M n) = LinearMap.id := by
    rw [symmetricPowerBaseChangeIncl, ← LinearMap.baseChange_comp,
      symmetricPowerProj_comp_subtype, LinearMap.baseChange_id]
  exact Function.LeftInverse.injective
    (g := LinearMap.baseChange A (symmetricPowerProj R M n))
    (LinearMap.congr_fun h)

/-- Multiplying by the base change of a degree-one generator raises the degree by one. -/
theorem baseChange_ι_mul_mem_range (i : ℕ) (z : A ⊗[R] M)
    (y : A ⊗[R] SymPow.symmetricPower i R M) :
    LinearMap.baseChange A (ι R M) z * symmetricPowerBaseChangeIncl R A M i y ∈
      LinearMap.range (symmetricPowerBaseChangeIncl R A M (i + 1)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      rw [map_add, add_mul]
      exact Submodule.add_mem _ hz hw
  | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ =>
          rw [map_add, mul_add]
          exact Submodule.add_mem _ h₁ h₂
      | tmul b x =>
          refine ⟨(a * b) ⊗ₜ[R] ⟨(ι R M m : SymmetricAlgebra R M) * (x : SymmetricAlgebra R M),
            SymPow.mul_mem_succ i m x⟩, ?_⟩
          rw [symmetricPowerBaseChangeIncl_tmul, symmetricPowerBaseChangeIncl_tmul,
            LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]

/-- `1 ⊗ x`, for `x` in the `n`-th symmetric power, lands in the `n`-th symmetric power of the
base change. -/
theorem symmetricAlgebraBaseChange_symm_one_tmul_mem :
    ∀ (n : ℕ) (x : SymmetricAlgebra R M), x ∈ SymPow.symmetricPower n R M →
      (symmetricAlgebraBaseChange R A M).symm (1 ⊗ₜ[R] x) ∈
        SymPow.symmetricPower n A (A ⊗[R] M) := by
  intro n x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      have h1 : (1 : A) ⊗ₜ[R] (algebraMap R (SymmetricAlgebra R M) r) =
          (algebraMap R A r) ⊗ₜ[R] (1 : SymmetricAlgebra R M) := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      show _ ∈ (LinearMap.range (ι A (A ⊗[R] M))) ^ 0
      rw [h1, TensorProduct.tmul_eq_smul_one_tmul,
        ← Algebra.TensorProduct.one_def, map_smul, map_one, pow_zero]
      exact Submodule.smul_mem _ _ (Submodule.one_le.1 le_rfl)
  | add x y k hx hy ihx ihy =>
      rw [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ ihx ihy
  | mem_mul w hw k x hx ih =>
      obtain ⟨m, rfl⟩ := hw
      have h2 : (1 : A) ⊗ₜ[R] ((ι R M m : SymmetricAlgebra R M) * x) =
          ((1 : A) ⊗ₜ[R] (ι R M m : SymmetricAlgebra R M)) * ((1 : A) ⊗ₜ[R] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show _ ∈ (LinearMap.range (ι A (A ⊗[R] M))) ^ (k + 1)
      rw [h2, map_mul, symmetricAlgebraBaseChange_symm_tmul_ι, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

/-- The base change of the `n`-th symmetric power lands in the `n`-th symmetric power of the
base change. -/
theorem symmetricAlgebraBaseChange_symm_incl_mem (n : ℕ)
    (y : A ⊗[R] SymPow.symmetricPower n R M) :
    (symmetricAlgebraBaseChange R A M).symm (symmetricPowerBaseChangeIncl R A M n y) ∈
      SymPow.symmetricPower n A (A ⊗[R] M) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ h₁ h₂
  | tmul a x =>
      rw [symmetricPowerBaseChangeIncl_tmul, TensorProduct.tmul_eq_smul_one_tmul, map_smul]
      exact Submodule.smul_mem _ a
        (symmetricAlgebraBaseChange_symm_one_tmul_mem R A M n _ x.2)

/-- Every element of `Symⁿ_A(A ⊗_R M)` comes from `A ⊗_R Symⁿ_R(M)`. -/
theorem exists_eq_symmetricAlgebraBaseChange_symm_incl :
    ∀ (n : ℕ) (w : SymmetricAlgebra A (A ⊗[R] M)),
      w ∈ SymPow.symmetricPower n A (A ⊗[R] M) →
      ∃ y : A ⊗[R] SymPow.symmetricPower n R M,
        (symmetricAlgebraBaseChange R A M).symm
          (symmetricPowerBaseChangeIncl R A M n y) = w := by
  intro n w hw
  induction hw using Submodule.pow_induction_on_left' with
  | algebraMap a =>
      refine ⟨a ⊗ₜ[R] ⟨1, ?_⟩, ?_⟩
      · show (1 : SymmetricAlgebra R M) ∈ (LinearMap.range (ι R M)) ^ 0
        rw [pow_zero]
        exact Submodule.one_le.1 le_rfl
      · rw [symmetricPowerBaseChangeIncl_tmul]
        show (symmetricAlgebraBaseChange R A M).symm
          (a ⊗ₜ[R] (1 : SymmetricAlgebra R M)) = _
        rw [TensorProduct.tmul_eq_smul_one_tmul,
          ← Algebra.TensorProduct.one_def, map_smul, map_one,
          Algebra.algebraMap_eq_smul_one]
  | add w₁ w₂ k hw₁ hw₂ ih₁ ih₂ =>
      obtain ⟨y₁, hy₁⟩ := ih₁
      obtain ⟨y₂, hy₂⟩ := ih₂
      exact ⟨y₁ + y₂, by rw [map_add, map_add, hy₁, hy₂]⟩
  | mem_mul u hu k w' hw' ih =>
      obtain ⟨z, rfl⟩ := hu
      obtain ⟨y, hy⟩ := ih
      obtain ⟨t, ht⟩ := baseChange_ι_mul_mem_range R A M k z y
      exact ⟨t, by rw [ht, map_mul, symmetricAlgebraBaseChange_symm_baseChange_ι, hy]⟩

/-- **The symmetric powers commute with base change.** For a commutative `R`-algebra `A` and an
`R`-module `M`, the base change of the `n`-th symmetric power of `M` is the `n`-th symmetric
power of the base change of `M`. -/
noncomputable def symmetricPowerBaseChange (n : ℕ) :
    A ⊗[R] SymPow.symmetricPower n R M ≃ₗ[A]
      SymPow.symmetricPower n A (A ⊗[R] M) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (SymPow.symmetricPower n A (A ⊗[R] M))
      ((symmetricAlgebraBaseChange R A M).symm.toLinearMap.comp
        (symmetricPowerBaseChangeIncl R A M n))
      (symmetricAlgebraBaseChange_symm_incl_mem R A M n))
    ⟨fun _ _ h => injective_symmetricPowerBaseChangeIncl R A M n
      ((symmetricAlgebraBaseChange R A M).symm.injective (Subtype.ext_iff.1 h)),
      fun w => (exists_eq_symmetricAlgebraBaseChange_symm_incl R A M n w w.2).imp
        fun _ => Subtype.ext⟩

/-- As an element of `Sym_A(A ⊗_R M)`, `symmetricPowerBaseChange R A M n y` is the image of
`symmetricPowerBaseChangeIncl R A M n y` under the inverse of `symmetricAlgebraBaseChange`. -/
theorem symmetricPowerBaseChange_apply_coe (n : ℕ)
    (y : A ⊗[R] SymPow.symmetricPower n R M) :
    (symmetricPowerBaseChange R A M n y : SymmetricAlgebra A (A ⊗[R] M)) =
      (symmetricAlgebraBaseChange R A M).symm
        (symmetricPowerBaseChangeIncl R A M n y) := rfl

/-- The degreewise comparison `symmetricPowerBaseChange` carries `a ⊗ (ι m₁ ⋯ ι mₙ)` to
`a • (ι (1 ⊗ m₁) ⋯ ι (1 ⊗ mₙ))`. -/
theorem symmetricPowerBaseChange_tmul_prod_ι (n : ℕ) (a : A) (s : Fin n → M) :
    (symmetricPowerBaseChange R A M n
          (a ⊗ₜ[R] ⟨∏ i : Fin n, ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩) :
        SymmetricAlgebra A (A ⊗[R] M)) =
      a • ∏ i : Fin n, ι A (A ⊗[R] M) (1 ⊗ₜ[R] s i) := by
  rw [symmetricPowerBaseChange_apply_coe, symmetricPowerBaseChangeIncl_tmul,
    TensorProduct.tmul_eq_smul_one_tmul, map_smul,
    symmetricAlgebraBaseChange_symm_one_tmul_prod_ι]

end SymmetricAlgebra
