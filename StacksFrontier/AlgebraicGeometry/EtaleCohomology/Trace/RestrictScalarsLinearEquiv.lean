module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# `F^{m d}` with the action of `E` by restriction of scalars is `E^m`

For a finite extension `E/F` with an `F`-basis `b` of size `d`, the `F`-linear isomorphism
`F^{m d} ≅ E^m`, `v ↦ (∑_l v_{(i, l)} b_l)_i`, carries the restriction of scalars
`restrictScalarsMatrix b N` of every `N ∈ Mat_m(E)` to `N`. Consequently an `E`-linear
endomorphism `T` of an `E`-vector space `V` which, under an `F`-linear isomorphism `V ≅ F^{m d}`
carrying the action of `e ∈ E` to the restriction of scalars of the scalar matrix `e`, becomes the
restriction of scalars of `N`, has the `E`-linear characteristic polynomial of `N`.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `restrictScalarsEquiv`: the `F`-linear isomorphism `F^{m d} ≅ E^m`.
* `restrictScalarsEquiv_mulVec`: it carries `restrictScalarsMatrix b N` to `N`.
* `charpoly_eq_of_restrictScalarsMatrix`: the `E`-linear characteristic polynomial of `T` is that
  of `N`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  (m : ℕ)

/-- **`F^{m d} ≅ E^m`**, `v ↦ (∑_l v_{(i, l)} b_l)_i`. -/
public def restrictScalarsEquiv : (Fin (m * d) → F) ≃ₗ[F] (Fin m → E) :=
  (LinearEquiv.funCongrLeft F F finProdFinEquiv).trans
    ((LinearEquiv.curry F F (Fin m) (Fin d)).trans
      (LinearEquiv.piCongrRight fun _ => b.equivFun.symm))

/-- The `i`-th coordinate of `restrictScalarsEquiv b m v` is `∑_l v_{(i, l)} b_l`. -/
public theorem restrictScalarsEquiv_apply (v : Fin (m * d) → F) (i : Fin m) :
    restrictScalarsEquiv b m v i = ∑ l, v (finProdFinEquiv (i, l)) • b l := by
  simp [restrictScalarsEquiv, Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply]

variable {m}

/-- **`F^{m d} ≅ E^m` carries `Res_b N` to `N`.** -/
public theorem restrictScalarsEquiv_mulVec (N : Matrix (Fin m) (Fin m) E) (v : Fin (m * d) → F) :
    restrictScalarsEquiv b m (restrictScalarsMatrix b N *ᵥ v) =
      N *ᵥ restrictScalarsEquiv b m v := by
  funext i
  simp only [restrictScalarsEquiv_apply, Matrix.mulVec, dotProduct]
  have hsplit : ∀ (w : Fin (m * d) → F),
      ∑ q, w q = ∑ j : Fin m, ∑ l' : Fin d, w (finProdFinEquiv (j, l')) := fun w => by
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp_rw [hsplit, restrictScalarsMatrix_apply, Finset.sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [mul_smul_comm]
  have h : N i j * b l' = ∑ x, Algebra.leftMulMatrix b (N i j) x l' • b x := by
    simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr _).symm
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, mul_comm]

/-- **`E`-linear characteristic polynomials through restriction of scalars**: if an `F`-linear
isomorphism `Ψ : V ≅ F^{m d}` carries the action of every `e ∈ E` to `Res_b (e · 1_m)` and the
`E`-linear endomorphism `T` to `Res_b N`, then `T` has the characteristic polynomial of `N`. -/
public theorem charpoly_eq_of_restrictScalarsMatrix {V : Type*} [AddCommGroup V] [Module E V]
    [Module F V] [IsScalarTower F E V] [Module.Free E V] [Module.Finite E V]
    (Ψ : V ≃ₗ[F] (Fin (m * d) → F))
    (hΨ : ∀ (e : E) (v : V), Ψ (e • v) = restrictScalarsMatrix b (Matrix.scalar (Fin m) e) *ᵥ Ψ v)
    (T : V →ₗ[E] V) (N : Matrix (Fin m) (Fin m) E)
    (hT : ∀ v, Ψ (T v) = restrictScalarsMatrix b N *ᵥ Ψ v) :
    T.charpoly = N.charpoly := by
  let Φ : V ≃ₗ[E] (Fin m → E) :=
    { (Ψ.trans (restrictScalarsEquiv b m)) with
      map_smul' := fun e v => by
        show restrictScalarsEquiv b m (Ψ (e • v)) = e • restrictScalarsEquiv b m (Ψ v)
        rw [hΨ, restrictScalarsEquiv_mulVec, Matrix.scalar_apply]
        funext i
        rw [Matrix.mulVec_diagonal]
        rfl }
  have hconj : Φ.conj T = Matrix.toLin' N := LinearMap.ext fun w => by
    obtain ⟨v, rfl⟩ := Φ.surjective w
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply]
    show restrictScalarsEquiv b m (Ψ (T v)) = N *ᵥ restrictScalarsEquiv b m (Ψ v)
    rw [hT, restrictScalarsEquiv_mulVec]
  rw [← LinearEquiv.charpoly_conj Φ T, hconj, Matrix.charpoly_toLin']

end Stacks.EtaleCohomology

end
