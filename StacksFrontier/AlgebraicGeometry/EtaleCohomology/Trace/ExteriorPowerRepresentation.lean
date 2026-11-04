module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerCharpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

/-!
# Exterior powers of matrix representations

For a matrix `A ∈ M_n(R)` over a commutative ring, the *`k`-th compound matrix* is the matrix of
`⋀ᵏ A` in the basis `e_S = e_{s₁} ∧ ⋯ ∧ e_{sₖ}` of `⋀ᵏ Rⁿ`, indexed by the `k`-element subsets `S`
of `{0, …, n - 1}`; its entries are the `k × k` minors of `A`.  It is multiplicative, so a
representation `σ : Γ → GL_n(R)` has an exterior power `⋀ᵏ σ`, continuous when `σ` is.  Over a
field the complex roots of the characteristic polynomial of `⋀ᵏ σ(g)` are the products of `k`
roots (with multiplicity) of that of `σ(g)`; in particular `⋀ᵏ` preserves `ι`-reality.

These are the representations `⋀^{N+1} ℰ` to which Deligne applies Rankin's bound in the proof
that the constituents of an `ι`-real lisse sheaf are pure (Weil II 1.5.1; Kedlaya, *Fourier
transforms and p-adic Weil II*, Theorem 6.5.2).

## Main definitions

* `Stacks.EtaleCohomology.compoundMonoidHom`: `A ↦ ⋀ᵏ A` as a monoid homomorphism of matrices.
* `Stacks.EtaleCohomology.exteriorPowerRepresentation`: `⋀ᵏ σ`.

## Main results

* `Stacks.EtaleCohomology.compoundMonoidHom_apply_apply`: the entries are minors.
* `Stacks.EtaleCohomology.continuous_exteriorPowerRepresentation`.
* `Stacks.EtaleCohomology.charpoly_exteriorPowerRepresentation_map`: the roots are the products of
  `k` roots.
* `Stacks.EtaleCohomology.exteriorPowerRepresentation_charpoly_real`: `ι`-reality is preserved.
-/

@[expose] public noncomputable section

open Polynomial Set.powersetCard

namespace Stacks.EtaleCohomology

section Compound

variable {R : Type*} [CommRing R] {n : ℕ} (k : ℕ)

/-- **The `k`-th compound matrix** `A ↦ ⋀ᵏ A`, the matrix of `exteriorPower.map k A` in the basis
of `⋀ᵏ Rⁿ` induced by the standard basis, as a monoid homomorphism. -/
public def compoundMonoidHom :
    Matrix (Fin n) (Fin n) R →*
      Matrix (Set.powersetCard (Fin n) k) (Set.powersetCard (Fin n) k) R where
  toFun A := LinearMap.toMatrix ((Pi.basisFun R (Fin n)).exteriorPower k)
    ((Pi.basisFun R (Fin n)).exteriorPower k) (exteriorPower.map k (Matrix.toLin' A))
  map_one' := by
    rw [Matrix.toLin'_one]
    exact (congrArg _ exteriorPower.map_id).trans
      (LinearMap.toMatrix_id ((Pi.basisFun R (Fin n)).exteriorPower k))
  map_mul' A B := by
    rw [Matrix.toLin'_mul, exteriorPower.map_comp]
    exact LinearMap.toMatrix_comp ((Pi.basisFun R (Fin n)).exteriorPower k)
      ((Pi.basisFun R (Fin n)).exteriorPower k) ((Pi.basisFun R (Fin n)).exteriorPower k) _ _

/-- The entries of the compound matrix are the `k × k` minors. -/
public theorem compoundMonoidHom_apply_apply (A : Matrix (Fin n) (Fin n) R)
    (T S : Set.powersetCard (Fin n) k) :
    compoundMonoidHom k A T S =
      (A.submatrix (ofFinEmbEquiv.symm T) (ofFinEmbEquiv.symm S)).det := by
  show LinearMap.toMatrix _ _ _ T S = _
  rw [toMatrix_exteriorPower_map, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- Over a topological ring, the compound matrix `A ↦ ⋀ᵏ A` is continuous. -/
public theorem continuous_compoundMonoidHom [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (compoundMonoidHom (R := R) (n := n) k) := by
  refine continuous_pi fun T => continuous_pi fun S => ?_
  simp only [compoundMonoidHom_apply_apply]
  exact (continuous_id.matrix_submatrix _ _).matrix_det

variable {Γ : Type*} [Group Γ]

/-- **`⋀ᵏ σ`**, the `k`-th exterior power of a matrix representation `σ : Γ → GL_n(R)`, written
in the basis `e_S` of `⋀ᵏ Rⁿ` numbered by `Fintype.equivFin`. -/
public def exteriorPowerRepresentation (σ : Γ →* GL (Fin n) R) :
    Γ →* GL (Fin (Fintype.card (Set.powersetCard (Fin n) k))) R :=
  (Units.map ((Matrix.reindexAlgEquiv R R
    (Fintype.equivFin (Set.powersetCard (Fin n) k))).toRingEquiv.toMonoidHom.comp
      (compoundMonoidHom k))).comp σ

/-- The matrix of `⋀ᵏ σ(g)` is the compound matrix of `σ(g)`, reindexed along
`Fintype.equivFin`. -/
public theorem exteriorPowerRepresentation_val (σ : Γ →* GL (Fin n) R) (g : Γ) :
    (exteriorPowerRepresentation k σ g :
      Matrix (Fin (Fintype.card (Set.powersetCard (Fin n) k)))
        (Fin (Fintype.card (Set.powersetCard (Fin n) k))) R) =
      Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
        (compoundMonoidHom k (σ g : Matrix (Fin n) (Fin n) R)) :=
  rfl

/-- `⋀ᵏ σ` is continuous when `σ` is. -/
public theorem continuous_exteriorPowerRepresentation [TopologicalSpace Γ] [TopologicalSpace R]
    [IsTopologicalRing R] {σ : Γ →* GL (Fin n) R} (hσ : Continuous σ) :
    Continuous (exteriorPowerRepresentation k σ) := by
  have hf : Continuous ((Matrix.reindexAlgEquiv R R
      (Fintype.equivFin (Set.powersetCard (Fin n) k))).toRingEquiv.toMonoidHom.comp
        (compoundMonoidHom (R := R) (n := n) k)) :=
    (continuous_compoundMonoidHom k).matrix_reindex _ _
  exact hf.units_map.comp hσ

end Compound

section Field

variable {F : Type*} [Field F] {n : ℕ} (k : ℕ)

/-- **The roots of the characteristic polynomial of a compound matrix** are, along
`ι : F →+* L` into an algebraically closed field, the products of the `k`-element sub-multisets of
the roots of that of `A`. -/
public theorem charpoly_compoundMonoidHom_map {L : Type*} [Field L] [IsAlgClosed L] (ι : F →+* L)
    (A : Matrix (Fin n) (Fin n) F) :
    (compoundMonoidHom k A).charpoly.map ι =
      (((A.charpoly.map ι).roots.powersetCard k).map
        fun s => Polynomial.X - Polynomial.C s.prod).prod := by
  show (LinearMap.toMatrix _ _ _).charpoly.map ι = _
  rw [LinearMap.charpoly_toMatrix, charpoly_exteriorPower_map_map, Matrix.charpoly_toLin']

variable {Γ : Type*} [Group Γ]

/-- Along `ι : F →+* L` into an algebraically closed field, the characteristic polynomial of
`⋀ᵏ σ(g)` has as roots the products of the `k`-element sub-multisets of the roots of that of
`σ(g)`. -/
public theorem charpoly_exteriorPowerRepresentation_map {L : Type*} [Field L] [IsAlgClosed L]
    (ι : F →+* L) (σ : Γ →* GL (Fin n) F) (g : Γ) :
    (exteriorPowerRepresentation k σ g :
      Matrix (Fin (Fintype.card (Set.powersetCard (Fin n) k)))
        (Fin (Fintype.card (Set.powersetCard (Fin n) k))) F).charpoly.map ι =
      ((((σ g : Matrix (Fin n) (Fin n) F).charpoly.map ι).roots.powersetCard k).map
        fun s => Polynomial.X - Polynomial.C s.prod).prod := by
  rw [exteriorPowerRepresentation_val, Matrix.charpoly_reindex, charpoly_compoundMonoidHom_map]

/-- **`⋀ᵏ` preserves `ι`-reality**: if the characteristic polynomial of `σ(g)` has `ι`-real
coefficients, so does that of `⋀ᵏ σ(g)`. -/
public theorem exteriorPowerRepresentation_charpoly_real (ι : F →+* ℂ) (σ : Γ →* GL (Fin n) F)
    (g : Γ) (hreal : ∀ m, ι ((σ g : Matrix (Fin n) (Fin n) F).charpoly.coeff m) ∈
      Set.range ((↑) : ℝ → ℂ)) (m : ℕ) :
    ι ((exteriorPowerRepresentation k σ g :
      Matrix (Fin (Fintype.card (Set.powersetCard (Fin n) k)))
        (Fin (Fintype.card (Set.powersetCard (Fin n) k))) F).charpoly.coeff m) ∈
      Set.range ((↑) : ℝ → ℂ) := by
  set P := (σ g : Matrix (Fin n) (Fin n) F).charpoly.map ι
  have hPc : P.map (starRingEnd ℂ) = P := by
    ext i
    rw [coeff_map]
    obtain ⟨c, hc⟩ := hreal i
    rw [show P.coeff i = ι ((σ g : Matrix (Fin n) (Fin n) F).charpoly.coeff i) from coeff_map _ _,
      ← hc, Complex.conj_ofReal]
  have hroots : P.roots.map (starRingEnd ℂ) = P.roots := by
    rw [((Matrix.charpoly_monic _).map ι).roots_map_of_card_eq_natDegree (starRingEnd ℂ)
      IsAlgClosed.card_roots_eq_natDegree, hPc]
  set Q := ((P.roots.powersetCard k).map fun s => Polynomial.X - Polynomial.C s.prod).prod
  have hQ : Q.map (starRingEnd ℂ) = Q := by
    simp only [Q, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.map_sub, map_X, map_C, map_multiset_prod]
    conv_rhs => rw [← hroots, Multiset.powersetCard_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp [Multiset.map_map]
  have h := charpoly_exteriorPowerRepresentation_map k ι σ g
  rw [← coeff_map, h]
  refine ⟨(Q.coeff m).re, ?_⟩
  have hc : starRingEnd ℂ (Q.coeff m) = Q.coeff m := by
    conv_rhs => rw [← hQ]
    rw [coeff_map]
  exact Complex.conj_eq_iff_re.mp hc

end Field

end Stacks.EtaleCohomology

end
