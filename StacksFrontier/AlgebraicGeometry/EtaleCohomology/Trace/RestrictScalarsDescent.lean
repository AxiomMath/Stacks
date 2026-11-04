module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Descent of a commuting action of a finite extension

Let `E/F` be a finite extension with an `F`-basis `b` of size `d`, and let
`α : E →ₐ[F] Mat_r(F)`, making `F^r` an `E`-vector space, of dimension `m` say. In the `F`-basis
`(b_l • c_i)` attached to an `E`-basis `c` of `F^r` (indexed as in
`Stacks.EtaleCohomology.restrictScalarsMatrix`), every matrix `M` commuting with `α` becomes the
restriction of scalars of an `m × m` matrix over `E` (the matrix of `M` in the basis `c`), and
`α x` becomes the restriction of scalars of the scalar matrix `x`
(`Stacks.EtaleCohomology.exists_conj_restrictScalarsMatrix`). Hence a representation
`ρ : G → GL_r(F)` commuting with `α` is conjugate to `Res_b τ` for a representation
`τ : G → GL_m(E)`.

## Main results

* `Stacks.EtaleCohomology.toMatrix_restrictScalars_smulTower`.
* `Stacks.EtaleCohomology.exists_conj_restrictScalarsMatrix`.
* `Stacks.EtaleCohomology.exists_restrictScalarsRep_conj`.
* `Stacks.EtaleCohomology.continuous_of_conj`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- **The matrix of an `E`-linear map in the tower basis** `(b_l • c_i)` is the restriction of
scalars of its matrix in `c`. -/
public theorem toMatrix_restrictScalars_smulTower {V : Type*} [AddCommGroup V] [Module E V]
    [Module F V] [IsScalarTower F E V] {m : ℕ} (c : Module.Basis (Fin m) E V) (f : V →ₗ[E] V) :
    LinearMap.toMatrix ((b.smulTower c).reindex ((Equiv.prodComm _ _).trans finProdFinEquiv))
        ((b.smulTower c).reindex ((Equiv.prodComm _ _).trans finProdFinEquiv))
        (f.restrictScalars F) =
      restrictScalarsMatrix b (LinearMap.toMatrix c c f) := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [restrictScalarsMatrix_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply, Algebra.leftMulMatrix_eq_repr_mul]
  have hq : ((Equiv.prodComm (Fin d) (Fin m)).trans finProdFinEquiv).symm
      (finProdFinEquiv (j, l')) = (l', j) := by simp
  have hp : ((Equiv.prodComm (Fin d) (Fin m)).trans finProdFinEquiv).symm
      (finProdFinEquiv (i, l)) = (l, i) := by simp
  rw [hq, hp, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    LinearMap.restrictScalars_apply]
  dsimp only
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- The common construction behind descent: matrices `P`, `Q` in the tower basis, and a monoid
homomorphism `Φ` on the commutant of `α` with `Q M P = Res_b (Φ M)`. -/
private theorem exists_conj_centralizer_hom {r : ℕ}
    (α : E →ₐ[F] Matrix (Fin r) (Fin r) F) :
    ∃ (m : ℕ) (P : Matrix (Fin r) (Fin (m * d)) F) (Q : Matrix (Fin (m * d)) (Fin r) F)
      (Φ : Submonoid.centralizer (Set.range α) →* Matrix (Fin m) (Fin m) E),
      P * Q = 1 ∧ Q * P = 1 ∧
      (∀ x : E, Q * α x * P = restrictScalarsMatrix b (Matrix.scalar (Fin m) x)) ∧
      ∀ M : Submonoid.centralizer (Set.range α), Q * M.val * P = restrictScalarsMatrix b (Φ M) := by
  classical
  let : Module E (Fin r → F) :=
    Module.compHom (Fin r → F) ((Matrix.toLinAlgEquiv' (R := F) (n := Fin r)).toRingHom.comp
      α.toRingHom)
  have hsmul : ∀ (x : E) (v : Fin r → F), x • v = α x *ᵥ v := fun _ _ => rfl
  have : IsScalarTower F E (Fin r → F) := ⟨fun c x v => by
    rw [hsmul, hsmul, map_smul, Matrix.smul_mulVec]⟩
  have : FiniteDimensional E (Fin r → F) := Module.Finite.of_restrictScalars_finite F E _
  let c := Module.finBasis E (Fin r → F)
  let cb := (b.smulTower c).reindex ((Equiv.prodComm _ _).trans finProdFinEquiv)
  let std := Pi.basisFun F (Fin r)
  have hconj : ∀ M : Matrix (Fin r) (Fin r) F,
      cb.toMatrix std * M * std.toMatrix cb = LinearMap.toMatrix cb cb (Matrix.toLin' M) := by
    intro M
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := cb) (b' := std) (c := cb)
      (c' := std),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  let lin : Submonoid.centralizer (Set.range α) →* Module.End E (Fin r → F) :=
    { toFun := fun M =>
        { toFun := fun v => M.val *ᵥ v
          map_add' := Matrix.mulVec_add _
          map_smul' := fun x v => by
            simp only [RingHom.id_apply, hsmul, Matrix.mulVec_mulVec,
              Submonoid.mem_centralizer_iff.1 M.2 _ ⟨x, rfl⟩] }
      map_one' := LinearMap.ext fun v => Matrix.one_mulVec v
      map_mul' := fun M N => LinearMap.ext fun v => (Matrix.mulVec_mulVec v _ _).symm }
  have hlin : ∀ M, (lin M).restrictScalars F = Matrix.toLin' M.val := fun _ => rfl
  refine ⟨Module.finrank E (Fin r → F), std.toMatrix cb, cb.toMatrix std,
    (LinearMap.toMatrixAlgEquiv c).toAlgHom.toMonoidHom.comp lin,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    fun x => ?_, fun M => ?_⟩
  · have hα : α x ∈ Submonoid.centralizer (Set.range α) := Submonoid.mem_centralizer_iff.2
      (by rintro _ ⟨y, rfl⟩; rw [← map_mul, ← map_mul, mul_comm])
    rw [hconj, ← hlin ⟨_, hα⟩, toMatrix_restrictScalars_smulTower]
    congr 1
    have : lin ⟨_, hα⟩ = x • LinearMap.id := LinearMap.ext fun v => (hsmul x v).symm
    rw [this, map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal]
    rfl
  · rw [hconj, ← hlin M, toMatrix_restrictScalars_smulTower]
    rfl

variable [FiniteDimensional F E] {r : ℕ} (α : E →ₐ[F] Matrix (Fin r) (Fin r) F)

omit [FiniteDimensional F E] in
/-- **Descent of a commuting action of `E`**: for `α : E →ₐ[F] Mat_r(F)` there are `m` and mutually
inverse matrices `P`, `Q` (the tower basis of an `E`-basis of `F^r` through `α`) such that
`Q (α x) P` is the restriction of scalars of the scalar matrix `x`, and `Q M P` is a restriction of
scalars for every `M` commuting with `α`. -/
public theorem exists_conj_restrictScalarsMatrix :
    ∃ (m : ℕ) (P : Matrix (Fin r) (Fin (m * d)) F) (Q : Matrix (Fin (m * d)) (Fin r) F),
      P * Q = 1 ∧ Q * P = 1 ∧
      (∀ x : E, Q * α x * P = restrictScalarsMatrix b (Matrix.scalar (Fin m) x)) ∧
      ∀ M : Matrix (Fin r) (Fin r) F, (∀ x : E, α x * M = M * α x) →
        ∃ N : Matrix (Fin m) (Fin m) E, Q * M * P = restrictScalarsMatrix b N := by
  obtain ⟨m, P, Q, Φ, hPQ, hQP, hα, hΦ⟩ := exists_conj_centralizer_hom b α
  exact ⟨m, P, Q, hPQ, hQP, hα, fun M hM =>
    ⟨_, hΦ ⟨M, Submonoid.mem_centralizer_iff.2 (by rintro _ ⟨x, rfl⟩; exact hM x)⟩⟩⟩

omit [FiniteDimensional F E] in
/-- **Descent of a representation commuting with `α`**: a representation `ρ : G → GL_r(F)`
commuting with `α : E →ₐ[F] Mat_r(F)` is conjugate, by mutually inverse matrices `P`, `Q`, to the
restriction of scalars `Res_b τ` of a representation `τ : G → GL_m(E)`, the conjugation carrying
`α x` to the restriction of scalars of the scalar matrix `x`. -/
public theorem exists_restrictScalarsRep_conj {G : Type*} [Monoid G] (ρ : G →* GL (Fin r) F)
    (hρ : ∀ (g : G) (x : E), α x * (ρ g).val = (ρ g).val * α x) :
    ∃ (m : ℕ) (τ : G →* GL (Fin m) E) (P : Matrix (Fin r) (Fin (m * d)) F)
      (Q : Matrix (Fin (m * d)) (Fin r) F),
      P * Q = 1 ∧ Q * P = 1 ∧
      (∀ x : E, Q * α x * P = restrictScalarsMatrix b (Matrix.scalar (Fin m) x)) ∧
      ∀ g : G, Q * (ρ g).val * P = (restrictScalarsRep b τ g).val := by
  obtain ⟨m, P, Q, Φ, hPQ, hQP, hα, hΦ⟩ := exists_conj_centralizer_hom b α
  let ρc : G →* (Submonoid.centralizer (Set.range α))ˣ :=
    { toFun := fun g =>
        { val := ⟨(ρ g).val, Submonoid.mem_centralizer_iff.2 (by rintro _ ⟨x, rfl⟩; exact hρ g x)⟩
          inv := ⟨(ρ g)⁻¹.val, Submonoid.mem_centralizer_iff.2 (by
            rintro _ ⟨x, rfl⟩; exact Commute.units_inv_right (hρ g x))⟩
          val_inv := Subtype.ext (ρ g).mul_inv
          inv_val := Subtype.ext (ρ g).inv_mul }
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun g h => Units.ext (Subtype.ext (by simp)) }
  exact ⟨m, (Units.map Φ).comp ρc, P, Q, hPQ, hQP, hα, fun g => by
    rw [restrictScalarsRep_val]
    exact hΦ (ρc g).val⟩

/-- **Continuity is preserved by a constant conjugation**: if `Q ρ(x) P = τ(x)` with `P`, `Q`
mutually inverse, and `ρ` is continuous, so is `τ`. -/
public theorem continuous_of_conj {X R : Type*} [TopologicalSpace X] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {n n' : ℕ} {ρ : X → GL (Fin n) R} (hρ : Continuous ρ)
    {τ : X → GL (Fin n') R} {P : Matrix (Fin n) (Fin n') R} {Q : Matrix (Fin n') (Fin n) R}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : ∀ x, Q * (ρ x).val * P = (τ x).val) :
    Continuous τ := by
  have hinv : ∀ x, ((τ x)⁻¹ : GL (Fin n') R).val = Q * (ρ x)⁻¹.val * P := fun x => by
    refine Units.inv_eq_of_mul_eq_one_right (u := τ x) ?_
    rw [← h x, show Q * (ρ x).val * P * (Q * (ρ x)⁻¹.val * P) =
      Q * (ρ x).val * (P * Q) * (ρ x)⁻¹.val * P by simp only [Matrix.mul_assoc], hPQ,
      Matrix.mul_one, Matrix.mul_assoc Q, Units.mul_inv, Matrix.mul_one, hQP]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (fun x => (τ x).val) = fun x => Q * (ρ x).val * P := funext fun x => (h x).symm
    simp only [Function.comp_def, this]
    exact (continuous_const.matrix_mul (Units.continuous_val.comp hρ)).matrix_mul continuous_const
  · have : (fun x => ((τ x)⁻¹ : GL (Fin n') R).val) = fun x => Q * (ρ x)⁻¹.val * P :=
      funext hinv
    simp only [this]
    exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp hρ)).matrix_mul
      continuous_const

end Stacks.EtaleCohomology

end
