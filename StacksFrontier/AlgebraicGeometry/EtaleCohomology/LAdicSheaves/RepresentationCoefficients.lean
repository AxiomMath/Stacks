module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.CharacterSheaf

/-!
# The `O`-sheaf of a representation with coefficients in `O`

Let `O` be a finite free `ℤ_ℓ`-algebra with basis `b` of rank `d` (for instance the ring of integers
of a finite extension of `ℚ_ℓ`), and let `ρ : π₁(X, x̄) → GL_r(O)` be a representation. Restricting
scalars along `b` turns `O^r` into `ℤ_ℓ^{rd}` and `ρ` into a representation
`π₁(X, x̄) → GL_{rd}(ℤ_ℓ)` commuting with the action of `O`; its sheaf is an `O`-sheaf whose stalks
are free of rank `r` over `O`, on which an endomorphism of a geometric point acts by the matrix
`ρ(g)` [Weil II, 1.1.1], [SGA 5, VI 1.5]. Twisting by an `O^×`-valued character `χ` multiplies the
representation by `χ`, so the stalk traces get multiplied by the values of `χ` (this is the twist
`ℱ ⊗ L_ψ(t x)` of the Fourier transform when `χ` is an Artin–Schreier character).

## Main definitions

* `Stacks.EtaleCohomology.coefficientMatrixRingHom`: the ring map `M_r(O) → M_{rd}(ℤ_ℓ)`.
* `Stacks.EtaleCohomology.coefficientVecEquiv`: `ℤ_ℓ^{rd} ≃ O^r`.
* `Stacks.EtaleCohomology.coefficientRepresentationSheaf`: the `O`-sheaf `ℱ_ρ`.
* `Stacks.EtaleCohomology.coefficientRepresentationSheafStalkLinearEquiv`: its stalks are `O^r`.
* `Stacks.EtaleCohomology.characterTwist`: the twist `g ↦ χ(g) ρ(g)`.

## Main results

* `Stacks.EtaleCohomology.coefficientVecEquiv_mulVec`: `coefficientMatrixRingHom` is the matrix
  of `M` acting on `O^r`.
* `Stacks.EtaleCohomology.coefficientRepresentationSheafStalkLinearEquiv_stalkEnd`,
  `Stacks.EtaleCohomology.trace_coefficientRepresentationSheaf_stalkEnd`: an endomorphism of a
  geometric point acts on the stalk by `ρ(g)`, with `O`-trace `tr ρ(g)`.
* `Stacks.EtaleCohomology.trace_characterTwist_stalkEnd`: on the twist by `χ` the trace is
  `χ(g) tr ρ(g)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

/-! ### Restriction of scalars of matrices along a basis -/

section Algebra

variable {R O : Type*} [CommRing R] [CommRing O] [Algebra R O] {d : ℕ}
  (b : Module.Basis (Fin d) R O) (r : ℕ)

/-- **Restriction of scalars of square matrices along a basis** `b` of `O` over `R`: the ring map
`M_r(O) → M_{rd}(R)` replacing each entry by the matrix of multiplication by it in the basis `b`,
the indices `Fin r × Fin d` being flattened to `Fin (r * d)`. -/
public def coefficientMatrixRingHom :
    Matrix (Fin r) (Fin r) O →+* Matrix (Fin (r * d)) (Fin (r * d)) R :=
  ((Matrix.reindexAlgEquiv R R finProdFinEquiv).toRingEquiv.toRingHom.comp
    (Matrix.compRingEquiv (Fin r) (Fin d) R).toRingHom).comp
    (Algebra.leftMulMatrix b).toRingHom.mapMatrix

/-- The entry of `coefficientMatrixRingHom b r M` at the flattened indices `(i, k)`, `(j, l)` is
the `(k, l)` entry of the matrix of multiplication by `M i j` in the basis `b`. -/
public theorem coefficientMatrixRingHom_apply (M : Matrix (Fin r) (Fin r) O) (i j : Fin r)
    (k l : Fin d) :
    coefficientMatrixRingHom b r M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) =
      Algebra.leftMulMatrix b (M i j) k l := by
  simp [coefficientMatrixRingHom]

/-- The `R`-linear identification `R^{rd} ≃ O^r` along the basis `b`: the coordinates indexed by
`(i, k)` are the `b`-coordinates of the `i`-th entry. -/
public def coefficientVecEquiv : (Fin (r * d) → R) ≃ₗ[R] (Fin r → O) :=
  (LinearEquiv.funCongrLeft R R finProdFinEquiv).trans
    ((LinearEquiv.curry R R (Fin r) (Fin d)).trans
      (LinearEquiv.piCongrRight fun _ => b.equivFun.symm))

/-- The `i`-th entry of `coefficientVecEquiv b r w` is the element of `O` whose `b`-coordinates
are the entries of `w` at the indices `(i, k)`. -/
public theorem coefficientVecEquiv_apply (w : Fin (r * d) → R) (i : Fin r) :
    coefficientVecEquiv b r w i = b.equivFun.symm fun k => w (finProdFinEquiv (i, k)) :=
  rfl

/-- **`coefficientMatrixRingHom M` is the matrix of `M` acting on `O^r`.** -/
public theorem coefficientVecEquiv_mulVec (M : Matrix (Fin r) (Fin r) O)
    (w : Fin (r * d) → R) :
    coefficientVecEquiv b r (coefficientMatrixRingHom b r M *ᵥ w) =
      M *ᵥ coefficientVecEquiv b r w := by
  funext i
  apply b.equivFun.injective
  funext k
  rw [coefficientVecEquiv_apply, LinearEquiv.apply_symm_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, Finset.sum_apply]
  rw [← (finProdFinEquiv (m := r) (n := d)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : (b.repr (coefficientVecEquiv b r w j) : Fin d → R) =
      fun l => w (finProdFinEquiv (j, l)) :=
    b.equivFun.apply_symm_apply _
  show _ = b.repr (M i j * coefficientVecEquiv b r w j) k
  rw [← Algebra.leftMulMatrix_mulVec_repr, hw]
  simp only [Matrix.mulVec, dotProduct, coefficientMatrixRingHom_apply]

/-- A scalar matrix acts on vectors by scalar multiplication. -/
public theorem _root_.Matrix.scalar_mulVec_eq_smul {n : Type*} [Fintype n] [DecidableEq n] (o : O)
    (v : n → O) :
    Matrix.scalar n o *ᵥ v = o • v := by
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- Scalar matrices commute with every matrix. -/
private theorem scalar_mul_comm {n : Type*} [Fintype n] [DecidableEq n] (o : O)
    (M : Matrix n n O) : Matrix.scalar n o * M = M * Matrix.scalar n o :=
  (Matrix.scalar_commute o (fun o' => Commute.all o o') M).eq

/-- The action of `O` on `R^{rd}`: the restriction of scalars of the scalar matrices. -/
public def coefficientScalarRingHom : O →+* Matrix (Fin (r * d)) (Fin (r * d)) R :=
  (coefficientMatrixRingHom b r).comp (Matrix.scalar (Fin r))

/-- `coefficientScalarRingHom b r o` acts on `R^{rd}` as scalar multiplication by `o` on `O^r`. -/
public theorem coefficientVecEquiv_scalar (o : O) (w : Fin (r * d) → R) :
    coefficientVecEquiv b r (coefficientScalarRingHom b r o *ᵥ w) =
      o • coefficientVecEquiv b r w := by
  rw [coefficientScalarRingHom, RingHom.comp_apply, coefficientVecEquiv_mulVec,
    Matrix.scalar_mulVec_eq_smul]

/-- The scalar matrices `coefficientScalarRingHom b r o` commute with the image of every matrix
under `coefficientMatrixRingHom b r`. -/
public theorem coefficientScalarRingHom_commute (o : O) (M : Matrix (Fin r) (Fin r) O) :
    coefficientScalarRingHom b r o * coefficientMatrixRingHom b r M =
      coefficientMatrixRingHom b r M * coefficientScalarRingHom b r o := by
  rw [coefficientScalarRingHom, RingHom.comp_apply, ← map_mul, ← map_mul, scalar_mul_comm]

end Algebra

/-! ### The `O`-sheaf of an `O`-linear representation -/

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) O)

/-- The `ℤ_ℓ`-representation `π₁(X, x̄) → GL_{rd}(ℤ_ℓ)` underlying an `O`-linear representation
`ρ : π₁(X, x̄) → GL_r(O)`: restriction of scalars along the basis `b`. -/
public def restrictScalarsRepresentation : EtaleFundamentalGroup X.1 x →* GL (Fin (r * d)) ℤ_[ℓ] :=
  (Units.map (coefficientMatrixRingHom b r).toMonoidHom).comp ρ

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The matrix of `restrictScalarsRepresentation B X x b ρ g` is the restriction of scalars of
the matrix of `ρ g`. -/
public theorem restrictScalarsRepresentation_val (g : EtaleFundamentalGroup X.1 x) :
    (restrictScalarsRepresentation B X x b ρ g).val = coefficientMatrixRingHom b r (ρ g).val :=
  rfl

variable (hρ : Continuous (restrictScalarsRepresentation B X x b ρ))

/-- **The `O`-sheaf `ℱ_ρ` of a representation `ρ : π₁(X, x̄) → GL_r(O)`**: the sheaf of the
underlying `ℤ_ℓ`-representation of rank `rd`, `O` acting through the scalar matrices. -/
public def coefficientRepresentationSheaf : LAdicSheaf.CoefficientSheaf B X ℓ O :=
  representationCoefficientSheaf B X x (restrictScalarsRepresentation B X x b ρ) hρ
    (coefficientScalarRingHom b r) fun o g => coefficientScalarRingHom_commute b r o (ρ g).val

/-- The stalk of `ℱ_ρ` at `s̄` is `O^r`, along a path `t` from `s̄` to `x̄`, as `ℤ_ℓ`-modules. -/
public def coefficientRepresentationSheafStalkEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    LAdicSheaf.stalk B X ℓ (coefficientRepresentationSheaf B X x b ρ hρ).toLAdicSheaf s ≃ₗ[ℤ_[ℓ]]
      (Fin r → O) :=
  (representationLevelTrivialization B X x (restrictScalarsRepresentation B X x b ρ) hρ
    t).stalkEquiv.trans (coefficientVecEquiv b r)

/-- The identification of the stalk of `ℱ_ρ` with `O^r` commutes with the action of `O`. -/
public theorem coefficientRepresentationSheafStalkEquiv_smul {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (o : O)
    (v : LAdicSheaf.stalk B X ℓ (coefficientRepresentationSheaf B X x b ρ hρ).toLAdicSheaf s) :
    coefficientRepresentationSheafStalkEquiv B X x b ρ hρ t (o • v) =
      o • coefficientRepresentationSheafStalkEquiv B X x b ρ hρ t v := by
  have h := representationLevelTrivialization_stalkEquiv_stalkMap B X x hρ hρ t
    (coefficientScalarRingHom b r o) (fun g => coefficientScalarRingHom_commute b r o (ρ g).val) v
  exact (congrArg (coefficientVecEquiv b r) h).trans (coefficientVecEquiv_scalar b r o _)

/-- **The stalks of `ℱ_ρ` are free of rank `r` over `O`**, along a path `t` from `s̄` to `x̄`. -/
public def coefficientRepresentationSheafStalkLinearEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    LAdicSheaf.stalk B X ℓ (coefficientRepresentationSheaf B X x b ρ hρ).toLAdicSheaf s ≃ₗ[O]
      (Fin r → O) :=
  { coefficientRepresentationSheafStalkEquiv B X x b ρ hρ t with
    map_smul' := fun o v => coefficientRepresentationSheafStalkEquiv_smul B X x b ρ hρ t o v }

/-- **An endomorphism `a` of the geometric point `s̄` acts on the stalk of `ℱ_ρ` by `ρ(g)`**, `g`
the transport along `t` of the automorphism `σ` of the fibre functor given by precomposition with
`a`. -/
public theorem coefficientRepresentationSheafStalkLinearEquiv_stalkEnd {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.hom = finiteEtaleFiberMap a)
    (v : LAdicSheaf.stalk B X ℓ (coefficientRepresentationSheaf B X x b ρ hρ).toLAdicSheaf s) :
    coefficientRepresentationSheafStalkLinearEquiv B X x b ρ hρ t
        ((coefficientRepresentationSheaf B X x b ρ hρ).stalkEnd a v) =
      (ρ (etaleFundamentalGroupMulEquiv t σ)).val *ᵥ
        coefficientRepresentationSheafStalkLinearEquiv B X x b ρ hρ t v := by
  have h := representationLevelTrivialization_stalkEquiv_stalkEnd B X x hρ t a σ hσ v
  exact (congrArg (coefficientVecEquiv b r) h).trans (coefficientVecEquiv_mulVec b r _ _)

/-- Conjugated by the trivialisation of the stalk, the action of `a` is the matrix `ρ(g)`. -/
public theorem conj_coefficientRepresentationSheaf_stalkEnd {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.hom = finiteEtaleFiberMap a) :
    (coefficientRepresentationSheafStalkLinearEquiv B X x b ρ hρ t).conj
        ((coefficientRepresentationSheaf B X x b ρ hρ).stalkEnd a) =
      Matrix.toLin' (ρ (etaleFundamentalGroupMulEquiv t σ)).val := by
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply_apply, coefficientRepresentationSheafStalkLinearEquiv_stalkEnd B X x
    b ρ hρ t a σ hσ, LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]

/-- **The `O`-trace of an endomorphism of the geometric point on the stalk of `ℱ_ρ` is
`tr ρ(g)`.** -/
public theorem trace_coefficientRepresentationSheaf_stalkEnd {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.hom = finiteEtaleFiberMap a) :
    LinearMap.trace O _ ((coefficientRepresentationSheaf B X x b ρ hρ).stalkEnd a) =
      (ρ (etaleFundamentalGroupMulEquiv t σ)).val.trace := by
  rw [← LinearMap.trace_conj' _ (coefficientRepresentationSheafStalkLinearEquiv B X x b ρ hρ t),
    conj_coefficientRepresentationSheaf_stalkEnd B X x b ρ hρ t a σ hσ, Matrix.trace_toLin'_eq]

/-! ### Twisting by a character -/

section Twist

variable {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The twist `g ↦ χ(g) ρ(g)` of a representation by a character** (the representation of
`ℱ_ρ ⊗ ℱ_χ`). -/
public def characterTwist (ρ : G →* GL n O) (χ : G →* Oˣ) : G →* GL n O where
  toFun g := ρ g * Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom (χ g)
  map_one' := by simp
  map_mul' g h := by
    ext : 1
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      (Matrix.scalar_commute (χ g : O) (fun o' => Commute.all _ o') (ρ h).val).eq]

/-- The matrix of `characterTwist ρ χ g` is `χ(g) • ρ(g)`. -/
public theorem characterTwist_val (ρ : G →* GL n O) (χ : G →* Oˣ) (g : G) :
    (characterTwist ρ χ g).val = (χ g : O) • (ρ g).val := by
  show (ρ g).val * Matrix.scalar n (χ g : O) = _
  rw [← scalar_mul_comm, Matrix.smul_eq_diagonal_mul]
  rfl

/-- The trace of `characterTwist ρ χ g` is `χ(g) tr ρ(g)`. -/
public theorem trace_characterTwist (ρ : G →* GL n O) (χ : G →* Oˣ) (g : G) :
    (characterTwist ρ χ g).val.trace = (χ g : O) * (ρ g).val.trace := by
  rw [characterTwist_val, Matrix.trace_smul, smul_eq_mul]

end Twist

variable (χ : EtaleFundamentalGroup X.1 x →* Oˣ)
  (hρχ : Continuous (restrictScalarsRepresentation B X x b (characterTwist ρ χ)))

/-- **The trace on the twist `ℱ_ρ ⊗ ℱ_χ`**: an endomorphism of the geometric point acts on the
stalk of the sheaf of `characterTwist ρ χ` with `O`-trace `χ(g) tr ρ(g)`. -/
public theorem trace_characterTwist_stalkEnd {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.hom = finiteEtaleFiberMap a) :
    LinearMap.trace O _
        ((coefficientRepresentationSheaf B X x b (characterTwist ρ χ) hρχ).stalkEnd a) =
      (χ (etaleFundamentalGroupMulEquiv t σ) : O) *
        (ρ (etaleFundamentalGroupMulEquiv t σ)).val.trace := by
  rw [trace_coefficientRepresentationSheaf_stalkEnd B X x b _ hρχ t a σ hσ, trace_characterTwist]

end Stacks.EtaleCohomology
