module

public import StacksFrontier.NumberTheory.Drinfeld.LFunctionLattice
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharPolynomial

/-!
# The Frobenius matrices of `ρ ⊗ χ` and of its `O_E`-sheaf

Let `X` be a connected scheme of finite type over a finite field `k`, `E` a finite extension of
`ℚ_ℓ` and `σ : π₁(X, x̄) → GL_r(E)` a representation (for Drinfeld's proof of
[Tag 03VU](https://stacks.math.columbia.edu/tag/03VU), `σ = ρ ⊗ χ`). Its L-function is the Euler
product of the local factors `det(1 - σ(F_y) T^{deg y})⁻¹` at the geometric Frobenius elements
`F_y`; these factors do not depend on the choice of `F_y`, which is defined up to conjugation.

If `σ_O : π₁(X, x̄) → GL_r(O_E)` is an integral model, `σ_O = P σ P⁻¹` over `E`, the `O_E`-sheaf
`ℱ` of `σ_O` (`Stacks.EtaleCohomology.coefficientRepresentationSheaf`) is a `ℤ_ℓ`-sheaf, and
its `ℚ_ℓ`-L-function `L(X, ℱ)` (Tag 03UX) has at `y` the local factor of the restriction of
scalars of `σ(F_y)` from `E` to `ℚ_ℓ`: the characteristic polynomial of the geometric Frobenius
`π_y^*` on the rational stalk of `ℱ` is that of the `ℚ_ℓ`-matrix of `σ(F_y)` acting on
`E^r = ℚ_ℓ^{r [E : ℚ_ℓ]}`.

## Main definitions

* `Stacks.Drinfeld.representationFrobeniusMatrices`: the matrices `σ(F_y)`, as
  `Stacks.EtaleCohomology.FrobeniusMatrices f E`.
* `Stacks.Drinfeld.restrictScalarsFrobeniusMatrices`: the restriction of scalars of a family of
  Frobenius matrices along a basis.

## Main results

* `Stacks.Drinfeld.localCharSeries_eq_of_charpoly_eq`: the local factor depends only on the
  characteristic polynomial.
* `Stacks.Drinfeld.localEulerFactor_frobeniusDataOfPath`: the local factor at `y` is that of
  `σ(F)` for every geometric Frobenius element `F = (frobeniusDataOfPath x y t).element⁻¹`;
  `Stacks.Drinfeld.localEulerFactor_of_isGeometricFrobeniusAt` for those at a place.
* `Stacks.Drinfeld.charpoly_rationalStalkFrobenius_coefficientRepresentationSheaf`: the
  characteristic polynomial of `π_y^*` on the rational stalk of `ℱ` is that of the restriction of
  scalars of `σ(F_y)`.
* `Stacks.Drinfeld.rationalLFunction_coefficientRepresentationSheaf`: `L(X, ℱ)` is the L-function
  of the restriction of scalars of the Frobenius matrices of `σ`.
* `Stacks.Drinfeld.rationalLFunction_twistSheaf`: the same for the sheaf of `ρ_O ⊗ χ_O` and the
  Frobenius matrices of `ρ ⊗ χ`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
  Stacks.Frobenius Matrix Module

universe u

namespace Stacks.Drinfeld

/-! ### Local factors and characteristic polynomials -/

section LocalFactor

variable {Λ : Type*} [CommRing Λ] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]

/-- The polynomial local factor `det(1 - A T^d)` is the reversed characteristic polynomial
`det(1 - A T)` evaluated at `T^d`. -/
public theorem localCharPolynomial_eq_expand_charpolyRev (A : Matrix n n Λ) (d : ℕ) :
    localCharPolynomial A d = Polynomial.expand Λ d A.charpolyRev := by
  rw [localCharPolynomial, Matrix.charpolyRev, AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, localCharPolyMatrix_apply]
  by_cases h : i = j <;> simp [h, Matrix.sub_apply, Matrix.smul_apply]

/-- **The local factor depends only on the characteristic polynomial.** -/
public theorem localCharSeries_eq_of_charpoly_eq (A : Matrix n n Λ) (B : Matrix m m Λ)
    (h : A.charpoly = B.charpoly) (d : ℕ) : localCharSeries A d = localCharSeries B d := by
  rw [← coe_localCharPolynomial, ← coe_localCharPolynomial,
    localCharPolynomial_eq_expand_charpolyRev, localCharPolynomial_eq_expand_charpolyRev,
    ← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, h]

/-- The local Euler factor depends only on the characteristic polynomial. -/
public theorem localEulerFactor_eq_of_charpoly_eq (A : Matrix n n Λ) (B : Matrix m m Λ)
    (h : A.charpoly = B.charpoly) (d : ℕ) : localEulerFactor A d = localEulerFactor B d := by
  rw [localEulerFactor, localEulerFactor, localCharSeries_eq_of_charpoly_eq A B h]

end LocalFactor

/-! ### Restriction of scalars along a localisation -/

section RestrictScalars

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E] [Algebra ℤ_[ℓ] E] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E] {d : ℕ}
  (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) (r : ℕ)

/-- **Restriction of scalars commutes with inverting `ℓ`**: the restriction of scalars of an
`O_E`-matrix along a basis `b` of `O_E`, read over `ℚ_ℓ`, is the restriction of scalars of the
matrix read over `E`, along the `ℚ_ℓ`-basis of `E` given by `b`. -/
public theorem map_coefficientMatrixRingHom
    (M : Matrix (Fin r) (Fin r) (integralClosure ℤ_[ℓ] E)) :
    (coefficientMatrixRingHom b r M).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      coefficientMatrixRingHom (rationalBasis b) r (M.map (algebraMap _ E)) := by
  ext p q
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [Matrix.map_apply, coefficientMatrixRingHom_apply, coefficientMatrixRingHom_apply,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply,
    Basis.localizationLocalization_apply, ← map_mul]
  exact (b.localizationLocalization_repr_algebraMap ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ]) E _ k).symm

/-- Restriction of scalars of a conjugate is a conjugate, so it has the same characteristic
polynomial. -/
public theorem charpoly_coefficientMatrixRingHom_conj {R O : Type*} [CommRing R] [CommRing O]
    [Algebra R O] {d : ℕ} (b : Basis (Fin d) R O) (P : GL (Fin r) O)
    (A : Matrix (Fin r) (Fin r) O) :
    (coefficientMatrixRingHom b r (P * A * P⁻¹ : Matrix (Fin r) (Fin r) O)).charpoly =
      (coefficientMatrixRingHom b r A).charpoly := by
  let Q : GL (Fin (r * d)) R := Units.map (coefficientMatrixRingHom b r).toMonoidHom P
  have hQ : ((Q⁻¹ : GL (Fin (r * d)) R) : Matrix (Fin (r * d)) (Fin (r * d)) R) =
      coefficientMatrixRingHom b r ((P⁻¹ : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) := by
    rw [← map_inv]
    rfl
  rw [map_mul, map_mul]
  show (Q.val * _ * coefficientMatrixRingHom b r ((P⁻¹ : GL (Fin r) O) :
    Matrix (Fin r) (Fin r) O)).charpoly = _
  rw [← hQ, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]

end RestrictScalars

/-! ### The Frobenius matrices of a representation -/

section FrobeniusMatrices

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [ConnectedSpace X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (base : GeometricPoint X)
  {Λ : Type*} [CommRing Λ] {r : ℕ}

/-- **The Frobenius matrices of a representation** `σ : π₁(X, x̄) → GL_r(Λ)`: at a closed point
`y` the matrix `σ(F_y)` of the geometric Frobenius element
`Stacks.EtaleCohomology.geometricFrobeniusFamily`. The local factors do not depend on the choice
of `F_y` (`Stacks.Drinfeld.localEulerFactor_frobeniusDataOfPath`). -/
public def representationFrobeniusMatrices (σ : EtaleFundamentalGroup X base →* GL (Fin r) Λ) :
    FrobeniusMatrices f Λ where
  rank _ := r
  matrix y := (σ (geometricFrobeniusFamily f base y)).val

/-- **The local factor at `y` is that of `σ(F)` for every geometric Frobenius element `F` at
`y`**, transported along any path `t`: the geometric Frobenius elements at `y` are conjugate and
the local factor is invariant under conjugation. -/
public theorem localEulerFactor_frobeniusDataOfPath
    (σ : EtaleFundamentalGroup X base →* GL (Fin r) Λ) (y : closedPoints X)
    [Finite (X.residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt X y.1) ≅ finiteEtaleFiberFunctor base) :
    localEulerFactor (σ (frobeniusDataOfPath base y t).element⁻¹).val (residueDegree f y.1) =
      (representationFrobeniusMatrices f base σ).localFactor y := by
  have := finite_residueField f y.1 y.2
  set t' := (nonempty_finiteEtaleFiberFunctorIso X (geometricPointAt X y.1) base).some
  let g : EtaleFundamentalGroup X base := Aut.of (t.symm ≪≫ t')
  have hg : (frobeniusDataOfPath base y t').element =
      g * (frobeniusDataOfPath base y t).element * g⁻¹ := by
    rw [← FrobeniusData.element_path_trans]
    congr 2
    simp only [g, frobeniusDataOfPath]
    exact (Iso.self_symm_id_assoc t t').symm
  have hF : geometricFrobeniusFamily f base y =
      g * (frobeniusDataOfPath base y t).element⁻¹ * g⁻¹ := by
    show (frobeniusDataOfPath base y t').element⁻¹ = _
    rw [hg]
    group
  rw [FrobeniusMatrices.localFactor]
  show _ = localEulerFactor (σ (geometricFrobeniusFamily f base y)).val _
  rw [hF, map_mul, map_mul, Units.val_mul, Units.val_mul, map_inv]
  exact (localEulerFactor_conj _ _ (by rw [← Units.val_mul]; simp)).symm

/-- The local factor at the centre of a place is that of `σ(F)` for every geometric Frobenius
element `F` at that place (`Stacks.Adeles.GlobalFunctionField.IsGeometricFrobeniusAt`). -/
public theorem localEulerFactor_of_isGeometricFrobeniusAt [IsIntegral X]
    (σ : EtaleFundamentalGroup X base →* GL (Fin r) Λ)
    {v : Stacks.Adeles.Place X.functionField} {F : EtaleFundamentalGroup X base}
    (hF : Stacks.Adeles.GlobalFunctionField.IsGeometricFrobeniusAt base v F) :
    ∃ y : closedPoints X, Stacks.Adeles.GlobalFunctionField.IsCentreOf v y.1 ∧
      localEulerFactor (σ F).val (residueDegree f y.1) =
        (representationFrobeniusMatrices f base σ).localFactor y := by
  obtain ⟨y, hy, _, t, rfl⟩ := hF
  exact ⟨y, hy, localEulerFactor_frobeniusDataOfPath f base σ y t⟩

/-- **Restriction of scalars of Frobenius matrices** along a basis `b` of `O` over `R`: the
matrix at `y` is `coefficientMatrixRingHom b` of the given one. -/
public def restrictScalarsFrobeniusMatrices {R O : Type*} [CommRing R] [CommRing O]
    [Algebra R O] {d : ℕ} (b : Basis (Fin d) R O) (D : FrobeniusMatrices f O) :
    FrobeniusMatrices f R where
  rank y := D.rank y * d
  matrix y := coefficientMatrixRingHom b (D.rank y) (D.matrix y)

end FrobeniusMatrices

/-! ### The Frobenius matrices of the `O_E`-sheaf -/

section Sheaf

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
  {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra ℤ_[ℓ] E]
  [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E] {d : ℕ} (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))
  (σO : EtaleFundamentalGroup X.1 x →* GL (Fin r) (integralClosure ℤ_[ℓ] E))
  (hσO : Continuous (restrictScalarsRepresentation B X x b σO))
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin r) E) (P : GL (Fin r) E)
  (hP : ∀ g, Matrix.GeneralLinearGroup.map (algebraMap (integralClosure ℤ_[ℓ] E) E) (σO g) =
    P * σ g * P⁻¹)

/-- The rational stalk is a free `ℚ_ℓ`-module (it is a vector space); stated here since instance
search times out finding it through the tensor product. -/
local instance moduleFree_rationalStalkLeft_lFunctionFrobenius (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (y : GeometricPoint X.1) : Module.Free ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B X ℓ F y) :=
  Module.Free.of_divisionRing _ _

include hP in
/-- **The geometric Frobenius `π_y^*` on the rational stalk of the `O_E`-sheaf `ℱ` of `σ_O` has
the characteristic polynomial of the restriction of scalars of `σ(F_y)`** from `E` to `ℚ_ℓ`
(along the `ℚ_ℓ`-basis of `E` given by `b`), for the geometric Frobenius element
`F_y = (frobeniusDataOfPath x y t).element⁻¹` of any path `t`; here `σ_O = P σ P⁻¹` over `E`. -/
public theorem charpoly_rationalStalkFrobenius_coefficientRepresentationSheaf
    (y : closedPoints X.1) [Finite (X.1.residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt X.1 y.1) ≅ finiteEtaleFiberFunctor x) :
    (LAdicSheaf.rationalStalkFrobenius B X ℓ
        (coefficientRepresentationSheaf B X x b σO hσO).toLAdicSheaf y.1 inferInstance).charpoly =
      (coefficientMatrixRingHom (rationalBasis b) r
        (σ (frobeniusDataOfPath x y t).element⁻¹).val).charpoly := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have h := charpoly_rationalStalkEnd_representationLAdicSheaf B X x
    (restrictScalarsRepresentation B X x b σO) hσO t (frobeniusPointHom X.1 y.1)
    ((frobeniusDataOfPath x y t).localElement⁻¹) (inv_localElement_hom x y t)
  have he : etaleFundamentalGroupMulEquiv t (frobeniusDataOfPath x y t).localElement⁻¹ =
      (frobeniusDataOfPath x y t).element⁻¹ :=
    MulEquiv.map_inv (etaleFundamentalGroupMulEquiv t) _
  rw [he, restrictScalarsRepresentation_val] at h
  refine h.trans ?_
  set F := (frobeniusDataOfPath x y t).element⁻¹
  have hmap : (σO F).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) =
      (P * σ F * P⁻¹ : GL (Fin r) E).val := by
    rw [← hP F]
    rfl
  rw [← Matrix.charpoly_map, map_coefficientMatrixRingHom, hmap, Units.val_mul, Units.val_mul]
  exact charpoly_coefficientMatrixRingHom_conj r (rationalBasis b) P _

variable {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]

include hP in
/-- **The local factor of `L(X, ℱ)` at `y`** is the local factor of the restriction of scalars to
`ℚ_ℓ` of `σ(F_y)`. -/
public theorem localFactor_frobeniusMatrices_coefficientRepresentationSheaf
    (y : closedPoints X.1) :
    (LAdicSheaf.frobeniusMatrices B X ℓ
        (coefficientRepresentationSheaf B X x b σO hσO).toLAdicSheaf f).localFactor y =
      (restrictScalarsFrobeniusMatrices f (rationalBasis b)
        (representationFrobeniusMatrices f x σ)).localFactor y := by
  have := finite_residueField f y.1 y.2
  rw [LAdicSheaf.localFactor_frobeniusMatrices, FrobeniusMatrices.localFactor,
    charPowerSeries_eq_localCharSeries_matrixOf]
  show PowerSeries.invOfUnit _ 1 = PowerSeries.invOfUnit _ 1
  congr 1
  refine localCharSeries_eq_of_charpoly_eq _ _ ?_ _
  rw [matrixOf, LinearMap.charpoly_toMatrix]
  exact charpoly_rationalStalkFrobenius_coefficientRepresentationSheaf B X x b σO hσO σ P hP y _

include hP in
/-- **`L(X, ℱ)` is the L-function of the restriction of scalars of the Frobenius matrices of
`σ`**: the `ℚ_ℓ`-L-function (Tag 03UX) of the `O_E`-sheaf of an integral model `σ_O = P σ P⁻¹`
is the Euler product of the local factors `det(1 - Res_{E/ℚ_ℓ} σ(F_y) T^{deg y})⁻¹`. -/
public theorem rationalLFunction_coefficientRepresentationSheaf [QuasiCompact f] :
    LAdicSheaf.rationalLFunction B X ℓ (coefficientRepresentationSheaf B X x b σO hσO).toLAdicSheaf
        f =
      (restrictScalarsFrobeniusMatrices f (rationalBasis b)
        (representationFrobeniusMatrices f x σ)).lFunction :=
  FrobeniusMatrices.lFunction_congr _ fun y =>
    localFactor_frobeniusMatrices_coefficientRepresentationSheaf B X x b σO hσO σ P hP f y

end Sheaf

/-! ### The sheaf of `ρ ⊗ χ` -/

section Twist

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (ℓ : ℕ) [Fact ℓ.Prime] {r : ℕ}
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
  {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra ℤ_[ℓ] E]
  [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E] [TopologicalSpace E] [IsModuleTopology ℚ_[ℓ] E] {d : ℕ}
  (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) E)
  (hρ : Continuous fun g => (ρ g : Matrix (Fin r) (Fin r) E))
  (χ : EtaleFundamentalGroup X.1 x →* Eˣ) (hχ : Continuous fun g => (χ g : E))

/-- **The `O_E`-sheaf `ℱ_{ρ ⊗ χ}`**: the sheaf of the twist `ρ_O ⊗ χ_O` of the integral model of
`ρ` (`Stacks.Drinfeld.integralClosureModel`) by the integral character
(`Stacks.Drinfeld.integralClosureCharacter`), along the basis `b` of `O_E`. -/
public def twistSheaf : LAdicSheaf.CoefficientSheaf B X ℓ (integralClosure ℤ_[ℓ] E) :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  coefficientRepresentationSheaf B X x b
    (characterTwist (integralClosureModel ℓ ρ hρ) (integralClosureCharacter ℓ χ hχ))
    (continuous_restrictScalars_characterTwist_integralClosureModel ρ hρ χ hχ b)

variable {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- **The local factors of `L(X, ℱ_{ρ ⊗ χ})`**: at `y`, the local factor of the restriction of
scalars to `ℚ_ℓ` of `χ(F_y) ρ(F_y)`. -/
public theorem localFactor_frobeniusMatrices_twistSheaf (y : closedPoints X.1) :
    (LAdicSheaf.frobeniusMatrices B X ℓ (twistSheaf B X x ℓ b ρ hρ χ hχ).toLAdicSheaf f).localFactor
        y =
      (restrictScalarsFrobeniusMatrices f (rationalBasis b)
        (representationFrobeniusMatrices f x (characterTwist ρ χ))).localFactor y :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  localFactor_frobeniusMatrices_coefficientRepresentationSheaf B X x b _ _ (characterTwist ρ χ)
    (integralClosureModelConj ℓ ρ hρ) (map_characterTwist_integralClosureModel ρ hρ χ hχ)
    f y

/-- **`L(X, ℱ_{ρ ⊗ χ}) = L(X, Res_{E/ℚ_ℓ}(ρ ⊗ χ))`**: the `ℚ_ℓ`-L-function of the sheaf of
`ρ_O ⊗ χ_O` is the Euler product over the closed points of
`det(1 - Res_{E/ℚ_ℓ}(χ(F_y) ρ(F_y)) T^{deg y})⁻¹`. -/
public theorem rationalLFunction_twistSheaf [QuasiCompact f] :
    LAdicSheaf.rationalLFunction B X ℓ (twistSheaf B X x ℓ b ρ hρ χ hχ).toLAdicSheaf f =
      (restrictScalarsFrobeniusMatrices f (rationalBasis b)
        (representationFrobeniusMatrices f x (characterTwist ρ χ))).lFunction :=
  FrobeniusMatrices.lFunction_congr _ fun y =>
    localFactor_frobeniusMatrices_twistSheaf B X x ℓ b ρ hρ χ hχ f y

end Twist

end Stacks.Drinfeld

end
