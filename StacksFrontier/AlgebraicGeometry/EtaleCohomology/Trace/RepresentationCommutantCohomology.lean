module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.CharacterSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel
public import Mathlib.RingTheory.Localization.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicCoefficientExtension

/-!
# The commutant of a representation acts on the rational cohomology of its sheaf

Let `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` be continuous and let `α : E → M_r(ℚ_ℓ)` be a homomorphism of
`ℚ_ℓ`-algebras whose image commutes with `ρ` (for instance `E` a finite extension of `ℚ_ℓ` and
`ρ = Res_{E/ℚ_ℓ} σ` the restriction of scalars of an `E`-linear representation).  The sheaf `ℱ_ρ`
is built from the integral model `P⁻¹ ρ P` of `ρ`; the elements `e` of `E` with `P⁻¹ α(e) P`
integral form a subring `S` of `E` acting on `ℱ_ρ` by the morphisms of these integral intertwiners,
and `E` is the localization of `S` at the powers of `ℓ`.  So `E` acts on the rational cohomology
`Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)`, compatibly with its `ℚ_ℓ`-structure, and `π_X^*` is `E`-linear.

## Main definitions

* `Stacks.EtaleCohomology.extendScalarsEndRingHom`: extension of scalars of endomorphisms
  from `ℤ_ℓ` to `ℚ_ℓ`.
* `Stacks.EtaleCohomology.conjIntegralSubring`: the subring of `E` of elements `e` with
  `P⁻¹ α(e) P` integral.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

open scoped IsMulCommutative

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### Extension of scalars of endomorphisms -/

section ExtendScalars

/-- **Extension of scalars of endomorphisms** from `ℤ_ℓ` to `ℚ_ℓ`, as a ring homomorphism
`End_{ℤ_ℓ}(H) → End_{ℚ_ℓ}(H ⊗ ℚ_ℓ)`. -/
public def extendScalarsEndRingHom (H : ModuleCat.{u + 1} ℤ_[ℓ]) :
    Module.End ℤ_[ℓ] H →+*
      Module.End ℚ_[ℓ] ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj H)
    where
  toFun g := ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (ModuleCat.ofHom g)).hom
  map_one' := by
    change ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map (𝟙 H)).hom = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_mul' g g' := by
    change ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (ModuleCat.ofHom g' ≫ ModuleCat.ofHom g)).hom = _
    rw [CategoryTheory.Functor.map_comp]
    rfl
  map_zero' := by
    rw [ModuleCat.ofHom_zero, CategoryTheory.Functor.map_zero]
    rfl
  map_add' g g' := by
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
    have := Functor.additive_of_preservesBinaryBiproducts
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
    rw [ModuleCat.ofHom_add, CategoryTheory.Functor.map_add]
    rfl

/-- `extendScalarsEndRingHom H g` is the image of `g` under extension of scalars to `ℚ_ℓ`. -/
public theorem extendScalarsEndRingHom_apply (H : ModuleCat.{u + 1} ℤ_[ℓ])
    (g : Module.End ℤ_[ℓ] H) :
    extendScalarsEndRingHom H g = ((ModuleCat.extendScalars.{0, 0, u + 1}
      (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map (ModuleCat.ofHom g)).hom :=
  rfl

/-- Extension of scalars of multiplication by `c ∈ ℤ_ℓ` is multiplication by `c`. -/
public theorem extendScalarsEndRingHom_smul_one (H : ModuleCat.{u + 1} ℤ_[ℓ]) (c : ℤ_[ℓ]) :
    extendScalarsEndRingHom H (c • 1) = (c : ℚ_[ℓ]) • 1 := by
  refine LinearMap.ext fun v => ?_
  induction v using TensorProduct.inductionOn with
  | tmul s m =>
    change s ⊗ₜ[ℤ_[ℓ]] ((c • 1 : Module.End ℤ_[ℓ] H) m) = _
    rw [LinearMap.smul_apply, Module.End.one_apply, TensorProduct.tmul_smul]
    rfl
  | add v w hv hw =>
    exact (map_add _ v w).trans ((congrArg₂ (· + ·) hv hw).trans (map_add _ v w).symm)

end ExtendScalars

/-! ### The integral part of the commutant -/

section Subring

variable {r : ℕ} (P : GL (Fin r) ℚ_[ℓ]) {E : Type} [CommRing E] [Algebra ℚ_[ℓ] E]
  (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ])

/-- Integral matrices are closed under addition. -/
public theorem IsIntegralMatrix.add {A B : Matrix (Fin r) (Fin r) ℚ_[ℓ]} (hA : IsIntegralMatrix A)
    (hB : IsIntegralMatrix B) : IsIntegralMatrix (A + B) := fun i j =>
  (Padic.nonarchimedean (A i j) (B i j)).trans (max_le (hA i j) (hB i j))

/-- Conjugation by `P` is multiplicative. -/
public theorem conj_mul_conj (A B : Matrix (Fin r) (Fin r) ℚ_[ℓ]) :
    (P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * A * P.val * ((P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * B * P.val) =
      (P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * (A * B) * P.val := by
  calc _ = (P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * A * (P.val * (P⁻¹ : GL (Fin r) ℚ_[ℓ]).val) * B *
        P.val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [P.mul_inv, Matrix.mul_one, Matrix.mul_assoc _ A B]

/-- **The integral part of `E` for `P`**: the elements `e` with `P⁻¹ α(e) P` integral. -/
public def conjIntegralSubring : Subring E where
  carrier := {e | IsIntegralMatrix ((P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * α e * P.val)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    rw [← conj_mul_conj]
    exact ha.mul hb
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one, Matrix.mul_one]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact isIntegralMatrix_one
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add, Matrix.mul_add, Matrix.add_mul] at ha hb ⊢
    exact ha.add hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, Matrix.mul_zero, Matrix.zero_mul]
    intro i j
    simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_neg, Matrix.mul_neg, Matrix.neg_mul] at ha ⊢
    intro i j
    rw [Matrix.neg_apply, norm_neg]
    exact ha i j

/-- `e` lies in the integral part of `E` for `P` if and only if `P⁻¹ α(e) P` is integral. -/
public theorem mem_conjIntegralSubring {e : E} :
    e ∈ conjIntegralSubring P α ↔
      IsIntegralMatrix ((P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * α e * P.val) :=
  Iff.rfl

/-- Elements of `ℤ_ℓ` are integral. -/
public theorem algebraMap_mem_conjIntegralSubring (c : ℤ_[ℓ]) :
    algebraMap ℚ_[ℓ] E c ∈ conjIntegralSubring P α := by
  rw [mem_conjIntegralSubring, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one c)).trans
    (isIntegralMatrix_one i j)

/-- The `ℤ_ℓ`-algebra structure of the integral part. -/
public instance conjIntegralSubring.algebra : Algebra ℤ_[ℓ] (conjIntegralSubring P α) :=
  (((algebraMap ℚ_[ℓ] E).comp (PadicInt.Coe.ringHom (p := ℓ))).codRestrict _
    fun c => algebraMap_mem_conjIntegralSubring P α c).toAlgebra

/-- Some `ℓ`-power multiple of every element is integral. -/
public theorem exists_pow_mul_mem_conjIntegralSubring (e : E) :
    ∃ N : ℕ, (ℓ : E) ^ N * e ∈ conjIntegralSubring P α := by
  set A := (P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * α e * P.val with hA
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ i, ∑ j, ‖A i j‖)
    (Nat.one_lt_cast.2 (Fact.out : ℓ.Prime).one_lt : (1 : ℝ) < ℓ)
  refine ⟨N, fun i j => ?_⟩
  have hc : (P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * α ((ℓ : E) ^ N * e) * P.val =
      ((ℓ : ℚ_[ℓ]) ^ N) • A := by
    rw [hA, show (ℓ : E) ^ N = algebraMap ℚ_[ℓ] E ((ℓ : ℚ_[ℓ]) ^ N) by simp, map_mul,
      AlgHom.commutes, ← Algebra.smul_def, Matrix.mul_smul, Matrix.smul_mul]
  have hle : ‖A i j‖ ≤ ∑ i, ∑ j, ‖A i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  rw [hc, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p, inv_pow,
    inv_mul_le_iff₀ (pow_pos (Nat.cast_pos.2 (Fact.out : ℓ.Prime).pos) N), mul_one]
  exact hle.trans hN.le

/-- **The integral matrix `P⁻¹ α(e) P`** of an integral element `e`, as a ring homomorphism. -/
public def conjIntegralLift : conjIntegralSubring P α →+* Matrix (Fin r) (Fin r) ℤ_[ℓ] where
  toFun e := IsIntegralMatrix.lift ((mem_conjIntegralSubring P α).1 e.2)
  map_one' := by
    apply mapMatrix_padicInt_injective
    rw [IsIntegralMatrix.mapMatrix_lift, map_one, OneMemClass.coe_one, map_one, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
  map_mul' a b := by
    apply mapMatrix_padicInt_injective
    rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift,
      IsIntegralMatrix.mapMatrix_lift, MulMemClass.coe_mul, map_mul, conj_mul_conj]
  map_zero' := by
    apply mapMatrix_padicInt_injective
    rw [IsIntegralMatrix.mapMatrix_lift, map_zero, ZeroMemClass.coe_zero, map_zero,
      Matrix.mul_zero, Matrix.zero_mul]
  map_add' a b := by
    apply mapMatrix_padicInt_injective
    rw [map_add, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift,
      IsIntegralMatrix.mapMatrix_lift, AddMemClass.coe_add, map_add, Matrix.mul_add,
      Matrix.add_mul]

/-- Read in `ℚ_ℓ`, the integral matrix `conjIntegralLift P α e` is `P⁻¹ α(e) P`. -/
public theorem mapMatrix_conjIntegralLift (e : conjIntegralSubring P α) :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (conjIntegralLift P α e) =
      (P⁻¹ : GL (Fin r) ℚ_[ℓ]).val * α e * P.val :=
  IsIntegralMatrix.mapMatrix_lift _

/-- **`E` is the localization of its integral part at the powers of `ℓ`.** -/
public instance isLocalization_conjIntegralSubring :
    IsLocalization (Submonoid.powers (ℓ : conjIntegralSubring P α)) E where
  map_units := by
    rintro ⟨_, k, rfl⟩
    have hℓ : IsUnit (ℓ : E) := by
      rw [← map_natCast (algebraMap ℚ_[ℓ] E)]
      exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)).map _
    simpa [Algebra.algebraMap_ofSubsemiring_apply] using hℓ.pow k
  surj e := by
    obtain ⟨N, hN⟩ := exists_pow_mul_mem_conjIntegralSubring P α e
    refine ⟨(⟨_, hN⟩, ⟨(ℓ : conjIntegralSubring P α) ^ N, N, rfl⟩), ?_⟩
    simp [Algebra.algebraMap_ofSubsemiring_apply, mul_comm]
  exists_of_eq {a b} h := ⟨1, by simpa using Subtype.ext h⟩

/-- The two maps `ℤ_ℓ → E` through the integral part and through `ℚ_ℓ` agree. -/
public theorem algebraMap_conjIntegralSubring_algebraMap (c : ℤ_[ℓ]) :
    algebraMap (conjIntegralSubring P α) E (algebraMap ℤ_[ℓ] (conjIntegralSubring P α) c) =
      algebraMap ℚ_[ℓ] E c :=
  rfl

end Subring

/-! ### The action on the rational cohomology of `ℱ_ρ` -/

section Conj

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
  {E : Type} [CommRing E] [Algebra ℚ_[ℓ] E] (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ])
  (hα : ∀ e g, α e * (ρ g).val = (ρ g).val * α e)

/-- The matrix `P` with `P⁻¹ ρ P` the integral model of `ρ` used to build `ℱ_ρ`. -/
public def representationSheafConj : GL (Fin r) ℚ_[ℓ] :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  (exists_conj_integral ρ hρ).choose

include hα in
/-- The integral intertwiners commute with the integral model. -/
public theorem conjIntegralLift_mul_integralModel
    (s : conjIntegralSubring (representationSheafConj B X x ρ hρ) α)
    (g : EtaleFundamentalGroup X.1 x) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    conjIntegralLift _ α s * (integralModel ρ hρ g).val =
      (integralModel ρ hρ g).val * conjIntegralLift _ α s := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  apply mapMatrix_padicInt_injective
  have h : (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ hρ g).val =
      ((representationSheafConj B X x ρ hρ)⁻¹ : GL (Fin r) ℚ_[ℓ]).val * (ρ g).val *
        (representationSheafConj B X x ρ hρ).val := by
    have h := congrArg Units.val (map_integralModel ρ hρ g)
    simp only [Units.val_mul] at h
    exact h
  rw [map_mul, map_mul, mapMatrix_conjIntegralLift, h, conj_mul_conj, conj_mul_conj, hα]

end Conj

/-! ### The rational cohomology of a sheaf with coefficients -/

namespace LAdicSheaf.CoefficientSheaf

section Rational

variable {B : BigEtaleSite.{u}} {X : B.Scheme}
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)

/-- The action of `O` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, the extension of scalars of its action on
`Hⁱ_c(X_k̄, F)`. -/
public def rationalIntegralRingHom : O →+* Module.End ℚ_[ℓ]
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :=
  (extendScalarsEndRingHom _).comp
    ((LAdicSheaf.geometricCompactlySupportedCohomologyEndRingHom f j kbar F.toLAdicSheaf i).comp
      F.act)

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The action of `ℤ_ℓ` through `O` is the canonical one. -/
public theorem rationalIntegralRingHom_algebraMap (c : ℤ_[ℓ]) :
    F.rationalIntegralRingHom f j kbar i (algebraMap ℤ_[ℓ] O c) =
      algebraMap ℚ_[ℓ] _ (c : ℚ_[ℓ]) := by
  conv_rhs => rw [Algebra.algebraMap_eq_smul_one]
  refine Eq.trans ?_ (extendScalarsEndRingHom_smul_one _ c)
  change extendScalarsEndRingHom _ (LAdicSheaf.geometricCompactlySupportedCohomologyEndRingHom f j
    kbar F.toLAdicSheaf i (F.act (algebraMap ℤ_[ℓ] O c))) = _
  congr 1
  refine LinearMap.ext fun v => ?_
  change (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
    (F.act (algebraMap ℤ_[ℓ] O c)).asHom i).hom v = c • v
  rw [LAdicSheaf.CoefficientSheaf.act_algebraMap]
  exact LAdicSheaf.geometricCompactlySupportedCohomologyMap_scalarEnd f j kbar _ i c v

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The geometric Frobenius commutes with the action of `O`. -/
public theorem commute_rationalIntegralRingHom (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (o : O) :
    Commute (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F.toLAdicSheaf i).hom
      (F.rationalIntegralRingHom f j kbar i o) := by
  change extendScalarsEndRingHom _ (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p
      q hcard F.toLAdicSheaf i).hom * extendScalarsEndRingHom _
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (F.act o).asHom i).hom =
    extendScalarsEndRingHom _ (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
        (F.act o).asHom i).hom *
      extendScalarsEndRingHom _ (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q
        hcard F.toLAdicSheaf i).hom
  rw [← map_mul, ← map_mul]
  congr 1
  exact congrArg ModuleCat.Hom.hom
    (LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius f j kbar p q hcard _ i)

/-- The commutative subalgebra of `End_{ℚ_ℓ}(Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ))` generated by the action
of `O`. -/
public def rationalAlgebra : Subalgebra ℚ_[ℓ] (Module.End ℚ_[ℓ]
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i)) :=
  Algebra.adjoin ℚ_[ℓ] (Set.range (F.rationalIntegralRingHom f j kbar i))

/-- The subalgebra generated by the action of `O` is commutative, as `O` is. -/
public instance rationalAlgebra.isMulCommutative :
    IsMulCommutative (F.rationalAlgebra f j kbar i) :=
  Algebra.isMulCommutative_adjoin ℚ_[ℓ] (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ -
    rw [Commute, SemiconjBy, ← map_mul, mul_comm, map_mul])

/-- The action of `O` with values in the commutative subalgebra it generates. -/
public def rationalIntegralRingHom' : O →+* F.rationalAlgebra f j kbar i :=
  (F.rationalIntegralRingHom f j kbar i).codRestrict _ fun o => Algebra.subset_adjoin ⟨o, rfl⟩

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The powers of `ℓ` act invertibly in the commutative subalgebra generated by the action of
`O`. -/
public theorem isUnit_rationalIntegralRingHom' (y : Submonoid.powers (ℓ : O)) :
    IsUnit (F.rationalIntegralRingHom' f j kbar i y) := by
  obtain ⟨_, k, rfl⟩ := y
  rw [map_pow, map_natCast, ← map_natCast (algebraMap ℚ_[ℓ] _)]
  exact ((isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)).map _).pow k

variable (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

/-- **The action of `E = O[1/ℓ]` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`**, extending that of `O`. -/
public def rationalRingHom : E →+* Module.End ℚ_[ℓ]
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :=
  (F.rationalAlgebra f j kbar i).val.toRingHom.comp
    (IsLocalization.lift (M := Submonoid.powers (ℓ : O))
      (F.isUnit_rationalIntegralRingHom' f j kbar i))

omit [Algebra ℚ_[ℓ] E] [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The action of `E` takes values in the commutative subalgebra generated by the action of `O`. -/
public theorem rationalRingHom_mem (e : E) :
    F.rationalRingHom f j kbar i E e ∈ F.rationalAlgebra f j kbar i :=
  (IsLocalization.lift (M := Submonoid.powers (ℓ : O))
    (F.isUnit_rationalIntegralRingHom' f j kbar i) e).2

omit [Algebra ℚ_[ℓ] E] [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The action of `E` extends that of `O`. -/
public theorem rationalRingHom_algebraMap_apply (o : O) :
    F.rationalRingHom f j kbar i E (algebraMap O E o) = F.rationalIntegralRingHom f j kbar i o := by
  change (IsLocalization.lift (M := Submonoid.powers (ℓ : O))
    (F.isUnit_rationalIntegralRingHom' f j kbar i) (algebraMap O E o)).1 = _
  rw [IsLocalization.lift_eq]
  rfl

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The action of `E` restricts to the `ℚ_ℓ`-structure, when `ℤ_ℓ → O → E` and `ℤ_ℓ → ℚ_ℓ → E`
agree. -/
public theorem rationalRingHom_algebraMap
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    (c : ℚ_[ℓ]) :
    F.rationalRingHom f j kbar i E (algebraMap ℚ_[ℓ] E c) = algebraMap ℚ_[ℓ] _ c := by
  have h : ((F.rationalRingHom f j kbar i E).comp (algebraMap ℚ_[ℓ] E)).comp
      (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = (algebraMap ℚ_[ℓ] _).comp (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    refine RingHom.ext fun c => ?_
    change F.rationalRingHom f j kbar i E (algebraMap ℚ_[ℓ] E (c : ℚ_[ℓ])) =
      algebraMap ℚ_[ℓ] _ (c : ℚ_[ℓ])
    rw [← hOE, rationalRingHom_algebraMap_apply, rationalIntegralRingHom_algebraMap]
  exact RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[ℓ]) h) c

omit [Algebra ℚ_[ℓ] E] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The geometric Frobenius commutes with the action of `E`.** -/
public theorem commute_rationalRingHom (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (e : E) :
    Commute (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F.toLAdicSheaf i).hom
      (F.rationalRingHom f j kbar i E e) :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute (F.rationalRingHom_mem f j kbar i E e) (by
    rintro _ ⟨o, rfl⟩
    exact F.commute_rationalIntegralRingHom f j kbar i p q hcard o)

/-- **The `E`-module structure on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.** -/
public abbrev rationalCohomologyModule :
    Module E
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :=
  Module.compHom _ (F.rationalRingHom f j kbar i E)

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The `E`-module structure on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is compatible with its `ℚ_ℓ`-structure,
when `ℤ_ℓ → O → E` and `ℤ_ℓ → ℚ_ℓ → E` agree. -/
public theorem rationalCohomologyModule_isScalarTower
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c) :
    letI := F.rationalCohomologyModule f j kbar i E
    IsScalarTower ℚ_[ℓ] E
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf
        i) := by
  let := F.rationalCohomologyModule f j kbar i E
  refine ⟨fun c e v => ?_⟩
  change F.rationalRingHom f j kbar i E (c • e) v = c • F.rationalRingHom f j kbar i E e v
  rw [Algebra.smul_def, map_mul, F.rationalRingHom_algebraMap f j kbar i E hOE,
    Module.End.mul_apply, Module.algebraMap_end_apply]

/-- **`π_X^*` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is `E`-linear.** -/
public def rationalGeometricCompactlySupportedFrobenius (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) :
    letI := F.rationalCohomologyModule f j kbar i E
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) →ₗ[E]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :=
  letI := F.rationalCohomologyModule f j kbar i E
  { toFun := (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
      F.toLAdicSheaf i).hom
    map_add' := map_add _
    map_smul' := fun e v =>
      LinearMap.congr_fun (F.commute_rationalRingHom f j kbar i E p q hcard e).eq v }

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- Restricted to `ℚ_ℓ`, the `E`-linear `π_X^*` is the geometric Frobenius on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`. -/
public theorem rationalGeometricCompactlySupportedFrobenius_restrictScalars
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) :
    letI := F.rationalCohomologyModule f j kbar i E
    letI := F.rationalCohomologyModule_isScalarTower f j kbar i E hOE
    (F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard).restrictScalars ℚ_[ℓ] =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F.toLAdicSheaf i).hom :=
  rfl

end Rational

end LAdicSheaf.CoefficientSheaf

/-! ### The commutant of a representation -/

section Sheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
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
  {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
  {E : Type} [CommRing E] [Algebra ℚ_[ℓ] E] (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ])
  (hα : ∀ e g, α e * (ρ g).val = (ρ g).val * α e)

/-- **`ℱ_ρ` as a sheaf with coefficients in the integral part of `E`**, acting through the
integral intertwiners `P⁻¹ α(e) P`. -/
public def representationSheafCommutantCoefficientSheaf :
    LAdicSheaf.CoefficientSheaf B X ℓ
      (conjIntegralSubring (representationSheafConj B X x ρ hρ) α) :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  representationCoefficientSheaf B X x (integralModel ρ hρ) (continuous_integralModel ρ hρ)
    (conjIntegralLift _ α) (conjIntegralLift_mul_integralModel B X x ρ hρ α hα)

/-- The underlying ℓ-adic sheaf of `representationSheafCommutantCoefficientSheaf` is `ℱ_ρ`. -/
public theorem representationSheafCommutantCoefficientSheaf_toLAdicSheaf :
    (representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).toLAdicSheaf =
      LAdicSheaf.representationSheaf B X x ρ hρ :=
  rfl

end Sheaf

end Stacks.EtaleCohomology

end
