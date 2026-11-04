module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelModuleIntertwiner
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.MatrixContinuousModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationOfTrivializations
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafRestrictScalarsNaturality

/-!
# Lisse sheaves with coefficients in `O / ℓⁿ` restricted to `ℤ / ℓⁿ`

Let `O` be a finite free `ℤ_ℓ`-algebra with basis `β` of rank `D` (the integers of a finite
extension of `ℚ_ℓ`), and `τ : π₁(X, x̄) → GL_m(O)` a representation whose reductions modulo every
`ℓⁿ` have open kernel. Restricting scalars along `β` gives `Res_β τ : π₁(X, x̄) → GL_{mD}(ℤ_ℓ)`
(`Stacks.EtaleCohomology.restrictScalarsRepresentation`), which is then continuous
(`Stacks.EtaleCohomology.continuous_restrictScalarsRepresentation_of_isOpen`): the reduction of
`Res_β M` modulo `ℓⁿ` only depends on the reduction of `M` modulo `ℓⁿ O`.

Reducing the coordinates along `β` modulo `ℓⁿ` identifies `(ℤ/ℓⁿ)^{mD}` with `(O/ℓⁿ)^m`
(`Stacks.EtaleCohomology.coefficientLevelAddEquiv`), carrying the reduction of `Res_β τ` to the
reduction of `τ`, the scalars `c ∈ ℤ/ℓⁿ` to their images in `O/ℓⁿ`, and the matrix of
multiplication by `o ∈ O` to multiplication by `o`. Hence the lisse sheaf of `(O/ℓⁿ)^m` with
`π₁` acting through `τ mod ℓⁿ`, read as a sheaf of `ℤ/ℓⁿ`-modules, is the lisse sheaf of the
level module of `Res_β τ` (`Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIntegersIso`),
and multiplication by `o` on the former is the lisse sheaf of multiplication by the matrix of `o`
on the latter (`Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIntegersIso_smul`). This is
how the sheaves with coefficients in `O/ℓⁿ` are compared with the levels of ℓ-adic sheaves in
piece L6 of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.coefficientLevelAddEquiv`: `(ℤ/ℓⁿ)^{mD} ≃ (O/ℓⁿ)^m`.
* `Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIntegersIso`.

## Main results

* `Stacks.EtaleCohomology.continuous_restrictScalarsRepresentation_of_isOpen`.
* `Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIntegersIso_smul`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.GroupCohomology Matrix

open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] neZero_pow_of_fact_prime discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

/-! ### Coordinates along a basis, modulo `ℓⁿ` -/

section Algebra

variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {D : ℕ}
  (β : Module.Basis (Fin D) ℤ_[ℓ] O) (m : ℕ)

/-- **The reduction of `Res_β M` modulo `ℓᴺ` only depends on the reduction of `M` modulo
`ℓᴺ O`**: the entries of `Res_β M` are the coordinates of the products `M i j * β l`, and those of
`ℓᴺ t * β l` are divisible by `ℓᴺ`. -/
theorem map_toZModPow_coefficientMatrixRingHom_eq (N : ℕ) {M M' : Matrix (Fin m) (Fin m) O}
    (h : M.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ N})) =
      M'.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ N}))) :
    (coefficientMatrixRingHom β m M).map (PadicInt.toZModPow N) =
      (coefficientMatrixRingHom β m M').map (PadicInt.toZModPow N) := by
  have hd : ∀ i j, ∃ t : O, t * (ℓ : O) ^ N = M i j - M' i j := fun i j =>
    Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun h i) j))
  choose t ht using hd
  ext p q
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Matrix.map_apply, coefficientMatrixRingHom_apply, Algebra.leftMulMatrix_eq_repr_mul]
  have hM : M i j * β l = M' i j * β l + ((ℓ : ℤ_[ℓ]) ^ N) • (t i j * β l) := by
    rw [Algebra.smul_def, map_pow, map_natCast, ← mul_assoc, mul_comm ((ℓ : O) ^ N), ht i j,
      sub_mul, add_sub_cancel]
  rw [hM, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_add,
    RingHom.map_mul, RingHom.map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul,
    add_zero]

variable (n : ℕ) [CharP (O ⧸ Ideal.span {(ℓ : O) ^ n}) (ℓ ^ n)]

/-- The reduction modulo `ℓⁿ O` of an `ℓ`-adic integer is the image of its reduction modulo
`ℓⁿ`. -/
theorem mk_algebraMap_eq_castHom_toZModPow (c : ℤ_[ℓ]) :
    Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}) (algebraMap ℤ_[ℓ] O c) =
      ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ n}) (PadicInt.toZModPow n c) := by
  have hc : c - (((PadicInt.toZModPow n c).val : ℕ) : ℤ_[ℓ]) ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hc
  have he : algebraMap ℤ_[ℓ] O c = algebraMap ℤ_[ℓ] O t * (ℓ : O) ^ n +
      (((PadicInt.toZModPow n c).val : ℕ) : O) := by
    rw [← map_natCast (algebraMap ℤ_[ℓ] O) ((PadicInt.toZModPow n c).val),
      ← map_natCast (algebraMap ℤ_[ℓ] O) ℓ, ← map_pow, ← map_mul, ← map_add, ht, sub_add_cancel]
  rw [he, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _),
    mul_zero, zero_add, map_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n c), map_natCast]

/-- The map `(ℤ/ℓⁿ)^{mD} → (O/ℓⁿ)^m`, `w ↦ (∑ₖ w_{(i, k)} β k)ᵢ` modulo `ℓⁿ`. -/
def coefficientLevelAddHom :
    (Fin (m * D) → ZMod (ℓ ^ n)) →+ (Fin m → O ⧸ Ideal.span {(ℓ : O) ^ n}) where
  toFun w i := ∑ k : Fin D,
    ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ n}) (w (finProdFinEquiv (i, k))) *
      Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}) (β k)
  map_zero' := by
    funext i
    simp
  map_add' a b := by
    funext i
    simp [add_mul, Finset.sum_add_distrib]

/-- On reductions of `ℓ`-adic vectors, `Stacks.EtaleCohomology.coefficientLevelAddHom` is the
reduction of `Stacks.EtaleCohomology.coefficientVecEquiv`. -/
theorem coefficientLevelAddHom_toZModPow (v : Fin (m * D) → ℤ_[ℓ]) :
    coefficientLevelAddHom β m n (fun p => PadicInt.toZModPow n (v p)) =
      fun i => Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}) (coefficientVecEquiv β m v i) := by
  funext i
  show ∑ k : Fin D, _ = _
  rw [coefficientVecEquiv_apply, Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, map_mul, mk_algebraMap_eq_castHom_toZModPow]

omit [CharP (O ⧸ Ideal.span {(ℓ : O) ^ n}) (ℓ ^ n)] in
/-- Every vector modulo `ℓⁿ` is the reduction of an `ℓ`-adic vector. -/
theorem toZModPow_natCast_val (w : Fin (m * D) → ZMod (ℓ ^ n)) :
    (fun p => PadicInt.toZModPow n (((w p).val : ℕ) : ℤ_[ℓ])) = w := by
  funext p
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- The map `Stacks.EtaleCohomology.coefficientLevelAddHom` is bijective. -/
theorem coefficientLevelAddHom_bijective :
    Function.Bijective (coefficientLevelAddHom (ℓ := ℓ) β m n) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
    rw [← toZModPow_natCast_val m n w, coefficientLevelAddHom_toZModPow] at hw
    rw [← toZModPow_natCast_val m n w]
    set v : Fin (m * D) → ℤ_[ℓ] := fun p => (((w p).val : ℕ) : ℤ_[ℓ])
    have ho : ∀ i, ∃ o : O, o * (ℓ : O) ^ n = coefficientVecEquiv β m v i := fun i =>
      Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hw i))
    choose o ho using ho
    have hv : v = ((ℓ : ℤ_[ℓ]) ^ n) • (coefficientVecEquiv β m).symm o := by
      apply (coefficientVecEquiv β m).injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, ← ho i, Algebra.smul_def, map_pow, map_natCast, mul_comm]
    show (fun p => PadicInt.toZModPow n (v p)) = 0
    rw [hv]
    funext p
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow,
      ZMod.natCast_self, zero_mul]
    rfl
  · intro y
    choose o ho using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨fun p => PadicInt.toZModPow n ((coefficientVecEquiv β m).symm o p), ?_⟩
    rw [coefficientLevelAddHom_toZModPow, LinearEquiv.apply_symm_apply]
    exact funext ho

/-- **`(ℤ/ℓⁿ)^{mD} ≃ (O/ℓⁿ)^m`**: the coordinates along `β`, modulo `ℓⁿ`. -/
def coefficientLevelAddEquiv :
    (Fin (m * D) → ZMod (ℓ ^ n)) ≃+ (Fin m → O ⧸ Ideal.span {(ℓ : O) ^ n}) :=
  AddEquiv.ofBijective (coefficientLevelAddHom β m n) (coefficientLevelAddHom_bijective β m n)

/-- The equivalence `Stacks.EtaleCohomology.coefficientLevelAddEquiv` acts as
`Stacks.EtaleCohomology.coefficientLevelAddHom`. -/
theorem coefficientLevelAddEquiv_apply (w : Fin (m * D) → ZMod (ℓ ^ n)) :
    coefficientLevelAddEquiv β m n w = coefficientLevelAddHom β m n w :=
  rfl

/-- The identification is semilinear along `ℤ/ℓⁿ → O/ℓⁿ`. -/
theorem coefficientLevelAddEquiv_smul (a : ZMod (ℓ ^ n)) (w : Fin (m * D) → ZMod (ℓ ^ n)) :
    coefficientLevelAddEquiv β m n (a • w) =
      ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ n}) a • coefficientLevelAddEquiv β m n w := by
  funext i
  show ∑ k : Fin D, (_ : O ⧸ Ideal.span {(ℓ : O) ^ n}) =
    (_ : O ⧸ Ideal.span {(ℓ : O) ^ n}) * ∑ k : Fin D, (_ : O ⧸ Ideal.span {(ℓ : O) ^ n})
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

/-- The identification carries the reduction of `A *ᵥ v` to the reduction of `A` applied to the
reduction of `v`, in the coordinates of `Stacks.EtaleCohomology.coefficientVecEquiv`. -/
private theorem coefficientLevelAddEquiv_map_mulVec (A : Matrix (Fin (m * D)) (Fin (m * D)) ℤ_[ℓ])
    (v : Fin (m * D) → ℤ_[ℓ]) :
    coefficientLevelAddEquiv β m n
        (A.map (PadicInt.toZModPow n) *ᵥ fun p => PadicInt.toZModPow n (v p)) =
      fun i => Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n})
        (coefficientVecEquiv β m (A *ᵥ v) i) := by
  have h1 : A.map (PadicInt.toZModPow n) *ᵥ (fun p => PadicInt.toZModPow n (v p)) =
      fun p => PadicInt.toZModPow n ((A *ᵥ v) p) :=
    funext fun p => (RingHom.map_mulVec _ _ _ p).symm
  rw [coefficientLevelAddEquiv_apply, h1, coefficientLevelAddHom_toZModPow]

/-- **The identification carries `Res_β M` modulo `ℓⁿ` to `M` modulo `ℓⁿ`.** -/
theorem coefficientLevelAddEquiv_mulVec (M : Matrix (Fin m) (Fin m) O)
    (w : Fin (m * D) → ZMod (ℓ ^ n)) :
    coefficientLevelAddEquiv β m n
        ((coefficientMatrixRingHom β m M).map (PadicInt.toZModPow n) *ᵥ w) =
      M.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n})) *ᵥ coefficientLevelAddEquiv β m n w := by
  rw [← toZModPow_natCast_val m n w, coefficientLevelAddEquiv_map_mulVec,
    coefficientLevelAddEquiv_apply,
    coefficientLevelAddHom_toZModPow, coefficientVecEquiv_mulVec]
  exact funext fun i => RingHom.map_mulVec _ _ _ i

/-- **The identification carries the matrix of multiplication by `o` to multiplication by `o`.** -/
theorem coefficientLevelAddEquiv_scalar (o : O) (w : Fin (m * D) → ZMod (ℓ ^ n)) :
    coefficientLevelAddEquiv β m n
        ((coefficientScalarRingHom β m o).map (PadicInt.toZModPow n) *ᵥ w) =
      Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}) o • coefficientLevelAddEquiv β m n w := by
  rw [← toZModPow_natCast_val m n w, coefficientLevelAddEquiv_map_mulVec,
    coefficientLevelAddEquiv_apply,
    coefficientLevelAddHom_toZModPow, coefficientVecEquiv_scalar]
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]

/-- If an additive equivalence intertwines `f` and `g`, so does its inverse. -/
private theorem symm_apply_comm {α β : Type*} [AddCommGroup α] [AddCommGroup β] (e : α ≃+ β)
    {f : α → α} {g : β → β} (h : ∀ w, e (f w) = g (e w)) (y : β) :
    e.symm (g y) = f (e.symm y) :=
  e.symm_apply_eq.2 ((h _).trans (congrArg _ (e.apply_symm_apply y))).symm

end Algebra

/-! ### The sheaves -/

section Sheaves

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {m : ℕ}
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {D : ℕ} (β : Module.Basis (Fin D) ℤ_[ℓ] O)

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
/-- **`Res_β τ` is continuous as soon as the reductions of `τ` modulo every `ℓⁿ` have open
kernel**: the reduction of `Res_β τ(g)` modulo `ℓⁿ` is constant on the cosets of the kernel of
`τ` modulo `ℓⁿ` (`Stacks.EtaleCohomology.map_toZModPow_coefficientMatrixRingHom_eq`). -/
theorem continuous_restrictScalarsRepresentation_of_isOpen
    (τO : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
    (hτ : ∀ n : ℕ, IsOpen (((GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}))).comp τO).ker :
        Set (EtaleFundamentalGroup X.1 x))) :
    Continuous (restrictScalarsRepresentation B X x β τO) := by
  have hval : Continuous fun g => (restrictScalarsRepresentation B X x β τO g).val := by
    refine continuous_pi fun i => continuous_pi fun j =>
      continuous_of_isOpen_setOf_toZModPow_eq fun k a => ?_
    refine isOpen_iff_forall_mem_open.2 fun g hg =>
      ⟨(g * ·) '' (((GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (k + 1)}))).comp τO).ker : Set _), ?_,
        isOpenMap_mul_left g _ (hτ (k + 1)), ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨h, hh, rfl⟩
    have hh' : (τO h).val.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (k + 1)})) = 1 :=
      congrArg Units.val (MonoidHom.mem_ker.1 hh)
    have hmod : (τO (g * h)).val.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (k + 1)})) =
        (τO g).val.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (k + 1)})) := by
      rw [map_mul, Units.val_mul, Matrix.map_mul, hh', Matrix.mul_one]
    have := congrFun (congrFun (map_toZModPow_coefficientMatrixRingHom_eq β m (k + 1) hmod) i) j
    simp only [Matrix.map_apply] at this
    show PadicInt.toZModPow (k + 1) (coefficientMatrixRingHom β m (τO (g * h)).val i j) = a
    rw [this]
    exact hg
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun g => ((restrictScalarsRepresentation B X x β τO g)⁻¹ : GL (Fin (m * D)) ℤ_[ℓ]).val) =
      (fun g => (restrictScalarsRepresentation B X x β τO g).val) ∘ fun g => g⁻¹ := by
    funext g
    rw [← map_inv]
    rfl
  rw [this]
  exact hval.comp continuous_inv

variable (τO : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hRes : Continuous (restrictScalarsRepresentation B X x β τO)) (n : ℕ)
  [CharP (O ⧸ Ideal.span {(ℓ : O) ^ n}) (ℓ ^ n)] [Finite (O ⧸ Ideal.span {(ℓ : O) ^ n})]
  (h : IsOpen (((GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}))).comp τO).ker :
        Set (EtaleFundamentalGroup X.1 x)))

/-- The forgetful functor from finite continuous modules to finite discrete modules. -/
local notation "φ" => finiteTypeContinuousModuleForgetAbelian

/-- The identification of the underlying finite discrete `π₁`-modules of `(O/ℓⁿ)^m` (acted on by
`τ` modulo `ℓⁿ`) and of the level module `(ℤ/ℓⁿ)^{mD}` of `Res_β τ`: the inverse of
`Stacks.EtaleCohomology.coefficientLevelAddEquiv`. -/
def coefficientLevelAbelianIso :
    (φ (O ⧸ Ideal.span {(ℓ : O) ^ n}) (EtaleFundamentalGroup X.1 x)).obj
        (matrixContinuousModule.{u + 1, u + 1} (O ⧸ Ideal.span {(ℓ : O) ^ n})
          ((GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}))).comp τO) h) ≅
      (φ (ZMod (ℓ ^ n)) (EtaleFundamentalGroup X.1 x)).obj
        (levelModule.{u + 1, u + 1} (restrictScalarsRepresentation B X x β τO) hRes n) where
  hom := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun y => ULift.up ((coefficientLevelAddEquiv β m n).symm y.down)
          map_zero' := ULift.ext _ _ (map_zero _)
          map_add' := fun a b => ULift.ext _ _ (map_add _ a.down b.down) }
      comm := fun g => by
        ext y
        exact ULift.ext _ _ ((coefficientLevelAddEquiv β m n).symm_apply_eq.2
          (((coefficientLevelAddEquiv_mulVec β m n (τO g).val _).trans (congrArg _
            ((coefficientLevelAddEquiv β m n).apply_symm_apply y.down))).symm)) }))
  inv := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun y => ULift.up (coefficientLevelAddEquiv β m n y.down)
          map_zero' := ULift.ext _ _ (map_zero _)
          map_add' := fun a b => ULift.ext _ _ (map_add _ a.down b.down) }
      comm := fun g => by
        ext y
        exact ULift.ext _ _ (coefficientLevelAddEquiv_mulVec β m n (τO g).val y.down) }))
  hom_inv_id := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact ULift.ext _ _ ((coefficientLevelAddEquiv β m n).apply_symm_apply y.down)
  inv_hom_id := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact ULift.ext _ _ ((coefficientLevelAddEquiv β m n).symm_apply_apply y.down)

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
/-- The identification is compatible with the scalars of `ℤ/ℓⁿ`. -/
theorem coefficientLevelAbelianIso_smul (a : ZMod (ℓ ^ n)) :
    (φ _ _).map (finiteTypeContinuousModuleSMul _ _
        (ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ n}) a)) ≫
        (coefficientLevelAbelianIso B X x β τO hRes n h).hom =
      (coefficientLevelAbelianIso B X x β τO hRes n h).hom ≫ (φ _ _).map
        (finiteTypeContinuousModuleSMul _ _ a) := by
  apply finiteContinuousAbelianHom_ext
  ext y
  exact ULift.ext _ _ (symm_apply_comm _ (coefficientLevelAddEquiv_smul β m n a) y.down)

/-- **The lisse sheaf of `(O/ℓⁿ)^m`, with `π₁` acting through `τ` modulo `ℓⁿ`, read as a sheaf
of `ℤ/ℓⁿ`-modules, is the lisse sheaf of the level module `(ℤ/ℓⁿ)^{mD}` of `Res_β τ`.** -/
def lisseEtaleSheafRestrictScalarsIntegersIso :
    (etaleModuleRestrictScalars (ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ n})) X.1).obj
        ((lisseEtaleSheaf B X x (O ⧸ Ideal.span {(ℓ : O) ^ n})).obj
          (matrixContinuousModule.{u + 1, u + 1} (O ⧸ Ideal.span {(ℓ : O) ^ n})
            ((GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}))).comp τO) h)) ≅
      (lisseEtaleSheaf B X x (ZMod (ℓ ^ n))).obj
        (levelModule.{u + 1, u + 1} (restrictScalarsRepresentation B X x β τO) hRes n) :=
  lisseEtaleSheafRestrictScalarsIso B X x (ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ n}))
    (coefficientLevelAbelianIso B X x β τO hRes n h)
    (coefficientLevelAbelianIso_smul B X x β τO hRes n h)

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
/-- **Multiplication by `o ∈ O` on the lisse sheaf of `(O/ℓⁿ)^m` is the lisse sheaf of
multiplication by the matrix of `o` on the level module of `Res_β τ`**, under
`Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIntegersIso` (multiplication by a scalar is
also `Stacks.EtaleCohomology.etaleModuleSMul`, by
`Stacks.EtaleCohomology.etaleModuleSMul_app_eq_smul_id`). -/
theorem lisseEtaleSheafRestrictScalarsIntegersIso_smul (o : O) :
    (etaleModuleRestrictScalars (ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ n})) X.1).map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}) o •
          𝟙 ((lisseEtaleSheaf B X x (O ⧸ Ideal.span {(ℓ : O) ^ n})).obj
            (matrixContinuousModule.{u + 1, u + 1} (O ⧸ Ideal.span {(ℓ : O) ^ n})
              ((GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}))).comp τO)
                h))) ≫
        (lisseEtaleSheafRestrictScalarsIntegersIso B X x β τO hRes n h).hom =
      (lisseEtaleSheafRestrictScalarsIntegersIso B X x β τO hRes n h).hom ≫
        (lisseEtaleSheaf B X x (ZMod (ℓ ^ n))).map
          (levelModuleHom hRes hRes (coefficientScalarRingHom β m o)
            (fun g => coefficientScalarRingHom_commute β m o (τO g).val) n) := by
  rw [← etaleModuleSMul_app_eq_smul_id, etaleModuleSMul_app_lisseEtaleSheaf]
  refine lisseEtaleSheafRestrictScalarsIso_hom_naturality _ _ _ _ _ _ _ ?_
  apply finiteContinuousAbelianHom_ext
  ext y
  exact ULift.ext _ _ (symm_apply_comm _ (coefficientLevelAddEquiv_scalar β m n o) y.down)

end Sheaves

end Stacks.EtaleCohomology

end
