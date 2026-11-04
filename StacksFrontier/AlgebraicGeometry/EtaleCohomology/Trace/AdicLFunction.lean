module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FlatStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharPolynomial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# The `ℤ_ℓ`-valued L-function of an ℓ-adic sheaf with flat levels

Let `F = (Fₙ)` be an ℓ-adic sheaf on a scheme `X` of finite type over a finite field `k` whose
levels are flat over `ℤ/ℓⁿ⁺¹ℤ`.  Then the ℓ-adic stalk `F_x̄ = limₙ F_{n, x̄}` at every geometric
point is a free `ℤ_ℓ`-module of finite rank (compatible bases of the finite-level stalks lift),
and the geometric Frobenius `π_x^*` at a closed point `x` acts on it.  The Euler product

`L_{ℤ_ℓ}(X, F) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) | F_x̄) ⁻¹ ∈ ℤ_ℓ⟦T⟧`

is the `ℤ_ℓ`-coefficient version of the L-function of Tags 03UV and 03UX.  Its image in `ℚ_ℓ⟦T⟧`
is the L-function `L(X, F ⊗ ℚ_ℓ)` of Tag 03UX, and its reduction modulo `ℓⁿ⁺¹` is the L-function
`L(X, Fₙ)` of the level `Fₙ`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.adicFrobeniusMatrices`: the matrices of `π_x^*` on the
  ℓ-adic stalks, in the compatible bases of the finite-level stalks.
* `Stacks.EtaleCohomology.LAdicSheaf.adicLFunction`: the L-function `L_{ℤ_ℓ}(X, F)`.

## Main results

* `Stacks.EtaleCohomology.charPowerSeries_baseChange`: the local factor `det(1 - φ T ^ d)` of a
  finite free module commutes with base change.
* `Stacks.EtaleCohomology.LAdicSheaf.map_adicLFunction_padic`:
  `L_{ℤ_ℓ}(X, F) ⊗ ℚ_ℓ = L(X, F ⊗ ℚ_ℓ)`.
* `Stacks.EtaleCohomology.LAdicSheaf.map_adicLFunction_toZModPow`: the reduction of
  `L_{ℤ_ℓ}(X, F)` modulo `ℓⁿ⁺¹` is `L(X, Fₙ)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-! ### Base change of the local factor -/

section BaseChange

variable {Λ : Type*} [CommRing Λ] [Nontrivial Λ] {Λ' : Type*} [CommRing Λ'] [Algebra Λ Λ']
  {M : Type*} [AddCommGroup M] [Module Λ M] [Module.Free Λ M] [Module.Finite Λ M]

/-- **The local factor commutes with base change.** For an endomorphism `φ` of a finite free
`Λ`-module and a `Λ`-algebra `Λ'`, `det(1 - (Λ' ⊗ φ) T ^ d) = det(1 - φ T ^ d)` in `Λ'⟦T⟧`. -/
public theorem charPowerSeries_baseChange (φ : M →ₗ[Λ] M) (d : ℕ) :
    charPowerSeries (φ.baseChange Λ') d =
      PowerSeries.map (algebraMap Λ Λ') (charPowerSeries φ d) := by
  classical
  let b := Module.finBasis Λ M
  rw [charPowerSeries_eq_localCharSeries (Algebra.TensorProduct.basis Λ' b),
    LinearMap.toMatrix_baseChange, charPowerSeries_eq_localCharSeries b, map_localCharSeries_eq]

end BaseChange

/-- In the basis of a trivialisation `e : M ≃ Λ^r`, the matrix of an endomorphism is the matrix of
its conjugate by `e`; so its local factor is that of `e.conj φ`. -/
public theorem charPowerSeries_eq_localCharSeries_conj {Λ : Type*} [CommRing Λ] {M : Type*}
    [AddCommGroup M] [Module Λ M] {r : ℕ} (e : M ≃ₗ[Λ] (Fin r → Λ)) (φ : M →ₗ[Λ] M) (d : ℕ) :
    charPowerSeries φ d = localCharSeries (LinearMap.toMatrix' (e.conj φ)) d := by
  classical
  rw [charPowerSeries_eq_localCharSeries (Module.Basis.ofEquivFun e)]
  congr 1

/-- The local factor is invariant under conjugation by a linear equivalence, on a module with a
finite trivialisation. -/
public theorem charPowerSeries_conj {Λ : Type*} [CommRing Λ] {M N : Type*} [AddCommGroup M]
    [Module Λ M] [AddCommGroup N] [Module Λ N] {r : ℕ} (g : M ≃ₗ[Λ] (Fin r → Λ))
    (e : M ≃ₗ[Λ] N) (φ : M →ₗ[Λ] M) (d : ℕ) :
    charPowerSeries (e.conj φ) d = charPowerSeries φ d := by
  rw [charPowerSeries_eq_localCharSeries_conj (e.symm.trans g),
    charPowerSeries_eq_localCharSeries_conj g]
  congr 2
  apply LinearMap.ext
  intro w
  simp [LinearEquiv.conj_apply]

/-! ### The L-function -/

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [AlgebraicGeometry.IsNoetherian X.1] [Fact ℓ.Prime]

variable {B X ℓ} in
/-- The trivialisation `F_x̄ ≅ ℤ_ℓ^r` of the ℓ-adic stalk of an ℓ-adic sheaf with flat levels, from
compatible bases of the finite-level stalks. -/
public def LAdicSheaf.flatStalkEquiv (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (s : GeometricPoint X.1) :
    LAdicSheaf.stalk B X ℓ F s ≃ₗ[ℤ_[ℓ]] (Fin (LAdicSheaf.flatStalkRank F s) → ℤ_[ℓ]) :=
  (LAdicSheaf.flatLevelTrivialization F s
    fun n => LAdicSheaf.isPowExact_finiteLevelStalk F s n (hF n)).stalkEquiv

variable {k : Type u} [Field k] [Finite k]

/-- The matrices of the geometric Frobenius `π_x^*` acting on the ℓ-adic stalks of an ℓ-adic sheaf
with flat levels at the closed points of `X`, in the trivialisations `flatStalkEquiv`. -/
public def LAdicSheaf.adicFrobeniusMatrices (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] : FrobeniusMatrices f ℤ_[ℓ] where
  rank x := LAdicSheaf.flatStalkRank F (geometricPointAt X.1 x.1)
  matrix x :=
    haveI := finite_residueField f x.1 x.2
    LinearMap.toMatrix' ((LAdicSheaf.flatStalkEquiv F hF (geometricPointAt X.1 x.1)).conj
      (LAdicSheaf.stalkEnd B X ℓ F (frobeniusPointHom X.1 x.1)))

/-- **The `ℤ_ℓ`-valued L-function of an ℓ-adic sheaf with flat levels**,
`L_{ℤ_ℓ}(X, F) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) | F_x̄) ⁻¹ ∈ ℤ_ℓ⟦T⟧`, the local factors
being those of the geometric Frobenius on the ℓ-adic stalks `F_x̄ ≅ ℤ_ℓ^r`. -/
public def LAdicSheaf.adicLFunction (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] : PowerSeries ℤ_[ℓ] :=
  (LAdicSheaf.adicFrobeniusMatrices B X ℓ F hF f).lFunction

/-- The local factor at a closed point `x` of `L_{ℤ_ℓ}(X, F)` is `det(1 - π_x^* T ^ d | F_x̄)`. -/
public theorem LAdicSheaf.localCharSeries_adicFrobeniusMatrices (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X.1) (d : ℕ) :
    haveI := finite_residueField f x.1 x.2
    localCharSeries ((LAdicSheaf.adicFrobeniusMatrices B X ℓ F hF f).matrix x) d =
      charPowerSeries (LAdicSheaf.stalkEnd B X ℓ F (frobeniusPointHom X.1 x.1)) d :=
  (charPowerSeries_eq_localCharSeries_conj _ _ d).symm

/-- **The image of `L_{ℤ_ℓ}(X, F)` in `ℚ_ℓ⟦T⟧` is the L-function `L(X, F ⊗ ℚ_ℓ)` of Tag 03UX.** -/
public theorem LAdicSheaf.map_adicLFunction_padic (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    PowerSeries.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) (LAdicSheaf.adicLFunction B X ℓ F hF f) =
      LAdicSheaf.rationalLFunction B X ℓ F f := by
  rw [LAdicSheaf.adicLFunction, FrobeniusMatrices.map_lFunction, LAdicSheaf.rationalLFunction]
  refine FrobeniusMatrices.lFunction_congr _ fun x => ?_
  have := finite_residueField f x.1 x.2
  let e := LAdicSheaf.flatStalkEquiv F hF (geometricPointAt X.1 x.1)
  have : Module.Free ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ F (geometricPointAt X.1 x.1)) :=
    Module.Free.of_equiv e.symm
  have : Module.Finite ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ F (geometricPointAt X.1 x.1)) :=
    Module.Finite.equiv e.symm
  rw [FrobeniusMatrices.localFactor, FrobeniusMatrices.localFactor, localEulerFactor,
    localEulerFactor, LAdicSheaf.localCharSeries_frobeniusMatrices]
  congr 1
  show localCharSeries (((LAdicSheaf.adicFrobeniusMatrices B X ℓ F hF f).matrix x).map
    (algebraMap ℤ_[ℓ] ℚ_[ℓ])) _ =
      charPowerSeries ((LAdicSheaf.stalkEnd B X ℓ F (frobeniusPointHom X.1 x.1)).baseChange
        ℚ_[ℓ]) _
  rw [← map_localCharSeries_eq, LAdicSheaf.localCharSeries_adicFrobeniusMatrices,
    charPowerSeries_baseChange]

/-! ### Reduction modulo `ℓⁿ⁺¹` -/

/-- In the compatible bases of the finite-level stalks, an endomorphism `a` of the geometric point
acts on the level-`n` stalk by the reduction modulo `ℓⁿ⁺¹` of its matrix on the ℓ-adic stalk. -/
public theorem LAdicSheaf.conj_finiteLevelStalkEnd (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (n : ℕ) :
    (LAdicSheaf.flatLevelBasis F s
        (fun n => LAdicSheaf.isPowExact_finiteLevelStalk F s n (hF n)) n).equivFun.conj
        (finiteLevelStalkEnd B X ℓ F a n).hom =
      Matrix.toLin' ((LinearMap.toMatrix' ((LAdicSheaf.flatStalkEquiv F hF s).conj
        (LAdicSheaf.stalkEnd B X ℓ F a))).map (PadicInt.toZModPow (n + 1))) := by
  let T := LAdicSheaf.flatLevelTrivialization F s
    fun n => LAdicSheaf.isPowExact_finiteLevelStalk F s n (hF n)
  let e := T.stalkEquiv
  let A := LinearMap.toMatrix' (e.conj (LAdicSheaf.stalkEnd B X ℓ F a))
  let b := LAdicSheaf.flatLevelBasis F s
    (fun n => LAdicSheaf.isPowExact_finiteLevelStalk F s n (hF n)) n
  show b.equivFun.conj (finiteLevelStalkEnd B X ℓ F a n).hom =
    Matrix.toLin' (A.map (PadicInt.toZModPow (n + 1)))
  apply LinearMap.ext
  intro w
  obtain ⟨w', hw'⟩ := (ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1))).comp_left w
  let v := e.symm w'
  have hv : b.equivFun (v.1 n) = w := by
    rw [← hw']
    funext i
    show T.equiv n (v.1 n) i = _
    rw [← LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv T v n i]
    simp only [v, e, LinearEquiv.apply_symm_apply, Function.comp_apply]
  rw [LinearEquiv.conj_apply_apply, ← hv, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply]
  funext i
  show T.equiv n ((LAdicSheaf.stalkEnd B X ℓ F a v).1 n) i = _
  rw [← LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv,
    show e (LAdicSheaf.stalkEnd B X ℓ F a v) = Matrix.toLin' A (e v) by
      rw [Matrix.toLin'_toMatrix', LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply],
    Matrix.toLin'_apply, RingHom.map_mulVec]
  congr 1
  funext j
  exact LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv T v n j

/-- The local factor of an endomorphism of the geometric point on the level-`n` stalk is the
reduction modulo `ℓⁿ⁺¹` of its local factor on the ℓ-adic stalk. -/
public theorem LAdicSheaf.charPowerSeries_finiteLevelStalkEnd (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (n d : ℕ) :
    charPowerSeries (finiteLevelStalkEnd B X ℓ F a n).hom d =
      PowerSeries.map (PadicInt.toZModPow (n + 1))
        (charPowerSeries (LAdicSheaf.stalkEnd B X ℓ F a) d) := by
  rw [charPowerSeries_eq_localCharSeries_conj (LAdicSheaf.flatLevelBasis F s
      (fun n => LAdicSheaf.isPowExact_finiteLevelStalk F s n (hF n)) n).equivFun,
    LAdicSheaf.conj_finiteLevelStalkEnd B X ℓ F hF a n, LinearMap.toMatrix'_toLin',
    ← map_localCharSeries_eq, ← charPowerSeries_eq_localCharSeries_conj]

/-- The geometric Frobenius of Mathlib's small étale site, acting on the stalk of the level `Fₙ` at
a closed point, has the local factor of `frobeniusPointHom` acting on the finite-level stalk of
the bounded site: the two stalks are identified compatibly with the two actions. -/
public theorem LAdicSheaf.charPowerSeries_frobeniusStalkEnd_level (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (n : ℕ) (x : closedPoints X.1) (d : ℕ) :
    haveI := finite_residueField f x.1 x.2
    charPowerSeries (frobeniusStalkEnd B X (ZMod (ℓ ^ (n + 1))) (F.level n) f x) d =
      charPowerSeries (finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x.1) n).hom d := by
  have := finite_residueField f x.1 x.2
  let s := geometricPointAt X.1 x.1
  let e := (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) s).app (F.level n)
  have hnat : e.inv ≫ frobeniusStalk (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) X.1 x.1
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.obj
        (F.level n)) =
      finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x.1) n ≫ e.inv := by
    have h := NatTrans.congr_app (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X
      (ZMod (ℓ ^ (n + 1))) (frobeniusPointHom X.1 x.1)) (F.level n)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    exact h
  have hfrob := (Iso.inv_comp_eq e).1 hnat
  have h : frobeniusStalkEnd B X (ZMod (ℓ ^ (n + 1))) (F.level n) f x =
      e.toLinearEquiv.symm.conj
        (finiteLevelStalkEnd B X ℓ F (frobeniusPointHom X.1 x.1) n).hom :=
    LinearMap.ext fun y => congrArg (fun g => g.hom y) hfrob
  exact (congrArg (fun φ => charPowerSeries φ d) h).trans
    (charPowerSeries_conj (LAdicSheaf.flatLevelBasis F s
      (fun n => LAdicSheaf.isPowExact_finiteLevelStalk F s n (hF n)) n).equivFun
      e.toLinearEquiv.symm _ d)

/-- **The reduction of `L_{ℤ_ℓ}(X, F)` modulo `ℓⁿ⁺¹` is the L-function `L(X, Fₙ)` of the level
`Fₙ`** (Tag 03UV), the Euler product of the local factors of the geometric Frobenius on the stalks
of `Fₙ`. -/
public theorem LAdicSheaf.map_adicLFunction_toZModPow (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ)
    (hfin : ∀ s : GeometricPoint X.1, Module.Finite (ZMod (ℓ ^ (n + 1)))
      ((etaleModuleStalkFunctor.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) s).obj (F.level n)))
    (hproj : ∀ s : GeometricPoint X.1, Module.Projective (ZMod (ℓ ^ (n + 1)))
      ((etaleModuleStalkFunctor.{u, u + 1, 0} B X (ZMod (ℓ ^ (n + 1))) s).obj (F.level n))) :
    haveI := zmod_pow_succ_isLocalRing (ℓ := ℓ) n
    PowerSeries.map (PadicInt.toZModPow (n + 1)) (LAdicSheaf.adicLFunction B X ℓ F hF f) =
      lFunctionOfSheaf B X (ZMod (ℓ ^ (n + 1))) (F.level n) f hfin hproj := by
  have := zmod_pow_succ_isLocalRing (ℓ := ℓ) n
  rw [LAdicSheaf.adicLFunction, FrobeniusMatrices.map_lFunction, lFunctionOfSheaf]
  refine FrobeniusMatrices.lFunction_congr _ fun x => ?_
  have := finite_residueField f x.1 x.2
  rw [FrobeniusMatrices.localFactor, FrobeniusMatrices.localFactor, localEulerFactor,
    localEulerFactor, ← charPowerSeries_frobeniusStalkEnd,
    LAdicSheaf.charPowerSeries_frobeniusStalkEnd_level B X ℓ F hF f n x,
    LAdicSheaf.charPowerSeries_finiteLevelStalkEnd B X ℓ F hF _ n,
    ← LAdicSheaf.localCharSeries_adicFrobeniusMatrices B X ℓ F hF f x, map_localCharSeries_eq]
  rfl

end Stacks.EtaleCohomology

end
