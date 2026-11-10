module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PointClassDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilCohomologyTheory
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The factors of `H^0(Spec k')` (Stacks 0FI3)

Let `H^*` be a Weil cohomology theory (Definition 0FI2) and let `X` be a geometrically
irreducible smooth projective scheme of dimension `d` over `k'`, with `k'/k` a finite separable
extension. Suppose `H^0(Spec(k')) = F_1 × ⋯ × F_r` for fields `F_i`. Remark 0FI3 observes:

* `H^*(X) = ∏_i H^*(X) ⊗_{H^0(Spec k')} F_i`;
* `H^0(X)` is free of rank `1` over `∏_i F_i`, i.e. each factor `H^0(X) ⊗_{H^0(Spec k')} F_i` has
  dimension `1` over `F_i`: this is the final assumption of Definition 0FI2, as
  `Γ(X, 𝒪_X) = k'`;
* by Poincaré duality the same holds in degree `2d`.

The rest of the remark says that it is not known whether the integers
`dim_{F_i} H^n(X) ⊗_{H^0(Spec k')} F_i` for `0 < n < dim(X)` are independent of `i`, and relates
this to an open question; it asserts nothing further.

## The objects

`H^*(X)` is an `H^0(Spec k')`-algebra by pullback along `X ⟶ Spec k'`
(`Stacks.WeilCohomology.WeilData.algebraH0SpecOfOver`), and its degree `n` part is an
`H^0(Spec k')`-submodule (`Stacks.WeilCohomology.WeilData.gradeOverSpec`), since the action is
by classes of degree zero. "`H^0(Spec k') = F_1 × ⋯ × F_r`" is a family of fields `F_i` which are
`H^0(Spec k')`-algebras such that `H^0(Spec k') → ∏_i F_i` is bijective. The factor
`M ⊗_{H^0(Spec k')} F_i` is written `F_i ⊗_{H^0(Spec k')} M`, the base change of `M` to `F_i`,
with its `F_i`-module structure; the two agree by the symmetry of the tensor product over the
commutative ring `H^0(Spec k')`.

## The argument

The decomposition is `M = H^0(Spec k') ⊗ M = (∏_i F_i) ⊗ M = ∏_i (F_i ⊗ M)`
(`Stacks.WeilCohomology.piFactorEquiv`). For degree zero, `Γ(X, 𝒪_X) = k'` (Tag 0BUG (7)), so
the final assumption of Definition 0FI2 says that `H^0(Spec k') → H^0(X)` is bijective.
For degree `2d`, let `ε_i ∈ H^0(Spec k')` be the idempotent of the factor `F_i`. Then
`F_i ⊗ M ≅ ε_i M` (`Stacks.WeilCohomology.tensorFactorEquivRange`). The Poincaré pairing
`H^0(X) × H^{2d}(X) → F` is perfect and balanced over `H^0(Spec k')`, degree-zero classes being
central, so it pairs `ε_i H^0(X)` perfectly with `ε_i H^{2d}(X)`. Hence
`dim_F (F_i ⊗ H^{2d}(X)) = dim_F (F_i ⊗ H^0(X)) = dim_F F_i`, which is
`dim_{F_i} (F_i ⊗ H^{2d}(X)) = 1` (`Stacks.WeilCohomology.finrank_tensorFactor_eq_one_of_pairing`).

## Main results

* `Stacks.WeilCohomology.WeilCohomologyTheory.factorwise_rank_one_of_geometricallyIrreducible`:
  for `X` geometrically irreducible smooth projective over `k'`, `H^*(X)` is the product of its
  base changes to the factors `F_i`, and in degrees `0` and `2d` each factor has dimension `1`.
* `Stacks.WeilCohomology.WeilData.bijective_pullDeg_toSpec_zero`: for `X` geometrically connected
  over `k'`, `H^0(Spec k') → H^0(X)` is bijective.

## References

* [Stacks Project, Tag 0FI3](https://stacks.math.columbia.edu/tag/0FI3)
* [Stacks Project, Tag 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u w

namespace Stacks.WeilCohomology

/-! ### Modules over a finite product of fields -/

section ProductOfFields

variable {A : Type*} [CommRing A]

/-- **A module over `∏_i F_i` is the product of its base changes to the `F_i`**:
`M = A ⊗_A M = (∏_i F_i) ⊗_A M = ∏_i F_i ⊗_A M` when `A → ∏_i F_i` is bijective. -/
def piFactorEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → Type*) [∀ i, CommRing (K i)]
    [∀ i, Algebra A (K i)] (hK : Function.Bijective (RingHom.pi fun i ↦ algebraMap A (K i)))
    (M : Type*) [AddCommGroup M] [Module A M] : M ≃ₗ[A] ∀ i, K i ⊗[A] M :=
  (TensorProduct.lid A M).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.ofBijective (LinearMap.pi fun i ↦ Algebra.linearMap A (K i))
      hK) (LinearEquiv.refl A M) ≪≫ₗ TensorProduct.piLeft A M (fun i ↦ K i)

/-- The `i`-th component of `piFactorEquiv K hK M x` is `1 ⊗ x`. -/
@[simp]
theorem piFactorEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → Type*)
    [∀ i, CommRing (K i)] [∀ i, Algebra A (K i)]
    (hK : Function.Bijective (RingHom.pi fun i ↦ algebraMap A (K i))) (M : Type*)
    [AddCommGroup M] [Module A M] (x : M) (i : ι) :
    piFactorEquiv K hK M x i = (1 : K i) ⊗ₜ x := by
  simp only [piFactorEquiv, piLeft, LinearEquiv.trans_apply, lid_symm_apply, congr_tmul,
    LinearEquiv.refl_apply, comm_tmul, piRight_apply, piRightHom_tmul,
    LinearEquiv.piCongrRight_apply]
  exact congrArg (· ⊗ₜ[A] x) (map_one (algebraMap A (K i)))

variable {K : Type*} [Field K] [Algebra A K]

/-- For the idempotent `ε` of a factor `K` of `A`, the submodule `I M` of `M`, `I` the kernel of
`A → K`, is the kernel of multiplication by `ε`. -/
theorem smul_top_eq_ker_lsmul {ε : A} (hε₁ : algebraMap A K ε = 1)
    (hε : ∀ a, algebraMap A K a = 0 → ε * a = 0) (M : Type*) [AddCommGroup M] [Module A M] :
    RingHom.ker (Algebra.ofId A K) • (⊤ : Submodule A M) =
      LinearMap.ker (LinearMap.lsmul A M ε) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, smul_smul, hε a ha, zero_smul]
  · intro x hx
    have hx' : ε • x = 0 := hx
    have h : x = (1 - ε) • x := by rw [sub_smul, one_smul, hx', sub_zero]
    rw [h]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [RingHom.mem_ker, Algebra.ofId_apply, map_sub, map_one, hε₁, sub_self]

/-- **`K ⊗_A M ≅ ε M`** for the idempotent `ε` of a factor `K` of `A`. -/
def tensorFactorEquivRange {ε : A} (hε₁ : algebraMap A K ε = 1)
    (hε : ∀ a, algebraMap A K a = 0 → ε * a = 0) (hsurj : Function.Surjective (algebraMap A K))
    (M : Type*) [AddCommGroup M] [Module A M] :
    K ⊗[A] M ≃ₗ[A] LinearMap.range (LinearMap.lsmul A M ε) :=
  TensorProduct.congr (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A K)
      hsurj).symm.toLinearEquiv (LinearEquiv.refl A M) ≪≫ₗ
    quotTensorEquivQuotSMul M (RingHom.ker (Algebra.ofId A K)) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (smul_top_eq_ker_lsmul hε₁ hε M) ≪≫ₗ
    (LinearMap.lsmul A M ε).quotKerEquivRange

variable {F : Type*} [Field F] [Algebra F A]

/-- A pairing `B : M × N → F` with `B` injective and `B(a m, n) = B(m, a n)` pairs `ε M`
injectively into the dual of `ε N`, for `ε` idempotent. -/
theorem finrank_range_lsmul_le_of_pairing {M N : Type*} [AddCommGroup M] [Module A M]
    [Module F M] [IsScalarTower F A M] [AddCommGroup N] [Module A N] [Module F N]
    [IsScalarTower F A N] [FiniteDimensional F N] (B : M →ₗ[F] N →ₗ[F] F)
    (hB : Function.Injective B) (hbal : ∀ (a : A) (m : M) (n : N), B (a • m) n = B m (a • n))
    {ε : A} (hε : IsIdempotentElem ε) :
    Module.finrank F (LinearMap.range (LinearMap.lsmul A M ε)) ≤
      Module.finrank F (LinearMap.range (LinearMap.lsmul A N ε)) := by
  set RM := LinearMap.range (LinearMap.lsmul A M ε)
  set RN := LinearMap.range (LinearMap.lsmul A N ε)
  have : FiniteDimensional F RN :=
    Module.Finite.of_injective (RN.subtype.restrictScalars F) Subtype.val_injective
  let φ : RM →ₗ[F] RN →ₗ[F] F :=
    B.compl₁₂ (RM.subtype.restrictScalars F) (RN.subtype.restrictScalars F)
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ h
    obtain ⟨m, rfl⟩ := hx
    have hx : ε • (ε • m) = ε • m := by rw [smul_smul, hε.eq]
    refine Subtype.ext (hB (LinearMap.ext fun n ↦ ?_))
    have h' := LinearMap.congr_fun h ⟨ε • n, n, rfl⟩
    simp only [φ, LinearMap.compl₁₂_apply, Submodule.coe_subtype, LinearMap.coe_restrictScalars,
      LinearMap.zero_apply] at h'
    simp only [ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply]
    change B (ε • m) n = 0
    rwa [← hx, hbal]
  exact (LinearMap.finrank_le_finrank_of_injective hφ).trans_eq Subspace.dual_finrank_eq

/-- `K ⊗_A M ≃ K` as `K`-modules when `M ≅ A`. -/
private def tensorEquivSelf {M : Type*} [AddCommGroup M] [Module A M] (eM : A ≃ₗ[A] M) :
    K ⊗[A] M ≃ₗ[K] K :=
  AlgebraTensorModule.congr (LinearEquiv.refl K K) eM.symm ≪≫ₗ
    AlgebraTensorModule.rid A K K

variable [Algebra F K] [IsScalarTower F A K]

/-- **The factors of a module dual to a free module of rank one are one-dimensional.** Let `K` be
a factor of `A` with idempotent `ε`, let `M ≅ A` and `N` be `A`-modules, finite dimensional over
`F`, and let `B : M × N → F` be a nondegenerate pairing with `B(a m, n) = B(m, a n)`. Then
`dim_K (K ⊗_A N) = 1`. -/
theorem finrank_tensorFactor_eq_one_of_pairing {ε : A} (hε₁ : algebraMap A K ε = 1)
    (hε : ∀ a, algebraMap A K a = 0 → ε * a = 0) (hsurj : Function.Surjective (algebraMap A K))
    {M N : Type*} [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    [FiniteDimensional F M] [AddCommGroup N] [Module A N] [Module F N] [IsScalarTower F A N]
    [FiniteDimensional F N] (eM : A ≃ₗ[A] M) (B : M →ₗ[F] N →ₗ[F] F)
    (hB : Function.Injective B) (hB' : Function.Injective B.flip)
    (hbal : ∀ (a : A) (m : M) (n : N), B (a • m) n = B m (a • n)) :
    Module.finrank K (K ⊗[A] N) = 1 := by
  have hidem : IsIdempotentElem ε := by
    have h := hε (1 - ε) (by rw [map_sub, map_one, hε₁, sub_self])
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm
  have e₁ := ((tensorFactorEquivRange hε₁ hε hsurj N).restrictScalars F).finrank_eq
  have e₂ := ((tensorFactorEquivRange hε₁ hε hsurj M).restrictScalars F).finrank_eq
  have e₃ : Module.finrank F (LinearMap.range (LinearMap.lsmul A M ε)) =
      Module.finrank F (LinearMap.range (LinearMap.lsmul A N ε)) :=
    le_antisymm (finrank_range_lsmul_le_of_pairing B hB hbal hidem)
      (finrank_range_lsmul_le_of_pairing B.flip hB' (fun a n m ↦ (hbal a m n).symm) hidem)
  have e₄ := ((tensorEquivSelf (K := K) eM).restrictScalars F).finrank_eq
  have : Module.Finite F A := Module.Finite.equiv (eM.symm.restrictScalars F)
  have : Module.Finite F K :=
    Module.Finite.of_surjective ((Algebra.linearMap A K).restrictScalars F) hsurj
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite F A N
  have hK : 0 < Module.finrank F K := Module.finrank_pos
  have h := Module.finrank_mul_finrank F K (K ⊗[A] N)
  rw [e₁, ← e₃, ← e₂, e₄] at h
  exact Nat.eq_of_mul_eq_mul_left hK (h.trans (mul_one _).symm)

end ProductOfFields

/-! ### `Γ(X, 𝒪_X)` and `k'` -/

namespace SmoothProjectiveScheme

section GlobalSectionsOverField

variable (k : Type u) [Field k] {k' : Type u} [Field k'] [Algebra k k'] [Module.Finite k k']
  [Algebra.Etale k k'] {X : Scheme.{u}} (π : X ⟶ Spec (.of k')) [Smooth π]
  (hπ : IsProjectiveMorphism π)

/-- `k' → Γ(X, 𝒪_X)`, the map on global sections of the structure morphism `X ⟶ Spec k'`, as a
`k`-algebra map. -/
def globalSectionsAlgHom : k' →ₐ[k] globalSections (ofOver k π hπ) where
  toRingHom := ((Scheme.ΓSpecIso (.of k')).inv ≫ π.appTop).hom
  commutes' r := by
    change ((Scheme.ΓSpecIso (.of k')).inv ≫ π.appTop).hom (algebraMap k k' r) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ specStructure k k').appTop).hom r
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, specStructure, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
    rfl

/-- `X ⟶ Spec k'` factors as `X ⟶ Spec Γ(X, 𝒪_X) ⟶ Spec k'`. -/
theorem toSpecGlobalSections_comp_specMap :
    toSpecGlobalSections (ofOver k π hπ) ≫ specMap (globalSectionsAlgHom k π hπ) =
      toSpec k π hπ := by
  apply hom_ext_left
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k')).inv ≫ π.appTop) = π
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end GlobalSectionsOverField

end SmoothProjectiveScheme

/-! ### The degree-zero part of a scheme over `k'` -/

namespace WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

section OverSpec

variable {k' : Type u} [CommRing k'] [Algebra k k'] [Module.Finite k k'] [Algebra.Etale k k']
  {X : Scheme.{u}} (π : X ⟶ Spec (.of k')) [Smooth π] (hπ : IsProjectiveMorphism π)

/-- **`H^n(X)` as an `H^0(Spec k')`-module**, for `X` smooth projective over `k'`: the degree `n`
part of the `H^0(Spec k')`-algebra `H^*(X)`, stable under the action since `H^0(Spec k')` acts by
classes of degree zero. -/
def gradeOverSpec (n : ℤ) : Submodule (W.H0 (spec k k')) (W.H (ofOver k π hπ)) where
  carrier := W.grade (ofOver k π hπ) n
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    change W.pull (toSpec k π hπ) (c : W.H (spec k k')) * x ∈ W.grade (ofOver k π hπ) n
    simpa using SetLike.GradedMul.mul_mem (W.pull_grade (toSpec k π hπ) 0 _ c.2) hx

/-- A class lies in `gradeOverSpec π hπ n` if and only if it has degree `n`. -/
theorem mem_gradeOverSpec {n : ℤ} {x : W.H (ofOver k π hπ)} :
    x ∈ W.gradeOverSpec π hπ n ↔ x ∈ W.grade (ofOver k π hπ) n :=
  Iff.rfl

/-- `H^n(X)` with its `H^0(Spec k')`-module structure is `H^n(X)` over `F`. -/
def gradeOverSpecEquiv (n : ℤ) : W.gradeOverSpec π hπ n ≃ₗ[F] W.grade (ofOver k π hπ) n where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `gradeOverSpecEquiv` is the identity on underlying classes. -/
@[simp]
theorem coe_gradeOverSpecEquiv (n : ℤ) (x : W.gradeOverSpec π hπ n) :
    (W.gradeOverSpecEquiv π hπ n x : W.H (ofOver k π hπ)) = x :=
  rfl

/-- The inverse of `gradeOverSpecEquiv` is the identity on underlying classes. -/
@[simp]
theorem coe_gradeOverSpecEquiv_symm (n : ℤ) (x : W.grade (ofOver k π hπ) n) :
    ((W.gradeOverSpecEquiv π hπ n).symm x : W.H (ofOver k π hπ)) = x :=
  rfl

/-- **The Poincaré pairing `H^0(X) × H^{2d}(X) → F`**, `(a, b) ↦ ∫_X a ∪ b`, on the
`H^0(Spec k')`-modules `H^0(X)` and `H^{2d}(X)`, through the coordinates of the twists. -/
def pairingOverSpec {d : ℕ} (hX : IsNonemptyEquidimensional (ofOver k π hπ) d) :
    W.gradeOverSpec π hπ 0 →ₗ[F] W.gradeOverSpec π hπ (2 * d) →ₗ[F] F :=
  (W.pairingTw (ofOver k π hπ) d hX 0 (2 * d) (zero_add _) d 0 (add_zero _)).compl₁₂
    (((W.gradeOverSpecEquiv π hπ 0).trans (W.twCoord _ 0 d).symm).toLinearMap)
    (((W.gradeOverSpecEquiv π hπ (2 * d)).trans (W.twCoord _ (2 * d) 0).symm).toLinearMap)

/-- `pairingOverSpec` sends `(a, b)` to the trace of the cup product `a ∪ b ∈ H^{2d}(X)(d)`. -/
theorem pairingOverSpec_apply {d : ℕ} (hX : IsNonemptyEquidimensional (ofOver k π hπ) d)
    (a : W.gradeOverSpec π hπ 0) (b : W.gradeOverSpec π hπ (2 * d)) :
    W.pairingOverSpec π hπ hX a b = W.trace (ofOver k π hπ) d hX
      ((W.twCoord _ (2 * d) d).symm ⟨(a : W.H (ofOver k π hπ)) * b, by
        have h := SetLike.GradedMul.mul_mem (A := W.grade (ofOver k π hπ)) a.2 b.2
        rwa [zero_add] at h⟩) := by
  rw [pairingOverSpec, LinearMap.compl₁₂_apply, pairingTw_apply]
  refine congrArg (W.trace (ofOver k π hπ) d hX) ?_
  apply (W.twCoord (ofOver k π hπ) (2 * d) d).injective
  rw [twCoord_cupTw, LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The Poincaré pairing is balanced over `H^0(Spec k')`: degree-zero classes are central. -/
theorem pairingOverSpec_smul {d : ℕ} (hX : IsNonemptyEquidimensional (ofOver k π hπ) d)
    (c : W.H0 (spec k k')) (a : W.gradeOverSpec π hπ 0) (b : W.gradeOverSpec π hπ (2 * d)) :
    W.pairingOverSpec π hπ hX (c • a) b = W.pairingOverSpec π hπ hX a (c • b) := by
  rw [pairingOverSpec_apply, pairingOverSpec_apply]
  congr 2
  apply Subtype.ext
  change W.pull (toSpec k π hπ) (c : W.H (spec k k')) * a * b =
    a * (W.pull (toSpec k π hπ) (c : W.H (spec k k')) * b)
  rw [W.mul_comm_of_mem_grade_zero _ (W.pull_grade (toSpec k π hπ) 0 _ c.2) a, mul_assoc]

/-- Under (A)(b) the pairing `H^0(X) × H^{2d}(X) → F` is nondegenerate on both sides. -/
theorem injective_pairingOverSpec (hA : W.PerfectPairing) {d : ℕ}
    (hX : IsNonemptyEquidimensional (ofOver k π hπ) d) :
    Function.Injective (W.pairingOverSpec π hπ hX) ∧
      Function.Injective (W.pairingOverSpec π hπ hX).flip := by
  have := hA.pairingTw (ofOver k π hπ) d hX 0 (2 * d) (zero_add _) d 0 (add_zero _)
  have : (W.pairingOverSpec π hπ hX).IsPerfPair := by
    unfold pairingOverSpec
    infer_instance
  exact ⟨(LinearMap.IsPerfPair.bijective_left _).injective,
    (LinearMap.IsPerfPair.bijective_right _).injective⟩

end OverSpec

/-! ### `H^0` of a geometrically connected scheme over `k'` -/

section GeometricallyConnected

variable {k' : Type u} [Field k'] [Algebra k k'] [Module.Finite k k'] [Algebra.Etale k k']
  {X : Scheme.{u}} (π : X ⟶ Spec (.of k')) [Smooth π] (hπ : IsProjectiveMorphism π)

/-- Pullback in a fixed degree along a composite. -/
theorem pullDeg_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℤ) : W.pullDeg (f ≫ g) n = W.pullDeg f n ∘ₗ W.pullDeg g n := by
  ext a
  simp [W.pull_comp]

/-- Pullback in a fixed degree along the identity. -/
theorem pullDeg_id (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    W.pullDeg (𝟙 X) n = LinearMap.id := by
  ext a
  simp [W.pull_id]

/-- **`H^0(Spec k') → H^0(X)` is bijective** for `X` smooth projective and geometrically connected
over `k'`, granted the final assumption of Definition 0FI2: `Γ(X, 𝒪_X) = k'` (Tag 0BUG (7)), so
`X ⟶ Spec k'` is `X ⟶ Spec Γ(X, 𝒪_X)` followed by an isomorphism. -/
theorem bijective_pullDeg_toSpec_zero [GeometricallyConnected π]
    (hW : W.GlobalSectionsCondition) : Function.Bijective (W.pullDeg (toSpec k π hπ) 0) := by
  have := isProper_of_isProjectiveMorphism π hπ
  have := geometricallyReduced_of_smooth π
  have hφ : Function.Bijective (globalSectionsAlgHom k π hπ) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper (k := k') π)
  let e := AlgEquiv.ofBijective (globalSectionsAlgHom k π hπ) hφ
  have h₁ : specMap e.symm.toAlgHom ≫ specMap (globalSectionsAlgHom k π hπ) = 𝟙 _ := by
    rw [← specMap_comp, ← specMap_id]
    congr 1
    ext r
    exact e.symm_apply_apply r
  have h₂ : specMap (globalSectionsAlgHom k π hπ) ≫ specMap e.symm.toAlgHom = 𝟙 _ := by
    rw [← specMap_comp, ← specMap_id]
    congr 1
    ext r
    exact e.apply_symm_apply r
  have hg : Function.Bijective (W.pullDeg (specMap (globalSectionsAlgHom k π hπ)) 0) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨W.pullDeg (specMap e.symm.toAlgHom) 0, fun a ↦ ?_, fun a ↦ ?_⟩
    · rw [← LinearMap.comp_apply, ← pullDeg_comp, h₁, pullDeg_id, LinearMap.id_apply]
    · rw [← LinearMap.comp_apply, ← pullDeg_comp, h₂, pullDeg_id, LinearMap.id_apply]
  rw [← toSpecGlobalSections_comp_specMap k π hπ, pullDeg_comp, LinearMap.coe_comp]
  exact (hW (ofOver k π hπ)).comp hg

end GeometricallyConnected

end WeilData

/-! ### Remark 0FI3 -/

namespace WeilCohomologyTheory

open SmoothProjectiveScheme WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F]

attribute [local instance] etale_of_isSeparable

/-- Let `H^*` be a Weil cohomology theory (Definition 0FI2). Let `X` be a geometrically
irreducible smooth projective scheme of dimension `d` over `k'`, with `k'/k` a finite separable
extension of fields. Suppose that `H^0(Spec(k')) = F_1 × ⋯ × F_r` for fields `F_i`. Then

1. `H^*(X) = ∏_i H^*(X) ⊗_{H^0(Spec k')} F_i`, by `x ↦ (x ⊗ 1)_i`, and likewise in each
   degree;
2. `H^0(X)` is free of rank `1` over `∏_i F_i`, and each factor
   `H^0(X) ⊗_{H^0(Spec k')} F_i` has dimension `1` over `F_i`;
3. the same is true in degree `2d`: `H^{2d}(X)` is free of rank `1` over `∏_i F_i`, and each
   `H^{2d}(X) ⊗_{H^0(Spec k')} F_i` has dimension `1` over `F_i`.

Here `X` is a scheme with a smooth projective, geometrically irreducible structure morphism
`p : X ⟶ Spec k'`, viewed over `k` through `Spec k' ⟶ Spec k` (`ofOver k p hp`), `Spec k'` is
the smooth projective `k`-scheme `spec k k'`, and "of dimension `d`" is
`topologicalKrullDim X = d`. `H^*(X)` is an `H^0(Spec k')`-algebra by pullback
along `X ⟶ Spec k'`, and `H^n(X)` is its degree `n` part (`WeilData.gradeOverSpec`).
"`H^0(Spec(k')) = F_1 × ⋯ × F_r`" is a finite family of fields `F_i`, each an
`H^0(Spec k')`-algebra, with `H^0(Spec k') → ∏_i F_i` bijective. The factor
`M ⊗_{H^0(Spec k')} F_i` is written as the base change `F_i ⊗_{H^0(Spec k')} M`, which is the same
module by the symmetry of the tensor product. The coefficient field `F` is not required to have
characteristic zero. -/
@[stacks 0FI3 "for H^* a Weil cohomology theory (0FI2), X geometrically irreducible smooth \
  projective of dimension d over a finite separable k'/k, viewed over k, and H^0(Spec k') → ∏ F_i \
  bijective for fields F_i: H^*(X) and each H^n(X) are ∏_i of their base changes to the F_i \
  by x ↦ (1 ⊗ x)_i; \
  H^0(X) and H^{2d}(X) are free of rank 1 over H^0(Spec k'), with each factor of dimension 1 over \
  F_i; M ⊗_{H^0(Spec k')} F_i is written F_i ⊗_{H^0(Spec k')} M; no CharZero F needed"]
theorem factorwise_rank_one_of_geometricallyIrreducible (W : WeilCohomologyTheory k F)
    {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k')) [Smooth p] [GeometricallyIrreducible p]
    (hp : IsProjectiveMorphism p) {d : ℕ} (hd : topologicalKrullDim X = d)
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, Field (K i)]
    [∀ i, Algebra (W.H0 (spec k k')) (K i)]
    (hK : Function.Bijective (RingHom.pi fun i ↦ algebraMap (W.H0 (spec k k')) (K i))) :
    Function.Bijective (fun (x : W.H (ofOver k p hp)) (i : ι) ↦
        (1 : K i) ⊗ₜ[W.H0 (spec k k')] x) ∧
      (∀ n : ℤ, Function.Bijective (fun (x : W.gradeOverSpec p hp n) (i : ι) ↦
        (1 : K i) ⊗ₜ[W.H0 (spec k k')] x)) ∧
      Nonempty (W.H0 (spec k k') ≃ₗ[W.H0 (spec k k')] W.gradeOverSpec p hp 0) ∧
      (∀ i, Module.finrank (K i) (K i ⊗[W.H0 (spec k k')] W.gradeOverSpec p hp 0) = 1) ∧
      Nonempty (W.H0 (spec k k') ≃ₗ[W.H0 (spec k k')] W.gradeOverSpec p hp (2 * d)) ∧
      (∀ i, Module.finrank (K i) (K i ⊗[W.H0 (spec k k')] W.gradeOverSpec p hp (2 * d)) = 1) := by
  classical
  have := Fintype.ofFinite ι
  set A := W.H0 (spec k k')
  have : Subsingleton (Spec (.of k')) := inferInstanceAs (Subsingleton (PrimeSpectrum k'))
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton p
  have : Nonempty X := IrreducibleSpace.toNonempty
  have : GeometricallyConnected p := geometricallyConnected_of_geometricallyIrreducible p
  obtain ⟨r, hr⟩ := exists_relativeDimension_of_irreducibleSpace p
  obtain rfl : d = r := by
    have h := topologicalKrullDim_eq_of_relativeDimension (d := r) p hr
    rw [hd] at h
    exact_mod_cast h
  have hX : IsNonemptyEquidimensional (ofOver k p hp) d :=
    isNonemptyEquidimensional_ofOverField (k := k) p hp hr
  have hbij := W.bijective_pullDeg_toSpec_zero p hp W.globalSections
  let f₀ : A →ₗ[A] W.gradeOverSpec p hp 0 :=
    { toFun := fun c ↦ ⟨W.pull (toSpec k p hp) (c : W.H (spec k k')),
        W.pull_grade (toSpec k p hp) 0 _ c.2⟩
      map_add' := fun a b ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun a b ↦ Subtype.ext (by
        change W.pull (toSpec k p hp) ((a : W.H (spec k k')) * b) =
          W.pull (toSpec k p hp) (a : W.H (spec k k')) * W.pull (toSpec k p hp) b
        exact map_mul _ _ _) }
  have hf₀ : Function.Bijective f₀ := by
    refine ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩
    · have h : W.pullDeg (toSpec k p hp) 0 ⟨a.1, a.2⟩ = W.pullDeg (toSpec k p hp) 0 ⟨b.1, b.2⟩ :=
        Subtype.ext (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg Subtype.val (hbij.1 h))
    · obtain ⟨y, hy⟩ := hbij.2 ⟨x.1, x.2⟩
      exact ⟨⟨y.1, y.2⟩, Subtype.ext (congrArg Subtype.val hy)⟩
  let e₀ : A ≃ₗ[A] W.gradeOverSpec p hp 0 := LinearEquiv.ofBijective f₀ hf₀
  have : FiniteDimensional F (W.gradeOverSpec p hp 0) :=
    have := W.poincareDuality.finiteDimensionality _ d hX 0
    Module.Finite.equiv (W.gradeOverSpecEquiv p hp 0).symm
  have : FiniteDimensional F (W.gradeOverSpec p hp (2 * d)) :=
    have := W.poincareDuality.finiteDimensionality _ d hX (2 * d)
    Module.Finite.equiv (W.gradeOverSpecEquiv p hp (2 * d)).symm
  have hsurj : ∀ i, Function.Surjective (algebraMap A (K i)) := fun i y ↦ by
    obtain ⟨a, ha⟩ := hK.2 (Pi.single i y)
    have h := congrFun ha i
    rw [Pi.single_eq_same] at h
    exact ⟨a, h⟩
  have hfactor : ∀ i, ∃ ε : A, algebraMap A (K i) ε = 1 ∧
      ∀ a, algebraMap A (K i) a = 0 → ε * a = 0 := fun i ↦ by
    obtain ⟨ε, hε⟩ := hK.2 (Pi.single i 1)
    have h := congrFun hε i
    rw [Pi.single_eq_same] at h
    refine ⟨ε, h, fun a ha ↦ hK.1 ?_⟩
    rw [map_mul, map_zero, hε]
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.mul_apply, Pi.single_eq_same, one_mul]
      exact ha
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hj, zero_mul]
      rfl
  have hdim : ∀ i, Module.finrank (K i) (K i ⊗[A] W.gradeOverSpec p hp (2 * d)) = 1 := by
    intro i
    obtain ⟨ε, hε₁, hε⟩ := hfactor i
    let : Algebra F (K i) := ((algebraMap A (K i)).comp (algebraMap F A)).toAlgebra
    have : IsScalarTower F A (K i) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    obtain ⟨hB, hB'⟩ := W.injective_pairingOverSpec p hp W.poincareDuality.perfectPairing hX
    exact finrank_tensorFactor_eq_one_of_pairing (F := F) hε₁ hε (hsurj i) e₀
      (W.pairingOverSpec p hp hX) hB hB' (W.pairingOverSpec_smul p hp hX)
  have hdec : ∀ (M : Type w) [AddCommGroup M] [Module A M],
      Function.Bijective (fun (x : M) (i : ι) ↦ (1 : K i) ⊗ₜ[A] x) := fun M _ _ ↦ by
    have h : ⇑(piFactorEquiv K hK M) = fun (x : M) (i : ι) ↦ (1 : K i) ⊗ₜ[A] x :=
      funext fun x ↦ funext fun i ↦ piFactorEquiv_apply K hK M x i
    exact h ▸ (piFactorEquiv K hK M).bijective
  refine ⟨hdec _, fun n ↦ hdec _, ⟨e₀⟩, fun i ↦ ?_, ?_, hdim⟩
  · exact (tensorEquivSelf e₀).finrank_eq.trans (Module.finrank_self (K i))
  · have e : ∀ i, K i ⊗[A] W.gradeOverSpec p hp (2 * d) ≃ₗ[A] K i := fun i ↦
      ((Classical.choice
        (haveI := Module.Free.of_divisionRing (K i) (K i ⊗[A] W.gradeOverSpec p hp (2 * d))
        Module.nonempty_linearEquiv_of_finrank_eq_one (hdim i))).symm).restrictScalars A
    exact ⟨((LinearEquiv.ofBijective (LinearMap.pi fun i ↦ Algebra.linearMap A (K i)) hK) ≪≫ₗ
      (LinearEquiv.piCongrRight e).symm ≪≫ₗ (piFactorEquiv K hK _).symm)⟩

end WeilCohomologyTheory

end Stacks.WeilCohomology

end
