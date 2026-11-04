module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksFrontier.RingTheory.TensorAlgebra.Localization

/-!
# The fibre of a symmetric algebra over a residue field

Let `R → R'` be a ring map and `R → K → L`, `R → R' → L` two factorizations of a map `R → L`
through fields `K` and `L`. A linear map of `R`-modules whose base change to `R'` is bijective has
bijective base change to `K`: base change to `L` factors through both, and `K → L` is faithfully
flat.

Let `θ : Sym_R(M) ⟶ A` be a comparison of `R`-algebras which becomes an isomorphism after base
change to `R'`, where `R' ⊗_R M` is free of rank `r`. Then `K ⊗_R A ≅ Sym_K(K ⊗_R M)` is a
polynomial ring in `r` variables over `K`, since `K ⊗_R M` has dimension `r`, its base change to
`L` being that of the free module `R' ⊗_R M`.
In geometric terms, when `R → K` is the residue field at a point `u` of `Spec R` and `R → R'` an
étale map with a point `v` over `u` with residue field `L`, the fibre of `Spec A → Spec R` at `u`
is affine space `𝐀^r_{κ(u)}`.

## Main results

* `SymmetricAlgebra.bijective_baseChange_of_comparison`: a comparison `Sym_R(M) ⟶ A` becomes
  bijective after base change along `R → R'` as soon as `M` and `A` base change to `M'` and `A'`
  and the comparison `Sym_{R'}(M') ⟶ A'` is bijective and compatible with the first on
  generators.
* `LinearMap.bijective_baseChange_of_bijective_baseChange_tower`: bijectivity of the base change
  to `R'` gives bijectivity of the base change to `K`.
* `SymmetricAlgebra.exists_isPushout_mvPolynomial_of_bijective_baseChange`: the square
  `R → A`, `R → K`, `A → K[X_1, …, X_r]`, `K → K[X_1, …, X_r]` is a pushout of commutative rings.

## References

* [Stacks Project, Tag 01M1](https://stacks.math.columbia.edu/tag/01M1)
-/

@[expose] public section

open TensorProduct CategoryTheory

universe u

/-- **A comparison with a symmetric algebra which is bijective after base change.** Let
`θ : Sym_R(M) ⟶ A` be a morphism of `R`-algebras, `R → R'` a ring map, and `M ⟶ M'`, `A ⟶ A'`
maps exhibiting `M'` and `A'` as the base changes of `M` and `A` to `R'`. If a morphism of
`R'`-algebras `θ' : Sym_{R'}(M') ⟶ A'` is bijective and agrees with `θ` on generators, then the
base change of `θ` to `R'` is bijective: it is identified with `θ'` through
`R' ⊗_R Sym_R(M) ≅ Sym_{R'}(R' ⊗_R M) ≅ Sym_{R'}(M')`. -/
theorem SymmetricAlgebra.bijective_baseChange_of_comparison
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [Module R M']
    [IsScalarTower R R' M']
    {A A' : Type*} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R' A'] [Algebra R A']
    [IsScalarTower R R' A']
    (θ : SymmetricAlgebra R M →ₐ[R] A) (θ' : SymmetricAlgebra R' M' →ₐ[R'] A')
    (resM : M →ₗ[R] M') (resA : A →ₐ[R] A')
    (hM : Function.Bijective (resM.liftBaseChange R'))
    (hA : Function.Bijective (resA.toLinearMap.liftBaseChange R'))
    (hθ' : Function.Bijective θ')
    (hnat : ∀ m, resA (θ (SymmetricAlgebra.ι R M m)) = θ' (SymmetricAlgebra.ι R' M' (resM m))) :
    Function.Bijective (θ.toLinearMap.baseChange R') := by
  obtain ⟨E₀, hE₀⟩ := SymmetricAlgebra.exists_algEquiv_baseChange R R' M
  let γ := LinearEquiv.ofBijective (resM.liftBaseChange R') hM
  let Sγ := SymPow.symAlgMap γ.toLinearMap
  have hSγ : Function.Bijective Sγ :=
    (AlgEquiv.ofAlgHom Sγ (SymPow.symAlgMap γ.symm.toLinearMap)
      (SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => by simp [Sγ, SymPow.symAlgMap_ι]))
      (SymmetricAlgebra.algHom_ext
        (LinearMap.ext fun m => by simp [Sγ, SymPow.symAlgMap_ι]))).bijective
  have hs : ∀ s, resA (θ s) = θ' (Sγ (E₀.symm (1 ⊗ₜ s))) := by
    intro s
    induction s using SymmetricAlgebra.induction with
    | algebraMap r =>
      have h1 : (1 : R') ⊗ₜ[R] algebraMap R (SymmetricAlgebra R M) r =
          algebraMap R' _ (algebraMap R R' r) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one r,
          ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_self,
          RingHom.id_apply]
      rw [h1, AlgEquiv.commutes, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes,
        AlgHom.commutes, IsScalarTower.algebraMap_apply R R' A']
    | ι m =>
      rw [hnat, show E₀.symm (1 ⊗ₜ SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι _ _ (1 ⊗ₜ m) from
        E₀.symm_apply_eq.2 (hE₀ m).symm, SymPow.symAlgMap_ι]
      congr 2
      simp [γ]
    | mul a b ha hb =>
      rw [map_mul, map_mul, ha, hb, ← map_mul, ← map_mul, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb, ← map_add, ← map_add, ← map_add, TensorProduct.tmul_add]
  have key : (resA.toLinearMap.liftBaseChange R') ∘ₗ θ.toLinearMap.baseChange R' =
      θ'.toLinearMap ∘ₗ (Sγ.toLinearMap ∘ₗ E₀.symm.toLinearMap) := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul r s =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul,
        LinearMap.liftBaseChange_tmul, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply]
      rw [show r ⊗ₜ[R] s = r • ((1 : R') ⊗ₜ s) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, map_smul, hs]
  have hcomp : Function.Bijective ((resA.toLinearMap.liftBaseChange R') ∘ₗ
      θ.toLinearMap.baseChange R') := by
    rw [key]
    exact hθ'.comp (hSγ.comp E₀.symm.bijective)
  exact (Function.Bijective.of_comp_iff' hA _).1 hcomp

/-- Base change of `f` to `L` is bijective iff that of `f.baseChange B` is, for a tower
`R → B → L`. -/
private theorem bijective_baseChange_baseChange_iff
    {R B L : Type*} [CommRing R] [CommRing B] [CommRing L]
    [Algebra R B] [Algebra B L] [Algebra R L] [IsScalarTower R B L]
    {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) :
    Function.Bijective ((f.baseChange B).baseChange L) ↔ Function.Bijective (f.baseChange L) := by
  rw [LinearMap.baseChange_baseChange (A := B) (B := L), LinearMap.coe_comp, LinearMap.coe_comp]
  exact ((AlgebraTensorModule.cancelBaseChange R B L L P).symm.bijective.of_comp_iff' _).trans
    ((AlgebraTensorModule.cancelBaseChange R B L L N).bijective.of_comp_iff _)

/-- **A linear map whose base change to `R'` is bijective has bijective base change to `K`**,
whenever `R → R'` and `R → K` are completed to a commutative square `R' → L ← K` with `K → L`
faithfully flat. -/
theorem LinearMap.bijective_baseChange_of_bijective_baseChange_tower
    {R R' K L : Type*} [CommRing R] [CommRing R'] [CommRing K] [CommRing L]
    [Algebra R R'] [Algebra R K] [Algebra R' L] [Algebra K L] [Algebra R L]
    [IsScalarTower R R' L] [IsScalarTower R K L] [Module.FaithfullyFlat K L]
    {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (h : Function.Bijective (f.baseChange R')) :
    Function.Bijective (f.baseChange K) := by
  have hL : Function.Bijective (f.baseChange L) := by
    rw [← bijective_baseChange_baseChange_iff (B := R'), LinearMap.baseChange_eq_ltensor]
    exact ((LinearEquiv.ofBijective _ h).lTensor L).bijective
  have hb : Function.Bijective ((f.baseChange K).baseChange L) :=
    (bijective_baseChange_baseChange_iff (B := K) f).2 hL
  rw [LinearMap.baseChange_eq_ltensor] at hb
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective K L _).1 hb

/-- **The fibre of a symmetric algebra is a polynomial ring.** Let `θ : Sym_R(M) ⟶ A` be a
morphism of `R`-algebras whose base change to `R'` is bijective, with `R' ⊗_R M` free on a finite
type `n`, and let `R → K → L ← R' ← R` be a commutative square with `K` and `L` fields. Then
`K ⊗_R A ≅ K[X_i, i ∈ n]` as `K`-algebras, in the form of a pushout square of commutative rings
`R → A → K[X_i, i ∈ n] ← K ← R`. -/
theorem SymmetricAlgebra.exists_isPushout_mvPolynomial_of_bijective_baseChange
    {R R' K L : Type u} [CommRing R] [CommRing R'] [Field K] [Field L]
    [Algebra R R'] [Algebra R K] [Algebra R' L] [Algebra K L] [Algebra R L]
    [IsScalarTower R R' L] [IsScalarTower R K L]
    {M : Type u} [AddCommGroup M] [Module R M] {A : Type u} [CommRing A] [Algebra R A]
    (θ : SymmetricAlgebra R M →ₐ[R] A) (hθ : Function.Bijective (θ.toLinearMap.baseChange R'))
    {n : Type u} [Finite n] (b : Module.Basis n R' (R' ⊗[R] M)) :
    ∃ φ : A →+* MvPolynomial n K,
      IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R K))
        (CommRingCat.ofHom φ) (CommRingCat.ofHom MvPolynomial.C) := by
  let ΘK : K ⊗[R] SymmetricAlgebra R M ≃ₐ[K] K ⊗[R] A :=
    AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id K K) θ)
      (LinearMap.bijective_baseChange_of_bijective_baseChange_tower (R' := R') (L := L)
        θ.toLinearMap hθ (K := K))
  have := Fintype.ofFinite n
  have hrankL : Module.rank L (L ⊗[K] (K ⊗[R] M)) = Fintype.card n := by
    rw [((AlgebraTensorModule.cancelBaseChange R K L L M).trans
      (AlgebraTensorModule.cancelBaseChange R R' L L M).symm).rank_eq,
      rank_eq_card_basis (b.baseChange L)]
  have hrankK : Module.rank K (K ⊗[R] M) = Fintype.card n := by
    have hbase := Module.rank_baseChange (R := L) (S := K) (M' := K ⊗[R] M)
    rw [hrankL] at hbase
    have hlift : Cardinal.lift.{u} (Module.rank K (K ⊗[R] M)) =
        Cardinal.lift.{u} (Fintype.card n : Cardinal.{u}) := by
      rw [← hbase]
      simp
    exact Cardinal.lift_injective hlift
  have : Module.Finite K (K ⊗[R] M) := by
    rw [← Module.rank_lt_aleph0_iff, hrankK]
    exact Cardinal.natCast_lt_aleph0
  let bK : Module.Basis n K (K ⊗[R] M) := (Module.finBasisOfFinrankEq K _
    (Module.finrank_eq_of_rank_eq hrankK)).reindex (Fintype.equivFin n).symm
  obtain ⟨e₀, -⟩ := SymmetricAlgebra.exists_algEquiv_baseChange R K M
  let Φ : K ⊗[R] A ≃ₐ[K] MvPolynomial n K :=
    ΘK.symm.trans (e₀.symm.trans (SymmetricAlgebra.equivMvPolynomial bK))
  refine ⟨Φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  refine ((CommRingCat.isPushout_tensorProduct R K A).flip).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Φ.toRingEquiv.toCommRingCatIso) ?_ ?_ ?_ ?_
  · simp
  · simp
  · ext a; simp
  · exact CommRingCat.hom_ext (RingHom.ext fun k => Φ.commutes k)
