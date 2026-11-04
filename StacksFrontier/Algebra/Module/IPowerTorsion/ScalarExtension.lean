module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.KerEval

/-!
# Scalar extension of ideal-power torsion modules

An `R`-algebra `S` which induces an isomorphism `R ⧸ Iⁿ ≅ S ⧸ IⁿS` for every `n > 0` does not
change a module all of whose elements are annihilated by some power of `I`: the canonical map
`M → M ⊗[R] S` is then bijective. For a finitely generated ideal the adic completion of `R` is
such an algebra, so an `I`-power torsion module is unchanged by completion.

## Main results

* `tensorProduct_mk_bijective_of_ideal_power_torsion`: the canonical scalar-extension map is
  bijective on ideal-power torsion modules, and in particular for the adic completion of a
  finitely generated ideal.

## Implementation notes

Torsion is taken in the elementwise form `∀ m, ∃ n, ∀ r ∈ Iⁿ, r • m = 0`, with no positivity
condition on the exponent. The hypothesis on `S` is stated as bijectivity of `Ideal.quotientMap`
at every positive power of `I`.

## References

* [Beauville--Laszlo]
* [The Stacks Project, Tag 0BNK](https://stacks.math.columbia.edu/tag/0BNK)
-/

@[expose] public section

universe u v w

open scoped TensorProduct

private theorem tmul_eq_zero_of_mem_map_pow
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M] (K : Ideal R)
    (x : M) (hx : ∀ r ∈ K, r • x = 0) {y : S}
    (hy : y ∈ Ideal.map (algebraMap R S) K) : x ⊗ₜ[R] y = 0 := by
  have hymod : y ∈ K • (⊤ : Submodule R S) := by rwa [Ideal.smul_top_eq_map]
  refine Submodule.smul_induction_on hymod ?_ ?_
  · intro r hr s hs
    rw [← TensorProduct.smul_tmul, hx r hr, TensorProduct.zero_tmul]
  · intro y z hy hz
    rw [TensorProduct.tmul_add, hy, hz, add_zero]

private theorem bounded_torsion_tensor_mk_bijective
    {R : Type u} [CommRing R] (I : Ideal R)
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    (n : ℕ)
    (e : (R ⧸ I ^ n) ≃ₐ[R]
      (S ⧸ Ideal.map (algebraMap R S) (I ^ n))) :
    Function.Bijective
      (fun x : Submodule.torsionBySet R M (I ^ n : Ideal R) =>
        TensorProduct.mk R _ _ x (1 : S)) := by
  classical
  let N := Submodule.torsionBySet R M (I ^ n : Ideal R)
  let J := Ideal.map (algebraMap R S) (I ^ n)
  let : Module (R ⧸ I ^ n) N :=
    (Submodule.torsionBySet_isTorsionBySet (R := R) (M := M)
      (s := (I ^ n : Ideal R))).module
  let f : S →+* (R ⧸ I ^ n) :=
    (e.symm.toRingEquiv.toRingHom).comp (Ideal.Quotient.mk J)
  let : Module S N := Module.compHom N f
  have hf (r : R) : f (algebraMap R S r) = Ideal.Quotient.mk (I ^ n) r := by
    apply e.injective
    show e (e.symm (Ideal.Quotient.mk J (algebraMap R S r))) =
      e (Ideal.Quotient.mk (I ^ n) r)
    rw [e.apply_symm_apply]
    calc
      Ideal.Quotient.mk J (algebraMap R S r) = algebraMap R (S ⧸ J) r := by simp
      _ = e (Ideal.Quotient.mk (I ^ n) r) := by
        simpa only [Ideal.Quotient.algebraMap_eq] using (e.commutes r).symm
  let actionMap : N →ₗ[R] S →ₗ[R] N :=
    { toFun := fun x =>
        { toFun := fun s => f s • x
          map_add' := fun s t => by simp [add_smul]
          map_smul' := fun r s => by
            show f (r • s) • x = r • (f s • x)
            rw [Algebra.smul_def, map_mul, hf,
              show r • (f s • x) = (Ideal.Quotient.mk (I ^ n) r) • (f s • x) by rfl, mul_smul] }
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => LinearMap.ext fun s => by
        show f s • ((algebraMap R (R ⧸ I ^ n) r) • x) =
          (algebraMap R (R ⧸ I ^ n) r) • (f s • x)
        exact smul_comm _ _ _ }
  let invMap : N ⊗[R] S →ₗ[R] N := TensorProduct.lift actionMap
  let can : N →ₗ[R] N ⊗[R] S := (TensorProduct.mk R N S).flip 1
  have hinv : Function.LeftInverse invMap can := fun x => by
    show f 1 • x = x
    simp [f]
  have hsurj : ∀ z : N ⊗[R] S, can (invMap z) = z := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [can]
    · intro x s
      show (f s • x) ⊗ₜ[R] (1 : S) = x ⊗ₜ[R] s
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk J s))
      have hquot : Ideal.Quotient.mk (I ^ n) r = e.symm (Ideal.Quotient.mk J s) := hr
      have hmk : Ideal.Quotient.mk J (algebraMap R S r) = Ideal.Quotient.mk J s := by
        calc
          Ideal.Quotient.mk J (algebraMap R S r) = e (Ideal.Quotient.mk (I ^ n) r) := by
            rw [Ideal.Quotient.mk_algebraMap]
            exact (e.commutes r).symm
          _ = Ideal.Quotient.mk J s := by simpa using congrArg e hquot
      have hdiff : s - algebraMap R S r ∈ J := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        rw [map_sub, hmk, sub_self]
      have hzero := tmul_eq_zero_of_mem_map_pow (I ^ n) x
        (fun a ha => Subtype.ext
          ((Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) x.1).mp x.2 ⟨a, ha⟩))
        hdiff
      have hscalar : (f s) • x = r • x := by
        show e.symm (Ideal.Quotient.mk J s) • x = r • x
        rw [← hquot]
        rfl
      rw [hscalar, TensorProduct.smul_tmul, Algebra.smul_def]
      have : s = algebraMap R S r + (s - algebraMap R S r) := by ring
      rw [this, TensorProduct.tmul_add, hzero, add_zero]
      simp
    · intro x y hx hy
      simp [hx, hy]
  exact ⟨hinv.injective, fun z => ⟨invMap z, hsurj z⟩⟩

set_option maxHeartbeats 1000000 in
-- Transporting the layer equivalences through the direct limit elaborates a large composed map.
private theorem torsion_tensor_mk_bijective
    {R : Type u} [CommRing R] (I : Ideal R)
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    (hM : ∀ m : M, ∃ n : ℕ, ∀ r ∈ I ^ n, r • m = 0)
    (hQ : ∀ n : ℕ, 0 < n →
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) (I ^ n))
          (algebraMap R S) Ideal.le_comap_map)) :
    Function.Bijective (fun m : M => TensorProduct.mk R M S m 1) := by
  classical
  let G : ℕ → Type w := fun n =>
    Submodule.torsionBySet R M ((I ^ (n + 1) : Ideal R) : Set R)
  let f : (i j : ℕ) → i ≤ j → G i →ₗ[R] G j := fun i j hij =>
    Submodule.inclusion <|
      Submodule.torsionBySet_le_torsionBySet_pow (i + 1) (j + 1)
        (Nat.add_le_add_right hij 1) I
  have : DirectedSystem G (f · · ·) := {
    map_self := by intro i x; rfl
    map_map := by intro i j k hij hjk x; rfl }
  let D := Module.DirectLimit G f
  let g : (i : ℕ) → G i →ₗ[R] M := fun i =>
    Submodule.subtype (Submodule.torsionBySet R M ((I ^ (i + 1) : Ideal R) : Set R))
  have Hg : ∀ i j (hij : i ≤ j) x, g j (f i j hij x) = g i x := fun _ _ _ _ => rfl
  let toM : D →ₗ[R] M := Module.DirectLimit.lift R ℕ G f g Hg
  have htoM_inj : Function.Injective toM :=
    Module.DirectLimit.lift_injective (g := g) (Hg := Hg) fun i x y hxy => Subtype.ext hxy
  have htoM_surj : Function.Surjective toM := by
    intro m
    obtain ⟨n, hn⟩ := hM m
    have hsmall : m ∈ Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) := by
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      exact hn a.1 a.2
    have hlarge : m ∈ Submodule.torsionBySet R M ((I ^ (n + 1) : Ideal R) : Set R) :=
      (Submodule.torsionBySet_le_torsionBySet_pow n (n + 1) (Nat.le_succ n) I) hsmall
    exact ⟨Module.DirectLimit.of R ℕ G f n ⟨m, hlarge⟩,
      Module.DirectLimit.lift_of (g := g) (Hg := Hg) (⟨m, hlarge⟩ : G n)⟩
  let eM : D ≃ₗ[R] M := LinearEquiv.ofBijective toM ⟨htoM_inj, htoM_surj⟩
  let qAlg (n : ℕ) (hn : 0 < n) :
      (R ⧸ I ^ n) ≃ₐ[R] (S ⧸ Ideal.map (algebraMap R S) (I ^ n)) :=
    AlgEquiv.ofBijective
      (Ideal.quotientMapₐ (Ideal.map (algebraMap R S) (I ^ n))
        (Algebra.ofId R S) Ideal.le_comap_map)
      (by
        show Function.Bijective
          (Ideal.quotientMap (Ideal.map (algebraMap R S) (I ^ n))
            (algebraMap R S) Ideal.le_comap_map)
        exact hQ n hn)
  let can (N : Type w) [AddCommGroup N] [Module R N] : N →ₗ[R] N ⊗[R] S :=
    (TensorProduct.mk R N S).flip 1
  have hcan : ∀ n, Function.Bijective (can (G n)) := by
    intro n
    convert (bounded_torsion_tensor_mk_bijective (R := R) I (S := S) (M := M)
      (n + 1) (qAlg (n + 1) (by omega))) using 1
    funext x
    rfl
  let eN : (n : ℕ) → G n ≃ₗ[R] G n ⊗[R] S := fun n =>
    LinearEquiv.ofBijective (can (G n)) (hcan n)
  let fT : (i j : ℕ) → i ≤ j → (G i ⊗[R] S) →ₗ[R] (G j ⊗[R] S) :=
    fun i j hij => LinearMap.rTensor S (f i j hij)
  have heN : ∀ i j (hij : i ≤ j),
      (eN j).toLinearMap.comp (f i j hij) = (fT i j hij).comp (eN i).toLinearMap := by
    intro i j hij
    ext x
    show (f i j hij x) ⊗ₜ[R] (1 : S) =
      LinearMap.rTensor S (f i j hij) (x ⊗ₜ[R] (1 : S))
    simp
  let eStage : Module.DirectLimit G f ≃ₗ[R]
      Module.DirectLimit (fun n => G n ⊗[R] S) fT :=
    Module.DirectLimit.congr eN heN
  let eD : D ≃ₗ[R] D ⊗[R] S :=
    eStage.trans (TensorProduct.directLimitLeft f S).symm
  have heD : eD.toLinearMap = can D := by
    apply Module.DirectLimit.hom_ext
    intro i
    ext x
    show (TensorProduct.directLimitLeft f S).symm
      (Module.DirectLimit.congr eN heN (Module.DirectLimit.of R ℕ G f i x)) =
      (Module.DirectLimit.of R ℕ G f i x) ⊗ₜ[R] 1
    rw [Module.DirectLimit.congr_apply_of]
    show (TensorProduct.directLimitLeft f S).symm
      (Module.DirectLimit.of R ℕ (fun n => G n ⊗[R] S) fT i (eN i x)) = _
    show (TensorProduct.directLimitLeft f S).symm
      (Module.DirectLimit.of R ℕ (fun n => G n ⊗[R] S) fT i (x ⊗ₜ[R] (1 : S))) = _
    exact TensorProduct.directLimitLeft_symm_of_tmul f S x 1
  let eTotal : M ≃ₗ[R] M ⊗[R] S :=
    eM.symm.trans (eD.trans (LinearEquiv.rTensor S eM))
  have heTotal : eTotal.toLinearMap = can M := by
    ext m
    show LinearEquiv.rTensor S eM (eD.toLinearMap (eM.symm m)) = m ⊗ₜ[R] 1
    rw [LinearMap.congr_fun heD (eM.symm m)]
    show (eM (eM.symm m)) ⊗ₜ[R] (1 : S) = m ⊗ₜ[R] (1 : S)
    simp
  rw [show (fun m : M => TensorProduct.mk R M S m 1) = can M from rfl, ← heTotal]
  exact eTotal.bijective

@[ega "0 7.2.12" "special case"]
private theorem adic_completion_quotient_map_bijective
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n))
        (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map) := by
  classical
  let C := AdicCompletion I R
  let J := Ideal.map (algebraMap R C) (I ^ n)
  have hker := AdicCompletion.ker_evalₐ_eq_map_pow I hI n
  constructor
  · rintro ⟨r⟩ ⟨s⟩ h
    apply Ideal.Quotient.eq.mpr
    have hmem : algebraMap R C r - algebraMap R C s ∈ J := Ideal.Quotient.eq.mp h
    have hmemKer : algebraMap R C (r - s) ∈ RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
      rw [hker]
      simpa [map_sub] using hmem
    have hquot : Ideal.Quotient.mk (I ^ n) (r - s) = 0 := by
      simpa [AdicCompletion.evalₐ_of, AdicCompletion.algebraMap_apply] using
        RingHom.mem_ker.mp hmemKer
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hquot
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    refine ⟨Ideal.Quotient.mk (I ^ n) r, ?_⟩
    have hzero : AdicCompletion.evalₐ I n (x - algebraMap R C r) = 0 := by
      rw [map_sub]
      have hmap : AdicCompletion.evalₐ I n (algebraMap R C r) =
          Ideal.Quotient.mk (I ^ n) r := by
        rw [AdicCompletion.algebraMap_apply]
        simp
      rw [hmap, hr]
      simp
    have hmem : x - algebraMap R C r ∈ J := by
      show x - algebraMap R C r ∈
        Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n)
      rw [← hker]
      exact (RingHom.mem_ker).mpr hzero
    show Ideal.Quotient.mk J (algebraMap R C r) = Ideal.Quotient.mk J x
    exact (Ideal.Quotient.eq).mpr (by simpa using J.neg_mem hmem)

/-- The canonical map from an ideal-power torsion module to its scalar extension is an
isomorphism when the scalar extension is unchanged modulo every positive power of the ideal. In
particular this holds for the adic completion of a finitely generated ideal; this is a slight
generalization of Beauville--Laszlo, Lemme 1. -/
@[stacks 0BNK, sga "2 IV 4.5" "more general", sga "2 IV 4.6" "more general"]
public theorem tensorProduct_mk_bijective_of_ideal_power_torsion
    (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type w) [AddCommGroup M] [Module R M]
    (hM : ∀ m : M, ∃ n : ℕ, ∀ r ∈ I ^ n, r • m = 0) :
    (∀ (S : Type v) [CommRing S] [Algebra R S],
      (∀ n : ℕ, 0 < n →
        Function.Bijective
          (Ideal.quotientMap (Ideal.map (algebraMap R S) (I ^ n))
            (algebraMap R S) Ideal.le_comap_map)) →
      Function.Bijective (fun m : M => TensorProduct.mk R M S m (1 : S))) ∧
    (I.FG →
      Function.Bijective
        (fun m : M => TensorProduct.mk R M (AdicCompletion I R) m 1)) := by
  exact ⟨fun S _ _ hQ => torsion_tensor_mk_bijective I hM hQ, fun hI =>
    torsion_tensor_mk_bijective I hM fun n _ => adic_completion_quotient_map_bijective I hI n⟩

end
