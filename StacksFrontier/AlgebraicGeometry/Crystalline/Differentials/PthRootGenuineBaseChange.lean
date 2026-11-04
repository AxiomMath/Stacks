module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeCompositeIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedGenuine
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionTorsionLevel

/-!
# The base change of completed de Rham complexes along `B' → D'` is bijective

Let `B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))` and let `D'` be its `p`-adic completion, the ring of
[Stacks, Lemma 60.25.3, Tag 07N1], with the divided powers `γ̂'` of [Stacks, Tag 07KD].  For every
`B'`-module `N` with a completed connection, the base change map of completed de Rham complexes
along `B' → D'`, from the forms of `B'` to the forms of `D'`, is bijective in every degree.

At the level `pⁿ` it is the comparison `N_n ⊗_{B'} Ω^q_{B'} → (D' ⊗_{B'} N_n) ⊗_{D'} Ω^q_{D'}` for
the module `N_n = N / pⁿ N`, which is killed by `pⁿ`; the `p`-adic completion of that comparison is
bijective by [Stacks, Lemma 60.20.1, Tag 07KK] in every degree
(`Crystalline.bijective_mapAddHom_of_tmul_ιMulti`), and a map between modules killed by `pⁿ` is its
own completion (`Crystalline.CompletedLevels.bijective_of_bijective_mapAddHom`).

## Main definitions

* `Crystalline.PthRootExtension.genuineFormsMapₛₗ` and
  `Crystalline.PthRootExtension.genuineCompletedFormsMap` — the comparison of forms along
  `B' → D'`.

## Main results

* `Crystalline.PthRootExtension.bijective_genuineBaseChangeTerm` — the base change map along
  `B' → D'` is bijective in every degree.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Lemma 60.19.1, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

namespace CompletedLevels

/-- A natural number kills a tensor product as soon as it kills every pure tensor. -/
private theorem nsmul_tensor_eq_zero_of_tmul {R : Type*} [CommRing R] {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (k : ℕ)
    (h : ∀ (x : X) (y : Y), k • (x ⊗ₜ[R] y) = 0) (t : X ⊗[R] Y) : k • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul x y => exact h x y
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

/-- `pⁿ` kills a tensor product as soon as it kills the first factor. -/
theorem pow_nsmul_tensor_eq_zero {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] (k : ℕ) (hX : ∀ x : X, k • x = 0)
    (t : X ⊗[R] Y) : k • t = 0 :=
  nsmul_tensor_eq_zero_of_tmul k
    (fun x y ↦ by rw [TensorProduct.smul_tmul', hX, TensorProduct.zero_tmul]) t

/-- `pⁿ` kills a tensor product as soon as it kills the second factor. -/
theorem pow_nsmul_tensor_eq_zero_right {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] (k : ℕ) (hY : ∀ y : Y, k • y = 0)
    (t : X ⊗[R] Y) : k • t = 0 :=
  nsmul_tensor_eq_zero_of_tmul k
    (fun x y ↦ by rw [← TensorProduct.tmul_smul, hY, TensorProduct.tmul_zero]) t

/-- `pⁿ` kills the level `pⁿ` of a module. -/
theorem pow_nsmul_levelModule_eq_zero {R : Type*} [CommRing R] (p n : ℕ) {X : Type*}
    [AddCommGroup X] [Module R X] (x : X ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X)) :
    (p ^ n : ℕ) • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact (PAdicCompletion.mem_pow_smul_top_iff p R n _).mpr ⟨y, rfl⟩

/-- **A completed base change of values is bijective as soon as the base changes of the values of
all the level modules are.** -/
theorem bijective_baseChangeValues_of_levels {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) (N : Type*) [AddCommGroup N] [Module R N] (X Y : Type*) [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module S Y] (g : X →ₛₗ[algebraMap R S] Y)
    (hlev : ∀ n : ℕ, Function.Bijective (Connection.baseChangeValues
      (M := N ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R N)) g)) :
    Function.Bijective (CompletedConnection.baseChangeValues p R S N
      (AdicCompletion (pAdicIdeal (A := R) p) X) (AdicCompletion (pAdicIdeal (A := S) p) Y)
      (adicCompletionMapₛₗ g (CompletedConnection.pAdicIdeal_map_le p R S))) := by
  refine adicCompletionMapₛₗ_bijective _ _ (fun n ↦ ?_)
  set e₁ := (levelTensorEquiv (pAdicIdeal (A := S) p) n
    (CompletedConnection.baseChangeCarrier p R S N) Y
    (CompletedConnection.pAdicIdeal_fg p S)).trans
    (TensorProduct.congr (baseChangeCarrierLevelEquiv p n N) (LinearEquiv.refl _ _)) with he₁
  set e₂ := levelTensorEquiv (pAdicIdeal (A := R) p) n N X
    (CompletedConnection.pAdicIdeal_fg p R) with he₂
  have hfac : (e₁ ∘ (adicQuotientMap (CompletedConnection.baseChangeTensor p R S N
      (AdicCompletion (pAdicIdeal (A := R) p) X) (AdicCompletion (pAdicIdeal (A := S) p) Y)
      (adicCompletionMapₛₗ g (CompletedConnection.pAdicIdeal_map_le p R S)))
      (CompletedConnection.pAdicIdeal_map_le p R S) n)) =
      (Connection.baseChangeValues g) ∘ e₂ :=
    funext fun y ↦ levelTensorEquiv_adicQuotientMap_baseChangeTensor p n N X Y g y
  have hbij := (hlev n).comp e₂.bijective
  rw [← hfac] at hbij
  exact (Function.Bijective.of_comp_iff' e₁.bijective _).mp hbij

end CompletedLevels

namespace PthRootExtension

open CompletedLevels

section Genuine

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))

/-- The structure map `B' → D'` as a morphism of `A`-algebras. -/
abbrev genuineAlgHom : primeRing B p lam →ₐ[A] completedPrimeRingSelf B p lam :=
  completionDPAlgHom (A := A) (B := primeRing B p lam) p

include hpnil in
/-- The structure map `B' → D'` is a divided power morphism. -/
theorem isDPMorphism_genuineAlgHom :
    IsDPMorphism (primeDividedPowers B p lam hp) (completedPrimeDividedPowers B p lam hp hpnil)
      (genuineAlgHom A B p lam).toRingHom :=
  completionDPAlgHom_isDPMorphism (A := A) (primeIdeal B p lam) (primeDividedPowers B p lam hp) p
    (isNilpotent_mk_primeIdeal B p lam hp hpnil)

/-- The comparison `Ω^q_{B'/A,γ'} → Ω^q_{D'/A,γ̂'}` of divided power forms along `B' → D'`. -/
def genuineFormsMapₛₗ (q : ℕ) :
    dividedPowerDifferentialForms (A := A) (primeDividedPowers B p lam hp) q →ₛₗ[algebraMap
      (primeRing B p lam) (completedPrimeRingSelf B p lam)]
      dividedPowerDifferentialForms (A := A) (completedPrimeDividedPowers B p lam hp hpnil) q where
  toFun := mapDifferentialFormsOfDPMorphism (A := A) (J := primeIdeal B p lam)
    (delta := primeDividedPowers B p lam hp) (completedPrimeDividedPowers B p lam hp hpnil)
    (genuineAlgHom A B p lam) (isDPMorphism_genuineAlgHom A B p lam hp hpnil) q
  map_add' := map_add _
  map_smul' := (mapDifferentialFormsOfDPMorphism (A := A) (J := primeIdeal B p lam)
    (delta := primeDividedPowers B p lam hp) (completedPrimeDividedPowers B p lam hp hpnil)
    (genuineAlgHom A B p lam) (isDPMorphism_genuineAlgHom A B p lam hp hpnil) q).map_smul'

/-- On a wedge of one-forms, the comparison along `B' → D'` is the wedge of the comparisons of
[Stacks, Lemma 60.20.1, Tag 07KK]. -/
theorem genuineFormsMapₛₗ_ιMulti (q : ℕ) (v : Fin q → primeForms A B p lam hp) :
    genuineFormsMapₛₗ A B p lam hp hpnil q (exteriorPower.ιMulti (primeRing B p lam) q v) =
      exteriorPower.ιMulti (completedPrimeRingSelf B p lam) q
        (completionDifferentialsMap (A := A) (primeIdeal B p lam) (primeDividedPowers B p lam hp) p
          (isNilpotent_mk_primeIdeal B p lam hp hpnil) ∘ v) :=
  mapDifferentialFormsOfDPMorphism_ιMulti (A := A) (J := primeIdeal B p lam)
    (delta := primeDividedPowers B p lam hp) (completedPrimeDividedPowers B p lam hp hpnil)
    (genuineAlgHom A B p lam) (isDPMorphism_genuineAlgHom A B p lam hp hpnil) q v

/-- The comparison `Ω̂^q_{B'} → Ω̂^q_{D'}` of completed forms along `B' → D'`. -/
abbrev genuineCompletedFormsMap (q : ℕ) :
    completedDividedPowerForms p A (primeDividedPowers B p lam hp) q →ₛₗ[algebraMap
      (primeRing B p lam) (completedPrimeRingSelf B p lam)]
      completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) q :=
  adicCompletionMapₛₗ (genuineFormsMapₛₗ A B p lam hp hpnil q)
    (CompletedConnection.pAdicIdeal_map_le p _ _)

/-- The completed comparison along `B' → D'` is
`Crystalline.completedMapDifferentialForms`. -/
theorem genuineCompletedFormsMap_eq (q : ℕ)
    (x : completedDividedPowerForms p A (primeDividedPowers B p lam hp) q) :
    genuineCompletedFormsMap A B p lam hp hpnil q x =
      completedMapDifferentialForms p A (primeDividedPowers B p lam hp)
        (completedPrimeDividedPowers B p lam hp hpnil) (genuineAlgHom A B p lam)
        (isDPMorphism_genuineAlgHom A B p lam hp hpnil) q x := rfl

end Genuine

section Bijective

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))

/-- **At every level, the base change of the values along `B' → D'` is bijective**, for a module
killed by `pⁿ`. -/
theorem bijective_genuineBaseChangeValues [Fact p.Prime] [Algebra (IntegersAtPrime p) A] (q n : ℕ)
    (P : Type u) [AddCommGroup P] [Module (primeRing B p lam) P] (hP : ∀ x : P, (p ^ n : ℕ) • x = 0)
        :
    Function.Bijective (Connection.baseChangeValues (M := P)
      (genuineFormsMapₛₗ A B p lam hp hpnil q)) := by
  have key : Function.Bijective (PAdicCompletion.mapAddHom p (primeRing B p lam)
      (completedPrimeRingSelf B p lam)
      (Connection.baseChangeValues (M := P) (genuineFormsMapₛₗ A B p lam hp hpnil q))) :=
    bijective_mapAddHom_of_tmul_ιMulti (A := A) (primeIdeal B p lam)
      (primeDividedPowers B p lam hp) p (isNilpotent_mk_primeIdeal B p lam hp hpnil) P q _
      (fun m v ↦ (Connection.baseChangeValues_tmul _ _ _).trans
        (congrArg (_ ⊗ₜ[completedPrimeRingSelf B p lam] ·)
          (genuineFormsMapₛₗ_ιMulti A B p lam hp hpnil q v)))
  exact bijective_of_bijective_mapAddHom p n (R := primeRing B p lam)
    (S := completedPrimeRingSelf B p lam)
    (fun t ↦ pow_nsmul_tensor_eq_zero (p ^ n) hP t)
    (fun t ↦ pow_nsmul_tensor_eq_zero (p ^ n) (pow_nsmul_tensor_eq_zero_right (p ^ n) hP) t)
    _ key

/-- **The base change of completed de Rham terms along `B' → D'` is bijective in every degree**,
for any `B'`-module. -/
theorem bijective_genuineBaseChangeValues_completed [Fact p.Prime] [Algebra (IntegersAtPrime p) A]
    (q : ℕ) (N : Type u) [AddCommGroup N] [Module (primeRing B p lam) N] :
    Function.Bijective (CompletedConnection.baseChangeValues p (primeRing B p lam)
      (completedPrimeRingSelf B p lam) N
      (completedDividedPowerForms p A (primeDividedPowers B p lam hp) q)
      (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) q)
      (genuineCompletedFormsMap A B p lam hp hpnil q)) :=
  bijective_baseChangeValues_of_levels p N _ _ (genuineFormsMapₛₗ A B p lam hp hpnil q)
    (fun n ↦ bijective_genuineBaseChangeValues A B p lam hp hpnil q n _
      (pow_nsmul_levelModule_eq_zero p n))

end Bijective

end PthRootExtension

end Crystalline
