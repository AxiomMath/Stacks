module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import StacksFrontier.RingTheory.AdicCompletion.AdicCompletionMapUniqueness
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension

/-!
# The degree of a finite extension of local domains after completion

Let `D ⊆ E` be a finite extension of Noetherian domains, `q` a prime of `E` lying over the prime
`p` of `D`, and `D_p ⟶ E_q` the induced local homomorphism of local rings. If `E_q` and `D_p`
have the same dimension and both completions are domains, then the completion `E_q^∧` is a
finite torsion free (indeed faithful) module over `D_p^∧`, of rank at most `[E : D]`.

## The argument

By [Stacks, Tag 07N9] the base change `E ⊗_D D_p^∧` is the product of the completions of the
local rings of `E` at the primes over `p`, one of which is `E_q^∧`. The projection to that factor
is a surjective `D_p^∧`-linear map `D_p^∧ ⊗_D E ⟶ E_q^∧`: its restriction to `D_p^∧` is the map
on completions induced by `D_p ⟶ E_q`, because a ring map out of a completion is determined by
its restriction to the base ring (`eq_adicCompletionMap_of_apply_algebraMap`), and a ring map out
of `D_p` by its restriction to `D`. The rank of `D_p^∧ ⊗_D E` over `D_p^∧` is `[E : D]`, as
`D ⟶ D_p^∧` is an injective map of domains, so finiteness and the rank bound follow.

Faithfulness is a dimension count: the kernel `P` of `D_p^∧ ⟶ E_q^∧` is prime, `E_q^∧` is
integral over `D_p^∧ / P`, so `dim E_q^∧ = dim D_p^∧ / P`; a nonzero element of `P` would make
this strictly smaller than `dim D_p^∧ = dim D_p = dim E_q = dim E_q^∧` ([Stacks, Tag 07NV]).

## Main definitions

* `AlgebraicGeometry.adicCompletionLocalAlgebra`: the algebra structure on the completion of a
  local ring `B` over the completion of a local ring `A`, for a local homomorphism `A ⟶ B`; its
  structure map is `adicCompletionMap (algebraMap A B) (maximalIdeal A) (maximalIdeal B) _`.

## Main results

* `AlgebraicGeometry.injective_algebraMap_of_isIntegral_of_ringKrullDim_eq`: an integral algebra
  over a Noetherian local domain which is a domain of the same dimension is faithful.
* `AlgebraicGeometry.finite_faithfulSMul_finrank_le_adicCompletion_of_isLocalization`.

## References

* [Stacks Project, Tag 07N9](https://stacks.math.columbia.edu/tag/07N9)
* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
* [Stacks Project, Tag 00OK](https://stacks.math.columbia.edu/tag/00OK)
-/

@[expose] public noncomputable section

open IsLocalRing TensorProduct

universe u

namespace AlgebraicGeometry

/-- The maximal ideal of a local ring maps into the maximal ideal along a local homomorphism. -/
theorem map_maximalIdeal_le_of_isLocalHom (A B : Type*) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] :
    (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B :=
  Ideal.map_le_iff_le_comap.mpr (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm.le

/-- **The completion of a local algebra over the completion of the base.** For a local
homomorphism of local rings `A ⟶ B`, the completion `B^∧` of `B` at its maximal ideal is an
algebra over the completion `A^∧` of `A` at its maximal ideal, through the induced map
`adicCompletionMap (algebraMap A B) (maximalIdeal A) (maximalIdeal B) _`. -/
abbrev adicCompletionLocalAlgebra (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] :
    Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
  (adicCompletionMap (algebraMap A B) (maximalIdeal A) (maximalIdeal B)
    (map_maximalIdeal_le_of_isLocalHom A B)).toAlgebra

/-- **An integral domain over a Noetherian local domain, of the same dimension, is faithful.**
The kernel `P` of `A ⟶ B` is prime and `B` is integral over `A / P`, so `dim B = dim A / P`
([Stacks, Tag 00OK]); a nonzero element `a ∈ P` would give `dim A / P ≤ dim A / (a) < dim A`. -/
theorem injective_algebraMap_of_isIntegral_of_ringKrullDim_eq (A B : Type*) [CommRing A]
    [CommRing B] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [IsDomain B] [Algebra A B]
    [Algebra.IsIntegral A B] (hdim : ringKrullDim B = ringKrullDim A) :
    Function.Injective (algebraMap A B) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let P := RingHom.ker (algebraMap A B)
  let : Algebra (A ⧸ P) B := (RingHom.kerLift (algebraMap A B)).toAlgebra
  have : IsScalarTower A (A ⧸ P) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral (A ⧸ P) B :=
    ⟨fun b => (Algebra.IsIntegral.isIntegral (R := A) b).tower_top⟩
  have : FaithfulSMul (A ⧸ P) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective _)
  have h1 : ringKrullDim (A ⧸ P) = ringKrullDim B := Algebra.IsIntegral.ringKrullDim_eq _ _
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr haP
  have h2 : ringKrullDim (A ⧸ P) ≤ ringKrullDim (A ⧸ Ideal.span {a}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have h4 : ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span {a}) := by
    rwa [← hdim, ← h1]
  have h5 : ringKrullDim A + 1 ≤ ringKrullDim A := (add_le_add_left h4 1).trans
    (ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero ha0))
  have hlt := ringKrullDim_lt_top (R := A)
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_of_gt (lt_of_lt_of_le
    (WithBot.bot_lt_coe (0 : ℕ∞)) hnn))
  rw [← hd] at hlt h5
  induction d using ENat.recTopCoe with
  | top => exact lt_irrefl _ hlt
  | coe m =>
    have : m + 1 ≤ m := by exact_mod_cast h5
    omega

/-- An `E`-algebra map `E ⊗[D] Dp^∧ ⟶ Eq^∧` restricts on `Dp^∧` to the map on completions induced
by `Dp ⟶ Eq`. -/
theorem algHom_comp_includeRight_eq_algebraMap (D E : Type*) [CommRing D] [CommRing E]
    [Algebra D E] (p : Ideal D) [p.IsPrime] (Dp Eq : Type*) [CommRing Dp] [CommRing Eq]
    [Algebra D Dp] [IsLocalization.AtPrime Dp p] [Algebra E Eq] [Algebra Dp Eq] [Algebra D Eq]
    [IsScalarTower D Dp Eq] [IsScalarTower D E Eq] [IsLocalRing Dp] [IsLocalRing Eq]
    [IsLocalHom (algebraMap Dp Eq)] [IsNoetherianRing Dp]
    (π : E ⊗[D] AdicCompletion (maximalIdeal Dp) Dp →ₐ[E] AdicCompletion (maximalIdeal Eq) Eq) :
    letI := adicCompletionLocalAlgebra Dp Eq
    π.toRingHom.comp (Algebra.TensorProduct.includeRight (R := D) (A := E)
      (B := AdicCompletion (maximalIdeal Dp) Dp)).toRingHom = algebraMap _ _ := by
  let := adicCompletionLocalAlgebra Dp Eq
  let R := AdicCompletion (maximalIdeal Dp) Dp
  let C := AdicCompletion (maximalIdeal Eq) Eq
  let ψ : R →+* C := π.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := D) (A := E) (B := R)).toRingHom
  change ψ = algebraMap R C
  refine eq_adicCompletionMap_of_apply_algebraMap (algebraMap Dp Eq) (maximalIdeal Dp)
    (maximalIdeal Eq) (map_maximalIdeal_le_of_isLocalHom Dp Eq)
    ((isNoetherianRing_iff_ideal_fg Dp).mp inferInstance _) ψ fun a => ?_
  have hext : ψ.comp (algebraMap Dp R) = (algebraMap Eq C).comp (algebraMap Dp Eq) := by
    refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun d => ?_)
    simp only [RingHom.comp_apply]
    have h2 : ψ (algebraMap D R d) = algebraMap E C (algebraMap D E d) := by
      change π ((1 : E) ⊗ₜ[D] algebraMap D R d) = _
      rw [show (1 : E) ⊗ₜ[D] algebraMap D R d = algebraMap E (E ⊗[D] R) (algebraMap D E d) by
        rw [Algebra.algebraMap_eq_smul_one (A := R) d, TensorProduct.tmul_smul,
          ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one,
          IsScalarTower.algebraMap_apply D E (E ⊗[D] R)]]
      exact π.commutes _
    rw [← IsScalarTower.algebraMap_apply D Dp R d, h2, ← IsScalarTower.algebraMap_apply D Dp Eq,
      IsScalarTower.algebraMap_apply D E Eq]
    rfl
  exact RingHom.congr_fun hext a

/-- For a finite algebra `E` over a Noetherian ring `D` and a prime `q` of `E` over `p`, there is a
`Dp^∧`-linear surjection `Dp^∧ ⊗[D] E ⟶ Eq^∧` ([Stacks, Tag 07N9]). -/
theorem exists_surjective_tensor_adicCompletion (D E : Type*) [CommRing D] [CommRing E]
    [IsNoetherianRing D] [Algebra D E] [Module.Finite D E]
    (p : Ideal D) [p.IsPrime] (q : Ideal E) [q.IsPrime] [q.LiesOver p]
    (Dp Eq : Type*) [CommRing Dp] [CommRing Eq] [Algebra D Dp] [IsLocalization.AtPrime Dp p]
    [Algebra E Eq] [IsLocalization.AtPrime Eq q] [Algebra Dp Eq] [Algebra D Eq]
    [IsScalarTower D Dp Eq] [IsScalarTower D E Eq]
    [IsLocalRing Dp] [IsLocalRing Eq] [IsLocalHom (algebraMap Dp Eq)] :
    letI := adicCompletionLocalAlgebra Dp Eq
    ∃ L : AdicCompletion (maximalIdeal Dp) Dp ⊗[D] E →ₗ[AdicCompletion (maximalIdeal Dp) Dp]
      AdicCompletion (maximalIdeal Eq) Eq, Function.Surjective L := by
  classical
  let := adicCompletionLocalAlgebra Dp Eq
  let R := AdicCompletion (maximalIdeal Dp) Dp
  let C := AdicCompletion (maximalIdeal Eq) Eq
  have : IsNoetherianRing Dp := IsLocalization.isNoetherianRing p.primeCompl Dp inferInstance
  obtain ⟨Φ⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (S := E) p Dp
    (fun x : p.primesOver E => Localization.AtPrime x.1)
  let x₀ : p.primesOver E := ⟨q, ‹q.IsPrime›, ‹q.LiesOver p›⟩
  obtain ⟨T⟩ := AdicCompletion.nonempty_algEquiv_of_algEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) Eq)
    (maximalIdeal (Localization.AtPrime q)) (maximalIdeal Eq)
    (IsLocalRing.map_ringEquiv_maximalIdeal
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) Eq).toRingEquiv).symm
  let π : E ⊗[D] R →ₐ[E] C :=
    (T.toAlgHom.comp (Pi.evalAlgHom E
      (fun x : p.primesOver E => AdicCompletion (maximalIdeal (Localization.AtPrime x.1))
        (Localization.AtPrime x.1)) x₀)).comp Φ.toAlgHom
  have hπs : Function.Surjective π := by
    intro c
    obtain ⟨y, hy⟩ := T.surjective c
    refine ⟨Φ.symm (Pi.single x₀ y), ?_⟩
    simp [π, hy]
  let σ := Algebra.TensorProduct.comm D R E
  let L : R ⊗[D] E →ₗ[R] C :=
    { toFun := fun z => π (σ z)
      map_add' := fun z w => by simp
      map_smul' := fun r z => by
        rw [Algebra.smul_def, map_mul, map_mul, RingHom.id_apply, Algebra.smul_def,
          ← algHom_comp_includeRight_eq_algebraMap D E p Dp Eq π]
        congr 1 }
  refine ⟨L, fun c => ?_⟩
  obtain ⟨y, rfl⟩ := hπs c
  exact ⟨σ.symm y, by simp [L]⟩

/-- **The completion of a finite extension of local domains.** Let `D ⊆ E` be a finite extension
of Noetherian domains, `q` a prime of `E` over the prime `p` of `D`, `Dp` and `Eq` the local rings
at `p` and `q`, with `Dp ⟶ Eq` local and `dim Eq = dim Dp`, and suppose both completions `R = Dp^∧`
and `C = Eq^∧` are domains. Then, for the algebra structure
`AlgebraicGeometry.adicCompletionLocalAlgebra Dp Eq`, `C` is a finite faithful `R`-module of
rank at most `[E : D]`. -/
theorem finite_faithfulSMul_finrank_le_adicCompletion_of_isLocalization (D E : Type u)
    [CommRing D] [CommRing E] [IsDomain D] [IsDomain E] [IsNoetherianRing D] [Algebra D E]
    [Module.Finite D E] [FaithfulSMul D E]
    (p : Ideal D) [p.IsPrime] (q : Ideal E) [q.IsPrime] [q.LiesOver p]
    (Dp Eq : Type u) [CommRing Dp] [CommRing Eq] [Algebra D Dp] [IsLocalization.AtPrime Dp p]
    [Algebra E Eq] [IsLocalization.AtPrime Eq q] [Algebra Dp Eq] [Algebra D Eq]
    [IsScalarTower D Dp Eq] [IsScalarTower D E Eq]
    [IsLocalRing Dp] [IsLocalRing Eq] [IsLocalHom (algebraMap Dp Eq)]
    (hdim : ringKrullDim Eq = ringKrullDim Dp)
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal Dp) Dp)]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal Eq) Eq)] :
    letI := adicCompletionLocalAlgebra Dp Eq
    Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal Dp) Dp)
        (AdicCompletion (IsLocalRing.maximalIdeal Eq) Eq) ∧
      FaithfulSMul (AdicCompletion (IsLocalRing.maximalIdeal Dp) Dp)
        (AdicCompletion (IsLocalRing.maximalIdeal Eq) Eq) ∧
      Module.finrank (AdicCompletion (IsLocalRing.maximalIdeal Dp) Dp)
          (AdicCompletion (IsLocalRing.maximalIdeal Eq) Eq) ≤ Module.finrank D E := by
  let := adicCompletionLocalAlgebra Dp Eq
  let R := AdicCompletion (maximalIdeal Dp) Dp
  let C := AdicCompletion (maximalIdeal Eq) Eq
  have : IsNoetherianRing Dp := IsLocalization.isNoetherianRing p.primeCompl Dp inferInstance
  have : IsNoetherianRing E := IsNoetherianRing.of_finite D E
  have : IsNoetherianRing Eq := IsLocalization.isNoetherianRing q.primeCompl Eq inferInstance
  obtain ⟨L, hLs⟩ := exists_surjective_tensor_adicCompletion D E p q Dp Eq
  have hfin : Module.Finite R C := Module.Finite.of_surjective L hLs
  have hDR : FaithfulSMul D R := by
    refine (faithfulSMul_iff_algebraMap_injective D R).mpr ?_
    rw [IsScalarTower.algebraMap_eq D Dp R]
    exact (AdicCompletion.of_injective (maximalIdeal Dp) Dp).comp
      (IsLocalization.injective Dp (Ideal.primeCompl_le_nonZeroDivisors p))
  have hdimRC : ringKrullDim C = ringKrullDim R := by
    rw [← ringKrullDim_adicCompletion_maximalIdeal, ← ringKrullDim_adicCompletion_maximalIdeal,
      hdim]
  exact ⟨hfin, (faithfulSMul_iff_algebraMap_injective R C).mpr
      (injective_algebraMap_of_isIntegral_of_ringKrullDim_eq R C hdimRC),
    (LinearMap.finrank_le_finrank_of_surjective hLs).trans
      (TensorProduct.isBaseChange D E R).finrank_eq.le⟩

end AlgebraicGeometry

end
