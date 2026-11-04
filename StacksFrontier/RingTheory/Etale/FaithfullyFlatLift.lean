module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Smooth.Flat
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# Faithfully flat étale algebras lift along square-zero surjections

Let $A' \twoheadrightarrow A$ be a surjection of commutative rings whose kernel $I$ satisfies
$I^2 = 0$, and let $B_0$ be an étale and faithfully flat $A$-algebra. Then there is an étale and
faithfully flat $A'$-algebra $C$ of cardinality at most $\max(|A'|, \aleph_0)$ with
$A \otimes_{A'} C \cong B_0$ as $A$-algebras.

## Main results

* `Stacks.ChartGlue.exists_etale_faithfullyFlat_lift`: the statement above.
-/

@[expose] public section

universe u

open TensorProduct Cardinal

namespace Stacks.ChartGlue

/-- If `A' → A` is surjective with square-zero kernel `I` and `B₀` is an étale, faithfully flat
`A`-algebra, then there is an étale, faithfully flat `A'`-algebra `C`, of cardinality at most
`max #A' ℵ₀`, whose base change `A ⊗[A'] C` (with its left `A`-algebra structure) is isomorphic to
`B₀` as an `A`-algebra. -/
theorem exists_etale_faithfullyFlat_lift (A' A B₀ : Type u) [CommRing A'] [CommRing A]
    [CommRing B₀] [Algebra A' A] [Algebra A B₀] [Algebra A' B₀] [IsScalarTower A' A B₀]
    (hA : Function.Surjective (algebraMap A' A)) (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    [Algebra.Etale A B₀] [Module.FaithfullyFlat A B₀] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A' C), Algebra.Etale A' C ∧
      Module.FaithfullyFlat A' C ∧ #C ≤ max #A' ℵ₀ ∧
      Nonempty (A ⊗[A'] C ≃ₐ[A] B₀) := by
  obtain ⟨C, _, _, hC, ψ, hψ, hker⟩ := etale_lift_along_surjection A' A B₀ hA
  set I := RingHom.ker (algebraMap A' A)
  refine ⟨C, inferInstance, inferInstance, hC, ?_, ?_, ?_⟩
  · refine Module.FaithfullyFlat.of_comap_surjective fun p ↦ ?_
    have hIp : I ≤ p.asIdeal := Ideal.IsPrime.le_of_pow_le (n := 2) (hI ▸ bot_le)
    have : (p.asIdeal.map (algebraMap A' A)).IsPrime := Ideal.map_isPrime_of_surjective hA hIp
    have hq : (p.asIdeal.map (algebraMap A' A)).comap (algebraMap A' A) = p.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ hA, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hIp]
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := B₀)
      ⟨p.asIdeal.map (algebraMap A' A), this⟩
    refine ⟨PrimeSpectrum.comap (ψ : C →+* B₀) Q, PrimeSpectrum.ext ?_⟩
    have hQ' : Q.asIdeal.comap (algebraMap A B₀) = p.asIdeal.map (algebraMap A' A) :=
      congrArg PrimeSpectrum.asIdeal hQ
    show (Q.asIdeal.comap (ψ : C →+* B₀)).comap (algebraMap A' C) = p.asIdeal
    rw [Ideal.comap_comap, show (ψ : C →+* B₀).comp (algebraMap A' C) = algebraMap A' B₀ from
      ψ.comp_algebraMap, IsScalarTower.algebraMap_eq A' A B₀, ← Ideal.comap_comap, hQ', hq]
  · obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType A' C)
    refine (Cardinal.mk_le_of_surjective hf).trans <|
      MvPolynomial.cardinalMk_le_max_lift.trans ?_
    simp only [Cardinal.lift_uzero, Cardinal.mk_fin, Cardinal.lift_natCast]
    exact max_le (max_le le_sup_left (Cardinal.natCast_lt_aleph0.le.trans le_sup_right))
      le_sup_right
  · let F : A ⊗[A'] C →ₐ[A] B₀ :=
      Algebra.TensorProduct.lift (Algebra.ofId A B₀) ψ fun _ _ ↦ Commute.all _ _
    have hIker : RingHom.ker (ψ : C →+* B₀) ≤
        RingHom.ker (Algebra.TensorProduct.includeRight : C →ₐ[A'] A ⊗[A'] C).toRingHom := by
      rw [hker, Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      rw [(RingHom.mem_ker).mp hr, zero_tmul]
    let G : B₀ →ₐ[A'] A ⊗[A'] C :=
      AlgHom.liftOfSurjective ψ hψ Algebra.TensorProduct.includeRight hIker
    have hGψ (c : C) : G (ψ c) = 1 ⊗ₜ c :=
      AlgHom.liftOfSurjective_apply ψ hψ _ hIker c
    have hGF : G.comp (F.restrictScalars A') = AlgHom.id A' _ := by
      refine Algebra.TensorProduct.ext' fun a c ↦ ?_
      obtain ⟨a', rfl⟩ := hA a
      simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
        AlgHom.coe_id, id_eq, F, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, map_mul, hGψ]
      rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one]
    refine ⟨AlgEquiv.ofBijective F ⟨fun x y hxy ↦ ?_, fun b ↦ ?_⟩⟩
    · simpa using (AlgHom.congr_fun hGF x).symm.trans
        ((congrArg G hxy).trans (AlgHom.congr_fun hGF y))
    · obtain ⟨c, rfl⟩ := hψ b
      exact ⟨1 ⊗ₜ c, by simp [F]⟩

end Stacks.ChartGlue
