module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.AdicCompletion.Quotient
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# A surjection onto a complete local ring from a completed local polynomial ring

Let `Λ` be a Noetherian ring and let `R` be a Noetherian complete local `Λ`-algebra.
Suppose a polynomial ring `Λ[x₁, …, x_s]` maps to `R` in such a way that the induced
map to `R / 𝔪_R ^ 2` is surjective, and let `p` be the inverse image of `𝔪_R`.  Then the
localization `A = Λ[x₁, …, x_s]_p` is a Noetherian local ring, its completion
`P = A^∧` is a Noetherian complete local ring, and the given map extends uniquely to a
*surjective* local homomorphism `P → R`.

This is the surjection labelled (07XC) inside the proof of Artin approximation for
objects of a limit preserving stack (Stacks 07XB).

The proof has two halves.  The map `A → R` is the universal property of the
localization, since the complement of `p` lands in the units of `R`; it extends to the
completion because `R` is `𝔪_R`-adically complete, and the extension is unique among
local maps because `R` is Hausdorff for the `𝔪_R`-adic topology.  Surjectivity is a
Nakayama argument: the hypothesis on `R / 𝔪_R ^ 2` forces
`𝔪_R ⊆ 𝔪_A · R + 𝔪_R ^ 2`, so `𝔪_A` generates `𝔪_R`, and then completeness upgrades
surjectivity modulo `𝔪_R` to surjectivity.

## Main results

* `AdicCompletion.exists_surjective_adicCompletionMap`: the completion `P` is a Noetherian
  complete local ring and the given map extends uniquely to a surjective local homomorphism
  `P → R`.

## References

* [Stacks Project, Tag 07XC](https://stacks.math.columbia.edu/tag/07XC)
-/

@[expose] public section

open IsLocalRing

namespace AdicCompletion

/-- The adic completion of a ring is a tower over itself through the identity, which is
the scalar tower needed to compare the completion's own module structures. -/
private theorem self_scalarTower {A : Type*} [CommRing A] (I : Ideal A) :
    IsScalarTower A (AdicCompletion I A) (AdicCompletion I A) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A ring map sending `I` into `J` sends the `n`-th power of `I` into the `n`-th power of `J`. -/
private theorem map_pow_le_pow_of_map_le {S T : Type*} [CommRing S] [CommRing T] (u : S →+* T)
    {I : Ideal S} {J : Ideal T} (h : I.map u ≤ J) (n : ℕ) : (I ^ n).map u ≤ J ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono h n

/-- **Stacks Project, Tag 07XC.** A map from a polynomial ring to a Noetherian
complete local ring which is surjective modulo the square of the maximal ideal
extends to a surjective local map from the completion of its localization at
the residue-field kernel. -/
@[stacks 07XC]
theorem exists_surjective_adicCompletionMap
    (Λ R : Type*) [CommRing Λ] [CommRing R] [Algebra Λ R]
    [IsNoetherianRing Λ] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (s : ℕ) (p : Ideal (MvPolynomial (Fin s) Λ)) [p.IsMaximal]
    (f : MvPolynomial (Fin s) Λ →ₐ[Λ] R)
    (hp : Ideal.comap f.toRingHom (maximalIdeal R) = p)
    (hmod : Function.Surjective
      ((Ideal.Quotient.mk ((maximalIdeal R) ^ 2)).comp f.toRingHom)) :
    let A := Localization.AtPrime p
    let P := AdicCompletion (maximalIdeal A) A
    IsNoetherianRing P ∧ IsLocalRing P ∧
      IsAdicComplete (maximalIdeal P) P ∧
      ∃ g : A →+* R,
        g.comp (algebraMap (MvPolynomial (Fin s) Λ) A) = f.toRingHom ∧
        IsLocalHom g ∧
        ∃ φ : P →+* R,
          φ.comp (algebraMap A P) = g ∧
            Function.Surjective φ ∧ IsLocalHom φ ∧
              ∀ ψ : P →+* R,
                ψ.comp (algebraMap A P) = g → IsLocalHom ψ → ψ = φ := by
  classical
  dsimp
  let A := Localization.AtPrime p
  let P := AdicCompletion (maximalIdeal A) A
  let g : A →+* R := IsLocalization.lift (M := p.primeCompl) (g := f.toRingHom)
    fun x => IsLocalRing.notMem_maximalIdeal.mp fun h => x.2 (hp ▸ h)
  have hg : g.comp (algebraMap (MvPolynomial (Fin s) Λ) A) = f.toRingHom :=
    IsLocalization.lift_comp (M := p.primeCompl) (g := f.toRingHom) _
  have hglocal : IsLocalHom g := by
    apply ((IsLocalRing.local_hom_TFAE g).out 4 1).mp
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_le_iff_le_comap,
      Ideal.comap_comap, hg, hp]
  have hgz (z : MvPolynomial (Fin s) Λ) : g (algebraMap _ A z) = f z := RingHom.congr_fun hg z
  have hmod' (r : R) : ∃ z, f z - r ∈ (maximalIdeal R) ^ 2 := by
    obtain ⟨z, hz⟩ := hmod (Ideal.Quotient.mk ((maximalIdeal R) ^ 2) r)
    exact ⟨z, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hz⟩
  have hgmod : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R)).comp g) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, hz⟩ := hmod' r
    refine ⟨algebraMap _ A z, ?_⟩
    change Ideal.Quotient.mk (maximalIdeal R) (g (algebraMap _ A z)) =
      Ideal.Quotient.mk (maximalIdeal R) r
    rw [hgz, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.pow_le_self (by simp) hz
  have hmap : Ideal.map g (maximalIdeal A) ≤ maximalIdeal R :=
    ((IsLocalRing.local_hom_TFAE g).out 1 3).mp hglocal
  have hφ : ∃ φ : P →+* R, φ.comp (algebraMap A P) = g := by
    have hle : ∀ n : ℕ, (maximalIdeal A) ^ n ≤
        ((maximalIdeal R) ^ n).comap g := fun n =>
      Ideal.map_le_iff_le_comap.mp (map_pow_le_pow_of_map_le g hmap n)
    let F := IsAdicComplete.liftRingHom (maximalIdeal R)
      (fun n => (Ideal.quotientMap _ g (hle n)).comp
        (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom)
      (fun {m n} hmn => by
        rw [← RingHom.comp_assoc, Ideal.Quotient.factorPow_comp_quotientMap g (maximalIdeal A)
          (maximalIdeal R) hmn (hle n) (hle m), RingHom.comp_assoc]
        congr 1
        ext x
        exact factorPow_evalₐ _ hmn x)
    refine ⟨F, ?_⟩
    ext x
    have hc : ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal R) hmn).comp
            ((Ideal.Quotient.mk ((maximalIdeal R) ^ n)).comp g) =
          (Ideal.Quotient.mk ((maximalIdeal R) ^ m)).comp g := by
      intro m n hmn
      ext y
      simp [Ideal.Quotient.factorPow]
    have h₁ := IsAdicComplete.eq_liftRingHom (maximalIdeal R)
      (fun n => (Ideal.Quotient.mk ((maximalIdeal R) ^ n)).comp g) hc
      (F.comp (algebraMap A P)) (by
        intro n
        ext y
        change Ideal.Quotient.mk ((maximalIdeal R) ^ n)
          (F (algebraMap A P y)) = Ideal.Quotient.mk ((maximalIdeal R) ^ n) (g y)
        dsimp only [F]
        rw [IsAdicComplete.mk_liftRingHom]
        change (Ideal.quotientMap ((maximalIdeal R) ^ n) g (hle n))
          (AdicCompletion.evalₐ (maximalIdeal A) n
            (AdicCompletion.of (maximalIdeal A) A y)) = _
        rw [AdicCompletion.evalₐ_of]
        simp)
    have h₂ := IsAdicComplete.eq_liftRingHom (maximalIdeal R)
      (fun n => (Ideal.Quotient.mk ((maximalIdeal R) ^ n)).comp g) hc g fun _ => rfl
    exact DFunLike.congr_fun (h₁.trans h₂.symm) x
  obtain ⟨φ, hφ⟩ := hφ
  have hφlocal : IsLocalHom φ := by
    apply ((IsLocalRing.local_hom_TFAE φ).out 4 1).mp
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap]
    change maximalIdeal A ≤ Ideal.comap (φ.comp (algebraMap A P)) (maximalIdeal R)
    rw [hφ]
    exact Ideal.map_le_iff_le_comap.mp hmap
  let : IsLocalHom φ := hφlocal
  have hmsub : (maximalIdeal R : Submodule R R) ≤
      (Ideal.map g (maximalIdeal A) : Submodule R R) ⊔
        (maximalIdeal R : Submodule R R) • (maximalIdeal R : Submodule R R) := by
    intro y hy
    obtain ⟨z, hdiff⟩ := hmod' y
    have hfz : f z ∈ maximalIdeal R := by
      simpa using (maximalIdeal R).add_mem (Ideal.pow_le_self (by simp) hdiff) hy
    have hzP : z ∈ p := by
      rw [← hp]
      exact hfz
    have hza : algebraMap (MvPolynomial (Fin s) Λ) A z ∈ maximalIdeal A := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A]
      exact Ideal.mem_map_of_mem _ hzP
    have hfzJ : f z ∈ Ideal.map g (maximalIdeal A) := by
      rw [← hgz z]
      exact Ideal.mem_map_of_mem g hza
    have hrest : y - f z ∈ (maximalIdeal R) ^ 2 := by
      rw [← neg_sub]
      exact (maximalIdeal R ^ 2).neg_mem hdiff
    have hySup : y ∈ Ideal.map g (maximalIdeal A) ⊔ (maximalIdeal R) ^ 2 := by
      simpa only [add_sub_cancel] using
        (Submodule.add_mem_sup hfzJ hrest :
          f z + (y - f z) ∈
            (Ideal.map g (maximalIdeal A) : Submodule R R) ⊔
              ((maximalIdeal R) ^ 2 : Submodule R R))
    simpa [Ideal.smul_eq_mul, pow_two] using hySup
  have hmap_ge : maximalIdeal R ≤ Ideal.map g (maximalIdeal A) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
      (maximalIdeal_le_jacobson (⊥ : Ideal R))
    simpa [Ideal.smul_eq_mul, pow_two] using hmsub
  have hmap_eq : Ideal.map g (maximalIdeal A) = maximalIdeal R :=
    le_antisymm hmap hmap_ge
  have hφmap : Ideal.map φ (maximalIdeal P) = maximalIdeal R := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hφ, hmap_eq]
  have hφ_surj : Function.Surjective φ := by
    have : IsHausdorff (Ideal.map φ (maximalIdeal P)) R := by
      rw [hφmap]
      infer_instance
    apply surjective_of_mk_map_comp_surjective (I := maximalIdeal P)
    rw [hφmap]
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hgmod (Ideal.Quotient.mk (maximalIdeal R) r)
    exact ⟨algebraMap A P x, (congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun hφ x)).trans hx⟩
  refine ⟨inferInstance, inferInstance, inferInstance, g, hg, hglocal, φ, hφ,
    hφ_surj, inferInstance, fun ψ hψ hψlocal => RingHom.ext fun x => ?_⟩
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
  intro n
  -- The local maps agree on the dense localization.  Compare them modulo every
  -- power by choosing a representative for the evaluation of `x`.
  have : IsScalarTower A P P := self_scalarTower (maximalIdeal A)
  have hmAfg : (maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing (maximalIdeal A)
  have hmapψ : Ideal.map ψ (maximalIdeal P) ≤ maximalIdeal R :=
    ((IsLocalRing.local_hom_TFAE ψ).out 1 3).mp hψlocal
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal A) n x)
  have heval : AdicCompletion.evalₐ (maximalIdeal A) n x =
      Ideal.Quotient.mk ((maximalIdeal A) ^ n) a := ha.symm
  have hdiff : x - algebraMap A P a ∈ (maximalIdeal P) ^ n := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    have hevalAlg : AdicCompletion.evalₐ (maximalIdeal A) n (algebraMap A P a) =
        Ideal.Quotient.mk ((maximalIdeal A) ^ n) a :=
      AdicCompletion.evalₐ_of (maximalIdeal A) n a
    have hevalEq : AdicCompletion.eval (maximalIdeal A) A n x =
        AdicCompletion.eval (maximalIdeal A) A n (algebraMap A P a) := by
      have hIeq :
          ((maximalIdeal A) ^ n : Ideal A) • (⊤ : Submodule A A) =
            (maximalIdeal A) ^ n := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact (Ideal.quotientEquivAlgOfEq A hIeq).injective (heval.trans hevalAlg.symm)
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hmAfg]
    exact LinearMap.mem_ker.mpr (by rw [map_sub, hevalEq, sub_self])
  have hdiff_map (u : P →+* R) (hu : Ideal.map u (maximalIdeal P) ≤ maximalIdeal R) :
      u (x - algebraMap A P a) ∈ (maximalIdeal R) ^ n := by
    exact map_pow_le_pow_of_map_le u hu n (Ideal.mem_map_of_mem u hdiff)
  have hsame : ψ (algebraMap A P a) = φ (algebraMap A P a) :=
    (RingHom.congr_fun hψ a).trans (RingHom.congr_fun hφ a).symm
  have hdiffEq : ψ x - φ x =
      ψ (x - algebraMap A P a) - φ (x - algebraMap A P a) := by
    simp [hsame]
  rw [SModEq.sub_mem]
  change ψ x - φ x ∈ (maximalIdeal R) ^ n • (⊤ : Submodule R R)
  rw [hdiffEq]
  simpa [Ideal.smul_eq_mul] using (maximalIdeal R ^ n).sub_mem
    (hdiff_map ψ hmapψ) (hdiff_map φ (le_of_eq hφmap))

end AdicCompletion

end
