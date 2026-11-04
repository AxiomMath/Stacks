module

public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthDimAdicCompletion
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Depth.Dimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending a depth–dimension alternative from the completion of a local ring

Let `B` be a Noetherian local ring with a dualizing complex, `J ⊆ 𝔪` an ideal, `N` a finite
`B`-module, and `B^∧`, `N^∧` the `J`-adic completions. Suppose that for every prime `𝔭''` of
`B^∧` outside `V(JB^∧)` with `V(𝔭'') ∩ V(JB^∧) ≠ {𝔪B^∧}` either `depth(N^∧_{𝔭''}) ≥ 1` or
`depth(N^∧_{𝔭''}) + dim(B^∧/𝔭'') > 1 + d`. Then the same alternative holds over `B`: for primes
`𝔭 ⊆ 𝔯` of `B` with `𝔭 ∉ V(J)`, `𝔯 ∈ V(J)` and `𝔯 ≠ 𝔪`, either `depth(N_𝔭) ≥ 1` or
`depth(N_𝔭) + dim(B/𝔭) > 1 + d`.

This is the step "(c) ⇒ (4)" of the proof of [Stacks, Tag 0EJF]. Choose the prime `𝔯''` of `B^∧`
above `𝔯` containing `JB^∧` and a minimal prime `𝔭''` of `𝔭B^∧` inside it. By going down along the
flat map `B → B^∧`, `𝔭''` lies over `𝔭`; it is outside `V(JB^∧)`, and `𝔯'' ≠ 𝔪B^∧` witnesses
`V(𝔭'') ∩ V(JB^∧) ≠ {𝔪B^∧}`. Minimality makes the fibre `B^∧_{𝔭''}/𝔭B^∧_{𝔭''}` Artinian, so
`depth(N^∧_{𝔭''}) = depth(N_𝔭)` by the depth formula along the flat local map `B_𝔭 → B^∧_{𝔭''}`;
and [Stacks, Tag 0EHW] gives `depth(N^∧_{𝔭''}) + dim(B^∧/𝔭'') = depth(N_𝔭) + dim(B/𝔭)`.

## Main results

* `Stacks.Algebraization.depth_or_depth_add_dim_of_adicCompletion` — the descent.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public noncomputable section

open IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {B : Type u} [CommRing B] [IsNoetherianRing B]

omit [IsNoetherianRing B] in
/-- **Going down for a minimal prime of an extended prime.** Along a flat map, a minimal prime
of the extension of a prime `𝔭` lies over `𝔭`. -/
theorem comap_eq_of_mem_minimalPrimes_map_of_flat {C : Type*} [CommRing C] [Algebra B C]
    [Module.Flat B C] (P : Ideal B) [P.IsPrime] {P'' : Ideal C}
    (hmin : P'' ∈ (P.map (algebraMap B C)).minimalPrimes) :
    P''.comap (algebraMap B C) = P := by
  have : Algebra.HasGoingDown B C := Algebra.HasGoingDown.of_flat
  have hprime : P''.IsPrime := hmin.1.1
  have hle := Ideal.map_le_iff_le_comap.mp hmin.1.2
  refine le_antisymm ?_ hle
  have : (P''.comap (algebraMap B C)).IsPrime := Ideal.comap_isPrime _ _
  have : P''.LiesOver (P''.comap (algebraMap B C)) := ⟨rfl⟩
  obtain ⟨P₁, hP₁le, hP₁prime, hP₁over⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := P) (q := P''.comap (algebraMap B C)) P'' hle
  have hmap : P.map (algebraMap B C) ≤ P₁ := Ideal.map_le_iff_le_comap.mpr hP₁over.over.le
  exact (Ideal.comap_mono (hmin.2 ⟨hP₁prime, hmap⟩ hP₁le)).trans_eq hP₁over.over.symm

/-- In a localization at a prime `𝔭''` minimal over an ideal `K`, the quotient by the extension
of `K` has Krull dimension zero. -/
theorem ringKrullDim_quotient_map_atPrime_of_mem_minimalPrimes {C : Type*} [CommRing C]
    (K : Ideal C) {P'' : Ideal C} [P''.IsPrime] (hmin : P'' ∈ K.minimalPrimes) :
    Ring.KrullDimLE 0 (Localization.AtPrime P'' ⧸
      K.map (algebraMap C (Localization.AtPrime P''))) := by
  rw [Ring.krullDimLE_zero_iff]
  intro Q hQ
  set Lc := Localization.AtPrime P''
  set π := Ideal.Quotient.mk (K.map (algebraMap C Lc))
  have hQ' : (Q.comap π).IsPrime := Ideal.comap_isPrime _ _
  have hKQ : K.map (algebraMap C Lc) ≤ Q.comap π := by
    intro a ha
    show π a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Q.zero_mem
  set Q₀ := (Q.comap π).comap (algebraMap C Lc)
  have hQ₀ : Q₀.IsPrime := Ideal.comap_isPrime _ _
  have hQ₀le : Q₀ ≤ P'' := by
    intro a ha
    by_contra hna
    exact hQ'.ne_top (Ideal.eq_top_of_isUnit_mem _ ha
      (IsLocalization.map_units Lc (⟨a, hna⟩ : P''.primeCompl)))
  have hKQ₀ : K ≤ Q₀ := Ideal.map_le_iff_le_comap.mp hKQ
  have hQ₀eq : Q₀ = P'' := le_antisymm hQ₀le (hmin.2 ⟨hQ₀, hKQ₀⟩ hQ₀le)
  have hmax : Q.comap π = maximalIdeal Lc := by
    rw [← IsLocalization.map_comap P''.primeCompl Lc (Q.comap π),
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact congrArg (Ideal.map (algebraMap C Lc)) hQ₀eq
  have hQeq : Q = (maximalIdeal Lc).map π := by
    rw [← hmax, Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective]
  rw [hQeq]
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (Ideal.mk_ker.trans_le (le_maximalIdeal fun htop => hQ'.ne_top (top_le_iff.mp (htop ▸ hKQ))))

/-- A finite module over a Noetherian local ring which is a quotient of the ring by an ideal
inside the maximal ideal, of Krull dimension zero, has depth zero. -/
@[ega "0 16.4.6" "(iii), special case"]
theorem depth_quotient_eq_zero_of_krullDimLE_zero {Lc : Type*} [CommRing Lc]
    [IsNoetherianRing Lc] [IsLocalRing Lc] (K : Ideal Lc) (hK : K ≤ maximalIdeal Lc)
    [Ring.KrullDimLE 0 (Lc ⧸ K)] :
    Module.depth Lc (maximalIdeal Lc) (Lc ⧸ K) = 0 := by
  have hnontriv : Nontrivial (Lc ⧸ K) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal Lc).ne_top hK
  have hdim : ringKrullDim (Lc ⧸ K) ≤ 0 := by
    exact_mod_cast (Ring.krullDimLE_iff (n := 0)).mp inferInstance
  have hnot : maximalIdeal Lc • (⊤ : Submodule Lc (Lc ⧸ K)) ≠ ⊤ := by
    intro heq
    have hmaxmap : (maximalIdeal Lc).map (Ideal.Quotient.mk K) ≠ ⊤ :=
      (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
        simpa using hK)).ne_top
    apply hmaxmap
    have hmaptop : Submodule.restrictScalars Lc
        ((maximalIdeal Lc).map (Ideal.Quotient.mk K)) = ⊤ := by
      simpa [Ideal.smul_top_eq_map] using heq
    simpa using hmaptop
  have hle := Module.depth_le_supportDim Lc (maximalIdeal Lc) (Lc ⧸ K) hnot
  rw [Module.supportDim_quotient_eq_ringKrullDim] at hle
  exact le_antisymm (by exact_mod_cast hle.trans hdim) zero_le

/-- **Descending the depth–dimension alternative from the completion of a local ring.** Let `B`
be a Noetherian local ring with a dualizing complex, `J ⊆ 𝔪` an ideal and `N` a finite
`B`-module. If at every prime `𝔭''` of `B^∧` outside `V(JB^∧)` with
`V(𝔭'') ∩ V(JB^∧) ≠ {𝔪B^∧}` either `depth(N^∧_{𝔭''}) ≥ 1` or
`depth(N^∧_{𝔭''}) + dim(B^∧/𝔭'') > 1 + d`, then for primes `𝔭 ⊆ 𝔯` of `B` with `𝔭 ∉ V(J)`,
`𝔯 ∈ V(J)`, `𝔯 ≠ 𝔪` either `depth(N_𝔭) ≥ 1` or `depth(N_𝔭) + dim(B/𝔭) > 1 + d`. -/
theorem depth_or_depth_add_dim_of_adicCompletion [IsLocalRing B]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} B), Dualizing.IsDualizingComplex K)
    (J : Ideal B) (hJ : J ≤ maximalIdeal B) (N : Type u) [AddCommGroup N] [Module B N]
    [Module.Finite B N] (d : ℤ)
    (hc : ∀ P'' : PrimeSpectrum (AdicCompletion J B),
      ¬ J.map (algebraMap B (AdicCompletion J B)) ≤ P''.asIdeal →
      {r : Ideal (AdicCompletion J B) | r.IsPrime ∧ P''.asIdeal ≤ r ∧
          J.map (algebraMap B (AdicCompletion J B)) ≤ r} ≠
        {(maximalIdeal B).map (algebraMap B (AdicCompletion J B))} →
      1 ≤ Module.depth (Localization.AtPrime P''.asIdeal)
          (maximalIdeal (Localization.AtPrime P''.asIdeal))
          (LocalizedModule P''.asIdeal.primeCompl (AdicCompletion J N)) ∨
        enatToEInt (Module.depth (Localization.AtPrime P''.asIdeal)
            (maximalIdeal (Localization.AtPrime P''.asIdeal))
            (LocalizedModule P''.asIdeal.primeCompl (AdicCompletion J N))) +
          krullDimToEInt (ringKrullDim (AdicCompletion J B ⧸ P''.asIdeal)) >
          ((1 + d : ℤ) : EInt))
    (P R : Ideal B) [P.IsPrime] [R.IsPrime] (hPR : P ≤ R) (hP : ¬ J ≤ P) (hR : J ≤ R)
    (hRm : R ≠ maximalIdeal B) :
    1 ≤ Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl N) ∨
      enatToEInt (Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
          (LocalizedModule P.primeCompl N)) +
        krullDimToEInt (ringKrullDim (B ⧸ P)) > ((1 + d : ℤ) : EInt) := by
  have : Module.Flat B (AdicCompletion J B) := AdicCompletion.flat_of_isNoetherian J
  set R'' := adicPrimeOver J hR with hR''
  have hPR'' : P.map (algebraMap B (AdicCompletion J B)) ≤ R''.asIdeal := by
    rwa [Ideal.map_le_iff_le_comap, comap_adicPrimeOver]
  obtain ⟨P'', hmin, hle⟩ := Ideal.exists_minimalPrimes_le hPR''
  have hprime : P''.IsPrime := hmin.1.1
  have hover : P''.comap (algebraMap B (AdicCompletion J B)) = P :=
    comap_eq_of_mem_minimalPrimes_map_of_flat P hmin
  have : P''.LiesOver P := ⟨hover.symm⟩
  have hI : ¬ J.map (algebraMap B (AdicCompletion J B)) ≤ P'' := fun h =>
    hP (by rw [← hover]; exact Ideal.map_le_iff_le_comap.mp h)
  have hfib : {r : Ideal (AdicCompletion J B) | r.IsPrime ∧ P'' ≤ r ∧
      J.map (algebraMap B (AdicCompletion J B)) ≤ r} ≠
        {(maximalIdeal B).map (algebraMap B (AdicCompletion J B))} := by
    intro heq
    have hmem := (Set.ext_iff.mp heq R''.asIdeal).mp
      ⟨R''.isPrime, hle, map_le_adicPrimeOver J hR⟩
    rw [Set.mem_singleton_iff] at hmem
    refine hRm (le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_)
    rw [← comap_adicPrimeOver J hR, hmem]
    exact Ideal.map_le_iff_le_comap.mp le_rfl
  have h := hc ⟨P'', hprime⟩ hI hfib
  have hdepth_eq : Module.depth (Localization.AtPrime P'')
      (maximalIdeal (Localization.AtPrime P''))
      (LocalizedModule P''.primeCompl (AdicCompletion J N)) =
      Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl N) := by
    rw [AlgebraicGeometry.depth_localized_adicCompletion J P P'']
    have hK : P.map (algebraMap B (Localization.AtPrime P'')) ≤
        maximalIdeal (Localization.AtPrime P'') := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq B
        (AdicCompletion J B) (Localization.AtPrime P''), ← Ideal.map_map]
      exact Ideal.map_mono hmin.1.2
    have hmapeq : (P.map (algebraMap B (AdicCompletion J B))).map
        (algebraMap (AdicCompletion J B) (Localization.AtPrime P'')) =
        P.map (algebraMap B (Localization.AtPrime P'')) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have hdim : Ring.KrullDimLE 0 (Localization.AtPrime P'' ⧸
        P.map (algebraMap B (Localization.AtPrime P''))) := by
      rw [← hmapeq]
      exact ringKrullDim_quotient_map_atPrime_of_mem_minimalPrimes _ hmin
    rw [depth_quotient_eq_zero_of_krullDimLE_zero _ hK, add_zero]
  have hsum := Module.depth_add_ringKrullDim_quotient_adicCompletion B hdual J hJ N P P''
  by_cases hone : 1 ≤ Module.depth (Localization.AtPrime P)
      (maximalIdeal (Localization.AtPrime P)) (LocalizedModule P.primeCompl N)
  · exact Or.inl hone
  · right
    have hzero : Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl N) = 0 := by
      rwa [not_le, ENat.lt_one_iff_eq_zero] at hone
    rw [hdepth_eq, hzero] at h hsum
    rcases h with h1 | h2
    · exact absurd h1 (by simp)
    · have hdimeq : ringKrullDim (AdicCompletion J B ⧸ P'') = ringKrullDim (B ⧸ P) := by
        simpa using hsum
      rwa [hzero, ← hdimeq]

/-! ### Away from `V(J)`, a quotient by a `J`-power torsion submodule changes nothing -/

omit [IsNoetherianRing B] in
/-- An element of the extension of `Jᵉ` to the completion kills the completion of a module
killed by `Jᵉ`. -/
theorem smul_eq_zero_adicCompletion_of_forall_smul_eq_zero (J : Ideal B) {K : Type u}
    [AddCommGroup K] [Module B K] (e : ℕ) (hK : ∀ a ∈ J ^ e, ∀ y : K, a • y = 0)
    {t : AdicCompletion J B} (ht : t ∈ (J ^ e).map (algebraMap B (AdicCompletion J B)))
    (y : AdicCompletion J K) : t • y = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, rfl⟩ := ht
    refine AdicCompletion.ext fun n => ?_
    rw [AdicCompletion.smul_eval, AdicCompletion.val_zero]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
    rw [← hz]
    show (algebraMap B (AdicCompletion J B) a).val n • Submodule.Quotient.mk z = 0
    rw [show (algebraMap B (AdicCompletion J B) a).val n • (Submodule.Quotient.mk z :
        K ⧸ (J ^ n • ⊤ : Submodule B K)) = Submodule.Quotient.mk (a • z) from rfl, hK a ha z,
      Submodule.Quotient.mk_zero]
  | zero => exact zero_smul _ y
  | add t₁ t₂ _ _ h₁ h₂ => rw [add_smul, h₁, h₂, add_zero]
  | smul r t _ h => rw [smul_eq_mul, mul_smul, h, smul_zero]

/-- **Away from `V(J)` the completion does not see a `J`-power torsion kernel.** If
`f : N → N'` is a surjection of finite modules over a Noetherian ring whose kernel is killed by
`Jᵉ`, then at a prime `𝔭''` of the `J`-adic completion not containing `JB^∧` the localizations of
`N^∧` and `N'^∧` have the same depth. -/
theorem depth_localized_adicCompletion_eq_of_surjective (J : Ideal B) {N N' : Type u}
    [AddCommGroup N] [Module B N] [Module.Finite B N] [AddCommGroup N'] [Module B N']
    [Module.Finite B N'] (f : N →ₗ[B] N') (hf : Function.Surjective f) (e : ℕ)
    (he : ∀ a ∈ J ^ e, ∀ x ∈ LinearMap.ker f, a • x = 0)
    (P'' : Ideal (AdicCompletion J B)) [P''.IsPrime]
    (hP : ¬ J.map (algebraMap B (AdicCompletion J B)) ≤ P'') :
    Module.depth (Localization.AtPrime P'') (maximalIdeal (Localization.AtPrime P''))
        (LocalizedModule P''.primeCompl (AdicCompletion J N)) =
      Module.depth (Localization.AtPrime P'') (maximalIdeal (Localization.AtPrime P''))
        (LocalizedModule P''.primeCompl (AdicCompletion J N')) := by
  set g := AdicCompletion.map J f
  set ι := AdicCompletion.map J (LinearMap.ker f).subtype
  have hexact : Function.Exact ι g :=
    AdicCompletion.map_exact (I := J) (Submodule.injective_subtype _)
      (LinearMap.exact_iff.mpr (by rw [Submodule.range_subtype])) hf
  have hgs : Function.Surjective g := AdicCompletion.map_surjective J hf
  obtain ⟨t, htJ, htP⟩ : ∃ t ∈ (J ^ e).map (algebraMap B (AdicCompletion J B)), t ∉ P'' := by
    by_contra hcon
    push Not at hcon
    apply hP
    have hpow : (J.map (algebraMap B (AdicCompletion J B))) ^ e ≤ P'' := by
      rwa [← Ideal.map_pow]
    exact Ideal.IsPrime.le_of_pow_le hpow
  have hkill : ∀ x : AdicCompletion J N, g x = 0 → t • x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hexact x).mp hx
    rw [← LinearMap.map_smul, smul_eq_zero_adicCompletion_of_forall_smul_eq_zero J e
      (fun a ha z => Subtype.ext (he a ha z.1 z.2)) htJ y, map_zero]
  let gl := LocalizedModule.map P''.primeCompl g
  have hinj : Function.Injective gl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    induction w using LocalizedModule.induction_on with
    | h m s =>
      rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hw
      obtain ⟨u, hu⟩ := hw
      have h1 : g (((u : AdicCompletion J B) * s) • m) = 0 := by
        rw [LinearMap.map_smul]
        simpa [Submonoid.smul_def, mul_smul] using hu
      have h2 : (t * ((u : AdicCompletion J B) * s)) • m = 0 := by
        rw [mul_smul]; exact hkill _ h1
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨t * u, P''.primeCompl.mul_mem htP u.2⟩, ?_⟩
      simp only [Submonoid.smul_def, smul_zero]
      rwa [← mul_smul, show (t * (u : AdicCompletion J B)) * s =
        t * ((u : AdicCompletion J B) * s) by ring]
  have hsurj : Function.Surjective gl := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h m' s =>
      obtain ⟨m, rfl⟩ := hgs m'
      exact ⟨LocalizedModule.mk m s, by rw [LocalizedModule.map_mk]⟩
  exact Module.depth_eq_depth_of_linearEquiv _ (LinearEquiv.ofBijective gl ⟨hinj, hsurj⟩)

end Stacks.Algebraization

end
