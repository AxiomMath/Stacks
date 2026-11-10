module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitCone
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapPerPrime
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHomVanishing
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniverse
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.LocalCohomology.LocalDualityTransfer.Uniform

/-!
# Uniformity over the primes of `T` in Stacks 0EFX

Let `S` be a bootstrap situation ([Stacks, Tag 0EFU]). The per-prime assertions of
[Stacks, Tag 0EFX] (`Stacks.Algebraization.exists_perPrime_map_idealPowerTower_eq_zero`,
`Stacks.Algebraization.exists_perPrime_degree_succ`) give, at each prime `𝔮 ∈ T`, an integer
`m'(m, 𝔮)` beyond which the maps of `{H^i_𝔮((IⁿM)_𝔮)}` behave. The source makes `m'(m, 𝔮)`
independent of `𝔮` through local duality: the maps `H^i_𝔮((IᵏM)_𝔮) → H^i_𝔮((IᵐM)_𝔮)` are, after
the faithfully flat completion of `A_𝔮` and Matlis duality, the maps
`Extʲ_A(IᵐM, ω) → Extʲ_A(IᵏM, ω)`, which are maps out of one finite module; their kernels
increase in `k`, so stabilize, and every property of the base-changed map depends only on its
kernel (`StacksFrontier/RingTheory/LocalCohomology/LocalDualityTransfer/Uniform.lean`). Only
finitely
many `j` are relevant, because `Extʲ_A(-, ω)` vanishes on modules outside a fixed window.

This file carries that argument out and feeds the globalization lemmas
`Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_local` and
`Stacks.LocalCohomology.exists_eventually_injective_image_idealPowerTower_of_local`, obtaining
both assertions of [Stacks, Tag 0EFX] for every bootstrap situation, in exactly the shapes that
`Stacks.LocalCohomology.Bootstrap.exists_isEssentiallyConstantWith_of_proZero` consumes.

Three inputs are taken as explicit hypotheses of the statements here, each a lemma proved
elsewhere: the cone form of [Stacks, Tag 0EFR] for complete local situations
(`Stacks.Algebraization.CompleteLocalConeHypothesis`), the per-prime local duality transfer
(`Stacks.Algebraization.PerPrimeDualityTransfer`) and the vanishing window of `Extʲ_A(-, ω)`
(`Stacks.Algebraization.ExtWindow`).

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

/-- The functor `N ↦ H^i_{𝔮A_𝔮}(N_𝔮)`. -/
abbrev perPrimeLocalCohomology (q : PrimeSpectrum A) (i : ℤ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} (Localization.AtPrime q.asIdeal) :=
  ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl ⋙
    localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) i

/-- The contravariant functor `N ↦ Extʲ_A(N, ω)`. -/
abbrev extIntoDualizing (ω : DerivedCategory (ModuleCat.{u} A)) (j : ℤ) :
    (ModuleCat.{u} A)ᵒᵖ ⥤ ModuleCat.{u} A :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
    Dualizing.dualizingDerivedHomFunctor.{u, u} A ω ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) j

/-- **The per-prime local duality transfer** ([Stacks, Tag 0AAK], read on maps). At a prime `𝔮`
and in degree `i` there are a degree `j` and a flat `A`-algebra `S` (the completion of `A_𝔮`)
such that, for maps of finite `A`-modules, vanishing, equality of images and injectivity of
images into a further term for `N ↦ H^i_{𝔮A_𝔮}(N_𝔮)` are equivalent to vanishing, equality of
kernels and equality of images for `N ↦ S ⊗_A Extʲ_A(N, ω)`. -/
def PerPrimeDualityTransfer (ω : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∀ (q : PrimeSpectrum A) (i : ℤ), ∃ (j : ℤ) (S : Type u) (_ : CommRing S) (_ : Algebra A S)
    (_ : Module.Flat A S),
    (∀ (N₀ N₁ : ModuleCat.{u} A) [Module.Finite A N₀] [Module.Finite A N₁] (g : N₀ ⟶ N₁),
      (perPrimeLocalCohomology A q i).map g = 0 ↔
        ((extIntoDualizing A ω j).map g.op).hom.lTensor S = 0) ∧
    (∀ (N₀ N₁ N₂ : ModuleCat.{u} A) [Module.Finite A N₀] [Module.Finite A N₁]
      [Module.Finite A N₂] (a : N₀ ⟶ N₁) (b : N₁ ⟶ N₂),
      LinearMap.range ((perPrimeLocalCohomology A q i).map (a ≫ b)).hom =
          LinearMap.range ((perPrimeLocalCohomology A q i).map b).hom ↔
        LinearMap.ker (((extIntoDualizing A ω j).map (a ≫ b).op).hom.lTensor S) =
          LinearMap.ker (((extIntoDualizing A ω j).map b.op).hom.lTensor S)) ∧
    (∀ (N₀ N₁ N₂ : ModuleCat.{u} A) [Module.Finite A N₀] [Module.Finite A N₁]
      [Module.Finite A N₂] (t : N₀ ⟶ N₁) (w : N₁ ⟶ N₂),
      (∀ x, ((perPrimeLocalCohomology A q i).map t).hom x ∈
          LinearMap.ker ((perPrimeLocalCohomology A q i).map w).hom →
        ((perPrimeLocalCohomology A q i).map t).hom x = 0) ↔
        LinearMap.range (((extIntoDualizing A ω j).map (t ≫ w).op).hom.lTensor S) =
          LinearMap.range (((extIntoDualizing A ω j).map t.op).hom.lTensor S))

/-- **The vanishing window of `Extʲ_A(-, ω)`.** There are bounds outside which `Extʲ_A(N, ω)`
vanishes for every module `N`. -/
def ExtWindow (ω : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∃ a b : ℤ, ∀ (N : ModuleCat.{u} A) (j : ℤ), (j < a ∨ b < j) →
    IsZero ((extIntoDualizing A ω j).obj (op N))

/-! ### Finiteness -/

omit [IsNoetherianRing A] in
/-- A finite module placed in degree `0` has finite cohomology in every degree. -/
theorem finite_homology_singleFunctor_of_finite (N : ModuleCat.{u} A) [Module.Finite A N]
    (j : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) := by
  set K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N with hK
  by_cases hj : j = 0
  · subst hj
    have : Module.Finite A ((𝟭 (ModuleCat.{u} A)).obj N) := ‹Module.Finite A N›
    exact Module.Finite.equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
        N).toLinearEquiv.symm
  · have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K) := by
      have : K.IsGE 0 := by
        rw [hK]
        infer_instance
      have : K.IsLE 0 := by
        rw [hK]
        infer_instance
      exact if hj' : j < 0 then DerivedCategory.isZero_of_isGE K 0 j hj'
        else DerivedCategory.isZero_of_isLE K 0 j (by omega)
    have := ModuleCat.isZero_iff_subsingleton.mp hzero
    exact Module.Finite.of_surjective
      (0 : A →ₗ[A] ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))
      fun x => ⟨0, Subsingleton.elim _ _⟩

/-- `Extʲ_A(N, ω)` is a finite module for a finite module `N` and a dualizing complex `ω`. -/
theorem finite_extIntoDualizing (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsDualizingComplex ω) (N : ModuleCat.{u} A) [Module.Finite A N] (j : ℤ) :
    Module.Finite A ((extIntoDualizing A ω j).obj (op N)) :=
  Dualizing.dualizingDerivedHom_finiteCohomology.{u, u} A ω hω _
    (finite_homology_singleFunctor_of_finite A N) j

/-! ### Uniform stabilization of the kernels -/

/-- A functor out of `ℕᵒᵖ` sends the composite `m ≤ k ≤ k'` to the composite of the images. -/
private theorem map_homOfLE_op_trans {C : Type*} [Category C] (T : ℕᵒᵖ ⥤ C) {m k k' : ℕ}
    (hmk : m ≤ k) (hkk' : k ≤ k') :
    T.map (homOfLE (hmk.trans hkk')).op = T.map (homOfLE hkk').op ≫ T.map (homOfLE hmk).op := by
  rw [← Functor.map_comp]
  exact congrArg T.map (Subsingleton.elim _ _)

/-- Every ideal power of a finite module over a Noetherian ring is finite. -/
private theorem finite_idealPowerTower_obj (I : Ideal A) (N : ModuleCat.{u} A)
    [Module.Finite A N] (k : ℕ) : Module.Finite A ((idealPowerTower.{u, u} I N).obj (op k)) :=
  Module.IsNoetherian.finite A ↥(I ^ k • (⊤ : Submodule A N))

/-- **The kernels of `Extʲ_A(IᵐN, ω) → Extʲ_A(IᵏN, ω)` stabilize uniformly in `j`.** For a
finite module `N`, a dualizing complex `ω` with a vanishing window and every `m`, there is
`c ≥ m` such that for all `j` and all `k ≥ c` the kernel of `Extʲ_A(IᵐN, ω) → Extʲ_A(IᵏN, ω)`
is the kernel of `Extʲ_A(IᵐN, ω) → Extʲ_A(I^cN, ω)`. -/
theorem exists_uniform_ker_stable (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsDualizingComplex ω) (hwin : ExtWindow A ω) (I : Ideal A)
    (N : ModuleCat.{u} A) [Module.Finite A N] (m : ℕ) :
    ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (j : ℤ) (k : ℕ) (hck : c ≤ k),
      LinearMap.ker ((extIntoDualizing A ω j).map
          ((idealPowerTower.{u, u} I N).map (homOfLE (hmc.trans hck)).op).op).hom =
        LinearMap.ker ((extIntoDualizing A ω j).map
          ((idealPowerTower.{u, u} I N).map (homOfLE hmc).op).op).hom := by
  obtain ⟨a, b, hab⟩ := hwin
  let P : ℤ → ModuleCat.{u} A := fun j =>
    (extIntoDualizing A ω j).obj (op ((idealPowerTower.{u, u} I N).obj (op m)))
  have hP : ∀ j, IsNoetherian A (P j) := fun j =>
    have := finite_idealPowerTower_obj A I N m
    have := finite_extIntoDualizing A ω hω ((idealPowerTower.{u, u} I N).obj (op m)) j
    isNoetherian_of_isNoetherianRing_of_finite A (P j)
  let Kf : ∀ j : ℤ, ℕ → Submodule A (P j) := fun j k =>
    if h : m ≤ k then LinearMap.ker ((extIntoDualizing A ω j).map
      ((idealPowerTower.{u, u} I N).map (homOfLE h).op).op).hom else ⊥
  have hKf : ∀ j k (h : m ≤ k), Kf j k = LinearMap.ker ((extIntoDualizing A ω j).map
      ((idealPowerTower.{u, u} I N).map (homOfLE h).op).op).hom := fun j k h => dite_eq_left h
  have hmono : ∀ j, Monotone (Kf j) := by
    intro j k k' hkk'
    by_cases hk : m ≤ k
    · rw [hKf j k hk, hKf j k' (hk.trans hkk')]
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [map_homOfLE_op_trans _ hk hkk', op_comp, Functor.map_comp, ModuleCat.hom_comp,
        LinearMap.comp_apply, hx, map_zero]
    · simp only [Kf, dite_eq_right hk, bot_le]
  have hstab : ∀ j, ∃ n, ∀ k, n ≤ k → Kf j n = Kf j k := fun j =>
    have := hP j
    (monotone_stabilizes_iff_noetherian.mpr inferInstance) ⟨Kf j, hmono j⟩
  choose n hn using hstab
  let c := max m ((Finset.Icc a b).sup fun j => n j)
  have hmc : m ≤ c := le_max_left _ _
  refine ⟨c, hmc, fun j k hck => ?_⟩
  by_cases hj : j ∈ Finset.Icc a b
  · have hnj : n j ≤ c :=
      (Finset.le_sup (f := fun j => n j) hj).trans (le_max_right _ _)
    rw [← hKf j k (hmc.trans hck), ← hKf j c hmc, ← hn j k (hnj.trans hck), hn j c hnj]
  · have hz : IsZero (P j) :=
      hab _ j (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hj)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _

/-! ### Transfer of vanishing along an inclusion of kernels -/

omit [IsNoetherianRing A] in
/-- After a flat base change, a map whose kernel contains the kernel of a map vanishing after the
base change vanishes too. -/
theorem lTensor_eq_zero_of_ker_le (R : Type u) [AddCommGroup R] [Module A R] [Module.Flat A R]
    {P Q Q' : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [AddCommGroup Q'] [Module A Q'] (φ : P →ₗ[A] Q) (φ' : P →ₗ[A] Q')
    (h : LinearMap.ker φ' ≤ LinearMap.ker φ) (h0 : φ'.lTensor R = 0) : φ.lTensor R = 0 := by
  rw [LinearMap.lTensor_eq_zero_iff_subsingleton_quotient_ker] at h0 ⊢
  exact (LinearMap.lTensor_surjective R (Submodule.factor_surjective h)).subsingleton

/-! ### The ideal-power tower, contravariantly -/

section Tower

variable {A} (ω : DerivedCategory (ModuleCat.{u} A)) (I : Ideal A) (N : ModuleCat.{u} A)

omit [IsNoetherianRing A] in
/-- For `m ≤ k ≤ k'`, the map `Extʲ_A(IᵐN, ω) → Extʲ_A(Iᵏ'N, ω)` is the composite of
`Extʲ_A(IᵐN, ω) → Extʲ_A(IᵏN, ω)` and `Extʲ_A(IᵏN, ω) → Extʲ_A(Iᵏ'N, ω)`. -/
theorem extIntoDualizing_map_tower_comp (j : ℤ) {k k' m : ℕ} (hkk' : k ≤ k') (hmk : m ≤ k) :
    ((extIntoDualizing A ω j).map
        ((idealPowerTower.{u, u} I N).map (homOfLE (hmk.trans hkk')).op).op).hom =
      ((extIntoDualizing A ω j).map
          ((idealPowerTower.{u, u} I N).map (homOfLE hkk').op).op).hom ∘ₗ
        ((extIntoDualizing A ω j).map
          ((idealPowerTower.{u, u} I N).map (homOfLE hmk).op).op).hom := by
  rw [map_homOfLE_op_trans _ hmk hkk', op_comp, Functor.map_comp, ModuleCat.hom_comp]

omit [IsNoetherianRing A] in
/-- The kernels of `Extʲ_A(IᵐN, ω) → Extʲ_A(IᵏN, ω)` increase with `k`. -/
theorem ker_extIntoDualizing_tower_mono (j : ℤ) {k k' m : ℕ} (hkk' : k ≤ k') (hmk : m ≤ k) :
    LinearMap.ker ((extIntoDualizing A ω j).map
        ((idealPowerTower.{u, u} I N).map (homOfLE hmk).op).op).hom ≤
      LinearMap.ker ((extIntoDualizing A ω j).map
        ((idealPowerTower.{u, u} I N).map (homOfLE (hmk.trans hkk')).op).op).hom := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [extIntoDualizing_map_tower_comp ω I N j hkk' hmk, LinearMap.comp_apply, hx, map_zero]

end Tower

/-! ### The two assertions of Stacks 0EFX for one bootstrap situation -/

section Situation

variable (S : BootstrapSituation.{u, u, w}) (hcomplete : CompleteLocalConeHypothesis.{u})
  (ω : DerivedCategory (ModuleCat.{u} S.A)) (hω : Dualizing.IsDualizingComplex ω)
  (hR2 : PerPrimeDualityTransfer S.A ω) (hwin : ExtWindow S.A ω)

include hcomplete hR2 in
/-- **The per-prime vanishing, uniformly in the prime.** If `c ≥ m` stabilizes the kernels of
`Extʲ_A(IᵐM, ω) → Extʲ_A(IᵏM, ω)` for all `j`, then for `i ≤ s`, every `𝔮 ∈ T` and every
`k ≥ c` the map `H^i_𝔮((IᵏM)_𝔮) → H^i_𝔮((IᵐM)_𝔮)` vanishes. -/
theorem perPrime_map_eq_zero_of_ker_stable (i : ℤ) (hi : i ≤ S.s) {m c : ℕ} (hmc : m ≤ c)
    (hc : ∀ (j : ℤ) (k : ℕ) (hck : c ≤ k),
      LinearMap.ker ((extIntoDualizing S.A ω j).map
          ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map
            (homOfLE (hmc.trans hck)).op).op).hom =
        LinearMap.ker ((extIntoDualizing S.A ω j).map
          ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE hmc).op).op).hom)
    (p : PrimeSpectrum S.A) (hp : p ∈ S.T) (k : ℕ) (hck : c ≤ k) :
    (perPrimeLocalCohomology S.A p i).map
      ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map
        (homOfLE (hmc.trans hck)).op) = 0 := by
  have hfin := finite_idealPowerTower_obj S.A S.I (ModuleCat.of S.A S.M)
  obtain ⟨j, R, _, _, _, hZ, -, -⟩ := hR2 p i
  obtain ⟨kp, hmkp, hkp⟩ := exists_perPrime_map_idealPowerTower_eq_zero hcomplete hp i hi m
  change (perPrimeLocalCohomology S.A p i).map _ = 0 at hkp
  rw [hZ] at hkp ⊢
  refine lTensor_eq_zero_of_ker_le S.A R _ _ ?_ hkp
  by_cases hk : kp ≤ k
  · exact ker_extIntoDualizing_tower_mono ω S.I _ j hk hmkp
  · rw [hc j kp (hck.trans (not_le.mp hk).le), hc j k hck]

include hcomplete hω hR2 hwin in
/-- **Stacks 0EFX, the pro-zero assertion**, for one bootstrap situation: for `i ≤ s` the system
`{H^i_T(IⁿM)}` is pro-zero. -/
theorem exists_map_idealPowerTower_eq_zero_of_perPrimeDualityTransfer (i : ℤ) (hi : i ≤ S.s)
    (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T i).map
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE h).op) = 0 := by
  rcases lt_or_ge i 0 with hneg | hnn
  · exact exists_map_idealPowerTower_eq_zero_of_neg.{u, u} S.T S.I _ i hneg m
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
  choose c hmc hc using fun m =>
    exists_uniform_ker_stable S.A ω hω hwin S.I (ModuleCat.of S.A S.M) m
  exact exists_map_idealPowerTower_eq_zero_of_local.{u, u} S.ringKrullDim_lt_top S.T
    S.stableUnderSpecialization S.I (ModuleCat.of S.A S.M) n c hmc
    (fun m k hbound p hp => perPrime_map_eq_zero_of_ker_stable S hcomplete ω hR2 (n : ℤ) hi
      (hmc m) (hc m) p hp k hbound) m

include hcomplete hω hR2 hwin in
/-- **Stacks 0EFX, the stable-image assertion**, for one bootstrap situation: there is `m₀` such
that for every `m ≥ m₀` the image of `H^{s+1}_T(IᵏM) → H^{s+1}_T(IᵐM)` injects into
`H^{s+1}_T(I^{m₀}M)` for all large `k`. -/
theorem exists_eventually_injective_of_perPrimeDualityTransfer :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T (S.s + 1)).obj (op k),
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T (S.s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
            localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T (S.s + 1)).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T (S.s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0 := by
  rcases lt_or_ge (S.s + 1) 0 with hneg | hnn
  · refine ⟨0, fun m _ => ⟨m, le_rfl, fun k hck x _ => ?_⟩⟩
    have hz : IsZero ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
        localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T (S.s + 1)).obj (op m)) :=
      isZero_localCohomologyWithSupportIn_single_of_neg.{u, u} S.A S.T
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).obj (op m)) _ hneg
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = S.s + 1 := ⟨(S.s + 1).toNat, Int.toNat_of_nonneg hnn⟩
  have hfin := finite_idealPowerTower_obj S.A S.I (ModuleCat.of S.A S.M)
  let T := idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)
  rw [← hn]
  refine exists_eventually_injective_image_idealPowerTower_of_local.{u, u} S.ringKrullDim_lt_top
    S.T S.stableUnderSpecialization S.I (ModuleCat.of S.A S.M) n fun m => ?_
  obtain ⟨c, hmc, hc⟩ := exists_uniform_ker_stable S.A ω hω hwin S.I (ModuleCat.of S.A S.M) m
  refine ⟨c, hmc, fun p hp k hck => ⟨?_, ?_, ?_⟩⟩
  · exact perPrime_map_eq_zero_of_ker_stable S hcomplete ω hR2 ((n : ℤ) - 1) (by omega) hmc hc
      p hp k hck
  · obtain ⟨j, R, _, _, _, -, hI, -⟩ := hR2 p n
    have hab := (map_homOfLE_op_trans T hmc hck).symm
    have h := (hI _ _ _ (T.map (homOfLE hck).op) (T.map (homOfLE hmc).op)).2 (by
      rw [hab]
      exact LinearMap.ker_lTensor_eq_of_ker_eq R _ _ (hc j k hck))
    rwa [hab] at h
  · obtain ⟨j, R, _, _, _, -, -, hK⟩ := hR2 p n
    obtain ⟨cp, hmcp, hcp⟩ := exists_perPrime_degree_succ hcomplete hp m
    let k' := max k cp
    have hk' := (hcp k' (le_max_right _ _)).2.2
    rw [← hn] at hk'
    have h' := (hK _ _ _ (T.map (homOfLE (hmcp.trans (le_max_right k cp))).op)
      (T.map (homOfLE (Nat.zero_le m)).op)).1 hk'
    refine (hK _ _ _ (T.map (homOfLE (hmc.trans hck)).op)
      (T.map (homOfLE (Nat.zero_le m)).op)).2 ?_
    rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.range_lTensor_comp_eq_iff]
      at h' ⊢
    have hker : LinearMap.ker ((extIntoDualizing S.A ω j).map
          (T.map (homOfLE (hmc.trans hck)).op).op).hom =
        LinearMap.ker ((extIntoDualizing S.A ω j).map
          (T.map (homOfLE (hmcp.trans (le_max_right k cp))).op).op).hom := by
      rw [hc j k hck, ← hc j k' (hck.trans (le_max_left _ _))]
    rwa [hker]

end Situation

/-! ### Both assertions of Stacks 0EFX for every bootstrap situation -/

/-- The cone form of [Stacks, Tag 0EFR] for complete local situations,
`Stacks.Algebraization.nonempty_isLimit_cone_of_isAdicComplete`. -/
theorem completeLocalConeHypothesis : CompleteLocalConeHypothesis.{u} :=
  fun S' _ _ hT i hi => nonempty_isLimit_cone_of_isAdicComplete S' hT i hi

/-- The vanishing window of `Extʲ_A(-, ω)`,
`Dualizing.exists_isZero_homology_dualizingDerivedHom_of_lt_or_gt`. -/
theorem extWindow (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) :
    ExtWindow A ω :=
  Dualizing.exists_isZero_homology_dualizingDerivedHom_of_lt_or_gt ω hω

/-- **Stacks 0EFX for every bootstrap situation, from the per-prime duality transfer.** Both
assertions, in the shapes `hXa` and `hXb` of
`Stacks.LocalCohomology.Bootstrap.exists_isEssentiallyConstantWith_of_proZero`. The one input is
the per-prime local duality transfer `hR2` (Stacks 0AAK read on maps). -/
theorem proZero_and_eventually_injective_of_perPrimeDualityTransfer
    (hR2 : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (ω : DerivedCategory (ModuleCat.{u} B)),
      Dualizing.IsDualizingComplex ω → PerPrimeDualityTransfer B ω) :
    (∀ S' : BootstrapSituation.{u, u, w}, ∀ i : ℤ, i ≤ S'.s → ∀ m : ℕ, ∃ k : ℕ, ∃ h : m ≤ k,
        (localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T i).map
          ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M)).map (homOfLE h).op) = 0) ∧
    (∀ S' : BootstrapSituation.{u, u, w}, ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m),
      ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).obj (op k),
        ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
            localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0) := by
  refine ⟨fun S' i hi m => ?_, fun S' => ?_⟩
  · obtain ⟨ω, hω⟩ := S'.exists_isDualizingComplex
    exact exists_map_idealPowerTower_eq_zero_of_perPrimeDualityTransfer S'
      completeLocalConeHypothesis ω hω (hR2 _ ω hω) (extWindow _ ω hω) i hi m
  · obtain ⟨ω, hω⟩ := S'.exists_isDualizingComplex
    exact exists_eventually_injective_of_perPrimeDualityTransfer S'
      completeLocalConeHypothesis ω hω (hR2 _ ω hω) (extWindow _ ω hω)

end Stacks.Algebraization

end
