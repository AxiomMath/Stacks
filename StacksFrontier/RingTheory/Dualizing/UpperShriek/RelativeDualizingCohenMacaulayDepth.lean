module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.ExtCohenMacaulaySerreDepth
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay

/-!
# Depth of the cohomology of the relative dualizing complex

For a finite type algebra `A` over a Noetherian ring `R` and a prime `𝔮` of `A`, a nonzero
localized cohomology module `H^{-r}(ω^•_{A/R})_𝔮` of the relative dualizing complex has depth at
least `min(2, dim A_𝔮)`.

## Main results

* `moduleSupportDim_localizedModule_ulift_self`: the support of `A_𝔮` over itself has dimension
  `dim A_𝔮`.
* `min_two_ringKrullDim_le_moduleDepth_localizedModule_homology_upperShriek`: a nonzero
  `H^{-r}(ω^•_{A/R})_𝔮` has depth at least `min(2, dim A_𝔮)`.
* `min_two_ringKrullDim_le_moduleDepth_localizedModule_homology_relativeDualizingComplex`: the
  same bound at a prime `𝔮` of `A` not meeting the image of `R ∖ 𝔭`, where `R_𝔭` is
  Cohen–Macaulay.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The localization of `A` at a prime `𝔮`, as a module over `A_𝔮`, has support of dimension
`dim(A_𝔮)`. -/
theorem moduleSupportDim_localizedModule_ulift_self {A : Type u} [CommRing A] (q : Ideal A)
    [q.IsPrime] :
    moduleSupportDim (Localization.AtPrime q) (LocalizedModule.AtPrime q (ULift.{u} A)) =
      ringKrullDim (Localization.AtPrime q) := by
  let T₀ := Localization.AtPrime q
  let e : LocalizedModule.AtPrime q (ULift.{u} A) ≃ₗ[T₀] T₀ :=
    (LocalizedModule.equivTensorProduct q.primeCompl (ULift.{u} A)).trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T₀ T₀)
        (ULift.moduleEquiv (R := A) (M := A))).trans
        (TensorProduct.AlgebraTensorModule.rid A T₀ T₀))
  rw [moduleSupportDim_eq_of_linearEquiv e, moduleSupportDim_eq_Module_supportDim,
    Module.supportDim_self_eq_ringKrullDim]

/-- For a surjection `φ : P → A` and a prime `𝔮` of `A` with `𝔯 = φ⁻¹(𝔮)`, the kernel of
`P_𝔯 → A_𝔮` kills `A_𝔯`. -/
theorem ker_localRingHom_le_annihilator_localizedModule_ulift {P A : Type u} [CommRing P]
    [CommRing A] {φ : P →+* A} (hφ : Function.Surjective φ) (q : Ideal A) [q.IsPrime] :
    RingHom.ker (Localization.localRingHom (q.comap φ) q φ rfl) ≤
      Module.annihilator (Localization.AtPrime (q.comap φ))
        (LocalizedModule (q.comap φ).primeCompl
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A (ULift.{u} A)))) := by
  have hIMap : RingHom.ker (Localization.localRingHom (q.comap φ) q φ rfl) =
      (RingHom.ker φ).map (algebraMap P (Localization.AtPrime (q.comap φ))) :=
    IsLocalization.ker_map (S := Localization.AtPrime (q.comap φ)) (Localization.AtPrime q) φ
      (Ideal.map_primeCompl_comap_of_surjective φ hφ q)
  rw [hIMap, Ideal.map_le_iff_le_comap]
  intro x hx
  change algebraMap P (Localization.AtPrime (q.comap φ)) x ∈ Module.annihilator _ _
  rw [Module.mem_annihilator]
  intro y
  change algebraMap P (Localization.AtPrime (q.comap φ)) x • y = 0
  rw [algebraMap_smul]
  induction y using LocalizedModule.induction_on with
  | h a t =>
    rw [LocalizedModule.smul'_mk]
    have hxa : x • a = 0 := by
      change ULift.up (φ x * a.down) = ULift.up 0
      rw [RingHom.mem_ker.mp hx, zero_mul]
    rw [hxa, LocalizedModule.zero_mk]

/-- Let `S` be a Cohen--Macaulay Noetherian local ring and `f : S → T` a surjection. If `N` is a
finite `S`-module killed by `ker f` with `dim Supp N = dim T` and `j ≤ depth_{ker f}(S)`, then a
nonzero `Ext^j_S(N, S)` has depth at least `min(2, dim T)`. -/
theorem min_two_ringKrullDim_le_moduleDepth_ext_of_surjective {S T : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] [CommRing T] [Nontrivial T] {f : S →+* T}
    (hf : Function.Surjective f) (hS : Module.IsMaximalCohenMacaulay S S) (N : ModuleCat.{u} S)
    [Module.Finite S N] (hN : RingHom.ker f ≤ Module.annihilator S N)
    (hdimN : Module.supportDim S N = ringKrullDim T) (j : ℕ)
    (hj : (j : ℕ∞) ≤ Module.depth S (RingHom.ker f) S)
    (hnt : Nontrivial (Abelian.Ext N (ModuleCat.of S S) j)) :
    min (2 : ℕ∞) ((ringKrullDim T).unbotD 0) ≤
      moduleDepth S (Abelian.Ext N (ModuleCat.of S S) j) := by
  have hCM : Module.IsCohenMacaulayAtMaximalIdeal S (ModuleCat.of S S) := by
    unfold Module.IsCohenMacaulayAtMaximalIdeal
    change (Module.depth S (IsLocalRing.maximalIdeal S) S : WithBot ℕ∞) = Module.supportDim S S
    rw [Module.supportDim_self_eq_ringKrullDim]
    exact hS
  have h0BUX := supportDim_quotient_add_depth_eq_supportDim (RingHom.ker f) (RingHom.ker_ne_top f)
    (hCM : Module.IsCohenMacaulayAtMaximalIdeal S S)
  rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ (RingHom.ker f : Submodule S S)
    (by simp)), Module.supportDim_quotient_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)] at h0BUX
  have hdim : Module.supportDim S N + j ≤ Module.supportDim S (ModuleCat.of S S) := by
    change _ ≤ Module.supportDim S S
    rw [hdimN, ← h0BUX]
    gcongr
    exact_mod_cast hj
  have h := min_two_supportDim_le_moduleDepth_ext_of_le_depth (RingHom.ker f) N hN j
    (ModuleCat.of S S) hCM (by simpa using hj) hdim hnt
  rwa [hdimN] at h

/-- **The depth of `H^{-r}(ω^•_{A/R})_𝔮` against the dimension of `A_𝔮`.** Under the hypotheses of
`Dualizing.subsingleton_and_min_two_le_moduleDepth_localizedModule_homology_upperShriek`, a
nonzero `H^{-r}(ω^•_{A/R})_𝔮` has depth at least `min(2, dim A_𝔮)`.

The module is `Ext^{n-r}_{P_𝔯}(A_𝔯, P_𝔯)` with `P_𝔯` Cohen--Macaulay, `n - r ≤ depth_{I₀}(P_𝔯)` and
`depth_{I₀}(P_𝔯) + dim(A_𝔮) = dim(P_𝔯)` [Stacks, Tag 0BUX]; see
`Dualizing.min_two_supportDim_le_moduleDepth_ext_of_le_depth`. -/
theorem min_two_ringKrullDim_le_moduleDepth_localizedModule_homology_upperShriek
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hCMR : Module.IsMaximalCohenMacaulay (Localization.AtPrime (q.under R))
      (Localization.AtPrime (q.under R)))
    (r : ℕ)
    (hr : ∀ (q' : Ideal A) [q'.IsPrime], q' ∈ minimalPrimes A → q' ≤ q →
      (Ideal.underResidueTrdeg R q' : ℕ∞) ≤ r)
    (hnt : Nontrivial (LocalizedModule.AtPrime q
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))) :
    min (2 : ℕ∞) ((ringKrullDim (Localization.AtPrime q)).unbotD 0) ≤
      moduleDepth (Localization.AtPrime q) (LocalizedModule.AtPrime q
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) := by
  let P := p.Poly
  let rP : Ideal P := q.comap p.toRingHom
  obtain ⟨hCMS, hdepth⟩ :=
    isMaximalCohenMacaulay_and_le_depth_ker_localRingHom p q hCMR r hr rP rfl
  let S₀ := Localization.AtPrime rP
  let T₀ := Localization.AtPrime q
  let fLocal : S₀ →+* T₀ := Localization.localRingHom rP q p.toRingHom rfl
  have hfLocal : Function.Surjective fLocal :=
    Localization.surjective_localRingHom p.toRingHom p.surjective rP q rfl
  let I₀ : Ideal S₀ := RingHom.ker fLocal
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  have : Module.Finite P M₀ := finite_restrictScalars_ulift p
  let N : ModuleCat.{u} S₀ := ModuleCat.of S₀ (LocalizedModule rP.primeCompl (M₀ : Type u))
  let H : ℤ → ModuleCat.{u} A := fun i => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
    (p.upperShriekFunctor.{u, 0}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  have key : ∀ (i : ℤ) (j : ℕ), i + p.variableCount = j →
      LocalizedModule rP.primeCompl ((ModuleCat.restrictScalars p.toRingHom).obj (H i)) ≃ₗ[S₀]
        Abelian.Ext N (ModuleCat.of S₀ S₀) j := fun i j hj =>
    (localizedHomologyUpperShriekLinearEquiv p rP i j hj).trans
      (Abelian.Ext.homLinearEquiv (R := S₀)).symm
  have := finite_homology_upperShriekFunctor p (-(r : ℤ))
  have hntP : Nontrivial (LocalizedModule rP.primeCompl
      ((ModuleCat.restrictScalars p.toRingHom).obj (H (-(r : ℤ))))) :=
    (localizedModuleRestrictScalarsAddEquiv p.toRingHom p.surjective q rP rfl
      (H (-(r : ℤ)))).toEquiv.nontrivial_congr.mpr hnt
  obtain ⟨hd, -⟩ := moduleDepth_and_moduleSupportDim_localizedModule_restrictScalars
    p.toRingHom p.surjective q rP rfl (H (-(r : ℤ)))
  change min (2 : ℕ∞) ((ringKrullDim T₀).unbotD 0) ≤
    moduleDepth T₀ (LocalizedModule.AtPrime q (H (-(r : ℤ))))
  rw [hd]
  have h0 : ¬ (-(r : ℤ) + p.variableCount < 0) := by
    intro h0
    have hs := (localizedHomologyUpperShriekLinearEquiv p rP (-(r : ℤ)) _
      rfl).toEquiv.subsingleton_congr.mpr (subsingleton_derivedExt_of_neg _ _ _ (by omega))
    exact (not_subsingleton_iff_nontrivial.mpr hntP) hs
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h0)
  have hjd : (j : ℕ∞) ≤ Module.depth S₀ I₀ S₀ := natCast_le_of_le_add hdepth (by omega)
  have hdimN : Module.supportDim S₀ N = ringKrullDim T₀ := by
    rw [← moduleSupportDim_eq_Module_supportDim, ← moduleSupportDim_localizedModule_ulift_self q]
    exact ((moduleDepth_and_moduleSupportDim_localizedModule_restrictScalars p.toRingHom
      p.surjective q rP rfl (ModuleCat.of A (ULift.{u} A))).2).symm
  rw [moduleDepth_eq_of_linearEquiv (key _ j hj)]
  exact min_two_ringKrullDim_le_moduleDepth_ext_of_surjective hfLocal hCMS N
    (ker_localRingHom_le_annihilator_localizedModule_ulift p.surjective q) hdimN j hjd
    ((key _ j hj).symm.toEquiv.nontrivial_congr.mpr hntP)

/-! ### Tag 0E9R -/

/-- **The depth of `H^{-r}(ω^•_{A/R})` at a prime of `A_𝔭`.** Under the hypotheses of
[Stacks, Tag 0E9R], let `𝔮 ⊂ A` be a prime not meeting the image of `R ∖ 𝔭`. If
`H^{-r}(ω^•_{A/R})_𝔮 ≠ 0`, then its depth is at least `min(2, dim A_𝔮)`. -/
theorem min_two_ringKrullDim_le_moduleDepth_localizedModule_homology_relativeDualizingComplex
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hCM : IsCohenMacaulayLocalRing (Localization.AtPrime 𝔭)) (r : ℕ)
    (htrdeg : ∀ (q : Ideal A) [q.IsPrime], q ∈ minimalPrimes A →
      letI := Ideal.ResidueField.algebraOfLiesOver (q.under R) q
      Algebra.trdeg (q.under R).ResidueField q.ResidueField ≤ r)
    (q : Ideal A) [q.IsPrime]
    (hq : Disjoint ((Submonoid.map (algebraMap R A) 𝔭.primeCompl : Submonoid A) : Set A)
      (q : Set A))
    (hnt : Nontrivial (LocalizedModule.AtPrime q
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))) :
    min (2 : ℕ∞) ((ringKrullDim (Localization.AtPrime q)).unbotD 0) ≤
      moduleDepth (Localization.AtPrime q) (LocalizedModule.AtPrime q
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) := by
  obtain ⟨hCMR, hr⟩ := hypotheses_at_prime 𝔭 hCM r htrdeg q hq
  exact min_two_ringKrullDim_le_moduleDepth_localizedModule_homology_upperShriek p q hCMR r hr hnt

end Dualizing

end
