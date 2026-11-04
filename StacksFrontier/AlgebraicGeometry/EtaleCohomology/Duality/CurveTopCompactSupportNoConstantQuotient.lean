module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.NoConstantQuotientRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLisseLevelDualityOpenImmersion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePointDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelTorsionLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.QuasiFiniteLowerShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperFrobeniusLeray
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass

/-!
# The top compactly supported cohomology of a curve without constant simple quotients

Let `Ω` be an algebraically closed field, `Y` a smooth proper curve over `Ω`, `C ⊆ Y` a nonempty
open, `Λ` a finite commutative ring whose characteristic is invertible in `Ω`, and `N` a locally
constant sheaf of `Λ`-modules with finite values on `C_étale` without constant simple quotient
(`Stacks.EtaleCohomology.HasNoConstantSimpleQuotient`). Then `H²_c(C, N) = 0`, computed through
any compactification of `C ⟶ Spec Ω`
(`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_of_hasNoConstantSimpleQuotient`).
This is the vanishing half of `H²_c(C, N) = (N_x̄)_{π₁(C, x̄)}(-1)`: the module of coinvariants
vanishes exactly when the monodromy has no simple quotient with trivial action.

The proof:

* restriction of scalars along `ℤ/n ⟶ Λ`, `n` the characteristic of `Λ`, commutes with `Rf_!`
  (`Stacks.EtaleCohomology.nonempty_homology_derivedLowerShriek_restrictScalars_iso`), so we may
  read `N` as a sheaf `N'` of `ℤ/n`-modules;
* `H²_c(C, -)` is right exact, `H³_c` vanishing on a curve
  (`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_two_mul_lt`), so for every prime
  `ℓ ∣ n` multiplication by `ℓ` is onto on `H²_c(C, N')` once `H²_c(C, N'/ℓN') = 0`; then
  multiplication by `n = 0` is onto, and `H²_c(C, N') = 0`;
* `N'/ℓN'` is a lisse sheaf `Q₀` of `ℤ/ℓ`-modules, and Poincaré duality on `Y`
  (`Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_lisse_zmodPow_of_isOpenImmersion`)
  identifies `H²_c(C, Q₀) = Ext²_Y(ℤ/ℓ, j_! Q₀)` with the dual of `Hom_C(Q₀, ℤ/ℓ)`;
* a morphism `Q₀ ⟶ ℤ/ℓ` gives a `ℤ/n`-linear morphism from `N'` to a constant sheaf, which
  vanishes since `N` has no constant simple quotient
  (`Stacks.EtaleCohomology.eq_zero_of_hasNoConstantSimpleQuotient_restrictScalars`).

This is the curve half of the generic coinvariant vanishing (L2) in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), and the top degree of the fibres of the
Fourier family away from `a = 0`.

## Main results

* `Stacks.EtaleCohomology.epi_homology_map_singleFunctor_map_f_of_isZero`,
  `Stacks.EtaleCohomology.epi_homology_map_singleFunctor_map_g_of_isZero`: the long exact sequence
  of a triangulated functor between two derived categories.
* `Stacks.EtaleCohomology.isZero_of_epi_nsmul_id_of_prime`.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_restrictScalars_of_finite`.
* `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_subsingleton_ext`.
* `Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_of_hasNoConstantSimpleQuotient`.

## Implementation notes

`Rf_!` lives in the standard model `HasDerivedCategory.standard`, and so do the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Functor.commShiftRightDerivedFunctorPlus Functor.isTriangulated_rightDerivedFunctorPlus

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-! ### The long exact sequence of a triangulated functor -/

section Sequence

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [Category* D] [Abelian D]
  [HasDerivedCategory D] (F : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D) [F.CommShift ℤ]
  [F.IsTriangulated]

/-- **`Hⁿ(F(X₁[0])) ⟶ Hⁿ(F(X₂[0]))` is onto when `Hⁿ(F(X₃[0])) = 0`**, for a short exact
sequence `0 → X₁ → X₂ → X₃ → 0` and a triangulated functor `F : D⁺(C) ⥤ D⁺(D)`. -/
theorem epi_homology_map_singleFunctor_map_f_of_isZero {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℤ) (hz : IsZero ((DerivedCategory.Plus.homologyFunctor D n).obj
      (F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₃)))) :
    Epi ((DerivedCategory.Plus.homologyFunctor D n).map
      (F.map ((DerivedCategory.Plus.singleFunctor C 0).map S.f))) :=
  ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₁_iff _
    (F.map_distinguished _ (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)) n).2
    (hz.eq_of_tgt _ _)

/-- **`Hⁿ⁰(F(X₂[0])) ⟶ Hⁿ⁰(F(X₃[0]))` is onto when `Hⁿ¹(F(X₁[0])) = 0`**, `n₀ + 1 = n₁`, for a
short exact sequence `0 → X₁ → X₂ → X₃ → 0` and a triangulated functor `F : D⁺(C) ⥤ D⁺(D)`. -/
theorem epi_homology_map_singleFunctor_map_g_of_isZero {S : ShortComplex C} (hS : S.ShortExact)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (hz : IsZero ((DerivedCategory.Plus.homologyFunctor D n₁).obj
      (F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)))) :
    Epi ((DerivedCategory.Plus.homologyFunctor D n₀).map
      (F.map ((DerivedCategory.Plus.singleFunctor C 0).map S.g))) :=
  ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff _
    (F.map_distinguished _ (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)) n₀ n₁
    h).2 (hz.eq_of_tgt _ _)

end Sequence

/-! ### Multiplication by primes -/

/-- **An object killed by `n ≠ 0` on which multiplication by every prime divisor of `n` is an
epimorphism is zero**: multiplication by `n` is a composite of multiplications by primes. -/
theorem isZero_of_epi_nsmul_id_of_prime {𝒜 : Type*} [Category* 𝒜] [Preadditive 𝒜]
    [HasZeroObject 𝒜] (A : 𝒜) (n : ℕ) (hn : n ≠ 0) (h0 : n • 𝟙 A = 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → Epi (ℓ • 𝟙 A)) : IsZero A := by
  have key : ∀ m : ℕ, m ∣ n → Epi (m • 𝟙 A) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · interval_cases m
        · exact absurd (Nat.eq_zero_of_zero_dvd hm) hn
        · rw [one_smul]; infer_instance
      · have hp := Nat.minFac_prime (show m ≠ 1 by omega)
        obtain ⟨k, hk⟩ := Nat.minFac_dvd m
        have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; omega)
        have hkm : k < m := by
          rw [hk]
          exact lt_mul_left hk0 hp.one_lt
        have hkn : k ∣ n := (Dvd.intro_left _ hk.symm).trans hm
        have hfac : m • 𝟙 A = (m.minFac • 𝟙 A) ≫ (k • 𝟙 A) := by
          rw [Preadditive.nsmul_comp, Category.id_comp, smul_smul, ← hk]
        have := h _ hp ((Nat.minFac_dvd m).trans hm)
        have := ih k hkm hkn
        rw [hfac]
        infer_instance
  have := key n dvd_rfl
  rw [h0] at this
  exact IsZero.of_epi_zero A A

/-! ### Restriction of scalars -/

section RestrictScalars

variable {Λ₀ Λ : Type} [CommRing Λ₀] [CommRing Λ] (ρ : Λ₀ →+* Λ) {X : Scheme.{u}}

/-- Restriction of scalars of sheaves of modules on the small étale site is faithful. -/
theorem eq_of_etaleModuleRestrictScalars_map_eq {F G : EtaleModules.{u, 0} Λ X} {φ ψ : F ⟶ G}
    (h : (etaleModuleRestrictScalars ρ X).map φ = (etaleModuleRestrictScalars ρ X).map ψ) :
    φ = ψ := by
  ext U x
  exact congrArg (fun χ : (etaleModuleRestrictScalars ρ X).obj F ⟶
    (etaleModuleRestrictScalars ρ X).obj G => χ.hom.app U x) h

/-- Restriction of scalars of sheaves of modules on the small étale site reflects zero objects. -/
theorem isZero_of_isZero_etaleModuleRestrictScalars (F : EtaleModules.{u, 0} Λ X)
    (h : IsZero ((etaleModuleRestrictScalars ρ X).obj F)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  exact eq_of_etaleModuleRestrictScalars_map_eq ρ (h.eq_of_src _ _)

/-- **Restriction of scalars to `Λ₀` of a finite type locally constant sheaf over a finite ring
`Λ` is finite type locally constant**: the constant sheaf commutes with restriction of scalars,
and a finitely generated module over a finite ring is finite. -/
theorem isFiniteTypeLocallyConstant_restrictScalars_of_finite [Finite Λ]
    (N : EtaleModules.{u, 0} Λ X)
    (hN : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology N) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ₀ X.smallEtaleTopology
      ((etaleModuleRestrictScalars ρ X).obj N) := by
  intro U
  obtain ⟨I, V, f, hcov, h⟩ := hN U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  have : Module.Finite Λ E := (ModuleCat.isFG_iff E).1 hE
  have : Finite E := Module.finite_of_finite Λ
  have : Finite ((ModuleCat.restrictScalars.{u + 1} ρ).obj E) := inferInstanceAs (Finite E)
  refine ⟨(ModuleCat.restrictScalars.{u + 1} ρ).obj E,
    (ModuleCat.isFG_iff _).2 Module.Finite.of_finite, ⟨?_⟩⟩
  exact ((constantCommuteCompose (X.smallEtaleTopology.over (V i))
      (ModuleCat.restrictScalars.{u + 1} ρ)).app E).symm ≪≫
    (sheafCompose (X.smallEtaleTopology.over (V i)) (ModuleCat.restrictScalars.{u + 1} ρ)).mapIso e

end RestrictScalars

/-! ### `H^q_c` over a separably closed field as `Ext` on a compactification -/

/-- **`H^q(Rf_!(G[0])) = 0` over a separably closed field when `Ext^q_X̄(Λ, j_! G) = 0`**: over
`Ω` global sections are an exact equivalence, and the global sections of `H^q(Rf_!(G[0]))` are
`H^q_c(X, G) = Ext^q_X̄(Λ, j_! G)`. -/
theorem isZero_homology_derivedLowerShriek_of_subsingleton_ext (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (Λ : Type) [CommRing Λ] {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (G : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (h : Subsingleton (Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} Λ
      j.space.smallEtaleTopology) ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G) q)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have : HasSheafify (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hasSheafifyEtale.{u, 0} (Spec (.of Ω)) Λ
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  let K := (derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have e := (compactlySupportedCohomologyGroupSingleIsoExt Λ Ω f j G q).addCommGroupIsoToAddEquiv
  have hc : IsZero ((compactlySupportedCohomologyGroup.{u, 0} Ω f j Λ q).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ (@Equiv.subsingleton _ _ e.toEquiv h)
  have h1 : IsZero (Γ.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :=
    hc.of_iso ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso Γ q).app K).symm
  rw [IsZero.iff_id_eq_zero]
  exact Γ.map_injective (by rw [Γ.map_id, Functor.map_zero]; exact h1.eq_of_src _ _)

/-! ### The top compactly supported cohomology of a curve -/

/-- **`H²_c` of a locally constant sheaf without constant simple quotient on a curve vanishes.**
Let `Ω` be algebraically closed, `Y` a smooth proper curve over `Ω`, `V : C ⟶ Y` an open
immersion of a nonempty `C` with structure morphism `g = V ≫ π_Y`, `Λ` a finite commutative ring
whose characteristic is invertible in `Ω`, and `N` a locally constant sheaf of `Λ`-modules with
finite values on `C_étale` every morphism of which to the constant sheaf on a simple `Λ`-module
vanishes. Then `H²_c(C, N) = H²(Rg_!(N[0])) = 0`, for every compactification of `g`. -/
theorem isZero_homology_two_derivedLowerShriek_of_hasNoConstantSimpleQuotient (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] (Λ : Type) [CommRing Λ] [Finite Λ]
    (hΛ : IsUnit ((ringChar Λ : ℕ) : Ω)) {Y C : Scheme.{u}} (πY : Y ⟶ Spec (.of Ω))
    [IsCurve Ω πY] [Smooth πY] [IsProper πY] (V : C ⟶ Y) [IsOpenImmersion V] [Nonempty C]
    (g : C ⟶ Spec (.of Ω)) (hg : V ≫ πY = g) (N : EtaleModules.{u, 0} Λ C)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ C.smallEtaleTopology
      (fun E => Module.Finite Λ E) N)
    (hNQ : HasNoConstantSimpleQuotient Λ N) (jc : CompactificationOf (Over.mk g)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} g jc Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N))) := by
  subst hg
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian πY
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := Ω) (f := πY)
  -- `C` is an irreducible normal curve
  have hCirr : IrreducibleSpace C := V.isOpenEmbedding.irreducibleSpace
  have : IsNormal (Spec (CommRingCat.of Ω)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed Ω)
  have : IsNormal C := isNormal_of_smooth (V ≫ πY)
  have hCu : IsGeometricallyUnibranch C := isGeometricallyUnibranch_of_isNormal
  have hdim : topologicalKrullDim C ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    refine V.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans ?_
    rw [IsCurve.topologicalKrullDim_eq_one (k := Ω) (f := πY)]
    rfl
  -- restriction of scalars to `ℤ/n`
  set n := ringChar Λ with hn_def
  have hn : NeZero n := ⟨CharP.char_ne_zero_of_finite Λ n⟩
  let ρ₀ : ZMod n →+* Λ := ZMod.castHom (dvd_refl n) Λ
  let N' := (etaleModuleRestrictScalars ρ₀ C).obj N
  have hNft : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ C.smallEtaleTopology N :=
    isLocallyConstantWith_of_imp Λ (fun E hE => (ModuleCat.isFG_iff E).2 hE) hN
  have hN' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod n) C.smallEtaleTopology N' :=
    isFiniteTypeLocallyConstant_restrictScalars_of_finite ρ₀ N hNft
  obtain ⟨eR⟩ := nonempty_homology_derivedLowerShriek_restrictScalars_iso ρ₀ (V ≫ πY) jc N 2
  refine isZero_of_isZero_etaleModuleRestrictScalars ρ₀ _ (IsZero.of_iso ?_ eR.symm)
  let T : EtaleModules.{u, 0} (ZMod n) C ⥤ EtaleModules.{u, 0} (ZMod n) (Spec (.of Ω)) :=
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ derivedLowerShriek.{u, 0} (V ≫ πY) jc (ZMod n) ⋙
      DerivedCategory.Plus.homologyFunctor _ 2
  change IsZero (T.obj N')
  have h0 : n • 𝟙 (T.obj N') = 0 := by
    rw [nsmul_id_sheaf_zmod_eq (T.obj N') (a := n) (b := 0) (by simp), zero_smul]
  refine isZero_of_epi_nsmul_id_of_prime (T.obj N') n hn.out h0 fun ℓ hℓ hℓn => ?_
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero (ℓ ^ 1) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hℓΩ : IsUnit (ℓ : Ω) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hℓn) hΛ
  have h1 : ℓ ^ 1 ∣ n := by rwa [pow_one]
  -- the factorization of multiplication by `ℓ` through its image
  let f := ℓ • 𝟙 N'
  let Q := cokernel f
  let p := Abelian.factorThruImage f
  let S₁ := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
  let S₂ := ShortComplex.mk (kernel.ι p) p (kernel.condition _)
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
  have hTf : ℓ • 𝟙 (T.obj N') = T.map p ≫ T.map S₁.f := by
    rw [← T.map_comp, Abelian.image.fac f, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rw [hTf]
  -- `H³_c` vanishes on a curve
  have : Epi (T.map p) := epi_homology_map_singleFunctor_map_g_of_isZero
    (derivedLowerShriek.{u, 0} (V ≫ πY) jc (ZMod n)) hS₂ 2 3 (by norm_num)
    (isZero_homology_derivedLowerShriek_of_two_mul_lt (ZMod n) Ω (V ≫ πY) jc 1 hdim _ 3
      (by norm_num))
  suffices hQ : IsZero (T.obj Q) by
    have : Epi (T.map S₁.f) := epi_homology_map_singleFunctor_map_f_of_isZero
      (derivedLowerShriek.{u, 0} (V ≫ πY) jc (ZMod n)) hS₁ 2 hQ
    infer_instance
  -- `Q = N' / ℓ N'` is killed by `ℓ`
  have hQℓ : ℓ • 𝟙 Q = 0 := by
    rw [← cancel_epi (cokernel.π f), comp_zero, Preadditive.comp_nsmul, Category.comp_id,
      ← Category.id_comp (cokernel.π f), ← Preadditive.nsmul_comp]
    exact cokernel.condition f
  let π₁ : ZMod n →+* ZMod (ℓ ^ 1) := ZMod.castHom h1 (ZMod (ℓ ^ 1))
  have hker : ∀ (W : C.Etaleᵒᵖ), ∀ a ∈ RingHom.ker π₁, ∀ x : Q.obj.obj W, a • x = 0 := by
    intro W a ha x
    have hx : ℓ • x = 0 := by
      have := etaleModules_map_nsmul_id_apply (ZMod n) Q ℓ W x
      rw [hQℓ, Functor.map_zero] at this
      exact this.symm
    have hval : ℓ ∣ a.val := by
      have h2 : ((a.val : ℕ) : ZMod (ℓ ^ 1)) = 0 := by
        rw [← RingHom.mem_ker.1 ha, ZMod.castHom_apply, ZMod.cast_eq_val]
      rwa [ZMod.natCast_eq_zero_iff, pow_one] at h2
    obtain ⟨c, hc⟩ := hval
    rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, hc, mul_nsmul, hx, nsmul_zero]
  let Q₀ := (etaleModuleCoextendScalars π₁ C).obj Q
  let eQ : (etaleModuleRestrictScalars π₁ C).obj Q₀ ≅ Q :=
    etaleModuleRestrictCoextendScalarsIso π₁ (ZMod.ringHom_surjective π₁) Q hker
  obtain ⟨eR'⟩ := nonempty_homology_derivedLowerShriek_restrictScalars_iso π₁ (V ≫ πY) jc Q₀ 2
  refine IsZero.of_iso ?_ (T.mapIso eQ.symm ≪≫ eR')
  refine Functor.map_isZero _ ?_
  -- `Q₀` is lisse
  have hQ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod n) C.smallEtaleTopology Q :=
    isFiniteTypeLocallyConstantModuleSheaf_cokernel.{u, u + 1, 0, 0} C.smallEtaleTopology
      (ZMod n) f hN' hN'
  have hQ₀ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ 1)) C.smallEtaleTopology
      Q₀ :=
    LevelChange.isFiniteTypeLocallyConstant_of_restrict h1 Q₀
      (isFiniteTypeLocallyConstant_congr _ _ eQ.symm hQ)
  -- every morphism `Q₀ ⟶ ℤ/ℓ` vanishes
  have hHom : ∀ ψ : Q₀ ⟶ unitSheaf (X := C) (ℓ ^ 1), ψ = 0 := by
    intro ψ
    let E₀ := ModuleCat.of (ZMod (ℓ ^ 1)) (ULift.{u + 1} (ZMod (ℓ ^ 1)))
    let φ : N' ⟶ (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))).obj
        ((ModuleCat.restrictScalars.{u + 1} π₁).obj E₀) :=
      cokernel.π f ≫ eQ.inv ≫ (etaleModuleRestrictScalars π₁ C).map ψ ≫
        ((etaleModuleRestrictScalarsConstantIso π₁ C).app E₀).hom
    have hφ : φ = 0 :=
      eq_zero_of_hasNoConstantSimpleQuotient_restrictScalars ρ₀ hCu N hNft hNQ _ φ
    refine eq_of_etaleModuleRestrictScalars_map_eq π₁ ?_
    rw [Functor.map_zero]
    rw [← cancel_epi (cokernel.π f ≫ eQ.inv), comp_zero,
      ← cancel_mono ((etaleModuleRestrictScalarsConstantIso π₁ C).app E₀).hom, zero_comp]
    simpa only [Category.assoc] using hφ
  -- Poincaré duality on `Y`
  obtain ⟨t, ht⟩ := exists_injective_trace_zmodPow_of_curve πY hℓΩ 1
  have hD := (isDualityPerfect_extensionByZero_lisse_zmodPow_of_isOpenImmersion πY hℓΩ t ht V Q₀
    hQ₀).1 2 0 rfl
  have hsub0 : Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ 1)) V).obj Q₀)
      (unitSheaf (X := Y) (ℓ ^ 1)) 0) := by
    refine ⟨fun a b => Ext.homEquiv₀.injective ?_⟩
    apply ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod (ℓ ^ 1)) V).homEquiv _ _).injective
    rw [← cancel_mono (((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod (ℓ ^ 1)) V).app
        (unitSheaf (X := Y) (ℓ ^ 1))).symm ≪≫
      (etaleModuleInverseImageConstantIso.{u, 0} (ZMod (ℓ ^ 1)) V).app
        (ModuleCat.of (ZMod (ℓ ^ 1)) (ULift.{u + 1} (ZMod (ℓ ^ 1))))).hom,
      hHom (_ ≫ _), hHom (_ ≫ _)]
  have hsub2 : Subsingleton (Ext (unitSheaf (X := Y) (ℓ ^ 1))
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ 1)) V).obj Q₀) 2) :=
    ⟨fun a b => hD.1 (AddMonoidHom.ext fun z => by
      rw [Subsingleton.elim z 0, map_zero, map_zero])⟩
  -- `H²_c(C, Q₀) = Ext²_Y(ℤ/ℓ, V_! Q₀)`, for any compactification
  let jP := CompactificationOf.ofFactorizationGeneral (V ≫ πY) V πY rfl
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod (ℓ ^ 1)) C) 0).obj Q₀
  exact (isZero_homology_derivedLowerShriek_of_subsingleton_ext Ω (ZMod (ℓ ^ 1)) (V ≫ πY) jP
    Q₀ 2 hsub2).of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    ((derivedLowerShriekCompactificationIso (V ≫ πY) jc jP (ZMod (ℓ ^ 1))).app
      ⟨K, isTorsionPlus_of_finite (ZMod (ℓ ^ 1)) _ K⟩))

end Stacks.EtaleCohomology

end
