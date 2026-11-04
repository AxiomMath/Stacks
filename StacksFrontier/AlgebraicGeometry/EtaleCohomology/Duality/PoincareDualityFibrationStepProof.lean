module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFibrationBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationNeighbourhood
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationNeighbourhoodExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CompactSupportTopExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurityGluing
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingDualizing
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField

/-!
# The fibration step of Poincaré duality

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`. This file
proves the fibration step `Stacks.EtaleCohomology.PoincareDualityFibrationStep ℓ k` of the
induction on the dimension in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH):
Poincaré duality at `Λ` in all dimensions `≤ d` gives duality on a dense open of every smooth
irreducible `W` of dimension `d + 1`
(`Stacks.EtaleCohomology.poincareDualityFibrationStep_of_inputs`), from the four geometric inputs
of `Stacks.EtaleCohomology.CohomologicalDimensionInput`,
`Stacks.EtaleCohomology.RelativeCurveDualityInput`,
`Stacks.EtaleCohomology.LowerShriekLowDegreeInput` and
`Stacks.EtaleCohomology.LisseDualityOfUnitInput`.

The dense open is an elementary fibration `f : U → S` over `S` smooth, affine and irreducible of
dimension `d` (SGA 4 XI 3.3, `Stacks.EtaleCohomology.existsElementaryFibrationNeighbourhood`). On
`U` (`Stacks.EtaleCohomology.isDualityPerfect_lowerShriek_fibration`): a trace on
`H^{2d+2}_c(U)` comes from a trace on `H^{2d}_c(S)` through the top-degree trace of `f`
(`Stacks.EtaleCohomology.bijective_transferHom_lowerShriekTopTrace`), relative duality moves
duality on `U` to duality on `S` for `Rf_! Λ`
(`Stacks.EtaleCohomology.isPerfect_lowerShriek_comp_iff`), which holds by the five lemma
(`Stacks.EtaleCohomology.isPerfect_lowerShriek_base`). On `W`: the dualizing object
`j_! Λ_U` of `U` is replaced by `j_! Λ_W` along the counit `j_! U_! U⁻¹ Λ_W → j_! Λ_W`, which
is bijective on `Ext(j_! U_! U⁻¹ Λ_W, -)`
(`Stacks.EtaleCohomology.bijective_comp_mk₀_extensionByZero_counit`) and on top-degree compactly
supported cohomology (the complement of `U` has dimension `≤ d`); and
`Ext^q(j_! U_! Λ, j_! Λ_W) = H^q(U, Λ) = 0` for `q > 2d + 2` by the cohomological dimension input.

Together with `Stacks.EtaleCohomology.poincareDualityCore_of_fibrationStep` this gives
`Stacks.EtaleCohomology.PoincareDualityCore ℓ k`
(`Stacks.EtaleCohomology.poincareDualityCore_of_inputs`).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_unitSheaf`.
* `Stacks.EtaleCohomology.exists_compactification_topologicalKrullDim_le`.
* `Stacks.EtaleCohomology.bijective_comp_mk₀_extensionByZero_counit`.
* `Stacks.EtaleCohomology.isDualityPerfect_lowerShriek_fibration`.
* `Stacks.EtaleCohomology.poincareDualityFibrationStep_of_inputs`.
* `Stacks.EtaleCohomology.poincareDualityCore_of_inputs`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor HomologicalDuality

attribute [local instance] HasDerivedCategory.standard

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The constant sheaf `ℤ/ℓ` is locally constant of finite type.** -/
theorem isFiniteTypeLocallyConstant_unitSheaf (X : Scheme.{u}) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology
      (unitSheaf (X := X) ℓ) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_constantSheaf _ _
    (by rw [ModuleCat.isFG_iff]; exact Module.Finite.of_finite)

variable {k : Type u} [Field k]

/-- **A smooth irreducible `S` of dimension `d` over `k` has a compactification of dimension at
most `d`**: the closure of `S` in any compactification (Nagata). -/
theorem exists_compactification_topologicalKrullDim_le {S : Scheme.{u}} (d : ℕ)
    (q : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension d q] [IrreducibleSpace S] [CompactSpace S]
    [QuasiSeparatedSpace S] [IsSeparated q] [QuasiCompact q] :
    ∃ jS : CompactificationOf (Over.mk q), topologicalKrullDim jS.space ≤ d := by
  have : Smooth q := SmoothOfRelativeDimension.smooth d q
  obtain ⟨c⟩ : Nonempty (CompactificationOf (Over.mk q)) := IsCofiltered.nonempty
  have : SmoothOfRelativeDimension d (𝟙 S ≫ 𝟙 S ≫ q) := by
    simp only [Category.id_comp]; infer_instance
  rw [show q = 𝟙 S ≫ 𝟙 S ≫ q by simp]
  exact ⟨_, topologicalKrullDim_restrictClosed_space_le q c (𝟙 S) (𝟙 S) d⟩

/-- **The counit `j_! U_! U⁻¹ L → j_! L` is bijective on `Ext(j_! U_! U⁻¹ L, -)`** for an open
`U` of `W` and a compactification `j : W → X̄`: both groups are `Ext_U(U⁻¹ L, U⁻¹ L)`, `j_!` and
`U_!` being fully faithful on `Ext` and `U⁻¹` of the counit an isomorphism. -/
theorem bijective_comp_mk₀_extensionByZero_counit {W : Scheme.{u}} (p : W ⟶ Spec (.of k))
    (jc : CompactificationOf (Over.mk p)) (U : W.Opens) (L : EtaleModules.{u, 0} (ZMod ℓ) W)
    (n : ℕ) :
    Function.Bijective (fun y : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj L))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj L)) n =>
      y.comp (Ext.mk₀ ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) U.ι).counit.app L))) (add_zero n)) := by
  let Φ := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion
  let A := (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj L
  let ε := (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) U.ι).counit.app L
  have := isIso_etaleModuleRestriction_map_counit (ZMod ℓ) U.ι L
  have hW := Purity.bijective_comp_mk₀_of_isIso_restriction (ZMod ℓ) U
    ((etaleModuleRestriction.{u, 0} (ZMod ℓ) U.ι).obj L) ε n
  have h₁ := bijective_mapExactFunctor_extensionByZero p jc ℓ A A n
  have h₂ := bijective_mapExactFunctor_extensionByZero p jc ℓ L A n
  have hsq : (fun y : Ext (Φ.obj A) (Φ.obj A) n => y.comp (Ext.mk₀ (Φ.map ε)) (add_zero n)) ∘
      (fun e : Ext A A n => (e.mapExactFunctor Φ : Ext _ _ n)) =
      (fun e : Ext A L n => (e.mapExactFunctor Φ : Ext _ _ n)) ∘
        (fun w : Ext A A n => w.comp (Ext.mk₀ ε) (add_zero n)) := by
    funext y
    simp only [Function.comp_apply]
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Function.Bijective.of_comp_iff _ h₁, hsq]
  exact h₂.comp hW

variable [IsAlgClosed k]

/-- **Poincaré duality on an elementary fibration.** Let `f : U → S` be an elementary fibration
over `S` smooth, affine and irreducible of dimension `d` over `k`, `ℓ` invertible in `k`, and
`j : U → X̄` a compactification of the structure morphism `g = q ∘ f` of `U`. Given the four inputs
and Poincaré duality at `Λ` in dimensions `≤ d`, for every injective trace `t` on
`H^{2d+2}_c(U) = Ext^{2d+2}_X̄(Λ, j_! f⁻¹ Λ_S)`, duality holds at `j_! f⁻¹ Λ_S`:
`Ext^i_X̄(Λ, j_! f⁻¹ Λ_S) × Ext^{2d+2-i}_X̄(j_! f⁻¹ Λ_S, j_! f⁻¹ Λ_S) → Λ` is perfect. -/
theorem isDualityPerfect_lowerShriek_fibration (hV : CohomologicalDimensionInput ℓ k)
    (hPD : RelativeCurveDualityInput ℓ k) (hR : LowerShriekLowDegreeInput ℓ k)
    (hL : LisseDualityOfUnitInput ℓ k) (hℓ : IsUnit (ℓ : k)) (d : ℕ)
    (hIH : UnitPoincareDualityUpTo ℓ k d) {U S : Scheme.{u}} (q : S ⟶ Spec (.of k))
    (f : U ⟶ S) [SmoothOfRelativeDimension d q] [IsAffine S] [IrreducibleSpace S]
    [CompactSpace U] [QuasiSeparatedSpace U] (hfib : IsElementaryFibration f)
    (g : U ⟶ Spec (.of k)) (hg : f ≫ q = g) (jU : CompactificationOf (Over.mk g))
    (t : Ext (unitSheaf (X := jU.space) ℓ) ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
      jU.immersion).obj ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))
        (2 * (d + 1)) →+ ZMod ℓ) (ht : Function.Injective t) :
    Ext.IsDualityPerfect (unitSheaf (X := jU.space) ℓ) ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
      jU.immersion).obj ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))
      (2 * (d + 1)) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
      jU.immersion).obj ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj
        (unitSheaf (X := S) ℓ))) := by
  subst hg
  have : Smooth q := SmoothOfRelativeDimension.smooth d q
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian S := ⟨⟩
  have : QuasiCompact q := inferInstance
  have : IsSeparated q := inferInstance
  -- the compactification of `f` given by the elementary fibration
  obtain ⟨Xbar, Z, j, fbar, iZ, hj, hjf, hsm, hproj, -, -, -, -, -, -, -⟩ :=
    hfib.exists_compactification
  have := hsm
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  let jf : CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk (Y := Over.mk fbar) (Over.homMk (U := Over.mk f) j hjf),
      ⟨hj, inferInstanceAs (IsProper fbar)⟩⟩
  have : IsOpenImmersion j := hj
  have : IsSeparated f := by rw [← hjf]; infer_instance
  have : LocallyOfFiniteType f := by rw [← hjf]; infer_instance
  have hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ (1 : WithBot ℕ∞) := fun y =>
    topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 fbar y
  -- a compactification of `S` of dimension `≤ d`, and the relative trace
  obtain ⟨jS, hdimS⟩ := exists_compactification_topologicalKrullDim_le d q
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let ν := (relativeTraceOfElementaryFibration k ℓ hℓ U S q f d hfib jf).some
  obtain ⟨hR0, hR1⟩ := hR hℓ U S q f d hfib jf
  -- the trace on `H^{2d}_c(S)` inducing `t`
  have hN : ((2 * (d + 1) : ℕ) : ℤ) + -2 = ((2 * d : ℕ) : ℤ) := by push_cast; ring
  have hbij := bijective_transferHom_lowerShriekTopTrace ℓ f jf hf ν q jS jU d hdimS hR0 hN
    (by push_cast; ring)
  let eT := AddEquiv.ofBijective _ hbij
  let τU := lowerShriekTrace (f ≫ q) jU ℓ
    ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)) (2 * (d + 1)) t
  have hτU : Function.Injective τU := by
    show Function.Injective (lowerShriekTrace (f ≫ q) jU ℓ _ (2 * (d + 1)) t)
    rw [lowerShriekTrace_eq_comp]
    exact ht.comp (lowerShriekTraceEquiv (f ≫ q) jU ℓ _ (2 * (d + 1))).injective
  let τS := τU.comp eT.symm.toAddMonoidHom
  have hτ : transferTrace (derivedLowerShriek.{u, 0} f jf (ZMod ℓ))
      (lowerShriekCoyonedaCompIso ℓ f q jf jS jU) (lowerShriekTopTraceTheta ℓ f jf hf ν) hN τS =
        τU := by
    ext x
    exact congrArg τU (eT.symm_apply_apply x)
  -- duality on `S` for `Rf_! Λ`, moved to `U`
  have hS := isPerfect_lowerShriek_base ℓ f jf hf ν d q jS hV hℓ hL hIH hdimS hR0 hR1 τS
    (hτU.comp eT.symm.injective)
  have hU := (isPerfect_lowerShriek_comp_iff ℓ f jf hf ν q jS jU hPD hℓ d hfib hN τS).2 hS
  rw [hτ] at hU
  exact isDualityPerfect_of_isPerfect_lowerShriek (f ≫ q) jU ℓ _ (2 * (d + 1)) t _ hU

/-- **The fibration step of Poincaré duality, from its four geometric inputs**: for `ℓ`
invertible in `k`, the cohomological dimension input, relative curve duality, the computation of
`R⁰f_! Λ` and `R¹f_! Λ` for elementary fibrations, and lisse duality from duality at `Λ` give
`Stacks.EtaleCohomology.PoincareDualityFibrationStep ℓ k`: Poincaré duality at `Λ` in dimensions
`≤ d` gives duality on a dense open (an elementary fibration) of every smooth irreducible variety
of dimension `d + 1`. -/
theorem poincareDualityFibrationStep_of_inputs (hℓ : IsUnit (ℓ : k))
    (hV : CohomologicalDimensionInput ℓ k) (hPD : RelativeCurveDualityInput ℓ k)
    (hR : LowerShriekLowDegreeInput ℓ k) (hL : LisseDualityOfUnitInput ℓ k) :
    PoincareDualityFibrationStep ℓ k := by
  intro d hIH W fW _ _ _ jc hdim m t hm ht
  have htinj : Function.Injective t := by
    cases m with
    | zero => exact ht
    | succ m => exact ht.1
  obtain ⟨U, S, q, f, hU, hfib, hq, hS, hSi, hfq⟩ :=
    existsDenseElementaryFibration_of_neighbourhood (existsElementaryFibrationNeighbourhood k) W fW
      (d + 1) (by omega)
  have : SmoothOfRelativeDimension d q := by simpa using hq
  have := hS
  have := hSi
  -- the scheme-level instances
  have : Smooth fW := SmoothOfRelativeDimension.smooth (d + 1) fW
  have : IsSeparated fW := by
    rw [← CompactificationOf.immersion_toBase jc]; infer_instance
  have : QuasiCompact fW := inferInstance
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace U.toScheme := inferInstance
  have : QuasiSeparatedSpace U.toScheme := NoetherianSpace.to_quasiSeparatedSpace
  have : CompactSpace jc.space := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := jc.toBase) Set.univ isOpen_univ
      isCompact_univ⟩
  have : IsLocallyNoetherian jc.space := LocallyOfFiniteType.isLocallyNoetherian jc.toBase
  have : IsNoetherian jc.space := ⟨⟩
  -- the complement of `U` has dimension at most `d`
  obtain ⟨Zc, iC, hiC, hrange⟩ := exists_isClosedImmersion_range_eq ((U : Set W)ᶜ)
    U.isOpen.isClosed_compl
  have := hiC
  have hint : interior ((U : Set W)ᶜ) = ∅ := by
    rw [interior_compl, (U.isOpen.dense hU).closure_eq, Set.compl_univ]
  have : Nonempty W := ⟨hU.some⟩
  have hdimW : topologicalKrullDim W ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (d + 1) fW).le
  have hlt := topologicalKrullDim_lt_of_isClosed_of_interior_eq_empty U.isOpen.isClosed_compl
    hint hdimW iC.isEmbedding.isInducing hrange.le
  have hdimZ : topologicalKrullDim Zc ≤ (d : WithBot ℕ∞) := by
    rcases hZ : topologicalKrullDim Zc with _ | y
    · exact bot_le
    · rw [hZ] at hlt
      have h0 : (y : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) := hlt
      have h1 : y < (d : ℕ∞) + 1 := by exact_mod_cast WithBot.coe_lt_coe.1 h0
      exact WithBot.coe_le_coe.2 (Order.le_of_lt_add_one h1)
  have hiU : Set.range U.ι.base = (Set.range iC.base)ᶜ := by
    rw [hrange, compl_compl, Scheme.Opens.range_ι]
  have hbij := bijective_ext_extensionByZero_counit_of_closed jc U iC hiU d hdimZ
    (unitSheaf (X := W) ℓ) (2 * (d + 1)) (by omega)
  -- `(j ∘ U)_! f⁻¹ Λ_S ≅ j_! U_! U⁻¹ Λ_W`
  let eU : unitSheaf (X := U.toScheme) ℓ ≅
      (etaleModuleRestriction.{u, 0} (ZMod ℓ) U.ι).obj (unitSheaf (X := W) ℓ) :=
    ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) U.ι).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).symm ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod ℓ) U.ι).app (unitSheaf (X := W) ℓ)
  let eE : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).obj
        (unitSheaf (X := U.toScheme) ℓ) ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj
          (unitSheaf (X := W) ℓ)) :=
    (etaleModuleExtensionByZeroCompIso (ZMod ℓ) U.ι jc.immersion).app _ ≪≫
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).mapIso
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) U.ι).mapIso eU)
  let ψ : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)) ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj
          (unitSheaf (X := W) ℓ)) :=
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).mapIso
      ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) f).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) ≪≫ eE
  -- the change of dualizing object along the counit `j_! U_! U⁻¹ Λ_W → j_! Λ_W`
  let φ := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) U.ι).counit.app (unitSheaf (X := W) ℓ))
  have hφ := bijective_comp_mk₀_extensionByZero_counit ℓ fW jc U (unitSheaf (X := W) ℓ)
  let t₁ := Ext.pullbackTrace t φ
  let t₂ := Ext.pullbackTrace t₁ ψ.hom
  have hψ := fun n : ℕ => Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
    (X := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj
        (unitSheaf (X := W) ℓ))) ψ.hom n
  have ht₂ : Function.Injective t₂ := fun _ _ hab =>
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso ψ.hom (2 * (d + 1))).1
      (hbij.1 (htinj hab))
  have hcore := isDualityPerfect_lowerShriek_fibration ℓ hV hPD hR hL hℓ d hIH q f hfib
    (U.ι ≫ fW) hfq (jc.restrictOpen U.ι) t₂ ht₂
  refine ⟨U, U.isOpen.dense hU, ?_, fun q' hq' => ?_⟩
  · have h₁ : Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))
        (2 * (d + 1)) t₂ ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj
            (unitSheaf (X := W) ℓ))) :=
      Ext.isDualityPerfect_of_iso ψ hcore
    exact (Ext.isDualityPerfect_pullbackTrace_iff t φ _ hφ).1
      ((Ext.isDualityPerfect_pullbackTrace_iff t₁ ψ.hom _ hψ).1 h₁)
  · -- `Ext^q(j_! U_! Λ, j_! Λ_W) = Ext^q_U(Λ, Λ) = 0` for `q > 2d + 2`
    have hdimU : topologicalKrullDim U.toScheme ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
      (topologicalKrullDim_le_of_etale U.ι).trans hdimW
    have := hV U.toScheme (U.ι ≫ fW) (d + 1) hdimU (unitSheaf (X := U.toScheme) ℓ)
      (unitSheaf (X := U.toScheme) ℓ) (isFiniteTypeLocallyConstant_unitSheaf ℓ U.toScheme) q' hq'
    have : Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
        (U.ι ≫ jc.immersion)).obj (unitSheaf (X := U.toScheme) ℓ))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).obj
          (unitSheaf (X := U.toScheme) ℓ)) q') :=
      (bijective_mapExactFunctor_extensionByZero (U.ι ≫ fW) (jc.restrictOpen U.ι) ℓ
        (unitSheaf (X := U.toScheme) ℓ) (unitSheaf (X := U.toScheme) ℓ) q').surjective.subsingleton
    have : Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj (unitSheaf (X := W) ℓ)))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj
            (unitSheaf (X := W) ℓ))) q') :=
      Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source eE q'
        (Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target eE q' inferInstance)
    exact (hφ q').surjective.subsingleton

/-- **Poincaré duality on a dense open, from the four geometric inputs**: for `ℓ` invertible in
`k`, `Stacks.EtaleCohomology.PoincareDualityCore ℓ k` follows from the inputs of the fibration
step (`Stacks.EtaleCohomology.poincareDualityFibrationStep_of_inputs`) by strong induction on the
dimension (`Stacks.EtaleCohomology.poincareDualityCore_of_fibrationStep`). -/
theorem poincareDualityCore_of_inputs (hℓ : IsUnit (ℓ : k))
    (hV : CohomologicalDimensionInput ℓ k) (hPD : RelativeCurveDualityInput ℓ k)
    (hR : LowerShriekLowDegreeInput ℓ k) (hL : LisseDualityOfUnitInput ℓ k) :
    PoincareDualityCore ℓ k :=
  poincareDualityCore_of_fibrationStep ℓ hℓ
    (poincareDualityFibrationStep_of_inputs ℓ hℓ hV hPD hR hL)

end Stacks.EtaleCohomology

end
