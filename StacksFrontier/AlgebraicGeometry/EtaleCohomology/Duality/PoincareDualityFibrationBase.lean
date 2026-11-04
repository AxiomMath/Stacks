module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekFibrationTopDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.HomologicalDualityZModExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCompactSupportVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# Poincaré duality on the base of an elementary fibration, for `Rf_! Λ`

Let `k` be algebraically closed, `ℓ` a prime invertible in `k`, `Λ = ℤ/ℓ`, and `f : U → S` an
elementary fibration over `S` affine, irreducible and smooth of dimension `d` over `k`, with a
compactification `j_S : S → S̄` of dimension at most `d`. Write `K = Rf_!(f⁻¹ Λ_S)`. If
`R⁰f_! Λ = 0` and `R¹f_! Λ` is locally constant of finite type, and Poincaré duality at `Λ` holds
in dimensions `≤ d` (`Stacks.EtaleCohomology.UnitPoincareDualityUpTo`), then for every injective
trace `t` on `H^{2d}_c(S) = Ext^{2d}_{S̄}(Λ, j_{S!} Λ_S)` duality holds on `S` for the complex `K`:
the pairing `H^i_c(S, K) × Hom(K, Λ_S[j]) → H^{2d}_c(S) → Λ` is perfect for all integers
`i + j = 2d` (`Stacks.EtaleCohomology.isPerfect_lowerShriek_base`).

The proof is the five lemma on the truncation triangle `R¹[-1] → K → R²[-2] → R¹[0]`
(`Stacks.HomologicalDuality.isPerfect_of_isGE_of_isLE`): at `R² ≅ Λ_S` (the relative trace `ν`)
duality is the induction hypothesis, at the lisse sheaf `R¹` it is lisse duality on `S`
(`Stacks.EtaleCohomology.LisseDualityOfUnitInput`), and in both cases the groups above the top
degree vanish: `H^q_c(S, -) = 0` for `q > 2d`
([Tag 095U](https://stacks.math.columbia.edu/tag/095U) on `S̄`) and `Ext^q_S(F, Λ) = 0` for
`q > 2d`, `F` lisse
(`Stacks.EtaleCohomology.CohomologicalDimensionInput`). The traces take values in the field `ℤ/ℓ`,
which has the extension property needed by the five lemma, `ℓ` killing `Λ_S`.

This is the base step of the fibration step of Poincaré duality, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.nsmul_id_single_unitSheaf_eq_zero`.
* `Stacks.EtaleCohomology.isPerfect_lowerShriek_base_of_trace`.
* `Stacks.EtaleCohomology.isPerfect_lowerShriek_base`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor HomologicalDuality

attribute [local instance] HasDerivedCategory.standard

/-- **`ℓ` kills `Λ_S[0]` in `D⁺(S, ℤ/ℓ)`.** -/
theorem nsmul_id_single_unitSheaf_eq_zero (ℓ : ℕ) (S : Scheme.{u}) :
    ℓ • 𝟙 ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul,
    nsmul_id_etaleModules_zmod, CategoryTheory.Functor.map_zero]

variable {k : Type u} [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] {U S : Scheme.{u}}
  (f : U ⟶ S) (jf : CompactificationOf (Over.mk f))
  (hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ 1)
  (ν : etaleModuleInverseImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod ℓ) S))
  (d : ℕ) (q : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension d q]
  [TopologicalSpace.NoetherianSpace S] [IrreducibleSpace S] [LocallyOfFiniteType q] [IsSeparated q]
  [CompactSpace S] (jS : CompactificationOf (Over.mk q))

include hf ν in
/-- **Duality on `S` for `Rf_! Λ`, for the trace induced by an injective trace on `H^{2d}_c(S)`.**
With `R⁰f_! Λ = 0`, `R¹f_! Λ` lisse and Poincaré duality at `Λ` in dimensions `≤ d`, duality for
`Hom(Λ_k[0], Rq_! -)` holds at `Rf_!(f⁻¹ Λ_S[0])`, with dualizing object `Λ_S[0]`, in degree `2d`,
for the trace `lowerShriekTrace t` of an injective trace `t` on `Ext^{2d}_{S̄}(Λ, j_{S!} Λ_S)`. -/
theorem isPerfect_lowerShriek_base_of_trace (hV : CohomologicalDimensionInput ℓ k)
    (hℓ : IsUnit (ℓ : k)) (hL : LisseDualityOfUnitInput ℓ k) (hIH : UnitPoincareDualityUpTo ℓ k d)
    (hdimS : topologicalKrullDim jS.space ≤ d)
    (hR0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))))
    (hR1 : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))))
    (t : Ext (unitSheaf (X := jS.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj (unitSheaf (X := S) ℓ))
        (2 * d) →+ ZMod ℓ) (ht : Function.Injective t) :
    IsPerfect (derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ))))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) ((2 * d : ℕ) : ℤ)
      (lowerShriekTrace q jS ℓ (unitSheaf (X := S) ℓ) (2 * d) t)
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))) := by
  let K := (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))
  have : Nonempty S := (‹IrreducibleSpace S›).toNonempty
  have hdim : topologicalKrullDim S ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d q).le
  have := isGE_one_lowerShriek_inverseImage_single ℓ f jf hR0
  have : (DerivedCategory.Plus.ι.obj K).IsLE (1 + 1) :=
    isLE_derivedLowerShriek_inverseImage_single f jf ℓ hf _
  have hO : ∀ F : EtaleModules.{u, 0} (ZMod ℓ) S, ∀ q' : ℕ, 2 * d < q' →
      Subsingleton (Ext (unitSheaf (X := jS.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj F) q') :=
    fun F q' hq' => subsingleton_ext_unitSheaf_of_proper jS.toBase d hdimS _ q' hq'
  obtain ⟨hIH₁, hIH₂⟩ := hIH d le_rfl S q jS hdimS t ht
  refine isPerfect_of_isGE_of_isLE K 1
    (fun M j Hs φ => exists_extend_zmod_of_nsmul_id_eq_zero ℓ
      (nsmul_id_single_unitSheaf_eq_zero ℓ S) M j Hs φ) ?_ ?_
  · refine isPerfect_lowerShriek_of_isDualityPerfect q jS ℓ (unitSheaf (X := S) ℓ) (2 * d) t
      ((DerivedCategory.Plus.homologyFunctor _ 1).obj K)
      (hL hℓ d hIH S q jS hdimS t ht _ hR1) (hO _) (fun q' hq' => ?_)
    have := hV S q d hdim ((DerivedCategory.Plus.homologyFunctor _ 1).obj K)
      (unitSheaf (X := S) ℓ) hR1 q' hq'
    exact (Equiv.ofBijective _ (bijective_mapExactFunctor_extensionByZero q jS ℓ
      (unitSheaf (X := S) ℓ) ((DerivedCategory.Plus.homologyFunctor _ 1).obj K)
      q')).symm.subsingleton
  · exact isPerfect_of_iso ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (ν.app (unitSheaf (X := S) ℓ)).symm)
      (isPerfect_lowerShriek_of_isDualityPerfect q jS ℓ (unitSheaf (X := S) ℓ) (2 * d) t
        (unitSheaf (X := S) ℓ) hIH₁ (hO _) hIH₂)

include hf ν in
/-- **Duality on `S` for `Rf_! Λ`, for every injective trace on `H^{2d}_c(S)` over the base
field.** With `R⁰f_! Λ = 0`, `R¹f_! Λ` lisse and Poincaré duality at `Λ` in dimensions `≤ d`, for
every injective trace `τ` on `Hom(Λ_k[0], Rq_!(Λ_S[0])[2d]) = H^{2d}_c(S)`, duality for
`Hom(Λ_k[0], Rq_! -)` holds at `Rf_!(f⁻¹ Λ_S[0])`, with dualizing object `Λ_S[0]`, in degree
`2d`. -/
theorem isPerfect_lowerShriek_base (hV : CohomologicalDimensionInput ℓ k)
    (hℓ : IsUnit (ℓ : k)) (hL : LisseDualityOfUnitInput ℓ k) (hIH : UnitPoincareDualityUpTo ℓ k d)
    (hdimS : topologicalKrullDim jS.space ≤ d)
    (hR0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))))
    (hR1 : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))))
    (τ : (derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)))).obj
      (((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦((2 * d : ℕ) : ℤ)⟧) →+
        ZMod ℓ) (hτ : Function.Injective τ) :
    IsPerfect (derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ))))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) ((2 * d : ℕ) : ℤ) τ
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))) := by
  have h := isPerfect_lowerShriek_base_of_trace ℓ f jf hf ν d q jS hV hℓ hL hIH hdimS hR0 hR1
    (τ.comp (lowerShriekTraceEquiv q jS ℓ (unitSheaf (X := S) ℓ) (2 * d)).symm.toAddMonoidHom)
    (hτ.comp (lowerShriekTraceEquiv q jS ℓ (unitSheaf (X := S) ℓ) (2 * d)).symm.injective)
  rwa [lowerShriekTrace_comp_symm] at h

end Stacks.EtaleCohomology

end
