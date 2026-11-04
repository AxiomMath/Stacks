module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLevelIsogenyCoreAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierKernelTwistModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LowerShriekRestrictScalarsIsogeny
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Fourier side of Laumon's level isogeny

This file proves `Stacks.EtaleCohomology.LaumonFourierFamilyLevelIsogenyInput`, input (B) of
`Stacks.EtaleCohomology.laumonFourierLevelIsogenyCoreInput_of_levelIsogenies` in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): for an `O_E`-model `σ_O` of
`σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` and every level `N'`, with `Λ = O_E/ℓ^{N'+1}` and `ψ_N = ψ' mod ℓ^{N'+1}`
(a nontrivial character: its values sum to zero), there is an `ℓᶜ`-isogeny, `c` independent of
`N'`, between `j_{V'}⁻¹ H¹(Φ_{ψ_N}(ℱ_{σ_O mod ℓ^{N'+1}}))` and `j_{V'}⁻¹ R¹pr₂!` of the level `N'`
of the Fourier family sheaf `K`, commuting exactly with the integral part of `E`. The chain is:

* `H¹ Φ(ℱ_σ) ≅ R¹pr₂!(ℱ_{pr₁^* σ ⊗ ψ(-χ_{x t})})` (pieces P2, P2b,
  `Stacks.EtaleCohomology.nonempty_homology_fourierTransform_iso_lowerShriekHomology_lisse`), the
  twist of `σ_O mod ℓ^{N'+1}` being the reduction of the `O_E`-model
  `Stacks.EtaleCohomology.laumonFourierTwistModel`;
* that model is conjugate over `E` to the Fourier family representation by the matrix `T₁` of
  `σ_O` (`Stacks.EtaleCohomology.map_laumonFourierTwistModel`), so integral intertwiners with the
  integral model of `Res_b K` exist
  (`Stacks.EtaleCohomology.exists_integralModel_intertwiner_of_padicIntegerRing_model`), giving
  level isogenies with the levels of `K`
  (`Stacks.EtaleCohomology.exists_levelIsogeny_lisseEtaleSheaf_padicTower`);
* `R¹pr₂!`, `j_{V'}⁻¹` and the restriction of scalars to `ℤ_ℓ` carry them along
  (`Stacks.EtaleCohomology.exists_isogeny_restrictScalars_inverseImage_lowerShriekHomology`).

## Main results

* `Stacks.EtaleCohomology.sum_compAddChar_padicIntegerRingAddChar`.
* `Stacks.EtaleCohomology.laumonFourierFamilyLevelIsogenyInput`.

## Implementation notes

The Fourier transform and `R¹pr₂!` live in the standard model `HasDerivedCategory.standard` of
the derived category, which is therefore a local instance in the last section.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Polynomial

universe u

namespace Stacks.EtaleCohomology

section Sum

attribute [local instance] padicIntAlgebraOfRat

/-- **A nontrivial additive character with values in `E`, reduced modulo an ideal of `O_E`, has
values summing to zero.** -/
@[sga "4½ Sommes_trig 2.7" "more general"]
theorem sum_compAddChar_padicIntegerRingAddChar {k : Type*} [AddCommGroup k] [Fintype k] {ℓ : ℕ}
    [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] (ψ' : AddChar k E) (hψ' : ψ' ≠ 1)
    (I : Ideal (integralClosure ℤ_[ℓ] E)) :
    ∑ x, ((Ideal.Quotient.mk I).toMonoidHom.compAddChar (padicIntegerRingAddChar ψ')) x = 0 := by
  have h : ∑ x, padicIntegerRingAddChar (ℓ := ℓ) ψ' x = 0 := by
    apply Subtype.val_injective
    change algebraMap (integralClosure ℤ_[ℓ] E) E (∑ x, padicIntegerRingAddChar (ℓ := ℓ) ψ' x) =
      algebraMap (integralClosure ℤ_[ℓ] E) E 0
    rw [map_sum, map_zero]
    simp only [algebraMap_padicIntegerRingAddChar]
    exact AddChar.sum_eq_zero_of_ne_one hψ'
  change ∑ x, Ideal.Quotient.mk I (padicIntegerRingAddChar ψ' x) = 0
  rw [← map_sum, h, map_zero]

end Sum

section Assembly

attribute [local instance] padicIntAlgebraOfRat HasDerivedCategory.standard

/-- **Input (B), the Fourier side of Laumon's level isogeny, holds**: at every level `N'`,
`j_{V'}⁻¹ H¹(Φ_{ψ_N}(ℱ_{σ_O mod ℓ^{N'+1}}))` and `j_{V'}⁻¹ R¹pr₂!` of the level `N'` of the Fourier
family sheaf are `ℓᶜ`-isogenous, `c` independent of `N'`, compatibly with the integral part of
`E`. -/
theorem laumonFourierFamilyLevelIsogenyInput : LaumonFourierFamilyLevelIsogenyInput.{u} := by
  intro B ℓ _ _ _ _ k' _ _ p _ _ hℓp E _ _ _ d b ψ' hψ' hζ n a hS hL z p₀ m σ₁ hσ₁ p₁ σO T₁ hT₁
    hσO jg V' jV'
  have : ConnectedSpace (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial (Polynomial k')))))
  have := compactSpace_etaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z
  have pK := (Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (Polynomial.C Polynomial.X * Polynomial.X : Polynomial (Polynomial k')) z).some
  have p₀' := (Stacks.ArtinSchreier.nonempty_finiteEtaleFiber_cover k'
    (Polynomial.X : Polynomial k') (affineLineOrigin k')).some
  have hj := hasCompactification_of_compactSpace_quasiSeparatedSpace
    (Stacks.ArtinSchreier.affineLineStructureMap k')
  have hσK := continuous_restrictScalarsRep_laumonFourierFamilyRep k' b ψ' n a z p₀ σ₁ hσ₁
  have hτO := isOpen_ker_map_laumonFourierTwistModel k' ψ' z pK σO hσO
  choose c A A' hA hA' hAA' hA'A hAeq using
    exists_integralModel_intertwiner_of_padicIntegerRing_model b
      (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁) hσK (laumonFourierTwistModel k' ψ' z pK σO) T₁
      (map_laumonFourierTwistModel k' ψ' z pK σO n a p₀ σ₁ p₁ T₁ hT₁)
  refine ⟨c, 0, fun N' => ?_⟩
  choose w w' hww' hw'w hweq using exists_levelIsogeny_lisseEtaleSheaf_padicTower B
    (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) z
    (padicIntegerRingBasisOf b) (laumonFourierTwistModel k' ψ' z pK σO) hτO
    (integralModel (restrictScalarsRep b (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁)) hσK)
    (continuous_integralModel _ hσK) A hA A' hA' c hAA' hA'A N'
  have hβ := nonempty_homology_fourierTransform_iso_lowerShriekHomology_lisse k'
    (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
    ((Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).toMonoidHom.compAddChar
      (padicIntegerRingAddChar ψ')) B p₀' hj.choose hS hL jg z pK
    ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp σO) (hσO (N' + 1))
    ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp
        (laumonFourierTwistModel k' ψ' z pK σO)) (hτO (N' + 1))
    (map_comp_laumonFourierTwistModel k' ψ' z pK σO (N' + 1)).symm
  choose h h' hhh' hh'h heq using exists_isogeny_restrictScalars_inverseImage_lowerShriekHomology
    ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
      (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)))
    (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg (B.inclusion.map jV') 1 hβ.some w w'
    (ℓ ^ c) hww' hw'w
  refine ⟨_, sum_compAddChar_padicIntegerRingAddChar ψ' hψ' _, p₀', hj.choose, h, h', hhh', hh'h,
    fun o o' ho => ?_⟩
  have hM := fun g => conjIntegralLift_mul_integralModel B
    (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) z
    (restrictScalarsRep b (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁)) hσK
    (restrictScalarsScalarAlgHom b m) (restrictScalarsScalarAlgHom_commute b _) o g
  have hw := hweq o' _ hM (hAeq o o' ho).1 (hAeq o o' ho).2
  have he := heq _ _ hw.1 hw.2
  exact ⟨congrArg (fun t => ℓ ^ 0 • t) he.1, congrArg (fun t => ℓ ^ 0 • t) he.2⟩

end Assembly

end Stacks.EtaleCohomology

end
