module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientHigherDirectImageStalkLinearIsoProof

/-!
# Purity of `τ` in Laumon's degeneration from the fibres of the family

In Laumon's degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece
P4 of `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`) the purity of the representation `τ`
of `G_V = R¹g'_!(K|_{U'})` (`Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep`) has
two inputs: `E`-linear proper base change at the stalks (b) and the identification of the fibres
of the family (c). Input (b) holds
(`Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput`), so the purity of `τ`
depends only on (c) (`Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep'`).

## Main results

* `Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep'`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **Purity of the representation `τ` of `G_V = R¹g'_!(K|_{U'})`** (piece P4 of
`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`, [Tag
03VH](https://stacks.math.columbia.edu/tag/03VH)), in the setting of
`Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep`: if the fibres of the two-parameter
family are pure of weight `β + 1` off `D = 0` (`Stacks.EtaleCohomology.LaumonFibrePure`), then `τ`
is `ι'`-pure of weight `β + 1`. The only input is the identification of the fibres of the family
(`Stacks.EtaleCohomology.LaumonFamilyFibreLinearInput`); `E`-linear proper base change at the
stalks is `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput`. -/
public theorem laumonFamily_isPure_restrictScalarsRep'
    (hc : LaumonFamilyFibreLinearInput.{u})
    (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Finite k] (U : B.Scheme) [ConnectedSpace U.1] [IsNoetherian U.1]
    (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e] (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (ι' : E →+* ℂ) (β : ℤ) (ψ : AddChar k E) (n₀ : ℕ) (D : MvPolynomial (Fin 2) k)
    (hfib : LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n₀ D)
    (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (c : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (f : Polynomial k')
    (hDf : MvPolynomial.aeval ![(Polynomial.X : Polynomial k'), Polynomial.C c * Polynomial.X] D ∣
      f)
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
    (hjV' : IsOpenImmersion (B.inclusion.map jV'))
    (hrange : Set.range (B.inclusion.map jV') ⊆
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial k'))))
    (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV'))
    (fV : V'.1 ⟶ Spec (.of k')) [LocallyOfFiniteType fV] (p n' : ℕ) [Fact p.Prime] [CharP k' p]
    (hcard' : Fintype.card k' = p ^ n') (xV : GeometricPoint V'.1) {r : ℕ}
    (ρ : EtaleFundamentalGroup V'.1 xV →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V' xV ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B V' xV ρ hρ ⟶
      (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g'
          jg').toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ : ℕ}
    (τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) E)
    (P : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Q : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ])
    (hPQ : P * Q = 1)
    (hα : ∀ e' : E, Q * isogenyCoefficientAlgHom B V' xV
      (laumonFamilyRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ c z p₀ _ hσ₁ jU g' jg')
      ρ hρ φ ψ₀ N E hφψ hψφ (algebraMap_conjIntegralSubring_algebraMap _ _) e' * P =
        restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e'))
    (hτ : ∀ g : EtaleFundamentalGroup V'.1 xV,
      haveI := compactSpace_etaleFundamentalGroup V'.1 xV
      Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val)
    (hQP : Q * P = 1) :
    ∀ (v : closedPoints V'.1) (z' : ℂ),
      ((τ (geometricFrobeniusFamily fV xV v)).val.charpoly.map ι').IsRoot z' →
      ‖z'‖ = ((p ^ n' : ℕ) : ℝ) ^ (((residueDegree fV v.1 : ℤ) * ((β + 1 : ℤ) : ℝ) : ℝ) / 2) :=
  laumonFamily_isPure_restrictScalarsRep coefficientHigherDirectImageStalkLinearInput hc B ℓ k U e
    x E b σ ι' β ψ n₀ D hfib k' c hS hL z hz p₀ hσ₁ f hDf V' U' jV' jU g' jg' hjV' hrange hpb fV p
    n' hcard' xV ρ hρ φ ψ₀ N hφψ hψφ τ P Q hPQ hα hτ hQP

end Stacks.EtaleCohomology

end
