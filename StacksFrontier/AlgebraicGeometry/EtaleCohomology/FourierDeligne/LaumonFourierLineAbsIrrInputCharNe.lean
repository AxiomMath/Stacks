module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily

/-!
# L6 for the Fourier family at fixed `a`, for `ℓ ≠ p`

`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'` is
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput` for `ℓ` different from the characteristic
`p` of `k'` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece L6; Kedlaya, *Fourier
transforms and p-adic Weil II*, §6.4): the absolute irreducibility of the representation `τ`
attached to `R¹pr₂!(pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t))` on an open of the `t`-line. The Fourier
transform needs `p` invertible in the coefficients, and every consumer in the proof of Weil II
works with `ℓ ≠ p`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Polynomial

universe u

namespace Stacks.EtaleCohomology

/-- **L6 for `ℓ ≠ p`: absolute irreducibility of the Fourier family at fixed `a` on its lisse
locus** ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and
p-adic Weil II*, §6.4). This is `Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput` with the
hypothesis `ℓ ≠ p` on the prime `ℓ` and the characteristic `p` of the finite field `k'`. -/
public def LaumonFourierLineAbsIrrInput' : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
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
    (k' : Type u) [Field k'] [Fintype k'] (p : ℕ) [Fact p.Prime] [CharP k' p], ℓ ≠ p →
    ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E), ψ' ≠ 1 →
    (∃ ζ : E, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (a : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (p₁ : (finiteEtaleFiberFunctor (z.map (laumonFamilyPr₁ k'))).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial k') (Polynomial.C a * Polynomial.X ^ n))),
    (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra E K] (W : Submodule K (Fin m → K)),
      (∀ g, ∀ v ∈ W, (characterTwist σ₁ (Stacks.ArtinSchreier.artinSchreierCharacter k'
        (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k'))
          p₁) g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
      (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
    IsOpenImmersion (B.inclusion.map jV') →
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    ∀ (xV : GeometricPoint V'.1) {r : ℕ}
      (ρ : EtaleFundamentalGroup V'.1 xV →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
      (φ : (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b ψ' n a z p₀ σ₁ hσ₁ jU g'
          jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V' xV ρ hρ)
      (ψ₀ : LAdicSheaf.representationSheaf B V' xV ρ hρ ⟶
        (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b ψ' n a z p₀ σ₁ hσ₁ jU g'
          jg').toLAdicSheaf) (N : ℕ)
      (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ : ℕ}
      (τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) E)
      (P : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Q : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ]),
      P * Q = 1 →
      (∀ e' : E, Q * isogenyCoefficientAlgHom B V' xV
        (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b ψ' n a z p₀ σ₁ hσ₁ jU g' jg')
        ρ hρ φ ψ₀ N E hφψ hψφ (algebraMap_conjIntegralSubring_algebraMap _ _) e' * P =
          restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e')) →
      (∀ g : EtaleFundamentalGroup V'.1 xV,
        haveI := compactSpace_etaleFundamentalGroup V'.1 xV
        Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val) →
      Q * P = 1 →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra E K] (W : Submodule K (Fin mτ → K)),
        (∀ g, ∀ v ∈ W, (τ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

end Stacks.EtaleCohomology

end
