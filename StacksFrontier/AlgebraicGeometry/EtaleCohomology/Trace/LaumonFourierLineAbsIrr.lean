module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily

/-!
# Absolute irreducibility of the Fourier family at fixed `a` on the lisse locus

`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput` is the absolute irreducibility of the Fourier
transform in Laumon's argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya,
*Fourier transforms and p-adic Weil II*, §6.4). Over a finite field `k'`, for `a ∈ k'`, a
nontrivial additive character `ψ'` and a representation `σ₁` of `π₁(𝔸¹_{k'})` such that
`σ₁ ⊗ χ_{a xⁿ}` is absolutely irreducible, the representation `τ` of `π₁(V)` attached (up to
isogeny, `E`-compatibly) to `G|_V = R¹pr₂!(pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t))|_V` over an open `V` of
the `t`-line is absolutely irreducible.

The absolute irreducibility is in the form of
`Stacks.EtaleCohomology.LaumonAffineLineLinearAbsIrrInput`: no nonzero proper subspace over any
algebraically closed field `K` over `E` is stable. This is the absolute irreducibility of the
Fourier transform of `σ := σ₁ ⊗ χ_{a xⁿ}` over `k'`, through
`L_ψ'(a xⁿ) ⊗ L_ψ'(x t) ≅ L_ψ'(a xⁿ + x t)`. When `σ₁ ⊗ χ_{a xⁿ}` is geometrically an
Artin–Schreier character of a linear form, `R¹pr₂!` vanishes and `τ` has dimension `0`, so no
non-degeneracy hypothesis is needed.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Polynomial

universe u

namespace Stacks.EtaleCohomology

/-- **Absolute irreducibility of the Fourier family at fixed `a` on its lisse locus**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, §6.4). Let `k'` be a finite field of characteristic `p`, `E` a finite extension of
`ℚ_ℓ` containing a primitive `p`-th root of unity, `ψ' ≠ 1` an additive character of `k'` with
values in `E`, `n ∈ ℕ`, `a ∈ k'`, and `σ₁ : π₁(𝔸¹_{k'}, x̄₁) → GL_m(E)` with `Res_b σ₁` continuous
such that `σ₁ ⊗ χ_{a xⁿ}` (the twist by the Artin–Schreier character of `a xⁿ`) is absolutely
irreducible. Let `V'` be a connected open of the `t`-line, `g' : U' → V'` the restriction of
`pr₂ : Spec k'[x][t] → Spec k'[t]`, and `τ : π₁(V', x̄_V) → GL(E)` attached to
`G_V = R¹g'_!(pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t))|_{U'}`
(`Stacks.EtaleCohomology.laumonFourierRestrictedHigherDirectImage`) through an isogeny with the
sheaf of a `ℚ_ℓ`-representation `ρ`, compatibly with `E` (the data of
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`). Then `τ` is absolutely
irreducible. -/
public def LaumonFourierLineAbsIrrInput : Prop :=
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
    (k' : Type u) [Field k'] [Fintype k'] (p : ℕ) [Fact p.Prime] [CharP k' p]
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
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
          p₁) g).val.map
          (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
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
