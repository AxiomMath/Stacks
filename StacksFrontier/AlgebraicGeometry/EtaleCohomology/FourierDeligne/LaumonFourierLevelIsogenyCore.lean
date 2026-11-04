module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonLatticeLevelDichotomyOfIsogeny

/-!
# The level isogeny of Laumon's comparison over the integers of `E`

`Stacks.EtaleCohomology.LaumonFourierLevelIsogenyInput` (the sheaf chain of the comparison in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) asks, for every finite
extension `E''` of `E` inside `Ē`, for a level isogeny over `O'' = integralClosure ℤ_ℓ E''`. This
file states its core case `E'' = E`: the coefficients are `O_E = integralClosure ℤ_ℓ E` and the
models `σ_E` of `σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` and `τ_E` of `τ` are over `O_E`. The general case is
deduced from it by restriction of scalars along an `O_E`-basis of `O''`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLevelIsogenyCoreInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
  Polynomial Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] padicIntAlgebraOfRat HasDerivedCategory.standard

/-- **The level isogeny over the integers of `E`** (the core case `E'' = E` of
`Stacks.EtaleCohomology.LaumonFourierLevelIsogenyInput`). In the situation of
`Stacks.EtaleCohomology.LaumonLatticeLevelDichotomyInput`, for every `O_E`-model `σ_E` of
`σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` and every `O_E`-model `τ_E` of `τ` (`O_E = integralClosure ℤ_ℓ E`, with
open kernels at every level), there is an exponent `c`, INDEPENDENT of the level `N'`, such that at
every level `N'`, for `Λ = O_E/ℓ^{N'+1}`, a nontrivial additive character `ψ_N : k' → Λ` and the
Fourier transform `Φ` attached to it, the restriction to `V'` of `H¹(Φ(ℱ_{σ_E mod ℓ^{N'+1}}))` and
the lisse sheaf of `τ_E mod ℓ^{N'+1}` on `V'` are `ℓᶜ`-isogenous as sheaves of `Λ`-modules. The
Fourier transform lives in the standard model of the derived category. -/
def LaumonFourierLevelIsogenyCoreInput : Prop :=
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
      ∀ (σO : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
          GL (Fin m) (integralClosure ℤ_[ℓ] E)) (T₁ : GL (Fin m) E),
        (∀ g, (σO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) =
          (T₁⁻¹ : GL (Fin m) E).val * (characterTwist σ₁
            (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
              (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k')) p₁) g).val *
            T₁.val) →
        ∀ (hσO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
            (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (k)}))).comp σO).ker :
            Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
          (τO : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) (integralClosure ℤ_[ℓ] E))
          (T : GL (Fin mτ) E),
        (∀ g, (τO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) =
          (T⁻¹ : GL (Fin mτ) E).val * (τ g).val * T.val) →
        ∀ (hτO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
            (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (k)}))).comp τO).ker :
            Set (EtaleFundamentalGroup V'.1 xV))),
        ∃ c : ℕ, ∀ N' : ℕ,
          ∃ (ψN : AddChar k'
              (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))
            (_ : ∑ x, ψN x = 0)
            (p₀' : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
              (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
            (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
            (f : (etaleModuleInverseImage.{u, 0}
                (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E ⧸
                      Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k')) (integralClosure ℤ_[ℓ] E ⧸
                          Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E ⧸
                              Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp σO)
                            (hσO (N' + 1))))))) ⟶
              (lisseEtaleSheaf B V' xV (integralClosure ℤ_[ℓ] E ⧸
                  Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E ⧸
                    Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                  ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                    (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
                  (hτO (N' + 1))))
            (g : (lisseEtaleSheaf B V' xV (integralClosure ℤ_[ℓ] E ⧸
                  Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E ⧸
                    Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                  ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                    (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
                  (hτO (N' + 1))) ⟶
              (etaleModuleInverseImage.{u, 0}
                (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E ⧸
                      Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k')) (integralClosure ℤ_[ℓ] E ⧸
                          Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E ⧸
                              Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp σO)
                            (hσO (N' + 1)))))))),
            f ≫ g = ℓ ^ c • 𝟙 _ ∧ g ≫ f = ℓ ^ c • 𝟙 _

end Stacks.EtaleCohomology

end
