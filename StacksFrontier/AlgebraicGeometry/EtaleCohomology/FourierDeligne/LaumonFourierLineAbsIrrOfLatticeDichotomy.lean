module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLineAbsIrrInputCharNe
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LatticeLevelDichotomyContradiction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AbsIrrOfFiniteExtension

/-!
# L6 for the Fourier family from the level dichotomy of a lattice of `τ ⊗ E'`

`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'` (piece L6 of Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) asks for the absolute irreducibility of
the representation `τ` attached to the Fourier family. By
`Stacks.EtaleCohomology.eq_bot_or_eq_top_of_forall_finiteDimensional` it suffices to show that
`τ ⊗ E'` is irreducible for every finite extension `E'` of `E` inside an algebraic closure. For
such `E'`, `Stacks.EtaleCohomology.LaumonLatticeLevelDichotomyInput` provides a valuation ring
`O ⊆ E'` with fraction field `E'`, an `O`-integral conjugate `τ_O = T⁻¹ τ T` of `τ`, and a level
`N` with an exponent `b ≤ N` at which the reduction of `τ_O` modulo `ℓ^{N+1}` satisfies the level
dichotomy. A `τ`-stable subspace `0 ≠ W ≠ E'^{m_τ}` would give the `τ_O`-stable `T⁻¹ W`,
contradicting the dichotomy
(`Stacks.EtaleCohomology.eq_bot_or_eq_top_of_continuousModuleLevelDichotomy`). The level dichotomy
itself comes from the dichotomy for the Fourier transform (S6) through the isogenies between the
levels of `τ_O` and the monodromy of `H¹Φ` of the levels of `σ₁`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonLatticeLevelDichotomyInput`.

## Main results

* `Stacks.EtaleCohomology.laumonFourierLineAbsIrrInput'_of_latticeLevelDichotomy`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Polynomial

universe u

namespace Stacks.EtaleCohomology

/-- **The level dichotomy of a lattice of `τ ⊗ E'`**, in the situation of
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'`: for every finite extension `E'` of `E`
inside `Ē` there are a valuation ring `O ⊆ E'` with fraction field `E'` in which `ℓ` is a nonzero
non-unit and every nonzero element divides a power of `ℓ`, an `O`-integral conjugate
`τ_O = T⁻¹ τ T`, and `b ≤ N` such that the finite module `(O/ℓ^{N+1})^{m_τ}` with `π₁(V', x̄)`
acting through `τ_O` satisfies the level dichotomy at `(N, b)`. -/
public def LaumonLatticeLevelDichotomyInput : Prop :=
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
        (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k')) p₁)
          g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
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
      ∀ E'' : IntermediateField E (AlgebraicClosure E), FiniteDimensional E E'' →
        ∃ (O : Subring E'') (_ : ValuationRing O) (_ : IsFractionRing O E''),
          ((ℓ : O) ≠ 0) ∧ ¬IsUnit (ℓ : O) ∧ (∀ o : O, o ≠ 0 → ∃ c : ℕ, o ∣ (ℓ : O) ^ c) ∧
          ∃ (τO : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) O) (T : GL (Fin mτ) E''),
            (∀ g, (τO g).val.map (algebraMap O E'') =
              (T⁻¹ : GL (Fin mτ) E'').val * (τ g).val.map (algebraMap E E'') * T.val) ∧
            ∃ (N b : ℕ) (_ : Finite (O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)})) (_ : b ≤ N)
              (hker : IsOpen (((Matrix.GeneralLinearGroup.map
                (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (N + 1)}))).comp τO).ker :
                  Set (EtaleFundamentalGroup V'.1 xV))),
              ContinuousModuleLevelDichotomy (matrixContinuousModule.{u + 1, u + 1}
                (O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)}) ((Matrix.GeneralLinearGroup.map
                  (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (N + 1)}))).comp τO) hker) ℓ N b

/-- **L6 for `ℓ ≠ p` from the level dichotomy of the lattices of `τ ⊗ E'`.** -/
public theorem laumonFourierLineAbsIrrInput'_of_latticeLevelDichotomy
    (h : LaumonLatticeLevelDichotomyInput.{u}) : LaumonFourierLineAbsIrrInput'.{u} := by
  intro B ℓ _ _ _ _ k' _ _ p _ _ hℓp E _ _ _ d b ψ' hψ' hζ n a hS hL z p₀ m σ₁ hσ₁ p₁ hirr V' U'
    _ _ _ jV' jU g' _ _ _ jg' hjV hpb xV r ρ hρ φ ψ₀ N hφψ hψφ mτ τ P Q hPQ hα hτ hQP K _ _ _ W hW
  refine eq_bot_or_eq_top_of_forall_finiteDimensional (fun g => (τ g).val)
    (fun g h => ⟨g * h, by simp⟩) ⟨1, by simp⟩ (fun E'' hE'' W'' hW'' => ?_) K W hW
  obtain ⟨O, _, _, hℓ0, hℓu, hℓ, τO, T, hT, N', c, _, hc, hker, hD⟩ :=
    h B ℓ k' p hℓp E b ψ' hψ' hζ n a hS hL z p₀ σ₁ hσ₁ p₁ hirr V' U' jV' jU g' jg' hjV hpb xV ρ hρ
      φ ψ₀ N hφψ hψφ τ P Q hPQ hα hτ hQP E'' hE''
  have hTT : ∀ w : Fin mτ → E'', T.val *ᵥ ((T⁻¹ : GL (Fin mτ) E'').val *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hs : Function.Surjective (Matrix.toLin' T.val) := fun w => ⟨_, hTT w⟩
  let W₀ : Submodule E'' (Fin mτ → E'') := W''.comap (Matrix.toLin' T.val)
  have hW₀ : ∀ g, ∀ v ∈ W₀, (τO g).val.map (algebraMap O E'') *ᵥ v ∈ W₀ := by
    intro g v hv
    change T.val *ᵥ ((τO g).val.map (algebraMap O E'') *ᵥ v) ∈ W''
    rw [hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTT]
    exact hW'' g _ hv
  have hmap := Submodule.map_comap_eq_of_surjective hs W''
  rcases eq_bot_or_eq_top_of_continuousModuleLevelDichotomy E'' ℓ hℓ0 hℓu hℓ hc τO hker hD W₀
      hW₀ with h0 | h0
  · left
    rw [← hmap, show W''.comap _ = ⊥ from h0, Submodule.map_bot]
  · right
    rw [← hmap, show W''.comap _ = ⊤ from h0, Submodule.map_top, LinearMap.range_eq_top.2 hs]

end Stacks.EtaleCohomology

end
