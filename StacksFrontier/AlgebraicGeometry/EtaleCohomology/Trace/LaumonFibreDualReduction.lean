module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePurityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRootConjugation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepContinuity

/-!
# L7: duality with complex conjugation from Poincaré duality and the trace formula

The duality step of Laumon's purity of the Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, proof of Theorem 6.4), `Stacks.EtaleCohomology.LaumonFibreReciprocityInput`, compares
the fibre `G = ℱ_σ ⊗ L_ψ(a xⁿ + c x)` over `k'` (`#k' = q`) with its dual `G^∨`, the sheaf of the
contragredient of the twisted representation. Let `P`, `Q` be the `E`-linear characteristic
polynomials of the Frobenius of `k'` on `H¹_c(𝔸¹_k̄', G ⊗ ℚ_ℓ)` and `H¹_c(𝔸¹_k̄', G^∨ ⊗ ℚ_ℓ)`
(`Stacks.EtaleCohomology.LaumonFibreDualCharpoly`). For `a ≠ 0` and `n` large prime to `p`:

* **Poincaré duality** (`Stacks.EtaleCohomology.LaumonFibreDualityInput`): there are no local
  terms at `∞` (Artin–Schreier inertia), so `H¹_c = H¹` and the cup product pairs the two fibres
  perfectly into `ℚ_ℓ(-1)`; the roots `z` of `P` along `ι'` are nonzero and `q / z` is a root of
  `Q`;
* **complex conjugation** (`Stacks.EtaleCohomology.LaumonFibreConjugationInput`): by the trace
  formula, `H⁰_c = H²_c = 0` for both sheaves, the `ι'`-purity of weight `β` of `σ` and
  `|ι' ψ| = 1`, the power sums of the roots of `Q` are those of `q ^ (-β) z̄`, `z` a root of `P`;
  so for a nonzero root `w` of `Q`, `q ^ β w̄` is a root of `P`.

Together (`Stacks.EtaleCohomology.isRoot_zpow_div_conj_of_dual`) they give
`Stacks.EtaleCohomology.laumonFibreReciprocityInput_of_duality_conjugation`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFibreDualCharpoly`.
* `Stacks.EtaleCohomology.LaumonFibreDualityInput`,
  `Stacks.EtaleCohomology.LaumonFibreConjugationInput`.

## Main results

* `Stacks.EtaleCohomology.LaumonFibreDualCharpoly.laumonFibreCharpoly`.
* `Stacks.EtaleCohomology.laumonFibreReciprocityInput_of_duality_conjugation`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

section Fibre

open Polynomial

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [ConnectedSpace U.1]
  (k : Type u) [Field k] [Fintype k] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
  (x : GeometricPoint U.1) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
  (ψ : AddChar k E) (n : ℕ)

/-- **A property of the Frobenius characteristic polynomials of a fibre of the Fourier family and
of its dual, off `D = 0`**: for every datum of `Stacks.EtaleCohomology.LaumonFibreCharpoly`, the
`H¹_c` of the dual fibre (the sheaf of the contragredient of the twisted representation) is
finite dimensional, and the `E`-linear characteristic polynomials `P` and `Q` of the Frobenius of
`k'` on `H¹_c(𝔸¹_k̄', ℱ_σ ⊗ L_ψ'(a xⁿ + c x) ⊗ ℚ_ℓ)` and on the `H¹_c` of the dual fibre satisfy
`Φ (#k') P Q`. -/
public def LaumonFibreDualCharpoly (D : MvPolynomial (Fin 2) k)
    (Φ : ℕ → Polynomial E → Polynomial E → Prop) : Prop :=
    ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
    (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    [IsNoetherian (Spec (.of (Polynomial k')))] [ConnectedSpace (Spec (.of (Polynomial k')))]
    (x' : GeometricPoint (Spec (.of (Polynomial k'))))
    (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
      inv e) = x)
    (a c : k'), MvPolynomial.eval ![a, c] (MvPolynomial.map (algebraMap k k') D) ≠ 0 →
    ∀ (p₀ : (finiteEtaleFiberFunctor x').obj
        (Stacks.ArtinSchreier.cover k' (Polynomial k')
          (C a * Polynomial.X ^ n + C c * Polynomial.X)))
      (hτ : Continuous (restrictScalarsRep b (characterTwist
        (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
          (C a * Polynomial.X ^ n + C c * Polynomial.X)
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀))))
      [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))]
      [QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))]
      [IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))]
      (j' : CompactificationOf (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))))
      (kbar' : Type u) [Field kbar'] [Algebra k' kbar'] [IsAlgClosure k' kbar'] (p n' : ℕ)
      [Fact p.Prime] [CharP k' p]
      (hcard' : Fintype.card k' = p ^ n')
      [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
        (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
        (LAdicSheaf.representationSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
          x' (restrictScalarsRep b _) hτ) 1)],
      letI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _ hτ).rationalCohomologyModule
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E
      haveI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
          hτ).rationalCohomologyModule_isScalarTower
        (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E
          (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _ hτ).toLAdicSheaf 1) := hV
      haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _ hτ).toLAdicSheaf 1) :=
        Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      ∃ hV' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
          (LAdicSheaf.representationSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
            x' (restrictScalarsRep b (contragredient _))
            (continuous_restrictScalarsRep_contragredient b hτ)) 1),
        letI := (restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
            (continuous_restrictScalarsRep_contragredient b hτ)).rationalCohomologyModule
            (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E
        haveI := (restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
            (continuous_restrictScalarsRep_contragredient b hτ))
            |>.rationalCohomologyModule_isScalarTower
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E
            (algebraMap_conjIntegralSubring_algebraMap _ _)
        haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
            (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
            (restrictScalarsRepCoefficientSheaf B
              (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
                (continuous_restrictScalarsRep_contragredient b hτ)).toLAdicSheaf 1) := hV'
        haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
            (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
            (restrictScalarsRepCoefficientSheaf B
              (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
                (continuous_restrictScalarsRep_contragredient b hτ)).toLAdicSheaf 1) :=
          Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
        Φ (p ^ n')
          (LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
              hτ).rationalGeometricCompactlySupportedFrobenius
            (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E p n'
              hcard'))
          (LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
              (continuous_restrictScalarsRep_contragredient b hτ))
              |>.rationalGeometricCompactlySupportedFrobenius
            (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E p n'
              hcard'))

variable {B U ℓ k e x E b σ ψ n}

omit [Fintype k] in
/-- **Properties of a fibre and its dual combine into a property of the fibre.** -/
public theorem LaumonFibreDualCharpoly.laumonFibreCharpoly {D : MvPolynomial (Fin 2) k}
    {Φ₁ Φ₂ : ℕ → Polynomial E → Polynomial E → Prop} {Ψ : ℕ → Polynomial E → Prop}
    (h₁ : LaumonFibreDualCharpoly B U ℓ k e x E b σ ψ n D Φ₁)
    (h₂ : LaumonFibreDualCharpoly B U ℓ k e x E b σ ψ n D Φ₂)
    (h : ∀ (p n' : ℕ), p.Prime → ∀ P Q, Φ₁ (p ^ n') P Q → Φ₂ (p ^ n') P Q → Ψ (p ^ n') P) :
    LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D Ψ := by
  intro k' _ _ _ hX' _ _ x' hx' a c hac p₀ hτ _ _ _ j' kbar' _ _ _ p n' _ _ hcard' _
  obtain ⟨_, h₁⟩ := h₁ k' hX' x' hx' a c hac p₀ hτ j' kbar' p n' hcard'
  obtain ⟨_, h₂⟩ := h₂ k' hX' x' hx' a c hac p₀ hτ j' kbar' p n' hcard'
  exact h p n' Fact.out _ _ h₁ h₂

end Fibre

/-- **Poincaré duality on the fibres of the Fourier family** (Kedlaya, *Fourier transforms and
p-adic Weil II*, proof of Theorem 6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonFibrePurityInput` and `ψ ≠ 1` there is `N` such that for `n > N`
prime to `p` and `a ≠ 0`, the `H¹_c` of the dual fibre `(ℱ_σ ⊗ L_ψ(a xⁿ + c x))^∨` over `k'`
(`#k' = q`) is finite dimensional and every Frobenius root `z` (along `ι'`) of the fibre is nonzero
with `q / z` a root of the dual fibre: there are no local terms at `∞` (Artin–Schreier inertia), so
`H¹_c = H¹` and the cup product is a perfect pairing into `ℚ_ℓ(-1)`. -/
public def LaumonFibreDualityInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
          kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      LaumonFibreDualCharpoly B U ℓ k e x E b σ ψ n (MvPolynomial.X 0) fun q P Q =>
        ∀ z : ℂ, (P.map ι').IsRoot z → z ≠ 0 ∧ (Q.map ι').IsRoot ((q : ℂ) / z)

/-- **Complex conjugation on the fibres of the Fourier family** (Kedlaya, *Fourier transforms and
p-adic Weil II*, proof of Theorem 6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonFibrePurityInput` and `ψ ≠ 1` there is `N` such that for `n > N`
prime to `p` and `a ≠ 0`, the `H¹_c` of the dual fibre `(ℱ_σ ⊗ L_ψ(a xⁿ + c x))^∨` over `k'`
(`#k' = q`) is finite dimensional and for every nonzero Frobenius root `w` (along `ι'`) of the dual
fibre, `q ^ β w̄` is a root of the fibre: `H⁰_c = H²_c = 0` for both sheaves, and by the trace
formula, the `ι'`-purity of weight `β` of `σ` and `|ι' ψ| = 1`, the power sums of the roots of the
dual fibre are those of `q ^ (-β) z̄`, `z` a root of the fibre. -/
public def LaumonFibreConjugationInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
          kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      LaumonFibreDualCharpoly B U ℓ k e x E b σ ψ n (MvPolynomial.X 0) fun q P Q =>
        ∀ w : ℂ, w ≠ 0 → (Q.map ι').IsRoot w → (P.map ι').IsRoot ((q : ℂ) ^ β * starRingEnd ℂ w)

/-- **Duality with complex conjugation on the Fourier family from Poincaré duality and the
conjugation of the dual fibre.** -/
public theorem laumonFibreReciprocityInput_of_duality_conjugation
    (h₁ : LaumonFibreDualityInput.{u}) (h₂ : LaumonFibreConjugationInput.{u}) :
    LaumonFibreReciprocityInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β _ hpure ψ hψ
  obtain ⟨N₁, h₁⟩ := h₁ B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure ψ hψ
  obtain ⟨N₂, h₂⟩ := h₂ B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure ψ hψ
  refine ⟨max N₁ N₂, fun n' hn' hpn' => ?_⟩
  exact (h₁ n' (lt_of_le_of_lt (le_max_left _ _) hn') hpn').laumonFibreCharpoly
    (h₂ n' (lt_of_le_of_lt (le_max_right _ _) hn') hpn')
    fun p₁ n₁ hp₁ _ _ hPD hconj => isRoot_zpow_div_conj_of_dual (pow_ne_zero _ hp₁.ne_zero) hPD
      hconj

end Stacks.EtaleCohomology

end
