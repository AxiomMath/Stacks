module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineAbsIrr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Twist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing

/-!
# Laumon's theorem on the affine line: the `E`-linear inputs

The statements in which Laumon's Fourier transform proof of Weil II 3.2.3 on `𝔸¹` (Kedlaya,
*Fourier transforms and p-adic Weil II*, §6) is assembled:

* `Stacks.EtaleCohomology.LaumonAffineLineLinearAbsIrrInput`: the `E`-linear statement, one
  embedding `ι'` of `E` at a time, for absolutely irreducible `σ` with `ζ_p ∈ E`; it gives
  `Stacks.EtaleCohomology.LaumonAffineLineAbsIrrInput`
  (`Stacks.EtaleCohomology.laumonAffineLineAbsIrrInput_of_linear`), hence
  `Stacks.EtaleCohomology.LaumonAffineLineInput`
  (`Stacks.EtaleCohomology.laumonAffineLineInput_of_absIrr`).
* `Stacks.EtaleCohomology.CurveLinearCoinvariantsInput`: `H²_c` of `ℱ_{Res_b σ}` as the geometric
  coinvariants, `E`-linearly (Tag 03VN).
* `Stacks.EtaleCohomology.LaumonFibrePurityInput` and
  `Stacks.EtaleCohomology.LaumonFibreDegenerationInput`: the purity of the two-parameter Fourier
  family `H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` off a curve of the `(a, c)`-plane
  (`Stacks.EtaleCohomology.LaumonFibrePure`), and the bound on `H¹_c(𝔸¹, ℱ_σ)` it implies by
  degeneration at the origin. Their conjunction is the `E`-linear absolutely irreducible statement
  (`Stacks.EtaleCohomology.laumonAffineLineLinearAbsIrrInput_of_fibrePurity`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonAffineLineLinearAbsIrrInput`.
* `Stacks.EtaleCohomology.CurveLinearCoinvariantsInput`.
* `Stacks.EtaleCohomology.LaumonFibrePure`, `Stacks.EtaleCohomology.LaumonFibrePurityInput`,
  `Stacks.EtaleCohomology.LaumonFibreDegenerationInput`.

## Main results

* `Stacks.EtaleCohomology.laumonAffineLineAbsIrrInput_of_linear`.
* `Stacks.EtaleCohomology.laumonAffineLineInput_of_linearAbsIrr`.
* `Stacks.EtaleCohomology.laumonAffineLineLinearAbsIrrInput_of_fibrePurity`,
  `Stacks.EtaleCohomology.laumonAffineLineInput_of_fibrePurity`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **Laumon's theorem on the affine line, `E`-linearly, for absolutely irreducible
representations with `ζ_p ∈ E`**: `Stacks.EtaleCohomology.LaumonAffineLineLinearInput` for those
`σ` which are irreducible over an algebraically closed field `K ⊇ E`, with `E` containing a
primitive `p`-th root of unity. This is the statement Laumon's Fourier transform argument proves
(Kedlaya, *Fourier transforms and p-adic Weil II*, §6). -/
public def LaumonAffineLineLinearAbsIrrInput : Prop :=
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
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI :=
      (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
        f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) := hV
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    IsCharpolyNormMixedOfWeightLE (p ^ n) ι' (β + 1)
      ((restrictScalarsRepCoefficientSheaf B U x b σ
        hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard)

/-- **`H²_c` of `ℱ_{Res_b σ}` on a smooth geometrically connected curve, `E`-linearly** (Tag 03VN
with coefficients in `E`): for every lift `φ` of the inverse of the Frobenius of `k`, there is an
`E`-linear isomorphism of `H²_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` with the coinvariants of `σ` under
`π₁(U_k̄)` carrying the `E`-linear `π_U^*` to `q · φ`. The `ℚ_ℓ`-statement
`Stacks.EtaleCohomology.CurveCoinvariantsInput` for `Res_b σ` is its restriction of scalars. -/
public def CurveLinearCoinvariantsInput : Prop :=
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
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (φ : EtaleFundamentalGroup U.1 x),
    etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹ →
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 2 E
    ∃ e : (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2) ≃ₗ[E]
        Representation.Coinvariants ((matrixRepresentation σ).comp
          (etaleFundamentalGroupMap f x).toMonoidHom.ker.subtype),
      ∀ v, e ((restrictScalarsRepCoefficientSheaf B U x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 2 E p n hcard v) =
        ((p ^ n : ℕ) : E) • coinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker
          σ φ (e v)

/-- **`Stacks.EtaleCohomology.LaumonAffineLineAbsIrrInput` from its `E`-linear form**, as
`Stacks.EtaleCohomology.laumonAffineLineInput_of_linear`. -/
public theorem laumonAffineLineAbsIrrInput_of_linear (h : LaumonAffineLineLinearAbsIrrInput.{u}) :
    LaumonAffineLineAbsIrrInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι w hV hP
  let := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
  have := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
      j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) := hV
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  change IsCharpolyNormMixedOfWeightLE (p ^ n) ι (w + 1)
    (((restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
      f j kbar 1 E p n hcard).restrictScalars ℚ_[ℓ])
  refine (isCharpolyNormMixedOfWeightLE_restrictScalars_iff _ _ ι _).2 fun ι' hι' => ?_
  obtain ⟨β, hβ, hpure⟩ := hP ι' hι'
  intro z hz
  obtain ⟨w', hw', hz'⟩ :=
    h B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure z hz
  exact ⟨w', hw'.trans (by omega), hz'⟩

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
  (ι' : E →+* ℂ) (β : ℤ) (ψ : AddChar k E) (n : ℕ)

/-- **Purity of the fibres of the two-parameter Fourier family off `D = 0`** (Laumon; Kedlaya,
*Fourier transforms and p-adic Weil II*, §6.4): for every finite extension `k'` of `k`, every
geometric point `x̄'` of `𝔸¹_{k'}` over `x̄` and every `(a, c) ∈ k'²` with `D(a, c) ≠ 0`, the
`E`-linear Frobenius of `k'` on `H¹_c(𝔸¹_{k̄'}, ℱ_σ ⊗ L_ψ'(a xⁿ + c x) ⊗ ℚ_ℓ)` (`k̄'` an algebraic
closure of `k'`) is `ι'`-pure of weight `β + 1` in absolute value (every root `z` along `ι'` of its
characteristic polynomial has `‖z‖ = (#k') ^ ((β + 1) / 2)`; algebraicity of the roots is not asked
for, and fails in general since `σ` is pure only in absolute value along the single embedding
`ι'`), where `σ` is pulled back to `𝔸¹_{k'}`, `ψ' = ψ ∘ Tr_{k'/k}`, and `ℱ_σ ⊗ L_ψ'(g)` is the
sheaf of the twist of `σ` by the Artin–Schreier character of `g`. -/
public def LaumonFibrePure (D : MvPolynomial (Fin 2) k) : Prop :=
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
      ∀ z : ℂ, ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
            hτ).rationalGeometricCompactlySupportedFrobenius
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E p n'
            hcard')).map ι').IsRoot z →
        ‖z‖ = ((p ^ n' : ℕ) : ℝ) ^ (((β + 1 : ℤ) : ℝ) / 2)

end Fibre

/-- **Laumon's theorem on the affine line from its `E`-linear absolutely irreducible case.** -/
public theorem laumonAffineLineInput_of_linearAbsIrr (h : LaumonAffineLineLinearAbsIrrInput.{u}) :
    LaumonAffineLineInput.{u} :=
  laumonAffineLineInput_of_absIrr (laumonAffineLineAbsIrrInput_of_linear h)

/-- **Purity of the two-parameter Fourier family** (Laumon; Kedlaya, *Fourier transforms and
p-adic Weil II*, §6.4): for `σ` as in `Stacks.EtaleCohomology.LaumonAffineLineLinearAbsIrrInput`,
`ι'`-pure of weight `β`, and every nontrivial additive character `ψ` of `k` with values in `E`,
there is `N` such that for every `n > N` prime to `p` the fibres
`H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` are `ι'`-pure of weight `β + 1` off a curve `D = 0` of the
`(a, c)`-plane (`Stacks.EtaleCohomology.LaumonFibrePure`). -/
public def LaumonFibrePurityInput : Prop :=
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
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n D

/-- **The bound on `H¹_c(𝔸¹, ℱ_σ)` from the purity of the Fourier family** (Laumon; Kedlaya,
*Fourier transforms and p-adic Weil II*, §6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonAffineLineLinearAbsIrrInput`, `ι'`-pure of weight `β`, if the
two-parameter family is pure of weight `β + 1` off a curve `D = 0` (the conclusion of
`Stacks.EtaleCohomology.LaumonFibrePurityInput`), then the `E`-linear `π^*` on
`H¹_c(𝔸¹_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` has weights `≤ β + 1` along `ι'`. -/
public def LaumonFibreDegenerationInput : Prop :=
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
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    (∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n D) →
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI :=
      (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
        f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) := hV
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    IsCharpolyNormMixedOfWeightLE (p ^ n) ι' (β + 1)
      ((restrictScalarsRepCoefficientSheaf B U x b σ
        hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard)

/-- **Laumon's theorem on the affine line, `E`-linearly, for absolutely irreducible `σ` with
`ζ_p ∈ E`**, from the purity of the Fourier family and the degeneration at `s = 0`. -/
public theorem laumonAffineLineLinearAbsIrrInput_of_fibrePurity
    (h7 : LaumonFibrePurityInput.{u}) (h8 : LaumonFibreDegenerationInput.{u}) :
    LaumonAffineLineLinearAbsIrrInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β _ hpure
  exact h8 B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure
    (h7 B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure)

/-- **Laumon's theorem on the affine line from the purity of the Fourier family and the
degeneration at `s = 0`.** -/
public theorem laumonAffineLineInput_of_fibrePurity (h7 : LaumonFibrePurityInput.{u})
    (h8 : LaumonFibreDegenerationInput.{u}) : LaumonAffineLineInput.{u} :=
  laumonAffineLineInput_of_linearAbsIrr (laumonAffineLineLinearAbsIrrInput_of_fibrePurity h7 h8)

end Stacks.EtaleCohomology

end
