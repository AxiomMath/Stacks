module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePurityReduction

/-!
# Fibre purity for representations which stay absolutely irreducible over every finite extension

The fibre purity `Stacks.EtaleCohomology.LaumonFibrePurityInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, §6.4) asks for the purity of all fibres `H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` over all finite
extensions `k'` of `k`, for `σ` absolutely irreducible over `π₁(𝔸¹_k)`. Absolute irreducibility
over `k` is not preserved by the passage to `k'` (`σ = Ind_{k₂/k} L_ψ(b x)` splits over `k₂`),
while the argument through Weil II 1.5.1 needs the Fourier transform over `k'` to be absolutely
irreducible. As in Kedlaya's reduction to geometric irreducibility, the argument is run for
representations which stay absolutely irreducible over every finite extension
(`Stacks.EtaleCohomology.LaumonStablyAbsIrr`):

* `Stacks.EtaleCohomology.LaumonFourierEquinormStableInput`: equal absolute values of the fibres
  for such `σ`;
* `Stacks.EtaleCohomology.laumonFibrePurityStableInput_of_equinorm_reciprocity`: with duality and
  complex conjugation (`Stacks.EtaleCohomology.LaumonFibreReciprocityInput`, which does not use
  the irreducibility beyond that over `k`), the fibres are pure for such `σ`
  (`Stacks.EtaleCohomology.LaumonFibrePurityStableInput`);
* `Stacks.EtaleCohomology.LaumonFibreStableReductionInput`: the reduction of the general case to
  that one (choose `k₀'` over which `σ` splits into constituents which stay absolutely irreducible,
  pass to the compositum `k' k₀'`, use that `H¹_c` of a direct sum is the direct sum, and come back
  down along the Frobenius powers); `Stacks.EtaleCohomology.laumonFibrePurityInput_of_stable`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonStablyAbsIrr`.
* `Stacks.EtaleCohomology.LaumonFourierEquinormStableInput`,
  `Stacks.EtaleCohomology.LaumonFibrePurityStableInput`,
  `Stacks.EtaleCohomology.LaumonFibreStableReductionInput`.

## Main results

* `Stacks.EtaleCohomology.laumonFibrePurityStableInput_of_equinorm_reciprocity`.
* `Stacks.EtaleCohomology.laumonFibrePurityInput_of_stable`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **`σ` stays absolutely irreducible over every finite extension of `k`**: for every finite
extension `k'` of `k` and every geometric point `x̄'` of `𝔸¹_{k'}` over `x̄`, the pullback of `σ`
to `π₁(𝔸¹_{k'}, x̄')` has no nonzero proper stable subspace over any algebraically closed field `K`
over `E` (the form of absolute irreducibility of
`Stacks.EtaleCohomology.LaumonAffineLineLinearAbsIrrInput`). -/
public def LaumonStablyAbsIrr {X : Scheme.{u}} [ConnectedSpace X] (k : Type u) [Field k]
    (e : X ⟶ Spec (.of (Polynomial k))) [IsIso e] (x : GeometricPoint X) {E : Type} [Field E]
    {m : ℕ} (σ : EtaleFundamentalGroup X x →* GL (Fin m) E) : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
    (x' : GeometricPoint (Spec (.of (Polynomial k'))))
    (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
      inv e) = x)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra E K] (W : Submodule K (Fin m → K)),
    (∀ g, ∀ v ∈ W, ((σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom)) g).val.map
        (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

/-- **Equal absolute values of the Fourier family off a curve, for `σ` which stays absolutely
irreducible over every finite extension** (Laumon; Kedlaya, *Fourier transforms and p-adic
Weil II*, Theorem 6.4, first half): `Stacks.EtaleCohomology.LaumonFourierEquinormInput` with the
extra hypothesis `Stacks.EtaleCohomology.LaumonStablyAbsIrr`. For `a ≠ 0` the family in `c` over
`k'` is the Fourier transform of `ℱ_σ ⊗ L_ψ(a xⁿ)`, absolutely irreducible on its lisse locus since
`σ` is so over `k'`, and Weil II 1.5.1 makes it pure of some weight there. -/
public def LaumonFourierEquinormStableInput : Prop :=
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
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
          j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ LaumonFibreEquinorm B U ℓ k e x E b σ ι' ψ n D

/-- **Purity of the fibres of the Fourier family, for `σ` which stays absolutely irreducible over
every finite extension**: `Stacks.EtaleCohomology.LaumonFibrePurityInput` with the extra
hypothesis `Stacks.EtaleCohomology.LaumonStablyAbsIrr`. -/
public def LaumonFibrePurityStableInput : Prop :=
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
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
          j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n D

/-- **Fibre purity for `σ` which stays absolutely irreducible, from equal absolute values and
duality**: the curve is `a · D₁ = 0`. Duality with complex conjugation
(`Stacks.EtaleCohomology.LaumonFibreReciprocityInput`) only uses the absolute irreducibility over
`k`. -/
public theorem laumonFibrePurityStableInput_of_equinorm_reciprocity
    (hE : LaumonFourierEquinormStableInput.{u}) (hR : LaumonFibreReciprocityInput.{u}) :
    LaumonFibrePurityStableInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hst hζ ι' β _ hpure ψ hψ
  obtain ⟨N₁, h₁⟩ := hE B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hst hζ ι' β hpure ψ hψ
  obtain ⟨N₂, h₂⟩ := hR B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure ψ hψ
  refine ⟨max N₁ N₂, fun n' hn' hpn' => ?_⟩
  obtain ⟨D, hD, hDe⟩ := h₁ n' (lt_of_le_of_lt (le_max_left _ _) hn') hpn'
  exact ⟨MvPolynomial.X 0 * D, mul_ne_zero (MvPolynomial.X_ne_zero _) hD,
    laumonFibrePure_of_equinorm_of_reciprocal hDe
      (h₂ n' (lt_of_le_of_lt (le_max_right _ _) hn') hpn')⟩

/-- **The reduction of fibre purity to representations which stay absolutely irreducible**
(Kedlaya, *Fourier transforms and p-adic Weil II*, reduction to geometric irreducibility): the
purity of the fibres for `σ` which stays absolutely irreducible over every finite extension of the
base field gives it for every absolutely irreducible `σ`. Over a finite extension `k₀'` of `k`, `σ`
splits (after enlarging `E`) into constituents which stay absolutely irreducible and are pure of
the same weight; at a fibre over `k'`, pass to the compositum `k' k₀'`, where `H¹_c` of the direct
sum is the direct sum of the `H¹_c` of the constituents, and come back down since the Frobenius of
`k' k₀'` is a power of that of `k'`. -/
public def LaumonFibreStableReductionInput : Prop :=
  LaumonFibrePurityStableInput.{u} → LaumonFibrePurityInput.{u}

/-- **Fibre purity from its case of representations which stay absolutely irreducible.** -/
public theorem laumonFibrePurityInput_of_stable (hred : LaumonFibreStableReductionInput.{u})
    (hE : LaumonFourierEquinormStableInput.{u}) (hR : LaumonFibreReciprocityInput.{u}) :
    LaumonFibrePurityInput.{u} :=
  hred (laumonFibrePurityStableInput_of_equinorm_reciprocity hE hR)

end Stacks.EtaleCohomology

end
