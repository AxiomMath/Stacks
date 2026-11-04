module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreDualReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDualTraceConjugation
public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineShiftFiniteEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteCompactSupportCohomology

/-!
# L7: the conjugation step on the fibres of the Fourier family

`Stacks.EtaleCohomology.LaumonFibreConjugationInput` (for a nonzero Frobenius root `w` of the dual
fibre, `q ^ β · w̄` is a root of the fibre) is the curve statement
`Stacks.EtaleCohomology.isRoot_zpow_mul_conj_of_curve` on `𝔸¹_{k'}` for the twisted
representation `τ = σ' ⊗ χ` of a fibre
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, proof of Theorem 6.4), granted:

* **purity of the fibre** (`Stacks.EtaleCohomology.LaumonFibreTwistPurityInput`): `τ` is
  `ι'`-pure of weight `β` at the closed points of `𝔸¹_{k'}` (the Frobenius of a closed point of
  `𝔸¹_{k'}` maps to a power of a Frobenius of `U`, and `χ` takes values in the roots of unity
  `ψ(k)`);
* **vanishing of `H²_c`** (`Stacks.EtaleCohomology.LaumonFibreTopVanishingInput`): for `a ≠ 0` and
  `n` large prime to `p`, `H²_c` of `ℱ_τ` and of `ℱ_{τ^∨}` vanish (`H²_c` is the twisted
  coinvariants of the geometric fundamental group, which contains the inertia at `∞`, where
  `τ` and `τ^∨` have no coinvariants by Artin–Schreier theory).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFibreTwistPurityInput`,
  `Stacks.EtaleCohomology.LaumonFibreTopVanishingInput`.

## Main results

* `Stacks.EtaleCohomology.laumonFibreConjugationInput_of_purity_vanishing`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Polynomial

universe u

namespace Stacks.EtaleCohomology

/-- **Purity of the fibres of the Fourier family at the closed points** (Kedlaya, *Fourier
transforms and p-adic Weil II*, proof of Theorem 6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonFibrePurityInput`, `ι'`-pure of weight `β`, every nontrivial `ψ`,
every `n` and every fibre datum of `Stacks.EtaleCohomology.LaumonFibreCharpoly` over `k'`
(`#k' = q`), the twisted representation `τ = σ' ⊗ χ` of `π₁(𝔸¹_{k'}, x̄')` is `ι'`-pure of weight
`β` at the closed points `y` of `𝔸¹_{k'}`: the roots of the characteristic polynomial of the
geometric Frobenius `τ(F_y)` along `ι'` have absolute value `q ^ (deg y · β / 2)`. -/
public def LaumonFibreTwistPurityInput : Prop :=
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
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∀ n : ℕ,
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
    (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    [IsNoetherian (Spec (.of (Polynomial k')))] [ConnectedSpace (Spec (.of (Polynomial k')))]
    (x' : GeometricPoint (Spec (.of (Polynomial k'))))
    (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
      inv e) = x)
    (a c : k'), ∀ (p₀ : (finiteEtaleFiberFunctor x').obj
        (Stacks.ArtinSchreier.cover k' (Polynomial k')
          (C a * Polynomial.X ^ n + C c * Polynomial.X)))
      (_ : Continuous (restrictScalarsRep b (characterTwist
        (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
          (C a * Polynomial.X ^ n + C c * Polynomial.X)
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀))))
      [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))]
      [QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))]
      [IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))]
      (_ : CompactificationOf (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))))
      (kbar' : Type u) [Field kbar'] [Algebra k' kbar'] [IsAlgClosure k' kbar'] (p n' : ℕ)
      [Fact p.Prime] [CharP k' p]
      (_ : Fintype.card k' = p ^ n'),
      ∀ (y : closedPoints (Stacks.ArtinSchreier.specObject (Polynomial k') B hX').1) (z : ℂ),
        (((characterTwist
        (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
          (C a * Polynomial.X ^ n + C c * Polynomial.X)
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀)) (geometricFrobeniusFamily
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) x' y)).val.charpoly.map
            ι').IsRoot z →
          ‖z‖ = ((p ^ n' : ℕ) : ℝ) ^ (((residueDegree
            (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) y.1 : ℤ) * β : ℝ) / 2)

/-- **Vanishing of `H²_c` on the fibres of the Fourier family** (Kedlaya, *Fourier transforms and
p-adic Weil II*, proof of Theorem 6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonFibrePurityInput` and `ψ ≠ 1` there is `N` such that for `n > N`
prime to `p` and every fibre datum of `Stacks.EtaleCohomology.LaumonFibreCharpoly` with `a ≠ 0`,
`H²_c(𝔸¹_k̄', ℱ_τ ⊗ ℚ_ℓ)` and `H²_c(𝔸¹_k̄', ℱ_{τ^∨} ⊗ ℚ_ℓ)` vanish (`τ = σ' ⊗ χ` the twisted
representation): `H²_c` is the twisted coinvariants of the geometric fundamental group, which
contains the inertia at `∞`, where `τ` and `τ^∨` have no coinvariants (Artin–Schreier theory,
Swan conductor `n` of `χ` at `∞`). -/
public def LaumonFibreTopVanishingInput : Prop :=
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
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
    (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    [IsNoetherian (Spec (.of (Polynomial k')))] [ConnectedSpace (Spec (.of (Polynomial k')))]
    (x' : GeometricPoint (Spec (.of (Polynomial k'))))
    (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
      inv e) = x)
    (a c : k'),
    MvPolynomial.eval ![a, c] (MvPolynomial.map (algebraMap k k') (MvPolynomial.X 0)) ≠ 0 →
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
      (_ : Fintype.card k' = p ^ n'),
      Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
            x' b _ hτ).toLAdicSheaf 2) ∧
        Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
            x' b (contragredient _)
            (continuous_restrictScalarsRep_contragredient b hτ)).toLAdicSheaf 2)

/-- **The conjugation step of L7 from the purity of the fibres and the vanishing of `H²_c`.** -/
public theorem laumonFibreConjugationInput_of_purity_vanishing
    (hpur : LaumonFibreTwistPurityInput.{u}) (hvan : LaumonFibreTopVanishingInput.{u}) :
    LaumonFibreConjugationInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β _ hpure ψ hψ
  obtain ⟨N, hN⟩ := hvan B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure ψ hψ
  refine ⟨N, fun n₀ hn₀ hpn₀ => ?_⟩
  intro k' _ _ _ hX' _ _ x' hx' a c hac p₀ hτ _ _ _ j' kbar' _ _ _ p' n' _ _ hcard' hV
  have hpp : p' = p := CharP.eq k' inferInstance ((Algebra.charP_iff k k' p).1 inferInstance)
  have hℓ' : ℓ ≠ p' := hpp ▸ hℓp
  have := Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial k'
  have := Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_polynomial k' kbar'
  have h2 := hN n₀ hn₀ hpn₀ k' hX' x' hx' a c hac p₀ hτ j' kbar' p' n' hcard'
  have hp := hpur B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure ψ hψ n₀ k'
    hX' x' hx' a c p₀ hτ j' kbar' p' n' hcard'
  have hfin := LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ
  have hV' := (hfin k' kbar' p' n' hcard' hℓ'
    (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
    (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j'
    (LAdicSheaf.representationSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
        x' (restrictScalarsRep b (contragredient _))
        (continuous_restrictScalarsRep_contragredient b hτ)) 1).1
  refine ⟨hV', ?_⟩
  have hc := isRoot_zpow_mul_conj_of_curve B (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
    ℓ k' (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' p' n' hcard' hℓ' x'
    E b _ hτ ι' β hp h2.1 h2.2 (hV := hV) (hV' := hV')
  exact hc

end Stacks.EtaleCohomology

end
