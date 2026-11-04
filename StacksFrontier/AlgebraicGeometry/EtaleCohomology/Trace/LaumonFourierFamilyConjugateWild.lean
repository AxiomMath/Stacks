module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity

/-!
# The real partner of the Fourier family in the totally wild range

The partner `τ'` of the representation `τ` of the Fourier family `G_V` at fixed `a`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, proof of Theorem 6.4) with `τ ⊕ τ'` real along `ι'` is the representation of the Fourier
family of `σ^∨` with `ψ⁻¹`, twisted by the unramified character `F_y ↦ q^{β deg y}`
(`Stacks.EtaleCohomology.exists_unramifiedCharacter`). The argument identifies the Frobenius at a
closed point `v` of `V'` on both families with the Frobenius on `H¹_c` of the fibres over `κ(v)`,
and compares these by the trace formula
(`Stacks.EtaleCohomology.roots_filter_ne_zero_contragredient_eq_map_conj_of_curve`), which needs
`H²_c = 0` on the fibres (`Stacks.EtaleCohomology.LaumonFibreTopVanishingInput`): it is stated in
the totally wild range `a ≠ 0`, `n > N` prime to `p`, where `LaumonFibreTopVanishingInput` holds
(the frozen `Stacks.EtaleCohomology.LaumonFourierFamilyConjugateInput` asks for every `a` and `n`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtension`,
  `Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtensionInput`: the fibre of the Fourier family
  over ANY point `v` of `V'` (not only a rational one) is the Fourier fibre over `κ(v)`, for all
  choices of its data (the compatibility of `R¹g'_!` with the constant field extension
  `κ(v) / k'`).
* `Stacks.EtaleCohomology.LaumonFourierFamilyConjugateWildInput`: the real partner for `a ≠ 0`,
  `n > N` prime to `p`, on an open `V'` over which the dual family is lisse too.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

section Family

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

/-- **The fibres of the Fourier family at fixed `a` over every point of `V'`, for all choices**:
for an open `V'` of the `t`-line, `U' = pr₂⁻¹(V')`, ANY point `v` of `V'` with finite residue field
(`κ(v)` a `k`-algebra through `k → k' → k'[t] → κ(v)`, `Stacks.EtaleCohomology.laumonPointAlgebra`)
and any fibre `Y` of `U' → V'` over `v` with a compactification, the `E`-linear Frobenius of `κ(v)`
on `H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` (`K` the Fourier family sheaf) has the characteristic polynomial of the
Frobenius of `κ(v)` on the Fourier fibre `H¹_c(𝔸¹_κ̄, ℱ_σ ⊗ L_ψ''(a xⁿ + t(v) x) ⊗ ℚ_ℓ)` over
`κ(v)` (`ψ'' = ψ ∘ Tr_{κ(v)/k}`), for EVERY choice of the data of that fibre. At a rational point
this is `Stacks.EtaleCohomology.LaumonFourierFamilyFibre` read through `κ(v) ≅ k'`; at a point of
degree `> 1` it is the compatibility of `R¹g'_!` with the constant field extension `κ(v) / k'`. -/
public def LaumonFourierFamilyFieldExtension : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V'),
    IsOpenImmersion (B.inclusion.map jV') →
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    ∀ (v : V'.1) [Fintype (V'.1.residueField v)] (Y : B.Scheme) [IsNoetherian Y.1] (i : Y ⟶ U')
      (fY : Y.1 ⟶ Spec (.of (V'.1.residueField v))) [LocallyOfFiniteType fY] [QuasiCompact fY]
      [IsSeparated fY],
    IsPullback (B.inclusion.map i) fY (B.inclusion.map g') (V'.1.fromSpecResidueField v) →
    ∀ (jY : CompactificationOf (Over.mk fY)) (kbarv : Type u) [Field kbarv]
      [Algebra (V'.1.residueField v) kbarv] [IsAlgClosure (V'.1.residueField v) kbarv] (pv nv : ℕ)
      [Fact pv.Prime] [CharP (V'.1.residueField v) pv]
      (hcardv : Fintype.card (V'.1.residueField v) = pv ^ nv),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    letI K := LAdicSheaf.CoefficientSheaf.inverseImage i
      (LAdicSheaf.CoefficientSheaf.inverseImage jU
      (laumonFourierFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n
        a z pz _ hσ₁))
    letI := laumonPointAlgebra jV' v k
    ∀ [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY
        jY kbarv K.toLAdicSheaf 1)]
    (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (V'.1.residueField v)))))
    [IsNoetherian (Spec (.of (Polynomial (V'.1.residueField v))))]
    [ConnectedSpace (Spec (.of (Polynomial (V'.1.residueField v))))]
    (x' : GeometricPoint (Spec (.of (Polynomial (V'.1.residueField v)))))
    (hx' : x'.map (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (algebraMap k (V'.1.residueField v)))) ≫
      inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor x').obj
        (Stacks.ArtinSchreier.cover (V'.1.residueField v) (Polynomial (V'.1.residueField v))
          (Polynomial.C (laumonPointRingHom jV' v (Polynomial.C a)) * Polynomial.X ^ n +
            Polynomial.C (laumonPointRingHom jV' v Polynomial.X) * Polynomial.X)))
      (hτ : Continuous (restrictScalarsRep b (characterTwist
        (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k (V'.1.residueField v)))) ≫ inv e) x').toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter (V'.1.residueField v)
          (Polynomial (V'.1.residueField v))
          (Polynomial.C (laumonPointRingHom jV' v (Polynomial.C a)) * Polynomial.X ^ n +
            Polynomial.C (laumonPointRingHom jV' v Polynomial.X) * Polynomial.X)
          (ψ.compAddMonoidHom (Algebra.trace k (V'.1.residueField v)).toAddMonoidHom) x' p₀))))
      [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
        (Polynomial (V'.1.residueField v)))))]
      [QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
        (Polynomial (V'.1.residueField v)))))]
      [IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
        (Polynomial (V'.1.residueField v)))))]
      (j' : CompactificationOf (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
          (Polynomial (V'.1.residueField v)))))))
      (kbar' : Type u) [Field kbar'] [Algebra (V'.1.residueField v) kbar']
      [IsAlgClosure (V'.1.residueField v) kbar']
      [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') ℓ
        (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
          (Polynomial (V'.1.residueField v))))) j' kbar'
        (LAdicSheaf.representationSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX')
          x' (restrictScalarsRep b _) hτ) 1)],
      letI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
          hτ).rationalCohomologyModule
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
            (Polynomial (V'.1.residueField v))))) j' kbar' 1 E
      haveI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
          hτ).rationalCohomologyModule_isScalarTower
        (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
          (Polynomial (V'.1.residueField v))))) j' kbar' 1 E
          (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
            (Polynomial (V'.1.residueField v))))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
              hτ).toLAdicSheaf 1) := hV
      haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
            (Polynomial (V'.1.residueField v))))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
              hτ).toLAdicSheaf 1) :=
        Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      letI := K.rationalCohomologyModule fY jY kbarv 1 E
      haveI := K.rationalCohomologyModule_isScalarTower fY jY kbarv 1 E
        (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY
          kbarv K.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      (K.rationalGeometricCompactlySupportedFrobenius fY jY kbarv 1 E pv nv hcardv).charpoly =
        (LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX') x' b _
            hτ).rationalGeometricCompactlySupportedFrobenius
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField v)
            (Polynomial (V'.1.residueField v))))) j' kbar' 1 E pv nv hcardv))


end Family

/-- **The fibres of the Fourier family over every point, for all choices**: the proposition
`Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtension` for all data. -/
public def LaumonFourierFamilyFieldExtensionInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
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
    (ψ : AddChar k E) (n : ℕ), LaumonFourierFamilyFieldExtension B U ℓ k e x E b σ ψ n

/-- **A partner of the Fourier family real along `ι'`, in the totally wild range** (Kedlaya,
*Fourier transforms and p-adic Weil II*, §6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonFourierEquinormStableInput`, `ι'`-pure of weight `β`, and `ψ ≠ 1`
there is `N` such that for `n₀ > N` prime to `p`, `a ≠ 0` in a finite extension `k'` of `k`, an
open `V'` of the `t`-line over which the Fourier family of `σ^∨` with `ψ⁻¹` is lisse too, and
`τ : π₁(V', x̄_V) → GL(E)` attached to the Fourier family `G_V` of `σ` (the data of
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`), there is `τ'` with continuous
restriction of scalars such that `τ ⊕ τ'` has Frobenius characteristic polynomials with real
coefficients along `ι'`. The partner is the representation of the dual family twisted by the
unramified character `F_y ↦ #k'^{β deg y}`. -/
public def LaumonFourierFamilyConjugateWildInput : Prop :=
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
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
          j kbar
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ (ψ : AddChar k E), ψ ≠ 1 → ∃ N : ℕ, ∀ n₀ : ℕ, N < n₀ → ¬ p ∣ n₀ →
    ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k'), a ≠ 0 → ∀
      (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
      (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
      (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
      (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
      (pz : (finiteEtaleFiberFunctor z).obj
        (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n₀ a)))
      (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
          (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
      (hσ₂ : Continuous (restrictScalarsRep b ((contragredient σ).comp
        (hz ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
          (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
      (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
      (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
      (fV : V'.1 ⟶ Spec (.of k')) [LocallyOfFiniteType fV],
      IsOpenImmersion (B.inclusion.map jV') →
      B.inclusion.map jV' ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fV →
      IsPullback (B.inclusion.map jU) (B.inclusion.map g')
        (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
      (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
        ((ψ⁻¹).compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ a z pz _ hσ₂ jU g'
          jg').toLAdicSheaf.IsLisse →
      ∀ (xV : GeometricPoint V'.1) {r : ℕ}
        (ρ : EtaleFundamentalGroup V'.1 xV →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
        (φ : (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ a z pz _ hσ₁ jU g'
            jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V' xV ρ hρ)
        (ψ₀ : LAdicSheaf.representationSheaf B V' xV ρ hρ ⟶
          (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ a z pz _ hσ₁ jU g'
            jg').toLAdicSheaf) (N : ℕ)
        (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ : ℕ}
        (τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) E)
        (P : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Q : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ]),
        P * Q = 1 →
        (∀ e' : E, Q * isogenyCoefficientAlgHom B V' xV
          (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
          (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n₀ a z pz _ hσ₁ jU g' jg')
          ρ hρ φ ψ₀ N E hφψ hψφ (algebraMap_conjIntegralSubring_algebraMap _ _) e' * P =
            restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e')) →
        (∀ g : EtaleFundamentalGroup V'.1 xV,
          haveI := compactSpace_etaleFundamentalGroup V'.1 xV
          Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
            (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val) →
        Q * P = 1 →
        ∃ (r' : ℕ) (τ' : EtaleFundamentalGroup V'.1 xV →* GL (Fin r') E),
          Continuous (restrictScalarsRep b τ') ∧ ∀ (y : closedPoints V'.1) (m' : ℕ),
            ι' (((τ (geometricFrobeniusFamily fV xV y)).val.charpoly *
              (τ' (geometricFrobeniusFamily fV xV y)).val.charpoly).coeff m') ∈
                Set.range ((↑) : ℝ → ℂ)

end Stacks.EtaleCohomology

end
