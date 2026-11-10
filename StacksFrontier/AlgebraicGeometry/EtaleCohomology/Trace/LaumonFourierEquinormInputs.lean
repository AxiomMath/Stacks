module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineAbsIrr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePurityStable

/-!
# The geometric inputs of the equal absolute values of the Fourier family

The equal absolute values of the fibres of Laumon's Fourier family for `σ` which stays
absolutely irreducible (`Stacks.EtaleCohomology.LaumonFourierEquinormStableInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) are read, at fixed `(k', a)`, from Weil II
1.5.1 on the `c`-line (`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isIotaRealizable_curve`)
applied to the representation `τ` of the Fourier family `G_V`. Besides the absolute irreducibility
of `τ` (`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`) and `E`-linear proper base change
at the stalks (`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearInput`), this uses:

* `Stacks.EtaleCohomology.LaumonFourierLineLisseInput`: a curve `D = 0` of the `(a, c)`-plane,
  uniform in `(k', a)`, off which the family is lisse, with the open `V' = D(D(a, t))`,
  `U' = pr₂⁻¹(V')` and the compactifications (Laumon's local theory: for `a ≠ 0` and `n` larger
  than the slopes of `σ` at `∞`, `ℱ_σ ⊗ L_ψ(a xⁿ)` is totally wild at `∞` and its Fourier
  transform is lisse on `𝔸¹`). It is also the missing supplier of `V'`, `U'`, `jg'` for the family
  of `Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep`.
* `Stacks.EtaleCohomology.LaumonFourierFamilyFibreInput`: the identification of the fibres of the
  family with the fibres of `Stacks.EtaleCohomology.LaumonFibreCharpoly`, for all their data.
* `Stacks.EtaleCohomology.LaumonFourierFamilyConjugateInput`: a partner `τ'` with `τ ⊕ τ'` real
  along `ι'` (the transform of `σ^∨ ⊗ χ` with `ψ⁻¹`, `χ` the unramified character with
  `F_y ↦ q^{β deg y}`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineLisse`,
  `Stacks.EtaleCohomology.LaumonFourierLineLisseInput`.
* `Stacks.EtaleCohomology.LaumonFourierFamilyFibre`,
  `Stacks.EtaleCohomology.LaumonFourierFamilyFibreInput`.
* `Stacks.EtaleCohomology.LaumonFourierFamilyConjugateInput`.
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

/-- **The Fourier family at fixed `a` is lisse off `D(a, t) = 0`, on an affine curve**: for every
finite extension `k'` of `k` and `a ∈ k'`, there are an open `V' = D(D(a, t))` of the `t`-line
(the zeros of `D(a, t) ∈ k'[t]` removed), `U' = pr₂⁻¹(V')`, `g' : U' → V'` the restriction of `pr₂`
with a compactification, and the structure of a smooth geometrically connected affine curve on
`V'` over `k'` with a compactification, such that `G_V = R¹g'_!(pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t))|_{U'}`
(`Stacks.EtaleCohomology.laumonFourierRestrictedHigherDirectImage`, `ψ' = ψ ∘ Tr_{k'/k}`) is lisse.
Stated in continuation-passing form. -/
public def LaumonFourierLineLisse (D : MvPolynomial (Fin 2) k) : Prop :=
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
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom)))) (C : Prop),
    (∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
      [IsAffine V'.1] (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
      (fV : V'.1 ⟶ Spec (.of k')) [LocallyOfFiniteType fV] [QuasiCompact fV] [IsSeparated fV]
      [SmoothOfRelativeDimension 1 fV] (_ : CompactificationOf (Over.mk fV)),
      IsOpenImmersion (B.inclusion.map jV') →
      Set.range (B.inclusion.map jV') = (PrimeSpectrum.basicOpen (MvPolynomial.eval₂
        (Polynomial.C.comp (algebraMap k k')) ![Polynomial.C a, Polynomial.X] D) :
          Set (PrimeSpectrum (Polynomial k'))) →
      B.inclusion.map jV' ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))) = fV →
      IsPullback (B.inclusion.map jU) (B.inclusion.map g')
        (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
      (∀ (Ω : Type u) [Field Ω] [Algebra k' Ω] [IsAlgClosed Ω],
        ConnectedSpace ↥(Limits.pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k' Ω))))) →
      (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
        (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁ jU g'
          jg').toLAdicSheaf.IsLisse → C) → C

/-- **The fibres of the Fourier family at fixed `a`, for all choices** (the `∀`-form of
`Stacks.EtaleCohomology.LaumonFamilyFibreLinearInput` for the kernel `a xⁿ + x t`): for an open
`V'` of the `t`-line, `U' = pr₂⁻¹(V')`, a point `v` of `V'` with `κ(v) = k'` lying over `t = c`,
and any fibre `Y` of `U' → V'` over `v` with a compactification, the `E`-linear Frobenius of `κ(v)`
on `H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` (`K` the Fourier family sheaf) has the characteristic polynomial of the
Frobenius of `k'` on the fibre `H¹_c(𝔸¹_k̄', ℱ_σ ⊗ L_ψ'(a xⁿ + c x) ⊗ ℚ_ℓ)` of
`Stacks.EtaleCohomology.LaumonFibreCharpoly`, for EVERY choice of the data of that fibre (geometric
point over `x̄`, point of the Artin–Schreier cover, compactification, algebraic closure). -/
public def LaumonFourierFamilyFibre : Prop :=
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
        (laumonFourierFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom)
          n a z pz _ hσ₁))
    ∀ [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY
        jY kbarv K.toLAdicSheaf 1)] (c : k'),
    Function.Bijective ((laumonPointRingHom jV' v).comp Polynomial.C) →
    laumonPointRingHom jV' v Polynomial.X = laumonPointRingHom jV' v (Polynomial.C c) →
    ∀ (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    [IsNoetherian (Spec (.of (Polynomial k')))] [ConnectedSpace (Spec (.of (Polynomial k')))]
    (x' : GeometricPoint (Spec (.of (Polynomial k'))))
    (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
      inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor x').obj
        (Stacks.ArtinSchreier.cover k' (Polynomial k')
          (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)))
      (hτ : Continuous (restrictScalarsRep b (characterTwist
        (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
          (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
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
      letI := K.rationalCohomologyModule fY jY kbarv 1 E
      haveI := K.rationalCohomologyModule_isScalarTower fY jY kbarv 1 E
        (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY
          kbarv K.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      (K.rationalGeometricCompactlySupportedFrobenius fY jY kbarv 1 E pv nv hcardv).charpoly =
        (LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
            hτ).rationalGeometricCompactlySupportedFrobenius
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E p n' hcard'))

end Family

/-- **The Fourier family at fixed `a` is lisse off a curve `D = 0`, uniform in `(k', a)`**
(Laumon; Kedlaya, *Fourier transforms and p-adic Weil II*, §6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonFourierEquinormStableInput` and `ψ ≠ 1` there is `N` such that for
`n > N` prime to `p` there is `D ≠ 0` with `Stacks.EtaleCohomology.LaumonFourierLineLisse`. -/
public def LaumonFourierLineLisseInput : Prop :=
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
    (p n : ℕ) [Fact p.Prime] [CharP k p], Fintype.card k = p ^ n → ∀ (_ : ℓ ≠ p)
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
      ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ LaumonFourierLineLisse B U ℓ k e x E b σ ψ n D

/-- **The fibres of the Fourier family at fixed `a`, for all choices**: the proposition
`Stacks.EtaleCohomology.LaumonFourierFamilyFibre` for all data. -/
public def LaumonFourierFamilyFibreInput : Prop :=
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
    (ψ : AddChar k E) (n : ℕ), LaumonFourierFamilyFibre B U ℓ k e x E b σ ψ n

/-- **A partner of the Fourier family real along `ι'`** (Kedlaya, *Fourier transforms and p-adic
Weil II*, §6.4: the Fourier family is `ι'`-real together with the transform of the dual): for
`σ` as in `Stacks.EtaleCohomology.LaumonFourierEquinormStableInput`, `ι'`-pure of weight `β`, and
`τ : π₁(V', x̄_V) → GL(E)` attached to the Fourier family `G_V` at fixed `a` over an open `V'` of
the `t`-line (the data of `Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`), there is
`τ'` with continuous restriction of scalars such that `τ ⊕ τ'` has Frobenius characteristic
polynomials with real coefficients along `ι'`. The partner is the representation of the Fourier
family of `σ^∨ ⊗ χ` with `ψ⁻¹` (`χ` the unramified character with `F_y ↦ q^{β deg y}`), whose
Frobenius roots are the complex conjugates of those of `τ` by the trace formula on the fibres. -/
public def LaumonFourierFamilyConjugateInput : Prop :=
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
    (p n : ℕ) [Fact p.Prime] [CharP k p], Fintype.card k = p ^ n → ∀ (_ : ℓ ≠ p)
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
    ∀ (ψ : AddChar k E), ψ ≠ 1 → ∀ (n₀ : ℕ) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
      (a : k')
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
