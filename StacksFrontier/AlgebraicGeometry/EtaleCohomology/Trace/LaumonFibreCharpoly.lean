module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineAssembly

/-!
# A property of the Frobenius characteristic polynomials of the fibres of the Fourier family

`Stacks.EtaleCohomology.LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D Φ` says that for every datum of
`Stacks.EtaleCohomology.LaumonFibrePure` (a finite extension `k'` of `k`, `(a, c) ∈ k'²` with
`D(a, c) ≠ 0`, …) the `E`-linear characteristic polynomial `P` of the Frobenius of `k'`
(`#k' = q`) on `H¹_c(𝔸¹_k̄', ℱ_σ ⊗ L_ψ'(a xⁿ + c x) ⊗ ℚ_ℓ)` satisfies `Φ q P`. The purity of the
fibres is the instance `Φ q P := ∀ z, P(z) = 0 along ι' → ‖z‖ = q ^ ((β + 1) / 2)`
(`Stacks.EtaleCohomology.laumonFibrePure_iff_laumonFibreCharpoly`), and such properties combine
(`Stacks.EtaleCohomology.LaumonFibreCharpoly.of_and`), which is how the reduction of L7
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) assembles its pieces.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFibreCharpoly`.

## Main results

* `Stacks.EtaleCohomology.laumonFibrePure_iff_laumonFibreCharpoly`.
* `Stacks.EtaleCohomology.LaumonFibreCharpoly.of_and`.
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
  (ι' : E →+* ℂ) (β : ℤ) (ψ : AddChar k E) (n : ℕ)

/-- **A property of the Frobenius characteristic polynomials of the fibres of the Fourier family
off `D = 0`**: for every datum of `Stacks.EtaleCohomology.LaumonFibrePure` (a finite extension
`k'` of `k`, `(a, c) ∈ k'²` with `D(a, c) ≠ 0`, a geometric point of `𝔸¹_{k'}` over `x̄`, …), the
`E`-linear characteristic polynomial `P` of the Frobenius of `k'` on
`H¹_c(𝔸¹_k̄', ℱ_σ ⊗ L_ψ'(a xⁿ + c x) ⊗ ℚ_ℓ)` satisfies `Φ (#k') P`. -/
public def LaumonFibreCharpoly (D : MvPolynomial (Fin 2) k) (Φ : ℕ → Polynomial E → Prop) :
    Prop :=
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
      Φ (p ^ n')
        (LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') x' b _
            hτ).rationalGeometricCompactlySupportedFrobenius
          (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 E p n' hcard'))

omit [Fintype k] in
/-- **The purity of the fibres is a property of their Frobenius characteristic polynomials.** -/
public theorem laumonFibrePure_iff_laumonFibreCharpoly (D : MvPolynomial (Fin 2) k) :
    LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n D ↔
      LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D fun q P =>
        ∀ z : ℂ, (P.map ι').IsRoot z → ‖z‖ = (q : ℝ) ^ (((β + 1 : ℤ) : ℝ) / 2) :=
  Iff.rfl

variable {B U ℓ k e x E b σ ψ n}

omit [Fintype k] in
/-- **Properties of the fibres combine**: if `Φ` holds off `D₁ = 0` and `Ψ` off `D₂ = 0`, and
`D(a, c) ≠ 0` forces `D₁(a, c) ≠ 0` and `D₂(a, c) ≠ 0` over every extension, then every
consequence `Χ` of `Φ ∧ Ψ` holds off `D = 0`. -/
public theorem LaumonFibreCharpoly.of_and {D D₁ D₂ : MvPolynomial (Fin 2) k}
    {Φ Ψ Χ : ℕ → Polynomial E → Prop}
    (h₁ : LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D₁ Φ)
    (h₂ : LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D₂ Ψ)
    (hD : ∀ (k' : Type u) [Field k'] [Algebra k k'] (a c : k'),
      MvPolynomial.eval ![a, c] (MvPolynomial.map (algebraMap k k') D) ≠ 0 →
        MvPolynomial.eval ![a, c] (MvPolynomial.map (algebraMap k k') D₁) ≠ 0 ∧
        MvPolynomial.eval ![a, c] (MvPolynomial.map (algebraMap k k') D₂) ≠ 0)
    (h : ∀ q P, Φ q P → Ψ q P → Χ q P) :
    LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D Χ := by
  intro k' _ _ _ hX' _ _ x' hx' a c hac p₀ hτ _ _ _ j' kbar' _ _ _ p n' _ _ hcard' _
  exact h _ _ (h₁ k' hX' x' hx' a c (hD k' a c hac).1 p₀ hτ j' kbar' p n' hcard')
    (h₂ k' hX' x' hx' a c (hD k' a c hac).2 p₀ hτ j' kbar' p n' hcard')

end Fibre

end Stacks.EtaleCohomology

end
