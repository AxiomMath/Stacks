module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLineAbsIrrInputProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssemblyAbsIrrCharNe

/-!
# Weil II: the weights of compactly supported cohomology

[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Deligne, Weil II): for `ρ` satisfying the
conclusions of Deligne's conjecture, the eigenvalues of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_ρ)` are
algebraic numbers of absolute value `q ^ (w / 2)` with `w ∈ ℤ`, `w ≤ i`, and `w = i` when `X` is
smooth and proper. This is `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_absIrr'` with the
absolute irreducibility of Laumon's Fourier family discharged by
`Stacks.EtaleCohomology.laumonFourierLineAbsIrrInput'`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.weightBound`.

## Implementation notes

The cohomology groups in the statement are those of
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_absIrr'`, defined in the standard model
`HasDerivedCategory.standard` of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section WeightBound

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **Weil II** ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, *La conjecture
de Weil II*). Let `k` be a finite field with `p ^ q` elements, `k̄` an algebraic closure, `ℓ ≠ p` a
prime, `X` connected and separated of finite type over `k` with a compactification `j`, and
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous, satisfying the conclusions of Deligne's conjecture
(`Stacks.EtaleCohomology.HasDeligneConclusions`) along every embedding `ι : ℚ_ℓ → ℂ`. Then for
every `i` the eigenvalues of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` (finite dimensional) are algebraic
numbers of absolute value `(p ^ q) ^ (w / 2)` along `ι` with `w ∈ ℤ`, `w ≤ i`; and if `X` is smooth
and proper over `k` (the source asks for projective), then `w = i`. -/
@[stacks 03VH "the whole tag: the eigenvalues of pi_X^* on H^i_c(X_kbar, F_rho) are algebraic \
numbers of absolute value q^(w/2) with w <= i an integer, and w = i for X smooth and proper \
(the source says projective), for rho satisfying the conclusions of Deligne's conjecture \
along every embedding of Q_ell in C"]
theorem LAdicSheaf.weightBound
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    (∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
        ℓ f j kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyMixedOfWeightLE (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) ∧
    (IsProper f → Smooth f → ∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
        ℓ f j kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyPureOfWeight (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) :=
  LAdicSheaf.weightBound_of_absIrr' B ℓ laumonFourierLineAbsIrrInput' kbar p q hcard hℓ X f j x ρ
    hρ hD

end WeightBound

end Stacks.EtaleCohomology

end
