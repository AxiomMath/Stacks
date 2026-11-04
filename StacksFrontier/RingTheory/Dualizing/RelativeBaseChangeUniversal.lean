module

public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeTransitivity
public import StacksFrontier.RingTheory.Dualizing.RelativeExistence
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorTransitivity

/-!
# The relative dualizing complex of the Noetherian model stays one under every base change

Let `R → A` be flat of finite presentation.  The source proves [stacks 0E2F] by reducing to the
Noetherian case: `A = A₁ ⊗_{R₁} R` for a flat map of finite type `R₁ → A₁` of Noetherian rings,
`ω₁ = φ^!(R₁)` is a relative dualizing complex for `R₁ → A₁` ([stacks 0E2E]) which stays one under
every base change `R₁ → R'` (the Noetherian case of clause (2)), and therefore so does
`ω₁ ⊗ᴸ_{A₁} A` for `R → A`, by transitivity of derived base change.  This file assembles that
argument.  Clause (2) for an *arbitrary* relative dualizing complex then follows from uniqueness,
[stacks 0E2D], exactly as in the source.

## Main results

* `Dualizing.exists_isUniversallyRelativeDualizing_of_projectionCompatibility` — a relative
  dualizing complex that stays one under every base change, and whose diagonal generators stay
  generators under every base change, exists.
* `Dualizing.isUniversallyRelativeDualizing_of_unique` and
  `Dualizing.isUniversallyGeneratorPreserving_of_unique` — granted uniqueness of relative
  dualizing complexes for `R → A`, every relative dualizing complex has both properties.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **A relative dualizing complex stable under every base change exists.**  For `R → A` flat of
finite presentation there is a relative dualizing complex `K` for `R → A` such that
`K ⊗ᴸ_A (A ⊗_R R')` is a relative dualizing complex for `R' → A ⊗_R R'` for every ring map
`R → R'`.

The hypothesis `hProj` is the projection-formula compatibility of [stacks 0E2A] at the square of
a presentation. -/
theorem exists_isUniversallyRelativeDualizing_of_projectionCompatibility
    (hProj : ∀ (S B : Type u) [CommRing S] [CommRing B] [Algebra S B]
      (q : PolynomialPresentation (algebraMap S B)) (S' : Type u) [CommRing S'] [Algebra S S'],
      q.ProjectionCompatibility S')
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A),
      IsRelativeDualizingComplex R A K ∧ IsUniversallyRelativeDualizing R A K ∧
        IsUniversallyGeneratorPreserving R A K := by
  classical
  obtain ⟨R₁, A₁, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := exists_noetherianFlatModel R A
  let : Algebra R (A₁ ⊗[R₁] R) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨p₁⟩ := nonempty_polynomialPresentation (algebraMap R₁ A₁)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hflat₁ : (algebraMap R₁ A₁).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hK₁ := p₁.relativeDualizingComplex_isRelativeDualizingComplex_of_flat hflat₁
    (fun t => hProj R₁ A₁ p₁ t.asIdeal.ResidueField) (hProj R₁ A₁ p₁ A₁)
  let : Algebra.FiniteType R₁ (A₁ ⊗[R₁] A₁) :=
    Algebra.FiniteType.trans (R := R₁) (S := A₁) (A := A₁ ⊗[R₁] A₁) inferInstance inferInstance
  let : IsNoetherianRing (A₁ ⊗[R₁] A₁) :=
    Algebra.FiniteType.isNoetherianRing R₁ (A₁ ⊗[R₁] A₁)
  obtain ⟨P, F, E, dP, dF, hPLE, hPproj, hPkflat, ⟨eP⟩, hFLE, hFflat, ⟨eF⟩, hE, hEflat, hEfin⟩ :=
    exists_diagonalHomComplexRepresentation R₁ A₁ _ hK₁
  have := hPLE
  have := hPproj
  have := hFLE
  have hU₁ : IsUniversallyRelativeDualizing R₁ A₁ _ :=
    fun R' _ _ => isRelativeDualizingComplex_baseChange_upperShriek_of_representation R₁ A₁ R' p₁
      hProj P dP hPkflat eP F dF hFflat eF E hE hEflat hEfin
  have hG₁ : IsUniversallyGeneratorPreserving R₁ A₁ _ :=
    fun R' _ _ => isGeneratorPreservingAt_of_residueFieldVanishing R₁ A₁ R' _ hK₁
      (fun t _ j hj =>
        isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek R₁ A₁ p₁ hflat₁ hProj
          t j hj)
  let : Module.Flat R (A₁ ⊗[R₁] R) := flat_baseChange R₁ A₁ R
  let : Algebra.FinitePresentation R (A₁ ⊗[R₁] R) :=
    Algebra.FinitePresentation.equiv (baseChangeComm R₁ A₁ R)
  exact ⟨_, RelativeExistence.isRelativeDualizingComplex_of_algEquiv e _ (hU₁ R),
    (hU₁.baseChange (R := R)).of_algEquiv e,
    (hG₁.baseChange (R := R) hK₁).of_algEquiv e (hU₁ R)⟩

/-- **Clause (2) of [stacks 0E2F] from uniqueness.**  If any two relative dualizing complexes for
`R → A` are isomorphic — which is [stacks 0E2D] — then every relative dualizing complex for
`R → A` stays one under every base change.

This is the last step of the source's reduction: "the uniqueness of relative dualizing complexes
then shows that this holds for any relative dualizing complex".  The complex it is compared with
is the one of `Dualizing.exists_isUniversallyRelativeDualizing_of_projectionCompatibility`. -/
theorem isUniversallyRelativeDualizing_of_unique
    (hProj : ∀ (S B : Type u) [CommRing S] [CommRing B] [Algebra S B]
      (q : PolynomialPresentation (algebraMap S B)) (S' : Type u) [CommRing S'] [Algebra S S'],
      q.ProjectionCompatibility S')
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (huniq : ∀ K L : DerivedCategory (ModuleCat.{u} A), IsRelativeDualizingComplex R A K →
      IsRelativeDualizingComplex R A L → Nonempty (K ≅ L))
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsRelativeDualizingComplex R A K) :
    IsUniversallyRelativeDualizing R A K := by
  obtain ⟨L, hL, hLU, -⟩ :=
    exists_isUniversallyRelativeDualizing_of_projectionCompatibility hProj R A
  obtain ⟨e⟩ := huniq L K hL hK
  exact hLU.of_iso e

/-- **The "moreover" clause of [stacks 0E2F] from uniqueness.**  If any two relative dualizing
complexes for `R → A` are isomorphic — which is [stacks 0E2D] — then for every relative dualizing
complex and every `R → R'`, derived base change preserves the generators of the diagonal Hom
module.  The complex it is compared with is the one of
`Dualizing.exists_isUniversallyRelativeDualizing_of_projectionCompatibility`. -/
theorem isUniversallyGeneratorPreserving_of_unique
    (hProj : ∀ (S B : Type u) [CommRing S] [CommRing B] [Algebra S B]
      (q : PolynomialPresentation (algebraMap S B)) (S' : Type u) [CommRing S'] [Algebra S S'],
      q.ProjectionCompatibility S')
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (huniq : ∀ K L : DerivedCategory (ModuleCat.{u} A), IsRelativeDualizingComplex R A K →
      IsRelativeDualizingComplex R A L → Nonempty (K ≅ L))
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsRelativeDualizingComplex R A K) :
    IsUniversallyGeneratorPreserving R A K := by
  obtain ⟨L, hL, -, hLG⟩ :=
    exists_isUniversallyRelativeDualizing_of_projectionCompatibility hProj R A
  obtain ⟨e⟩ := huniq L K hL hK
  exact hLG.of_iso e

end Dualizing

end
