module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityResolved
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeUniversal
public import StacksFrontier.RingTheory.Dualizing.RelativeExistence
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensor
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChange

/-!
# Existence and base change of relative dualizing complexes

`Dualizing.UpperShriekInputs` bundles the two inputs the upper shriek formalism of this tree
carried: `Dualizing.PolynomialEvalDuality`, which is Stacks 0BZH at the evaluation surjections of
polynomial algebras in one variable, and
`Dualizing.PolynomialPresentation.ProjectionCompatibility`, the projection-formula compatibility
of Stacks 0E2A at the square of a presentation. Both are proved, as
`Dualizing.polynomialEvalDuality` and `Dualizing.PolynomialPresentation.projectionCompatibility`;
the second at every presentation follows from `Dualizing.KFlatAlgebraActionEq`, the
projection-formula compatibility at an arbitrary Tor-independent square, proved as
`Dualizing.kFlatAlgebraActionEq`.

This file first restates Stacks 0E2E and Stacks 0E2F over `Dualizing.KFlatAlgebraActionEq`, and
then proves Stacks 0E2F in full by supplying it.

## Main results

* `Dualizing.upperShriekInputs_of_projectionCompatibility` — `Dualizing.UpperShriekInputs`
  follows from the projection-formula compatibility alone.
* `Dualizing.upperShriekInputs_of_kFlatAlgebraActionEq` — and therefore from
  `Dualizing.KFlatAlgebraActionEq`.
* `PolynomialPresentation.nonempty_relativeDualizingComplex_isRelativeDualizingComplex_of_flat`
  (in namespace `Dualizing`) — Stacks 0E2E in the form carrying the projection-formula
  compatibility of Stacks 0E2A; the unconditional form is
  `Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex`.
* `Dualizing.exists_isRelativeDualizingComplex_of_kFlatAlgebraActionEq` — Stacks 0E2F (1)
  carrying only `Dualizing.KFlatAlgebraActionEq`.
* `Dualizing.isRelativeDualizingComplex_baseChange_of_kFlatAlgebraActionEq` and
  `Dualizing.span_derivedBaseChange_diagonalGenerator_of_kFlatAlgebraActionEq` — Stacks 0E2F (2)
  and its "moreover" clause, at an arbitrary relative dualizing complex, carrying only
  `Dualizing.KFlatAlgebraActionEq`; the uniqueness of relative dualizing complexes, Stacks 0E2D,
  through which the source itself passes from the Noetherian model to an arbitrary complex, is
  `Dualizing.IsRelativeDualizingComplex.nonempty_iso`.
* `Dualizing.exists_isRelativeDualizingComplex_of_flat`,
  `Dualizing.IsRelativeDualizingComplex.baseChange` and
  `Dualizing.IsRelativeDualizingComplex.span_derivedBaseChange_diagonalGenerator` — **Stacks
  0E2F**: (1), (2) and the "moreover" clause.

## References

* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

/-- **The bundle of standing open inputs reduces to the projection-formula compatibility.** The
first conjunct of `Dualizing.UpperShriekInputs` is `Dualizing.polynomialEvalDuality`, which is
proved, so only the compatibility of Stacks 0E2A at the square of a presentation remains. -/
theorem upperShriekInputs_of_projectionCompatibility
    (hProj : ∀ (S B : Type u) [CommRing S] [CommRing B] [Algebra S B]
      (p : PolynomialPresentation (algebraMap S B)) (S' : Type u) [CommRing S'] [Algebra S S'],
      p.ProjectionCompatibility S') :
    UpperShriekInputs.{u} :=
  ⟨polynomialEvalDuality, hProj⟩

/-- **The bundle of standing open inputs follows from `Dualizing.KFlatAlgebraActionEq`.** The
surviving conjunct of `Dualizing.UpperShriekInputs` is the projection-formula compatibility of
Stacks 0E2A at the square of a presentation, and
`Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq` supplies it at
every presentation and every target ring from the same compatibility at an arbitrary
Tor-independent square. -/
theorem upperShriekInputs_of_kFlatAlgebraActionEq (hAct : KFlatAlgebraActionEq.{u}) :
    UpperShriekInputs.{u} :=
  upperShriekInputs_of_projectionCompatibility fun _ _ _ _ _ p _ _ _ =>
    PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq hAct p

namespace PolynomialPresentation

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **Stacks 0E2E, in the form carrying the projection-formula compatibility of Stacks 0E2A.**
The tag itself is registered on
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex`, which
carries nothing and subsumes this statement; it is kept for its callers.  For a
flat ring map `R → A` of finite type of Noetherian rings with a polynomial presentation `p`, the
value of the upper shriek functor of `p` at `R` is a relative dualizing complex.

This is an alias of
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex_of_flat`.
The hypotheses `hProjFib` and `hProjSelf` are the projection-formula compatibility of Stacks 0E2A
at the presentation square, read at the residue fields of `R` and at `A`. -/
alias nonempty_relativeDualizingComplex_isRelativeDualizingComplex_of_flat :=
  Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex_of_flat

end PolynomialPresentation

/-- Stacks 0E2F (1) over `Dualizing.KFlatAlgebraActionEq`; the unconditional form, which supplies
it by `Dualizing.kFlatAlgebraActionEq`, is `Dualizing.exists_isRelativeDualizingComplex_of_flat`.
 A flat ring map of finite
presentation `R → A` admits a relative dualizing complex, granted
`Dualizing.KFlatAlgebraActionEq` — the projection-formula compatibility of Stacks 0E2A at an
arbitrary Tor-independent square.

This is `Dualizing.exists_isRelativeDualizingComplex` with its one hypothesis supplied by
`Dualizing.upperShriekInputs_of_kFlatAlgebraActionEq`. The surviving hypothesis does not mention
relative dualizing complexes: it is an equality of two natural transformations attached to a
Tor-independent square of rings. The clause-(2) input
`Dualizing.DiagonalDerivedHomBaseChangeAt` is no longer carried; see
`StacksFrontier.RingTheory.Dualizing.RelativeExistence`. -/
theorem exists_isRelativeDualizingComplex_of_kFlatAlgebraActionEq
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A), IsRelativeDualizingComplex R A K :=
  exists_isRelativeDualizingComplex R A

/-- Stacks 0E2F (2) over `Dualizing.KFlatAlgebraActionEq`; the unconditional form is
`Dualizing.IsRelativeDualizingComplex.baseChange`.
  Let `R → A`
be a flat ring map of finite presentation, `K` a relative dualizing complex for `R → A` and
`R → R'` any ring map.  Then `K' = K ⊗ᴸ_A (A ⊗_R R')` is a relative dualizing complex for
`R' → A ⊗_R R'`, granted `Dualizing.KFlatAlgebraActionEq`.

This is the source's proof: (2) holds at the base change of `φ₁^!(R₁)` from the Noetherian model
by transitivity of derived base change
(`Dualizing.exists_isUniversallyRelativeDualizing_of_projectionCompatibility`), and uniqueness,
[stacks 0E2D] (`Dualizing.IsRelativeDualizingComplex.nonempty_iso`), carries it to any relative
dualizing complex (`Dualizing.isUniversallyRelativeDualizing_of_unique`).
-/
theorem isRelativeDualizingComplex_baseChange_of_kFlatAlgebraActionEq
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) :=
  isUniversallyRelativeDualizing_of_unique
    (fun _ _ hK hL => hK.nonempty_iso hL) hK R'

/-- The "moreover" clause of Stacks 0E2F over `Dualizing.KFlatAlgebraActionEq`; the unconditional
form is `Dualizing.IsRelativeDualizingComplex.span_derivedBaseChange_diagonalGenerator`.
  Let `R → A` be flat of finite presentation, `K` a relative dualizing complex for
`R → A`, and `ξ : A ⟶ K ⊗ᴸ_A (A ⊗_R A)` a generator of the cyclic module
`Hom_{D(A ⊗_R A)}(A, K ⊗ᴸ_A (A ⊗_R A))`.  For every `R → R'` the derived base change of `ξ` along
`A ⊗_R A → A' ⊗_{R'} A'` generates `Hom_{D(A' ⊗_{R'} A')}(A', K' ⊗ᴸ_{A'} (A' ⊗_{R'} A'))`, through
any identifications `eΔ`, `eM` — granted `Dualizing.KFlatAlgebraActionEq`.

The source's proof: at the Noetherian model the degreewise chase makes the degree-zero cycles of
the Hom complex of [stacks 0E1U] commute with base change
(`Dualizing.isGeneratorPreservingAt_of_residueFieldVanishing`), the property is carried to `R → A`
by `Dualizing.IsUniversallyGeneratorPreserving.baseChange` and
`Dualizing.IsUniversallyGeneratorPreserving.of_algEquiv`, and uniqueness, [stacks 0E2D]
(`Dualizing.IsRelativeDualizingComplex.nonempty_iso`), carries it to any relative dualizing
complex (`Dualizing.isUniversallyGeneratorPreserving_of_unique`). -/
theorem span_derivedBaseChange_diagonalGenerator_of_kFlatAlgebraActionEq
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (ξ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K)
    (hξ : Submodule.span (A ⊗[R] A) ({ξ} : Set _) = ⊤) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    ∀ (eΔ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj (diagonalSingle R A) ≅
          diagonalSingle R' (A ⊗[R] R'))
      (eM : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj
              ((diagonalDerivedExtension R A).obj K) ≅
          (diagonalDerivedExtension R' (A ⊗[R] R')).obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)),
      Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
        ({eΔ.inv ≫ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (envelopingBaseChangeRingHom R A R')).functor.map ξ ≫ eM.hom} : Set _) = ⊤ :=
  span_derivedBaseChange_diagonalGenerator_of_isGeneratorPreservingAt
    (isUniversallyGeneratorPreserving_of_unique
      (fun _ _ hK hL => hK.nonempty_iso hL) hK R') ξ hξ

/-- **Stacks Project, Tag 0E2F (1).** A flat ring map of finite presentation `R → A` admits a
relative dualizing complex.

The source's proof: a Noetherian model `R₀ → A₀` of `R → A` has the relative dualizing complex
`φ₀^!(R₀)` of [stacks 0E2E], and its derived base change to `A` is one by (2) at the model and
transitivity of derived base change. -/
@[stacks 0E2F "(1)"]
theorem exists_isRelativeDualizingComplex_of_flat (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A), IsRelativeDualizingComplex R A K :=
  exists_isRelativeDualizingComplex_of_kFlatAlgebraActionEq R A

/-- **Stacks Project, Tag 0E2F (2).** Let `R → A` be a flat ring map of finite presentation, `K`
a relative dualizing complex for `R → A` and `R → R'` any ring map. Then
`K' = K ⊗ᴸ_A (A ⊗_R R')` is a relative dualizing complex for `R' → A ⊗_R R'`. -/
@[stacks 0E2F "(2)"]
theorem IsRelativeDualizingComplex.baseChange {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsRelativeDualizingComplex R A K)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) :=
  isRelativeDualizingComplex_baseChange_of_kFlatAlgebraActionEq K hK R'

/-- **Stacks Project, Tag 0E2F, the "moreover" clause.** Let `R → A` be flat of finite
presentation, `K` a relative dualizing complex for `R → A`, and `ξ : A ⟶ K ⊗ᴸ_A (A ⊗_R A)` a
generator of the cyclic module `Hom_{D(A ⊗_R A)}(A, K ⊗ᴸ_A (A ⊗_R A))`. For every `R → R'` the
derived base change of `ξ` along `A ⊗_R A → A' ⊗_{R'} A'` generates
`Hom_{D(A' ⊗_{R'} A')}(A', K' ⊗ᴸ_{A'} (A' ⊗_{R'} A'))`, through any identifications `eΔ` of the
base change of `A` with `A'` and `eM` of the base change of `K ⊗ᴸ_A (A ⊗_R A)` with
`K' ⊗ᴸ_{A'} (A' ⊗_{R'} A')`. -/
@[stacks 0E2F "moreover clause"]
theorem IsRelativeDualizingComplex.span_derivedBaseChange_diagonalGenerator {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsRelativeDualizingComplex R A K)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (ξ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K)
    (hξ : Submodule.span (A ⊗[R] A) ({ξ} : Set _) = ⊤) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    ∀ (eΔ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj (diagonalSingle R A) ≅
          diagonalSingle R' (A ⊗[R] R'))
      (eM : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj
              ((diagonalDerivedExtension R A).obj K) ≅
          (diagonalDerivedExtension R' (A ⊗[R] R')).obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)),
      Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
        ({eΔ.inv ≫ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (envelopingBaseChangeRingHom R A R')).functor.map ξ ≫ eM.hom} : Set _) = ⊤ :=
  span_derivedBaseChange_diagonalGenerator_of_kFlatAlgebraActionEq K hK R' ξ hξ

end Dualizing

end
