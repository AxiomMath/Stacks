module

public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Dualizing.RelativeAlgEquivTransport
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChange
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDiagonalRepresentation
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingDiagonal
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Existence of a relative dualizing complex

Let `R → A` be a flat ring map of finite presentation.  This file proves that there is a
relative dualizing complex for `R → A` in the sense of [stacks 0E2C], which is part (1) of
[stacks 0E2F].

## Main definitions

* `Dualizing.UpperShriekInputs` — the library's two standing open inputs for the upper shriek
  formalism, quantified over the Noetherian stage the proof produces; see below.

## Main results

* `Dualizing.exists_isRelativeDualizingComplex` — [stacks 0E2F] (1), unconditionally; the
  Noetherian-stage lemmas it uses no longer take `Dualizing.UpperShriekInputs`.

## The proof

The source reduces to the Noetherian case, and so does this file.  By [stacks 00R1],
`Algebra.exists_subring_finiteType_int_isPushout_isBaseChange`, there is a subring `R₀ ⊆ R` of
finite type over `ℤ` and an `R₀`-algebra `A₀` of finite type with `A = R ⊗_{R₀} A₀`.  In the
directed system of finite type `ℤ`-subalgebras of `R` containing `R₀` the algebra becomes flat at
some stage, by the localized flatness argument of [stacks 02JO],
`Algebra.FiniteTypeSystem.exists_flat_stage`: flatness of `A` over `R` gives flatness of each
localization, so the flat locus of the stage eventually exhausts `Spec`.  At that stage `R₁ → A₁`
is a flat map of finite type of Noetherian rings — `R₁` is of finite type over `ℤ` and `A₁` of
finite type over `R₁`, so both are Noetherian — and [stacks 0E2E],
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex_of_flat`,
says that `ω^•_{A₁/R₁} = φ^!(R₁)` is a relative dualizing complex there.  Base change along
`R₁ → R` is clause (2), in the form
`Dualizing.isRelativeDualizingComplex_baseChange_upperShriek_of_representation`, and gives a
relative dualizing complex for `R → A₁ ⊗_{R₁} R`.  Finally `A₁ ⊗_{R₁} R ≅ A` as `R`-algebras, and
being a relative dualizing complex transports along such an isomorphism, which is
`Dualizing.RelativeExistence.isRelativeDualizingComplex_of_algEquiv` of
`StacksFrontier.RingTheory.Dualizing.RelativeAlgEquivTransport`.

## The bundle `Dualizing.UpperShriekInputs`

Everything above is proved, and `Dualizing.exists_isRelativeDualizingComplex` carries no
hypothesis.  This file still defines the bundle the theorem once carried; it does not mention
`Dualizing.IsRelativeDualizingComplex` or any part of the conclusion.

`Dualizing.UpperShriekInputs` bundles the two standing open inputs of the upper shriek formalism:
`Dualizing.PolynomialEvalDuality`, which is [stacks 0BZH] at the evaluation surjections of
polynomial algebras in one variable and the one input of [stacks 0BZJ]; and
`Dualizing.PolynomialPresentation.ProjectionCompatibility`, the projection-formula compatibility
of [stacks 0E2A] at the square of a presentation, which every case of [stacks 0BZV] carries in
this library.  Only the second is still open, and it is exactly the hypotheses `hProjFib` and
`hProjSelf` of [stacks 0E2E]; the first is proved as `Dualizing.polynomialEvalDuality`, and
`Dualizing.upperShriekInputs_of_projectionCompatibility` of
`StacksFrontier.RingTheory.Dualizing.RelativeExistenceInputs` reduces the bundle to the second
conjunct alone.

It is quantified over the ring data rather than instantiated, because the Noetherian stage
`R₁ → A₁` and its presentation are produced inside the proof and are not available in the
statement.

### The clause-(2) input is proved

This statement does not carry the hypothesis `hbc`, the derived-Hom base-change map of
[stacks 0E1X] at the diagonal square read at the relative dualizing complex the Noetherian stage
produces — `Dualizing.DiagonalDerivedHomBaseChangeAt`, which is what
`Dualizing.isRelativeDualizingComplex_baseChange_at` consumes, the
clause-(2) side being complete at the object this proof reads it at.  The three pieces:

* [stacks 0E1U], `StacksDraft.RelativelyPerfect.exists_homComplex_representation`, applied at the
  diagonal square to produce the representatives `P^•`, `F^•` and the bounded below complex `E^•`
  — `Dualizing.exists_diagonalHomComplexRepresentation` of
  `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDiagonalRepresentation`;
* the degreewise chase on `E^•`, together with its degree-zero generator, which is
  `Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldVanishing` of
  `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDegreeZero`;
* the residue-field vanishing that chase consumes — the vanishing of the cohomology of
  `RHom_{B_𝔭}(A_𝔭, K_𝔭 ⊗ᴸ_{A_𝔭} B_𝔭)` outside degree zero at the residue fields `κ(𝔭)` of the
  base, which is the Noetherian case of the clause itself.  The source takes it from
  [stacks 0BZV] and [stacks 0E2E], and so does
  `Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek` of
  `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian`: each `κ(𝔭)` is Noetherian, so
  the base change of `ω^•_{A/R}` to it is a relative dualizing complex by those two tags, whose
  diagonal condition is exactly the vanishing.  What that carries is the projection-formula
  compatibility of [stacks 0E2A] — the same proposition `hUS` already bundles.

The reason the residue-field
vanishing could be discharged where the clause-(2) input could not is that it is read at
`K = ω^•_{A/R} = φ^!(R)` rather than at an arbitrary relative dualizing complex: identifying an
arbitrary one with `φ^!(R)` is [stacks 0E2D], which this library does not have.  The Noetherian
stage of this proof produces `φ^!(R₁)` itself, so no such identification is needed here.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 00R1](https://stacks.math.columbia.edu/tag/00R1)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

open RelativeExistence

/-- **The two inputs for the upper shriek formalism that this library once carried**, quantified
over every polynomial presentation and every target ring.

The first conjunct is `Dualizing.PolynomialEvalDuality`, which is [stacks 0BZH] at the evaluation
surjections of polynomial algebras in one variable and the one input of [stacks 0BZJ]; it is no
longer open, being proved as `Dualizing.polynomialEvalDuality`, so
`Dualizing.upperShriekInputs_of_projectionCompatibility` of
`StacksFrontier.RingTheory.Dualizing.RelativeExistenceInputs` supplies it and reduces this bundle to
the second conjunct alone.  The second is
`Dualizing.PolynomialPresentation.ProjectionCompatibility`, the projection-formula
compatibility of [stacks 0E2A] at the square of a presentation, which every case of
[stacks 0BZV] carries in this library and which is still open; it is the hypotheses `hProjFib`
and `hProjSelf` of [stacks 0E2E].

Neither conjunct mentions relative dualizing complexes: the first is a statement about derived
Hom along evaluation maps, the second a property of the Tor-independent square of a presentation
alone. -/
def UpperShriekInputs : Prop :=
  PolynomialEvalDuality.{u} ∧
    ∀ (S B : Type u) [CommRing S] [CommRing B] [Algebra S B]
      (p : PolynomialPresentation (algebraMap S B)) (S' : Type u) [CommRing S'] [Algebra S S'],
      p.ProjectionCompatibility S'

/-- **The Noetherian model of [stacks 0E2F].**  A flat ring map of finite presentation `R → A` is
the base change of a flat ring map of finite presentation `R₁ → A₁` of Noetherian rings along a
ring map `R₁ → R`: there is an isomorphism of `R`-algebras `A₁ ⊗_{R₁} R ≅ A`.

This is the reduction to the Noetherian case of the source.  By [stacks 00R1],
`Algebra.exists_subring_finiteType_int_isPushout_isBaseChange`, `A` is defined over a subring `R₀`
of finite type over `ℤ`; in the directed system of finite type `ℤ`-subalgebras of `R` containing
`R₀` the model becomes flat at some stage `R₁`, by [stacks 02JO],
`Algebra.FiniteTypeSystem.exists_flat_stage`; and `R₁`, `A₁` are Noetherian, being of finite type
over `ℤ`. -/
@[sga "1 VIII 3.6" "(ii) ⇒ (i), partial"]
theorem exists_noetherianFlatModel (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] :
    ∃ (R₁ A₁ : Type u) (_ : CommRing R₁) (_ : CommRing A₁) (_ : Algebra R₁ A₁)
      (_ : Algebra R₁ R),
      IsNoetherianRing R₁ ∧ IsNoetherianRing A₁ ∧ Module.Flat R₁ A₁ ∧
        Algebra.FinitePresentation R₁ A₁ ∧
        letI : Algebra R (A₁ ⊗[R₁] R) := Algebra.TensorProduct.rightAlgebra
        Nonempty (A₁ ⊗[R₁] R ≃ₐ[R] A) := by
  classical
  obtain ⟨R₀, A₀, M₀, _, _, _, _, _, _, _, _, f, hftR₀, hftA₀, _, hpush, hbase⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := R) (S := A) A
  obtain ⟨i, hi⟩ := by
    let : Module A₀ A := (Algebra.toModule : Module A₀ A)
    let : IsScalarTower A₀ A A :=
      IsScalarTower.of_algebraMap_smul fun _ _ => by simp [Algebra.smul_def]
    have hflat (q : PrimeSpectrum A) :
        Module.Flat R (TensorProduct A₀ (Localization.AtPrime q.asIdeal) A₀) :=
      (Module.flat_localizedModule_atPrime_iff_of_isBaseChange (Algebra.linearMap A₀ A)
          (IsBaseChange.linearMap A₀ A) q.asIdeal).mp
        (Module.Flat.of_isLocalizedModule_of_tower (R := R) q.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl A))
    exact Algebra.FiniteTypeSystem.exists_flat_stage R₀ A₀ A₀ hflat
  let R₁ := Algebra.FiniteTypeSystem.Base R₀ i
  let A₁ := Algebra.FiniteTypeSystem.Ring R₀ A₀ i
  have : Algebra.IsPushout R₁ R A₁ A :=
    Algebra.FiniteTypeSystem.ringToRing_isPushout R₀ A₀ i
  let : Algebra R (A₁ ⊗[R₁] R) := Algebra.TensorProduct.rightAlgebra
  let eComm : A₁ ⊗[R₁] R ≃ₐ[R] R ⊗[R₁] A₁ :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R₁ R A₁).toRingEquiv.symm)
      (fun r => by
        apply (Algebra.TensorProduct.comm R₁ R A₁).injective
        change (Algebra.TensorProduct.comm R₁ R A₁)
            (algebraMap R (R ⊗[R₁] A₁) r) =
          algebraMap R (A₁ ⊗[R₁] R) r
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
          Algebra.TensorProduct.comm_tmul]
        rfl)
  let e : A₁ ⊗[R₁] R ≃ₐ[R] A :=
    eComm.trans (Algebra.IsPushout.equiv R₁ R A₁ A)
  let : Algebra A₀ A₁ := Algebra.TensorProduct.rightAlgebra
  let eTensorA₀ : (A₁ ⊗[A₀] A₀) ≃ₗ[A₀] A₁ :=
    (Algebra.TensorProduct.rid A₀ A₀ A₁).toLinearEquiv
  let eTensor : (A₁ ⊗[A₀] A₀) ≃ₗ[R₁] A₁ :=
    { toEquiv := eTensorA₀.toEquiv
      map_add' := eTensorA₀.map_add
      map_smul' := by
        intro r z
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
            change (Algebra.TensorProduct.rid A₀ A₀ A₁)
                (r • (x ⊗ₜ[A₀] y)) =
              r • (Algebra.TensorProduct.rid A₀ A₀ A₁) (x ⊗ₜ[A₀] y)
            rw [TensorProduct.smul_tmul', Algebra.TensorProduct.rid_tmul,
              Algebra.TensorProduct.rid_tmul]
            simp only [Algebra.smul_def]
            ring
        | add x y hx hy =>
            change eTensorA₀ (r • (x + y)) = r • eTensorA₀ (x + y)
            change eTensorA₀ (r • x) = r • eTensorA₀ x at hx
            change eTensorA₀ (r • y) = r • eTensorA₀ y at hy
            simp only [smul_add, eTensorA₀.map_add, hx, hy] }
  have : Module.Flat R₁ A₁ :=
    have : Module.Flat R₁ (A₁ ⊗[A₀] A₀) := hi
    .of_linearEquiv eTensor.symm
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  have : IsNoetherianRing A₁ := Algebra.FiniteType.isNoetherianRing R₁ A₁
  have : Algebra.FinitePresentation R₁ A₁ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨R₁, A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ⟨e⟩⟩

/-- **Stacks Project, Tag 0E2F (1).**  A flat ring map of finite presentation `R → A` admits a
relative dualizing complex.

The proof is the source's reduction to the Noetherian case by spreading out, followed by
[stacks 0E2E] at the Noetherian stage, clause (2) of this tag for the base change back to `R`,
and transport along the resulting isomorphism of `R`-algebras.  Nothing is carried.

Clause (2) is read at the complex the Noetherian stage produces, namely `φ^!(R₁)`, through
`Dualizing.isRelativeDualizingComplex_baseChange_upperShriek_of_representation`, and the
representatives of [stacks 0E1U] it consumes come from
`Dualizing.exists_diagonalHomComplexRepresentation`.  Nothing about clause (2) is carried: the
residue-field vanishing the degreewise chase needs is the Noetherian case of the clause, which at
`φ^!(R₁)` is [stacks 0BZV] with [stacks 0E2E]. -/
theorem exists_isRelativeDualizingComplex (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A), IsRelativeDualizingComplex R A K := by
  classical
  obtain ⟨R₁, A₁, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := exists_noetherianFlatModel R A
  let : Algebra R (A₁ ⊗[R₁] R) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨p₁⟩ := nonempty_polynomialPresentation (algebraMap R₁ A₁)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hflat₁ : (algebraMap R₁ A₁).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hK₁ := p₁.relativeDualizingComplex_isRelativeDualizingComplex_of_flat hflat₁
  let : Algebra.FiniteType R₁ (A₁ ⊗[R₁] A₁) :=
    Algebra.FiniteType.trans (R := R₁) (S := A₁) (A := A₁ ⊗[R₁] A₁) inferInstance inferInstance
  let : IsNoetherianRing (A₁ ⊗[R₁] A₁) :=
    Algebra.FiniteType.isNoetherianRing R₁ (A₁ ⊗[R₁] A₁)
  obtain ⟨P, F, E, dP, dF, hPLE, hPproj, hPkflat, ⟨eP⟩, hFLE, hFflat, ⟨eF⟩, hE, hEflat, hEfin⟩ :=
    exists_diagonalHomComplexRepresentation R₁ A₁ _ hK₁
  have := hPLE
  have := hPproj
  have := hFLE
  have hK' := isRelativeDualizingComplex_baseChange_upperShriek_of_representation R₁ A₁ R p₁
    P dP hPkflat eP F dF hFflat eF E hE hEflat hEfin
  have : Module.Flat R (A₁ ⊗[R₁] R) := flat_baseChange R₁ A₁ R
  have : Algebra.FinitePresentation R (A₁ ⊗[R₁] R) :=
    Algebra.FinitePresentation.equiv (baseChangeComm R₁ A₁ R)
  exact ⟨_, isRelativeDualizingComplex_of_algEquiv e _ hK'⟩

end Dualizing

end
