module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveCotangentPresentation
public import StacksFrontier.Homology.DoubleMappingCone
public import StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
public import StacksFrontier.RingTheory.CompleteIntersection.NaiveCotangentPerfect
public import StacksFrontier.RingTheory.NaiveCotangent.ConormalFiniteProjective
public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso
public import StacksFrontier.RingTheory.Syntomic.ConormalRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The determinant of the naive cotangent complex of a syntomic algebra

Let `B` be a syntomic `A`-algebra. Its naive cotangent complex `NL_{B/A}`, as an object of the
derived category `D(B)`, is perfect of Tor-amplitude in `[-1, 0]`: every finite polynomial
presentation `P` of `B` over `A` has finite projective conormal module, and the two-term complex
`NL(P) = (I/I² → Ω_{A[x]/A} ⊗ B)` is a presentation of `NL_{B/A}` by finite projective modules.
So the determinant functor of More on Algebra, Section 0FJI (Stacks 0FJM) applies to it, and
`det(NL_{B/A})` is an invertible `B`-module; if `B` is moreover quasi-finite over `A`, then
`NL_{B/A}` has rank zero and carries the canonical element `δ(NL_{B/A})`.

## Main definitions

* `NaiveCotangent.presentationComplex P`: the two-term cochain complex `NL(P)` of a presentation,
  in degrees `-1` and `0`.
* `NaiveCotangent.presentationIso P`: the canonical isomorphism `NL_{B/A} ≅ NL(P)` in `D(B)`.
* `NaiveCotangent.presentationTwoTerm P`: `NL(P)` as a two-term presentation of `NL_{B/A}` by
  finite projective modules, when `P` is finite with finite projective conormal module.
* `NaiveCotangent.naiveCotangentPerfect A B`: `NL_{B/A}` as a perfect object of Tor-amplitude in
  `[-1, 0]` of `D(B)`, for `B` syntomic over `A`.
* `NaiveCotangent.detNL A B` and `NaiveCotangent.deltaNL A B`: the invertible module
  `det(NL_{B/A})` and, for `B` quasi-finite and syntomic over `A`, its canonical element
  `δ(NL_{B/A})`.
* `NaiveCotangent.detNLPresentationEquiv P`: the identification of `det(NL_{B/A})` with the
  determinant line of the two-term complex `NL(P)`.

## Main results

* `NaiveCotangent.presentationIso_hom_eq`: the comparison isomorphisms for two presentations
  differ by the map induced by any morphism of presentations.
* `NaiveCotangent.detNLPresentationEquiv_deltaNL`: under the identification with the determinant
  line of `NL(P)`, `δ(NL_{B/A})` is the canonical element of More on Algebra, Section 0FJI of the
  rank-zero complex `NL(P)`.

## Implementation notes

`NL_{B/A}` is `NaiveCotangent.naiveCotangentObject A B`, the object of Stacks 0FV0 and 0FJV. Its
comparison with `NL(P)` passes through the canonical presentation: the mapping cone of the
canonical differential is the two-term complex on it (`HomologicalComplex.singleConeDoubleIso`),
and any morphism of extensions between `P` and the canonical presentation induces a homotopy
equivalence of naive cotangent complexes (Stacks 00S1 (4)), whose class in `D(B)` does not
depend on the morphism (Stacks 00S1 (2)).

Presentations are indexed by types in the lowest universe (for instance `Fin n`), so that the
conormal and cotangent modules of `P` lie in the universe of `B`.

## References

* [Stacks Project, Section 0FJI](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Tag 0FJM](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Tag 0FV0](https://stacks.math.columbia.edu/tag/0FV0)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra

namespace NaiveCotangent

universe u

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ### The two-term complex of a presentation -/

/-- The naive cotangent complex `NL(P) = (I/I² → Ω_{A[x]/A} ⊗ B)` of a presentation, as a
cochain complex of `B`-modules in degrees `-1` and `0`. -/
abbrev presentationComplex {ι : Type} (P : Generators A B ι) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  Deformation.Artin.twoTermComplex (nlOfExtension P.toExtension)

/-- The morphism of complexes `NL(P) ⟶ NL(P')` induced by a morphism of extensions of `B` over
`A`. -/
abbrev extensionComplexMap {P P' : Extension.{u} A B} (φ : P.Hom P') :
    Deformation.Artin.twoTermComplex (nlOfExtension P) ⟶
      Deformation.Artin.twoTermComplex (nlOfExtension P') :=
  Deformation.Artin.twoTermHom (nlExtensionMap φ)

/-- A morphism of extensions admitting a morphism in the other direction induces an isomorphism
in the derived category (Stacks 00S1 (4)). -/
@[sga "6 0 4.3" "partial"]
theorem isIso_Q_map_extensionComplexMap {P P' : Extension.{u} A B} (φ : P.Hom P')
    (ψ : P'.Hom P) : IsIso (DerivedCategory.Q.map (extensionComplexMap φ)) :=
  Deformation.Artin.isIso_Q_map_twoTermHom (nlExtensionMap_isHomotopyEquiv φ ψ)

/-- Any two morphisms of extensions induce the same map in the derived category
(Stacks 00S1 (2)). -/
theorem Q_map_extensionComplexMap_eq {P P' : Extension.{u} A B} (φ ψ : P.Hom P') :
    DerivedCategory.Q.map (extensionComplexMap φ) =
      DerivedCategory.Q.map (extensionComplexMap ψ) :=
  Deformation.Artin.Q_map_twoTermHom_eq_of_homotopic (nlExtensionMap_homotopic φ ψ)

/-- The map induced by a morphism of extensions between two presentations is an isomorphism in
the derived category. -/
@[sga "6 0 4.3" "partial"]
instance isIso_Q_map_presentationComplexMap {ι ι' : Type} {P : Generators A B ι}
    {P' : Generators A B ι'} (φ : P.toExtension.Hom P'.toExtension) :
    IsIso (DerivedCategory.Q.map (extensionComplexMap φ)) :=
  isIso_Q_map_extensionComplexMap φ ((Extension.defaultHom A B P.toExtension).comp
    (P'.defaultHom (Generators.self A B)).toExtensionHom)

/-- The two-term complex on the canonical differential is the mapping cone presenting
`NL_{B/A}`. -/
def canonicalIso :
    naiveCotangentObject A B ≅
      DerivedCategory.Q.obj
        (Deformation.Artin.twoTermComplex (nlOfExtension (Generators.self A B).toExtension)) :=
  (DerivedCategory.Q.mapIso (HomologicalComplex.singleConeDoubleIso
    (ModuleCat.ofHom (nlOfExtension (Generators.self A B).toExtension).d))).symm

/-- **The comparison `NL_{B/A} ≅ NL(P)` in `D(B)`** for an extension `P` of `B` over `A` admitting
a morphism to the canonical presentation (for instance a presentation, or any extension whose
ring is a polynomial ring): the map induced by the canonical morphism from the canonical
presentation. The morphism `ψ` is only used to see that the map is invertible. -/
def extensionIso (P : Extension.{u} A B) (ψ : P.Hom (Generators.self A B).toExtension) :
    naiveCotangentObject A B ≅
      DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex (nlOfExtension P)) :=
  haveI := isIso_Q_map_extensionComplexMap (Extension.defaultHom A B P) ψ
  canonicalIso ≪≫ asIso (DerivedCategory.Q.map (extensionComplexMap
    (Extension.defaultHom A B P)))

/-- The comparison isomorphisms of two extensions differ by the map induced by any morphism of
extensions between them. -/
theorem extensionIso_hom_eq (P P' : Extension.{u} A B)
    (ψ : P.Hom (Generators.self A B).toExtension) (ψ' : P'.Hom (Generators.self A B).toExtension)
    (φ : P.Hom P') :
    (extensionIso P' ψ').hom =
      (extensionIso P ψ).hom ≫ DerivedCategory.Q.map (extensionComplexMap φ) := by
  simp only [extensionIso, Iso.trans_hom, asIso_hom, Category.assoc, ← Functor.map_comp,
    ← Deformation.Artin.twoTermHom_comp, ← nlExtensionMap_comp]
  rw [Q_map_extensionComplexMap_eq (φ.comp (Extension.defaultHom A B P))
    (Extension.defaultHom A B P')]

/-- **The comparison `NL_{B/A} ≅ NL(P)` in `D(B)`** for a presentation `P` of `B` over `A`. -/
abbrev presentationIso {ι : Type} (P : Generators A B ι) :
    naiveCotangentObject A B ≅ DerivedCategory.Q.obj (presentationComplex P) :=
  extensionIso P.toExtension (P.defaultHom (Generators.self A B)).toExtensionHom

/-- The comparison isomorphisms of two presentations differ by the map induced by any morphism
of extensions between them. -/
theorem presentationIso_hom_eq {ι ι' : Type} (P : Generators A B ι) (P' : Generators A B ι')
    (φ : P.toExtension.Hom P'.toExtension) :
    (presentationIso P').hom =
      (presentationIso P).hom ≫ DerivedCategory.Q.map (extensionComplexMap φ) :=
  extensionIso_hom_eq _ _ _ _ φ

/-! ### The two-term presentation of `NL_{B/A}` -/

section Presentation

variable {ι : Type} [Finite ι] (P : Generators A B ι)

/-- The terms of `NL(P)` in degrees `-1` and `0` are finite projective, and all other terms are
zero, when the conormal module is finite projective. -/
theorem presentationComplex_finite_projective [Module.Finite B P.toExtension.Cotangent]
    [Module.Projective B P.toExtension.Cotangent] (i : ℤ) :
    Module.Finite B ((presentationComplex P).X i) ∧
      Module.Projective B ((presentationComplex P).X i) := by
  have : Module.Free B P.toExtension.CotangentSpace := Module.Free.of_basis P.cotangentSpaceBasis
  have : Module.Finite B (nlOfExtension P.toExtension).X₁ :=
    ‹Module.Finite B P.toExtension.Cotangent›
  have : Module.Projective B (nlOfExtension P.toExtension).X₁ :=
    ‹Module.Projective B P.toExtension.Cotangent›
  have : Module.Free B (nlOfExtension P.toExtension).X₀ :=
    ‹Module.Free B P.toExtension.CotangentSpace›
  have : Module.Finite B (nlOfExtension P.toExtension).X₀ :=
    Module.Finite.of_basis P.cotangentSpaceBasis
  rcases eq_or_ne i (-1) with rfl | h₁
  · let e := (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom
      (nlOfExtension P.toExtension).d) ComplexShape.upIntRelNegOneZero).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩
  rcases eq_or_ne i 0 with rfl | h₀
  · let e := (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom
      (nlOfExtension P.toExtension).d) ComplexShape.upIntRelNegOneZero
      (by decide)).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩
  have : Subsingleton ((presentationComplex P).X i) :=
    ModuleCat.isZero_iff_subsingleton.mp (HomologicalComplex.isZero_double_X (ModuleCat.ofHom
      (nlOfExtension P.toExtension).d) ComplexShape.upIntRelNegOneZero i h₁ h₀)
  exact ⟨inferInstance, inferInstance⟩

omit [Finite ι] in
/-- The two-term complex of a presentation vanishes in degrees below `-1`. -/
theorem presentationComplex_isStrictlyGE : (presentationComplex P).IsStrictlyGE (-1) :=
  (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

omit [Finite ι] in
/-- The two-term complex of a presentation vanishes in degrees above `0`. -/
theorem presentationComplex_isStrictlyLE : (presentationComplex P).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

/-- **`NL(P)` as a two-term presentation of `NL_{B/A}` by finite projective modules**, for a
finite presentation `P` with finite projective conormal module. -/
def presentationTwoTerm [Module.Finite B P.toExtension.Cotangent]
    [Module.Projective B P.toExtension.Cotangent] :
    TwoTermDeterminant.TwoTermPresentation (naiveCotangentObject A B) where
  complex := presentationComplex P
  finite i := (presentationComplex_finite_projective P i).1
  projective i := (presentationComplex_finite_projective P i).2
  strictlyGE := presentationComplex_isStrictlyGE P
  strictlyLE := presentationComplex_isStrictlyLE P
  iso := presentationIso P

end Presentation

/-- Every finite polynomial presentation of a syntomic algebra has finite projective conormal
module, and such a presentation exists. -/
theorem exists_generators_finite_projective [Algebra.Syntomic A B] :
    ∃ (n : ℕ) (P : Generators A B (Fin n)),
      Module.Finite B P.toExtension.Cotangent ∧ Module.Projective B P.toExtension.Cotangent := by
  obtain ⟨n, f, hf, -⟩ := Algebra.FinitePresentation.out (R := A) (A := B)
  have heval : MvPolynomial.aeval (fun i : Fin n => f (MvPolynomial.X i)) = f := by
    ext i
    simp
  let P : Generators A B (Fin n) :=
    Generators.ofSurjective (fun i => f (MvPolynomial.X i)) (by rwa [heval])
  have hlci : RingHom.IsLocalCompleteIntersection (algebraMap A B) :=
    (hasTorAmplitude_tfae_syntomic A B (Algebra.Syntomic A B) (by simp)
      (RingHom.IsLocalCompleteIntersection (algebraMap A B)) (by simp)).mp ‹_›
  exact ⟨n, P, P.cotangent_finite_projective_of_isLocalCompleteIntersection hlci⟩

/-- `NL_{B/A}` is perfect of Tor-amplitude in `[-1, 0]` as soon as it has a two-term
presentation by finite projective modules. -/
theorem perfectTwoTermComplexProperty_of_presentation
    (T : TwoTermDeterminant.TwoTermPresentation (naiveCotangentObject A B)) :
    TwoTermDeterminant.perfectTwoTermComplexProperty B (naiveCotangentObject A B) := by
  refine ⟨⟨T.complex, -1, 0, T.strictlyGE, T.strictlyLE, T.finite, T.projective, ⟨T.iso⟩⟩,
    ⟨T.complex, fun i => ?_, T.strictlyGE, T.strictlyLE, ⟨T.iso⟩⟩⟩
  have := T.projective i
  infer_instance

/-- **`NL_{B/A}` as a perfect object of `D(B)` of Tor-amplitude in `[-1, 0]`**, for `B`
syntomic over `A`. -/
def naiveCotangentPerfect (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] : TwoTermDeterminant.PerfectTwoTermComplex B :=
  ⟨naiveCotangentObject A B, by
    obtain ⟨n, P, h₁, h₂⟩ := exists_generators_finite_projective (A := A) (B := B)
    exact perfectTwoTermComplexProperty_of_presentation (presentationTwoTerm P)⟩

/-- **The invertible `B`-module `det(NL_{B/A})`** of a syntomic `A`-algebra `B`: the determinant
of More on Algebra, Section 0FJI, of the naive cotangent complex. -/
abbrev detNL (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B] :
    ModuleCat.{u} B :=
  ((TwoTermDeterminant.det B).obj ⟨naiveCotangentPerfect A B⟩).of.obj

/-- `det(NL_{B/A})` is an invertible `B`-module. -/
instance (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B] :
    Module.Invertible B (detNL A B) :=
  ((TwoTermDeterminant.det B).obj ⟨naiveCotangentPerfect A B⟩).of.property

/-- **The canonical element `δ(NL_{B/A})`** of `det(NL_{B/A})`, for `B` quasi-finite and
syntomic over `A`, where `NL_{B/A}` has rank zero. -/
def deltaNL (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
    [Algebra.QuasiFinite A B] : detNL A B :=
  TwoTermDeterminant.delta (naiveCotangentPerfect A B)
    Algebra.isRankZero_naiveCotangentObject_of_quasiFinite_syntomic

/-- The identification of `det(NL_{B/A})` with the determinant line of the two-term complex
`NL(P)` of a finite presentation with finite projective conormal module. -/
def detNLPresentationEquiv [Algebra.Syntomic A B] {ι : Type} [Finite ι] (P : Generators A B ι)
    [Module.Finite B P.toExtension.Cotangent] [Module.Projective B P.toExtension.Cotangent] :
    detNL A B ≃ₗ[B] TwoTermDeterminant.presentationDeterminant (presentationTwoTerm P) :=
  TwoTermDeterminant.detPresentationIso (naiveCotangentPerfect A B) (presentationTwoTerm P)

/-- Under the identification with the determinant line of a rank-zero two-term complex `NL(P)`,
`δ(NL_{B/A})` is the canonical element of that complex. -/
theorem detNLPresentationEquiv_deltaNL [Algebra.Syntomic A B] [Algebra.QuasiFinite A B]
    {ι : Type} [Finite ι] (P : Generators A B ι)
    [Module.Finite B P.toExtension.Cotangent] [Module.Projective B P.toExtension.Cotangent]
    (hP : (presentationTwoTerm P).IsRankZero) :
    detNLPresentationEquiv P (deltaNL A B) =
      TwoTermDeterminant.presentationDelta (presentationTwoTerm P) hP :=
  TwoTermDeterminant.detPresentationIso_delta _ _ hP

end NaiveCotangent

end
