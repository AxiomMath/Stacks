module

public import StacksFrontier.Homology.TwoTermComplex.ExtAnnihilationFactorization
public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.PresentationIndependence
public import StacksFrontier.RingTheory.Rig.Obstruction

/-!
# Annihilation of `Ext¹` out of the completed naive cotangent complex

Let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` an `I`-adically complete
`A`-algebra of finite type modulo `I`.  A completed polynomial presentation
`B = A[x₁, …, xᵣ]^ / J` gives the two-term complex `NL^∧_{B/A} = (J/J² → ⨁ i, B dxᵢ)` of
`Rig.CompletedNaiveCotangentComplex.cochainComplex`; this file reads that complex in `D(B)`
and characterises, for a single scalar `f ∈ B`, the condition

`f · Ext¹_B(NL^∧_{B/A}, N) = 0 for every B-module N`

which is the hypothesis of rig-smoothness (Stacks 0GAI) and of Stacks 0GAL.  The
characterisation is that multiplication by `f` on `J/J²` factors through the differential:
there is `h : ⨁ i, B dxᵢ → J/J²` with `h ∘ d = f`.  It is Stacks 0G9F for the principal
ideal `(f)`, specialised to the presentation's own complex, which is legitimate because the
degree `0` term `⨁ i, B dxᵢ` is free.

Two consequences are recorded.  First, the condition does not depend on the presentation:
the complexes of two presentations are homotopy equivalent (Stacks 0GAE), hence isomorphic
in `D(B)`.  Second — and this is the reduction of Stacks 0GAL to Stacks 0GAG — for a
completed base change `(A₁, I₁) → (A₂, I₂)` the annihilation transfers from `B₁` to
`B₂ = (B₁ ⊗_{A₁} A₂)^∧` as soon as the factorization over `B₁` can be carried to one over
`B₂`, which is exactly what the comparison map

`NL^∧_{B₁/A₁} ⊗_{B₁} B₂ → NL^∧_{B₂/A₂}`

of Stacks 0GAG provides: it is surjective on `H⁻¹`, so the base change of a factorization
pushes forward.  The derived-category form of the same step, for a comparison morphism which
is an isomorphism on `H⁰` and an epimorphism on `H⁻¹`, is
`Rig.smul_ext_one_derived_of_comparison`.

## Main definitions

* `Rig.derivedCompletedNaiveCotangentComplex`: the completed naive cotangent complex of a
  presentation, read in `D(B)`.

## Main results

* `Rig.smul_ext_one_derived_iff_exists_factorization`: the factorization criterion.
* `Rig.smul_ext_one_derived_congr_presentation`: independence of the presentation.
* `Rig.smul_ext_one_derived_of_comparison`: the criterion through a comparison morphism which
  is an `H⁰`-isomorphism and an `H⁻¹`-epimorphism.
* `Rig.smul_ext_one_of_baseChange_of_factorization`: the reduction of Stacks 0GAL to the
  comparison map of Stacks 0GAG.

## Implementation notes

The complex of a presentation is a `HomologicalComplex.double`, so it is strictly supported
in degrees `-1` and `0` and its degree `0` term is the universe lift of `Fin r → B`, which is
free.  These three facts are
`Rig.CompletedNaiveCotangentComplex.{isStrictlyGE, isStrictlyLE, free_X_zero}` from
`StacksFrontier.RingTheory.Rig.Obstruction`, now imported above; they are kept there as plain
lemmas rather than instances, because as instances they are keyed on `HomologicalComplex.X`
and on the strict-support classes, so they would be attempted against every two-term complex
in the library and would unfold the large definition `Rig.completedNaiveCotangentComplex`
while doing it.  Each is introduced into the local context with `have` at the point of use,
so the effect on instance synthesis is confined to that proof.

Stacks 0GAL itself is **not** proved in this file: its geometric input, the comparison map of
Stacks 0GAG, is not available.  The reduction lemma takes that input as a hypothesis, in the
module form the comparison map produces, and nothing else is missing; the derived form of the
same input is consumed by `Rig.smul_ext_one_derived_of_comparison`.

## References

* [Stacks Project, Tag 0GAL](https://stacks.math.columbia.edu/tag/0GAL)
* [Stacks Project, Tag 0GAE](https://stacks.math.columbia.edu/tag/0GAE)
* [The Stacks Project, Lemma 15.85.6 (0G9F)](https://stacks.math.columbia.edu/tag/0G9F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Rig

universe u v u₁ u₂

open AdicFiniteTypeAlgebra CompletedNaiveCotangentComplex

attribute [local instance] HasDerivedCategory.standard

section Defs

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- The completed naive cotangent complex `NL^∧_{B/A}` of a completed polynomial presentation
of `B`, read in the derived category `D(B)`. -/
public def derivedCompletedNaiveCotangentComplex (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    DerivedCategory (ModuleCat.{max u v} B.carrier) :=
  DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex

variable (B : AdicFiniteTypeAlgebra.{u, v} A I)

/-- The completed naive cotangent complex has no cohomology outside degrees `-1` and `0`. -/
public theorem isZero_homology_derivedCompletedNaiveCotangentComplex
    (P : CompletedPolynomialPresentation I B) (i : ℤ) (h₁ : i ≠ -1) (h₀ : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) i).obj
      (derivedCompletedNaiveCotangentComplex B P)) :=
  have := (completedNaiveCotangentComplex B P).isStrictlyGE
  have := (completedNaiveCotangentComplex B P).isStrictlyLE
  TwoTermComplex.isZero_homology_Q_obj_of_twoTerm _ i h₁ h₀

/-- The completed naive cotangent complexes of two completed polynomial presentations of `B`
become isomorphic in `D(B)`: they are homotopy equivalent by **Stacks 0GAE**, and a homotopy
equivalence is a quasi-isomorphism. -/
public theorem nonempty_derivedCompletedNaiveCotangentComplex_iso
    (P Q : CompletedPolynomialPresentation I B) :
    Nonempty (derivedCompletedNaiveCotangentComplex B P ≅
      derivedCompletedNaiveCotangentComplex B Q) := by
  obtain ⟨e⟩ := completedNaiveCotangentComplex_homotopyEquiv I B P Q
  have hiso : IsIso (DerivedCategory.Q.map e.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ e.hom).mpr inferInstance
  exact ⟨@asIso _ _ _ _ (DerivedCategory.Q.map e.hom) hiso⟩

/-- Annihilation of `Ext¹` out of an object of `D(B)` isomorphic to `NL^∧_{B/A}` by `f` is
equivalent to the factorization of `f` through the differential. -/
private theorem smul_ext_one_iff_exists_factorization_of_iso
    (P : CompletedPolynomialPresentation I B) (f : B.carrier)
    {K : DerivedCategory (ModuleCat.{max u v} B.carrier)}
    (e : derivedCompletedNaiveCotangentComplex B P ≅ K) :
    (∀ (N : ModuleCat.{max u v} B.carrier)
        (ξ : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
        f • ξ = 0)
      ↔ ∃ h : (completedNaiveCotangentComplex B P).cochainComplex.X 0 ⟶
          (completedNaiveCotangentComplex B P).cochainComplex.X (-1),
        (completedNaiveCotangentComplex B P).cochainComplex.d (-1) 0 ≫ h =
          f • 𝟙 ((completedNaiveCotangentComplex B P).cochainComplex.X (-1)) :=
  have := (completedNaiveCotangentComplex B P).isStrictlyGE
  have := (completedNaiveCotangentComplex B P).isStrictlyLE
  have := (completedNaiveCotangentComplex B P).free_X_zero
  TwoTermComplex.smul_ext_one_eq_zero_iff_exists_factorization f _ e

/-- A scalar `f ∈ B` annihilates `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N` exactly when
multiplication by `f` on the conormal module `J/J²` factors through the differential
`d : J/J² → ⨁ i, B dxᵢ`, that is, when there is `h` with `d ≫ h = f`.

This is **Stacks 0G9F** for the principal ideal `(f)`, applied to the presentation's own
complex; it applies because the degree `0` term is free. -/
public theorem smul_ext_one_derived_iff_exists_factorization
    (P : CompletedPolynomialPresentation I B) (f : B.carrier) :
    (∀ (N : ModuleCat.{max u v} B.carrier)
        (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B P)
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
        f • ξ = 0)
      ↔ ∃ h : (completedNaiveCotangentComplex B P).cochainComplex.X 0 ⟶
          (completedNaiveCotangentComplex B P).cochainComplex.X (-1),
        (completedNaiveCotangentComplex B P).cochainComplex.d (-1) 0 ≫ h =
          f • 𝟙 ((completedNaiveCotangentComplex B P).cochainComplex.X (-1)) :=
  smul_ext_one_iff_exists_factorization_of_iso B P f (Iso.refl _)

/-- Annihilation of `Ext¹` out of the completed naive cotangent complex by a scalar does not
depend on the chosen completed polynomial presentation of `B`. -/
public theorem smul_ext_one_derived_congr_presentation
    (P Q : CompletedPolynomialPresentation I B) (f : B.carrier)
    (h : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B P)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      f • ξ = 0) :
    ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B Q)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      f • ξ = 0 := by
  obtain ⟨e⟩ := nonempty_derivedCompletedNaiveCotangentComplex_iso B Q P
  exact (smul_ext_one_derived_iff_exists_factorization B Q f).mpr
    ((smul_ext_one_iff_exists_factorization_of_iso B Q f e).mp h)

/-- If multiplication by `f ∈ B` on the degree `-1` term of a two-term complex `L` of
`B`-modules with free degree `0` term factors through the differential of `L`, and `L` maps to
`NL^∧_{B/A}` in `D(B)` by a morphism which is an isomorphism on `H⁰` and an epimorphism on
`H⁻¹`, then `f` annihilates `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`.

This is **Stacks 0G9J** (after **Stacks 0G9F**) for the principal ideal `(f)`, read at the
completed naive cotangent complex. -/
public theorem smul_ext_one_derived_of_comparison
    (P : CompletedPolynomialPresentation I B) (f : B.carrier)
    (L : CochainComplex (ModuleCat.{max u v} B.carrier) ℤ)
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0] [Module.Free B.carrier (L.X 0)]
    (α : DerivedCategory.Q.obj L ⟶ derivedCompletedNaiveCotangentComplex B P)
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) 0).map α)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) (-1)).map α)]
    (h : L.X 0 ⟶ L.X (-1)) (hh : L.d (-1) 0 ≫ h = f • 𝟙 (L.X (-1))) :
    ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B P)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      f • ξ = 0 :=
  TwoTermComplex.smul_ext_one_eq_zero_of_comparison f L
    (isZero_homology_derivedCompletedNaiveCotangentComplex B P) α h hh

end Defs

section BaseChange

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
variable {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
variable {I₁ : Ideal A₁} {I₂ : Ideal A₂}

/-- The image in the completed base change `B₂ = (B₁ ⊗_{A₁} A₂)^∧` of a scalar `f₁ ∈ B₁`,
taken through the canonical identification of `B₂` with that completion. -/
public abbrev CompletedBaseChange.scalar
    (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (f₁ : B₁.carrier) :
    (C.functor.obj B₁).carrier :=
  (C.completedTensorProductEquiv B₁).symm
    (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁)
      (baseChangedAlgebra (A₂ := A₂) B₁)
      ((Algebra.TensorProduct.includeLeft : B₁.carrier →ₐ[A₁]
        baseChangedAlgebra (A₂ := A₂) B₁) f₁))

variable (C : CompletedBaseChange (A₁ := A₁) (A₂ := A₂) (I₁ := I₁) (I₂ := I₂))
  (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁)
  (P₁ : CompletedPolynomialPresentation I₁ B₁)
  (P₂ : CompletedPolynomialPresentation I₂ (C.functor.obj B₁))
  (f₁ : B₁.carrier)

/-- **Reduction of Stacks 0GAL to Stacks 0GAG, in module form.**  Let `(A₁, I₁) → (A₂, I₂)`
be a completed base change of Noetherian adic pairs, `B₁` adically of finite type over
`(A₁, I₁)`, and `B₂ = (B₁ ⊗_{A₁} A₂)^∧` its base change.  Let `f₁ ∈ B₁` with image
`f₂ ∈ B₂`.  If every factorization of multiplication by `f₁` through the differential of
`NL^∧_{B₁/A₁}` yields a factorization of multiplication by `f₂` through the differential of
`NL^∧_{B₂/A₂}` — which is what the comparison map `NL^∧_{B₁/A₁} ⊗_{B₁} B₂ → NL^∧_{B₂/A₂}` of
Stacks 0GAG supplies, being surjective on `H⁻¹` — then annihilation of all first Ext groups
of `NL^∧_{B₁/A₁}` by `f₁` gives annihilation of all first Ext groups of `NL^∧_{B₂/A₂}` by
`f₂`. -/
public theorem smul_ext_one_of_baseChange_of_factorization
    (hcomparison : ∀ h₁ : (completedNaiveCotangentComplex B₁ P₁).cochainComplex.X 0 ⟶
        (completedNaiveCotangentComplex B₁ P₁).cochainComplex.X (-1),
        (completedNaiveCotangentComplex B₁ P₁).cochainComplex.d (-1) 0 ≫ h₁ =
            f₁ • 𝟙 ((completedNaiveCotangentComplex B₁ P₁).cochainComplex.X (-1)) →
          ∃ h₂ : (completedNaiveCotangentComplex (C.functor.obj B₁) P₂).cochainComplex.X 0 ⟶
            (completedNaiveCotangentComplex (C.functor.obj B₁) P₂).cochainComplex.X (-1),
            (completedNaiveCotangentComplex (C.functor.obj B₁) P₂).cochainComplex.d (-1) 0 ≫
                h₂ =
              C.scalar B₁ f₁ • 𝟙 ((completedNaiveCotangentComplex (C.functor.obj B₁)
                P₂).cochainComplex.X (-1)))
    (h : ∀ (N : ModuleCat.{max u₁ v} B₁.carrier)
      (ξ : DerivedCategory.Ext (derivedCompletedNaiveCotangentComplex B₁ P₁)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ v} B₁.carrier) 0).obj N) 1),
        f₁ • ξ = 0) :
    ∀ (N : ModuleCat.{max u₂ v} (C.functor.obj B₁).carrier)
      (ξ : DerivedCategory.Ext
        (derivedCompletedNaiveCotangentComplex (C.functor.obj B₁) P₂)
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max u₂ v} (C.functor.obj B₁).carrier) 0).obj N) 1),
      (C.completedTensorProductEquiv B₁).symm
        (AdicCompletion.of (baseChangedIdeal (A₂ := A₂) (I₂ := I₂) B₁)
          (baseChangedAlgebra (A₂ := A₂) B₁)
          ((Algebra.TensorProduct.includeLeft : B₁.carrier →ₐ[A₁]
            baseChangedAlgebra (A₂ := A₂) B₁) f₁)) • ξ = 0 := by
  obtain ⟨h₁, hh₁⟩ := (smul_ext_one_derived_iff_exists_factorization B₁ P₁ f₁).mp h
  exact (smul_ext_one_derived_iff_exists_factorization (C.functor.obj B₁) P₂
    (C.scalar B₁ f₁)).mpr (hcomparison h₁ hh₁)

end BaseChange

end Rig

end
