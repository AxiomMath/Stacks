module

public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExactBaseChangeFlat
public import StacksFrontier.Homology.TwoTermComplex.PresentationBaseChange
import all StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor

/-!
# Base change of the transport between the determinant lines of two-term presentations

Let `φ : R → A` be a flat homomorphism of commutative rings, let `K` and `L` be objects of `D(R)`
carrying two-term presentations `P` and `Q` by finite projective modules, and let
`a : Q(P.complex) ≅ Q(Q.complex)` be an isomorphism in the derived category. The transport
`TwoTermDeterminant.determinantTransport P Q a` between the two determinant lines is intertwined
by the comparison `TwoTermComplex.determinantLineBaseChange` with the transport between the
determinant lines of the base-changed presentations, along the base change of `a`.

This is the compatibility that makes the determinant of a two-term perfect complex on a scheme
independent of the affine chart: on a smaller chart the presenting complex is the termwise base
change of the presenting complex on the larger one, and the identification of the two determinant
lines there is the base change of the identification upstairs.

## Main definitions

* `TwoTermDeterminant.extendScalarsComplex`: termwise extension of scalars along `φ` on cochain
  complexes of modules.
* `TwoTermDeterminant.presentationComparisonIso`: the comparison identifying the derived
  extension of scalars of a presented object with the object presented by the base change of the
  presentation.
* `TwoTermDeterminant.presentationBaseChangeMap`: the termwise extension of scalars of a chain
  map of presenting complexes.
* `TwoTermDeterminant.presentationBaseChangeIso`: **the base change of an isomorphism between two
  objects given by two-term presentations.**
* `TwoTermDeterminant.presentationDeterminantBaseChange`: **the comparison
  `A ⊗_R det(P) ≅ det(P ⊗_R A)` between the determinant line of a two-term presentation and that
  of its base change.**

## Main results

* `TwoTermDeterminant.determinantTransport_baseChange`: **transport between the determinant lines
  of two two-term presentations commutes with flat base change.**
* `TwoTermDeterminant.presentationTransport_baseChange`: the same statement for the transport
  attached to an isomorphism of the presented objects.

## Implementation notes

The base change is taken along a ring homomorphism `φ : R →+* A` whose algebra structure is
`φ.toAlgebra`, rather than along an ambient `Algebra R A`. This is forced: the presenting complex
of `TwoTermDeterminant.TwoTermPresentation.baseChange` is built from `ModuleCat.extendScalars`,
whose `R`-module structure on `A` is `Module.compHom A φ`, and that agrees definitionally with
`Algebra.toModule` only for the algebra structure `φ.toAlgebra`. With that spelling the
differential of the base-changed presentation is `LinearMap.baseChange A` of the differential by
`rfl`, so `TwoTermComplex.determinantLineBaseChange` applies to
`TwoTermDeterminant.presentationDeterminant` with nothing to transport. Flatness is accordingly
a hypothesis `letI := φ.toAlgebra; Module.Flat R A`, the spelling of
`AlgebraicGeometry.IsAffineOpen.moduleFlat_presheaf_map`.

That reconciliation is expensive for the elaborator — reconciling the two spellings of a single
`ProjectiveDeterminant.module` costs some forty thousand heartbeats — so it is performed once, in
`TwoTermDeterminant.presentationDeterminantBaseChange`, and everything downstream is phrased in
terms of `TwoTermDeterminant.presentationDeterminant`. The declarations that still have to
perform it raise `maxHeartbeats`; without that the default budget is exhausted comparing the two
determinant lines. For the same reason the termwise extension of scalars of a chain map is named,
in `TwoTermDeterminant.presentationBaseChangeMap`, with its target type written in terms of the
base-changed presentations: `rw` works at a reduced transparency at which the two spellings of
the presenting complex are not interchangeable.

Transport is defined through a surjective span, so the proof base-changes the span and appeals
twice to the keystone `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_baseChange_comp`.
Degreewise surjectivity of a leg survives base change because the tensor product is right exact,
and invertibility in the derived category survives it because the comparison from derived to
termwise extension of scalars is invertible on the presenting complexes, which are bounded
complexes of projectives and hence K-flat by Tag 064K; naturality of that comparison turns the
one into the other. No flatness is needed for the span itself, only for the comparison of
determinant lines.

## References

* [Stacks Project, Lemma 15.63.2 (Tag 064K)](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Tag 0FJM](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SurjectiveSpan.left_isIso SurjectiveSpan.right_isIso

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] (φ : R →+* A)
variable {K L : DerivedCategory (ModuleCat.{u} R)}


/-! ### The comparison with derived extension of scalars -/

/-- Termwise extension of scalars along `φ` on cochain complexes of modules. -/
abbrev extendScalarsComplex :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The comparison from derived to termwise extension of scalars is invertible at the complex
presenting a two-term presentation: that complex is a bounded complex of projectives, hence
K-flat by Tag 064K, and a K-flat complex computes derived extension of scalars. -/
theorem isIso_comparison_presentation (P : TwoTermPresentation K) :
    IsIso ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex) :=
  have := P.strictlyLE
  have : ∀ i, Module.Flat R (P.complex.X i) := fun i =>
    have := P.projective i; Module.Flat.of_projective
  (totalDerivedExtensionScalars.{u, u, u} φ).comparison_isIso_of_kFlat P.complex
    (CochainComplex.KFlat.kFlat_of_flat.{u, u} P.complex 0)

/-- The comparison isomorphism identifying the derived extension of scalars of the object
presented by `P` with the object presented by
`TwoTermDeterminant.TwoTermPresentation.baseChange`. -/
def presentationComparisonIso (P : TwoTermPresentation K) :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj (DerivedCategory.Q.obj P.complex) ≅
      DerivedCategory.Q.obj (P.baseChange φ).complex :=
  @asIso _ _ _ _ _ (isIso_comparison_presentation φ P)

/-- The isomorphism exhibiting the base change of a presentation as a presentation is the derived
extension of scalars of the given one, followed by the comparison. -/
theorem TwoTermPresentation.baseChange_iso (P : TwoTermPresentation K) :
    (P.baseChange φ).iso =
      (totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso P.iso ≪≫
        presentationComparisonIso φ P :=
  rfl

/-- The termwise extension of scalars of a chain map of presenting complexes, read as a chain map
between the presenting complexes of the base-changed presentations. -/
def presentationBaseChangeMap (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (g : P.complex ⟶ Q.complex) : (P.baseChange φ).complex ⟶ (Q.baseChange φ).complex :=
  (extendScalarsComplex φ).map g

/-- Naturality of the comparison from derived to termwise extension of scalars, at a chain map of
presenting complexes. -/
theorem comparison_naturality_presentation (P : TwoTermPresentation K)
    (Q : TwoTermPresentation L) (g : P.complex ⟶ Q.complex) :
    (presentationComparisonIso φ P).hom ≫
        DerivedCategory.Q.map (presentationBaseChangeMap φ P Q g) =
      (totalDerivedExtensionScalars.{u, u, u} φ).functor.map (DerivedCategory.Q.map g) ≫
        (presentationComparisonIso φ Q).hom :=
  ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.naturality g).symm

/-- The localization of the termwise extension of scalars of a chain map of presenting complexes
is the derived extension of scalars of its localization, conjugated by the comparison
isomorphisms. -/
theorem Q_map_presentationBaseChangeMap (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (g : P.complex ⟶ Q.complex) :
    DerivedCategory.Q.map (presentationBaseChangeMap φ P Q g) =
      (presentationComparisonIso φ P).inv ≫
        (totalDerivedExtensionScalars.{u, u, u} φ).functor.map (DerivedCategory.Q.map g) ≫
          (presentationComparisonIso φ Q).hom :=
  (Iso.eq_inv_comp (presentationComparisonIso φ P)).mpr
    (comparison_naturality_presentation φ P Q g)

/-- **The termwise extension of scalars of a chain map of presenting complexes that is invertible
in the derived category is again invertible in the derived category.** -/
theorem isIso_Q_map_presentationBaseChangeMap (P : TwoTermPresentation K)
    (Q : TwoTermPresentation L) (g : P.complex ⟶ Q.complex)
    [IsIso (DerivedCategory.Q.map g)] :
    IsIso (DerivedCategory.Q.map (presentationBaseChangeMap φ P Q g)) := by
  have : IsIso ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map
    (DerivedCategory.Q.map g)) := inferInstance
  rw [Q_map_presentationBaseChangeMap φ P Q g]
  infer_instance

/-- **The termwise extension of scalars of a degreewise-surjective chain map of two-term
presentations is degreewise surjective**, the tensor product being right exact. -/
theorem isDegreewiseSurjective_presentationBaseChangeMap (P : TwoTermPresentation K)
    (Q : TwoTermPresentation L) (g : P.complex ⟶ Q.complex)
    (hs : (P.hom Q g).IsDegreewiseSurjective) :
    ((P.baseChange φ).hom (Q.baseChange φ)
      (presentationBaseChangeMap φ P Q g)).IsDegreewiseSurjective :=
  let : Algebra R A := φ.toAlgebra
  ⟨LinearMap.baseChange_surjective A hs.1, LinearMap.baseChange_surjective A hs.2⟩

/-- **The base change of an isomorphism between two objects given by two-term presentations**:
the derived extension of scalars of the isomorphism, conjugated by the comparison isomorphisms of
`TwoTermDeterminant.presentationComparisonIso`. -/
def presentationBaseChangeIso (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    DerivedCategory.Q.obj (P.baseChange φ).complex ≅
      DerivedCategory.Q.obj (Q.baseChange φ).complex :=
  (presentationComparisonIso φ P).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso a ≪≫
      presentationComparisonIso φ Q

/-- The morphism underlying `TwoTermDeterminant.presentationBaseChangeIso`. -/
theorem presentationBaseChangeIso_hom (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    (presentationBaseChangeIso φ P Q a).hom =
      (presentationComparisonIso φ P).inv ≫
        (totalDerivedExtensionScalars.{u, u, u} φ).functor.map a.hom ≫
          (presentationComparisonIso φ Q).hom :=
  rfl

/-! ### The determinant line of a base-changed presentation -/

/-- **The comparison between the determinant line of a two-term presentation and that of its
base change**, `A ⊗_R det(P) ≅ det(P ⊗_R A)`. This is
`TwoTermComplex.determinantLineBaseChange` at the differential of the presenting complex: the
differential of the base-changed presentation is the base change of that differential. -/
def presentationDeterminantBaseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A) (P : TwoTermPresentation K) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    A ⊗[R] presentationDeterminant P ≃ₗ[A] presentationDeterminant (P.baseChange φ) :=
  letI : Algebra R A := φ.toAlgebra
  haveI : Module.Flat R A := hφ
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  TwoTermComplex.determinantLineBaseChange A (P.complex.d (-1) 0).hom

/-! ### Base change of a surjective span -/

/-- **The base change of a surjective span.** The apex is the base change of the apex and the two
legs are the termwise extensions of scalars of the two legs: both stay degreewise surjective
because the tensor product is right exact, both stay invertible in the derived category by
`TwoTermDeterminant.isIso_Q_map_presentationBaseChangeMap`, and the square commutes by naturality
of the comparison. -/
private def SurjectiveSpan.baseChange {P : TwoTermPresentation K} {Q : TwoTermPresentation L}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (s : SurjectiveSpan P Q a) :
    SurjectiveSpan (P.baseChange φ) (Q.baseChange φ) (presentationBaseChangeIso φ P Q a) where
  middle := s.middle.baseChange φ
  left := presentationBaseChangeMap φ s.middle P s.left
  right := presentationBaseChangeMap φ s.middle Q s.right
  left_surjective :=
    isDegreewiseSurjective_presentationBaseChangeMap φ s.middle P s.left s.left_surjective
  right_surjective :=
    isDegreewiseSurjective_presentationBaseChangeMap φ s.middle Q s.right s.right_surjective
  left_isIso := isIso_Q_map_presentationBaseChangeMap φ s.middle P s.left
  right_isIso := isIso_Q_map_presentationBaseChangeMap φ s.middle Q s.right
  comm := by
    rw [Q_map_presentationBaseChangeMap φ s.middle P s.left,
      Q_map_presentationBaseChangeMap φ s.middle Q s.right, presentationBaseChangeIso_hom,
      ← s.comm]
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- The equivalence computed by a surjective span undoes the determinant equivalence of its left
leg and applies that of its right leg. -/
private theorem spanEquiv_apply_left {P : TwoTermPresentation K} {Q : TwoTermPresentation L}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (s : SurjectiveSpan P Q a) (z : presentationDeterminant s.middle) :
    spanEquiv s ((isoSurjectiveDeterminant s.middle P s.left s.left_surjective) z) =
      (isoSurjectiveDeterminant s.middle Q s.right s.right_surjective) z := by
  show (isoSurjectiveDeterminant s.middle Q s.right s.right_surjective)
      ((isoSurjectiveDeterminant s.middle P s.left s.left_surjective).symm
        ((isoSurjectiveDeterminant s.middle P s.left s.left_surjective) z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The equivalence computed by a surjective span, precomposed with the determinant equivalence
of its left leg, is the determinant equivalence of its right leg. -/
private theorem spanEquiv_comp_left {P : TwoTermPresentation K} {Q : TwoTermPresentation L}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (s : SurjectiveSpan P Q a) :
    (spanEquiv s).toLinearMap ∘ₗ
        (isoSurjectiveDeterminant s.middle P s.left s.left_surjective).toLinearMap =
      (isoSurjectiveDeterminant s.middle Q s.right s.right_surjective).toLinearMap :=
  LinearMap.ext fun z => spanEquiv_apply_left s z

/-! ### Base change of the transport between determinant lines -/

/-- **The canonical determinant equivalence of a degreewise-surjective quasi-isomorphism of
two-term presentations commutes with flat base change.** This is
`TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_baseChange_comp` read on the presenting
complexes, the differential of the base-changed presentation being the base change of the
differential. -/
private theorem isoSurjectiveDeterminant_baseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (g : P.complex ⟶ Q.complex)
    (hs : (P.hom Q g).IsDegreewiseSurjective) [IsIso (DerivedCategory.Q.map g)] :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    haveI := isIso_Q_map_presentationBaseChangeMap φ P Q g
    (isoSurjectiveDeterminant (P.baseChange φ) (Q.baseChange φ)
            (presentationBaseChangeMap φ P Q g)
            (isDegreewiseSurjective_presentationBaseChangeMap φ P Q g hs)).toLinearMap ∘ₗ
        (presentationDeterminantBaseChange φ hφ P).toLinearMap =
      (presentationDeterminantBaseChange φ hφ Q).toLinearMap ∘ₗ
        LinearMap.baseChange A (isoSurjectiveDeterminant P Q g hs).toLinearMap := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := Q.finite (-1)
  let := Q.projective (-1)
  let := Q.finite 0
  let := Q.projective 0
  exact TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_baseChange_comp R A (P.hom Q g) hs
    (twoTerm_quasiIso_of_isIso_Q_map P Q g)

/-- **Transport between the determinant lines of two two-term presentations commutes with flat
base change.** The comparison `TwoTermDeterminant.presentationDeterminantBaseChange` intertwines
`TwoTermDeterminant.determinantTransport` over `R` with the transport between the determinant
lines of the base-changed presentations over `A`, along the base change
`TwoTermDeterminant.presentationBaseChangeIso` of the isomorphism.

Transport is computed by any surjective span, and the base change of a span is a span for the
base-changed isomorphism, so this reduces to
`isoSurjectiveDeterminant_baseChange` applied to the two legs. -/
theorem determinantTransport_baseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    (determinantTransport (P.baseChange φ) (Q.baseChange φ)
            (presentationBaseChangeIso φ P Q a)).toLinearMap ∘ₗ
        (presentationDeterminantBaseChange φ hφ P).toLinearMap =
      (presentationDeterminantBaseChange φ hφ Q).toLinearMap ∘ₗ
        LinearMap.baseChange A (determinantTransport P Q a).toLinearMap := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  obtain ⟨s⟩ := nonempty_surjectiveSpan P Q a
  rw [determinantTransport_eq_span (s.baseChange φ), determinantTransport_eq_span s]
  have hl := fun y => LinearMap.congr_fun
    (isoSurjectiveDeterminant_baseChange φ hφ s.middle P s.left s.left_surjective) y
  have hr := fun y => LinearMap.congr_fun
    (isoSurjectiveDeterminant_baseChange φ hφ s.middle Q s.right s.right_surjective) y
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hsurj : Function.Surjective (LinearMap.baseChange A
      (isoSurjectiveDeterminant s.middle P s.left s.left_surjective).toLinearMap) :=
    LinearMap.baseChange_surjective A
      (isoSurjectiveDeterminant s.middle P s.left s.left_surjective).surjective
  obtain ⟨y, rfl⟩ := hsurj x
  have hD : LinearMap.baseChange A (spanEquiv s).toLinearMap
        (LinearMap.baseChange A
          (isoSurjectiveDeterminant s.middle P s.left s.left_surjective).toLinearMap y) =
      LinearMap.baseChange A
        (isoSurjectiveDeterminant s.middle Q s.right s.right_surjective).toLinearMap y := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, spanEquiv_comp_left]
  exact ((((congrArg (spanEquiv (s.baseChange φ)) (hl y)).symm.trans
        (spanEquiv_apply_left (s.baseChange φ) _)).trans (hr y)).trans
      (congrArg (fun z => presentationDeterminantBaseChange φ hφ Q z) hD).symm)

/-- **The transport between the determinant lines of two-term presentations of isomorphic objects
commutes with flat base change.** The form of
`TwoTermDeterminant.determinantTransport_baseChange` for the public
`TwoTermDeterminant.presentationTransport`, the isomorphism of the base-changed objects being the
derived extension of scalars of the given one. -/
theorem presentationTransport_baseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (b : K ≅ L) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    (presentationTransport (P.baseChange φ) (Q.baseChange φ)
            ((totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso b)).toLinearMap ∘ₗ
        (presentationDeterminantBaseChange φ hφ P).toLinearMap =
      (presentationDeterminantBaseChange φ hφ Q).toLinearMap ∘ₗ
        LinearMap.baseChange A (presentationTransport P Q b).toLinearMap := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  have h : (P.baseChange φ).iso.symm ≪≫
        (totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso b ≪≫ (Q.baseChange φ).iso =
      presentationBaseChangeIso φ P Q (P.iso.symm ≪≫ b ≪≫ Q.iso) := by
    refine Iso.ext ?_
    rw [TwoTermPresentation.baseChange_iso φ P, TwoTermPresentation.baseChange_iso φ Q,
      presentationBaseChangeIso_hom]
    simp only [Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have key := determinantTransport_baseChange φ hφ P Q (P.iso.symm ≪≫ b ≪≫ Q.iso)
  rw [← h] at key
  exact key

end TwoTermDeterminant

end
