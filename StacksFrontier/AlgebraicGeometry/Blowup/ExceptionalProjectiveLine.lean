module

public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSpaceEmbedding
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAssociatedGraded
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.BaseChange
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Algebra
public import StacksFrontier.RingTheory.RegularLocalRing.AssociatedGradedPolynomial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional divisor of the blowup of a regular local surface is the projective line

Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `f : X ⟶ S = Spec A` be the blowup
of `Spec A` in `𝔪` and let `E` be its exceptional divisor. The closed immersion
`r : X ⟶ 𝐏¹_S = Proj A[T₀, T₁]` of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveSpaceEmbedding.lean`, attached to any
generating pair of `𝔪`, restricts on `E` to an **isomorphism onto `𝐏¹_κ = Proj κ[T₀, T₁]`**
(`Stacks.Blowup.exists_iso_exceptional_projectiveLine`). This is part (1) of Stacks tag 0AGQ; the
twists of parts (2) and (3) are in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveSpaceEmbeddingTwist.lean`, and the tag itself,
all three parts for one closed immersion, is
`Stacks.Blowup.exists_isClosedImmersion_blowUpSpec_maximalIdeal_exceptional_projectiveLine` in
`StacksFrontier/AlgebraicGeometry/Blowup/RegularSurfaceProjectiveLine.lean`.

The proof is the source's, in three steps, the first two of which hold for an arbitrary ideal `I`
of an arbitrary commutative ring `R`.

* `E` is the fibre of the blowup over the closed subscheme `V(I)`, hence `Proj` of the base change
  of the Rees algebra along `R → R/I` (`Stacks.Blowup.exceptionalIsoProjBaseChange`). This is base
  change for `Proj`, tag 01N2, in the form `Stacks.ProjBaseChange.isPullback_map_Spec`, together
  with `AlgebraicGeometry.Scheme.IdealSheafData.comapIso` and the identification of the closed
  subscheme `V(I)` of `Spec R` with `Spec (R/I)`.
* That base change is the associated graded ring `⨁ₙ Iⁿ/Iⁿ⁺¹` as a graded ring
  (`Stacks.Blowup.tensorGradedHomGr`), so the two have the same `Proj`.
* For `I = 𝔪` the maximal ideal of a regular local ring and `x₁, …, x_d` a minimal generating
  family, the associated graded ring is the graded polynomial algebra `κ[X₁, …, X_d]`: this is the
  graded-ring form of tag 00NO,
  `IsRegularLocalRing.gradedRing_maximalIdeal_isPolynomialAlgebra`. Taking `Proj` of it gives
  `𝐏^{d-1}_κ`.

## Main definitions

* `AssociatedGraded.polyGradedRingHom` and `AssociatedGraded.gradedRingHomPoly`: the canonical map
  `(A/I)[X₁, …, X_c] → Gr_I(A)` of tag 00NO and, when it is bijective, its inverse, as
  homomorphisms of graded rings.
* `Stacks.Blowup.exceptionalIsoProjBaseChange`: the exceptional divisor of the blowup of `Spec R`
  in `I` is `Proj ((R/I) ⊗[R] ⨁ₙ Iⁿ)`.
* `Stacks.Blowup.exceptionalGradedHom`: the graded ring homomorphism
  `(R/I)[T₀, …, T_{c-1}] ⟶ (R/I) ⊗[R] ⨁ₙ Iⁿ` whose `Proj` is that comparison.
* `Stacks.Blowup.exceptionalIsoProjectiveSpace`: the exceptional divisor is `𝐏^{c-1}_{R/I}`, for a
  generating family of `c` elements whose presentation of the associated graded ring is bijective.

## Main results

* `AssociatedGraded.isIso_projMap_polyGradedRingHom`: `Proj` of the associated graded ring is
  projective space over `A/I`, whenever the canonical map of tag 00NO is bijective.
* `Stacks.Blowup.isPullback_projBaseChangeMap_toSpec`: the exceptional divisor is the fibre of the
  blowup over `V(I)`.
* `Stacks.Blowup.subschemeι_comp_blowUpSpecToProjSpace`: the restriction of `r` to the exceptional
  divisor is `Stacks.Blowup.exceptionalIsoProjectiveSpace` followed by the inclusion of the
  special fibre `𝐏^{c-1}_{R/I} ⟶ 𝐏^{c-1}_{Spec R}`.
* `Stacks.Blowup.exists_iso_exceptional_projectiveLine`: for a regular local ring of dimension
  two and every generating pair of its maximal ideal, `r|_E` is an isomorphism onto `𝐏¹_κ`,
  part (1) of Stacks tag 0AGQ.

## Implementation notes

The special fibre `𝐏^{c-1}_{R/I} ⟶ 𝐏^{c-1}_{Spec R}` is `AlgebraicGeometry.Proj.map` of
`Stacks.ProjectiveCohomology.polyGradedMap`, coefficient change along `R → R/I`. Because that
inclusion is a monomorphism, the comparison isomorphism of
`Stacks.Blowup.subschemeι_comp_blowUpSpecToProjSpace` is the unique morphism `E ⟶ 𝐏^{c-1}_{R/I}`
through which `r|_E` factors; the statement is therefore the source's assertion that `r|_E`
*is* the identification of `E` with the special fibre, and not merely that the two schemes are
isomorphic.

The `GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin c) R)` instance is
`MvPolynomial.gradedAlgebra`, ascribed `local` here as in every other file that forms `Proj` of a
polynomial ring.

The exceptional divisor is written out as the pullback along `toSpec I` of the ideal sheaf
`Scheme.IdealSheafData.ofIdealTop (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)`,
the spelling of `StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveSpaceEmbeddingTwist.lean` and of
`Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec_ofIdealTop`.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 00NO](https://stacks.math.columbia.edu/tag/00NO)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TensorProduct HomogeneousIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AssociatedGraded

variable {A : Type u} [CommRing A] {c : ℕ}

/-! ### Tag 00NO as a homomorphism of graded rings -/

/-- `AssociatedGraded.polyGradedHom` as a homomorphism of graded rings, from the grading of
`(A/I)[X_1, …, X_c]` by homogeneous degree to the grading of `Gr_I(A)`. -/
def polyGradedRingHom (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I) :
    MvPolynomial.homogeneousSubmodule (Fin c) (A ⧸ I) →+*ᵍ grading I where
  toRingHom := polyGradedHom I x hx
  map_mem {n p} hp :=
    polyGradedHom_mem_grading I x hx ((MvPolynomial.mem_homogeneousSubmodule n p).1 hp)

/-- The inverse of `AssociatedGraded.polyGradedRingHom`, as a homomorphism of graded rings. Its
degree-preservation is `AssociatedGraded.mem_grading_iff_exists_isHomogeneous`: a homogeneous
element of degree `n` of `Gr_I(A)` is the value of a homogeneous polynomial of degree `n`. -/
def gradedRingHomPoly (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (polyGradedHom I x hx)) :
    grading I →+*ᵍ MvPolynomial.homogeneousSubmodule (Fin c) (A ⧸ I) where
  toRingHom := (RingEquiv.ofBijective _ hbij).symm.toRingHom
  map_mem {n z} hz := by
    obtain ⟨p, hp, hpz⟩ := (mem_grading_iff_exists_isHomogeneous I x hx hI n z).1 hz
    have hsymm : (RingEquiv.ofBijective _ hbij).symm z = p := by
      rw [← hpz]
      exact (RingEquiv.ofBijective _ hbij).symm_apply_apply p
    rw [show (RingEquiv.ofBijective _ hbij).symm.toRingHom z
        = (RingEquiv.ofBijective _ hbij).symm z from rfl, hsymm]
    exact (MvPolynomial.mem_homogeneousSubmodule n p).2 hp

/-- `AssociatedGraded.gradedRingHomPoly` is a left inverse of
`AssociatedGraded.polyGradedRingHom`. -/
theorem gradedRingHomPoly_comp_polyGradedRingHom (I : Ideal A) (x : Fin c → A)
    (hx : ∀ i, x i ∈ I) (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (polyGradedHom I x hx)) :
    (gradedRingHomPoly I x hx hI hbij).comp (polyGradedRingHom I x hx) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin c) (A ⧸ I)) :=
  GradedRingHom.ext fun p => (RingEquiv.ofBijective _ hbij).symm_apply_apply p

/-- `AssociatedGraded.gradedRingHomPoly` is a right inverse of
`AssociatedGraded.polyGradedRingHom`. -/
theorem polyGradedRingHom_comp_gradedRingHomPoly (I : Ideal A) (x : Fin c → A)
    (hx : ∀ i, x i ∈ I) (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (polyGradedHom I x hx)) :
    (polyGradedRingHom I x hx).comp (gradedRingHomPoly I x hx hI hbij) =
      GradedRingHom.id (grading I) :=
  GradedRingHom.ext fun z => (RingEquiv.ofBijective _ hbij).apply_symm_apply z

/-- The irrelevant-ideal hypothesis `AlgebraicGeometry.Proj.map` asks of
`AssociatedGraded.polyGradedRingHom`. -/
theorem irrelevant_le_map_polyGradedRingHom (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (polyGradedHom I x hx)) :
    irrelevant (grading I) ≤
      (irrelevant (MvPolynomial.homogeneousSubmodule (Fin c) (A ⧸ I))).map
        (polyGradedRingHom I x hx) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
    (polyGradedRingHom_comp_gradedRingHomPoly I x hx hI hbij)

/-- The irrelevant-ideal hypothesis `AlgebraicGeometry.Proj.map` asks of
`AssociatedGraded.gradedRingHomPoly`. -/
theorem irrelevant_le_map_gradedRingHomPoly (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (polyGradedHom I x hx)) :
    irrelevant (MvPolynomial.homogeneousSubmodule (Fin c) (A ⧸ I)) ≤
      (irrelevant (grading I)).map (gradedRingHomPoly I x hx hI hbij) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
    (gradedRingHomPoly_comp_polyGradedRingHom I x hx hI hbij)

/-- **`Proj` of the associated graded ring is projective space over `A/I`**, whenever the
canonical map of Tag 00NO is bijective. -/
theorem isIso_projMap_polyGradedRingHom (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (polyGradedHom I x hx)) :
    IsIso (Proj.map (polyGradedRingHom I x hx)
      (irrelevant_le_map_polyGradedRingHom I x hx hI hbij)) :=
  Proj.isIso_map _ (irrelevant_le_map_gradedRingHomPoly I x hx hI hbij)
    (gradedRingHomPoly_comp_polyGradedRingHom I x hx hI hbij)
    (polyGradedRingHom_comp_gradedRingHomPoly I x hx hI hbij)

end AssociatedGraded

/-! ### The exceptional divisor as `Proj` of the base-changed Rees algebra -/

namespace Stacks.Blowup

open CommRingCat (ofHom)

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The comparison of `Spec (R/I)` with the closed subscheme of `Spec R` cut out by `I`, in the
spelling `Scheme.IdealSheafData.ofIdealTop (Ideal.comap (Scheme.ΓSpecIso _).hom.hom I)` in which
the exceptional divisor of the blowup is written. This is the source component of
`AlgebraicGeometry.Spec.arrowIsoQuotientSubschemeι`, with the kernel computed by
`AlgebraicGeometry.ker_Spec_map_quotient_mk` respelled by
`AlgebraicGeometry.Ideal.comap_hom_eq_map_inv`. -/
def specQuotientIsoSubscheme :
    Spec (CommRingCat.of (R ⧸ I)) ≅
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).subscheme :=
  letI : IsClosedImmersion (Spec.map (ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  asIso (Spec.map (ofHom (Ideal.Quotient.mk I))).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (by
      rw [AlgebraicGeometry.ker_Spec_map_quotient_mk,
        AlgebraicGeometry.Ideal.comap_hom_eq_map_inv]))

/-- The comparison `Stacks.Blowup.specQuotientIsoSubscheme` followed by the inclusion of the
closed subscheme into `Spec R` is `Spec` of the quotient map `R → R/I`. -/
@[reassoc]
theorem specQuotientIsoSubscheme_hom_comp_subschemeι :
    (specQuotientIsoSubscheme I).hom ≫
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).subschemeι =
      Spec.map (ofHom (Ideal.Quotient.mk I)) := by
  let : IsClosedImmersion (Spec.map (ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [specQuotientIsoSubscheme, Iso.trans_hom, asIso_hom, Category.assoc,
    eqToIso.hom, AlgebraicGeometry.eqToHom_subscheme_comp_subschemeι]
  · exact (Spec.map (ofHom (Ideal.Quotient.mk I))).toImage_imageι
  · rw [AlgebraicGeometry.ker_Spec_map_quotient_mk, AlgebraicGeometry.Ideal.comap_hom_eq_map_inv]

/-- The structure morphism of the blowup, written through the structure map of the degree-zero
part of the Rees grading. This is the spelling in which the base-change square of
`Stacks.ProjBaseChange.isPullback_map_Spec` is phrased. -/
theorem toSpec_eq_toSpecZero_comp_specMap_algebraMap :
    toSpec I = Proj.toSpecZero (reesGrading I) ≫
      Spec.map (ofHom (algebraMap R ↥(reesGrading I 0))) := by
  rw [toSpec]
  congr 2

/-- **The exceptional divisor of the blowup of `Spec R` in `I` is the fibre of the blowup over
`V(I)`.** The square exhibiting `Proj ((R/I) ⊗[R] ⨁ₙ Iⁿ)` as that fibre, with the closed
subscheme `V(I)` of `Spec R` written as the subscheme of the ideal sheaf attached to `I`. -/
theorem isPullback_projBaseChangeMap_toSpec :
    IsPullback (Stacks.ProjBaseChange.map (reesGrading I) (R ⧸ I))
      ((Proj.toSpecZero (Stacks.ProjBaseChange.grading (reesGrading I) (R ⧸ I)) ≫
        Spec.map (ofHom (algebraMap (R ⧸ I)
          ↥(Stacks.ProjBaseChange.grading (reesGrading I) (R ⧸ I) 0)))) ≫
        (specQuotientIsoSubscheme I).hom)
      (toSpec I)
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).subschemeι := by
  refine (Stacks.ProjBaseChange.isPullback_map_Spec (reesGrading I) (R ⧸ I)).of_iso
    (Iso.refl _) (Iso.refl _) (specQuotientIsoSubscheme I) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.id_comp _).symm)
    (((Category.comp_id _).trans
      (toSpec_eq_toSpecZero_comp_specMap_algebraMap I).symm).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (specQuotientIsoSubscheme_hom_comp_subschemeι I).symm)

/-- **The exceptional divisor of the blowup of `Spec R` in `I` is `Proj` of the base change of the
Rees algebra along `R → R/I`.** -/
def exceptionalIsoProjBaseChange :
    ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).comap
          (toSpec I)).subscheme ≅
      Proj (Stacks.ProjBaseChange.grading (reesGrading I) (R ⧸ I)) :=
  (Scheme.IdealSheafData.comapIso _ (toSpec I)) ≪≫
    (IsPullback.of_hasPullback (toSpec I)
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).subschemeι).isoIsPullback
      _ _ (isPullback_projBaseChangeMap_toSpec I)

/-- The comparison of the exceptional divisor with `Proj` of the base-changed Rees algebra is
compatible with the two inclusions into the blowup. -/
@[reassoc]
theorem exceptionalIsoProjBaseChange_hom_comp_map :
    (exceptionalIsoProjBaseChange I).hom ≫
        Stacks.ProjBaseChange.map (reesGrading I) (R ⧸ I) =
      ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).comap
          (toSpec I)).subschemeι :=
  ((Category.assoc _ _ _).trans
    (congrArg (fun k => (Scheme.IdealSheafData.comapIso _ (toSpec I)).hom ≫ k)
      (IsPullback.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback (toSpec I) _)
        (isPullback_projBaseChangeMap_toSpec I)))).trans
    (Scheme.IdealSheafData.comapIso_hom_fst _ (toSpec I))

/-! ### The exceptional divisor as `Proj` of the associated graded ring -/

/-- **`Proj` of the base-changed Rees algebra is `Proj` of the associated graded ring.** -/
theorem isIso_projMap_grGradedHomTensor :
    IsIso (Proj.map (grGradedHomTensor I) (irrelevant_le_map_grGradedHomTensor I)) :=
  Proj.isIso_map _ (irrelevant_le_map_tensorGradedHomGr I) (tensorGradedHomGr_comp I)
    (grGradedHomTensor_comp I)

/-- The class in `Iⁿ/Iⁿ⁺¹` of an element `a` of `Iⁿ` is sent to `1 ⊗ a tⁿ` in
`(R/I) ⊗[R] ⨁ₙ Iⁿ`. -/
theorem grToTensor_classOfPow (n : ℕ) (a : ↥(I ^ n)) :
    grToTensor I (AssociatedGraded.classOfPow I n a) =
      1 ⊗ₜ[R] reesMonomialPow I n ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩ :=
  grToTensor_of I n _

variable {c : ℕ}

/-- The graded ring homomorphism `(R/I)[T₀, …, T_{c-1}] ⟶ (R/I) ⊗[R] ⨁ₙ Iⁿ` attached to a
generating family `x₀, …, x_{c-1}` of `I`: the polynomial presentation of the associated graded
ring of Tag 00NO, read through the identification of the associated graded ring with the base
change of the Rees algebra. -/
def exceptionalGradedHom (x : Fin c → R) (hx : ∀ i, x i ∈ I) :
    MvPolynomial.homogeneousSubmodule (Fin c) (R ⧸ I) →+*ᵍ
      Stacks.ProjBaseChange.grading (reesGrading I) (R ⧸ I) :=
  (grGradedHomTensor I).comp (AssociatedGraded.polyGradedRingHom I x hx)

/-- The irrelevant-ideal hypothesis `AlgebraicGeometry.Proj.map` asks of
`Stacks.Blowup.exceptionalGradedHom`. -/
theorem irrelevant_le_map_exceptionalGradedHom (x : Fin c → R) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (AssociatedGraded.polyGradedHom I x hx)) :
    irrelevant (Stacks.ProjBaseChange.grading (reesGrading I) (R ⧸ I)) ≤
      (irrelevant (MvPolynomial.homogeneousSubmodule (Fin c) (R ⧸ I))).map
        (exceptionalGradedHom I x hx) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (AssociatedGraded.irrelevant_le_map_polyGradedRingHom I x hx hI hbij)
    (irrelevant_le_map_grGradedHomTensor I)

/-- `Proj` of `Stacks.Blowup.exceptionalGradedHom` is the composite of `Proj` of
`Stacks.Blowup.grGradedHomTensor` and `Proj` of `AssociatedGraded.polyGradedRingHom`. -/
theorem projMap_exceptionalGradedHom_eq (x : Fin c → R) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (AssociatedGraded.polyGradedHom I x hx)) :
    Proj.map (exceptionalGradedHom I x hx)
        (irrelevant_le_map_exceptionalGradedHom I x hx hI hbij) =
      Proj.map (grGradedHomTensor I) (irrelevant_le_map_grGradedHomTensor I) ≫
        Proj.map (AssociatedGraded.polyGradedRingHom I x hx)
          (AssociatedGraded.irrelevant_le_map_polyGradedRingHom I x hx hI hbij) :=
  Proj.map_comp _ _ _ _

/-- `Proj` of `Stacks.Blowup.exceptionalGradedHom` is an isomorphism whenever the polynomial
presentation of the associated graded ring is bijective. -/
theorem isIso_projMap_exceptionalGradedHom (x : Fin c → R) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (AssociatedGraded.polyGradedHom I x hx)) :
    IsIso (Proj.map (exceptionalGradedHom I x hx)
      (irrelevant_le_map_exceptionalGradedHom I x hx hI hbij)) := by
  rw [projMap_exceptionalGradedHom_eq I x hx hI hbij]
  have := isIso_projMap_grGradedHomTensor I
  have := AssociatedGraded.isIso_projMap_polyGradedRingHom I x hx hI hbij
  infer_instance

/-- **The exceptional divisor of the blowup of `Spec R` in `I` is `𝐏^{c-1}_{R/I}`**, for an ideal
`I` generated by `c` elements whose polynomial presentation of the associated graded ring is
bijective — by Tag 00NO, any minimal generating family of the maximal ideal of a regular local
ring. -/
def exceptionalIsoProjectiveSpace (x : Fin c → R) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hbij : Function.Bijective (AssociatedGraded.polyGradedHom I x hx)) :
    ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).comap
          (toSpec I)).subscheme ≅
      Proj (MvPolynomial.homogeneousSubmodule (Fin c) (R ⧸ I)) :=
  letI := isIso_projMap_exceptionalGradedHom I x hx hI hbij
  exceptionalIsoProjBaseChange I ≪≫
    asIso (Proj.map (exceptionalGradedHom I x hx)
      (irrelevant_le_map_exceptionalGradedHom I x hx hI hbij))

/-! ### The comparison is the restriction of the immersion into projective space -/

/-- **The polynomial presentation of the Rees algebra, base changed to `R/I`, is the polynomial
presentation of the associated graded ring.** Both send `Tᵢ` to the class of `xᵢ` in degree one
and a constant `a` to `1 ⊗ a`; this is the compatibility that makes the comparison of the
exceptional divisor with projective space the restriction of the immersion of the blowup. -/
theorem includeRight_comp_reesPresentation (x : Fin c → R) (hx : ∀ i, x i ∈ I) :
    (Stacks.ProjBaseChange.includeRight (reesGrading I) (R ⧸ I)).comp
        (reesPresentation I x hx) =
      (exceptionalGradedHom I x hx).comp
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin c) (Ideal.Quotient.mk I)) := by
  have key : ∀ (n : ℕ) (a : R) (ha : a ∈ I ^ n) (y : reesAlgebra I)
      (z : AssociatedGraded.gradedRing I), (y : Polynomial R) = Polynomial.monomial n a →
      z = AssociatedGraded.classOfPow I n ⟨a, ha⟩ → (1 : R ⧸ I) ⊗ₜ[R] y = grToTensor I z :=
    fun n a ha y z hy hz => by
      rw [hz, grToTensor_classOfPow]
      exact congrArg _ (Subtype.ext (by simp [hy]))
  refine GradedRingHom.coe_ringHom_injective
    (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · refine key 0 a (by simp) _ _ (by simp [reesPresentation]) ?_
    exact (congrArg (AssociatedGraded.polyGradedHom I x hx) (MvPolynomial.map_C _ _)).trans
      ((MvPolynomial.eval₂Hom_C _ _ _).trans (AssociatedGraded.quotientRingHom_mk I a (by simp)))
  · refine key 1 (x i) (by simpa using hx i) _ _ (by simp [reesPresentation]) ?_
    exact (congrArg (AssociatedGraded.polyGradedHom I x hx) (MvPolynomial.map_X _ _)).trans
      (MvPolynomial.eval₂Hom_X' _ _ _)

/-- **The immersion of the blowup into projective space, restricted to the exceptional divisor,
is the comparison with projective space over `R/I` followed by the inclusion of the special
fibre.** -/
theorem projBaseChangeMap_comp_blowUpSpecToProjSpace (x : Fin c → R) (hx : ∀ i, x i ∈ I)
    (hspan : I = Ideal.span (Set.range x))
    (hbij : Function.Bijective (AssociatedGraded.polyGradedHom I x hx)) :
    Stacks.ProjBaseChange.map (reesGrading I) (R ⧸ I) ≫ blowUpSpecToProjSpace I x hx hspan =
      Proj.map (exceptionalGradedHom I x hx)
          (irrelevant_le_map_exceptionalGradedHom I x hx hspan.symm hbij) ≫
        Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin c) (Ideal.Quotient.mk I))
          (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin c)
            (Ideal.Quotient.mk I)) :=
  (Proj.map_comp (reesPresentation I x hx)
      (Stacks.ProjBaseChange.includeRight (reesGrading I) (R ⧸ I)) _ _).symm.trans
    ((Proj.map_congr (includeRight_comp_reesPresentation I x hx) _ _).trans
      (Proj.map_comp (Stacks.ProjectiveCohomology.polyGradedMap (Fin c) (Ideal.Quotient.mk I))
        (exceptionalGradedHom I x hx) _ _))

/-- **The restriction of `r` to the exceptional divisor is the comparison with `𝐏^{c-1}_{R/I}`.**
The immersion `E ⟶ X ⟶ 𝐏^{c-1}_{Spec R}` of the exceptional divisor into projective space over
the base factors as the isomorphism `Stacks.Blowup.exceptionalIsoProjectiveSpace` onto
`𝐏^{c-1}_{R/I}` followed by the inclusion of that special fibre. -/
theorem subschemeι_comp_blowUpSpecToProjSpace (x : Fin c → R) (hx : ∀ i, x i ∈ I)
    (hspan : I = Ideal.span (Set.range x))
    (hbij : Function.Bijective (AssociatedGraded.polyGradedHom I x hx)) :
    ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)).comap
            (toSpec I)).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
      (exceptionalIsoProjectiveSpace I x hx hspan.symm hbij).hom ≫
        Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin c) (Ideal.Quotient.mk I))
          (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin c)
            (Ideal.Quotient.mk I)) :=
  (congrArg (fun k => k ≫ blowUpSpecToProjSpace I x hx hspan)
      (exceptionalIsoProjBaseChange_hom_comp_map I).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => (exceptionalIsoProjBaseChange I).hom ≫ k)
          (projBaseChangeMap_comp_blowUpSpecToProjSpace I x hx hspan hbij)).trans
        (Category.assoc _ _ _).symm))

/-! ### The exceptional divisor of a regular local surface -/

open IsLocalRing in
/-- **The restriction of `r` to the exceptional divisor of a regular local surface identifies it
with `𝐏¹_κ`.** Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let
`X = Proj (⨁ₙ 𝔪ⁿ) ⟶ S = Spec A` be the blowup of `Spec A` in `𝔪` and let `E` be its exceptional
divisor, the inverse image of the closed point. For **every** generating pair `x` of `𝔪` and the
closed immersion `r : X ⟶ 𝐏¹_S = Proj A[T₀, T₁]` it determines, the restriction `r|_E` of `r` to
`E` is an isomorphism of `E` onto `𝐏¹_κ = Proj κ[T₀, T₁]`: there is an isomorphism
`ρ : E ≅ 𝐏¹_κ` with `r|_E = ρ` followed by the inclusion of the special fibre `𝐏¹_κ ⟶ 𝐏¹_S`,
which is the morphism of projective lines induced by `A → κ`. As that inclusion is a
monomorphism, `ρ` is the unique such comparison.

This is part (1) of Stacks tag 0AGQ for the closed immersion attached to `x`; the tag is
`Stacks.Blowup.exists_isClosedImmersion_blowUpSpec_maximalIdeal_exceptional_projectiveLine`.

The proof is the source's: the fibre of the Rees algebra over `κ` is the associated graded ring
`⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹` (`Stacks.Blowup.tensorGradedHomGr`), which is the polynomial algebra `κ[T₀, T₁]` on
the classes of `x` by the graded-ring form of Tag 00NO
(`IsRegularLocalRing.gradedRing_maximalIdeal_isPolynomialAlgebra`), because two generators of the
maximal ideal of a regular local ring of dimension two form a regular system of parameters; and
`E` is the fibre of the blowup over `Spec κ` by base change for `Proj` (Tag 01N2,
`Stacks.ProjBaseChange.isPullback_map_Spec`). -/
@[sga "6 VII 3.1" "special case"]
theorem exists_iso_exceptional_projectiveLine (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) (x : Fin 2 → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : maximalIdeal A = Ideal.span (Set.range x)) :
    ∃ ρ : ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
            (maximalIdeal A))).comap (toSpec (maximalIdeal A))).subscheme ≅
        Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)),
      ((Scheme.IdealSheafData.ofIdealTop
            (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
              (maximalIdeal A))).comap
              (toSpec (maximalIdeal A))).subschemeι ≫
          blowUpSpecToProjSpace (maximalIdeal A) x hx hspan =
        ρ.hom ≫ Proj.map
          (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2)
            (Ideal.Quotient.mk (maximalIdeal A)))
          (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
            (Ideal.Quotient.mk (maximalIdeal A))) := by
  have hfr : (maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  have hbij : Function.Bijective (AssociatedGraded.polyGradedHom (maximalIdeal A) x hx) := by
    have hofList : Ideal.ofList (List.ofFn x) = maximalIdeal A := by
      rw [hspan]
      unfold Ideal.ofList
      congr 1
      ext a
      simp [eq_comm]
    have hqr := IsRegularLocalRing.isQuasiRegular (List.ofFn x) hofList
      (by rw [List.length_ofFn]; exact hfr.symm)
    exact AssociatedGraded.bijective_polyGradedHom _ _ hx hspan.symm
      ((Stacks.RingTheory.RegularIdealSheaf.bijective_associatedGradedMap_iff x).1
        ((Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff x).1 hqr)).injective
  exact ⟨exceptionalIsoProjectiveSpace _ x hx hspan.symm hbij,
    subschemeι_comp_blowUpSpecToProjSpace _ x hx hspan hbij⟩

end Stacks.Blowup

end
