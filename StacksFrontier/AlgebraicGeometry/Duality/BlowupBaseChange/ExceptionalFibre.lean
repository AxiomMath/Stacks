module

public import StacksFrontier.AlgebraicGeometry.Duality.BlowupBaseChange.Setup
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveLine
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.RegularToQuasiRegular
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular

/-!
# The exceptional divisor of the blowup of the affine plane in the origin

Let `k` be a field, `A = k[x, y]`, `I = (x, y)` the ideal of the origin and `f : X ⟶ 𝐀²_k` the
blowup in `I`. This file constructs the inclusion `g' : 𝐏¹_k = Proj k[T₀, T₁] ⟶ X` of the
exceptional divisor and proves that the square formed by `g'`, the structure morphism
`𝐏¹_k ⟶ Spec k`, `f` and the origin `g : Spec k ⟶ 𝐀²_k` is cartesian, as asserted in
[Stacks, Example 0AAC].

The morphism `g'` is `Proj` of the graded ring homomorphism `⨁ₙ Iⁿ ⟶ k[T₀, T₁]` sending an
element `a ∈ Iⁿ` of degree `n` to its homogeneous component of degree `n`, with `x ↦ T₀` and
`y ↦ T₁`. It factors as the base change `(A/I) ⊗[A] ⨁ₙ Iⁿ` of the Rees algebra, the associated
graded ring `⨁ₙ Iⁿ/Iⁿ⁺¹`, its inverse polynomial presentation onto `(A/I)[T₀, T₁]` and the
residue isomorphism `A/I ≅ k`. The proof pastes three cartesian squares:

* base change for `Proj` along `A → A/I` (Tag 01N2, `Stacks.ProjBaseChange.isPullback_map_Spec`);
* the isomorphism `Proj ((A/I) ⊗[A] ⨁ₙ Iⁿ) ≅ 𝐏¹_{A/I}`: the polynomial presentation
  `(A/I)[T₀, T₁] ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` of Tag 00NO is bijective because `x, y` is a regular, hence
  quasi-regular, sequence of `k[x, y]`;
* the base change of projective space along `A/I ⟶ k`
  (`Stacks.ProjectiveCohomology.isPullback_projModelToSpec`).

## Main definitions

* `Stacks.Duality.BlowupBaseChange.exceptionalHom`: the graded ring homomorphism
  `⨁ₙ Iⁿ ⟶ k[T₀, T₁]`.
* `Stacks.Duality.BlowupBaseChange.g'`: the inclusion `𝐏¹_k ⟶ X` of the exceptional divisor.

## Main results

* `Stacks.Duality.BlowupBaseChange.isPullback`: the fibre of the blowup over the origin is `𝐏¹_k`.

## References

* [Stacks Project, Tag 0AAC](https://stacks.math.columbia.edu/tag/0AAC)
* [Stacks Project, Tag 00NO](https://stacks.math.columbia.edu/tag/00NO)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.BlowupBaseChange

variable (k : Type u) [Field k]

/-- The coordinates `x, y` lie in the ideal of the origin. -/
theorem X_mem_origin (i : Fin 2) : (MvPolynomial.X i : A k) ∈ origin k :=
  Ideal.subset_span ⟨i, rfl⟩

/-- **The associated graded ring of `k[x, y]` along `(x, y)` is the polynomial ring
`(A/I)[T₀, T₁]`** (Tag 00NO): the canonical map sending `Tᵢ` to the class of the `i`-th coordinate
in `I/I²` is bijective, because the coordinates form a regular, hence quasi-regular, sequence. -/
theorem bijective_polyGradedHom_X :
    Function.Bijective
      (AssociatedGraded.polyGradedHom (origin k) MvPolynomial.X (X_mem_origin k)) :=
  AssociatedGraded.bijective_polyGradedHom _ _ _ rfl
    ((Stacks.RingTheory.RegularIdealSheaf.bijective_associatedGradedMap_iff _).1
      ((Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff _).1
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegular_ofFn_of_isWeaklyRegular _
          (MvPolynomial.isWeaklyRegular_ofFn_X 1)))).injective

/-- The residue map `k[x, y]/(x, y) ⟶ k` at the origin, induced by evaluation at `x = y = 0`. -/
def residue : A k ⧸ origin k →+* k :=
  Ideal.Quotient.lift (origin k) MvPolynomial.constantCoeff fun _ ha =>
    RingHom.mem_ker.1 ((Ideal.span_le (I := RingHom.ker MvPolynomial.constantCoeff)).2
      (by rintro _ ⟨i, rfl⟩; exact RingHom.mem_ker.2 (MvPolynomial.constantCoeff_X _ i)) ha)

/-- The residue map composed with the quotient map is evaluation at the origin. -/
theorem residue_comp_mk :
    (residue k).comp (Ideal.Quotient.mk (origin k)) = MvPolynomial.constantCoeff :=
  Ideal.Quotient.lift_comp_mk _ _ _

open Stacks.Blowup in
/-- The graded ring homomorphism `(A/I) ⊗[A] ⨁ₙ Iⁿ ⟶ (A/I)[T₀, T₁]`: the identification of the
base-changed Rees algebra with the associated graded ring `⨁ₙ Iⁿ/Iⁿ⁺¹`, followed by the inverse of
its polynomial presentation. It is inverse to `Stacks.Blowup.exceptionalGradedHom`. -/
def exceptionalGradedInv :
    Stacks.ProjBaseChange.grading (reesGrading (origin k)) (A k ⧸ origin k) →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin 2) (A k ⧸ origin k) :=
  (AssociatedGraded.gradedRingHomPoly (origin k) MvPolynomial.X (X_mem_origin k) rfl
      (bijective_polyGradedHom_X k)).comp (tensorGradedHomGr (origin k))

open Stacks.Blowup in
/-- The irrelevant-ideal hypothesis `AlgebraicGeometry.Proj.map` asks of
`Stacks.Duality.BlowupBaseChange.exceptionalGradedInv`. -/
theorem irrelevant_le_map_exceptionalGradedInv :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) (A k ⧸ origin k)) ≤
      (HomogeneousIdeal.irrelevant
        (Stacks.ProjBaseChange.grading (reesGrading (origin k)) (A k ⧸ origin k))).map
        (exceptionalGradedInv k) :=
  HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_tensorGradedHomGr _)
    (AssociatedGraded.irrelevant_le_map_gradedRingHomPoly _ _ _ rfl _)

open Stacks.Blowup in
/-- `Stacks.Blowup.exceptionalGradedHom` is a left inverse of `exceptionalGradedInv`. -/
theorem exceptionalGradedHom_comp_exceptionalGradedInv :
    (exceptionalGradedHom (origin k) MvPolynomial.X (X_mem_origin k)).comp
        (exceptionalGradedInv k) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => by
    change grGradedHomTensor (origin k)
      (AssociatedGraded.polyGradedRingHom (origin k) MvPolynomial.X (X_mem_origin k)
      (AssociatedGraded.gradedRingHomPoly _ _ _ rfl (bijective_polyGradedHom_X k)
        (tensorGradedHomGr (origin k) x))) = x
    rw [show ∀ z, AssociatedGraded.polyGradedRingHom (origin k) MvPolynomial.X (X_mem_origin k)
        (AssociatedGraded.gradedRingHomPoly _ _ _ rfl (bijective_polyGradedHom_X k) z) = z from
      DFunLike.congr_fun (AssociatedGraded.polyGradedRingHom_comp_gradedRingHomPoly _ _ _ rfl
        (bijective_polyGradedHom_X k))]
    exact DFunLike.congr_fun (grGradedHomTensor_comp (origin k)) x

open Stacks.Blowup in
/-- `exceptionalGradedInv` is a left inverse of `Stacks.Blowup.exceptionalGradedHom`. -/
theorem exceptionalGradedInv_comp_exceptionalGradedHom :
    (exceptionalGradedInv k).comp
        (exceptionalGradedHom (origin k) MvPolynomial.X (X_mem_origin k)) =
      GradedRingHom.id _ :=
  GradedRingHom.ext fun p => by
    change AssociatedGraded.gradedRingHomPoly _ _ _ rfl (bijective_polyGradedHom_X k)
      (tensorGradedHomGr (origin k) (grGradedHomTensor (origin k)
        (AssociatedGraded.polyGradedRingHom (origin k) MvPolynomial.X (X_mem_origin k) p))) = p
    rw [show ∀ z, tensorGradedHomGr (origin k) (grGradedHomTensor (origin k) z) = z from
      DFunLike.congr_fun (tensorGradedHomGr_comp (origin k))]
    exact DFunLike.congr_fun (AssociatedGraded.gradedRingHomPoly_comp_polyGradedRingHom _ _ _ rfl
      (bijective_polyGradedHom_X k)) p

/-- `Proj` of the base-changed Rees algebra is `𝐏¹_{A/I}`. -/
instance isIso_projMap_exceptionalGradedInv :
    IsIso (Proj.map (exceptionalGradedInv k) (irrelevant_le_map_exceptionalGradedInv k)) :=
  Proj.isIso_map _
    (Stacks.Blowup.irrelevant_le_map_exceptionalGradedHom _ _ _ rfl (bijective_polyGradedHom_X k))
    (exceptionalGradedHom_comp_exceptionalGradedInv k)
    (exceptionalGradedInv_comp_exceptionalGradedHom k)

open Stacks.Blowup in
/-- **The graded ring homomorphism `⨁ₙ (x, y)ⁿ ⟶ k[T₀, T₁]` cutting out the exceptional divisor.**
An element `a ∈ (x, y)ⁿ` in degree `n` is sent to its homogeneous component of degree `n`, with
`x ↦ T₀` and `y ↦ T₁`: the composite of the base change to `A/I`,
`Stacks.Duality.BlowupBaseChange.exceptionalGradedInv` and the residue map `A/I ⟶ k` on
coefficients. -/
def exceptionalHom : reesGrading (origin k) →+*ᵍ polyGrading k 1 :=
  (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (residue k)).comp
    ((exceptionalGradedInv k).comp
      (Stacks.ProjBaseChange.includeRight (reesGrading (origin k)) (A k ⧸ origin k)))

open Stacks.Blowup in
/-- The irrelevant-ideal hypothesis `AlgebraicGeometry.Proj.map` asks of
`Stacks.Duality.BlowupBaseChange.exceptionalHom`. -/
theorem irrelevant_le_map_exceptionalHom :
    HomogeneousIdeal.irrelevant (polyGrading k 1) ≤
      (HomogeneousIdeal.irrelevant (reesGrading (origin k))).map (exceptionalHom k) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (HomogeneousIdeal.irrelevant_le_map_comp
      (Stacks.ProjBaseChange.irrelevant_le_map _ _)
      (irrelevant_le_map_exceptionalGradedInv k))
    (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap _ _)

/-- The inclusion `𝐏¹_k = E ⟶ X` of the exceptional divisor: `Proj` of
`Stacks.Duality.BlowupBaseChange.exceptionalHom`. -/
def g' : AlgebraicGeometry.Proj (polyGrading k 1) ⟶ blowup k :=
  Proj.map (exceptionalHom k) (irrelevant_le_map_exceptionalHom k)

/-- The inclusion of the exceptional divisor factors as the base change of `𝐏¹` along `A/I ⟶ k`,
the isomorphism `𝐏¹_{A/I} ≅ Proj ((A/I) ⊗[A] ⨁ₙ Iⁿ)` and the base change of the blowup along
`A ⟶ A/I`. -/
theorem g'_eq : g' k = Stacks.ProjectiveCohomology.projModelMap 1 (residue k) ≫
    Proj.map (exceptionalGradedInv k) (irrelevant_le_map_exceptionalGradedInv k) ≫
      Stacks.ProjBaseChange.map (Stacks.Blowup.reesGrading (origin k)) (A k ⧸ origin k) := by
  simp only [Stacks.ProjectiveCohomology.projModelMap, Stacks.ProjBaseChange.map,
    ← Proj.map_comp]
  rfl

open Stacks.Blowup in
/-- `Stacks.Duality.BlowupBaseChange.exceptionalGradedInv` sends a scalar of `A/I` to the
corresponding constant polynomial. -/
theorem exceptionalGradedInv_algebraMap (r : A k ⧸ origin k) :
    exceptionalGradedInv k (algebraMap (A k ⧸ origin k)
      (Stacks.ProjBaseChange.grading (reesGrading (origin k)) (A k ⧸ origin k) 0) r : _) =
      MvPolynomial.C r := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (1 : A k ⧸ origin k) ⊗ₜ[A k] algebraMap (A k) (reesAlgebra (origin k)) a =
      exceptionalGradedHom (origin k) MvPolynomial.X (X_mem_origin k)
        (MvPolynomial.C (Ideal.Quotient.mk _ a)) := by
    have h := DFunLike.congr_fun
      (includeRight_comp_reesPresentation (origin k) MvPolynomial.X (X_mem_origin k))
      (MvPolynomial.C a)
    change (1 : A k ⧸ origin k) ⊗ₜ[A k] reesPresentation (origin k) MvPolynomial.X
        (X_mem_origin k) (MvPolynomial.C a) =
      exceptionalGradedHom (origin k) MvPolynomial.X (X_mem_origin k)
        (MvPolynomial.map (Ideal.Quotient.mk _) (MvPolynomial.C a)) at h
    rw [MvPolynomial.map_C] at h
    rw [← h]
    exact congrArg _ (MvPolynomial.eval₂Hom_C _ _ _).symm
  have h2 : Subtype.val (algebraMap (A k ⧸ origin k)
      (Stacks.ProjBaseChange.grading (reesGrading (origin k)) (A k ⧸ origin k) 0)
        (Ideal.Quotient.mk _ a)) =
      (1 : A k ⧸ origin k) ⊗ₜ[A k] algebraMap (A k) (reesAlgebra (origin k)) a := by
    change Ideal.Quotient.mk _ a ⊗ₜ[A k] (1 : reesAlgebra (origin k)) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
    rfl
  rw [h2, h1]
  exact DFunLike.congr_fun (exceptionalGradedInv_comp_exceptionalGradedHom k) _

/-- The isomorphism `𝐏¹_{A/I} ≅ Proj ((A/I) ⊗[A] ⨁ₙ Iⁿ)` is a morphism over `Spec (A/I)`. -/
theorem commSq_exceptionalGradedInv :
    CommSq (Proj.map (exceptionalGradedInv k) (irrelevant_le_map_exceptionalGradedInv k))
      (projToSpecCoeff (A k ⧸ origin k) 1)
      (Proj.toSpecZero (Stacks.ProjBaseChange.grading (Stacks.Blowup.reesGrading (origin k))
          (A k ⧸ origin k)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (A k ⧸ origin k)
          ↥(Stacks.ProjBaseChange.grading (Stacks.Blowup.reesGrading (origin k))
            (A k ⧸ origin k) 0))))
      (𝟙 _) := by
  constructor
  rw [Proj.map_toSpecZero_assoc, projToSpecCoeff, Category.comp_id, ← Spec.map_comp]
  congr 2
  rw [Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap]
  exact CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext (exceptionalGradedInv_algebraMap k r))

/-- **The fibre of the blowup over the origin is `𝐏¹_k`** [Stacks, Example 0AAC]: the square
formed by the inclusion `g'` of the exceptional divisor, the structure morphism `𝐏¹_k ⟶ Spec k`,
the blowup `f : X ⟶ 𝐀²_k` and the origin `g : Spec k ⟶ 𝐀²_k` is cartesian. -/
theorem isPullback : IsPullback (g' k) (projToSpecCoeff k 1) (f k) (g k) := by
  have s1 := (Stacks.ProjectiveCohomology.isPullback_projModelToSpec (n := 1) (f := residue k)).flip
  rw [← Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec,
    ← Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec] at s1
  have s2 := IsPullback.of_horiz_isIso (commSq_exceptionalGradedInv k)
  have s3 := Stacks.ProjBaseChange.isPullback_map_Spec
    (Stacks.Blowup.reesGrading (origin k)) (A k ⧸ origin k)
  rw [← Stacks.Blowup.toSpec_eq_toSpecZero_comp_specMap_algebraMap] at s3
  have hbot : Spec.map (CommRingCat.ofHom (residue k)) ≫ 𝟙 _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap (A k) (A k ⧸ origin k))) = g k := by
    rw [Category.id_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (residue_comp_mk k))
  rw [g'_eq, ← hbot]
  exact s1.paste_horiz (s2.paste_horiz s3)

end Stacks.Duality.BlowupBaseChange
