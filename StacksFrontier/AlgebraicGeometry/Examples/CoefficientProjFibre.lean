module

public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Examples.CoefficientProjBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.RingTheory.GradedAlgebra.QuotientKerGradedIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibres of a coefficientwise projective family

The base change of a coefficientwise projective family along `R → S` is the coefficientwise
projective family of the extended coefficients, and the square it forms with the two structure
morphisms over `Spec S ⟶ Spec R` is cartesian. So the fibre of the family over a point of the
base is the `Proj` of the family whose coefficient ideals are the extensions of the original ones
to the residue field at that point — and any graded ring presenting that extended family
presents the fibre.

## Main results

* `Stacks.CoefficientProj.isPullback_baseChange`: the base-change square of the family is
  cartesian.
* `Stacks.CoefficientProj.exists_isPullback_of_gradedIso`: a graded ring isomorphic to the
  base-changed quotient has a `Proj` which is the fibre, over the base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open HomogeneousIdeal TensorProduct Stacks.GradedModel

namespace Stacks.CoefficientProj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {m : ℕ} {R : Type u} [CommRing R] (K : (Fin (m + 1) →₀ ℕ) → Ideal R)
  (S : Type u) [CommRing S] [Algebra R S]

/-! ### The comparison with the base change is a graded isomorphism -/

/-- The graded comparison `baseChangeGradedHom K S` agrees with the algebra isomorphism
`baseChangeAlgEquiv K S` on elements. -/
@[simp]
theorem baseChangeGradedHom_apply (x : S ⊗[R] (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K)) :
    baseChangeGradedHom K S x = baseChangeAlgEquiv K S x := rfl

/-- `baseChangeGradedInv K S` is a left inverse of `baseChangeGradedHom K S` as graded ring
homomorphisms. -/
theorem baseChangeGradedInv_comp_hom :
    (baseChangeGradedInv K S).comp (baseChangeGradedHom K S) =
      GradedRingHom.id (Stacks.ProjBaseChange.grading (projGrading K) S) :=
  GradedRingHom.ext fun x => (baseChangeAlgEquiv K S).symm_apply_apply x

/-- `baseChangeGradedInv K S` is a right inverse of `baseChangeGradedHom K S` as graded ring
homomorphisms. -/
theorem baseChangeGradedHom_comp_inv :
    (baseChangeGradedHom K S).comp (baseChangeGradedInv K S) =
      GradedRingHom.id (projGrading (baseChange K S)) :=
  GradedRingHom.ext fun x => (baseChangeAlgEquiv K S).apply_symm_apply x

/-- The irrelevant ideal of the family of extended coefficients is contained in the image of the
irrelevant ideal of the base-changed grading under `baseChangeGradedHom K S`. -/
theorem irrelevant_le_map_baseChangeGradedHom :
    (projGrading (baseChange K S))₊ ≤
      (Stacks.ProjBaseChange.grading (projGrading K) S)₊.map (baseChangeGradedHom K S) :=
  Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse _ _
    (baseChangeGradedHom_comp_inv K S)

/-- The irrelevant ideal of the base-changed grading is contained in the image of the irrelevant
ideal of the family of extended coefficients under `baseChangeGradedInv K S`. -/
theorem irrelevant_le_map_baseChangeGradedInv :
    (Stacks.ProjBaseChange.grading (projGrading K) S)₊ ≤
      (projGrading (baseChange K S))₊.map (baseChangeGradedInv K S) :=
  Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse _ _
    (baseChangeGradedInv_comp_hom K S)

/-- The comparison with the base change is a homomorphism of algebras over the extended base
ring, in degree zero. -/
theorem gradedZeroRingHom_baseChangeGradedHom :
    CommRingCat.ofHom (algebraMap S ↥(Stacks.ProjBaseChange.grading (projGrading K) S 0)) ≫
        CommRingCat.ofHom (baseChangeGradedHom K S).gradedZeroRingHom =
      CommRingCat.ofHom (algebraMap S ↥(projGrading (baseChange K S) 0)) := by
  rw [← CommRingCat.ofHom_comp]
  congr 1
  refine RingHom.ext fun s => Subtype.ext ?_
  simpa [SetLike.GradeZero.coe_algebraMap] using (baseChangeAlgEquiv K S).commutes s

/-! ### `Proj` of a graded homomorphism, over the base ring -/

section Transport

variable {k A' B' : Type u} [CommRing k] [CommRing A'] [CommRing B'] [Algebra k A'] [Algebra k B']
  {𝒞 : ℕ → Submodule k A'} {𝒟 : ℕ → Submodule k B'} [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

/-- **`AlgebraicGeometry.Proj.map` of a graded homomorphism is a morphism over the base ring**,
for any two structure maps to the degree-zero parts which the degree-zero component of the
homomorphism carries one to the other. -/
@[ega "II 2.8.5" "Case G(φ) = Proj(S)"]
theorem map_comp_toSpecZero_comp {w : 𝒞 →+*ᵍ 𝒟} (hw : 𝒟₊ ≤ 𝒞₊.map w)
    {u : CommRingCat.of k ⟶ CommRingCat.of ↥(𝒞 0)}
    {v : CommRingCat.of k ⟶ CommRingCat.of ↥(𝒟 0)}
    (huv : u ≫ CommRingCat.ofHom w.gradedZeroRingHom = v) :
    Proj.map w hw ≫ Proj.toSpecZero 𝒞 ≫ Spec.map u =
      Proj.toSpecZero 𝒟 ≫ Spec.map v := by
  rw [← Category.assoc, AlgebraicGeometry.Proj.map_toSpecZero w hw, Category.assoc,
    ← Spec.map_comp, huv]

end Transport

/-! ### The base-change square -/

/-- The irrelevant-ideal containment for the comparison of the family with the family of the
extended coefficients. -/
theorem irrelevant_le_map_baseChangeComp :
    (projGrading (baseChange K S))₊ ≤ (projGrading K)₊.map
      ((baseChangeGradedHom K S).comp
        (Stacks.ProjBaseChange.includeRight (projGrading K) S)) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (Stacks.ProjBaseChange.irrelevant_le_map (projGrading K) S)
    (irrelevant_le_map_baseChangeGradedHom K S)

/-- **The base-change square of a coefficientwise projective family is cartesian.** The `Proj` of
the family of extended coefficients is the fibre product of the family with `Spec S`. -/
theorem isPullback_baseChange :
    IsPullback
      (Proj.map ((baseChangeGradedHom K S).comp
          (Stacks.ProjBaseChange.includeRight (projGrading K) S))
        (irrelevant_le_map_baseChangeComp K S))
      (Proj.toSpecZero (projGrading (baseChange K S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S ↥(projGrading (baseChange K S) 0))))
      (toSpecBase K)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have h := map_comp_toSpecZero_comp (w := baseChangeGradedHom K S)
    (irrelevant_le_map_baseChangeGradedHom K S)
    (u := CommRingCat.ofHom (algebraMap S ↥(Stacks.ProjBaseChange.grading (projGrading K) S 0)))
    (gradedZeroRingHom_baseChangeGradedHom K S)
  rw [← h]
  exact Stacks.ProjBaseChange.isPullback_map_of_baseChange (projGrading K) S
    (irrelevant_le_map_baseChangeComp K S) (irrelevant_le_map_baseChangeGradedHom K S)
    (irrelevant_le_map_baseChangeGradedInv K S) (baseChangeGradedInv_comp_hom K S)
    (baseChangeGradedHom_comp_inv K S) rfl

/-! ### Transporting the fibre along a graded isomorphism -/

variable {M : Type u} [CommRing M] [Algebra S M] (ℳ : ℕ → Submodule S M) [GradedAlgebra ℳ]

/-- **A graded ring isomorphic to the quotient of the extended family has a `Proj` which is the
fibre of the family over `Spec S`.** -/
theorem exists_isPullback_of_gradedIso
    (w : projGrading (baseChange K S) →+*ᵍ ℳ) (w' : ℳ →+*ᵍ projGrading (baseChange K S))
    (hww' : w'.comp w = GradedRingHom.id (projGrading (baseChange K S)))
    (hw'w : w.comp w' = GradedRingHom.id ℳ)
    {v : CommRingCat.of S ⟶ CommRingCat.of ↥(ℳ 0)}
    (hv : CommRingCat.ofHom (algebraMap S ↥(projGrading (baseChange K S) 0)) ≫
        CommRingCat.ofHom w.gradedZeroRingHom = v) :
    ∃ g : AlgebraicGeometry.Proj ℳ ⟶ AlgebraicGeometry.Proj (projGrading K),
      IsPullback g (Proj.toSpecZero ℳ ≫ Spec.map v) (toSpecBase K)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have hw : ℳ₊ ≤ (projGrading (baseChange K S))₊.map w :=
    Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse w w' hw'w
  have hw' : (projGrading (baseChange K S))₊ ≤ ℳ₊.map w' :=
    Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse w' w hww'
  have hiso : IsIso (Proj.map w hw) := Proj.isIso_map hw hw' hww' hw'w
  refine ⟨Proj.map w hw ≫ Proj.map ((baseChangeGradedHom K S).comp
      (Stacks.ProjBaseChange.includeRight (projGrading K) S))
    (irrelevant_le_map_baseChangeComp K S), ?_⟩
  refine (isPullback_baseChange K S).of_iso' (asIso (Proj.map w hw)) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  rw [Iso.refl_hom, Category.comp_id, asIso_hom]
  exact map_comp_toSpecZero_comp hw hv

end Stacks.CoefficientProj

end
