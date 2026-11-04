module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModule
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective space of a module commutes with base change

Let `R` be a commutative ring, `S` an `R`-algebra and `M` an `R`-module. This file proves that

`𝐏_S(S ⊗_R M) = Spec S ×_{Spec R} 𝐏_R(M)`,

that is, the projective space of a base-changed module is the base change of the projective
space. It is Stacks tag 01N2 for the graded algebra `Sym_R(M)`, transported along the
base-change comparison `SymPow.symAlgBaseChangeEquiv` of symmetric algebras read as an
isomorphism of *graded* rings.

## Main definitions

* `Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedHom` and
  `Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedInv`: the graded ring isomorphism
  `S ⊗_R Sym_R(M) ≅ Sym_S(S ⊗_R M)` and its inverse, both carried by
  `SymPow.symAlgBaseChangeEquiv`.
* `Stacks.ProjectiveSpaceBaseChange.symBaseChangeGraded`: the graded ring homomorphism
  `Sym_R(M) → Sym_S(S ⊗_R M)`, `x ↦ 1 ⊗ x`.
* `Stacks.ProjectiveSpaceBaseChange.map`: the induced morphism `𝐏_S(S ⊗_R M) ⟶ 𝐏_R(M)`.
* `Stacks.ProjectiveSpaceBaseChange.isoPullback`: **the identification of `𝐏_S(S ⊗_R M)` with the
  fibre product `𝐏_R(M) ×_{Spec R} Spec S`.**

## Main results

* `Stacks.ProjectiveSpaceBaseChange.map_symmetricPower_baseChange`: the degreewise transport.
* `Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec`: **`𝐏_S(S ⊗_R M)` is
  the base change of `𝐏_R(M)` along `Spec S ⟶ Spec R`.**

## Implementation notes

The cartesian square for a *literal* tensor product of graded algebras is
`Stacks.ProjBaseChange.isPullback_map_Spec`, and its transport along a graded isomorphism onto
that tensor product is `Stacks.ProjBaseChange.isPullback_map_of_baseChange`, so the remaining
content is the graded isomorphism `S ⊗_R Sym_R(M) ≅ Sym_S(S ⊗_R M)`. The degreewise fact it
needs, that `SymPow.symAlgBaseChangeEquiv` carries the scalar extension of the degree-`n`
symmetric power onto the degree-`n` symmetric power, is
`SymPow.map_symAlgBaseChangeEquiv_baseChange`.

All three of `R`, `S` and `M` are in one universe: `Stacks.ProjBaseChange.grading` quantifies the
graded algebra, its base ring and the extension ring at a single universe.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open HomogeneousIdeal HomogeneousLocalization Graded

universe u

namespace Stacks.ProjectiveSpaceBaseChange

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (M : Type u) [AddCommGroup M] [Module R M]

/-! ### The graded isomorphism `S ⊗_R Sym_R(M) ≅ Sym_S(S ⊗_R M)` -/

/-- **The base-change comparison of symmetric algebras carries the scalar extension of the
degree-`n` symmetric power onto the degree-`n` symmetric power.** This is
`SymPow.map_symAlgBaseChangeEquiv_baseChange` with the base-changed grading of
`Stacks.ProjBaseChange.grading` on the left. -/
public theorem map_symmetricPower_baseChange (n : ℕ) :
    Submodule.map (SymPow.symAlgBaseChangeEquiv S M).toAlgHom.toLinearMap
        ((SymPow.symmetricPower n R M).baseChange S) =
      SymPow.symmetricPower n S (S ⊗[R] M) :=
  SymPow.map_symAlgBaseChangeEquiv_baseChange S M n

/-- **Scalar extension of a symmetric algebra is a symmetric algebra, as graded rings.**
`SymPow.symAlgBaseChangeEquiv` carries the base-changed grading of `S ⊗_R Sym_R(M)` to the
grading of `Sym_S(S ⊗_R M)` by symmetric powers. -/
public def symBaseChangeGradedHom :
    (fun n => (SymPow.symmetricPower n R M).baseChange S) →+*ᵍ
      (fun n => SymPow.symmetricPower n S (S ⊗[R] M)) where
  __ := (SymPow.symAlgBaseChangeEquiv S M).toRingHom
  map_mem {n x} hx := by
    have h : (SymPow.symAlgBaseChangeEquiv S M).toAlgHom.toLinearMap x ∈
        Submodule.map (SymPow.symAlgBaseChangeEquiv S M).toAlgHom.toLinearMap
          ((SymPow.symmetricPower n R M).baseChange S) :=
      Submodule.mem_map_of_mem hx
    rwa [map_symmetricPower_baseChange] at h

/-- The inverse of `Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedHom`, carried by the
inverse of `SymPow.symAlgBaseChangeEquiv`. -/
public def symBaseChangeGradedInv :
    (fun n => SymPow.symmetricPower n S (S ⊗[R] M)) →+*ᵍ
      (fun n => (SymPow.symmetricPower n R M).baseChange S) where
  __ := (SymPow.symAlgBaseChangeEquiv S M).symm.toRingHom
  map_mem {n y} hy := by
    rw [← map_symmetricPower_baseChange R S M n] at hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
    have hsymm : (SymPow.symAlgBaseChangeEquiv S M).symm y = z :=
      hzy ▸ (SymPow.symAlgBaseChangeEquiv S M).symm_apply_apply z
    exact hsymm ▸ hz

/-- `Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedHom` acts as
`SymPow.symAlgBaseChangeEquiv`. -/
@[simp]
public theorem symBaseChangeGradedHom_apply (x : S ⊗[R] SymmetricAlgebra R M) :
    symBaseChangeGradedHom R S M x = SymPow.symAlgBaseChangeEquiv S M x := rfl

/-- `Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedInv` acts as the inverse of
`SymPow.symAlgBaseChangeEquiv`. -/
@[simp]
public theorem symBaseChangeGradedInv_apply (y : SymmetricAlgebra S (S ⊗[R] M)) :
    symBaseChangeGradedInv R S M y = (SymPow.symAlgBaseChangeEquiv S M).symm y := rfl

/-- `symBaseChangeGradedInv` is a left inverse of `symBaseChangeGradedHom`: their composite is the
identity of `S ⊗_R Sym_R(M)` as a graded ring. -/
public theorem symBaseChangeGradedInv_comp_hom :
    (symBaseChangeGradedInv R S M).comp (symBaseChangeGradedHom R S M) =
      GradedRingHom.id (fun n => (SymPow.symmetricPower n R M).baseChange S) :=
  GradedRingHom.ext fun x => (SymPow.symAlgBaseChangeEquiv S M).symm_apply_apply x

/-- `symBaseChangeGradedInv` is a right inverse of `symBaseChangeGradedHom`: their composite is
the identity of `Sym_S(S ⊗_R M)` as a graded ring. -/
public theorem symBaseChangeGradedHom_comp_inv :
    (symBaseChangeGradedHom R S M).comp (symBaseChangeGradedInv R S M) =
      GradedRingHom.id (fun n => SymPow.symmetricPower n S (S ⊗[R] M)) :=
  GradedRingHom.ext fun y => (SymPow.symAlgBaseChangeEquiv S M).apply_symm_apply y

/-- The containment of irrelevant ideals for
`Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedHom`. -/
public theorem irrelevant_le_map_symBaseChangeGradedHom :
    (fun n => SymPow.symmetricPower n S (S ⊗[R] M))₊ ≤
      (fun n => (SymPow.symmetricPower n R M).baseChange S)₊.map
        (symBaseChangeGradedHom R S M) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (symBaseChangeGradedHom_comp_inv R S M)

/-- The containment of irrelevant ideals for
`Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedInv`. -/
public theorem irrelevant_le_map_symBaseChangeGradedInv :
    (fun n => (SymPow.symmetricPower n R M).baseChange S)₊ ≤
      (fun n => SymPow.symmetricPower n S (S ⊗[R] M))₊.map (symBaseChangeGradedInv R S M) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (symBaseChangeGradedInv_comp_hom R S M)

/-! ### The graded homomorphism `Sym_R(M) → Sym_S(S ⊗_R M)` and its morphism of `Proj`s -/

/-- **The canonical graded homomorphism `Sym_R(M) → Sym_S(S ⊗_R M)`**, the inclusion
`x ↦ 1 ⊗ x` into the scalar extension followed by the graded isomorphism. -/
public def symBaseChangeGraded :
    (fun n => SymPow.symmetricPower n R M) →+*ᵍ
      (fun n => SymPow.symmetricPower n S (S ⊗[R] M)) :=
  (symBaseChangeGradedHom R S M).comp
    (Stacks.ProjBaseChange.includeRight (fun n => SymPow.symmetricPower n R M) S)

/-- The containment of irrelevant ideals for
`Stacks.ProjectiveSpaceBaseChange.symBaseChangeGraded`. -/
public theorem irrelevant_le_map_symBaseChangeGraded :
    (fun n => SymPow.symmetricPower n S (S ⊗[R] M))₊ ≤
      (fun n => SymPow.symmetricPower n R M)₊.map (symBaseChangeGraded R S M) :=
  irrelevant_le_map_comp
    (Stacks.ProjBaseChange.irrelevant_le_map (fun n => SymPow.symmetricPower n R M) S)
    (irrelevant_le_map_symBaseChangeGradedHom R S M)

/-- **The morphism of projective spaces induced by a base change of the module**,
`𝐏_S(S ⊗_R M) ⟶ 𝐏_R(M)`. -/
public def map : projectiveSpaceOfModule S (S ⊗[R] M) ⟶ projectiveSpaceOfModule R M :=
  Proj.map (symBaseChangeGraded R S M) (irrelevant_le_map_symBaseChangeGraded R S M)

/-! ### The degree-zero identification -/

/-- **The degree-zero part of the graded isomorphism is the structure map of `S`.** The
degree-zero scalar `s ⊗ₜ 1` of the base-changed grading goes to the image of `s` in
`Sym_S(S ⊗_R M)`. -/
public theorem gradedZeroRingHom_symBaseChangeGradedHom_comp_algebraMap :
    (symBaseChangeGradedHom R S M).gradedZeroRingHom.comp
        (algebraMap S ↥(Stacks.ProjBaseChange.grading
          (fun n => SymPow.symmetricPower n R M) S 0)) =
      algebraMap S ↥(SymPow.symmetricPower 0 S (S ⊗[R] M)) :=
  RingHom.ext fun s => Subtype.ext (by
    change SymPow.symAlgBaseChangeEquiv S M (s ⊗ₜ[R] (1 : SymmetricAlgebra R M)) =
      algebraMap S (SymmetricAlgebra S (S ⊗[R] M)) s
    rw [SymPow.symAlgBaseChangeEquiv_apply, SymPow.symAlgBaseChangeHom_tmul, map_one, mul_one])

/-! ### The cartesian square -/

/-- **The projective space of a module commutes with base change.** For a commutative ring `R`,
an `R`-algebra `S` and an `R`-module `M`, the square formed by
`𝐏_S(S ⊗_R M) ⟶ 𝐏_R(M)` and the two structure morphisms to `Spec S` and `Spec R` is cartesian:
`𝐏_S(S ⊗_R M) = 𝐏_R(M) ×_{Spec R} Spec S`.

This is Stacks tag 01N2 for the graded algebra `Sym_R(M)`, transported along the base-change
comparison of symmetric algebras read as an isomorphism of graded rings. -/
@[ega "II 4.1.3" "special case"]
public theorem isPullback_projectiveSpaceOfModuleToSpec :
    IsPullback (map R S M) (projectiveSpaceOfModuleToSpec S (S ⊗[R] M))
      (projectiveSpaceOfModuleToSpec R M)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have H := Stacks.ProjBaseChange.isPullback_map_of_baseChange
    (fun n => SymPow.symmetricPower n R M) S
    (f := symBaseChangeGraded R S M) (irrelevant_le_map_symBaseChangeGraded R S M)
    (e := symBaseChangeGradedHom R S M) (irrelevant_le_map_symBaseChangeGradedHom R S M)
    (e' := symBaseChangeGradedInv R S M) (irrelevant_le_map_symBaseChangeGradedInv R S M)
    (symBaseChangeGradedInv_comp_hom R S M) (symBaseChangeGradedHom_comp_inv R S M) rfl
  rw [Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    gradedZeroRingHom_symBaseChangeGradedHom_comp_algebraMap] at H
  exact H

/-- **The projective space of a base-changed module is the fibre product.** The identification
`𝐏_S(S ⊗_R M) ≅ 𝐏_R(M) ×_{Spec R} Spec S` carried by
`Stacks.ProjectiveSpaceBaseChange.isPullback_projectiveSpaceOfModuleToSpec`. -/
public def isoPullback :
    projectiveSpaceOfModule S (S ⊗[R] M) ≅
      pullback (projectiveSpaceOfModuleToSpec R M)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (isPullback_projectiveSpaceOfModuleToSpec R S M).isoPullback

/-- The identification `isoPullback` followed by the first projection of the fibre product is
the morphism `map R S M : 𝐏_S(S ⊗_R M) ⟶ 𝐏_R(M)`. -/
@[reassoc]
public theorem isoPullback_hom_fst :
    (isoPullback R S M).hom ≫
        pullback.fst (projectiveSpaceOfModuleToSpec R M)
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      map R S M :=
  (isPullback_projectiveSpaceOfModuleToSpec R S M).isoPullback_hom_fst

/-- The identification `isoPullback` followed by the second projection of the fibre product is
the structure morphism `𝐏_S(S ⊗_R M) ⟶ Spec S`. -/
@[reassoc]
public theorem isoPullback_hom_snd :
    (isoPullback R S M).hom ≫
        pullback.snd (projectiveSpaceOfModuleToSpec R M)
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      projectiveSpaceOfModuleToSpec S (S ⊗[R] M) :=
  (isPullback_projectiveSpaceOfModuleToSpec R S M).isoPullback_hom_snd

end Stacks.ProjectiveSpaceBaseChange

end
