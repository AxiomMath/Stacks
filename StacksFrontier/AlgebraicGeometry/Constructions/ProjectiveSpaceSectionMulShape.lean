module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionFiniteFamily
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwist

/-!
# Recognising multiplication by a global section of `𝒪(1)` after twisting

Let `s` be a global section of `𝒪(1)` on `ℙⁿ_S`. An arrow `A ⟶ Z` of modules satisfies
`IsSectionMul` if it is multiplication by `s` followed by some isomorphism `A ⊗ 𝒪(1) ≅ Z`. This
property is closed under pre- and post-composition with isomorphisms and under whiskering, and it
holds of `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`. A short
exact sequence whose first arrow has the property, as in the twisted sequences of
[Stacks, Tag 08A0] and [Stacks, Tag 0EGK], can be rewritten with `twistSectionMul` as its first
arrow.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape.IsSectionMul`: the arrow is
  multiplication by `s` followed by an isomorphism.

## Main results

* `…IsSectionMul.iso_comp`, `…IsSectionMul.comp_iso` and `…IsSectionMul.whiskerRight`: the three
  closure properties.
* `…isSectionMul_twistSectionMul` and `…isSectionMul_twistSectionMulNegOne`: the two spellings of
  multiplication by `s` have the property.
* `…exists_shortExact_twistSectionMul_of_objIso`: a short exact sequence whose first arrow has
  the property, transported along isomorphisms of its three objects, can be written with
  `twistSectionMul` itself as its first arrow.

## Implementation notes

The monoidal structure is `…ProjectiveSpaceSectionFiniteFamily.tensorMonoidal`, the one
`twistSectionMul` is built from, and the braiding is
`Stacks.SheafOfModules.sheafTensorSymmetric` at the same spelling; `tensorMonoidal`'s tensor
product is `Stacks.RelativeVeryAmple.tensorModules`, so `ℱ ⊗ 𝒪(d)` is
`AlgebraicGeometry.projectiveTwist` and `(tensorRightModules X B).map` is `· ▷ B`, both by
`rfl`.

In `isSectionMul_twistSectionMulNegOne` the bound isomorphism is the assembled
`…ProjectiveSpaceSectionMultiplication.twistNegOneTensorIso`. Composing `twistZeroIsoUnit` onto
`ρ_` instead would ask for `Stacks.Ample.unitModule` to be the monoidal unit, which sends the
elaborator through the sheafification of the tensor unit.

## References

* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily.tensorMonoidal

variable (n : ℕ) (S : Scheme.{u})

/-- The symmetric monoidal structure on modules over `ℙⁿ_S`, extending
`…ProjectiveSpaceSectionFiniteFamily.tensorMonoidal`. -/
@[instance_reducible]
noncomputable def tensorSymmetric :
    SymmetricCategory ((projectiveSpaceOver n S).Modules) :=
  Stacks.SheafOfModules.sheafTensorSymmetric (projectiveSpaceOver n S).presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n S))

attribute [local instance] tensorSymmetric

/-- Multiplication of a module `ℳ` by a global section `s` of `𝒪(1)`, as the arrow
`ℳ ≅ ℳ ⊗ 𝒪 ⟶ ℳ ⊗ 𝒪(1)`. -/
def mulSection (M : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections) :
    M ⟶ M ⊗ twistOver n S 1 :=
  (ρ_ M).inv ≫ M ◁ unitSectionHom n S s

/-- The isomorphism `(ℳ ⊗ 𝒪(1)) ⊗ B ≅ (ℳ ⊗ B) ⊗ 𝒪(1)` built from the associator and the
braiding. -/
def swapRight (M B : (projectiveSpaceOver n S).Modules) :
    (M ⊗ twistOver n S 1) ⊗ B ≅ (M ⊗ B) ⊗ twistOver n S 1 :=
  α_ M (twistOver n S 1) B ≪≫ whiskerLeftIso M (β_ (twistOver n S 1) B) ≪≫
    (α_ M B (twistOver n S 1)).symm

/-- Multiplying `ℳ` by `s` and then whiskering by `B`, followed by `swapRight`, is multiplying
`ℳ ⊗ B` by `s`. -/
theorem mulSection_whiskerRight (M B : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    mulSection n S M s ▷ B ≫ (swapRight n S M B).hom = mulSection n S (M ⊗ B) s := by
  rw [mulSection, mulSection, swapRight, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, comp_whiskerRight]
  rw [Category.assoc, associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_left, braiding_tensorUnit_left,
    whiskerLeft_comp, whiskerLeft_comp, Category.assoc, Category.assoc,
    associator_inv_naturality_right]
  have h : (ρ_ M).inv ▷ B ≫ (α_ M (𝟙_ (projectiveSpaceOver n S).Modules) B).hom ≫
      M ◁ (λ_ B).hom ≫ M ◁ (ρ_ B).inv ≫
        (α_ M B (𝟙_ (projectiveSpaceOver n S).Modules)).inv = (ρ_ (M ⊗ B)).inv := by
    monoidal
  rw [reassoc_of% h]

/-- The arrow `a : A ⟶ Z` is multiplication by the global section `s` of `𝒪(1)` followed by some
isomorphism `A ⊗ 𝒪(1) ≅ Z`. -/
def IsSectionMul {A Z : (projectiveSpaceOver n S).Modules} (s : (twistOver n S 1).sections)
    (a : A ⟶ Z) : Prop :=
  ∃ e : A ⊗ twistOver n S 1 ≅ Z, a = mulSection n S A s ≫ e.hom

variable {n S}

/-- Postcomposing with an isomorphism preserves the property. -/
theorem IsSectionMul.comp_iso {A Z Z' : (projectiveSpaceOver n S).Modules}
    {s : (twistOver n S 1).sections} {a : A ⟶ Z} (h : IsSectionMul n S s a) (e : Z ≅ Z') :
    IsSectionMul n S s (a ≫ e.hom) := by
  obtain ⟨f, rfl⟩ := h
  exact ⟨f ≪≫ e, by simp⟩

/-- Precomposing with an isomorphism preserves the property. -/
theorem IsSectionMul.iso_comp {A A' Z : (projectiveSpaceOver n S).Modules}
    {s : (twistOver n S 1).sections} {a : A ⟶ Z} (h : IsSectionMul n S s a) (e : A' ≅ A) :
    IsSectionMul n S s (e.hom ≫ a) := by
  obtain ⟨f, rfl⟩ := h
  refine ⟨whiskerRightIso e (twistOver n S 1) ≪≫ f, ?_⟩
  rw [mulSection, mulSection, Iso.trans_hom, whiskerRightIso_hom]
  simp only [Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]

/-- Whiskering on the right preserves the property. -/
theorem IsSectionMul.whiskerRight {A Z : (projectiveSpaceOver n S).Modules}
    {s : (twistOver n S 1).sections} {a : A ⟶ Z} (h : IsSectionMul n S s a)
    (B : (projectiveSpaceOver n S).Modules) :
    IsSectionMul n S s (a ▷ B) := by
  obtain ⟨f, rfl⟩ := h
  refine ⟨(swapRight n S A B).symm ≪≫ whiskerRightIso f B, ?_⟩
  rw [comp_whiskerRight, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    ← mulSection_whiskerRight n S A B s, Category.assoc, Iso.hom_inv_id_assoc]

variable (n S)

/-- `twistSectionMul` is multiplication by `s` followed by the regrouping of the twists. -/
theorem isSectionMul_twistSectionMul (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    IsSectionMul n S s (twistSectionMul n S F s d) :=
  ⟨α_ F (twistOver n S d) (twistOver n S 1) ≪≫
      whiskerLeftIso F (twistOverMulIso n S d 1), by
    rw [twistSectionMul_eq_monoidal, mulSection, Iso.trans_hom, whiskerLeftIso_hom]
    simp only [Category.assoc]
    rfl⟩

/-- `twistSectionMulNegOne` is multiplication by `s` followed by an isomorphism: the regrouping
of the twists and the trivialisation of `𝒪(-1 + 1)`. -/
theorem isSectionMul_twistSectionMulNegOne (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    IsSectionMul n S s (twistSectionMulNegOne n S F s) :=
  ⟨twistNegOneTensorIso n S F, by
    rw [twistSectionMulNegOne_eq_comp, mulSection, ← tensorRightOfUnitHom_eq_whiskerLeft]
    rfl⟩

/-- Let `C` be a short exact sequence whose first arrow is multiplication by `s` followed by an
isomorphism, with isomorphisms of its three objects onto `A₁`, `A₂`, `A₃`, and let `u` identify
`ℱ ⊗ 𝒪(d)` with `A₁`. Then there is an arrow `b : ℱ ⊗ 𝒪(d + 1) ⟶ A₃` such that
`twistSectionMul` followed by `b` is a short exact sequence. -/
theorem exists_shortExact_twistSectionMul_of_objIso
    (F : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections) (d : ℤ)
    {C : ShortComplex ((projectiveSpaceOver n S).Modules)} (hC : C.ShortExact)
    (hf : IsSectionMul n S s C.f)
    {A₁ A₂ A₃ : (projectiveSpaceOver n S).Modules}
    (e₁ : C.X₁ ≅ A₁) (e₂ : C.X₂ ≅ A₂) (e₃ : C.X₃ ≅ A₃)
    (u : tensorModules (projectiveSpaceOver n S) F (twistOver n S d) ≅ A₁) :
    ∃ (b : tensorModules (projectiveSpaceOver n S) F (twistOver n S (d + 1)) ⟶ A₃)
      (w : twistSectionMul n S F s d ≫ b = 0),
      (ShortComplex.mk (twistSectionMul n S F s d) b w).ShortExact := by
  set a : A₁ ⟶ A₂ := e₁.inv ≫ C.f ≫ e₂.hom with ha
  set b₀ : A₂ ⟶ A₃ := e₂.inv ≫ C.g ≫ e₃.hom with hb₀
  have hw : a ≫ b₀ = 0 := by
    rw [ha, hb₀]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc C.f, C.zero, Limits.zero_comp, Limits.comp_zero]
  have hSE : (ShortComplex.mk a b₀ hw).ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ (by simp [ha]) (by simp [hb₀])) hC
  have hmul : IsSectionMul n S s (u.hom ≫ a) :=
    (((hf.comp_iso e₂).iso_comp e₁.symm).iso_comp u)
  obtain ⟨g, hg⟩ := hmul
  obtain ⟨g', hg'⟩ := isSectionMul_twistSectionMul n S F s d
  set ψ : tensorModules (projectiveSpaceOver n S) F (twistOver n S (d + 1)) ≅ A₂ :=
    g'.symm ≪≫ g with hψ
  have key : u.hom ≫ a = twistSectionMul n S F s d ≫ ψ.hom := by
    rw [hg', hψ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, hg]
  have comm : a ≫ ψ.inv = u.inv ≫ twistSectionMul n S F s d := by
    rw [Iso.comp_inv_eq, Category.assoc, ← key, Iso.inv_hom_id_assoc]
  refine ⟨ψ.hom ≫ b₀, ?_, ?_⟩
  · rw [← Category.assoc, ← key, Category.assoc, hw, Limits.comp_zero]
  · exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk u.symm ψ.symm (Iso.refl A₃) comm.symm (by simp)) hSE

end Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape

end
