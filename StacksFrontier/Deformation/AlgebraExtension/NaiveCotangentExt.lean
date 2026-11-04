module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPresentationComparison
public import StacksFrontier.Deformation.AlgebraExtension.Restriction
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble

/-!
# The low degree `Ext` groups of `NL_{𝒪/𝒜}` read off on a presentation

Let `α : ℰ ⟶ 𝒪` be a family of generators of `𝒪` over `𝒜` and `NL(α) = (ℐ/ℐ² ⟶ Ω)` its naive
cotangent complex, in degrees `-1` and `0`. For a sheaf of `𝒪`-modules `𝒢`:

* `Ext⁰(NL(α), 𝒢)` is the group of morphisms `θ : Ω ⟶ 𝒢` with `θ ∘ d = 0`: a morphism out of
  `NL(α)` is determined by its restriction to `Ω`, and a morphism out of `Ω` killing `ℐ/ℐ²`
  extends, by the distinguished triangle `ℐ/ℐ² ⟶ Ω ⟶ NL(α) ⟶ (ℐ/ℐ²)[1]` and the vanishing of
  negative `Ext` groups between modules;
* a class in `Ext¹(NL(α), 𝒢)` of a morphism `δ : ℐ/ℐ² ⟶ 𝒢` vanishes exactly when `δ` factors
  through `d`.

Since `NL(α) ⟶ NL_{𝒪/𝒜}` is a quasi-isomorphism ([Stacks Project, Tag 08TY]), a hypothesis
that `φ : ℳ ⟶ 𝒩` induces bijections `Ext^i(NL_{𝒪/𝒜}, ℳ) ⟶ Ext^i(NL_{𝒪/𝒜}, 𝒩)` for
`i = 0, 1` translates into the concrete statements about `Ω` and `ℐ/ℐ²` used in the proof of
[Stacks Project, Tag 0D3P]: injectivity and surjectivity of `θ ↦ φ ∘ θ` on the morphisms
`Ω ⟶ −` killing `ℐ/ℐ²`, and the fact that `δ` factors through `d` as soon as `φ ∘ δ` does.

## Main results

* `Deformation.AlgebraExtension.eq_zero_of_naiveCotangent_injective`,
  `Deformation.AlgebraExtension.exists_comp_eq_of_naiveCotangent_surjective`: degree `0`.
* `Deformation.AlgebraExtension.exists_d_comp_eq_of_naiveCotangent_injective`: degree `1`.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpaceThickening (NaiveCotangentTwoTerm)
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence
  presentationNaiveCotangentComplex naiveCotangentComplex naiveCotangentComplexComparison)

universe t u

namespace Deformation.AlgebraExtension

/-- Bijectivity of post-composition transfers along an isomorphism of sources. -/
theorem injective_postcomp_of_iso {𝒟 : Type*} [Category 𝒟] {X Y M N : 𝒟} (e : X ≅ Y)
    (g : M ⟶ N) (h : Function.Injective (fun ξ : Y ⟶ M => ξ ≫ g)) :
    Function.Injective (fun ξ : X ⟶ M => ξ ≫ g) := fun ξ ξ' hξ => by
  have : e.inv ≫ ξ = e.inv ≫ ξ' := h (by
    show (e.inv ≫ ξ) ≫ g = (e.inv ≫ ξ') ≫ g
    rw [Category.assoc, Category.assoc]
    exact congrArg (e.inv ≫ ·) hξ)
  simpa using congrArg (e.hom ≫ ·) this

/-- Surjectivity of post-composition transfers along an isomorphism of sources. -/
theorem surjective_postcomp_of_iso {𝒟 : Type*} [Category 𝒟] {X Y M N : 𝒟} (e : X ≅ Y)
    (g : M ⟶ N) (h : Function.Surjective (fun ξ : Y ⟶ M => ξ ≫ g)) :
    Function.Surjective (fun ξ : X ⟶ M => ξ ≫ g) := fun ξ' => by
  obtain ⟨ξ, hξ⟩ := h (e.inv ≫ ξ')
  refine ⟨e.hom ≫ ξ, ?_⟩
  show (e.hom ≫ ξ) ≫ g = ξ'
  rw [Category.assoc]
  exact (congrArg (e.hom ≫ ·) hξ).trans (e.hom_inv_id_assoc ξ')

/-! ### Two-term complexes in the derived category -/

section TwoTerm

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasDerivedCategory.{t} 𝒞] {X₀ X₁ : 𝒞}
  (d : X₀ ⟶ X₁)

/-- A morphism from a shifted object of `𝒞` to an object of `𝒞` in the derived category
vanishes: negative `Ext` groups between objects of an abelian category are zero. -/
theorem singleFunctor_shift_hom_eq_zero (X G : 𝒞)
    (g : ((DerivedCategory.singleFunctor 𝒞 0).obj X)⟦(1 : ℤ)⟧ ⟶
      (DerivedCategory.singleFunctor 𝒞 0).obj G) : g = 0 := by
  have : DerivedCategory.TStructure.t.IsLE
      (((DerivedCategory.singleFunctor 𝒞 0).obj X)⟦(1 : ℤ)⟧) (-1) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1)
  exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g (-1) 0 (by decide) inferInstance
    inferInstance

/-- A morphism out of the two-term complex is determined by its restriction to the degree `0`
term. -/
theorem ofDoubleNegOne_incl_cancel {G : 𝒞}
    {ξ ξ' : (NaiveCotangentTwoTerm.ofDoubleNegOne d).obj ⟶
      (DerivedCategory.singleFunctor 𝒞 0).obj G}
    (h : (NaiveCotangentTwoTerm.ofDoubleNegOne d).incl ≫ ξ =
      (NaiveCotangentTwoTerm.ofDoubleNegOne d).incl ≫ ξ') : ξ = ξ' := by
  rw [← sub_eq_zero]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (NaiveCotangentTwoTerm.ofDoubleNegOne d).distinguished
    (ξ - ξ') (by
      show (NaiveCotangentTwoTerm.ofDoubleNegOne d).incl ≫ (ξ - ξ') = 0
      rw [Preadditive.comp_sub, h, sub_self])
  rw [hg, singleFunctor_shift_hom_eq_zero X₀ G g]
  exact comp_zero

/-- A morphism out of the degree `0` term killing the degree `-1` term extends to the two-term
complex. -/
theorem ofDoubleNegOne_exists_incl_comp {G : 𝒞} (θ : X₁ ⟶ G) (hθ : d ≫ θ = 0) :
    ∃ ξ : (NaiveCotangentTwoTerm.ofDoubleNegOne d).obj ⟶
        (DerivedCategory.singleFunctor 𝒞 0).obj G,
      (NaiveCotangentTwoTerm.ofDoubleNegOne d).incl ≫ ξ =
        (DerivedCategory.singleFunctor 𝒞 0).map θ := by
  obtain ⟨ξ, hξ⟩ := Triangle.yoneda_exact₂ _
    (NaiveCotangentTwoTerm.ofDoubleNegOne d).distinguished
    ((DerivedCategory.singleFunctor 𝒞 0).map θ) (by
      show (DerivedCategory.singleFunctor 𝒞 0).map d ≫
        (DerivedCategory.singleFunctor 𝒞 0).map θ = 0
      rw [← Functor.map_comp, hθ, Functor.map_zero])
  exact ⟨ξ, hξ.symm⟩


variable {G G' : 𝒞} (φ : G ⟶ G') {K : DerivedCategory 𝒞}
  (e : (NaiveCotangentTwoTerm.ofDoubleNegOne d).obj ≅ K)
include e

/-- Degree `0` injectivity, on a two-term complex. -/
theorem twoTerm_eq_zero_of_injective
    (h : Function.Injective (fun ξ : K ⟶ (DerivedCategory.singleFunctor 𝒞 0).obj G =>
      ξ ≫ (DerivedCategory.singleFunctor 𝒞 0).map φ))
    (θ : X₁ ⟶ G) (hθ : d ≫ θ = 0) (hφ : θ ≫ φ = 0) : θ = 0 := by
  have h' := injective_postcomp_of_iso e _ h
  obtain ⟨ξ, hξ⟩ := ofDoubleNegOne_exists_incl_comp d θ hθ
  have hz : ξ = 0 := h' (by
    show ξ ≫ _ = 0 ≫ _
    rw [zero_comp]
    refine ofDoubleNegOne_incl_cancel d ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hξ]
    refine ((Functor.map_comp _ _ _).symm.trans ?_).trans comp_zero.symm
    rw [hφ]
    exact Functor.map_zero _ _ _)
  refine (DerivedCategory.singleFunctor 𝒞 0).map_injective (hξ.symm.trans ?_)
  rw [hz, comp_zero]
  exact (Functor.map_zero _ _ _).symm

/-- Degree `0` surjectivity, on a two-term complex. -/
theorem twoTerm_exists_comp_eq_of_surjective
    (h : Function.Surjective (fun ξ : K ⟶ (DerivedCategory.singleFunctor 𝒞 0).obj G =>
      ξ ≫ (DerivedCategory.singleFunctor 𝒞 0).map φ))
    (θ' : X₁ ⟶ G') (hθ' : d ≫ θ' = 0) : ∃ θ : X₁ ⟶ G, d ≫ θ = 0 ∧ θ ≫ φ = θ' := by
  have h' := surjective_postcomp_of_iso e _ h
  obtain ⟨ξ', hξ'⟩ := ofDoubleNegOne_exists_incl_comp d θ' hθ'
  obtain ⟨ξ, hξ⟩ := h' ξ'
  obtain ⟨θ, hθ⟩ : ∃ θ : X₁ ⟶ G, (DerivedCategory.singleFunctor 𝒞 0).map θ =
      (NaiveCotangentTwoTerm.ofDoubleNegOne d).incl ≫ ξ :=
    (DerivedCategory.singleFunctor 𝒞 0).map_surjective _
  refine ⟨θ, (DerivedCategory.singleFunctor 𝒞 0).map_injective ?_,
    (DerivedCategory.singleFunctor 𝒞 0).map_injective ?_⟩
  · refine (Functor.map_comp _ _ _).trans ?_
    rw [hθ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ) (comp_distTriang_mor_zero₁₂ _
      (NaiveCotangentTwoTerm.ofDoubleNegOne d).distinguished)).trans
        (zero_comp.trans (Functor.map_zero (DerivedCategory.singleFunctor 𝒞 0) X₀ G).symm))
  · refine (Functor.map_comp _ _ _).trans ?_
    rw [hθ, ← hξ']
    exact (Category.assoc _ _ _).trans
      (congrArg ((NaiveCotangentTwoTerm.ofDoubleNegOne d).incl ≫ ·) hξ)

/-- Degree `1` injectivity, on a two-term complex. -/
theorem twoTerm_exists_d_comp_eq_of_injective
    (h : Function.Injective (fun ξ : K ⟶ ((DerivedCategory.singleFunctor 𝒞 0).obj G)⟦(1 : ℤ)⟧ =>
      ξ ≫ ((DerivedCategory.singleFunctor 𝒞 0).map φ)⟦(1 : ℤ)⟧'))
    (δ : X₀ ⟶ G) (hδ : ∃ θ' : X₁ ⟶ G', d ≫ θ' = δ ≫ φ) : ∃ θ : X₁ ⟶ G, d ≫ θ = δ := by
  have h' := injective_postcomp_of_iso e _ h
  have hz := ((NaiveCotangentTwoTerm.ofDoubleNegOne d).conormalExtClass_eq_zero_iff _
    (δ ≫ φ)).2 hδ
  refine ((NaiveCotangentTwoTerm.ofDoubleNegOne d).conormalExtClass_eq_zero_iff _ δ).1 (h' ?_)
  show (NaiveCotangentTwoTerm.ofDoubleNegOne d).conormalExtClass _ δ ≫ _ = 0 ≫ _
  rw [zero_comp, ← hz]
  exact (Category.assoc _ _ _).trans (congrArg ((NaiveCotangentTwoTerm.ofDoubleNegOne d).proj ≫ ·)
    (((shiftFunctor (DerivedCategory 𝒞) (1 : ℤ)).map_comp _ _).symm.trans
      (congrArg (shiftFunctor (DerivedCategory 𝒞) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor 𝒞 0).map_comp _ _).symm)))

end TwoTerm

/-! ### Presentations -/

section Presentation

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} (a : A ⟶ O)
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)} (φ : M ⟶ N)
  (E : Cᵒᵖ ⥤ Type u) (α : E ⟶ underlyingPresheaf J O)
  [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]

/-- `NL(α)` as a two-term complex. -/
noncomputable abbrev presentationTwoTerm :=
  NaiveCotangentTwoTerm.ofDoubleNegOne (presentationConormalSequence.{u, u, u, u} J A O a E α).f

/-- The comparison `NL(α) ≅ NL_{𝒪/𝒜}` in the derived category, [Stacks Project, Tag 08TY]. -/
noncomputable def presentationTwoTermIso :
    (presentationTwoTerm a E α).obj ≅
      DerivedCategory.Q.obj (naiveCotangentComplex.{u, u, u, u} J A O a) :=
  haveI : IsIso (DerivedCategory.Q.map
      (naiveCotangentComplexComparison.{u, u, u, u} J A O a E α)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
    (φ := naiveCotangentComplexComparison.{u, u, u, u} J A O a E α)).2
    (Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison_site.{u, u, u, u}
      J A O a E α)
  @asIso _ _ _ _ (DerivedCategory.Q.map
    (naiveCotangentComplexComparison.{u, u, u, u} J A O a E α)) this

variable {a} {E} {α}

/-- **Degree `0`, injectivity.** If `φ` induces an injection on `Ext⁰(NL_{𝒪/𝒜}, −)`, then a
morphism `θ : Ω ⟶ ℳ` killing `ℐ/ℐ²` with `φ ∘ θ = 0` vanishes. -/
theorem eq_zero_of_naiveCotangent_injective
    (h : Function.Injective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj (tensorModule M) =>
      ξ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map (tensorMap φ)))
    (θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule M)
    (hθ : (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ = 0)
    (hφ : θ ≫ tensorMap φ = 0) : θ = 0 :=
  twoTerm_eq_zero_of_injective _ (tensorMap φ) (presentationTwoTermIso a E α) h θ hθ hφ

/-- **Degree `0`, surjectivity.** If `φ` induces a surjection on `Ext⁰(NL_{𝒪/𝒜}, −)`, then every
morphism `θ' : Ω ⟶ 𝒩` killing `ℐ/ℐ²` is `φ ∘ θ` for a morphism `θ : Ω ⟶ ℳ` killing `ℐ/ℐ²`. -/
theorem exists_comp_eq_of_naiveCotangent_surjective
    (h : Function.Surjective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj (tensorModule M) =>
      ξ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map (tensorMap φ)))
    (θ' : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule N)
    (hθ' : (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ' = 0) :
    ∃ θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule M,
      (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ = 0 ∧
        θ ≫ tensorMap φ = θ' :=
  twoTerm_exists_comp_eq_of_surjective _ (tensorMap φ) (presentationTwoTermIso a E α) h θ' hθ'

/-- **Degree `1`, injectivity.** If `φ` induces an injection on `Ext¹(NL_{𝒪/𝒜}, −)`, then a
morphism `δ : ℐ/ℐ² ⟶ ℳ` factors through `d : ℐ/ℐ² ⟶ Ω` as soon as `φ ∘ δ` does. -/
theorem exists_d_comp_eq_of_naiveCotangent_injective
    (h : Function.Injective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj
          (tensorModule M))⟦(1 : ℤ)⟧ =>
      ξ ≫ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map
          (tensorMap φ))⟦(1 : ℤ)⟧'))
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ tensorModule M)
    (hδ : ∃ θ' : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule N,
      (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ' = δ ≫ tensorMap φ) :
    ∃ θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ tensorModule M,
      (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ = δ :=
  twoTerm_exists_d_comp_eq_of_injective _ (tensorMap φ) (presentationTwoTermIso a E α) h δ hδ

end Presentation

end Deformation.AlgebraExtension

end
