module

public import StacksFrontier.Homology.DerivedCategory.HomFromSingleNonzero

/-!
# Shifts of a projective generator detect isomorphisms in the derived category

Let `𝒜` be an abelian category and `P` a projective object of `𝒜` such that every nonzero object
receives a nonzero morphism from `P` (for `𝒜` the modules over a ring, `P` the ring itself). Then
an object `K` of `D(𝒜)` all of whose morphisms from the shifts `P[-j]` vanish is zero, and a
morphism `f : X ⟶ Y` of `D(𝒜)` such that `a ↦ a ≫ f` is bijective on morphisms out of every
`P[-j]` is an isomorphism.

Unlike `DerivedCategory.isZero_of_isGE_of_forall_hom_singleFunctor_eq_zero`, no boundedness is
needed: a morphism `P ⟶ Hʲ(D)` lifts to the cocycles of `D` because `P` is projective.

## Main results

* `DerivedCategory.isZero_of_forall_hom_singleFunctor_projective_eq_zero`
* `DerivedCategory.isIso_of_bijective_comp_singleFunctor_projective`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category Pretriangulated
open HomologicalComplex

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (P : C) [Projective P]

/-- **The shifts of a projective generator detect the zero object of `D(𝒜)`.** -/
theorem isZero_of_forall_hom_singleFunctor_projective_eq_zero
    (hP : ∀ F : C, ¬ IsZero F → ∃ ψ : P ⟶ F, ψ ≠ 0) (K : DerivedCategory C)
    (h : ∀ (j : ℤ) (φ : (singleFunctor C j).obj P ⟶ K), φ = 0) : IsZero K := by
  rw [isZero_iff_forall_isZero_homology]
  intro j
  by_contra hj
  obtain ⟨ψ, hψ⟩ := hP _ hj
  let D := Q.objPreimage K
  let e : Q.obj D ≅ K := Q.objObjPreimageIso K
  let α : (homologyFunctor C j).obj K ≅ D.homology j :=
    (homologyFunctor C j).mapIso e.symm ≪≫ (homologyFunctorFactors C j).app D
  let v : P ⟶ D.cycles j := Projective.factorThru (ψ ≫ α.hom) (D.homologyπ j)
  have hv : v ≫ D.homologyπ j ≠ 0 := by
    rw [Projective.factorThru_comp]
    exact fun hh => hψ ((cancel_mono α.hom).1 (hh.trans zero_comp.symm))
  exact homFromSingleOfCycles_ne_zero v hv
    ((cancel_mono e.hom).1 ((h j (homFromSingleOfCycles v ≫ e.hom)).trans zero_comp.symm))

/-- **The shifts of a projective generator detect isomorphisms in `D(𝒜)`.** If `a ↦ a ≫ f` is a
bijection on morphisms out of every `P[-j]`, then `f` is an isomorphism. -/
theorem isIso_of_bijective_comp_singleFunctor_projective
    (hP : ∀ F : C, ¬ IsZero F → ∃ ψ : P ⟶ F, ψ ≠ 0) {X Y : DerivedCategory C} (f : X ⟶ Y)
    (h : ∀ j : ℤ, Function.Bijective (fun a : (singleFunctor C j).obj P ⟶ X => a ≫ f)) :
    IsIso f := by
  obtain ⟨Z, g, k, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g k
  apply (Triangle.isZero₃_iff_isIso₁ T hT).mp
  -- morphisms `P[-j] ⟶ X⟦1⟧` killed by `f⟦1⟧` vanish
  have hi (j : ℤ) (a : (singleFunctor C j).obj P ⟶ X⟦(1 : ℤ)⟧)
      (ha : a ≫ f⟦(1 : ℤ)⟧' = 0) : a = 0 := by
    let e := ((singleFunctors C).shiftIso (-1) (j + 1) j (by omega)).app P
    let ι := shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by omega)
    let a' : (singleFunctor C (j + 1)).obj P ⟶ X := e.inv ≫ a⟦(-1 : ℤ)⟧' ≫ ι.hom.app X
    have ha' : a' = 0 := by
      apply (h (j + 1)).injective
      change a' ≫ f = 0 ≫ f
      have hnat := ι.hom.naturality f
      simp only [Functor.comp_map, Functor.id_map] at hnat
      simp only [a', Category.assoc, ← hnat, ← Functor.map_comp_assoc, ha, Functor.map_zero,
        zero_comp, comp_zero]
    have h1 : a⟦(-1 : ℤ)⟧' = 0 := by
      have : e.inv ≫ a⟦(-1 : ℤ)⟧' ≫ ι.hom.app X = e.inv ≫ 0 ≫ ι.hom.app X := by
        rwa [zero_comp, comp_zero]
      exact (cancel_mono (ι.hom.app X)).1 ((cancel_epi e.inv).1 this)
    exact (shiftFunctor (DerivedCategory C) (-1 : ℤ)).map_injective
      (h1.trans (Functor.map_zero _ _ _).symm)
  refine isZero_of_forall_hom_singleFunctor_projective_eq_zero P hP Z fun j a => ?_
  have hak : a ≫ k = 0 := hi j (a ≫ k) (by
    rw [Category.assoc]
    exact (congrArg (a ≫ ·) (comp_distTriang_mor_zero₃₁ T hT)).trans comp_zero)
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ T hT a hak
  obtain ⟨c, hc⟩ := (h j).surjective b
  rw [hb, ← hc, Category.assoc]
  exact (c ≫= comp_distTriang_mor_zero₁₂ T hT).trans comp_zero

end DerivedCategory
