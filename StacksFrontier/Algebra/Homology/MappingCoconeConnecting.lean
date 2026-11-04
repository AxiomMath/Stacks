module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The connecting morphism of the triangle of a mapping cocone

For a morphism `φ : K ⟶ L` of cochain complexes in an abelian category, the triangle

`C(φ)[-1] ⟶ K ⟶ L ⟶ C(φ)[-1][1]`

of the mapping cocone has a connecting morphism `Hⁿ⁰(L) ⟶ Hⁿ¹(C(φ)[-1])` on cohomology, namely
`CochainComplex.homologyδOfTriangle`, which is the morphism of the long exact sequence of the
image of that triangle in the derived category.  This file identifies it with
`CochainComplex.coneHomologyConnecting`, the connecting morphism built from the inclusion
`mappingCone.inr φ` and the identification `Hⁿ¹(C(φ)[-1]) ≅ Hⁿ⁰(C(φ))`, which is the one the
six-term exact sequence of Stacks 0E1Y is written over.

## Main results

* `CategoryTheory.Functor.shiftMap_shiftFunctorCompIsoId_inv_app`: for a functor with a shift
  sequence indexed by `ℤ`, the `shiftMap` of the canonical morphism `X ⟶ (X[-1])[1]` is the
  inverse of the shift comparison isomorphism of the sequence.
* `CochainComplex.homologyδOfTriangle_mappingCocone_triangle`: **the connecting morphism of the
  triangle of the mapping cocone is `coneHomologyConnecting`.**

## Implementation notes

The third morphism of `CochainComplex.mappingCocone.triangle φ` is the inclusion
`mappingCone.inr φ : L ⟶ C(φ)` followed by the canonical morphism
`C(φ) ⟶ (C(φ)[-1])[1]`, so the computation splits into the functoriality of `shiftMap` in its
first argument and the shift bookkeeping of the second factor, which is the abstract lemma
above.  That lemma is `CategoryTheory.Functor.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero`
together with the coherence `shift_shiftFunctorCompIsoId_inv_app`, which makes the right-hand
side the image of an identity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory.Functor

variable {D : Type*} [Category* D] {A : Type*} [Category* A]
  [HasShift D ℤ] (F : D ⥤ A) [F.ShiftSequence ℤ]

/-- For a functor equipped with a shift sequence indexed by `ℤ`, the `shiftMap` in degrees
`a ⟶ a'` with `1 + a = a'` of the canonical morphism `X ⟶ (X[-1])[1]` is the inverse of the
comparison isomorphism `F.shiftIso (-1) a' a`. -/
theorem shiftMap_shiftFunctorCompIsoId_inv_app (X : D) (a a' : ℤ) (ha' : 1 + a = a') :
    F.shiftMap ((shiftFunctorCompIsoId D (-1) 1 (by omega)).inv.app X) a a' ha' =
      (F.shiftIso (-1) a' a (by omega)).inv.app X := by
  have key := F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero
    ((shiftFunctorCompIsoId D (-1) 1 (by omega : (-1 : ℤ) + 1 = 0)).inv.app X)
    (-1 : ℤ) (by omega) a a' ha'
  rw [shift_shiftFunctorCompIsoId_inv_app (-1 : ℤ) 1 (by omega) X, Iso.inv_hom_id_app] at key
  simp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.map_id] at key
  rw [← cancel_epi ((F.shiftIso (-1) a' a (by omega)).hom.app X), key, Iso.hom_inv_id_app]
  rfl

end CategoryTheory.Functor

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {K L : CochainComplex C ℤ}

omit [HasDerivedCategory C] in
/-- **The connecting morphism of the triangle of a mapping cocone.**  For a morphism
`φ : K ⟶ L` of cochain complexes, the connecting morphism `Hⁿ⁰(L) ⟶ Hⁿ¹(C(φ)[-1])` of the
triangle `C(φ)[-1] ⟶ K ⟶ L ⟶ C(φ)[-1][1]` is `CochainComplex.coneHomologyConnecting`, the map
induced by the inclusion `mappingCone.inr φ` read through the identification
`Hⁿ¹(C(φ)[-1]) ≅ Hⁿ⁰(C(φ))`. -/
theorem homologyδOfTriangle_mappingCocone_triangle (φ : K ⟶ L) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    homologyδOfTriangle (mappingCocone.triangle φ) n₀ n₁ h =
      coneHomologyConnecting φ n₀ n₁ (by omega) := by
  have key : HomologicalComplex.homologyMap
        ((shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).inv.app
          (mappingCone φ)) n₀ ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 n₀ n₁
        (by omega)).hom.app (mappingCocone φ) =
      (shiftedMappingConeHomologyIso φ n₁ n₀ (by omega)).inv :=
    Functor.shiftMap_shiftFunctorCompIsoId_inv_app
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0) (mappingCone φ) n₀ n₁ (by omega)
  have h1 : HomologicalComplex.homologyMap (mappingCocone.triangle φ).mor₃ n₀ =
      HomologicalComplex.homologyMap (mappingCone.inr φ) n₀ ≫
        HomologicalComplex.homologyMap
          ((shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).inv.app
            (mappingCone φ)) n₀ :=
    HomologicalComplex.homologyMap_comp _ _ n₀
  exact (congrArg (fun k => k ≫ ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ)
        0).shiftIso 1 n₀ n₁ (by omega)).hom.app (mappingCocone φ)) h1).trans
    ((Category.assoc _ _ _).trans (congrArg (fun k =>
      HomologicalComplex.homologyMap (mappingCone.inr φ) n₀ ≫ k) key))

end CochainComplex

end
