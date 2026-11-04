module

public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import Mathlib.Algebra.Homology.Additive

/-!
# The Koszul braiding is carried along a comparison of total tensor complexes

Let `A` and `B` be symmetric monoidal preadditive categories with enough coproducts for the
Koszul symmetric monoidal structure of `StacksFrontier/Algebra/Homology/KoszulSymmetric.lean` to
exist on `CochainComplex A ℤ` and `CochainComplex B ℤ`, and let `P : A ⥤ B` be an additive
functor equipped with a degreewise comparison `ε a a' : P(a ⊗ a') ≅ P a ⊗ P a'` which commutes
with the symmetries of `A` and `B`.  Suppose moreover given, for every pair of complexes, a
comparison

`cx K L : P(Tot(K ⊗ L)) ≅ Tot(P K ⊗ P L)`

whose value on the summand of bidegree `(p, q)` is `ε (K^p) (L^q)` there.  Then `cx` commutes
with the Koszul braidings.

This is the content-free half of the statement that a comparison of total tensor complexes is
braided: the Koszul signs on the two sides are `(-1)^(p*q)` on the summand of bidegree
`(p, q)` for both, so they cancel, and what is left is the degreewise hypothesis `hε`.  The
hypotheses `hcx_hom` and `hcx_inv` are exactly what
`CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom` and `_inv` provide for a comparison built
by `CategoryTheory.Functor.mapBifunctorTotalIso`.

## Main results

* `CochainComplex.totalTensorComparison_koszulBraiding`: **a comparison of total tensor
  complexes whose summandwise value is a braided degreewise comparison commutes with the Koszul
  braidings.**

## Implementation notes

The comparison, the degreewise comparison and their summandwise descriptions are explicit
arguments rather than instance data: there is no class saying that a functor carries one total
tensor complex to another, and the concrete comparisons this is applied to are not the
tensorator of a monoidal functor on the nose.

The identity is proved on the inverse of `cx` first — that is the direction in which both sides
are morphisms *out of* `Tot(P K ⊗ P L)`, where `HomologicalComplex.mapBifunctor.hom_ext`
applies — and then transported to `cx` itself.  Writing it the other way round would ask for
extensionality on `P` of a coproduct.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [Preadditive A]
  [MonoidalPreadditive A] [HasZeroObject A]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [SymmetricCategory A]
  {B : Type u} [Category.{v} B] [MonoidalCategory B] [Preadditive B]
  [MonoidalPreadditive B] [HasZeroObject B]
  [∀ (X₁ X₂ : GradedObject ℤ B), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [SymmetricCategory B]

/-- **A comparison of total tensor complexes whose summandwise value is a degreewise comparison
commuting with the symmetries commutes with the Koszul braidings.**

On the summand of bidegree `(p, q)` both sides are the degreewise braiding scaled by the one
Koszul sign `(-1)^(p*q)`, so the signs cancel and the identity is the degreewise hypothesis
`hε` at `(K^p, L^q)`. -/
theorem totalTensorComparison_koszulBraiding (P : A ⥤ B) [P.Additive]
    (ε : ∀ a a' : A, P.obj (a ⊗ a') ≅ P.obj a ⊗ P.obj a')
    (hε : ∀ a a' : A, (ε a a').inv ≫ P.map (β_ a a').hom ≫ (ε a' a).hom =
      (β_ (P.obj a) (P.obj a')).hom)
    (cx : ∀ K L : CochainComplex A ℤ,
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K ⊗ L) ≅
        (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⊗
          (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (hcx_hom : ∀ (K L : CochainComplex A ℤ) (p q n : ℤ) (h : p + q = n),
      P.map (HomologicalComplex.ιTensorObj K L p q n h) ≫ (cx K L).hom.f n =
        (ε (K.X p) (L.X q)).hom ≫ HomologicalComplex.ιTensorObj
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) p q n h)
    (hcx_inv : ∀ (K L : CochainComplex A ℤ) (p q n : ℤ) (h : p + q = n),
      HomologicalComplex.ιTensorObj
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) p q n h ≫ (cx K L).inv.f n =
        (ε (K.X p) (L.X q)).inv ≫ P.map (HomologicalComplex.ιTensorObj K L p q n h))
    (K L : CochainComplex A ℤ) :
    (cx K L).hom ≫ (koszulBraiding
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom =
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map (koszulBraiding K L).hom ≫
        (cx L K).hom := by
  have key : (koszulBraiding
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom =
      (cx K L).inv ≫
        (P.mapHomologicalComplex (ComplexShape.up ℤ)).map (koszulBraiding K L).hom ≫
          (cx L K).hom := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    have hpq : p + q = n := h
    have hqp : q + p = n := by omega
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    rw [ιTensorObj_koszulBraiding _ _ p q n hpq,
      reassoc_of% (hcx_inv K L p q n hpq), ← P.map_comp_assoc,
      ιTensorObj_koszulBraiding K L p q n hpq, Functor.map_units_smul, P.map_comp,
      Linear.units_smul_comp, Category.assoc, hcx_hom L K q p n hqp,
      Linear.comp_units_smul, reassoc_of% (hε (K.X p) (L.X q))]
    rfl
  rw [key, Iso.hom_inv_id_assoc]

end CochainComplex

end

end
