module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksCore.Tactic.StacksAttribute

/-!
# An exact functor induces a right t-exact functor on derived categories

Let `F : C₁ ⥤ C₂` be an exact functor between abelian categories. Mathlib's
`CategoryTheory.Functor.mapDerivedCategory` is the induced triangulated functor
`D(C₁) ⥤ D(C₂)`. This file records that it carries `D^{≤ n}(C₁)` into `D^{≤ n}(C₂)` for the
canonical t-structures, provided `F` is in addition faithful.

The proof is the usual one. An object of `D^{≤ n}(C₁)` is represented by a complex whose terms
vanish above `n`, by `CategoryDerived.exists_iso_Q_obj_of_isLE`; applying `F` termwise leaves
the terms above `n` zero, which is Mathlib's
`CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff`, and
`CategoryTheory.Functor.mapDerivedCategoryFactors` identifies the image of the representative
with the image of the object.

Faithfulness is used only through that `iff`, whose right-to-left direction is all that is
needed; it holds for the two functors this is applied to, the two directions of an equivalence
of abelian categories.

## Main results

* `CategoryTheory.Functor.isLE_mapDerivedCategory`: **an exact faithful functor's induced
  functor on derived categories preserves boundedness above**, with the same bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]

/-- **An exact faithful functor between abelian categories induces a right t-exact functor on
the derived categories**: if `X` lies in `D^{≤ n}(C₁)` then `F.mapDerivedCategory.obj X` lies in
`D^{≤ n}(C₂)`.

`X` is represented by a complex `K` whose terms vanish above `n`; applying `F` termwise leaves
them zero, and `F.mapDerivedCategoryFactors` identifies the image of `K` with the image of
`X`. -/
theorem isLE_mapDerivedCategory (X : DerivedCategory C₁) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X n
  have hmap : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
    rw [CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff]
    exact hK
  have e₂ : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      F.mapDerivedCategory.obj X :=
    (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e.symm
  have := hmap
  exact DerivedCategory.TStructure.t.isLE_of_iso e₂ n

end CategoryTheory.Functor

end
