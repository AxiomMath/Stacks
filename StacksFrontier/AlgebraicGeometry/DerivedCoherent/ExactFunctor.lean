module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory

/-!
# Exact equivalences and cohomological bounds in the derived category

An exact additive functor `F` between abelian categories induces `D(F) : D(𝒜) ⥤ D(ℬ)`, and the
comparison `Hⁿ ∘ D(F) ≅ F ∘ Hⁿ` of
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` identifies its cohomology. When `F` is
an equivalence that comparison is enough to see that `D(F)` *reflects* upper cohomological
bounds as well as preserving them, so that `D(F)` restricts to the bounded above
subcategories. This file records that, together with the identification of cohomological
boundedness above with being `≤ n` for some `n`.

## Main results

* `CategoryTheory.Functor.isLE_mapDerivedCategory_obj_iff`: for an exact equivalence of abelian
  categories, an object of the derived category of the source is `≤ n` exactly when its image
  is.
* `CategoryTheory.Functor.mapDerivedCategoryOpIso`: the derived functor of an exact functor
  commutes with the derived opposite equivalence.
* `DerivedCategoryB.isBoundedAbove_iff_exists_isLE`: being cohomologically bounded above is
  being `≤ n` for some `n`.

## Implementation notes

The reflection direction is proved from the comparison isomorphism alone: `Hⁱ(D(F) K)` is
isomorphic to `F(Hⁱ K)`, and a functor which is an equivalence is faithful, so it sends a
non-zero identity to a non-zero identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- An exact additive equivalence of abelian categories induces a functor on derived categories
which both preserves and reflects the objects that are `≤ n`; so it restricts to an
equivalence of the bounded above subcategories. -/
lemma isLE_mapDerivedCategory_obj_iff (e : C ≌ D) [e.functor.Additive]
    [PreservesFiniteLimits e.functor] [PreservesFiniteColimits e.functor]
    (K : DerivedCategory C) (n : ℤ) :
    (e.functor.mapDerivedCategory.obj K).IsLE n ↔ K.IsLE n := by
  rw [DerivedCategory.isLE_iff, DerivedCategory.isLE_iff]
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have hz : IsZero (e.functor.obj ((DerivedCategory.homologyFunctor C i).obj K)) :=
      (h i hi).of_iso ((e.functor.mapDerivedCategoryHomologyIso i).app K).symm
    refine (IsZero.iff_id_eq_zero _).2 (e.functor.map_injective ?_)
    simpa using (IsZero.iff_id_eq_zero _).mp hz
  · exact (e.functor.map_isZero (h i hi)).of_iso
      ((e.functor.mapDerivedCategoryHomologyIso i).app K)

section Opposite

universe wop wop'

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

/-- **The derived functor of an exact functor commutes with the derived opposite
equivalence.** Both sides are lifts through the localization `DerivedCategory.opQ` of the same
functor on cochain complexes, so they are chained out of
`CategoryTheory.Functor.mapDerivedCategoryFactors` and
`DerivedCategory.opQCompDerivedOpEquivalenceFunctorIso`. -/
def mapDerivedCategoryOpIso [HasDerivedCategory.{wop} Cᵒᵖ] [HasDerivedCategory.{wop'} Dᵒᵖ]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.op ⋙ (DerivedCategory.derivedOpEquivalence (C := D)).functor ≅
      (DerivedCategory.derivedOpEquivalence (C := C)).functor ⋙ F.op.mapDerivedCategory := by
  let := DerivedCategory.isLocalization_opQ (C := C)
  let h : DerivedCategory.opQ (C := C) ⋙ F.mapDerivedCategory.op ≅
      F.op.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.opQ (C := D) :=
    Functor.isoWhiskerLeft (CochainComplex.opEquivalence C).inverse
      (NatIso.op F.mapDerivedCategoryFactors.symm)
  exact Localization.liftNatIso (DerivedCategory.opQ (C := C))
    (HomologicalComplex.quasiIso Cᵒᵖ (.up ℤ))
    (DerivedCategory.opQ ⋙ (F.mapDerivedCategory.op ⋙
      (DerivedCategory.derivedOpEquivalence (C := D)).functor))
    (DerivedCategory.opQ ⋙ ((DerivedCategory.derivedOpEquivalence (C := C)).functor ⋙
      F.op.mapDerivedCategory)) _ _ <|
    Functor.isoWhiskerRight h (DerivedCategory.derivedOpEquivalence (C := D)).functor ≪≫
    Functor.isoWhiskerLeft (F.op.mapHomologicalComplex (.up ℤ))
      DerivedCategory.opQCompDerivedOpEquivalenceFunctorIso ≪≫
    F.op.mapDerivedCategoryFactors.symm ≪≫
    (Functor.isoWhiskerRight DerivedCategory.opQCompDerivedOpEquivalenceFunctorIso
      F.op.mapDerivedCategory).symm

end Opposite

end CategoryTheory.Functor

namespace DerivedCategoryB

/-- An object of the derived category is cohomologically bounded above exactly when it is `≤ n`
for some `n`. -/
lemma isBoundedAbove_iff_exists_isLE
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DerivedCategory C) : IsBoundedAbove K ↔ ∃ n : ℤ, K.IsLE n := by
  constructor <;> rintro ⟨n, hn⟩
  · exact ⟨n, (DerivedCategory.isLE_iff K n).2 hn⟩
  · exact ⟨n, (DerivedCategory.isLE_iff K n).1 hn⟩

end DerivedCategoryB

end
