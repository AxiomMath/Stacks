module

public import
    StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.CategoryTheory.Localization.InducedNatTrans

/-!
# The comparisons of degreewise derived functors are induced degreewise

An exact functor `F` of abelian categories induces `F.mapDerivedCategory` on unbounded derived
categories, factoring through the localization `DerivedCategory.Q` along
`CategoryTheory.Functor.mapDerivedCategoryFactors`. This file records that the comparisons
`CategoryTheory.Functor.mapDerivedCategoryCongr` and
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso` attached to isomorphisms of exact functors
are induced, in the sense of `CategoryTheory.NatTrans.IsInducedBy`, by the corresponding
comparisons of the functors on cochain complexes.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCongr_isInducedBy`
* `CategoryTheory.Functor.mapDerivedCategoryCompIso_isInducedBy`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- The comparison of derived functors attached to an isomorphism of exact functors is induced
by its action on cochain complexes. -/
theorem mapDerivedCategoryCongr_isInducedBy
    {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.IsInducedBy F.mapDerivedCategoryFactors G.mapDerivedCategoryFactors
      (Functor.mapDerivedCategoryCongr e).hom
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)) := fun K => by
  simp only [Functor.mapDerivedCategoryCongr, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Category.assoc]
  simp [Localization.Lifting.iso]
  rfl

/-- The comparison `F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`
attached to `e : F ⋙ G ≅ H` is induced by the comparison of the functors on cochain
complexes. -/
theorem mapDerivedCategoryCompIso_isInducedBy
    {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {H : C₁ ⥤ C₃} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) :
    NatTrans.IsInducedBy
      (Functor.compFactorization F.mapDerivedCategoryFactors G.mapDerivedCategoryFactors)
      H.mapDerivedCategoryFactors (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom := fun K => by
  rw [mapDerivedCategoryCompIso_hom_app_Q, Functor.compFactorization_hom_app]
  simp

end CategoryTheory.Functor
