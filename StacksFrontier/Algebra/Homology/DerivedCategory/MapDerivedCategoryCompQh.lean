module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The derived functors of exact functors around an isomorphism of composites

Let `G : C₁ ⥤ C₂`, `H : C₂ ⥤ C₃` and `K : C₁ ⥤ C₃` be exact functors between abelian categories
and let `e : G ⋙ H ≅ K`. The functors they induce on the unbounded derived categories are then
related by an isomorphism `K.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ H.mapDerivedCategory`,
obtained by lifting along the localization `DerivedCategory.Qh` the isomorphism
`Functor.mapHomotopyCategoryCompIso e` of the induced functors on the homotopy categories.

The lift is taken along `Qh` (rather than along `DerivedCategory.Q`) because that is the
localization through which the functors `mapDerivedCategory` are compared with their
homotopy-level counterparts by `Functor.mapDerivedCategoryFactorsh`; the value of the isomorphism
at `Qh X` is therefore computed by those comparisons alone
(`Functor.mapDerivedCategoryCompIsoOfIso_hom_app`).

## Main definitions

* `CategoryTheory.Functor.liftingMapDerivedCategoryCompQh`: the composite of two derived functors
  lifts the composite of the homotopy-level functors along `Qh`.
* `CategoryTheory.Functor.mapDerivedCategoryCompIsoOfIso`: the isomorphism
  `K.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ H.mapDerivedCategory` attached to
  `e : G ⋙ H ≅ K`.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCompIsoOfIso_hom_app` and `_inv_app`: its components
  at an object `Qh X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]

/-- The composite of the derived functors of two exact functors is a lift along `Qh` of the
composite of the two functors on the homotopy categories, through the two comparisons
`mapDerivedCategoryFactorsh`. -/
instance liftingMapDerivedCategoryCompQh (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
      (G.mapDerivedCategory ⋙ H.mapDerivedCategory) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight G.mapDerivedCategoryFactorsh H.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (G.mapHomotopyCategory (ComplexShape.up ℤ))
          H.mapDerivedCategoryFactorsh⟩

variable {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃} {K : C₁ ⥤ C₃}
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]

/-- **The derived functors around an isomorphism of composites of exact functors.** An
isomorphism `e : G ⋙ H ≅ K` of exact functors induces
`K.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ H.mapDerivedCategory`, the lift along `Qh` of
`Functor.mapHomotopyCategoryCompIso e`. -/
def mapDerivedCategoryCompIsoOfIso (e : G ⋙ H ≅ K) :
    K.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
    _ _ _ _
    (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _)

/-- The component of `mapDerivedCategoryCompIsoOfIso` at `Qh X`. -/
theorem mapDerivedCategoryCompIsoOfIso_hom_app (e : G ⋙ H ≅ K)
    (X : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIsoOfIso e).hom.app (DerivedCategory.Qh.obj X) =
      K.mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app X) ≫
        H.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        H.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.inv.app X) := by
  simp [mapDerivedCategoryCompIsoOfIso, Localization.liftNatTrans_app, Localization.Lifting.iso]

/-- The inverse of `mapDerivedCategoryCompIsoOfIso` at `Qh X`. -/
theorem mapDerivedCategoryCompIsoOfIso_inv_app (e : G ⋙ H ≅ K)
    (X : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIsoOfIso e).inv.app (DerivedCategory.Qh.obj X) =
      H.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app X) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app X) ≫
        K.mapDerivedCategoryFactorsh.inv.app X := by
  simp [mapDerivedCategoryCompIsoOfIso, Localization.liftNatTrans_app, Localization.Lifting.iso]

end CategoryTheory.Functor

end
