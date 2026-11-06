module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans

/-!
# The derived comparison of a composition of exact functors is the degreewise comparison

Let `U₁ : C₀ ⥤ C₁`, `U₂ : C₁ ⥤ C₂` and `U : C₀ ⥤ C₂` be exact additive functors of abelian
categories with derived categories, the first two sources having enough injectives, and let
`c : U₁ ⋙ U₂ ≅ U`. On bounded below derived categories there are two comparisons of
`U₂ ∘ U₁` with `U`: the derived one, `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`
for `c`, and the degreewise one, the comparison of the degreewise actions followed by the
degreewise action of `c`. This file shows that the first is the second, conjugated by the three
identifications `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso` of a right derived
functor of an exact functor with its degreewise action.

## Main definitions

* `Stacks.DerivedFunctor.mapDerivedCategoryPlusCompNatTrans`: the degreewise comparison
  `U₂ ∘ U₁ ⟶ U` on bounded below derived categories.
* `Stacks.DerivedFunctor.mapDerivedCategoryPlusGlue`: its value on an object coming from the
  bounded below homotopy category, written out through the three degreewise factorizations.

## Main results

* `Stacks.DerivedFunctor.mapDerivedCategoryPlusGlue_fac`: on an object coming from the bounded
  below homotopy category, the derived comparison conjugated by the three identifications is the
  degreewise comparison written out.
* `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_compNatTrans`: **the same statement on
  every object of the bounded below derived category**, with the degreewise comparison named.

## Implementation notes

Both sides of the main result are natural transformations between functors out of the bounded
below derived category, so by `CategoryTheory.Localization.natTrans_ext` it suffices to check
them on an object coming from the bounded below homotopy category. There the right derived
functors are pinned down by their units, by
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac` and
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_hom_app_Qh`, and the degreewise comparison
is the composite of the three factorizations through the bounded below homotopy category.

This generalizes `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_comp_hom_app`, which is
the case `U = U₁ ⋙ U₂` and `c` the identity.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₀ v₁ v₂ u₀ u₁ u₂

namespace Stacks.DerivedFunctor

section Transfer

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The inclusion of the bounded below subcategory carries the bounded below factorization of
the degreewise action through the homotopy category to the unbounded one. -/
theorem ι_map_mapDerivedCategoryPlusFactorsh_hom_app (N : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactorsh.hom.app N) =
      F.mapDerivedCategoryFactorsh.hom.app N.obj := rfl

/-- The inverse half of `ι_map_mapDerivedCategoryPlusFactorsh_hom_app`. -/
theorem ι_map_mapDerivedCategoryPlusFactorsh_inv_app (N : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactorsh.inv.app N) =
      F.mapDerivedCategoryFactorsh.inv.app N.obj := rfl

end Transfer

section Glue

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The degreewise comparison `U₂ ∘ U₁ ⟶ U` on bounded below derived categories**: the
comparison of the degreewise actions, followed by the degreewise action of `c`. Nothing about
right derivation enters. -/
def mapDerivedCategoryPlusCompNatTrans :
    U₁.mapDerivedCategoryPlus ⋙ U₂.mapDerivedCategoryPlus ⟶ U.mapDerivedCategoryPlus :=
  (mapDerivedCategoryPlusCompIso U₁ U₂).hom ≫ mapDerivedCategoryPlusNatTrans c.hom

/-- **The degreewise comparison `U₂ ∘ U₁ ⟶ U` on bounded below derived categories**, on an
object coming from the bounded below homotopy category: the two degreewise factorizations, the
degreewise comparison `c` on bounded below homotopy categories, and the third factorization
backwards. Nothing about right derivation enters. -/
def mapDerivedCategoryPlusGlue (N : HomotopyCategory.Plus C₀) :
    U₂.mapDerivedCategoryPlus.obj
        (U₁.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj N)) ⟶
      U.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj N) :=
  U₂.mapDerivedCategoryPlus.map (U₁.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
    U₂.mapDerivedCategoryPlusFactorsh.hom.app (U₁.mapHomotopyCategoryPlus.obj N) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso c).hom.app N) ≫
        U.mapDerivedCategoryPlusFactorsh.inv.app N

omit [HasDerivedCategory C₁] in
/-- The degreewise action of `c`, on an object coming from the bounded below homotopy category:
the two factorizations of the degreewise actions of `U₁ ⋙ U₂` and of `U`, with `c` applied
degreewise in between. -/
theorem Qh_map_mapHomotopyCategoryPlusCompIso_hom_app_comp (N : HomotopyCategory.Plus C₀) :
    DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso c).hom.app N) ≫
        U.mapDerivedCategoryPlusFactorsh.inv.app N =
      (U₁ ⋙ U₂).mapDerivedCategoryPlusFactorsh.inv.app N ≫
        (mapDerivedCategoryPlusNatTrans c.hom).app (DerivedCategory.Plus.Qh.obj N) :=
  DerivedCategory.Plus.ι.map_injective (Qh_map_comp_mapDerivedCategoryFactorsh_inv_app c.hom N.obj)

/-- Replacing the last two legs of a four-fold composite by an equal two-fold composite, and
reassociating. Stated on variables because at the types at hand the composites are not
type-correct at the transparency `rw` reassociates with. -/
private theorem glue_rearrange {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ o₆ : E}
    {a : o₁ ⟶ o₂} {b : o₂ ⟶ o₃} {p : o₃ ⟶ o₄} {q : o₄ ⟶ o₆} {r : o₃ ⟶ o₅} {t : o₅ ⟶ o₆}
    (h : p ≫ q = r ≫ t) : a ≫ b ≫ p ≫ q = (a ≫ b ≫ r) ≫ t := by
  rw [h]
  simp

/-- The degreewise comparison written out is the degreewise comparison named. -/
theorem mapDerivedCategoryPlusGlue_eq (N : HomotopyCategory.Plus C₀) :
    mapDerivedCategoryPlusGlue U₁ U₂ U c N =
      (mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c).app
        (DerivedCategory.Plus.Qh.obj N) := by
  rw [mapDerivedCategoryPlusGlue, mapDerivedCategoryPlusCompNatTrans, NatTrans.comp_app,
    mapDerivedCategoryPlusCompIso_hom_app_Qh]
  exact glue_rearrange
    (Qh_map_mapHomotopyCategoryPlusCompIso_hom_app_comp U₁ U₂ U c N)

end Glue

section Exact

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [EnoughInjectives C₀] [EnoughInjectives C₁]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The derived comparison `RU₁ ⋙ RU₂ ≅ RU` is the degreewise comparison**, conjugated by the
three identifications of a right derived functor with the degreewise action. Both are
determined on an object coming from the bounded below homotopy category, the derived one by
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac`, and there the two agree. -/
theorem mapDerivedCategoryPlusGlue_fac (N : HomotopyCategory.Plus C₀) :
    (exactMapDerivedCategoryPlusIso U₂).hom.app
          (U₁.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj N)) ≫
        U₂.rightDerivedFunctorPlus.map
            ((exactMapDerivedCategoryPlusIso U₁).hom.app
              (DerivedCategory.Plus.Qh.obj N)) ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom.app
            (DerivedCategory.Plus.Qh.obj N) =
      mapDerivedCategoryPlusGlue U₁ U₂ U c N ≫
        (exactMapDerivedCategoryPlusIso U).hom.app (DerivedCategory.Plus.Qh.obj N) := by
  have hΦ₂ : (exactMapDerivedCategoryPlusIso U₂).hom.app
        (DerivedCategory.Plus.Qh.obj (U₁.mapHomotopyCategoryPlus.obj N)) =
      U₂.mapDerivedCategoryPlusFactorsh.hom.app (U₁.mapHomotopyCategoryPlus.obj N) ≫
        U₂.rightDerivedFunctorPlusUnith.app (U₁.mapHomotopyCategoryPlus.obj N) :=
    exactMapDerivedCategoryPlusIso_hom_app_Qh U₂ (U₁.mapHomotopyCategoryPlus.obj N)
  have hΦ₁ : (exactMapDerivedCategoryPlusIso U₁).hom.app (DerivedCategory.Plus.Qh.obj N) =
      U₁.mapDerivedCategoryPlusFactorsh.hom.app N ≫ U₁.rightDerivedFunctorPlusUnith.app N :=
    exactMapDerivedCategoryPlusIso_hom_app_Qh U₁ N
  have hΦU : (exactMapDerivedCategoryPlusIso U).hom.app (DerivedCategory.Plus.Qh.obj N) =
      U.mapDerivedCategoryPlusFactorsh.hom.app N ≫ U.rightDerivedFunctorPlusUnith.app N :=
    exactMapDerivedCategoryPlusIso_hom_app_Qh U N
  rw [mapDerivedCategoryPlusGlue, hΦU, hΦ₁, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.rightDerivedFunctorPlusCompIsoOfExact_fac U₁ U₂ U c N, reassoc_of% hΦ₂.symm,
    reassoc_of% ((exactMapDerivedCategoryPlusIso U₂).hom.naturality
      (U₁.mapDerivedCategoryPlusFactorsh.hom.app N))]

/-- **The derived comparison `RU₁ ⋙ RU₂ ≅ RU` is the degreewise comparison**, on every object of
the bounded below derived category. -/
theorem exactMapDerivedCategoryPlusIso_compNatTrans (K : DerivedCategory.Plus C₀) :
    (exactMapDerivedCategoryPlusIso U₂).hom.app (U₁.mapDerivedCategoryPlus.obj K) ≫
        U₂.rightDerivedFunctorPlus.map ((exactMapDerivedCategoryPlusIso U₁).hom.app K) ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom.app K =
      (mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c).app K ≫
        (exactMapDerivedCategoryPlusIso U).hom.app K := by
  have key : Functor.whiskerLeft U₁.mapDerivedCategoryPlus
          (exactMapDerivedCategoryPlusIso U₂).hom ≫
        Functor.whiskerRight (exactMapDerivedCategoryPlusIso U₁).hom
            U₂.rightDerivedFunctorPlus ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom =
      mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c ≫
        (exactMapDerivedCategoryPlusIso U).hom := by
    refine Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₀) (fun N => ?_)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← mapDerivedCategoryPlusGlue_eq]
    exact mapDerivedCategoryPlusGlue_fac U₁ U₂ U c N
  exact NatTrans.congr_app key K

end Exact

end Stacks.DerivedFunctor

end
