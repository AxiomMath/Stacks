module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactMapDerivedPlusIsoApp
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition

/-!
# The identification of a right derived functor with the degreewise action is compatible with
composition

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be exact additive functors of abelian categories with derived
categories, the first two with enough injectives. For an exact functor the derived-functor unit
is invertible, so `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso` identifies the total
right derived functor with the degreewise action on the bounded below derived category. This
file shows that this identification is compatible with composing `F` and `G`: the comparison
`RF ⋙ RG ≅ R(G ∘ F)` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact` corresponds, under the
identification, to the comparison `F ⋙ G ≅ G ∘ F` of the degreewise actions,
`Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso`.

## Main results

* `Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso_hom_app_Qh`: the comparison of the
  degreewise actions on bounded below derived categories, on the image of the localization of
  the bounded below homotopy category.
* `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_comp_hom_app`: **the compatibility of
  the identification with composition**, on every object of the bounded below derived category.

## Implementation notes

Both sides of the compatibility are natural transformations between functors out of the bounded
below derived category, so by `CategoryTheory.Localization.natTrans_ext` it suffices to check
them on an object coming from the bounded below homotopy category. There the right derived
functors are pinned down by their units: the comparison of the derived functors is computed by
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac` and each identification by
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_hom_app_Qh`, which together reduce the
statement to the comparison of the degreewise actions. That comparison is defined on the
unbounded derived category as a lift along the localization of the category of complexes, so
reading it on the image of the localization of the homotopy category is
`Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Qh`; the bounded below statement is
the unbounded one read through the fully faithful inclusion.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.DerivedFunctor

section Degreewise

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The comparison of the degreewise actions on bounded below derived categories, on the
image of the localization of the bounded below homotopy category.** It is the two
factorizations of the degreewise actions through the bounded below homotopy category, followed
by the inverse of the factorization for the composite. -/
theorem mapDerivedCategoryPlusCompIso_hom_app_Qh (N : HomotopyCategory.Plus A) :
    (mapDerivedCategoryPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj N) =
      G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj N) ≫
          (F ⋙ G).mapDerivedCategoryPlusFactorsh.inv.app N := by
  apply DerivedCategory.Plus.ι.map_injective
  refine Eq.trans (ι_map_mapDerivedCategoryPlusCompIso_hom_app F G
    (DerivedCategory.Plus.Qh.obj N)) ?_
  refine Eq.trans (mapDerivedCategoryCompIso_hom_app_Qh F G N.obj) ?_
  rfl

omit [HasDerivedCategory B] in
/-- The degreewise comparison for the identity isomorphism `F ⋙ G ≅ F ⋙ G` on bounded below
homotopy categories does not contribute to the factorization for the composite. -/
theorem Qh_map_mapHomotopyCategoryPlusCompIso_refl_hom_comp (N : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app N) ≫
        (F ⋙ G).mapDerivedCategoryPlusFactorsh.inv.app N =
      (F ⋙ G).mapDerivedCategoryPlusFactorsh.inv.app N :=
  (congrArg (fun t => t ≫ (F ⋙ G).mapDerivedCategoryPlusFactorsh.inv.app N)
      ((congrArg (fun f => DerivedCategory.Plus.Qh.map f)
        (show (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app N =
          𝟙 ((F ⋙ G).mapHomotopyCategoryPlus.obj N) from rfl)).trans
        (DerivedCategory.Plus.Qh.map_id _))).trans
    (Category.id_comp _)

end Degreewise

section Exact

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The identification of a right derived functor with the degreewise action is compatible
with composition.** On every object of the bounded below derived category, the comparison
`RF ⋙ RG ≅ R(G ∘ F)` read through the identifications for `F`, `G` and `G ∘ F` is the
comparison of the degreewise actions. -/
theorem exactMapDerivedCategoryPlusIso_comp_hom_app (K : DerivedCategory.Plus A) :
    (exactMapDerivedCategoryPlusIso G).hom.app (F.mapDerivedCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map ((exactMapDerivedCategoryPlusIso F).hom.app K) ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfExact F G (F ⋙ G)
            (Iso.refl (F ⋙ G))).hom.app K =
      (mapDerivedCategoryPlusCompIso F G).hom.app K ≫
        (exactMapDerivedCategoryPlusIso (F ⋙ G)).hom.app K := by
  have key : Functor.whiskerLeft F.mapDerivedCategoryPlus
          (exactMapDerivedCategoryPlusIso G).hom ≫
        Functor.whiskerRight (exactMapDerivedCategoryPlusIso F).hom
            G.rightDerivedFunctorPlus ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfExact F G (F ⋙ G)
            (Iso.refl (F ⋙ G))).hom =
      (mapDerivedCategoryPlusCompIso F G).hom ≫
        (exactMapDerivedCategoryPlusIso (F ⋙ G)).hom := by
    refine Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso A) (fun N => ?_)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    -- the derived comparison, on the image of the localization, is the degreewise one
    have glue : (exactMapDerivedCategoryPlusIso G).hom.app
            (F.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj N)) ≫
          G.rightDerivedFunctorPlus.map ((exactMapDerivedCategoryPlusIso F).hom.app
              (DerivedCategory.Plus.Qh.obj N)) ≫
            (Functor.rightDerivedFunctorPlusCompIsoOfExact F G (F ⋙ G)
              (Iso.refl (F ⋙ G))).hom.app (DerivedCategory.Plus.Qh.obj N) =
        (G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
            G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj N) ≫
              DerivedCategory.Plus.Qh.map
                  ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app N) ≫
                (F ⋙ G).mapDerivedCategoryPlusFactorsh.inv.app N) ≫
          (exactMapDerivedCategoryPlusIso (F ⋙ G)).hom.app
            (DerivedCategory.Plus.Qh.obj N) := by
      have hfac := Functor.rightDerivedFunctorPlusCompIsoOfExact_fac F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) N
      have hG := exactMapDerivedCategoryPlusIso_hom_app_Qh G (F.mapHomotopyCategoryPlus.obj N)
      simp only [Iso.trans_hom, asIso_hom, NatTrans.comp_app] at hG
      have hnat := (exactMapDerivedCategoryPlusIso G).hom.naturality
        (F.mapDerivedCategoryPlusFactorsh.hom.app N)
      rw [exactMapDerivedCategoryPlusIso_hom_app_Qh (F ⋙ G) N,
        exactMapDerivedCategoryPlusIso_hom_app_Qh F N]
      simp only [Iso.trans_hom, asIso_hom, NatTrans.comp_app, Functor.map_comp,
        Category.assoc, Iso.inv_hom_id_app_assoc]
      rw [← hfac, reassoc_of% hG.symm, reassoc_of% hnat]
    exact glue.trans
      ((congrArg (fun t => (G.mapDerivedCategoryPlus.map
              (F.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
            G.mapDerivedCategoryPlusFactorsh.hom.app
              (F.mapHomotopyCategoryPlus.obj N) ≫ t) ≫
          (exactMapDerivedCategoryPlusIso (F ⋙ G)).hom.app
            (DerivedCategory.Plus.Qh.obj N))
          (Qh_map_mapHomotopyCategoryPlusCompIso_refl_hom_comp F G N)).trans
        (congrArg (fun t => t ≫ (exactMapDerivedCategoryPlusIso (F ⋙ G)).hom.app
            (DerivedCategory.Plus.Qh.obj N))
          (mapDerivedCategoryPlusCompIso_hom_app_Qh F G N).symm))
  exact NatTrans.congr_app key K

end Exact

end Stacks.DerivedFunctor

end
