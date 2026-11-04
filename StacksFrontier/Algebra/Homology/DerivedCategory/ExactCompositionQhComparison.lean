module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition

/-!
# The comparison of the degreewise actions, read on the homotopy category

For exact additive functors `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` of abelian categories with derived
categories, `Stacks.DerivedFunctor.mapDerivedCategoryCompIso` identifies the composite of the
degreewise actions on unbounded derived categories with the degreewise action of the composite.
It is constructed as a lift along the localization `Q : C(𝒜) ⥤ D(𝒜)` of the category of
complexes, and is therefore computed by
`Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Q` on the image of `Q`. This file
computes it instead on the image of the localization `Qh : K(𝒜) ⥤ D(𝒜)` of the homotopy
category, where it is the composite of the three factorizations of the degreewise actions
through the homotopy category.

## Main results

* `Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso`: for a
  single exact functor, the factorization through the homotopy category followed by the
  identification of `K(𝒜) ⥤ D(𝒜)` with `C(𝒜) ⥤ D(𝒜)` is the factorization through the
  category of complexes.
* `Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Qh`: **the comparison of the
  degreewise actions on the image of `Qh`**, written through the factorizations of the three
  degreewise actions through the homotopy category.

## Implementation notes

The two localizations are compared by
`DerivedCategory.quotientCompQhIso : HomotopyCategory.quotient ⋙ Qh ≅ Q`, whose components are
not identities, so `CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` is a composite of
four morphisms; `mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso` telescopes it. The
comparison for a composite then follows by cancelling the invertible comparison of the two
localizations.

The proofs are in term mode: `(F ⋙ G).mapHomologicalComplex c` and
`F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c` agree only definitionally, so `rw` and
`simp` (including for associativity) fail on goals mixing the two spellings.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.DerivedFunctor

section Single

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- **The two factorizations of the degreewise action of an exact functor agree.** On a complex
`K`, the factorization of `E.mapDerivedCategory` through the homotopy category, followed by the
identification of the two localizations at `E(K)`, is the identification of the two
localizations at `K` followed by the factorization through the category of complexes. -/
theorem mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso (K : CochainComplex A ℤ) :
    E.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      E.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
        E.mapDerivedCategoryFactors.hom.app K := by
  have hQh : DerivedCategory.Qh.map
        ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) =
      𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :=
    (congrArg (fun f => DerivedCategory.Qh.map f)
      (show (E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K =
        𝟙 ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) from rfl)).trans
      (DerivedCategory.Qh.map_id _)
  have hcancel : ((DerivedCategory.quotientCompQhIso B).inv.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
            ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K)) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      𝟙 (DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => (DerivedCategory.quotientCompQhIso B).inv.app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ t)
          ((congrArg (fun t => t ≫ (DerivedCategory.quotientCompQhIso B).hom.app
              ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) hQh).trans
            (Category.id_comp _))).trans
        (Iso.inv_hom_id_app _ _))
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  exact (Category.assoc _ _ _).trans (congrArg (fun t =>
    E.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫ t)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => E.mapDerivedCategoryFactors.hom.app K ≫ t) hcancel).trans
          (Category.comp_id _))))

end Single

section Comp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The comparison of the degreewise actions of two exact functors, on the image of the
localization of the homotopy category.** On a bounded or unbounded object `M` of the homotopy
category it is the two factorizations of the degreewise actions through the homotopy category,
followed by the inverse of the factorization for the composite. -/
theorem mapDerivedCategoryCompIso_hom_app_Qh (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj M) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app M) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
          (F ⋙ G).mapDerivedCategoryFactorsh.inv.app M := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  have hnat : G.mapDerivedCategory.map (F.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso A).hom.app K)) ≫
      (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) =
    (mapDerivedCategoryCompIso F G).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      (F ⋙ G).mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K) :=
    (mapDerivedCategoryCompIso F G).hom.naturality _
  have hQ : (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
        (F ⋙ G).mapDerivedCategoryFactors.hom.app K =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (congrArg (fun t => t ≫ (F ⋙ G).mapDerivedCategoryFactors.hom.app K)
        (mapDerivedCategoryCompIso_hom_app_Q F G K)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => G.mapDerivedCategory.map
            (F.mapDerivedCategoryFactors.hom.app K) ≫ t)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun t => G.mapDerivedCategoryFactors.hom.app
                  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ t)
                (Iso.inv_hom_id_app (F ⋙ G).mapDerivedCategoryFactors K)).trans
              (Category.comp_id _)))))
  have hleft : ((mapDerivedCategoryCompIso F G).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        (F ⋙ G).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app
            (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso A).hom.app K)) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => (mapDerivedCategoryCompIso F G).hom.app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫ t)
          (mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso (F ⋙ G) K)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ (F ⋙ G).mapDerivedCategoryFactors.hom.app K)
              hnat.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun t => G.mapDerivedCategory.map (F.mapDerivedCategory.map
                ((DerivedCategory.quotientCompQhIso A).hom.app K)) ≫ t) hQ)))))
  have hright : (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
          G.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app
            (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso A).hom.app K)) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫ t)
          (mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso G
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ G.mapDerivedCategoryFactors.hom.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
              ((G.mapDerivedCategory.map_comp _ _).symm.trans
                (congrArg (fun t => G.mapDerivedCategory.map t)
                  (mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso F K)))).trans
            ((congrArg (fun t => t ≫ G.mapDerivedCategoryFactors.hom.app
                  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
                (G.mapDerivedCategory.map_comp _ _)).trans
              (Category.assoc _ _ _)))))
  have hiso : IsIso ((DerivedCategory.quotientCompQhIso C).hom.app
      (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    (Iso.app (DerivedCategory.quotientCompQhIso C) _).isIso_hom
  have key : (mapDerivedCategoryCompIso F G).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      (F ⋙ G).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) :=
    (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app
      (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).1
        (hleft.trans hright.symm)
  exact (((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (F ⋙ G).mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) key.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => (mapDerivedCategoryCompIso F G).hom.app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫ t)
          (Iso.hom_inv_id_app (F ⋙ G).mapDerivedCategoryFactorsh
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).trans
          (Category.comp_id _)))))).symm

end Comp

end Stacks.DerivedFunctor

end
