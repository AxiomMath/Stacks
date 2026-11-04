module

public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroHom

/-!
# The `k`-linear form of Tag 08DK is natural in the target

`AlgebraicGeometry.homLinearEquivDegreeZeroSections` identifies `Hom(N, N')` with
`H⁰RΓ(X, R𝓗om(N, N'))`. This file proves that it carries postcomposition with `χ : N' ⟶ N''` to
`H⁰RΓ(X, R𝓗om(N, χ))`: each of its three constituents (the identification of
`AlgebraicGeometry.homologyZeroGlobalSectionsOverIso`, the forgetful comparison, and
[Stacks, Tag 08DK] itself) is natural in the object.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry

open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.AlgebraicGeometry.ProperSupportCoherent

variable (k : Type u) [Field k] (X : Over (Spec (.of k)))

/-- **[Stacks, Tag 08DK], additively, is natural in the target.** -/
theorem degreeZeroSectionsHomAddEquiv_naturality_target (N : DerivedCategory X.left.Modules)
    {N' N'' : DerivedCategory X.left.Modules} (χ : N' ⟶ N'')
    (x : degreeZeroSectionsField k X.hom (derivedSheafHomObj k X N N')) :
    degreeZeroSectionsHomAddEquiv k X N N''
        (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
          ((sectionsOverBase X.hom.toLRSHom.toShHom).map ((sheafHomOutOf k X N).map χ))).hom x) =
      degreeZeroSectionsHomAddEquiv k X N N' x ≫ χ := by
  set y := (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N')).inv.hom x
  have hy : (homologyZeroGlobalSectionsOverIso k X (derivedSheafHomObj k X N N'')).inv.hom
      (((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
          ((sectionsOverBase X.hom.toLRSHom.toShHom).map ((sheafHomOutOf k X N).map χ))).hom x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver X.hom).map ((sheafHomOutOf k X N).map χ))).hom y :=
    ConcreteCategory.congr_hom
      ((homologyZeroGlobalSectionsOverNatIso k X).inv.naturality ((sheafHomOutOf k X N).map χ)) x
  have key : (homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N'')).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver X.hom).map
          ((sheafHomOutOf k X N).map χ))) y) =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf)).map
            ((sheafHomOutOf k X N).map χ)))
        ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).hom y) :=
    ((CategoryTheory.comp_apply
        ((derivedGlobalSectionsOver X.hom ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ⋙
          forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map
            ((sheafHomOutOf k X N).map χ))
        ((homologyZeroForgetNatIso X.hom).hom.app _) y).symm.trans
      (ConcreteCategory.congr_hom ((homologyZeroForgetNatIso X.hom).hom.naturality _) y)).trans
        (CategoryTheory.comp_apply ((homologyZeroForgetNatIso X.hom).hom.app _)
          ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
            (Stacks.SheafOfModules.ringedSite X.left.sheaf) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              ((sheafHomOutOf k X N).map χ)) y)
  have h08DK := Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv_naturality_target
    X.left.sheaf N χ ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N')).hom y)
  exact (congrArg (fun z => derivedSheafHomGlobalSectionsEquivScheme k X N N''
      ((homologyZeroForgetIso X.hom (derivedSheafHomObj k X N N'')).hom z)) hy).trans
    ((congrArg (derivedSheafHomGlobalSectionsEquivScheme k X N N'') key).trans h08DK)

/-- **The class of a morphism is the image of the class of the identity**:
`e(φ) = H⁰RΓ(R𝓗om(N, φ))(e(𝟙_N))`. -/
theorem homLinearEquivDegreeZeroSections_eq_map {N N' : DerivedCategory X.left.Modules}
    (φ : N ⟶ N') :
    homLinearEquivDegreeZeroSections k X N N' φ =
      ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
        ((sectionsOverBase X.hom.toLRSHom.toShHom).map ((sheafHomOutOf k X N).map φ))).hom
        (homLinearEquivDegreeZeroSections k X N N (𝟙 N)) := by
  have h := homLinearEquivDegreeZeroSections_comp k X N N N' (𝟙 N) φ
  rw [Category.id_comp] at h
  exact h

end AlgebraicGeometry
