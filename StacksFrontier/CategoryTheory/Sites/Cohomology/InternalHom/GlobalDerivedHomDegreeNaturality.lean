module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftNaturality

/-!
# The cohomology of the global derived hom in every degree is natural

Let `(C, O)` be a ringed site. The degree-`n` identification

`H^n(RHom_O(K, L)) = Hom_{D(O)}(K, L[n]) = Ext^n_{D(O)}(K, L)`

is `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift`, where it is
stated at each pair of objects and no naturality is claimed. This file proves that it **is**
natural in both variables, for arbitrary morphisms of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_naturality`: **the degree-`n`
  identification of the global derived hom is natural in both variables.** For `φ : K' ⟶ K` and
  `ψ : L ⟶ L'` it carries the map induced on `H^n(RHom_O(-, -))` to precomposition with `φ` and
  postcomposition with `ψ[n]`.

## Implementation notes

The identification is the composite of four steps, and its naturality is the naturality of each.
The shift sequence of the homology functors of the derived category is natural by Mathlib's
`CategoryTheory.Functor.isoShift_inv_naturality`; derived global sections commute with the
translation naturally by `CategoryTheory.Functor.commShiftIso_inv_naturality`; the derived
internal Hom commutes with the translation in its covariant variable naturally in both variables
by `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_hom_naturality`; and the
degree-zero identification of Tag 08JA is natural in both variables by
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`.

The last two are the ones with mathematical content, and both are recorded in the files they come
from as absent for arbitrary morphisms of `D(O)`; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftNaturality` and of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence` for
why the obstruction those files describe does not in fact arise.

*No attribute is placed in this file.* Tag 0B6E records the identification
`H^0(RHom_O(K, L)) = Hom_{D(O)}(K, L)` and `H^p(RHom_O(K, L)) = Ext^p_{D(O)}(K, L)`, which is
already carried by `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift`. It asserts no
naturality in either variable; the only functoriality it discusses is along a morphism of ringed
topoi, pulling both arguments back along `Lf^*`, and that only as "a canonical map". So the
naturality proved here is infrastructure for the central clause of Tag 0CS6 and not a second
statement of 0B6E's result, and it is registered against no tag.

## References

* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Two morphisms of `D(Ab)` applied in succession to a degree-zero cohomology class act as
their composite. -/
theorem homologyZero_map_comp_apply
    {Z Z' Z'' : DerivedCategory AddCommGrpCat.{u}} (a : Z ⟶ Z') (b : Z' ⟶ Z'')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj Z : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map b
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map a x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map (a ≫ b) x := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

variable (X : RingedSite.{u, u, u})

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The degree-`n` identification of the global derived hom, written out on an element: the
degree is moved into the covariant variable by the shift sequence of the homology functors, the
commutation of derived global sections with the translation and
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso`, and Tag 08JA is then applied in
degree zero. -/
theorem globalDerivedHomDegreeEquiv_apply
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L)) : Type u)) :
    globalDerivedHomDegreeEquiv X K L n ξ =
      derivedSheafHomGlobalSectionsEquiv X K (L⟦n⟧)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((((derivedModuleGlobalSections X).commShiftIso n).app
                (((derivedSheafHomBifunctor X).obj (op K)).obj L)).inv ≫
            (derivedModuleGlobalSections X).map (derivedSheafHomTargetShiftIso X K L n).inv)
          (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
            ((derivedModuleGlobalSections X).obj
              (((derivedSheafHomBifunctor X).obj (op K)).obj L)) ξ)) := rfl

/-- **The degree-`n` cohomology of the global derived hom is natural in both variables.** For
`φ : K' ⟶ K` and `ψ : L ⟶ L'` in `D(O)`, the map induced on the degree-`n` cohomology of
`RHom_O(-, -)` is carried by
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` to precomposition with `φ` and
postcomposition with `ψ[n]`, so that the identification of `H^n(RHom_O(K, L))` with
`Ext^n_{D(O)}(K, L)` is an identification of functors and not merely of groups.

The four steps the identification is composed of are each natural; see the implementation
notes.

*This carries no tag.* It is the naturality of the degree-`n` identification, which Tag 0B6E does
not assert: that tag records the identification itself, `H^0(RHom_O(K, L)) = Hom_{D(O)}(K, L)`
and `H^p(RHom_O(K, L)) = Ext^p_{D(O)}(K, L)`, and claims no naturality in either variable — the
only functoriality it discusses is along a morphism of ringed topoi, pulling both arguments back
along `Lf^*`, and that only as "a canonical map". Registering the statement below against 0B6E
would attribute a bivariant naturality assertion to a source that makes none, so it is registered
against no tag. -/
theorem globalDerivedHomDegreeEquiv_naturality
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : K' ⟶ K) (ψ : L ⟶ L')
    (n : ℤ)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L)) : Type u)) :
    globalDerivedHomDegreeEquiv X K' L' n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map φ.op).app L ≫
              ((derivedSheafHomBifunctor X).obj (op K')).map ψ)) ξ) =
      φ ≫ globalDerivedHomDegreeEquiv X K L n ξ ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            n).map ψ := by
  rw [globalDerivedHomDegreeEquiv_apply, globalDerivedHomDegreeEquiv_apply]
  -- Move the degree past the induced map: the shift sequence of the homology functors is natural.
  have ha : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op K')).obj L'))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map φ.op).app L ≫
              ((derivedSheafHomBifunctor X).obj (op K')).map ψ)) ξ) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map φ.op).app L ≫
              ((derivedSheafHomBifunctor X).obj (op K')).map ψ)))
        (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
          ((derivedModuleGlobalSections X).obj
            (((derivedSheafHomBifunctor X).obj (op K)).obj L)) ξ) :=
    ConcreteCategory.congr_hom
      (CategoryTheory.Functor.isoShift_inv_naturality
        (F := DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) n
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map φ.op).app L ≫
            ((derivedSheafHomBifunctor X).obj (op K')).map ψ))) ξ
  rw [ha, homologyZero_map_comp_apply]
  -- The composite of the three morphisms of `D(Ab)` is the induced map after the degree move.
  have hb : (CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map φ.op).app L ≫
              ((derivedSheafHomBifunctor X).obj (op K')).map ψ)) ≫
        ((((derivedModuleGlobalSections X).commShiftIso n).app
              (((derivedSheafHomBifunctor X).obj (op K')).obj L')).inv ≫
          (derivedModuleGlobalSections X).map
            (derivedSheafHomTargetShiftIso X K' L' n).inv) =
      ((((derivedModuleGlobalSections X).commShiftIso n).app
              (((derivedSheafHomBifunctor X).obj (op K)).obj L)).inv ≫
            (derivedModuleGlobalSections X).map
              (derivedSheafHomTargetShiftIso X K L n).inv) ≫
        (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map φ.op).app (L⟦n⟧) ≫
            ((derivedSheafHomBifunctor X).obj (op K')).map
              ((CategoryTheory.shiftFunctor
                (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
                  n).map ψ)) := by
    have hTSI : (CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              n).map
            (((derivedSheafHomBifunctor X).map φ.op).app L ≫
              ((derivedSheafHomBifunctor X).obj (op K')).map ψ) ≫
          (derivedSheafHomTargetShiftIso X K' L' n).inv =
        (derivedSheafHomTargetShiftIso X K L n).inv ≫
          (((derivedSheafHomBifunctor X).map φ.op).app (L⟦n⟧) ≫
            ((derivedSheafHomBifunctor X).obj (op K')).map
              ((CategoryTheory.shiftFunctor
                (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
                  n).map ψ)) := by
      rw [Iso.comp_inv_eq, Category.assoc,
        derivedSheafHomTargetShiftIso_hom_naturality X φ ψ n, Iso.inv_hom_id_assoc]
    rw [← Category.assoc]
    simp only [Iso.app_inv]
    rw [CategoryTheory.Functor.commShiftIso_inv_naturality]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hTSI]
  have hfinal := (homologyZero_map_comp_apply
      ((((derivedModuleGlobalSections X).commShiftIso n).app
            (((derivedSheafHomBifunctor X).obj (op K)).obj L)).inv ≫
        (derivedModuleGlobalSections X).map (derivedSheafHomTargetShiftIso X K L n).inv)
      ((derivedModuleGlobalSections X).map
        (((derivedSheafHomBifunctor X).map φ.op).app (L⟦n⟧) ≫
          ((derivedSheafHomBifunctor X).obj (op K')).map
            ((CategoryTheory.shiftFunctor
              (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
                n).map ψ)))
      (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op K)).obj L)) ξ)).trans
    (congrArg (fun f => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map f
        (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
          ((derivedModuleGlobalSections X).obj
            (((derivedSheafHomBifunctor X).obj (op K)).obj L)) ξ)) hb.symm)
  refine (congrArg (fun z => derivedSheafHomGlobalSectionsEquiv X K' (L'⟦n⟧) z) hfinal.symm).trans
    (derivedSheafHomGlobalSectionsEquiv_naturality X φ
      ((CategoryTheory.shiftFunctor
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          n).map ψ) _)

end AlgebraicGeometry.RingedSite

end
