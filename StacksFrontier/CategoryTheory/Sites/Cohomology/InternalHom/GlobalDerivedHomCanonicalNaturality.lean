module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeReading

/-!
# The canonical map is natural in both complexes

Let `(C, O)` be a ringed site. The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is natural in `F` and `G` for
morphisms of complexes, **with no hypothesis on any of the four complexes**: for `k : F' ⟶ F` and
`m : G ⟶ G'` the square comparing it at `(F, G)` with it at `(F', G')`, along
`CochainComplex.HomComplex.homComplexConj` on the source and the map induced on the derived
internal Hom on the target, commutes.

This is the input the transport of the degree-`n` reading off a representative pair needs: that
reading
(`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_of_isKFlat`) assumes a
K-flat source and a K-injective target, and the complexes the central clause of Tag 0CS6 is about
— the tensor products `M ⊗_E K` and `N ⊗_E K` — are neither.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomComplexUnit_naturality`: the comparison with the derived
  internal Hom is natural in both complexes, for arbitrary complexes.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_naturality`: the canonical map is
  natural in both complexes, for arbitrary complexes.

## Implementation notes

*The comparison with the derived internal Hom needs no K-injectivity.*
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` assumes both targets
K-injective, so it does not apply here; but
`AlgebraicGeometry.RingedSite.sheafHomComplexUnit` is built from the comparison with the chosen
*resolution* of the target rather than from the comparison at a K-injective target, and
`AlgebraicGeometry.RingedSite.derivedSheafHomResolutionComparison_naturality` has **no**
hypothesis — it is the naturality of the lifting datum of the descent. What is left after it is
the naturality of `AlgebraicGeometry.RingedSite.kInjectiveAugmentation`, which is free. So the
shortcut that made the shift compatibility of `sheafHomComplexUnit` free (passing to Tag 0A97 at
a K-injective target) is *not* what works here; passing instead to the resolution comparison is.

*The three factors.* The canonical map is the inverse of Tag 0A8Z with its universe lift, the
unit of derived global sections, and the comparison with the derived internal Hom, and each is
natural: the first by `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap` together with
`AlgebraicGeometry.RingedSite.uliftComplexSelfIso_inv_naturality`, the second by
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_naturality`, the third by the statement
above. Only the third had to be built.

*The associativity hazard.* The proof opens with `dsimp only [globalDerivedHom, …]` for the
reason recorded in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftSquare` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeReading`: the
target of the canonical map is spelled with
`AlgebraicGeometry.RingedSite.globalDerivedHom` while its factors are spelled with
`AlgebraicGeometry.RingedSite.derivedModuleGlobalSections` applied to the derived internal Hom,
the two are equal by `rfl` but not syntactically, and `CategoryTheory.Category.assoc` will not
instantiate across the mismatch.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The comparison with the derived internal Hom is natural in both complexes**, for arbitrary
complexes: for `k : F' ⟶ F` and `m : G ⟶ G'` the comparison intertwines `homMap k m` with the
map induced on the derived internal Hom.

No complex is assumed K-injective. The comparison is built from
`AlgebraicGeometry.RingedSite.derivedSheafHomResolutionComparison`, whose naturality carries no
hypothesis, and from the augmentation into the chosen K-injective resolution, whose naturality is
free; see the implementation notes. -/
theorem sheafHomComplexUnit_naturality
    {F F' G G' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : F' ⟶ F) (m : G ⟶ G') :
    DerivedCategory.Q.map (homMap X k m) ≫ sheafHomComplexUnit X F' G' =
      sheafHomComplexUnit X F G ≫
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
            (DerivedCategory.Q.obj G) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F'))).map
            (DerivedCategory.Q.map m)) := by
  have hres : (derivedSheafHomResolutionComparison X F G).inv ≫
      (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
          (DerivedCategory.Q.obj G) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F'))).map
          (DerivedCategory.Q.map m)) =
      DerivedCategory.Q.map (homMap X k ((kInjectiveResolution X).map m)) ≫
        (derivedSheafHomResolutionComparison X F' G').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Category.assoc,
      derivedSheafHomResolutionComparison_naturality X k m]
  rw [sheafHomComplexUnit, sheafHomComplexUnit, Category.assoc, hres,
    ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    homMap_comp, homMap_comp, Category.id_comp, Category.comp_id]
  have hnat : (kInjectiveAugmentation X).app G ≫ (kInjectiveResolution X).map m =
      m ≫ (kInjectiveAugmentation X).app G' :=
    ((kInjectiveAugmentation X).naturality m).symm
  rw [hnat]

/-- **The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` is natural in both complexes**, for
arbitrary complexes: for `k : F' ⟶ F` and `m : G ⟶ G'` it intertwines pre- and postcomposition
`CochainComplex.HomComplex.homComplexConj k m` on the Hom complex with the map induced on the
global derived hom.

No complex is assumed K-flat or K-injective, which is the whole point: this is what lets the
degree-`n` reading of the canonical map be transported off the representative pair at which it is
proved. The three factors of the canonical map are natural separately; see the implementation
notes. -/
theorem homComplexToGlobalDerivedHom_naturality
    {F F' G G' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : F' ⟶ F) (m : G ⟶ G') :
    DerivedCategory.Q.map (homComplexConj k m) ≫ homComplexToGlobalDerivedHom X F' G' =
      homComplexToGlobalDerivedHom X F G ≫
        (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
              (DerivedCategory.Q.obj G) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F'))).map
              (DerivedCategory.Q.map m)) := by
  have hdef :
      ∀ A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      homComplexToGlobalDerivedHom X A B =
        DerivedCategory.Q.map ((uliftComplexSelfIso (A.HomComplex B)).inv ≫
            (sheafHomComplex X A B).globalSectionsIso.inv) ≫
          globalSectionsDerivedUnit X (sheafHomComplex X A B).obj ≫
            (derivedModuleGlobalSections X).map (sheafHomComplexUnit X A B) := fun _ _ => rfl
  have ha : homComplexConj k m ≫ ((uliftComplexSelfIso (F'.HomComplex G')).inv ≫
        (sheafHomComplex X F' G').globalSectionsIso.inv) =
      ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv) ≫
        globalSectionsComplexMap X (homMap X k m) := by
    rw [← Category.assoc, uliftComplexSelfIso_inv_naturality, Category.assoc, Category.assoc]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, globalSectionsIso_homMap X k m,
      Iso.inv_hom_id_assoc]
  have h1 : DerivedCategory.Q.map (homComplexConj k m) ≫
        DerivedCategory.Q.map ((uliftComplexSelfIso (F'.HomComplex G')).inv ≫
          (sheafHomComplex X F' G').globalSectionsIso.inv) =
      DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv) ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X (homMap X k m)) := by
    rw [← CategoryTheory.Functor.map_comp, ha, CategoryTheory.Functor.map_comp]
  have h3 : (derivedModuleGlobalSections X).map
        (DerivedCategory.Q.map (homMap X k m)) ≫
      (derivedModuleGlobalSections X).map (sheafHomComplexUnit X F' G') =
      (derivedModuleGlobalSections X).map (sheafHomComplexUnit X F G) ≫
        (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
              (DerivedCategory.Q.obj G) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F'))).map
              (DerivedCategory.Q.map m)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      sheafHomComplexUnit_naturality X k m]
  dsimp only [globalDerivedHom, Functor.comp_obj, Functor.whiskeringRight_obj_obj]
  simp only [hdef, Category.assoc]
  rw [reassoc_of% h1,
    reassoc_of% (globalSectionsDerivedUnit_naturality X (homMap X k m)),
    h3]

end AlgebraicGeometry.RingedSite

end
