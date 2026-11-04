module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftCompatibility

/-!
# The canonical map against the translation

Let `(C, O)` be a ringed site, let `F` be a complex of `O`-modules and let `G` be a K-injective
one. This file assembles the four factor compatibilities of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftCompatibility` into
the single square they were collected for: the canonical map
`Hom^•(F, G) ⟶ RHom_O(F, G)` of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is compatible with the translation in
its covariant variable.

## Main results

* `AlgebraicGeometry.RingedSite.uliftComplexSelfIso_inv_naturality` and
  `AlgebraicGeometry.RingedSite.uliftComplexSelfIso_shift_inv`: the universe comparison is natural
  and its inverse is compatible with the translation; both hold degreewise by `ULift.up`.
* `AlgebraicGeometry.RingedSite.globalSectionsIso_inv_shift`: the **first leg** of the canonical
  map, the morphism of complexes `Hom^•(F, G) ⟶ Γ(C, SheafHom(F, G))` inverse to Tag 0A8Z and
  its universe lift, is compatible with the translation.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_shift`: **the square.** The
  canonical map at `(F, G[n])`, followed by the commutation of the derived internal Hom with the
  translation at a K-injective target and by the commutation of derived global sections with the
  translation, is the Hom-complex target shift followed by the `n`-shift of the canonical map at
  `(F, G)`.

## Implementation notes

*Why a separate module.* The square is a chase through six rewrites in
`D(Ab)`, each of which is one of the four factor compatibilities or a naturality of
`CategoryTheory.Functor.commShiftIso`; it introduces no new mathematics and the file it would
otherwise extend is already the collection of its inputs.

*The one place the goal has to be renormalized.* The target of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is written with
`AlgebraicGeometry.RingedSite.globalDerivedHom`, whereas the three morphisms it is the composite
of are written with `AlgebraicGeometry.RingedSite.derivedModuleGlobalSections` applied to the
derived internal Hom. The two are equal by `rfl`
(`AlgebraicGeometry.RingedSite.globalDerivedHom_obj_obj`) but not syntactically, and
`CategoryTheory.Category.assoc` does not instantiate across the mismatch — so the composite is
left unassociated and every subsequent rewrite fails. Unfolding `globalDerivedHom` with `dsimp`
at the start of the proof is what makes the chase go through; this is the reason for the opening
`dsimp only`.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The universe comparison -/

/-- **The universe comparison of a complex of abelian groups is natural**, in the direction from
a complex to its degreewise lift. Both sides are `ULift.up` in each degree. -/
theorem uliftComplexSelfIso_inv_naturality {D D' : CochainComplex AddCommGrpCat.{u} ℤ}
    (ψ : D ⟶ D') :
    ψ ≫ (uliftComplexSelfIso D').inv =
      (uliftComplexSelfIso D).inv ≫
        (AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rfl

/-- **The inverse of the universe comparison is compatible with the translation.** This is the
inverse form of `AlgebraicGeometry.RingedSite.uliftComplexSelfIso_shift`; both sides are
`ULift.up` in each degree. -/
theorem uliftComplexSelfIso_shift_inv (D : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    (uliftComplexSelfIso (D⟦n⟧)).inv =
      (CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) n).map
          (uliftComplexSelfIso D).inv ≫
        ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso n).inv.app D := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rfl

/-! ### The first leg of the canonical map against the translation -/

/-- **The first leg of the canonical map is compatible with the translation in the covariant
variable.** The morphism of complexes of abelian groups
`Hom^•(F, G) ⟶ Γ(C, SheafHom(F, G))` — the inverse of Tag 0A8Z preceded by the inverse of the
universe comparison, with which
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` begins — commutes with moving a
shift from the Hom complex into the covariant variable, along
`CochainComplex.HomComplex.homComplexTargetShiftIso` on the module side and
`AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso` on the sheaf side.

This is `AlgebraicGeometry.RingedSite.globalSectionsIso_sheafHomTargetShiftIso` together with
the two statements above about the universe comparison. -/
theorem globalSectionsIso_inv_shift
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (homComplexTargetShiftIso F G n).hom ≫
        ((uliftComplexSelfIso (F.HomComplex (G⟦n⟧))).inv ≫
          (sheafHomComplex X F (G⟦n⟧)).globalSectionsIso.inv) =
      (CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) n).map
          ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
            (sheafHomComplex X F G).globalSectionsIso.inv) ≫
        (globalSectionsComplexShiftIso X (sheafHomComplex X F G).obj n).inv ≫
          globalSectionsComplexMap X (sheafHomTargetShiftIso X (K := F) (M := G) n).hom := by
  rw [← Category.assoc, uliftComplexSelfIso_inv_naturality,
    uliftComplexSelfIso_shift_inv (F.HomComplex G) n, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc, Category.assoc,
    globalSectionsIso_sheafHomTargetShiftIso X F G n, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-! ### The canonical map against the translation -/

/-- **The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` is compatible with the translation in its
covariant variable, at a K-injective target.** For a complex `F` and a K-injective complex `G` of
`O`-modules, the canonical map at `(F, G[n])` followed by the commutation
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective` of the derived internal
Hom with the translation and by the commutation of derived global sections with the translation
is the Hom-complex target shift `CochainComplex.HomComplex.homComplexTargetShiftIso` followed by
the `n`-shift of the canonical map at `(F, G)`.

This is the square the degree-`n` reading of the canonical map needs: with it, the degree-`n`
reading follows from the degree-zero reading
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero_of_isKFlat`, since for
a K-flat `F` and a K-injective `G` the pair `(F, G[n])` is a representative pair along with
`(F, G)`.

The proof is the composite of the four factor compatibilities: the first leg by
`AlgebraicGeometry.RingedSite.globalSectionsIso_inv_shift`, the unit of derived global sections
by `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_shift` and its naturality
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_naturality`, and the comparison with the
derived internal Hom by
`AlgebraicGeometry.RingedSite.sheafHomComplexUnit_derivedSheafHomTargetShiftIsoOfKInjective`. -/
theorem homComplexToGlobalDerivedHom_shift
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective] (n : ℤ) :
    DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom ≫
        homComplexToGlobalDerivedHom X F (G⟦n⟧) ≫
          (derivedModuleGlobalSections X).map
              (derivedSheafHomTargetShiftIsoOfKInjective X F G n).hom ≫
            ((derivedModuleGlobalSections X).commShiftIso n).hom.app
              (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
                (DerivedCategory.Q.obj G)) =
      (DerivedCategory.Q.commShiftIso n).hom.app (F.HomComplex G) ≫
        (CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
          (homComplexToGlobalDerivedHom X F G) := by
  have hdef :
      ∀ M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
        homComplexToGlobalDerivedHom X F M =
          DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex M)).inv ≫
              (sheafHomComplex X F M).globalSectionsIso.inv) ≫
            globalSectionsDerivedUnit X (sheafHomComplex X F M).obj ≫
              (derivedModuleGlobalSections X).map (sheafHomComplexUnit X F M) := fun _ => rfl
  have h1 : DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom ≫
        DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex (G⟦n⟧))).inv ≫
          (sheafHomComplex X F (G⟦n⟧)).globalSectionsIso.inv) =
      DerivedCategory.Q.map
          ((CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) n).map
            ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
              (sheafHomComplex X F G).globalSectionsIso.inv)) ≫
        DerivedCategory.Q.map
            (globalSectionsComplexShiftIso X (sheafHomComplex X F G).obj n).inv ≫
          DerivedCategory.Q.map
            (globalSectionsComplexMap X (sheafHomTargetShiftIso X (K := F) (M := G) n).hom) := by
    rw [← CategoryTheory.Functor.map_comp, globalSectionsIso_inv_shift]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have h3 : (derivedModuleGlobalSections X).map (sheafHomComplexUnit X F (G⟦n⟧)) ≫
        (derivedModuleGlobalSections X).map
          (derivedSheafHomTargetShiftIsoOfKInjective X F G n).hom =
      (derivedModuleGlobalSections X).map
          (DerivedCategory.Q.map (sheafHomTargetShiftIso X (K := F) (M := G) n).inv) ≫
        (derivedModuleGlobalSections X).map
            ((DerivedCategory.Q.commShiftIso n).hom.app (sheafHomComplex X F G).obj) ≫
          (derivedModuleGlobalSections X).map
            ((CategoryTheory.shiftFunctor
              (DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              n).map (sheafHomComplexUnit X F G)) := by
    rw [← CategoryTheory.Functor.map_comp,
      sheafHomComplexUnit_derivedSheafHomTargetShiftIsoOfKInjective,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  have hcancel : (derivedModuleGlobalSections X).map
        (DerivedCategory.Q.map (sheafHomTargetShiftIso X (K := F) (M := G) n).hom) ≫
      (derivedModuleGlobalSections X).map
        (DerivedCategory.Q.map (sheafHomTargetShiftIso X (K := F) (M := G) n).inv) = 𝟙 _ := by
    simp [← CategoryTheory.Functor.map_comp]
  have hcancel2 : DerivedCategory.Q.map
        (globalSectionsComplexShiftIso X (sheafHomComplex X F G).obj n).inv ≫
      DerivedCategory.Q.map
        (globalSectionsComplexShiftIso X (sheafHomComplex X F G).obj n).hom = 𝟙 _ := by
    simp [← CategoryTheory.Functor.map_comp]
  dsimp only [globalDerivedHom, Functor.comp_obj, Functor.whiskeringRight_obj_obj]
  simp only [hdef, Category.assoc]
  rw [reassoc_of% h1,
    reassoc_of% (globalSectionsDerivedUnit_naturality X
      (sheafHomTargetShiftIso X (K := F) (M := G) n).hom),
    reassoc_of% h3, reassoc_of% hcancel,
    CategoryTheory.Functor.commShiftIso_hom_naturality (derivedModuleGlobalSections X)
      (sheafHomComplexUnit X F G) n,
    ← reassoc_of% (globalSectionsDerivedUnit_shift X (sheafHomComplex X F G).obj n),
    reassoc_of% hcancel2,
    reassoc_of% (CategoryTheory.Functor.commShiftIso_hom_naturality DerivedCategory.Q
      ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
        (sheafHomComplex X F G).globalSectionsIso.inv) n)]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end AlgebraicGeometry.RingedSite

end
