module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleSections

/-!
# The canonical map into the global derived hom, over `Γ(C, O)`

Let `(C, O)` be a ringed site and let `F`, `G` be complexes of `O`-modules. Stacks 0CS6 asserts
its canonical map in `D(R)` for a ring `R` with a sheaf of commutative `R`-algebra structures on
`O`. Every such `R` maps to the ring `Γ(C, O)` of global sections of the structure sheaf
(`Stacks.Cohomology.SiteModules.AlgebraSheaf.toGlobalSections`), so `Γ(C, O)` is the universal
base ring: a statement in `D(Γ(C, O))` gives the statement in `D(R)` by restricting scalars along
that map.

`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is the canonical map
`Hom^•(F, G) ⟶ RHom_O(F, G)` read in `D(ℤ)`. This file builds the same composite over
`Γ(C, O)`, landing in the `D(Γ(C, O))`-valued global derived hom
`AlgebraicGeometry.RingedSite.globalDerivedHomModules` of Stacks 0B6E. All three of its legs are
available at the module level: the identification of Stacks 0A8Z is
`AlgebraicGeometry.RingedSite.globalSectionsHomComplexModulesIso`, the unit of derived global
sections is transcribed here, and the comparison with the derived internal Hom is a morphism of
`D(O)` to which module-valued derived global sections may be applied directly.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalSectionsModulesDerivedUnit`: the comparison from the
  `Γ(C, O)`-module of global sections of a complex to its derived global sections.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules`: the canonical map
  `Hom^•_{Comp^dg(O)}(F, G) ⟶ RHom_O(F, G)` of Stacks 0CS6 in `D(Γ(C, O))`.
* `AlgebraicGeometry.RingedSite.homComplexModulesForgetIso` and
  `AlgebraicGeometry.RingedSite.homComplexModulesDerivedForgetIso`: forgetting the scalars of the
  `Γ(C, O)`-module-valued Hom complex, on complexes and in the derived category.

## Main results

* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget_naturality`: the third leg of
  the canonical map forgets to the third leg of the `D(ℤ)`-valued one. That the whole map does is
  `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules_forget` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleForget`.
* `AlgebraicGeometry.RingedSite.globalSectionsModulesForgetUnit_comp_forget`: the universal
  property that defines
  `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget`, the identification of the
  two readings of derived global sections.
* `AlgebraicGeometry.RingedSite.forgetDerivedFactors_quotient`: on the class of a complex, the
  comparison of the forgetful functor with the localization is the homotopy-category comparison
  read through the two quotient functors.
* `AlgebraicGeometry.RingedSite.forgetMapHomotopyCategoryFactors_comp`: on the homotopy category
  the two routes from the module-valued global sections of a complex to its abelian-group-valued
  ones agree, on the nose.

## Implementation notes

*What this map is.* The map below **does** forget to
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`:
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules_forget` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleForget`. The two
are one map read over two base rings, so a statement about either is a statement about both.
Restricting the scalars along the map from the source's base ring is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleRestrict`, which
is the canonical map of Stacks 0CS6 in the source's `D(R)`; the registrations of that tag are
stated at the maps built from it, in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver` and
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtClauseOver`.

The compatibility is leg by leg, and the inputs of two of the three legs are here.

The third leg, `(derivedGlobalSectionsModules X).map (sheafHomComplexUnit X F G)`, is the
naturality of
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget`, which is
`derivedGlobalSectionsModulesForget_naturality` below and costs nothing: the comparison is a
natural transformation and the leg is a functor applied to a morphism of `D(O)`.

The second leg is the unit of derived global sections. What defines the identification of the
two readings is the universal property of the right derived functor, which is
`globalSectionsModulesForgetUnit_comp_forget` below; and the comparison of the two localizations
that the universal property has to be fed through consists of
`forgetDerivedFactors_quotient`, Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` read at the forgetful functor of
modules, and `forgetMapHomotopyCategoryFactors_comp`, which holds on the nose.

What assembling the second leg needed was a **spelling** and not a mathematical input. The
abelian-group-valued complex of global sections
`AlgebraicGeometry.RingedSite.globalSectionsComplex` is the abelian global sections of the
underlying complex of abelian sheaves, whereas forgetting the scalars of
`AlgebraicGeometry.RingedSite.globalSectionsModulesComplex` produces
`CategoryTheory.Functor.mapHomologicalComplex` of the forgetful functor applied to the
module-valued one. The two are equal — that is
`AlgebraicGeometry.RingedSite.globalSectionsModulesComplex_forget`, and it is `rfl` — but only
after a semireducible definition is unfolded. A composite passing through both spellings is
therefore not type-correct at `implicit` transparency, and every tactic rewriting under that
transparency — `simp`, and `rw` with a pattern carrying metavariables, `Category.assoc` among
them — refuses to fire on it, reporting that the pattern does not occur. The remedy, carried out
in `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleForget`, is to
install each such equality as a named isomorphism whose declared type mentions both spellings and
to carry it through the statements, so that no junction is defeq-only.

*The universe parameters* are the diagonal ones of the site, as everywhere around the global
derived hom; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom`.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The canonical map over `Γ(C, O)` -/

/-- **The comparison from global sections to derived global sections, over `Γ(C, O)`.** The class
of the complex of `Γ(C, O)`-modules of global sections of a complex of `O`-modules maps
canonically to its derived global sections. This is
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit` with its scalars kept: the unit of the
derived functor of Stacks 0D6I read through the identifications of the localization with
`CategoryTheory.Functor.mapHomologicalComplex`. -/
def globalSectionsModulesDerivedUnit
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj (globalSectionsModulesComplex X H) ⟶
      (derivedGlobalSectionsModules X).obj (DerivedCategory.Q.obj H) :=
  letI : (globalSectionsModules X).Additive :=
    globalSectionsFunctor_additive.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  ((DerivedCategory.quotientCompQhIso
      (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).app
      (globalSectionsModulesComplex X H)).inv ≫
    DerivedCategory.Qh.map
        (((globalSectionsModules X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app H).inv ≫
      (derivedGlobalSectionsModulesUnit X).app
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) ≫
        (derivedGlobalSectionsModules X).map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app H).hom

variable {X}
  (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Forgetting the scalars of the `Γ(C, O)`-module-valued Hom complex gives the Hom complex.**
In each degree both are the degree-`n` cochains `F ⟶ G`, and both differentials are
`CochainComplex.HomComplex.δ`. -/
def homComplexModulesForgetIso :
    ((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          F G) ≅
      F.HomComplex G :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    let := linearSheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun f => ?_)
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d]
    exact (CochainComplex.dgCategoryLinear_homComplexModules_d_apply
      (B := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (R := ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      F G n (n + 1) rfl f).symm)

/-- **Stacks 0CS6, the canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` over `Γ(C, O)`.** The Hom
complex of two complexes of `O`-modules, taken in the differential graded category `Comp^dg(O)`
over `Γ(C, O)`, is the complex of `Γ(C, O)`-modules of global sections of their internal Hom
complex (Stacks 0A8Z over `Γ(C, O)`,
`AlgebraicGeometry.RingedSite.globalSectionsHomComplexModulesIso`), which maps to the
`D(Γ(C, O))`-valued global derived hom of Stacks 0B6E through the unit of derived global sections
and the comparison with the derived internal Hom.

Since every base ring of Stacks 0CS6 maps to `Γ(C, O)`, this is the canonical map for each of
them, by restriction of scalars. It forgets to
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`, by
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules_forget`, so the two are one
map; see the implementation notes. -/
def homComplexToGlobalDerivedHomModules :
    DerivedCategory.Q.obj
        ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          F G) ⟶
      ((globalDerivedHomModules X).obj (op (DerivedCategory.Q.obj F))).obj
        (DerivedCategory.Q.obj G) :=
  DerivedCategory.Q.map (globalSectionsHomComplexModulesIso F G).inv ≫
    globalSectionsModulesDerivedUnit X (sheafHomComplex X F G).obj ≫
      (derivedGlobalSectionsModules X).map (sheafHomComplexUnit X F G)

/-- **The source of the canonical map over `Γ(C, O)`, with its scalars forgotten, is the source
of the canonical map in `D(ℤ)`.** -/
def homComplexModulesDerivedForgetIso :
    (underlyingDerivedGroup X).obj
        (DerivedCategory.Q.obj
          ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
            F G)) ≅
      DerivedCategory.Q.obj (F.HomComplex G) :=
  (Functor.mapDerivedCategoryFactors
      (forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        AddCommGrpCat.{u})).app _ ≪≫
    DerivedCategory.Q.mapIso (homComplexModulesForgetIso F G)

/-! ### Towards forgetting the scalars of the canonical map -/

variable (X)

/-- **The third leg forgets.** Applying module-valued derived global sections to a morphism of
`D(O)` and then forgetting the scalars is applying abelian-group-valued derived global sections
to it: the naturality of
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget`. -/
@[reassoc]
theorem derivedGlobalSectionsModulesForget_naturality
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A ⟶ B) :
    (underlyingDerivedGroup X).map ((derivedGlobalSectionsModules X).map f) ≫
        (derivedGlobalSectionsModulesForget X).hom.app B =
      (derivedGlobalSectionsModulesForget X).hom.app A ≫
        (derivedModuleGlobalSections X).map f :=
  (derivedGlobalSectionsModulesForget X).hom.naturality f

/-- **The universal property that defines the identification of the two derived global
sections.** `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget` compares two right
derived functors of one functor, so composing it with the unit of the first returns the unit of
the second. -/
theorem globalSectionsModulesForgetUnit_comp_forget
    (Y : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (globalSectionsModulesForgetUnit X).app Y ≫
        (derivedGlobalSectionsModulesForget X).hom.app (DerivedCategory.Qh.obj Y) =
      (derivedModuleGlobalSectionsUnit X).app Y := by
  have := isRightDerivedFunctor_globalSectionsModulesForgetUnit X
  simp [derivedGlobalSectionsModulesForget]

/-- **The comparison of the forgetful functor with the localization, on the class of a
complex.** Mathlib's `CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` at the forgetful
functor from `Γ(C, O)`-modules to abelian groups, with the two comparisons of the quotient
functor with the localization cancelled. -/
theorem forgetDerivedFactors_quotient
    (K : CochainComplex
      (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    (underlyingDerivedGroup X).map
        ((DerivedCategory.quotientCompQhIso
          (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom.app
            K) ≫
      (Functor.mapDerivedCategoryFactors (forget₂ (ModuleCat.{u}
        (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u})).hom.app K =
    (Functor.mapDerivedCategoryFactorsh (forget₂ (ModuleCat.{u}
          (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u})).hom.app
        ((HomotopyCategory.quotient
          (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        (((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u}).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).hom.app
          (((forget₂
            (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Category.assoc]
  slice_rhs 4 5 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, Category.comp_id]

/-- **On the homotopy category the two routes to the abelian-group-valued global sections agree,
on the nose.** Taking module-valued global sections of a complex and then forgetting the scalars
is taking abelian-group-valued global sections, and the comparison of each with the quotient
functor turns that equality of functors into a commuting square — which holds definitionally, so
the second leg of the canonical map needs no further input on the homotopy category. -/
theorem forgetMapHomotopyCategoryFactors_comp
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    letI : (globalSectionsModules X).Additive :=
      globalSectionsFunctor_additive.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    ((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u}).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((globalSectionsModules X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app H) ≫
      ((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u}).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
        (globalSectionsModulesComplex X H) =
    (Functor.mapHomotopyCategoryCompIso
        (eqToIso (globalSectionsModules_comp_forget₂ X)) (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) ≫
      (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app H) :=
  rfl

end AlgebraicGeometry.RingedSite

end
