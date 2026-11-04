module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleMap

/-!
# The canonical map of Stacks 0CS6 over `Γ(C, O)` forgets to the one in `D(ℤ)`

Let `(C, O)` be a ringed site and let `F`, `G` be complexes of `O`-modules. Stacks 0CS6 asserts a
canonical map `Hom^•_{Comp^dg(O)}(F, G) ⟶ RHom_O(F, G)` in `D(R)` for a ring `R` with a sheaf of
commutative `R`-algebra structures on `O`.
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules` is that map over the universal
such ring `Γ(C, O)`, and `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is the same
composite read in `D(ℤ)`.

This file proves that the first forgets to the second: forgetting the `Γ(C, O)`-action of the
module-valued canonical map, and identifying its source and target with those of the
`D(ℤ)`-valued one, returns the `D(ℤ)`-valued one. So the two maps are the same map, and a
statement about either is a statement about both — which is what lets the registrations of
Stacks 0CS6 be read at the source's `D(R)` instead of at `R = ℤ`.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalSectionsForgetComplexIso`: forgetting the scalars of the
  `Γ(C, O)`-module-valued complex of global sections gives the abelian-group-valued one, as an
  explicit isomorphism of complexes.
* `AlgebraicGeometry.RingedSite.globalSectionsForgetDerivedIso`: the same comparison in the
  derived category, through `CategoryTheory.Functor.mapDerivedCategoryFactors`.
* `AlgebraicGeometry.RingedSite.globalDerivedHomModulesObjIso` and
  `AlgebraicGeometry.RingedSite.globalDerivedHomObjIso`: the global derived hom of Stacks 0B6E at
  a pair of objects is derived global sections of the derived internal Hom, as an explicit
  isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules_forget`: **the canonical map
  of Stacks 0CS6 over `Γ(C, O)` forgets to the canonical map in `D(ℤ)`.**
* `AlgebraicGeometry.RingedSite.globalSectionsModulesDerivedUnit_forget`: its second leg — the
  unit of derived global sections over `Γ(C, O)`, with its scalars forgotten, is the
  abelian-group-valued unit.
* `AlgebraicGeometry.RingedSite.homComplexForgetComparison` and
  `AlgebraicGeometry.RingedSite.homComplexModulesDerivedForgetIso_inv_comp`: its first leg — the
  identification of Stacks 0A8Z over `Γ(C, O)`, with its scalars forgotten, is the
  abelian-group-valued identification composed with the universe lift.

## Implementation notes

*Why every junction is an explicit isomorphism.* Three pairs of objects occurring here are equal
by `rfl` and not syntactically: the abelian-group-valued complex of global sections
`AlgebraicGeometry.RingedSite.globalSectionsComplex`, which takes global sections of the
underlying complex of abelian sheaves, versus the forgetful image of
`AlgebraicGeometry.RingedSite.globalSectionsModulesComplex`, which is
`CategoryTheory.Functor.mapHomologicalComplex` of the forgetful functor; and the global derived
hom of Stacks 0B6E at a pair of objects, in either of its two readings, versus derived global
sections of the derived internal Hom, which differ by the whiskering that builds the bifunctor.
Each equality needs a semireducible definition unfolded, so a composite passing through both
spellings of a pair is not type-correct at `implicit` transparency, and every tactic rewriting
under that transparency — `simp`, and `rw` with a pattern carrying metavariables, including
`Category.assoc` — refuses to fire on it, reporting that the pattern does not occur.

The remedy, used throughout, is to install each such equality as a named isomorphism whose
declared type mentions both spellings, and to carry that isomorphism in the statements. The
isomorphisms are then explicit where the composites join, each statement is type-correct as
written, and the rewriting is ordinary. `AlgebraicGeometry.RingedSite.globalDerivedHomObjIso` and
`AlgebraicGeometry.RingedSite.globalDerivedHomModulesObjIso` are the identity of their object
spelled at the two types; `AlgebraicGeometry.RingedSite.globalSectionsForgetComplexIso` is the
degreewise identity, the content being that both differentials are the forgetful image of the
differential of the complex of modules. The handful of steps that *cross* a junction — pushing
such an isomorphism down to an identity — are the only ones proved in term mode rather than by
`rw`, since term elaboration works at default transparency.

*The second leg* is the universal property of the right derived functor. Composing the unit of
module-valued derived global sections with
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget` returns the
abelian-group-valued unit
(`AlgebraicGeometry.RingedSite.globalSectionsModulesForgetUnit_comp_forget`), and the two
comparisons of the localization with `CategoryTheory.Functor.mapHomologicalComplex` that the
universal property has to be fed through are
`AlgebraicGeometry.RingedSite.forgetDerivedFactors_quotient`,
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` read at the forgetful functor of
modules, and `AlgebraicGeometry.RingedSite.forgetMapHomotopyCategoryFactors_comp`.

*The third leg* is the naturality of
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget`, which is
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget_naturality`.

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

/-! ### Comparing the two readings of the complex of global sections -/

/-- **Forgetting the scalars of the `Γ(C, O)`-module-valued global sections of a complex gives
the abelian-group-valued ones.** In each degree both are the compatible global sections of the
underlying sheaf of abelian groups, and both differentials are the forgetful image of the
differential of the complex of modules; this is that equality as an explicit isomorphism of
complexes, so that a composite through both readings is type-correct as written. -/
def globalSectionsForgetComplexIso
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (globalSectionsModulesComplex X H) ≅ globalSectionsComplex X H :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    simp only [Iso.refl_hom]
    rfl)

/-- The comparison of the two readings is the identity, read in the derived category. -/
theorem Q_map_globalSectionsForgetComplexIso_hom
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.map (globalSectionsForgetComplexIso X H).hom =
      𝟙 (DerivedCategory.Q.obj (((forget₂ (ModuleCat.{u}
          (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (globalSectionsModulesComplex X H))) :=
  DerivedCategory.Q.map_id _

/-- **The class of the `Γ(C, O)`-module-valued complex of global sections, with its scalars
forgotten, is the class of the abelian-group-valued one.** The forgetful functor is exact, so it
commutes with the localization
(`CategoryTheory.Functor.mapDerivedCategoryFactors`); the resulting complex of abelian groups is
the one of Stacks 0A8Z by `AlgebraicGeometry.RingedSite.globalSectionsForgetComplexIso`. -/
def globalSectionsForgetDerivedIso
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (underlyingDerivedGroup X).obj
        (DerivedCategory.Q.obj (globalSectionsModulesComplex X H)) ≅
      DerivedCategory.Q.obj (globalSectionsComplex X H) :=
  (Functor.mapDerivedCategoryFactors (forget₂ (ModuleCat.{u}
      (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      AddCommGrpCat.{u})).app (globalSectionsModulesComplex X H) ≪≫
    DerivedCategory.Q.mapIso (globalSectionsForgetComplexIso X H)

/-- The comparison in the derived category is the one coming from the exactness of the forgetful
functor: the degreewise comparison it is composed with is the identity. -/
theorem globalSectionsForgetDerivedIso_hom
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (globalSectionsForgetDerivedIso X H).hom =
      (Functor.mapDerivedCategoryFactors (forget₂ (ModuleCat.{u}
        (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u})).hom.app
          (globalSectionsModulesComplex X H) :=
  (congrArg (fun z => (Functor.mapDerivedCategoryFactors (forget₂ (ModuleCat.{u}
        (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u})).hom.app
          (globalSectionsModulesComplex X H) ≫ z)
      (Q_map_globalSectionsForgetComplexIso_hom X H)).trans (Category.comp_id _)

/-! ### The second leg: the unit of derived global sections -/

/-- **The unit of module-valued derived global sections, with its scalars forgotten, is the
abelian-group-valued unit** — read through the two comparisons of the localization that
`AlgebraicGeometry.RingedSite.globalSectionsModulesForgetUnit` is built from. This is the
universal property
`AlgebraicGeometry.RingedSite.globalSectionsModulesForgetUnit_comp_forget` with those two
comparisons moved to the other side. -/
@[reassoc]
theorem derivedGlobalSectionsModulesUnit_comp_forget
    (Y : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (underlyingDerivedGroup X).map ((derivedGlobalSectionsModulesUnit X).app Y) ≫
        (derivedGlobalSectionsModulesForget X).hom.app (DerivedCategory.Qh.obj Y) =
      (Functor.mapDerivedCategoryFactorsh (forget₂ (ModuleCat.{u}
            (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              AddCommGrpCat.{u})).hom.app
          (((globalSectionsModules X).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
              (eqToIso (globalSectionsModules_comp_forget₂ X)) (ComplexShape.up ℤ)).hom.app Y) ≫
          (derivedModuleGlobalSectionsUnit X).app Y := by
  rw [← globalSectionsModulesForgetUnit_comp_forget X Y]
  dsimp only [globalSectionsModulesForgetUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp

/-- The naturality of the comparison of the forgetful functor with the localization, stated at
the objects at which it is used so that the two readings of a homotopy category of complexes do
not have to be unified by the rewriting. -/
@[reassoc]
theorem mapDerivedCategoryFactorsh_hom_naturality'
    (A B : HomotopyCategory
      (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ))
    (g : A ⟶ B) :
    (underlyingDerivedGroup X).map (DerivedCategory.Qh.map g) ≫
        (Functor.mapDerivedCategoryFactorsh (forget₂ (ModuleCat.{u}
          (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u})).hom.app B =
      (Functor.mapDerivedCategoryFactorsh (forget₂ (ModuleCat.{u}
            (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              AddCommGrpCat.{u})).hom.app A ≫
        DerivedCategory.Qh.map (((forget₂ (ModuleCat.{u}
          (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u}).mapHomotopyCategory (ComplexShape.up ℤ)).map g) :=
  (Functor.mapDerivedCategoryFactorsh _).hom.naturality g

/-- **On the homotopy category the two routes to the abelian-group-valued global sections agree**,
with the comparison of the two readings of the complex of global sections carried explicitly.
This is `AlgebraicGeometry.RingedSite.forgetMapHomotopyCategoryFactors_comp` read backwards, and
like it it holds on the nose. -/
theorem forgetMapHomotopyCategoryFactors_inv_comp
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u}).mapHomotopyCategory (ComplexShape.up ℤ)).map
          (((globalSectionsModules X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).app H).inv ≫
        (Functor.mapHomotopyCategoryCompIso (eqToIso (globalSectionsModules_comp_forget₂ X))
            (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) =
      ((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u}).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
          (globalSectionsModulesComplex X H) ≫
        (HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
            (globalSectionsForgetComplexIso X H).hom ≫
          (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app H).inv :=
  rfl

/-- `AlgebraicGeometry.RingedSite.forgetDerivedFactors_quotient` with the comparison of the
quotient functor with the localization moved to the other side, which is the form in which the
second leg uses it. -/
@[reassoc]
theorem forgetDerivedFactors_quotient'
    (K : CochainComplex
      (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    (Functor.mapDerivedCategoryFactorsh (forget₂ (ModuleCat.{u}
            (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              AddCommGrpCat.{u})).hom.app
          ((HomotopyCategory.quotient
            (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map (((forget₂ (ModuleCat.{u}
          (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u}).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) =
      (underlyingDerivedGroup X).map (((DerivedCategory.quotientCompQhIso
            (ModuleCat.{u}
              (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).app K).hom) ≫
        (Functor.mapDerivedCategoryFactors (forget₂ (ModuleCat.{u}
            (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              AddCommGrpCat.{u})).hom.app K ≫
          ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
            (((forget₂ (ModuleCat.{u}
              (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).inv := by
  conv_rhs => rw [Iso.app_hom, ← Category.assoc, forgetDerivedFactors_quotient X K]
  simp

/-- The comparison of the two readings of the complex of global sections is the identity on the
homotopy category: this is the step that crosses the junction, so it is proved in term mode. -/
theorem quotient_map_globalSectionsForgetComplexIso_hom_comp
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
          (globalSectionsForgetComplexIso X H).hom ≫
        (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app H).inv =
      (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app H).inv :=
  (congrArg (· ≫ (((moduleGlobalSections X).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app H).inv)
      ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map_id _)).trans
    (Category.id_comp _)

/-- **The second leg of the canonical map forgets.** The comparison from the `Γ(C, O)`-module of
global sections of a complex to its derived global sections, with its scalars forgotten, is the
abelian-group-valued comparison of
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit`. -/
@[reassoc]
theorem globalSectionsModulesDerivedUnit_forget
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (underlyingDerivedGroup X).map (globalSectionsModulesDerivedUnit X H) ≫
        (derivedGlobalSectionsModulesForget X).hom.app (DerivedCategory.Q.obj H) =
      (globalSectionsForgetDerivedIso X H).hom ≫ globalSectionsDerivedUnit X H := by
  rw [globalSectionsModulesDerivedUnit, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, Category.assoc,
    derivedGlobalSectionsModulesForget_naturality,
    derivedGlobalSectionsModulesUnit_comp_forget_assoc,
    mapDerivedCategoryFactorsh_hom_naturality'_assoc X
      ((HomotopyCategory.quotient
        (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ)).obj (globalSectionsModulesComplex X H))
      (((globalSectionsModules X).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj H))
      (((globalSectionsModules X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app H).inv,
    ← Functor.map_comp_assoc, forgetMapHomotopyCategoryFactors_inv_comp,
    Functor.map_comp_assoc, forgetDerivedFactors_quotient'_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    quotient_map_globalSectionsForgetComplexIso_hom_comp, globalSectionsForgetDerivedIso_hom]
  rfl

/-! ### The third leg and the target of the canonical map -/

/-- **The `D(Γ(C, O))`-valued global derived hom of Stacks 0B6E at a pair of objects is derived
global sections of the derived internal Hom**, on the nose: the bifunctor is built by whiskering
the derived internal Hom with derived global sections. This is that equality as an explicit
isomorphism, so that a composite through both spellings is type-correct as written. -/
def globalDerivedHomModulesObjIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedGlobalSectionsModules X).obj (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((globalDerivedHomModules X).obj (op K)).obj L :=
  Iso.refl _

/-- **The `D(ℤ)`-valued global derived hom at a pair of objects is derived global sections of the
derived internal Hom**, on the nose; the companion of
`AlgebraicGeometry.RingedSite.globalDerivedHomModulesObjIso` with the scalars forgotten. -/
def globalDerivedHomObjIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedModuleGlobalSections X).obj (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((globalDerivedHom X).obj (op K)).obj L :=
  Iso.refl _

/-- **The third leg, at the target of the canonical map.** Forgetting the scalars of the global
derived hom is `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget` at the derived
internal Hom, with the two spellings of that object made explicit. -/
theorem globalDerivedHomForgetApp_hom
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (underlyingDerivedGroup X).map (globalDerivedHomModulesObjIso X K L).inv ≫
        (derivedGlobalSectionsModulesForget X).hom.app
            (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≫
          (globalDerivedHomObjIso X K L).hom =
      (globalDerivedHomForgetApp X K L).hom :=
  ((congrArg (fun z => z ≫ (derivedGlobalSectionsModulesForget X).hom.app
          (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≫ (globalDerivedHomObjIso X K L).hom)
        (CategoryTheory.Functor.map_id (underlyingDerivedGroup X) _)).trans
      (Category.id_comp _)).trans (Category.comp_id _)

variable {X}

/-! ### The first leg: the identification of Stacks 0A8Z -/

/-- **The first leg of the canonical map forgets, on complexes.** Forgetting the scalars of the
identification of Stacks 0A8Z over `Γ(C, O)`
(`AlgebraicGeometry.RingedSite.globalSectionsHomComplexModulesIso`) gives the abelian-group-valued
identification `AlgebraicGeometry.RingedSite.SheafHomComplex.globalSectionsIso` composed with the
universe lift. Both sides send a cochain to the global section of the internal Hom complex it
names, so the comparison is degreewise the identity. -/
theorem homComplexForgetComparison
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (globalSectionsHomComplexModulesIso F G).inv ≫
        (globalSectionsForgetComplexIso X (sheafHomComplex X F G).obj).hom =
      (homComplexModulesForgetIso F G).hom ≫
        (uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => rfl)

/-- **The first leg of the canonical map forgets, in the derived category.** The class of the
`Γ(C, O)`-module-valued Hom complex, with its scalars forgotten and identified with the class of
the Hom complex, maps to the class of the complex of global sections of the internal Hom complex
by the `D(ℤ)`-valued first leg of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`. -/
@[reassoc]
theorem homComplexModulesDerivedForgetIso_inv_comp
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (homComplexModulesDerivedForgetIso F G).inv ≫
        (underlyingDerivedGroup X).map (DerivedCategory.Q.map
            (globalSectionsHomComplexModulesIso F G).inv) ≫
          (globalSectionsForgetDerivedIso X (sheafHomComplex X F G).obj).hom =
      DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
        (sheafHomComplex X F G).globalSectionsIso.inv) := by
  rw [Iso.inv_comp_eq, homComplexModulesDerivedForgetIso, globalSectionsForgetDerivedIso,
    Iso.trans_hom, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.app_hom, Category.assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun z => (Functor.mapDerivedCategoryFactors (forget₂ (ModuleCat.{u}
      (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) AddCommGrpCat.{u})).hom.app
        ((compDGGlobalSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
          F G) ≫ DerivedCategory.Q.map z)
    (homComplexForgetComparison F G)

/-! ### The canonical map over `Γ(C, O)` forgets to the one in `D(ℤ)` -/

/-- The canonical map over `Γ(C, O)` with the two spellings of its target made explicit. -/
theorem homComplexToGlobalDerivedHomModules_eq
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.map (globalSectionsHomComplexModulesIso F G).inv ≫
        globalSectionsModulesDerivedUnit X (sheafHomComplex X F G).obj ≫
          (derivedGlobalSectionsModules X).map (sheafHomComplexUnit X F G) ≫
            (globalDerivedHomModulesObjIso X (DerivedCategory.Q.obj F)
              (DerivedCategory.Q.obj G)).hom =
      homComplexToGlobalDerivedHomModules F G :=
  congrArg (fun z => DerivedCategory.Q.map (globalSectionsHomComplexModulesIso F G).inv ≫
      globalSectionsModulesDerivedUnit X (sheafHomComplex X F G).obj ≫ z)
    (Category.comp_id ((derivedGlobalSectionsModules X).map (sheafHomComplexUnit X F G)))

/-- The canonical map in `D(ℤ)` with the two spellings of its target made explicit. The name
avoids `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_eq` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomLocalization`, which is
a different statement about the same map and which a file reading both this and the degree-`n`
chain would otherwise be unable to import. -/
theorem homComplexToGlobalDerivedHom_eq_objIso
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv) ≫
        globalSectionsDerivedUnit X (sheafHomComplex X F G).obj ≫
          (derivedModuleGlobalSections X).map (sheafHomComplexUnit X F G) ≫
            (globalDerivedHomObjIso X (DerivedCategory.Q.obj F)
              (DerivedCategory.Q.obj G)).hom =
      homComplexToGlobalDerivedHom X F G :=
  congrArg (fun z => DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
        (sheafHomComplex X F G).globalSectionsIso.inv) ≫
      globalSectionsDerivedUnit X (sheafHomComplex X F G).obj ≫ z)
    (Category.comp_id ((derivedModuleGlobalSections X).map (sheafHomComplexUnit X F G)))

/-- **Stacks 0CS6: the canonical map over `Γ(C, O)` forgets to the canonical map in `D(ℤ)`.**
Forgetting the `Γ(C, O)`-action of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules`, and identifying its source
with the class of the Hom complex
(`AlgebraicGeometry.RingedSite.homComplexModulesDerivedForgetIso`) and its target with the
`D(ℤ)`-valued global derived hom
(`AlgebraicGeometry.RingedSite.globalDerivedHomForgetApp`), gives
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`.

The two are therefore one map, read over two base rings; since every base ring of Stacks 0CS6
maps to `Γ(C, O)`, a statement about the module-valued map is a statement about the `D(ℤ)`-valued
one and conversely, leg by leg: the first leg is
`AlgebraicGeometry.RingedSite.homComplexModulesDerivedForgetIso_inv_comp`, the second
`AlgebraicGeometry.RingedSite.globalSectionsModulesDerivedUnit_forget`, and the third the
naturality `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget_naturality`. -/
theorem homComplexToGlobalDerivedHomModules_forget
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (homComplexModulesDerivedForgetIso F G).inv ≫
        (underlyingDerivedGroup X).map (homComplexToGlobalDerivedHomModules F G) ≫
          (globalDerivedHomForgetApp X (DerivedCategory.Q.obj F)
            (DerivedCategory.Q.obj G)).hom =
      homComplexToGlobalDerivedHom X F G := by
  rw [← homComplexToGlobalDerivedHomModules_eq, ← globalDerivedHomForgetApp_hom,
    ← homComplexToGlobalDerivedHom_eq_objIso]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc (underlyingDerivedGroup X)
      (globalDerivedHomModulesObjIso X (DerivedCategory.Q.obj F)
        (DerivedCategory.Q.obj G)).hom
      (globalDerivedHomModulesObjIso X (DerivedCategory.Q.obj F)
        (DerivedCategory.Q.obj G)).inv,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    derivedGlobalSectionsModulesForget_naturality_assoc,
    globalSectionsModulesDerivedUnit_forget_assoc,
    homComplexModulesDerivedForgetIso_inv_comp_assoc, CategoryTheory.Functor.map_comp,
    Category.assoc]

end AlgebraicGeometry.RingedSite

end
