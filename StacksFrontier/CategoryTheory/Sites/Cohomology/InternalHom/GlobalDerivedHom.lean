module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# The global derived hom on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L` be objects of `D(O)`. Taking derived global
sections of the derived internal Hom produces the *global derived hom*

`RHom_O(K, L) = RΓ(C, RSheafHom(K, L))`,

an object of the derived category `D(Γ(C, O))` of modules over the ring of global sections of the
structure sheaf, whose degree-zero cohomology is the group of morphisms `K ⟶ L` in `D(O)`. It is
the object of the derived category through which the morphism and `Ext` groups of `D(O)` are
computed.

Forgetting the `Γ(C, O)`-action gives the same construction read in abelian groups, which is the
form in which the global derived hom receives the canonical map out of an ordinary Hom complex.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalDerivedHomModules`: the bifunctor `RHom_O(-, -)` with
  values in `D(Γ(C, O))`.
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModules`: derived global sections
  `RΓ(C, -) : D(O) ⥤ D(Γ(C, O))`.
* `AlgebraicGeometry.RingedSite.globalDerivedHom`: the same bifunctor with its scalars
  forgotten.
* `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit`: the comparison from the global
  sections of a complex to its derived global sections.
* `AlgebraicGeometry.RingedSite.sheafHomComplexUnit`: the comparison from the internal Hom
  complex of two complexes to the derived internal Hom of their classes.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`: the canonical map from the Hom
  complex of two complexes of `O`-modules to their global derived hom.

## Main results

* `AlgebraicGeometry.RingedSite.globalDerivedHomModulesDegreeZeroEquiv`: the degree-zero
  cohomology of `RHom_O(K, L)` is `Hom_{D(O)}(K, L)`.
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget` and
  `AlgebraicGeometry.RingedSite.globalDerivedHomForget`: forgetting the scalars identifies the
  two readings of `RΓ(C, -)` and of `RHom_O(-, -)`.

## Implementation notes

Global sections valued in `Γ(C, O)`-modules are
`Stacks.Cohomology.SiteModules.globalSectionsFunctor` of Stacks 071H, and `Γ(C, O)` is its
`Stacks.Cohomology.SiteModules.GlobalSectionRing`, the compatible families of sections of the
structure sheaf. Its composition with the forgetful functor to abelian groups is the
abelian-group-valued global sections of Stacks 0D6I *on the nose*
(`globalSectionsModules_comp_forget₂`, an equality of functors), which is
`Stacks.Cohomology.SiteModules.globalSectionsFunctorForget` read in abelian groups rather than in
types. The two derived functors are therefore identified by the universal property: the forgetful
functor is exact, so module-valued derived global sections followed by it is again a right
derived functor of the abelian-group-valued global sections, which is
`isRightDerivedFunctor_globalSectionsModulesForgetUnit`, proved by the K-injective criterion of
Stacks 07A5.

Both readings are kept because they are used for different things. The `D(Γ(C, O))`-valued one is
the object the source constructs. The abelian-group-valued one is what carries the canonical map
out of an ordinary Hom complex, because the identification of the global sections of the internal
Hom complex with the Hom complex (Stacks 0A8Z) is a statement about complexes of abelian groups.

The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` of `homComplexToGlobalDerivedHom` is the composite
of three comparisons: the global sections of the internal Hom complex are the Hom complex
(Stacks 0A8Z, the `globalSectionsIso` of
`AlgebraicGeometry.RingedSite.SheafHomComplex`), global sections map to derived global sections
(the unit of Stacks 0D6I), and the internal Hom complex maps to the derived internal Hom (the
augmentation of the target into its K-injective resolution, Stacks 0A97). The universe lift that
Stacks 0A8Z carries is undone by `AddEquiv.ulift`, which loses nothing.

The functoriality of the global derived hom along a morphism of ringed topoi, which the source
obtains from Remark 21.35.11, is not here: the internal half is the canonical map
`Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)` of Stacks 08JF
(`AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`), and taking global sections
of it needs `RΓ(C, M) ⟶ RΓ(C', Lh^* M)`, hence the identification `RΓ(C, Rh_* N) = RΓ(C', N)` of
Stacks 08J6 on the *unbounded* derived category and with its scalars kept;
`Stacks.Cohomology.Leray.derivedGlobalSectionsPushforwardIso` is that identification on `D⁺` and
read in abelian groups.

## References

* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The global derived hom -/

/-- The global derived hom with its scalars forgotten: `RΓ(C, RSheafHom(K, L))` read with the
abelian-group-valued derived global sections of Stacks 0D6I. It is
`AlgebraicGeometry.RingedSite.globalDerivedHomModules` composed with the forgetful functor, by
`AlgebraicGeometry.RingedSite.globalDerivedHomForget`, and it is the form in which the global
derived hom is a `D(ℤ)`-valued bifunctor. -/
def globalDerivedHom :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
        DerivedCategory AddCommGrpCat.{u} :=
  derivedSheafHomBifunctor X ⋙
    (Functor.whiskeringRight _ _ _).obj (derivedModuleGlobalSections X)

/-- The global derived hom of `K` and `L` is the abelian-group-valued derived global sections of
the derived internal Hom `RSheafHom(K, L)`. -/
theorem globalDerivedHom_obj_obj
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((globalDerivedHom X).obj (op K)).obj L =
      (derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) :=
  rfl

/-! ### The canonical map from the Hom complex -/

/-- A complex of abelian groups is isomorphic to its degreewise universe lift inside the same
universe. -/
def uliftComplexSelfIso (D : CochainComplex AddCommGrpCat.{u} ℤ) :
    (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj D ≅ D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => addEquivIsoAddCommGroupIso.hom (AddEquiv.ulift (α := D.X n))) (by
      intro i j _
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      rfl)

/-- **The comparison from global sections to derived global sections.** The class of the complex
of global sections of a complex of `O`-modules maps canonically to its derived global sections;
this is the unit of the derived functor of Stacks 0D6I, read through the identifications of the
localization with `Functor.mapHomologicalComplex`. It is invertible on a K-injective complex,
which is `Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso`. -/
def globalSectionsDerivedUnit
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj (globalSectionsComplex X H) ⟶
      (derivedModuleGlobalSections X).obj (DerivedCategory.Q.obj H) :=
  ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
      (globalSectionsComplex X H)).inv ≫
    DerivedCategory.Qh.map
        (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app H).inv ≫
      (derivedModuleGlobalSectionsUnit X).app
          ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) ≫
        (derivedModuleGlobalSections X).map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app H).hom

/-- **The comparison from the internal Hom complex to the derived internal Hom.** The class of
`SheafHom(F, G)` maps canonically to `RSheafHom(Q F, Q G)`: the internal Hom complex of the
augmentation of `G` into its chosen K-injective resolution, followed by the inverse of the
comparison of Stacks 0A97 with that resolution. -/
def sheafHomComplexUnit
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj (sheafHomComplex X F G).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
        (DerivedCategory.Q.obj G) :=
  DerivedCategory.Q.map (homMap X (𝟙 F) ((kInjectiveAugmentation X).app G)) ≫
    (derivedSheafHomResolutionComparison X F G).inv

/-- **The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)`.** The Hom complex of two complexes of
`O`-modules is the complex of global sections of their internal Hom complex (Stacks 0A8Z), which
maps to the global derived hom of their classes through the unit of derived global sections and
the comparison with the derived internal Hom. -/
def homComplexToGlobalDerivedHom
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj (F.HomComplex G) ⟶
      ((globalDerivedHom X).obj (op (DerivedCategory.Q.obj F))).obj
        (DerivedCategory.Q.obj G) :=
  DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
      (sheafHomComplex X F G).globalSectionsIso.inv) ≫
    globalSectionsDerivedUnit X (sheafHomComplex X F G).obj ≫
      (derivedModuleGlobalSections X).map (sheafHomComplexUnit X F G)

/-! ### Derived global sections valued in modules over the ring of global sections -/

/-- Global sections of a sheaf of `O`-modules as a module over the ring `Γ(C, O)` of global
sections of the structure sheaf, which is
`Stacks.Cohomology.SiteModules.globalSectionsFunctor` of Stacks 071H. -/
abbrev globalSectionsModules :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **Forgetting the scalars gives the abelian-group-valued global sections on the nose.** The
`Γ(C, O)`-module of compatible global sections of a sheaf of `O`-modules has as underlying
abelian group the compatible global sections of Stacks 0A8Z, by definition; this is the
`AddCommGrpCat`-valued form of `Stacks.Cohomology.SiteModules.globalSectionsFunctorForget`. -/
theorem globalSectionsModules_comp_forget₂ :
    globalSectionsModules X ⋙
        forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          AddCommGrpCat.{u} =
      moduleGlobalSections X :=
  rfl

/-- Global sections of complexes of `O`-modules, valued in `Γ(C, O)`-modules, followed by
localization at the quasi-isomorphisms. -/
abbrev homotopyGlobalSectionsModules :
    HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory
        (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  haveI : (globalSectionsModules X).Additive :=
    globalSectionsFunctor_additive.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  (globalSectionsModules X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **Derived global sections `RΓ(C, -) : D(O) ⥤ D(Γ(C, O))`**, valued in modules over the ring
of global sections of the structure sheaf. -/
abbrev derivedGlobalSectionsModules :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory
        (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (homotopyGlobalSectionsModules X).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- The unit comparing the `Γ(C, O)`-module of global sections of a complex with its derived
global sections. -/
abbrev derivedGlobalSectionsModulesUnit :
    homotopyGlobalSectionsModules X ⟶
      DerivedCategory.Qh ⋙ derivedGlobalSectionsModules X :=
  (homotopyGlobalSectionsModules X).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- Forgetting the `Γ(C, O)`-action, on derived categories. It is exact, being the forgetful
functor of modules over a ring. -/
abbrev underlyingDerivedGroup :
    DerivedCategory
        (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    AddCommGrpCat.{u}).mapDerivedCategory

/-- The unit exhibiting module-valued derived global sections, followed by forgetting the
scalars, as a right derived functor of abelian-group-valued global sections. -/
def globalSectionsModulesForgetUnit :
    homotopyModuleGlobalSections X ⟶
      DerivedCategory.Qh ⋙ (derivedGlobalSectionsModules X ⋙ underlyingDerivedGroup X) :=
  haveI : (globalSectionsModules X).Additive :=
    globalSectionsFunctor_additive.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (F := globalSectionsModules X)
      (G := forget₂
        (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        AddCommGrpCat.{u})
      (H := moduleGlobalSections X)
      (eqToIso (globalSectionsModules_comp_forget₂ X))
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((globalSectionsModules X).mapHomotopyCategory (ComplexShape.up ℤ))
        (Functor.mapDerivedCategoryFactorsh
          (forget₂ (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            AddCommGrpCat.{u})).inv ≫
      Functor.whiskerRight (derivedGlobalSectionsModulesUnit X) (underlyingDerivedGroup X)

/-- **Module-valued derived global sections, with the scalars forgotten, is a right derived
functor of abelian-group-valued global sections.** Both the comparison coming from the exact
forgetful functor and the unit of the module-valued derived functor are invertible on a
K-injective complex, so the criterion of Stacks 07A5 applies. -/
theorem isRightDerivedFunctor_globalSectionsModulesForgetUnit :
    (derivedGlobalSectionsModules X ⋙ underlyingDerivedGroup X).IsRightDerivedFunctor
      (globalSectionsModulesForgetUnit X)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I _
  have h : IsIso ((derivedGlobalSectionsModulesUnit X).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (homotopyGlobalSectionsModules X) (derivedGlobalSectionsModules X)
      (derivedGlobalSectionsModulesUnit X) I
  have _ := h
  dsimp only [globalSectionsModulesForgetUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- **`RΓ(C, -)` with its scalars forgotten is the abelian-group-valued `RΓ(C, -)`.** Both are
right derived functors of the same functor on `K(O)`, the underived ones agreeing on the nose by
`AlgebraicGeometry.RingedSite.globalSectionsModules_comp_forget₂`, so they agree by the universal
property. -/
def derivedGlobalSectionsModulesForget :
    derivedGlobalSectionsModules X ⋙ underlyingDerivedGroup X ≅ derivedModuleGlobalSections X :=
  haveI := isRightDerivedFunctor_globalSectionsModulesForgetUnit X
  Functor.rightDerivedUnique _ _ (globalSectionsModulesForgetUnit X)
    (derivedModuleGlobalSectionsUnit X)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-! ### The global derived hom in `D(Γ(C, O))` -/

/-- **Stacks 0B6E.** *Applying the construction of the internal hom in the derived category we
get the object* `RHom_O(K, L) = RΓ(C, RHom(K, L))` *in* `D(Γ(C, O))`: the derived internal Hom of
two objects of `D(O)`, followed by derived global sections valued in modules over the ring of
global sections of the structure sheaf. -/
@[stacks 0B6E "the global derived hom RHom_O(K, L) = RΓ(C, RHom(K, L)) in D(Γ(C, O))"]
def globalDerivedHomModules :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
        DerivedCategory
          (ModuleCat.{u} (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  derivedSheafHomBifunctor X ⋙
    (Functor.whiskeringRight _ _ _).obj (derivedGlobalSectionsModules X)

/-- **The global derived hom of `D(Γ(C, O))`, with its scalars forgotten, is the
`AddCommGrpCat`-valued one**, naturally in the covariant variable. -/
def globalDerivedHomForget
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (globalDerivedHomModules X).obj (op K) ⋙ underlyingDerivedGroup X ≅
      (globalDerivedHom X).obj (op K) :=
  Functor.isoWhiskerLeft ((derivedSheafHomBifunctor X).obj (op K))
    (derivedGlobalSectionsModulesForget X)

/-- The global derived hom of `D(Γ(C, O))` at a pair of objects, with its scalars forgotten. -/
def globalDerivedHomForgetApp
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (underlyingDerivedGroup X).obj (((globalDerivedHomModules X).obj (op K)).obj L) ≅
      ((globalDerivedHom X).obj (op K)).obj L :=
  (globalDerivedHomForget X K).app L

/-! ### The cohomology of the global derived hom -/

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 0B6E, the cohomology of the global derived hom.** The degree-zero cohomology of
`RHom_O(K, L)` is the group of morphisms `K ⟶ L` in `D(O)`. This is Stacks 08JA, which is the
statement the source cites for the cohomology modules of the global derived hom, transported to
`RHom_O(K, L)` of `D(Γ(C, O))` along
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsModulesForget`; the cohomology is read on the
underlying complex of abelian groups, as Stacks 08JA states it. -/
@[stacks 0B6E "the degree-zero cohomology of RHom_O(K, L) is Hom_{D(O)}(K, L)"]
def globalDerivedHomModulesDegreeZeroEquiv
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((underlyingDerivedGroup X).obj
          (((globalDerivedHomModules X).obj (op K)).obj L)) : Type u) ≃+ (K ⟶ L) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      (globalDerivedHomForgetApp X K L)).addCommGroupIsoToAddEquiv).trans
    (derivedSheafHomGlobalSectionsEquiv X K L)

end AlgebraicGeometry.RingedSite

end
