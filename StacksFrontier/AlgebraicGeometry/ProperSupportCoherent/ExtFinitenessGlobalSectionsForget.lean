module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# `A`-linear derived global sections of a scheme, with the scalars forgotten

Let `A` be a commutative ring and let `f : X ⟶ Spec A` be a scheme over `A`. Two derived
global-sections functors on `D(𝒪_X)` with values in abelian groups are in play:

* `AlgebraicGeometry.derivedGlobalSectionsOver f : D(𝒪_X) ⥤ D(A)`, the `A`-linear one of
  [Stacks, Tag 0D5W], composed with the functor that forgetting the `A`-action induces on derived
  categories;
* `Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections` of the ringed *site* of `X` —
  the site of opens with the open-cover topology — which is the functor the identifications of
  [Stacks, Tag 08DK] are phrased with.

They agree. Both are right derived functors of the same functor on `K(𝒪_X)`: forgetting the
`A`-action of the global sections of a sheaf of `𝒪_X`-modules gives the abelian group of
compatible families of sections of the underlying abelian sheaf, because `⊤` is a terminal open
and a compatible family is therefore determined by its value there. Uniqueness of right derived
functors turns that into `derivedGlobalSectionsOverForgetIso`, and exactness of the forgetful
functor lets the identification be read on homology, which is `homologyZeroForgetNatIso` — the
form a consumer of [Stacks, Tag 08DK] over a base ring uses.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperSupportCoherent.abelianGlobalSectionsTopIso`: compatible
  families of sections of an abelian sheaf on a space are its sections over `⊤`.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.homotopyLinearSections`,
  `derivedLinearSections`, `derivedLinearSectionsUnit`: an `R`-linear sections functor on a
  ringed site read on the homotopy category, its total right derived functor and the unit, for
  an arbitrary ringed site and an arbitrary such functor.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.linearSectionsForgetUnit`: the comparison
  exhibiting that derived functor, with the scalars forgotten, as a candidate right derived
  functor of the abelian-group-valued global sections of the site.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.siteSections`: `A`-linear global sections of
  a scheme over `A`, written in the ringed-site spelling and with no derived category in its
  signature.

## Main results

* `Stacks.AlgebraicGeometry.ProperSupportCoherent.isRightDerivedFunctor_linearSectionsForgetUnit`
  and `derivedLinearSectionsForgetIso`: on an arbitrary ringed site, an `R`-linear derived
  sections functor with the scalars forgotten is derived global sections, as soon as the underived
  functors agree.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.siteSectionsForgetIso`: the underived
  comparison, `A`-linear global sections with the scalars forgotten are the abelian-group-valued
  global sections of the ringed site.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso`:
  **`A`-linear derived global sections, with the scalars forgotten, are the abelian-group-valued
  derived global sections of the ringed site of the space.**
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.homologyZeroForgetNatIso` and
  `homologyZeroForgetIso`: the same identification in degree zero, naturally in the object and
  objectwise.

## Implementation notes

The derived category is the standard model, activated as a local instance at a priority high
enough to displace the locally small model that arrives with the imports: the two sides of every
statement below are then functors between the same categories rather than between two models of
them. That priority has a cost which shapes the proofs: for a goal `HasDerivedCategory ?C` with
`?C` still a metavariable, `CategoryTheory.HasDerivedCategory.standard` is now tried first, and
it asks for `Abelian ?C`, which sends instance search through the colimit and sheafification
instances of every category in scope. So the two lemmas of
`Stacks.Cohomology.Localization` used in
`isRightDerivedFunctor_linearSectionsForgetUnit` are applied with their category arguments
`(C := …)` and `(H := …)` given by name; without that the elaboration of that proof does not
terminate inside the heartbeat budget, which is what the `(C := …)` annotations there are for.

The derived half of the comparison is carried out once, for an arbitrary ringed site `Z` and an
arbitrary `R`-linear sections functor on it, and only then instantiated at the scheme. That is
not merely for reuse: with `Z` a variable, the instances of
`SheafOfModules Z.ringSheaf` — Grothendieck abelianness above all — are synthesized generically
and once, whereas at the concrete `Stacks.SheafOfModules.ringedSite X.sheaf` each occurrence
re-runs a search through `CategoryTheory.sheafCompose` that the budget does not cover.

`AlgebraicGeometry.globalSectionsOver`, the `A`-linear global sections of
`StacksFrontier.AlgebraicGeometry.DerivedGlobalSections`, is declared under binders
`[HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]` which its body
does not use, so `globalSectionsOver f` carries two universe metavariables and two pending
instance goals and `(globalSectionsOver f).Additive` is not synthesizable — which is exactly what
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` asks for below. Hence `siteSections`, the
same functor with no derived category in its signature. This is the situation already described
in the implementation notes of
`StacksFrontier.AlgebraicGeometry.DerivedAcyclic.HypercohomologyOverABase`, whose assembly this file
repeats with the forgetful functor in place of restriction of scalars.

`X.Modules`, `SheafOfModules X.ringCatSheaf` and
`SheafOfModules (Stacks.SheafOfModules.ringedSite X.sheaf).ringSheaf` are definitionally equal
but carry separately declared instances which instance search does not cross. Every declaration
below therefore stays in the ringed-site spelling, which is the one
`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections` is stated at, and the crossing to
`AlgebraicGeometry.derivedGlobalSectionsOver` happens only in the declared type of
`derivedGlobalSectionsOverForgetIso`, where it is a definitional unfolding — `siteSections f` is
`AlgebraicGeometry.globalSectionsOver f` by `rfl`, hence so are the homotopy-category functor and
the total right derived functor built from it — and not an instance search.

The underived comparison needs no sheaf condition: global sections on a ringed site are taken as
`AlgebraicGeometry.RingedSite.abelianGlobalSectionsFunctor`, the compatible families of
[Stacks, Tag 0A8Z], and on the site of opens of a space a compatible family is determined by its
value at the terminal open `⊤`, every arrow of `(Opens X)ᵒᵖ` out of `op ⊤` being the unique one.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Compatible families of sections are the sections over the whole space -/

section Terminal

variable {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)

/-- **Compatible families of sections of an abelian sheaf on a space are its sections over the
whole space.** Global sections on a ringed site are the compatible families of
[Stacks, Tag 0A8Z]; on the site of opens the open `⊤` is terminal, so a compatible family is its
value at `op ⊤`, and conversely a section over `⊤` restricts to a compatible family because every
arrow of `(Opens X)ᵒᵖ` out of `op ⊤` is the unique one. -/
def abelianGlobalSectionsTopIso :
    _root_.AlgebraicGeometry.RingedSite.abelianGlobalSectionsFunctor
        (Stacks.SheafOfModules.ringedSite Rc) ≅
      (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents
    (fun F =>
      { hom := AddCommGrpCat.ofHom
          { toFun := fun s => s.val (op ⊤)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        inv := AddCommGrpCat.ofHom
          { toFun := fun x =>
              ⟨fun U => F.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op x, by
                intro U V g
                calc (F.obj.map g) ((F.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op) x)
                    = (F.obj.map ((homOfLE (le_top : U.unop ≤ ⊤)).op ≫ g)) x := by
                      rw [F.obj.map_comp]; rfl
                  _ = (F.obj.map (homOfLE (le_top : V.unop ≤ ⊤)).op) x := by
                      rw [show (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ g = (homOfLE le_top).op from
                        Quiver.Hom.unop_inj (Subsingleton.elim _ _)]⟩
            map_zero' := by ext U; exact map_zero _
            map_add' := by intros; ext U; exact map_add _ _ _ }
        hom_inv_id := by
          ext s
          refine Subtype.ext (funext fun U => ?_)
          exact s.property (homOfLE (le_top : U.unop ≤ ⊤)).op
        inv_hom_id := by
          ext x
          change (F.obj.map (homOfLE (le_top : (⊤ : Opens Y) ≤ ⊤)).op) x = x
          rw [show (homOfLE (le_top : (⊤ : Opens Y) ≤ ⊤)).op = 𝟙 (op (⊤ : Opens Y)) from
            Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]
          rfl })
    (fun _ => by ext s; rfl)

end Terminal

/-! ### Derived global sections of a ringed site, with the scalars forgotten -/

section Generic

variable {Z : _root_.AlgebraicGeometry.RingedSite.{u, u, u}} {R : Type u} [CommRing R]
  (S : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⥤ ModuleCat.{u} R)
  [S.Additive]

/-- An `R`-linear sections functor read on the homotopy category of cochain complexes of
`O`-modules, with values in `D(R)`. -/
abbrev homotopyLinearSections :
    HomotopyCategory (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The unbounded total right derived functor of an `R`-linear sections functor. -/
abbrev derivedLinearSections :
    DerivedCategory (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  (homotopyLinearSections S).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))

/-- The unit comparing the `R`-module of sections of a complex with its derived sections. -/
abbrev derivedLinearSectionsUnit :
    homotopyLinearSections S ⟶ DerivedCategory.Qh ⋙ derivedLinearSections S :=
  (homotopyLinearSections S).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))

variable (e : S ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅ moduleGlobalSections Z)

/-- The comparison exhibiting an `R`-linear derived sections functor, with the scalars
forgotten, as a candidate right derived functor of the abelian-group-valued global sections of
the site: the underived comparison `e` read degreewise, the comparison of the exact forgetful
functor with the localization, and the unit of the `R`-linear derived functor. -/
def linearSectionsForgetUnit :
    homotopyModuleGlobalSections Z ⟶
      DerivedCategory.Qh ⋙ (derivedLinearSections S ⋙
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (F := S) (G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (H := moduleGlobalSections Z) e (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (S.mapHomotopyCategory (ComplexShape.up ℤ))
        (Functor.mapDerivedCategoryFactorsh
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv ≫
      Functor.whiskerRight (derivedLinearSectionsUnit S)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory

/-- **An `R`-linear derived sections functor, with the scalars forgotten, is a right derived
functor of the abelian-group-valued global sections of the site.** Both the comparison coming
from the exact forgetful functor and the unit of the `R`-linear derived functor are invertible on
a K-injective complex, so the recognition criterion of [Stacks, Tag 070K] applies. -/
theorem isRightDerivedFunctor_linearSectionsForgetUnit :
    (derivedLinearSections S ⋙
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory).IsRightDerivedFunctor
      (linearSectionsForgetUnit S e)
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
    (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (H := DerivedCategory AddCommGrpCat.{u})
  intro I _
  have : IsIso ((derivedLinearSectionsUnit S).app
      ((HomotopyCategory.quotient
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (H := DerivedCategory (ModuleCat.{u} R))
      (homotopyLinearSections S) (derivedLinearSections S) (derivedLinearSectionsUnit S) I
  dsimp only [linearSectionsForgetUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- **An `R`-linear derived sections functor, with the scalars forgotten, is derived global
sections of the ringed site**, as soon as the underived functors agree. Both are right derived
functors of the abelian-group-valued global sections, so they agree by the universal property of
a right derived functor. -/
def derivedLinearSectionsForgetIso :
    derivedLinearSections S ⋙
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory ≅
      derivedModuleGlobalSections Z :=
  haveI := isRightDerivedFunctor_linearSectionsForgetUnit S e
  Functor.rightDerivedUnique _ _ (linearSectionsForgetUnit S e)
    (derivedModuleGlobalSectionsUnit Z)
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))

end Generic

/-! ### The underived comparison -/

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- **`A`-linear global sections of a scheme over `A`**, in the spelling of the ringed site of
its space: sections over `⊤` of a sheaf of `𝒪_X`-modules, regarded as an `A`-module by
restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`. It is
`AlgebraicGeometry.globalSectionsOver f`, with no derived category in its signature. -/
abbrev siteSections :
    _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O) ⥤
      ModuleCat.{u} A :=
  _root_.SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O) (op ⊤) ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)

/-- `A`-linear global sections is an additive functor; addition of sections of a sheaf of
modules is computed open by open. -/
instance siteSections_additive : (siteSections f).Additive where
  map_add := rfl

/-- **The underived comparison.** Forgetting the `A`-action of the `A`-linear global sections of
a sheaf of `𝒪_X`-modules gives the abelian-group-valued global sections of the ringed site of
`X`: restriction of scalars does not change the underlying abelian group, sections over an open
of a sheaf of modules are the sections of the underlying abelian sheaf
(`Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso`), and sections over `⊤` are the
compatible families (`abelianGlobalSectionsTopIso`). -/
def siteSectionsForgetIso :
    siteSections f ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ≅
      moduleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) :=
  Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O) ⊤ ≪≫
    Functor.isoWhiskerLeft
      (_root_.SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))
      (abelianGlobalSectionsTopIso X.sheaf).symm

/-! ### The derived comparison -/

/-- **`A`-linear derived global sections, with the scalars forgotten, are the
abelian-group-valued derived global sections of the ringed site of the space.** This is
`derivedLinearSectionsForgetIso` at the `A`-linear global sections of `X`, read at
`AlgebraicGeometry.derivedGlobalSectionsOver`, which is the total right derived functor of the
same underived functor in the scheme API's spelling of sheaves of `𝒪_X`-modules. -/
def derivedGlobalSectionsOverForgetIso :
    derivedGlobalSectionsOver f ⋙
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory ≅
      derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) :=
  derivedLinearSectionsForgetIso (siteSections f) (siteSectionsForgetIso f)

/-! ### Degree zero -/

/-- **The identification in degree zero, naturally in the object.** The forgetful functor is
exact, so it commutes with homology on the derived category
(`Stacks.Homology.derivedHomologyIso`); composing that with
`derivedGlobalSectionsOverForgetIso` identifies the degree-zero cohomology `A`-module of
`A`-linear derived global sections, with its scalars forgotten, with the degree-zero
hypercohomology group of the ringed site. -/
def homologyZeroForgetNatIso :
    derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ≅
      derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0 :=
  Functor.isoWhiskerLeft (derivedGlobalSectionsOver f)
      (Stacks.Homology.derivedHomologyIso
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) 0).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedGlobalSectionsOverForgetIso f)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)

/-- **The identification in degree zero at an object**, which is the form a consumer holding a
hypercohomology group of the ringed site uses. -/
def homologyZeroForgetIso (E : DerivedCategory X.Modules) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((derivedGlobalSectionsOver f).obj E)) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf)).obj E) :=
  (homologyZeroForgetNatIso f).app E

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
