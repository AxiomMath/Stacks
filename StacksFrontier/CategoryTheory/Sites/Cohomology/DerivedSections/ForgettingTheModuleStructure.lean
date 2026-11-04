module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Localization.HomBijective
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting the module structure in unbounded derived sections on a site

Let `(C, O)` be a site with a sheaf of rings and let `K` be an object of the unbounded derived
category `D(O)`. Writing `K_ab` for the image of `K` under the forgetful functor to the
unbounded derived category of abelian sheaves, the canonical comparisons

`RΓ(C, K) ⟶ RΓ(C, K_ab)` and `RΓ(U, K) ⟶ RΓ(U, K_ab)`

are isomorphisms in `D(Ab)`, for every object `U` of `C`.

The comparisons are the maps of right derived functors induced, through the universal property
of `RΓ(C, -)` resp. `RΓ(U, -)` on `D(O)`, by the identity identification of the two underived
sections functors. They are invertible because they are invertible on K-injective complexes of
`O`-modules, and those suffice because sheaves of `O`-modules form a Grothendieck abelian
category.

## Main definitions

* `Stacks.Cohomology.ForgetModule.underlyingDerivedSheaf`: the functor `D(O) ⥤ D(Ab_C)`
  forgetting the module structure.
* `Stacks.Cohomology.ForgetModule.derivedAbelianGlobalSections`,
  `Stacks.Cohomology.ForgetModule.derivedAbelianSections`: unbounded derived global sections,
  and derived sections over an object, of abelian sheaves.
* `Stacks.Cohomology.ForgetModule.globalSectionsForgetComparison`,
  `Stacks.Cohomology.ForgetModule.sectionsForgetComparison`: the canonical comparisons.

## Main results

* `Stacks.Cohomology.ForgetModule.globalSectionsForgetComparison_isIso` (Tag 0D6J, part (1)):
  the comparison for global sections is an isomorphism.
* `Stacks.Cohomology.ForgetModule.sectionsForgetComparison_isIso` (Tag 0D6J, part (2)): the
  comparison for sections over an object is an isomorphism.

## Implementation notes

The K-injective criterion reduces both claims to the invertibility, at the underlying abelian
complex of a K-injective complex `I` of `O`-modules, of the derived unit of the abelian sections
functor. That is where the content sits: extension of scalars `- ⊗_ℤ O`, the left adjoint of
`SheafOfModules.toSheaf` supplied by `ModuleSheafCohomology.tensorSheafHomIso`, is exact on
sectionwise torsion-free abelian sheaves, so morphisms out of a bounded-above sectionwise
torsion-free complex into the underlying abelian complex of `I` are already computed in the
homotopy category. That is
`Stacks.Cohomology.ForgetModule.toSheaf_localization_map_bijective_of_isLE`, proved along with
the extension of scalars it needs in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers`. Both
sections functors are corepresented by such a sheaf — by
`ModuleSheafCohomology.evaluationRepresentation` over an object, and by
`ModuleSheafCohomology.globalSectionsRepresentation` globally — so
`Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable` applies.

Global sections of abelian sheaves are taken in Mathlib's spelling `Sheaf.Γ`, the right adjoint
of the constant sheaf functor, because that is the spelling in which
`ModuleSheafCohomology.globalSectionsRepresentation` corepresents them. This is *not* the
spelling `AlgebraicGeometry.RingedSite.abelianGlobalSectionsFunctor` of
`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections`; the two underived functors are
isomorphic, both being the limit of the underlying presheaf, but no bridge between them is
available in the library, so the global clause here is stated for the `Sheaf.Γ` spelling and the
module side is `SheafOfModules.toSheaf O ⋙ Sheaf.Γ`. Sections over an object are the library's
`Stacks.Cohomology.Localization.sectionsOverObject`, which is the composite of forgetting the
module structure with evaluation on the nose.

This is the counterpart on a general site of
`Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetComparison_isIso`, which is Tag 0D5Y for
a ringed space; the argument is the same, and the part of it that is not about the site — the
exactness of extension of scalars and the resulting homotopy-category computation of morphisms —
is shared with that development through `ForgetModuleHelpers`, which states it for an arbitrary
small site. Nothing else of the ringed-space development is reused here.

Part (3) of Tag 0D6J, about the unbounded derived direct image along a morphism of ringed
sites, is `Stacks.Cohomology.ForgetModule.pushforwardForgetComparison_isIso`. It reduces to the
invertibility of the abelian `Rf_*` unit at the underlying abelian complex of a K-injective
complex of modules, and that follows from `qh_map_bijective_single_of_isKInjective` below — the
corepresentability input of parts (1) and (2) — applied over each object of the source site.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0D5Y](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ZeroObject

namespace Stacks.Cohomology.ForgetModule

universe u

attribute [local instance] HasDerivedCategory.standard

section Machinery

open ModuleSheafCohomology

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Morphisms out of a sectionwise torsion-free single complex into the underlying abelian
complex of a K-injective complex of modules are computed in the homotopy category**, in every
shift. This is `toSheaf_localization_map_bijective_of_isLE` specialised to a single complex and
transported across the shift, and it is the corepresentability input of
`unit_isIso_of_isKInjective`. -/
theorem qh_map_bijective_single_of_isKInjective (O : Sheaf J RingCat.{u})
    (A₀ : Sheaf J AddCommGrpCat.{u})
    (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V))
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] (n : ℤ) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj A₀) ⟶
          (HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
            ((((SheafOfModules.toSheaf O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) :=
  DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)).mapIso
      (((SheafOfModules.toSheaf O).mapCochainComplexShiftIso n).app I))
    (toSheaf_localization_map_bijective_of_isLE J O
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj A₀) 0
      (torsionFree_single J A₀ hA₀ 0) (I⟦n⟧))

/-- **The derived unit of a corepresented sections functor is invertible at the underlying
abelian complex of a K-injective complex of modules.** The corepresenting sheaf is assumed
sectionwise torsion free, which is what makes extension of scalars exact on a resolution by
such sheaves. -/
private lemma unit_isIso_of_isKInjective (O : Sheaf J RingCat.{u})
    (T : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) [T.Additive]
    (A₀ : Sheaf J AddCommGrpCat.{u})
    (e : preadditiveCoyoneda.obj (op A₀) ≅ T)
    (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V))
    (RT : DerivedCategory (Sheaf J AddCommGrpCat.{u}) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso (α.app (((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ)).obj I))) :=
  (NatTrans.isIso_app_iff_of_iso α
    (((SheafOfModules.toSheaf O).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I)).mp
    (DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable T A₀ e RT α _
      (qh_map_bijective_single_of_isKInjective J O A₀ hA₀ I))

end Machinery

section Statements

open ModuleSheafCohomology

variable (X : RingedSite.{u, u, u})

/-- Forgetting the module structure on an object of the unbounded derived category. -/
abbrev underlyingDerivedSheaf :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (Sheaf X.J AddCommGrpCat.{u}) :=
  (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategory

/-! ### Sections over an object of the site -/

/-- Unbounded derived sections over an object of the site, for abelian sheaves. -/
abbrev derivedAbelianSections (U : X.C) :
    DerivedCategory (Sheaf X.J AddCommGrpCat.{u}) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  DerivedLowerShriek.derivedAbelianSections X.J U

/-- The unit of derived sections over an object, for abelian sheaves. -/
abbrev derivedAbelianSectionsUnit (U : X.C) :
    ((sheafSections X.J AddCommGrpCat.{u}).obj (op U)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianSections X U :=
  ((DerivedLowerShriek.alongFunctor_abelianSections X.J U).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- Ordinary sections over an object agree after forgetting the module structure. -/
def ordinarySectionsForgetIso (U : X.C) :
    Localization.sectionsOverObject X U ≅
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (sheafSections X.J AddCommGrpCat.{u}).obj (op U) :=
  Iso.refl _

/-- The canonical unit comparison for derived sections over an object after forgetting the
module structure. -/
def sectionsForgetUnit (U : X.C) :
    Localization.homotopySectionsOverObject X U ⟶
      DerivedCategory.Qh ⋙ (underlyingDerivedSheaf X ⋙ derivedAbelianSections X U) := by
  letI : (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
    ⟨by intros; rfl⟩
  exact
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (Localization.sectionsOverObject X U))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (ordinarySectionsForgetIso X U)
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          (sheafSections X.J AddCommGrpCat.{u}).obj (op U)))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (((sheafSections X.J AddCommGrpCat.{u}).obj (op U)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (derivedAbelianSectionsUnit X U) ≫
    Functor.whiskerRight
      (SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactorsh.inv
      (derivedAbelianSections X U)

/-- **The canonical map `RΓ(U, K) ⟶ RΓ(U, K_ab)`**, induced by `sectionsForgetUnit` through the
universal property of the right derived functor of sections over `U`. -/
def sectionsForgetComparison (U : X.C) :
    Localization.derivedSectionsOverObject X U ⟶
      underlyingDerivedSheaf X ⋙ derivedAbelianSections X U :=
  (Localization.derivedSectionsOverObject X U).rightDerivedDesc
    (ModuleSections.derivedSectionsOverObjectUnit X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    _ (sectionsForgetUnit X U)

/-- **Stacks 0D6J, part (2).** For every object `U` of the site, the canonical map
`RΓ(U, K) ⟶ RΓ(U, K_ab)` from unbounded derived sections of a sheaf of modules to derived
sections of the underlying abelian sheaf is an isomorphism, naturally in `K`. -/
@[stacks 0D6J "part (2): sections over an object of the site"]
theorem sectionsForgetComparison_isIso (U : X.C) :
    IsIso (sectionsForgetComparison X U) := by
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)
  let γ := sectionsForgetUnit X U
  have hγ : ∀ (I : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [I.IsKInjective],
      IsIso (γ.app (Q.obj I)) := by
    intro I _
    have := unit_isIso_of_isKInjective X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((sheafSections X.J AddCommGrpCat.{u}).obj (op U))
      ((presheafToSheaf X.J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free))
      (evaluationRepresentation X.J U).symm
      (isTorsionFree_sheafify X.J _ fun W => by
        show Module.IsTorsionFree ℤ (FreeAbelianGroup (W.unop ⟶ U))
        exact Module.Flat.isTorsionFree)
      (derivedAbelianSections X U) (derivedAbelianSectionsUnit X U) I
    dsimp only [γ, sectionsForgetUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (Localization.derivedSectionsOverObject X U)
    (ModuleSections.derivedSectionsOverObjectUnit X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ)) _ γ).mp
    (Localization.rightDerived_of_kInjectives (Localization.homotopySectionsOverObject X U)
      (underlyingDerivedSheaf X ⋙ derivedAbelianSections X U) γ hγ)

/-! ### Global sections of the site -/

/-- Global sections of abelian sheaves on the site, in Mathlib's spelling. -/
abbrev abelianGlobalSections : Sheaf X.J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Sheaf.Γ X.J AddCommGrpCat.{u}

/-- The global sections functor on abelian sheaves is additive. -/
instance abelianGlobalSections_additive : (abelianGlobalSections X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections of a sheaf of modules, with the module structure forgotten. -/
abbrev moduleGlobalSections :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ abelianGlobalSections X

/-- The global sections functor on sheaves of modules is additive. -/
instance moduleGlobalSections_additive : (moduleGlobalSections X).Additive :=
  inferInstanceAs
    ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      abelianGlobalSections X)).Additive

/-- Global sections of complexes of abelian sheaves, followed by localization. -/
abbrev homotopyAbelianGlobalSections :
    HomotopyCategory (Sheaf X.J AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (abelianGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Unbounded derived global sections `RΓ(C, -)` of abelian sheaves. -/
abbrev derivedAbelianGlobalSections :
    DerivedCategory (Sheaf X.J AddCommGrpCat.{u}) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (homotopyAbelianGlobalSections X).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- The unit of derived global sections of abelian sheaves. -/
abbrev derivedAbelianGlobalSectionsUnit :
    homotopyAbelianGlobalSections X ⟶
      DerivedCategory.Qh ⋙ derivedAbelianGlobalSections X :=
  (homotopyAbelianGlobalSections X).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- The canonical unit comparison for derived global sections after forgetting the module
structure. -/
def globalSectionsForgetUnit :
    ((moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ (underlyingDerivedSheaf X ⋙ derivedAbelianGlobalSections X) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (moduleGlobalSections X))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      ((abelianGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (derivedAbelianGlobalSectionsUnit X) ≫
    Functor.whiskerRight
      (SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactorsh.inv
      (derivedAbelianGlobalSections X)

/-- **The canonical map `RΓ(C, K) ⟶ RΓ(C, K_ab)`**, induced by `globalSectionsForgetUnit`
through the universal property of the right derived functor of global sections. -/
def globalSectionsForgetComparison :
    (((moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))) ⟶
      underlyingDerivedSheaf X ⋙ derivedAbelianGlobalSections X :=
  ((((moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))).rightDerivedDesc
    ((((moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    _ (globalSectionsForgetUnit X)

/-- **Stacks 0D6J, part (1).** The canonical map `RΓ(C, K) ⟶ RΓ(C, K_ab)` from unbounded
derived global sections of a sheaf of modules to derived global sections of the underlying
abelian sheaf is an isomorphism, naturally in `K`. -/
@[stacks 0D6J "part (1): global sections of the site"]
theorem globalSectionsForgetComparison_isIso :
    IsIso (globalSectionsForgetComparison X) := by
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)
  let γ := globalSectionsForgetUnit X
  have hγ : ∀ (I : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [I.IsKInjective],
      IsIso (γ.app (Q.obj I)) := by
    intro I _
    have := unit_isIso_of_isKInjective X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (abelianGlobalSections X)
      ((constantSheaf X.J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
      (globalSectionsRepresentation X.J).symm
      (isTorsionFree_sheafify X.J _ fun _ => by
        apply Module.IsTorsionFree.of_smul_eq_zero
        intro n x hx
        obtain h | h := mul_eq_zero.mp (congrArg ULift.down hx : (n * x.down : ℤ) = 0)
        · exact Or.inl h
        · exact Or.inr (ULift.ext _ _ h))
      (derivedAbelianGlobalSections X) (derivedAbelianGlobalSectionsUnit X) I
    dsimp only [γ, globalSectionsForgetUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (((moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
    (((moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (.up ℤ)) _ γ).mp
    (Localization.rightDerived_of_kInjectives
      ((moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (underlyingDerivedSheaf X ⋙ derivedAbelianGlobalSections X) γ hγ)

end Statements

end Stacks.Cohomology.ForgetModule

end
