module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.VanishingStatements
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Module-valued and abelian-valued crystalline cohomology agree

Fix a global crystalline situation at level `u`.  `SmallSite/ModuleCohomologyComparison.lean`
proves [Stacks, Tag 03FD] at the universes of the small crystalline site: deriving
`Γ(Cris(X/S), -)` after forgetting a sheaf of `𝒪_{X/S}`-modules to its underlying abelian sheaf
agrees with forgetting after deriving.  What that comparison is *about* is the composite functor
`toAbelianSheaf S ⋙ Γ`, and what the chapter's module-valued cohomology
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleCohomology` is the derived functor of is
`baseModuleGlobalSections S`, the `A`-module of compatible families of sections.  This file
identifies the two underived functors and draws the consequence:
`Crystalline.GlobalCrystallineSituation.SmallSite.VanishingTransfer03FD` holds, so by
`vanishing07MR_of_abelianVanishing07MR` the only thing still between the library and
[Stacks, Tag 07MR] is `AbelianVanishing07MR`, its abelian form.

## The identification of the two global sections functors

`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso` identifies the global sections of a
sheaf of modules with the maps out of the structure sheaf, but only when the modules have their
sections in the universe of the structure rings, which here they do not.  The identification used
instead runs through the corepresentation of the *abelian* global sections: morphisms out of the
constant sheaf on `ℤ` are morphisms out of the constant *presheaf* on `ℤ` by the sheafification
adjunction, and those are exactly the compatible families of sections, by evaluation at the
integer generator.  That is `constantIntegerHomSectionsAddEquiv` below, and it is the only step
done by hand; the other two are the corepresentation of `Γ(Cris(X/S), -)` and the sheafification
adjunction read on corepresented functors.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `forgetBaseAction` — the forgetful functor from `A`-modules to abelian groups.
* `constantIntegerHomSectionsAddEquiv` — additive maps from the constant presheaf on `ULift ℤ`
  into the underlying abelian presheaf of a module are its compatible families of sections.
* `moduleGlobalSectionsIsoAbelian` — **the two global sections functors agree**:
  `baseModuleGlobalSections S ⋙ forgetBaseAction S ≅ toAbelianSheaf S ⋙ globalSections S`.

## Main results

* `isZero_moduleCohomology_iff` — the module-valued `H^j(Cris(X/S), M)` vanishes exactly when the
  abelian-valued `R^j Γ(Cris(X/S), -)` of the underlying abelian sheaf does.
* `vanishingTransfer03FD` — **`VanishingTransfer03FD` is discharged.**
* `vanishing07MR_of_abelianVanishing07MR'` — [Stacks, Tag 07MR] follows from
  `AbelianVanishing07MR` alone.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The two global sections functors -/

/-- Forgetting the `A`-action on an `A`-module.  This is the functor along which the
module-valued cohomology of the chapter is compared with the abelian-valued one; it is exact and
faithful, so it loses no vanishing information. -/
abbrev forgetBaseAction : ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}

/-- Restriction in the underlying abelian presheaf of a sheaf of `𝒪_{X/S}`-modules is
restriction in the module.  This is a definitional identity, isolated as a lemma because the
elaborator will not take it at its default transparency. -/
private lemma presheaf_map_apply {M : ModuleSheaf S}
    {A B : (CrystallineThickening S)ᵒᵖ} (f : A ⟶ B) (y : M.val.presheaf.obj A) :
    M.val.presheaf.map f y = M.val.map f y := rfl

/-- **Additive maps from the constant presheaf on `ULift ℤ` into the underlying abelian presheaf
of a sheaf of `𝒪_{X/S}`-modules are its compatible families of sections.**  A natural
transformation out of a constant presheaf is determined by its value on the integer generator,
and its naturality is exactly the compatibility of that family. -/
def constantIntegerHomSectionsAddEquiv (M : ModuleSheaf S) :
    (constantIntegerPresheaf S ⟶ M.val.presheaf) ≃+ M.sections where
  toFun η := M.val.sectionsMk
    (fun A => AddCommGrpCat.uliftZMultiplesAddEquiv (M.val.presheaf.obj A) (η.app A))
    (fun {A B} f => (ConcreteCategory.congr_hom (η.naturality f) (ULift.up (1 : ℤ))).symm)
  invFun s :=
    { app A := (AddCommGrpCat.uliftZMultiplesAddEquiv (M.val.presheaf.obj A)).symm (s.eval A)
      naturality := fun {A B} f => by
        ext z
        refine Eq.trans ?_ (presheaf_map_apply S f (z.down • s.eval A)).symm
        exact (congrArg (fun y => z.down • y) (M.val.sections_property s f)).symm.trans
          (map_zsmul (M.val.map f).hom.toAddMonoidHom z.down (s.eval A)).symm }
  left_inv η := NatTrans.ext <| funext fun A =>
    (AddCommGrpCat.uliftZMultiplesAddEquiv (M.val.presheaf.obj A)).symm_apply_apply (η.app A)
  right_inv s := PresheafOfModules.sections_ext _ _ fun A =>
    (AddCommGrpCat.uliftZMultiplesAddEquiv (M.val.presheaf.obj A)).apply_symm_apply (s.eval A)
  map_add' η θ := rfl

/-- The sheafification of the constant presheaf on `ULift ℤ` is the constant sheaf on it, so
morphisms out of the constant sheaf are morphisms out of the constant presheaf into the
underlying abelian presheaf. -/
def abelianCorepresentingSheafCoyonedaIso :
    sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        preadditiveCoyoneda.obj (op (constantIntegerPresheaf S)) ≅
      preadditiveCoyoneda.obj (op (abelianCorepresentingSheaf S)) :=
  have : (presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1}).Additive :=
    (sheafificationAdjunction (smallTopology S) AddCommGrpCat.{u + 1}).left_adjoint_additive
  Stacks.Cohomology.ObjectSections.coyonedaAdjunctionIso
    (sheafificationAdjunction (smallTopology S) AddCommGrpCat.{u + 1})
    (constantIntegerPresheaf S)

/-- The compatible families of sections of a sheaf of `𝒪_{X/S}`-modules, read as an abelian
group, are the additive maps out of the constant presheaf on `ULift ℤ`. -/
def sectionsCoyonedaIso :
    toAbelianSheaf S ⋙ sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        preadditiveCoyoneda.obj (op (constantIntegerPresheaf S)) ≅
      baseModuleGlobalSections S ⋙ forgetBaseAction S :=
  NatIso.ofComponents (fun M => (constantIntegerHomSectionsAddEquiv S M).toAddCommGrpIso)
    (fun {_ _} _ => by ext _; rfl)

/-- **The module-valued and the abelian-valued global sections of the small crystalline site
agree.**  Forgetting the `A`-action on `Γ(Cris(X/S), M)` gives the abelian group
`Γ(Cris(X/S), -)` of the underlying abelian sheaf of `M`.

Both are read as morphisms out of the constant presheaf on `ULift ℤ`: on the abelian side by the
corepresentation of `Γ(Cris(X/S), -)` followed by the sheafification adjunction, on the module
side by `constantIntegerHomSectionsAddEquiv`. -/
def moduleGlobalSectionsIsoAbelian :
    baseModuleGlobalSections S ⋙ forgetBaseAction S ≅
      toAbelianSheaf S ⋙ globalSections S :=
  (sectionsCoyonedaIso S).symm ≪≫
    Functor.isoWhiskerLeft (toAbelianSheaf S) (abelianCorepresentingSheafCoyonedaIso S) ≪≫
      (Functor.isoWhiskerLeft (toAbelianSheaf S) (globalSectionsCorepresentation S)).symm

/-! ### Left exactness in degree zero -/

/-- **The `A`-module-valued global sections of the small crystalline site are left exact.**

`SmallSite/ModuleCohomology.lean` records this as unavailable, the library's proof of left
exactness of module-valued global sections
(`Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor_ringUniverse`) going
through corepresentability by `CategoryTheory.SheafOfModules.unit`, which lives at the module
universe equal to the ring universe and so is not an object of `ModuleSheaf S`.  It follows from
`moduleGlobalSectionsIsoAbelian` instead: the abelian-valued global sections are a right adjoint,
hence left exact, and `forgetBaseAction` reflects finite limits. -/
instance preservesFiniteLimits_baseModuleGlobalSections :
    PreservesFiniteLimits (baseModuleGlobalSections S) :=
  have : PreservesFiniteLimits (baseModuleGlobalSections S ⋙ forgetBaseAction S) :=
    preservesFiniteLimits_of_natIso (moduleGlobalSectionsIsoAbelian S).symm
  preservesFiniteLimits_of_reflects_of_preserves _ (forgetBaseAction S)

/-- **`H^0(Cris(X/S), -) = Γ(Cris(X/S), -)` as `A`-modules.**  The degree-zero comparison
`...SmallSite.toModuleCohomologyZero` is therefore an isomorphism, which
`SmallSite/ModuleCohomology.lean` records as unavailable for want of
`preservesFiniteLimits_baseModuleGlobalSections`. -/
def moduleCohomologyZeroIso : moduleCohomologyFunctor S 0 ≅ baseModuleGlobalSections S :=
  (baseModuleGlobalSections S).rightDerivedZeroIsoSelf

/-! ### The transfer of vanishing -/

/-- **The module-valued cohomology of the small crystalline site, after forgetting the
`A`-action, is the abelian-valued right derived global sections of the underlying abelian
sheaf.**

Three steps: the exact functor `forgetBaseAction` comes out of the right derived functor
(`CategoryTheory.Functor.rightDerivedCompIso`), the two underived functors agree
(`moduleGlobalSectionsIsoAbelian`), and the composite derived functor splits by
[Stacks, Tag 03FD] at this site (`abelianComparisonIso`). -/
@[sga "4 V 3.5" "special case"]
def moduleCohomologyFunctorIsoAbelian (j : ℕ) :
    moduleCohomologyFunctor S j ⋙ forgetBaseAction S ≅
      toAbelianSheaf S ⋙ (globalSections S).rightDerived j :=
  (Functor.rightDerivedCompIso (baseModuleGlobalSections S) (forgetBaseAction S) j).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (moduleGlobalSectionsIsoAbelian S) j ≪≫
      abelianComparisonIso S j

/-- **The module-valued `H^j(Cris(X/S), M)` vanishes exactly when the abelian-valued
`R^j Γ(Cris(X/S), -)` of the underlying abelian sheaf of `M` does.** -/
theorem isZero_moduleCohomology_iff (M : ModuleSheaf S) (j : ℕ) :
    IsZero (moduleCohomology S M j) ↔
      IsZero (((globalSections S).rightDerived j).obj ((toAbelianSheaf S).obj M)) :=
  (ModuleCat.isZero_iff_subsingleton.trans (AddCommGrpCat.isZero_iff_subsingleton
    (G := (forgetBaseAction S).obj (moduleCohomology S M j))).symm).trans
    ((moduleCohomologyFunctorIsoAbelian S j).app M).isZero_iff

/-- **[Stacks, Tag 03FD] transfers vanishing at the small crystalline site**, which is
`VanishingTransfer03FD`: if the abelian-valued `R^j Γ(Cris(X/S), -)` of the abelian sheaf
underlying a sheaf of `𝒪_{X/S}`-modules vanishes, so does the module-valued
`H^j(Cris(X/S), -)`. -/
theorem vanishingTransfer03FD : VanishingTransfer03FD S :=
  fun M j => (isZero_moduleCohomology_iff S M j).2

/-- **[Stacks, Tag 07MR] follows from its abelian form alone.**  `VanishingTransfer03FD`, the
other hypothesis of `vanishing07MR_of_abelianVanishing07MR`, is now proved, so the gap between
the abelian form of the remark — the form the source's hint reduces to — and the remark itself
is closed. -/
theorem vanishing07MR_of_abelianVanishing07MR' (hab : AbelianVanishing07MR S) :
    Vanishing07MR S :=
  vanishing07MR_of_abelianVanishing07MR S (vanishingTransfer03FD S) hab

end Crystalline.GlobalCrystallineSituation.SmallSite

end
