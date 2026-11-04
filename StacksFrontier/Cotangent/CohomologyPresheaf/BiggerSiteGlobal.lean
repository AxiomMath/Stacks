module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison

/-!
# Ext-based cohomology of a site does not change on a bigger site

Let `u : C ⥤ D` be a continuous and cocontinuous functor between small sites whose restriction
functor on abelian sheaves admits an exact left adjoint and a right adjoint, and let `e_C`, `e_D`
be terminal objects with `u(e_C) = e_D`. Restriction along `u` does not change the cohomology of
the whole site, where cohomology is Mathlib's `Ext`-based `Sheaf.H`: the `Ext`-groups out of the
constant abelian sheaf `ℤ`.

## Main results

* `Stacks.Cohomology.SiteSections.nonempty_extFunctorObj_iso_rightDerived_siteSections`: the
  `Ext`-functors out of the constant abelian sheaf `ℤ` are the right-derived functors of global
  sections over the site.
* `Stacks.Cohomology.SiteSections.functorHIsoRightDerivedSiteSections`:
  `Sheaf.functorH J p ≅ (Γ(C, -)).rightDerived p`, with `Γ(C, -)` the limit of the underlying
  presheaf.
* `Stacks.Cohomology.BiggerSite.functorHIso`: the natural isomorphism
  `u^{-1} ⋙ H^p(C, -) ≅ H^p(D, -)` of functors on abelian sheaves over the bigger site, with
  cohomology taken to be Mathlib's `Sheaf.functorH`.
* `Stacks.Cohomology.BiggerSite.sheafHIso`: its evaluation at a sheaf,
  `Sheaf.H F p ≅ Sheaf.H (u^{-1} F) p`.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.SiteSections

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) [HasSheafify J Ab.{u}]

/-- Global sections over the site, as the limit of the underlying presheaf, are corepresented by
the constant abelian sheaf `ℤ`. -/
def siteSectionsRepresentation :
    Stacks.Cohomology.CompositeRightDerived.siteSections J ≅ preadditiveCoyoneda.obj
      (op ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) :=
  (Sheaf.ΓNatIsoLim J Ab.{u}).symm ≪≫ ModuleSheafCohomology.globalSectionsRepresentation J

/-- Global sections over the site, as the limit of the underlying presheaf, are left exact. -/
instance preservesFiniteLimits_siteSections :
    PreservesFiniteLimits (Stacks.Cohomology.CompositeRightDerived.siteSections J) :=
  preservesFiniteLimits_of_natIso (Sheaf.ΓNatIsoLim J Ab.{u})

/-- **The `Ext`-functors out of the constant abelian sheaf `ℤ` are the right-derived functors of
global sections over the site.** -/
theorem nonempty_extFunctorObj_iso_rightDerived_siteSections
    [HasExt.{u} (Sheaf J Ab.{u})] [HasInjectiveResolutions (Sheaf J Ab.{u})] (p : ℕ) :
    Nonempty (Abelian.extFunctorObj
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) p ≅
      Stacks.Cohomology.CompositeRightDerived.siteCohomology J p) :=
  ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived
    (Stacks.Cohomology.CompositeRightDerived.siteSections J) _ (siteSectionsRepresentation J) p

/-- **Cohomology of a site is right-derived global sections.** Mathlib's `Sheaf.functorH J p`, the
`p`-th `Ext`-functor out of the constant abelian sheaf `ℤ`, is identified with the `p`-th
right-derived functor of global sections over the site, by a chosen isomorphism. -/
def functorHIsoRightDerivedSiteSections
    [HasExt.{u} (Sheaf J Ab.{u})] [HasInjectiveResolutions (Sheaf J Ab.{u})] (p : ℕ) :
    Sheaf.functorH J p ≅ Stacks.Cohomology.CompositeRightDerived.siteCohomology J p :=
  (nonempty_extFunctorObj_iso_rightDerived_siteSections J p).some

end Stacks.Cohomology.SiteSections

namespace Stacks.Cohomology.BiggerSite

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] [u.IsCocontinuous J K]
  [(u.sheafPushforwardContinuous Ab.{u} J K).IsRightAdjoint]
  [∀ P : Cᵒᵖ ⥤ Ab.{u}, u.op.HasPointwiseRightKanExtension P]
  [(u.sheafPullback Ab.{u} J K).PreservesMonomorphisms]
  [HasSheafify J Ab.{u}] [HasSheafify K Ab.{u}]

/-- **Stacks 03YU, statement 1, in `Ext`-based form.** For terminal objects `e_C` of `C` and
`e_D` of `D` with `u(e_C) = e_D`, restriction along `u` does not change the `Ext`-groups out of
the constant abelian sheaf `ℤ`, naturally in the abelian sheaf on the bigger site. -/
def functorHIso (eC : C) (eD : D) (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD) (p : ℕ) :
    u.sheafPushforwardContinuous Ab.{u} J K ⋙ Sheaf.functorH J p ≅ Sheaf.functorH K p :=
  Functor.isoWhiskerLeft (u.sheafPushforwardContinuous Ab.{u} J K)
      (SiteSections.functorHIsoRightDerivedSiteSections J p) ≪≫
    (Stacks.Cohomology.CompositeRightDerived.statement1_cohomology J K u eC eD heC heD hu p).some ≪≫
    (SiteSections.functorHIsoRightDerivedSiteSections K p).symm

/-- **Stacks 03YU, statement 1.** Cohomology of an abelian sheaf on the bigger site agrees with
the cohomology of its restriction, with cohomology taken to be Mathlib's `Sheaf.H`. -/
def sheafHIso (eC : C) (eD : D) (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD) (F : Sheaf K Ab.{u}) (p : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u, u, u, u} F p) ≅
      AddCommGrpCat.of
        (Sheaf.H.{u, u, u, u}
          ((u.sheafPushforwardContinuous Ab.{u} J K).obj F) p) :=
  ((functorHIso J K u eC eD heC heD hu p).app F).symm

end Stacks.Cohomology.BiggerSite

end
