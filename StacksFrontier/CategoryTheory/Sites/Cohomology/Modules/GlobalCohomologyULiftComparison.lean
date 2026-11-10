module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicAnySite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.CategoryTheory.Sites.Modules.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective

/-!
# Module cohomology on a site whose objects lie above its morphisms

Let `(C, J)` be a site with objects in `Type u'` and morphisms in `Type u`, and `R` a sheaf of
rings on it with values in `RingCat.{u}`.  For a sheaf of `R`-modules `M` with sections in
`Type u` there are two cohomologies in sight:

* the right derived functors of the module-valued global sections
  `Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u', u, u, u}` (Stacks 071H), which take
  values in `Type (max u' u)`;
* the right derived functors of Mathlib's `CategoryTheory.Sheaf.Γ` on abelian sheaves with
  coefficients in `AddCommGrpCat.{max u' u}`, applied to the universe lift of the abelian sheaf
  underlying `M`.

This file identifies them in every degree (Stacks 03FD for global sections, at these universes),
and deduces that module cohomology commutes with a filtered colimit as soon as abelian cohomology
does.  This is how a statement about abelian sheaves such as Stacks 073E — the cohomology of a
quasi-compact and quasi-separated algebraic space commutes with filtered colimits, stated in
`AddCommGrpCat.{u + 1}` — is read for modules at the universe `u` of the structure rings, where
the direct image of modules lives.

## Main definitions

* `Stacks.Cohomology.ModuleULiftComparison.liftGlobalSectionsCoyonedaIso`: global sections of the
  universe lift of an abelian sheaf are corepresented by the free abelian sheaf on the final
  sheaf.
* `Stacks.Cohomology.ModuleULiftComparison.rightDerivedGlobalSectionsULiftIso`: the comparison
  of the two cohomologies.

## Main results

* `Stacks.Cohomology.ModuleULiftComparison.isZero_rightDerived_of_isColimit`: module cohomology
  of a filtered colimit vanishes when it vanishes on the terms, provided abelian cohomology
  commutes with that colimit.

## Implementation notes

The comparison runs through `Ext`: global sections of modules are `Ext⁰` out of the unit sheaf of
modules (`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`), `Ext` out of the unit is
`Ext` out of the free abelian sheaf `ℤ_*` on the final sheaf after forgetting the module
structure (`ModuleSheafCohomology.extComparisonIso`, with the torsion-free acyclicity of
Stacks 03FD), and `Ext` out of `ℤ_*` is the right derived functor of the functor it
corepresents, which is global sections of the universe lift.  That last functor is the composite
of the universe lift — exact, and preserving injectives by hypothesis — with `Sheaf.Γ`, so its
right derived functors are those of `Sheaf.Γ` on the lift.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Sheaves.UniverseLift

attribute [local instance 5000] SheafOfModules.instAbelian

universe u' u

namespace Stacks.Cohomology.ModuleULiftComparison

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free abelian sheaf `ℤ_*` on the final sheaf of sets, with coefficients at the universe
of the morphisms of the site. -/
abbrev freeFinal : Sheaf J AddCommGrpCat.{u} :=
  (Presheaf.freeAbelianSheaf J).obj (finalSheaf J).obj

/-- Morphisms out of `ℤ_*` are the sections of the underlying presheaf of sets. -/
def homFreeFinalEquivSections (A : Sheaf J AddCommGrpCat.{u}) :
    (freeFinal J ⟶ A) ≃ (A.obj ⋙ forget AddCommGrpCat.{u}).sections :=
  ((Presheaf.freeAbelianSheafAdj J).homEquiv (finalSheaf J).obj A).trans
    (Functor.sectionsEquivHom (A.obj ⋙ forget AddCommGrpCat.{u}) PUnit).symm

/-- The sections of the universe lift of a presheaf of abelian groups are its sections. -/
def sectionsULiftEquiv (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((G ⋙ AddCommGrpCat.uliftFunctor.{u'}) ⋙ forget AddCommGrpCat.{max u u'}).sections ≃
      (G ⋙ forget AddCommGrpCat.{u}).sections where
  toFun s := ⟨fun V => ULift.down (s.1 V), fun f => congrArg ULift.down (s.2 f)⟩
  invFun s := ⟨fun V => ULift.up (s.1 V), fun f => congrArg ULift.up (s.2 f)⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `ℤ_*` is sectionwise torsion free, being the sheafification of a sectionwise free presheaf. -/
lemma freeFinal_isTorsionFree (U : Cᵒᵖ) : Module.IsTorsionFree ℤ ((freeFinal J).obj.obj U) :=
  ModuleSheafCohomology.isTorsionFree_sheafify J _ (fun V => by
    change Module.IsTorsionFree ℤ (FreeAbelianGroup PUnit)
    exact Module.Flat.isTorsionFree) U

variable [HasSheafify J AddCommGrpCat.{max u' u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u' u}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u' u}]

/-- Global sections of an abelian sheaf, read as a type, are the sections of its underlying
presheaf of sets: `Sheaf.Γ` is the limit of the sections, and the forgetful functor preserves it,
being a right adjoint. -/
def globalSectionsEquivSections (B : Sheaf J AddCommGrpCat.{max u' u}) :
    (Sheaf.Γ J AddCommGrpCat.{max u' u}).obj B ≃
      (B.obj ⋙ forget AddCommGrpCat.{max u' u}).sections :=
  have := AddCommGrpCat.adj.{max u' u}.rightAdjoint_preservesLimits.{u, u'}
  Types.isLimitEquivSections (isLimitOfPreserves (forget AddCommGrpCat.{max u' u})
    (Sheaf.isLimitConeΓ B))

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u' u}] in
/-- The section of `globalSectionsEquivSections J B x` over `V` is the restriction of the global
section `x` to `V`. -/
lemma globalSectionsEquivSections_apply (B : Sheaf J AddCommGrpCat.{max u' u})
    (x : (Sheaf.Γ J AddCommGrpCat.{max u' u}).obj B) (V : Cᵒᵖ) :
    (globalSectionsEquivSections J B x).1 V = Sheaf.ΓRes B V x :=
  rfl

/-- The comparison of the sections of the lift of an abelian sheaf with morphisms out of `ℤ_*`,
as a map of types. -/
def liftGlobalSectionsEquiv (A : Sheaf J AddCommGrpCat.{u}) :
    (Sheaf.Γ J AddCommGrpCat.{max u' u}).obj ((uliftSheafFunctor.{u', u} J).obj A) ≃
      (freeFinal J ⟶ A) :=
  (globalSectionsEquivSections J _).trans
    ((sectionsULiftEquiv.{u'} A.obj).trans (homFreeFinalEquivSections J A).symm)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{max u' u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u' u}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u' u}] in
/-- Naturality of `(homFreeFinalEquivSections J A).symm` in the abelian sheaf `A`: pushing a
section forward along `g : A ⟶ A'` corresponds to composing the morphism out of `ℤ_*` with `g`. -/
lemma homFreeFinalEquivSections_symm_comp {A A' : Sheaf J AddCommGrpCat.{u}} (g : A ⟶ A')
    (s : (A.obj ⋙ forget AddCommGrpCat.{u}).sections) :
    (homFreeFinalEquivSections J A').symm
        ((Functor.sectionsFunctor _).map (Functor.whiskerRight g.hom (forget _)) s) =
      (homFreeFinalEquivSections J A).symm s ≫ g := by
  change ((Presheaf.freeAbelianSheafAdj.{u} J).homEquiv _ A').symm
      ((A'.obj ⋙ forget AddCommGrpCat.{u}).sectionsEquivHom PUnit
        ((Functor.sectionsFunctor _).map (Functor.whiskerRight g.hom (forget _)) s)) =
    ((Presheaf.freeAbelianSheafAdj.{u} J).homEquiv _ A).symm
      ((A.obj ⋙ forget AddCommGrpCat.{u}).sectionsEquivHom PUnit s) ≫ g
  rw [Functor.sectionsEquivHom_naturality]
  exact (Presheaf.freeAbelianSheafAdj.{u} J).homEquiv_naturality_right_symm _ g

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u' u}] in
/-- Naturality of `liftGlobalSectionsEquiv` in the abelian sheaf. -/
lemma liftGlobalSectionsEquiv_naturality {A A' : Sheaf J AddCommGrpCat.{u}} (g : A ⟶ A')
    (x : (Sheaf.Γ J AddCommGrpCat.{max u' u}).obj ((uliftSheafFunctor.{u', u} J).obj A)) :
    liftGlobalSectionsEquiv J A'
        ((Sheaf.Γ J AddCommGrpCat.{max u' u}).map ((uliftSheafFunctor.{u', u} J).map g) x) =
      liftGlobalSectionsEquiv J A x ≫ g := by
  change (homFreeFinalEquivSections J A').symm _ = (homFreeFinalEquivSections J A).symm _ ≫ g
  rw [← homFreeFinalEquivSections_symm_comp]
  congr 1
  apply Subtype.ext
  funext V
  change ULift.down (Sheaf.ΓRes ((uliftSheafFunctor.{u', u} J).obj A') V
      ((Sheaf.Γ J AddCommGrpCat.{max u' u}).map ((uliftSheafFunctor.{u', u} J).map g) x)) =
    g.hom.app V (ULift.down (Sheaf.ΓRes ((uliftSheafFunctor.{u', u} J).obj A) V x))
  rw [← ConcreteCategory.comp_apply, Sheaf.ΓRes_naturality]
  rfl

/-- Global sections of abelian sheaves are additive, being a right adjoint. -/
instance additive_globalSections : (Sheaf.Γ J AddCommGrpCat.{max u' u}).Additive :=
  (constantSheafΓAdj J AddCommGrpCat.{max u' u}).right_adjoint_additive

/-- **Global sections of the universe lift are corepresented by `ℤ_*`.** -/
def liftGlobalSectionsCoyonedaIso :
    uliftSheafFunctor.{u', u} J ⋙ Sheaf.Γ J AddCommGrpCat.{max u' u} ≅
      preadditiveCoyoneda.obj (op (freeFinal J)) := by
  let φ : (uliftSheafFunctor.{u', u} J ⋙ Sheaf.Γ J AddCommGrpCat.{max u' u}) ⋙
      forget AddCommGrpCat ⟶ preadditiveCoyoneda.obj (op (freeFinal J)) ⋙ forget AddCommGrpCat :=
    { app A := TypeCat.ofHom fun x => liftGlobalSectionsEquiv J A x
      naturality {A A'} g := by
        ext x
        exact liftGlobalSectionsEquiv_naturality J g x }
  exact NatIso.ofComponents (fun A => AddEquiv.toAddCommGrpIso
    { liftGlobalSectionsEquiv J A with
      map_add' := (Stacks.Cohomology.naturalTransformationAddHom _ _ φ A).map_add })
    (fun {A A'} g => by
      ext x
      exact liftGlobalSectionsEquiv_naturality J g x)

/-! ### The comparison -/

variable (R : Sheaf J RingCat.{u})
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] [HasExt.{max u' u} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} R)] [HasExt.{max u' u} (SheafOfModules.{u} R)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u' u})]
  [(uliftSheafFunctor.{u', u} J).PreservesInjectiveObjects]

/-- **Stacks 03FD for global sections, across the universe gap.**  The cohomology of a sheaf of
`R`-modules, computed as the right derived functors of the module-valued global sections and
read as abelian groups, is the cohomology of the universe lift of its underlying abelian
sheaf. -/
def rightDerivedGlobalSectionsULiftIso (M : SheafOfModules.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat.{max u' u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u' u}).obj
        (((SiteModules.globalSectionsFunctor.{u', u, u, u} R).rightDerived n).obj M) ≅
      ((Sheaf.Γ J AddCommGrpCat.{max u' u}).rightDerived n).obj
        ((uliftSheafFunctor.{u', u} J).obj ((SheafOfModules.toSheaf R).obj M)) :=
  have := SiteModules.preservesFiniteLimits_globalSectionsFunctor_ringUniverse R
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    ObjectSections.toSheaf_preservesFiniteColimits J R
  ((Functor.rightDerivedCompIso (SiteModules.globalSectionsFunctor.{u', u, u, u} R)
      (forget₂ _ AddCommGrpCat.{max u' u}) n).app M).symm ≪≫
    ((ModuleSheafCohomology.extFunctorObjIsoRightDerived
      (SiteModules.globalSectionsFunctor.{u', u, u, u} R ⋙ forget₂ _ AddCommGrpCat.{max u' u})
      (SheafOfModules.unit R) (SiteModules.coyonedaUnitGlobalSectionsIso R).symm n).app M).symm ≪≫
    (ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R) (freeFinal J)
      (SheafOfModules.unit R)
      (fun I _ m e => ObjectSections.ext_eq_zero_of_isTorsionFree J R I _
        (freeFinal_isTorsionFree J) m e)
      (unitCoyonedaIsoFreeAbelianSheaf J R) n).app M ≪≫
    (ModuleSheafCohomology.extFunctorObjIsoRightDerived
      (uliftSheafFunctor.{u', u} J ⋙ Sheaf.Γ J AddCommGrpCat.{max u' u}) (freeFinal J)
      (liftGlobalSectionsCoyonedaIso J) n).app _ ≪≫
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (uliftSheafFunctor.{u', u} J)
      (Sheaf.Γ J AddCommGrpCat.{max u' u}) n).app _

/-! ### Filtered colimits -/

/-- **Module cohomology of a colimit vanishes when it vanishes on the terms**, as soon as the
abelian cohomology of the universe lifts commutes with that colimit — which is what Stacks 073E
supplies on a quasi-compact and quasi-separated algebraic space.

Forgetting the module structure and lifting the universe preserves the colimit, so by
`rightDerivedGlobalSectionsULiftIso` the cohomology of the colimit is the abelian cohomology of a
colimit, which is the colimit of the abelian cohomology groups of the terms, all zero. -/
theorem isZero_rightDerived_of_isColimit {I : Type u} [SmallCategory I]
    (D : I ⥤ SheafOfModules.{u} R) (c : Cocone D) (hc : IsColimit c) (n : ℕ)
    (hpost : IsIso (colimit.post (D ⋙ SheafOfModules.toSheaf R ⋙ uliftSheafFunctor.{u', u} J)
      ((Sheaf.Γ J AddCommGrpCat.{max u' u}).rightDerived n)))
    (hD : ∀ i, IsZero (((SiteModules.globalSectionsFunctor.{u', u, u, u} R).rightDerived n).obj
      (D.obj i))) :
    IsZero (((SiteModules.globalSectionsFunctor.{u', u, u, u} R).rightDerived n).obj c.pt) := by
  have := Stacks.SheafOfModules.preservesColimits_toSheaf.{u} (R := R)
  have := sheafCompose_uliftFunctor_preservesColimits.{u', u, u, u'} (J := J)
  let Φ := SheafOfModules.toSheaf R ⋙ uliftSheafFunctor.{u', u} J
  let H := (Sheaf.Γ J AddCommGrpCat.{max u' u}).rightDerived n
  have hzero : ∀ M : SheafOfModules.{u} R,
      IsZero (((SiteModules.globalSectionsFunctor.{u', u, u, u} R).rightDerived n).obj M) ↔
        IsZero (H.obj (Φ.obj M)) := fun M =>
    ⟨fun h => (rightDerivedGlobalSectionsULiftIso J R M n).isZero_iff.1
      ((forget₂ _ _).map_isZero h),
     fun h => ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1
      ((rightDerivedGlobalSectionsULiftIso J R M n).isZero_iff.2 h))⟩
  rw [hzero]
  let e : Φ.obj c.pt ≅ colimit (D ⋙ Φ) :=
    (isColimitOfPreserves Φ hc).coconePointUniqueUpToIso (colimit.isColimit _)
  refine IsZero.of_iso ?_ (H.mapIso e)
  refine IsZero.of_iso ?_ (asIso (colimit.post (D ⋙ Φ) H)).symm
  exact (colimit.isColimit _).isZero_pt (Functor.isZero _ fun i => (hzero (D.obj i)).1 (hD i))

end Stacks.Cohomology.ModuleULiftComparison
