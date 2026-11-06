module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing

/-!
# Global sections of a sheaf of modules against the cohomology of its underlying abelian sheaf

Let `(C, J)` be a site whose objects need not form a small type (objects in `Type u'`,
morphisms in `Type u`), `R` a sheaf of rings and `F` a sheaf of `R`-modules. The global sections
of `F` can be derived in the category of sheaves of `R`-modules, through
`Stacks.Cohomology.SiteModules.globalSectionsFunctor`, or in the category of abelian sheaves,
where the cohomology `CategoryTheory.Sheaf.H` is the `Ext` out of the constant sheaf on `ℤ`.
In every positive degree, the vanishing of the first implies the vanishing of the second.

This is the global form of Stacks 03FD on such a site, and the converse direction to the one
proved over an object in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing`.

## Main results

* `constantHomAddEquivSections`: morphisms out of the constant presheaf on `ℤ` are the
  compatible families of sections.
* `subsingleton_sheafH_of_subsingleton_rightDerived_globalSections`: if the `(n + 1)`-st right
  derived functor of global sections of sheaves of `R`-modules vanishes at `F`, then `H^{n+1}` of
  the underlying abelian sheaf of `F` vanishes.

## Implementation notes

The comparison is the one of Stacks 03FD (`Stacks.ModuleSheafCohomology.comparisonIso`), with the
forgetful functor `SheafOfModules.toSheaf R`, the constant sheaf `X` on `ULift ℤ` corepresenting
the global sections of abelian sheaves, and the module sheaf `T` obtained by sheafifying the
extension of scalars of the constant presheaf corepresenting the global sections of modules; the
acyclicity input is `ext_eq_zero_of_isTorsionFree`, the constant presheaf being torsion free.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

universe u u'

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.Cohomology.ObjectSections

section Constant

variable {C : Type u'} [Category.{u} C]

/-- The constant abelian presheaf on `ℤ`, read in `Ab.{u}`. -/
abbrev constantZPresheaf : Cᵒᵖ ⥤ Ab.{u} :=
  (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))

/-- **Morphisms out of the constant presheaf on `ℤ` into the underlying presheaf of a sheaf of
modules are its global sections.** -/
def constantHomAddEquivSections {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    (M : SheafOfModules.{u} R) :
    (constantZPresheaf (C := C) ⟶ M.val.presheaf) ≃+ M.sections where
  toFun φ := M.val.sectionsMk (fun X => φ.app X (ULift.up 1)) (fun {X Y} f =>
    (ConcreteCategory.congr_hom (φ.naturality f) (ULift.up 1)).symm)
  invFun s :=
    { app := fun X => AddCommGrpCat.ofHom
        ((zmultiplesHom (M.val.presheaf.obj X) (s.eval X)).comp
          (AddEquiv.ulift (α := ℤ)).toAddMonoidHom)
      naturality := fun {X Y} f => by
        ext ⟨n⟩
        exact ((map_zsmul (M.val.presheaf.map f).hom n (s.eval X)).trans
          (congrArg (n • ·) (M.val.sections_property s f))).symm }
  left_inv φ := by
    ext X ⟨n⟩
    change n • φ.app X (ULift.up 1) = φ.app X (ULift.up n)
    rw [← map_zsmul]
    congr 1
    exact ULift.ext (by simp)
  right_inv s := by
    refine Subtype.ext ?_
    funext X
    exact one_zsmul (s.eval X)
  map_add' φ ψ := by
    refine Subtype.ext ?_
    funext X
    rfl

/-- The constant presheaf on `ℤ` is sectionwise torsion free. -/
theorem isTorsionFree_constantZPresheaf (X : Cᵒᵖ) :
    Module.IsTorsionFree ℤ ((constantZPresheaf (C := C)).obj X) := by
  show Module.IsTorsionFree ℤ (ULift.{u} ℤ)
  exact Function.Injective.moduleIsTorsionFree (fun x : ULift ℤ => x.down)
    ULift.down_injective (fun _ _ => rfl)

end Constant

section Bridge

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}]

/-- The constant abelian sheaf on `ℤ`, the object out of which `CategoryTheory.Sheaf.H` takes
`Ext`. -/
abbrev constantZSheaf : Sheaf J Ab.{u} :=
  (presheafToSheaf J Ab.{u}).obj (constantZPresheaf (C := C))

/-- The sheaf of modules corepresenting global sections: the sheafified extension of scalars of
the constant presheaf on `ℤ`. -/
abbrev globalSectionObject (R : Sheaf J RingCat.{u}) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (ModuleSheafCohomology.tensorPresheaf R.obj (constantZPresheaf (C := C)))

/-- **Global sections of sheaves of modules are corepresented by `globalSectionObject`.** -/
private def globalSectionObjectCoyonedaIso (R : Sheaf J RingCat.{u}) :
    preadditiveCoyoneda.obj (op (globalSectionObject J R)) ≅
      Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u', u, u, u} R ⋙
        forget₂ (ModuleCat.{max u' u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u' u} :=
  tensorSheafHomIso J R (constantZPresheaf (C := C)) ≪≫
    NatIso.ofComponents (fun M =>
      (((sheafificationAdjunction J Ab.{u}).homAddEquiv (constantZPresheaf (C := C))
        ((SheafOfModules.toSheaf R).obj M)).trans
          (constantHomAddEquivSections R M)).toAddCommGrpIso) (fun {M N} f => by
      refine AddCommGrpCat.hom_ext ?_
      refine AddMonoidHom.ext fun a => ?_
      refine Subtype.ext ?_
      funext X
      change (((sheafificationAdjunction J Ab.{u}).homEquiv _ _
          (a ≫ (SheafOfModules.toSheaf R).map f)).app X) (ULift.up 1) =
        f.val.app X ((((sheafificationAdjunction J Ab.{u}).homEquiv _ _ a).app X) (ULift.up 1))
      have hn := (sheafificationAdjunction J Ab.{u}).homEquiv_naturality_right
        (a : (presheafToSheaf J Ab.{u}).obj (constantZPresheaf (C := C)) ⟶
          (SheafOfModules.toSheaf R).obj M) ((SheafOfModules.toSheaf R).map f)
      exact congrArg (fun φ => (φ.app X) (ULift.up 1)) hn)

/-- **Global sections of a sheaf of modules control the cohomology of its underlying abelian
sheaf.** If the `(n + 1)`-st right derived functor of the global sections of sheaves of
`R`-modules vanishes at `F`, then `H^{n+1}` of the underlying abelian sheaf of `F` vanishes. -/
theorem subsingleton_sheafH_of_subsingleton_rightDerived_globalSections
    [HasExt.{max u' u} (Sheaf J Ab.{u})] [EnoughInjectives (Sheaf J Ab.{u})]
    (R : Sheaf J RingCat.{u})
    [EnoughInjectives (SheafOfModules.{u} R)] [HasExt.{max u' u} (SheafOfModules.{u} R)]
    (F : SheafOfModules.{u} R) (n : ℕ)
    (hF : Subsingleton (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u', u, u, u}
      R).rightDerived (n + 1)).obj F)) :
    Subsingleton (Sheaf.H.{max u' u} ((SheafOfModules.toSheaf R).obj F) (n + 1)) := by
  have := toSheaf_preservesFiniteColimits J R
  have h : ∀ (I : SheafOfModules.{u} R) [Injective I] (m : ℕ)
      (e : Ext.{max u' u} (constantZSheaf J) ((SheafOfModules.toSheaf R).obj I) (m + 1)),
      e = 0 :=
    fun I _ m e => ext_eq_zero_of_isTorsionFree J R I _
      (ModuleSheafCohomology.isTorsionFree_sheafify J _ isTorsionFree_constantZPresheaf) m e
  let c := (ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R) (constantZSheaf J)
    (globalSectionObject J R) h (tensorSheafHomIso J R (constantZPresheaf (C := C)))
    (n + 1)).app F
  let d := (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso (globalSectionObject J R) n).app F
  let r := (ModuleSheafCohomology.rightDerivedIso (globalSectionObjectCoyonedaIso J R)
    (n + 1)).app F
  let q := (Stacks.Cohomology.DerivedForget.rightDerivedCompIso
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u', u, u, u} R)
    (forget₂ (ModuleCat.{max u' u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u' u})
    (n + 1)).app F
  let e : AddCommGrpCat.of (Sheaf.H.{max u' u} ((SheafOfModules.toSheaf R).obj F) (n + 1)) ≅
      (forget₂ (ModuleCat.{max u' u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u' u}).obj
        (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u', u, u, u}
          R).rightDerived (n + 1)).obj F) :=
    c.symm ≪≫ d.symm ≪≫ r ≪≫ q.symm
  exact ((forget AddCommGrpCat).mapIso e).toEquiv.subsingleton_congr.mpr hF

end Bridge

end Stacks.Cohomology.ObjectSections

end
