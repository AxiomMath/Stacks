module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ULiftUnitAbelianComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction

/-!
# `Ext` out of the sheafified extension of scalars of a torsion-free abelian presheaf

Let `R` be a sheaf of rings on a site `(C, J)` and `P` a presheaf of abelian groups on `C`, in the
universe of the modules. The sheafified extension of scalars `𝒪_P = (R ⊗_ℤ P)^#` corepresents
`M ↦ Hom(P^#, M_ab)` (`Stacks.SheafOfModules.tensorSheafHomIso`). When `P` is sectionwise
torsion-free this identification persists in every degree:

`Ext^n_R(𝒪_P, M) ≅ Ext^n(P^#, M_ab)`,

naturally in the sheaf of `R`-modules `M`. This is the argument of **Stacks 03FD** for an
arbitrary torsion-free coefficient presheaf in place of the constant presheaf `ℤ`.

## Main definitions

* `Stacks.Cohomology.TensorSheafComparison.tensorSheaf`: the sheaf of `R`-modules `𝒪_P`.
* `Stacks.Cohomology.TensorSheafComparison.extTensorSheafIso`: the comparison in every degree.

## Main results

* `Stacks.Cohomology.TensorSheafComparison.isZero_rightDerived_of_iso_preadditiveCoyoneda`: the
  right derived functors of a functor corepresented by `𝒪_P` vanish at `M` as soon as
  `Ext^n(P^#, M_ab)` does.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u

namespace Stacks.Cohomology.TensorSheafComparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{w})

attribute [local instance] Stacks.Cohomology.BiggerSiteModules.hasSheafify_source
  Stacks.Cohomology.BiggerSiteModules.wEqualsLocallyBijective_source
  Stacks.Cohomology.ModuleAbelianComparison.hasExt
  Stacks.Cohomology.ULiftUnitComparison.enoughInjectivesAb
  Stacks.Cohomology.ULiftUnitComparison.enoughInjectivesModules
  Stacks.Cohomology.ULiftUnitComparison.hasExtModules
  Stacks.Cohomology.ULiftUnitComparison.toSheaf_preservesFiniteColimits

/-- **The sheafified extension of scalars `𝒪_P = (R ⊗_ℤ P)^#`** of a presheaf of abelian groups
`P`, a sheaf of `R`-modules. -/
abbrev tensorSheaf (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) : SheafOfModules.{max u v w} R :=
  (PresheafOfModules.sheafification.{max u v w} (𝟙 R.obj)).obj
    (Stacks.SheafOfModules.tensorPresheaf.{u, v, max u v w, w} R.obj P)

/-- **`Ext` out of the sheafified extension of scalars of a torsion-free presheaf.** For a
sectionwise torsion-free presheaf of abelian groups `P`, `Ext^n_R(𝒪_P, M) ≅ Ext^n(P^#, M_ab)`,
naturally in `M`.

Both sides are `δ`-functors on sheaves of `R`-modules, the second because forgetting to abelian
sheaves is exact; they agree in degree zero by `Stacks.SheafOfModules.tensorSheafHomIso`; and both
are universal, the second because the underlying abelian sheaf of an injective sheaf of modules
has no higher `Ext` out of the sectionwise torsion-free sheaf `P^#`
(`Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`). -/
def extTensorSheafIso (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})
    (hP : ∀ U, Module.IsTorsionFree ℤ (P.obj U)) (n : ℕ) :
    extFunctorObj (tensorSheaf J R P) n ≅
      SheafOfModules.toSheaf R ⋙
        extFunctorObj ((presheafToSheaf J AddCommGrpCat.{max u v w}).obj P) n :=
  ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R)
    ((presheafToSheaf J AddCommGrpCat.{max u v w}).obj P) (tensorSheaf J R P)
    (fun I _ m e => Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{max u v w,
      max u v, w, v, u} J R I _ (ModuleSheafCohomology.isTorsionFree_sheafify J P hP) m e)
    (Stacks.SheafOfModules.tensorSheafHomIso.{max u v w, w, v, u} J R P) n

/-- The free abelian presheaf on a presheaf of sets is sectionwise torsion-free. -/
theorem isTorsionFree_freeAbelian {D : Type*} [Category* D] (F : Dᵒᵖ ⥤ Type w) (U : Dᵒᵖ) :
    Module.IsTorsionFree ℤ ((Presheaf.freeAbelian.obj F).obj U) := by
  change Module.IsTorsionFree ℤ (FreeAbelianGroup (F.obj U))
  exact Module.Flat.isTorsionFree

/-- **The right derived functors of a functor corepresented by `𝒪_P` vanish where `Ext` out of
`P^#` does.** Let `Φ` be an additive functor on sheaves of `R`-modules isomorphic to
`Hom(𝒪_P, -)` for a sectionwise torsion-free presheaf of abelian groups `P`. If every element of
`Ext^n(P^#, M_ab)` is zero then `R^nΦ(M) = 0`: `R^nΦ` is `Ext^n(𝒪_P, -)`
(`Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda`), which is
`Ext^n(P^#, (-)_ab)` by `extTensorSheafIso`. -/
theorem isZero_rightDerived_of_iso_preadditiveCoyoneda
    (Φ : SheafOfModules.{max u v w} R ⥤ AddCommGrpCat.{max u v w}) [Φ.Additive]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (hP : ∀ U, Module.IsTorsionFree ℤ (P.obj U))
    (e : Φ ≅ preadditiveCoyoneda.obj (op (tensorSheaf J R P))) (M : SheafOfModules.{max u v w} R)
    (n : ℕ) (h : ∀ x : Ext ((presheafToSheaf J AddCommGrpCat.{max u v w}).obj P)
      ((SheafOfModules.toSheaf R).obj M) n, x = 0) :
    IsZero ((Φ.rightDerived n).obj M) :=
  ((Functor.rightDerivedIsoOfNatIso e n ≪≫
      (Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda _ n).symm ≪≫
      extTensorSheafIso J R P hP n).app M).isZero_iff.2
    (@AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => (h a).trans (h b).symm⟩)

end Stacks.Cohomology.TensorSheafComparison

end
