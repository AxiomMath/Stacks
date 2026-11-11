module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.InjectiveModuleGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity

/-!
# Injective sheaves of `R`-modules are acyclic for abelian global sections

Let `(C, J)` be a site and `R` a ring.  The underlying abelian sheaf of an injective sheaf of
`R`-modules (a sheaf with values in `ModuleCat R`) is right acyclic for the global sections
functor `Γ(C, -)` of abelian sheaves, in the sense of [Stacks, Tag 0157].  This is the
`ModuleCat R`-valued counterpart of
`Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_toSheaf_obj_of_injective`, which is about
sheaves of modules over a sheaf of rings.

## Main results

* `Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_sheafCompose_forget₂_obj_of_injective`.

## References

* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w₁ w₂ w r v u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.Cohomology.GlobalSections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type r) [Ring R]
  [HasSheafify J AddCommGrpCat.{max u r w}] [HasSheafify J (ModuleCat.{max u r w} R)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u r w} R) AddCommGrpCat.{max u r w})]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u r w}]
  [(Sheaf.Γ J AddCommGrpCat.{max u r w}).Additive]
  [HasExt.{max u r w} (Sheaf J AddCommGrpCat.{max u r w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u r w})]
  [HasDerivedCategory.{w₁} (Sheaf J AddCommGrpCat.{max u r w})]
  [HasDerivedCategory.{w₂} AddCommGrpCat.{max u r w}]

/-- **The underlying abelian sheaf of an injective sheaf of `R`-modules is right acyclic for
`Γ(C, -)`.**  Its higher `Ext` out of the constant sheaf on `ℤ` vanishes
(`Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree`), that sheaf being the
sheafification of a sectionwise torsion-free presheaf. -/
theorem rightAcyclic_Γ_sheafCompose_forget₂_obj_of_injective
    (I : Sheaf J (ModuleCat.{max u r w} R)) [Injective I] :
    (Sheaf.Γ J AddCommGrpCat.{max u r w}).rightAcyclic
      ((sheafCompose J (forget₂ (ModuleCat.{max u r w} R) AddCommGrpCat.{max u r w})).obj I) :=
  rightAcyclic_Γ_of_ext_eq_zero.{w₁, w₂, max r w} J _ fun n e =>
    Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree.{max u r w, max u w, r, v, u} J R I
      _ (ModuleSheafCohomology.isTorsionFree_sheafify J _
        (fun _ => (Module.Flat.isTorsionFree : Module.IsTorsionFree ℤ (ULift.{max u r w} ℤ)))) n e

end Stacks.Cohomology.GlobalSections

end
