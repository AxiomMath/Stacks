module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction

/-!
# The underlying abelian sheaf of an injective module is acyclic for global sections

Let `(C, J)` be a site and `R` a sheaf of rings on it.  The underlying abelian sheaf of an
injective sheaf of `R`-modules is in general not an injective abelian sheaf, but it is
*right acyclic* for the global sections functor `Γ(C, -)` of abelian sheaves, in the sense of
[Stacks, Tag 0157]: the single complex on it computes `RΓ(C, -)` on `D⁺(Ab(C))`.  This is the
acyclicity input of [Stacks, Tag 03FD], here stated with no smallness hypothesis on the site and
with the universes of the site, of the ring and of the modules independent.

## Main results

* `Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_of_ext_eq_zero` — an abelian sheaf with no
  higher `Ext` out of the constant sheaf on `ℤ` is right acyclic for `Γ(C, -)`.
* `Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_toSheaf_obj_of_injective` — the underlying
  abelian sheaf of an injective sheaf of `R`-modules is right acyclic for `Γ(C, -)`.

## Implementation notes

`Γ(C, -)` is corepresented by the constant sheaf `ℤ_C` on `ℤ`
(`Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation`), so its right derived
functors are `Ext^n(ℤ_C, -)` (`ModuleSheafCohomology.rightDerivedCoyonedaSuccIso`), and for a
left exact functor right acyclicity is the vanishing of the higher right derived functors.  The
`Ext`-vanishing at the underlying abelian sheaf of an injective module is
`Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`, the constant sheaf on `ℤ` being the
sheafification of a sectionwise torsion-free presheaf.

The additivity of `Γ(C, -)` is taken as an instance argument: it always holds
(`Stacks.Cohomology.GlobalSections.additive_Γ`), but stated universe-polymorphically at the
coefficient universe `max u w` it cannot be found by instance search, the universe constraint
`max u ?w = max u w` being left unsolved; at a concrete site it is an existing instance.

The coefficient universe is `max u w` resp. `max u r w`, which is what
`Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation` (it must contain the objects of
the site) and `Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree` (it must contain the ring)
require.  Nothing here carries a tag: the statements are the acyclicity input of
[Stacks, Tag 03FD] at a generality the source does not state separately.

## References

* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w₁ w₂ w r v u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.Cohomology.GlobalSections

section Ext

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u w}] [HasGlobalSectionsFunctor J AddCommGrpCat.{max u w}]
  [(Sheaf.Γ J AddCommGrpCat.{max u w}).Additive]
  [HasExt.{max u w} (Sheaf J AddCommGrpCat.{max u w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u w})]
  [HasDerivedCategory.{w₁} (Sheaf J AddCommGrpCat.{max u w})]
  [HasDerivedCategory.{w₂} AddCommGrpCat.{max u w}]

/-- **An abelian sheaf with no higher `Ext` out of the constant sheaf on `ℤ` is right acyclic
for `Γ(C, -)`.**  The higher right derived functors of `Γ(C, -)` are the `Ext`-groups out of the
constant sheaf on `ℤ`, which corepresents it. -/
theorem rightAcyclic_Γ_of_ext_eq_zero (F : Sheaf J AddCommGrpCat.{max u w})
    (hF : ∀ (n : ℕ) (e : Ext.{max u w} ((constantSheaf J AddCommGrpCat.{max u w}).obj
      (AddCommGrpCat.of (ULift.{max u w} ℤ))) F (n + 1)), e = 0) :
    (Sheaf.Γ J AddCommGrpCat.{max u w}).rightAcyclic F := by
  rw [rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have : Subsingleton (Ext.{max u w} ((constantSheaf J AddCommGrpCat.{max u w}).obj
      (AddCommGrpCat.of (ULift.{max u w} ℤ))) F (n + 1)) :=
    ⟨fun a b => (hF n a).trans (hF n b).symm⟩
  have hExt : IsZero ((extFunctorObj ((constantSheaf J AddCommGrpCat.{max u w}).obj
      (AddCommGrpCat.of (ULift.{max u w} ℤ))) (n + 1)).obj F) :=
    show IsZero (AddCommGrpCat.of (Ext.{max u w} ((constantSheaf J AddCommGrpCat.{max u w}).obj
      (AddCommGrpCat.of (ULift.{max u w} ℤ))) F (n + 1))) from
    AddCommGrpCat.isZero_of_subsingleton _
  exact hExt.of_iso
    ((ModuleSheafCohomology.rightDerivedIso (globalSectionsCorepresentation.{w} J) (n + 1)).app F ≪≫
      (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso _ n).app F)

end Ext

section Modules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u r w}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u r w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u r w}]
  [(Sheaf.Γ J AddCommGrpCat.{max u r w}).Additive]
  [HasExt.{max u r w} (Sheaf J AddCommGrpCat.{max u r w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u r w})]
  [HasDerivedCategory.{w₁} (Sheaf J AddCommGrpCat.{max u r w})]
  [HasDerivedCategory.{w₂} AddCommGrpCat.{max u r w}]

/-- **The underlying abelian sheaf of an injective sheaf of modules is right acyclic for
`Γ(C, -)`**, on any site, with the ring universe and the module universe independent.  Its
higher `Ext` out of the constant sheaf on `ℤ` vanishes because that sheaf is the sheafification
of a sectionwise torsion-free presheaf (`Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`). -/
theorem rightAcyclic_Γ_toSheaf_obj_of_injective (R : Sheaf J RingCat.{r})
    (I : SheafOfModules.{max u r w} R) [Injective I] :
    (Sheaf.Γ J AddCommGrpCat.{max u r w}).rightAcyclic ((SheafOfModules.toSheaf R).obj I) :=
  rightAcyclic_Γ_of_ext_eq_zero.{w₁, w₂, max r w} J _ fun n e =>
    Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{max u r w, max u w, r, v, u} J R I _
      (ModuleSheafCohomology.isTorsionFree_sheafify J _
        (fun _ => (Module.Flat.isTorsionFree : Module.IsTorsionFree ℤ (ULift.{max u r w} ℤ)))) n e

end Modules

end Stacks.Cohomology.GlobalSections

end
