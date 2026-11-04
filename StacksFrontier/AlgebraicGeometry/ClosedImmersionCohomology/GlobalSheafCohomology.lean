module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import
  StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer

/-!
# Cohomology does not change along a closed immersion, in the group-valued spellings

For a closed immersion of schemes `v : Z ⟶ X` and a sheaf of modules `G` on `Z`,

`Hⁿ(Z, G) ≅ Hⁿ(X, v_* G)`

as abelian groups, in both of the library's group-valued models of global cohomology: `Hgroup`,
the right derived functor of sections over `⊤`, and `CategoryTheory.Sheaf.H`, Mathlib's
`Ext`-theoretic sheaf cohomology of the underlying abelian sheaf.

## Main results

* `Stacks.Cohomology.ClosedImmersion.hgroupPushforwardIso` and
  `isZero_hgroup_iff_pushforward`: the isomorphism and its vanishing form for `Hgroup`.
* `Stacks.Cohomology.ClosedImmersion.sheafHAddEquivPushforward` and
  `eq_zero_sheafH_pushforward`: the same for `CategoryTheory.Sheaf.H`.

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.ClosedImmersion

universe u

attribute [local instance] HasDerivedCategory.standard

variable {Z X : AlgebraicGeometry.Scheme.{u}} (v : Z ⟶ X)

/-- **Cohomology does not change along a closed immersion**, as abelian groups: for a closed
immersion `v : Z ⟶ X` and any sheaf of modules `G` on `Z`, `Hⁿ(Z, G) ≅ Hⁿ(X, v_* G)`. -/
noncomputable def hgroupPushforwardIso [AlgebraicGeometry.IsClosedImmersion v]
    (G : Z.Modules) (n : ℕ) :
    Hgroup Z.ringCatSheaf ⊤ n G ≅
      Hgroup X.ringCatSheaf ⊤ n
        ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G) :=
  ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
      Z.ringCatSheaf ⊤ n).app G).symm ≪≫
    (Iso.refl _ : (forget₂ (ModuleCat.{u} Γ(Z, ⊤)) AddCommGrpCat.{u}).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections Z).rightDerived n).obj G) ≅
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        ((ModuleCat.restrictScalars v.appTop.hom).obj
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections Z).rightDerived n).obj G))) ≪≫
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).mapIso
      (cohomologyObjIsoPushforward v G n).symm ≪≫
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
      X.ringCatSheaf ⊤ n).app ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G)

/-- **Vanishing of cohomology transfers across a closed immersion in both directions**:
`Hⁿ(Z, G)` is a zero object exactly when `Hⁿ(X, v_* G)` is. -/
theorem isZero_hgroup_iff_pushforward [AlgebraicGeometry.IsClosedImmersion v]
    (G : Z.Modules) (n : ℕ) :
    IsZero (Hgroup Z.ringCatSheaf ⊤ n G) ↔
      IsZero (Hgroup X.ringCatSheaf ⊤ n
        ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G)) :=
  (hgroupPushforwardIso v G n).isZero_iff

/-- **Cohomology does not change along a closed immersion**, in Mathlib's `Ext`-theoretic model:
the degree-`n` sheaf cohomology of the abelian sheaf underlying `G` is that of the one
underlying `v_* G`. -/
noncomputable def sheafHAddEquivPushforward [AlgebraicGeometry.IsClosedImmersion v]
    (G : Z.Modules) (n : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf Z.ringCatSheaf).obj G) n ≃+
      Sheaf.H.{u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G)) n :=
  (Stacks.Cohomology.ModuleComparison.schemeHgroupTopAddEquivSheafH Z n G).symm.trans
    (((hgroupPushforwardIso v G n).addCommGroupIsoToAddEquiv).trans
      (Stacks.Cohomology.ModuleComparison.schemeHgroupTopAddEquivSheafH X n _))

/-- **Vanishing of global sheaf cohomology transfers across a closed immersion**: if every
degree-`n` cohomology class of the abelian sheaf underlying `G` is zero, then so is every
degree-`n` class of the one underlying `v_* G`. -/
theorem eq_zero_sheafH_pushforward [AlgebraicGeometry.IsClosedImmersion v]
    (G : Z.Modules) (n : ℕ)
    (h : ∀ y : Sheaf.H.{u} ((SheafOfModules.toSheaf Z.ringCatSheaf).obj G) n, y = 0)
    (y : Sheaf.H.{u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G)) n) : y = 0 :=
  have := (Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH
    X n ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G)).1
      ((isZero_hgroup_iff_pushforward v G n).1
        ((Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH
          Z n G).2 ⟨fun a b => by rw [h a, h b]⟩))
  Subsingleton.elim y 0

end Stacks.Cohomology.ClosedImmersion

end
