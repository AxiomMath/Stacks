module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Cohomology of sheaves of modules on an algebraic stack, for parasitic modules

Let `𝒳` be an algebraic stack and `ℱ` a parasitic sheaf of `𝒪_𝒳`-modules (**Stacks 0773**): its
module of sections vanishes at every object of `𝒳` lying over a scheme flat over `𝒳`.  Part (1) of
**Stacks 0775** asserts that then

`H^i(𝒳, ℱ) = 0` for all `i`.

That statement is proved, with no hypothesis, as
`AlgebraicGeometry.Stack.isZero_ext_uliftUnit_of_isParasitic` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticFlatSubsiteCohomology.lean`. This
file supplies the cohomology of sheaves of modules on `𝒳` at the unlifted structure sheaf, and on
the flat-fppf site of **Stacks 0787**.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.fppfModuleCohomology`: `H^i(𝒳, -) = Ext^i(𝒪_𝒳, -)`.
* `AlgebraicGeometry.Stack.FlatFppf.fppfModuleCohomologyZeroEquivSections`: its degree-zero
  identification with the global sections.
* `AlgebraicGeometry.Stack.FlatFppf.flatFppfModuleCohomology`: the same on the flat-fppf site.

## Implementation notes

Cohomology of sheaves of modules on a site is `Ext` out of the structure sheaf viewed as a module
over itself — Mathlib's `CategoryTheory.Abelian.extFunctorObj` at
`SheafOfModules.unit`, which is what
`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH` is defined to be and what its degree-zero
identification `Stacks.Cohomology.BiggerSiteModules.extZeroEquivSections` pins as the global
sections.

Part (2) of **Stacks 0775** — that `R^i f_* ℱ` is again parasitic — is **not** formalized here.
Its proof needs the description of `R^i f_*` as the sheafification of
`y ↦ H^i_τ(V ×_{y,𝒴} 𝒳, pr^{-1}ℱ)` (Sheaves on Stacks, Lemma 96.21.2), which the library does not
have in any form.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w t

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
  [HasExt.{t} (fppfModules B S hS 𝒳)] [HasExt.{t} (flatFppfModules B S hS 𝒳)]

/-- **Cohomology of sheaves of `𝒪_𝒳`-modules on an algebraic stack**: `H^i(𝒳, -) = Ext^i(𝒪_𝒳, -)`,
the `Ext`-groups out of the structure sheaf of **Stacks 06TV** viewed as a module over itself.

This is `Stacks.Cohomology.BiggerSiteModules.moduleFunctorH` at the unlifted structure sheaf; in
degree zero it is the compatible global sections, by
`Stacks.Cohomology.BiggerSiteModules.extZeroEquivSections`, which is what identifies it as the
cohomology of the source. -/
abbrev fppfModuleCohomology (i : ℕ) : fppfModules B S hS 𝒳 ⥤ AddCommGrpCat.{t} :=
  Abelian.extFunctorObj (SheafOfModules.unit
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids SiteKind.fppf)) i

/-- **Degree zero of `AlgebraicGeometry.Stack.FlatFppf.fppfModuleCohomology` is the global
sections.** `Ext⁰(𝒪_𝒳, ℱ) = Hom(𝒪_𝒳, ℱ) = Γ(𝒳, ℱ)`.  This is what identifies
`fppfModuleCohomology` as *the* cohomology of the source rather than an arbitrary sequence of
functors, and it is the same identification
`Stacks.Cohomology.BiggerSiteModules.extZeroEquivSections` makes for
`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`. -/
def fppfModuleCohomologyZeroEquivSections (F : fppfModules B S hS 𝒳) :
    Abelian.Ext (SheafOfModules.unit
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids SiteKind.fppf)) F 0 ≃ F.sections :=
  Abelian.Ext.addEquiv₀.toEquiv.trans (SheafOfModules.unitHomEquiv F)

/-- **Cohomology of sheaves of modules on the flat-fppf site**, the same `Ext`-groups out of the
restricted structure sheaf of **Stacks 0788**, `flat_ringed`. -/
abbrev flatFppfModuleCohomology (i : ℕ) : flatFppfModules B S hS 𝒳 ⥤ AddCommGrpCat.{t} :=
  Abelian.extFunctorObj (SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (ringedTopos B S hS 𝒳).O)) i

end AlgebraicGeometry.Stack.FlatFppf

end
