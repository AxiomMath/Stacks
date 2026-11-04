module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteCokernel

/-!
# The cokernel of a map of coherent modules on a locally Noetherian stack (Stacks 0GR9, part (1))

Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of coherent
`𝒪_𝒳`-modules.  **Stacks 0GR9** part (1) says that the cokernel of `φ` computed in `Mod(𝒪_𝒳)` is
again coherent.  That is proved here with coherence read as **Stacks 0GR6**, that is as
`AlgebraicGeometry.Stack.IsCoherent`, the conjunction of the two conditions of Stacks 0GR5 this
library states.

## Main results

* `AlgebraicGeometry.Stack.isCoherentModule_cokernel`: **Stacks 0GR9** part (1) with coherence
  read as condition (2) of Stacks 0GR5, finite presentation on the big fppf site.
* `AlgebraicGeometry.Stack.isCoherent_cokernel`: **Stacks 0GR9** part (1) with coherence read as
  Stacks 0GR6, `AlgebraicGeometry.Stack.IsCoherent`.

## Implementation notes

**Which reading of "coherent" is used.**  Stacks 0GR6 calls an `𝒪_𝒳`-module coherent when it
satisfies the equivalent conditions of Stacks 0GR5.  `AlgebraicGeometry.Stack.IsCoherent` is the
conjunction of conditions (1), quasi-coherent of finite type, and (2), of finite presentation, and
is equivalent to condition (2) alone on a locally Noetherian algebraic stack, by
`AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule`.  So the clause reduces to the statement
that a cokernel of a map of modules of finite presentation on the fppf site of `𝒳` is of finite
presentation, and that is a theorem over an arbitrary site: it is Stacks 0H98, proved for the
covering-family condition of Stacks 03DL(7) at
`Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel`.

This is not the sectionwise coherence `SheafOfModules.IsCoherentOnSite` of Stacks 03DL(8) that
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentKernelCokernelLocallyNoetherian` reads the clauses
of Stacks 0GR9 in; that condition is strictly stronger, by
`AlgebraicGeometry.Stack.isCoherent_of_isCoherentOnSite`.

**Local Noetherianity is used.**  It enters through
`AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule`, which turns condition (2) of
Stacks 0GR5 back into the conjunction defining `IsCoherent`.
`AlgebraicGeometry.Stack.isCoherentModule_cokernel`, stated for condition (2) alone, does not use
it and carries it because the source has it.

**The module universe is the universe `u` of the schemes.**  That is the universe in which
`Mod(𝒪_𝒳)` has cokernels: sheafification of presheaves of abelian groups with sections in the
universe of the coefficient rings is
`AlgebraicGeometry.Stack.hasSheafifyAddCommGrpCat_associatedTopology`, which holds because the
fppf site of `𝒳` is essentially small in `u`
(`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`, an instance).  The proof needs the
same on every slice of that site, and the slices are essentially small too, by
`AlgebraicGeometry.Stack.essentiallySmall_over_obj`; the two instances recording that are the
first declarations below.

## References

* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w t

namespace AlgebraicGeometry.Stack

section Slices

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (τ : GrothendieckTopology B.Schemes) [EssentiallySmall.{u} X]

/-- Sheafification of presheaves of abelian groups with sections in the universe of the structure
sheaf of **Stacks 06TV** exists on every slice of the site of **Stacks 06TP**, that slice being
again essentially small in that universe.  This is the slice form of
`AlgebraicGeometry.Stack.hasSheafifyAddCommGrpCat_associatedTopology`. -/
instance hasSheafifyAddCommGrpCat_over_associatedTopology (V : X) :
    HasSheafify ((associatedTopology B S hS p τ).over V) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{w, u, max v w, u + 1, u} _ _

/-- On every slice of the site of **Stacks 06TP**, sheafification of presheaves of abelian groups
inverts exactly the locally bijective morphisms.  This is the slice form of
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_associatedTopology`. -/
instance wEqualsLocallyBijective_over_associatedTopology (V : X) :
    ((associatedTopology B S hS p τ).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{w, u, max v w, u + 1, u} _

end Slices

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, t} B S hS)

/-- **Stacks 0GR9, part (1), with coherence read as condition (2) of Stacks 0GR5.**  Let `𝒳` be a
locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of `𝒪_𝒳`-modules of finite presentation
on the big fppf site of `𝒳`.  The cokernel of `φ` computed in `Mod(𝒪_𝒳)` is of finite
presentation.

The content is Stacks 0H98 on the fppf site of `𝒳`, at
`Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel`: a cokernel of a map whose source is
of finite type and whose target is of finite presentation is of finite presentation, and a module
of finite presentation is of finite type.  Local Noetherianity is the hypothesis of the source
and is not used here; it is used in
`AlgebraicGeometry.Stack.isCoherent_cokernel`. -/
theorem isCoherentModule_cokernel
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hF : IsCoherentModule B S hS 𝒳 F) (hG : IsCoherentModule B S hS 𝒳 G) (φ : F ⟶ G) :
    IsCoherentModule B S hS 𝒳 (cokernel φ) :=
  have := hF
  _root_.Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel φ inferInstance hG

/-- **Stacks 0GR9, part (1).**  Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a
map of coherent `𝒪_𝒳`-modules.  The cokernel of `φ` computed in `Mod(𝒪_𝒳)` is a coherent
`𝒪_𝒳`-module.

Coherence is `AlgebraicGeometry.Stack.IsCoherent`, the reading of Stacks 0GR6 as the conjunction
of the conditions (1) and (2) of Stacks 0GR5 this library states.  On a locally Noetherian
algebraic stack that conjunction is condition (2) alone, by
`AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule`, so the clause is
`AlgebraicGeometry.Stack.isCoherentModule_cokernel`; local Noetherianity is used, in that
reduction. -/
@[stacks 0GR9 "part (1): the cokernel computed in Mod(O_X) of a map of coherent modules \
  (Stacks 0GR6) is coherent"]
theorem isCoherent_cokernel
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hF : IsCoherent B S hS 𝒳 F) (hG : IsCoherent B S hS 𝒳 G) (φ : F ⟶ G) :
    IsCoherent B S hS 𝒳 (cokernel φ) :=
  (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).mpr
    (isCoherentModule_cokernel B S hS 𝒳 h𝒳
      ((isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 F).mp hF)
      ((isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 G).mp hG) φ)

end AlgebraicGeometry.Stack

end
