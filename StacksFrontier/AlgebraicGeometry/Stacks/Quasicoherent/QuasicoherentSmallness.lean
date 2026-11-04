module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInputs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules

/-!
# Smallness of the module categories on a category fibred in groupoids

The special adjoint functor theorem that builds the coherator of **Stacks 0778** and
**Stacks 0781** part (2) asks three size conditions of the categories it runs on: that
`QCoh(𝒪_𝒳)` be locally `u`-small, that `LQCoh^fbc(𝒪_𝒳)` be locally `u`-small, and that
`QCoh(𝒪_𝒳)` be well-copowered at `u`.  Here `u` is the universe of the schemes, while the
objects of `𝒳` live in `Type (u + 1)` and a morphism of module sheaves is a family of module
maps indexed by them, so none of the three is automatic.

All three hold, and for one reason: `𝒳` is essentially `u`-small.  An essentially `u`-small
site has sheafification for `AddCommGrpCat.{u}`-valued presheaves and its sheaves of modules
over a `RingCat.{u}`-valued structure sheaf form a Grothendieck abelian category at `u`
(`AlgebraicGeometry.SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`), and local
`u`-smallness is one of the four conditions in that package.  It passes to a full subcategory,
which both `QCoh(𝒪_𝒳)` and `LQCoh^fbc(𝒪_𝒳)` are.

Well-copoweredness is not inherited that way, because a monomorphism of `QCoh(𝒪_𝒳)` need not
be a monomorphism of `Mod(𝒪_𝒳)` — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentKernelCokernel.lean`.  It is
instead the separator: a separator of an abelian category is a detector, a detecting family of
`u`-small index in a category with pullbacks and locally `u`-small makes it well-powered at
`u`, and a well-powered abelian category is well-copowered.

## Main results

* `CategoryTheory.wellPowered_op_of_hasSeparator`: an abelian category which is locally
  `w`-small and has a separator is well-copowered at `w`.
* `AlgebraicGeometry.Stack.locallySmall_quasicoherentOfStack` and
  `AlgebraicGeometry.Stack.wellPowered_op_quasicoherentOfStack`: `QCoh(𝒪_𝒳)` of an algebraic
  stack is locally `u`-small and well-copowered at `u`, by
  `AlgebraicGeometry.FibredSite.locallySmall_quasicoherentModules` and
  `AlgebraicGeometry.FibredSite.wellPowered_op_quasicoherentModules`.
* `AlgebraicGeometry.Stack.locallySmall_locallyQuasicoherentFlatBaseChangeModules`:
  `LQCoh^fbc(𝒪_𝒳)` is locally `u`-small.

## Implementation notes

The two sheafification inputs of
`AlgebraicGeometry.SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` are supplied here
rather than taken as hypotheses: on an essentially `u`-small site they are
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`, which ask for
nothing beyond that smallness.  The two topologies involved are spelled differently — the fppf
one as `AlgebraicGeometry.BigFppfOver.associatedTopology … AlgebraicGeometry.SiteKind.fppf` and
the étale one as `AlgebraicGeometry.Stack.associatedTopology … (etaleTopology B)` — and instance
search keys on the syntax, so each statement supplies its own pair.

`CategoryTheory.wellPowered_op_of_hasSeparator` is stated for an abstract abelian category
rather than inlined.  Instance search for `CategoryTheory.Balanced` and
`CategoryTheory.Limits.HasPullbacks` at the unfolded spelling of `QCoh(𝒪_𝒳)` — a
`CategoryTheory.ObjectProperty.FullSubcategory` of a category of sheaves of modules — exhausts
the default heartbeat budget, while at an abstract `[Abelian C]` it is immediate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

/-- **An abelian category which is locally `w`-small and has a separator is well-copowered at
`w`.**  The separator is a detector because the category is balanced, a single object is a
`w`-small family, and a category with pullbacks which is locally `w`-small and has a `w`-small
detecting family is well-powered at `w`; a well-powered abelian category is well-copowered. -/
theorem CategoryTheory.wellPowered_op_of_hasSeparator {C : Type*} [Category C] [Abelian C]
    [LocallySmall.{w} C] [HasSeparator C] : WellPowered.{w} Cᵒᵖ :=
  have : WellPowered.{w} C :=
    wellPowered_of_isDetecting (isSeparator_separator C).isDetector
  inferInstance

namespace AlgebraicGeometry.Stack

section FibredGroupoid

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **`LQCoh^fbc(𝒪_𝒳)` is locally `u`-small**, for `𝒳` a category fibred in groupoids over the
big fppf site of `S` which is essentially small at the universe `u` of the schemes.

As for `AlgebraicGeometry.FibredSite.locallySmall_quasicoherentModules`: the modules on the
associated étale site are Grothendieck abelian at `u` because that site is essentially
`u`-small, and local `u`-smallness passes to the full subcategory of the locally quasi-coherent
modules with the flat base change property. -/
theorem locallySmall_locallyQuasicoherentFlatBaseChangeModules :
    LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp) :=
  have : HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  have : (associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
  have := (SheafOfModules.isGrothendieckAbelian_of_essentiallySmall
    (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))).locallySmall
  inferInstance

end FibredGroupoid

section Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`QCoh(𝒪_𝒳)` is locally `u`-small** for an algebraic stack `𝒳`: the size hypothesis `hls`
of the construction of the coherator in **Stacks 0778** and of the adjoint functor theorem in
**Stacks 0781** part (1), discharged.

It is `AlgebraicGeometry.FibredSite.locallySmall_quasicoherentModules` at the structure functor
of `𝒳`, whose essential `u`-smallness is
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`. -/
theorem locallySmall_quasicoherentOfStack :
    LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
  FibredSite.locallySmall_quasicoherentModules B S hS _ _

attribute [local instance] locallySmall_quasicoherentOfStack

/-- **`LQCoh^fbc(𝒪_𝒳)` is locally `u`-small** for an algebraic stack `𝒳`: the size hypothesis
`hlsD` of the construction of the coherator in **Stacks 0778**, discharged.

It is `AlgebraicGeometry.Stack.locallySmall_locallyQuasicoherentFlatBaseChangeModules` at the
structure functor of `𝒳`. -/
theorem locallySmall_flatBaseChangeOfStack :
    LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u}
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
  locallySmall_locallyQuasicoherentFlatBaseChangeModules B E h S hS _ _

/-- **`QCoh(𝒪_𝒳)` is well-copowered at `u`** for an algebraic stack `𝒳`: the size hypothesis
`hwp` of the construction of the coherator in **Stacks 0778**, discharged from the separator.

It is `AlgebraicGeometry.FibredSite.wellPowered_op_quasicoherentModules` at the structure
functor of `𝒳`. -/
theorem wellPowered_op_quasicoherentOfStack
    [Abelian (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)]
    (_hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)) :
    WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)ᵒᵖ :=
  FibredSite.wellPowered_op_quasicoherentModules B S hS _ _

end Stack

end AlgebraicGeometry.Stack

end
