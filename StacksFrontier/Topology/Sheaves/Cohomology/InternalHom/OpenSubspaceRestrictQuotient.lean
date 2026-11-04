module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedIsoOpenSubspace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelLocalClosureRecognition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientRingSheafOpenSubspaceIdeal
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# The restriction to an open subspace of a quotient of the structure sheaf

Let `X` be a ringed space, `U` an open of it and `Φ : F ⟶ O_X` a morphism of sheaves of
`O_X`-modules into the structure sheaf; its cokernel is the quotient `O_X/I` by the sheaf of
ideals `I` that `Φ` generates. **This file identifies the restriction of that quotient to
`X|_U` with the quotient formed over `U` by any morphism generating there the same sheaf of
ideals.**

Two steps, and both are needed because the quotient over `U` that the local statements of a
tag use is not built by restricting anything: it is built on `X|_U` in its own right, from
sections read there. The first step is that restriction commutes with the quotient —
restriction to the slice site over `U` and the transport off that site are both exact, so the
restriction of a cokernel is the cokernel of the restriction. The second is the recognition
`Stacks.Sites.cokernelIsoOfSectionIdealEq`: two morphisms into the structure sheaf of `X|_U`
generating sheaves of ideals with the same sections have the same cokernel.

## Main definitions

* `Stacks.SheafOfModules.openSubspaceRestrictHom`: the restriction to `X|_U` of a morphism into
  the structure sheaf of `X`, with its target written as the structure sheaf of `X|_U`.
* `Stacks.SheafOfModules.openSubspaceRestrictCokernelIso`: **restriction to an open subspace
  commutes with forming the quotient.**
* `Stacks.SheafOfModules.openSubspaceRestrictQuotientIso`: **the identification.** The
  restriction of `O_X/I` to `U` is the quotient of the structure sheaf of `X|_U` by a morphism
  generating the same sheaf of ideals there.
* `Stacks.SheafOfModules.openSubspaceRestrictQuotientIsoOfSlice`: the same identification with
  its hypothesis read on the *slice site* `Opens X / U`, which is where a comparison of two
  sheaves of ideals over `U` is naturally stated.

## Main statements

* `Stacks.SheafOfModules.sectionIdeal_idealOfHom_openSubspaceRestrictHom`: the sheaf of ideals
  the restricted morphism generates on `X|_U` has the sections, over an open of `U`, of the one
  the restriction to the slice site generates over the corresponding slice object. This is
  `Stacks.SheafOfModules.sectionIdeal_idealOfHom_openSubspaceEquiv` at the restriction of a
  global morphism, and it is what turns a slice-site comparison of ideals into the hypothesis of
  the identification.

## Implementation notes

**Where the exactness comes from.** Restriction to the slice site preserves finite colimits
(`Stacks.SheafOfModules.overFunctor_preservesFiniteColimits`, it being a left adjoint) and the
transport off the slice site is one half of an equivalence, so both preserve cokernels and
`CategoryTheory.Limits.PreservesCokernel.iso` applies twice. No exactness statement about
`Stacks.SheafOfModules.openSubspaceRestrictModule` itself is needed, and none is proved here.

**One spelling for the structure sheaf of `X|_U`.** Every statement writes it as
`Stacks.SheafOfModules.openSubspaceRing`, the `Stacks.SheafOfModules.Tensor.ringSheaf` spelling at
the `↥U` spelling of the site: that is the one `Stacks.Sites.idealOfHom` and
`Stacks.Sites.sectionIdeal` are stated at. The target of the restricted morphism and the
category the restricted module lives in are the other spellings, and they are *reducibly* the
same sheaf of rings, so the ascription on `openSubspaceRestrictHom` costs nothing and every
consumer sees one name.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

open Stacks.Sites

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
  [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The restriction to `X|_U` of a morphism into the structure sheaf of `X`**, with its target
ascribed as the structure sheaf of rings of `X|_U` at the spelling the sheaves of ideals are
stated at. -/
abbrev openSubspaceRestrictHom {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X)) :
    openSubspaceRestrictModule U F ⟶ _root_.SheafOfModules.unit (openSubspaceRing U) :=
  (openSubspaceEquiv U).functor.map
    ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map Φ)

/-- **Restriction to an open subspace commutes with forming the quotient of the structure
sheaf.** Both steps of the restriction preserve cokernels: restriction to the slice site is a
left adjoint and the transport off the slice site is an equivalence. -/
def openSubspaceRestrictCokernelIso {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X)) :
    openSubspaceRestrictModule U (cokernel Φ) ≅ cokernel (openSubspaceRestrictHom U Φ) :=
  (openSubspaceEquiv U).functor.mapIso
      (PreservesCokernel.iso (_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U) Φ) ≪≫
    PreservesCokernel.iso (openSubspaceEquiv U).functor
      ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map Φ)

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
  [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The sheaf of ideals generated on `X|_U` by the restriction of a global morphism is the
open-subspace reading of the one its slice-site restriction generates**, on sections. This is
`Stacks.SheafOfModules.sectionIdeal_idealOfHom_openSubspaceEquiv` at a restricted morphism: the
restriction to `X|_U` is by construction the transport off the slice site of the restriction to
the slice site. -/
theorem sectionIdeal_idealOfHom_openSubspaceRestrictHom
    {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ) :
    sectionIdeal (idealOfHom (O := openSubspaceSheaf U) (openSubspaceRestrictHom U Φ)) V =
      sectionIdeal (idealOfHom (O := X.sheaf.over U)
          ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map Φ))
        (op ((openSubspaceSiteFunctor U).obj V.unop)) :=
  sectionIdeal_idealOfHom_openSubspaceEquiv U _ V

/-- **The restriction of a quotient of the structure sheaf is the quotient formed over `U` by any
morphism generating the same sheaf of ideals there.** Restriction commutes with the quotient
(`openSubspaceRestrictCokernelIso`), and two morphisms into the structure sheaf of `X|_U` whose
sheaves of ideals have the same sections have the same cokernel
(`Stacks.Sites.cokernelIsoOfSectionIdealEq`). -/
def openSubspaceRestrictQuotientIso {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X))
    {F' : _root_.SheafOfModules.{u} (openSubspaceRing U)}
    (φ : F' ⟶ _root_.SheafOfModules.unit (openSubspaceRing U))
    (h : ∀ V : (Opens ↥U)ᵒᵖ,
      sectionIdeal (idealOfHom (O := openSubspaceSheaf U)
          (openSubspaceRestrictHom U Φ)) V =
        sectionIdeal (idealOfHom (O := openSubspaceSheaf U) φ) V) :
    openSubspaceRestrictModule U (cokernel Φ) ≅ cokernel φ :=
  openSubspaceRestrictCokernelIso U Φ ≪≫
    cokernelIsoOfSectionIdealEq (openSubspaceRestrictHom U Φ) φ h

/-- **The identification with its hypothesis read on the slice site.** A comparison of two
sheaves of ideals over `U` is naturally stated on `Opens X / U` — that is where the restriction
of a global sheaf of ideals lives — and this is the form in which the identification consumes
it. The two readings are reconciled by
`sectionIdeal_idealOfHom_openSubspaceRestrictHom`. -/
def openSubspaceRestrictQuotientIsoOfSlice {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X))
    {F' : _root_.SheafOfModules.{u} (openSubspaceRing U)}
    (φ : F' ⟶ _root_.SheafOfModules.unit (openSubspaceRing U))
    (h : ∀ V : (Opens ↥U)ᵒᵖ,
      sectionIdeal (idealOfHom (O := openSubspaceSheaf U) φ) V =
        sectionIdeal (idealOfHom (O := X.sheaf.over U)
            ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map Φ))
          (op ((openSubspaceSiteFunctor U).obj V.unop))) :
    openSubspaceRestrictModule U (cokernel Φ) ≅ cokernel φ :=
  openSubspaceRestrictQuotientIso U Φ φ fun V =>
    (sectionIdeal_idealOfHom_openSubspaceRestrictHom U Φ V).trans (h V).symm

end Stacks.SheafOfModules

end
