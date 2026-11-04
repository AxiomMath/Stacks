module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of `Rf_*` for a morphism of representable algebraic spaces

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated representable algebraic spaces
over `S`, represented by a morphism of schemes `f_0 : X_0 ⟶ Y_0`.  The right adjoint
`a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` of `Rf_*` of Stacks 0E55 and the right adjoint
`a_0 : D_QCoh(𝒪_{Y_0}) ⥤ D_QCoh(𝒪_{X_0})` of `Rf_{0,*}` of Stacks 0A9E correspond under the
equivalences of Stacks 071Q (Stacks 0E6E): the two derived direct images correspond by
Stacks 08GH, and right adjoints are unique.

## Main results

* `AlgebraicGeometry.Space.representedRightAdjointIso`: Stacks 0E6E.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u})) {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hXqc : IsQuasiCompactSpace B S hS (yoneda.obj T'))
  (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T'))
  (hYqc : IsQuasiCompactSpace B S hS (yoneda.obj T))
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T))

include hZ hXqc hYqs in
/-- The represented morphism of quasi-compact and quasi-separated algebraic spaces is
quasi-compact. -/
theorem representedSpaceMap_isQuasiCompact :
    IsQuasiCompact B S hS (representedSpaceMap B S hS g).hom :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (representedSpace T).2 hYqs hXqc
    (representedSpaceMap B S hS g).hom

include hZ hXqs in
/-- The represented morphism of algebraic spaces with quasi-separated source is quasi-separated. -/
theorem representedSpaceMap_isQuasiSeparated :
    IsQuasiSeparated B S hS (representedSpaceMap B S hS g).hom :=
  isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ
    (representedSpace T').2 hXqs (representedSpaceMap B S hS g).hom

/-- **Stacks 08GH, the second square, for the functor `Rf_{0,*}` of Stacks 0A9E**, for a
quasi-compact and quasi-separated morphism of schemes with quasi-compact target. -/
def representedQcqsRestrictedDerivedPushforwardIso [CompactSpace (B.inclusion.obj T.left)]
    [QuasiCompact (B.inclusion.map g.left)] [QuasiSeparated (B.inclusion.map g.left)]
    (hfqc : IsQuasiCompact B S hS (representedSpaceMap B S hS g).hom)
    (hfqs : IsQuasiSeparated B S hS (representedSpaceMap B S hS g).hom) :
    Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward (B.inclusion.map g.left) ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor ≅
      (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ⋙
        quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g) hfqc hfqs :=
  representedQuasicoherentDerivedPushforwardIsoOfCompιIso g hfqc hfqs
    (@Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward _ _
      (B.inclusion.map g.left)
      ‹_› ‹_› (inferInstanceAs (CompactSpace (B.inclusion.obj T.left))))
    (ObjectProperty.liftCompιIso _ _ _)

/-- **Stacks 0E6E.** Let `f : X ⟶ Y` be the morphism of quasi-compact and quasi-separated
representable algebraic spaces over `S` represented by a morphism `g : T' ⟶ T` of the big fppf
site, with underlying morphism of schemes `f_0 = g_0 : X_0 ⟶ Y_0`.  Let `a` be the right adjoint
of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of Stacks 0E55 and `a_0` the right adjoint of
`Rf_{0,*} : D_QCoh(𝒪_{X_0}) ⥤ D_QCoh(𝒪_{Y_0})` of Stacks 0A9E.  Then `a_0` and `a` correspond
under the equivalences `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)`, `D_QCoh(𝒪_{Y_0}) ≌ D_QCoh(𝒪_Y)` of
Stacks 071Q. -/
@[stacks 0E6E]
def representedRightAdjointIso :
    haveI : CompactSpace (B.inclusion.obj T'.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
    haveI : CompactSpace (B.inclusion.obj T.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
    haveI :=
      Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
        (B.inclusion.map g.left)
    haveI := isLeftAdjoint_quasicoherentDerivedPushforward hZ (representedSpaceMap B S hS g)
      hXqc hXqs hYqs
    (Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward
        (B.inclusion.map g.left)).rightAdjoint ⋙
        (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor ≅
      (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor ⋙
        (quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g)
          (representedSpaceMap_isQuasiCompact hZ g hXqc hYqs)
          (representedSpaceMap_isQuasiSeparated hZ g hXqs)).rightAdjoint :=
  haveI : CompactSpace (B.inclusion.obj T'.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
  haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
  haveI : CompactSpace (B.inclusion.obj T.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
  haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
  haveI := Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
    (B.inclusion.map g.left)
  haveI := isLeftAdjoint_quasicoherentDerivedPushforward hZ (representedSpaceMap B S hS g)
    hXqc hXqs hYqs
  (CatCommSq.hInv (representedDualityQuasicoherentDerivedEquivalence B S hS T).symm _ _
    (representedDualityQuasicoherentDerivedEquivalence B S hS T').symm
    ⟨(conjugateIsoEquiv
      ((representedDualityQuasicoherentDerivedEquivalence B S hS T').toAdjunction.comp
        (Adjunction.ofIsLeftAdjoint _))
      ((Adjunction.ofIsLeftAdjoint _).comp
        (representedDualityQuasicoherentDerivedEquivalence B S hS T).toAdjunction)
      (representedQcqsRestrictedDerivedPushforwardIso g
        (representedSpaceMap_isQuasiCompact hZ g hXqc hYqs)
        (representedSpaceMap_isQuasiSeparated hZ g hXqs))).symm⟩).iso.symm

end AlgebraicGeometry.Space
