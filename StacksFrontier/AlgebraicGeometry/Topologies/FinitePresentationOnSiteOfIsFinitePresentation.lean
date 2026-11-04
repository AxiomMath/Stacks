module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesId
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSitePullbackModules

/-!
# From Mathlib's finite presentation to finite presentation on the site

On a ringed topos whose slices admit sheafification, a sheaf of modules of finite presentation in
the sense of Mathlib (`SheafOfModules.IsFinitePresentation`, a finite presentation on the members
of a covering of the final object) is of finite presentation on the site in the sense of
Stacks 03DL(7) (`SheafOfModules.IsFinitePresentationOnSite`, a finite presentation on a covering of
every object). It is its own pullback along the identity, to which Stacks 03DO applies.
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.Sheaves.FinitePresentation

open Stacks.Sheaves.RingedToposModules

/-- **Finite presentation in the sense of Mathlib is finite presentation on the site**,
Stacks 03DL(7), on a ringed topos whose slices admit sheafification. -/
theorem isFinitePresentationOnSite_of_isFinitePresentation
    {X : _root_.AlgebraicGeometry.RingedTopos.{v, u, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [F.IsFinitePresentation] :
    F.IsFinitePresentationOnSite :=
  SheafOfModules.IsFinitePresentationOnSite.of_iso
    ((Adjunction.leftAdjointUniq (pullbackAdjPushforwardModules (RingedToposHom.id X))
      (Adjunction.id.ofNatIsoRight (pushforwardModulesIdIso X).symm)).app F)
    (pullbackModules_isFinitePresentationOnSite_of_isFinitePresentation (RingedToposHom.id X) F)

end Stacks.Sheaves.FinitePresentation

end
