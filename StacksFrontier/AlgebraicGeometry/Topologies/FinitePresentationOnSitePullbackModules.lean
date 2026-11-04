module

public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationAssembly
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Pullback of modules preserves finite presentation on a site

Declarations extending
`StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses`
(`pullbackModules_isFinitePresentationOnSite_of_isFinitePresentation`), kept in their own module
so that the base file is unchanged.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{m}}
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

end SheafOfModules

namespace Stacks.Sheaves.FinitePresentation

open AlgebraicGeometry Stacks.Sheaves.PresentationTransport
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback

universe v' u' w

/-- **Stacks 03DO, from Mathlib's finite presentation to finite presentation on the site.**  The
pullback `f^*F` along a morphism of ringed topoi of a sheaf of modules of finite presentation in
the sense of Mathlib is of finite presentation on the site, Stacks 03DL(7): the inverse image
produces a covering of each object of the source site on whose members `f⁻¹F` has a finite
presentation, and extension of scalars carries those presentations across `f⁻¹O_D ⟶ O_C`. -/
theorem pullbackModules_isFinitePresentationOnSite_of_isFinitePresentation
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ Z : X.C, HasWeakSheafify (X.J.over Z) AddCommGrpCat.{w}]
    [∀ Z : Y.C, HasWeakSheafify (Y.J.over Z) AddCommGrpCat.{w}]
    [∀ Z : X.C, (X.J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ Z : Y.C, (Y.J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [F.IsFinitePresentation] :
    ((f.pullbackModules).obj F).IsFinitePresentationOnSite := by
  refine ⟨fun V => ?_⟩
  obtain ⟨T, hT⟩ := exists_cover_isFinite_presentation_inverseImage f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    (pullbackModule X.J Y.J f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) F V
  refine ⟨Σ W : X.C, {g : W ⟶ V // T.1 g}, fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine X.J.superset_covering (fun Z g hg => ?_) T.2
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Z, g, hg⟩, 𝟙 Z, (Category.id_comp g).symm⟩
  · obtain ⟨P, hP⟩ := hT i.1 i.2.1 i.2.2
    exact SheafOfModules.HasFiniteGlobalPresentation.of_presentation'
      (presentationExtendScalarsOver (fSharpCommRing f)
        (ToposPushforward.inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        i.1 P)
      (isFinite_presentationExtendScalarsOver (fSharpCommRing f) _ _ _ i.1 P hP)

end Stacks.Sheaves.FinitePresentation

end
