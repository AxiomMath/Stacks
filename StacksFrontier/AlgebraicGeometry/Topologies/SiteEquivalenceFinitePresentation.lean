module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteEquivalenceTensor

/-!
# Reindexing along an equivalence of ringed sites preserves finite presentation

Let `e : C' ≌ C` be an equivalence of sites and `𝒪` a sheaf of commutative rings on `C`. The
functor of `Stacks.SheafOfModules.reindexEquivalence` — the direct image along `e.functor` — is
the pullback of modules along the morphism of ringed topoi presented by `e.inverse`
(`Stacks.SheafOfModules.pullbackModulesReindexIso`), so by Stacks 03DO it carries sheaves of
modules of finite presentation to sheaves of modules of finite presentation.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_reindexEquivalence_functor_obj`: the
  reindexing of a sheaf of modules of finite presentation is of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (e : C' ≌ C) [e.functor.IsContinuous J' J]
  (O : Sheaf J CommRingCat.{w}) [IsMorphismOfSites.{w} e.inverse J J']
  [J.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C] [LocallySmall.{w} C']
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C', HasWeakSheafify (J'.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C', (J'.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Reindexing along an equivalence of ringed sites preserves finite presentation.** It is the
pullback of modules along the morphism of ringed topoi presented by `e.inverse`, so this is
Stacks 03DO. -/
theorem isFinitePresentation_reindexEquivalence_functor_obj
    (M : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hM : M.IsFinitePresentation) :
    ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e
      ((Stacks.SheafOfModules.Tensor.ringSheaf O))).functor.obj
        M).IsFinitePresentation := by
  have := hM
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    ((pullbackModulesReindexIso J' e O).app M)
    (Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules
      (reindexRingedToposModulesHom J' e O) M)

end Stacks.SheafOfModules

end
