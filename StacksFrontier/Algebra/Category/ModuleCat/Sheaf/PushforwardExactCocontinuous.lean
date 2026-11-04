module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact

/-!
# Exactness of the direct image of modules along a cocontinuous functor

Let `v : C ⥤ D` be a functor between sites which is both continuous and cocontinuous, and let
`φ : S ⟶ v_* R` make it a morphism of ringed sites. The direct image
`v_* : Mod(R) ⥤ Mod(S)` is then exact.

Exactness on the left is unconditional: the direct image of sheaves of modules is a right
adjoint. Exactness on the right holds because a cocontinuous functor is almost cocontinuous,
which is the hypothesis under which the direct image preserves finite colimits.

## Main results

* `SheafOfModules.exactFunctor_pushforward_of_isCocontinuous`: the direct image of sheaves of
  modules along a continuous and cocontinuous functor of sites is exact.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.PushforwardRightExact

universe uC vC uD vD r m

namespace SheafOfModules

/-- The direct image of sheaves of modules along a functor of sites which is both continuous
and cocontinuous is exact.

A cocontinuous functor is almost cocontinuous, so the direct image preserves finite colimits;
it preserves finite limits because it is a right adjoint. The module universe `m` is
independent of the ring universe `r`.
-/
public theorem exactFunctor_pushforward_of_isCocontinuous
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (v : C ⥤ D)
    [v.IsContinuous J K] [v.IsCocontinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{r} J K).obj R)
    [HasSheafify J AddCommGrpCat.{m}] [HasSheafify K AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    exactFunctor (SheafOfModules.{m} R) (SheafOfModules.{m} S)
      (SheafOfModules.pushforward φ) :=
  ⟨SheafOfModules.preservesFiniteLimits_pushforward φ,
    preservesFiniteColimits_pushforward_of_isAlmostCocontinuous v φ
      (isAlmostCocontinuous_of_isCocontinuous v J K)⟩

end SheafOfModules

end
