module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.ConormalEquations.RankGenerators
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.EpiIso

/-!
# The conormal map of a cartesian square of immersions of equal conormal rank

For a cartesian square of immersions

```
Z  --i-->  X
|f         |g
Z' --i'--> X'
```

the canonical map `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks, Tag 01R4] is an epimorphism
(`Stacks.Immersion.epi_immersionConormalSheafMap`). If both conormal sheaves are finite locally
free of the same rank `c`, it is an isomorphism, since an epimorphism of finite locally free
sheaves of the same rank is one. This is the hypothesis on the conormal sheaves in the base change
of the Gysin map, [Stacks, Tag 0G89] and [Stacks, Tag 0G8D], for instance for the base change of
a section of a smooth morphism of relative dimension `c`.

## Main results

* `Stacks.Immersion.isIso_immersionConormalSheafMap_of_conormalRank`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ConormalEquations

namespace Stacks.Immersion

universe u

variable {Z X Z' X' : Scheme.{u}}

/-- **The conormal map of a cartesian square of immersions whose conormal sheaves are finite
locally free of the same rank is an isomorphism.** -/
theorem isIso_immersionConormalSheafMap_of_conormalRank (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X') (sq : IsPullback i f g i')
    {c : ℕ} (hE : ConormalRank i c) (hE' : ConormalRank i' c) :
    IsIso (immersionConormalSheafMap i i' f g (toShHom_square sq.w)) := by
  have hepi := epi_immersionConormalSheafMap i i' f g sq
  have h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((modulePullback f.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf i')) c :=
    Stacks.Chow.isFiniteLocallyFreeOfRank_modulePullback f _ c hE'
  have h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheaf i) c := hE
  exact @AlgebraicGeometry.SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfRank Z
    ((modulePullback f.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf i'))
    (Stacks.Conormal.conormalSheaf i) _ hepi c h₁ h₂

end Stacks.Immersion
