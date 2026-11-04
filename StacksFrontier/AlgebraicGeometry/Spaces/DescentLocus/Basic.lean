module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# The descent condition of Stacks 0D23

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and `E` an `𝒪_X`-module on
the small étale site. For a morphism `g : Y' ⟶ Y` with base change square

```
X' = X ×_Y Y' --g'--> X
      |f'              |f
      v                v
      Y'  -----g---->  Y
```

Stacks 0D23 considers the condition that `(g')^*E` is the pullback `(f')^*N` of a finite locally
free `𝒪_{Y'}`-module `N`. This file names that condition.

## Main definitions

* `AlgebraicGeometry.Space.HasDescentAt`: the condition at `g`.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The descent condition of Stacks 0D23 at a morphism `g : Y' ⟶ Y`.** The pullback of `E`
along the projection `g' : X ×_Y Y' ⟶ X` is isomorphic to the pullback, along the projection
`f' : X ×_Y Y' ⟶ Y'`, of a finite locally free `𝒪_{Y'}`-module `N`. -/
def HasDescentAt {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (E : Modules.{u, u} B S hS X.1 X.2)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) : Prop :=
  ∃ N : Modules.{u, u} B S hS Y'.1 Y'.2, SheafOfModules.IsFiniteLocallyFree N ∧
    Nonempty ((modulePullback B S hS (pullback.snd f g)).obj N ≅
      (modulePullback B S hS (pullback.fst f g)).obj E)

end AlgebraicGeometry.Space

end
