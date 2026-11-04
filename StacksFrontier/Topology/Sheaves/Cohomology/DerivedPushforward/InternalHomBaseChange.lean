module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for a derived internal hom

Let

```
X' --h--> X
|         |
f'        f
v         v
S' --g--> S
```

be a commutative square of ringed spaces and let `K, L ∈ D(𝒪_X)`.  Tag 08I4 is the canonical
base change map

`Lg^* Rf_* R𝓗om_{𝒪_X}(K, L) ⟶ R(f')_* R𝓗om_{𝒪_{X'}}(Lh^*K, Lh^*L)`

in `D(𝒪_{S'})`.  The source defines it as adjoint to the composition of three steps: the
identification `L(f')^* Lg^* Rf_* ⟶ Lh^* Lf^* Rf_*` coming from commutativity of the square,
the derived counit `Lf^* Rf_* ⟶ id`, and the canonical map of Tag 08I3.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomBaseChange.derivedBaseChangeSheafHomMap`: **Tag 08I4**,
  the canonical base change map.

## Implementation notes

*How the three steps enter.*  The first two of them are exactly the derived base change map of
Tag 08HY, `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`, whose adjoint
characterization `derivedBaseChangeMap_adjoint` is the composite of the two identifications of
the iterated derived pullbacks around the square with the derived pullback along `h` of the
derived counit — step 1 and step 2 of the source, at the object `R𝓗om_{𝒪_X}(K, L)`.  So the
base change map of this file is that map followed by `R(f')_*` of the map of Tag 08I3,
`Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap`, which is step 3.
Composing in that order is the same as taking the adjoint of the three-step composition,
because transposing a morphism of the form `a ≫ R(f')_* b` under `L(f')^* ⊣ R(f')_*` gives the
transpose of `a` followed by `b`.

*No hypotheses beyond the square.*  Derived pullback and derived pushforward exist for every
morphism of ringed spaces (Tag 079W), the derived internal hom and its tensor–internal-hom
bijection for every ringed space (Tag 08DI), and the map of Tag 08I3 for every morphism; so the
only data are the four morphisms, the commutativity of the square, and `K, L`.  The source
likewise asks for nothing more.

*One spelling for the category of module sheaves.*  The derived pullback and pushforward of
Tag 079W are declared over `SheafOfModules (structureSheafRing X)` and the
derived internal hom over `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)`.
The two are the same sheaf of rings, by `rfl`, and the statement below mixes them; the first is
a `def` and so is made reducible at `implicit` transparency for this file, which is what makes
the two types recognised as equal where a statement meets both.

*What is not stated.*  The source states no compatibility of this map with composition of
squares, no transitivity, and no criterion for it to be an isomorphism; Remark 20.42.14 asserts
existence and gives the recipe, and nothing else is claimed here.

The recipe itself is not stated as an equation either.  It is one application of
`CategoryTheory.Adjunction.homEquiv_naturality_right_symm` followed by
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint`, and the step that defeats
the budget is identifying the transpose of the definition with the transpose of
`derivedBaseChangeMap ... ≫ R(f')_* (…)` — even after giving
`homEquiv_naturality_right_symm` its three objects explicitly or making the definition
reducible.  This is the wall the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap` describe: a defeq
question about a term naming four total derived functors at once unfolds the standard derived
category at too many positions.  Raising the budget is not permitted here.

## References

* [Stacks Project, Tag 08I4](https://stacks.math.columbia.edu/tag/08I4)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.Cohomology.DerivedInternalHomBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback and pushforward of Tag 079W name the structure sheaf of a ringed space
-- by `structureSheafRing`, the derived internal hom by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`.  The two are the same sheaf of rings by `rfl`, and
-- the statement below mixes them, so the first is unfolded at `implicit` transparency here.
attribute [local implicit_reducible] structureSheafRing

noncomputable section

variable {X' X S' S : RingedSpace.{u, u}}
  (h : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : h ≫ f = f' ≫ g)
  (K L : DerivedCategory
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))

/-- **Tag 08I4: the base change map for a derived internal hom.**  For a commutative square of
ringed spaces with `h : X' ⟶ X` over `g : S' ⟶ S` and objects `K, L` of `D(𝒪_X)`, the canonical
map

`Lg^* Rf_* R𝓗om_{𝒪_X}(K, L) ⟶ R(f')_* R𝓗om_{𝒪_{X'}}(Lh^*K, Lh^*L)`

in `D(𝒪_{S'})`.  It is the derived base change map of Tag 08HY at `R𝓗om_{𝒪_X}(K, L)` followed
by `R(f')_*` of the canonical map of Tag 08I3, which is the adjoint of the three-step
composition the source describes. -/
@[stacks 08I4]
def derivedBaseChangeSheafHomMap :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).obj L)) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f').obj
        (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
            (op ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj
              K))).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj L)) :=
  Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h f' f g sq
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).obj L) ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f').map
      (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap h K L)

end

end Stacks.Cohomology.DerivedInternalHomBaseChange

end
