module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart

/-!
# The inverse image of a module, restricted to the preimage of an open

For a morphism of schemes `b : X' ⟶ X`, an open `W` of `X` and a sheaf of modules `N` on `X`, the
restriction of the inverse image `b^*N` to the preimage `b ⁻¹ᵁ W` is the inverse image along the
restricted morphism `b ∣_ W` of the restriction of `N` to `W`.  Both are the inverse image of `N`
along the two equal composites of the commuting square

```
b ⁻¹ᵁ W  --->  X'
   |            |
   |            | b
   v            v
   W     --->   X
```

so the comparison is `AlgebraicGeometry.pullbackCompIsoOfEq` twice, through the equality
`AlgebraicGeometry.morphismRestrict_ι` of those composites, with the passage between restriction
and inverse image at the two ends.

This is the comparison the essential surjectivity half of [Stacks, Tag 0EXD] needs in order to
glue the identification `b^*N ≅ 𝒢` over a cover of `X` by opens:  over the preimage of such an
open the identification is read through the restriction of `N` to the open, which is where the
trivialisations of `N` live.

## Main definitions

* `AlgebraicGeometry.restrictPullbackPreimageIso`: **the comparison**, as stated above.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The restriction of the inverse image `b^*N` to the preimage of an open `W` is the inverse
image along `b ∣_ W` of the restriction of `N` to `W`.**  Both are the inverse image of `N` along
the composite side of the commuting square cut out by `W`, the two presentations of that composite
being identified by `AlgebraicGeometry.morphismRestrict_ι`. -/
def restrictPullbackPreimageIso {X X' : Scheme.{u}} (b : X' ⟶ X) (W : X.Opens) (N : X.Modules) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback b).obj N) (b ⁻¹ᵁ W).ι ≅
      (Scheme.Modules.pullback (b ∣_ W)).obj (Scheme.Modules.restrict N W.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ W).ι).app
      ((Scheme.Modules.pullback b).obj N) ≪≫
    pullbackCompIsoOfEq (b ⁻¹ᵁ W).ι b (morphismRestrict_ι b W).symm N ≪≫
    (pullbackCompIsoOfEq (b ∣_ W) W.ι rfl N).symm ≪≫
    (Scheme.Modules.pullback (b ∣_ W)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N).symm

end AlgebraicGeometry

end
