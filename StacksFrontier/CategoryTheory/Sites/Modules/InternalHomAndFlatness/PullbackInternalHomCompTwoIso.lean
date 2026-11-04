module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompData

/-!
# The canonical map of Stacks 0GMX is invariant under a 2-isomorphism of factorizations

Let `χ : X ⟶ Z` be a morphism of ringed topoi between the topoi of two ringed sites, and suppose
`χ` is presented as a composite in two ways: through a middle ringed site `Y` by `(φ, ψ)` and
through a middle ringed site `Y'` by `(φ', ψ')`. The four-field morphism of ringed topoi of the
modules development has no composition, so each presentation is the data of a comparison of the
geometric direct images carrying the composite structure map to the structure map of `χ`, which
is to say a 2-morphism from the composite to `χ`; the composition law for the canonical map of
Stacks 0GMX is stated in exactly that form by
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf`.

Both presentations therefore compute the *same* canonical map
`χ^* Hom_{O_Z}(F, G) ⟶ Hom_{O_X}(χ^*F, χ^*G)`, and the result below says so: the two
composite expressions agree. For instance, the square of Stacks 04J0

```
  (Sh(C/U), O_U)   --j_U-->  (Sh(C), O)
       | f'                     | f
  (Sh(D/V), O'_V)  --j_V-->  (Sh(D), O')
```

with `U = u(V)` presents one morphism `(Sh(C/U), O_U) ⟶ (Sh(D), O')` as a composite in two ways,
`f` after the localization `j_U` and the localization `j_V` after the localized morphism `f'`, and
the result below then expresses the restriction of the canonical map of `f` to `C/U` through the
canonical map of `f'`.

## Main results

* `Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf_congr`: the two composite
  expressions for the canonical map of Stacks 0GMX attached to two presentations of one morphism
  as a composite agree.

## Implementation notes

The result is stated with the two presentations as variables and is proved by transitivity of the
composition law with itself. The two sides of the composition law mention the pullback along `χ`
and the pullback along `φ` after the pullback along `ψ`, spellings which are definitionally but
not syntactically equal; unifying them inside a concrete goal is expensive, whereas at variables
each side is the right-hand side of the composition law at its own data and neither is unfolded.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Sheaves.RingedToposModules (fSharpSet fSharpSetComp)

namespace Stacks.SheafOfModules.InternalHom

universe u

section CompTwoIso

variable {X Y Y' Z : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (ψ : RingedToposHom (RingedSite.ringedTopos Y) (RingedSite.ringedTopos Z))
  (χ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Z))
  (τ : φ.toModulesHom.toToposHom.pushforward ⋙ ψ.toModulesHom.toToposHom.pushforward ≅
      χ.toModulesHom.toToposHom.pushforward)
  (hτ : fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫ τ.hom.app _ =
    fSharpSet χ.toModulesHom)
  (φ' : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y'))
  (ψ' : RingedToposHom (RingedSite.ringedTopos Y') (RingedSite.ringedTopos Z))
  (τ' : φ'.toModulesHom.toToposHom.pushforward ⋙ ψ'.toModulesHom.toToposHom.pushforward ≅
      χ.toModulesHom.toToposHom.pushforward)
  (hτ' : fSharpSetComp φ'.toModulesHom ψ'.toModulesHom ≫ τ'.hom.app _ =
    fSharpSet χ.toModulesHom)

/-- **The canonical map of Stacks 0GMX is invariant under a 2-isomorphism of factorizations.**
Let `χ : X ⟶ Z` be a morphism of ringed topoi between the topoi of two ringed sites presented as
a composite in two ways — through a middle ringed site `Y` by `(φ, ψ)` with the comparison `τ` of
the geometric direct images, and through a middle ringed site `Y'` by `(φ', ψ')` with the
comparison `τ'`. Then the two composite expressions that
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf` gives for the canonical map

`χ^* Hom_{O_Z}(F, G) ⟶ Hom_{O_X}(χ^*F, χ^*G)`

agree, since each of them *is* that canonical map. -/
theorem toposPullbackInternalHomMap_compOf_congr
    (F G : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    toposPullbackCompComparisonOf φ ψ χ τ hτ ((internalHomSecondFunctor Z.J Z.O F).obj G) ≫
          (toposPullback φ).map (toposPullbackInternalHomMap ψ F G) ≫
            toposPullbackInternalHomMap φ ((toposPullback ψ).obj F) ((toposPullback ψ).obj G) ≫
              (internalHomPre X.O (toposPullbackCompComparisonOf φ ψ χ τ hτ F)).app
                  ((toposPullback φ).obj ((toposPullback ψ).obj G)) ≫
                (internalHomSecondFunctor X.J X.O ((toposPullback χ).obj F)).map
                  (toposPullbackCompComparisonInvOf φ ψ χ τ hτ G) =
      toposPullbackCompComparisonOf φ' ψ' χ τ' hτ' ((internalHomSecondFunctor Z.J Z.O F).obj G) ≫
        (toposPullback φ').map (toposPullbackInternalHomMap ψ' F G) ≫
          toposPullbackInternalHomMap φ' ((toposPullback ψ').obj F) ((toposPullback ψ').obj G) ≫
            (internalHomPre X.O (toposPullbackCompComparisonOf φ' ψ' χ τ' hτ' F)).app
                ((toposPullback φ').obj ((toposPullback ψ').obj G)) ≫
              (internalHomSecondFunctor X.J X.O ((toposPullback χ).obj F)).map
                (toposPullbackCompComparisonInvOf φ' ψ' χ τ' hτ' G) :=
  (toposPullbackInternalHomMap_compOf φ ψ χ τ hτ F G).symm.trans
    (toposPullbackInternalHomMap_compOf φ' ψ' χ τ' hτ' F G)

end CompTwoIso

end Stacks.SheafOfModules.InternalHom

end
