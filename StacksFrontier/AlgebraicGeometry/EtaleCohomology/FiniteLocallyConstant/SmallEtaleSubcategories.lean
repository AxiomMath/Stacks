module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite locally constant sheaves on the small étale site of a scheme

Let `X` be a scheme. Inside the topos of sheaves on the small étale site of `X`, the finite
locally constant sheaves of sets are closed under finite limits and finite colimits, the finite
locally constant abelian sheaves form a weak Serre subcategory, and — over a Noetherian
coefficient ring `Λ` — the finite type locally constant sheaves of `Λ`-modules form a weak Serre
subcategory.

All three assertions hold on an arbitrary site, and the library already proves them there. The
small étale site `AlgebraicGeometry.SmallEtale.topology` is a site, so no further argument is
needed: this file records that the general statements are exactly the étale ones, by attaching
the étale tag to the declarations that carry the general one.

## Main results

The three parts are carried by the general-site results

* `Stacks.ConstantSheaf.isClosedUnderFiniteLimits_isFiniteLocallyConstantSetSheaf` and
  `Stacks.ConstantSheaf.isClosedUnderFiniteColimits_isFiniteLocallyConstantSetSheaf` for sheaves
  of sets,
* `Stacks.ConstantSheaf.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf` for abelian
  sheaves,
* `Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf` for sheaves of
  modules over a Noetherian ring.

The file also records the consequence used downstream, that the category of finite locally
constant sheaves of sets on the small étale site has finite products
(`AlgebraicGeometry.finiteLocallyConstantSheaf_hasFiniteProducts`); an equivalence with another
category, such as the category of finite continuous sets over the fundamental group, then
preserves them automatically.

## Implementation notes

Part (1) is two independent closure assertions, so it is recorded on the two closure instances
separately rather than on the conjunction (in the namespace `Stacks`)
`ConstantSheaf.isClosedUnderFiniteLimits_and_finiteColimits_isFiniteLocallyConstantSetSheaf`; a
reader looking for the limit half alone finds a declaration stating only that.

The finiteness in part (2) is finiteness of the local constant value, while the finiteness in
part (3) is finite generation over the coefficient ring; neither part is an instance of the
other, which is why three separate results are needed.

## References

* [Stacks Project, Tag 03RX](https://stacks.math.columbia.edu/tag/03RX)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public section

add_to_stacks 03RX "part (1), finite limits"
  Stacks.ConstantSheaf.isClosedUnderFiniteLimits_isFiniteLocallyConstantSetSheaf
add_to_stacks 03RX "part (1), finite colimits"
  Stacks.ConstantSheaf.isClosedUnderFiniteColimits_isFiniteLocallyConstantSetSheaf
add_to_stacks 03RX "part (2)"
  Stacks.ConstantSheaf.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf
add_to_stacks 03RX "part (3)"
  Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf

namespace AlgebraicGeometry

universe u

/-- The finite locally constant sheaves of sets on the small étale site of an object of a big
étale site have finite products, being closed under them by part (1) above. -/
public instance finiteLocallyConstantSheaf_hasFiniteProducts (B : BigEtaleSite.{u})
    (X : B.Scheme) :
    HasFiniteProducts
      (ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)) =>
          IsFiniteLocallyConstant (SmallEtale.topology B X.obj X.property) F)) :=
  hasFiniteProducts_isFiniteLocallyConstantSetSheaf.{u, u + 1, 0} _

end AlgebraicGeometry

end
