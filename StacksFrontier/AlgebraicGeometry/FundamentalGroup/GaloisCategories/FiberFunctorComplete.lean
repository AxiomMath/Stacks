module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.BaseChangeColimits
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Defs
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms

/-!
# The finite étale covers of a connected scheme are a Galois category

Let `X` be a connected scheme and `x` a geometric point of `X`. Stacks Tag 0BNB says that the
geometric fibre functor `F_x : FÉt_X ⥤ Type` makes `FÉt_X` a Galois category, that is, satisfies
the six axioms of `CategoryTheory.IsGaloisCategory`. Five of them are proved in
`GaloisCategoryAxioms.lean` and the sixth, the colimit half of exactness of `F_x`, is
`Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleFiberFunctor` of
`FiniteEtaleGaloisCategory.lean`; this file assembles the instance.

That colimit half is proved there from the factorisation of the fibre functor as base change
along `x` followed by the functor corepresented by the identity cover of `Spec Ω`
(`AlgebraicGeometry.fiberIsoPointCoyoneda`): a lift of `x` to a cover `Y` is a section over
`Spec Ω` of `Y ×_X Spec Ω`. The second factor preserves finite colimits because `FÉt_{Spec Ω}` is
equivalent to finite sets for a separably closed `Ω`, and the first does by
`Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleBaseChange_geometricPoint`.

Both factorisations of the fibre functor are `private` in `GaloisCategoryAxioms.lean`, so that
module is also imported with `import all`, as its module docstring asks.

## Main results

* `AlgebraicGeometry.finiteEtaleFiberFunctor_isGaloisCategory` — **the finite étale covers of a
  connected scheme, with the fibre functor at a geometric point, are a Galois category.**

## References

* [Stacks Project, Tag 0BMY](https://stacks.math.columbia.edu/tag/0BMY)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The fibre functor at a geometric point makes finite étale covers of a connected scheme into
a Galois category. -/
@[stacks 0BNB, sga "1 XIII 2.1.3" "(C_t, special case"]
instance finiteEtaleFiberFunctor_isGaloisCategory (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) :
    CategoryTheory.IsGaloisCategory (finiteEtaleFiberFunctor x) where
  hasFiniteLimits := Stacks.FundamentalGroup.hasFiniteLimits_finiteEtaleOver X
  hasFiniteColimits := Stacks.FundamentalGroup.hasFiniteColimits_finiteEtaleOver X
  exists_finite_coproduct_connected := exists_finiteCoproduct_isConnected_finiteEtaleOver x
  finite_obj := finite_finiteEtaleFiber x
  reflectsIsomorphisms := reflectsIsomorphisms_finiteEtaleFiberFunctor x
  exact := ⟨preservesFiniteLimits_finiteEtaleFiberFunctor x,
    Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleFiberFunctor x⟩

end AlgebraicGeometry

end
