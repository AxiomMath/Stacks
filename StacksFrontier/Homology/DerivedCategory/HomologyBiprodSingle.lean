module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The cohomology of `A[0] ⊕ M[-n]` in degree `n`

In the derived category of an abelian category, the `n`-th cohomology object of
`A[0] ⊕ M[-n]` is `M` for `n > 0`: cohomology commutes with finite direct sums, `A[0]` has no
cohomology in degree `n`, and `M[-n]` has `M` there. In the proof of Stacks 0E1J this reads off
`R¹f_*𝒪_X = H¹(Rf_*𝒪_X)` from the local decomposition `Rf_*𝒪_X ≅ 𝒪_S ⊕ M[-1]`.

The statement is over any model `[HasDerivedCategory C]` of the derived category.

## Main definitions

* `DerivedCategory.homologyBiprodSingleIso`: the isomorphism `H^n(A[0] ⊕ M[-n]) ≅ M` for `n > 0`.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **`H^n(A[0] ⊕ M[-n]) ≅ M` for `n > 0`.** -/
def homologyBiprodSingleIso (A M : C) {n : ℤ} (hn : 0 < n) :
    (homologyFunctor C n).obj ((singleFunctor C 0).obj A ⊞ (singleFunctor C n).obj M) ≅ M :=
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (homologyFunctor C n)
  (homologyFunctor C n).mapBiprod _ _ ≪≫
    (isoZeroBiprod (((singleFunctor C 0).obj A).isZero_of_isLE 0 n hn)).symm ≪≫
    (singleFunctorCompHomologyFunctorIso C n).app M

end DerivedCategory

end
