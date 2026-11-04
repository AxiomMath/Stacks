module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedAffineComparison
public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChange

/-!
# The derived décalage of a bounded complex of finite free modules

Let `A` be a commutative ring, let `f ∈ A` be a nonzerodivisor and let `M^•` be a bounded
complex of finite free `A`-modules, written in chosen bases as a `BoundedComplex A`.  Then the
derived décalage `Lη_f` of [Stacks, Tag 0F7R] is computed on the object `[M^•]` of `D(A)` by the
naive décalage `η_f M^•`:

`Lη_f [M^•] ≅ [η_f M^•]`.

Every term of `M^•` is a finite free module, so `f` acts injectively on it; the derived
décalage is computed by the naive one on any complex of `f`-torsion-free modules, which is
`Stacks.Eta.DerivedDescent.moduleDerivedEta_iso`.

## Main results

* `Stacks.Eta.DerivedDescent.isTorsionFree_toCochainComplex`: every term of a bounded complex of
  finite free `A`-modules is `f`-torsion-free when `f` is a nonzerodivisor.
* `Stacks.Eta.DerivedDescent.moduleDerivedEtaToCochainComplexIso`:
  **`Lη_f [M^•] ≅ [η_f M^•]`.**

## Implementation notes

`Stacks.Eta.DerivedDescent.moduleDerivedEta_iso` is a natural isomorphism of functors on
complexes of `f`-torsion-free modules;
`Stacks.Eta.GoodBaseChange.liftTorsionFree` moves `M^•` into that subcategory and
`Stacks.Eta.DerivedFunctor.underlyingComplex` brings it back on the nose, so the comparison is
read off by evaluating the natural isomorphism, with no transport.  The décalage the
right-hand side names is `Stacks.Eta.DerivedFunctor.etaObjectFunctor`, whose value on an object
is `EtaComplex.etaObject` by definition.

## References

* [Stacks Project, Tag 0F7R](https://stacks.math.columbia.edu/tag/0F7R)
* [Stacks Project, Tag 0F7Q](https://stacks.math.columbia.edu/tag/0F7Q)
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped nonZeroDivisors

universe w u

namespace Stacks.Eta.DerivedDescent

/-- **A bounded complex of finite free modules is termwise torsion-free for a
nonzerodivisor.**  The degree-`i` term is `A^{r_i}`, on which `f` acts coordinatewise, so a
section killed by `f` has every coordinate killed by `f`, hence is zero. -/
theorem isTorsionFree_toCochainComplex {A : Type u} [CommRing A] {f : A}
    (hf : f ∈ A⁰) (C : BoundedComplex A) :
    EtaComplex.IsTorsionFree f C.toCochainComplex := by
  intro i x hx
  funext j
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hf).mp (congrFun hx j)

/-- **The derived décalage of a bounded complex of finite free modules is its naive
décalage:** `Lη_f [M^•] ≅ [η_f M^•]` in `D(A)`, for `f` a nonzerodivisor of `A`.

The terms of `M^•` are finite free, hence `f`-torsion-free by
`Stacks.Eta.DerivedDescent.isTorsionFree_toCochainComplex`, and the derived décalage is computed
by the naive one on such a complex: this is
`Stacks.Eta.DerivedDescent.moduleDerivedEta_iso` evaluated at `M^•` read in the subcategory of
`f`-torsion-free modules. -/
def moduleDerivedEtaToCochainComplexIso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : A) (hf : f ∈ A⁰) (C : BoundedComplex A) :
    (moduleDerivedEta f hf).obj (DerivedCategory.Q.obj C.toCochainComplex) ≅
      DerivedCategory.Q.obj (EtaComplex.etaObject f C.toCochainComplex) :=
  (moduleDerivedEta_iso f hf).app
    (Stacks.Eta.GoodBaseChange.liftTorsionFree f C.toCochainComplex
      (isTorsionFree_toCochainComplex hf C))

end Stacks.Eta.DerivedDescent

end
