module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Associated points are unchanged by tensoring with an invertible module

Let `X` be a scheme, `F` an `𝒪_X`-module and `L` an invertible `𝒪_X`-module. Then
`Ass(F ⊗_{𝒪_X} L) = Ass(F)`.

Being an associated point of a module is a condition on its stalk: `x` is associated to `F`
when the maximal ideal of `𝒪_{X,x}` is the annihilator of an element of `F_x`. Both the ring
and the ideal are the same for `F` and for `F ⊗ L`, and the two stalks are isomorphic as
`𝒪_{X,x}`-modules — the stalk of a tensor product is the tensor product of the stalks
([Stacks, Tag 01CB]) and the stalk of an invertible module is free of rank one over the local
ring `𝒪_{X,x}` (the pointwise converse half of [Stacks, Tag 0B8M]). So the two conditions are
literally the same condition, in every integer twist at once: no hypothesis of positivity, and
none of coherence or quasi-coherence, enters.

## Main definitions

* `Stacks.Divisors.tensorInvertibleStalkEquiv`: the `𝒪_{X,x}`-linear equivalence
  `(F ⊗_{𝒪_X} L)_x ≃ F_x` at an invertible `L`.

## Main results

* `Stacks.Divisors.isAssociatedPoint_tensorObj_iff_of_isInvertible`: a point is associated to
  `F ⊗ L` exactly when it is associated to `F`.
* `Stacks.Divisors.associatedPoints_tensorObj_eq_of_isInvertible`: the set form,
  `Ass(F ⊗ L) = Ass(F)`.
* `Stacks.Divisors.associatedPoints_tensorModules_eq_of_isInvertibleModule`: the same equality
  at the `Stacks.RelativeVeryAmple.tensorModules` spelling of the tensor product and the
  `Stacks.Ample.IsInvertibleModule` spelling of invertibility, which is the pair the twists
  `𝒪(d)` of projective space are stated over.

## Implementation notes

The equivalence of stalks is noncomputable in a second way beyond the usual one: rank-one
freeness of the stalk of an invertible module is available only as a `Nonempty`
(`Stacks.Divisors.nonempty_stalk_linearEquiv_of_isInvertible`), there being no canonical
trivialization, so a choice is made. Nothing downstream depends on which: the two results below
are propositions.

Invertibility of a sheaf of modules is two classes in this library, neither an instance for the
other — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Modules/TensorInvertible.lean`. The statements are made over
`AlgebraicGeometry.SheafOfModules.IsInvertible`, the one
`Stacks.Divisors.nonempty_stalk_linearEquiv_of_isInvertible` is phrased with, and
`associatedPoints_tensorModules_eq_of_isInvertibleModule` converts from the other with
`Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry`.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

open scoped TensorProduct

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **The stalk of `F ⊗_{𝒪_X} L` at an invertible `L` is the stalk of `F`.** The stalk of a
tensor product is the tensor product of the stalks ([Stacks, Tag 01CB],
`AlgebraicGeometry.tensorStalkEquiv`), and the stalk of an invertible module is free of rank one
over `𝒪_{X,x}`, so the second factor cancels.

A trivialization of `L_x` is chosen; see the implementation notes. -/
def tensorInvertibleStalkEquiv (F L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (Scheme.Modules.tensorObj F L).presheaf x
        ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x :=
  (AlgebraicGeometry.tensorStalkEquiv F L x).trans
    ((TensorProduct.congr (LinearEquiv.refl _ _)
        (nonempty_stalk_linearEquiv_of_isInvertible L x).some).trans
      (TensorProduct.rid _ _))

/-- **Tensoring with an invertible module does not change the associated points, pointwise.**
`x` is associated to `F ⊗_{𝒪_X} L` exactly when it is associated to `F`: the condition is the
annihilator of an element of the stalk being the maximal ideal of `𝒪_{X,x}`, and the two stalks
are `𝒪_{X,x}`-linearly isomorphic by `Stacks.Divisors.tensorInvertibleStalkEquiv`. -/
theorem isAssociatedPoint_tensorObj_iff_of_isInvertible (F L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) :
    IsAssociatedPoint (Scheme.Modules.tensorObj F L) x ↔ IsAssociatedPoint F x :=
  ⟨fun h => isAssociatedPrimeStacks_of_linearEquiv (tensorInvertibleStalkEquiv F L x) h,
    fun h => isAssociatedPrimeStacks_of_linearEquiv (tensorInvertibleStalkEquiv F L x).symm h⟩

/-- **`Ass(F ⊗_{𝒪_X} L) = Ass(F)` for an invertible `L`.** The set form of
`Stacks.Divisors.isAssociatedPoint_tensorObj_iff_of_isInvertible`.

Applied to `L = 𝒪_X(d)` this is twist-invariance of the associated points, in every integer
degree `d` at once. -/
theorem associatedPoints_tensorObj_eq_of_isInvertible (F L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    associatedPoints (Scheme.Modules.tensorObj F L) = associatedPoints F :=
  Set.ext fun x => isAssociatedPoint_tensorObj_iff_of_isInvertible F L x

/-- **`Ass(F ⊗_{𝒪_X} L) = Ass(F)`**, at the `Stacks.RelativeVeryAmple.tensorModules` spelling of
the tensor product and the `Stacks.Ample.IsInvertibleModule` spelling of invertibility. This is
the pair the twisting sheaves `𝒪(d)` of projective space are stated over, so it is this form
that applies to `ℱ(d) = ℱ ⊗ 𝒪(d)`. -/
theorem associatedPoints_tensorModules_eq_of_isInvertibleModule (F L : X.Modules)
    [hL : Stacks.Ample.IsInvertibleModule X L] :
    associatedPoints (Stacks.RelativeVeryAmple.tensorModules X F L) = associatedPoints F :=
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  associatedPoints_tensorObj_eq_of_isInvertible F L

end Stacks.Divisors

end
