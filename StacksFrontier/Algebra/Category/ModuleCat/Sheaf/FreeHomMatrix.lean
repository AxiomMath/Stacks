module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# Morphisms between finite free sheaves of modules are matrices

Let `R` be a sheaf of rings on a site with a terminal object `T` — for instance the structure
sheaf, or the Frobenius colimit of it, on the site of opens of a scheme, where `T = ⊤`. A
morphism `R^{⊕I} ⟶ R^{⊕K}` of free sheaves of modules with `K` finite is the same thing as a
matrix of global sections of `R`, that is, of elements of `R(T)`.

The two halves are both available and are only composed here: a morphism out of a free sheaf of
modules is a family of sections of the target (`CategoryTheory.SheafOfModules.freeHomEquiv`),
sections of a sheaf of modules on a site with a terminal object are its sections over that
object (`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`), and sections of a
finite free sheaf of modules over an object are families of sections of the sheaf of rings
(`Stacks.SheafOfModules.freeCoord_bijective`).

## Main definitions

* `Stacks.SheafOfModules.freeHomMatrixEquiv`: **a morphism `R^{⊕I} ⟶ R^{⊕K}` of free sheaves of
  modules, `K` finite, is a matrix `I → K → R(T)` of global sections.**

## Main results

* `Stacks.SheafOfModules.freeHomMatrixEquiv_apply`: the `(i, k)` entry of the matrix of a
  morphism is the `k`-th coordinate of the image of the `i`-th tautological section. This holds
  by definition and is what makes the matrix computable.

## Implementation notes

Finiteness and decidable equality of the *target* index type are what
`Stacks.SheafOfModules.freeCoord_bijective` needs; the source index type is arbitrary, since a
morphism out of a coproduct is a family of morphisms with no finiteness condition.

No hypothesis of quasi-compactness appears: the identification is over the terminal object of
the site, where no sheaf condition has to be solved. On the site of opens of a scheme the
terminal object is the top open, so this is the statement that a morphism of trivial bundles on
`X` is a matrix of global functions — and for the Frobenius colimit of the structure sheaf the
global functions are then identified with the Frobenius colimit of the global functions of `X`
by `AlgebraicGeometry.bijective_frobeniusColimitSectionsComparison`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u'

namespace Stacks.SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A morphism of finite free sheaves of modules is a matrix of global sections.** On a site
with a terminal object `T`, a morphism `R^{⊕I} ⟶ R^{⊕K}` with `K` finite is the same thing as a
matrix `I → K → R(T)`: it is a family of sections of `R^{⊕K}`, indexed by `I`, and a section of
`R^{⊕K}` is a `K`-tuple of sections of `R`. -/
noncomputable def freeHomMatrixEquiv {T : C} (hT : IsTerminal T)
    (I K : Type u) [Fintype K] [DecidableEq K] :
    (_root_.SheafOfModules.free (R := R) I ⟶ _root_.SheafOfModules.free (R := R) K) ≃
      (I → K → ToType (R.obj.obj (op T))) :=
  (_root_.SheafOfModules.freeHomEquiv _).trans
    (Equiv.piCongrRight fun _ =>
      (FiniteTypeKernel.sectionsEquivOfTerminal (_root_.SheafOfModules.free (R := R) K) hT).trans
        (Equiv.ofBijective _ (freeCoord_bijective (S := R) (ι := K) (op T))))

/-- **The entries of the matrix of a morphism of finite free sheaves of modules**: the `(i, k)`
entry is the `k`-th coordinate, over the terminal object, of the image of the `i`-th tautological
section. -/
theorem freeHomMatrixEquiv_apply {T : C} (hT : IsTerminal T)
    (I K : Type u) [Fintype K] [DecidableEq K]
    (f : _root_.SheafOfModules.free (R := R) I ⟶ _root_.SheafOfModules.free (R := R) K)
    (i : I) (k : K) :
    freeHomMatrixEquiv hT I K f i k =
      freeCoord (S := R) (op T)
        ((_root_.SheafOfModules.ιFree i ≫ f).val.app (op T) (unitOne (S := R) (op T))) k := rfl

end Stacks.SheafOfModules

end
