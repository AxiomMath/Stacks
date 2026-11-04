module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The stalk of an isomorphism of `𝒪_X`-modules, as a linear equivalence

An isomorphism of sheaves of `𝒪_X`-modules on a scheme induces a bijection of stalks, and that
bijection is linear over the stalk of the structure sheaf. This module carries that one
construction.

It exists because the construction had been written twice, in two modules whose import closures
have no cheap common ancestor: taking either one's import into the other costs a hundred modules
or more for a one-line wrapper.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence` is a common ancestor that
both already import, and it supplies every piece used here, so the canonical declaration
belongs just above it.

## Main definitions

* `Stacks.SheafOfModules.FlatShortExact.stalkLinearEquivOfIso` — the linear equivalence of stalks
  induced by an isomorphism of `𝒪_X`-modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.SheafOfModules.FlatShortExact

/-- The linear equivalence of stalks induced by an isomorphism of `𝒪_X`-modules: the stalk
functor carries an isomorphism to an isomorphism, and the induced map of stalks is linear over
the stalk of the structure sheaf. -/
public noncomputable def stalkLinearEquivOfIso {X : Scheme.{u}} {L M : X.Modules}
    (e : L ≅ M) (x : X) :
    letI := stalkModule (X := X.toRingedSpace) L x
    letI := stalkModule (X := X.toRingedSpace) M x
    abStalk L x ≃ₗ[X.presheaf.stalk x] abStalk M x := by
  letI := stalkModule (X := X.toRingedSpace) L x
  letI := stalkModule (X := X.toRingedSpace) M x
  exact LinearEquiv.ofBijective (stalkLinearMap (X := X.toRingedSpace) e.hom x)
    ((ConcreteCategory.isIso_iff_bijective
      ((TopCat.Presheaf.stalkFunctor Ab x).mapIso
        ((PresheafOfModules.toPresheaf (structureSheafRing X.toRingedSpace).obj).mapIso
          ((_root_.SheafOfModules.forget _).mapIso e))).hom).mp inferInstance)

end Stacks.SheafOfModules.FlatShortExact

end
