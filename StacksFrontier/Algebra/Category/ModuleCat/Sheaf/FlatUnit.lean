module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor

/-!
# The structure sheaf is a flat sheaf of modules

For a ringed site `(C, O)` the unit sheaf of modules — the structure sheaf read as a module over
itself — is flat: tensoring with it is the identity functor up to isomorphism, and the identity
functor is exact.

Flatness is `AlgebraicGeometry.SheafOfModules.IsFlat`, which by
`Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor` is exactness of
`- ⊗_O M`. The monoidal structure `SheafOfModules.monoidalCategorySheafTensor` has
`Stacks.SheafOfModules.Tensor.sheafTensor` for its tensor product and `SheafOfModules.unit` for
its unit (`SheafOfModules.curriedTensor_sheafTensor`, `SheafOfModules.tensorUnit_sheafTensor`),
so the right unitor is an isomorphism `- ⊗_O O ≅ 𝟭` and the exactness is transported along it.

This is the flatness that Stacks 06YY's computation clause consumes when the derived pullback is
evaluated at the structure sheaf placed in degree zero — the complex that corepresents global
sections, in the global-sections clause of Stacks 0D6H.

## Main results

* `Stacks.SheafOfModules.isFlat_unit`: the unit sheaf of modules is flat.

## References

* [Stacks Project, Tag 05NI](https://stacks.math.columbia.edu/tag/05NI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

/-- **The structure sheaf is flat.** Tensoring with the unit sheaf of modules is the right
unitor of the monoidal structure on sheaves of modules, hence isomorphic to the identity
functor, hence exact. -/
theorem isFlat_unit {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) := by
  let := _root_.SheafOfModules.monoidalCategorySheafTensor.{u, u} R
  have e : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ≅
      𝟭 (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :=
    NatIso.ofComponents (fun M => ρ_ M)
      (fun f => MonoidalCategory.rightUnitor_naturality f)
  refine (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))).2 ?_
  exact ⟨preservesFiniteLimits_of_natIso e.symm, preservesFiniteColimits_of_natIso e.symm⟩

end Stacks.SheafOfModules

end
