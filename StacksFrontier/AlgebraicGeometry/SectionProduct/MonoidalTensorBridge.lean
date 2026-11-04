module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalUnitBridge
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic

/-!
# The monoidal tensor product and the sheafified presheaf tensor product, compared

The sibling file `StacksFrontier/AlgebraicGeometry/SectionProduct/MonoidalUnitBridge.lean` compares
the two units of the sheaves of modules on a scheme. The same comparison for the two tensor
products is needed for the same reason: the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory` is obtained by *localizing* the sectionwise
monoidal structure on presheaves of modules, so its tensor product `A ⊗ B` is a
localization-induced object and **not** the sheafification of the presheaf tensor product on the
nose. The sheafification of the presheaf tensor product is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, and that is the spelling in which the
twisting-sheaf multiplication isomorphisms of [Stacks, Tag 01MT] — Equation 01MO
`𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` and Equation 03GJ — and the nonvanishing-locus and zero-scheme APIs are
all stated.

That comparison already exists, and this file does nothing but put it in scope:

* `Stacks.TensorSheafSpellingIso.monoidalTensorIso` is the isomorphism
  `A ⊗ B ≅ Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X.toRingedSpace A B` for
  `A B : X.Modules`, with `Stacks.TensorSheafSpellingIso.monoidalTensorIso_naturality` its
  naturality in both arguments against Tag 01CB's own `tensorSheafMap`.
* `Stacks.TensorSheafDedup.tensorSheaf_eq`, in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree`, is the underlying
  equality of objects — the two packagings of the tensor product sheaf, the
  `TensorStalkRingedSpace` one indexed by a ringed space and the `TensorSheafification` one
  indexed by `X.presheaf`, are the same object by `rfl`. Use `.symm` where the opposite
  orientation is wanted.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/
