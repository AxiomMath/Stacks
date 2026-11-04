module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex

/-!
# The monoidal-closed internal hom of sheaves of modules is the internal Hom sheaf

Two constructions of the internal hom of sheaves of `O`-modules on a ringed site exist
independently in this development:

* `(MonoidalClosed.ihom F).obj G`, the internal hom of the monoidal closed structure on sheaves
  of modules (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean`), which
  comes from Day's reflection theorem and is therefore a *sheafification* of a presheaf-level
  internal hom;
* `AlgebraicGeometry.RingedSite.internalHomSheaf X F G`, the internal Hom of Stacks
  Tag 03EM, whose sections over `U` are the morphisms of
  `O|_U`-modules `F|_U ⟶ G|_U` on the slice site `C/U`, and which is already a sheaf.

This file identifies them, in the `AlgebraicGeometry.RingedSite` vocabulary. The identification
is not a comparison of the two constructions: both are internal homs out of `F`, hence right
adjoints of tensoring by `F`, so they agree by uniqueness of adjoints. The sheaf-level
adjunction that makes this argument available is the sheaf clause of Stacks 03EO,
`Stacks.SheafOfModules.InternalHom.sheafTensorHomAdjunction`, and the identification itself is
`Stacks.SheafOfModules.InternalHom.ihomIsoInternalHom`; this file only restates it at the
ringed-site spelling of the sheaf of rings.

## Main results

* `AlgebraicGeometry.RingedSite.ihomIsoInternalHomSheafFunctor`: the two internal-hom functors
  out of `F` are isomorphic.
* `AlgebraicGeometry.RingedSite.ihomIsoInternalHomSheaf`: the object-level identification
  `(ihom F).obj G ≅ internalHomSheaf X F G`.

## Implementation notes

`X.ringSheaf` and `Stacks.SheafOfModules.Tensor.ringSheaf X.O` are the same sheaf of rings by
  `rfl`, both
being `(sheafCompose X.J (forget₂ CommRingCat RingCat)).obj X.O` — the `HasSheafCompose`
hypothesis is a `Prop`, so the two routes to it do not separate the terms. The same remark is
already recorded for Stacks Tag 0A90. Likewise
`(internalHomSecondFunctor X.J X.O F).obj G` and `internalHomSheaf X F G` are the same sheaf of
modules by `rfl`, both being `internalHom X.O.obj F.val G.val` with the sheaf condition of
`internalHom_isSheaf`; so the two statements below are
`Stacks.SheafOfModules.InternalHom.ihomIsoInternalHomSecondFunctor` and
`Stacks.SheafOfModules.InternalHom.ihomIsoInternalHom` with no transport inserted.

**Universe narrowing, inherited from the chain and recorded rather than decided here.** The
statements are at `RingedSite.{u, v, max u v}` with modules in `SheafOfModules.{max u v}`. Two
independent reasons force this and neither is a choice made here: `internalHomSheaf X A B` has
type `SheafOfModules.{max u v m}` for `A B : SheafOfModules.{m}`, so a statement comparing it to
an endofunctor of `SheafOfModules.{m}` is ill-typed unless `m = max u v m`; and the monoidal
closed structure on sheaves of modules, hence `MonoidalClosed.ihom` itself, is available only at
module universe `max u v` over a `CommRingCat.{max u v}`-valued structure sheaf. The same
narrowing is already carried by `AlgebraicGeometry.RingedSite` in the neighbouring file.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

noncomputable section

universe v u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v})
  [HasWeakSheafify X.J AddCommGrpCat.{max u v}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  SheafOfModules.monoidalClosed

/-- **The two internal homs out of `F` agree.** Both `MonoidalClosed.ihom F` and Stacks 03EM's
`internalHomSheaf X F -` are right adjoint to `F ⊗_O -`, so they are isomorphic as functors. -/
def ihomIsoInternalHomSheafFunctor :
    ihom F ≅
      Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{v, u, max u v, u}
        X.J X.O F :=
  Stacks.SheafOfModules.InternalHom.ihomIsoInternalHomSecondFunctor X.O F

/-- **The monoidal-closed internal hom is Stacks 03EM's internal Hom sheaf.** The internal hom
of the monoidal closed structure on sheaves of `O`-modules, which Day's reflection theorem
produces as a sheafification, is the internal Hom sheaf of Stacks 03EM, whose sections over `U`
are the morphisms `F|_U ⟶ G|_U` of `O|_U`-modules on the slice site. -/
def ihomIsoInternalHomSheaf
    (G : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (ihom F).obj G ≅ internalHomSheaf X F G :=
  Stacks.SheafOfModules.InternalHom.ihomIsoInternalHom X.O F G

end AlgebraicGeometry.RingedSite

end

end
