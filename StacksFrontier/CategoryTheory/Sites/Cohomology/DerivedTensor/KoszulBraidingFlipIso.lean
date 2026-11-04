module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraiding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.Homology.MapHomologicalComplexBraided

/-!
# The Koszul braiding of `Comp(Mod(O))` is the symmetry of the total tensor complex

Complexes of `O`-modules carry two symmetries of the total tensor product, built along
different routes:

* `CochainComplex.koszulBraiding`, the commutativity constraint of
  `CochainComplex.symmetricCategory`, assembled degreewise out of the symmetry of `Mod(O)`
  times the Koszul sign `(-1)^{pq}`; it is the `β_` of `Comp(Mod(O))` and the one the coherence
  clauses of [Stacks, Tag 0FPT] are stated with; and
* `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`, which transports the total complex along
  `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` and then exchanges the two factors with
  Mathlib's `HomologicalComplex.mapBifunctorFlipIso`; it is the one the commutativity
  constraint of the *derived* tensor product of [Stacks, Tag 06YU] is descended from
  (`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingTrans`).

**They are the same isomorphism**, and this file proves it.  Nothing in the tree related the
two, and that was the whole gap between the two spellings of the commutativity constraint of
[Stacks, Tag 0FPT] in the derived category.

## Main results

* `Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso`: **the two agree.**

## Implementation notes

The proof is summandwise, and the Koszul sign is not an obstruction but the point: on the
summand of bidegree `(p, q)` the left-hand side is the symmetry of `Mod(O)` times
`(-1)^{pq}` (`CochainComplex.ιTensorObj_braiding`), and the right-hand side is
`sheafTensorBraiding` at that bidegree — contributing no sign
(`HomologicalComplex.ι_mapBifunctorNatIso_hom`) — times the sign
`ComplexShape.σ (ComplexShape.up ℤ) _ _ q p` that Mathlib's flip carries
(`HomologicalComplex.ι_mapBifunctorFlipIso_hom`), which is `(-1)^{qp}`.  So the two signs are
the *same* sign, and what is left is the identification of the two symmetries of `⊗_O`,
`SheafOfModules.braiding_eq_sheafTensorBraiding`.

The two inclusions of the target summand are written `HomologicalComplex.ιTensorObj L K q p n`
and `HomologicalComplex.ιMapBifunctor L K (sheafTensor R) (ComplexShape.up ℤ) q p n`; those are
the same morphism, the tensor product of the re-seated structure on `Mod(O)` being
`sheafTensor R` by `rfl` (`SheafOfModules.curriedTensor_sheafTensor`), which is the closing
`rfl`.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0FNI](https://stacks.math.columbia.edu/tag/0FNI)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **The commutativity constraint of `Comp(Mod(O))` is the symmetry of the total tensor
complex.**

The left-hand side is `CochainComplex.koszulBraiding`, the braiding of
`CochainComplex.symmetricCategory`; the right-hand side is
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`, the composite of the transport along
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` with Mathlib's
`HomologicalComplex.mapBifunctorFlipIso`.  See the implementation notes of this module for the
summandwise comparison, in which the two Koszul signs are the same sign. -/
theorem koszulBraiding_eq_tensorComplexFlipIso
    (K L : CochainComplex
      (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    (β_ K L).hom = (tensorComplexFlipIso R K L).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hflip : (tensorComplexFlipIso R K L).hom.f n =
      (HomologicalComplex.mapBifunctorNatIso K L (ComplexShape.up ℤ)
          (sheafTensorBraiding R)).hom.f n ≫
        (HomologicalComplex.mapBifunctorFlipIso L K (sheafTensor R)
          (ComplexShape.up ℤ)).hom.f n := rfl
  have hn : p + q = n := h
  have hsig : ComplexShape.σ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) q p =
      ((p * q).negOnePow : ℤˣ) := congrArg Int.negOnePow (mul_comm q p)
  rw [hflip, CochainComplex.ιTensorObj_braiding K L p q n hn (by omega), ← Category.assoc,
    HomologicalComplex.ι_mapBifunctorNatIso_hom, Category.assoc,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom, hsig,
    _root_.SheafOfModules.braiding_eq_sheafTensorBraiding R (K.X p) (L.X q),
    Linear.comp_units_smul]
  rfl

end Stacks.SheafOfModules.Tensor

end
