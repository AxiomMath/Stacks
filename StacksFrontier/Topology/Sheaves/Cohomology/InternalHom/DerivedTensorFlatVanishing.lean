module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# The derived tensor product of two flat modules with vanishing tensor product

Let `(C, O)` be a ringed site, or `(X, O_X)` a ringed space, and let `M` and `N` be flat
`O`-modules with `M ⊗_O N = 0`. Then `M` and `N`, placed in degree zero, have vanishing derived
tensor product in `D(O)`.

The three steps are: a flat module placed in a single degree is a K-flat complex, so the
comparison isomorphism of the derived monoidal structure identifies `M[0] ⊗^L N[0]` with the
image under `Q` of the total tensor product `M[0] ⊗ N[0]` of complexes; that total tensor
product is the termwise complex `p ↦ M[0]^p ⊗_O N`, which vanishes in every degree, in degree
zero because `M ⊗_O N` does and elsewhere because `M[0]^p` does; and `Q` carries a zero object
to a zero object.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.isZero_tensorObj_single_of_isZero`: the total tensor
  product of two modules placed in degree zero is a zero complex as soon as their tensor
  product is a zero module. No flatness is used here.
* `Stacks.SheafOfModules.DerivedMonoidal.isZero_derivedTensorSingle_of_isZero_tensorObj`: the
  statement on a ringed site, for an arbitrary monoidal structure on `D(O)` whose comparison
  identifies the tensor product with the total tensor product on K-flat complexes.
* `Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat`: the
  statement on a ringed space, for the derived tensor product of Stacks 0FPB.

## Implementation notes

The monoidal structure on `D(O)` is passed as an explicit argument, together with its
comparison, rather than taken from an instance: the ringed-space structure
`Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory` is *by definition* the
`monoidal` field of `Stacks.Cohomology.MonoidalDerived.symmetricMonoidalDerivedCategory`, so
passing that field makes the two statements match with no transport.

The monoidal structure on `Mod(O)` is `SheafOfModules.monoidalCategorySheafTensor`, the
re-seated one, for which `F ⊗ G` *is* the tensor product sheaf of Tag 01CA and
`curriedTensor (Mod O)` *is* `Stacks.SheafOfModules.Tensor.sheafTensor`. It is not
interchangeable with `Stacks.SheafOfModules.monoidalCategory`, and only at the re-seated one is
`totalSingleIso` applicable to `K ⊗ L` without transport. Its universes do not solve against the
diagonal universes of a `RingedSpace.{u, u}` while they are metavariables, so on the ringed space
it is named by `letI` rather than left to `attribute [local instance]`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose proof needs the derived form of the orthogonality of the factors.
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN) — K-flat complexes.
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB) — the derived tensor
  product on `D(O_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.SheafOfModules.DerivedMonoidal

/-- A homological complex all of whose terms are zero objects is a zero object.

The same statement appears, each time locally, as
`Stacks.Cohomology.CechSpectralSequence.isZero_of_forall_isZero_X`, as a private lemma of
`StacksFrontier.Homology.TorAmplitude.Composition` and as one of
`StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonSurjective`; it belongs in a
low-level homology file, which none of those four is. -/
private theorem isZero_of_forall_isZero_X {D : Type*} [Category* D] [Preadditive D] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex D c) (h : ∀ i, IsZero (K.X i)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  exact (h i).eq_of_src _ _

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- Every term of the termwise complex `p ↦ M[0]^p ⊗_O N` is a zero object when `M ⊗_O N` is:
in degree zero it is `M ⊗_O N` up to the identification `M[0]^0 ≅ M`, and in every other degree
`M[0]^p` is a zero object, which an additive bifunctor carries to one. -/
private theorem isZero_rowComplex_single_X (M N : Mod R)
    (h : IsZero (MonoidalCategory.tensorObj (C := Mod R) M N)) (p : ℤ) :
    IsZero ((CochainComplex.KFlatBifunctor.rowComplex (curriedTensor (Mod R))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) N).X p) := by
  by_cases hp : p = 0
  · subst hp
    exact h.of_iso (((curriedTensor (Mod R)).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).app N)
  · exact CochainComplex.KFlatBifunctor.isZero_obj_obj_of_isZero (curriedTensor (Mod R))
      (HomologicalComplex.isZero_single_obj_X _ 0 M p hp) N

/-- **The total tensor product of two modules placed in degree zero vanishes with their tensor
product.** The double complex is concentrated in the row zero, so the total complex is the
termwise complex `p ↦ M[0]^p ⊗_O N` of `CochainComplex.KFlatBifunctor.totalSingleIso`, and that
complex is zero in every degree. No flatness is used. -/
public theorem isZero_tensorObj_single_of_isZero (M N : Mod R)
    (h : IsZero (MonoidalCategory.tensorObj (C := Mod R) M N)) :
    IsZero (MonoidalCategory.tensorObj (C := Complexes R)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N)) :=
  (isZero_of_forall_isZero_X _ (isZero_rowComplex_single_X R M N h)).of_iso
    (CochainComplex.KFlatBifunctor.totalSingleIso (curriedTensor (Mod R)) _ N)

variable [HasDerivedCategory.{d} (Mod R)]

/-- **The derived tensor product of two flat modules with vanishing tensor product vanishes**, on
a ringed site. `mono` is a monoidal structure on `D(Mod(O))` and `cmp` its comparison with the
total tensor product of K-flat complexes; both modules placed in degree zero are K-flat complexes
because they are flat, so the comparison applies to them, and the complex it compares with is a
zero object by `isZero_tensorObj_single_of_isZero`. -/
public theorem isZero_derivedTensorSingle_of_isZero_tensorObj
    (mono : Monoidal R) (cmp : letI := mono; Comparison R) (M N : Mod R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
    (h : IsZero (MonoidalCategory.tensorObj (C := Mod R) M N)) :
    letI := mono
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod R) 0).obj M)
      ((DerivedCategory.singleFunctor (Mod R) 0).obj N)) := by
  let := mono
  exact (Functor.map_isZero _ (isZero_tensorObj_single_of_isZero R M N h)).of_iso
    (cmp _ _ (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R M hM 0)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R N hN 0))

end Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.MonoidalDerived

open AlgebraicGeometry

/-- **The derived tensor product of two flat modules with vanishing tensor product vanishes**, on
a ringed space, for the derived tensor product of Stacks 0FPB.

This is the passage from the orthogonality `𝒪_n ⊗_{𝒪_X} 𝒪_m = 0` of a product decomposition of
the structure sheaf to its derived form, which is one of the three obligations of the implication
`(2) ⟹ (1)` of Stacks 0FPG; it is a step of that proof and not a clause of the tag, so it
carries no `@[stacks]` attribute. -/
public theorem isZero_derivedTensor_of_isZero_tensor_of_isFlat (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] (M N : Mod X.sheaf)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) N)
    (h : letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
      IsZero (MonoidalCategory.tensorObj (C := Mod X.sheaf) M N)) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj M)
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj N)) :=
  isZero_derivedTensorSingle_of_isZero_tensorObj X.sheaf
    (symmetricMonoidalDerivedCategory.{u, d} X).monoidal
    (symmetricMonoidalDerivedCategory.{u, d} X).comparison M N hM hN h

end Stacks.Cohomology.MonoidalDerived

end
