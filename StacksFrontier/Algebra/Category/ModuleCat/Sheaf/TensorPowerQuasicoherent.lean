module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice

/-!
# The direct sum of the integer tensor powers of an invertible sheaf is quasi-coherent

Let `O` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `O`-modules
which is locally trivial. Then `⨁_{n ∈ ℤ} L^{⊗ n}` is quasi-coherent.

The warning that opens Stacks Tag 01CL is that one and the same covering family must present
every summand, and for a locally trivial invertible sheaf there is such a family: over an open
on which `L` is the structure sheaf, so is every one of its tensor powers, positive or negative,
and the structure sheaf is free of rank one.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.overTensorPowerUnitIso`: **over an open trivializing `L`,
  every integer tensor power of `L` is the structure sheaf.**
* `Stacks.SheafOfModules.TensorPower.overTensorPowerPresentation`: the resulting presentation of
  each tensor power over that open.

## Main results

* `Stacks.SheafOfModules.TensorPower.isQuasicoherent_coprod_tensorPower`: **the direct sum over
  all of `ℤ` of the integer tensor powers of a locally trivial invertible sheaf of modules is
  quasi-coherent.**

## Implementation notes

The trivialization is the composite of three isomorphisms that already exist: restriction to a
slice commutes with tensor powers in every integer degree
(`Stacks.SheafOfModules.TensorPower.overTensorPowerIso`), tensor powers depend only on the
isomorphism class of the sheaf tensored by (`tensorPowerCongr`), and every integer tensor power
of the structure sheaf is the structure sheaf (`unitTensorPowerIso`). The `ℕ`-indexed composite
`Stacks.SheafOfModules.TensorPower.trivPow` is not usable here: it covers the nonnegative
exponents only.

Tensoring on the right by the restricted sheaf has to be known to be an equivalence before any
of the three can be applied, and that instance is produced by hand at each of the three
spellings of the restricted sheaf which the three isomorphisms use — `L.over U` and
`(whiskerRestriction O hO (Over.forget U)).obj L` are definitionally equal but are different
`DiscrTree` keys, so an instance registered at one is invisible at the other.

The index type `ℤ` does not lie in the module universe, so the builder used is
`SheafOfModules.isQuasicoherent_coprod_of_small`, whose index type is only required to be
`Small`, rather than `SheafOfModules.isQuasicoherent_coprod`.

## References

* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L]

/-- **Over an open trivializing `L`, every integer tensor power of `L` is the structure
sheaf.** -/
def overTensorPowerUnitIso (U : C)
    (e : L.over U ≅ SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U))
    (n : ℤ) :
    (tensorPower O hO L n).over U ≅
      SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U) := by
  haveI : IsInvertible ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
      (SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U)) :=
    isInvertible_unit _ _
  haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} (J := J.over U)
      ⟨(Over.forget U).op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp _ ((Over.forget U).op ⋙ O)
        (forget₂ CommRingCat RingCat) (sliceStructureIsSheaf O hO U)⟩).flip.obj
        (SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U))).IsEquivalence :=
    isEquivalence_tensorRightFunctor _ _ _
  haveI : IsInvertible ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
      ((whiskerRestriction O hO (Over.forget U)).obj L) :=
    isInvertible_of_iso _ _ e.symm
  haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} (J := J.over U)
      ⟨(Over.forget U).op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp _ ((Over.forget U).op ⋙ O)
        (forget₂ CommRingCat RingCat) (sliceStructureIsSheaf O hO U)⟩).flip.obj
        ((whiskerRestriction O hO (Over.forget U)).obj L)).IsEquivalence :=
    isEquivalence_tensorRightFunctor _ _ _
  haveI : IsInvertible ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U) (L.over U) :=
    isInvertible_of_iso _ _ e.symm
  haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} (J := J.over U)
      ⟨(Over.forget U).op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp _ ((Over.forget U).op ⋙ O)
        (forget₂ CommRingCat RingCat) (sliceStructureIsSheaf O hO U)⟩).flip.obj
        (L.over U)).IsEquivalence :=
    isEquivalence_tensorRightFunctor _ _ _
  exact overTensorPowerIso O hO U L n ≪≫
    tensorPowerCongr ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U) e n ≪≫
    unitTensorPowerIso ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U) n

/-- **Over an open trivializing `L`, every integer tensor power of `L` has a presentation**, the
structure sheaf being free of rank one. -/
def overTensorPowerPresentation (U : C)
    (e : L.over U ≅ SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U))
    (n : ℤ) : ((tensorPower O hO L n).over U).Presentation :=
  Stacks.SheafOfModules.presentationOfIso
    (overTensorPowerUnitIso O hO L U e n).symm Stacks.SheafOfModules.presentationUnit

/-- **The direct sum over all of `ℤ` of the integer tensor powers of a locally trivial
invertible sheaf of modules is quasi-coherent.** A covering family trivializing `L` trivializes
every tensor power of `L` at once, which is the uniformity Tag 01CL requires. -/
theorem isQuasicoherent_coprod_tensorPower [HasBinaryProducts C]
    [Invertible.IsLocallyTrivial L] :
    (∐ fun n : ℤ => tensorPower O hO L n).IsQuasicoherent := by
  obtain ⟨I, X, hX, e⟩ := Invertible.IsLocallyTrivial.exists_trivializing_cover (M := L)
  exact SheafOfModules.isQuasicoherent_coprod_of_small X hX fun i n =>
    overTensorPowerPresentation O hO L (X i) (e i).some n

end Stacks.SheafOfModules.TensorPower

end
