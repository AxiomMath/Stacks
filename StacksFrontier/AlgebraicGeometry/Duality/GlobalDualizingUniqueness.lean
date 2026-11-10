module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLocality.InvertibilityOnACovering
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InvertibleDerivedSheafHomCounit
import StacksCore.Tactic.StacksAttribute

/-!
# Two dualizing complexes on a locally Noetherian scheme differ by an invertible object

**Stacks 0ATP.** Let `X` be a locally Noetherian scheme and let `K`, `K'` be dualizing complexes
on `X`. Then `K'` is isomorphic to `K ⊗^L_{𝒪_X} L` for an invertible object `L` of `D(𝒪_X)`.

The proof puts `L = R𝓗om_{𝒪_X}(K, K')`: affine locally `L` is invertible and the evaluation
`L ⊗^L_{𝒪_X} K ⟶ K'` is an isomorphism ([Stacks, Tag 0A7F]), and both conclusions are local.
This file proves the globalization step, with the two affine-local inputs as hypotheses.

Invertibility of an object is an existence statement about objects and not in itself local, so
it is replaced by invertibility of a morphism: `L` is invertible exactly when the evaluation
`R𝓗om_{𝒪_X}(L, 𝒪_X) ⊗^L_{𝒪_X} L ⟶ 𝒪_X` of [Stacks, Tag 08DI] is an isomorphism, and
invertibility of a morphism of `D(𝒪_X)` is local
(`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`). The tensor product of
`Stacks.SheafOfModules.derivedMonoidalStructure` is the derived tensor product of
[Stacks, Tag 06YU] by definition.

The statement of [Stacks, Tag 0ATP] with the affine-local inputs proved is
`Stacks.Duality.exists_isInvertible_tensor_iso_of_isDualizingComplex` in
`StacksFrontier/AlgebraicGeometry/Duality/DualizingComplexUniqueness.lean`.

## Main definitions

* `Stacks.SheafOfModules.derivedUnitEvaluation` — the evaluation `L^∨ ⊗^L L ⟶ 𝒪_X` of `L`
  against the unit, where `L^∨ = R𝓗om_{𝒪_X}(L, 𝒪_X)`.

## Main results

* `CategoryTheory.MonoidalCategory.isInvertible_of_isIso_tensorHom_unit` — in a braided
  monoidal category, an object admitting a morphism from a tensor product onto the unit which
  is an isomorphism is invertible.
* `Stacks.SheafOfModules.isInvertible_iff_isIso_derivedUnitEvaluation` — an object of `D(𝒪_X)`
  is invertible exactly when its unit evaluation is an isomorphism.
* `Stacks.SheafOfModules.isInvertible_of_isIso_restrict_derivedUnitEvaluation` — an object of
  `D(𝒪_X)` whose unit evaluation restricts to an isomorphism on each member of a covering
  family is invertible.
* `Stacks.SheafOfModules.exists_isInvertible_tensor_iso_of_isIso_restrict` — the globalization
  step of [Stacks, Tag 0ATP] on a ringed space, with the two affine-local inputs as hypotheses.
* `Stacks.SheafOfModules.exists_isInvertible_tensor_iso_of_affineLocal` — the same on a scheme,
  the covering family being the affine opens.

## Implementation notes

Everything is stated for a ringed space `(X, 𝒪_X)`, read as the ringed site of its opens, at the
model `HasDerivedCategory.standard` of the derived category; the scheme form is the instance
`Rc := X.sheaf`. Restriction is restriction to the slice site of the opens contained in `V`.

## References

* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

/-! ### Invertibility from a morphism onto the unit -/

namespace CategoryTheory.MonoidalCategory

/-- **An object of a braided monoidal category is invertible as soon as some tensor product
onto it maps isomorphically to the unit.** If `e : D ⊗ L ⟶ 𝟙_ C` is an isomorphism then `D` is
a two-sided tensor inverse of `L`: the isomorphism `D ⊗ L ≅ 𝟙_ C` is `e`, and the isomorphism
`L ⊗ D ≅ 𝟙_ C` is `e` read through the braiding. -/
theorem isInvertible_of_isIso_tensorHom_unit {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {L D : C} (e : D ⊗ L ⟶ 𝟙_ C) (he : IsIso e) : IsInvertible L := by
  have := he
  exact ⟨{ inv := D, isoLeft := β_ L D ≪≫ asIso e, isoRight := asIso e }⟩

end CategoryTheory.MonoidalCategory

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-! ### The evaluation of an object against the unit -/

/-- **The evaluation of `L` against the unit**, `R𝓗om_{𝒪_X}(L, 𝒪_X) ⊗^L_{𝒪_X} L ⟶ 𝒪_X`: the
counit `Stacks.SheafOfModules.derivedSheafHomCounit` of the tensor–internal-hom bijection of
[Stacks, Tag 08DI] taken with the unit of [Stacks, Tag 0FPT] — the structure sheaf in degree
zero — as its target. -/
def derivedUnitEvaluation (L : DerivedCategory (StructureSheafModules Rc)) :
    letI := derivedMonoidalStructure Rc
    ((derivedTensor Rc).obj
          (((derivedSheafHom Rc).obj (op L)).obj
            (𝟙_ (DerivedCategory (StructureSheafModules Rc))))).obj L ⟶
      𝟙_ (DerivedCategory (StructureSheafModules Rc)) :=
  letI := derivedMonoidalStructure Rc
  derivedSheafHomCounit Rc L (𝟙_ (DerivedCategory (StructureSheafModules Rc)))

/-- **An object of `D(𝒪_X)` whose unit evaluation is an isomorphism is invertible**, its
inverse being `R𝓗om_{𝒪_X}(L, 𝒪_X)`. -/
theorem isInvertible_of_isIso_derivedUnitEvaluation
    (L : DerivedCategory (StructureSheafModules Rc))
    (h : IsIso (derivedUnitEvaluation Rc L)) :
    letI := derivedMonoidalStructure Rc
    MonoidalCategory.IsInvertible L := by
  let := derivedMonoidalStructure Rc
  let := derivedSymmetricStructure Rc
  exact MonoidalCategory.isInvertible_of_isIso_tensorHom_unit (derivedUnitEvaluation Rc L) h

/-- **An invertible object of `D(𝒪_X)` has an invertible unit evaluation**: the evaluation
`R𝓗om_{𝒪_X}(L, 𝒪_X) ⊗^L_{𝒪_X} L ⟶ 𝒪_X` is an isomorphism when `L` is invertible. -/
theorem isIso_derivedUnitEvaluation_of_isInvertible
    (L : DerivedCategory (StructureSheafModules Rc))
    (hL : letI := derivedMonoidalStructure Rc; MonoidalCategory.IsInvertible L) :
    IsIso (derivedUnitEvaluation Rc L) :=
  let := derivedMonoidalStructure Rc
  isIso_derivedSheafHomCounit_of_isInvertible Rc L
    (𝟙_ (DerivedCategory (StructureSheafModules Rc))) hL

/-- **An object of `D(𝒪_X)` is invertible exactly when its unit evaluation is an
isomorphism.** -/
theorem isInvertible_iff_isIso_derivedUnitEvaluation
    (L : DerivedCategory (StructureSheafModules Rc)) :
    letI := derivedMonoidalStructure Rc
    MonoidalCategory.IsInvertible L ↔ IsIso (derivedUnitEvaluation Rc L) :=
  ⟨isIso_derivedUnitEvaluation_of_isInvertible Rc L,
    isInvertible_of_isIso_derivedUnitEvaluation Rc L⟩

/-! ### Glueing an invertible object of `D(𝒪_X)` -/

variable [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, (SheafOfModules.overFunctor.{u} (structureSheaf Rc) V).Additive]

/-- **Invertible objects of `D(𝒪_X)` glue.** Let `Y : ι → Opens X` be a family of opens
covering `X`. If the unit evaluation of `L` restricts to an isomorphism over each `Y i`, then
`L` is an invertible object of `D(𝒪_X)`. -/
theorem isInvertible_of_isIso_restrict_derivedUnitEvaluation
    (L : DerivedCategory (StructureSheafModules Rc))
    {ι : Type*} {Y : ι → Opens X} (hY : (Opens.grothendieckTopology X).CoversTop Y)
    (hinv : ∀ i, IsIso ((SheafOfModules.overFunctor.{u} (structureSheaf Rc)
      (Y i)).mapDerivedCategory.map (derivedUnitEvaluation Rc L))) :
    letI := derivedMonoidalStructure Rc
    MonoidalCategory.IsInvertible L :=
  isInvertible_of_isIso_derivedUnitEvaluation Rc L
    (Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor hY _ hinv)

/-! ### Tag 0ATP -/

/-- **[Stacks, Tag 0ATP] on a ringed space, with the affine-local inputs as hypotheses.**

Let `(X, 𝒪_X)` be a ringed space, let `K`, `K'` be objects of `D(𝒪_X)` and put
`L = R𝓗om_{𝒪_X}(K, K')`. Suppose that over each member of a covering family both the unit
evaluation of `L` and the evaluation `L ⊗^L_{𝒪_X} K ⟶ K'` restrict to isomorphisms. Then `L`
is an invertible object of `D(𝒪_X)` and `K' ≅ K ⊗^L_{𝒪_X} L`. -/
theorem exists_isInvertible_tensor_iso_of_isIso_restrict
    (K K' : DerivedCategory (StructureSheafModules Rc))
    {ι : Type*} {Y : ι → Opens X} (hY : (Opens.grothendieckTopology X).CoversTop Y)
    (hinv : ∀ i, IsIso ((SheafOfModules.overFunctor.{u} (structureSheaf Rc)
      (Y i)).mapDerivedCategory.map
        (derivedUnitEvaluation Rc (((derivedSheafHom Rc).obj (op K)).obj K'))))
    (hev : ∀ i, IsIso ((SheafOfModules.overFunctor.{u} (structureSheaf Rc)
      (Y i)).mapDerivedCategory.map (derivedSheafHomCounit Rc K K'))) :
    letI := derivedMonoidalStructure Rc
    ∃ L : DerivedCategory (StructureSheafModules Rc),
      MonoidalCategory.IsInvertible L ∧ Nonempty (K' ≅ K ⊗ L) := by
  let := derivedMonoidalStructure Rc
  let := derivedSymmetricStructure Rc
  have : IsIso (derivedSheafHomCounit Rc K K') :=
    Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor hY _ hev
  refine ⟨((derivedSheafHom Rc).obj (op K)).obj K',
    isInvertible_of_isIso_restrict_derivedUnitEvaluation Rc _ hY hinv,
    ⟨(β_ K (((derivedSheafHom Rc).obj (op K)).obj K') ≪≫
      asIso (derivedSheafHomCounit Rc K K')).symm⟩⟩

/-- **The globalization step of [Stacks, Tag 0ATP] on a scheme**, the covering family being the
affine opens: for objects `K`, `K'` of `D(𝒪_X)` whose evaluation morphisms restrict to
isomorphisms over each affine open, `R𝓗om_{𝒪_X}(K, K')` is invertible and
`K' ≅ K ⊗^𝐋_{𝒪_X} R𝓗om_{𝒪_X}(K, K')`. -/
theorem exists_isInvertible_tensor_iso_of_affineLocal (W : Scheme.{u})
    [IsLocallyNoetherian W]
    [HasSheafify (Opens.grothendieckTopology W.toTopCat) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology W.toTopCat).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).Additive]
    [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} W.sheaf)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
        (ComplexShape.up ℤ)]
    [∀ V : Opens W.toTopCat,
      HasSheafify ((Opens.grothendieckTopology W.toTopCat).over V) AddCommGrpCat.{u}]
    [∀ V : Opens W.toTopCat, ((Opens.grothendieckTopology W.toTopCat).over
      V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : Opens W.toTopCat,
      (SheafOfModules.overFunctor.{u} (structureSheaf W.sheaf) V).Additive]
    (K K' : DerivedCategory (StructureSheafModules W.sheaf))
    (hinv : ∀ V : W.affineOpens, IsIso ((SheafOfModules.overFunctor.{u}
      (structureSheaf W.sheaf) (V : W.Opens)).mapDerivedCategory.map
        (derivedUnitEvaluation W.sheaf (((derivedSheafHom W.sheaf).obj (op K)).obj K'))))
    (hev : ∀ V : W.affineOpens, IsIso ((SheafOfModules.overFunctor.{u}
      (structureSheaf W.sheaf) (V : W.Opens)).mapDerivedCategory.map
        (derivedSheafHomCounit W.sheaf K K'))) :
    letI := derivedMonoidalStructure W.sheaf
    ∃ L : DerivedCategory (StructureSheafModules W.sheaf),
      MonoidalCategory.IsInvertible L ∧ Nonempty (K' ≅ K ⊗ L) := by
  have hY : (Opens.grothendieckTopology W.toTopCat).CoversTop
      (fun V : W.affineOpens => (V : W.Opens)) :=
    (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top W))
  exact exists_isInvertible_tensor_iso_of_isIso_restrict W.sheaf K K' hY hinv hev

end Stacks.SheafOfModules

end
