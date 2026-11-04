module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SliceDerivedTensorTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The mate of the slice tensor comparison, and Stacks 08DL

Let `(C, O)` be a ringed site and `U` an object of `C`. Restriction to the slice site `C/U`
carries the derived tensor product to the derived tensor product of `C/U`
(`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso`) and carries the derived
internal hom to the derived internal hom of `C/U` (Stacks 08DL,
`AlgebraicGeometry.RingedSite.DerivedHomRestriction.iso`). The two comparisons are not
independent: the tensor–internal-hom bijection of Stacks 08J8 makes each the *adjoint
transpose* — the **mate** — of the other.

This file writes down the mate. For objects `L`, `M` of `D(O)` the tensor–internal-hom
bijection of the slice turns a morphism

`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`

into a morphism `R𝓗om_O(L, M)|_U ⊗^𝐋_{O|_U} L|_U ⟶ M|_U`, and there is one canonical
morphism of the second kind: the tensor comparison followed by the restriction of the
evaluation `R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` of Stacks 08J8. Transposing it back gives
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose`, which is the
canonical map of Stacks 08I3 read at the localization morphism `C/U ⟶ C`.

## The mate statement

**The mate statement is the equation**

`derivedSheafHomRestrictionTranspose X U L M = ((derivedHomRestriction X U).iso L M).hom`,

i.e. that the comparison Stacks 08DL asserts to be an isomorphism *is* that canonical
transpose. It is **not proved here**, and nothing below assumes it. What is proved is that the
transpose exists, that it is the unique morphism with the stated adjoint
(`eq_derivedSheafHomRestrictionTranspose_iff`, since the bijection of Stacks 08J8 is a
bijection), and hence that the mate statement is equivalent to a single identity of morphisms
of `D(O|_U)` — `derivedSheafHomRestrictionTranspose_eq_iso_iff`, which is the 2-cell identity a
proof would have to supply.

The mate statement is restated with the bijection of Stacks 08J8 eliminated, as the
commutativity of a square of named morphisms of `D(O|_U)`, in
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose_eq_iso_iff_square`.

## Main definitions

* `Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso`: the comparison
  `(K ⊗^𝐋_O L)|_U ≅ K|_U ⊗^𝐋_{O|_U} L|_U` at the derived tensor product the derived internal
  hom is stated over.
* `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionDatum`: the morphism
  `R𝓗om_O(L, M)|_U ⊗^𝐋_{O|_U} L|_U ⟶ M|_U` the mate is the transpose of.
* `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose`: **the mate**,
  `R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`.

## Main results

* `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose_eq_symm_apply`:
  the defining equation of the mate.
* `Stacks.Cohomology.SliceDerivedSheafHom.eq_derivedSheafHomRestrictionTranspose_iff`: that
  equation determines the mate — a morphism is the mate exactly when its transpose is the
  tensor comparison followed by the restricted evaluation.
* `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose_eq_iso_iff`: the
  mate statement, reduced to one identity of morphisms. It is reduced further, to a square with
  no bijection in it, by
  `Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose_eq_iso_iff_square`
  in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomMateSquare`.
* `Stacks.Cohomology.SliceDerivedSheafHom.map_derivedSheafHomCounit_eq`: **the restriction of
  the evaluation morphism factors** as the tensor comparison followed by the transpose of the
  mate. This is the factorization that the affine-local inputs of Stacks 0ATP are meant to be
  fed into; see `StacksFrontier/AlgebraicGeometry/Duality/GlobalDualizingUniqueness.lean`.
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit`: invertibility
  transfers along that factorization.

## Implementation notes

*Two derived tensor products.* The repository carries two independent choices of a derived
tensor product of Stacks 06YU on `D(O)`, as the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/InterfaceDerivedTensorComparison.lean`
record. The slice comparison of
`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso` is stated at
`CochainComplex.KFlatBifunctor.derivedBifunctor`, and the tensor–internal-hom bijection of
Stacks 08J8 at `Stacks.SheafOfModules.derivedTensorProductFunctor`.
`Stacks.SheafOfModules.DerivedMonoidal.interfaceDerivedBifunctorTensorIso` identifies them, and
`sliceTensorRestrictionObjIso` is the slice comparison conjugated by it at both ends.

*Why the construction is written out rather than instantiated.*
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` is this construction over
abstract data, and `Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap` is
Stacks 08I3 as its instance at a morphism of ringed spaces. Instantiating it here would need the
tensor products at the uncurried spelling `D(O) × D(O) ⥤ D(O)` and the tensor comparison as an
isomorphism of functors on pairs; the slice comparison is available in the curried transport shape
`CochainComplex.KFlatBifunctor.derivedTransportSource ≅ derivedTransportTarget`, so an
uncurrying step would come first. The three definitions below are therefore the curried form of
that construction, taken at objects.

*One spelling of the category of module sheaves, and one name for the bijection.* Restriction to
the slice is `Stacks.DerivedTensor.ExtensionByZero.restriction`, which is
`SheafOfModules.overFunctor X.ringSheaf U` on the nose; that is the spelling at which the
transport engine's additivity and exactness instances are seated. Its source and target
*categories*, however, are named here at `AlgebraicGeometry.RingedSite.ringSheaf` rather than at
`Stacks.DerivedTensor.RingedSite.Modules`, the two being the same by `rfl`: with the mixture, the
statement that applies the bijection of Stacks 08J8 to the mate confronts the elaborator with the
equality of two `Category` instances on one derived category and exhausts its recursion budget.
For the same reason the bijection is given the name `sliceCurryEquiv` at the three objects it is
used at, the transpose datum a name of its own, and the defining equation is stated with the
datum on the left, so that the side carrying the bijection is elaborated against a known type.
Each of those three is load-bearing — the statement fails to elaborate without them, and raising
the recursion budget is not permitted here. The implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/InternalHomPullbackMap.lean` record
the same failure for the ringed-space form of Stacks 08I3, where it was not worked around.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)
open CochainComplex.KFlatBifunctor (derivedBifunctor)

universe u

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-! ### The two derived tensor products -/

section Bridge

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- The comparison of the two derived tensor products of Stacks 06YU carried by this
repository, at the diagonal universes of the derived-internal-hom cluster: the K-flat descent
`CochainComplex.KFlatBifunctor.derivedBifunctor`, which the slice comparison is stated at, and
`Stacks.SheafOfModules.derivedTensorProductFunctor`, which the tensor–internal-hom bijection of
Stacks 08J8 is stated at. -/
abbrev kFlatTensorBridge :=
  Stacks.SheafOfModules.DerivedMonoidal.interfaceDerivedBifunctorTensorIso X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)

end Bridge


/-! ### The slice tensor comparison at the tensor product of Stacks 08J8 -/

section Slice

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]

/-- Restriction of `O`-modules to the slice site `C/U`, on unbounded derived categories.

The functor is `Stacks.DerivedTensor.ExtensionByZero.restriction`, at whose spelling the
transport engine's instances are seated, while the two derived categories are named at
`AlgebraicGeometry.RingedSite.ringSheaf`, the spelling the derived internal hom and the
tensor–internal-hom bijection of Stacks 08J8 are stated at. The two namings of the category of
module sheaves are the same by `rfl`, and naming them at one spelling here is what keeps the
statements below elaborable; see the implementation notes. -/
abbrev restrictD :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) :=
  (restriction X U).mapDerivedCategory

/-- **`(K ⊗^𝐋_O L)|_U ≅ K|_U ⊗^𝐋_{O|_U} L|_U`**, at the derived tensor product the derived
internal hom and the tensor–internal-hom bijection of Stacks 08J8 are stated over. It is
`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso` conjugated by
`Stacks.Cohomology.SliceDerivedSheafHom.kFlatTensorBridge` over `C` and over `C/U`. -/
def sliceTensorRestrictionObjIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (restrictD X U).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≅
      ((@Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, _} (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).obj
          ((restrictD X U).obj K)).obj ((restrictD X U).obj L) :=
  (restrictD X U).mapIso (((kFlatTensorBridge X).app K).app L).symm ≪≫
    Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso X U K L ≪≫
    ((@kFlatTensorBridge (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))).app
      ((restrictD X U).obj K)).app ((restrictD X U).obj L)

/-! ### The mate -/

variable (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The datum the mate is the transpose of**: the slice tensor comparison followed by the
restriction to `C/U` of the evaluation morphism `R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` of Stacks 08J8. -/
def derivedSheafHomRestrictionDatum :
    ((@Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, _} (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
      (inferInstance : HasDerivedCategory (Modules (X.O.over U)))).obj
          ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))).obj
        ((restrictD X U).obj L) ⟶
      (restrictD X U).obj M :=
  (sliceTensorRestrictionObjIso X U
        (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) L).inv ≫
    (restrictD X U).map (RingedSite.derivedSheafHomCounit X L M)

/-- The tensor–internal-hom bijection of Stacks 08J8 on the slice site `C/U`, at the three
objects the mate lives between:

`Hom(R𝓗om_O(L, M)|_U, R𝓗om_{O|_U}(L|_U, M|_U)) ≃ Hom(R𝓗om_O(L, M)|_U ⊗^𝐋_{O|_U} L|_U, M|_U)`.

Naming it is not cosmetic: a statement that writes it out and applies it to the mate presents the
elaborator with a term whose implicit arguments it cannot finish checking. See the
implementation notes. -/
abbrev sliceCurryEquiv :=
  @RingedSite.derivedCurryHomEquiv (X.over U)
      (inferInstance : HasSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (inferInstance : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive)
      (inferInstance : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive)
      (inferInstance : ∀ K L : CochainComplex (Modules (X.O.over U)) ℤ,
        HomologicalComplex.HasMapBifunctor K L
          (sheafTensor.{u, u, u, u, u} (X.O.over U)) (ComplexShape.up ℤ))
    ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))
    ((restrictD X U).obj L) ((restrictD X U).obj M)

/-- **The mate of the slice tensor comparison**, `R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`.

Under the tensor–internal-hom bijection of Stacks 08J8 on the slice site it is the same datum
as a morphism `R𝓗om_O(L, M)|_U ⊗^𝐋_{O|_U} L|_U ⟶ M|_U`, and the canonical such morphism is
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionDatum`. This is the
construction of Stacks 08I3 read at the localization morphism `C/U ⟶ C`; whether the comparison
Stacks 08DL asserts to be an isomorphism is this morphism is the mate statement, which is not
proved here — see the module documentation. -/
def derivedSheafHomRestrictionTranspose :
    (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) ⟶
      ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
          (op ((restrictD X U).obj L))).obj ((restrictD X U).obj M) :=
  (sliceCurryEquiv X U L M).symm (derivedSheafHomRestrictionDatum X U L M)

/-- **The defining equation of the mate**, in the direction the elaborator will take: the mate
is the inverse image of the transpose datum under the tensor–internal-hom bijection of
Stacks 08J8 on the slice site. The forward reading — that the *transpose* of the mate is the
datum — is `Stacks.Cohomology.SliceDerivedSheafHom.eq_derivedSheafHomRestrictionTranspose_iff`
read at the mate itself; it cannot be stated here, see the implementation notes. -/
theorem derivedSheafHomRestrictionTranspose_eq_symm_apply :
    derivedSheafHomRestrictionTranspose X U L M =
      (sliceCurryEquiv X U L M).symm (derivedSheafHomRestrictionDatum X U L M) :=
  rfl

/-- **The defining equation determines the mate.** The tensor–internal-hom bijection of
Stacks 08J8 is a bijection, so a morphism `R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)` is the
mate exactly when its transpose is the slice tensor comparison followed by the restricted
evaluation. -/
theorem eq_derivedSheafHomRestrictionTranspose_iff
    (g : (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) ⟶
      ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
        (op ((restrictD X U).obj L))).obj ((restrictD X U).obj M)) :
    g = derivedSheafHomRestrictionTranspose X U L M ↔
      derivedSheafHomRestrictionDatum X U L M = sliceCurryEquiv X U L M g :=
  Iff.trans eq_comm (AddEquiv.symm_apply_eq (sliceCurryEquiv X U L M))

/-- **The restriction of the evaluation morphism factors through the mate.** Restricting

`R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M`

to the slice site is the slice tensor comparison followed by the transpose of the mate.

This is the factorization that the affine-local hypotheses of Stacks 0ATP are to be fed into:
the restricted evaluation is invertible as soon as the transpose of the mate is, the tensor
comparison being an isomorphism. -/
theorem map_derivedSheafHomCounit_eq :
    (restrictD X U).map (RingedSite.derivedSheafHomCounit X L M) =
      (sliceTensorRestrictionObjIso X U
            (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) L).hom ≫
        derivedSheafHomRestrictionDatum X U L M := by
  rw [derivedSheafHomRestrictionDatum, Iso.hom_inv_id_assoc]

/-- **Invertibility transfers along that factorization**: if the transpose datum is an
isomorphism then so is the restriction of the evaluation morphism to the slice site.

Bookkeeping, and the reason the mate statement is worth having: with the comparison of
Stacks 08DL identified as the mate, the transpose datum becomes that comparison tensored with
`L|_U` followed by the evaluation morphism formed over `C/U`, so the affine-local invertibility
that Stacks 0ATP asks for turns into a statement about the member of the covering family, which
is where the affine case of Stacks 0A7F lives. -/
theorem isIso_map_derivedSheafHomCounit
    (h : IsIso (derivedSheafHomRestrictionDatum X U L M)) :
    IsIso ((restrictD X U).map (RingedSite.derivedSheafHomCounit X L M)) := by
  have := h
  rw [map_derivedSheafHomCounit_eq]
  infer_instance

end Slice

/-! ### The mate statement -/

section MateStatement

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The mate statement for Stacks 08DL, reduced to one identity of morphisms.**

The comparison of Stacks 08DL is the mate of the slice tensor comparison if and only if its
transpose under the tensor–internal-hom bijection of Stacks 08J8 on the slice site is
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionDatum`, that is, the slice
tensor comparison followed by the restriction of the evaluation morphism. Unwound, the
right-hand side says that the square

```
R𝓗om_O(L, M)|_U ⊗^𝐋_{O|_U} L|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U) ⊗^𝐋_{O|_U} L|_U ⟶ M|_U
            ‖                                                             ‖
    (R𝓗om_O(L, M) ⊗^𝐋_O L)|_U -------------------------------------→   M|_U
```

commutes, the bottom row being the restriction of the evaluation morphism and the top row the
comparison of Stacks 08DL followed by the evaluation morphism formed over `C/U`.

Neither side is proved: the right-hand identity is exactly the 2-cell identity missing from this
development, and nothing in this file asserts it. What this statement does is make the mate
statement a single equation between existing morphisms. -/
theorem derivedSheafHomRestrictionTranspose_eq_iso_iff :
    ((RingedSite.derivedHomRestriction X U).iso L M).hom =
        derivedSheafHomRestrictionTranspose X U L M ↔
      derivedSheafHomRestrictionDatum X U L M =
        sliceCurryEquiv X U L M ((RingedSite.derivedHomRestriction X U).iso L M).hom :=
  eq_derivedSheafHomRestrictionTranspose_iff X U L M _

end MateStatement

end Stacks.Cohomology.SliceDerivedSheafHom

end
