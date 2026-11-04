module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The commutativity and unit constraints of the derived tensor product on a ringed site

Let `(C, 𝒪)` be a ringed site and let `T` be a derived tensor product on it in the sense of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, i.e. Stacks 06YU. This file supplies the
two constraints of the symmetric monoidal structure of [Stacks, Tag 0FPT] that are needed to
move a tensor factor across `⊗^L_𝒪` and to cancel the structure sheaf against it:

* the commutativity constraint `A ⊗^L_𝒪 B ≅ B ⊗^L_𝒪 A`, and
* the two unit constraints `A ⊗^L_𝒪 𝒪 ≅ A` and `𝒪 ⊗^L_𝒪 A ≅ A`.

All names below live in the namespace
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`.

## Main definitions

* `braidingIso` is the commutativity constraint `A ⊗^L_𝒪 B ≅ B ⊗^L_𝒪 A`.
* `rightUnitIso` is the unit constraint `A ⊗^L_𝒪 𝒪 ≅ A`.
* `leftUnitIso` is the unit constraint `𝒪 ⊗^L_𝒪 A ≅ A`.

## Main results

* `leftUnitIso_eq` records that the left unit constraint is the right one transported along the
  commutativity constraint, which is how it is built.

## Implementation notes

**What is and is not supplied.** [Stacks, Tag 0FPT] asserts that `D(𝒪)` is a *symmetric
monoidal* category under `⊗^L_𝒪`. The three isomorphisms below are its commutativity and unit
constraints read one pair of objects at a time. The associativity constraint and the coherence
axioms — the pentagon, the hexagon, the unit triangles and the involutivity of the braiding —
are **not** proved here, and so the monoidal structure itself is not assembled. The clause
strings on the attributes say exactly this. What the constraints are used for downstream is
transporting a map across a tensor factor, for which the isomorphisms alone suffice.

**Where the representatives come from.** The derived tensor product is only computed by
`DerivedTensorProduct.comparison` on K-flat representatives, so each construction below passes
to representatives and back. The representatives are
`AlgebraicGeometry.RingedSite.kFlatModel`, the repository's chosen K-flat model of an object of
`D(𝒪)`, together with `AlgebraicGeometry.RingedSite.kFlatModelIso` and
`AlgebraicGeometry.RingedSite.isKFlat_kFlatModel`; nothing is chosen beyond that model, which is
the same device the derived internal Hom is built from. The unit needs no model: the structure
sheaf in degree zero is K-flat outright, by
`Stacks.SheafOfModules.isKFlat_single_unit`.

**The content on representatives.** Once both factors are K-flat complexes the derived tensor
product is the ordinary total tensor complex, and there the two statements are already available:
the commutativity is the Koszul symmetry
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` of Stacks 06YM, whose signs are the ones
[Stacks, Tag 0FPT] refers to, and the unit law is
`Stacks.SheafOfModules.tensorComplexUnitIso`. So no new computation with signs is carried out
here; the file is the descent of those two isomorphisms through the K-flat comparisons.

**The derived category is the standard one.** `AlgebraicGeometry.RingedSite.kFlatModel` is
stated with `CategoryTheory.HasDerivedCategory.standard` in force, so the declarations below
are too, rather than being generic in the derived category's hom universe. This is the setting
in which the clients of these constraints live.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedTensor.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The structure sheaf of a ringed site, placed in degree zero as a complex: the unit of the
derived tensor product. -/
abbrev unitComplex : CochainComplex (Modules X.O) ℤ :=
  (HomologicalComplex.single (Modules X.O) (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The structure sheaf of a ringed site, as an object of `D(𝒪)` in degree zero. -/
abbrev unitObject : DerivedModules X.O :=
  (DerivedCategory.singleFunctor (Modules X.O) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O)

/-- **[Stacks, Tag 0FPT], the commutativity constraint.** The derived tensor product of two
objects of `D(𝒪)` is symmetric: `A ⊗^L_𝒪 B ≅ B ⊗^L_𝒪 A`.

Both objects are replaced by their chosen K-flat models, on which the derived tensor product is
the ordinary total tensor complex; there the isomorphism is the Koszul symmetry
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`. -/
@[stacks 0FPT "the commutativity constraint at a pair of objects, as an isomorphism; not the \
  monoidal structure and not its coherence axioms"]
def braidingIso (A B : DerivedModules X.O) :
    (T.tensor.obj A).obj B ≅ (T.tensor.obj B).obj A :=
  ((T.tensor.mapIso (RingedSite.kFlatModelIso X A)).app B).symm ≪≫
    ((T.tensor.obj (DerivedCategory.Q.obj (RingedSite.kFlatModel X A))).mapIso
      (RingedSite.kFlatModelIso X B)).symm ≪≫
    T.comparison (RingedSite.kFlatModel X A) (RingedSite.kFlatModel X B)
      (RingedSite.isKFlat_kFlatModel X A) (RingedSite.isKFlat_kFlatModel X B) ≪≫
    DerivedCategory.Q.mapIso (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
      (RingedSite.kFlatModel X A) (RingedSite.kFlatModel X B)) ≪≫
    (T.comparison (RingedSite.kFlatModel X B) (RingedSite.kFlatModel X A)
      (RingedSite.isKFlat_kFlatModel X B) (RingedSite.isKFlat_kFlatModel X A)).symm ≪≫
    (T.tensor.obj (DerivedCategory.Q.obj (RingedSite.kFlatModel X B))).mapIso
      (RingedSite.kFlatModelIso X A) ≪≫
    (T.tensor.mapIso (RingedSite.kFlatModelIso X B)).app A

/-- **[Stacks, Tag 0FPT], the unit constraint on the right.** The structure sheaf in degree zero
is a unit for the derived tensor product: `A ⊗^L_𝒪 𝒪 ≅ A`.

The right factor is already K-flat by `Stacks.SheafOfModules.isKFlat_single_unit`, so only the
left factor is replaced by its chosen K-flat model; on representatives the statement is the
ordinary unit law `Stacks.SheafOfModules.tensorComplexUnitIso`. -/
@[stacks 0FPT "the unit constraint on the right at an object, as an isomorphism; not the \
  monoidal structure and not its coherence axioms"]
def rightUnitIso (A : DerivedModules X.O) :
    (T.tensor.obj A).obj (unitObject X) ≅ A :=
  ((T.tensor.mapIso (RingedSite.kFlatModelIso X A)).app (unitObject X)).symm ≪≫
    T.comparisonRight (RingedSite.kFlatModel X A) (unitComplex X)
      (Stacks.SheafOfModules.isKFlat_single_unit X.O) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.tensorComplexUnitIso X.O (RingedSite.kFlatModel X A)) ≪≫
    RingedSite.kFlatModelIso X A

/-- **[Stacks, Tag 0FPT], the unit constraint on the left.** The structure sheaf in degree zero
is a unit for the derived tensor product on the other side too: `𝒪 ⊗^L_𝒪 A ≅ A`.

It is the right unit constraint read through the commutativity constraint. -/
@[stacks 0FPT "the unit constraint on the left at an object, as an isomorphism; not the \
  monoidal structure and not its coherence axioms"]
def leftUnitIso (A : DerivedModules X.O) :
    (T.tensor.obj (unitObject X)).obj A ≅ A :=
  T.braidingIso X (unitObject X) A ≪≫ T.rightUnitIso X A

/-- The left unit constraint is the right one transported along the commutativity constraint. -/
theorem leftUnitIso_eq (A : DerivedModules X.O) :
    T.leftUnitIso X A = T.braidingIso X (unitObject X) A ≪≫ T.rightUnitIso X A :=
  rfl

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
