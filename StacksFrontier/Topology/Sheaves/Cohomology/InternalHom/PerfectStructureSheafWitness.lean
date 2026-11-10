module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.NonDegenerateGradedDualWitness

/-!
# A non-degenerate perfect object on a ringed space, and the four assertions of Stacks 08DQ at it

Every clause of **Stacks 08DQ** binds a perfect object `K` of `D(O_X)` — in the site-level
reading of Stacks 08G5, `(ringedSite Rc).IsPerfect K`. A statement quantified over such `K` says
nothing unless some such `K` is not a zero object, and until now the only inhabitant of that
predicate available unconditionally over an arbitrary ringed space was the zero object
(`AlgebraicGeometry.RingedSite.isPerfect_of_isZero`): every instance of every clause one could
actually form was degenerate, with `K^∨`, `M ⊗^L K^∨` and `RSheafHom(K, M)` all zero.

This file removes that. The structure sheaf placed in degree zero is a perfect object
(`isPerfect_derivedStructureSheaf`, off the ringed-site statement
`AlgebraicGeometry.RingedSite.isPerfect_derivedStructureSheaf`), it is **not** a zero object as
soon as some section ring of `O_X` is not the zero ring (`not_isZero_derivedStructureSheaf`), and
all four assertions of the tag are then instantiated at it, with every binder filled and
nothing assumed of `M`.

**Nothing here is a clause of Stacks 08DQ and nothing here is tagged.** An inhabitant of a tag's
hypotheses is not part of its assertion. What it certifies is that the tagged statements have
content.

## Main results

* `Stacks.SheafOfModules.isPerfect_derivedStructureSheaf`: `O_X[0]` is a perfect object of
  `D(O_X)`.
* `Stacks.SheafOfModules.not_isZero_derivedStructureSheaf`: it is not a zero object once
  `1 ≠ 0` in some section ring of `O_X`.
* `Stacks.SheafOfModules.OnSpace.isPerfect_derivedStructureSheaf_specULiftInt` and
  `Stacks.SheafOfModules.OnSpace.not_isZero_derivedStructureSheaf_specULiftInt`: the two
  together at a *named* ringed space, `Spec ℤ` — the hypothesis of every clause of Stacks 08DQ
  inhabited there by an object that is not zero.
* `Stacks.SheafOfModules.isPerfect_derivedDual_derivedStructureSheaf`: the first assertion of
  Stacks 08DQ at `K = O_X[0]`.
* `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_derivedStructureSheaf`: the third
  assertion of Stacks 08DQ at `K = O_X[0]` and arbitrary `M`.
* `Stacks.SheafOfModules.derivedBidualIsoDerivedStructureSheaf` and
  `Stacks.SheafOfModules.isIso_derivedBidualMap_derivedStructureSheaf`: the second assertion at
  `K = O_X[0]`.
* `Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap_derivedStructureSheaf`: the
  fourth assertion at `K = O_X[0]` and arbitrary `M`.

## Implementation notes

The witness is built from the definition of Stacks 08G5 directly — the maximal sieve of every
open already carries a strictly perfect model, namely the restriction of `O_X[0]` itself — and so
it does **not** pass through the local criterion
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect`. The maximal
sieve of every open already carries a strictly perfect model, so no derived isomorphism has to
be turned into a map of complexes.

The non-vanishing is the degree-zero cohomology computation
`AlgebraicGeometry.RingedSite.not_isZero_derivedStructureSheaf`, fed by
`Stacks.SheafOfModules.not_isZero_unit_of_one_ne_zero`.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- **The structure sheaf in degree zero is a perfect object of `D(O_X)`.** This is the
ringed-site statement `AlgebraicGeometry.RingedSite.isPerfect_derivedStructureSheaf` read at the
site of opens of the space; perfectness is the site-level notion of Stacks 08G5, which is the one
every clause of Stacks 08DQ binds. -/
theorem isPerfect_derivedStructureSheaf :
    (ringedSite Rc).IsPerfect (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  RingedSite.isPerfect_derivedStructureSheaf (ringedSite Rc)

omit [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- **That perfect object is not a zero object**, as soon as `1 ≠ 0` in one section ring of
`O_X`. Its degree-zero cohomology is `O_X`, which is not a zero module.

This is what makes the perfectness hypothesis of Stacks 08DQ non-degenerately inhabited: it rules
out the reading on which every clause of the tag is discharged because the objects in it
vanish. -/
theorem not_isZero_derivedStructureSheaf (W : (Opens X)ᵒᵖ)
    (hW : (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O)).obj.obj W) ≠ 0) :
    ¬ IsZero (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  RingedSite.not_isZero_derivedStructureSheaf (ringedSite Rc)
    (not_isZero_unit_of_one_ne_zero W hW)

/-- **Stacks 08DQ, first assertion, at the structure sheaf**: the dual `(O_X)^∨` is perfect. -/
theorem isPerfect_derivedDual_derivedStructureSheaf :
    (ringedSite Rc).IsPerfect
      (derivedDual Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))) :=
  isPerfect_derivedDual Rc _ (isPerfect_derivedStructureSheaf Rc)

section Clauses

variable [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Stacks 08DQ, third assertion, at the structure sheaf.** The canonical map

`O_X ⊗^L_{O_X} (O_X)^∨ ⟶ RSheafHom(O_X, M)`

is an isomorphism for every `M`. Every binder of
`isIso_derivedTensorDualToSheafHom_of_isPerfect` is instantiated here, the perfectness
hypothesis at an object that `not_isZero_derivedStructureSheaf` shows is not zero. -/
theorem isIso_derivedTensorDualToSheafHom_derivedStructureSheaf
    (M : DerivedCategory (StructureSheafModules Rc)) :
    IsIso (derivedTensorDualToSheafHom Rc
      (RingedSite.derivedStructureSheaf (ringedSite Rc)) M) :=
  isIso_derivedTensorDualToSheafHom_of_isPerfect Rc _ M (isPerfect_derivedStructureSheaf Rc)

/-- **Stacks 08DQ, second assertion, at the structure sheaf**: `((O_X)^∨)^∨ ≅ O_X`. -/
def derivedBidualIsoDerivedStructureSheaf :
    RingedSite.derivedStructureSheaf (ringedSite Rc) ≅
      derivedDual Rc (derivedDual Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))) :=
  derivedBidualIso Rc _ (isPerfect_derivedStructureSheaf Rc)

/-- **Stacks 08DQ, second assertion, at the structure sheaf**, in the canonical-map form. -/
theorem isIso_derivedBidualMap_derivedStructureSheaf :
    IsIso (derivedBidualMap Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))) :=
  isIso_derivedBidualMap Rc _ (isPerfect_derivedStructureSheaf Rc)

/-- **Stacks 08DQ, fourth assertion, at the structure sheaf**:

`H⁰(X, M ⊗^L_{O_X} (O_X)^∨) ⟶ Hom_{D(O_X)}(O_X, M)`

is bijective for every `M`. -/
theorem bijective_derivedTensorDualGlobalSectionsMap_derivedStructureSheaf
    (M : DerivedCategory (StructureSheafModules Rc)) :
    Function.Bijective (derivedTensorDualGlobalSectionsMap Rc
      (RingedSite.derivedStructureSheaf (ringedSite Rc)) M) :=
  bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect Rc _ M
    (isPerfect_derivedStructureSheaf Rc)

end Clauses

namespace OnSpace

/-- **A named ringed space at which the witness is not degenerate.** On `Spec ℤ` the ring of
global sections is `ULift ℤ`, in which `1 ≠ 0`, so `O[0]` is a perfect object of `D(O)` that is
not a zero object. This is the inhabitant of the perfectness hypothesis of Stacks 08DQ that the
previous audit of the tag recorded as owed. -/
theorem not_isZero_derivedStructureSheaf_specULiftInt :
    ¬ IsZero (RingedSite.derivedStructureSheaf
      (ringedSite (specULiftIntRingedSpace.{u}).sheaf)) :=
  Stacks.SheafOfModules.not_isZero_derivedStructureSheaf
    (specULiftIntRingedSpace.{u}).sheaf (op ⊤) one_ne_zero_specULiftIntRingedSpace

/-- **That object is perfect**, so the hypothesis of each clause of Stacks 08DQ is inhabited at
`Spec ℤ` by something `not_isZero_derivedStructureSheaf_specULiftInt` shows is not zero. -/
theorem isPerfect_derivedStructureSheaf_specULiftInt :
    (ringedSite (specULiftIntRingedSpace.{u}).sheaf).IsPerfect
      (RingedSite.derivedStructureSheaf
        (ringedSite (specULiftIntRingedSpace.{u}).sheaf)) :=
  Stacks.SheafOfModules.isPerfect_derivedStructureSheaf
    (specULiftIntRingedSpace.{u}).sheaf

end OnSpace

end Stacks.SheafOfModules

end
