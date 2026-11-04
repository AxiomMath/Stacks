module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectStructureSheafWitness

/-!
# The clauses of Example 0FPC at a perfect object that is not a zero object

Every clause of **Stacks Example 0FPC** that this library carries binds a perfect object `K` of
`D(O_X)` on a ringed space: the isomorphism `K ⊗^L_{O_X} K^∨ ≅ RSheafHom(K, K)`, the coevaluation
`η : O_X ⟶ K ⊗^L_{O_X} K^∨`, and the defining property of `η`.  (The evaluation `ε` binds
nothing.)  The module docstring of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` certifies that
hypothesis as inhabited by citing
`AlgebraicGeometry.RingedSite.isPerfect_of_isZero` — perfectness of a **zero** object.  That is a
degenerate certificate: it leaves open the reading on which each clause holds because the objects
in it vanish.

**A non-degenerate witness is available and is used here.** `O_X` in degree zero is a perfect
object of `D(O_X)` (`Stacks.SheafOfModules.isPerfect_derivedStructureSheaf`, the ringed-space form
of Tag 08G5's `AlgebraicGeometry.RingedSite.isPerfect_derivedStructureSheaf`), and it is not a
zero object as soon as `1 ≠ 0` in one section ring
(`Stacks.SheafOfModules.not_isZero_derivedStructureSheaf`), with the hypothesis-free instance
`Stacks.SheafOfModules.OnSpace.not_isZero_derivedStructureSheaf_specULiftInt` over `Spec ℤ`.  This
file instantiates each 0FPC clause at that object, so each is a statement about something the
library proves is not zero.

## Main results

* `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_self_derivedStructureSheaf`: the
  isomorphism clause at `O_X[0]`.
* `Stacks.SheafOfModules.derivedDualCoevaluation_derivedStructureSheaf`: the coevaluation at
  `O_X[0]`.
* `Stacks.SheafOfModules.derivedDualCoevaluation_comp_derivedStructureSheaf`: its defining
  property at `O_X[0]` — the equation that pins `η`, at an object that is not zero.

## Nothing here is tagged

An inhabitant of a hypothesis is not a clause of the tag, and an instance of a clause at one
object is a special case rather than the clause.  The `@[stacks 0FPC]` attribute is on the
general statement `Stacks.SheafOfModules.derivedDual_isLeftDual`; nothing here carries one.
This is the same convention `…InternalHom.PerfectStructureSheafWitness` follows for Stacks 08DQ.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/- The three pinnings of the opens-site tensor product this file elaborates against are taken
from `…InternalHom.LeftDualOnARingedSpace`, as in `…InternalHom.PerfectCoevaluation` and for the
same reason: the library instances tie the sections universe to the site universes as `max u v`,
which instance synthesis cannot solve against the diagonal `u` of this cluster. -/
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The isomorphism clause of Example 0FPC at `O_X[0]`.** The canonical map
`O_X ⊗^L_{O_X} (O_X)^∨ ⟶ RSheafHom(O_X, O_X)` is invertible, the perfectness hypothesis of
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_self` being discharged at an object
that `Stacks.SheafOfModules.not_isZero_derivedStructureSheaf` shows is not zero. -/
theorem isIso_derivedTensorDualToSheafHom_self_derivedStructureSheaf :
    IsIso (derivedTensorDualToSheafHom Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
      (RingedSite.derivedStructureSheaf (ringedSite Rc))) :=
  isIso_derivedTensorDualToSheafHom_self Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
    (isPerfect_derivedStructureSheaf Rc)

/-- **The coevaluation of Example 0FPC at `O_X[0]`**, `η : O_X ⟶ O_X ⊗^L_{O_X} (O_X)^∨`. -/
def derivedDualCoevaluation_derivedStructureSheaf :
    letI := derivedMonoidalStructure Rc
    𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
      RingedSite.derivedStructureSheaf (ringedSite Rc) ⊗
        derivedDual Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  derivedDualCoevaluation Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
    (isPerfect_derivedStructureSheaf Rc)

/-- **The defining property of the coevaluation, at `O_X[0]`.** The source's "sending `1` to the
section corresponding to `id_K`" at `K = O_X[0]`: this is the equation that pins `η`, instantiated
at an object the library proves is not a zero object, so the clause is not discharged by
vanishing. -/
theorem derivedDualCoevaluation_comp_derivedStructureSheaf :
    derivedDualCoevaluation Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
          (isPerfect_derivedStructureSheaf Rc) ≫
        derivedTensorDualToSheafHom Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) =
      RingedSite.derivedIdentitySection (ringedSite Rc)
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) :=
  derivedDualCoevaluation_comp Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
    (isPerfect_derivedStructureSheaf Rc)

end Stacks.SheafOfModules

end
