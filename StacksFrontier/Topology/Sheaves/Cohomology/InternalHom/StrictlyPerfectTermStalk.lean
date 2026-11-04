module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FinitePresentationOfSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafStalkNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of an internal Hom sheaf out of a term of a strictly perfect complex

The stalk comparison of Stacks 01CP, `Hom_{O_X}(F, G)_x ≅ (F_x →ₗ[O_{X,x}] G_x)`, is
`Stacks.SheafOfModules.internalHomSheafStalkEquiv`, stated for `F` of finite presentation. The
terms of a strictly perfect complex satisfy `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`
instead: they are retracts of an iterated binary biproduct `unitPower X r`. This file shows that
such a module satisfies the Stacks 08FL condition `IsDirectSummandOfFiniteFree`, a retract of
`SheafOfModules.free (ULift (Fin r))`, and hence is of finite presentation, so that 01CP applies
to it.

## Main statements

* `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand.isDirectSummandOfFiniteFree`: a finite free
  summand satisfies the Stacks 08FL termwise condition.
* `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand.isFinitePresentation`: a finite free summand
  is of finite presentation.
* `Stacks.SheafOfModules.internalHomSheafStalkEquivOfIsFiniteFreeSummand`: the 01CP stalk
  identification `Hom_{O_X}(F, G)_x ≃ (F_x →ₗ[O_{X,x}] G_x)` for `F` a finite free summand.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A finite free summand satisfies the Stacks 08FL termwise condition.** A module which is a
retract of `unitPower X r` is a direct summand of the finite free module
`SheafOfModules.free (ULift (Fin r))`. -/
theorem IsFiniteFreeSummand.isDirectSummandOfFiniteFree
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    _root_.IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M := by
  obtain ⟨r, ⟨ρ⟩⟩ := (isFiniteFreeSummand_iff_retract_biproduct X M).1 hM
  exact InvertibleDerived.isDirectSummandOfFiniteFree_of_retract_biproduct
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ρ

/-- **A finite free summand is of finite presentation.** -/
theorem IsFiniteFreeSummand.isFinitePresentation
    [∀ T : X.C, HasSheafify (X.J.over T) AddCommGrpCat.{u}]
    [∀ T : X.C, (X.J.over T).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    M.IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_of_isDirectSummandOfFiniteFree
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M (hM.isDirectSummandOfFiniteFree X)

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  (F G : SheafOfModules.{u} (structureSheaf Rc))

/-- **The 01CP stalk identification at a finite free summand.** For `F` a finite free summand of
`O_X`-modules, the stalk of `Hom_{O_X}(F, G)` at `x` is the module of `O_{X,x}`-linear maps
`F_x →ₗ G_x`. -/
@[ega "0 5.2.6" "special case"]
def internalHomSheafStalkEquivOfIsFiniteFreeSummand
    (hF : _root_.AlgebraicGeometry.RingedSite.IsFiniteFreeSummand (ringedSite Rc) F) (x : X) :
    SheafHomStalk.modStalk
        (_root_.AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSite Rc) F G) x
        ≃ₗ[SheafHomStalk.ringStalk Rc x]
      (SheafHomStalk.modStalk F x →ₗ[SheafHomStalk.ringStalk Rc x]
        SheafHomStalk.modStalk G x) :=
  haveI : F.IsFinitePresentation := hF.isFinitePresentation (ringedSite Rc)
  internalHomSheafStalkEquiv Rc F G x

end Stacks.SheafOfModules

end
