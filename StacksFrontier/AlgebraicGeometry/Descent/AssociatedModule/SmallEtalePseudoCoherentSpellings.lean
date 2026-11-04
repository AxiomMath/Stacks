module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence on the small étale ringed site of a scheme

The sheaf of rings `Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X hX).O` of
the small étale ringed site of a scheme `X` is `AlgebraicGeometry.SmallEtale.structureSheaf`, and
a model of the derived category of modules over the latter gives one over the former. This makes
the pseudo-coherence predicate `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` of
[Stacks, Tag 08FT] available on the small étale ringed site, as [Stacks, Tag 08HE] uses it.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtaleRingedSite_ringSheaf`: the sheaf of rings of the small
  étale ringed site is `AlgebraicGeometry.SmallEtale.structureSheaf`.
* `AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite`: a model of the derived
  category of modules over the sheaf of rings of the small étale ringed site, from one over
  `AlgebraicGeometry.SmallEtale.structureSheaf`.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The sheaf of rings of the small étale ringed site of `X` is
`AlgebraicGeometry.SmallEtale.structureSheaf`. -/
public theorem smallEtaleRingedSite_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X hX).O) =
      structureSheaf B X hX :=
  rfl

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (structureSheaf B X hX))]

/-- A model of the derived category of modules over the sheaf of rings of the small étale ringed
site of `X`, obtained from a model over `AlgebraicGeometry.SmallEtale.structureSheaf`. -/
public instance hasDerivedCategory_smallEtaleRingedSite :
    HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X hX).O)) :=
  inferInstanceAs (HasDerivedCategory.{d} (SheafOfModules.{u} (structureSheaf B X hX)))

end SmallEtale

end AlgebraicGeometry

end
