module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings

/-!
# Universal openness is étale local on the source and target

Being a universally open morphism of schemes is local for the étale topology on both the source
and the target.

## Main results

* `AlgebraicGeometry.UniversallyOpen.isLocalAtSource_etalePrecoverage`: universal openness is
  local on the source for the étale topology.
* `AlgebraicGeometry.UniversallyOpen.respectsRight_etale`: postcomposition with an étale
  morphism preserves universal openness.
* `AlgebraicGeometry.UniversallyOpen.isEtaleLocalOnSourceAndTarget`: universal openness is étale
  local on the source and target.

## References

* [Stacks Project, Tag 036Q](https://stacks.math.columbia.edu/tag/036Q)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Universal openness of morphisms of schemes is local on the source for the étale topology. -/
instance UniversallyOpen.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource (@UniversallyOpen : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  MorphismProperty.IsLocalAtSource.of_le Scheme.etalePrecoverage_le_fppfPrecoverage

/-- Postcomposition with an étale morphism preserves universal openness. -/
theorem UniversallyOpen.respectsRight_etale :
    MorphismProperty.RespectsRight (@UniversallyOpen : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf := by
    let : Etale i := hi
    let : UniversallyOpen f := hf
    let : UniversallyOpen i := UniversallyOpen.of_flat i
    exact inferInstance

/-- Being a universally open morphism of schemes is étale local on the source and target. -/
@[stacks 04R3 "universally open", sga "4 IV 8.5.5" "special case"]
theorem UniversallyOpen.isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@UniversallyOpen : MorphismProperty Scheme.{u}) :=
  let := UniversallyOpen.respectsRight_etale.{u}
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

end AlgebraicGeometry

end
