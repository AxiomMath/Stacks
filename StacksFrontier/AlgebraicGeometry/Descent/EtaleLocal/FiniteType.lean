module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.ZariskiToEtale
public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local finite type is étale local on the source and target

Local finite type of a morphism of schemes is Zariski local on the source and on the target
in Mathlib. This file upgrades both localities from the Zariski precoverage to the étale
precoverage and feeds the two upgrades into the criterion of Tag 04R2, which yields
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` for local finite type.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isLocalAtSource_etalePrecoverage_locallyOfFiniteType` and
  `AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_locallyOfFiniteType` are the two
  localities for the étale precoverage.
* `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_locallyOfFiniteType` is their
  combination through Tag 04R2.

## Implementation notes

Both upgrades are instances of
`AlgebraicGeometry.isLocalAtSource_etalePrecoverage_of_zariski_of_descent` and
`AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_zariski_of_descent`, so all that is
supplied here is the descent of local finite type along a surjective étale morphism of
sources — which is `AlgebraicGeometry.locallyOfFiniteType_of_comp_surjective_etale`, in turn
the fppf descent `AlgebraicGeometry.locallyOfFiniteType_of_comp_of_fppf`, an étale morphism
being flat and locally of finite presentation — together with preservation under composition
with an étale morphism on either side, which is typeclass inference.

The criterion of Tag 04R2 also asks for stability under postcomposition with open immersions,
which is recorded here as
`AlgebraicGeometry.respectsRight_isOpenImmersion_locallyOfFiniteType`. It is the special case
of postcomposition with an étale morphism, an open immersion being étale; the generic form is
`AlgebraicGeometry.respectsRight_isOpenImmersion_of_etale_postcomp`.

The Zariski localities that the two upgrades take as instance arguments have to be passed by
name rather than found by typeclass inference: the goal `IsZariskiLocalAtSource P` for a
concrete `P` does not unify with the conclusion of
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`.

Both localities are stated for the étale precoverage only, which is weaker than Stacks 036O
("fppf local on the source") and than Stacks 02KX ("fpqc local on the base"); neither of those
tags is claimed here.

## References

* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- Postcomposition with an open immersion preserves local finite type: an open immersion is
étale, hence locally of finite type, and local finite type is stable under composition. -/
@[ega "I 6.6.6" "(ii), special case", ega "IV 1.3.4" "(ii), special case"]
instance respectsRight_isOpenImmersion_locallyOfFiniteType :
    MorphismProperty.RespectsRight (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) where
  postcomp g hg f hf := by
    have : IsOpenImmersion g := hg
    have : LocallyOfFiniteType f := hf
    infer_instance

/-- Local finite type of a morphism of schemes is étale local on the source. -/
instance isLocalAtSource_etalePrecoverage_locallyOfFiniteType :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u})
  isLocalAtSource_etalePrecoverage_of_zariski_of_descent _
    (fun g f hg hf => have : Etale g := hg; have : LocallyOfFiniteType f := hf; inferInstance)
    locallyOfFiniteType_of_comp_surjective_etale

/-- Local finite type of a morphism of schemes is étale local on the target. -/
instance isLocalAtTarget_etalePrecoverage_locallyOfFiniteType :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  have _ : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{u})
  isLocalAtTarget_etalePrecoverage_of_zariski_of_descent _
    (fun f g hf hg => have : Etale g := hg; have : LocallyOfFiniteType f := hf; inferInstance)
    locallyOfFiniteType_of_comp_surjective_etale

/-- **Local finite type is étale local on the source and target**, which is item (3) of the
list of Stacks 04R3. The two separate localities are combined by the criterion of Stacks 04R2,
`AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget`. -/
theorem isEtaleLocalOnSourceAndTarget_locallyOfFiniteType :
    IsEtaleLocalOnSourceAndTarget (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
  isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget _

end AlgebraicGeometry
