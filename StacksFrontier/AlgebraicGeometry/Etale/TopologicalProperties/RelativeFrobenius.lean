module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Isomorphism

/-!
# Relative Frobenius of an étale scheme

If a scheme `U` is étale over a scheme `X` of prime characteristic, then the relative Frobenius
of `U` over `X` is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_relativeFrobenius_of_etale`: the relative Frobenius of an étale
  `X`-scheme is an isomorphism in `Over X`.

## References

* [Stacks Project, Tag 0EBS](https://stacks.math.columbia.edu/tag/0EBS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The relative Frobenius of an étale scheme is an isomorphism. -/
@[stacks 0EBS, sga "4½ Fonctions_L 3.4", sga "5 XV 1.Proposition2" "Clause c) 2)"]
public instance isIso_relativeFrobenius_of_etale (X : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (U : Over X) [Etale U.hom] :
    IsIso (relativeFrobenius X p hX U) :=
  inferInstance

end AlgebraicGeometry

end
