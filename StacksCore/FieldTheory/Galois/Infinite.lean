module

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import StacksCore.FieldTheory.KrullTopology
import StacksCore.FieldTheory.Normal.Defs
import StacksCore.Tactic.StacksAttribute

/-! # Infinite Galois theory -/

@[expose] public section

add_to_stacks 0BML InfiniteGalois.IntermediateFieldEquivClosedSubgroup
add_to_stacks 0BML "finite subextension ↔ open subgroup" InfiniteGalois.isOpen_iff_finite
add_to_stacks 0BML "Galois subextension ↔ normal closed subgroup" InfiniteGalois.normal_iff_isGalois

add_to_stacks 0BMK "homomorphism" AlgEquiv.restrictNormalHom
add_to_stacks 0BMK "surjective" AlgEquiv.restrictNormalHom_surjective
add_to_stacks 0BMK "continuous, for an intermediate field"
  InfiniteGalois.restrictNormalHom_continuous

namespace AlgEquiv

variable (K M L : Type*) [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
  [IsScalarTower K M L]

/-- **Stacks 0BMM** (the inclusion is continuous).
For a tower `L/M/K` with `L/K` algebraic, the inclusion `Gal(L/M) → Gal(L/K)` is continuous for
the Krull topologies. -/
@[stacks 0BMM "continuous"]
theorem continuous_restrictScalarsHom [Algebra.IsAlgebraic K L] :
    Continuous (restrictScalarsHom K : Gal(L/M) →* Gal(L/K)) :=
  continuous_krullTopology fun x y ↦
    isOpen_krullTopology_apply_eq M x ((Algebra.IsAlgebraic.isAlgebraic (R := K) y).tower_top M)

/-- **Stacks 0BMK** (the restriction is continuous).
For a tower `L/M/K` with `L/K` algebraic and `M/K` normal, the restriction
`Gal(L/K) → Gal(M/K)` is continuous for the Krull topologies. -/
@[stacks 0BMK "continuous", stacks 0BMM "continuous"]
theorem continuous_restrictNormalHom [Normal K M] [Algebra.IsAlgebraic K L] :
    Continuous (restrictNormalHom M : Gal(L/K) →* Gal(M/K)) :=
  continuous_krullTopology fun x y ↦ by
    convert isOpen_krullTopology_apply_eq' K (algebraMap M L x) (algebraMap M L y) using 1
    ext σ
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, coe_restrictNormalHom,
      ← (algebraMap M L).injective.eq_iff, restrictNormal_commutes]

/-- **Stacks 0BMM** (`Gal(L/M)` is a closed subgroup).
For a tower `L/M/K` with `L/K` Galois, the inclusion `Gal(L/M) → Gal(L/K)` is a closed
embedding. -/
@[stacks 0BMM "closed embedding"]
theorem isClosedEmbedding_restrictScalarsHom [IsGalois K L] :
    Topology.IsClosedEmbedding (restrictScalarsHom K : Gal(L/M) →* Gal(L/K)) :=
  have := IsGalois.tower_top_of_isGalois K M L
  (continuous_restrictScalarsHom K M L).isClosedEmbedding (restrictScalars_injective K)

/-- **Stacks 0BMM** (`Gal(M/K)` carries the quotient topology).
For a tower `L/M/K` with `L/K` Galois and `M/K` normal, the restriction `Gal(L/K) → Gal(M/K)` is
a quotient map. -/
@[stacks 0BMM "quotient map"]
theorem isQuotientMap_restrictNormalHom [IsGalois K L] [Normal K M] :
    Topology.IsQuotientMap (restrictNormalHom M : Gal(L/K) →* Gal(M/K)) :=
  .of_surjective_continuous (restrictNormalHom_surjective L) (continuous_restrictNormalHom K M L)

end AlgEquiv
