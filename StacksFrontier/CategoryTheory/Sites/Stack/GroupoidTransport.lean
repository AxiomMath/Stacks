module

import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init

public import StacksFrontier.CategoryTheory.Sites.Stack.Transport

/-!
# Being a stack in groupoids transports along an equivalence over the base (Stacks 042X)

Let `(𝒞, J)` be a site and let `𝒳`, `𝒴` be categories over `𝒞` which are equivalent as
categories over `𝒞`, that is `BasedCategory.Equivalence 𝒳 𝒴` (Stacks 042G,
`StacksFrontier/CategoryTheory/FiberedCategory/EquivalenceInvariance.lean`). Then `𝒳` is a stack
in groupoids over `𝒞` if and only if `𝒴` is.

Stacks 042X is Stacks 042W — the same statement for stacks,
`BasedCategory.isStack_iff_of_equivalence` in
`StacksFrontier/CategoryTheory/Sites/Stack/Transport.lean` — combined with the transport of being
fibred in groupoids, which is what this file adds.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.isFiberedInGroupoids` and
  `CategoryTheory.BasedCategory.isFiberedInGroupoids_iff_of_equivalence`: being fibred in groupoids
  transports along an equivalence over `𝒞`.
* `CategoryTheory.BasedCategory.isFiberedInGroupoids_and_isStack_iff_of_equivalence`:
  **Stacks 042X**.

## Implementation notes

"Stack in groupoids" is read here as clause (3) of Stacks 02ZJ: a category over `𝒞` which is fibred
in groupoids over `𝒞` *and* is a stack over `𝒞`. That is the reading which 042X's own proof uses —
it cites 02ZJ precisely in order to reduce to 042W — and it is the one whose two halves are
available: `CategoryTheory.Functor.IsStack` is Stacks 026F and `Stacks 042W` is proved for it.
Equivalently, by Stacks 003V (`Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid`),
this is clause (2) of 02ZJ: a stack over `𝒞` all of whose fibre categories are groupoids.

The library's other rendering of a stack in groupoids,
`CategoryTheory.Functor.IsStackInGroupoids` (Stacks 02ZI, in
`StacksFrontier/CategoryTheory/Sites/InheritedTopology/Stack.lean`), spells the sheaf and descent
conditions out for covering families with genuine fibre-product overlaps instead of going through
`Functor.IsStack`; the two are not related by a lemma, so the statement below is not phrased with
it. No new predicate is introduced here, so nothing has to be bridged either.

Both halves of the transport are already available. Fibredness is Stacks 042G,
`BasedCategory.Equivalence.isFibered`; groupoid fibres transport by
`BasedCategory.Equivalence.fiber_isGroupoid`, proved in `Stack/Transport.lean` for Stacks 0431; and
Stacks 003V assembles the two into being fibred in groupoids. So no separate argument through the
quasi-inverse is needed, and in particular the transport stays inside the
`BasedCategory.Equivalence` world in which 042W is stated.

The two categories over `𝒞` live in independent object and morphism universes, as everywhere in
that world.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : BasedCategory.{v₂, u₂} 𝒞}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒞}

/-- Being fibred in groupoids transports along an equivalence over `𝒞`: by Stacks 003V it is
fibredness together with the fibre categories being groupoids, and each of those transports —
fibredness by Stacks 042G and groupoid fibres by `BasedCategory.Equivalence.fiber_isGroupoid`. -/
theorem BasedCategory.Equivalence.isFiberedInGroupoids (e : BasedCategory.Equivalence 𝒳 𝒴)
    (h : 𝒳.p.IsFiberedInGroupoids) : 𝒴.p.IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.2
    ⟨e.isFibered h.isFibered, e.fiber_isGroupoid h.fiber_isGroupoid⟩

/-- Two categories over `𝒞` which are equivalent as categories over `𝒞` are fibred in groupoids
over `𝒞` at the same time. -/
theorem BasedCategory.isFiberedInGroupoids_iff_of_equivalence
    (e : BasedCategory.Equivalence 𝒳 𝒴) :
    𝒳.p.IsFiberedInGroupoids ↔ 𝒴.p.IsFiberedInGroupoids :=
  ⟨e.isFiberedInGroupoids, e.symm.isFiberedInGroupoids⟩

/-- **Stacks 042X**. Let `(𝒞, J)` be a site and let `𝒳`, `𝒴` be categories over `𝒞`. If `𝒳` and
`𝒴` are equivalent as categories over `𝒞`, then `𝒳` is a stack in groupoids over `𝒞` if and only
if `𝒴` is.

"Stack in groupoids" is read as clause (3) of Stacks 02ZJ, fibred in groupoids together with being
a stack, which is the reading 042X's proof uses; the two conjuncts transport by
`BasedCategory.isFiberedInGroupoids_iff_of_equivalence` and by Stacks 042W,
`BasedCategory.isStack_iff_of_equivalence`. -/
@[stacks 042X]
theorem BasedCategory.isFiberedInGroupoids_and_isStack_iff_of_equivalence
    (e : BasedCategory.Equivalence 𝒳 𝒴) (J : GrothendieckTopology 𝒞) :
    𝒳.p.IsFiberedInGroupoids ∧ 𝒳.p.IsStack J ↔
      𝒴.p.IsFiberedInGroupoids ∧ 𝒴.p.IsStack J :=
  and_congr (isFiberedInGroupoids_iff_of_equivalence e) (isStack_iff_of_equivalence e J)

end CategoryTheory
