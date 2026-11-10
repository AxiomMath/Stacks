module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-!
# A stack in groupoids for a topology is a stack in groupoids for every coarser topology

The two descent conditions of `CategoryTheory.Functor.IsStackInGroupoids` are universally
quantified over the covering families of the topology, so they get weaker as the topology gets
coarser: a category fibred in groupoids which is a stack in groupoids for `J` is one for every
`J' ≤ J`. The same monotonicity holds for the localized topology of a slice category, whose
covering sieves are, by definition, the sieves whose image in the base lies in the topology.

Together these say that the fppf stack condition of a category over a big fppf site implies its
étale stack condition — axiom [0] of Artin's axioms (Stacks 07Y3) — since the big étale topology
is coarser than the big fppf topology.

## Main results

* `CategoryTheory.Functor.IsStackInGroupoids.of_le`: **Stacks 02ZI for a coarser topology**.

## Implementation notes

Monotonicity of the localized topology `CategoryTheory.GrothendieckTopology.over` is not restated
here: it is `CategoryTheory.GrothendieckTopology.over_mono` of
`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean`, and the consumers of this file
that need it are in `AlgebraicGeometry` and spell it out in one line rather than import that module.

Only the groupoid-indexed rendering of Stacks 02ZJ is treated. The sieve-indexed
`CategoryTheory.Functor.IsStack` of Stacks 026F is phrased through the sheaf condition for the
presheaves `Mor(x, y)` on a slice site and through `HasEffectiveDescent`, neither of which is a
bare quantification over the covering families of the topology, so its monotonicity is a separate
statement and is not needed by the consumers of this file.
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ u₁ v₂ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace Functor

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **Stacks 02ZI for a coarser topology.** A category fibred in groupoids which is a stack in
groupoids for `J` is a stack in groupoids for every topology `J' ≤ J`: both descent conditions
range over the covering families of the topology, and every covering family of `J'` is one of
`J`. -/
theorem IsStackInGroupoids.of_le {p : 𝒮 ⥤ 𝒞} {J J' : GrothendieckTopology 𝒞}
    (hp : p.IsStackInGroupoids.{w} J) (h : J' ≤ J) :
    p.IsStackInGroupoids.{w} J' where
  isFiberedInGroupoids := hp.isFiberedInGroupoids
  isom_isSheaf := by
    intro U x y hx hy I V f hf
    exact hp.isom_isSheaf x y hx hy V f (h _ hf)
  effective_descent := by
    intro U I V f hf
    exact hp.effective_descent V f (h _ hf)

end Functor

end CategoryTheory

end
