module

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
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Sites.Grothendieck


/-! # The topology inherited from a base site

Let `(𝒞, J)` be a site and let `q : 𝒴 ⥤ 𝒞` be a fibred category. The topology on `𝒴`
*inherited* from `𝒞` (Stacks, Definition 8.10.2 and Lemma 8.10.1) has as covering
families the families of strongly cartesian morphisms of `𝒴` whose `q`-images cover in
`𝒞`. No global `HasPullbacks 𝒴` is required: `𝒴` only needs the fibre products of
covering arrows, which exist by Stacks, Categories Lemma 4.35.15.
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒴 : Type u₃} [Category.{v₁} 𝒞] [Category.{v₃} 𝒴]

/-- A Grothendieck topology `J𝒴` on `𝒴` *is the topology inherited from `(𝒞, J)` along
`q : 𝒴 ⥤ 𝒞`* (Stacks, Definition 8.10.2 and Lemma 8.10.1) when a family
`{ g i : Y' i ⟶ Y }` of strongly cartesian morphisms of `𝒴` generates a covering sieve
of `J𝒴` exactly when its image family `{ q(g i) : q(Y' i) ⟶ q Y }` generates a covering
sieve of `J` in `𝒞`.

The biconditional constrains `J𝒴` only on families assumed strongly cartesian, but for
a `q` fibred in groupoids that is no restriction: every morphism of `𝒴` is then
`q`-strongly cartesian (`IsFiberedInGroupoids.isStronglyCartesian`, Stacks 003V), so
every `J𝒴`-covering family is a strongly cartesian family and the biconditional
descends it to a `J`-covering family of `𝒞`.

**Stacks 06NV** names the site `(𝒴, Cov(𝒴))` produced by Stacks 06NU "the structure of site on
`𝒴` inherited from `𝒞`". That name belongs to the CONSTRUCTION, which is
`CategoryTheory.Functor.inheritedTopology` (`Sites/Stack/InheritedSite.lean`) and is where the
`@[stacks 06NV]` tag sits. This predicate is the characterisation: it says of a *given* topology on
`𝒴` that it is the inherited one, which is what consumers quantifying over an arbitrary topology
need. It deliberately carries no tag — a definition tag on a predicate asserts nothing until
something is shown to satisfy it, and while no witness exists the notion may be empty. -/
def IsInheritedTopology
    (q : 𝒴 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴) : Prop :=
  ∀ {Y : 𝒴} {I : Type w} (Y' : I → 𝒴) (g : ∀ i, Y' i ⟶ Y),
    (∀ i, q.IsStronglyCartesian (q.map (g i)) (g i)) →
    (Sieve.ofArrows Y' g ∈ J𝒴 Y ↔
      Sieve.ofArrows (fun i => q.obj (Y' i)) (fun i => q.map (g i)) ∈ J (q.obj Y))

end CategoryTheory.Functor
