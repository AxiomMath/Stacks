module

public import Mathlib.AlgebraicGeometry.Artinian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BoundedDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Vanishing of long first Chern class products on a scheme of bounded dimension

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, with `S` a Jacobson
scheme whose dimension function vanishes at every closed point, and let `X` be a scheme locally
of finite type over `S` whose topological dimension is at most `d`. Stacks 0FDX says that for
invertible modules `L_1, …, L_{d+1}` on `X` the product

  `c₁(L_1) ∘ ⋯ ∘ c₁(L_{d+1}) = 0`   in `A^{d+1}(X)`.

Over such a base the delta-dimension of `X` is pinned between `0` and `d`: it is nonnegative by
Stacks 02QO (`Stacks.Chow.relativeDimension_nonneg`) and at a point `x` it is the dimension of
the integral closed subscheme `closure {x}`, again by Stacks 02QO, which is at most the
dimension of `X`. So `CH_k(X) = 0` unless `0 ≤ k ≤ d`, and an operation that lowers the
delta-dimension by `d + 1` has, for every `k`, either zero source or zero target.

That gives three vanishing statements outright:

* the cap-product form of Stacks 0FDX on `X` itself — a product of `d + 1` first Chern class
  cap operators annihilates every Chow class of `X`;
* the same for the product of the first Chern classes of a *given* sequence of invertible
  modules on `X`, taken as the tower of the cap products those modules themselves define;
* for every bivariant class of degree at least `d + 1`, the vanishing of its cap operation on
  every test scheme of dimension at most `d`.

Independently of that, step 1 of the source proof — the case `d = 0` — is proved outright on
cycles: a scheme of dimension zero locally of finite type over the base is locally Artinian,
hence discrete, so every invertible module on it is trivial and its first Chern class cap
product vanishes by Stacks 02SP.

## Main definitions

* `Stacks.Chow.firstChernCapTower` — the composite `A_n(X) ⟶ A_{n-r}(X)` of the first Chern
  class cap products of a sequence of invertible modules on `X`.

## Main results

* `Stacks.Chow.firstChernClassCapOfInvertible_eq_zero_of_topologicalKrullDim_le_zero` — **step 1
  of the proof of Stacks 0FDX**: in dimension zero every first Chern class cap product is zero.
* `Stacks.Chow.chowGroup_eq_zero_of_neg`,
  `Stacks.Chow.chowGroup_eq_zero_of_topologicalKrullDim_lt` — `CH_k(X) = 0` below `0` and above
  the dimension of `X`.
* `Stacks.Chow.iteratedChernCapOnChow_eq_zero_of_topologicalKrullDim_le` — **Stacks 0FDX, the
  cap-product form on `X`**: `c₁(L_1) ∩ ⋯ ∩ c₁(L_{d+1}) ∩ α = 0` for every `α`, for an arbitrary
  list of first Chern class cap operators.
* `Stacks.Chow.firstChernCapTower_eq_zero_of_topologicalKrullDim_le` — **Stacks 0FDX for given
  invertible modules**: the same vanishing for the tower of the cap products of `L_1, …, L_r`
  themselves, which is the form that mentions the modules of the source statement.
* `Stacks.Chow.BivariantClass.cap_eq_zero_of_topologicalKrullDim_le` — **Stacks 0FDX on test
  schemes of dimension at most `d`**: a bivariant class of degree at least `d + 1` caps every
  class of such a test scheme to zero.

## Implementation notes

### What of Stacks 0FDX is proved here, and what is not

The conclusion of Stacks 0FDX is an equality in `A^{d+1}(X)`, and a bivariant class is zero
exactly when it caps to zero on **every** test scheme locally of finite type over `X`
(Stacks 02UC, available here as
`Stacks.Chow.BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero`). A test scheme
may have dimension far larger than `d`, so the dimension of `X` alone does not make the target
Chow groups vanish there, and the argument of this file reaches only the test schemes of
dimension at most `d` — among them `X` itself. The source closes the remaining test schemes by
geometry: it writes `L_{d+1}` as a difference of effective Cartier divisors (Stacks 0AYM,
available here as
`AlgebraicGeometry.InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf`),
factors `c₁(L_{d+1})` as the Gysin class of such a divisor followed by proper pushforward
(Stacks 02T9, available here as
`Stacks.Chow.properChowPushforward_gysinHomomorphismOfInvertible`), and induces on the
dimension. That induction, and with it the equality `c₁(L_1) ∘ ⋯ ∘ c₁(L_{d+1}) = 0` in
`A^{d+1}(X)` of the source, is
`Stacks.Chow.firstChernClassProduct_eq_zero_of_topologicalKrullDim_le`, where the product is the
composite of bivariant first Chern classes `Stacks.Chow.firstChernClassProduct`.

### The product of first Chern classes is taken as the iterated cap operation

`Stacks.Chow.iteratedChernCapOnChow` is the repository's `c₁ ∩ ⋯ ∩ c₁ ∩ -`, indexed by a list of
`Stacks.Chow.ChernCapOperator`s — the datum an invertible module provides once Stacks 02SJ and
Stacks 02TI are formalized. Quantifying over all lists of operators of length at least `d + 1` is
stronger than fixing the operators attached to a given tuple of invertible modules, so the statement
proved here does not depend on which cap operators an invertible module turns out to provide.

That form mentions no invertible module, so the form that does is also proved:
`Stacks.Chow.firstChernCapTower` composes the `Stacks.Chow.firstChernCapStep` operations
of a given sequence of invertible modules, each of which is the cap product of the module itself
at `Stacks.Chow.firstChernComponentCycleRule`. What it carries for each module is
`Stacks.Chow.InvertibleChernCapDescends`, namely Stacks 02TI in every degree, which by
`Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_iff` is equivalent to the
existence of the descended cap products and so is not a weakening.

### The hypotheses that are not needed

Stacks 0FDX assumes `X` of finite type over `S` with an ample invertible module; the ample
module is used in the source only to reach Stacks 0AYM, and finite type only through local
finite type. Neither is a hypothesis below. In their place stand the two conditions under which
the delta-dimension of `X` is bounded by its topological dimension, namely that `S` is a
Jacobson space and that its dimension function vanishes at closed points — exactly the
hypotheses of `Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat`.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Step 1 of the source proof: the case of dimension zero -/

/-- **Step 1 of the proof of Stacks 0FDX, proved outright.** On a scheme `X` locally of finite
type over the base and of topological dimension at most zero, the first Chern class cap product
of every invertible `𝒪_X`-module vanishes:

  `c₁(L) ∩ α = 0`  in `A_k(X)`,  for every `α ∈ Z_{k+1}(X)`.

`X` is locally Noetherian, being locally of finite type over a locally Noetherian base, so
dimension zero makes it locally Artinian and hence discrete; on a discrete scheme every
invertible module is trivial
(`Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`), and the cap product depends
only on the isomorphism class of the module and vanishes on `𝒪_X` by Stacks 02SP.

This is the `d = 0` instance of Stacks 0FDX read on cycles. No Jacobson hypothesis is needed,
and the cap product is the canonical one of
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule` rather than a carried datum. -/
theorem firstChernClassCapOfInvertible_eq_zero_of_topologicalKrullDim_le_zero
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 0) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k L α = 0 := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have _ : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have _ : DiscreteTopology (X : Type u) := inferInstance
  have hinv : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology X L
  rw [firstChernClassCapOfInvertible_congr C p k L (SheafOfModules.unit X.ringCatSheaf) e α,
    firstChernClassCapOfInvertible_unit]

variable (C : ChowSituation.{u}) [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)

include hδ

/-! ### The Chow groups outside the range of the delta-dimension -/

/-- `CH_k(X) = 0` in negative degrees: over a Jacobson base whose dimension function vanishes at
closed points the delta-dimension is nonnegative, by Stacks 02QO. -/
theorem chowGroup_eq_zero_of_neg {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ}
    (hk : k < 0) (α : chowGroup C p k) : α = 0 :=
  chowGroup_eq_zero C p (fun x => by
    have := relativeDimension_nonneg C hδ p x
    omega) α

/-- `CH_k(X) = 0` above the topological dimension of `X`: no point of `X` has delta-dimension
larger than `dim X`, by `Stacks.Chow.relativeDimension_le_of_topologicalKrullDim_le` read on the
closed subset `X` of `X`. -/
theorem chowGroup_eq_zero_of_topologicalKrullDim_lt {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {d : ℕ} (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {k : ℤ}
    (hk : (d : ℤ) < k) (α : chowGroup C p k) : α = 0 :=
  chowGroup_eq_zero C p (fun x => by
    have := relativeDimension_le_of_topologicalKrullDim_le C hδ p
      (T := (Set.univ : Set X)) isClosed_univ (r := d)
      (by rwa [topologicalKrullDim_univ]) (Set.mem_univ x)
    omega) α

/-- An additive map between Chow groups is zero when its source is zero because the degree is
negative or above `d` (with `dim X ≤ d`), or when its target is zero because the degree is
negative. -/
private theorem map_eq_zero_of_degree {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] {d : ℕ} (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    {a b : ℤ} (f : chowGroup C p a →+ chowGroup C q b) (h : a < 0 ∨ (d : ℤ) < a ∨ b < 0)
    (α : chowGroup C p a) : f α = 0 := by
  rcases h with h | h | h
  · rw [chowGroup_eq_zero_of_neg C hδ p h α, map_zero]
  · rw [chowGroup_eq_zero_of_topologicalKrullDim_lt C hδ p hd h α, map_zero]
  · exact chowGroup_eq_zero_of_neg C hδ q h _

/-! ### Stacks 0FDX, the cap-product form on `X` -/

/-- **Stacks 0FDX, the cap-product form on `X` itself.** Let `X` be locally of finite type over
a Jacobson base whose dimension function vanishes at closed points, and let the topological
dimension of `X` be at most `d`. Then any `d + 1` (or more) first Chern class cap operators on
`X` annihilate every Chow class of `X`:

  `c₁(L_1) ∩ ⋯ ∩ c₁(L_{d+1}) ∩ α = 0`   in `CH_k(X)`,  for every `α ∈ CH_{k + d + 1}(X)`.

The operation goes `CH_{k + r}(X) ⟶ CH_k(X)` with `r = Os.length ≥ d + 1`. For `k < 0` the
target vanishes, and for `k ≥ 0` the source has degree `k + r ≥ d + 1 > d` and vanishes. So the
proof is a delta-dimension count, not the induction on `d` of the source, and it establishes the
same vanishing for every additive map of that bidegree. -/
theorem iteratedChernCapOnChow_eq_zero_of_topologicalKrullDim_le {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {d : ℕ} (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (Os : List (ChernCapOperator C p)) (hlen : d + 1 ≤ Os.length) (k : ℤ)
    (α : chowGroup C p (k + (Os.length : ℤ))) :
    iteratedChernCapOnChow C p Os k α = 0 := by
  have hcast : (d : ℤ) + 1 ≤ (Os.length : ℤ) := by exact_mod_cast hlen
  exact map_eq_zero_of_degree C hδ p p hd _ (by omega) α

/-! ### Stacks 0FDX for the first Chern classes of given invertible modules -/

/-- The tower of first Chern class cap products of a sequence of invertible modules: the composite

  `A_n(X) ⟶ A_{n-1}(X) ⟶ ⋯ ⟶ A_{n-r}(X)`

whose `i`-th arrow is intersection with `c₁(L i)`, namely
`Stacks.Chow.firstChernCapStep` at `i`. For `r = 0` it is the identity.

The source of the composite is written `A_{n - 0}(X)`, the degree the step at `i = 0` consumes.

The sequence of modules is indexed by `ℕ` because that is what the recursion consumes; a finite
family `L_1, …, L_r` is fed in by extending it arbitrarily past `r`, for instance by repeating
one of its members, which preserves both hypotheses since each member carries them. Only the
indices below `r` are used. -/
def firstChernCapTower {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (n : ℤ)
    (L : ℕ → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)]
    (hfac : ∀ i, InvertibleChernCapDescends C p (L i)) :
    (r : ℕ) → chowGroup C p (n - ((0 : ℕ) : ℤ)) →+ chowGroup C p (n - (r : ℤ))
  | 0 => AddMonoidHom.id _
  | r + 1 =>
      (firstChernCapStep C p n (L r) (hfac r) r).comp (firstChernCapTower p n L hfac r)

/-- **Stacks 0FDX for the first Chern classes of given invertible modules.** Let `X` be locally
of finite type over a Jacobson base whose dimension function vanishes at closed points, and let
the topological dimension of `X` be at most `d`. Then for every sequence `L_1, L_2, …` of
invertible `𝒪_X`-modules on `X` and every `r ≥ d + 1`,

  `c₁(L_1) ∩ ⋯ ∩ c₁(L_r) ∩ α = 0`   in `A_{n-r}(X)`,  for every `α ∈ A_n(X)`,

the product being the tower `Stacks.Chow.firstChernCapTower` of the cap products
`Stacks.Chow.firstChernCapStep` of the `L_i` themselves.

The degree count: if `n - r < 0` the target `A_{n-r}(X)` vanishes, and otherwise
`n ≥ r ≥ d + 1 > d`, so the source `A_n(X)` vanishes. -/
theorem firstChernCapTower_eq_zero_of_topologicalKrullDim_le {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {d : ℕ} (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (n : ℤ)
    (L : ℕ → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)]
    (hfac : ∀ i, InvertibleChernCapDescends C p (L i)) (r : ℕ) (hr : d + 1 ≤ r)
    (α : chowGroup C p (n - ((0 : ℕ) : ℤ))) :
    firstChernCapTower C p n L hfac r α = 0 := by
  have hcast : (d : ℤ) + 1 ≤ (r : ℤ) := by exact_mod_cast hr
  exact map_eq_zero_of_degree C hδ p p hd _ (by omega) α

/-! ### Stacks 0FDX on test schemes of bounded dimension -/

/-- **Stacks 0FDX on the test schemes of dimension at most `d`.** A bivariant class of degree at
least `d + 1` caps every Chow class of every test scheme of topological dimension at most `d` to
zero. Applied to a product of `d + 1` first Chern classes on a scheme `X` of dimension `d`, and
to the test scheme `X` itself, this is the conclusion of Stacks 0FDX read on that test scheme.

For a test scheme `T` of dimension at most `d` the source group `CH_k(T)` vanishes unless
`0 ≤ k ≤ d`, and in that range the target group has degree `k - p ≤ d - (d + 1) < 0`, so it
vanishes by nonnegativity of the delta-dimension. -/
theorem BivariantClass.cap_eq_zero_of_topologicalKrullDim_le (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) {d : ℕ} (hp : (d : ℤ) + 1 ≤ p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    c.cap g k α = 0 := by
  exact map_eq_zero_of_degree C hδ _ _ hT _ (by omega) α

end Stacks.Chow

end
