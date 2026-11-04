module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs

/-!
# Weakly associated points of a sheaf of modules on a scheme

Let `X` be a scheme and let `F` be an `𝒪_X`-module. A point `x : X` is *weakly associated* to
`F` when the maximal ideal `𝔪_x` of the local ring `𝒪_{X, x}` is a weakly associated prime of
the `𝒪_{X, x}`-module `F_x`, that is, when `𝔪_x` is minimal among the primes containing the
annihilator of some element of the stalk `F_x`. The weakly associated points of the scheme `X`
itself are those of its structure sheaf.

This file also defines the *relative assassin* `Ass_{X/S}(F)` of an `𝒪_X`-module along a
morphism `f : X ⟶ S`: the union over the points of `S` of the images in `X` of the associated
points of the restriction of `F` to the scheme-theoretic fibre.

## Main definitions

* `Stacks.Divisors.IsWeaklyAssociatedPoint` is the predicate that a point of a scheme is weakly
  associated to a sheaf of modules on it.
* `Stacks.Divisors.weaklyAssociatedPoints` is the set `WeakAss(F)` of weakly associated points
  of a sheaf of modules.
* `Stacks.Divisors.schemeWeaklyAssociatedPoints` is the set `WeakAss(X)` of weakly associated
  points of a scheme.
* `Stacks.Divisors.relativeAssassin` is the relative assassin `Ass_{X/S}(F)`.

## Main results

* `Stacks.Divisors.mem_weaklyAssociatedPoints_iff` and
  `Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff` identify membership in the two sets
  with the corresponding pointwise predicate.
* `Stacks.Divisors.isWeaklyAssociatedPoint_iff_exists_radical_annihilator_eq` and
  `Stacks.Divisors.isWeaklyAssociatedPoint_iff_forall_exists_pow_smul_eq_zero` describe the
  predicate purely in terms of the stalk: the minimality clause of the underlying
  ring-theoretic definition may be traded, over the local ring `𝒪_{X, x}`, for an equality of
  radicals of annihilators, or read elementwise.
* `Stacks.Divisors.IsAssociatedPoint.isWeaklyAssociatedPoint`: an associated point is weakly
  associated, so `Ass(F) ⊆ WeakAss(F)` (`Stacks.Divisors.associatedPoints_subset`).
* `Stacks.Divisors.IsWeaklyAssociatedPoint.nontrivial`: a weakly associated point has nonzero
  stalk.
* `Stacks.Divisors.mem_relativeAssassin`: the pointwise description of the relative assassin.

## Implementation notes

The ring-theoretic notion is `IsWeaklyAssociatedPrime` of Stacks tag 0547, in
`StacksFrontier/RingTheory/Ideal/WeaklyAssociatedPrime/Defs.lean`, which asks for an element whose
annihilator has the given prime as a *minimal* prime. It is therefore weaker than the
associated-prime notion `IsAssociatedPrimeStacks` of tag 00LA used by
`Stacks.Divisors.IsAssociatedPoint`, which asks for the annihilator to be equal to the prime.

The module structure on the stalk is `AlgebraicGeometry.Scheme.Modules.moduleStalk`, the
instance restated at the shape an `X.Modules` presents; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints.lean`.

Both notions are defined for every sheaf of modules: quasi-coherence is not used to form them,
so this is more general than the source, which states the definitions for a quasi-coherent
sheaf. In the same way the relative assassin is formed for every sheaf of modules.

The restriction of a module to the fibre over `s : S` is its pullback along
`AlgebraicGeometry.Scheme.Hom.fiberι`, and the associated points of that restriction are
carried into `X` by the same morphism.

## References

* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **Stacks 056L, part (1).** A point `x` is *weakly associated* to an `𝒪_X`-module `F` when
the maximal ideal of the local ring `𝒪_{X, x}` is a weakly associated prime of the stalk
`F_x`, that is, when it is minimal among the primes containing the annihilator of some element
of `F_x`. -/
@[stacks 056L "part (1)"]
abbrev IsWeaklyAssociatedPoint (F : X.Modules) (x : X) : Prop :=
  IsWeaklyAssociatedPrime (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

/-- **Stacks 056L, part (2).** The set `WeakAss(F)` of points weakly associated to an
`𝒪_X`-module `F`. -/
@[stacks 056L "part (2)"]
abbrev weaklyAssociatedPoints (F : X.Modules) : Set X := {x | IsWeaklyAssociatedPoint F x}

/-- Membership in the weakly associated points of a sheaf of modules is the weakly associated
point predicate. -/
@[simp]
theorem mem_weaklyAssociatedPoints_iff (F : X.Modules) (x : X) :
    x ∈ weaklyAssociatedPoints F ↔ IsWeaklyAssociatedPoint F x :=
  Iff.rfl

/-- **Stacks 056L, part (3).** The weakly associated points `WeakAss(X)` of a scheme `X` are
the weakly associated points of its structure sheaf. -/
@[stacks 056L "part (3)"]
abbrev schemeWeaklyAssociatedPoints (X : Scheme.{u}) : Set X :=
  weaklyAssociatedPoints (SheafOfModules.unit X.ringCatSheaf)

/-- A point is weakly associated to a scheme exactly when it is weakly associated to the
structure sheaf. -/
@[simp]
theorem mem_schemeWeaklyAssociatedPoints_iff (X : Scheme.{u}) (x : X) :
    x ∈ schemeWeaklyAssociatedPoints X ↔
      IsWeaklyAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x :=
  Iff.rfl

/-- Over the local ring `𝒪_{X, x}` the minimality clause may be traded for an equality of
radicals: `x` is weakly associated to `F` exactly when some element of the stalk `F_x` has
annihilator with radical the maximal ideal. -/
theorem isWeaklyAssociatedPoint_iff_exists_radical_annihilator_eq {F : X.Modules} {x : X} :
    IsWeaklyAssociatedPoint F x ↔
      ∃ m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        (Submodule.span (X.presheaf.stalk x) {m}).annihilator.radical =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  weaklyAssociated_maximalIdeal_iff_exists_radical_eq
    (N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)

/-- Elementwise form: a point is weakly associated to `F` exactly when some element of the
stalk `F_x` is killed by a power of every element of the maximal ideal, and is killed only by
elements of the maximal ideal. -/
theorem isWeaklyAssociatedPoint_iff_forall_exists_pow_smul_eq_zero {F : X.Modules} {x : X} :
    IsWeaklyAssociatedPoint F x ↔
      ∃ m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        (∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), ∃ n : ℕ, r ^ n • m = 0) ∧
          ∀ r : X.presheaf.stalk x,
            r • m = 0 → r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [isWeaklyAssociatedPoint_iff_exists_radical_annihilator_eq]
  refine exists_congr fun m => ?_
  simp only [← Submodule.mem_annihilator_span_singleton]
  refine ⟨fun h => ⟨fun r hr => h.ge hr, fun r hr => h.le (Ideal.le_radical hr)⟩, fun h => ?_⟩
  exact le_antisymm (fun r ⟨n, hn⟩ =>
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem n (h.2 _ hn)) h.1

/-- **Stacks 0589** at a point of a scheme: an associated point is weakly associated. The
annihilator of a witnessing element is then the maximal ideal itself, which is therefore
trivially minimal among the primes containing it. -/
theorem IsAssociatedPoint.isWeaklyAssociatedPoint {F : X.Modules} {x : X}
    (h : IsAssociatedPoint F x) : IsWeaklyAssociatedPoint F x := by
  obtain ⟨m, hm⟩ := isAssociatedPoint_iff_annihilator_span_eq.mp h
  exact ⟨m, ⟨⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, hm.le⟩,
    fun q hq _ => hm.ge.trans hq.2⟩⟩

/-- `Ass(F) ⊆ WeakAss(F)`: the associated points of a sheaf of modules on a scheme are weakly
associated. -/
theorem associatedPoints_subset (F : X.Modules) :
    associatedPoints F ⊆ weaklyAssociatedPoints F :=
  fun _ hx => hx.isWeaklyAssociatedPoint

/-- The stalk of `F` at a weakly associated point is nonzero: the annihilator of `0` is the
whole ring, whose radical is not the maximal ideal. -/
theorem IsWeaklyAssociatedPoint.nontrivial {F : X.Modules} {x : X}
    (h : IsWeaklyAssociatedPoint F x) :
    Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := by
  obtain ⟨m, hm⟩ := isWeaklyAssociatedPoint_iff_exists_radical_annihilator_eq.mp h
  refine ⟨m, 0, fun hm0 => ?_⟩
  refine (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top ?_
  rw [← hm, hm0, Submodule.span_zero_singleton, Submodule.annihilator_bot, Ideal.radical_top]

variable {S : Scheme.{u}}

/-- **Stacks Project, Tag 05AT.** The *relative assassin* `Ass_{X/S}(F)` of an `𝒪_X`-module
along `f : X ⟶ S` is the union over the points of `S` of the images in `X` of the associated
points of the restriction of `F` to the scheme-theoretic fibre. -/
@[stacks 05AT]
noncomputable def relativeAssassin (f : X ⟶ S) (F : X.Modules) : Set X :=
  ⋃ s : S, f.fiberι s '' associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F)

/-- A point lies in the relative assassin exactly when it is the image of an associated point
of the restriction of the module to one of the fibres. -/
@[simp]
theorem mem_relativeAssassin (f : X ⟶ S) (F : X.Modules) (x : X) :
    x ∈ relativeAssassin f F ↔
      ∃ (s : S) (y : f.fiber s),
        y ∈ associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) ∧
          f.fiberι s y = x := by
  simp only [relativeAssassin, Set.mem_iUnion, Set.mem_image]

end Stacks.Divisors

end
