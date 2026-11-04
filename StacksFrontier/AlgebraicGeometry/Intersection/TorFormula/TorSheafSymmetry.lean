module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionProductCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity

/-!
# The symmetry of the Tor-formula intersection product

The `Tor` sheaves `Tor_p^{𝒪_X}(ℱ, 𝒢)` and `Tor_p^{𝒪_X}(𝒢, ℱ)` of two `𝒪_X`-modules are built
from a derived tensor product that fixes the second argument, so they are not compared here as
sheaves; but everything a cycle sees of them agrees: at every point their stalks have the same
length over the local ring. That is enough to make the alternating sum
`∑ₚ (-1)ᵖ [Tor_p^{𝒪_X}(ℱ, 𝒢)]_k` of Tag 0AZR symmetric in its two arguments, which is what lets
the dévissage in the proof of Tag 0B0W be run in the second variable as well as the first.

The symmetry comes from `Module.length_tor_comm`, the balancing of `Tor` for modules over a
commutative ring, read at each stalk through
`AlgebraicGeometry.TorFormula.length_stalk_torSheaf_eq_length_tor_stalk`.

## Main results

* `AlgebraicGeometry.TorFormula.length_stalk_torSheaf_comm` and
  `sheafMultiplicity_torSheaf_comm` — the stalks of `Tor_p(ℱ, 𝒢)` and `Tor_p(𝒢, ℱ)` at a point
  have the same length, hence the same multiplicity.
* `AlgebraicGeometry.TorFormula.supp_torSheaf_comm` — the two `Tor` sheaves have the same
  support, so the delta-dimension bounds that `Stacks.Chow.coherentSheafCycle` needs are the
  same condition for both.
* `AlgebraicGeometry.TorFormula.intersectionProductCycle_comm` — **the alternating sum of Tag
  0AZR is symmetric**: `∑ₚ (-1)ᵖ [Tor_p(ℱ, 𝒢)]_k = ∑ₚ (-1)ᵖ [Tor_p(𝒢, ℱ)]_k`.

## Implementation notes

A support is a set of points at which the stalk is nontrivial, and a module is trivial exactly
when its length is zero, so equal lengths at every point give equal supports. The two
delta-dimension bounds are then literally the same proposition, because
`Stacks.Chow.reducedSupport` depends on the sheaf only through the closed set its support is:
that is `reducedSupport_torSheaf_comm`.

## References

* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

variable {X : Scheme.{u}}

/-! ### The symmetry at a point -/

/-- **The stalks of the two `Tor` sheaves of a pair of modules have the same length.** This is
`Module.length_tor_comm`, the balancing of `Tor` over the local ring, read through the
identification of the stalk of a `Tor` sheaf with the `Tor` module of the stalks. -/
theorem length_stalk_torSheaf_comm (F G : X.Modules) (p : ℕ) (x : X) :
    Module.length (X.presheaf.stalk x) ((torSheaf X F G p).presheaf.stalk x) =
      Module.length (X.presheaf.stalk x) ((torSheaf X G F p).presheaf.stalk x) := by
  rw [length_stalk_torSheaf_eq_length_tor_stalk, length_stalk_torSheaf_eq_length_tor_stalk]
  exact Module.length_tor_comm _ _ p

/-- **The two `Tor` sheaves of a pair of modules have the same multiplicity at every point.** -/
theorem sheafMultiplicity_torSheaf_comm (F G : X.Modules) (p : ℕ) (x : X) :
    Stacks.Chow.sheafMultiplicity (torSheaf X F G p) x =
      Stacks.Chow.sheafMultiplicity (torSheaf X G F p) x :=
  congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (length_stalk_torSheaf_comm F G p x)

/-- **The two `Tor` sheaves of a pair of modules have the same support**: a stalk is nontrivial
exactly when its length is nonzero, and the two lengths agree. -/
theorem supp_torSheaf_comm (F G : X.Modules) (p : ℕ) :
    SheafOfModules.supp (torSheaf X F G p) = SheafOfModules.supp (torSheaf X G F p) := by
  refine Set.ext fun x => ?_
  have key (A : X.Modules) : x ∈ SheafOfModules.supp A ↔
      Module.length (X.presheaf.stalk x) (A.presheaf.stalk x) ≠ 0 := by
    refine (SheafOfModules.mem_supp_iff_nontrivial_stalk A x).trans ?_
    rw [← not_subsingleton_iff_nontrivial, Ne, Module.length_eq_zero_iff]
    exact Iff.rfl
  rw [key, key, length_stalk_torSheaf_comm F G p x]

/-- **The reduced supports of the two `Tor` sheaves of a pair of modules agree.** The reduced
support of a coherent sheaf is the vanishing ideal of the closed set its support is, and the two
supports are the same set. -/
theorem reducedSupport_torSheaf_comm (F G : X.Modules) (p : ℕ)
    [(torSheaf X F G p).IsCoherent] [(torSheaf X G F p).IsCoherent] :
    Stacks.Chow.reducedSupport (torSheaf X F G p) =
      Stacks.Chow.reducedSupport (torSheaf X G F p) := by
  unfold Stacks.Chow.reducedSupport
  exact congrArg Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.ext (supp_torSheaf_comm F G p))

/-! ### The symmetry of the alternating sum -/

/-- **The alternating sum of Tag 0AZR is symmetric in its two arguments.** For coherent
`𝒪_X`-modules `ℱ` and `𝒢` on a regular scheme,

`∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_k = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(𝒢, ℱ)]_k`.

The two `Tor` sheaves have the same support and the same multiplicity at every point, so each
summand is the same cycle; no isomorphism of `Tor` sheaves is used. -/
theorem intersectionProductCycle_comm (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (hGk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX G F hG hF i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X G F i)).subschemeι ≫ f) ≤ WithBotTop.coe k) :
    intersectionProductCycle C f hX F G hF hG k hFk =
      intersectionProductCycle C f hX G F hG hF k hGk := by
  classical
  refine finsum_congr fun i => ?_
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
  have := isCoherent_torSheaf_of_isRegular X hX G F hG hF i
  have hcyc : Stacks.Chow.coherentSheafCycle C f (torSheaf X F G i) k (hFk i) =
      Stacks.Chow.coherentSheafCycle C f (torSheaf X G F i) k (hGk i) := by
    apply Function.locallyFinsuppWithin.ext
    intro x
    change Stacks.Chow.sheafCycleCoeff C f (torSheaf X F G i) k x =
      Stacks.Chow.sheafCycleCoeff C f (torSheaf X G F i) k x
    simp only [Stacks.Chow.sheafCycleCoeff, supp_torSheaf_comm F G i,
      sheafMultiplicity_torSheaf_comm F G i x]
  rw [hcyc]

end AlgebraicGeometry.TorFormula

end
