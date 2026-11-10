module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.RingTheory.LocalRing.PuncturedSpectrumArtinian

/-!
# Shrinking an affine chart until an invertible module on its punctured part is free

Let `V` be an affine open of a scheme `X`, let `x` be a point of `V` whose local ring is
Noetherian of Krull dimension at most one, and let `f ∈ Γ(X, V)` vanish at `x`. The basic open
`X.basicOpen f` is then the part of `V` away from the zero locus of `f`, which in the situation
of [Stacks, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA) is `V ⊓ U` for the retrocompact
open `U` of the tag.

This file records, in scheme-theoretic form, that an invertible module over the sections of
`X.basicOpen f` becomes free after shrinking `V` to a smaller basic open neighbourhood of `x`.
That is the commutative-algebra input to clause (2) of Tag 09NA: an invertible module on `U`
becomes trivial near each point of the complement, which is what lets it be glued to the
structure sheaf there.

The content is `Stacks.PuncturedSpectrum.exists_notMem_free_of_isLocalizedModule`; what happens
here is the translation of its hypotheses, through Mathlib's dictionary for an affine open:
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` presents the local ring at `x` as the
localization of `Γ(X, V)` at `AlgebraicGeometry.IsAffineOpen.primeIdealOf x`, and
`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` presents the sections over a basic
open as the localization away from the function.

## Main results

* `AlgebraicGeometry.IsAffineOpen.notMem_primeIdealOf_iff_mem_basicOpen`: a function lies outside
  the prime of a point exactly when the point lies in its nonvanishing locus.
* `AlgebraicGeometry.IsAffineOpen.exists_mem_basicOpen_free_of_krullDimLE_one`: the shrinking
  statement.

## Implementation notes

The conclusion is stated for an arbitrary model `B` of the localization of `Γ(X, X.basicOpen f)`
away from the restriction of `g`, rather than for `Localization.Away`, because that is how a
scheme presents it: by `AlgebraicGeometry.Scheme.basicOpen_res` the restriction of `g` has
`X.basicOpen f ⊓ X.basicOpen g` as its nonvanishing locus inside `X.basicOpen f`, and
`isLocalization_basicOpen` makes the sections there such a model. No comparison isomorphism is
therefore needed at the point of use.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- A section of an affine open lies outside the prime ideal of a point exactly when the point
lies in the nonvanishing locus of the section: the prime of the point is its image under the
isomorphism with the spectrum, which carries the basic open of the spectrum to the nonvanishing
locus. -/
theorem notMem_primeIdealOf_iff_mem_basicOpen (x : V) (r : Γ(X, V)) :
    r ∉ (hV.primeIdealOf x).asIdeal ↔ (x : X) ∈ X.basicOpen r := by
  change hV.primeIdealOf x ∈ PrimeSpectrum.basicOpen r ↔ _
  rw [← hV.fromSpec_preimage_basicOpen]
  change hV.fromSpec (hV.primeIdealOf x) ∈ X.basicOpen r ↔ _
  rw [hV.fromSpec_primeIdealOf]

include hV in
/-- **Shrinking an affine chart to make an invertible module free.** Let `x` be a point of an
affine open `V` of a scheme whose local ring is Noetherian of Krull dimension at most one, and
let `f ∈ Γ(X, V)` vanish at `x`. Then every invertible module over `Γ(X, X.basicOpen f)` is free
over the sections of a smaller basic open: there is `g ∈ Γ(X, V)` nonvanishing at `x` such that
the module becomes free after inverting the restriction of `g`, whose nonvanishing locus inside
`X.basicOpen f` is `X.basicOpen f ⊓ X.basicOpen g`. -/
theorem exists_mem_basicOpen_free_of_krullDimLE_one (x : V)
    [IsNoetherianRing (X.presheaf.stalk (x : X))] [Ring.KrullDimLE 1 (X.presheaf.stalk (x : X))]
    (f : Γ(X, V)) (hf : (x : X) ∉ X.basicOpen f)
    (M : Type u) [AddCommGroup M] [Module Γ(X, X.basicOpen f) M]
    [Module.Invertible Γ(X, X.basicOpen f) M] :
    ∃ g : Γ(X, V), (x : X) ∈ X.basicOpen g ∧
      ∀ (B Mg : Type u) [CommRing B] [Algebra Γ(X, X.basicOpen f) B]
        [IsLocalization.Away (algebraMap Γ(X, V) Γ(X, X.basicOpen f) g) B]
        [AddCommGroup Mg] [Module Γ(X, X.basicOpen f) Mg] [Module B Mg]
        [IsScalarTower Γ(X, X.basicOpen f) B Mg]
        (l : M →ₗ[Γ(X, X.basicOpen f)] Mg)
        [IsLocalizedModule
          (Submonoid.powers (algebraMap Γ(X, V) Γ(X, X.basicOpen f) g)) l],
        Module.Free B Mg := by
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  have : IsLocalization.AtPrime (X.presheaf.stalk (x : X)) (hV.primeIdealOf x).asIdeal :=
    hV.isLocalization_stalk x
  have hfp : f ∈ (hV.primeIdealOf x).asIdeal := by
    by_contra h
    exact hf ((hV.notMem_primeIdealOf_iff_mem_basicOpen x f).mp h)
  obtain ⟨g, hg, hfree⟩ :=
    Stacks.PuncturedSpectrum.exists_notMem_free_of_isLocalizedModule
      Γ(X, V) (hV.primeIdealOf x).asIdeal hfp (X.presheaf.stalk (x : X))
      Γ(X, X.basicOpen f) M
  exact ⟨g, (hV.notMem_primeIdealOf_iff_mem_basicOpen x g).mp hg, hfree⟩

end AlgebraicGeometry.IsAffineOpen

end
