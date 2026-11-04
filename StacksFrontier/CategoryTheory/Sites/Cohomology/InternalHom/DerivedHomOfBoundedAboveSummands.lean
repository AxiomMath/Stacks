module

public import Mathlib.Data.Int.Interval
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.BoundedAboveHomComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a bounded above complex of finite free summands

Let `(C, O)` be a ringed site, let `E` be a complex of `O`-modules which vanishes in all
sufficiently large degrees and all of whose terms are isomorphic to direct summands of finite
free `O`-modules, and let `F` be a complex of `O`-modules which vanishes in all sufficiently
small degrees. **Stacks 08JI** asserts that the derived internal Hom `RSheafHom(E, F)` is
represented by the complex `H` with

  `H^n = ⨁_{n = p + q} SheafHom_O(E^{-q}, F^p)`

and the internal Hom differential.

That complex is the internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z: its degree-`n` term is
the *product*, over `q : ℤ`, of the internal Hom sheaves `SheafHom(E^{-q}, F^{n-q})`, and here
only finitely many of those factors are nonzero, because the factor at `q` vanishes as soon as
`E^{-q}` does — which happens for `q` small — or `F^{n-q}` does — which happens for `q` large.
So the product is a finite direct sum, as the source writes it. Note that neither bound alone
suffices: the two hypotheses of Stacks 08JI cut the index range down from both sides.

## Main definitions

* `AlgebraicGeometry.RingedSite.boundedAboveHomRepresentation`: **Stacks 08JI** entire, in one
  statement: `RSheafHom(E, F)` is represented by the internal Hom complex `SheafHom(E, F)`, and
  the degree-`n` term of that complex is `⨁_{n = p + q} SheafHom(E^{-q}, F^p)`.
* `AlgebraicGeometry.RingedSite.boundedAboveHomDegreeIso`: the second component on its own, the
  degreewise direct-sum description of the internal Hom complex.

## Main results

The first component is not proved here. It is
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_boundedAbove`, already in
the library under Stacks 08I5 with exactly the hypotheses of Stacks 08JI, and
`boundedAboveHomRepresentation` is assembled from it rather than restating it, so that the two
tags share the one theorem instead of each carrying a copy.

## Implementation notes

**The differential.** The degree-`n` term is described here as a coproduct of internal Hom
sheaves, and no separate description of the differential is given, because none is needed: the
complex is `AlgebraicGeometry.RingedSite.sheafHomComplex` (Stacks 0A8X), whose defining data
include an isomorphism of complexes from its sections on each slice site onto
`CochainComplex.HomComplex`. Its differential is therefore the standard Hom-complex one,
`d(f) = d_F ∘ f - (-1)^n f ∘ d_E` on a degree-`n` cochain, which is the convention of
Section 21.35 that Stacks 08JI refers to.

**Relation to Stacks 08JH and 08I5.** Stacks 08JH is the same statement with `E` strictly
perfect, hence bounded in both directions, and its degreewise direct-sum description
`AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso` uses only the boundedness of `E`; it
does not apply here, where `E` is bounded above only. The representation statement, on the other
hand, is already available: `strictlyPerfectHomComparison_isIso_of_boundedAbove` is the ringed
site form of the ringed space lemma Stacks 08I5, and it has exactly the hypotheses of Stacks
08JI, so this file does not restate it; `boundedAboveHomRepresentation` applies it. Its `IsIso`
of the canonical comparison `strictlyPerfectHomComparison` is what "is represented by" means
here, and keeping the one theorem under both tags avoids a second copy of it.

**Why a `PSigma`.** The two assertions of the source are a proposition and a construction, so
the combined statement cannot be a conjunction; `Σ' _ : …, …` is the non-dependent pair of a
`Prop` with data. Making the second component a `Nonempty` instead would turn the construction
into an existence claim and is not what the source says.

**Why `IsFiniteFreeSummand`.** The predicate `IsStrictlyPerfect` carrying the Stacks 08FL tag is
universe-monomorphic and cannot be mentioned at the universes where the internal Hom complex
lives; `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` is the condition "isomorphic to a
direct summand of a finite free `O`-module" stated universe-polymorphically.

**The derived internal Hom datum.** The statements are taken over an arbitrary
`AlgebraicGeometry.RingedSite.DerivedInternalHom X` rather than over the chosen
`canonicalDerivedInternalHom X`, which is opaque; instantiating at the canonical datum recovers
the form Stacks 08JI states.

## References

* [Stacks Project, Tag 08JI](https://stacks.math.columbia.edu/tag/08JI)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The degreewise direct-sum half of **Stacks 08JI**. If `F` vanishes below `a` and `E`
vanishes above `b`, then the degree-`n` term of the internal Hom complex `SheafHom(E, F)` of
Stacks 0A8Z is the direct sum, over `q : ℤ`, of the internal Hom sheaves
`SheafHom(E^{-q}, F^{n-q})`, which is the complex `H^n = ⨁_{n = p + q} SheafHom(E^{-q}, F^p)` of
the source.

By `homDegreeIsLimit` the term is the *product* of those sheaves, with no hypothesis at all. The
factor at `q` vanishes once `q < -b`, where `E^{-q}` is zero, and once `n - a < q`, where
`F^{n-q}` is zero, so the support of the family is contained in `Icc (-b) (n - a)` and
`productCoproductIsoOfFiniteSupport` identifies the product with the coproduct. The differential
needs no separate description; see the implementation notes. The tag itself is carried by
`boundedAboveHomRepresentation`, which pairs this with the representation statement. -/
def boundedAboveHomDegreeIso (a b : ℤ)
    (hF : ∀ i : ℤ, i < a → IsZero (F.X i)) (hE : ∀ i : ℤ, b < i → IsZero (E.X i)) (n : ℤ) :
    (sheafHomComplex X E F).obj.X n ≅
      ∐ (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) := by
  classical
  have hsupp : ∀ q : ℤ, q ∉ Finset.Icc (-b) (n - a) →
      IsZero (internalHomSheaf X (E.X (-q)) (F.X (n - q))) := by
    intro q hq
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
    rcases hq with h | h
    · exact internalHomSheaf_isZero_of_isZero X (hE (-q) (by omega))
    · exact internalHomSheaf_isZero_of_isZero_target X (hF (n - q) (by omega))
  exact ((homDegreeIsLimit X E F n).conePointUniqueUpToIso
      (limit.isLimit (Discrete.functor
        (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q)))))).trans
    (productCoproductIsoOfFiniteSupport
      (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) _ hsupp)

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Stacks 08JI**, the whole statement. Let `E` be a complex of `O`-modules vanishing above
`b` all of whose terms are direct summands of finite free `O`-modules, and let `F` be a complex
of `O`-modules vanishing below `a`. Then the derived internal Hom `RSheafHom(E, F)` is
represented by the internal Hom complex `H = SheafHom(E, F)` of Stacks 0A8Z — the comparison
being the canonical `strictlyPerfectHomComparison` — and that complex has
`H^n = ⨁_{n = p + q} SheafHom(E^{-q}, F^p)` in every degree.

The two components are exactly the two assertions of the source, and neither is restated here:
the first is `strictlyPerfectHomComparison_isIso_of_boundedAbove`, the library's Stacks 08I5, at
exactly the hypotheses of Stacks 08JI; the second is `boundedAboveHomDegreeIso`. The differential
needs no separate component; see the implementation notes. -/
@[stacks 08JI "derived internal Hom represented by the Hom complex, with finite direct-sum terms"]
def boundedAboveHomRepresentation (D : DerivedInternalHom.{u, d} X) (a b : ℤ)
    (hF : ∀ i : ℤ, i < a → IsZero (F.X i)) (hE : ∀ i : ℤ, b < i → IsZero (E.X i))
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (E.X i)) :
    Σ' _ : IsIso (strictlyPerfectHomComparison X D E F),
      ∀ n : ℤ, (sheafHomComplex X E F).obj.X n ≅
        ∐ (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) :=
  ⟨strictlyPerfectHomComparison_isIso_of_boundedAbove X E F D a hF ⟨b, hE⟩ hterm,
    boundedAboveHomDegreeIso X E F a b hF hE⟩

end AlgebraicGeometry.RingedSite

end
