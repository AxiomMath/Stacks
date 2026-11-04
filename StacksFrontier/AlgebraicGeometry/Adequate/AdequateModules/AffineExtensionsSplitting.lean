module

public import StacksFrontier.Algebra.Module.Adequate.Splitting06V7Domain
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.AdjoinRootSize
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFiniteFreeLift
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineExtensions

/-!
# Tag 06V7 over the algebras of a site, and adequacy under extensions

`AdequateFunctor.LaurentDomain.exists_retraction_of_shortExact` is [Stacks, Tag 06V7] on a
domain of algebras cut out by a property, given four inputs: the domain has a base object, and
it is closed under symmetric algebras of finitely generated modules, under Laurent polynomial
algebras, and under root extensions. This file discharges all four for the domain that matters
geometrically — the algebras whose spectra have size below a cutoff — and so states
[Stacks, Tag 06V7] over the algebras of a site.

That was the one open input of `AdequateFunctor.isAdequate_of_shortExact_site`, so
[Stacks, Tag 06V8] over the algebras of a site follows unconditionally, and with it
`Stacks.Adequate.AffineAdequateExtensions`.

## Main results

* `AdequateFunctor.linearlyAdequateSplitting_site` — [Stacks, Tag 06V7] over the algebras of a
  site, in the form `AdequateFunctor.LinearlyAdequateSplitting` that
  `AdequateFunctor.isAdequate_of_shortExact_on` consumes.
* `AdequateFunctor.isAdequate_of_shortExact_site_unconditional` — [Stacks, Tag 06V8] over the
  algebras of a site, with no remaining hypothesis beyond the cutoff's being an uncountable
  strong prelimit and the base ring's spectrum being an object of the site.
* `Stacks.Adequate.affineAdequateExtensions` — `Stacks.Adequate.AffineAdequateExtensions`
  holds: adequacy of module-valued functors on the algebras of the site over an affine scheme
  of the site is closed under extensions.

## Implementation notes

The three closure properties are the two unconditional clauses of [Stacks, Tag 000R] (9) that
the library carries, applied three times.

* The symmetric algebra on a finitely generated module is of finite type, so this is clause
  (9)(b): `AdequateFunctor.size_lt_of_spec_symmetricAlgebra`.
* The Laurent polynomial algebra `R[T, T⁻¹]` is the localization of `R[X]` at the powers of
  `X`, so it is clause (9)(b) followed by clause (9)(c):
  `AdequateFunctor.size_lt_of_spec_laurentPolynomial`.
* `AdjoinRoot p` is `R[X] / (p)`, generated over `R` by the root alone, so it is clause (9)(b)
  again: `AdequateFunctor.size_lt_of_spec_adjoinRoot`. No monicity is needed, and none is
  available at the point of use anyway, since the hypothesis quantifies over all polynomials.

Membership in the site's domain, `AdequateFunctor.algebraInSite`, is a condition on the
spectrum of the *underlying ring*, so the root-extension closure is insensitive to which
`Algebra A (AdjoinRoot p)` instance the statement carries — which is what lets the explicitly
restricted-scalars instance that [Stacks, Tag 06V5] produces be matched.

The base object is the base ring itself, `AdequateFunctor.BaseAlgebraObject.siteOfSpecMem`,
which is an algebra of the site exactly when its spectrum is an object of the site.

No `@[stacks]` attribute is placed here: the tagged statement of 06V7 is
`AdequateFunctor.exists_retraction_of_shortExact` and that of 06V8 is
`AdequateFunctor.isAdequate_of_shortExact`, both over all commutative algebras, and these are
those statements transported to the algebras of a site. This is the same convention as
`AdequateFunctor.exists_lift_from_finite_free_kernel_site` for 06V0.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 06V5](https://stacks.math.columbia.edu/tag/06V5)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06V8](https://stacks.math.columbia.edu/tag/06V8)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u m

namespace AdequateFunctor

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)

include hκ hsl in
/-- **Stacks Lemma 06V7 over the algebras of a site.** An extension of a linearly adequate
module-valued functor by an adequate one, on the algebras whose spectra have size below the
cutoff, admits a retraction onto its kernel term.

The four inputs of `AdequateFunctor.LaurentDomain.exists_retraction_of_shortExact` are
discharged by the three size bounds of [Stacks, Tag 000R] (9) together with
`AdequateFunctor.BaseAlgebraObject.siteOfSpecMem`. -/
public theorem linearlyAdequateSplitting_site (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ) :
    LinearlyAdequateSplitting.{w, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) :=
  LaurentDomain.exists_retraction_of_shortExact.{w, u, u}
    (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA)
    (fun V _ _ _ => size_lt_of_spec_symmetricAlgebra hκ hsl A hA V)
    (fun R _ _ hR => size_lt_of_spec_laurentPolynomial hκ hsl R hR)
    (fun R _ _ hR q => size_lt_of_spec_adjoinRoot hκ hsl R q hR)

include hκ hsl in
/-- **Stacks Lemma 06V8 over the algebras of a site.** The middle term of a short exact sequence
of module-valued functors on the algebras whose spectra have size below the cutoff, whose outer
terms are adequate, is adequate.

This is `AdequateFunctor.isAdequate_of_shortExact_site` with its splitting hypothesis
discharged by `AdequateFunctor.linearlyAdequateSplitting_site`. -/
public theorem isAdequate_of_shortExact_site_unconditional (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    (T : ShortComplex (ModuleValuedFunctorOn.{max u w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))))
    (hT : T.ShortExact)
    (h₁ : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) T.X₁)
    (h₃ : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) T.X₃) :
    IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) T.X₂ :=
  isAdequate_of_shortExact_site.{w} hκ hsl A hA
    (linearlyAdequateSplitting_site.{w} hκ hsl A hA) T hT h₁ h₃

end AdequateFunctor

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- `Stacks.Adequate.AffineAdequateExtensions` holds: adequacy of module-valued functors on the
algebras of the site over an affine scheme of the site is closed under extensions. This is
[Stacks, Tag 06V8] on the site's domain of algebras.

It is `Stacks.Adequate.affineAdequateExtensions_of_linearlyAdequateSplitting`, whose one
hypothesis — [Stacks, Tag 06V7] on the algebras of the site — is
`AdequateFunctor.linearlyAdequateSplitting_site`. The two unconditional inputs are the same as
those of `Stacks.Adequate.affineAdequateKernels` and
`Stacks.Adequate.affineAdequateCokernels`: the base ring as an object of the site and the
lifting property of [Stacks, Tag 06V0] there, carried by the two unconditional clauses of
[Stacks, Tag 000R] (9) together with the cutoff's being an uncountable strong prelimit. -/
public theorem affineAdequateExtensions : AffineAdequateExtensions.{u, m} B :=
  affineAdequateExtensions_of_linearlyAdequateSplitting B fun A hA =>
    AdequateFunctor.linearlyAdequateSplitting_site.{m}
      (lt_of_le_of_lt (Scheme.aleph0_le_size (Spec A)) hA)
      B.cutoff_isStrongPrelimit A hA

end Stacks.Adequate

end
