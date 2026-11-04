module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Basic
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Construction
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.SpectralSequence

/-!
# Cartan-Eilenberg resolutions

Let `C` be an abelian category with enough injectives. A *Cartan-Eilenberg resolution* of a
bounded below cochain complex `K` of `C` (`CochainComplex.CartanEilenbergResolution`,
[Stacks, Tag 015H]) is a double complex `I` of injective objects together with an augmentation
`ε : K ⟶ I^{•,0}` such that `I^{p,•}`, `Ker(d₁^{p,•})`, `Im(d₁^{p,•})` and `H^p_I(I^{•,•})` are
injective resolutions of `K^p`, `Ker(d_K^p)`, `Im(d_K^p)` and `H^p(K^•)` respectively. These
files prove that such resolutions exist, and compute with them the two spectral sequences of
the double complex `F(I)` obtained by applying an additive functor `F` to `I` termwise.

The development is split into:

* `StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Basic`: the definition of a
  Cartan-Eilenberg resolution, and the horseshoe lemma for a short exact sequence both of whose
  ends are resolved;
* `StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Construction`: gluing a complex out of
  its short exact sequences of cycles, boundaries and cohomology, and the assembly of a
  Cartan-Eilenberg resolution from the horseshoe property;
* `StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.SpectralSequence`: the existence of
  Cartan-Eilenberg resolutions (`CochainComplex.exists_cartanEilenbergResolution`) and the
  identification of the `'E₁`- and `''E₂`-pages and of the abutment of the two spectral
  sequences of `F(I)`
  (`CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus`).

## Implementation notes

A double complex is a cochain complex of cochain complexes, as in [Stacks, Tag 015H]: for
`L : HomologicalComplex₂ ℬ (up ℤ) (up ℤ)`, the object `L.X p` is the column `L^{p,•}`, so
`(L.X p).homology q` is `H^q(L^{p,•})`, i.e. `'E₁^{p,q}`; and `L.homology q` is
`H^q_I(L^{•,•})` as a complex in the second variable, so `(L.homology q).X p` is `''E₁^{p,q}`
and `(L.homology q).homology p` is `H^p_{II}(H^q_I(L^{•,•}))`, i.e. `''E₂^{p,q}`
([Stacks, Tag 0130] (3), (4) and (6)). `HomologicalComplex₂.total` is `Tot`, and
`HomologicalComplex₂.HasTotal` is the existence of the coproducts that define it; it holds as
soon as `ℬ` has countable coproducts.

The existence statement takes as an argument a degree `n` below which `K` vanishes, rather than
merely the hypothesis that `K` is bounded below, and records in its conclusion that the
resolution can be chosen supported in first degrees `≥ n` as well: this is what the induction
produces, it is what a user of the second spectral sequence of a Cartan-Eilenberg resolution
needs in order to bound its range, and it implies the bare existence statement. Condition (1)
of [Stacks, Tag 015H] is already a field of `CochainComplex.CartanEilenbergResolution`
(bounded belowness of `I` with an unspecified bound), so the extra conclusion sharpens that
bound to `n` rather than adding an independent requirement. A Cartan-Eilenberg resolution is
data, not a proposition, so the conclusion is an `∃` over that structure rather than a
`Nonempty` of a subtype; `Exists.choose` extracts a witness when one is wanted, as for
Mathlib's `CategoryTheory.HasInjectiveResolution`.

Neither the spectral sequence of a double complex nor the notions of an `E_∞`-page, of
boundedness, of convergence and of the induced filtration exist in Mathlib at the time of
writing, so the second result states what the pages and the abutment *are*, which is the
content specific to it; boundedness, convergence and finiteness of the two filtrations are
[Stacks, Tag 0132] applied to `F(I)`, a statement about an arbitrary double complex with
finitely many nonzero terms on each antidiagonal, whose hypothesis holds for `F(I)` by
conditions (1) and (2) of [Stacks, Tag 015H].

The identification of the `'E₁`-page is an isomorphism of *complexes* in the first variable,
not merely a family of isomorphisms of objects: it says that the `'E₁`-page in the row `q` is
the complex `p ↦ R^qF(K^p)` with the differential induced by `d_K`, which is what makes
`'E₂^{p,q} = H^p(R^qF(K^•))`. It is phrased as an isomorphism family together with the
naturality square rather than as an isomorphism of cochain complexes because assembling
`p ↦ R^qF(K^p)` into a complex needs `(R^qF).Additive`, which Mathlib does not yet provide for
`Functor.rightDerivedFunctorPlus`. The `''E₂`-page is identified for the cohomology of `F(I)`,
not for `F` applied to the cohomology of `I`: the two agree, and that they do is precisely the
splitting step (each differential of the row `I^{•,q}` is a split surjection onto a direct
summand, because its kernel, image and cohomology are injective, and this survives applying
`F`), so the stronger form is the one recorded.

`F` is assumed additive, where the source assumes it left exact: no part of the conclusion uses
left exactness. The pages are computed from injective resolutions and from the splitting of the
rows of `I`, and `RF` and `R^iF` are available for an additive functor out of a category with
enough injectives, as in [Stacks, Tag 015A] and [Stacks, Tag 015M].

## References

* [Stacks, Tag 015H]
* [Stacks, Tag 015I]
* [Stacks, Tag 015J]
* [Stacks, Tag 013T]
* [Stacks, Tag 0133]
-/
