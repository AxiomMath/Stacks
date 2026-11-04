module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.InducedFiltration
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.PageComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.StablePage
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.Convergence

/-!
# Spectral sequences: filtered complexes

Let `𝒜` be an abelian category and let `(K^•, F)` be a filtered complex of `𝒜`, that is, a cochain
complex `K^•` together with a decreasing filtration of it by subcomplexes `F^p K^•`. Write
`n = p + q`. The spectral sequence of `(K^•, F)` ([Stacks, Tag 012M]) has, inside its zeroth page
`E_0^{p, q} = gr^p K^n`, the cycles and boundaries
```
Z_r^{p, q} = (F^p K^n ∩ (d^n)⁻¹(F^{p + r} K^{n + 1}) + F^{p + 1} K^n)/F^{p + 1} K^n,
B_r^{p, q} = (F^p K^n ∩ d^{n - 1}(F^{p - r + 1} K^{n - 1}) + F^{p + 1} K^n)/F^{p + 1} K^n
```
of the filtration of [Stacks, Tag 011O]. This file develops the limit of that spectral sequence and
its relation to the cohomology of `K^•`, which carries the induced filtration
`F^p H^n(K^•) = Im(H^n(F^p K^•) ⟶ H^n(K^•))` of [Stacks, Tag 012P].

If the stable cycles `Z_∞^{p, q} = ⋂_r Z_r^{p, q}` and the stable boundaries
`B_∞^{p, q} = ⋃_r B_r^{p, q}` exist, then so does the limit
`E_∞^{p, q} = Z_∞^{p, q}/B_∞^{p, q}`, and the graded piece `gr^p H^n(K^•)` is a *subquotient* of
`E_∞^{p, n - p}`, cut out by the cycles of `K^•` lying in `F^p K^n`: those cycles land in
`Z_∞^{p, q}`, hence generate a subobject `S` of `E_∞^{p, q}`, and their classes exhaust
`F^p H^n(K^•)`, so `S` maps onto `gr^p H^n(K^•)`. That subquotient is all of `E_∞^{p, q}` — the
spectral sequence *weakly converges* to `H^*(K^•)` — exactly when the two inclusions
```
Ker(d^n) ∩ F^p K^n + F^{p + 1} K^n ⊆ Z_∞^{p, q}        (012S)
B_∞^{p, q} ⊆ Im(d^{n - 1}) ∩ F^p K^n + F^{p + 1} K^n   (012T)
```
produced along the way are equalities; both can be strict, so the subquotient is the whole of what
holds in general. The two further conditions defining *abutment* ([Stacks, Tag 012U]),
`⋂_p F^p H^n(K^•) = 0` and `⋃_p F^p H^n(K^•) = H^n(K^•)`, hold exactly when
```
⋂_p (Ker(d^n) ∩ F^p K^n + Im(d^{n - 1})) = Im(d^{n - 1}),
⋃_p (Ker(d^n) ∩ F^p K^n + Im(d^{n - 1})) = Ker(d^n)
```
inside `K^n`, by the description
`F^p H^n(K^•) = (Ker(d^n) ∩ F^p K^n + Im(d^{n - 1}))/Im(d^{n - 1})` of the induced filtration
([Stacks, Tag 012R]).

Finally, when the filtration is finite in each degree all of this is unconditional: the spectral
sequence is bounded, the induced filtration on each `H^n(K^•)` is finite, the spectral sequence
converges to `H^*(K^•)`, and a weak Serre subcategory of `𝒜` containing one whole page contains
every `H^n(K^•)`.

## Main results

* `CochainComplex.exists_epi_gradedPiece_homology_of_isGLB_isLUB`: where the stable cycles and
  boundaries exist, `B_∞^{p, q} ≤ Z_∞^{p, q}`, so the limit `E_∞^{p, n - p}` exists, and
  `gr^p H^n(K^•)` is a subquotient of it, by a subobject and an epimorphism which are pinned by
  the cycles of `K^•` lying in `F^p K^n`.
* `CochainComplex.exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff`: that
  subquotient is all of `E_∞^{p, n - p}` if and only if (012S) and (012T) are equalities; and the
  induced filtration on `H^n(K^•)` is separated, resp. exhaustive, if and only if the two
  displayed conditions in `K^n` hold.
* `CochainComplex.epi_comp_cokernel_π_ofLE_of_eq_sup` and
  `CochainComplex.iso_eq_of_comp_cokernel_π_eq_of_eq_sup`: where (012S) is an equality the cycles
  of `K^•` lying in `F^p K^n` *generate* `E_∞^{p, n - p}`, so the comparison of (012V) is unique.
* `CochainComplex.stableCyclesLift`, `CochainComplex.toImageHomologyMap`,
  `CochainComplex.stablePageImage`, `CochainComplex.stablePageImageToGradedPiece` and
  `CochainComplex.stablePageIsoGradedPiece`: the data of (012Q) and (012V) as `def`s, each with
  the equation characterising it and a statement that it is the only morphism satisfying that
  equation.
* `CochainComplex.isGLB_stableCycles_of_eventually_isZero` and
  `CochainComplex.isLUB_stableBoundaries_of_eventually_isIso`: construct the stable bounds from
  eventual control of the homology of filtration steps, including acyclic nonzero tails.
* `CochainComplex.firstPage_cycles_le_boundaries`: first-page vanishing from surjectivity and
  injectivity of the adjacent transition on homology in two consecutive degrees.
* `CochainComplex.isBounded_and_converges_of_isDegreewiseFinite`: for a degreewise finite
  filtration, boundedness, finiteness of the induced filtration, convergence, and the weak Serre
  subcategory clause.
* `CochainComplex.isBounded_and_converges_of_eventually_isZero_of_eventually_isIso`: if the
  cohomology of `F^pK^•` vanishes for `p ≫ 0` and agrees with that of `K^•` for `p ≪ 0`, degree by
  degree, then the spectral sequence is bounded, the induced filtration is finite, and the
  spectral sequence converges to `H^*(K^•)`.

## Implementation notes

*Filtered complexes.* As in [Stacks, Tag 05TW] and [Stacks, Tag 015W], a complex of filtered
objects is the same datum as a complex filtered by subcomplexes, so a filtered complex is
`CategoryTheory.FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ`, with `ℤᵒᵖ` recording that the
filtration decreases. Its degreewise subobjects `F^p K^n` are the family `F` of the statements,
pinned by `hF` to `Subobject.mk ((K.filtration.ι.app (op p)).f n)`; naming them is an
abbreviation, not a hypothesis, and the decrease of `F` and the compatibility
`d(F^p K^n) ≤ F^p K^{n + 1}` are part of the filtration, so they are not assumed separately.

*Subobjects of `K^n` rather than of `gr^p K^n`.* The source's `Z_r^{p, q}` and `B_r^{p, q}` are
subobjects of `E_0^{p, q} = gr^p K^n = K^n/F^{p + 1}K^n`; they are presented here by their
numerators in `K^n`, displayed above, which contain `F^{p + 1}K^n`. A quotient of two such
subobjects is the quotient of their images in `gr^p K^n`, so `E_∞^{p, q}` is computed by the same
cokernel either way and no quotient object has to be formed. Keeping the summand `F^{p + 1} K^n`
inside the intersection and the union is not cosmetic: `⋂_r (Z_r + F^{p + 1}K^n)` is in general
strictly larger than `(⋂_r Z_r) + F^{p + 1}K^n`, and it is the former that is `Z_∞^{p, q}`.

*Bounds as `IsGLB`/`IsLUB`.* "The stable cycles and boundaries exist" is `IsGLB` and `IsLUB` for
the two families, which is exactly existence of the intersection and of the union; no completeness
of `Subobject (K^n)`, and no well-poweredness of `𝒜`, is assumed anywhere, and the same holds for
`⋂_p F^p H^n(K^•) = 0` and `⋃_p F^p H^n(K^•) = H^n(K^•)`. Both families are indexed by `r : ℕ`,
monotonically: the source's `r ≥ 1` for `B_r` and `r ≥ 0` for `Z_r` are cofinal in `ℕ`, so the
bounds are the source's.

*Existence statements and data.* (012Q) and (012V) are stated as existence statements, because
that is how the source states them: a subquotient of `E_∞^{p, q}`, a subobject `S` and two
epimorphisms, and an isomorphism compatible with the maps out of `A = Ker(d^n) ∩ F^pK^n`.  All of
them are in fact *unique*.  `a` and `b` are pinned by the monomorphisms `Z_∞^{p, q} ⟶ K^n` and
`F^pH^n(K^•) ⟶ H^n(K^•)`; `S` is an image and `g` the canonical map onto it; and `e` is unique
because `A ⟶ S` is an epimorphism, which is all of `E_∞^{p, q}` exactly where (012S) is an
equality.  So each existence statement is accompanied by a `def` and the equation characterising
it, and the `∃`-forms are kept for the consumers that use them.  The distinction matters for
*naturality*: two isomorphisms chosen at two objects of a category are related by nothing,
whereas two morphisms each uniquely determined by an equation are related by the naturality of
the equations.

*Weak convergence and abutment appear through their content, not through a predicate.* Weak
convergence is a condition on all bidegrees at once and abutment adds a condition on each degree,
so the source's biconditionals are the conjunction over `p` and `n` of the ones stated here. There
is in general no morphism between `gr^p H^n(K^•)` and `E_∞^{p, n - p}` in either direction; both
receive canonical maps from `A = Ker(d^n) ∩ F^p K^n`, and "`gr^p H^n(K^•) = E_∞^{p, n - p}`" says
that the unique morphism relating them over `A` is an isomorphism. The project's
`WeaklyConvergesTo` and `AbutsTo` are phrased for filtered differential objects with an abstract
comparison map supplied as data, so they are not used.

*The graded piece of cohomology.* `gr^p H^n(K^•)` is the cokernel of
`F^{p + 1}H^n(K^•) → F^p H^n(K^•)`, written as `Limits.image.preComp` of the two homology maps of
the factorisation `F^{p + 1}K^• → F^p K^• → K^•`: that is a monomorphism between the two images
with no side condition to discharge, and its source is `F^{p + 1}H^n(K^•)` because the composite
is `H^n(F^{p + 1}K^•) → H^n(K^•)`.

*The spectral sequence is a hypothesis of the last result, not a conclusion.* Its existence is
[Stacks, Tag 012M]: `E` is carried as data together with the identification of its page at
`(r, p, q)` with `Z_r^{p, q}/D_r^{p, q}` that 012M provides. Boundedness ([Stacks, Tag 0BDU]) is
stated on the `E_0`-page, which is where that definition puts it; regularity is stated literally,
as vanishing of the differentials for `r ≫ 0`. Finiteness of the induced filtration is
`∃ a ≤ b, F^a = ⊤ ∧ F^b = ⊥` on the subobjects `F^p H^n(K^•)` rather than through
`Filtration.IsFinite`, which asks for a diagram over `ℤᵒᵖ` together with its monomorphisms into
the ambient object: the induced filtration arises as a family of subobjects, and turning a family
into a diagram needs its antitonicity as an input.

## References

* [Stacks Project, Tag 012Q](https://stacks.math.columbia.edu/tag/012Q)
* [Stacks Project, Tag 012V](https://stacks.math.columbia.edu/tag/012V)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 0BK5](https://stacks.math.columbia.edu/tag/0BK5)
* [Stacks Project, Tag 011O](https://stacks.math.columbia.edu/tag/011O)
* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 012R](https://stacks.math.columbia.edu/tag/012R)
* [Stacks Project, Tag 012U](https://stacks.math.columbia.edu/tag/012U)
* [Stacks Project, Tag 0BDU](https://stacks.math.columbia.edu/tag/0BDU)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

