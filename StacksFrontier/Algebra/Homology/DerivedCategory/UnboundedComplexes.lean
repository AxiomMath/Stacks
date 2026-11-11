module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes.TruncLEResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes.TruncGEResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes.PCellularComplexes
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes.LeftDerivedFunctor

/-!
# Resolving all the truncations of an unbounded complex at once, compatibly

Let `A` be an abelian category and let `P` be a class of objects of `A`. This file treats an
arbitrary — in particular not bounded — cochain complex `K` of `A` by resolving all of its
canonical truncations simultaneously, in a way compatible with the transition maps between
them, in the two dual situations.

In the first, `P` contains a zero object, is closed under finite direct sums, and every object
of `A` is a quotient of an object satisfying `P` (for `P` the projective objects of a category
with enough projectives these are the standing assumptions of projective resolutions; for `P`
the free modules over a ring they hold as well). Then the resolutions of the truncations
`τ_{≤ n} K` provided by Stacks 05T7 can be chosen compatibly with the maps
`τ_{≤ n} K ⟶ τ_{≤ n + 1} K`: there is a commutative ladder

```text
  Q 0 ------> Q 1 ------> Q 2 ------> ⋯
   |           |           |
   v           v           v
 τ_{≤0}K --> τ_{≤1}K --> τ_{≤2}K --> ⋯
```

whose vertical arrows are degreewise epimorphic quasi-isomorphisms, whose complexes `Q n` are
bounded above with all terms satisfying `P`, and whose horizontal arrows are degreewise split
injections with cokernels satisfying `P` as well. The colimit of the top row is then a
resolution of `K` itself by a complex with terms satisfying `P`, which is how the result is
used (Stacks 0794).

In the second, dual, situation `P` contains a zero object, is closed under finite products, and
every object of `A` is a subobject of an object satisfying `P` (for `P` the injective objects of
a category with enough injectives these are the standing assumptions of injective resolutions).
Then the resolutions of the truncations `τ_{≥ -n} K` can be chosen compatibly with the canonical
maps `τ_{≥ -(n + 1)} K ⟶ τ_{≥ -n} K`: there is a commutative ladder

```text
  ⋯ --> τ_{≥-2}K --> τ_{≥-1}K --> τ_{≥0}K
            |            |           |
            v            v           v
  ⋯ -->    I 2   -->    I 1   -->   I 0
```

whose vertical arrows are degreewise monomorphic quasi-isomorphisms, whose complexes `I n` are
bounded below with all terms satisfying `P`, and whose horizontal arrows are degreewise split
surjections with kernels satisfying `P` as well. The limit of the bottom row is then a
K-injective complex representing `R lim τ_{≥ -n} K`, which is how the result is used
(Stacks 070M).

## Main results

* `CochainComplex.exists_sequence_quasiIso_truncLE`: the ladder over the truncations
  `τ_{≤ n} K`, with its three numbered conclusions (1), (2), (3) in this order, followed by the
  commutativity of the ladder.
* `CochainComplex.exists_sequence_quasiIso_truncGE`: the dual ladder under the truncations
  `τ_{≥ -n} K`, stated dually arrow for arrow.
* `CategoryTheory.Functor.isLeftDerivable_of_acyclic_mapHomologicalComplex`: **Stacks 0794**
  itself, `LF` is defined on all of `D(A)` in the sense of Tags 05S9/05SV.
* `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex`:
  under the same hypotheses, the pointwise left derived functor exists in Mathlib's sense.
* `CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex`: that
  left derived functor is *absolute*, which is what a derived adjunction requires of it.

## Implementation notes

The class `P ⊂ Ob(A)` is a `CategoryTheory.ObjectProperty A`, spelled as in Stacks 05T7, which
is the main input to the first proof: "contains `0`" is
`CategoryTheory.ObjectProperty.ContainsZero` (some zero object satisfies `P`, which is what a
proof uses and is weaker than `P 0` for a chosen zero object unless `P` is closed under
isomorphisms), "closed under finite direct sums", resp. "under finite products", is closure
under binary biproducts, `P X → P Y → P (X ⊞ Y)` (together with `ContainsZero`, the empty sum,
this gives all finite sums, which in an abelian category agree with the finite products), and
"every object is a quotient of", resp. "a subobject of", "an element of `P`" is the existence,
for each `X`, of an epimorphism onto `X` from, resp. a monomorphism from `X` into, an object
satisfying `P`.

No closure of `P` under isomorphisms is assumed, so the conclusions are phrased to be invariant
under replacing an object by an isomorphic one: the cokernel, resp. kernel, of clause (3)
appears as an object `C` with `P C` together with an isomorphism
`(Q (n + 1)).X i ≅ (Q n).X i ⊞ C` identifying `(g n).f i` with `biprod.inl`, resp. with
`biprod.fst`, rather than as `cokernel ((g n).f i)`, resp. `kernel ((g n).f i)`, which is only
defined up to isomorphism. In particular `(g n).f i` is a split monomorphism, resp. a split
epimorphism, and `C` is its cokernel, resp. its kernel — which is the form the application
takes, where the decompositions `I_{n + 1}^p = I_n^p ⊕ C^p` are what produces the product
complex.

The truncations are `CochainComplex.truncLE` and `CochainComplex.truncGE`. Mathlib has no
transition morphism `K.truncLE n ⟶ K.truncLE (n + 1)`, nor
`K.truncGE (-(n + 1)) ⟶ K.truncGE (-n)`, so the commutativity of each ladder is expressed by
the equality of the two composites into, resp. out of, `K` along the canonical
`CochainComplex.ιTruncLE`, resp. `CochainComplex.πTruncGE`; since `K.ιTruncLE (n + 1)` is a
monomorphism and `K.πTruncGE (-(n + 1))` an epimorphism, this says exactly that the square built
from the canonical transition morphism commutes. Each system is indexed by `n : ℕ` and given by
the objects and the transition maps, from which `CategoryTheory.Functor.ofSequence`, resp.
`CategoryTheory.Functor.ofOpSequence`, builds the functor `ℕ ⥤ CochainComplex A ℤ`, resp.
`ℕᵒᵖ ⥤ CochainComplex A ℤ`, whose colimit, resp. limit, is taken in applications; the source
starts each ladder at `n = 1`, and starting it at `n = 0` is the same statement re-indexed.
Finally, where the source asks only that `Q n` be bounded above and `I n` bounded below, the
statements record the sharp bounds the proofs give, `(Q n).IsStrictlyLE n` and
`(I n).IsStrictlyGE (-n)` — Mathlib's spellings of `(Q n).X i = 0` for `i > n` and
`(I n).X i = 0` for `i < -n`.

The first proof is an induction. Given `f : Q n ⟶ τ_{≤ n} K`, let `h : Q n ⟶ τ_{≤ n + 1} K` be
the transition map — available because `Q n` vanishes in degrees `> n + 1`, so that
`Q n ⟶ τ_{≤ n + 1} (Q n)` is invertible — and resolve its mapping cone by a degreewise
epimorphic quasi-isomorphism `u : R ⟶ C(h)` with `R` in `P` and vanishing in degrees `> n + 1`,
again by Stacks 05T7(1). The next rung is the extension of `Q n` by `R` twisted by the first
component of `u`: degreewise the biproduct `(Q n) ^ p ⊞ R ^ p`, with the differential of the
biproduct corrected by the cochain `ent`, so that the tautological sequence
`0 ⟶ Q n ⟶ glue h u ⟶ R ⟶ 0` is a degreewise split short exact sequence of complexes whose
triangle in `K(A)` is the triangle of `C(h)` pulled back along `u`. Where one would fit the
composition `R ⟶ C(h) ⟶ (Q n)[1]` into a distinguished triangle of `K(A)` and then invoke
Stacks 0G6C to realise that triangle by a termwise split short exact sequence of complexes, the
twisted extension `glue h u` is that sequence, written down: its connecting cocycle is the first
component of `u` (`homOfDegreewiseSplit_glueSC`), the square against the triangle of the cone
commutes up to the homotopy given by that same component (`glueHomotopy`), and the resulting
morphism of triangles has invertible outer legs, so its middle leg `glue h u ⟶ τ_{≤ n + 1} K` is
a quasi-isomorphism (`quasiIso_glueDesc`, read off in the derived category, where an isomorphism
of the images is exactly a quasi-isomorphism). The map `Q n ⟶ glue h u` is degreewise
`biprod.inl`, which makes conclusion (3) hold on the nose with cokernel `R ^ p`. The correction
of the vertical arrow in degrees `n` and `n + 1` by a complex `P ⟶ P`, which the source performs
in order to make it termwise surjective, is unnecessary here: the resolution `u` of the cone
supplied by Stacks 05T7(1) is itself termwise surjective, and `glue h u ⟶ τ_{≤ n + 1} K`
restricted to the summand `R ^ p` is `u ^ p` followed by the termwise split epimorphism
`C(h) ⟶ τ_{≤ n + 1} K` (`epi_glueDesc_f`).

The second result is deduced from the first, applied in `Aᵒᵖ` to the isomorphism closure of the
class `fun Y ↦ P Y.unop`. The dualisation is the composite of `HomologicalComplex.opEquivalence`
with the reindexing `n ↦ -n` turning a chain complex into a cochain complex, exactly as in the
proof of Stacks 05T6. It is reduced in two steps: the dualisation itself
(`exists_ladder_isoClosure`), and the passage from the isomorphism closure of `P` to `P` itself
(`exists_ladder_of_isoClosure`, which replaces each term of each complex of the ladder by an
isomorphic object satisfying `P`, using `replaceTerms`). The dualisation rests on
`exists_truncGE_iso`: the complex opposite to the truncation `τ_{≤ n}` of the opposite complex
is the truncation `τ_{≥ -n}`. That is proved from the universal properties of the canonical
morphisms `πTruncGE` and `ιTruncLE` (`descTruncGE` and `liftTruncLE`, which factor a morphism to
a complex which is strictly `≥ a`, resp. from a complex which is strictly `≤ a`, through the
truncation; both follow from the naturality of these morphisms together with the fact that they
are isomorphisms on a complex which is already strictly bounded), so that no comparison of
cycles and opcycles is needed: the two candidate morphisms are inverse to each other because
`πTruncGE` and the dual of `ιTruncLE` are epimorphisms. The class transported to `Aᵒᵖ` has to be
the isomorphism closure of `P.op`: the binary biproduct of `Aᵒᵖ` is only isomorphic to, and not
equal to, the opposite of the binary biproduct of `A` (`biprodUnopIso`), so `P.op` need not be
closed under biproducts on the nose when `P` is not closed under isomorphisms. That
`P.op.isoClosure` satisfies the three hypotheses is `containsZero_op_isoClosure`,
`biprod_op_isoClosure` and `exists_epi_op_isoClosure`; a monomorphism `X ⟶ Y` of `A` becomes the
epimorphism `Yᵒᵖ ⟶ Xᵒᵖ` of `Aᵒᵖ`, which is where the duality between "subobject of" and
"quotient of" enters.

## References

* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 070F](https://stacks.math.columbia.edu/tag/070F)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 0G6C](https://stacks.math.columbia.edu/tag/0G6C)
-/
