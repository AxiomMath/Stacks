module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.StandardResolutionSquareFunctoriality
public import StacksFrontier.RingTheory.Cotangent.StandardResolution

/-!
# The cotangent complex of a product of algebras

Let `A → B` and `A → C` be ring maps. The two projections `B × C → B` and `B × C → C` are maps of
`A`-algebras, so the functoriality of the cotangent complex in a commutative square of ring maps
gives a canonical map of complexes of `B × C`-modules

`L_{B×C/A} → L_{B/A} ⊕ L_{C/A}`,

where the two summands are read as complexes of `B × C`-modules along the projections. This file
constructs that map. [Stacks, Tag 08SC] asserts that it is an isomorphism in `D(B × C)`; that is
`CommAlgCat.isIso_Q_map_cotangentComplexProductMap` of
`StacksFrontier/Cotangent/ProductDecompositionBase.lean`, and the implementation notes below set out
the route, which is the source's.

## Main definitions

* `CommAlgCat.productFstSquare` and `CommAlgCat.productSndSquare`: the two projections, read as
  commutative squares of ring maps with identical base `A`.
* `CommAlgCat.cotangentComplexProductMap`: **the canonical map of [Stacks, Tag 08SC]**, at chain
  level.

## Main results

* `Algebra.isPolynomialAlgebra_polynomial`: `A[x]` is a polynomial algebra over `A`, which is the
  hypothesis that the distinguished triangle of [Stacks, Tag 08SA] takes.
* `CommAlgCat.cotangentComplexProductMap_fst` and `CommAlgCat.cotangentComplexProductMap_snd`: the
  two components of the canonical map are the two functoriality maps. That the canonical map is a
  quasi-isomorphism as soon as those two components become invertible after one base change each
  is `CommAlgCat.quasiIso_cotangentComplexProductMap_of_components_counit` of
  `StacksFrontier/Cotangent/ProductDecompositionCriterion.lean`.

## Implementation notes

**The source's proof.** It factors `A → B × C` as
`A → A[x] → B × C` with `x ↦ (1, 0)`, takes the distinguished triangles of [Stacks, Tag 08SA]

`L_{A[x]/A} ⊗^𝐋_{A[x]} D → L_{D/A} → L_{D/A[x]} → (L_{A[x]/A} ⊗^𝐋_{A[x]} D)[1]`

for `D = B × C`, `D = B` and `D = C`, and compares the three. Comparing them is a map of
triangles: the first terms match because `B × C = B ⊕ C` as `A[x]`-modules, and the conclusion
that the middle terms agree is read off from the third terms agreeing, which is the lemma over the
base `A[x]`. That last step is where [Stacks, Tag 08QQ] enters: the map
`L_{B×C/A[x]} → L_{B/A[x]} ⊕ L_{C/A[x]}` becomes invertible after inverting `x`, which kills the
`C` factor, and after inverting `x - 1`, which kills the `B` factor.

**Tag 08QQ is available with its arrow pinned.** The step needs it as a statement about **the**
functoriality map, not merely as an isomorphism *of objects* of `D(B')`, and without Remark 08QI
as a hypothesis.
`CommAlgCat.isIso_Q_map_cotangentExtendScalarsComplexMap` of
`StacksFrontier/Cotangent/BaseChangeQuasiIso.lean` says that **the** functoriality map of
[Stacks, Tag 08PN] is invertible in `D(B')`, under the source's own two hypotheses and no others,
Remark 08QI being proved — `CommAlgCat.cotangentComputedByEveryResolution` of
`StacksFrontier/Cotangent/BaseChangeQuasiIso.lean`, read off at the standard resolution from
`CommAlgCat.quasiIso_alternatingFaceMapComplex_map_of_isResolution` of
`StacksFrontier/Cotangent/ResolutionIndependence.lean`, which carries `@[stacks 08QI]`. And
`CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso` of
`StacksFrontier/Cotangent/DerivedPushoutBaseChange.lean` carries `@[stacks 08QQ]`, with
`CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso_hom` identifying its underlying
morphism with the image of that chain-level map by `rfl`. So the arrow is pinned, and the step of
the source's proof that inverts `x` and `x - 1` has the input it needs.

**What blocks the lemma is one step further on**, and it is not a matter of bookkeeping either:
the object-level information the three triangles carry is strictly weaker than the lemma. Indeed
the first map of
each of the three triangles is *zero*. In `D(D)` the source `L_{A[x]/A} ⊗^𝐋_{A[x]} D` is the free
module `D` in degree `0`, so a map out of it into the nonpositively graded `L_{D/A}` is determined
by its effect on `H^0`, namely `dx ⊗ 1 ↦ d e` for `e` the image of `x` in `D`; and `d e = 0` in
all three cases, because `e` is `1` for `D = B`, is `0` for `D = C`, and is idempotent for
`D = B × C`, where `e² = e` gives `(1 - 2e) · d e = 0` with `1 - 2e` a unit. A distinguished
triangle whose first map vanishes splits, so the only object-level consequence of the three
triangles is

`L_{D/A[x]} ≅ L_{D/A} ⊕ D[1]` for `D = B × C`, `B`, `C`,

and the object-level form of the lemma over `A[x]` then yields no more than

`L_{B×C/A} ⊕ (B × C)[1] ≅ L_{B/A} ⊕ L_{C/A} ⊕ (B × C)[1]`,

from which the lemma does not follow — a direct summand may not be cancelled in a triangulated
category. The three triangles have to be compared *as triangles*, so their morphisms are needed,
and the library's Tag 08SA does not have them.
`CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex` of
`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean` is purely existential,
`∃ f g h, Triangle.mk f g h ∈ distTriang`, and the morphisms are not recoverable from it: the
triangle of the short exact sequence of differentials is transported onto the named objects by
`CategoryTheory.Pretriangulated.exists_distinguished_of_objIso` along two *chosen* isomorphisms,
one of them `CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex`, which is a
`Nonempty` and not data. The short complex the triangle comes from,
`CommAlgCat.restrictedCotangentComplexShortComplex`, is moreover stated at one fixed top algebra
and has no functoriality in it at all, so there is nothing to make the comparison out of either.

So what Tag 08SC needs is **Tag 08SA with its first two morphisms pinned as the functoriality
maps of [Stacks, Tag 08PN]**, which is in turn the comparison of [Stacks, Tag 08PU] between two
resolutions of `C` over `A` made natural **in the algebra `C`**. The naturality
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality`
of `StacksFrontier/Cotangent/ResolutionCotangentDerivedNaturality.lean`, is naturality **in the
resolution** for a fixed `A → C`, and does not give
the other one. **The other axis is available too**; see the next note but one.

**The comparison of the two resolutions of Tag 08SA has its arrow named, and is natural in
the top algebra.** The identification of the middle term is more than a `Nonempty` isomorphism
of objects, and no `A[x]`-algebra structure on `P_•(C/A)` is needed to avoid Tag 08PU.
There is a canonical morphism of simplicial `A`-algebras over `C`

`P_•(C/A) ⟶ P_•(C/B)`,

namely `CommAlgCat.standardResolutionSquareMap` of the square `(A → B, 𝟙_C)`, and when `B` is a
polynomial algebra over `A` *both* sides are resolutions of `C` over `A` — the second by
`CommAlgCat.standardResolution_isResolution_restrictScalars`. Remark 08QI at the arrow level,
`CommAlgCat.quasiIso_alternatingFaceMapComplex_map_of_isResolution` of
`StacksFrontier/Cotangent/ResolutionIndependence.lean`, then inverts the induced map. All of this is
in `StacksFrontier/Cotangent/RestrictedResolutionComparison.lean`:

* `CommAlgCat.restrictedResolutionComparisonOver` is the morphism of resolutions, and
  `CommAlgCat.restrictedCotangentComparison` the induced map
  `L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C` of cochain complexes of `C`-modules;
* `CommAlgCat.quasiIso_restrictedCotangentComparison` is that it is a quasi-isomorphism, for `B`
  a polynomial algebra over `A`. This is what
  `CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex` says about objects
  only;
* `CommAlgCat.standardResolutionSquareMap_restrictedTowerSquare_naturality` is **naturality in
  the top algebra**: for a `B`-algebra map `f : C → C'` the comparison commutes with the
  functoriality of the standard resolution in `f`. It is `standardResolutionSquareMap_comp`
  twice, the two composite squares `(A → B, 𝟙_C) ∘ (𝟙_B, f)` and `(𝟙_A, f) ∘ (A → B, 𝟙_{C'})`
  being definitionally the same square `(A → B, f)`.

So naturality in the top algebra is available, and the iterated-generator route — whose first
brick
`MvPolynomial.isPolynomialAlgebra_polynomial_of_X` of
`StacksFrontier/Cotangent/PolynomialAlgebraOverVariable.lean` is proved — is **not needed for the
descent**. It is kept because the brick is a general fact worth having, but nothing below depends
on it.

**There is no lemma to be had which pins the morphisms of an existential triangle, and this is
worth saying once for every tag that wants one.** From `∃ f g h, Triangle.mk f g h ∈ distTriang`
no particular `f` is recoverable, so no amount of ingenuity turns
`CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex` into a statement about
the functoriality maps of [Stacks, Tag 08PN]. Nor does
`CommAlgCat.exists_distinguished_of_objIso` of
`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean` help: it transports a
distinguished triangle along isomorphisms of the three *objects*, and the triangle it returns has
the conjugated maps, with nothing identifying them with the display's own. What is actually
needed is transport along an **isomorphism of triangles** — which is standard and already
available — and the content of that is the three commuting squares, i.e. the compatibility of the
chosen object isomorphisms with the maps. For Tag 08SA the object isomorphism in question is
`CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex` (Tag 08PU), a `Nonempty`
with no compatibility statement attached, so the squares do not exist to be used. The way out is
not a lemma about existential triangles but a construction which never discards the maps: build
the triangle from a short exact sequence whose morphisms are named, which is what the route above
does by arranging the middle term to be `L_{C/A}` on the nose. Any sibling tag whose obstruction
reads "`exists_distTriang_of_iso` conjugates a triangle's morphisms and nothing identifies the
conjugates with the display's own maps" — Tag 08QS has the same shape — has the same obstruction
and the same way out, and a general "pin the morphisms" lemma is not it.

**A general fact proved along the way, no longer on the critical path.**
`MvPolynomial.isPolynomialAlgebra_polynomial_of_X` of
`StacksFrontier/Cotangent/PolynomialAlgebraOverVariable.lean` says that `A[ι]`, read over `A[x]` by
sending `x` to one of its variables `X i₀`, is again a polynomial algebra over `A[x]`, on
`{i : ι // i ≠ i₀}`; and
`MvPolynomial.isPolynomialAlgebra_polynomial_of_algEquiv_X` says the same for an algebra
presented as `A[ι]` by a chosen `A`-algebra equivalence. These were the first brick of the
iterated-generator route, which the named comparison above makes unnecessary: that route wanted
`P_•(C/A)` lifted to a `SimplicialObject (CommAlgCat A[x])`, which would have required naming the
iterated polynomial generator of the image of `x` through the `eqToHom`s of
`CommAlgCat.standardEndofunctor_obj` and proving it preserved by Godement's faces and
degeneracies. **None of that is needed.** The two lemmas are kept as general facts.

**The next obstruction, exactly.** With the middle term of the [Stacks, Tag 08SA] sequence now
identified with `L_{C/A}` by a named, `C`-natural quasi-isomorphism, what remains is to carry
that identification through the sequence and to compare the sequences for `C = B × C₀`, `C = B`
and `C = C₀`. In order:

* *The sequence functorial in the top algebra.* **This is now proved**, in
  `StacksFrontier/Cotangent/RestrictedCotangentTopFunctoriality.lean`. A `B`-algebra map
  `f : C ⟶ C'` induces `u : P_•(C/B) ⟶ P_•(C'/B)` — `CommAlgCat.standardResolutionSquareMap` of
  `CommAlgCat.topSquareOfAlgHom`, the square `(𝟙_B, f)` — and
  `CommAlgCat.restrictedCotangentTopMap` is the induced map
  `Ω[Pₙ⁄A] ⊗[Pₙ] C ⟶ Ω[P'ₙ⁄A] ⊗[P'ₙ] C'` of the middle term, pinned by
  `CommAlgCat.restrictedCotangentTopMap_D` to `1 ⊗ d p ↦ 1 ⊗ d (u p)`. It is simplicial
  (`CommAlgCat.restrictedCotangentTopMap_naturality`) and commutes with **both** maps of the
  sequence: with the first by `CommAlgCat.restrictedCotangentTopMap_fromBase`, the left-hand
  vertical being `f ⊗ 𝟙` on `C ⊗[B] Ω[B⁄A]`; and with the second by
  `CommAlgCat.restrictedCotangentTopMap_toRelative`, the right-hand vertical being the
  functoriality of `L_{C/B}` in `C`, which is `CommAlgCat.squareCotangentTermMap` at the same
  square. What is *not* yet written is the packaging: the three maps as a morphism of
  `ShortComplex (SimplicialObject (ModuleCat C))`, hence of the short complexes of cochain
  complexes, hence of the two distinguished triangles. That packaging is bookkeeping over the
  four results just named.
* *The comparison must commute with the sequence's third map.* The third map of the sequence is
  the canonical surjection `Ω[P_n⁄A] ⊗ C ⟶ Ω[P_n⁄A[x]] ⊗ C` and the composite of the comparison
  with it is `1 ⊗ d q ↦ 1 ⊗ d (u q)` for `u` the comparison of resolutions, which is exactly the
  formula `CommAlgCat.cotangentComplexBaseRingMap_differential` of
  `StacksFrontier/Cotangent/Triangle/DisplayMorphisms.lean` pins for the second displayed morphism
  `L_{C/A} ⟶ L_{C/A[x]}`. So that square should be the two pinning formulas compared, and it is
  what makes the sequence's triangle the triangle *of the display*. **This is now proved**, in
  `StacksFrontier/Cotangent/RestrictedComparisonDisplay.lean`:
  `CommAlgCat.restrictedResolutionComparison_toRelative` says that in every simplicial degree the
  comparison followed by `CommAlgCat.restrictedCotangentToRelative` *is*
  `CommAlgCat.squareCotangentTermMap` at `CommAlgCat.restrictedTowerSquare`, which is
  `CommAlgCat.displaySquare₂` of the display written with `CommAlgCat.restrictedBase` as its
  source. The missing link was `CommAlgCat.overDifferentialsFunctor_map_mk` of
  `StacksFrontier/Cotangent/BaseChangeQuasiIso.lean`, which pins the degreewise component of the
  comparison on the pure differential; the three spellings of `1 ⊗ d p` which meet there —
  `CommAlgCat.overDifferentialsMk`, `CommAlgCat.cotangentTermDifferential` and
  `CommAlgCat.restrictedCotangentDifferential` — are definitionally equal but not syntactically
  so, and a `rw` across them is rejected, its motive leaving the target not type-correct at
  `implicit` transparency. The proof is therefore a term: a chain of `congrArg` and `Eq.trans`
  with no `rw` at all.
* *The five-lemma step.* **This is where the argument stops, and it is the only step left.**
  From the two outer verticals being quasi-isomorphisms — the third being Tag 08SC over `A[x]`,
  `CommAlgCat.quasiIso_cotangentExtendScalars_productFstSquare` of
  `StacksFrontier/Cotangent/ProductDecompositionSplittingElement.lean`, and the first being an
  isomorphism because `Ω[A[x]⁄A]` is free of rank one — conclude that the middle one is. Base
  change along the projection `B × C₀ → B` is exact without further hypothesis, the degreewise
  sequence being *split* by [Stacks, Tag 031K]. Ahead of it sits one piece of bookkeeping: the
  four results of `StacksFrontier/Cotangent/RestrictedCotangentTopFunctoriality.lean` have to be
  packaged as a morphism of `ShortComplex (SimplicialObject (ModuleCat C))`, hence of the short
  complexes of cochain complexes; no new mathematics is involved, every square being one of those
  four.

**What is in place for the eventual proof.** Besides the canonical map below: Tag 08QQ with the
arrow pinned and unconditional, as above; `Algebra.isPolynomialAlgebra_polynomial`, which
discharges the hypothesis of
`CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex` (Tag 08SA)
for the middle ring `A[x]` — that statement takes its three rings in one universe, so the tower is
read at `v = u`; Mathlib's `IsLocalization.away_fst` and `IsLocalization.away_snd`, which say that
`B` and `C` are the localizations of `B × C` at the two orthogonal idempotents, so that inverting
the image of `x` kills the `C` factor; `IsLocalization.flat` with
`CommAlgCat.torIndependent_of_flat`, for the flatness of `A[x] → A[x, x⁻¹]` and hence the
Tor-independence hypothesis of Tag 08QQ; and `CommAlgCat.bijective_baseChangeUnit_of_isPushout`
with `Algebra.isPushout_of_isLocalization` for its second hypothesis. Those last two discharges
are carried out, for exactly this shape of localization square, in
`StacksFrontier/Cotangent/Localization.lean`, whose
`CommAlgCat.nonempty_cotangentComplexDerived_iso_localizationBase` is already one of the two
instances of Tag 08QQ that the step over `A[x]` consumes. The vanishing of the
first map of the triangle is `CommAlgCat.nonempty_homotopy_squareCotangentComplexMap_zero`
([Stacks, Tag 08SB]) for `D = B` and for `D = C`, where `A[x] → D` factors through `A[x] → A`
sending `x` to `1` respectively to `0`; for `D = B × C` it does not, and the idempotency argument
above is needed instead.

**The splitting of `B × C`-modules is available**, in the form that a map of complexes of
`B × C`-modules is a quasi-isomorphism as soon as its two base changes along the projections
are. That is
`ModuleCat.quasiIso_of_quasiIso_extendScalars_prod` of
`StacksFrontier/Homology/ExtendScalars/ProductRing.lean`, for complexes over any complex shape; the
module-level statement it rests on is
`Module.bijective_of_bijective_baseChange_of_sections`, and the exactness of the two base changes
comes from `RingHom.flat_fst` and `RingHom.flat_snd` there together with
`extendScalars_preservesHomology_of_flat`. (The nearest other criterion,
`CommAlgCat.isZero_of_isZero_extendScalars_away` of
`StacksFrontier/Cotangent/KoszulRegularIdealQuotient.lean`, is for a single module and is phrased
through `Localization.Away`; it is not what the end of the source's proof consumes.)

**The inputs the product criterion needs on the target side are available**: the counit
`B ⊗_{B×C} M ⟶ M` is invertible on a `B`-module read over `B × C`, and `B ⊗_{B×C} N = 0` on a
`C`-module. The counit is invertible along any surjection of rings —
`Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app` of
`StacksFrontier/Algebra/Category/ModuleCat/ExtendScalarsAlongSurjection.lean` — and the two
projections are surjective by `RingHom.surjective_fst` and `RingHom.surjective_snd`. The
vanishing is `ModuleCat.isZero_extendScalars_fst_restrictScalars_snd` and its mirror
`ModuleCat.isZero_extendScalars_snd_restrictScalars_fst`, both instances of
`ModuleCat.isZero_extendScalars_of_smul_eq_zero` at the two orthogonal idempotents; the three
are in `StacksFrontier/Homology/ExtendScalars/ProductRing.lean`.

**The two shapes of the functoriality map now agree on the cotangent complexes.**
`CommAlgCat.squareCotangentComplexMap` lands in `ModuleCat.restrictScalars sq.map` of the target
while `CommAlgCat.cotangentExtendScalarsComplexMap` is the adjoint map out of
`ModuleCat.extendScalars`, and `CommAlgCat.cotangentExtendScalarsComplexMap_eq_counit` of
`StacksFrontier/Cotangent/BaseChangeComplexCounit.lean` says that the second is extension of scalars
of the first followed by the counit of the adjunction, as an equality of maps of cotangent
complexes. It is transported from the Moore complexes, where it is
`CommAlgCat.cotangentExtendScalarsMooreMap_f_eq_counit` of
`StacksFrontier/Cotangent/BaseChangeQuasiIso.lean`, through the reindexing which places
simplicial degree `n` in cohomological degree `-n`. So the base change along `RingHom.fst B C` of the canonical map
below *is*, up to the two identifications above, the map `L_{B×C/A} ⊗_{B×C} B ⟶ L_{B/A}` which
Tag 08QQ pins.

**Tag 08QQ does not invert that map, and this is the sharp obstruction.** The square in question
is `(A →𝟙 A, B × C → B)`, and the hypothesis `hpush` of
`CommAlgCat.quasiIso_cotangentExtendScalarsComplexMap` is
`Function.Bijective (CommAlgCat.baseChangeUnit b)`, which here is bijectivity of
`A ⊗_A (B × C) → B`, that is of the projection itself. It fails unless `C` is the zero ring. So
the product criterion does not reduce Tag 08SC over the base `A` to Tag 08QQ, and no
rearrangement of the inputs above does.

Over the base `A[x]`, with `x ↦ (1, 0)`, Tag 08QQ does apply, twice. `A[x] → A[x, x⁻¹]` is flat,
so the Tor independence holds, and `(B × C) ⊗_{A[x]} A[x, x⁻¹] = B` because inverting the
idempotent `(1, 0)` kills the `C` factor (`IsLocalization.away_fst`): Tag 08QQ at the square
`(A[x] → A[x, x⁻¹], B × C → B)` gives `L_{B×C/A[x]} ⊗_{B×C} B ≅ L_{B/A[x, x⁻¹]}`. At the square
`(A[x] → A[x, x⁻¹], B → B)` it gives `L_{B/A[x]} ≅ L_{B/A[x, x⁻¹]}`, the unit being bijective
because `x` acts on `B` as `1`. The component map `L_{B×C/A[x]} ⊗_{B×C} B ⟶ L_{B/A[x]}` is the
first followed by the inverse of the second, and recognising it as such is what the composition
lemma `CommAlgCat.squareCotangentComplexMap_comp_counit` of
`StacksFrontier/Cotangent/BaseChangeCompositionCounit.lean` is for: it is the composition law for
the **adjoint** shape of the functoriality map, the shape Tag 08QQ inverts. The composition law
`CommAlgCat.squareCotangentComplexMap_comp` is for the unextended map only. The mirror argument at
`x - 1` kills the `B` factor. So what the product criterion closes is the statement of Tag 08SC
**over the base `A[x]`** — which is now closed, in
`StacksFrontier/Cotangent/ProductDecompositionSplittingElement.lean`; see below — and the step from
the base `A[x]` down to the base `A` is exactly the comparison of the three triangles described
above, which still wants Tag 08SA with its first two morphisms pinned.

**Tag 08SC is now reduced to its two components.**
`CommAlgCat.quasiIso_cotangentComplexProductMap_of_components_counit` of
`StacksFrontier/Cotangent/ProductDecompositionCriterion.lean` says that the canonical map below is a
quasi-isomorphism as soon as the two maps

`L_{B×C/A} ⊗_{B×C} B ⟶ L_{B/A}` and `L_{B×C/A} ⊗_{B×C} C ⟶ L_{C/A}`

are, each written in the adjoint shape which Tag 08QQ inverts. The biproduct is no longer in the
way: base change along one projection kills the other summand degreewise, so it inverts the
projection of `L_{B/A} ⊕ L_{C/A}` onto the surviving summand
(`CommAlgCat.isIso_extendScalars_biprod_fst` and its mirror), and the base change of the
canonical map is the base change of one component alone.

**Tag 08SC over the base `A[x]` is proved**: the two component statements over the base `A[x]`,
with `x ↦ (1, 0)`, come from the two instances of Tag 08QQ above, assembled with the
`A[x]`-algebra structures, the mirror element `1 - x`, and the identification of
`CommAlgCat.algebraSquareOfAlgHom` of the projection with the horizontal composite of the two
squares. All of that is in
`StacksFrontier/Cotangent/ProductDecompositionSplittingElement.lean`:

* `CommAlgCat.quasiIso_cotangentComplexProductMap_polynomialBase` is **the canonical map below
  proved a quasi-isomorphism over the base `A[x]`**, for any two `A`-algebras `B` and `C` read
  over `A[x]` through `x ↦ 1` and `x ↦ 0`. The product `A[x]`-algebra structure on `B × C` is
  `Polynomial.aeval (1, 0)` by `Polynomial.aeval_prodMk` of the same file.
* It is a corollary of
  `CommAlgCat.quasiIso_cotangentComplexProductMap_of_splittingElement`, which needs no polynomial
  ring: over *any* base `R` carrying an element of image `1` in `B` and image `0` in `C` the
  canonical map is a quasi-isomorphism. The two components are
  `CommAlgCat.quasiIso_cotangentExtendScalars_productFstSquare` at `x` and
  `CommAlgCat.quasiIso_cotangentExtendScalars_productSndSquare` at `1 - x`.
* The second of the two Tag 08QQ instances — at the square `(A[x] → A[x, x⁻¹], B → B)`, whose top
  map is the identity — is `CommAlgCat.quasiIso_squareCotangentComplexMap_away_of_isUnit`, its
  `hpush` being `IsLocalization.isPushout_of_isUnit` of
  `StacksFrontier/Cotangent/ProductDecompositionLocalization.lean`: inverting an element already
  invertible changes nothing. The mirror localization lemmas
  `IsLocalization.isPushout_prod_snd` and its two auxiliaries are there too.
* The identification of the two squares needed no lemma: `CommAlgCat.AlgebraSquare.comp` composes
  with `RingHom.comp`, and composing with an identity is a definitional equality of squares, as
  is `ModuleCat.restrictScalars` along the identity on a complex. So the hypothesis of
  `CommAlgCat.quasiIso_squareCotangentComplexMap_counit_of_comp` is reached by `exact`, with no
  `rw` building a motive across the two spellings.

**Tag 08SC is proved.** The descent from the base `A[x]` to the base `A`, which every note above
calls the headline obstruction, is
`CommAlgCat.quasiIso_cotangentExtendScalars_restrictedTopSquare` of
`StacksFrontier/Cotangent/RestrictedCotangentDescent.lean`, and the lemma itself is
`CommAlgCat.quasiIso_cotangentComplexProductMap` and
`CommAlgCat.isIso_Q_map_cotangentComplexProductMap` of
`StacksFrontier/Cotangent/ProductDecompositionBase.lean`.

The route is the one the notes above describe, with one simplification which is why the
existential form of the library's Tag 08SA never gets in the way: **the three triangles are never
formed.** What is compared is the short exact *sequences* they come from,
`CommAlgCat.restrictedCotangentComplexShortComplex`, whose two morphisms are named, and the
comparison is the five lemma on them rather than a map of triangles. In detail, for the first
projection `B × C → B` (and symmetrically for the second):

* the sequence is functorial in the top algebra, packaged as a morphism of short complexes of
  simplicial modules by `CommAlgCat.restrictedCotangentShortComplexTopMap` of
  `StacksFrontier/Cotangent/RestrictedCotangentShortComplexTop.lean`, and carried to the complexes
  by `AlgebraicTopology.extendMooreMap`;
* base changed along the projection, which is flat (`RingHom.flat_fst`), both sequences stay
  short exact (`ModuleCat.shortExact_map_extendScalars_of_flat`);
* the first vertical becomes an isomorphism, `B ⊗_{B×C} ((B × C) ⊗_{A[x]} Ω[A[x]⁄A])` being
  `B ⊗_{A[x]} Ω[A[x]⁄A]` by cancellation of base change
  (`CommAlgCat.baseDifferentialsCancelIso`); no freeness of `Ω[A[x]⁄A]` is used;
* the third vertical is Tag 08SC over the base `A[x]`,
  `CommAlgCat.quasiIso_cotangentExtendScalars_productFstSquare`;
* so `quasiIso_τ₂_of_shortExact` inverts the middle vertical, and transporting it along the named
  comparison `CommAlgCat.restrictedCotangentComparison` of [Stacks, Tag 08PU] — which is natural
  in the top algebra, `CommAlgCat.restrictedCotangentComparisonSimplicial_naturality` — gives the
  component `L_{B×C/A} ⊗_{B×C} B ⟶ L_{B/A}` that the product criterion consumes.

**Tag 08SF is not a shortcut.** `B` is the localization of `B × C` at the idempotent `(1, 0)`,
so [Stacks, Tag 08SF] reads `L_{B/A} = L_{B×C/A} ⊗^𝐋_{B×C} B`, which is the component statement
over the base `A`. But the library's Tag 08SF,
`CommAlgCat.nonempty_cotangentComplexDerivedBaseChange_iso_localization` of
`StacksFrontier/Cotangent/Localization.lean`, has as its conclusion a `Nonempty` isomorphism of
objects naming no arrow, which cannot invert the canonical map below; and that file sits
downstream of this one, since the fundamental triangle it reads off, Proposition 08QX, is proved
in `StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, whose own proof consumes the product
decomposition built here.

**The canonical map is stated at chain level.** `CommAlgCat.squareCotangentComplexMap` is a map of
complexes of `B × C`-modules, so the pair of the two projection maps is a chain-level map into the
biproduct of complexes, which `Mathlib.Algebra.Homology.HomologicalComplexAbelian` provides.
Applying `DerivedCategory.Q`, an additive functor, gives the map in `D(B × C)` that Tag 08SC talks
about; no choice is involved, in contrast to the identifications discussed above.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 08SB](https://stacks.math.columbia.edu/tag/08SB)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Algebra

/-- The polynomial algebra `A[x]` in one variable is a polynomial algebra over `A`, on the
one-element set of variables. This is the hypothesis that the distinguished triangle of
[Stacks, Tag 08SA] takes of the middle ring of its tower. -/
public theorem isPolynomialAlgebra_polynomial (A : Type u) [CommRing A] :
    Algebra.IsPolynomialAlgebra A (Polynomial A) :=
  ⟨PUnit.{u + 1}, ⟨MvPolynomial.uniqueAlgEquiv A PUnit.{u + 1}⟩⟩

end Algebra

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B C : CommAlgCat.{max u v} A)

/-- The first projection `B × C → B`, read as a commutative square of ring maps over the identity
of `A`. -/
public def productFstSquare : AlgebraSquare.{u, v, u} A A (CommAlgCat.of A (B × C)) B where
  base := RingHom.id A
  map := RingHom.fst B C
  map_algebraMap _ := rfl

/-- The second projection `B × C → C`, read as a commutative square of ring maps over the identity
of `A`. -/
public def productSndSquare : AlgebraSquare.{u, v, u} A A (CommAlgCat.of A (B × C)) C where
  base := RingHom.id A
  map := RingHom.snd B C
  map_algebraMap _ := rfl

/-- **The canonical map of [Stacks, Tag 08SC].** For ring maps `A → B` and `A → C`, the pair of
the functoriality maps of the two projections `B × C → B` and `B × C → C` is a map of complexes of
`B × C`-modules

`L_{B×C/A} → L_{B/A} ⊕ L_{C/A}`,

the two summands being read over `B × C` along the projections. Tag 08SC asserts that
`DerivedCategory.Q` of this map is an isomorphism in `D(B × C)`; that is
`CommAlgCat.isIso_Q_map_cotangentComplexProductMap` of
`StacksFrontier/Cotangent/ProductDecompositionBase.lean`. -/
@[stacks 08SC "the canonical map `L_{B×C/A} → L_{B/A} ⊕ L_{C/A}` of the lemma, at chain level: \
  the pair of the functoriality maps of the two projections, whose `DerivedCategory.Q` is the map \
  in `D(B × C)` of the statement. That this map is an isomorphism in `D(B × C)` is \
  `CommAlgCat.isIso_Q_map_cotangentComplexProductMap` of \
  `StacksFrontier/Cotangent/ProductDecompositionBase.lean`, over an arbitrary base"]
public noncomputable def cotangentComplexProductMap :
    cotangentComplex.{u, v} A (CommAlgCat.of A (B × C)) ⟶
      (((ModuleCat.restrictScalars (productFstSquare.{u, v} A B C).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v} A B)) ⊞
        (((ModuleCat.restrictScalars (productSndSquare.{u, v} A B C).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v} A C)) :=
  biprod.lift (squareCotangentComplexMap.{u, v, u} (productFstSquare.{u, v} A B C))
    (squareCotangentComplexMap.{u, v, u} (productSndSquare.{u, v} A B C))

/-- The first component of the canonical map of [Stacks, Tag 08SC] is the functoriality map of the
first projection. -/
@[simp]
public theorem cotangentComplexProductMap_fst :
    cotangentComplexProductMap.{u, v} A B C ≫ biprod.fst =
      squareCotangentComplexMap.{u, v, u} (productFstSquare.{u, v} A B C) :=
  biprod.lift_fst _ _

/-- The second component of the canonical map of [Stacks, Tag 08SC] is the functoriality map of
the second projection. -/
@[simp]
public theorem cotangentComplexProductMap_snd :
    cotangentComplexProductMap.{u, v} A B C ≫ biprod.snd =
      squareCotangentComplexMap.{u, v, u} (productSndSquare.{u, v} A B C) :=
  biprod.lift_snd _ _

end CommAlgCat

end
