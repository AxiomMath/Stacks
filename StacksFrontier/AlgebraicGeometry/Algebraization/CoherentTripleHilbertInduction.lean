module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSupport
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The induction on the dimension of the support in Tag 0F27

[Stacks, Tag 0F27] is proved by induction on the dimension of the support of the
punctured-spectrum member of the coherent triple. This file carries out that induction. It
isolates the geometric input of the induction step as
`Stacks.Algebraization.HasHilbertInductionStep` and proves that the input yields the
proposition: a natural number `d` bounding `dim(Supp F)` gives a rational polynomial of degree
at most `d` computing `n ↦ χ((F, F₀, α) ⊗ (L, L₀, λ)^{⊗ n})` at every integer.

## Main definitions

* `Stacks.Algebraization.HasHilbertInductionStep`: the geometric input of the induction step of
  [Stacks, Tag 0F27].

## Main results

* `Stacks.Algebraization.eq_of_forall_succ_eq`: a function on `ℤ` whose consecutive values agree
  is constant.
* `Stacks.Algebraization.exists_polynomial_eulerCharacteristic_twistZ_of_hasInductionStep`:
  **the induction of [Stacks, Tag 0F27] on the dimension of the support**, from that input.
* `Stacks.Algebraization.topologicalKrullDim_ne_top_of_subset_puncturedSpectrum`: a subset of
  the punctured spectrum of a Noetherian local ring has finite Krull dimension.
* `Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp_of_hasInductionStep`: the same
  conclusion at the source's spelling of the degree bound, `dim(Supp F)` truncated at `0`.

## Implementation notes

The induction is on a natural number `d` bounding `dim(Supp F)` rather than on the dimension
itself, so that nothing has to be assumed about the dimension being finite. The bound is phrased
with `topologicalKrullDim`, whose value on an empty support is `⊥`, so a vanishing
punctured-spectrum member satisfies the hypothesis for `d = 0` and receives a constant
polynomial. That is the reading of the tag's degree bound which its own "more precisely"
paragraph supplies: `F = 0` and `F` of finite support in `U` both make the function constant.

The induction step as the source states it has two halves, and
`Stacks.Algebraization.HasHilbertInductionStep` records both. First the triple is replaced by
its quotient by the sections of the closed-fibre member supported at the closed point; that is
the short exact sequence `0 → K → T → T' → 0` with `IsZero K.F`, across which polynomiality of a
given degree transfers by
`Stacks.Algebraization.exists_polynomial_eulerCharacteristic_twistZ_of_shortExact_isZero`. Then
a section of `L` not vanishing at the associated points of `F` and of `F/fF` produces, for every
`n`, the short exact sequence
`0 → T' ⊗ L^{⊗ n} → T' ⊗ L^{⊗ n+1} → G ⊗ L^{⊗ n} → 0`, whose quotient `G` has support of
strictly smaller dimension; the Euler characteristics of the twists of `T'` then come from those
of the twists of `G` by
`Stacks.Algebraization.exists_polynomial_eulerCharacteristic_of_shortExact_succ`.

The dimension drop is recorded in the two forms the induction consumes rather than as the single
inequality `dim(Supp G) + 1 ≤ dim(Supp F)`: a bound `e + 1` for `dim(Supp F)` gives the bound `e`
for `dim(Supp G)`, and the bound `0` for `dim(Supp F)` forces `Supp G` to be empty. Both follow
from that inequality, and stating them this way keeps all arithmetic in `WithBot ℕ∞` out of the
induction.

The last clause of the input, that a `G` with vanishing punctured-spectrum member has vanishing
Euler characteristic, is what makes the degree bound *sharp at the bottom*, and it is a genuine
part of the source's claim rather than a convenience. Without it the induction gives only
`deg ≤ dim(Supp F) + 1` when `dim(Supp F) = 0`: the first difference of the function is then the
constant `χ(G)`, which is a polynomial of degree `0`, so the function itself is only known to be
linear, whereas the source asserts that a triple with finite support in `U` has a *constant*
function.

**That clause carries the hypothesis `dim(Supp F) ≤ 0`, and the hypothesis is not optional.** The
bare implication `IsZero G.F → χ(G) = 0` is false at the remaining hypotheses; the witness is
written out below. The hypothesis the source
itself argues under is `dim(Supp F) ≤ 0`, and under it the source's own argument goes through:
after the first reduction the closed point is not an associated point of `F₀`, and for `F` of
zero-dimensional support in `U` the element `f` lies in no prime of `Supp F` — a point of a
zero-dimensional support is minimal in it, hence an associated point of `F`, and `f` is a
nonzerodivisor on `F` — so `F/fF = 0`, so `F₀|_{U_0} = 0`, so `F₀ = 0` and the quotient's
closed-fibre member vanishes too.

**The induction never needs the clause anywhere else**, and that is why attaching the hypothesis
costs nothing. In the recursion below, the bottom case `d = 0` is exactly the case in which
`Supp G` is forced to be empty (that is the second form of the dimension drop, `hdrop₀`), and
there `dim(Supp F) ≤ 0` is the hypothesis of the theorem itself. Above the bottom, `d = e + 1`,
the induction hypothesis applies to `G` whatever its support is — an empty support gives
`dim(Supp G) = ⊥ ≤ e` — so the recursion goes through
`Stacks.Algebraization.exists_polynomial_eulerCharacteristic_of_shortExact_succ` and the clause
is not consulted. An earlier shape of the proof split on whether
`Supp G` is empty instead of on `d`, which demanded the clause at every `d`, and that is what
made its false form look necessary.

`Stacks.Algebraization.HasHilbertInductionStep` is **not an assumption**: the witness is
`Stacks.Algebraization.hasHilbertInductionStep` in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInductionStep`, and
`Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp` there is the conclusion of
[Stacks, Tag 0F27] with no hypothesis beyond the source's. What that assembly cost beyond the
four clauses below is recorded in that file's implementation notes: two trivializations of the
invertible triple, six quasi-coherence arguments, and a restatement of the third clause with its
quotient named rather than produced existentially — no mathematics. The state of the four clauses
is

* the first, the opening reduction, is closed:
  `Stacks.Algebraization.CoherentTriple.exists_shortExact_isZero_F`, and its payoff
  `𝔪 ∉ Ass(F₀/G₀)` is
  `Stacks.Algebraization.CoherentTriple.not_isAssociatedPoint_closedPoint_quotientTriple`;
* the third, the dimension drop, is
  `Stacks.Algebraization.CoherentTriple.dimension_drop_of_isNowhereDense`, which delivers both
  of the forms the induction consumes and owes *three* hypotheses about the quotient, not only
  nowhere-density: the containment `Supp G ⊆ Supp F`, closedness of `Supp G`, and nowhere-density
  of `Supp G` in `Supp F`. **Two of the three are discharged**, in
  `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelSupport`, and the whole
  clause is packaged owing only the third as
  `Stacks.Algebraization.CoherentTriple.dimension_drop_cokernelTriple_twistZ` (and
  `..._of_forall_irreducibleComponents` with the hypothesis in the shape a supplier checks). The
  bound on the support of that cokernel is
  `AlgebraicGeometry.Scheme.Modules.supp_cokernel_subset_supp`, five lines off two lemmas that
  were already in `StacksFrontier.AlgebraicGeometry.Modules.StalkSupport` -- its
  `notMem_supp_iff_isZero_stalk` and its pointwise stalkwise criterion
  `surjective_stalkLinearMap_iff_notMem_supp_cokernel`, outside the support of the target the
  stalk map being surjective for want of anything to hit -- and closedness is proved
  in that same file, as `AlgebraicGeometry.Scheme.Modules.isClosed_supp_cokernel`. The
  containment is read against `Supp F` itself rather than against the support of the twist
  because `Stacks.Algebraization.CoherentTriple.supp_twistZ_F` says twisting does not move the
  support. Of the nowhere density the **geometric half is discharged**: a component of
  `Supp F` has a generic point, the punctured spectrum being a scheme and hence sober, and that
  generic point is an associated point of `F` by [Stacks, Tag 05AL] --
  `AlgebraicGeometry.mem_associatedPoints_of_isGenericPoint_irreducibleComponent_supp`, in
  `StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization`. So the
  clause reduces to a *pointwise* statement, and is packaged
  that way as
  `...CoherentTriple.dimension_drop_cokernelTriple_twistZ_of_notMem_associatedPoints`:
  what is owed is that **no associated point of `F` lies in `Supp G`**. For multiplication by a
  section that is the stalkwise statement the nonvanishing gives:
  `Stacks.SectionProduct.bijective_mapFun_mulRight_of_le_nonvanishingLocus` composed with
  `AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`, the
  punctured-spectrum member of
  `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` being put into the shape of
  `Stacks.TensorSectionNonvanishing.mulRight` by
  `Stacks.Algebraization.tensorModulesMap_id_eq_whiskerLeft`,
  `Stacks.Algebraization.whiskerLeft_mulSectionPowScheme` and
  `Stacks.Algebraization.rightUnitor_inv_comp_whiskerLeft`, with the two trailing isomorphisms
  absorbed by `AlgebraicGeometry.Scheme.Modules.supp_cokernel_comp_isIso`. **That is now done**,
  in `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelNonvanishing`: the
  stalkwise statement is
  `Stacks.Algebraization.CoherentTriple.notMem_supp_cokernelTriple_mulSectionTwistZ` and the two
  clauses themselves are
  `Stacks.Algebraization.CoherentTriple.dimension_drop_cokernelTriple_mulSectionTwistZ`, which
  owes nothing beyond the nonvanishing of the section near the associated points of `F` -- the
  same hypothesis the monicity of the second clause already consumes, so a supplier holding that
  one holds this one. No bridge is needed between `Stacks.ModuleStalk.mapFun`, which the
  bijectivity lemma is about, and `AlgebraicGeometry.Scheme.Modules.stalkLinearMap`, which the
  support criterion is about: **the two are the same function**, both
  `((TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf φ)).hom` applied to an
  argument, one packaged as a bare function and one as the `toFun` of a linear map over the local
  ring, so the second projection of the bijectivity is accepted for the surjectivity by `exact`.
  The substantive step is the support step, which cannot be a `rw`; see that file's
  implementation notes. No quasi-coherence hypothesis appears either, the monicity's two coming
  from [Stacks, Tag 0AVL] and not from clause 2 of [Stacks, Tag 01CY];
* the fourth, the vanishing, is **closed, at the hypothesis the predicate now carries**. Its
  endpoint is `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_zero_of_isZero_F`,
  which asks that the closed point of the closed fibre not be an associated point of the
  quotient's closed-fibre member. The hypothesis-free
  `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_quotientTriple_eq_zero_of_isZero_F`
  discharges exactly that condition, but only for the triple the *opening reduction* produces,
  not for the quotient `G` this clause is about. **That hypothesis is not an intermediate step
  towards `IsZero G.F₀`; under the antecedent `IsZero G.F` it is equivalent to it**, by
  `Stacks.Algebraization.CoherentTriple.not_isAssociatedPoint_closedPoint_iff_isZero_F₀_of_isZero_F`
  -- the support of `G₀` already lies in the closed point, and a nonzero quasi-coherent module on
  a locally Noetherian scheme has an associated point in its support. So the debt is exactly
  `IsZero G.F → IsZero G.F₀` for the cokernel triple, and **that implication is false** as soon
  as it is asked for at an arbitrary triple -- which is why this clause carries
  `dim(Supp T.F) ≤ 0`.

  Two witnesses, in increasing strength. For `A = k[[x, y]]`, `f = y`, `T` and `L` the unit
  triple, `σ = x` and `m = 0`, the quotient has `G₀ = k[[x]]/x = k`, a skyscraper at the closed
  point, whose unique associated point *is* the closed point -- so the antecedent `IsZero G.F` is
  load-bearing. **It is not, however, enough: the implication is false even with the opening
  reduction's `𝔪₀ ∉ Ass(T.F₀)` added.** Take `A = k[[x, y]]`, `f = y` and `T` the unit triple --
  so `T.F₀ = k[[x]]`, whose only associated point is the generic one, and the opening reduction's
  conclusion holds of `T` -- and for `L` the triple `(𝒪_U, 𝒪_{A/f}, α)` whose gluing `α` is
  multiplication by `x`, a unit of `k((x)) = Γ(U₀, 𝒪)`; `L` is invertible, and *not* isomorphic
  to the unit triple. Then `σ = 1`, `σ₀ = x` is a legitimate section pair -- `hcompat` reads
  `1 · x = x` over the punctured closed fibre -- nonvanishing at every associated point of both
  members, and at `m = 0` the quotient has `G.F = 0` and `G.F₀ = k[[x]]/x = k`. Note that
  `dim(Supp T.F) = 1` there: the witness does not survive the hypothesis this clause now carries.

  What that witness locates is a break in the *mapped* route, and the break is not the Nakayama
  step. The closed fibre being affine and local, `G₀ = 0` does say that multiplication by `σ₀` is
  surjective on the stalk at the closed point, so by Nakayama either `σ₀` is nonvanishing there
  or `T.F₀ = 0`; and `IsZero G.F` does say that `σ` vanishes nowhere on `Supp F` inside the
  punctured spectrum. But **the closed point of the closed fibre is not a point of the punctured
  spectrum**, so the vanishing of `σ₀` there is not the vanishing of `σ` anywhere: `σ` may be
  nonvanishing on the whole of `U`, as it is in the witness, precisely because `L.alpha` is an
  arbitrary unit over the punctured closed fibre and absorbs the discrepancy. `hcompat` relates
  `σ` and `σ₀` over that punctured closed fibre and nowhere else. No repair of the clause can run
  through `σ₀`.

  **The repair is the source's own hypothesis, and the chain under it is proved**, in
  `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroDimensionalVanishing`. Under
  `dim(Supp T.F) ≤ 0` the points of `Supp T.F` are minimal in it
  (`Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero`), hence associated
  points of `T.F` by [Stacks, Tag 05AH]
  (`AlgebraicGeometry.mem_associatedPoints_of_mem_supp_of_specialization`), and `f` lies in no
  associated prime of the sections of `T.F` over an affine open, being a nonzerodivisor on them
  (`Stacks.Algebraization.CoherentTriple.torsionFree` against
  `isSMulRegular_iff_forall_notMem_associatedPrimes`, the two notions of an associated point
  being matched on one affine open by
  `...AssociatedPointPrime.divisorsIsAssociatedPoint_iff_mem_associatedPrimes`);
  so `Supp T.F` misses `V(f)` inside `U`
  (`...CoherentTriple.notMem_asIdeal_of_mem_supp_of_topologicalKrullDim_le`), the inverse image of
  `T.F` on the punctured closed fibre has empty support
  (`...CoherentTriple.supp_pullback_eq_empty_of_topologicalKrullDim_le`), and the gluing gives
  `T.F₀ = 0` (`...CoherentTriple.isZero_F₀_of_topologicalKrullDim_le`, and with the opening
  reduction's condition automatic,
  `...CoherentTriple.isZero_F₀_quotientTriple_of_topologicalKrullDim_le`).

  Three remarks about that chain.

  * The containment `Supp (i^* F) ⊆ i ⁻¹' Supp F` for an arbitrary morphism, used in
    `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedFibreSupportTransfer`,
    holds, and as an *equality*: `SheafOfModules.supp_pullback` in
    `StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic`, [Stacks, Tag 056J], for every
    morphism of schemes and every module of finite type. (A second, module-private copy sits in
    `StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper`.)
  * No dimension theory is needed. A second repair is possible -- carrying the
    *multiplier* `g ∈ 𝔪` of
    `Stacks.Algebraization.exists_mem_maximalIdeal_nonvanishing_smul_pow` in the clause, so that
    `V(g) ⊆ Spec A` is a genuine closed set, deducing `Supp T.F ∩ V(g) ∩ U = ∅` from
    `IsZero G.F`, and then `dim(Supp T.F) ≤ 0` from Krull's principal-ideal theorem in `A/p'` --
    with the scheme-level principal-ideal theorem as its main input. That route works
    (its dimension step is `Ideal.not_lt_of_lt_of_mem_minimalPrimes_sup_span_singleton` applied
    to `𝔪 ∈ (p' ⊔ (g)).minimalPrimes`, about twenty lines) but it is **unnecessary**: the
    hypothesis it manufactures is the one the predicate can simply carry.
  * The clause is not needed at every `d`. The source's argument "covers only `dim(Supp F) = 0`",
    and that is exactly the case the induction uses it in; see the discussion of the recursion
    above.

  The Nakayama link the mapped route would have needed is nonetheless proved:
  `Stacks.SheafOfModules.eq_zero_grpStalk_tensorSheaf_of_notMem_nonvanishingLocus`
  in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.VanishingSectionNakayama` -- where a global
  section vanishes, surjectivity of multiplication by it on a stalk means that the stalk is zero.
  Clause 2 of [Stacks, Tag 01CY] is the converse. What that
  link still owes a consumer in *this* spelling is two bridges, both named in its own notes:
  `AlgebraicGeometry.stalkLinearMap` against
  `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL`, and the monoidal product of
  `AlgebraicGeometry.Scheme.Modules` against
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`. It is not used here.

  Finally, the clause is discharged **in the shape this predicate asks for it** -- about the `G`
  the third clause produces, not about an abstract triple -- as
  `...CoherentTriple.eulerCharacteristic_eq_zero_of_shortExact_twistZ_quotientTriple`: twisting
  does not move the closed-fibre member (`...CoherentTriple.twistZF₀Iso`, which assumes nothing
  of the triple), so `T'.F₀ = 0` makes the middle term of the twisted sequence zero on the closed
  fibre and the quotient's closed-fibre member a quotient of that
  (`...CoherentTriple.isZero_F₀_of_shortExact_twistZ`), after which
  `...CoherentTriple.eulerCharacteristic_eq_zero_of_isZero` applies. Note that this clause is the
  only one of the four that is indifferent to *which* quotient the third produces: it reads the
  quotient off a short exact sequence, so it is discharged for whatever `G` that clause supplies;
* the second, the short exact sequences, is **closed**. Its left-hand map is
  `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` and its quotient is
  `Stacks.Algebraization.CoherentTriple.cokernelTriple`, whose short exactness is
  `Stacks.Algebraization.CoherentTriple.shortExact_cokernelHom`; the clause itself is
  `Stacks.Algebraization.CoherentTriple.exists_shortExact_twistZ_quotientTriple` in
  `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSequence`, which produces the
  one quotient `G` and both families for the triple the opening reduction supplies with **no**
  hypothesis about the section -- only the quasi-coherence of the tensor products and the
  trivialization of each member of `L` that
  `Stacks.Algebraization.exists_sectionPair_mono_quotientTriple` already carries. All three of
  its inputs are discharged: the section *pair* -- a global section of each member of the
  invertible triple corresponding over the punctured closed fibre, which [Stacks, Tag 0F20]
  supplies on the punctured spectrum alone, plus the source's omitted adjustment by an element of
  `𝔪`; injectivity of multiplication by it on both members, from the choice off
  `Ass(F) ∪ Ass(F/fF)`, which is also what gives the `f`-torsion-freeness
  `Stacks.Algebraization.CoherentTriple.cokernelTriple` takes as a hypothesis; and the
  identification of the quotients in the separate degrees with the twists of one quotient. The
  routes are recorded below.

**The first of those three is closed, at the hypotheses of this predicate and no others.**
`hcompat` is reduced to a single equation of global sections by
`Stacks.Algebraization.hcompat_of_eq_globalSectionsMap`, and to the compatibility square of a
morphism out of the unit triple by `Stacks.Algebraization.hcompat_of_hom`; the
`x₀ : Γ(L.F₀, ⊤)` with `globalSectionsMap A f L x` equal to the inverse image of `x₀` is supplied
by `Stacks.Algebraization.exists_sectionPair_nonvanishing_on_associatedPoints_depthFree`, and the
morphism `Stacks.Algebraization.CoherentTriple.Hom (Stacks.Algebraization.CoherentTriple.unit A f
h) L` itself by
`Stacks.Algebraization.exists_homUnit_nonvanishing_on_associatedPoints_depthFree`, both in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairDepthFree`. Neither needs
`hreg`.

The source's "multiplying `s` by a suitable element of `𝔪`" has two halves and both are proved.
The multiplier is chosen *first*, by prime avoidance off the finitely many primes of
`Ass(F) ∪ Ass(F/fF)`, so that **every** power of it keeps the nonvanishing:
`Stacks.Algebraization.exists_mem_maximalIdeal_nonvanishing_smul_pow`. The extension of the
section across the closed point of the closed fibre -- which
`Stacks.Algebraization.closedFibre` presents as `Spec (A / fA)`, with punctured part the
punctured spectrum of that ring by
`Stacks.Algebraization.puncturedClosedFibre_eq_puncturedSpectrum` -- is then
`Stacks.Algebraization.hasPowerExtendableClosedFibreSections`.

That extension does not come from
`Stacks.LocalCohomology.exists_idealPow_hom_of_section_on_affine_of_torsionFree` (assembled on
`Spec A` as
`Stacks.Algebraization.PreparedExtension.exists_pow_smul_eq_sectionOnIdealComplement`)
instantiated at `A / fA`. It comes from the global-sections clause of [Stacks, Tag 01YB],
`...IdealPowerColimit.exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent`,
which carries no torsion-freeness and no depth hypothesis, covers all of the punctured spectrum
rather than a basic open, and leaves the multiplier to the caller -- which is what makes it
composable with the prime avoidance that has already fixed `g`.

The second owes the monicity of the two members and the `f`-torsion-freeness of the quotient, and
those two are **not** independent of each other.

*The monicity on the punctured member is **done**:*
`Stacks.Algebraization.CoherentTriple.mono_onPunctured_mulSectionTwistZ`, in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoPunctured`.
`Stacks.SectionProduct.mono_mulRight_of_associatedPoints` proves monicity for
`Stacks.TensorSectionNonvanishing.mulRight` at an *arbitrary* quasi-coherent domain, so the
degree-`n` map needs no statement of its own, and
`Stacks.Algebraization.whiskerLeft_mulSectionPowScheme` already puts the member of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` into the body `(ρ_ _).inv ≫ _ ◁ σ` of
`mulRight`. What separated the two statements was not the tensor product: it was the *unit*.
The twists are written in `Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product
is `Stacks.RelativeVeryAmple.tensorModules` and whose unit is `Stacks.Ample.unitModule`, both on
the nose, while `mulRight` is written in `Stacks.SheafInternalHom.monoidalCategory`, whose unit is
the sheafification of the presheaf unit
(`Stacks.SectionProduct.monoidalUnit_eq_sheafify_unit`, by `rfl`) and is therefore *not*
definitionally `Stacks.Ample.unitModule X`: elaborating `mulRight M σ` at
`σ : Stacks.Ample.unitModule X ⟶ L` is an application type mismatch, which
`Stacks.SectionProduct.ofUnitHom` repairs, and the two right unitors are different morphisms,
which is the part that needed a lemma.

*That lemma is three steps, and its hard half is already in the library.* The comparison of the
two localized right unitors does not require opening up
`CategoryTheory.Localization.Monoidal`'s unitor construction: Mathlib's
`CategoryTheory.Monoidal.Localization.rightUnitor_hom_app` writes a localized
right unitor as `X ◁ ε.inv ≫ μ.hom ≫ L.map (ρ_ X).hom`, so two localizations of one functor
differing only in the unit datum `ε` differ only in that first factor — and the resulting
comparison for *these* two structures was already proved, as
`AlgebraicGeometry.rightUnitor_sheafOfModulesMonoidal_hom` in
`StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare`, together with its
consumer `AlgebraicGeometry.tensorProductRightUnitor_inv_comp_sheafifyWhiskerLeft`, which is
`mulRight` of the re-seated section read against the fixed unit constraint of [Stacks, Tag 01CU].
What remains is restating those at the *strict* structure the twists use:
`Stacks.Algebraization.whiskerLeft_eq_sheafifyWhiskerLeft`,
`Stacks.Algebraization.rightUnitor_eq_tensorProductRightUnitor` (the one identity factor between
the two statements of the unit constraint is absorbed by
`Stacks.SheafOfModules.Strict.rightUnitor_hom_aux`) and
`Stacks.Algebraization.rightUnitor_inv_comp_whiskerLeft`, each a term of two or three
applications.

*The monicity on the closed-fibre member is that same corollary one scheme over, and it is now
stated:* `Stacks.Algebraization.CoherentTriple.mono_onClosedFibre_mulSectionTwistZ` in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoClosedFibre` is
`Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme` at `closedFibre A f` and
`σ₀`, the closed fibre being `Spec(A/fA)` and therefore locally Noetherian. What it asks for is
the nonvanishing of `σ₀` near every point of `Ass(T.F₀)`. At the **closed point** this
hypothesis has a producer, and it is not the
section pair: `Stacks.Algebraization.exists_mem_maximalIdeal_nonvanishing_smul_pow` chooses its
multiplier `g` inside `𝔪`, so `g` vanishes at the closed point and no power of it can be made
nonvanishing there. The producer is the *opening reduction* of this same clause list, which is
where the source puts it: the triple being twisted is the quotient `T'` by the sections of `F₀`
supported at the closed point, and
`Stacks.Algebraization.CoherentTriple.not_isAssociatedPoint_closedPoint_quotientTriple` says the
closed point is not an associated point of it. Hence
`Stacks.Algebraization.CoherentTriple.mono_onClosedFibre_mulSectionTwistZ_quotientTriple`, which
asks for nonvanishing only away from the closed point -- that is, over the punctured closed
fibre, where `σ₀` corresponds to `σ` and the section pair does speak.

Two further inputs complete the closed-fibre member: the transfer of `Ass(T.F₀)` over the
punctured closed fibre across `T.alpha` to the `Ass(T.F / f T.F)` the section already avoids,
and the identification of `Stacks.NonvanishingOpen.nonvanishingOpen` with
`Stacks.SheafOfModules.nonvanishingLocus` on the punctured spectrum. The spelling identification is
`StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.UnitHom`, and the transfer is
`Stacks.Algebraization.isAssociatedPoint_cokernel_of_isAssociatedPoint_F₀_quotientTriple` in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleAssociatedPointsTransfer`: the point
goes across the open immersion of the punctured closed fibre by
`Stacks.Algebraization.isAssociatedPoint_pullback_open_iff`, across `alpha` by
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr`, and down the
punctured closed immersion by `Stacks.Divisors.isAssociatedPoint_pullback_iff_quotient` read
with the two stalk computations
`Stacks.Algebraization.ker_stalkMap_puncturedClosedImmersion` (the kernel of the stalk map is the
ideal of the germ of `f`) and
`Stacks.Algebraization.isAssociatedPoint_cokernel_smulPowHom_one_iff` (the stalk of `F / f F` is
`F_q / f F_q`). So the closed-fibre monicity is unconditional:
`Stacks.Algebraization.exists_sectionPair_mono_quotientTriple` produces one section pair for
which multiplication by it on the quotient triple is monic on *both* members and has
`f`-torsion-free cokernel on the punctured spectrum, with no hypothesis beyond quasi-coherence of
the tensor products and a trivialization of each member of `L`.

What the clause owed beyond that was not about the section or its nonvanishing at all: it was the
single-`G` identification, discussed below, and it is now discharged.

*The `f`-torsion-freeness is that same monicity once more, one quotient down, and the snake
lemma that says so is now built.* The snake lemma applied to multiplication by `f` on
`0 → F → F ⊗ L → G → 0`, whose two outer terms are `f`-torsion-free, leaves
`0 → G[f] → F/fF → (F ⊗ L)/f(F ⊗ L)`, so the `f`-torsion of `G` is the kernel of the map the
*same section* induces on `F/fF`. That is why the section is chosen off `Ass(F) ∪ Ass(F/fF)` and
not merely off `Ass(F)`, and both halves of that union are what
`Stacks.Algebraization.exists_section_nonvanishing_on_associatedPoints` already delivers.

`Stacks.Algebraization.IsFTorsionFree` is a condition on the *sections over every open*, which
the module-level `Module.linearMapSnakeInput` does not reach directly; turning it into the
vanishing of a kernel is short:
`Stacks.Algebraization.isFTorsionFree_iff_mono_smulPowHom` in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeSnake` says
`f`-torsion-freeness *is* monicity of multiplication by `f`, because multiplication by a global
section is a morphism of sheaves of modules
(`Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom`) and a morphism of sheaves of
modules is monic exactly when it is injective on sections over every open. The snake input itself
is `Stacks.Algebraization.smulSnakeInput`, `Module.linearMapSnakeInput`'s construction carried
out in the abelian category of `𝒪_X`-modules, and
`Stacks.Algebraization.mono_smulPowHom_cokernel_of_mono` is the step: with `δ` monic because the
zeroth row's middle term vanishes, monicity of `F/fF ⟶ (F ⊗ L)/f(F ⊗ L)` forces `δ = 0` and hence
`G[f] = 0`. Packaged for the clause as
`Stacks.Algebraization.isFTorsionFree_cokernel_of_mono`.

*The hypothesis of that step is also discharged, and both of the identifications it needed were
already in the repository.* They are in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeTensor`, and the clause
itself is
`Stacks.Algebraization.CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ`
there (with
`...CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ_of_nonvanishing`
reading its hypothesis back to `Ass(F/fF)`, the second half of the union the section is chosen
off). The map the step asks about is `(Stacks.Algebraization.smulSnakeInput φ c).L₃.f`, a
cokernel taken in `ShortComplex` rather than `CategoryTheory.Limits.cokernel.map` of the two
multiplications, and what the snake produces concerns `(F ⊗ L^{⊗ n})/f(F ⊗ L^{⊗ n})` whereas the
available nonvanishing is about `Ass(F/fF)`. Neither gap is a real obstacle:

* no `CategoryTheory.IsColimit.coconePointUniqueUpToIso` bookkeeping is needed, because
  `Stacks.Algebraization.mono_of_isColimit_cokernelCofork` says once and for all that monicity
  of the map induced on two cokernels does not depend on the presentations it is read through;
* and exactness of `- ⊗ L^{⊗ n}` is available at this spelling of the tensor product. The
  functor spelling of the twists' tensor product is
  `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules` by `rfl`, and that
  functor is `AlgebraicGeometry.SheafOfModules.sheafTensorRight X.sheaf` by `rfl`, so right
  exactness is `Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits`
  — [Stacks, Tag 05NB], with no hypothesis on `L` — and its commutation with multiplication by
  `f` is `AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`.
  Invertibility of `L`, which would give exactness through the equivalence of
  [Stacks, Tag 0FFM] (`CategoryTheory.MonoidalCategory.HasInverse.tensorRightEquivalence`, and
  `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules_preservesFiniteColimits`
  at the scheme spelling), is not needed.

The monicity those identifications feed is `mono_tensorModulesMap_id_mulSectionPowScheme` with
`F` replaced by `F/fF`, as expected.

The last of those three is **not avoidable by restructuring this clause**, and that is worth
recording because the shape of the clause suggests it. Asking instead for a *family*
`G : ℤ → CoherentTriple A f` — one quotient per degree, which is what the cokernel machinery
produces — breaks the induction below at `ih e _ G _`: the induction hypothesis applied to a
family gives one polynomial per member, whereas
`Stacks.Algebraization.exists_polynomial_eulerCharacteristic_of_shortExact_succ` needs a single
`Q` with `χ(G n) = Q.eval n`. Carrying the step along as a hypothesis about families, so that it
can be reapplied to the quotient family (a `StepChain` recursing on the dimension bound, which is
well founded), does not help either: the step chooses a *new* section at each level, so the next
level needs a monomorphism `G n ⟶ G (n + 1)`, and multiplication by a section of `L` only gives
`G n ⟶ G n ⊗ L`. Every formulation therefore needs `G n ⊗ L ≅ G (n + 1)`, i.e. the successor
identification of the twists; the clause has to be *discharged*, not reshaped.

At the level of modules that identification is built:
`Stacks.Algebraization.tensorModulesSuccIso` in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor`, together with
`Stacks.Algebraization.whiskerLeft_mulSectionPowScheme`, which reads the member of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` through it as multiplication of a single
module by the section. The compatibility of
`Stacks.Algebraization.IsInvertibleTriple.alphaPow` with that successor comparison -- the square
that makes the comparison an identification of *triples* rather than of each member separately --
is now `Stacks.Algebraization.alphaPow_tensorPowSchemeSuccIso`, in the same file, assembled from
the two squares of the two factors of `alphaPow`:
`Stacks.Algebraization.pullbackTensorPowSchemeIso_tensorPowSchemeSuccIso` for the inverse-image
comparison and `Stacks.Algebraization.tensorPowSchemeCongr_tensorPowSchemeSuccIso` for the
comparison of the powers of two isomorphic modules.

The step from that square to the compatibility square of the *triples* needed the *associator*:
`Stacks.Algebraization.tensorModulesSuccIso` is the associativity constraint followed by the
successor comparison, so the compatibility square of the triple needs the coherence of
[Stacks, Tag 01CD] with the associator as well. That coherence is available at the scheme
spelling the twists are written in, as
`Stacks.Algebraization.pullbackTensorModulesIso_associator`, and with the naturality of the
comparison in its second variable,
`Stacks.Algebraization.pullbackTensorModulesIso_whiskerLeft`, it composes to
`Stacks.Algebraization.pullbackTensorModulesIso_assoc_whiskerLeft`, which carries the whole
shape of `Stacks.Algebraization.tensorModulesSuccIso` across the inverse image. Its source is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator`, reached because
`Stacks.PullbackGradedAlgebra.monoidalCategory`, the structure that statement is about, *is*
`Stacks.SheafOfModules.Strict.monoidalCategory` — by `rfl`, as
`Stacks.PullbackGradedAlgebra.monoidalCategory_eq` records. (The route through
`Stacks.PullbackSheafTensor.sheafTensorComparison_associator` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree` is therefore not
needed.)

That pasting is **done**. Between the square and the identification of triples lies an
elaboration obstacle -- the two routes around the square of a coherent triple carry
syntactically different instance terms for `Stacks.SheafOfModules.Strict.monoidalCategory` on
the modules of the punctured closed fibre, which exhausts the heartbeat budget when they are
compared. The three rearrangements the pasting needs are
`Stacks.Algebraization.assoc_whiskerLeft_tensorHom_of_succ_square`,
`Stacks.Algebraization.whiskerRight_tensorHom_comp_whiskerRight` and
`Stacks.Algebraization.comp_eq_of_outer_squares`, and the obstacle is routed around by never
writing down the expensive expected type, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor` record, and the
assembled square is `Stacks.Algebraization.alpha_twistZ_tensorModulesSuccIso`. It is packaged as
the morphism of coherent triples
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccHom`,
`(T ⊗ L^{⊗ n}) ⊗ L ⟶ T ⊗ L^{⊗ (n + 1)}`, both of whose members are isomorphisms by
`Stacks.Algebraization.CoherentTriple.isIso_tensorInvertibleTwistZSuccHom` -- a `Hom` whose two
members are isomorphisms being what stands in for an isomorphism of triples, there being no
`Iso` for them.

What the clause owed beyond that identification was the identification of the quotients in
the separate degrees with the twists of **one** `G`, and that reduces to a single swap of two
tensor factors. There are two routes: the degree-one route, through a degree-one morphism of
triples `T ⟶ T ⊗ L` and a comparison of the two orders `(T ⊗ L) ⊗ L^{⊗ n}` and
`(T ⊗ L^{⊗ n}) ⊗ L` composed with `Stacks.Algebraization.CoherentTriple.ShortExact.twistZ`, and
the degree-`n` route, which moves only the *third* term of the sequence, as
`Stacks.Algebraization.CoherentTriple.ShortExact.compIso` does, whereas the degree-one route
moves the first and the middle. *Both* routes need the swap. **The clause is closed by the
degree-one route**, and the two transports it needs are three lines each:
`Stacks.Algebraization.CoherentTriple.ShortExact.isoComp` (first term) beside `compIso`, and
`Stacks.Algebraization.CoherentTriple.ShortExact.midIso` (middle term) in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistHom`, where it has to live
because it is the one of the three that consumes
`Stacks.Algebraization.CoherentTriple.Hom.inverse`. What the degree-one route saves is far
larger: twisting is exact, so one sequence twisted gives every degree at once, and the quotient
of the degree-`n` multiplication never has to be identified with the `n`-th twist of a fixed
quotient -- a different identification in each degree.

Concretely, in the degree-`n` route the quotient comes out one factor better than the
`(T ⊗ L) ⊗ L^{⊗ n}` one might expect, and the lemma that says so is:
`Stacks.Algebraization.whiskerLeft_mulSectionPowScheme` writes the punctured-spectrum member of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` as a right unitor, then
`(T.F ⊗ L^{⊗ n}) ◁ σ`, then `Stacks.Algebraization.tensorModulesSuccIso` -- the outer two being
isomorphisms. So the cokernel is `(T.F ⊗ L^{⊗ n}) ⊗ Q` with `Q` the cokernel of `σ`, while
`G ⊗ L^{⊗ n}` asks for `(T.F ⊗ Q) ⊗ L^{⊗ n}`: what is owed is exactly
`(T ⊗ L^{⊗ n}) ⊗ Q ≅ (T ⊗ Q) ⊗ L^{⊗ n}`, an associator, the braiding of `L^{⊗ n}` with `Q`
whiskered into `T`, and an associator back, *as a morphism of triples* -- i.e. with the
compatibility square of each of the three.

The associator's square is
`Stacks.Algebraization.pullbackTensorModulesIso_associator`, and the braiding's is
`Stacks.Algebraization.pullbackTensorModulesIso_braiding`, in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistBraiding` -- the same single
term, from `Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding` through
`Stacks.PullbackGradedAlgebra.monoidalCategory_eq`, exactly as this note predicted. What it did
not predict is the one thing that had to be found first: the statement has to be made at the
braiding *of* `Stacks.Algebraization.strictModulesMonoidal`, and no such instance existed; it is
`Stacks.Algebraization.strictModulesBraided`, declared beside it. Note that it is `β_` and not
`Stacks.Algebraization.tensorModulesBraidingIso` that the coherence lands on, and those are two
different morphisms rather than two spellings of one -- see that file's implementation notes --
though under `strictModulesMonoidal` the tensor product *is*
`Stacks.RelativeVeryAmple.tensorModules` on the nose, so a consumer loses nothing by staying at
`β_`.

The three compatibility squares and the morphism of triples assembled from them are:
`Stacks.Algebraization.CoherentTriple.twistZTensorInvertibleBraidHom`,
`(T ⊗ L^{⊗ n}) ⊗ Q ⟶ (T ⊗ Q) ⊗ L^{⊗ n}`, and its composite with the successor identification,
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccDegreeOneHom`,
`(T ⊗ L) ⊗ L^{⊗ n} ⟶ T ⊗ L^{⊗ (n + 1)}` -- which is the identification the *middle* term of the
twisted degree-one sequence needs, and the only term of that sequence that has to move.

The degree-zero end of the degree-one sequence is
`Stacks.Algebraization.CoherentTriple.twistZZeroHom`,
`T ⊗ L^{⊗ 0} ⟶ T`, in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistZero`: the degree-zero tensor
power of an invertible module **is** the structure sheaf (an equality by `rfl`), so the two
members are the right unitors, and the compatibility square is one more coherence of
[Stacks, Tag 01CD] at the scheme spelling,
`Stacks.Algebraization.pullbackTensorModulesIso_rightUnitor`, read against the degeneration of
`Stacks.Algebraization.IsInvertibleTriple.alphaPow` in degree zero,
`Stacks.Algebraization.alphaPow_zero`. The degree-one end,
`Stacks.Algebraization.CoherentTriple.twistZOneHom`, `T ⊗ L^{⊗ 1} ⟶ T ⊗ L`, needs nothing new: it
is the successor identification at `n = 0` inverted, composed with `twistZZeroHom` tensored
with `L`.

The transports the clause consumes are therefore all three of
`Stacks.Algebraization.CoherentTriple.ShortExact.isoComp`,
`...ShortExact.midIso` and -- not in this chain, but available --
`...ShortExact.compIso`; and the Euler characteristic is an invariant of the isomorphism class by
`Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom`.

The section itself is *not* an obstacle: [Stacks, Tag 0F20] is proved outright, with no
hypotheses beyond quasi-affineness and invertibility, as
`Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite`
(`StacksFrontier/AlgebraicGeometry/QuasiAffineGlobalGeneration/Basic.lean`), and the punctured
spectrum of a Noetherian local ring is quasi-affine by
`Stacks.Algebraization.isQuasiAffine_puncturedSpectrum`. The conditional restatement in
`StacksFrontier/AlgebraicGeometry/QuasiAffineFiniteNonvanishing/Basic.lean`, which carries global
generation and [Stacks, Tag 01PV] as hypotheses, is an earlier route and not the state of the
repository. What the clause still owes about the section is the *pair*: a global section of each
member of the invertible triple, corresponding over the punctured closed fibre -- that is, a
morphism of coherent triples out of `Stacks.Algebraization.CoherentTriple.unit` -- and the
source's omitted adjustment by an element of the maximal ideal which makes the two correspond.

Only the *successor* degree is reachable this way, and that is the degree the induction uses. The
full addition law `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` with its associativity, commutativity and
unit constraints does exist, as `Stacks.SheafOfModules.TensorPower.coherentMulIso` and the five
laws beside it in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence` — so the note under
"What is not done" in `StacksFrontier.AlgebraicGeometry.TensorPowers.Monoidal`, which says the
constraints of *its* addition law are not proved, is about that other construction and does not
describe the library. But `coherentMulIso` is a `Classical.choice` of a coherence datum, chosen
independently on the two members of the invertible triple, so it carries no compatibility with
the inverse-image comparison and cannot be used for `alphaPow`; in degree `(n, 1)` it is
identified with the canonical successor comparison by
`Stacks.SheafOfModules.TensorPower.coherentMulIso_one_right`, which is the route back.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace Stacks.Algebraization

/-! ### The geometric input of the induction step -/

/-- **The geometric input of the induction step of [Stacks, Tag 0F27].** For every coherent
triple `T = (F, F₀, α)` whose punctured-spectrum member has nonempty support it asks for

* a short exact sequence `0 → K → T → T' → 0` of coherent triples whose left member has
  vanishing punctured-spectrum member — the source's replacement of `F₀` by its quotient by the
  submodule of sections supported at the closed point;
* a coherent triple `G` and, for every integer `n`, a short exact sequence
  `0 → T' ⊗ L^{⊗ n} → T' ⊗ L^{⊗ n+1} → G ⊗ L^{⊗ n} → 0` — the source's sequence attached to a
  section of `L` not vanishing at the associated points of `F` and of `F/fF`;
* that the support of `G` has dimension at least one less than that of `F`, in the two forms the
  induction consumes;
* and that **when `Supp F` is zero-dimensional** a `G` with vanishing punctured-spectrum member
  has vanishing Euler characteristic, which is what makes the degree bound sharp at the bottom of
  the induction.

The dimension hypothesis on the last clause is the source's own, and it is load-bearing: without
it the clause is false, and a witness is recorded in the implementation notes below. The
induction only ever applies the clause at the bottom of the recursion, where that hypothesis is
in hand. -/
public def HasHilbertInductionStep {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {f : A} (L : CoherentTriple A f) (hL : IsInvertibleTriple L) : Prop :=
  ∀ T : CoherentTriple A f, SheafOfModules.supp T.F ≠ ∅ →
    ∃ (K T' G : CoherentTriple A f) (φ : K.Hom T) (ψ : T.Hom T')
      (u : ∀ n : ℤ, (T'.twistZ L hL n).Hom (T'.twistZ L hL (n + 1)))
      (v : ∀ n : ℤ, (T'.twistZ L hL (n + 1)).Hom (G.twistZ L hL n)),
      IsZero K.F ∧ CoherentTriple.ShortExact φ ψ ∧
      (∀ n : ℤ, CoherentTriple.ShortExact (u n) (v n)) ∧
      (∀ e : ℕ, topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim ↥(SheafOfModules.supp G.F) ≤ ((e : ℕ) : WithBot ℕ∞)) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        SheafOfModules.supp G.F = ∅) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        IsZero G.F → G.eulerCharacteristic = 0)

/-! ### A function on the integers with equal consecutive values -/

/-- A function on the integers whose consecutive values agree is constant. -/
public theorem eq_of_forall_succ_eq {g : ℤ → ℤ} (h : ∀ n : ℤ, g (n + 1) = g n) (n : ℤ) :
    g n = g 0 := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [h (k : ℤ)]; exact ih
  | pred k ih =>
    have h' := h (-(k : ℤ) - 1)
    rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at h'
    rw [← h']; exact ih

/-! ### The induction -/

/-- **The induction of [Stacks, Tag 0F27] on the dimension of the support.** Given the geometric
input of the induction step, a natural number bounding the dimension of the support of the
punctured-spectrum member of a coherent triple bounds the degree of a rational polynomial
computing the Euler characteristics of all of its integer twists. -/
public theorem exists_polynomial_eulerCharacteristic_twistZ_of_hasInductionStep {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (hstep : HasHilbertInductionStep L hL) :
    ∀ (d : ℕ) (T : CoherentTriple A f),
      topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((d : ℕ) : WithBot ℕ∞) →
      ∃ P : Polynomial ℚ, P.natDegree ≤ d ∧
        ∀ n : ℤ, (((T.twistZ L hL n).eulerCharacteristic : ℤ) : ℚ) = P.eval (n : ℚ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro T hT
    by_cases hsupp : SheafOfModules.supp T.F = ∅
    · obtain ⟨P, hP, hPn⟩ := exists_polynomial_eulerCharacteristic_twistZ_of_isZero hf T L hL
        (Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty T.F hsupp)
      exact ⟨P, hP.le.trans (Nat.zero_le d), hPn⟩
    obtain ⟨K, T', G, φ, ψ, u, v, hK, hse, hseq, hdrop, hdrop₀, hvanish⟩ := hstep T hsupp
    rcases d with _ | e
    · -- the bottom of the induction: the quotient's support is empty, so the first difference of
      -- the function vanishes identically and the function is constant
      have hz := Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty G.F
        (hdrop₀ hT)
      have hconst : ∀ n : ℤ, (T'.twistZ L hL (n + 1)).eulerCharacteristic =
          (T'.twistZ L hL n).eulerCharacteristic := fun n => by
        rw [CoherentTriple.eulerCharacteristic_add_of_shortExact hf (hseq n),
          G.eulerCharacteristic_twistZ_eq_of_isZero hf L hL hz n, hvanish hT hz, add_zero]
      refine exists_polynomial_eulerCharacteristic_twistZ_of_shortExact_isZero hf hse hK L hL
        (d := 0) (P := Polynomial.C
          (((T'.twistZ L hL 0).eulerCharacteristic : ℤ) : ℚ))
        (Polynomial.natDegree_C _).le fun n => ?_
      rw [eq_of_forall_succ_eq
        (g := fun m : ℤ => (T'.twistZ L hL m).eulerCharacteristic) hconst n]
      simp
    · -- above the bottom the induction hypothesis handles the quotient, whatever its support
      obtain ⟨Q, hQ, hQn⟩ := ih e (Nat.lt_succ_self e) G (hdrop e hT)
      obtain ⟨P', hP', hP'n⟩ := exists_polynomial_eulerCharacteristic_of_shortExact_succ hf
        (fun n => T'.twistZ L hL n) (fun n => G.twistZ L hL n) u v hseq hQ hQn
      exact exists_polynomial_eulerCharacteristic_twistZ_of_shortExact_isZero hf hse hK L hL
        hP' hP'n

/-! ### The degree bound at the source's spelling -/

/-- An element of `WithBot ℕ∞` other than `⊤` is bounded by a natural number, and that natural
number can be taken to be its own truncation at `0`. -/
public theorem exists_natCast_le_and_eq_max_zero {x : WithBot ℕ∞} (hx : x ≠ ⊤) :
    ∃ d : ℕ, x ≤ ((d : ℕ) : WithBot ℕ∞) ∧ ((d : ℕ) : WithBot ℕ∞) = max 0 x := by
  induction x using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le, by simp⟩
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd (by rfl) hx
    | coe k => exact ⟨k, by simp, by simp⟩

/-- **The Krull dimension of a subset of the punctured spectrum of a Noetherian local ring is
finite**, being bounded by the Krull dimension of the ring. -/
public theorem topologicalKrullDim_ne_top_of_subset_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (s : Set (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    topologicalKrullDim ↥s ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_
    (le_trans (topologicalKrullDim_subspace_le _ s)
      (topologicalKrullDim_subspace_le (PrimeSpectrum A) _))
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_ne_top

/-- **[Stacks, Tag 0F27] at the source's spelling of the degree bound**, from the geometric input
of the induction step: the Euler characteristics of the integer twists of a coherent triple are
given at every integer by a rational polynomial whose degree is at most the dimension of the
support of the punctured-spectrum member, truncated at `0`.

The truncation is the convention the source's own "more precisely" paragraph supplies: a triple
with vanishing punctured-spectrum member, whose support has dimension `-∞`, has a *constant*
function, not the zero function. -/
public theorem exists_polynomial_natDegree_le_dim_supp_of_hasInductionStep {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (hstep : HasHilbertInductionStep L hL) (T : CoherentTriple A f) :
    ∃ P : Polynomial ℚ,
      (P.natDegree : WithBot ℕ∞) ≤ max 0 (topologicalKrullDim ↥(SheafOfModules.supp T.F)) ∧
        ∀ n : ℤ, (((T.twistZ L hL n).eulerCharacteristic : ℤ) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨d, hd, hdmax⟩ := exists_natCast_le_and_eq_max_zero
    (topologicalKrullDim_ne_top_of_subset_puncturedSpectrum A (SheafOfModules.supp T.F))
  obtain ⟨P, hP, hPn⟩ := exists_polynomial_eulerCharacteristic_twistZ_of_hasInductionStep hf
    L hL hstep d T hd
  refine ⟨P, ?_, hPn⟩
  rw [← hdmax]
  exact_mod_cast hP

end Stacks.Algebraization

end
