module

public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.SupportBounds
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Integral
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree on a scheme of dimension at most one is a sum over its components

Let `k` be a field, let `f : X ⟶ Spec k` be proper with `topologicalKrullDim X ≤ 1` and let `ℰ`
be a finite locally free `𝒪_X`-module of rank `n`. Stacks 0AYW asserts

  `deg(ℰ) = ∑ᶠ ξ, m(ξ) · deg(ℰ|_{C(ξ)})`,

the sum running over the generic points of the one-dimensional irreducible components of `X`,
with `C(ξ)` the component with its reduced induced structure and `m(ξ)` its multiplicity, the
length of the local ring of `X` at `ξ`. This file proves that equation from the two paragraphs
of the source argument: the degree is the sum of the degrees on a finite family of closed
subschemes covering the components, and on each such subscheme the degree is the multiplicity
times the degree on the reduced component.

The equation itself, with no hypothesis, is
`Stacks.AlgebraicGeometry.ComponentDegrees.curveDegree_eq_finsum_componentDegree_of_isProper`
in `ComponentMultiplicity/Unconditional.lean`, by the dévissage route described below; what
this file records is the source's own argument, each form of it carrying as hypotheses the
inputs of the two paragraphs it is run from.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.ComponentDegrees`.

* `curveDegree_eq_finsum_componentDegree` — the component formula, from the two steps as
  hypotheses.
* `exists_curveDegree_eq_finsum` — the same in the existential form the source states, the three
  proof obligations the conclusion carries being supplied.
* `curveDegree_eq_sum_componentDegree` — the same with the locally finite sum read as a finite
  sum over the components.
* `curveDegree_eq_finsum_componentDegree_of_stalk_bijective` — the component formula with the
  first step replaced by its own input: the finite family and the stalkwise bijectivity of
  `𝒪_X ⟶ g_*𝒪_{X'}` away from a finite set of closed points. Stacks 02O6 is no longer assumed
  here.

## Implementation notes

**The two steps, and which of their inputs are unlanded.** The first step is the reduction to
the irreducible case: `X` is replaced by the disjoint union of the scheme-theoretic closures
`Xᵢ` of the complements of the other components, which changes no degree because the comparison
map `𝒪_X ⟶ g_*𝒪_{X'}` is an isomorphism on the local rings at the generic points of the
one-dimensional components. That reduction is
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective`, and it is
used here; what it still carries is the geometric statement that the comparison map attached to
the family is bijective on stalks off a finite set of closed points. Its other input, the finite
dimensionality of coherent cohomology on a proper scheme over a field — Stacks 02O6 — is no
longer a hypothesis of anything below: it is supplied by
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`. The second step is
the induction on the least `e` with `ℐ^{e+1} = 0`, for `ℐ` the ideal of the reduction; its
arithmetic is
`AlgebraicGeometry.curveDegree_eq_mul_of_shortExact_pushforward_of_isCurve`, which now assumes
neither Stacks 02O6 nor Stacks 0AYV, the latter being
`exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve`.
What the step still needs and the library does not have is the short exact sequence
`0 ⟶ ℐ^e ⟶ 𝒪_X ⟶ 𝒪_{X'} ⟶ 0` — the ideal of the reduction, its powers, the subschemes they cut
out and the nilpotence of Stacks 01Y9 — together with the length identity `m = r + m'` at the
generic point. That is what the hypothesis `hirreducible` stands for, and it is the only
remaining content of the second step.

**The family may be larger than the set of one-dimensional components**, and on a scheme with an
isolated point it must be: `Spec k ⊔ 𝐏¹_k` is proper of dimension at most one, and the
comparison map of a family missing the isolated point is not bijective on the stalk there. So
`σ` is an injection of the one-dimensional components into the family rather than a bijection,
and the remaining members are required to contribute nothing — which is clause (5) of
Stacks 0AYT at their structure sheaves, by
`AlgebraicGeometry.curveDegree_eq_zero_of_eulerCharacteristic_unit_tensorSheaf_eq`.

**`hzero` cannot be discharged at this shape, and not for want of an input.** `σ` is an
arbitrary injection `genericPointsOne X ↪ Fin N`; nothing here ties `σ ξ` to a member of the
family that *contains* `ξ`. A member `Zs j` outside the image of `σ` may therefore be a
one-dimensional component of `X` carrying a nonzero degree, with `σ` enumerating the components
in some unrelated way, and the stalk hypothesis `hbij` does not exclude it. What does exclude it
is the family the source constructs, where `Xᵢ` is attached to `Cᵢ` by construction: at a
generic point `η` of a one-dimensional component the stalk of `g_*𝒪_{X'}` is the direct sum of
the `𝒪_{Zs j, η}` over the members through `η`, so bijectivity at `η` — which holds, `η` being
non-closed and `Z` a set of closed points — forces exactly one member through `η`, and that
member is `Xᵢ`. So `hzero` goes with `hreduce`: both are discharged by constructing the family,
not by supplying a further hypothesis to this statement.

**The two-paragraph route above is not the only one, and it is not the cheapest.** The source's
paragraph 1 — replace `X` by the disjoint union of the scheme-theoretic closures `Xᵢ` — is only
one way to reach the formula, and it is the way that forces the family, the stalk bijectivity
and `hzero` above. There is a second route, which never mentions the `Xᵢ` and never needs an
`hreduce`: **dévissage of `𝒪_X` itself**, by [Stacks, Tag 01YF]. That tag is proved, at
`Stacks.AlgebraicGeometry.CoherentDevissage.exists_filtration_by_integral_ideal_pushforwards`,
in the shape

`⊥ = G 0 ⊆ ⋯ ⊆ G n = ⊤`,  `G (j+1) / G j ≅ (iⱼ)_*ℐⱼ`,  `iⱼ : Zⱼ ⟶ X` closed immersion,
`Zⱼ` integral, `ℐⱼ ⊆ 𝒪_{Zⱼ}` a nonzero coherent ideal,

and the formula follows from it in four steps, every one of whose geometric inputs is already
in the library:

1. `D(𝒪_X) = deg(ℰ)` for `D = ` `AlgebraicGeometry.eulerCharacteristicTensorSheafSub`, from
   `AlgebraicGeometry.eulerCharacteristic_unit_tensorSheaf` and
   `AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub`;
2. `D` is additive along the filtration, which is
   `AlgebraicGeometry.eulerCharacteristicTensorSheafSub_eq_add_sum_of_filtration` after the
   `Fin (n+1)`-indexed chain of subobjects is reindexed by `ℕ`;
3. per layer, `D((iⱼ)_*ℐⱼ) = ∑ᶠ ξ, len_ξ((iⱼ)_*ℐⱼ) · deg(ℰ|_{C(ξ)})`. For
   `dim Zⱼ ≤ 0` both sides vanish — the left by clause (5) of [Stacks, Tag 0AYT] at a
   zero-dimensional support, the right by
   `Stacks.AlgebraicGeometry.ComponentDegrees.stalkLength_eq_zero_of_notMem_range`. For
   `dim Zⱼ = 1`, `Zⱼ` is an integral curve, so
   `AlgebraicGeometry.eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion` moves
   both Euler characteristics onto `Zⱼ`, the hypothesis-free [Stacks, Tag 0AYV]
   (`exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve`)
   evaluates the difference as `r·deg(ℰ|_{Zⱼ})` with `r` the fibre rank of `ℐⱼ` at the generic
   point, and `exists_isIso_hom_to_reducedComponent` identifies `Zⱼ` with `C(ξ)` over `X`;
4. the weights add up to the multiplicities, by
   `Stacks.AlgebraicGeometry.ComponentDegrees.stalkLength_eq_sum_of_subobject_filtration`
   applied to the same chain of subobjects at `ξ`.

Steps 1 and 2 are arithmetic. Steps 3 and 4 each need the **same single identification**: that
`Stacks.AlgebraicGeometry.ComponentDegrees.stalkLength F x`, the length of `ℱ_x` over the
`RingCat`-valued stalk of the structure sheaf, equals the length over the `CommRingCat`-valued
one. That identification is proved as
`Stacks.AlgebraicGeometry.ComponentDegrees.stalkLength_eq_length_grpStalk` in
`ComponentMultiplicity/StalkLengthBridge.lean`, together with the two statements it is used
for: step 4's weight is `componentMultiplicity_eq_sum_stalkLength_of_filtration` — along a
finite monotone chain of subobjects of `𝒪_X` from `⊥` to `⊤` the sum at `ξ` of the lengths of
the successive quotients is `componentMultiplicity X ξ` — and step 3's is
`stalkLength_eq_fiberRank_genericPoint`, the length at the generic point of an integral scheme
read as the fibre rank there. Its engine is
`length_eq_of_surjective_smul_eq`, the two actions being related by the surjection
`Stacks.RingedSpace.ringStalkCommIso`; the remaining input is the germ compatibility
`φ r • m = r • m` of the two stalk module structures, and the difficulty there is that every
`rw` inside that germ computation fails with *"the target expression is
not type-correct under the `implicit` transparency level"* —
`AlgebraicGeometry.Scheme.ringCatSheaf` is reducible while `structureSheafRing` is only
`@[instance_reducible]`, so the motive does not typecheck at the transparency `rw` uses. The
proof therefore computes each side into the common value `germ_x(a • n)` by a separate `have`
and joins them with `Eq.trans`, which converts at default transparency.

**Step 3's geometry is carried out in `ComponentMultiplicity/Unconditional.lean`.** Per layer
`(iⱼ : Zⱼ ⟶ X, ℐⱼ)` of [Stacks, Tag 01YF] applied to `𝒪_X` that step is

  `D((iⱼ)_*ℐⱼ) = ∑ᶠ ξ, len_ξ((iⱼ)_*ℐⱼ) · deg(ℰ|_{C(ξ)})`

for `D =` `AlgebraicGeometry.eulerCharacteristicTensorSheafSub k f E hE rank`, and it splits as
the source's case distinction. For `topologicalKrullDim Zⱼ ≤ 0` both sides vanish: the left by
clause (5) of [Stacks, Tag 0AYT] at a zero-dimensional support, the right by
`Stacks.AlgebraicGeometry.ComponentDegrees.stalkLength_eq_zero_of_notMem_range`, the generic
point of a one-dimensional component not lying in the image of `iⱼ`. For
`topologicalKrullDim Zⱼ = 1` the scheme `Zⱼ` is an integral curve over `k`, so
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion` moves both
Euler characteristics onto `Zⱼ`, the hypothesis-free [Stacks, Tag 0AYV] evaluates the difference
as `r · deg(ℰ|_{Zⱼ})` with `r = fiberRank ℐⱼ (genericPoint Zⱼ)`,
`Stacks.AlgebraicGeometry.ComponentDegrees.exists_isIso_hom_to_reducedComponent` identifies
`Zⱼ` with `C(ξ)` over `X` for `ξ = iⱼ(genericPoint Zⱼ)`, and the two weights agree by
`stalkLength_pushforward` followed by `stalkLength_eq_fiberRank_genericPoint`. Summing the
layers against step 2 and exchanging the finite sum over `j` with the locally finite sum over
`ξ` gives the formula with no hypothesis left, which is
`curveDegree_eq_finsum_componentDegree_of_isProper`.

**Two cases of the formula are proved directly** and do not go through the dévissage at all:
`curveDegree_eq_finsum_componentDegree_of_isIntegral` for an integral scheme of dimension one,
where the sum has a single term of weight one, and
`curveDegree_eq_finsum_componentDegree_of_isInvertible_of_topologicalKrullDim_le_zero` for an
invertible module on a scheme of dimension at most zero, where both sides vanish.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.AlgebraicGeometry.ComponentDegrees

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hX : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
  [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
  (Y : genericPointsOne X → Scheme.{u}) (i : ∀ ξ, Y ξ ⟶ X)
  (hproper : ∀ ξ, IsProper (i ξ ≫ f)) (hdimY : ∀ ξ, topologicalKrullDim (Y ξ) ≤ 1)

/-- **Stacks 0AYW.** The degree of a finite locally free module of constant rank on a proper
scheme of dimension at most one over a field is the multiplicity-weighted sum of its degrees on
the reduced one-dimensional components. -/
@[stacks 0AYW "the component formula, from the two steps of the source argument"]
theorem curveDegree_eq_finsum_componentDegree
    (hreduce : curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X, @curveDegree k _ (Y ξ) (i ξ ≫ f) (hproper ξ) (hdimY ξ)
        ((Scheme.Modules.pullback (i ξ)).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ξ) E rank))
    (hirreducible : ∀ ξ : genericPointsOne X,
      @curveDegree k _ (Y ξ) (i ξ ≫ f) (hproper ξ) (hdimY ξ)
          ((Scheme.Modules.pullback (i ξ)).obj E) rank
          (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ξ) E rank) =
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ) :
    curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  rw [hreduce]
  exact finsum_congr hirreducible

/-- **Stacks 0AYW**, in the existential form the source states: each reduced one-dimensional
component is proper over the base, has dimension at most one and carries a restriction of `ℰ`
that is again finite locally free of the same rank, and the component formula holds with respect
to those three proofs. -/
@[stacks 0AYW "the existential form the source states"]
theorem exists_curveDegree_eq_finsum
    (hreduce : curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X, @curveDegree k _ (Y ξ) (i ξ ≫ f) (hproper ξ) (hdimY ξ)
        ((Scheme.Modules.pullback (i ξ)).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ξ) E rank))
    (hirreducible : ∀ ξ : genericPointsOne X,
      @curveDegree k _ (Y ξ) (i ξ ≫ f) (hproper ξ) (hdimY ξ)
          ((Scheme.Modules.pullback (i ξ)).obj E) rank
          (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ξ) E rank) =
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ) :
    ∃ (hproperC : ∀ ξ : genericPointsOne X, IsProper (reducedComponentι X ξ ≫ f))
      (hdimC : ∀ ξ : genericPointsOne X, topologicalKrullDim (reducedComponent X ξ) ≤ 1)
      (hrank : ∀ ξ : genericPointsOne X,
        _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank),
      curveDegree k f hX E rank =
        ∑ᶠ ξ : genericPointsOne X,
          (componentMultiplicity X ξ : ℤ) *
            @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
              (hproperC ξ) (hdimC ξ)
              ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank (hrank ξ) :=
  (exists_curveDegree_eq_finsum_iff k f hX E rank).2
    (curveDegree_eq_finsum_componentDegree k f hX E rank Y i hproper hdimY hreduce hirreducible)

/-- **Stacks 0AYW** with the locally finite sum read as a finite sum over the components. This is
the shape in which a consumer that already has the components as a `Fintype` uses the formula. -/
@[stacks 0AYW "the component formula as a finite sum"]
theorem curveDegree_eq_sum_componentDegree [Fintype (genericPointsOne X)]
    (hreduce : curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X, @curveDegree k _ (Y ξ) (i ξ ≫ f) (hproper ξ) (hdimY ξ)
        ((Scheme.Modules.pullback (i ξ)).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ξ) E rank))
    (hirreducible : ∀ ξ : genericPointsOne X,
      @curveDegree k _ (Y ξ) (i ξ ≫ f) (hproper ξ) (hdimY ξ)
          ((Scheme.Modules.pullback (i ξ)).obj E) rank
          (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ξ) E rank) =
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ) :
    curveDegree k f hX E rank =
      ∑ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  rw [curveDegree_eq_finsum_componentDegree k f hX E rank Y i hproper hdimY hreduce hirreducible,
    finsum_eq_sum_of_fintype]


/-! ### The first paragraph of the source proof discharged -/

/-- **Stacks 0AYW**, with the first paragraph of the source proof discharged from the
reduction to a finite family of closed subschemes.

The family `Zs` is the source's `Xᵢ`, the scheme-theoretic closures of the complements of the
other components, enumerated by `0, …, N - 1`; `σ` picks out the member attached to a given
one-dimensional component, and `hzero` says the remaining members — the zero-dimensional
components — contribute nothing. -/
@[stacks 0AYW "the component formula, from the reduction to the irreducible case"]
theorem curveDegree_eq_finsum_componentDegree_of_stalk_bijective
    {Zs : ℕ → Scheme.{u}} (ι : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (ι j)] (N : ℕ)
    (σ : genericPointsOne X → Fin N) (hσ : Function.Injective σ)
    (Z : Set X) (hZfin : Z.Finite) (hZcl : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hbij : ∀ x ∉ Z, Function.Bijective (ConcreteCategory.hom
      ((_root_.AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map
        (Scheme.Modules.pushforwardUnitSeriesMap ι N))))
    (hirreducible : ∀ ξ : genericPointsOne X,
      @curveDegree k _ (Zs (σ ξ)) (ι (σ ξ) ≫ f) _
          (le_trans (IsClosedImmersion.isClosedEmbedding
            (ι (σ ξ))).isInducing.topologicalKrullDim_le hX)
          ((Scheme.Modules.pullback (ι (σ ξ))).obj E) rank
          (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (ι (σ ξ)) E rank) =
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ)
    (hzero : ∀ j : Fin N, (∀ ξ : genericPointsOne X, σ ξ ≠ j) →
      @curveDegree k _ (Zs j) (ι j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (ι j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (ι j)).obj E) rank
        (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (ι j) E rank) = 0) :
    curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  classical
  have hfinite : Finite (genericPointsOne X) :=
    (finite_genericPointsOne_of_isProper k f).to_subtype
  let _ : Fintype (genericPointsOne X) := Fintype.ofFinite _
  rw [_root_.AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective
      k f ι hX E rank N Z hZfin hZcl hbij
      (_root_.AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper k f),
    finsum_eq_sum_of_fintype, ← Fin.sum_univ_eq_sum_range]
  refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.image σ)) ?_).symm.trans ?_
  · intro j _ hj
    exact hzero j fun ξ hξ => hj (Finset.mem_image.mpr ⟨ξ, Finset.mem_univ ξ, hξ⟩)
  · rw [Finset.sum_image fun a _ b _ h => hσ h]
    exact Finset.sum_congr rfl fun ξ _ => hirreducible ξ

end Stacks.AlgebraicGeometry.ComponentDegrees

end
