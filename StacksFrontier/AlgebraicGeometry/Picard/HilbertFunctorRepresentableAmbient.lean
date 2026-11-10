module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness

/-!
# The Hilbert functor of points of a scheme whose fibres have enough affine opens

Let `X ⟶ S` be a morphism of schemes and let `d` be a natural number with `d ≠ 1`. If every
tuple of `d` points of a single fibre of `X ⟶ S` lies in an affine open of `X`, then the
degree-`d` Hilbert functor of points `Hilb^d_{X/S}` is representable by a scheme over `S`. That
is the proposition of Stacks Tag 0B9A verbatim, hypothesis for hypothesis, on every `d` but one:
in the namespace `Stacks.Hilbert`,
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`.

The value `d = 1` is where the tag is false. For `d ≤ 1` the source's `d`-tuple hypothesis is
vacuous for every morphism of schemes; at `d = 0` the conclusion holds anyway, `Hilb^0_{X/S}`
being `S`, but at `d = 1` it is **false** — that is a refutation, formalized here, not a gap.
The generalisation
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem`
reaches every `d`, the excluded value included, by asking instead for an affine open around
every `max d 2`-tuple of points of one fibre: for `2 ≤ d` that is the source's own hypothesis,
`max d 2 = d`, and below it the extra two-point demand is the weakest repair of the `d = 1`
case. The last section of this docstring is about that.

## Main results

* `AlgebraicGeometry.isSeparated_of_exists_isAffineOpen_pair` — if every *two* points of a single
  fibre of `f : X ⟶ S` lie in an affine open of `X`, then `f` is separated.

The remaining results are in the namespace `Stacks.Hilbert`.

* `nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`
  — **Stacks Tag 0B9A**: representability of `Hilb^d_{X/S}` by a scheme, under the `d`-tuple
  affine-open hypothesis the source states, for every `d ≠ 1`.
* `nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_two_le`
  — the same on the range `2 ≤ d`, where the argument of the source runs.
* `…_of_exists_isAffineOpen_forall_mem` — its generalisation to every `d`, under the affine-open
  hypothesis at `max d 2` points of one fibre.

## Implementation notes

*The two inputs, and where they come from.* The gluing assembly is
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_familiesClosedInAmbient`, which asks
for exactly the two things the source's proof needs of `X ⟶ S`:

* `Stacks.Hilbert.FamiliesClosedInAmbient X`, the conclusion of the source's footnote — a
  degree-`d` Hilbert family in an open `U ⊆ X` cuts out a *closed* subscheme of `X ×_S T` — which
  is what identifies the subfunctor of families supported in `U` with `Hilb^d_{U/S}` and so
  discharges condition (2)(a) of the criterion of Stacks 01JJ through the affine case Stacks
  0B99; and
* the `d`-tuple form of the fibrewise affineness hypothesis, which discharges the covering
  condition (2)(c).

Here the first input is obtained from separatedness of `X ⟶ S`
(`Stacks.Hilbert.familiesClosedInAmbient_of_isSeparated`), and separatedness is obtained from the
two-point case of the hypothesis: the opens `U ×_S U` for `U` affine cover `X ×_S X` as soon as
every two points of a fibre lie in a common affine open, and the diagonal is closed inside each
of them because an affine scheme is separated. In Lean that argument is run through the footnote
itself, applied to the diagonal `X ⟶ X ×_S X`, whose composite with the second projection is the
identity and therefore finite, and whose fibres are singletons — so the footnote's assumption
there asks for an affine open around two points and nothing more.

The source instead reduces to an affine base and takes the first input from the *set* form of the
hypothesis — an affine open around every finite set of points of a fibre — which is
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_hasAffineFinitePointsInFibres`. All
seven cases of Stacks Tag 0B9B give the set form, so no application of the tag is affected by
which route is taken.

*Why the generalisation asks for `max d 2` and not `d`: the source's hypothesis is too weak for
`d ≤ 1`.* For `2 ≤ d` the `d`-tuple form already contains the two-point form, so there `max d 2`
and `d` are the same demand and the two theorems below are the same theorem. For `d ≤ 1` the
source's form is vacuous — every point of a scheme lies in an affine open — and at `d = 0` the
proposition is true anyway, `Hilb^0_{X/S}` being `S` itself by
`Stacks.Hilbert.representsHilbertFunctorOfRankZero`. At `d = 1` the proposition as literally
stated is **false**, so the generalisation to every `d` has to strengthen the hypothesis there,
and asking for the two-point case is the weakest strengthening that works.

That is not a gap in this development but a refutation, and it is formalized:
`Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one`, in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbientNotRepresentable.lean`,
proves that no scheme represents `Hilb^1_{X/S}` for `X` the affine line with the origin doubled
and `X ⟶ S` its coordinate morphism to affine `1`-space — a morphism of schemes satisfying the
tag's hypothesis at `d = 1` vacuously, and not separated
(`AlgebraicGeometry.not_isSeparated_coordinateMorphism`).

The counterexample is the one the source's own footnote is about, and it runs as follows. Over a
base scheme `T ⟶ S`, the two charts pull back to two opens of `X ×_S T`, each isomorphic to `T`,
whose intersection is the preimage of the punctured base; so a degree-`1` family over `T` — a
closed subscheme of `X ×_S T` mapping isomorphically to `T` — cuts those two opens in two
*clopen* subsets of `T` whose intersection is the preimage of the punctured base. Hence a
degree-`1` family exists only over those `T` for which the pullback of the coordinate has clopen
vanishing locus (`Stacks.Hilbert.isClosed_preimage_basicOpen_of_hilbertFamily`), and over such a
`T` each chart gives one (`Stacks.Hilbert.doubledChartFamily`). Over the fat point
`Spec (k[y]/(yⁿ⁺¹))` the coordinate is nilpotent, so the vanishing locus is everything and both
families exist; over `S` itself the vanishing locus is the origin, which is not open, so no
family exists at all.

Now suppose `H` represented the functor. The universal family forces the vanishing locus of the
coordinate on `H` to be open, and the family of a chart is compatible with base change
(`Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap`), so the fat points
`Spec (k[y]/(yⁿ⁺¹))` are all classified by morphisms through one and the same point `h` of `H`,
lying in that open locus. On an affine open neighbourhood of `h` inside it the pulled-back
coordinate vanishes at every point, hence is nilpotent, say of order `N`; but the fat point of
order `N + 1` factors through that neighbourhood and pulls the coordinate back to `y`, forcing
`yᴺ = 0` in `k[y]/(y^{N+1})`. So `Hilb^1_{X/S}` is representable by no scheme, while the
`1`-tuple form of the tag's hypothesis holds vacuously.

(The remark in the module docstring of
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorOpenAmbient.lean` that `Hilb^1` of the
doubled line is `(𝔸¹ ∖ {0}) ⊔ Spec k ⊔ Spec k` counts only the field-valued points of the
functor; the families over the fat points above are the ones it misses, and they are what
obstructs representability. The same computation shows that the subfunctor `F_U` of families
supported in a chart is `(𝔸¹ ∖ {0})` together with the functor of nilpotents, so it is not
representable either, and condition (2)(a) of the criterion cannot be discharged for it
directly.)

So the tag's statement here takes every `d ≠ 1`, under the source's hypothesis unchanged: for
`2 ≤ d` by the argument above, and at `d = 0` because `Hilb^0_{X/S} = S` needs no hypothesis at
all (`Stacks.Hilbert.representsHilbertFunctorOfRankZero`). The `max d 2` theorem stands beside it
as the generalisation covering `d = 1` too, and at `d = 1` the tag's own statement is refuted.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B9B](https://stacks.math.columbia.edu/tag/0B9B)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Two points of a fibre in a common affine open make a morphism separated.** If for every
`s ∈ S` and every two points of the fibre of `f : X ⟶ S` over `s` there is an affine open of `X`
containing both, then `f` is separated.

The diagonal `X ⟶ X ×_S X` is always an immersion, so only its image has to be seen to be
closed; and that is the footnote to the proof of Stacks Tag 0B9A
(`Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism`) applied to the diagonal,
whose composite with the second projection is the identity, hence finite, and whose fibres are
single points — so the affine open that argument asks for has to contain two points of a fibre
and nothing more. -/
theorem isSeparated_of_exists_isAffineOpen_pair {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ (s : S) (x y : X), f.base x = s → f.base y = s →
      ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U) :
    IsSeparated f := by
  have : IsFinite (pullback.diagonal f ≫
      ((Over.pullback (Over.mk f).hom).obj (Over.mk f)).hom) := by
    change IsFinite (pullback.diagonal f ≫ pullback.snd f f)
    rw [pullback.diagonal_snd]
    infer_instance
  refine ⟨IsClosedImmersion.of_isPreimmersion _
    (Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism
      (Over.mk f) (Over.mk f) (pullback.diagonal f) fun x => ?_)⟩
  have hcond : f.base (pullback.snd f f x) = f.base (pullback.fst f f x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  obtain ⟨U, hU, hxU, hyU⟩ :=
    h (f.base (pullback.fst f f x)) (pullback.fst f f x) (pullback.snd f f x) rfl hcond
  refine ⟨U, hU, hxU, fun z hz => ?_⟩
  have h1 : ∀ g : pullback f f ⟶ X, pullback.diagonal f ≫ g = 𝟙 X →
      ∀ z, g (pullback.diagonal f z) = z := fun g hg z => by
    rw [← Scheme.Hom.comp_apply, hg]
    rfl
  have hz' : z = pullback.snd f f x := by
    rw [← h1 _ (pullback.diagonal_snd f) z]
    exact hz
  change pullback.fst f f (pullback.diagonal f z) ∈ U
  rw [h1 _ (pullback.diagonal_fst f) z, hz']
  exact hyU

end AlgebraicGeometry

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-- **Representability of `Hilb^d_{X/S}` for every `d`, under the affine-open hypothesis at
`max d 2` points of one fibre.** Let `X ⟶ S` be a morphism of schemes and let `d ≥ 0`. Assume
that for every `s ∈ S` and every tuple of points `x₁, …, x_{max d 2}` of the fibre `X_s` there is
an affine open `U ⊆ X` with `x₁, …, x_{max d 2} ∈ U`. Then the degree-`d` Hilbert functor of
points `Hilb^d_{X/S}` is representable by a scheme over `S`.

This is the generalisation of Stacks Tag 0B9A to every `d`, and the `@[stacks 0B9A]` attribute
sits not here but on
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`,
which is the tag's statement for every `d ≠ 1`, where the tag holds. On the range `2 ≤ d` the two
statements agree, `max d 2 = d`; below it the hypothesis here is strictly the stronger of the
two, which is what buys the extra reach. That extra reach is real content: at `d = 0` and `d = 1`
the source's `d`-tuple hypothesis is vacuous for every morphism of schemes, so the conclusion
cannot follow from it at `d = 1`, where it is **false**
(`Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one`), while the two-point demand
made here does yield it. The module docstring explains why that demand is the weakest one that
does.

The proof is the source's, with the reduction to an affine base replaced by indexing the charts
of the criterion of Stacks 01JJ by pairs of an affine open `V ⊆ S` and an affine open `U ⊆ X`
over it, and with the source's footnote supplied by separatedness of `X ⟶ S`, which the
two-point case of the hypothesis provides
(`AlgebraicGeometry.isSeparated_of_exists_isAffineOpen_pair`). The assembly is
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_familiesClosedInAmbient` and the
affine case it feeds on is Stacks 0B99,
`Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine`. -/
theorem nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem (X : Over S)
    (d : ℕ)
    (hX : ∀ (s : S) (x : Fin (max d 2) → X.left), (∀ i, X.hom.base (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  have : IsSeparated X.hom := by
    refine isSeparated_of_exists_isAffineOpen_pair X.hom fun s x y hx hy => ?_
    obtain ⟨U, hU, hmem⟩ := hX s (fun i => if (i : ℕ) = 0 then x else y) (by
      intro i
      by_cases hi : (i : ℕ) = 0 <;> simp [hi, hx, hy])
    refine ⟨U, hU, ?_, ?_⟩
    · simpa using hmem ⟨0, by omega⟩
    · simpa using hmem ⟨1, by omega⟩
  refine nonempty_representsHilbertFunctorOfRank_of_familiesClosedInAmbient
    (familiesClosedInAmbient_of_isSeparated X) d fun s x hx => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨⊥, isAffineOpen_bot _, fun i => i.elim0⟩
  obtain ⟨U, hU, hmem⟩ := hX s (fun i => x ⟨min (i : ℕ) (d - 1), by omega⟩)
    (fun i => hx _)
  refine ⟨U, hU, fun i => ?_⟩
  simpa [Nat.min_eq_left (by omega : (i : ℕ) ≤ d - 1)] using hmem ⟨i, by omega⟩

/-- **Representability of `Hilb^d_{X/S}` for `2 ≤ d`.** Let `X ⟶ S` be a morphism of schemes and
let `2 ≤ d`. Assume that for every `s ∈ S` and every tuple of points `x₁, …, x_d` of the fibre
`X_s` there is an affine open `U ⊆ X` with `x₁, …, x_d ∈ U`. Then the degree-`d` Hilbert
functor of points `Hilb^d_{X/S}` is representable by a scheme over `S`.

The hypothesis is the source's own, point for point: an affine open around every `d`-tuple of
points of one fibre, for the same `d` as the degree.

`2 ≤ d` is the range on which the source's argument runs. The source states it for every `d ≥ 0`,
but at
`d ≤ 1` its `d`-tuple hypothesis is vacuous for every morphism of schemes
(`Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_le_one`) and at `d = 1` the conclusion is then
**false**: by
`Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one`, in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbientNotRepresentable.lean`,
no scheme represents the degree-`1` Hilbert functor of the affine line with the
origin doubled over affine `1`-space along its coordinate morphism. The two halves are put
side by side in
`Stacks.Hilbert.exists_isAffineOpen_forall_mem_and_not_representable_one` in that same file. So
`2 ≤ d` is not a restriction of convenience: outside it there is nothing true to state, except
at `d = 0`, where `Hilb^0_{X/S} = S` holds with no hypothesis whatever
(`Stacks.Hilbert.representsHilbertFunctorOfRankZero`); the two together are
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`.

The proof is the generalisation
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem`,
which runs the source's argument under the affine-open hypothesis at `max d 2` points. From
`2 ≤ d` one has `max d 2 = d`, so `Fin (max d 2)` and `Fin d` are the same type and the
hypothesis here *is* that one, rewritten; no part of the argument is repeated. -/
theorem nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_two_le
    (X : Over S) {d : ℕ} (hd : 2 ≤ d)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom.base (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) :=
  nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem X d
    (by rwa [max_eq_left hd])

/-- **Stacks Project, Tag 0B9A, for every `d ≠ 1`.** Let `X ⟶ S` be a morphism of schemes and
let `d ≥ 0` with `d ≠ 1`. Assume that for every `s ∈ S` and every tuple of points `x₁, …, x_d` of
the fibre `X_s` there is an affine open `U ⊆ X` with `x₁, …, x_d ∈ U`. Then the degree-`d`
Hilbert functor of points `Hilb^d_{X/S}` is representable by a scheme over `S`.

The hypothesis is the source's own, point for point, and the conclusion is the source's. The
one value of `d` left out is the one at which the proposition is false: at `d = 1` the
`d`-tuple hypothesis holds for every morphism of schemes
(`Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_le_one`), while no scheme represents the
degree-`1` Hilbert functor of the affine line with the origin doubled over affine `1`-space
(`Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one`).

For `2 ≤ d` this is
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_two_le`;
for `d = 0` the base `S` itself represents `Hilb^0_{X/S}`, with no hypothesis needed
(`Stacks.Hilbert.representsHilbertFunctorOfRankZero`). -/
@[stacks 0B9A "the source's own hypothesis, an affine open around every `d`-tuple of points of \
  one fibre, for every `d ≠ 1`; at `d = 1` that hypothesis is vacuous and the tag's conclusion \
  fails, refuted by `Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one`"]
theorem nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one
    (X : Over S) {d : ℕ} (hd : d ≠ 1)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom.base (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 0 := by omega
    exact ⟨⟨Over.mk (𝟙 S), representsHilbertFunctorOfRankZero X⟩⟩
  · exact
      nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_two_le X h hX

end Stacks.Hilbert

end
