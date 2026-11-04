module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpenLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmoothEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmoothEssSurj
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Purity for a smooth morphism, unconditionally

Let `f : X ⟶ S` be a morphism of schemes and `U ⊆ X` an open subscheme. Assume

1. `f` is smooth,
2. `S` is Noetherian,
3. for every `s ∈ S` with `depth 𝒪_{S, s} ≤ 1` the fibres agree, `X_s = U_s`,
4. `U_s ⊆ X_s` is dense for every `s ∈ S`.

Then the restriction functor `FÉt_X ⟶ FÉt_U` is an equivalence. This is [Stacks, Tag 0EYB].

Essential surjectivity is `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_of_smooth`,
the source's second paragraph, which goes through [Stacks, Tag 0EYA]. Full faithfulness is the
source's first paragraph: [Stacks, Tag 0BQF] combined with [Stacks, Tag 0BLR] and
[Stacks, Tag 0337]. The source applies Tag 0BQF, which asks for the underlying space of `X` to be
Noetherian, although `X` smooth over a Noetherian `S` is only locally Noetherian; here the
locally Noetherian form of Tag 0BQF,
`AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_dense_of_isLocallyNoetherian`, is used,
so that no quasi-compactness of `X` is needed.

## Main results

* `Stacks.FundamentalGroup.nonempty_fullyFaithful_finiteEtaleBaseChange_of_smooth`: the fully
  faithful half, for `S` only locally Noetherian.
* `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_of_smooth_of_fibrewise_dense`:
  **[Stacks, Tag 0EYB]**, with no hypothesis beyond the tag's.

## References

* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR)
* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 0EYA](https://stacks.math.columbia.edu/tag/0EYA)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.FundamentalGroup

/-- **The fully faithful half of [Stacks, Tag 0EYB].** Let `f : X ⟶ S` be a smooth morphism with
`S` locally Noetherian and let `U ⊆ X` be an open such that the fibre `f⁻¹(s)` is contained in `U`
whenever `depth 𝒪_{S, s} ≤ 1` (`hfib`) and `U ∩ f⁻¹(s)` is dense in `f⁻¹(s)` for every `s`
(`hdense`). Then restriction of finite étale covers `FÉt_X ⟶ FÉt_U` is fully faithful.

`U` is dense in `X` by `dense_of_fibrewise_dense`; at a point of `X` outside `U` the local ring
has depth at least two by `two_le_depth_stalk_of_notMem_of_fibre_subset` ([Stacks, Tag 0337]),
so the punctured spectra of its strict henselizations are connected
([Stacks, Tag 0BLR]); and [Stacks, Tag 0BQF] for the locally Noetherian scheme `X` concludes. -/
@[sga "1 XIII 4.7" "special case"]
public theorem nonempty_fullyFaithful_finiteEtaleBaseChange_of_smooth {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [IsLocallyNoetherian S] (U : X.Opens)
    (hfib : ∀ s : S, Module.depth (S.presheaf.stalk s) (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s) ≤ 1 → f.base ⁻¹' {s} ⊆ (U : Set X))
    (hdense : ∀ s : S, f.base ⁻¹' {s} ⊆ closure ((U : Set X) ∩ f.base ⁻¹' {s})) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdepth := two_le_depth_stalk_of_notMem_of_fibre_subset f U hfib
  exact fullyFaithful_finiteEtaleBaseChange_of_dense_of_isLocallyNoetherian X U
    (dense_of_fibrewise_dense f U hdense)
    fun x hx => isConnectedPuncturedStrictHenselization_of_two_le_depth _ (hdepth x hx)

/-- **[Stacks, Tag 0EYB].** Let `f : X ⟶ S` be a morphism of schemes and `U ⊆ X` an open
subscheme. Assume that

1. `f` is smooth,
2. `S` is Noetherian,
3. for every `s ∈ S` with `depth 𝒪_{S, s} ≤ 1` we have `X_s = U_s`, spelled as containment of
   the fibre `f⁻¹(s)` in `U` (`hfib`), and
4. `U_s ⊆ X_s` is dense for every `s ∈ S`, spelled as every point of `f⁻¹(s)` lying in the
   closure of `U ∩ f⁻¹(s)` (`hdense`).

Then the restriction functor `FÉt_X ⟶ FÉt_U` is an equivalence of categories.

Full faithfulness is `nonempty_fullyFaithful_finiteEtaleBaseChange_of_smooth` (the source's first
paragraph, by [Stacks, Tag 0BQF], [Stacks, Tag 0BLR] and [Stacks, Tag 0337]) and essential
surjectivity is `essSurj_finiteEtaleBaseChange_of_smooth` (the source's second paragraph, by
[Stacks, Tag 0EY6] and [Stacks, Tag 0EYA]). -/
@[stacks 0EYB "the full statement under the tag's four hypotheses and nothing else: (1) \
`Smooth f`, (2) `IsNoetherian S`, (3) `hfib`, the tag's `X_s = U_s` at every `s` with \
`depth 𝒪_{S, s} ≤ 1`, spelled as containment of the fibre `f⁻¹(s)` in `U`, and (4) `hdense`, \
the density of `U_s` in `X_s`, spelled as every point of `f⁻¹(s)` lying in the closure of \
`U ∩ f⁻¹(s)`; the conclusion is that the restriction `finiteEtaleBaseChange U.ι` is an \
equivalence `FÉt_X ⟶ FÉt_U`."]
public theorem isEquivalence_finiteEtaleBaseChange_of_smooth_of_fibrewise_dense
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsNoetherian S] (U : X.Opens)
    (hfib : ∀ s : S, Module.depth (S.presheaf.stalk s) (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s) ≤ 1 → f.base ⁻¹' {s} ⊆ (U : Set X))
    (hdense : ∀ s : S, f.base ⁻¹' {s} ⊆ closure ((U : Set X) ∩ f.base ⁻¹' {s})) :
    (finiteEtaleBaseChange U.ι).IsEquivalence := by
  obtain ⟨hff⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_of_smooth f U hfib hdense
  exact { faithful := hff.faithful, full := hff.full,
          essSurj := essSurj_finiteEtaleBaseChange_of_smooth f U hfib hdense }

end Stacks.FundamentalGroup

end
