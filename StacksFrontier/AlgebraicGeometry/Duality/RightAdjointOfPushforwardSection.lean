module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineLineUncoheratedTrace
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjointDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.CoherentCohomologySheaves
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DualNumbersNotBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceCoheratorErasure
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHomQcqs
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceQcqs
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of pushforward: the covering set of Stacks 0A9D

Stacks 0A9D is a *section* tag — `\section{Right adjoint of pushforward}` of the chapter on
duality for schemes, Section 48.3. Its preamble fixes a morphism of schemes `f : X ⟶ Y` and
announces the subject, "the right adjoint to the functor
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`", together with the remark that this functor is sometimes
written `f^×` and that `f^!` is avoided because it would clash with [RD]. It states no
mathematics of its own, so its tag belongs on the declarations that
carry the section's eleven labelled items, and this module places it there. Every one of those
declarations is proved elsewhere in this library; nothing is proved here, and nothing is restated
here.

## The section's eleven items, and where each lives

1. **Lemma 48.3.1, Tag 0A9E** — for `f` between quasi-separated and quasi-compact schemes,
   `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint.
   `Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`.
2. **Example 48.3.2, Tag 0A9F** — for `f = Spec φ` affine, `Rf_*` is restriction of scalars and
   the right adjoint is `K ↦ R Hom_A(B, K)`.
   `AlgebraicGeometry.exists_adj_derivedQuasicoherentPushforward_isoDerivedHom`, which states
   both halves at once.
3. **Example 48.3.3, Tag 0A9G** — for `f : 𝐀¹_k ⟶ Spec k` the adjoint does not preserve
   coherence, `R Hom(k[x], k)` not being a finite `k[x]`-module.
   `AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_isCoherent`.
4. **Example 48.3.4, Tag 0A9H** — over the dual numbers every `Ext^i_{k[ε]}(k, k)` is nonzero, so
   `a` need not preserve `D^-_QCoh` even for a finite morphism.
   `AlgebraicGeometry.dualNumberRightAdjoint_not_minus` for the object that is carried out of
   `D^-`, and `AlgebraicGeometry.dualNumberRightAdjoint_not_preserves_minus` for the resulting
   failure of the functor.
5. **Lemma 48.3.5, Tag 0A9I** — `a` maps `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`, with a shift
   bound `N`: vanishing of `H^i(K)` for `i ≤ c` forces `H^i(a(K)) = 0` for `i ≤ c - N`.
   `Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound`, whose conjunction is
   the lemma's two assertions.
6. **Equation 48.3.5.1, Tag 0B6H** — the sheafy trace map
   `Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`.
   `Stacks.Duality.qcqsSheafyTrace`, the map with the right adjoint discharged.
7. **Lemma 48.3.6, Tag 0A9Q** — that map becomes an isomorphism after the coherator `DQ_Y`.
   `Stacks.Duality.isIso_coherator_map_sheafyTrace_of_qcqs`.
8. **Example 48.3.7, Tag 0GEU** — the `DQ_Y` is needed: for `X = 𝐀¹_R` over `Y = Spec R` with
   `L = 𝒪_X` and `K = 𝒪_Y` the right-hand side is `∏_{n ≥ 0} 𝒪_Y`, not quasi-coherent.
   `Stacks.Duality.AffineLine.uncoheratedTrace_example` for the example in the corrected form,
   and `Stacks.Duality.AffineLine.uncoheratedTrace_example_int` for the witness over `ℤ` that
   the failure actually occurs. (The source asserts the failure for an arbitrary `R`; it does
   not hold over a field, and the second of these two records is what makes the example's claim
   true as stated. The correction is set out in the module docstring of
   `StacksFrontier.AlgebraicGeometry.Duality.AffineLineUncoheratedTrace`.)
9. **Remark 48.3.8, Tag 0GEV** — when the `DQ_Y` can be "erased", and the two criteria that
   follow. The remark erases it on the left of the arrow of item 7 as soon as
   `R𝓗om_{𝒪_X}(L, a(K))` is quasi-coherent, on the right as soon as `R𝓗om_{𝒪_Y}(Rf_*L, K)` is,
   and concludes that item 6 is an isomorphism when both are; two sufficient conditions follow.
   `Stacks.Duality.isIso_coherator_homEquiv_sheafyTrace_of_qcqs` for the erasure on the left,
   `Stacks.Duality.isIso_coherator_counit_comp_sheafyTrace_of_qcqs` for the one on the right,
   `Stacks.Duality.isIso_sheafyTrace_of_derivedCategoryB_of_qcqs` for the isomorphism when both
   hold, and `Stacks.Duality.sheafyTrace_quasiCoherent_criteria`, whose three conjuncts are the
   remark's appeal to [Stacks, Tag 0CR1] and its clauses (1) and (2).
10. **Example 48.3.9, Tag 0GEW** — for `f` proper between Noetherian schemes,
    `L ∈ D^-_Coh(X)` and `K ∈ D^+_QCoh(𝒪_Y)`, the map is an isomorphism.
    `Stacks.Duality.isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus`.
11. **Lemma 48.3.10, Tag 0B6I** — the map induces an isomorphism
    `R Hom_X(L, a(K)) ⟶ R Hom_Y(Rf_*L, K)` of global derived homs.
    `Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs`.

## Why the records rather than an attribute

The covering set is spread over twelve modules, so the tag cannot be written as an attribute at
every point of definition; `add_to_stacks` records it against the declarations proved elsewhere,
exactly as `StacksFrontier.Topology.Sheaves.Modules.LocallyFreeSection` does for the section tag
01C5. The command runs on an already elaborated declaration and its duplicate check is per
declaration-and-tag pair, so one tag over several declarations is recorded once for each.

Each carrier named above is unconditional: none takes a hypothesis standing for a Stacks result
this library does not prove. Items 3 and 4 are the section's counterexamples and take the right
adjoint and its adjunction as data, which is what the source's own examples do — the existence of
`a` is Lemma 48.3.1, item 1 of this very section, and is not reasserted inside the examples.

## References

* [Stacks Project, Tag 0A9D](https://stacks.math.columbia.edu/tag/0A9D)
-/

@[expose] public section

-- Tag 0A9D is the section tag of `\section{Right adjoint of pushforward}`; these sixteen
-- declarations are its covering set, one or more for each labelled item the section contains.
add_to_stacks 0A9D "section tag; 0A9E (Lemma 48.3.1), Rf_* has a right adjoint for qcqs schemes"
  Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
add_to_stacks 0A9D "section tag; 0A9F (Example 48.3.2), the affine case: Rf_* is restriction of \
scalars and the adjoint is R Hom_A(B, -)"
  AlgebraicGeometry.exists_adj_derivedQuasicoherentPushforward_isoDerivedHom
add_to_stacks 0A9D "section tag; 0A9G (Example 48.3.3), the adjoint of the affine line does not \
preserve coherence"
  AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_isCoherent
add_to_stacks 0A9D "section tag; 0A9H (Example 48.3.4), the dual numbers: a(O_Y) is unbounded \
above"
  AlgebraicGeometry.dualNumberRightAdjoint_not_minus
add_to_stacks 0A9D "section tag; 0A9H (Example 48.3.4), so the adjoint does not preserve \
D-minus-QCoh even for a finite morphism"
  AlgebraicGeometry.dualNumberRightAdjoint_not_preserves_minus
add_to_stacks 0A9D "section tag; 0A9I (Lemma 48.3.5), the adjoint preserves D-plus-QCoh, with \
the shift bound N"
  Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound
add_to_stacks 0A9D "section tag; 0B6H (Equation 48.3.5.1), the sheafy trace map"
  Stacks.Duality.qcqsSheafyTrace
add_to_stacks 0A9D "section tag; 0A9Q (Lemma 48.3.6), the trace map is an isomorphism after the \
coherator DQ_Y"
  Stacks.Duality.isIso_coherator_map_sheafyTrace_of_qcqs
add_to_stacks 0A9D "section tag; 0GEU (Example 48.3.7), the coherator cannot be dropped: the \
right-hand side is a product of copies of O_Y"
  Stacks.Duality.AffineLine.uncoheratedTrace_example
add_to_stacks 0A9D "section tag; 0GEU (Example 48.3.7), the witness over Z for which the product \
really fails to be quasi-coherent"
  Stacks.Duality.AffineLine.uncoheratedTrace_example_int
add_to_stacks 0A9D "section tag; 0GEV (Remark 48.3.8), erasing the coherator on the left of the \
arrow, where RHom(L, a(K)) is quasi-coherent"
  Stacks.Duality.isIso_coherator_homEquiv_sheafyTrace_of_qcqs
add_to_stacks 0A9D "section tag; 0GEV (Remark 48.3.8), erasing the coherator on the right of the \
arrow, where RHom(Rf_*L, K) is quasi-coherent"
  Stacks.Duality.isIso_coherator_counit_comp_sheafyTrace_of_qcqs
add_to_stacks 0A9D "section tag; 0GEV (Remark 48.3.8), both erasures at once: the map of \
Equation 48.3.5.1 is an isomorphism"
  Stacks.Duality.isIso_sheafyTrace_of_derivedCategoryB_of_qcqs
add_to_stacks 0A9D "section tag; 0GEV (Remark 48.3.8), the appeal to Tag 0CR1 and the two \
criteria: clause (1), L and Rf_*L perfect, and clause (2), K bounded below and L, Rf_*L \
pseudo-coherent"
  Stacks.Duality.sheafyTrace_quasiCoherent_criteria
add_to_stacks 0A9D "section tag; 0GEW (Example 48.3.9), f proper between Noetherian schemes"
  Stacks.Duality.isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus
add_to_stacks 0A9D "section tag; 0B6I (Lemma 48.3.10), the isomorphism of global derived homs"
  Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs
