module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionFiniteFamily
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneSequenceCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure

/-!
# [Stacks, Tag 08A1]: one hyperplane for a finite family of coherent sheaves on `ℙⁿ_k`

Let `k` be an infinite field, let `n ≥ 1` and let `ℱ_i` be finitely many coherent `𝒪`-modules on
`ℙⁿ_k`. Tag 08A1 asserts that a single nonzero `s ∈ Γ(ℙⁿ_k, 𝒪(1))` can be chosen for which the
conclusion of [Stacks, Tag 08A0] holds for every member of the family at once: writing
`i : H ⟶ ℙⁿ_k` for the hyperplane cut out by `s`, each

`0 ⟶ ℱ_i(-1) ⟶ ℱ_i ⟶ i_* i^* ℱ_i ⟶ 0`

is short exact.

## Main results

* `…ProjectiveSpaceSectionFiniteFamily.sectionWorksFor_of_mono`: for an arbitrary `𝒪`-module on
  `ℙⁿ_S`, the three conditions of [Stacks, Tag 08A0] reduce to monicity of multiplication by `s`.
* `…ProjectiveSpaceSectionFiniteFamily.isCoherent_biproduct`: a finite direct sum of coherent
  `𝒪`-modules is coherent.
* `…ProjectiveSpaceSectionFiniteFamily.exists_section_forall_shortExact_coherent`:
  **[Stacks, Tag 08A1]**, on no hypothesis beyond `k` infinite, `n ≥ 1` and the `ℱ_i` coherent.

## The mathematics

This is the source's own argument: apply [Stacks, Tag 08A0] to `⨁ ℱ_i` and descend to the
summands.

[Stacks, Tag 08A0] is `AlgebraicGeometry.exists_section_shortExact_hyperplaneUnit`, which is
unconditional on a coherent module over an infinite field; the direct sum of a finite family of
coherent modules is coherent, by `Stacks.SheafOfModules.isCoherent_sigma` transported from the
coproduct to the biproduct, so the lemma applies to `⨁ ℱ_i` and produces a nonzero `s`.

What the lemma returns is a short exact sequence, and what the descent
`…ProjectiveSpaceSectionFiniteFamily.sectionWorksFor_of_retract` consumes is
`…ProjectiveSpaceSectionFiniteFamily.SectionWorksFor`, the three conditions under which the
sequence is asserted. The two are joined by `sectionWorksFor_of_mono`: the vanishing of the
composite and the invertibility of the unit at the cokernel hold for *every* module
(`…ProjectiveSpaceSectionMultiplication.twistSectionMulNegOne_comp_hyperplaneUnit` and
`…isIso_unit_app_cokernel_twistSectionMulNegOne`), so only monicity of multiplication by `s` is
a real condition, and that is the `mono_f` of the short exact sequence returned for `⨁ ℱ_i`.

Each `ℱ_i` is a split summand of `⨁ ℱ_i`, so `sectionWorksFor_of_retract` carries the three
conditions down to it, and
`…ProjectiveSpaceSectionMultiplication.shortExact_hyperplaneUnit` turns them back into the
sequence of [Stacks, Tag 08A0] for `ℱ_i`, with this one `s`.

The tag is registered twice, once per strength: on
`…ProjectiveSpaceSectionFiniteFamily.exists_section_forall_shortExact_of_infiniteField`, the
descent on the conclusion of Tag 08A0 for the direct sum, and here, where that conclusion is
discharged for a family of coherent modules.

## References

* [Stacks Project, Tag 08A1](https://stacks.math.columbia.edu/tag/08A1)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

variable (n : ℕ) (S : Scheme.{u})

/-- **Only monicity is a condition on `s`.** The three conditions under which [Stacks, Tag 08A0]
states its sequence hold for a module `ℱ` on `ℙⁿ_S` and a global section `s` of `𝒪(1)` as soon as
multiplication by `s` is a monomorphism `ℱ(-1) ⟶ ℱ`: the other two hold for every `ℱ`. -/
theorem sectionWorksFor_of_mono (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (hmono : Mono (twistSectionMulNegOne n S F s)) :
    SectionWorksFor n S F s :=
  ⟨hmono, twistSectionMulNegOne_comp_hyperplaneUnit n S F s,
    isIso_unit_app_cokernel_twistSectionMulNegOne n S F s⟩

/-- **A finite direct sum of coherent `𝒪`-modules is coherent.** The biproduct is isomorphic to
the coproduct, where this is `Stacks.SheafOfModules.isCoherent_sigma`; the two coherence
predicates of the library are exchanged by
`AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent`. -/
theorem isCoherent_biproduct {ι : Type*} [Finite ι]
    (F : ι → (projectiveSpaceOver n S).Modules) (hF : ∀ i, (F i).IsCoherent) :
    (⨁ F).IsCoherent :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
    ((Stacks.SheafOfModules.coherentModules
        (projectiveSpaceOver n S).ringCatSheaf).prop_of_iso
      (Limits.biproduct.isoCoproduct F).symm
      (Stacks.SheafOfModules.isCoherent_sigma F fun i =>
        AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hF i)))

/-- **[Stacks, Tag 08A1].** Let `k` be an infinite field, let `n ≥ 1` and let `ℱ_i` be a finite
family of coherent `𝒪`-modules on `ℙⁿ_k`. Then a single nonzero global section `s` of `𝒪(1)`
serves all of them: with `i : H ⟶ ℙⁿ_k` the hyperplane cut out by `s`, the sequence

`0 ⟶ ℱ_i(-1) ⟶ ℱ_i ⟶ i_* i^* ℱ_i ⟶ 0`

of [Stacks, Tag 08A0] is short exact for every member of the family, the first arrow being
multiplication by `s` and the second the restriction to `H`.

This is the source's argument: [Stacks, Tag 08A0]
(`AlgebraicGeometry.exists_section_shortExact_hyperplaneUnit`) is applied to the coherent module
`⨁ ℱ_i`, and the resulting conditions descend to each summand by
`sectionWorksFor_of_retract`. -/
@[stacks 08A1 "one section of O(1) works for a whole finite family of coherent modules"]
theorem exists_section_forall_shortExact_coherent {k : Type u} [Field k] [Infinite k]
    (_hn : 1 ≤ n) {ι : Type*} [Finite ι]
    (F : ι → (projectiveSpaceOver n (Spec (CommRingCat.of k))).Modules)
    (hF : ∀ i, (F i).IsCoherent) :
    ∃ s : (twistOver n (Spec (CommRingCat.of k)) 1).sections,
      PresheafOfModules.sections.eval s (op ⊤) ≠ 0 ∧ ∀ i : ι,
      ∃ hz : twistSectionMulNegOne n (Spec (CommRingCat.of k)) (F i) s ≫
          hyperplaneUnit n (Spec (CommRingCat.of k)) (F i) s = 0,
        (ShortComplex.mk (twistSectionMulNegOne n (Spec (CommRingCat.of k)) (F i) s)
          (hyperplaneUnit n (Spec (CommRingCat.of k)) (F i) s) hz).ShortExact := by
  have hsum : (⨁ F).IsCoherent := isCoherent_biproduct n (Spec (CommRingCat.of k)) F hF
  obtain ⟨s, hs0, _, hSE⟩ :=
    AlgebraicGeometry.exists_section_shortExact_hyperplaneUnit k n (⨁ F)
  have hworks : SectionWorksFor n (Spec (CommRingCat.of k)) (⨁ F) s :=
    sectionWorksFor_of_mono n (Spec (CommRingCat.of k)) (⨁ F) s hSE.mono_f
  refine ⟨s, hs0, fun i => ?_⟩
  obtain ⟨hmono, hzero, hiso⟩ :=
    sectionWorksFor_of_retract n (Spec (CommRingCat.of k)) (Limits.biproduct.ι F i)
      (Limits.biproduct.π F i) (Limits.biproduct.ι_π_self F i) s hworks
  exact shortExact_hyperplaneUnit n (Spec (CommRingCat.of k)) (F i) s hzero hiso

end Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily

end
