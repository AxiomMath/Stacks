module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardFiniteType

/-!
# Relative pseudo-coherence of a sheaf of modules in degree zero

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `ℱ` be a sheaf of
`𝒪_X`-modules. Stacks 09UM describes relative `m`-pseudo-coherence of `ℱ` in the three ranges
`0 < m`, `m = 0` and `m = -1`. This file proves the case `m = 0`: relative `0`-pseudo-coherence
is finiteness of type.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_zero_iff_isFiniteType`:
  **Stacks 09UM, the degree-zero clause.**

## Implementation notes

By Stacks 09UJ relative `0`-pseudo-coherence is the local condition of Stacks 09UI at every
compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, and at such a pair the condition is finiteness of
type of `ℱ|_U`:
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_zero_iff`,
which is Stacks 09V9(1) composed with Stacks 01C4. So the clause reduces to finiteness of type
being inherited by restriction to an open subscheme and local on the scheme, both of which are in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardFiniteType.lean`.

The cover used for the locality step is indexed by the compatible pairs of affine opens
themselves, so that the pair supplying the local condition is the one whose source open is the
member of the cover.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.8 (09UM)](https://stacks.math.columbia.edu/tag/09UM)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.60.11 (09V9)](https://stacks.math.columbia.edu/tag/09V9)
* [The Stacks Project, Lemma 17.9.5 (01C4)](https://stacks.math.columbia.edu/tag/01C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 09UM, the degree-zero clause.** For a morphism of schemes locally of finite type, a
sheaf of `𝒪_X`-modules is `0`-pseudo-coherent relative to the base if and only if it is of finite
type.

Stacks 09UJ turns relative `0`-pseudo-coherence into the local condition of Stacks 09UI at every
compatible pair of affine opens, where it is finiteness of type of the restriction of `ℱ` to the
source open; finiteness of type is inherited by restriction and is local on `X`, which gives the
two implications. -/
@[stacks 09UM "degree_zero"]
public theorem isModulePseudoCoherentFrom_zero_iff_isFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) :
    IsModulePseudoCoherentFrom f F 0 ↔ F.IsFiniteType := by
  refine ⟨fun hF => ?_, fun hF => ?_⟩
  · refine Scheme.Modules.isFiniteType_of_isFiniteType_restrict F
      (ι := {p : X.affineOpens × S.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : S.Opens)})
      (fun p => (p.1.1 : X.Opens)) ?_ ?_
    · refine top_unique fun x _ => ?_
      obtain ⟨V, hV, hfxV, -⟩ :=
        exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f.base x) (by simp)
      obtain ⟨U, hU, hxU, hUV⟩ :=
        exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := x) hfxV
      exact Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩
    · intro p
      obtain ⟨n, i, hi, -, hpc⟩ :=
        isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hF p.1.1 p.1.2 p.2
      have := hi
      exact (Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_zero_iff
        _ i F).1 hpc
  · refine isPseudoCoherentFrom_of_forall_affinePair f _ 0 fun U V hUV => ?_
    obtain ⟨n, i, hi, hio⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
    exact ⟨n, i, hi, hio,
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_zero_iff _ i F).2
        (Scheme.Modules.isFiniteType_restrict F hF U.1)⟩

end AlgebraicGeometry.Scheme.Hom

end
