module

public import StacksFrontier.AlgebraicGeometry.AmpleTheory.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Stacks 0B3E: ampleness pulls back along a quasi-compact locally closed immersion

Stacks Tag 0B3E says that for `L` ample on `X` and `i : X' ⟶ X` satisfying one of

1. `i` quasi-compact and an immersion,
2. `X'` quasi-compact and `i` an immersion,
3. `i` quasi-compact and a homeomorphism onto its image,
4. `X'` quasi-compact and a homeomorphism onto its image,

the pullback `i^* L` is ample on `X'`. This file proves it from three further hypotheses on `L`
and `i^* L`, listed under `Stacks.AmpleLocallyClosed.isAmple_modulePullback`.

## Main definitions

* `Stacks.AmpleLocallyClosed.pullbackModule`: the pullback `i^* L`.
* `Stacks.AmpleLocallyClosed.SectionPullbackCompatible`: a family of maps on global sections of
  the tensor powers whose nonvanishing loci are the preimages of the nonvanishing loci upstairs,
  `X'_{φ s} = i^{-1}(X_s)`.

## Main results

* `Stacks.AmpleLocallyClosed.compactSpace_of_quasiCompact`: a quasi-compact morphism into a
  quasi-compact scheme has quasi-compact source.
* `Stacks.AmpleLocallyClosed.compactSpace_and_isEmbedding_iff`: over a quasi-compact `X`, the
  four hypotheses above are equivalent to (4).
* `Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback`: clause (3) of Stacks Tag 01Q3 is
  inherited by `i^* L` along a topological embedding.
* `Stacks.AmpleLocallyClosed.isAmple_modulePullback`: Stacks Tag 0B3E, given clause (3) of Stacks
  Tag 01Q3 for `L`, the compatibility `SectionPullbackCompatible`, and the affineness condition
  `Stacks.AmpleTheory.IsAffineOfLeAffine` for `i^* L`.

## Implementation notes

`isBasisNonvanishing_pullback` is stated for a topological embedding, the hypothesis of the
source, although an inducing map would do.

Ampleness is `Stacks.Ample.IsAmple`, over the tensor powers `Stacks.Ample.tensorPowModule` of
Stacks Tag 01CU, and invertibility is `Stacks.Ample.IsInvertibleModule`, an `abbrev` for
`AlgebraicGeometry.SheafOfModules.IsInvertible`. The invertibility of the pullback is Stacks Tag
0B8L, the instance `Stacks.InvertiblePullback.isInvertibleModule_pullback`.

## References

* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleLocallyClosed

/-! ### Quasi-compactness of the source -/

/-- A quasi-compact morphism whose target has quasi-compact underlying space has quasi-compact
source. -/
theorem compactSpace_of_quasiCompact {X X' : Scheme.{u}} (i : X' ⟶ X) (hi : QuasiCompact i)
    (hX : CompactSpace X) : CompactSpace X' := by
  have h := hi.isCompact_preimage (Set.univ) isOpen_univ (hX.isCompact_univ)
  rw [Set.preimage_univ] at h
  exact isCompact_univ_iff.mp h

/-! ### The four hypotheses of Stacks Tag 0B3E -/

/-- On a quasi-compact `X`, the four hypotheses of Stacks Tag 0B3E on `i : X' ⟶ X` are equivalent
to the last of them: `X'` quasi-compact and `i` a homeomorphism onto its image. -/
theorem compactSpace_and_isEmbedding_iff {X X' : Scheme.{u}} (i : X' ⟶ X)
    (hX : CompactSpace X) :
    ((QuasiCompact i ∧ IsImmersion i) ∨ (CompactSpace X' ∧ IsImmersion i) ∨
        (QuasiCompact i ∧ Topology.IsEmbedding i) ∨
        (CompactSpace X' ∧ Topology.IsEmbedding i)) ↔
      (CompactSpace X' ∧ Topology.IsEmbedding i) := by
  refine ⟨?_, fun h => Or.inr (Or.inr (Or.inr h))⟩
  rintro (⟨hq, him⟩ | ⟨hc, him⟩ | ⟨hq, he⟩ | ⟨hc, he⟩)
  · exact ⟨compactSpace_of_quasiCompact i hq hX, let := him; IsPreimmersion.isEmbedding i⟩
  · exact ⟨hc, let := him; IsPreimmersion.isEmbedding i⟩
  · exact ⟨compactSpace_of_quasiCompact i hq hX, he⟩
  · exact ⟨hc, he⟩

/-! ### The pullback module and the compatibility of nonvanishing loci -/

variable {X X' : Scheme.{u}} (i : X' ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- The pullback `i^* L` of `L` along `i`. -/
abbrev pullbackModule : X'.Modules := (modulePullback i.toLRSHom.toShHom).obj L

/-- A family `φ` of maps on global sections of the tensor powers, from `L` to `i^* L`, is
compatible with pullback when the nonvanishing locus of each `φ n s` is the preimage of the
nonvanishing locus of `s`: `X'_{φ s} = i^{-1}(X_s)`. -/
def SectionPullbackCompatible
    (φ : ∀ n : ℕ, Γ(tensorPowModule X L (n : ℤ), ⊤) →
      Γ(tensorPowModule X' (pullbackModule i L) (n : ℤ), ⊤)) : Prop :=
  ∀ (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)),
    (powNonvanishingOpen X' (pullbackModule i L) n (φ n s) : Set X') =
      i.base ⁻¹' (powNonvanishingOpen X L n s : Set X)

/-! ### Transport of the basis of nonvanishing loci -/

/-- **Clause (3) of Stacks Tag 01Q3 is inherited along a topological embedding.** If the
nonvanishing loci of global sections of positive tensor powers of `L` form a basis for the
topology of `X`, and the nonvanishing loci downstairs are their preimages, then the nonvanishing
loci of `i^* L` form a basis for the topology of `X'`. -/
theorem isBasisNonvanishing_pullback (hemb : Topology.IsEmbedding i)
    (hbasis : IsBasisNonvanishing X L)
    {φ : ∀ n : ℕ, Γ(tensorPowModule X L (n : ℤ), ⊤) →
      Γ(tensorPowModule X' (pullbackModule i L) (n : ℤ), ⊤)}
    (hφ : SectionPullbackCompatible i L φ) :
    IsBasisNonvanishing X' (pullbackModule i L) := by
  intro x' U' hx'
  obtain ⟨V, hV, hVU⟩ := hemb.isInducing.isOpen_iff.mp U'.isOpen
  have hxV : i.base x' ∈ (⟨V, hV⟩ : X.Opens) := by
    have : x' ∈ (i.base) ⁻¹' V := by rw [hVU]; exact hx'
    exact this
  obtain ⟨n, hn, s, hxs, hsV⟩ := hbasis (i.base x') ⟨V, hV⟩ hxV
  have key : ∀ y, y ∈ powNonvanishingOpen X' (pullbackModule i L) n (φ n s) ↔
      i.base y ∈ powNonvanishingOpen X L n s := fun y => Set.ext_iff.mp (hφ n s) y
  refine ⟨n, hn, φ n s, (key x').2 hxs, fun y hy => ?_⟩
  have : y ∈ (i.base) ⁻¹' V := hsV ((key y).1 hy)
  rw [hVU] at this
  exact this

/-! ### Stacks Tag 0B3E -/

/-- **Stacks Tag 0B3E**: if `L` is ample on `X` and `i : X' ⟶ X` satisfies one of the four
hypotheses of the tag, then `i^* L` is ample on `X'`, given clause (3) of Stacks Tag 01Q3 for `L`
(`hbasis`), the compatibility of nonvanishing loci `SectionPullbackCompatible` (`hφ`), and the
affineness condition `Stacks.AmpleTheory.IsAffineOfLeAffine` for `i^* L` (`haff`). -/
theorem isAmple_modulePullback (hL : IsAmple X L)
    (hi : (QuasiCompact i ∧ IsImmersion i) ∨ (CompactSpace X' ∧ IsImmersion i) ∨
      (QuasiCompact i ∧ Topology.IsEmbedding i) ∨
      (CompactSpace X' ∧ Topology.IsEmbedding i))
    (hbasis : IsBasisNonvanishing X L)
    {φ : ∀ n : ℕ, Γ(tensorPowModule X L (n : ℤ), ⊤) →
      Γ(tensorPowModule X' (pullbackModule i L) (n : ℤ), ⊤)}
    (hφ : SectionPullbackCompatible i L φ)
    (haff : IsAffineOfLeAffine X' (pullbackModule i L)) :
    IsAmple X' (pullbackModule i L) := by
  obtain ⟨hc, hemb⟩ :=
    (compactSpace_and_isEmbedding_iff i hL.compactSpace).mp hi
  exact isAmple_of_isBasisAffineNonvanishing X' _ hc
    (isBasisAffineNonvanishing_of_isBasisNonvanishing X' _
      (isBasisNonvanishing_pullback i L hemb hbasis hφ) haff)

end Stacks.AmpleLocallyClosed

end
