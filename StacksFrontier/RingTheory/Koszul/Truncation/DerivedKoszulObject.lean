module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# The Koszul complex of a sequence as an object of `D(𝒪_{Spec A})`

Let `A` be a commutative ring and let `f₁, …, f_r ∈ A`. Two objects attached to this data appear
throughout the compact-generation arguments of [Stacks, Tag 0GEK] and [Stacks, Tag 09IR]: the
open subscheme of `Spec A` on which the `f_i` do not all vanish, which is the union of the
principal opens `D(f_i)`, and the Koszul complex `K_•(f₁, …, f_r)` sheafified and viewed in the
derived category of `𝒪_{Spec A}`-modules. This file defines both.

The Koszul complex is built as a chain complex of `A`-modules indexed by `ℕ`
(`Koszul.seqComplex`). To regard it as an object of the derived category it is re-indexed as a
cochain complex over `ℤ` concentrated in non-positive degrees, by extending along
`ComplexShape.embeddingDownNat`, then sheafified termwise by the affine comparison functor
`AlgebraicGeometry.tilde.functor` and localized.

## Main definitions

* `Stacks.Koszul.Truncation.openComplement` — the union `⋃ᵢ D(f_i) ⊆ Spec A`, the open
  complement of the common zero locus of the sequence.
* `Stacks.Koszul.Truncation.koszulObject` — the sheafified Koszul complex of the sequence as an
  object of `D(𝒪_{Spec A})`.

## Implementation notes

The derived category is left as an instance argument rather than pinned to
`CategoryTheory.HasDerivedCategory.standard`. That model puts the morphisms of `D(𝒪_X)` in
`Type (u + 1)`, one universe above the morphisms of `X.Modules` rather than above its objects,
which makes the direct sums occurring in Stacks 09IS and 0A9A — the statements these objects are
used for — false rather than merely unavailable; see the implementation notes of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`.

Termwise sheafification needs `AlgebraicGeometry.tilde.functor` to preserve zero morphisms, which
is not an instance in Mathlib because `tilde.functor` is not declared additive there. It holds by
`AlgebraicGeometry.tilde.map_zero` and is supplied here as an instance.

No `@[stacks]` attribute is attached. Tag 0GEK has two tagged statements, the two implications
relating vanishing of maps out of `koszulObject` to invertibility of a truncated restriction map;
neither is proved here, and both are currently unstatable in this repository because they are
phrased with the unit of the derived pullback–pushforward adjunction of Stacks 079W, which has no
counterpart in the library (the derived pullback `Lf^*` of Stacks 06YJ is missing). What is
provided here is the vocabulary those statements are written in.

## References

* [Stacks Project, Tag 0GEK](https://stacks.math.columbia.edu/tag/0GEK)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe w u

namespace Stacks.Koszul.Truncation

/-- Termwise sheafification `M ↦ M^~` of modules over an affine scheme preserves zero
morphisms, so it may be applied to a complex. -/
instance tilde_functor_preservesZeroMorphisms (A : Type u) [CommRing A] :
    (tilde.functor (CommRingCat.of A)).PreservesZeroMorphisms :=
  ⟨fun _ _ => tilde.map_zero (R := CommRingCat.of A)⟩

/-- The open complement of the common zero locus of a finite sequence `f₁, …, f_r` in a ring `A`,
that is the union `⋃ᵢ D(f_i)` of the principal opens of `Spec A` attached to the `f_i`. -/
abbrev openComplement {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) : (Spec (.of A)).Opens :=
  ⨆ i, (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i))

/-- The Koszul complex `K_•(f₁, …, f_r)` of a finite sequence in `A`, sheafified termwise and
viewed as an object of the derived category of `𝒪_{Spec A}`-modules: the chain complex
`Koszul.seqComplex f` re-indexed as a cochain complex in non-positive degrees, pushed through the
affine comparison functor, and localized. -/
abbrev koszulObject {A : Type u} [CommRing A] {r : ℕ}
    [HasDerivedCategory.{w} (Spec (CommRingCat.of A)).Modules] (f : Fin r → A) :
    DerivedCategory (Spec (.of A)).Modules :=
  DerivedCategory.Q.obj
    (((tilde.functor (.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat))

end Stacks.Koszul.Truncation

end
