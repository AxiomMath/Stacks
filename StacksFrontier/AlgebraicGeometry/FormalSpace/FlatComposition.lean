module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionPresented
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalPropertyRefined

/-!
# Composition of flat morphisms of locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GCF** says that if
`f : X ⟶ Y` and `g : Y ⟶ Z` are flat morphisms of locally Noetherian formal algebraic spaces
over `S`, then so is `g ∘ f`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFlat_comp_of_isLocallyNoetherian`: **Stacks 0GCF**.

## Implementation notes

The source's proof combines Remark 0GBK with Lemma 0GCB, and that is the proof here. By
Definition 0GCC, read through
`AlgebraicGeometry.FormalSpace.isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`, flatness of a
morphism is condition (1) of Stacks 0ANG for the class `WAdm^{Noeth}` and the property of being
a flat ring homomorphism. That property is local and stable under composition on
`WAdm^{Noeth}` (Stacks 0GC9 and 0GCB, `TopologicalRing.flat_isStableUnderCompositionNoetherian`),
and it does not depend on the presentations of source and target
(`TopologicalRing.flat_isomorphismInvariant`). Remark 0GBK,
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian`,
then transfers composition-stability to morphisms of locally Noetherian formal algebraic
spaces; the factorization of a chart square of `g ∘ f` through charts of `Y` happens inside the
proof of that remark, on a covering, and is not asked of the reader.

## References

* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GCB](https://stacks.math.columbia.edu/tag/0GCB)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCF](https://stacks.math.columbia.edu/tag/0GCF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GCF.** If `f : X ⟶ Y` and `g : Y ⟶ Z` are flat morphisms of locally Noetherian
formal algebraic spaces over `S`, then `g ∘ f` is flat.

Flatness is condition (1) of Stacks 0ANG for Noetherian adic rings and flat ring maps, a local
property stable under composition (Stacks 0GCB), so Remark 0GBK applies. -/
@[stacks 0GCF]
theorem isFlat_comp_of_isLocallyNoetherian {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsFlat B S hS f) (hg : IsFlat B S hS g) :
    IsFlat B S hS (f ≫ g) := by
  rw [isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram] at hf hg ⊢
  exact (hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian B S hS _
    TopologicalRing.flat_isStableUnderCompositionNoetherian
    (fun eB eA heB heB' heA heA' φ hφ _ _ _ _ ↦
      TopologicalRing.flat_isomorphismInvariant TopologicalRing.IsNoetherianAdic eB eA heB heB'
        heA heA' φ hφ ‹_› ‹_› ‹_› ‹_›)
    f g hX hY hZ hf hg).1

end AlgebraicGeometry.FormalSpace

end
