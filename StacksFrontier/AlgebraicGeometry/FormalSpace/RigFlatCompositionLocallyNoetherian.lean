module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionPresented
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.RingTheory.Rig.FlatIsLocalRefined
public import StacksFrontier.RingTheory.Rig.FlatStableUnderComposition

/-!
# Composition of rig-flat morphisms of locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GH0** says that if
`f` and `g` are rig-flat (Definition 0GGX), then so is `g ∘ f`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigFlat_comp_of_isLocallyNoetherian`: **Stacks 0GH0**.

## Implementation notes

The proof is the one of the source: by Remark 0GBK it follows from Lemma 0GGV.

* Remark 0GBK, the variant of Stacks 0GBI for locally Noetherian formal algebraic spaces, is
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian`:
  condition (1) of Stacks 0ANG passes to the composite for every local property of arrows of
  `WAdm^Noeth` which is stable under composition.
* Lemma 0GGV, stability of rig-flatness under composition in `WAdm^Noeth`, is
  `Rig.rigFlat_isStableUnderCompositionNoetherian`; its locality field is Stacks 0GGU.
* The invariance under isomorphism of source and target that Situation 0CBA assumes of a local
  property is `Rig.rigFlat_isomorphismInvariant`.
* Definition 0GGX is condition (1) of Stacks 0ANG for rig-flatness,
  `AlgebraicGeometry.FormalSpace.isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`.

`AlgebraicGeometry.FormalSpace.isRigFlat_comp` states the same composition for arbitrary fppf
sheaves, from the uniform transfer `TransfersCompositionOnAffineEtaleDiagrams`; it is not a
registration of Stacks 0GH0, whose statement is the one here and needs no such transfer.

Definition 0GGX, `AlgebraicGeometry.FormalSpace.IsRigFlat`, quantifies over every presentation
of the chart morphism `U ⟶ V` by a continuous homomorphism of adic Noetherian topological rings
and asks each one to be rig-flat in the sense of Stacks 0GGP.

The locally Noetherian hypotheses of the source on `X`, `Y` and `Z` are the hypotheses `hX`,
`hY` and `hZ`; they are what the covering of the proof of Stacks 0GBI is built from.

## References

* [Stacks Project, Tag 0GH0](https://stacks.math.columbia.edu/tag/0GH0)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GGV](https://stacks.math.columbia.edu/tag/0GGV)
* [Stacks Project, Tag 0GGX](https://stacks.math.columbia.edu/tag/0GGX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GH0.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `f` and `g` are rig-flat, then so is `g ∘ f`. -/
@[stacks 0GH0]
theorem isRigFlat_comp_of_isLocallyNoetherian {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z) (hf : IsRigFlat B S hS f) (hg : IsRigFlat B S hS g) :
    IsRigFlat B S hS (f ≫ g) :=
  (isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram (f ≫ g)).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian B S hS _
      Rig.rigFlat_isStableUnderCompositionNoetherian Rig.rigFlat_isomorphismInvariant f g hX hY hZ
      ((isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram f).mp hf)
      ((isRigFlat_iff_hasPropertyOnEveryAffineEtaleDiagram g).mp hg)).1

end AlgebraicGeometry.FormalSpace

end
