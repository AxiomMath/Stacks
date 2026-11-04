module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionPresented
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothComposition
public import StacksFrontier.RingTheory.Rig.RigSmoothLocalityRefined

/-!
# Rig-smoothness of locally Noetherian formal algebraic spaces is stable under composition

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCS** says that if
`f` and `g` are rig-smooth (Stacks 0GCP), then so is `g ∘ f`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_comp_of_isLocallyNoetherian`: **Stacks 0GCS**.

## Implementation notes

The Stacks proof reads: by Remark 0GBK this follows from Lemma 0GCM. Each ingredient is a
library statement.

* Rig-smoothness is a local property of arrows of `WAdm^{Noeth}` (Stacks 0GCK,
  `Rig.rigSmooth_isLocalNoetherian`), invariant under isomorphism of source and target
  (`Rig.rigSmooth_isomorphismInvariant`), and stable under composition (Stacks 0GCM,
  `Rig.rigSmooth_comp`); together these are the stability bundle
  `Rig.rigSmooth_isStableUnderCompositionNoetherian`.
* Remark 0GBK transfers such a property from arrows of `WAdm^{Noeth}` to morphisms of locally
  Noetherian formal algebraic spaces:
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian`.
* Definition 0GCP and condition (1) of Stacks 0ANG for rig-smoothness agree:
  `AlgebraicGeometry.FormalSpace.isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram`.

The statement here takes neither the locality of rig-smoothness nor the transfer of Remark 0GBK
as a hypothesis, and asks `X`, `Y`, `Z` to be locally Noetherian, as the source does.

## References

* [Stacks Project, Tag 0GCS](https://stacks.math.columbia.edu/tag/0GCS)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0GCM](https://stacks.math.columbia.edu/tag/0GCM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0GCS.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `f` and `g` are rig-smooth, then so is `g ∘ f`. -/
@[stacks 0GCS]
theorem isRigSmooth_comp_of_isLocallyNoetherian (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsRigSmooth B S hS f) (hg : IsRigSmooth B S hS g) :
    IsRigSmooth B S hS (f ≫ g) :=
  (isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_comp_of_isLocallyNoetherian B S hS _
      (Rig.rigSmooth_isStableUnderCompositionNoetherian Rig.rigSmooth_isLocalNoetherian)
      Rig.rigSmooth_isomorphismInvariant f g hX hY hZ
      ((isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf)
      ((isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg)).1

end AlgebraicGeometry.FormalSpace

end
