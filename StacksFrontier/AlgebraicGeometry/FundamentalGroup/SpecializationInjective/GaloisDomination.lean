module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GaloisObjectCover

/-!
# A connected finite étale cover is dominated by a finite étale Galois cover

Let `X` be a connected scheme and `Y ⟶ X` a finite étale cover whose total space is connected.
Then there is a finite étale Galois cover `Z ⟶ X`, in the sense of
`AlgebraicGeometry.FiniteEtaleGaloisCover`, together with a morphism `Z ⟶ Y` over `X`.

This packages two results that already exist. Over a connected scheme the finite étale covers
form a Galois category (`AlgebraicGeometry.galoisCategory_finiteEtaleOver`) with fibre functor
the geometric fibre at any geometric point
(`AlgebraicGeometry.fiberFunctor_finiteEtaleFiberFintypeFunctor`), and a connected scheme carries
a geometric point at each of its points (`AlgebraicGeometry.Scheme.algClosedPoint`). In a Galois
category every connected object receives a morphism from a Galois object
(`CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_connected`), and a Galois object of
`FÉt_X` is a finite étale Galois cover with group its automorphism group
(`AlgebraicGeometry.FiniteEtaleGaloisCover.ofIsGalois`). The hypothesis of the first is
categorical connectedness, which for finite étale covers is topological connectedness of the
total space (`AlgebraicGeometry.isConnected_of_connectedSpace_left`); that is the form in which
a descent argument has it, so it is the form taken here.

The group is `Aut Y'` for the Galois object `Y'` produced by the Mathlib lemma, so it lives in
`Type u` and is finite; it is not determined by `Y`, hence is existentially quantified along with
the cover.

## Main results

* `AlgebraicGeometry.exists_finiteEtaleGaloisCover_hom_of_connectedSpace` — the statement above.

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

/-- **A connected finite étale cover is dominated by a finite étale Galois cover.** Let `X` be a
connected scheme and let `Y` be a finite étale cover of `X` with connected total space. Then there
is a finite group `G`, a finite étale Galois cover `Z` of `X` with group `G`, and a morphism
`p : Z ⟶ Y` of finite étale covers of `X`; on underlying schemes `p.left` is a morphism
`Z.obj.left ⟶ Y.left` over `X`, which is the triangle recorded by the conclusion. -/
theorem exists_finiteEtaleGaloisCover_hom_of_connectedSpace {X : Scheme.{u}} [ConnectedSpace X]
    (Y : FiniteEtaleOver X) [ConnectedSpace Y.left] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (Z : FiniteEtaleGaloisCover X G)
      (p : Z.obj ⟶ Y), p.left ≫ Y.hom = Z.obj.hom := by
  have : PreGaloisCategory.IsConnected Y := isConnected_of_connectedSpace_left Y
  obtain ⟨Y', p, hY'⟩ := exists_hom_from_galois_of_connected
    (finiteEtaleFiberFintypeFunctor X (X.algClosedPoint (Classical.arbitrary X))) Y
  exact ⟨Aut Y', inferInstance, inferInstance, FiniteEtaleGaloisCover.ofIsGalois Y', p,
    MorphismProperty.Over.w p⟩

end AlgebraicGeometry

end
