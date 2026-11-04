module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDiagonal
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPerfectComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps

/-!
# The upper shriek of an étale morphism

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be an étale morphism of
`AlgebraicGeometry.FTS S`. [Stacks, Tag 0FWI] asserts `f^! ≅ f^*` on `D^+_QCoh(𝒪_Y)`.

Since `f` is flat, `μ_{f,K} : Lf^*K ⊗ᴸ f^!𝒪_Y ⟶ f^!K` is an isomorphism for `K` in
`D^+_QCoh(𝒪_Y)` ([Stacks, Tag 0B6U] (e)), so it suffices to show `f^!𝒪_Y ≅ 𝒪_X`. Since `f` is
unramified, its diagonal `X ⟶ X ×_Y X` is an open immersion, so the whole of `X` is an open of
`X ×_Y X` through which the diagonal factors as the closed immersion `𝟙_X`. For this open the
computation `Δ^!(Lp^* f^!𝒪_Y) ≅ 𝒪_X` of the proof of [Stacks, Tag 0E9W]
(`Stacks.Duality.diagonalUpperShriekIso`, built from [Stacks, Tag 0E9U], [Stacks, Tag 0AU0] and
[Stacks, Tag 0ATX]) has `Δ = 𝟙_X` and `p = 𝟙_X`, and reads `f^!𝒪_Y ≅ 𝒪_X`.

## Main results

* `Stacks.Duality.etaleDiagonalOpen`: `X` as an open of `X ×_Y X` containing the diagonal.
* `Stacks.Duality.upperShriekStructureSheafIsoOfEtale`: `f^!𝒪_Y ≅ 𝒪_X` for étale `f`.
* `Stacks.Duality.upperShriekCompareWithPullbackPlusIso`: `μ_{f,-}` as an isomorphism of functors
  on `D^+_QCoh(𝒪_Y)`, for perfect `f`.
* `Stacks.Duality.upperShriekIsoPullbackOfEtale`: **[Stacks, Tag 0FWI]**.

## References

* [Stacks Project, Tag 0FWI](https://stacks.math.columbia.edu/tag/0FWI)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0E9W](https://stacks.math.columbia.edu/tag/0E9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open DerivedPushforward

/-- For a morphism `f : X ⟶ Y` whose diagonal is an open immersion, `X` itself, embedded in
`X ×_Y X` by the diagonal, is an open through which the diagonal factors as the closed
immersion `𝟙_X`. -/
abbrev etaleDiagonalOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion (pullback.diagonal f)] :
    f.DiagonalOpen where
  W := X
  ι := pullback.diagonal f
  isOpenImmersion := inferInstance
  diag := 𝟙 X
  isClosedImmersion := inferInstance
  fac := Category.id_comp _

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- **`f^!𝒪_Y ≅ 𝒪_X` for an étale morphism `f` of `FTS S`**, `f^!` computed at any
compactification `j`. This is `Stacks.Duality.diagonalUpperShriekIso` for the open
`Stacks.Duality.etaleDiagonalOpen`, where `Δ = 𝟙_X` and `p = 𝟙_X`. -/
def upperShriekStructureSheafIsoOfEtale [Etale f.left] :
    (upperShriek f j).obj (derivedStructureSheaf Y.left) ≅ derivedStructureSheaf X.left :=
  ((quasiCoherentDerivedPullbackIdIsoOfComp X.left).app _).symm ≪≫
    ((quasiCoherentDerivedPullbackCongr (pullback.diagonal_fst f.left)).app _).symm ≪≫
    ((twistedInverseImageIdIso X.left
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))).app _).symm ≪≫
    diagonalUpperShriekIso f j (etaleDiagonalOpen f.left)

/-- **`μ_{f,-}` as an isomorphism of functors on `D^+_QCoh(𝒪_Y)`** for a perfect morphism `f`:
`Lf^*K ⊗ᴸ f^!𝒪_Y ≅ f^!K`, naturally in `K` ([Stacks, Tag 0B6U] (e) and [Stacks, Tag 0B6T]). -/
def upperShriekCompareWithPullbackPlusIso [Perfect f.left] :
    ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left) ⋙
      (quasiCoherentDerivedTensor X.left).flip.obj
        ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≅
    (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙ upperShriek f j :=
  NatIso.ofComponents
    (fun K => @asIso _ _ _ _ (upperShriekCompareWithPullbackCanonical f j K.obj)
      (isIso_upperShriekCompareWithPullback f j K.obj K.property))
    (fun {_ _} h => upperShriekCompareWithPullbackCanonical_naturality f j
      ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _).map h))

/-- **Stacks Project, Tag 0FWI.** In Situation 48.16.1 let `f : X ⟶ Y` be an
étale morphism of `FTS S`. Then `f^! ≅ f^*` as functors on `D^+_QCoh(𝒪_Y)`, for `f^!` computed
at any compactification `j`. The isomorphism at `K` is
`Lf^*K ≅ Lf^*K ⊗ᴸ 𝒪_X ≅ Lf^*K ⊗ᴸ f^!𝒪_Y ≅ f^!K`, the last map being `μ_{f,K}` of
[Stacks, Tag 0B6U] (e). -/
@[stacks 0FWI]
def upperShriekIsoPullbackOfEtale [Etale f.left] :
    (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙ upperShriek f j ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left :=
  (upperShriekCompareWithPullbackPlusIso f j).symm ≪≫
    Functor.isoWhiskerLeft
      ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left)
      ((quasiCoherentDerivedTensor X.left).flip.mapIso
          (upperShriekStructureSheafIsoOfEtale f j) ≪≫
        quasiCoherentDerivedTensorRightUnitor X.left) ≪≫
    Functor.rightUnitor _

end Stacks.Duality

end
