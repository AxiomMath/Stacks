module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryProperDuality
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.Immersion
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.SheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRigidity
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekEtale
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.Factorization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
public import StacksCore.Tactic.StacksAttribute

/-!
# A duality theory: the upper shriek of a Koszul-regular immersion

Clause (8) of [Stacks, Section 0AU3]: for a Koszul-regular immersion `f : X ⟶ Y` of codimension
`c` into an object of `FTS S`,

`f^!(-) ≅ Lf^*(-) ⊗ᴸ_{𝒪_X} ∧^c 𝒩[-c]`

on `D⁺_QCoh(𝒪_Y)`, where `𝒩` is the normal sheaf of `f`. The immersion `f` factors as a
Koszul-regular closed immersion `i : X ⟶ U` followed by the inclusion of an open `U ⊆ Y`; the
normal sheaf of `f` is that of `i`, and codimension `c` means that the conormal sheaf of `i` is
finite locally free of rank `c`. The proof:

* `f^!𝒪_Y ≅ a_i(Lu^*(a_{id}(𝒪_Y)))` for the factorization `f = i ≫ u ≫ id`
  (`Stacks.Duality.ClosedOpenProperFactorization.upperShriekObjIso`), `a_{id} = id`,
  `Lu^*𝒪_Y = 𝒪_U`, and `a_i(𝒪_U) ≅ ∧^c 𝒩[-c]` by [Stacks, Tag 0BR0]
  (`Stacks.Duality.KoszulRegular.twistedInverseImageIsoOfIsKoszulRegularImmersion`);
* a Koszul-regular immersion is perfect, so `μ_{f,-} : Lf^*(-) ⊗ᴸ f^!𝒪_Y ⟶ f^!(-)` is an
  isomorphism of functors on `D⁺_QCoh(𝒪_Y)` ([Stacks, Tag 0B6U] (e)).

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsKoszulRegularImmersion)

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (U : Y.left.Opens) (i : X.left ⟶ U.toScheme) [IsClosedImmersion i] (hf : i ≫ U.ι = f.left)
  (hi : IsKoszulRegularImmersion i) (c : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf i) c]
  (j : CompactificationOf (Over.mk f.left))

omit [AlgebraicGeometry.IsNoetherian S] in
include hf hi in
/-- A morphism of `FTS S` which is a Koszul-regular closed immersion into an open is perfect. -/
theorem perfect_left_of_isKoszulRegularImmersion : Perfect f.left := by
  have := perfect_of_isKoszulRegularImmersion i hi
  rw [← hf]
  infer_instance

/-- **`f^!𝒪_Y ≅ ∧^c 𝒩[-c]`** for `f = i ≫ U.ι` with `i` a Koszul-regular closed immersion whose
conormal sheaf has rank `c`, at any compactification: the factorization `f = i ≫ U.ι ≫ id` and
[Stacks, Tag 0BR0]. -/
def upperShriekStructureSheafIsoOfKoszulRegular :
    ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)).obj ≅
      (DerivedCategory.singleFunctor X.left.Modules (c : ℤ)).obj
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c) :=
  haveI : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  haveI : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  have hf' : i ≫ U.ι ≫ 𝟙 Y.left = f.left := by rw [Category.comp_id, hf]
  (ObjectProperty.ι _).mapIso (ClosedOpenProperFactorization.upperShriekObjIso f i U.ι (𝟙 _) hf'
      j _ (KoszulRegular.isBoundedBelow_singleFunctor_obj _)) ≪≫
    (ObjectProperty.ι _).mapIso ((twistedInverseImage i
        (isQuasicoherent_homology_derivedPushforward_of_qcqs i)).mapIso
      ((quasiCoherentDerivedPullback' U.ι).mapIso ((twistedInverseImageIdIso Y.left
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 Y.left))).app _) ≪≫
        quasiCoherentDerivedPullbackStructureSheafIso U.ι)) ≪≫
    (KoszulRegular.twistedInverseImageIsoOfIsKoszulRegularImmersion i
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i) hi c).symm

/-- **`f^!(-) ≅ Lf^*(-) ⊗ᴸ ∧^c 𝒩[-c]`** on `D⁺_QCoh(𝒪_Y)`, naturally, for `f = i ≫ U.ι` with `i`
a Koszul-regular closed immersion whose conormal sheaf has rank `c`, at any compactification. -/
def upperShriekIsoPullbackTensorOfKoszulRegular :
    ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left ⋙ ObjectProperty.ι _) ⋙
      (derivedTensor X.left).flip.obj
        ((DerivedCategory.singleFunctor X.left.Modules (c : ℤ)).obj
          (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)) ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        upperShriek f j ⋙ ObjectProperty.ι _ :=
  haveI := perfect_left_of_isKoszulRegularImmersion f U i hf hi
  Functor.isoWhiskerLeft _
      ((derivedTensor X.left).flip.mapIso
        (upperShriekStructureSheafIsoOfKoszulRegular f U i hf hi c j).symm) ≪≫
    Functor.isoWhiskerLeft
      ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left)
      (quasiCoherentDerivedTensorFlipCompιIso X.left
        ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left))).symm ≪≫
    Functor.isoWhiskerRight (upperShriekCompareWithPullbackPlusIso f j) (ObjectProperty.ι _)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- If an immersion `f` is Koszul-regular, so is its canonical closed factor
`f.liftCoborder : X ⟶ f.coborderRange` ([Stacks, Tag 067S], an open immersion being smooth). -/
theorem isKoszulRegularImmersion_liftCoborder_of_isKoszulRegularImmersion [IsImmersion f.left]
    (hf : IsKoszulRegularImmersion f.left) :
    IsKoszulRegularImmersion f.left.liftCoborder := by
  have : IsImmersion (f.left.liftCoborder ≫ f.left.coborderRange.ι) := by
    rw [Scheme.Hom.liftCoborder_ι]; infer_instance
  refine Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_comp_of_smooth
    f.left.liftCoborder f.left.coborderRange.ι ?_
  convert hf using 2
  simp

/-- **Stacks Project, Section 0AU3, clause (8).** Let `S` be a Noetherian scheme and let
`f : X ⟶ Y` be a Koszul-regular immersion of codimension `c` into an object of `FTS S`: an
immersion whose canonical closed factor `i = f.liftCoborder : X ⟶ f.coborderRange` (a closed
immersion into an open of `Y`) has conormal sheaf finite locally free of rank `c`. Write `𝒩` for
the normal sheaf of `f`, the dual of the conormal sheaf of `i`. Then, with `f^!` computed at any
compactification,

`f^!(-) ≅ Lf^*(-) ⊗ᴸ_{𝒪_X} ∧^c 𝒩[-c]`

as functors on `D⁺_QCoh(𝒪_Y)`. -/
@[stacks 0AU3 "clause (8): for a Koszul-regular immersion f : X to Y of codimension c into an \
  object of FTS S (the conormal sheaf of its canonical closed factor into an open of Y finite \
  locally free of rank c) and any compactification, f^!(-) = Lf^*(-) tensor wedge^c N[-c] as \
  functors on D^+_QCoh(O_Y), N the normal sheaf; from Tag 0BR0 and Tag 0B6U (e)"]
theorem nonempty_upperShriekIsoPullbackTensorOfKoszulRegular [IsImmersion f.left]
    (hf : IsKoszulRegularImmersion f.left)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf f.left.liftCoborder) c] :
    Nonempty (((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' f.left ⋙ ObjectProperty.ι _) ⋙
      (derivedTensor X.left).flip.obj
        ((DerivedCategory.singleFunctor X.left.Modules (c : ℤ)).obj
          (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf f.left.liftCoborder) c)) ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        upperShriek f j ⋙ ObjectProperty.ι _) :=
  ⟨upperShriekIsoPullbackTensorOfKoszulRegular f f.left.coborderRange f.left.liftCoborder
    f.left.liftCoborder_ι (isKoszulRegularImmersion_liftCoborder_of_isKoszulRegularImmersion f hf)
    c j⟩

end Stacks.Duality

end
