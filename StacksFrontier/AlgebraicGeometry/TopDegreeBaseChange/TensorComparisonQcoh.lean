module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonAffine
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonCanonical
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# Both ends of the canonical map of Tag 0EX3 (b) are quasi-coherent, and what that buys

`TensorComparisonCanonical.lean` builds the canonical map

`R^n f_* F ⊗_{𝒪_Y} G ⟶ R^n f_*(F ⊗_{𝒪_X} f^* G)`

of conclusion (b) of [Stacks, Tag 0EX3] for an arbitrary morphism of schemes and arbitrary
modules.  Conclusion (b) is the assertion that it is invertible, and invertibility of a morphism
of **quasi-coherent** modules is a local question: it is enough to check it on the sections over
the members of an affine open covering of the base.

This file records that both ends are quasi-coherent, for a quasi-compact quasi-separated `f` and
quasi-coherent `F` and `G` — [Stacks, Tag 01CE] for the tensor product, [Stacks, Tag 01BG] for
the pullback and [Stacks, Tag 01XJ] for the higher direct image — and draws the three reduction
statements that quasi-coherence buys.

## Main definitions

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `topDirectImageTensorSource`: the source `R^n f_* F ⊗_{𝒪_Y} G` of the canonical map, with its
  type *declared* as `Y.Modules`.

## Main results

* `isQuasicoherent_topDirectImageTensorSource` and `isQuasicoherent_topDirectImageTensor`:
  **both ends of the canonical map are quasi-coherent.**
* `isIso_higherDirectImageTensorMap_of_isIso_restrict`: conclusion (b) from the invertibility of
  the restrictions of the canonical map to the members of an open covering of the base.  No
  hypothesis at all: the morphism restricted is the morphism itself.
* `isIso_higherDirectImageTensorMap_of_bijective_app`: **conclusion (b) from bijectivity on the
  sections over the affine opens of the base.**
* `isIso_of_bijective_app_top_of_tensorSource`: over an affine base, **any** morphism between
  the two ends is invertible as soon as it is bijective on global sections.
* `isIso_higherDirectImageTensorMap_of_isIso_app_top`: over an affine base, conclusion (b) from
  invertibility on global sections alone.

## Implementation notes

*Why the source is given a declared type.* The tensor product's own type is
`SheafOfModules (structureSheafRing Y.toRingedSpace)` whereas the affine criterion is stated for
`AlgebraicGeometry.Scheme.Modules`, and the directory records that instance search does not cross
between the two spellings; `topDirectImageTensorSource` is the same term with the second spelling
declared, which is what makes `SheafOfModules.IsQuasicoherent` resolve.  The target needs no such
wrapper: `topDirectImageTensor` is already declared at `Y.Modules`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (n : ℕ)

/-- The source `R^n f_* F ⊗_{𝒪_Y} G` of the canonical map of conclusion (b) of
[Stacks, Tag 0EX3], with its type *declared* as `Y.Modules`.  At that spelling dot notation
finds `SheafOfModules.IsQuasicoherent` over `Y.ringCatSheaf`, which is the spelling the affine
criterion is stated over. -/
abbrev topDirectImageTensorSource : Y.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)).obj G)

/-- **The source `R^n f_* F ⊗_{𝒪_Y} G` of the canonical map is quasi-coherent**, by
[Stacks, Tag 01XJ] for the higher direct image and [Stacks, Tag 01CE] for the tensor product. -/
instance isQuasicoherent_topDirectImageTensorSource [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (topDirectImageTensorSource f F G n).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent Y.toRingedSpace (topDirectImage f F n) G
    (inferInstanceAs (topDirectImage f F n).IsQuasicoherent)
    (inferInstanceAs G.IsQuasicoherent)

/-- **The target `R^n f_*(F ⊗_{𝒪_X} f^* G)` of the canonical map is quasi-coherent**, by
[Stacks, Tag 01BG] for the pullback, [Stacks, Tag 01CE] for the tensor product and
[Stacks, Tag 01XJ] for the higher direct image. -/
instance isQuasicoherent_topDirectImageTensor [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (topDirectImageTensor f F G n).IsQuasicoherent :=
  inferInstanceAs ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
    (tensorPullbackObj f F G)).IsQuasicoherent)

/-- **Conclusion (b) of [Stacks, Tag 0EX3] from the invertibility of the restrictions of the
canonical map to the members of an open covering of the base.**  Nothing is assumed: the
morphism restricted is the morphism itself, so no compatibility of the canonical map with
restriction is involved. -/
theorem isIso_higherDirectImageTensorMap_of_isIso_restrict {I : Type*} (W : I → Y.Opens)
    (hcover : IsOpenCover W)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (W i).ι).map
      (higherDirectImageTensorMap f F G n))) :
    IsIso (higherDirectImageTensorMap f F G n) :=
  AffineBaseChange.isIso_of_isIso_restrict _ W hcover h

/-- **Conclusion (b) of [Stacks, Tag 0EX3] from bijectivity on the sections over the affine
opens of the base.**  Both ends are quasi-coherent, so the affine criterion
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover` applies to the
covering of the base by its affine opens. -/
theorem isIso_higherDirectImageTensorMap_of_bijective_app [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (h : ∀ V : Y.affineOpens, Function.Bijective
      ((higherDirectImageTensorMap f F G n).val.app (op (V : Y.Opens)))) :
    IsIso (higherDirectImageTensorMap f F G n) :=
  AffineBaseChange.isIso_of_bijective_app_of_isOpenCover (higherDirectImageTensorMap f F G n)
    (fun V : Y.affineOpens => (V : Y.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top Y))
    (fun V => V.2) h

/-- **Over an affine base, a morphism between the two ends of the canonical map of
[Stacks, Tag 0EX3] (b) is invertible as soon as it is bijective on global sections.**  Both ends
are quasi-coherent and the top open of an affine scheme is an affine open covering it by itself,
so the affine criterion applies.  The map is arbitrary: nothing is assumed of it beyond its
source and target. -/
theorem isIso_of_bijective_app_top_of_tensorSource [IsAffine Y] [QuasiCompact f]
    [QuasiSeparated f] [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : topDirectImageTensorSource f F G n ⟶ topDirectImageTensor f F G n)
    (h : Function.Bijective (φ.val.app (op (⊤ : Y.Opens)))) : IsIso φ :=
  AffineBaseChange.isIso_of_bijective_app_of_isOpenCover φ
    (fun _ : PUnit.{u + 1} => (⊤ : Y.Opens)) (IsOpenCover.mk iSup_const)
    (fun _ => isAffineOpen_top Y) (fun _ => h)

/-- **Over an affine base, conclusion (b) of [Stacks, Tag 0EX3] from bijectivity on global
sections alone.**  The top open of an affine scheme is an affine open covering it by itself. -/
theorem isIso_higherDirectImageTensorMap_of_bijective_app_top [IsAffine Y] [QuasiCompact f]
    [QuasiSeparated f] [F.IsQuasicoherent] [G.IsQuasicoherent]
    (h : Function.Bijective
      ((higherDirectImageTensorMap f F G n).val.app (op (⊤ : Y.Opens)))) :
    IsIso (higherDirectImageTensorMap f F G n) :=
  isIso_of_bijective_app_top_of_tensorSource f F G n (higherDirectImageTensorMap f F G n) h

/-- **Over an affine base, conclusion (b) of [Stacks, Tag 0EX3] from invertibility on global
sections alone.**  Both ends are quasi-coherent, so
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top` applies. -/
theorem isIso_higherDirectImageTensorMap_of_isIso_app_top [IsAffine Y] [QuasiCompact f]
    [QuasiSeparated f] [F.IsQuasicoherent] [G.IsQuasicoherent]
    (h : IsIso (Scheme.Modules.Hom.app (higherDirectImageTensorMap f F G n) ⊤)) :
    IsIso (higherDirectImageTensorMap f F G n) :=
  AffineBaseChange.isIso_of_isIso_app_top (higherDirectImageTensorMap f F G n) h

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
