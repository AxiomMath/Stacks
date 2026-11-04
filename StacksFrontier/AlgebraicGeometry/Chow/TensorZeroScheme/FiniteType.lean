module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism

/-!
# The scheme of Tag 0F97 is affine and of finite type over the base

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules and let `s` be a global
section of `L₁ ⊗_{𝒪_Y} L₂`. The scheme `p : L → Y` of [Stacks, Tag 0F97] is built in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic` as the zero scheme of
`z₁ ⊗ z₂ - q^*s` inside the fibre product `Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two line
bundles of [Stacks, Tag 01M2].

This file proves that `p` is an affine morphism and locally of finite type, hence quasi-compact
and so **of finite type** — the first half of the tag's condition (2). Every step is a stability
property of a morphism class: the structure morphism of a line bundle is the structure morphism
of a relative spectrum, hence affine, and it is locally of finite type because the symmetric
algebra of a module of finite presentation is of finite type; the first projection of the fibre
product is a base change of the second line bundle's structure morphism; the composite with the
first line bundle's structure morphism is `q`; and the closed immersion of the zero scheme into
the fibre product is affine and locally of finite type.

## Main results

* `Stacks.LineBundle.isAffineHom_lineBundleProj` and
  `Stacks.LineBundle.locallyOfFiniteType_lineBundleProj`: the structure morphism of the total
  space of a line bundle is affine and locally of finite type, at the `lineBundleProj` spelling
  of [Stacks, Tag 01M2] that Tag 0F97's construction uses.
* `Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_proj` and
  `Stacks.Chow.TensorZeroScheme.quasiCompact_proj`: **the finite-type half of Tag 0F97(2)**.
* `Stacks.Chow.TensorZeroScheme.isAffineHom_proj`: `p` is an affine morphism, which is stronger
  than the quasi-compactness the tag asks for and is what delivers it.

## Implementation notes

The two base-change steps are not symmetric in the API available: `LocallyOfFiniteType` has a
Mathlib instance for `pullback.fst`, while `IsAffineHom` has only the
`MorphismProperty.IsStableUnderBaseChange` instance, from which the
`IsStableUnderBaseChangeAlong` hypothesis of `MorphismProperty.pullback_fst` has to be produced
by hand — instance search does not chain the two under this project's
`maxSynthPendingDepth`.

*The rest of condition (2).* Flatness of `p` and its relative dimension one are
`Stacks.Chow.TensorZeroScheme.flat_proj` and `relativeDimension_proj` in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FlatRelativeDimension`. Both are local
statements about the ring `A[z₁, z₂]/(z₁z₂ - f)` over an affine open `Spec A ⊆ Y` trivializing
both `L₁` and `L₂`, the local model `Stacks.AffineBundle.LocalModel`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LineBundle (lineBundleProj)

universe u

@[expose] public noncomputable section

namespace Stacks.LineBundle

variable (Y : Scheme.{u}) (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-- **The structure morphism of the total space of a line bundle is an affine morphism**: the
total space is the relative spectrum of `Sym(L^{⊗ -1})`. -/
instance isAffineHom_lineBundleProj : IsAffineHom (lineBundleProj Y M) :=
  inferInstanceAs (IsAffineHom
    (Stacks.RelativeSpec.gluedSpectrum (inverseSituation Y M).relativeSpecSituation).toBase)

/-- **The structure morphism of the total space of a line bundle is locally of finite type.** -/
instance locallyOfFiniteType_lineBundleProj : LocallyOfFiniteType (lineBundleProj Y M) :=
  inferInstanceAs (LocallyOfFiniteType (inverseSituation Y M).totalSpaceToBase)

end Stacks.LineBundle

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

include h₁ h₂ in
/-- The first projection of the fibre product of the two line bundles is affine, being a base
change of the second line bundle's structure morphism. -/
theorem isAffineHom_firstProj : IsAffineHom (firstProj Y L₁ L₂) := by
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) (lineBundleProj Y L₁) :=
    ⟨fun pb h => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  rw [firstProj]
  exact MorphismProperty.pullback_fst _ _ inferInstance

include h₁ h₂ in
/-- The first projection of the fibre product of the two line bundles is locally of finite type,
being a base change of the second line bundle's structure morphism. -/
theorem locallyOfFiniteType_firstProj : LocallyOfFiniteType (firstProj Y L₁ L₂) := by
  have : LocallyOfFiniteType (pullback.fst (lineBundleProj Y L₁) (lineBundleProj Y L₂)) :=
    inferInstance
  rw [firstProj]
  exact this

include h₁ h₂ in
/-- The structure morphism `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` is affine. -/
theorem isAffineHom_totalProj : IsAffineHom (totalProj Y L₁ L₂) := by
  have := isAffineHom_firstProj Y L₁ L₂
  rw [totalProj]
  infer_instance

include h₁ h₂ in
/-- The structure morphism `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` is locally of finite
type. -/
theorem locallyOfFiniteType_totalProj : LocallyOfFiniteType (totalProj Y L₁ L₂) := by
  have := locallyOfFiniteType_firstProj Y L₁ L₂
  rw [totalProj]
  infer_instance

variable (s : Γ(((((Stacks.SheafOfModules.Tensor.sheafTensor
  ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
    (Y.ringCatSheaf.property)⟩).obj (L₁)).obj (L₂))), ⊤))

include h₁ h₂ in
/-- **The structure morphism `p : L ⟶ Y` of Tag 0F97 is an affine morphism**: it is the closed
immersion of a zero scheme followed by the affine morphism `q`. -/
theorem isAffineHom_proj : IsAffineHom (proj Y L₁ L₂ s) := by
  have := isAffineHom_totalProj Y L₁ L₂
  rw [proj, spaceι]
  infer_instance

include h₁ h₂ in
/-- **Stacks Project, Tag 0F97(2), the locally-of-finite-type clause**: the structure morphism
`p : L ⟶ Y` is locally of finite type. -/
theorem locallyOfFiniteType_proj : LocallyOfFiniteType (proj Y L₁ L₂ s) := by
  have := locallyOfFiniteType_totalProj Y L₁ L₂
  rw [proj, spaceι]
  infer_instance

include h₁ h₂ in
/-- **Stacks Project, Tag 0F97(2), the quasi-compactness clause**: the structure morphism
`p : L ⟶ Y` is quasi-compact, being affine. Together with
`locallyOfFiniteType_proj` this is the statement that `p` is of finite type. -/
theorem quasiCompact_proj : QuasiCompact (proj Y L₁ L₂ s) :=
  have := isAffineHom_proj Y L₁ L₂ s
  inferInstance

end Stacks.Chow.TensorZeroScheme

end
