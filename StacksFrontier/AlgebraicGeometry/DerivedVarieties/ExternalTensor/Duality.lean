module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Chow.MinusAdamsOperator
public import StacksFrontier.AlgebraicGeometry.Modules.OnSpaceMonoidalScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorFunctorial

/-!
# The dual of an external tensor product

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes, let `ℰ` be a finite locally free
`𝒪_X`-module and `𝒢` a finite locally free `𝒪_Y`-module, and let

`ℰ ⊠ 𝒢 = pr₁^*ℰ ⊗_{𝒪_{X ×_S Y}} pr₂^*𝒢`

be their external tensor product on `X ×_S Y` ([Stacks, Tag 0G46]). This file proves

`(ℰ ⊠ 𝒢)^∨ ≅ ℰ^∨ ⊠ 𝒢^∨`,

naturally in `ℰ` and `𝒢`: for a finite locally free module the dual sheaf is a *left dual* in the
monoidal category of modules, duals are unique up to a canonical isomorphism, and `ℰ^∨ ⊠ 𝒢^∨` is a
left dual of `ℰ ⊠ 𝒢`.

## Main definitions

* `AlgebraicGeometry.externalTensorProductFirstPairing` and
  `AlgebraicGeometry.externalTensorProductSecondPairing`: `pr₁^*(ℰ^∨)` is a left dual of `pr₁^*ℰ`
  and `pr₂^*(𝒢^∨)` is a left dual of `pr₂^*𝒢`.
* `AlgebraicGeometry.externalTensorProductExactPairing`: **`ℰ^∨ ⊠ 𝒢^∨` is a left dual of
  `ℰ ⊠ 𝒢`**, with its canonical coevaluation and evaluation.
* `AlgebraicGeometry.externalTensorProductDualIso`: **the isomorphism
  `(ℰ ⊠ 𝒢)^∨ ≅ ℰ^∨ ⊠ 𝒢^∨`.**
* `AlgebraicGeometry.dualSheafMate`: the dual `φ^∨ : 𝒩^∨ ⟶ ℳ^∨` of a morphism `φ : ℳ ⟶ 𝒩` of
  finite locally free modules, namely its right adjoint mate for the canonical pairings.
* `AlgebraicGeometry.externalTensorProductMate`: the dual of `φ ⊠ ψ` computed through the
  pairing `externalTensorProductExactPairing`, a morphism
  `ℰ₂^∨ ⊠ 𝒢₂^∨ ⟶ ℰ₁^∨ ⊠ 𝒢₁^∨`.

## Main results

* `CategoryTheory.rightAdjointMate_comp_rightDualIso`: **the comparison of two left duals of the
  same object is natural in that object.** If `A₁`, `A₂` are both left duals of `A` and `B₁`,
  `B₂` are both left duals of `B`, then for every `u : A ⟶ B` the square formed by the two
  comparison isomorphisms `A₁ ≅ A₂`, `B₁ ≅ B₂` and the two mates of `u` commutes.
* `AlgebraicGeometry.isFiniteLocallyFree_externalTensorProduct`: the external tensor product of
  two finite locally free modules is finite locally free.
* `AlgebraicGeometry.externalTensorProductDualIso_naturality`: **`(ℰ ⊠ 𝒢)^∨ ≅ ℰ^∨ ⊠ 𝒢^∨` is
  natural in `ℰ` and in `𝒢` simultaneously**, in the sense that it carries the dual of `φ ⊠ ψ`
  formed on the left-hand side to the dual of `φ ⊠ ψ` formed on the right-hand side, for every
  `φ : ℰ₁ ⟶ ℰ₂` and `ψ : 𝒢₁ ⟶ 𝒢₂`.

## Implementation notes

`ℰ^∨ ⊠ 𝒢^∨` is a left dual of `ℰ ⊠ 𝒢` because `pr₁^*(ℰ^∨)` is a left dual of `pr₁^*ℰ` and
`pr₂^*(𝒢^∨)` is a left dual of `pr₂^*𝒢` — this is
`AlgebraicGeometry.VectorBundleKZero.pullbackDualSheafIso`, that duality commutes with pullback of
finite locally free modules, transported along `CategoryTheory.exactPairingCongrRight` — and
because a tensor product of left duals is a left dual of the tensor product, which is Mathlib's
`CategoryTheory.ExactPairing.tensor` ([Stacks, Tag 0FFS]). Mathlib states the latter with the two
factors of the dual in the opposite order, so the symmetry of the tensor product sheaf,
`Stacks.SheafOfModules.tensorSheafBraiding`, is applied once at the end to put them back; its two
tensor products are those of [Stacks, Tag 05NA] and agree with the ones here by `rfl`.

The dual sheaf of a finite locally free module is a left dual for the monoidal structure
`Stacks.SheafOfModules.OnSpace.monoidal` on modules over the underlying ringed space, whose tensor
product on objects *is* the tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` out of
which the external tensor product is built — so `ℰ ⊠ 𝒢` is literally `pr₁^*ℰ ⊗ pr₂^*𝒢` for that
structure, by `rfl`. That structure can only be synthesised at the spelling
`CategoryTheory.SheafOfModules (structureSheafRing W.toRingedSpace)` of the category of
`𝒪_W`-modules and not at the spelling `AlgebraicGeometry.Scheme.Modules` used here, so
`onSpaceModulesMonoidal` renames it and the exact pairings below are passed to
`CategoryTheory.exactPairingCongrRight` and `CategoryTheory.ExactPairing.tensor` as explicit
arguments rather than found by instance search: the two spellings are definitionally equal, so
unification sees through them, but the discrimination tree that instance search is keyed into does
not.

The dual of a morphism in this monoidal language is its right adjoint mate,
`CategoryTheory.rightAdjointMate`. A mate is taken with respect to a chosen left dual, so the dual
of `φ ⊠ ψ` has two readings, `dualSheafMate` through the canonical dual `(ℰ ⊠ 𝒢)^∨` and
`externalTensorProductMate` through the pairing `externalTensorProductExactPairing`, and naturality
is the statement that `externalTensorProductDualIso` carries the first to the second.

## References

* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0FFS](https://stacks.math.columbia.edu/tag/0FFS)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.FiniteLocallyFree Stacks.SheafOfModules.TensorStalkRingedSpace

universe u v

namespace CategoryTheory

/-- **The comparison of two left duals of the same object is natural in that object.** Let
`A₁` and `A₂` both be left duals of `A`, let `B₁` and `B₂` both be left duals of `B`, and let
`u : A ⟶ B`. The two comparison isomorphisms `CategoryTheory.rightDualIso` and the two right
adjoint mates of `u` form a commuting square. -/
theorem rightAdjointMate_comp_rightDualIso {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {A B A₁ A₂ B₁ B₂ : C} (pA₁ : ExactPairing A A₁) (pA₂ : ExactPairing A A₂)
    (pB₁ : ExactPairing B B₁) (pB₂ : ExactPairing B B₂) (u : A ⟶ B) :
    @rightAdjointMate C _ _ A B ⟨A₁⟩ ⟨B₁⟩ u ≫ (rightDualIso pA₁ pA₂).hom =
      (rightDualIso pB₁ pB₂).hom ≫ @rightAdjointMate C _ _ A B ⟨A₂⟩ ⟨B₂⟩ u := by
  have h₁ : @rightAdjointMate C _ _ A B ⟨A₁⟩ ⟨B₁⟩ u =
      (rightDualIso pB₁ pB₂).hom ≫ @rightAdjointMate C _ _ A B ⟨A₁⟩ ⟨B₂⟩ u := by
    have h := @comp_rightAdjointMate C _ _ A B B ⟨A₁⟩ ⟨B₂⟩ ⟨B₁⟩ u (𝟙 B)
    rwa [Category.comp_id] at h
  have h₂ : @rightAdjointMate C _ _ A B ⟨A₁⟩ ⟨B₂⟩ u =
      @rightAdjointMate C _ _ A B ⟨A₂⟩ ⟨B₂⟩ u ≫ (rightDualIso pA₁ pA₂).inv := by
    have h := @comp_rightAdjointMate C _ _ A A B ⟨A₁⟩ ⟨A₂⟩ ⟨B₂⟩ (𝟙 A) u
    rwa [Category.id_comp] at h
  rw [h₁, h₂]; simp

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.VectorBundleKZero

attribute [local instance] onSpaceModulesMonoidal

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **`pr₁^*(ℰ^∨)` is a left dual of `pr₁^*ℰ`**, for a finite locally free `𝒪_X`-module `ℰ`. -/
@[instance_reducible]
noncomputable def externalTensorProductFirstPairing (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    ExactPairing ((Scheme.Modules.pullback (pullback.fst f g)).obj E)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj (dualSheaf E)) :=
  @exactPairingCongrRight _ _ _ _ _ _
    (dualSheafExactPairing (pullback f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj E)
      (isFiniteLocallyFree_pullback (pullback.fst f g) E hE))
    (pullbackDualSheafIso (pullback.fst f g) E hE)

/-- **`pr₂^*(𝒢^∨)` is a left dual of `pr₂^*𝒢`**, for a finite locally free `𝒪_Y`-module `𝒢`. -/
@[instance_reducible]
noncomputable def externalTensorProductSecondPairing (G : Y.Modules)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    ExactPairing ((Scheme.Modules.pullback (pullback.snd f g)).obj G)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj (dualSheaf G)) :=
  @exactPairingCongrRight _ _ _ _ _ _
    (dualSheafExactPairing (pullback f g)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj G)
      (isFiniteLocallyFree_pullback (pullback.snd f g) G hG))
    (pullbackDualSheafIso (pullback.snd f g) G hG)

/-- **`ℰ^∨ ⊠ 𝒢^∨` is a left dual of `ℰ ⊠ 𝒢`.** For a finite locally free `𝒪_X`-module `ℰ` and
a finite locally free `𝒪_Y`-module `𝒢`, the external tensor product of the duals, with a
coevaluation `𝒪_{X ×_S Y} ⟶ (ℰ ⊠ 𝒢) ⊗ (ℰ^∨ ⊠ 𝒢^∨)` and an evaluation
`(ℰ^∨ ⊠ 𝒢^∨) ⊗ (ℰ ⊠ 𝒢) ⟶ 𝒪_{X ×_S Y}`, satisfies the two triangle identities. -/
@[instance_reducible]
noncomputable def externalTensorProductExactPairing (E : X.Modules) (G : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    ExactPairing (externalTensorProduct f g E G)
      (externalTensorProduct f g (dualSheaf E) (dualSheaf G)) :=
  @exactPairingCongrRight _ _ _ _ _ _
    (@ExactPairing.tensor _ _ _ _ _ _ _
      (externalTensorProductFirstPairing f g E hE)
      (externalTensorProductSecondPairing f g G hG))
    (Stacks.SheafOfModules.tensorSheafBraiding (pullback f g).toRingedSpace.presheaf
      (structureSheafRing (pullback f g).toRingedSpace).property
      ((Scheme.Modules.pullback (pullback.fst f g)).obj (dualSheaf E))
      ((Scheme.Modules.pullback (pullback.snd f g)).obj (dualSheaf G)))

/-- **The external tensor product of two finite locally free modules is finite locally
free.** -/
theorem isFiniteLocallyFree_externalTensorProduct (E : X.Modules) (G : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    IsFiniteLocallyFree.{u, u, u} (R := (pullback f g).ringCatSheaf)
      (externalTensorProduct f g E G) :=
  @isFiniteLocallyFree_tensorObj (pullback f g) _ _
    (isFiniteLocallyFree_pullback (pullback.fst f g) E hE)
    (isFiniteLocallyFree_pullback (pullback.snd f g) G hG)

/-- **`(ℰ ⊠ 𝒢)^∨ ≅ ℰ^∨ ⊠ 𝒢^∨`.** The dual of an external tensor product of finite locally free
modules is the external tensor product of the duals: the canonical comparison
`CategoryTheory.rightDualIso` of the two left duals of `ℰ ⊠ 𝒢`. -/
noncomputable def externalTensorProductDualIso (E : X.Modules) (G : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    dualSheaf (externalTensorProduct f g E G) ≅
      externalTensorProduct f g (dualSheaf E) (dualSheaf G) :=
  rightDualIso
    (dualSheafExactPairing (pullback f g) (externalTensorProduct f g E G)
      (isFiniteLocallyFree_externalTensorProduct f g E G hE hG))
    (externalTensorProductExactPairing f g E G hE hG)

/-- **The dual `φ^∨ : 𝒩^∨ ⟶ ℳ^∨` of a morphism of finite locally free modules**: its right
adjoint mate for the canonical left-dual pairings of `ℳ` and of `𝒩`. -/
noncomputable def dualSheafMate {W : Scheme.{u}} {M N : W.Modules}
    (hM : IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) M)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) N) (φ : M ⟶ N) :
    dualSheaf N ⟶ dualSheaf M :=
  @rightAdjointMate W.Modules _ (onSpaceModulesMonoidal W) M N
    (@HasRightDual.mk _ _ (onSpaceModulesMonoidal W) _ _ (dualSheafExactPairing W M hM))
    (@HasRightDual.mk _ _ (onSpaceModulesMonoidal W) _ _ (dualSheafExactPairing W N hN)) φ

/-- **The dual of `φ ⊠ ψ` read through `ℰ^∨ ⊠ 𝒢^∨`**: the right adjoint mate of
`externalTensorProductMap f g φ ψ` for the two pairings
`AlgebraicGeometry.externalTensorProductExactPairing`. -/
noncomputable def externalTensorProductMate {E₁ E₂ : X.Modules} {G₁ G₂ : Y.Modules}
    (hE₁ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₁)
    (hE₂ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₂)
    (hG₁ : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G₁)
    (hG₂ : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G₂)
    (φ : E₁ ⟶ E₂) (ψ : G₁ ⟶ G₂) :
    externalTensorProduct f g (dualSheaf E₂) (dualSheaf G₂) ⟶
      externalTensorProduct f g (dualSheaf E₁) (dualSheaf G₁) :=
  @rightAdjointMate (pullback f g).Modules _ (onSpaceModulesMonoidal (pullback f g)) _ _
    (@HasRightDual.mk _ _ (onSpaceModulesMonoidal (pullback f g)) _ _
      (externalTensorProductExactPairing f g E₁ G₁ hE₁ hG₁))
    (@HasRightDual.mk _ _ (onSpaceModulesMonoidal (pullback f g)) _ _
      (externalTensorProductExactPairing f g E₂ G₂ hE₂ hG₂))
    (externalTensorProductMap f g φ ψ)

/-- **`(ℰ ⊠ 𝒢)^∨ ≅ ℰ^∨ ⊠ 𝒢^∨` is natural in `ℰ` and in `𝒢` simultaneously.** For
`φ : ℰ₁ ⟶ ℰ₂` and `ψ : 𝒢₁ ⟶ 𝒢₂` the isomorphism carries the dual of `φ ⊠ ψ` formed through the
canonical dual of the external tensor product to the dual of `φ ⊠ ψ` formed through
`AlgebraicGeometry.externalTensorProductExactPairing`. -/
theorem externalTensorProductDualIso_naturality {E₁ E₂ : X.Modules} {G₁ G₂ : Y.Modules}
    (hE₁ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₁)
    (hE₂ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₂)
    (hG₁ : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G₁)
    (hG₂ : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G₂)
    (φ : E₁ ⟶ E₂) (ψ : G₁ ⟶ G₂) :
    dualSheafMate (isFiniteLocallyFree_externalTensorProduct f g E₁ G₁ hE₁ hG₁)
          (isFiniteLocallyFree_externalTensorProduct f g E₂ G₂ hE₂ hG₂)
          (externalTensorProductMap f g φ ψ) ≫
        (externalTensorProductDualIso f g E₁ G₁ hE₁ hG₁).hom =
      (externalTensorProductDualIso f g E₂ G₂ hE₂ hG₂).hom ≫
        externalTensorProductMate f g hE₁ hE₂ hG₁ hG₂ φ ψ :=
  @rightAdjointMate_comp_rightDualIso _ _ (onSpaceModulesMonoidal (pullback f g)) _ _ _ _ _ _
    (dualSheafExactPairing (pullback f g) (externalTensorProduct f g E₁ G₁)
      (isFiniteLocallyFree_externalTensorProduct f g E₁ G₁ hE₁ hG₁))
    (externalTensorProductExactPairing f g E₁ G₁ hE₁ hG₁)
    (dualSheafExactPairing (pullback f g) (externalTensorProduct f g E₂ G₂)
      (isFiniteLocallyFree_externalTensorProduct f g E₂ G₂ hE₂ hG₂))
    (externalTensorProductExactPairing f g E₂ G₂ hE₂ hG₂)
    (externalTensorProductMap f g φ ψ)

end AlgebraicGeometry

end
