module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineChosenPullback

/-!
# Cancelling the base change of a module pulled back from the base ring

Let `B` be an `R`-algebra and let `M` be an `R`-module.  Pulling `M` back to `Spec B` and then to
`Spec (B ⊗[R] B)` along either projection gives the same thing as pulling it back to
`Spec (B ⊗[R] B)` directly: on modules,

`(B ⊗[R] B) ⊗[B] (B ⊗[R] M) ≅ (B ⊗[R] B) ⊗[R] M`.

This file provides that isomorphism for `ModuleCat.extendScalars` along
`Stacks.Descent.tensorInl` and `Stacks.Descent.tensorInr`, together with the value of both
directions on `1 ⊗ (1 ⊗ m)`.

## Main definitions

* `ModuleCat.ExtendScalars.oneTmul`: the element `1 ⊗ x` of `(ModuleCat.extendScalars f).obj X`.
* `ModuleCat.extendScalarsCongr`: equal ring maps have isomorphic extensions of scalars.
* `ModuleCat.cancelExtendScalars`: for ring maps `f₁₂ : R₁ →+* R₂`, `f₂₃ : R₂ →+* R₃` and
  `g : R₁ →+* R₃` with `f₂₃ ∘ f₁₂ = g`, the isomorphism
  `(extendScalars f₂₃).obj ((extendScalars f₁₂).obj X) ≅ (extendScalars g).obj X`.
* `Stacks.Descent.cancelExtendScalarsInl` and `Stacks.Descent.cancelExtendScalarsInr`: that
  isomorphism at the two inclusions `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b` of `B ⊗[R] B`, which are the
  two projections of `Stacks.Descent.specTensorChosenPullback`.
* `Stacks.Descent.cancelExtendScalarsHomEquiv`: consequently morphisms from the first pullback of
  `M₁` to the second pullback of `M₂` are exactly morphisms between the two direct pullbacks.

## Main results

* `Stacks.Descent.tensorInl_hom_comp_algHom_hom` and
  `Stacks.Descent.tensorInr_hom_comp_algHom_hom`: the two ring maps `B → B ⊗[R] B` both compose
  with `algebraMap R B` to `algebraMap R (B ⊗[R] B)`.
* `ModuleCat.cancelExtendScalars_hom_oneTmul` and `ModuleCat.cancelExtendScalars_inv_oneTmul`,
  with their specialisations `Stacks.Descent.cancelExtendScalarsInl_hom_oneTmul`,
  `Stacks.Descent.cancelExtendScalarsInl_inv_oneTmul`,
  `Stacks.Descent.cancelExtendScalarsInr_hom_oneTmul` and
  `Stacks.Descent.cancelExtendScalarsInr_inv_oneTmul`: the two directions send `1 ⊗ (1 ⊗ m)` and
  `1 ⊗ m` to each other.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

open scoped ChangeOfRings

universe u

namespace ModuleCat

namespace ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The element `1 ⊗ x` of `(ModuleCat.extendScalars f).obj X`. -/
def oneTmul (f : R →+* S) {X : ModuleCat.{u} R} (x : X) :
    ((extendScalars f).obj X : Type u) :=
  (1 : S) ⊗ₜ[R,f] x

/-- `ModuleCat.ExtendScalars.hom_ext` phrased with `ModuleCat.ExtendScalars.oneTmul`: two maps
out of an extension of scalars agree as soon as they agree on the elements `1 ⊗ x`. -/
theorem hom_ext' {f : R →+* S} {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S}
    {α β : (extendScalars f).obj X ⟶ Y} (h : ∀ x : X, α (oneTmul f x) = β (oneTmul f x)) :
    α = β :=
  ModuleCat.ExtendScalars.hom_ext h

/-- The extension of scalars of a linear map `g` sends `1 ⊗ x` to `1 ⊗ g x`. -/
@[simp]
theorem map_oneTmul (f : R →+* S) {X Y : ModuleCat.{u} R} (g : X ⟶ Y) (x : X) :
    (extendScalars f).map g (oneTmul f x) = oneTmul f (g x) :=
  rfl

/-- The map `x ↦ 1 ⊗ x` is additive. -/
theorem oneTmul_add (f : R →+* S) {X : ModuleCat.{u} R} (x y : X) :
    oneTmul f (x + y) = oneTmul f x + oneTmul f y :=
  TensorProduct.tmul_add _ _ _

/-- The map `x ↦ 1 ⊗ x` sends `r • x` to `f r • (1 ⊗ x)`. -/
theorem oneTmul_smul (f : R →+* S) {X : ModuleCat.{u} R} (r : R) (x : X) :
    oneTmul f (r • x) = f r • oneTmul f x :=
  (TensorProduct.smul_tmul (R := R) (M := (restrictScalars f).obj (of S S)) (N := X)
    r (1 : S) x).symm

variable {f g : R →+* S}

/-- The unit `x ↦ 1 ⊗ x` of the comparison between two equal extensions of scalars. -/
def congrUnit (h : f = g) (X : ModuleCat.{u} R) :
    X ⟶ (restrictScalars f).obj ((extendScalars g).obj X) :=
  ofHom (Y := (restrictScalars f).obj ((extendScalars g).obj X))
    { toFun := fun x => oneTmul g x
      map_add' := fun x y => oneTmul_add g x y
      map_smul' := fun r x => by subst h; exact oneTmul_smul f r x }

/-- The comparison between two equal extensions of scalars, obtained from
`ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars` at
`ModuleCat.ExtendScalars.congrUnit`. -/
def congrHom (h : f = g) (X : ModuleCat.{u} R) :
    (extendScalars f).obj X ⟶ (extendScalars g).obj X :=
  ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f (congrUnit h X)

/-- `ModuleCat.ExtendScalars.congrHom` sends `1 ⊗ x` to `1 ⊗ x`. -/
@[simp]
theorem congrHom_oneTmul (h : f = g) (X : ModuleCat.{u} R) (x : X) :
    congrHom h X (oneTmul f x) = oneTmul g x := by
  show (1 : S) • (oneTmul g x : ((extendScalars g).obj X : Type u)) = oneTmul g x
  exact one_smul _ _

end ExtendScalars

open ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] {f g : R →+* S}

/-- **Equal ring maps have isomorphic extensions of scalars.** -/
def extendScalarsCongr (h : f = g) (X : ModuleCat.{u} R) :
    (extendScalars f).obj X ≅ (extendScalars g).obj X where
  hom := congrHom h X
  inv := congrHom h.symm X
  hom_inv_id := hom_ext' fun x => by
    rw [comp_apply, congrHom_oneTmul, congrHom_oneTmul, id_apply]
  inv_hom_id := hom_ext' fun x => by
    rw [comp_apply, congrHom_oneTmul, congrHom_oneTmul, id_apply]

/-- The isomorphism `ModuleCat.extendScalarsCongr` sends `1 ⊗ x` to `1 ⊗ x`. -/
@[simp]
theorem extendScalarsCongr_hom_oneTmul (h : f = g) (X : ModuleCat.{u} R) (x : X) :
    (extendScalarsCongr h X).hom (oneTmul f x) = oneTmul g x :=
  congrHom_oneTmul h X x

/-- The inverse of `ModuleCat.extendScalarsCongr` sends `1 ⊗ x` to `1 ⊗ x`. -/
@[simp]
theorem extendScalarsCongr_inv_oneTmul (h : f = g) (X : ModuleCat.{u} R) (x : X) :
    (extendScalarsCongr h X).inv (oneTmul g x) = oneTmul f x :=
  congrHom_oneTmul h.symm X x

section Cancel

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]

/-- **Cancelling a base change.**  Extending scalars along `f₁₂` and then along `f₂₃` is
extending scalars along a ring map `g` equal to the composite. -/
def cancelExtendScalars (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) {g : R₁ →+* R₃}
    (h : f₂₃.comp f₁₂ = g) (X : ModuleCat.{u} R₁) :
    (extendScalars f₂₃).obj ((extendScalars f₁₂).obj X) ≅ (extendScalars g).obj X :=
  ((extendScalarsComp f₁₂ f₂₃).app X).symm ≪≫ extendScalarsCongr h X

/-- The inverse of `ModuleCat.cancelExtendScalars` sends `1 ⊗ x` to `1 ⊗ (1 ⊗ x)`. -/
@[simp]
theorem cancelExtendScalars_inv_oneTmul (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) {g : R₁ →+* R₃}
    (h : f₂₃.comp f₁₂ = g) (X : ModuleCat.{u} R₁) (x : X) :
    (cancelExtendScalars f₁₂ f₂₃ h X).inv (oneTmul g x) = oneTmul f₂₃ (oneTmul f₁₂ x) := by
  rw [cancelExtendScalars, Iso.trans_inv, comp_apply, extendScalarsCongr_inv_oneTmul,
    Iso.symm_inv, Iso.app_hom]
  exact extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ X x

/-- The isomorphism `ModuleCat.cancelExtendScalars` sends `1 ⊗ (1 ⊗ x)` to `1 ⊗ x`. -/
@[simp]
theorem cancelExtendScalars_hom_oneTmul (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) {g : R₁ →+* R₃}
    (h : f₂₃.comp f₁₂ = g) (X : ModuleCat.{u} R₁) (x : X) :
    (cancelExtendScalars f₁₂ f₂₃ h X).hom (oneTmul f₂₃ (oneTmul f₁₂ x)) = oneTmul g x := by
  rw [← cancelExtendScalars_inv_oneTmul f₁₂ f₂₃ h X x, ← comp_apply, Iso.inv_hom_id, id_apply]

end Cancel

/-- `CategoryTheory.Iso.homCongr` evaluated at an element. -/
theorem homCongr_apply_apply {X Y X' Y' : ModuleCat.{u} R} (α : X ≅ X') (β : Y ≅ Y')
    (φ : X ⟶ Y) (x : X') :
    Iso.homCongr α β φ x = β.hom (φ (α.inv x)) := by
  rw [Iso.homCongr_apply, comp_apply, comp_apply]

end ModuleCat

namespace Stacks.Descent

open ModuleCat.ExtendScalars

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The inclusion `b ↦ b ⊗ 1` composes with `algebraMap R B` to `algebraMap R (B ⊗[R] B)`. -/
theorem tensorInl_hom_comp_algHom_hom :
    (tensorInl R B).hom.comp (algHom R B).hom = algebraMap R (B ⊗[R] B) :=
  rfl

/-- The inclusion `b ↦ 1 ⊗ b` composes with `algebraMap R B` to `algebraMap R (B ⊗[R] B)`. -/
theorem tensorInr_hom_comp_algHom_hom :
    (tensorInr R B).hom.comp (algHom R B).hom = algebraMap R (B ⊗[R] B) := by
  ext r
  exact (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B)).commutes r

variable (M : ModuleCat.{u} R)

/-- **Cancelling the base change along the first projection of `Spec (B ⊗[R] B)`.**  For an
`R`-module `M`, extending scalars to `B` and then along `b ↦ b ⊗ 1` is extending scalars to
`B ⊗[R] B` directly. -/
def cancelExtendScalarsInl :
    (ModuleCat.extendScalars (tensorInl R B).hom).obj
        ((ModuleCat.extendScalars (algHom R B).hom).obj M) ≅
      (ModuleCat.extendScalars (algebraMap R (B ⊗[R] B))).obj M :=
  ModuleCat.cancelExtendScalars (algHom R B).hom (tensorInl R B).hom
    (tensorInl_hom_comp_algHom_hom R B) M

/-- The value of the inverse of `Stacks.Descent.cancelExtendScalarsInl` on `1 ⊗ m`. -/
theorem cancelExtendScalarsInl_inv_oneTmul (m : M) :
    (cancelExtendScalarsInl R B M).inv (oneTmul (algebraMap R (B ⊗[R] B)) m) =
      oneTmul (tensorInl R B).hom (oneTmul (algHom R B).hom m) :=
  ModuleCat.cancelExtendScalars_inv_oneTmul _ _ (tensorInl_hom_comp_algHom_hom R B) M m

/-- The value of `Stacks.Descent.cancelExtendScalarsInl` on `1 ⊗ (1 ⊗ m)`. -/
theorem cancelExtendScalarsInl_hom_oneTmul (m : M) :
    (cancelExtendScalarsInl R B M).hom
        (oneTmul (tensorInl R B).hom (oneTmul (algHom R B).hom m)) =
      oneTmul (algebraMap R (B ⊗[R] B)) m :=
  ModuleCat.cancelExtendScalars_hom_oneTmul _ _ (tensorInl_hom_comp_algHom_hom R B) M m

/-- **Cancelling the base change along the second projection of `Spec (B ⊗[R] B)`.** -/
def cancelExtendScalarsInr :
    (ModuleCat.extendScalars (tensorInr R B).hom).obj
        ((ModuleCat.extendScalars (algHom R B).hom).obj M) ≅
      (ModuleCat.extendScalars (algebraMap R (B ⊗[R] B))).obj M :=
  ModuleCat.cancelExtendScalars (algHom R B).hom (tensorInr R B).hom
    (tensorInr_hom_comp_algHom_hom R B) M

/-- The value of the inverse of `Stacks.Descent.cancelExtendScalarsInr` on `1 ⊗ m`. -/
theorem cancelExtendScalarsInr_inv_oneTmul (m : M) :
    (cancelExtendScalarsInr R B M).inv (oneTmul (algebraMap R (B ⊗[R] B)) m) =
      oneTmul (tensorInr R B).hom (oneTmul (algHom R B).hom m) :=
  ModuleCat.cancelExtendScalars_inv_oneTmul _ _ (tensorInr_hom_comp_algHom_hom R B) M m

/-- The value of `Stacks.Descent.cancelExtendScalarsInr` on `1 ⊗ (1 ⊗ m)`. -/
theorem cancelExtendScalarsInr_hom_oneTmul (m : M) :
    (cancelExtendScalarsInr R B M).hom
        (oneTmul (tensorInr R B).hom (oneTmul (algHom R B).hom m)) =
      oneTmul (algebraMap R (B ⊗[R] B)) m :=
  ModuleCat.cancelExtendScalars_hom_oneTmul _ _ (tensorInr_hom_comp_algHom_hom R B) M m

/-- A morphism from the pullback of `M₁` along `b ↦ b ⊗ 1` to the pullback of `M₂` along
`b ↦ 1 ⊗ b` is the same thing as a morphism between the two direct pullbacks to
`Spec (B ⊗[R] B)`, by conjugating with `Stacks.Descent.cancelExtendScalarsInl` and
`Stacks.Descent.cancelExtendScalarsInr`. -/
def cancelExtendScalarsHomEquiv (M₁ M₂ : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars (tensorInl R B).hom).obj
          ((ModuleCat.extendScalars (algHom R B).hom).obj M₁) ⟶
        (ModuleCat.extendScalars (tensorInr R B).hom).obj
          ((ModuleCat.extendScalars (algHom R B).hom).obj M₂)) ≃
      ((ModuleCat.extendScalars (algebraMap R (B ⊗[R] B))).obj M₁ ⟶
        (ModuleCat.extendScalars (algebraMap R (B ⊗[R] B))).obj M₂) :=
  Iso.homCongr (cancelExtendScalarsInl R B M₁) (cancelExtendScalarsInr R B M₂)

/-- The value of `Stacks.Descent.cancelExtendScalarsHomEquiv` on `1 ⊗ m`. -/
theorem cancelExtendScalarsHomEquiv_apply_oneTmul (M₁ M₂ : ModuleCat.{u} R)
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj
          ((ModuleCat.extendScalars (algHom R B).hom).obj M₁) ⟶
        (ModuleCat.extendScalars (tensorInr R B).hom).obj
          ((ModuleCat.extendScalars (algHom R B).hom).obj M₂))
    (m : M₁) :
    cancelExtendScalarsHomEquiv R B M₁ M₂ α (oneTmul (algebraMap R (B ⊗[R] B)) m) =
      (cancelExtendScalarsInr R B M₂).hom
        (α (oneTmul (tensorInl R B).hom (oneTmul (algHom R B).hom m))) := by
  rw [cancelExtendScalarsHomEquiv, ModuleCat.homCongr_apply_apply,
    cancelExtendScalarsInl_inv_oneTmul]

end Stacks.Descent

end

end
