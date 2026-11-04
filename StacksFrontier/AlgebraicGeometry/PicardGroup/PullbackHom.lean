module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback homomorphism of Picard groups of schemes

Let `φ : X ⟶ Y` be a morphism of schemes. Pulling back invertible modules along `φ` induces a
homomorphism of abelian groups `φ^* : Pic(Y) ⟶ Pic(X)`. The class-level rules of
`StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback` — independence of the representative, and
additivity for the tensor product — are exactly what is needed to define it, and the composition
rule there makes the construction functorial: `(φ ≫ ψ)^* = φ^* ∘ ψ^*` and `(𝟙 X)^* = id`.

## Main definitions

* `Stacks.SheafOfModules.pullbackPicardHom`: the homomorphism `φ^* : Pic(Y) →+ Pic(X)`.
* `Stacks.SheafOfModules.picardGroupAddEquivOfIso`: an isomorphism of schemes induces an
  isomorphism of Picard groups.

## Main results

* `Stacks.SheafOfModules.pullbackPicardHom_picardClass`: `φ^*` sends the class of `L` to the
  class of `φ^*L`.
* `Stacks.SheafOfModules.pullbackPicardHom_comp` and `Stacks.SheafOfModules.pullbackPicardHom_id`:
  functoriality.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.SheafOfModules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- The pullback of a Picard class along `φ : X ⟶ Y`, computed on a chosen representative. -/
def pullbackPicardFun (φ : X ⟶ Y) (x : Y.picardGroup) : X.picardGroup :=
  pullbackPicardClass φ (Classical.choose (exists_picardClass_eq Y.presheaf Y.ringCatIsSheaf x))
    (Classical.choose (Classical.choose_spec
      (exists_picardClass_eq Y.presheaf Y.ringCatIsSheaf x)))

/-- The pullback of a Picard class does not depend on the chosen representative. -/
theorem pullbackPicardFun_picardClass (φ : X ⟶ Y)
    (L : _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : IsInvertible Y.presheaf Y.ringCatIsSheaf L) :
    pullbackPicardFun φ (Y.picardClass L hL) = pullbackPicardClass φ L hL := by
  have h := Classical.choose_spec (Classical.choose_spec
    (exists_picardClass_eq Y.presheaf Y.ringCatIsSheaf (Y.picardClass L hL)))
  obtain ⟨e⟩ := (picardClass_eq_iff Y.presheaf Y.ringCatIsSheaf _ _ _ _).mp h
  exact pullbackPicardClass_congr φ _ _ _ _ e

/-- **The pullback homomorphism `φ^* : Pic(Y) →+ Pic(X)`** of a morphism of schemes
`φ : X ⟶ Y`. -/
def pullbackPicardHom (φ : X ⟶ Y) : Y.picardGroup →+ X.picardGroup :=
  AddMonoidHom.mk' (pullbackPicardFun φ) fun x y => by
    obtain ⟨L, hL, rfl⟩ := exists_picardClass_eq Y.presheaf Y.ringCatIsSheaf x
    obtain ⟨N, hN, rfl⟩ := exists_picardClass_eq Y.presheaf Y.ringCatIsSheaf y
    have hLN := isInvertible_schemeTensor Y L N hL hN
    have h := Y.picardClass_tensorSheaf L N hL hN hLN
    change pullbackPicardFun φ (Y.picardClass L hL + Y.picardClass N hN) =
      pullbackPicardFun φ (Y.picardClass L hL) + pullbackPicardFun φ (Y.picardClass N hN)
    exact (congrArg (pullbackPicardFun φ) h).trans
      ((pullbackPicardFun_picardClass φ (schemeTensor Y L N) hLN).trans
        ((pullbackPicardClass_tensorSheaf φ L N hL hN hLN).trans
          (congrArg₂ (· + ·) (pullbackPicardFun_picardClass φ L hL).symm
            (pullbackPicardFun_picardClass φ N hN).symm)))

/-- `φ^*` sends the class of an invertible module `L` to the class of `φ^*L`. -/
@[simp, ega "0 5.4.8" "special case"]
theorem pullbackPicardHom_picardClass (φ : X ⟶ Y)
    (L : _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hL : IsInvertible Y.presheaf Y.ringCatIsSheaf L) :
    pullbackPicardHom φ (Y.picardClass L hL) = pullbackPicardClass φ L hL :=
  pullbackPicardFun_picardClass φ L hL

/-- **Functoriality of the pullback homomorphism:** `(φ ≫ ψ)^* = φ^* ∘ ψ^*`. -/
theorem pullbackPicardHom_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    pullbackPicardHom (φ ≫ ψ) = (pullbackPicardHom φ).comp (pullbackPicardHom ψ) := by
  ext x
  obtain ⟨L, hL, rfl⟩ := exists_picardClass_eq Z.presheaf Z.ringCatIsSheaf x
  have := hL
  have hψ : IsInvertible Y.presheaf Y.ringCatIsSheaf
      ((RingedSpaceModuleAdjunction.modulePullback ψ.toLRSHom.toShHom).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible _ L
  exact (pullbackPicardHom_picardClass (φ ≫ ψ) L hL).trans
    ((pullbackPicardClass_comp φ ψ L hL hψ).trans
      ((pullbackPicardHom_picardClass φ _ hψ).symm.trans
        (congrArg (pullbackPicardHom φ) (pullbackPicardHom_picardClass ψ L hL).symm)))

/-- **The pullback homomorphism of an identity is the identity.** -/
theorem pullbackPicardHom_id (X : AlgebraicGeometry.Scheme.{u}) :
    pullbackPicardHom (𝟙 X) = AddMonoidHom.id X.picardGroup := by
  ext x
  obtain ⟨L, hL, rfl⟩ := exists_picardClass_eq X.presheaf X.ringCatIsSheaf x
  exact (pullbackPicardHom_picardClass (𝟙 X) L hL).trans (pullbackPicardClass_id L hL)

/-- `(φ ≫ ψ)^* x = φ^* (ψ^* x)`, pointwise. -/
theorem pullbackPicardHom_comp_apply (φ : X ⟶ Y) (ψ : Y ⟶ Z) (x : Z.picardGroup) :
    pullbackPicardHom (φ ≫ ψ) x = pullbackPicardHom φ (pullbackPicardHom ψ x) := by
  rw [pullbackPicardHom_comp]
  rfl

/-- **An isomorphism of schemes induces an isomorphism of Picard groups**, pulling back along
the inverse. -/
def picardGroupAddEquivOfIso (e : X ≅ Y) : X.picardGroup ≃+ Y.picardGroup where
  toFun := pullbackPicardHom e.inv
  invFun := pullbackPicardHom e.hom
  left_inv x := by
    rw [← pullbackPicardHom_comp_apply, e.hom_inv_id, pullbackPicardHom_id]
    rfl
  right_inv x := by
    rw [← pullbackPicardHom_comp_apply, e.inv_hom_id, pullbackPicardHom_id]
    rfl
  map_add' := map_add _

/-- The isomorphism `picardGroupAddEquivOfIso e` sends a class `x` to its pullback along
`e.inv`. -/
@[simp]
theorem picardGroupAddEquivOfIso_apply (e : X ≅ Y) (x : X.picardGroup) :
    picardGroupAddEquivOfIso e x = pullbackPicardHom e.inv x :=
  rfl

end Stacks.SheafOfModules

end
