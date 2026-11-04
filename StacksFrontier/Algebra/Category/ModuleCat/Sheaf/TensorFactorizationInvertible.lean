module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Cancel

/-!
# The tensor factorization of a morphism of invertible modules

Let `𝒩` and `ℒ` be invertible sheaves of `𝒪_Z`-modules on a ringed space and `φ : 𝒩 ⟶ ℒ` a
morphism. Then `φ` is a tensor product: there is an invertible `ℳ`, a global section `σ` of
`ℳ` and an isomorphism `𝒩 ⊗ ℳ ≅ ℒ` carrying the local pure tensor `x ⊗ σ` to `φ(x)`.

## Main results

* `CategoryTheory.MonoidalCategory.HasInverse.exists_whiskerLeft_tensorCancel`: the statement in
  an arbitrary monoidal category, for an object with a two-sided tensor inverse.
* `Stacks.SheafOfModules.TensorFactorization.exists_tensorFactorization`: the statement for the
  tensor product sheaf of [Stacks, Tag 01CA] on a ringed space, with the pure tensor spelled by
  `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry
open Stacks.RingedSpace (structureRingSheaf)
open scoped TensorProduct

universe u

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The cancellation isomorphism `X ⊗ (X⁻¹ ⊗ L) ≅ L` for an object `X` with a two-sided tensor
inverse. -/
noncomputable def HasInverse.tensorCancel {X : C} (h : HasInverse X) (L : C) :
    X ⊗ (h.inv ⊗ L) ≅ L :=
  (α_ X h.inv L).symm ≪≫ whiskerRightIso h.isoLeft L ≪≫ λ_ L

/-- The tensor factorization of a morphism out of an invertible object: a morphism `φ : X ⟶ L`
out of an object with a two-sided tensor inverse satisfies
`X ◁ a ≫ (h.tensorCancel L).hom = (ρ_ X).hom ≫ φ` for some `a : 𝟙_ C ⟶ X⁻¹ ⊗ L`. -/
theorem HasInverse.exists_whiskerLeft_tensorCancel {X : C} (h : HasInverse X) {L : C}
    (φ : X ⟶ L) :
    ∃ a : 𝟙_ C ⟶ h.inv ⊗ L, X ◁ a ≫ (h.tensorCancel L).hom = (ρ_ X).hom ≫ φ := by
  have : (tensorLeft X).IsEquivalence := h.tensorLeftEquivalence.isEquivalence_functor
  refine ⟨(tensorLeft X).preimage ((ρ_ X).hom ≫ φ ≫ (h.tensorCancel L).inv), ?_⟩
  have hp : (tensorLeft X).map
        ((tensorLeft X).preimage ((ρ_ X).hom ≫ φ ≫ (h.tensorCancel L).inv)) =
      (ρ_ X).hom ≫ φ ≫ (h.tensorCancel L).inv := (tensorLeft X).map_preimage _
  show (tensorLeft X).map _ ≫ (h.tensorCancel L).hom = _
  rw [hp, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.MonoidalCategory

namespace Stacks.SheafOfModules.TensorFactorization

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable (Z : RingedSpace.{u, u})

/-- Tensoring on the left by `N` in the monoidal structure
`Stacks.PullbackGradedAlgebra.monoidalCategory` is the tensor functor
`Stacks.SheafOfModules.Tensor.sheafTensor` at `N`. -/
noncomputable def tensorLeftIso (N : SheafOfModules.{u} (structureRingSheaf Z)) :
    MonoidalCategory.tensorLeft N ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Z.presheaf) (forget₂ CommRingCat RingCat)
          ((_root_.structureSheafRing Z).property)⟩).obj (N)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro B B' g
    have h : (𝟙 N ⊗ₘ g) =
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Z.presheaf)
            (forget₂ CommRingCat RingCat) ((_root_.structureSheafRing Z).property)⟩).obj
              (N))).map g :=
      (Stacks.SheafOfModules.Strict.tensorHom_eq_sheafifyMap Z.presheaf
        (_root_.structureSheafRing Z).property (𝟙 N) g).trans
        (congrArg (Stacks.SheafOfModules.sheafifyFunctor Z.presheaf
          (_root_.structureSheafRing Z).property).map
          (MonoidalCategory.id_tensorHom N.val g.val))
    simp only [Iso.refl_hom]
    exact (MonoidalCategory.id_tensorHom N g).symm.trans h)

/-- An invertible sheaf of modules has a two-sided tensor inverse for the monoidal structure
`Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
noncomputable def hasInverse (N : SheafOfModules.{u} (structureRingSheaf Z))
    [Stacks.SheafOfModules.IsInvertible Z.presheaf
      (_root_.structureSheafRing Z).property N] :
    MonoidalCategory.HasInverse N :=
  haveI : (MonoidalCategory.tensorLeft N).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso (tensorLeftIso Z N)).mpr
      (Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence Z.presheaf
        (_root_.structureSheafRing Z).property N)
  MonoidalCategory.hasInverse_of_tensorLeft_isEquivalence

/-- A sheaf of modules with a two-sided tensor inverse for the monoidal structure
`Stacks.PullbackGradedAlgebra.monoidalCategory` is invertible. -/
theorem isInvertible_of_tensorInverse (M : SheafOfModules.{u} (structureRingSheaf Z))
    (h : MonoidalCategory.HasInverse M) :
    Stacks.SheafOfModules.IsInvertible Z.presheaf
      (_root_.structureSheafRing Z).property M :=
  (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence Z.presheaf
      (_root_.structureSheafRing Z).property M).mpr
    ((Functor.isEquivalence_iff_of_iso (tensorLeftIso Z M)).mp
      h.tensorLeftEquivalence.isEquivalence_functor)

/-- If `𝒩 ◁ a ≫ e.hom = (ρ_ 𝒩).hom ≫ φ` for a morphism `a : 𝒪_Z ⟶ ℳ` and an isomorphism
`e : 𝒩 ⊗ ℳ ≅ 𝓛`, then `e` carries `x ⊗ σ` to `φ(x)` over every open, where `σ` is the global
section of `ℳ` corresponding to `a`. -/
theorem tensorCancel_toTensorSheafSection
    {N L M : SheafOfModules.{u} (structureRingSheaf Z)}
    (a : 𝟙_ (SheafOfModules.{u} (structureRingSheaf Z)) ⟶ M) (e : N ⊗ M ≅ L) (φ : N ⟶ L)
    (ha : N ◁ a ≫ e.hom = (ρ_ N).hom ≫ φ)
    (U : (Opens Z.carrier)ᵒᵖ) (x : N.val.obj U) :
    e.hom.val.app U
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z N M U
          (x ⊗ₜ[Z.presheaf.obj U] (_root_.SheafOfModules.unitHomEquiv M a).eval U)) =
      φ.val.app U x := by
  set t := Stacks.PullbackTensorCoherence.tmul Z N
    (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) U x
    (Stacks.PullbackTensorCoherence.oneSec Z U)
  calc _ = (N ◁ a ≫ e.hom).val.app U t :=
        (congrArg (e.hom.val.app U) (Stacks.PullbackTensorCoherence.whiskerLeft_tmul a U x
          (Stacks.PullbackTensorCoherence.oneSec Z U))).symm
    _ = ((ρ_ N).hom ≫ φ).val.app U t := by rw [ha]
    _ = φ.val.app U x :=
        (congrArg (φ.val.app U) (Stacks.PullbackTensorCoherence.rightUnitor_hom_tmul U x
          (Stacks.PullbackTensorCoherence.oneSec Z U))).trans
          (congrArg (φ.val.app U) (one_smul ((structureRingSheaf Z).obj.obj U) x))

/-- The tensor factorization of a morphism of invertible sheaves of modules: for invertible `𝒩`
and `𝓛` and a morphism `φ : 𝒩 ⟶ 𝓛` there are an invertible `ℳ`, a global section `σ` of `ℳ`
and an isomorphism `𝒩 ⊗ ℳ ≅ 𝓛` carrying the local pure tensor `x ⊗ σ` to `φ(x)` over every
open. -/
theorem exists_tensorFactorization (N L : SheafOfModules.{u} (structureRingSheaf Z))
    [Stacks.SheafOfModules.IsInvertible Z.presheaf
      (_root_.structureSheafRing Z).property N]
    [Stacks.SheafOfModules.IsInvertible Z.presheaf
      (_root_.structureSheafRing Z).property L]
    (φ : N ⟶ L) :
    ∃ (M : SheafOfModules.{u} (structureRingSheaf Z)) (σ : M.sections)
      (e : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf, ((Z)).IsSheaf⟩).obj
        (N)).obj (M)) ≅ L),
      Stacks.SheafOfModules.IsInvertible Z.presheaf
          (_root_.structureSheafRing Z).property M ∧
        ∀ (U : (Opens Z.carrier)ᵒᵖ) (x : N.val.obj U),
          e.hom.val.app U
              (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Z N M U
                (x ⊗ₜ[Z.presheaf.obj U] σ.eval U)) = φ.val.app U x :=
  let hN := hasInverse Z N
  let a := (hN.exists_whiskerLeft_tensorCancel φ).choose
  ⟨hN.inv ⊗ L, _root_.SheafOfModules.unitHomEquiv _ a, hN.tensorCancel L,
    isInvertible_of_tensorInverse Z _ (hN.hasInverseInv.tensor (hasInverse Z L)),
    tensorCancel_toTensorSheafSection Z a (hN.tensorCancel L) φ
      (hN.exists_whiskerLeft_tensorCancel φ).choose_spec⟩

end Stacks.SheafOfModules.TensorFactorization

end
