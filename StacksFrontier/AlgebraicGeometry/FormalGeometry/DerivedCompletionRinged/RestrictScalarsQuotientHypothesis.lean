module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorIdealImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalars

/-!
# The hypothesis `𝒪/ℐ ≅ 𝒪'/ℐ𝒪'` of [Stacks, Tag 099I]

Let `α : 𝒪 ⟶ 𝒪'` be a homomorphism of sheaves of commutative rings on a site and `ℐ ⊂ 𝒪` a sheaf
of ideals. The canonical map `q : 𝒪/ℐ ⟶ 𝒪'/ℐ𝒪'` of `𝒪`-modules is induced by `α`, since `α`
carries `ℐ` into `ℐ𝒪'`. [Stacks, Tag 099I] assumes that `q` is an isomorphism. This file shows that
this hypothesis gives the one [Stacks, Tag 099H] and [Stacks, Tag 0GLY] are stated with in this
library: an isomorphism `𝒪/ℐ ≅ (𝒪 ⊗_𝒪 𝒪')/(ℐ ⊗_𝒪 𝒪')` through which the quotient map `𝒪 ⟶ 𝒪/ℐ`
becomes `x ↦ x ⊗ 1` followed by the quotient map. The two are related by
`Stacks.Sheaves.FlatNeighbourhood.cokernelTensorIdealIso`, which identifies
`(𝒪 ⊗_𝒪 𝒪')/(ℐ ⊗_𝒪 𝒪')` with `𝒪'/ℐ𝒪'`; no flatness is needed for that.

## Main definitions

* `Stacks.SheafOfModules.DerivedRestrictScalars.quotientMap`: the canonical map
  `q : 𝒪/ℐ ⟶ 𝒪'/ℐ𝒪'`, the target read as an `𝒪`-module.

## Main results

* `Stacks.SheafOfModules.DerivedRestrictScalars.exists_quotientIso_of_isIso`: if `q` is an
  isomorphism, then so is `𝒪/ℐ ⟶ (𝒪 ⊗_𝒪 𝒪')/(ℐ ⊗_𝒪 𝒪')`, compatibly with `x ↦ x ⊗ 1`.
* `Stacks.SheafOfModules.DerivedRestrictScalars.isIso_quotientMap_iff`: the two forms of the
  hypothesis are equivalent.

## References

* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
* [Stacks Project, Tag 099I](https://stacks.math.columbia.edu/tag/099I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules.DerivedRestrictScalars

open _root_.AlgebraicGeometry
open Stacks.Sheaves.FlatNeighbourhood (RestrictedRingModule tensorUnitMap RingModule unitRingMap
  cokernelTensorIdealIso)

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O O' : Sheaf J CommRingCat.{u}} (α : O ⟶ O')
  (I : _root_.SheafOfModules.Submodule
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite J O).O)))

/-- `α` carries `ℐ` into `ℐ𝒪'`: the composite `ℐ ⟶ 𝒪 ⟶ 𝒪' ⟶ 𝒪'/ℐ𝒪'` vanishes. -/
theorem ι_comp_unitRingMap_comp_π :
    I.ι ≫ unitRingMap α ≫
      (_root_.SheafOfModules.restrictScalars (ringSheafHom (O := O) (O' := O') α)).map
        (cokernel.π (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I).ι) = 0 := by
  refine (_root_.SheafOfModules.forget _).map_injective
    (PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  have hx := RingedSite.mem_extendIdeal_of_mem (ringSheafHom (O := O) (O' := O') α) I X _ x.2
  exact congrArg (fun k ↦ k.val.app X ⟨_, hx⟩)
    (cokernel.condition (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I).ι)

/-- **The canonical map `q : 𝒪/ℐ ⟶ 𝒪'/ℐ𝒪'`** of `𝒪`-modules induced by `α`. -/
def quotientMap :
    cokernel I.ι ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafHom (O := O) (O' := O') α)).obj
      (cokernel (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I).ι) :=
  cokernel.desc I.ι (unitRingMap α ≫
    (_root_.SheafOfModules.restrictScalars (ringSheafHom (O := O) (O' := O') α)).map
      (cokernel.π (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I).ι))
    (ι_comp_unitRingMap_comp_π α I)

/-- `q` is induced by `α`: the quotient map `𝒪 ⟶ 𝒪/ℐ` followed by `q` is `α` followed by the
quotient map `𝒪' ⟶ 𝒪'/ℐ𝒪'`. -/
@[reassoc (attr := simp)]
theorem π_comp_quotientMap :
    cokernel.π I.ι ≫ quotientMap α I =
      unitRingMap α ≫
        (_root_.SheafOfModules.restrictScalars (ringSheafHom (O := O) (O' := O') α)).map
          (cokernel.π (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I).ι) :=
  cokernel.π_desc _ _ _

/-- The quotient map `𝒪 ⟶ 𝒪/ℐ` followed by `q` is `x ↦ x ⊗ 1` followed by the quotient map and
`Stacks.Sheaves.FlatNeighbourhood.cokernelTensorIdealIso`. -/
private theorem π_comp_quotientMap_eq_tensorUnitMap_comp :
    cokernel.π I.ι ≫ quotientMap α I =
      (tensorUnitMap α (RingModule O)).val ≫ cokernel.π
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule α))).map I.ι) ≫ (cokernelTensorIdealIso α I).hom := by
  rw [π_comp_quotientMap, Stacks.Sheaves.FlatNeighbourhood.π_comp_cokernelTensorIdealIso_hom]
  exact (congrArg (· ≫ (_root_.SheafOfModules.restrictScalars
    (Stacks.Sheaves.FlatNeighbourhood.ringSheafMap α)).map
      (cokernel.π (Stacks.Sheaves.FlatNeighbourhood.extendedIdeal α I).ι))
    (Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap_comp_unitIso_hom α)).symm.trans
      (Category.assoc _ _ _)

/-- **`𝒪/ℐ ≅ 𝒪'/ℐ𝒪'` in the form of [Stacks, Tag 099H].** If the canonical map
`q : 𝒪/ℐ ⟶ 𝒪'/ℐ𝒪'` is an isomorphism, then there is an isomorphism
`e : 𝒪/ℐ ≅ (𝒪 ⊗_𝒪 𝒪')/(ℐ ⊗_𝒪 𝒪')` through which the quotient map `𝒪 ⟶ 𝒪/ℐ` is `x ↦ x ⊗ 1`
followed by the quotient map: `e` is `q` followed by the inverse of
`Stacks.Sheaves.FlatNeighbourhood.cokernelTensorIdealIso`. -/
theorem exists_quotientIso_of_isIso (h : IsIso (quotientMap α I)) :
    ∃ e : cokernel I.ι ≅ cokernel
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule α))).map I.ι),
      cokernel.π I.ι ≫ e.hom = (tensorUnitMap α (RingModule O)).val ≫ cokernel.π
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule α))).map I.ι) := by
  refine ⟨asIso (quotientMap α I) ≪≫ (cokernelTensorIdealIso α I).symm, ?_⟩
  rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, ← Category.assoc, Iso.comp_inv_eq]
  exact π_comp_quotientMap_eq_tensorUnitMap_comp α I

/-- Conversely, an isomorphism `𝒪/ℐ ≅ (𝒪 ⊗_𝒪 𝒪')/(ℐ ⊗_𝒪 𝒪')` compatible with `x ↦ x ⊗ 1` makes
the canonical map `q : 𝒪/ℐ ⟶ 𝒪'/ℐ𝒪'` an isomorphism: `q` is that isomorphism followed by
`Stacks.Sheaves.FlatNeighbourhood.cokernelTensorIdealIso`. -/
theorem isIso_quotientMap_of_exists
    (h : ∃ e : cokernel I.ι ≅ cokernel
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule α))).map I.ι),
      cokernel.π I.ι ≫ e.hom = (tensorUnitMap α (RingModule O)).val ≫ cokernel.π
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule α))).map I.ι)) :
    IsIso (quotientMap α I) := by
  obtain ⟨e, he⟩ := h
  have hq : quotientMap α I = e.hom ≫ (cokernelTensorIdealIso α I).hom := by
    refine coequalizer.hom_ext ?_
    rw [π_comp_quotientMap_eq_tensorUnitMap_comp, ← Category.assoc, ← he, Category.assoc]
  rw [hq]
  infer_instance

/-- **The two forms of `𝒪/ℐ ≅ 𝒪'/ℐ𝒪'` agree**: the canonical map `q : 𝒪/ℐ ⟶ 𝒪'/ℐ𝒪'` is an
isomorphism exactly when there is an isomorphism `𝒪/ℐ ≅ (𝒪 ⊗_𝒪 𝒪')/(ℐ ⊗_𝒪 𝒪')` compatible with
`x ↦ x ⊗ 1`. -/
theorem isIso_quotientMap_iff :
    IsIso (quotientMap α I) ↔
      ∃ e : cokernel I.ι ≅ cokernel
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
            (RestrictedRingModule α))).map I.ι),
        cokernel.π I.ι ≫ e.hom = (tensorUnitMap α (RingModule O)).val ≫ cokernel.π
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
            (RestrictedRingModule α))).map I.ι) :=
  ⟨exists_quotientIso_of_isIso α I, isIso_quotientMap_of_exists α I⟩

end Stacks.SheafOfModules.DerivedRestrictScalars

end
