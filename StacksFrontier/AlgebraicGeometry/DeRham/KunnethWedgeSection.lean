module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethExternalTensorSection

/-!
# The degreewise de Rham Künneth isomorphism on a pure external tensor section

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `W = X ×_S Y`. By
`AlgebraicGeometry.Scheme.Hom.ιTotal_comp_deRhamBoxTotalDegreeIso_wedge` the restriction of the
degreewise Künneth comparison to the `(p, q)` summand of `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})` is the
composite of the comparison of [Stacks, Tag 01CI] in each factor with the wedge-product component
of the Künneth decomposition of an exterior power. This file evaluates that composite on the
section of `Ω^p_{X/S} ⊠ Ω^q_{Y/S}` attached to a local `p`-form `ω` on `X` and a local `q`-form
`η` on `Y`: the result is

`pr₁^*ω ∧ pr₂^*η`,

the wedge product in `Ω^•_{W/S}` of the pullbacks of the two forms along the projections,
restricted to the open the section lives on.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamBoxLeftPullback` and
  `AlgebraicGeometry.Scheme.Hom.deRhamBoxRightPullback`: the pullback of a local differential
  form along the first, resp. the second, projection of the fibre product, read over the base
  `S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pieceMap_deRhamBoxLeftMap_modulesPullbackUnit` and
  `AlgebraicGeometry.Scheme.Hom.pieceMap_deRhamBoxRightMap_modulesPullbackUnit`: the comparison
  of [Stacks, Tag 01CI] followed by the functorial map on exterior powers of the canonical map of
  [Stacks, Tag 01UV] is the pullback of a differential form.
* `Stacks.Tag01VSPullbackTensor.tensorSheafMapIso_inv_val_app_tensorSheafUnit`: the inverse of
  the functoriality isomorphism of the tensor product sheaf carries the sheafification unit of
  `x ⊗ y` to the unit of `eA⁻¹ x ⊗ eB⁻¹ y`.
* `AlgebraicGeometry.Scheme.Hom.prodWedgeHom_deRhamBoxSummandIso_inv_externalTensorSection`:
  **the degreewise Künneth comparison carries the external tensor section attached to `ω` and `η`
  to `pr₁^*ω ∧ pr₂^*η`.**

## Implementation notes

The two spellings bridged here are the one the Künneth decomposition is stated in — the exterior
powers `⋀ᵖ(pr₁^*Ω_{X/S})` of the pullback — and the one the external tensor section lives in — the
pullback `pr₁^*(⋀ᵖΩ_{X/S})` of the exterior power. The first is
`AlgebraicGeometry.Scheme.Hom.deRhamBoxSummandIso`, whose inverse is a functorial map of the
tensor-product bifunctor and so is computed on a sheafification unit of a pure tensor by
`tensorSheafMapIso_inv_val_app_tensorSheafUnit`; the second is
`Stacks.Tag01VSPullbackTensor.externalTensorSection_eq_tensorSheafUnit`, which exhibits the
external tensor section as such a unit.

`Stacks.Tag01VSPullbackTensor.tensorSheafMapIso` composes the two whiskerings of
`Stacks.SheafOfModules.Tensor.sheafTensor`, so its inverse presents them in the order opposite to
the one `Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit` is stated in.
The two orders are exchanged by the naturality of `(sheafTensor O).map eA⁻¹` at `eB⁻¹`, an
identity of morphisms of sheaves; matching them by definitional equality instead makes the
elaborator reduce inside the sheafification, which exhausts the heartbeat budget. That exchange
is therefore made once, at the general spelling, in
`tensorSheafMapIso_inv_val_app_tensorSheafUnit`, and the Künneth proof instantiates it.

Once the two spellings meet, the composite is the factorization
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` is defined by, so the identification
with the pullback of a form is `relativeDifferentialFormsPullback_eq` and no section-level
computation in the exterior algebra is needed. The sections are taken over an arbitrary open `W`
of `X ×_S Y` inside `pr₁⁻¹U ⊓ pr₂⁻¹V`, so the restriction to `W` is moved across the two
morphisms of sheaves by naturality.

## References

* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Tag01VSPullbackTensor
open scoped TensorProduct

universe u

namespace Stacks.Tag01VSPullbackTensor

open _root_.AlgebraicGeometry

/-- **The inverse of the functoriality isomorphism of the tensor product sheaf, on a
sheafification unit of a pure tensor**: it carries the unit of `x ⊗ y` to the unit of
`eA⁻¹ x ⊗ eB⁻¹ y`.

`Stacks.Tag01VSPullbackTensor.tensorSheafMapIso` is the composite of the two whiskerings of the
tensor product bifunctor, so its inverse presents them in the order opposite to the one
`Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit` is stated in; the two
orders are exchanged by the naturality of `(sheafTensor O).map eA⁻¹` at `eB⁻¹`, which is an
identity of morphisms of sheaves and needs no reduction inside the sheafification. -/
theorem tensorSheafMapIso_inv_val_app_tensorSheafUnit {X : Scheme.{u}} {A A' B B' : X.Modules}
    (eA : A ≅ A') (eB : B ≅ B') (V : (X.Opens)ᵒᵖ)
    (x : A'.val.obj V) (y : B'.val.obj V) :
    (tensorSheafMapIso eA eB).inv.val.app V
        ((PresheafOfModules.tensorSheafUnit A' B').app V (x ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit A B).app V
        (eA.inv.val.app V x ⊗ₜ eB.inv.val.app V y) := by
  refine Eq.trans (PresheafOfModules.hom_congr_apply'
    (congrArg (fun φ => SheafOfModules.Hom.val φ)
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        X.toRingedSpace.sheaf).map eA.inv).naturality eB.inv)) V _) ?_
  exact Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    X.toRingedSpace.sheaf A' B' eA.inv eB.inv V x y

end Stacks.Tag01VSPullbackTensor

namespace AlgebraicGeometry

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace Scheme.Hom

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The pullback `pr₁^*ω` of a local differential form on `X` along the first projection of
`X ×_S Y`**, read over the base `S`: the canonical map of [Stacks, Tag 0FL5] for the commutative
square whose vertical arrows are `pr₁ ≫ a` and the identity of `S`. -/
noncomputable abbrev deRhamBoxLeftPullback (n : ℤ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms a n, U)) :
    Γ(relativeDifferentialForms (pullback.fst a b ≫ a) n, pullback.fst a b ⁻¹ᵁ U) :=
  relativeDifferentialFormsPullback (pullback.fst a b) a (pullback.fst a b ≫ a) (𝟙 S)
    (Category.comp_id (pullback.fst a b ≫ a)).symm n U ω

/-- **The pullback `pr₂^*η` of a local differential form on `Y` along the second projection of
`X ×_S Y`**, read over the base `S`: the canonical map of [Stacks, Tag 0FL5] for the commutative
square whose vertical arrows are `pr₁ ≫ a` and the identity of `S`. -/
noncomputable abbrev deRhamBoxRightPullback (n : ℤ) (V : Y.Opens)
    (η : Γ(relativeDifferentialForms b n, V)) :
    Γ(relativeDifferentialForms (pullback.fst a b ≫ a) n, pullback.snd a b ⁻¹ᵁ V) :=
  relativeDifferentialFormsPullback (pullback.snd a b) b (pullback.fst a b ≫ a) (𝟙 S)
    ((IsPullback.of_hasPullback a b).w.symm.trans
      (Category.comp_id (pullback.fst a b ≫ a)).symm) n V η

/-- **The left leg of the Künneth comparison on a pullback unit is the pullback of a form**: the
comparison of [Stacks, Tag 01CI] followed by the functorial map on exterior powers of the
canonical map `pr₁^*Ω_{X/S} ⟶ Ω_{X ×_S Y/S}` is the factorization
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` is defined by. -/
theorem pieceMap_deRhamBoxLeftMap_modulesPullbackUnit (p : ℕ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms a (p : ℤ), U)) :
    (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap
        (deRhamBoxAlgebrasLeft a b).exterior_isExteriorAlgebra
        (deRhamAlgebras (pullback.fst a b ≫ a)).exterior_isExteriorAlgebra
        (deRhamBoxLeftMap a b) (p : ℤ)).val.app (op (pullback.fst a b ⁻¹ᵁ U))
      ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst a b)
          (relativeDifferentials a) (p : ℤ)).hom.val.app (op (pullback.fst a b ⁻¹ᵁ U))
        (modulesPullbackUnit (pullback.fst a b)
          (relativeDifferentialForms a (p : ℤ)) U ω)) =
      deRhamBoxLeftPullback a b (p : ℤ) U ω :=
  (relativeDifferentialFormsPullback_eq (pullback.fst a b) a (pullback.fst a b ≫ a) (𝟙 S)
    (Category.comp_id (pullback.fst a b ≫ a)).symm (p : ℤ) U ω).symm

/-- **The right leg of the Künneth comparison on a pullback unit is the pullback of a form**, the
statement of `AlgebraicGeometry.Scheme.Hom.pieceMap_deRhamBoxLeftMap_modulesPullbackUnit` for the
second projection. -/
theorem pieceMap_deRhamBoxRightMap_modulesPullbackUnit (q : ℕ) (V : Y.Opens)
    (η : Γ(relativeDifferentialForms b (q : ℤ), V)) :
    (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap
        (deRhamBoxAlgebrasRight a b).exterior_isExteriorAlgebra
        (deRhamAlgebras (pullback.fst a b ≫ a)).exterior_isExteriorAlgebra
        (deRhamBoxRightMap a b) (q : ℤ)).val.app (op (pullback.snd a b ⁻¹ᵁ V))
      ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd a b)
          (relativeDifferentials b) (q : ℤ)).hom.val.app (op (pullback.snd a b ⁻¹ᵁ V))
        (modulesPullbackUnit (pullback.snd a b)
          (relativeDifferentialForms b (q : ℤ)) V η)) =
      deRhamBoxRightPullback a b (q : ℤ) V η :=
  (relativeDifferentialFormsPullback_eq (pullback.snd a b) b (pullback.fst a b ≫ a) (𝟙 S)
    ((IsPullback.of_hasPullback a b).w.symm.trans
      (Category.comp_id (pullback.fst a b ≫ a)).symm) (q : ℤ) V η).symm

/-- A composite of two morphisms of presheaves of modules commutes with restriction. -/
private theorem comp_app_map_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    {M₁ M₂ M₃ : _root_.PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) {X Y : Cᵒᵖ} (i : X ⟶ Y)
    (x : M₁.obj X) :
    g.app Y (f.app Y (M₁.map i x)) = M₃.map i (g.app X (f.app X x)) := by
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]

/-- `AlgebraicGeometry.Scheme.Hom.pieceMap_deRhamBoxLeftMap_modulesPullbackUnit` on a pullback
unit restricted to a smaller open of the fibre product: both factors are morphisms of sheaves, so
the restriction passes through them. -/
theorem pieceMap_deRhamBoxLeftMap_restrict (p : ℕ) {U : X.Opens}
    (ω : Γ(relativeDifferentialForms a (p : ℤ), U)) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) :
    (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap
        (deRhamBoxAlgebrasLeft a b).exterior_isExteriorAlgebra
        (deRhamAlgebras (pullback.fst a b ≫ a)).exterior_isExteriorAlgebra
        (deRhamBoxLeftMap a b) (p : ℤ)).val.app (op W)
      ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst a b)
          (relativeDifferentials a) (p : ℤ)).hom.val.app (op W)
        (((Scheme.Modules.pullback (pullback.fst a b)).obj
            (relativeDifferentialForms a (p : ℤ))).presheaf.map (homOfLE hW₁).op
          (modulesPullbackUnit (pullback.fst a b)
            (relativeDifferentialForms a (p : ℤ)) U ω))) =
      (relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map (homOfLE hW₁).op
        (deRhamBoxLeftPullback a b (p : ℤ) U ω) := by
  exact (comp_app_map_apply _ _ (homOfLE hW₁).op _).trans
    (congrArg _ (pieceMap_deRhamBoxLeftMap_modulesPullbackUnit a b p _ _))

/-- `AlgebraicGeometry.Scheme.Hom.pieceMap_deRhamBoxRightMap_modulesPullbackUnit` on a pullback
unit restricted to a smaller open of the fibre product. -/
theorem pieceMap_deRhamBoxRightMap_restrict (q : ℕ) {V : Y.Opens}
    (η : Γ(relativeDifferentialForms b (q : ℤ), V)) (W : (pullback a b).Opens)
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) :
    (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap
        (deRhamBoxAlgebrasRight a b).exterior_isExteriorAlgebra
        (deRhamAlgebras (pullback.fst a b ≫ a)).exterior_isExteriorAlgebra
        (deRhamBoxRightMap a b) (q : ℤ)).val.app (op W)
      ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd a b)
          (relativeDifferentials b) (q : ℤ)).hom.val.app (op W)
        (((Scheme.Modules.pullback (pullback.snd a b)).obj
            (relativeDifferentialForms b (q : ℤ))).presheaf.map (homOfLE hW₂).op
          (modulesPullbackUnit (pullback.snd a b)
            (relativeDifferentialForms b (q : ℤ)) V η))) =
      (relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map (homOfLE hW₂).op
        (deRhamBoxRightPullback a b (q : ℤ) V η) := by
  exact (comp_app_map_apply _ _ (homOfLE hW₂).op _).trans
    (congrArg _ (pieceMap_deRhamBoxRightMap_modulesPullbackUnit a b q _ _))

/-- **The degreewise de Rham Künneth comparison on a pure external tensor section is the wedge
product of the two pullbacks.** On the `(p, q)` summand it carries the section of
`Ω^p_{X/S} ⊠ Ω^q_{Y/S}` attached to a local `p`-form `ω` on `X` and a local `q`-form `η` on `Y`
to `pr₁^*ω ∧ pr₂^*η`, the product being taken in the exterior algebra `Ω^•_{X ×_S Y/S}`. -/
theorem prodWedgeHom_deRhamBoxSummandIso_inv_externalTensorSection (n : ℕ)
    (j : deRhamBoxIndex n) {U : X.Opens} {V : Y.Opens}
    (ω : Γ(relativeDifferentialForms a (j.1.1 : ℤ), U))
    (η : Γ(relativeDifferentialForms b (j.1.2 : ℤ), V))
    (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) :
    (SheafOfModules.prodWedgeHom (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b)
          (deRhamAlgebras (pullback.fst a b ≫ a)) (deRhamBoxLeftMap a b)
          (deRhamBoxRightMap a b) j.1.1 j.1.2).val.app (op W)
        ((deRhamBoxSummandIso a b n j).inv.val.app (op W)
          (externalTensorSection a b (relativeDifferentialForms a (j.1.1 : ℤ))
            (relativeDifferentialForms b (j.1.2 : ℤ)) ω η W hW₁ hW₂)) =
      SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) j.1.1 j.1.2 (op W)
        ((relativeDifferentialForms (pullback.fst a b ≫ a) (j.1.1 : ℤ)).presheaf.map
          (homOfLE hW₁).op (deRhamBoxLeftPullback a b (j.1.1 : ℤ) U ω))
        ((relativeDifferentialForms (pullback.fst a b ≫ a) (j.1.2 : ℤ)).presheaf.map
          (homOfLE hW₂).op (deRhamBoxRightPullback a b (j.1.2 : ℤ) V η)) := by
  refine Eq.trans (congrArg (fun z =>
    (SheafOfModules.prodWedgeHom (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b)
        (deRhamAlgebras (pullback.fst a b ≫ a)) (deRhamBoxLeftMap a b)
        (deRhamBoxRightMap a b) j.1.1 j.1.2).val.app (op W)
      ((deRhamBoxSummandIso a b n j).inv.val.app (op W) z))
    (externalTensorSection_eq_tensorSheafUnit a b (relativeDifferentialForms a (j.1.1 : ℤ))
      (relativeDifferentialForms b (j.1.2 : ℤ)) ω η W hW₁ hW₂)) ?_
  refine Eq.trans (congrArg (fun z =>
    (SheafOfModules.prodWedgeHom (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b)
        (deRhamAlgebras (pullback.fst a b ≫ a)) (deRhamBoxLeftMap a b)
        (deRhamBoxRightMap a b) j.1.1 j.1.2).val.app (op W) z)
    (tensorSheafMapIso_inv_val_app_tensorSheafUnit
      (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst a b)
        (relativeDifferentials a) (j.1.1 : ℤ)).symm
      (Scheme.Modules.exteriorPowerPullbackIso (pullback.snd a b)
        (relativeDifferentials b) (j.1.2 : ℤ)).symm (op W) _ _)) ?_
  refine Eq.trans (SheafOfModules.prodWedgeHom_unit (deRhamBoxAlgebrasLeft a b)
    (deRhamBoxAlgebrasRight a b) (deRhamAlgebras (pullback.fst a b ≫ a))
    (deRhamBoxLeftMap a b) (deRhamBoxRightMap a b) j.1.1 j.1.2 (op W) _ _) ?_
  exact congrArg₂ (fun u v => ((deRhamAlgebras (pullback.fst a b ≫ a)).exterior.mul
      (j.1.1 : ℤ) (j.1.2 : ℤ)).app (op W) u v)
    (pieceMap_deRhamBoxLeftMap_restrict a b j.1.1 ω W hW₁)
    (pieceMap_deRhamBoxRightMap_restrict a b j.1.2 η W hW₂)

end Scheme.Hom

end AlgebraicGeometry

end
