module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AbstractKunnethMapSecondFactor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsTensorComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.KunnethOverFieldMapComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsProperProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperKunneth.KunnethFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsOpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsProperBaseChangeUnit

/-!
# The Künneth step of [Stacks, Tag 0F1H] on `D(-_étale, ℤ/n)`

Let `k` be a separably closed field, `j : U ⟶ X` an open immersion of schemes of finite type over
`k`, `Y` a proper scheme over `k`, and consider
```
Y ×_k X  ←-h-  Y ×_k U
   |q              |p
   X     ←-j-      U
```
The last paragraph of the proof of [Stacks, Tag 0F1H] computes both
`RΓ(Y ×_k X, q⁻¹Rj_*𝓕)` and `RΓ(Y ×_k X, Rh_*p⁻¹𝓕) = RΓ(Y ×_k U, p⁻¹𝓕)` by the Künneth formula
[Stacks, Tag 0F14] as `RΓ(U, 𝓕) ⊗^L RΓ(Y, ℤ/n)`, and concludes that the base change map
`q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` induces an isomorphism on `RΓ(Y ×_k X, -)`.

This file runs that argument on the derived categories `D(-_étale, ℤ/n)` of the Künneth section
(`Stacks.EtaleCohomology.EtaleCoefficients.DerivedModules`): for every `G ∈ D(U_étale, ℤ/n)` the
direct image to `Spec k` of the base change map `q⁻¹Rj_*G ⟶ Rh_*p⁻¹G` is an isomorphism
(`isIso_pushforward_map_baseChangeMap_of_isProper`). It is the abstract Künneth step
`Stacks.Cohomology.AbstractKunnethMap.isIso_map_tensor_baseChangeMap_of_kunneth` at `E = ℤ/n`,
whose inputs are

* the composition laws of [Stacks, Tag 07A4] for the identifications of composite inverse images
  (`tensorCompat_pullbackCompIso`, `tensorCompat_pullbackCongr`);
* the projection formula to a separably closed point
  (`isIso_projectionMap_of_isSepClosed`, the point case of [Stacks, Tag 0F0E], with
  [Stacks, Tag 0F10] for the finiteness of the cohomological dimension);
* [Stacks, Tag 0F0G] for the base changes `q` and `p` of the proper `Y ⟶ Spec k`;
* base change along the open immersion `j` (`isIso_baseChangeMap_app_of_isOpenImmersion`);
* the projection map of `h` at the unit, and `ℤ/n ⊗^L - = id`;
* proper base change for `Y ⟶ Spec k` along `X ⟶ Spec k` at `ℤ/n`
  (`Stacks.EtaleCohomology.EtaleCoefficients.isIso_baseChangeMap_app_unit_of_isProper`).

## Main results

* `isIso_projectionMap_of_isSepClosed` — the projection formula to a separably closed point.
* `isIso_baseChangeMap_app_of_isOpenImmersion` — base change along an open immersion on `D⁺`.
* `isIso_pushforward_map_baseChangeMap_of_isProper` — the Künneth step of [Stacks, Tag 0F1H].

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.AbstractKunnethMap
open scoped CategoryTheory.Prod

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `Stacks.EtaleCohomology.EtaleCoefficients.pullback` and `baseChangeMap`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Kunneth/EtaleKunnethMap.lean:199`) are built on
-- `derivedPullback`, stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

/-! ### The composition law of Stacks 07A4 -/

section TensorCompat

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The identification `f⁻¹ ⋙ p⁻¹ ≅ (p ≫ f)⁻¹` carries the composite comparison of Stacks 07A4
to the comparison along `p ≫ f`.** -/
theorem tensorCompat_pullbackCompIso {W X Y : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ Y) :
    TensorCompat (compTensor (pullbackTensorIso Λ f).hom (pullbackTensorIso Λ p).hom)
      (pullbackTensorIso Λ (p ≫ f)).hom (pullbackCompIso Λ p f).hom := fun M N => by
  simpa using pullbackCompIso_hom_app_comp_pullbackTensorIso_hom_app Λ p f M N

/-- The identification of the inverse images along equal morphisms carries one comparison of
Stacks 07A4 to the other. -/
theorem tensorCompat_pullbackCongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f') :
    TensorCompat (pullbackTensorIso Λ f).hom (pullbackTensorIso Λ f').hom
      (pullbackCongr Λ e).hom := by
  subst e
  exact TensorCompat.refl _

end TensorCompat

/-! ### The projection formula to a separably closed point -/

section Point

/-- Sheafification of presheaves of sets on the small model `AsSmall X.Etale`, at the universe of
its objects. -/
local instance (priority := high) hasSheafify_etaleRingedSite_type_of_point (Λ : Type)
    [CommRing Λ] (Z : Scheme.{u}) :
    HasSheafify (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (etaleRingedSite.{u, 0} Λ Z)).J
      (Type (u + 1)) :=
  instHasSheafifyType.{u + 1, u + 1} _

/-- **The projection formula to a separably closed point** on `D(-_étale, ℤ/n)` of the Künneth
section: for `k` separably closed, `g : X ⟶ Spec k` of finite type and `n ≥ 1`, the projection map
`A ⊗^L Rg_*B ⟶ Rg_*(g⁻¹A ⊗^L B)` is an isomorphism for all unbounded `A` and `B`. This is the
point case of [Stacks, Tag 0F0E], the cohomological dimension of `g` being finite by
[Stacks, Tag 0F10]. -/
theorem isIso_projectionMap_of_isSepClosed (n : ℕ) [NeZero n] (k : Type u) [Field k]
    [IsSepClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    [QuasiCompact g] (A : DerivedModules (ULift.{u + 1} (ZMod n)) (Spec (.of k)))
    (B : DerivedModules (ULift.{u + 1} (ZMod n)) X) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod n)) g A B) := by
  have : CompactSpace X := Scheme.compactSpace_of_finiteType k g
  have : QuasiSeparatedSpace X := Scheme.quasiSeparatedSpace_of_finiteType k g
  have hk : Scheme.etaleCohomologicalDimension (Spec (.of k)) < ⊤ :=
    (Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k).trans_lt ENat.top_pos
  have hcd := Scheme.Hom.etaleCohomologicalDimension_lt_top_of_isSepClosed g
    (Scheme.etaleCohomologicalDimension_lt_top_of_finiteType k g hk)
  rw [projectionMap, Stacks.Cohomology.AbstractKunnethMap.isIso_projectionMap_iff_of_iso_objects
    _ _ _ _ ((etaleModulesDerivedComparison (ZMod n) (Spec (.of k))).objObjPreimageIso A).symm
    ((etaleModulesDerivedComparison (ZMod n) X).objObjPreimageIso B).symm, ← projectionMap,
    ← isIso_etalePushforwardProjectionMap_iff_isIso_projectionMap]
  exact isIso_etalePushforwardProjectionMap_zmod_of_etaleCohomologicalDimension_lt_top n
    (Nat.pos_of_ne_zero (NeZero.ne n)) k g hcd _ _

end Point


/-! ### The unit -/

section Unit

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The identification of the inverse images along equal morphisms, read backwards. -/
theorem pullbackCongr_symm {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f') :
    (pullbackCongr Λ e).symm = pullbackCongr Λ e.symm := by
  subst e
  rfl

/-- **Tensoring by the inverse image of the structure sheaf is the identity**: for
`r : W ⟶ Y`, a morphism `φ` of `D(W_étale, Λ)` and a morphism `c : W ⟶ S`, the direct image along
`c` of `r⁻¹Λ̲[0] ⊗^L φ` is invertible exactly when the direct image of `φ` is. -/
theorem isIso_pushforward_map_tensor_pullback_unit_iff {W Y S : Scheme.{u}} (r : W ⟶ Y)
    (c : W ⟶ S) {A B : DerivedModules Λ W} (φ : A ⟶ B) :
    IsIso ((pushforward Λ c).map ((Functor.uncurry.obj (tensor Λ W)).map
      (𝟙 ((pullback Λ r).obj (unit Λ Y)) ×ₘ φ))) ↔ IsIso ((pushforward Λ c).map φ) := by
  have e : (Functor.uncurry.obj (tensor Λ W)).map (𝟙 ((pullback Λ r).obj (unit Λ Y)) ×ₘ φ) =
      ((tensor Λ W).obj ((pullback Λ r).obj (unit Λ Y))).map φ := by
    simp
  rw [e]
  exact NatIso.isIso_map_iff (Functor.isoWhiskerRight
    ((tensor Λ W).mapIso (pullbackUnitIso Λ r) ≪≫ tensorUnitIso Λ W) (pushforward Λ c)) φ

end Unit

/-! ### The Künneth step -/

/-- `baseChangeMap` of `D(-_étale, Λ)` is the abstract base change map of the derived adjunctions,
at the identification `(f')⁻¹ ⋙ h⁻¹ ≅ (e ≫ g)⁻¹ ≅ g⁻¹ ⋙ e⁻¹` written through `e ≫ g`. -/
theorem baseChangeMap_eq_abstract (Λ : Type (u + 1)) [CommRing Λ]
    {X' S' T Y' : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y' ⟶ X') (e : Y' ⟶ T)
    (w : e ≫ g = h ≫ f') :
    baseChangeMap Λ f' g h e w.symm =
      Stacks.Cohomology.AbstractKunnethMap.baseChangeMap (adjunction Λ g) (adjunction Λ h)
        (pullback Λ f') (pullback Λ e)
        (pullbackCompIso Λ h f' ≪≫ (pullbackCompIso Λ e g ≪≫ pullbackCongr Λ w).symm) := by
  rw [Iso.trans_symm, pullbackCongr_symm]
  rfl

/-- `baseChangeMap` of `D(-_étale, Λ)` of the square read the other way round is the abstract base
change map of the inverse of the identification `(f')⁻¹ ⋙ h⁻¹ ≅ g⁻¹ ⋙ e⁻¹`. -/
theorem baseChangeMap_eq_abstract_symm (Λ : Type (u + 1)) [CommRing Λ]
    {X' S' T Y' : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y' ⟶ X') (e : Y' ⟶ T)
    (w : e ≫ g = h ≫ f') :
    baseChangeMap Λ g f' e h w =
      Stacks.Cohomology.AbstractKunnethMap.baseChangeMap (adjunction Λ f') (adjunction Λ e)
        (pullback Λ g) (pullback Λ h)
        (pullbackCompIso Λ h f' ≪≫ pullbackCongr Λ w.symm ≪≫
          (pullbackCompIso Λ e g).symm).symm := by
  rw [Iso.trans_symm, Iso.trans_symm, Iso.symm_symm_eq, pullbackCongr_symm, Iso.trans_assoc]
  rfl

/-- **[Stacks, Tag 0F0G] on `D(-_étale, ℤ/n)`**, in the form of the projection formula map
`Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L f⁻¹K)` of the adjunction `f⁻¹ ⊣ Rf_*`. -/
theorem isIso_adjunctionTensorMap_zmod_of_isProper (n : ℕ) [NeZero n] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (E : DerivedModules (ULift.{u + 1} (ZMod n)) X)
    (K : DerivedModules (ULift.{u + 1} (ZMod n)) Y) :
    IsIso (adjunctionTensorMap (adjunction (ULift.{u + 1} (ZMod n)) f)
      (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod n)) Y))
      (Functor.uncurry.obj (tensor (ULift.{u + 1} (ZMod n)) X))
      (pullbackTensorIso (ULift.{u + 1} (ZMod n)) f).hom E K) := by
  rw [← projectionFormulaMap_eq_adjunctionTensorMap]
  exact isIso_projectionFormulaMap_zmod_of_isProper n f E K


section KunnethStep

variable {k : Type u} [Field k] [IsSepClosed k] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (j : U ⟶ X) [IsOpenImmersion j]
  [LocallyOfFiniteType sX] [QuasiCompact sX] [QuasiCompact (j ≫ sX)] [IsProper sY]
  (n : ℕ) [NeZero n]

/-- The identification `β : q⁻¹ ⋙ h⁻¹ ≅ j⁻¹ ⋙ p⁻¹` around the square `h ≫ q = p ≫ j` of
`D(-_étale, Λ)` carries the composite comparisons of Stacks 07A4 to each other. -/
theorem tensorCompat_baseChangeIso (Λ : Type (u + 1)) [CommRing Λ] {X' S' T Y' : Scheme.{u}}
    (f' : X' ⟶ S') (g : T ⟶ S') (h : Y' ⟶ X') (e : Y' ⟶ T) (w : h ≫ f' = e ≫ g) :
    TensorCompat (compTensor (pullbackTensorIso Λ f').hom (pullbackTensorIso Λ h).hom)
      (compTensor (pullbackTensorIso Λ g).hom (pullbackTensorIso Λ e).hom)
      (pullbackCompIso Λ h f' ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ e g).symm).hom :=
  (tensorCompat_pullbackCompIso Λ h f').comp ((tensorCompat_pullbackCongr Λ w).comp
    (TensorCompat.symm (tensorCompat_pullbackCompIso Λ e g)))

/-- **The Künneth step of [Stacks, Tag 0F1H]** on `D(-_étale, ℤ/n)`: let `k` be separably closed,
`j : U ⟶ X` an open immersion of schemes of finite type over `k`, `Y` proper over `k` and
`n ≥ 1`. For `h : Y ×_k U ⟶ Y ×_k X` over `Y` making the square cartesian and every
`G ∈ D(U_étale, ℤ/n)`, the base change map `q⁻¹Rj_*G ⟶ Rh_*p⁻¹G` of the square
```
Y ×_k X  ←-h-  Y ×_k U
   |q              |p
   X     ←-j-      U
```
induces an isomorphism on derived direct images to `Spec k`, that is on
`RΓ(Y ×_k X, -)`. Both sides are computed by the Künneth formula
(`Stacks.Cohomology.AbstractKunnethMap.isIso_map_tensor_baseChangeMap_of_kunneth` at `E = ℤ/n`),
and `ℤ/n ⊗^L -` is the identity. -/
theorem isIso_pushforward_map_baseChangeMap_of_isProper
    (hh : Limits.pullback sY (j ≫ sX) ⟶ Limits.pullback sY sX)
    (hhr : hh ≫ pullback.fst sY sX = pullback.fst sY (j ≫ sX))
    (sq : IsPullback (pullback.snd sY (j ≫ sX)) hh j (pullback.snd sY sX))
    (G : DerivedModules (ULift.{u + 1} (ZMod n)) U) :
    IsIso ((pushforward (ULift.{u + 1} (ZMod n)) (pullback.snd sY sX ≫ sX)).map
      ((baseChangeMap (ULift.{u + 1} (ZMod n)) (pullback.snd sY sX) j hh
        (pullback.snd sY (j ≫ sX)) sq.w.symm).app G)) := by
  rw [← isIso_pushforward_map_tensor_pullback_unit_iff _ (pullback.fst sY sX)]
  refine isIso_map_tensor_baseChangeMap_of_kunneth
    (Functor.uncurry.obj (tensor _ (Spec (.of k)))) (Functor.uncurry.obj (tensor _ X))
    (Functor.uncurry.obj (tensor _ U)) (Functor.uncurry.obj (tensor _ (Limits.pullback sY sX)))
    (Functor.uncurry.obj (tensor _ (Limits.pullback sY (j ≫ sX))))
    (adjunction _ sY) (adjunction _ sX) (adjunction _ (j ≫ sX)) (adjunction _ j)
    (adjunction _ (pullback.snd sY sX ≫ sX)) (adjunction _ hh)
    (adjunction _ (pullback.snd sY sX)) (adjunction _ (pullback.snd sY (j ≫ sX)))
    (pullback _ (pullback.fst sY sX)) (pullback _ (pullback.fst sY (j ≫ sX)))
    (pullbackTensorIso _ (pullback.snd sY sX ≫ sX)).hom (pullbackTensorIso _ hh).hom
    (pullbackTensorIso _ sX).hom (pullbackTensorIso _ (j ≫ sX)).hom (pullbackTensorIso _ j).hom
    (pullbackTensorIso _ (pullback.snd sY sX)).hom
    (pullbackTensorIso _ (pullback.snd sY (j ≫ sX))).hom
    (pullbackCompIso _ (pullback.fst sY sX) sY ≪≫
      pullbackCongr _ (IsPullback.of_hasPullback sY sX).w)
    (pullbackCompIso _ (pullback.snd sY sX) sX)
    (pullbackCompIso _ hh (pullback.fst sY sX) ≪≫ pullbackCongr _ hhr)
    _ (pullbackCompIso _ j sX)
    (tensorCompat_pullbackCompIso _ (pullback.snd sY sX) sX)
    (tensorCompat_baseChangeIso _ _ _ _ _ _) (tensorCompat_pullbackCompIso _ j sX)
    (unit _ Y) G (isIso_projectionMap_of_isSepClosed n k sX _ _)
    (isIso_projectionMap_of_isSepClosed n k (j ≫ sX) _ _)
    _ (baseChangeMap_eq_abstract _ _ _ _ _ (IsPullback.of_hasPullback sY sX).w)
    (Stacks.EtaleCohomology.EtaleCoefficients.isIso_baseChangeMap_app_unit_of_isProper n sX sY _ _
      (IsPullback.of_hasPullback sY sX))
    _ (baseChangeMap_eq_abstract_symm _ _ _ _ _ sq.w)
    (isIso_baseChangeMap_app_pullback_unit_of_isOpenImmersion n j (pullback.snd sY sX)
      (pullback.snd sY (j ≫ sX)) hh sq (pullback.fst sY sX))
    (isIso_adjunctionTensorMap_zmod_of_isProper n (pullback.snd sY sX) _ _)
    (isIso_adjunctionTensorMap_zmod_of_isProper n (pullback.snd sY (j ≫ sX)) _ _)
    (isIso_projectionMap_of_iso_unit _ _ (pullbackUnitIso _ (pullback.fst sY sX)) _)

end KunnethStep

end Stacks.EtaleCohomology.EtaleCoefficients

end
