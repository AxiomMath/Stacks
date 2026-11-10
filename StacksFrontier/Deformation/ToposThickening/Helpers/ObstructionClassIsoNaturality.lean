module

public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundaryPushout

/-!
# The existence obstruction under an isomorphism of the quotient module

For a first order thickening `i` of ringed topoi, an isomorphism `α : F ≅ F'` of modules over the
base and a prescribed action `c : ℐ ⊗ F' ⟶ K`, the obstruction class of Stacks 08MF of `F` for
the action `(ℐ ⊗ α) ≫ c` is that of `F'` for `c`, precomposed with `α`. An extension of `F'` with
injective action map, read as an extension of `F` through `α`, carries a presentation of the
class of `F`.

## Main results

* `Deformation.ToposThickening.existenceObstructionClass_of_iso`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  {i : RingedToposHom X Y} (hi : FirstOrderThickening i)

omit [HasSheafify Y.J AddCommGrpCat.{w'}] in
/-- Tensoring a morphism on the left with the square-zero ideal acts on the image of a pure
tensor by applying the morphism to the second factor. -/
theorem idealTensor_map_unit_tmul
    {M N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))} (f : M ⟶ N)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (y : M.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj hi.I).map f).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val M.val)).app U (a ⊗ₜ[(baseRing i).obj.obj U] y)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
        (PresheafOfModules.tensorObj hi.I.val N.val)).app U
          (a ⊗ₜ[(baseRing i).obj.obj U] f.val.app U y) :=
  (congrArg (fun φ => φ.app U (a ⊗ₜ[(baseRing i).obj.obj U] y))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.naturality
        (PresheafOfModules.tensorHom (𝟙 hi.I.val) f.val))).symm

variable [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- Composing the quotient map of a degree-zero Yoneda extension with an isomorphism of the
quotient gives a short exact sequence. -/
private theorem yonedaExtension_shortExact_comp_iso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {B A B' : 𝒜} (E : Abelian.YonedaExtension B A 0) (e : B ≅ B') :
    (ShortComplex.mk E.f (E.g ≫ e.hom)
      (by rw [← Category.assoc, yonedaExtension_comp_zero, zero_comp])).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk E.f E.g (yonedaExtension_comp_zero E))
      (Iso.refl _) (Iso.refl _) e (by simp) (by simp))
    (yonedaExtension_shortExact E)

/-- **The obstruction class under an isomorphism of the quotient module**: for `α : F ≅ F'` and
`c : ℐ ⊗ F' ⟶ K`, `o(F, K, (ℐ ⊗ α) ≫ c)` is `o(F', K, c)` precomposed with `α`. -/
theorem existenceObstructionClass_of_iso
    {F F' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
    (α : F ≅ F') (K : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj hi.I).obj F' ⟶ K) :
    existenceObstructionClass hi F K
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj hi.I).map α.hom ≫ c) =
      (Abelian.Ext.mk₀ α.hom).comp (existenceObstructionClass hi F' K c) (zero_add 2) := by
  classical
  obtain ⟨Q, E', ⟨P'⟩⟩ := exists_extension_monoActionPresentation hi F'
  have hres := restrictScalars_exact (structureRingMap i)
  -- `E'` read as an extension of `F` through `α`
  have hSE := yonedaExtension_shortExact_comp_iso E' ((structureRestrict i).mapIso α.symm)
  let E := Abelian.shortExactYonedaExtension hSE
  let ι := ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj hi.I).mapIso α
  have hdE : (extensionActionMap hi E).1 = ι.hom ≫ (extensionActionMap hi E').1 := by
    refine extensionActionMap_unique hi E _ ?_
    intro U a x
    refine (congrArg (fun t => E'.f.val.app U ((extensionActionMap hi E').1.val.app U t))
      (idealTensor_map_unit_tmul hi α.hom U a _)).trans ?_
    refine Eq.trans ?_ ((extensionActionMap hi E').2 U a x)
    exact congrArg (fun t => E'.f.val.app U ((extensionActionMap hi E').1.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
        (PresheafOfModules.tensorObj hi.I.val F'.val)).app U
          (a ⊗ₜ[(baseRing i).obj.obj U] t))))
      (congrArg (fun φ => φ.val.app U (E'.g.val.app U x))
        ((structureRestrict i).mapIso α).inv_hom_id)
  -- the presentation of `E`
  have hz : (extensionActionMap hi E).1 ≫ P'.proj = 0 := by
    rw [hdE, Category.assoc, P'.zero, comp_zero]
  have hSP : (ShortComplex.mk _ _ hz).ShortExact := by
    refine ShortComplex.shortExact_of_iso ?_ P'.shortExact
    exact ShortComplex.isoMk ι.symm (Iso.refl _) (Iso.refl _)
      ((congrArg (ι.inv ≫ ·) hdE).trans ((ι.inv_hom_id_assoc _).trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hSD := yonedaExtension_shortExact_comp_iso P'.descent α.symm
  let D := Abelian.shortExactYonedaExtension hSD
  let P : MonoActionPresentation hi E :=
    { C := P'.C
      proj := P'.proj
      zero := hz
      shortExact := hSP
      descent := D
      comparison := P'.comparison
      comparison_left := P'.comparison_left
      comparison_right := by
        change P'.comparison ≫ (structureRestrict i).map (P'.descent.g ≫ α.inv) =
          E'.g ≫ (structureRestrict i).map α.inv
        rw [Functor.map_comp, ← Category.assoc, P'.comparison_right] }
  rw [existenceObstructionClass_eq_obstruction hi F K _ P,
    existenceObstructionClass_eq_obstruction hi F' K c P']
  -- the two classes of the presentations
  have h₁ := (yonedaExtension_shortExact D).extClass_naturality
    (yonedaExtension_shortExact P'.descent)
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := α.hom,
      comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm,
      comm₂₃ := (Category.id_comp _).trans ((Category.comp_id _).symm.trans
        ((congrArg (P'.descent.g ≫ ·) α.inv_hom_id).symm.trans (Category.assoc _ _ _).symm)) }
  have h₂ := hSP.extClass_naturality P'.shortExact
    { τ₁ := ι.hom, τ₂ := 𝟙 _, τ₃ := 𝟙 _,
      comm₁₂ := hdE.symm.trans (Category.comp_id _).symm,
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  dsimp only at h₁ h₂
  rw [Abelian.Ext.mk₀_id_comp] at h₂
  rw [Abelian.Ext.comp_mk₀_id] at h₁
  simp only [MonoActionPresentation.obstruction, MonoActionPresentation.universalClass]
  have h₂' : hSP.extClass.comp ((Abelian.Ext.mk₀ ι.hom).comp (Abelian.Ext.mk₀ c) (add_zero 0))
      (add_zero 1) = P'.shortExact.extClass.comp (Abelian.Ext.mk₀ c) (add_zero 1) := by
    rw [← Abelian.Ext.comp_assoc_of_third_deg_zero, h₂]
  rw [← Abelian.Ext.mk₀_comp_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero]
  refine (congrArg (fun z => (yonedaExtension_shortExact D).extClass.comp z
    (show 1 + 1 = 2 from rfl)) h₂').trans ?_
  refine (congrArg (fun z => z.comp (P'.shortExact.extClass.comp (Abelian.Ext.mk₀ c) (add_zero 1))
    (show 1 + 1 = 2 from rfl)) h₁).trans ?_
  exact Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (zero_add 2) (by lia)

end Deformation.ToposThickening

end
