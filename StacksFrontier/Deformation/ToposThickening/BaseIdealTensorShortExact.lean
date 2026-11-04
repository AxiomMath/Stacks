module

public import StacksFrontier.Deformation.ToposThickening.QuotientLiftObstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatExtendScalars
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.Deformation.ToposThickening.FlatLiftPullbackIdealComparison

/-!
# Tensoring a short exact sequence with a flat third term by the pulled-back base ideal

Remark 0CZU (Stacks Project) tensors a short exact sequence `0 ⟶ 𝒦 ⟶ ℱ ⟶ 𝒬 ⟶ 0` of
`O`-modules with the pullback `f^*𝒥` of the ideal of the thickening of the base: "since `𝒬` is
flat over `T`, we obtain a short exact sequence
`0 ⟶ 𝒦 ⊗_{O_T} 𝒥 ⟶ ℱ ⊗_{O_T} 𝒥 ⟶ 𝒬 ⊗_{O_T} 𝒥 ⟶ 0`". This file proves that.

`f^*𝒥` is the extension of scalars along `f^♯ : f⁻¹O_ℬ ⟶ O` of `f⁻¹𝒥`, and tensoring an `O`-module
with an extension of scalars is, on underlying sheaves of abelian groups, tensoring its
restriction to `f⁻¹O_ℬ` with `f⁻¹𝒥` (`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso`).
Restriction of scalars is exact, and over `f⁻¹O_ℬ` Stacks 03EX applies to the flat third term.

## Main results

* `Deformation.ToposThickening.shortExact_map_sheafTensorFlipObj_extendScalars`: for a morphism
  `φ : O₁ ⟶ O₂` of sheaves of commutative rings, tensoring a short exact sequence of
  `O₂`-modules whose third term is flat over `O₁` with an extension of scalars `O₂ ⊗_{O₁} G`
  gives a short exact sequence.
* `Deformation.ToposThickening.shortExact_map_baseIdealTensor_of_isFlat`: **Remark 0CZU**, the
  sequence `0 ⟶ 𝒦 ⊗ f^*𝒥 ⟶ ℱ ⊗ f^*𝒥 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ 0` is short exact when `𝒬` is flat over the
  base.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

universe v u w vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

section ExtendScalars

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- Tensoring on the right with a fixed sheaf of modules preserves zero morphisms, being right
exact. -/
instance preservesZeroMorphisms_sheafTensorFlipObj (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf O)) :
    ((sheafTensor.{u, v, w, w, w} O).flip.obj G).PreservesZeroMorphisms := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj O G
  infer_instance

/-- **Tensoring by an extension of scalars, on underlying sheaves of abelian groups**: for
`φ : O₁ ⟶ O₂` and an `O₁`-module `G`, the functor `H ↦ H ⊗_{O₂} (O₂ ⊗_{O₁} G)` followed by
forgetting to sheaves of abelian groups is `H ↦ H|_{O₁} ⊗_{O₁} G` followed by forgetting. -/
noncomputable def tensorExtendScalarsToSheafIso (φ : O₁ ⟶ O₂)
    (G : SheafOfModules.{w} (ringSheaf O₁)) :
    SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap φ) ⋙
        (sheafTensor.{u, v, w, w, w} O₁).flip.obj G ⋙ SheafOfModules.toSheaf (ringSheaf O₁) ≅
      (sheafTensor.{u, v, w, w, w} O₂).flip.obj
          ((Stacks.FlatChangeOfRings.extendScalars φ).obj G) ⋙
        SheafOfModules.toSheaf (ringSheaf O₂) :=
  Stacks.FlatChangeOfRings.tensorBaseChangeSheafIso φ G ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.forget (ringSheaf O₂))
        (Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso φ G))
      (SheafOfModules.toSheaf (ringSheaf O₂))

/-- **Stacks 03EX along a change of rings.** For `φ : O₁ ⟶ O₂`, tensoring a short exact sequence
of `O₂`-modules whose third term is flat over `O₁` with an extension of scalars `O₂ ⊗_{O₁} G` gives
a short exact sequence. -/
theorem shortExact_map_sheafTensorFlipObj_extendScalars (φ : O₁ ⟶ O₂)
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (Sc : ShortComplex (SheafOfModules.{w} (ringSheaf O₂))) (hSc : Sc.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O₁)
      ((SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap φ)).obj
        Sc.X₃)) :
    (Sc.map ((sheafTensor.{u, v, w, w, w} O₂).flip.obj
      ((Stacks.FlatChangeOfRings.extendScalars φ).obj G))).ShortExact := by
  have hcolim := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj O₂
    ((Stacks.FlatChangeOfRings.extendScalars φ).obj G)
  have h₁ : (Sc.map (SheafOfModules.restrictScalars.{w}
      (Stacks.FlatChangeOfRings.ringSheafMap φ))).ShortExact := hSc.map_of_exact _
  have h₂ := Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj O₁ _ h₁ hflat G
  have hm₁ : Mono ((SheafOfModules.toSheaf (ringSheaf O₁)).map
      (((sheafTensor.{u, v, w, w, w} O₁).flip.obj G).map
        ((SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap φ)).map
          Sc.f))) := by
    have : Mono (((sheafTensor.{u, v, w, w, w} O₁).flip.obj G).map
        ((SheafOfModules.restrictScalars.{w} (Stacks.FlatChangeOfRings.ringSheafMap φ)).map
          Sc.f)) := h₂.mono_f
    exact Functor.map_mono _ _
  have hnat := (tensorExtendScalarsToSheafIso φ G).hom.naturality Sc.f
  have hm₂ : Mono ((SheafOfModules.toSheaf (ringSheaf O₂)).map
      (((sheafTensor.{u, v, w, w, w} O₂).flip.obj
        ((Stacks.FlatChangeOfRings.extendScalars φ).obj G)).map Sc.f)) := by
    have e : (SheafOfModules.toSheaf (ringSheaf O₂)).map
        (((sheafTensor.{u, v, w, w, w} O₂).flip.obj
          ((Stacks.FlatChangeOfRings.extendScalars φ).obj G)).map Sc.f) =
        (tensorExtendScalarsToSheafIso φ G).inv.app Sc.X₁ ≫
          (SheafOfModules.toSheaf (ringSheaf O₁)).map
            (((sheafTensor.{u, v, w, w, w} O₁).flip.obj G).map
              ((SheafOfModules.restrictScalars.{w}
                (Stacks.FlatChangeOfRings.ringSheafMap φ)).map Sc.f)) ≫
          (tensorExtendScalarsToSheafIso φ G).hom.app Sc.X₂ :=
      ((tensorExtendScalarsToSheafIso φ G).inv_hom_id_app_assoc Sc.X₁ _).symm.trans
        (congrArg _ hnat.symm)
    rw [e]
    infer_instance
  have hmono : Mono (((sheafTensor.{u, v, w, w, w} O₂).flip.obj
      ((Stacks.FlatChangeOfRings.extendScalars φ).obj G)).map Sc.f) :=
    (SheafOfModules.toSheaf (ringSheaf O₂)).mono_of_mono_map hm₂
  have := hSc.epi_g
  exact ShortComplex.ShortExact.mk'
    (hSc.exact.map_of_epi_of_preservesCokernel _ hSc.epi_g inferInstance) hmono
    (show Epi (((sheafTensor.{u, v, w, w, w} O₂).flip.obj
      ((Stacks.FlatChangeOfRings.extendScalars φ).obj G)).map Sc.g) from inferInstance)

end ExtendScalars

section BaseIdeal

variable {X : RingedTopos.{v, u, w}} {S : RingedTopos.{vS, uS, wS}}
  {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  (t : RingedToposHom S S') (f : RingedToposHom X S) (ht : FirstOrderThickening t)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Remark 0CZU: `0 ⟶ 𝒦 ⊗ f^*𝒥 ⟶ ℱ ⊗ f^*𝒥 ⟶ 𝒬 ⊗ f^*𝒥 ⟶ 0` is short exact** when `𝒬` is flat
over the base. For a short exact sequence `0 ⟶ 𝒦 ⟶ ℱ ⟶ 𝒬 ⟶ 0` of `O`-modules with `𝒬` flat over
`f⁻¹O_ℬ`, tensoring with the pullback `f^*𝒥` of the ideal of the thickening `t` of the base gives a
short exact sequence: `f^*𝒥` is the extension of scalars of `f⁻¹𝒥` along `f^♯`, so this is
Stacks 03EX over `f⁻¹O_ℬ`
(`Deformation.ToposThickening.shortExact_map_sheafTensorFlipObj_extendScalars`). -/
theorem shortExact_map_baseIdealTensor_of_isFlat
    (Sc : ShortComplex (SheafOfModules.{w} (ringSheaf X.O))) (hSc : Sc.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f.fSharpInverseImage)).obj Sc.X₃)) :
    (Sc.map (baseIdealTensor t f ht)).ShortExact :=
  shortExact_map_sheafTensorFlipObj_extendScalars
    (Stacks.Sheaves.RingedToposModules.fSharpCommRingSheaf f.toRingedToposModulesHom)
    ((Stacks.Sheaves.RingedToposModules.inverseImageModules f.toToposHom (ringSheaf S.O)).obj
      ((t.toRingedToposModulesHom.pullbackModules).obj ht.idealOfThickening.I)) Sc hSc hflat

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Remark 0CZU, for a quotient `ℱ ⟶ ℱ/𝒦`**: if `ℱ/𝒦` is flat over the base, then
`0 ⟶ 𝒦 ⊗ f^*𝒥 ⟶ ℱ ⊗ f^*𝒥 ⟶ (ℱ/𝒦) ⊗ f^*𝒥 ⟶ 0` is short exact. -/
theorem shortExact_map_baseIdealTensor_of_isFlat_cokernel
    {M : SheafOfModules.{w} (ringSheaf X.O)} (K : Subobject M)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f.fSharpInverseImage)).obj (cokernel K.arrow))) :
    ((ShortComplex.mk K.arrow (cokernel.π K.arrow) (cokernel.condition _)).map
      (baseIdealTensor t f ht)).ShortExact :=
  shortExact_map_baseIdealTensor_of_isFlat t f ht _
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      inferInstance inferInstance) hflat

end BaseIdeal

end Deformation.ToposThickening

end
