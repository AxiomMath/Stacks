module

public import StacksFrontier.Deformation.AlgebraExtension.PushoutFullyFaithful

/-!
# The pushout functor along a map of modules

Let `φ : ℳ ⟶ 𝒩` be a morphism of `𝒪`-modules. The square-zero pushout of `𝒪'_P` along the
composite `Ker(𝒪'_P ⟶ 𝒪) ≅ ℳ ⟶ 𝒩` is an extension `φ_* P` by `𝒩`, and `P ↦ φ_* P` is a functor
from extensions by `ℳ` to extensions by `𝒩` with the universal property
`Deformation.AlgebraExtension.IsPushoutFunctor`. This is the functor `F` "given by pushout" of
the situation preceding [Stacks Project, Tag 0D3P].

## Main definitions

* `Deformation.AlgebraExtension.pushoutFunctor`: the functor `P ↦ φ_* P`.
* `Deformation.AlgebraExtension.isPushoutFunctor_pushoutFunctor`: its universal property.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)} (φ : M ⟶ N)

/-- The pushout data of `P` along `φ`: the presentation `𝒪'_P ⟶ 𝒪` with the map
`Ker(𝒪'_P ⟶ 𝒪) ≅ ℳ ⟶ 𝒩`. -/
noncomputable def pushoutAlongData (P : AlgebraExtension a M) : PresentationPushout a N where
  presentation := P.extension
  proj := P.reduction
  locallySurjective := P.locallySurjective
  base := P.algebraMap
  base_proj := P.algebraMap_reduction
  psi :=
    { app := fun U => AddMonoidHom.mk' (fun g => φ.val.app U (P.kernelPreimage g)) fun g h =>
        (congrArg (φ.val.app U) (P.kernelPreimage_eq (g + h) _ ((P.incl_add _ _).trans
          (congrArg₂ (· + ·) (P.incl_kernelPreimage g) (P.incl_kernelPreimage h))))).trans
          (map_add (φ.val.app U).hom _ _)
      app_smul := fun U r g =>
        (congrArg (φ.val.app U) (P.kernelPreimage_eq (r • g)
          (scalar (P.reduction.hom.app U r) • P.kernelPreimage g)
          ((P.mul_incl r (P.kernelPreimage g)).symm.trans
            (congrArg (r * ·) (P.incl_kernelPreimage g))))).trans
          ((φ.val.app U).hom.map_smul _ _)
      app_map := fun {U V} f g =>
        (congrArg (φ.val.app V) (P.kernelPreimage_eq _
          (show M.val.obj V from M.val.map f (P.kernelPreimage g))
          ((P.incl_naturality f _).trans
            (congrArg (P.extension.obj.map f).hom (P.incl_kernelPreimage g))))).trans
          (PresheafOfModules.naturality_apply φ.val f (P.kernelPreimage g))
      smul_eq_zero := fun U g m => by
        have h : (show (underlyingRingSheaf O).obj.obj U from
            P.reduction.hom.app U (g : P.extension.obj.obj U)) = 0 := RingHom.mem_ker.1 g.2
        have h2 : (show (underlyingRingSheaf O).obj.obj U from
              P.reduction.hom.app U (g : P.extension.obj.obj U)) •
            (show N.val.obj U from m) = 0 := by
          rw [h, zero_smul]
        exact h2 }

variable [J.WEqualsLocallyBijective CommRingCat.{u}]

/-- The pushout `φ_* P`. -/
noncomputable abbrev pushoutAlong (P : AlgebraExtension a M) : AlgebraExtension a N :=
  (pushoutAlongData φ P).extension

/-- The comparison morphism `P ⟶ φ_* P` along `φ`. -/
noncomputable def pushoutAlongι (P : AlgebraExtension a M) : MapAlong φ P (pushoutAlong φ P) where
  hom := (pushoutAlongData φ P).lift
  reduction_comm := (pushoutAlongData φ P).lift_reduction
  algebraMap_comm := (pushoutAlongData φ P).base_lift
  kernel_comm U m := by
    have hm : P.reduction.hom.app U (P.incl m) = 0 := P.reduction_incl m
    refine ((pushoutAlongData φ P).lift_app_kernel U ⟨P.incl m, hm⟩).trans ?_
    exact congrArg (fun x => (pushoutAlong φ P).incl (φ.val.app U x))
      (P.kernelPreimage_eq _ m rfl)

/-- The morphism `φ_* P ⟶ Q` induced by a morphism `P ⟶ Q` along `φ`. -/
noncomputable def pushoutAlongDesc {P : AlgebraExtension a M} {Q : AlgebraExtension a N}
    (h : MapAlong φ P Q) : pushoutAlong φ P ⟶ Q :=
  (pushoutAlongData φ P).desc (𝟙 N) h.hom h.reduction_comm h.algebraMap_comm fun U g => by
    refine Eq.trans ?_ (h.kernel_comm U (P.kernelPreimage g))
    exact congrArg (h.hom.hom.app U) (P.incl_kernelPreimage g).symm

/-- The composite of `P ⟶ φ_* P` with `pushoutAlongDesc φ h` is the underlying morphism of `h`. -/
theorem pushoutAlongι_desc {P : AlgebraExtension a M} {Q : AlgebraExtension a N}
    (h : MapAlong φ P Q) : (pushoutAlongι φ P).hom ≫ (pushoutAlongDesc φ h).hom = h.hom :=
  (pushoutAlongData φ P).lift_desc _ _ _ _ _

/-- Morphisms out of `φ_* P` are determined by their composite with `P ⟶ φ_* P`. -/
theorem pushoutAlong_hom_ext {P : AlgebraExtension a M} {Q : AlgebraExtension a N}
    {g₁ g₂ : pushoutAlong φ P ⟶ Q}
    (h : (pushoutAlongι φ P).hom ≫ g₁.hom = (pushoutAlongι φ P).hom ≫ g₂.hom) : g₁ = g₂ :=
  MapAlong.ext_of_comp ((fibreFst P P).comp (pushoutAlongι φ P)) (by
    show (fibreFst P P).comp ((pushoutAlongι φ P).comp g₁ (Category.comp_id φ)) =
      (fibreFst P P).comp ((pushoutAlongι φ P).comp g₂ (Category.comp_id φ))
    exact congrArg (fibreFst P P).comp (MapAlong.ext h))

variable (a) in
/-- **The pushout functor along `φ`.** -/
noncomputable def pushoutFunctor : AlgebraExtension a M ⥤ AlgebraExtension a N where
  obj := pushoutAlong φ
  map {P P'} k := pushoutAlongDesc φ (MapAlong.comp k (pushoutAlongι φ P') (Category.id_comp φ))
  map_id P := pushoutAlong_hom_ext φ (by
    rw [pushoutAlongι_desc]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)
  map_comp {P P' P''} k k' := pushoutAlong_hom_ext φ (by
    rw [pushoutAlongι_desc, comp_hom', ← Category.assoc, pushoutAlongι_desc]
    change (k.hom ≫ k'.hom) ≫ _ = (k.hom ≫ (pushoutAlongι φ P').hom) ≫ _
    rw [Category.assoc, Category.assoc, pushoutAlongι_desc]
    rfl)

variable (a) in
/-- **The pushout functor has the universal property of pushout along `φ`.** -/
noncomputable def isPushoutFunctor_pushoutFunctor : IsPushoutFunctor φ (pushoutFunctor a φ) where
  ι := pushoutAlongι φ
  naturality _k := pushoutAlongι_desc φ _
  desc_unique _P _Q h := ⟨pushoutAlongDesc φ h, pushoutAlongι_desc φ h,
    fun _k hk => pushoutAlong_hom_ext φ (hk.trans (pushoutAlongι_desc φ h).symm)⟩

end Deformation.AlgebraExtension

end
