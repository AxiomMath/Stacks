module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageConormalBaseChange
public import StacksFrontier.Deformation.ToposThickening.InverseImageExtensionSolutions
public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionClassCanonical

/-!
# The identification `g⁻¹(ℐ/ℐ²) ≅ ℐ'/ℐ'²` on the square-zero ideal of a solution

Let `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be a morphism of ringed topoi and `𝒪_{𝒞'} ⟶ 𝒪_𝒞` the
reduction of a solution of the deformation problem of Stacks 0GQ5, with square-zero ideal `ℱ`
identified with `ℐ/ℐ²` for `ℐ = Ker(𝒪_{𝒞'} ⟶ 𝒪_𝒞)`. This file computes the identification
`g⁻¹(ℐ/ℐ²) ≅ ℐ'/ℐ'²` of Stacks 08TZ (with `ℐ' = Ker(g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞)`) on the classes of
local sections of `ℐ'`: the inverse of the identification, followed by `g⁻¹(ℐ/ℐ² ≅ ℱ)` and the
inclusion `g⁻¹ℱ ⟶ g⁻¹𝒪_{𝒞'}`, sends the class of a local section `x` of `ℐ'` back to `x`.

## Main results

* `InverseImageExtension.invKernelIncl_inverseImageConormalSheafIso_inv`, in the namespace
  `Deformation.ToposThickening`: the computation above.

## References

* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u v' u' w'

namespace Deformation.ToposThickening.InverseImageExtension

/-- A composite `z`, `h`, `k` of morphisms of sheaves of modules across two restrictions of
scalars, read on underlying sheaves of sets, acts on local sections as the composite does. -/
lemma sectionsFunctor_map_moduleSheafFunctor_comp_comp {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget AddCommGrpCat.{u})]
    {R R' : Sheaf J RingCat.{u}} (α β : R ⟶ R') {M Q' : SheafOfModules.{u} R}
    {N P : SheafOfModules.{u} R'} (z : M ⟶ (SheafOfModules.restrictScalars α).obj N)
    (h : N ⟶ P) (k : (SheafOfModules.restrictScalars β).obj P ⟶ Q') (V : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J V).obj ((Sheaf.moduleSheafFunctor R).obj M)) :
    @Eq ↥(Q'.val.obj V)
      ((Sheaf.sectionsFunctor J V).map ((Sheaf.moduleSheafFunctor R).map z ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α N) ≫
          (Sheaf.moduleSheafFunctor R').map h ≫
            eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars β P).symm ≫
              (Sheaf.moduleSheafFunctor R).map k) x)
      (k.val.app V (h.val.app V (z.val.app V x))) :=
  rfl

open Stacks.Sites.Conormal
open Stacks.Sheaves.RingedToposModules (inverseImageModules moduleSheaf_restrictScalars
  conormalClassHom)
open RingedToposExtensionProblem (ofTrivialBase)

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {Y X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {f : RingedToposHom X B}
  {F : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)}
  (Q : (ofTrivialBase f F).CompatibleFirstOrderThickening)
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]

/-- **The class map of the reduction, followed by the identification `ℐ/ℐ² ≅ ℱ` and the inclusion
`ℱ ⟶ 𝒪_{𝒞'}`, is the inclusion `ℐ ⟶ 𝒪_{𝒞'}`**, on underlying sheaves of sets. -/
theorem conormalClassHom_comp_kernelConormalToModule_comp_kernelInclSheafSets :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).map
        (conormalClassHom.{u, u, u} Q.reduction) ≫
      eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{u, u, u} X.J Q.reduction)
        (conormalModule.{u, u, u} X.J Q.reduction)) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        Q.kernelConormalToModule ≫
      eqToHom (moduleSheaf_restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map Q.reduction) F).symm ≫
      kernelInclSheafSets Q =
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).map
      (SheafOfModules.kerIota (presentationModuleHom.{u, u, u} X.J
        (presentationRingHom.{u, u, u} X.J Q.reduction))) := by
  refine Sheaf.hom_ext_sections fun V t ↦ ?_
  have hy := coe_mem_kernelIdeal.{u, u, u} X.J Q.reduction
    (presentationRingHom.{u, u, u} X.J Q.reduction) rfl V t
  have h₁ := conormalModuleHomEquivOf_app_conormalClass.{u, u, u} X.J Q.reduction
    (presentationRingHom.{u, u, u} X.J Q.reduction) rfl Q.extension (𝟙 _) _ (𝟙 _) V t ⟨t.1, hy⟩ rfl
  have h₂ := conormalDesc_toAssociatedModule.{u, u, u, u} Q.reduction (ofTrivialBase f F).G
    Q.kernelIdentification V ⟨t.1, hy⟩
  have h₃ := Q.incl_kernelPreimage ⟨t.1, hy⟩
  have hL := sectionsFunctor_map_moduleSheafFunctor_comp_comp
    (presentationRingHom.{u, u, u} X.J Q.reduction)
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map Q.reduction)
    (conormalClassHom.{u, u, u} Q.reduction) Q.kernelConormalToModule Q.kernelInclusion V t
  exact hL.trans ((congrArg (Q.kernelInclusion.val.app V)
    ((congrArg (Q.kernelConormalToModule.val.app V) h₁).trans h₂)).trans h₃)

/-- A composite with an identification in the middle, read on local sections after a functor
of sheaves of sets, is the composite of the two remaining maps on local sections. -/
lemma sectionsFunctor_map_functor_map_comp_eqToHom_comp {C D : Type u} [Category.{u} C]
    [Category.{u} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (Φ : Sheaf K (Type u) ⥤ Sheaf J (Type u)) {X₁ X₂ X₃ X₅ : Sheaf K (Type u)}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (p : X₃ = X₃) (c : X₃ ⟶ X₅) (U : Cᵒᵖ)
    (v : (Sheaf.sectionsFunctor J U).obj (Φ.obj X₁)) :
    (Sheaf.sectionsFunctor J U).map (Φ.map (a ≫ b ≫ eqToHom p ≫ c)) v =
      (Sheaf.sectionsFunctor J U).map (Φ.map c)
        ((Sheaf.sectionsFunctor J U).map (Φ.map b)
          ((Sheaf.sectionsFunctor J U).map (Φ.map a) v)) := by
  rw [eqToHom_refl, Category.id_comp, Φ.map_comp, Φ.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

variable [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify Y.J CommRingCat.{u}]
  (g : RingedToposHom Y X)

omit [HasWeakSheafify X.J CommRingCat] [HasWeakSheafify Y.J CommRingCat] in
/-- **The inverse of `g⁻¹(ℐ/ℐ²) ≅ ℐ'/ℐ'²` on classes.** For a local section `x` of the kernel
`ℐ'` of `g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞`, the inverse of the identification of Stacks 08TZ sends the class
of `x` to a local section of `g⁻¹(ℐ/ℐ²)`, which the inverse image of `ℐ/ℐ² ≅ ℱ` followed by the
inclusion `g⁻¹ℱ ⟶ g⁻¹𝒪_{𝒞'}` carries back to `x`. -/
theorem invKernelIncl_inverseImageConormalSheafIso_inv (U : Y.Cᵒᵖ)
    (x : kernelIdeal ((invImage g).map Q.reduction).hom U) :
    haveI := isLocallySurjective_invImage_map g Q.reduction Q.locallySurjective
    (show ((invImage g).obj Q.extension).obj.obj U from
      (invKernelIncl Q g).val.app U
        (((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          Q.kernelConormalToModule).val.app U
          ((Stacks.SheafOfModules.inverseImageConormalSheafIso Y.J X.J g.toToposHom
            Q.reduction).inv.val.app U
            (toAssociatedModule.{u, u, u, u} Y.J ((invImage g).obj Q.extension)
              ((invImage g).obj X.O) ((invImage g).map Q.reduction)
              (conormalPresheaf ((invImage g).map Q.reduction).hom) U
              ((kernelIdeal ((invImage g).map Q.reduction).hom U).toCotangent x))))) = x.1 := by
  have := isLocallySurjective_invImage_map g Q.reduction Q.locallySurjective
  have hx : (Stacks.Sheaves.RingedToposModules.inverseImagePresentationRingHom.{u, u, u, u, u, u}
      g.toToposHom Q.reduction).hom.app U x.1 = 0 :=
    (congrArg (fun α ↦ α.hom.app U x.1)
      (Stacks.Sheaves.RingedToposModules.inverseImageRingMap_presentationRingHom.{u, u, u, u, u, u}
        g.toToposHom Q.reduction)).trans (RingHom.mem_ker.1 x.2)
  let y : ↥((idealSheaf.{u, u, u} Y.J
      (Stacks.Sheaves.RingedToposModules.inverseImagePresentationRingHom.{u, u, u, u, u, u}
        g.toToposHom Q.reduction)).val.obj U) := ⟨x.1, hx⟩
  have v1 := congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m y)
    (Stacks.Sheaves.RingedToposModules.inverseImageIdealIso_inv_comp_inverseImage_conormalClassHom.{
      u, u, u, u, u, u}
      g.toToposHom Q.reduction)
  have v2 := Stacks.Sites.Conormal.sectionsFunctor_map_moduleSheafFunctor_map_comp_eqToHom_comp.{u,
    u, u} Y.J (Stacks.Sheaves.RingedToposModules.inverseImagePresentationRingHom.{u, u, u, u, u, u}
      g.toToposHom Q.reduction)
    (Stacks.Sheaves.RingedToposModules.inverseImageConormalClassHom.{u, u, u, u, u, u}
      g.toToposHom Q.reduction)
    (Stacks.Sheaves.RingedToposModules.inverseImageConormalIso.{u, u, u, u, u, u}
      g.toToposHom Q.reduction).inv U y
  have v3 := conormalModuleHomEquivOf_app_conormalClass.{u, u, u} Y.J
    (g.toToposHom.inverseImageRing.map Q.reduction)
    (Stacks.Sheaves.RingedToposModules.inverseImagePresentationRingHom.{u, u, u, u, u, u}
      g.toToposHom Q.reduction)
    (Stacks.Sheaves.RingedToposModules.inverseImageRingMap_presentationRingHom.{u, u, u, u, u, u}
      g.toToposHom Q.reduction)
    (g.toToposHom.inverseImageRing.obj Q.extension) (𝟙 _) _ (𝟙 _) U y x rfl
  have v4 := fun w ↦ congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m w)
    (Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageModules_map g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Q.kernelConormalToModule)
  have H := congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map (g.toToposHom.inverseImage.map m)
      ((Sheaf.sectionsFunctor Y.J U).map ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (g.toToposHom.inverseImageRing.obj Q.extension))).map
          (Stacks.Sheaves.RingedToposModules.inverseImageIdealIso.{u, u, u, u, u, u}
            g.toToposHom Q.reduction).inv) y))
    ((Category.assoc _ _ _).trans
      (conormalClassHom_comp_kernelConormalToModule_comp_kernelInclSheafSets Q))
  have hι := congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m y)
    (Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealIso_inv_comp.{u, u,
      u, u, u, u}
      g.toToposHom Q.extension Q.reduction)
  have L := sectionsFunctor_map_functor_map_comp_eqToHom_comp g.toToposHom.inverseImage
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Q.extension)).map
        (conormalClassHom.{u, u, u} Q.reduction) ≫
      eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{u, u, u} X.J Q.reduction)
        (conormalModule.{u, u, u} X.J Q.reduction)))
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        Q.kernelConormalToModule)
    (moduleSheaf_restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map Q.reduction) F).symm
    (kernelInclSheafSets Q) U
    ((Sheaf.sectionsFunctor Y.J U).map ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (g.toToposHom.inverseImageRing.obj Q.extension))).map
          (Stacks.Sheaves.RingedToposModules.inverseImageIdealIso.{u, u, u, u, u, u}
            g.toToposHom Q.reduction).inv) y)
  have E := (congrArg ((Stacks.Sheaves.RingedToposModules.inverseImageConormalIso.{u, u, u, u, u, u}
    g.toToposHom Q.reduction).inv.val.app U) v3).symm.trans (v2.symm.trans v1.symm)
  refine (invKernelIncl_val_app Q g U _).trans ?_
  refine (congrArg ((Sheaf.sectionsFunctor Y.J U).map
    (g.toToposHom.inverseImage.map (kernelInclSheafSets Q))) ((v4 _).trans
      (congrArg ((Sheaf.sectionsFunctor Y.J U).map (g.toToposHom.inverseImage.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          Q.kernelConormalToModule))) E))).trans ?_
  exact L.symm.trans (H.trans hι)

end Deformation.ToposThickening.InverseImageExtension
