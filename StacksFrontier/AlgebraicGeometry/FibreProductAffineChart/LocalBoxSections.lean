module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxProductUnitSections

/-!
# Sections of a box product on an affine chart, attached to local sections of the two factors

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F` and `G` be quasi-coherent modules on `X` and on `Y`, and
let `Spec (A ⊗_R B) ⟶ X ×_S Y` be an affine chart of the fibre product coming from `Spec A ⟶ X`
and `Spec B ⟶ Y` over `Spec R ⟶ S`. A section `s` of `F` over an open `U` of `X` whose preimage in
`Spec A` is everything, and a section `t` of `G` over an open `V` of `Y` with the same property,
give a global section of `F ⊠ G` on the chart. This file evaluates the chart identifications on
that section: the answer is `s ⊗ t` in `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`, where `s` and `t` are now
read as global sections of the inverse images.

## Main definitions

* `Stacks.FibreProductAffineChart.chartBoxSectionLocal`: the global section of `F ⊠ G` on the
  chart attached to `s` and `t`. It is
  `Stacks.Tag01VSPullbackTensor.externalTensorSection` over `pr₁⁻¹U ∩ pr₂⁻¹V`, pulled back along
  the chart, read over `⊤` because the chart's preimage of `pr₁⁻¹U ∩ pr₂⁻¹V` is everything.

## Main results

* `Stacks.FibreProductAffineChart.preimage_affineChart_preimage_fst` and
  `preimage_affineChart_preimage_snd`: the chart's preimage of `pr₁⁻¹U` is the preimage of `u⁻¹U`
  along `Spec (A ⟶ A ⊗_R B)`, and likewise on the right.
* `Stacks.FibreProductAffineChart.preimage_affineChart_inf_eq_top`: hence the chart's preimage of
  `pr₁⁻¹U ∩ pr₂⁻¹V` is everything as soon as `u⁻¹U` and `v⁻¹V` are.
* `Stacks.FibreProductAffineChart.chartPullbackExternalTensorIso_hom_externalTensorSection`: the
  sheaf-level chart identification on the pulled-back external tensor section, over the chart's
  preimage of `pr₁⁻¹U ∩ pr₂⁻¹V`.
* `Stacks.FibreProductAffineChart.chartPullbackExternalTensorIso_hom_chartBoxSectionLocal`: the
  same over `⊤`.
* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsIso_hom_chartBoxSectionLocal`: the
  sections of `F ⊠ G` on the chart attached to `s` and `t` correspond to `(1 ⊗ s) ⊗ (1 ⊗ t)`.
* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsBaseIso_hom_chartBoxSectionLocal`:
  over the base ring they correspond to `s ⊗ t` in `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.FibreProductAffineChart

universe u

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (u : Spec (.of A) ⟶ X) (v : Spec (.of B) ⟶ Y) (w : Spec (.of R) ⟶ S)
  (hu : Spec.map (ofHom (algebraMap R A)) ≫ w = u ≫ a)
  (hv : Spec.map (ofHom (algebraMap R B)) ≫ w = v ≫ b)
  (F : X.Modules) (G : Y.Modules)

/-- On an affine chart, the preimage of `pr₁⁻¹U` is the preimage of `u⁻¹U` along
`Spec (A ⟶ A ⊗_R B)`. -/
theorem preimage_affineChart_preimage_fst (U : X.Opens) :
    affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U)
      = Spec.map (chartInclLeft R A B) ⁻¹ᵁ (u ⁻¹ᵁ U) := by
  change (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) ⁻¹ᵁ U = _
  rw [affineChart_fst]
  rfl

/-- On an affine chart, the preimage of `pr₂⁻¹V` is the preimage of `v⁻¹V` along
`Spec (B ⟶ A ⊗_R B)`. -/
theorem preimage_affineChart_preimage_snd (V : Y.Opens) :
    affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.snd a b ⁻¹ᵁ V)
      = Spec.map (chartInclRight R A B) ⁻¹ᵁ (v ⁻¹ᵁ V) := by
  change (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) ⁻¹ᵁ V = _
  rw [affineChart_snd]
  rfl

/-- If `U` pulls back to all of `Spec A` and `V` to all of `Spec B`, then `pr₁⁻¹U ∩ pr₂⁻¹V`
pulls back to all of the chart. -/
theorem preimage_affineChart_inf_eq_top (U : X.Opens) (V : Y.Opens)
    (hU : u ⁻¹ᵁ U = ⊤) (hV : v ⁻¹ᵁ V = ⊤) :
    affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) = ⊤ := by
  change affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U) ⊓
    affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.snd a b ⁻¹ᵁ V) = ⊤
  rw [preimage_affineChart_preimage_fst, preimage_affineChart_preimage_snd, hU, hV]
  exact top_inf_eq _

/-- A natural isomorphism of functors into the modules on a scheme acts on sections by the
component of its underlying natural transformation. -/
theorem modulesHomApp_app_hom_apply {Z : Scheme.{u}} {C : Type*} [Category C]
    {Φ Ψ : C ⥤ Z.Modules} (e : Φ ≅ Ψ) (M : C) (U : Z.Opens) (s : Γ(Φ.obj M, U)) :
    Scheme.Modules.Hom.app (e.app M).hom U s
      = Scheme.Modules.Hom.app (e.hom.app M) U s := rfl

/-- The tensor product on the chart of the pullbacks of `F` and of `G` along the chart's two
composites with the projections, the middle term of
`Stacks.FibreProductAffineChart.chartPullbackExternalTensorIso`. -/
abbrev chartPullbackTensorSheaf (F : X.Modules) (G : Y.Modules) :
    (Spec (CommRingCat.of (A ⊗[R] B))).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace)).presheaf,
        (((Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace)).IsSheaf⟩).obj
      (((Scheme.Modules.pullback
        (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)).obj F))).obj
    (((Scheme.Modules.pullback
      (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)).obj G)))

/-- **The pullback of a box product along an affine chart on an external tensor section.** The
identification of the pullback of `F ⊠ G` along the chart with the tensor product of the two base
changes carries the pulled-back section attached to `s` over `U` and `t` over `V` to the section
coming from the pure tensor of the pullbacks of `s` to `Spec (A ⊗_R B)` through `Spec A`, and of
`t` through `Spec B`, each restricted to the chart's preimage of `pr₁⁻¹U ∩ pr₂⁻¹V`. -/
theorem chartPullbackExternalTensorIso_hom_externalTensorSection (U : X.Opens) (V : Y.Opens)
    (s : Γ(F, U)) (t : Γ(G, V))
    (hj₁ : affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ Spec.map (chartInclLeft R A B) ⁻¹ᵁ (u ⁻¹ᵁ U))
    (hj₂ : affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ Spec.map (chartInclRight R A B) ⁻¹ᵁ (v ⁻¹ᵁ V)) :
    Scheme.Modules.Hom.app (chartPullbackExternalTensorIso a b R A B u v w hu hv F G).hom
        (affineChart a b R A B u v w hu hv ⁻¹ᵁ
          (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V))
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv)
          (externalTensorProduct a b F G)
          (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
          (externalTensorSection a b F G s t
            (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) inf_le_left inf_le_right))
      = toTensorSheafSection (Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace
          ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
            ((Scheme.Modules.pullback u).obj F))
          ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
            ((Scheme.Modules.pullback v).obj G))
          (op (affineChart a b R A B u v w hu hv ⁻¹ᵁ
            (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)))
          (((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
                ((Scheme.Modules.pullback u).obj F)).presheaf.map (homOfLE hj₁).op
              (modulesPullbackUnit (Spec.map (chartInclLeft R A B))
                ((Scheme.Modules.pullback u).obj F) (u ⁻¹ᵁ U)
                (modulesPullbackUnit u F U s)) ⊗ₜ
            ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
                ((Scheme.Modules.pullback v).obj G)).presheaf.map (homOfLE hj₂).op
              (modulesPullbackUnit (Spec.map (chartInclRight R A B))
                ((Scheme.Modules.pullback v).obj G) (v ⁻¹ᵁ V)
                (modulesPullbackUnit v G V t))) := by
  have hjj₁ : pullback.lift (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
        (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
        (affineChart_comp_comm a b R A B u v w hu hv) ⁻¹ᵁ
      (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) ⁻¹ᵁ U := by
    rw [lift_affineChart]; exact fun _ hz => hz.1
  have hjj₂ : pullback.lift (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
        (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
        (affineChart_comp_comm a b R A B u v w hu hv) ⁻¹ᵁ
      (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) ⁻¹ᵁ V := by
    rw [lift_affineChart]; exact fun _ hz => hz.2
  have stepA := modulesPullbackUnit_pullbackCongr_hom
    (lift_affineChart a b R A B u v w hu hv).symm (externalTensorProduct a b F G)
    (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
    (externalTensorSection a b F G s t
      (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) inf_le_left inf_le_right)
  have e₀ : affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      = pullback.lift (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
          (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
          (affineChart_comp_comm a b R A B u v w hu hv) ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) := by
    rw [lift_affineChart]
  have stepB := homApp_presheaf_map
    (pullbackLift_externalTensorProductIso a b
      (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
      (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
      (affineChart_comp_comm a b R A B u v w hu hv) F G).hom (eqToHom e₀)
    (modulesPullbackUnit (pullback.lift
        (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
        (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
        (affineChart_comp_comm a b R A B u v w hu hv)) (externalTensorProduct a b F G)
      (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      (externalTensorSection a b F G s t
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) inf_le_left inf_le_right))
  have stepC := pullbackLift_externalTensorProductIso_hom_externalTensorSection a b
    (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
    (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
    (affineChart_comp_comm a b R A B u v w hu hv) F G s t
    (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) inf_le_left inf_le_right hjj₁ hjj₂
  have stepD := toTensorSheafSection_presheaf_map
    ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)).obj F)
    ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)).obj G)
    (eqToHom e₀)
    (((Scheme.Modules.pullback
        (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)).obj F).presheaf.map
      (homOfLE hjj₁).op
      (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) F U s))
    (((Scheme.Modules.pullback
        (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)).obj G).presheaf.map
      (homOfLE hjj₂).op
      (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) G V t))
  have hi₁ : affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) ⁻¹ᵁ U := fun _ hz => hz.1
  have hi₂ : affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) ⁻¹ᵁ V := fun _ hz => hz.2
  have stepE := tensorSheafMapIso_hom_toTensorSheafSection
    (pullbackCompCongrIso (Spec.map (chartInclLeft R A B)) u
      (affineChart_fst a b R A B u v w hu hv).symm F).symm
    (pullbackCompCongrIso (Spec.map (chartInclRight R A B)) v
      (affineChart_snd a b R A B u v w hu hv).symm G).symm
    (affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V))
    (((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)).obj
      F).presheaf.map (eqToHom e₀).op
      (((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)).obj
        F).presheaf.map
        (homOfLE hjj₁).op
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) F U s)))
    (((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)).obj
      G).presheaf.map (eqToHom e₀).op
      (((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)).obj
        G).presheaf.map
        (homOfLE hjj₂).op
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) G V t)))
  have stepF₁ := (congrArg (fun q => Scheme.Modules.Hom.app
        (pullbackCompCongrIso (Spec.map (chartInclLeft R A B)) u
          (affineChart_fst a b R A B u v w hu hv).symm F).symm.hom
        (affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)) q)
      (presheaf_map_map ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.fst
        a b)).obj F)
        (homOfLE hjj₁) (eqToHom e₀) (homOfLE hi₁)
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) F U s))).trans
    ((homApp_presheaf_map (pullbackCompCongrIso (Spec.map (chartInclLeft R A B)) u
          (affineChart_fst a b R A B u v w hu hv).symm F).symm.hom (homOfLE hi₁)
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) F U s)).trans
      ((congrArg (fun q => ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
              ((Scheme.Modules.pullback u).obj F)).presheaf.map (homOfLE hi₁).op q)
          (modulesPullbackUnit_pullbackCompCongrIso_inv (Spec.map (chartInclLeft R A B)) u
            (affineChart_fst a b R A B u v w hu hv).symm F U s)).trans
        (presheaf_map_map ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
            ((Scheme.Modules.pullback u).obj F)) _ (homOfLE hi₁) (homOfLE hj₁)
          (modulesPullbackUnit (Spec.map (chartInclLeft R A B))
            ((Scheme.Modules.pullback u).obj F) (u ⁻¹ᵁ U) (modulesPullbackUnit u F U s)))))
  have stepF₂ := (congrArg (fun q => Scheme.Modules.Hom.app
        (pullbackCompCongrIso (Spec.map (chartInclRight R A B)) v
          (affineChart_snd a b R A B u v w hu hv).symm G).symm.hom
        (affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)) q)
      (presheaf_map_map ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv ≫ pullback.snd
        a b)).obj G)
        (homOfLE hjj₂) (eqToHom e₀) (homOfLE hi₂)
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) G V t))).trans
    ((homApp_presheaf_map (pullbackCompCongrIso (Spec.map (chartInclRight R A B)) v
          (affineChart_snd a b R A B u v w hu hv).symm G).symm.hom (homOfLE hi₂)
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) G V t)).trans
      ((congrArg (fun q => ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
              ((Scheme.Modules.pullback v).obj G)).presheaf.map (homOfLE hi₂).op q)
          (modulesPullbackUnit_pullbackCompCongrIso_inv (Spec.map (chartInclRight R A B)) v
            (affineChart_snd a b R A B u v w hu hv).symm G V t)).trans
        (presheaf_map_map ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
            ((Scheme.Modules.pullback v).obj G)) _ (homOfLE hi₂) (homOfLE hj₂)
          (modulesPullbackUnit (Spec.map (chartInclRight R A B))
            ((Scheme.Modules.pullback v).obj G) (v ⁻¹ᵁ V) (modulesPullbackUnit v G V t)))))
  have stepG := congrArg₂
    (fun (z : Γ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
          ((Scheme.Modules.pullback u).obj F), affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst
            a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)))
        (wz : Γ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
          ((Scheme.Modules.pullback v).obj G), affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst
            a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V))) =>
      toTensorSheafSection (Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace
        ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
          ((Scheme.Modules.pullback u).obj F))
        ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
          ((Scheme.Modules.pullback v).obj G))
        (op (affineChart a b R A B u v w hu hv ⁻¹ᵁ (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ
          V))) (z ⊗ₜ wz)) stepF₁ stepF₂
  have inner1 := stepB.trans ((congrArg (fun q => (Scheme.Modules.presheaf
            (X := Spec (CommRingCat.of (A ⊗[R] B)))
            (chartPullbackTensorSheaf a b R A B u v w hu hv F G)).map (eqToHom e₀).op q)
          stepC).trans stepD)
  have inner2 := stepE.trans stepG
  have inner := modulesHomApp_trans _ _ _ inner1 inner2
  have hx : chartPullbackExternalTensorIso a b R A B u v w hu hv F G =
      (Scheme.Modules.pullbackCongr (lift_affineChart a b R A B u v w hu hv).symm).app
          (externalTensorProduct a b F G) ≪≫
        pullbackLift_externalTensorProductIso a b
            (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) (affineChart a b R A B u v w hu
              hv ≫ pullback.snd a b)
            (affineChart_comp_comm a b R A B u v w hu hv) F G ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
            (pullbackCompCongrIso (Spec.map (chartInclLeft R A B)) u
              (affineChart_fst a b R A B u v w hu hv).symm F).symm
            (pullbackCompCongrIso (Spec.map (chartInclRight R A B)) v
              (affineChart_snd a b R A B u v w hu hv).symm G).symm := rfl
  have stepA' := (modulesHomApp_app_hom_apply
          (Scheme.Modules.pullbackCongr (lift_affineChart a b R A B u v w hu hv).symm)
          (externalTensorProduct a b F G)
          (affineChart a b R A B u v w hu hv ⁻¹ᵁ
            (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V))
          (modulesPullbackUnit (affineChart a b R A B u v w hu hv)
            (externalTensorProduct a b F G)
            (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
            (externalTensorSection a b F G s t
              (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
              inf_le_left inf_le_right))).trans stepA
  have outer := modulesHomApp_trans _ _ _ stepA' inner
  have cg := congrArg (fun e => Scheme.Modules.Hom.app e.hom
      (affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V))
      (modulesPullbackUnit (affineChart a b R A B u v w hu hv)
        (externalTensorProduct a b F G)
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
        (externalTensorSection a b F G s t
          (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
          inf_le_left inf_le_right))) hx
  exact cg.trans outer

/-- **The global section of `F ⊠ G` on an affine chart attached to a pair of local sections.**
For `s` a section of `F` over `U` with `u⁻¹U` everything and `t` a section of `G` over `V` with
`v⁻¹V` everything, this is the section of `F ⊠ G` over `pr₁⁻¹U ∩ pr₂⁻¹V` coming from the pure
tensor of the pullbacks of `s` and `t`, pulled back along the chart and read over `⊤`. -/
def chartBoxSectionLocal (U : X.Opens) (V : Y.Opens) (hU : u ⁻¹ᵁ U = ⊤) (hV : v ⁻¹ᵁ V = ⊤)
    (s : Γ(F, U)) (t : Γ(G, V)) :
    Γ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv)).obj
        (externalTensorProduct a b F G), ⊤) :=
  ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv)).obj
      (externalTensorProduct a b F G)).presheaf.map
    (homOfLE (preimage_affineChart_inf_eq_top a b R A B u v w hu hv U V hU hV).ge).op
    (modulesPullbackUnit (affineChart a b R A B u v w hu hv) (externalTensorProduct a b F G)
      (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      (externalTensorSection a b F G s t (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
        inf_le_left inf_le_right))

/-- `Stacks.FibreProductAffineChart.chartBoxSectionLocal` written out. -/
theorem chartBoxSectionLocal_eq (U : X.Opens) (V : Y.Opens) (hU : u ⁻¹ᵁ U = ⊤)
    (hV : v ⁻¹ᵁ V = ⊤) (s : Γ(F, U)) (t : Γ(G, V)) :
    chartBoxSectionLocal a b R A B u v w hu hv F G U V hU hV s t =
      ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv)).obj
          (externalTensorProduct a b F G)).presheaf.map
        (homOfLE (preimage_affineChart_inf_eq_top a b R A B u v w hu hv U V hU hV).ge).op
        (modulesPullbackUnit (affineChart a b R A B u v w hu hv) (externalTensorProduct a b F G)
          (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
          (externalTensorSection a b F G s t (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
            inf_le_left inf_le_right)) := rfl

/-- **The pullback of a box product along an affine chart on a local box section.** The same
identification, read over `⊤`: it carries
`Stacks.FibreProductAffineChart.chartBoxSectionLocal` to the section coming from the pure tensor
of the global sections of the two inverse images attached to `s` and to `t`. -/
theorem chartPullbackExternalTensorIso_hom_chartBoxSectionLocal (U : X.Opens) (V : Y.Opens)
    (hU : u ⁻¹ᵁ U = ⊤) (hV : v ⁻¹ᵁ V = ⊤) (s : Γ(F, U)) (t : Γ(G, V)) :
    Scheme.Modules.Hom.app
        (chartPullbackExternalTensorIso a b R A B u v w hu hv F G).hom ⊤
        (chartBoxSectionLocal a b R A B u v w hu hv F G U V hU hV s t)
      = toTensorSheafSection (Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace
          ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
            ((Scheme.Modules.pullback u).obj F))
          ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
            ((Scheme.Modules.pullback v).obj G))
          (op ⊤)
          (modulesPullbackUnit (Spec.map (chartInclLeft R A B))
                ((Scheme.Modules.pullback u).obj F) ⊤
              (modulesPullbackUnitTop u F U hU s) ⊗ₜ
            modulesPullbackUnit (Spec.map (chartInclRight R A B))
                ((Scheme.Modules.pullback v).obj G) ⊤
              (modulesPullbackUnitTop v G V hV t)) := by
  have hj₁ : affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ Spec.map (chartInclLeft R A B) ⁻¹ᵁ (u ⁻¹ᵁ U) := by
    rw [← preimage_affineChart_preimage_fst a b R A B u v w hu hv]
    exact fun _ hz => hz.1
  have hj₂ : affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      ≤ Spec.map (chartInclRight R A B) ⁻¹ᵁ (v ⁻¹ᵁ V) := by
    rw [← preimage_affineChart_preimage_snd a b R A B u v w hu hv]
    exact fun _ hz => hz.2
  have hTop : (⊤ : (Spec (CommRingCat.of (A ⊗[R] B))).Opens)
      ≤ affineChart a b R A B u v w hu hv ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) :=
    (preimage_affineChart_inf_eq_top a b R A B u v w hu hv U V hU hV).ge
  have t1 := homApp_presheaf_map
    (chartPullbackExternalTensorIso a b R A B u v w hu hv F G).hom (homOfLE hTop)
    (modulesPullbackUnit (affineChart a b R A B u v w hu hv) (externalTensorProduct a b F G)
      (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
      (externalTensorSection a b F G s t (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
        inf_le_left inf_le_right))
  have t2 := congrArg (fun q => (Scheme.Modules.presheaf
        (X := Spec (CommRingCat.of (A ⊗[R] B)))
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(((Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace)).presheaf,
              (((Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
              ((Scheme.Modules.pullback u).obj F)))).obj
          (((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
            ((Scheme.Modules.pullback v).obj G)))))).map
        (homOfLE hTop).op q)
    (chartPullbackExternalTensorIso_hom_externalTensorSection a b R A B u v w hu hv F G U V
      s t hj₁ hj₂)
  have t3 := toTensorSheafSection_presheaf_map
    ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj ((Scheme.Modules.pullback
      u).obj F))
    ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj ((Scheme.Modules.pullback
      v).obj G)) (homOfLE hTop)
    (((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
        ((Scheme.Modules.pullback u).obj F)).presheaf.map (homOfLE hj₁).op
      (modulesPullbackUnit (Spec.map (chartInclLeft R A B)) ((Scheme.Modules.pullback u).obj F) (u
        ⁻¹ᵁ U)
        (modulesPullbackUnit u F U s)))
    (((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
        ((Scheme.Modules.pullback v).obj G)).presheaf.map (homOfLE hj₂).op
      (modulesPullbackUnit (Spec.map (chartInclRight R A B)) ((Scheme.Modules.pullback v).obj G) (v
        ⁻¹ᵁ V)
        (modulesPullbackUnit v G V t)))
  have t4a := (presheaf_map_map
      ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj ((Scheme.Modules.pullback
        u).obj F))
      (homOfLE hj₁) (homOfLE hTop)
      (homOfLE (show (⊤ : (Spec (CommRingCat.of (A ⊗[R] B))).Opens) ≤
        Spec.map (chartInclLeft R A B) ⁻¹ᵁ (u ⁻¹ᵁ U) from le_trans hTop hj₁))
      (modulesPullbackUnit (Spec.map (chartInclLeft R A B)) ((Scheme.Modules.pullback u).obj F) (u
        ⁻¹ᵁ U)
        (modulesPullbackUnit u F U s))).trans
    (modulesPullbackUnit_map (Spec.map (chartInclLeft R A B)) ((Scheme.Modules.pullback u).obj F)
      hU.ge
      (modulesPullbackUnit u F U s)).symm
  have t4b := (presheaf_map_map
      ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj ((Scheme.Modules.pullback
        v).obj G))
      (homOfLE hj₂) (homOfLE hTop)
      (homOfLE (show (⊤ : (Spec (CommRingCat.of (A ⊗[R] B))).Opens) ≤
        Spec.map (chartInclRight R A B) ⁻¹ᵁ (v ⁻¹ᵁ V) from le_trans hTop hj₂))
      (modulesPullbackUnit (Spec.map (chartInclRight R A B)) ((Scheme.Modules.pullback v).obj G) (v
        ⁻¹ᵁ V)
        (modulesPullbackUnit v G V t))).trans
    (modulesPullbackUnit_map (Spec.map (chartInclRight R A B)) ((Scheme.Modules.pullback v).obj G)
      hV.ge
      (modulesPullbackUnit v G V t)).symm
  have t5 := congrArg₂
    (fun (z : Γ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
      ((Scheme.Modules.pullback u).obj F), ⊤))
        (wz : Γ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
          ((Scheme.Modules.pullback v).obj G), ⊤)) =>
      toTensorSheafSection (Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace
        ((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj ((Scheme.Modules.pullback
          u).obj F))
        ((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj ((Scheme.Modules.pullback
          v).obj G))
        (op ⊤) (z ⊗ₜ wz)) t4a t4b
  rw [chartBoxSectionLocal_eq]
  exact t1.trans (t2.trans (t3.trans t5))


attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped ChangeOfRings in
/-- **Sections of a box product on an affine chart, on a local box section.** The module of
sections of `F ⊠ G` on the chart, identified with the tensor product over `A ⊗_R B` of the two
base changes, matches `Stacks.FibreProductAffineChart.chartBoxSectionLocal` with
`(1 ⊗ s) ⊗ (1 ⊗ t)`, where `s` and `t` are now read as global sections of the inverse images on
`Spec A` and on `Spec B`. -/
theorem chartExternalTensorSectionsIso_hom_chartBoxSectionLocal [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : X.Opens) (V : Y.Opens) (hU : u ⁻¹ᵁ U = ⊤) (hV : v ⁻¹ᵁ V = ⊤)
    (s : Γ(F, U)) (t : Γ(G, V)) :
    (chartExternalTensorSectionsIso a b R A B u v w hu hv F G).hom
        (chartBoxSectionLocal a b R A B u v w hu hv F G U V hU hV s t)
      = ((((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] modulesPullbackUnitTop u F U hU s)
            ⊗ₜ[CommRingCat.of (A ⊗[R] B)]
            ((1 : A ⊗[R] B) ⊗ₜ[B, algebraMap B (A ⊗[R] B)] modulesPullbackUnitTop v G V hV t)) :
          ↑(MonoidalCategory.tensorObj
            ((ModuleCat.extendScalars (chartInclLeft R A B).hom).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
            ((ModuleCat.extendScalars (chartInclRight R A B).hom).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))))) :=
  moduleIsoTrans_apply _ _
    ((moduleSpecΓFunctor_mapIso_hom_apply
        (chartPullbackExternalTensorIso a b R A B u v w hu hv F G)
        (chartBoxSectionLocal a b R A B u v w hu hv F G U V hU hV s t)).trans
      (chartPullbackExternalTensorIso_hom_chartBoxSectionLocal a b R A B u v w hu hv F G U V
        hU hV s t))
    (tensorPullbackSectionsIso_hom_toTensorSheafSection (chartInclLeft R A B)
      (chartInclRight R A B) ((Scheme.Modules.pullback u).obj F)
      ((Scheme.Modules.pullback v).obj G) (modulesPullbackUnitTop u F U hU s)
      (modulesPullbackUnitTop v G V hV t))

/-- **Sections of a box product on an affine chart over the base ring, on a local box section.**
The module of sections of `F ⊠ G` on the chart, identified as a module over `R` with
`Γ(Spec A, F) ⊗_R Γ(Spec B, G)`, matches the section attached to a section `s` of `F` over `U` and
a section `t` of `G` over `V` with the pure tensor `s ⊗ t` of the corresponding global sections of
the inverse images on `Spec A` and on `Spec B`. -/
theorem chartExternalTensorSectionsBaseIso_hom_chartBoxSectionLocal [F.IsQuasicoherent]
    [G.IsQuasicoherent] (U : X.Opens) (V : Y.Opens) (hU : u ⁻¹ᵁ U = ⊤) (hV : v ⁻¹ᵁ V = ⊤)
    (s : Γ(F, U)) (t : Γ(G, V)) :
    (chartExternalTensorSectionsBaseIso a b R A B u v w hu hv F G).hom
        (chartBoxSectionLocal a b R A B u v w hu hv F G U V hU hV s t)
      = (modulesPullbackUnitTop u F U hU s ⊗ₜ[R] modulesPullbackUnitTop v G V hV t :
          ↑(MonoidalCategory.tensorObj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
            ((ModuleCat.restrictScalars (algebraMap R B)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))))) := by
  have h₁ := (restrictScalars_mapIso_hom_apply (algebraMap R (A ⊗[R] B))
      (chartExternalTensorSectionsIso a b R A B u v w hu hv F G)
      (chartBoxSectionLocal a b R A B u v w hu hv F G U V hU hV s t)).trans
    (chartExternalTensorSectionsIso_hom_chartBoxSectionLocal a b R A B u v w hu hv F G U V
      hU hV s t)
  have h₂ := Stacks.TensorProductPushout.extendScalarsCancelIso_hom_one_tmul R A B
    (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F))
    (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))
    (modulesPullbackUnitTop u F U hU s) (modulesPullbackUnitTop v G V hV t)
  exact moduleIsoTrans_apply _ _ h₁ h₂

end Stacks.FibreProductAffineChart

end
