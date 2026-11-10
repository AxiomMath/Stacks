module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceConservativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.FlatLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent

/-!
# Flatness descends along `ε` on a Zariski slice

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 08H7, with pullback of modules the associated-module functor `𝓕 ↦ ε^*𝓕`. This module
proves that flatness of an `𝒪_S`-module over an open `W` of `S` can be checked after `ε^*`, and
even étale locally over `W`: if the restrictions of `ε^*N` to the members of a covering sieve of
`ε(W)` are flat, then `N|_W` is flat.

## The argument

It is the classical one: `ε^*` is exact (Stacks 08H8), it detects the zero sheaf (Stacks 08H8,
localized to a Zariski slice), and it commutes with tensor products (Stacks 03EL at `ε`). For a
monomorphism `ι : A ⟶ B` of `𝒪_W`-modules, the kernel `K` of `ι ⊗ N|_W` satisfies
`ε^*K = ker(ε^*ι ⊗ ε^*N)` over `ε(W)`, which vanishes over each member of the covering because
`ε^*N` is flat there; so `ε^*K` vanishes over `ε(W)`, hence so does `K`.

Two devices keep everything on the whole of `S` and of `S_étale`, where Stacks 03EL is available:

* a test module on the slice over `W` is the restriction of a module on `S`, namely its image
  under the left exact section `AlgebraicGeometry.SmallEtale.opensRestrictionSection` of
  restriction, so a monomorphism over `W` is the restriction of a monomorphism over `S`;
* the tensor product commutes with restriction to a slice, naturally
  (`AlgebraicGeometry.RingedSite.sheafTensorOverIso_naturality_left`), on both sites.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModuleTensorRightIso`: Stacks 03EL at `ε` as an
  isomorphism of functors in the first variable, `ε^*(- ⊗ N) ≅ ε^*(-) ⊗ ε^*N`.

## Main results

* `AlgebraicGeometry.SmallEtale.isFlat_over_of_isFlat_over_associatedModule`: **flatness
  descends along `ε` on a Zariski slice, étale locally.**

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u u₁ v₁

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Fixing the second variable of a bifunctor is restricting its uncurried form along
`M ↦ (M, N)`. -/
def flipObjIsoUncurry {C D E : Type*} [Category C] [Category D] [Category E] (T : C ⥤ D ⥤ E)
    (N : D) :
    T.flip.obj N ≅ (Functor.prod' (𝟭 C) ((Functor.const C).obj N)) ⋙ Functor.uncurry.obj T :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp)

/-- Restricting `G × G` followed by an uncurried bifunctor along `M ↦ (M, N)` is fixing the
second variable at `G N` after `G`. -/
def pairIsoFlipObj {C C' E : Type*} [Category C] [Category C'] [Category E] (G : C ⥤ C')
    (T : C' ⥤ C' ⥤ E) (N : C) :
    Functor.prod' (𝟭 C) ((Functor.const C).obj N) ⋙ (Functor.prod G G ⋙ Functor.uncurry.obj T) ≅
      G ⋙ T.flip.obj (G.obj N) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M M' g
    simp only [Functor.comp_obj, Functor.prod'_obj, Functor.id_obj, Functor.const_obj_obj,
      Functor.prod_obj, Functor.uncurry_obj_obj, Functor.flip_obj_obj, Functor.comp_map,
      Functor.prod'_map, Functor.id_map, Functor.const_obj_map, Functor.prod_map,
      Functor.uncurry_obj_map, Category.comp_id, Iso.refl_hom,
      Category.id_comp, Functor.flip_obj_map]
    rw [G.map_id, CategoryTheory.Functor.map_id, Category.comp_id])

/-- **Stacks 03EL at `ε`, natural in the first variable**: for an `𝒪_S`-module `N`,
`ε^*(- ⊗ N) ≅ ε^*(-) ⊗ ε^*N` as functors.

It is `Stacks.SheafOfModules.pullbackTensorIso`, Stacks 03EL for the morphism of ringed topoi
attached to `ε`, restricted along `M ↦ (M, N)` and read through the identification
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso` of that pullback with the
associated-module functor; its components are those of
`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso` up to that identification. -/
def associatedModuleTensorRightIso (N : S.Modules) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S.zariskiRingedSite.toRingedTopos.O).flip.obj N ⋙ associatedModule B S hS ≅
      associatedModule B S hS ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS).toRingedTopos.O).flip.obj
          ((associatedModule B S hS).obj N) :=
  let f := toZariskiRingedToposModulesHom B S hS
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S.zariskiRingedSite.toRingedTopos.O
  let T' := Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS).toRingedTopos.O
  let e := pullbackModulesToZariskiIso B S hS
  Functor.isoWhiskerLeft (T.flip.obj N) e.symm ≪≫
    Functor.isoWhiskerRight (flipObjIsoUncurry T N) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Stacks.SheafOfModules.pullbackTensorIso f) ≪≫
    pairIsoFlipObj f.pullbackModules T' N ≪≫
    Functor.isoWhiskerRight e _ ≪≫
    Functor.isoWhiskerLeft (associatedModule B S hS) (T'.flip.mapIso (e.app N))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Monomorphy over an object is local along its covering sieves.** A morphism of sheaves of
modules which is a monomorphism over every member of a covering sieve of `U` is a monomorphism
over `U`: restriction to a slice preserves kernels, and vanishing is local. -/
theorem mono_over_of_mono_over {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M M' : SheafOfModules.{u} R} (f : M ⟶ M') {U : C} (Sv : Sieve U) (hSv : Sv ∈ J U)
    (h : ∀ ⦃Z : C⦄ (g : Z ⟶ U), Sv g → Mono (f.over Z)) :
    Mono (f.over U) := by
  have hK : IsZero ((kernel f).over U) := by
    refine Stacks.SheafOfModules.isZero_of_coversTop
      (Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem J U
        (fun i : Σ Z : C, { g : Z ⟶ U // Sv g } => i.1) (fun i => i.2.1)
        (J.superset_covering (fun Z g hg => by
          rw [Sieve.mem_ofArrows_iff]
          exact ⟨⟨Z, g, hg⟩, 𝟙 Z, by simp⟩) hSv))
      _ fun i => ?_
    refine Stacks.SheafOfModules.isZero_over_over_of_isZero_over _ U _ ?_
    have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R i.1) :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits.{u₁, v₁, u, u} i.1
    have := h i.2.1 i.2.2
    exact ((Preadditive.mono_iff_isZero_kernel (f.over i.1)).1 inferInstance).of_iso
      (PreservesKernel.iso (SheafOfModules.overFunctor.{u} R i.1) f)
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits.{u₁, v₁, u, u} U
  exact (Preadditive.mono_iff_isZero_kernel (f.over U)).2
    (hK.of_iso (PreservesKernel.iso (SheafOfModules.overFunctor.{u} R U) f).symm)

/-- **Monomorphy over an open descends along `ε`.** A morphism `φ` of `𝒪_S`-modules such that
`ε^*φ` is a monomorphism over `ε(W)` is a monomorphism over `W`. -/
theorem mono_over_of_mono_over_associatedModule (W : S.Opens)
    {X Y : SheafOfModules.{u} S.ringCatSheaf} (φ : X ⟶ Y)
    (h : Mono (((associatedModule B S hS).map φ).over ((opensToSmallEtale B S hS).obj W))) :
    Mono (φ.over W) := by
  let F := associatedModule B S hS
  let GE := SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
    ((opensToSmallEtale B S hS).obj W)
  have : PreservesFiniteLimits GE :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits.{u + 1, u, u, u} _
  have : PreservesFiniteLimits F := preservesFiniteLimits_associatedModuleOfSheaf B S hS
  have : F.Additive := additive_associatedModuleOfSheaf B S hS
  let G' : SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u}
      ((structureSheaf B S hS).over ((opensToSmallEtale B S hS).obj W)) := F ⋙ GE
  have : G'.PreservesZeroMorphisms :=
    ⟨fun X Y => (congrArg GE.map (F.map_zero X Y)).trans (GE.map_zero _ _)⟩
  have : PreservesFiniteLimits G' := comp_preservesFiniteLimits F GE
  let c : KernelFork φ := KernelFork.ofι (kernel.ι φ) (kernel.condition φ)
  have hK : IsZero (GE.obj (F.obj (kernel φ))) :=
    (Preadditive.mono_iff_isZero_kernel' (c.map G')
      (KernelFork.mapIsLimit c (kernelIsKernel φ) G')).1 h
  let GW := SheafOfModules.overFunctor.{u} S.ringCatSheaf W
  have : PreservesFiniteLimits GW :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits.{u, u, u, u} W
  exact (Preadditive.mono_iff_isZero_kernel' (c.map GW)
    (KernelFork.mapIsLimit c (kernelIsKernel φ) GW)).2
    (isZero_over_of_isZero_over_associatedModule B S hS W (kernel φ) hK)

/-- **Flatness of `ε^*N` over `Z` makes `ε^*(- ⊗ N)` injective over `Z`.** If `ε^*N` is flat over
an object `Z` of the small étale site, then `ε^*(ι ⊗ N)` is a monomorphism over `Z` for every
monomorphism `ι` of `𝒪_S`-modules. -/
theorem mono_over_associatedModule_sheafTensor_map (N : S.Modules) {X Y : S.Modules}
    (ι : X ⟶ Y) [Mono ι] {Z : SmallEtale B S hS}
    (hZ : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := ((smallEtaleRingedSite B S hS).over Z).O)
      (((associatedModule B S hS).obj N).over Z)) :
    Mono (((associatedModule B S hS).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S.zariskiRingedSite.O).map ι).app N)).over Z) := by
  let Es := smallEtaleRingedSite B S hS
  let F := associatedModule B S hS
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.zariskiRingedSite.O
  let T' := Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} Es.O
  let TZ := Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (Es.O.over Z)
  let G := SheafOfModules.overFunctor.{u} (structureSheaf B S hS) Z
  let c := associatedModuleTensorRightIso B S hS N
  have : PreservesFiniteLimits F := preservesFiniteLimits_associatedModuleOfSheaf B S hS
  have : F.PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have hF := Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat
    (Es.O.over Z) ((F.obj N).over Z) hZ
  rw [exactFunctor_iff] at hF
  obtain ⟨hlim, hcolim⟩ := hF
  have := Stacks.SheafOfModules.preservesHomology_overFunctor (R := structureSheaf B S hS) Z
  have hFι : Mono (F.map ι) := F.map_mono ι
  have hGι : Mono (G.map (F.map ι)) := @Functor.map_mono _ _ _ _ G inferInstance _ _ _ hFι
  have hmono : Mono ((TZ.map (G.map (F.map ι))).app ((F.obj N).over Z)) :=
    @Functor.map_mono _ _ _ _ (TZ.flip.obj ((F.obj N).over Z)) inferInstance _ _ _ hGι
  have hnat : G.map ((T'.map (F.map ι)).app (F.obj N)) ≫
      (RingedSite.sheafTensorOverIso Es Z (F.obj Y) (F.obj N)).hom =
      (RingedSite.sheafTensorOverIso Es Z (F.obj X) (F.obj N)).hom ≫
        (TZ.map (G.map (F.map ι))).app ((F.obj N).over Z) :=
    RingedSite.sheafTensorOverIso_naturality_left Es Z (F.map ι) (F.obj N)
  have h₁ : Mono (G.map ((T'.map (F.map ι)).app (F.obj N))) := by
    have : Mono (G.map ((T'.map (F.map ι)).app (F.obj N)) ≫
        (RingedSite.sheafTensorOverIso Es Z (F.obj Y) (F.obj N)).hom) := by
      rw [hnat]
      exact @mono_comp _ _ _ _ _ _
        (SplitMono.mono ⟨(RingedSite.sheafTensorOverIso Es Z (F.obj X) (F.obj N)).inv,
          (RingedSite.sheafTensorOverIso Es Z (F.obj X) (F.obj N)).hom_inv_id⟩) _ hmono
    exact mono_of_mono _ (RingedSite.sheafTensorOverIso Es Z (F.obj Y) (F.obj N)).hom
  have hc : F.map ((T.map ι).app N) ≫ c.hom.app Y =
      c.hom.app X ≫ (T'.map (F.map ι)).app (F.obj N) := c.hom.naturality ι
  have hc' : G.map (F.map ((T.map ι).app N)) ≫ G.map (c.hom.app Y) =
      G.map (c.hom.app X) ≫ G.map ((T'.map (F.map ι)).app (F.obj N)) := by
    rw [← G.map_comp, hc]
    exact G.map_comp _ _
  have : Mono (G.map (F.map ((T.map ι).app N)) ≫ G.map (c.hom.app Y)) := by
    rw [hc']
    exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso (G.mapIso (c.app X)).hom) _ h₁
  exact mono_of_mono _ (G.map (c.hom.app Y))

/-- **Flatness descends along `ε` on a Zariski slice, étale locally.** Let `N` be an
`𝒪_S`-module and `W` an open of `S`. If the restriction of `ε^*N` to every member of a covering
sieve of `ε(W)` in the small étale site is flat, then `N|_W` is a flat `𝒪_W`-module. -/
theorem isFlat_over_of_isFlat_over_associatedModule (N : S.Modules) (W : S.Opens)
    (Sv : Sieve ((opensToSmallEtale B S hS).obj W))
    (hSv : Sv ∈ topology B S hS ((opensToSmallEtale B S hS).obj W))
    (hflat : ∀ ⦃Z : SmallEtale B S hS⦄ (g : Z ⟶ (opensToSmallEtale B S hS).obj W), Sv g →
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := ((smallEtaleRingedSite B S hS).over Z).O)
        (((associatedModule B S hS).obj N).over Z)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (S.zariskiRingedSite.over W).O)
      (N.over W) := by
  let Zs := S.zariskiRingedSite
  let F := associatedModule B S hS
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Zs.O
  let TW := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Zs.O.over W)
  let E := opensRestrictionSection S W
  let e := opensRestrictionSectionIso S W
  let _ : PreservesFiniteColimits (TW.flip.obj (N.over W)) :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj (Zs.O.over W) (N.over W)
  let _ : (TW.flip.obj (N.over W)).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (TW.flip.obj (N.over W))
    Functor.additive_of_preservesBinaryBiproducts _
  let _ : (TW.flip.obj (N.over W)).PreservesMonomorphisms := by
    refine ⟨fun {A A'} ι hι => ?_⟩
    let ι' := E.map ι
    have hι' : Mono ι' := @Functor.map_mono _ _ _ _ E inferInstance _ _ ι hι
    let φ := (T.map ι').app N
    -- Read `φ` in the category of modules at the spelling `S.ringCatSheaf`, where `ε^*` lives.
    let X₀ : SheafOfModules.{u} S.ringCatSheaf := (T.obj (E.obj A)).obj N
    let Y₀ : SheafOfModules.{u} S.ringCatSheaf := (T.obj (E.obj A')).obj N
    let φ₀ : X₀ ⟶ Y₀ := φ
    -- `ε^*(ι' ⊗ N)` is a monomorphism over every member of the covering, hence over `ε(W)`.
    have hφ₀ : Mono (φ₀.over W) := mono_over_of_mono_over_associatedModule B S hS W φ₀
      (mono_over_of_mono_over (F.map φ) Sv hSv fun _ g hg =>
        @mono_over_associatedModule_sheafTensor_map B S hS N _ _ ι' hι' _ (hflat g hg))
    let GW := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Zs.O) W
    have hφ : Mono (GW.map φ) := hφ₀
    -- Through the restriction of the tensor product, and back along the section `E`.
    let H := TW.flip.obj (N.over W)
    let i₁ := RingedSite.sheafTensorOverIso Zs W (E.obj A) N
    let i₂ := RingedSite.sheafTensorOverIso Zs W (E.obj A') N
    have hnat : GW.map φ ≫ i₂.hom = i₁.hom ≫ H.map (GW.map ι') :=
      RingedSite.sheafTensorOverIso_naturality_left Zs W ι' N
    have h₂ : Mono (H.map (GW.map ι')) := by
      rw [← (Iso.inv_comp_eq i₁).2 hnat]
      exact @mono_comp _ _ _ _ _ _ (SplitMono.mono ⟨i₁.hom, i₁.inv_hom_id⟩) _
        (@mono_comp _ _ _ _ _ _ hφ _ (SplitMono.mono ⟨i₂.inv, i₂.hom_inv_id⟩))
    have he : GW.map ι' ≫ e.hom.app A' = e.hom.app A ≫ ι := e.hom.naturality ι
    have hι : ι = e.inv.app A ≫ GW.map ι' ≫ e.hom.app A' :=
      ((Iso.inv_comp_eq (e.app A)).2 he).symm
    have hHι : H.map ι = H.map (e.inv.app A) ≫ H.map (GW.map ι') ≫ H.map (e.hom.app A') := by
      conv_lhs => rw [hι]
      exact (H.map_comp _ _).trans (congrArg _ (H.map_comp _ _))
    change Mono (H.map ι)
    rw [hHι]
    exact @mono_comp _ _ _ _ _ _
      (SplitMono.mono ⟨(H.mapIso (e.app A)).hom, (H.mapIso (e.app A)).inv_hom_id⟩)
      _ (@mono_comp _ _ _ _ _ _ h₂ _
        (SplitMono.mono ⟨(H.mapIso (e.app A')).inv, (H.mapIso (e.app A')).hom_inv_id⟩))
  change exactFunctor _ _ (TW.flip.obj (N.over W))
  exact Stacks.Sites.AbelianLowerShriek.exactFunctor_of_preservesMonomorphisms _

end AlgebraicGeometry.SmallEtale

end
