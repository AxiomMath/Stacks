module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SliceTransport
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# Quasi-coherent modules of finite type on a locally Noetherian scheme are coherent

A sheaf of modules is coherent when it is of finite type and, over every open subset, the kernel
of every map to it from a finite free module is again of finite type. On a locally Noetherian
scheme the second condition is automatic for a quasi-coherent module of finite type, and that is
the content of this file. Taking the structure sheaf for the module gives that the structure
sheaf is coherent as a module over itself.

The second condition is affine-local, and on the spectrum of a Noetherian ring `R` it is
commutative algebra: a quasi-coherent module of finite type is the sheaf associated with a finite
`R`-module `N`, a map to it from a finite free module comes from a map `R^I → N` because the
association functor is fully faithful, and the kernel of that map is a submodule of a finite free
module over a Noetherian ring, hence finite. Reaching the affine case needs two reductions, both
supplied by `StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SliceTransport`: the
slice site over an open `U` is traded for the scheme `U`, and the scheme is then covered by its
affine opens.

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_kernel_free`: on a locally Noetherian
  scheme, the kernel of a map from a finite free module to a quasi-coherent module of finite type
  is of finite type.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_isQuasicoherent_of_isFiniteType`: a
  quasi-coherent module of finite type on a locally Noetherian scheme is coherent.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`: the structure sheaf of a locally
  Noetherian scheme is coherent as a module over itself.

## Implementation notes

`kernelFreeIso` is stated for an arbitrary functor of sheaves of modules preserving finite
limits, colimits and zero morphisms and identifying the two structure sheaves, because it is
applied three times: for the restriction along the inclusion of an affine open, for the
restriction along the canonical isomorphism `U ≅ Spec Γ(X, U)`, and for the functor of the slice
equivalence `Scheme.Modules.overEquiv U`.

`isFiniteType_kernel_free` establishes the affine-local condition (4) of the coherence
characterisation for the kernel and then invokes
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn`, rather than
proving quasi-coherence of the kernel and appealing to a locality statement for finite type; this
avoids needing that kernels of maps of quasi-coherent modules are quasi-coherent.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 00IK](https://stacks.math.columbia.edu/tag/00IK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

/-! ### The affine case -/

/-- **On the spectrum of a Noetherian ring, the kernel of a map from a finite free module to the
sheaf associated with a finite module is the sheaf associated with a finite module.** The map
comes from a map of modules because the association functor is fully faithful, and the kernel of
a map out of a finite free module over a Noetherian ring is finite. -/
theorem exists_finite_tilde_iso_kernel_free (R : CommRingCat.{u})
    [IsNoetherianRing R] {I : Type u} [Finite I] (N : ModuleCat.{u} R)
    (φ : (SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) I) ⟶ AlgebraicGeometry.tilde N) :
    ∃ M : ModuleCat.{u} R, Module.Finite R M ∧
      Nonempty (AlgebraicGeometry.tilde M ≅ kernel φ) := by
  classical
  let eF := AlgebraicGeometry.tildeFinsupp (R := R) I
  let ψ : AlgebraicGeometry.tilde (ModuleCat.of R (I →₀ R)) ⟶ AlgebraicGeometry.tilde N :=
    eF.hom ≫ φ
  let g : ModuleCat.of R (I →₀ R) ⟶ N := (AlgebraicGeometry.tilde.functor R).preimage ψ
  let e₁ : kernel φ ≅ kernel ψ :=
    kernel.mapIso φ ψ eF.symm (Iso.refl _)
      ((Category.comp_id φ).trans (Iso.inv_hom_id_assoc eF φ).symm)
  let e₂ : AlgebraicGeometry.tilde (ModuleCat.of R (LinearMap.ker g.hom)) ≅ kernel ψ :=
    ((AlgebraicGeometry.tilde.functor R).mapIso (ModuleCat.kernelIsoKer g)).symm ≪≫
      PreservesKernel.iso (AlgebraicGeometry.tilde.functor R) g ≪≫
        kernel.mapIso ((AlgebraicGeometry.tilde.functor R).map g) ψ
          (Iso.refl _) (Iso.refl _) ((AlgebraicGeometry.tilde.functor R).map_preimage ψ)
  have hnoeth : IsNoetherian R (I →₀ R) :=
    isNoetherian_of_isNoetherianRing_of_finite _ (I →₀ R)
  exact ⟨ModuleCat.of R (LinearMap.ker g.hom),
    Module.Finite.of_fg (IsNoetherian.noetherian _), ⟨e₂ ≪≫ e₁.symm⟩⟩

/-! ### Transport of such a kernel -/

/-- Restriction along an open immersion of schemes preserves finite limits of sheaves of
modules. -/
theorem preservesFiniteLimits_restrictFunctor {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf Z) :=
    preservesLimitsOfSize_shrink _
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf Z) := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj f.opensFunctor.op) := inferInstance
  have e : Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf Y ≅
      Scheme.Modules.toPresheaf Z ⋙
        (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op := Iso.refl _
  have : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf Y) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf Y)

/-- Restriction along an open immersion of schemes preserves colimits of sheaves of modules: it
is isomorphic to the pullback functor, which is a left adjoint. -/
@[ega "0 4.3.2" "special case"]
theorem preservesColimits_restrictFunctor {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsOpenImmersion f] :
    PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) :=
  preservesColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback f).symm

/-- Restriction along an open immersion of schemes preserves zero morphisms. -/
theorem preservesZeroMorphisms_restrictFunctor {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (Scheme.Modules.restrictFunctorIsoPullback f).symm

/-- A functor of sheaves of modules preserving finite limits, colimits and zero morphisms and
identifying the two structure sheaves carries the kernel of a map out of a finite free module to
the kernel of the corresponding map on the target site. -/
noncomputable def kernelFreeIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    (hlim : PreservesFiniteLimits F) (hzero : F.PreservesZeroMorphisms)
    (η : F.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    {I : Type u} (hI : PreservesColimitsOfShape.{u, u} (Discrete I) F)
    {G : SheafOfModules.{u} R} (φ : SheafOfModules.free I ⟶ G) :
    F.obj (kernel φ) ≅ kernel
      ((@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I hI η.symm).hom ≫ F.map φ) :=
  have := hlim
  have := hzero
  PreservesKernel.iso F φ ≪≫ kernel.mapIso _ _
    (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I hI η.symm).symm (Iso.refl _) (by simp)

/-! ### The kernel condition on a locally Noetherian scheme -/

/-- **On a locally Noetherian scheme the kernel of a map from a finite free module to a
quasi-coherent module of finite type is of finite type.** The kernel is computed on each affine
open: there the module is the sheaf associated with a finite module over a Noetherian ring, and
`exists_finite_tilde_iso_kernel_free` identifies the kernel with the sheaf associated with a
finite module. -/
theorem isFiniteType_kernel_free (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (G : Y.Modules) (hqc : G.IsQuasicoherent) (hft : G.IsFiniteType) {I : Type u} (hI : Finite I)
    (φ : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ G) : (kernel φ).IsFiniteType := by
  have := hqc
  have := hft
  have := hI
  refine isFiniteType_of_cover_isFiniteTildeOn (kernel φ)
    (fun V : Y.affineOpens => (V : Y.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top Y))
    (fun V => V.2) (fun V => ?_)
  obtain ⟨W, hW⟩ := V
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  -- restrict first to the open subscheme `W`, then to `Spec Γ(Y, W)`
  let F₁ := Scheme.Modules.restrictFunctor W.ι
  have hl₁ : PreservesFiniteLimits F₁ := preservesFiniteLimits_restrictFunctor W.ι
  have hz₁ : F₁.PreservesZeroMorphisms := preservesZeroMorphisms_restrictFunctor W.ι
  have hd₁ : PreservesColimitsOfShape.{u, u} (Discrete I) F₁ :=
    (preservesColimits_restrictFunctor W.ι).preservesColimitsOfShape
  let η₁ := Scheme.Modules.restrictUnitIso W.ι
  let φ₁ := (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F₁ I hd₁ η₁.symm).hom ≫ F₁.map φ
  let F₂ := Scheme.Modules.restrictFunctor hW.isoSpec.inv
  have hl₂ : PreservesFiniteLimits F₂ := preservesFiniteLimits_restrictFunctor hW.isoSpec.inv
  have hz₂ : F₂.PreservesZeroMorphisms := preservesZeroMorphisms_restrictFunctor hW.isoSpec.inv
  have hd₂ : PreservesColimitsOfShape.{u, u} (Discrete I) F₂ :=
    (preservesColimits_restrictFunctor hW.isoSpec.inv).preservesColimitsOfShape
  let η₂ := Scheme.Modules.restrictUnitIso hW.isoSpec.inv
  let φ₂ := (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F₂ I hd₂ η₂.symm).hom ≫ F₂.map φ₁
  -- the target of `φ₂` is the module `G` read on `Spec Γ(Y, W)`, hence a `tilde`
  have : (G.restrict W.ι).IsFiniteType := isFiniteType_restrict W.ι G
  have : (specRestrict G hW).IsFiniteType := isFiniteType_restrict hW.isoSpec.inv _
  have : (specRestrict G hW).IsQuasicoherent := inferInstance
  let eG : specRestrict G hW ≅ tilde (specModule G hW) :=
    (asIso (specRestrict G hW).fromTildeΓ).symm
  let φ₃ : SheafOfModules.free (R := (Spec Γ(Y, W)).ringCatSheaf) I ⟶ tilde (specModule G hW) :=
    φ₂ ≫ eG.hom
  obtain ⟨M, hM, ⟨eM⟩⟩ :=
    exists_finite_tilde_iso_kernel_free (CommRingCat.of Γ(Y, W)) (specModule G hW) φ₃
  -- chase the kernel back along the two restrictions
  let e₃ : kernel φ₃ ≅ kernel φ₂ :=
    kernel.mapIso φ₃ φ₂ (Iso.refl _) eG.symm
      ((Category.assoc φ₂ eG.hom eG.inv).trans
        ((congrArg (fun t => φ₂ ≫ t) (Iso.hom_inv_id eG)).trans
          ((Category.comp_id φ₂).trans (Category.id_comp φ₂).symm)))
  let e₂ : F₂.obj (kernel φ₁) ≅ kernel φ₂ := kernelFreeIso F₂ hl₂ hz₂ η₂ hd₂ φ₁
  let e₁ : F₁.obj (kernel φ) ≅ kernel φ₁ := kernelFreeIso F₁ hl₁ hz₁ η₁ hd₁ φ
  let eKer : F₂.obj (F₁.obj (kernel φ)) ≅ tilde M :=
    F₂.mapIso e₁ ≪≫ e₂ ≪≫ e₃.symm ≪≫ eM.symm
  exact ⟨M, hM, ⟨(restrictIsoSelf hW.isoSpec (F₁.obj (kernel φ))).symm ≪≫
    (Scheme.Modules.restrictFunctor hW.isoSpec.hom).mapIso eKer ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hW.isoSpec.hom).app (tilde M)⟩⟩

/-- **A quasi-coherent module of finite type on a locally Noetherian scheme is coherent.** The
kernel condition over an open `U` is carried along the slice equivalence
`Scheme.Modules.overEquiv U` to the scheme `U`, where it is `isFiniteType_kernel_free`. -/
theorem isCoherent_of_isQuasicoherent_of_isFiniteType (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : F.IsCoherent := by
  refine ⟨inferInstance, fun U I hI φ => ?_⟩
  have := hI
  let E := Scheme.Modules.overEquiv U
  have hEequiv : E.functor.IsEquivalence := E.isEquivalence_functor
  have hlim : PreservesFiniteLimits E.functor := inferInstance
  have hzero : E.functor.PreservesZeroMorphisms := inferInstance
  have hdisc : PreservesColimitsOfShape.{u, u} (Discrete I) E.functor :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} E.functor
  let η := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let ψ := (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ E.functor I hdisc η.symm).hom ≫
    E.functor.map φ
  let eOF := (Scheme.Modules.overFunctorEquiv U).app F
  let ψ' : SheafOfModules.free I ⟶ F.restrict (Scheme.Opens.ι (X := X) U) := ψ ≫ eOF.hom
  have hψ' := isFiniteType_kernel_free (Scheme.Opens.toScheme (X := X) U)
    (F.restrict (Scheme.Opens.ι (X := X) U)) inferInstance
    (isFiniteType_restrict (Scheme.Opens.ι (X := X) U) F) hI ψ'
  have hψ : (kernel ψ).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := kernel ψ')
      (kernel.mapIso ψ' ψ (Iso.refl _) eOF.symm
        ((Category.assoc ψ eOF.hom eOF.inv).trans
          ((congrArg (fun t => ψ ≫ t) (Iso.hom_inv_id eOF)).trans
            ((Category.comp_id ψ).trans (Category.id_comp ψ).symm))))
  have hE : (E.functor.obj (kernel φ)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := kernel ψ)
      (kernelFreeIso E.functor hlim hzero η hdisc φ).symm
  have hinv := isFiniteType_overEquiv_inverse U (E.functor.obj (kernel φ))
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (M := E.inverse.obj (E.functor.obj (kernel φ))) (E.unitIso.app (kernel φ)).symm

/-- **The structure sheaf of a locally Noetherian scheme is coherent.** It is quasi-coherent and
generated by the unit section, so `isCoherent_of_isQuasicoherent_of_isFiniteType` applies. -/
theorem isCoherent_unit (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (SheafOfModules.unit X.ringCatSheaf).IsCoherent := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsFiniteType :=
    AlgebraicGeometry.structureSheaf_isFiniteType X
  exact isCoherent_of_isQuasicoherent_of_isFiniteType X (SheafOfModules.unit X.ringCatSheaf)

end Stacks.AlgebraicGeometry.CoherentTFAE

end
