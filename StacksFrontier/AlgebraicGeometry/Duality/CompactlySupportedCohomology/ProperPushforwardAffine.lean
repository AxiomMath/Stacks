module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerSections
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerCohomologyProIso
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ArtinReesChain
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic

/-!
# Higher direct images of ideal powers over an affine base

Let `f : X ⟶ Y` be a proper morphism with `Y` affine and Noetherian, `𝓙` a quasi-coherent sheaf
of ideals on `Y` with global ideal `I₀ = 𝓙(Y) ⊆ A = Γ(Y, 𝒪_Y)`, `𝓘 = I₀ · 𝒪_X` and `𝓕` a
coherent `𝒪_X`-module. This file proves that the two inverse systems
`(Rⁱf_*(𝓘ⁿ𝓕))ₙ` and `(𝓙ⁿ Rⁱf_*𝓕)ₙ` of `𝒪_Y`-modules are pro-isomorphic. This is the step of the
proof of [Stacks, Tag 0G4W] which treats a coherent module placed in a single degree over an
affine base.

The proof is that of the source. By [Stacks, Tag 01XK] the global sections of `Rⁱf_*𝓖` are
`Hⁱ(X, 𝓖)` for quasi-coherent `𝓖`, and by [Stacks, Tag 02OA] part (5) the systems
`(Hⁱ(X, 𝓘ⁿ𝓕))ₙ` and `(I₀ⁿ Hⁱ(X, 𝓕))ₙ` are pro-isomorphic; the global sections of `𝓙ⁿ Rⁱf_*𝓕`
are `I₀ⁿ Γ(Y, Rⁱf_*𝓕) ≅ I₀ⁿ Hⁱ(X, 𝓕)`. So the two systems have pro-isomorphic global sections,
and since all their terms are quasi-coherent and `Y` is affine, global sections are fully
faithful on them, and the pro-isomorphism lifts.

## Main results

* `AlgebraicGeometry.nonempty_proIso_rightDerivedPlus_idealPowerSystem`: the pro-isomorphism
  `(Rⁱf_*(𝓘ⁿ𝓕))ₙ ≅ (𝓙ⁿ Rⁱf_*𝓕)ₙ`.
* `AlgebraicGeometry.fullyFaithfulModuleGlobalSectionsQcoh`: global sections are fully faithful
  on quasi-coherent modules over an affine scheme.
* `AlgebraicGeometry.proIsoOfModuleGlobalSections`: a pro-isomorphism of the global sections of
  two inverse systems of quasi-coherent modules over an affine scheme lifts to the systems.

## References

* [Stacks Project, Tag 0G4W](https://stacks.math.columbia.edu/tag/0G4W)
* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Stacks.RingTheory

/-- An `R`-linear isomorphism `M ≃ N` induces an isomorphism of the inverse systems
`n ↦ Iⁿ M` and `n ↦ Iⁿ N`, as `e (Iⁿ M) = Iⁿ e(M) = Iⁿ N`. -/
def idealPowerSmulSystemCongr {R : Type u} [CommRing R] (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    idealPowerSmulSystem I M ≅ idealPowerSmulSystem I N :=
  NatIso.ofComponents (fun n => LinearEquiv.toModuleIso (e.ofSubmodules _ _ (by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]))) (by
    rintro ⟨m⟩ ⟨n⟩ g
    ext x
    rfl)

end Stacks.RingTheory

namespace AlgebraicGeometry

open Stacks.Cohomology.FormalFunctions AlgebraicGeometry.CoherentAbelian
open scoped ModuleCat.Algebra

attribute [local instance] Stacks.Cohomology.AffineBase.baseSectionsAlgebra

section GlobalSections

variable (Y : Scheme.{u}) [IsAffine Y]

/-- **Global sections are fully faithful on quasi-coherent modules over an affine scheme.** On an
affine scheme `Y`, the functor `𝓕 ↦ Γ(Y, 𝓕)` from quasi-coherent `𝒪_Y`-modules to
`Γ(Y, 𝒪_Y)`-modules is fully faithful: every `Γ(Y, 𝒪_Y)`-linear map of global sections comes
from a unique morphism of modules. -/
def fullyFaithfulModuleGlobalSectionsQcoh :
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙
      AlgebraicGeometry.moduleGlobalSections Y).FullyFaithful where
  preimage {M N} w :=
    haveI : (M.obj : Y.Modules).IsQuasicoherent := M.property
    haveI : (N.obj : Y.Modules).IsQuasicoherent := N.property
    ObjectProperty.homMk (Classical.choose
      (Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq (F := M.obj) (G := N.obj)
        w.hom))
  map_preimage {M N} w := by
    have : (M.obj : Y.Modules).IsQuasicoherent := M.property
    have : (N.obj : Y.Modules).IsQuasicoherent := N.property
    exact ModuleCat.hom_ext (LinearMap.ext (Classical.choose_spec
      (Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq (F := M.obj) (G := N.obj)
        w.hom)))
  preimage_map {M N} φ := by
    have : (M.obj : Y.Modules).IsQuasicoherent := M.property
    have : (N.obj : Y.Modules).IsQuasicoherent := N.property
    exact ObjectProperty.hom_ext _ (Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top
      (Classical.choose_spec
        (Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq (F := M.obj) (G := N.obj)
          ((AlgebraicGeometry.moduleGlobalSections Y).map φ.hom).hom)))

variable {Y} in
/-- **A pro-isomorphism of global sections lifts.** On an affine scheme `Y`, two inverse systems
`(𝓕_n)` and `(𝓖_n)` of quasi-coherent `𝒪_Y`-modules are pro-isomorphic as soon as the inverse
systems `(Γ(Y, 𝓕_n))` and `(Γ(Y, 𝓖_n))` of `Γ(Y, 𝒪_Y)`-modules are, global sections being fully
faithful on quasi-coherent modules (`fullyFaithfulModuleGlobalSectionsQcoh`). -/
def proIsoOfModuleGlobalSections {F G : ℕᵒᵖ ⥤ Y.Modules}
    (hF : ∀ n, (F.obj n).IsQuasicoherent) (hG : ∀ n, (G.obj n).IsQuasicoherent)
    (e : InverseSequence.ProIso (F ⋙ AlgebraicGeometry.moduleGlobalSections Y)
      (G ⋙ AlgebraicGeometry.moduleGlobalSections Y)) :
    InverseSequence.ProIso F G :=
  Pro.proIsoWhiskerRight (InverseSequence.ProIso.ofFullyFaithful
    (fullyFaithfulModuleGlobalSectionsQcoh Y)
    (F := (SheafOfModules.isQuasicoherent Y.ringCatSheaf).lift F hF)
    (G := (SheafOfModules.isQuasicoherent Y.ringCatSheaf).lift G hG) e)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι

end GlobalSections

section AffineBase

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]

/-- For `f : X ⟶ Y` with `Y` affine, regard `X` as a scheme over `Spec Γ(Y, 𝒪_Y)` through
`f` followed by `Y ≅ Spec Γ(Y, 𝒪_Y)`. The resulting map `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)` on global
functions is `f^♯` on global sections. -/
theorem baseRingToSections_isoSpec :
    baseRingToSections Γ(Y, ⊤) (Over.mk (f ≫ Y.isoSpec.hom)) (op ⊤) = f.appTop.hom := by
  have h : (Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (f ≫ Y.isoSpec.hom).appTop = f.appTop := by
    rw [Scheme.Hom.comp_appTop]
    show (Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ Y.toSpecΓ.appTop ≫ f.appTop = f.appTop
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
  have hid : (TopologicalSpace.Opens.leTop (⊤ : X.Opens)).op = 𝟙 (op ⊤) := rfl
  ext a
  show ((forget₂ CommRingCat RingCat).map ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫
    (f ≫ Y.isoSpec.hom).appTop) ≫
      X.ringCatSheaf.obj.map (TopologicalSpace.Opens.leTop (⊤ : X.Opens)).op).hom a = _
  rw [hid, CategoryTheory.Functor.map_id]
  show ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (f ≫ Y.isoSpec.hom).appTop).hom a = _
  rw [h]
  rfl

/-- **[Stacks, Tag 01XK] in degree `i : ℕ`.** For `f : X ⟶ Y` quasi-compact and quasi-separated
with `Y` affine, the cohomology `Hⁱ(X, 𝓕)`, a `Γ(Y, 𝒪_Y)`-module by restriction of scalars along
`f^♯`, is naturally isomorphic to `Γ(Y, Rⁱf_*𝓕)` for quasi-coherent `𝓕`. This is
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.cohomologyIsoGlobalSectionsRightDerivedPushforward`
with the cohomology of `X` read in the `ℕ`-indexing of `CategoryTheory.Functor.rightDerived`. -/
def cohomologyIsoSectionsHigherDirectImage [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (AlgebraicGeometry.moduleGlobalSections X).rightDerived i ⋙
        ModuleCat.restrictScalars f.appTop.hom ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ) ⋙
          AlgebraicGeometry.moduleGlobalSections Y :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (Stacks.DerivedIndexing.rightDerivedIso (AlgebraicGeometry.moduleGlobalSections X) i) _) ≪≫
  Stacks.AlgebraicGeometry.HigherDirectImageQcoh.cohomologyIsoGlobalSectionsRightDerivedPushforward
      (X := X) (S := Y) f (i : ℤ)

/-- For `f : X ⟶ Y` with `Y` affine, `I ⊆ Γ(Y, 𝒪_Y)` an ideal and `𝓘 = I · 𝒪_X`, the inverse system
`n ↦ Hⁱ(X, 𝓘ⁿ𝓕)` of [Stacks, Tag 02OA], built for `X` over `Spec Γ(Y, 𝒪_Y)`, is the inverse
system `n ↦ Hⁱ(X, 𝓘ⁿ𝓕)` obtained by applying cohomology to the ideal-power system and restricting
scalars along `f^♯`: the two `Γ(Y, 𝒪_Y)`-module structures come from equal ring maps
(`baseRingToSections_isoSpec`). -/
def cohomologyIdealPowerFunctorIso (I : Ideal Γ(Y, ⊤)) (F : X.Modules) (i : ℕ) :
    cohomologyIdealPowerFunctor I (Over.mk (f ≫ Y.isoSpec.hom)) F i ≅
      Stacks.Duality.idealPowerSystem (baseIdealSheaf Γ(Y, ⊤) I (f ≫ Y.isoSpec.hom)) F ⋙
        (AlgebraicGeometry.moduleGlobalSections X).rightDerived i ⋙
          ModuleCat.restrictScalars f.appTop.hom :=
  (NatIso.ofComponents (G := Stacks.Duality.idealPowerSystem
      (baseIdealSheaf Γ(Y, ⊤) I (f ≫ Y.isoSpec.hom)) F ⋙
        (AlgebraicGeometry.moduleGlobalSections X).rightDerived i ⋙
          ModuleCat.restrictScalars
            (algebraMap Γ(Y, ⊤) Γ((Over.mk (f ≫ Y.isoSpec.hom)).left, ⊤)))
    (fun _ => Iso.refl _) (by
      rintro ⟨m⟩ ⟨n⟩ g
      have h : n ≤ m := leOfHom g.unop
      obtain rfl : g = (homOfLE h).op := Subsingleton.elim _ _
      have ht : (Stacks.Duality.idealPowerSystem
          (baseIdealSheaf Γ(Y, ⊤) I (f ≫ Y.isoSpec.hom)) F).map (homOfLE h).op = subHom _ :=
        Stacks.Duality.tr_idealPowerSystem (baseIdealSheaf Γ(Y, ⊤) I (f ≫ Y.isoSpec.hom)) F h
      simp only [Functor.comp_map, Iso.refl_hom]
      rw [cohomologyIdealPowerFunctor_map, ht]
      ext x
      rfl)) ≪≫
    Functor.isoWhiskerLeft (Stacks.Duality.idealPowerSystem
        (baseIdealSheaf Γ(Y, ⊤) I (f ≫ Y.isoSpec.hom)) F ⋙
          (AlgebraicGeometry.moduleGlobalSections X).rightDerived i)
      (ModuleCat.restrictScalarsCongr (baseRingToSections_isoSpec f))

end AffineBase

section IdealPowerSections

variable {Y : Scheme.{u}} [IsAffine Y]

/-- **Sections of `𝓙ⁿ𝓗` over an affine scheme.** For `Y` affine, `𝓙` a quasi-coherent sheaf of
ideals with global ideal `J = 𝓙(Y)` and `𝓗` quasi-coherent, the inverse system
`n ↦ Jⁿ Γ(Y, 𝓗)` is isomorphic to `n ↦ Γ(Y, 𝓙ⁿ𝓗)`, since `Γ(Y, 𝓙ⁿ𝓗) = Jⁿ Γ(Y, 𝓗)`
(`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen`). -/
def idealPowerSmulSystemIsoSections (J : Y.IdealSheafData) (H : Y.Modules) [H.IsQuasicoherent] :
    Stacks.RingTheory.idealPowerSmulSystem (J.ideal ⟨⊤, isAffineOpen_top Y⟩)
        ((AlgebraicGeometry.moduleGlobalSections Y).obj H) ≅
      Stacks.Duality.idealPowerSystem J H ⋙ AlgebraicGeometry.moduleGlobalSections Y :=
  NatIso.ofComponents (fun n => LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen J n.unop H
        ⟨⊤, isAffineOpen_top Y⟩).symm)) (by
    rintro ⟨m⟩ ⟨n⟩ g
    have h : n ≤ m := leOfHom g.unop
    obtain rfl : g = (homOfLE h).op := Subsingleton.elim _ _
    have ht : (Stacks.Duality.idealPowerSystem J H).map (homOfLE h).op = subHom _ :=
      Stacks.Duality.tr_idealPowerSystem J H h
    rw [Functor.comp_map, ht]
    ext x
    rfl)

end IdealPowerSections

/-- **The higher direct images of the ideal powers over an affine base.** Let `f : X ⟶ Y` be
proper with `Y` affine and Noetherian, `𝓙` a quasi-coherent sheaf of ideals on `Y` with global
ideal `I₀ = 𝓙(Y) ⊆ Γ(Y, 𝒪_Y)`, `𝓘 = I₀ · 𝒪_X` and `𝓕` a coherent `𝒪_X`-module. Then for every
`i ≥ 0` the inverse systems `(Rⁱf_*(𝓘ⁿ𝓕))ₙ` and `(𝓙ⁿ Rⁱf_*𝓕)ₙ` of `𝒪_Y`-modules are
pro-isomorphic.

On global sections this is [Stacks, Tag 02OA] part (5), for `X` over `Spec Γ(Y, 𝒪_Y)`, combined
with [Stacks, Tag 01XK]; it lifts to the systems by `proIsoOfModuleGlobalSections`. -/
theorem nonempty_proIso_rightDerivedPlus_idealPowerSystem
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsNoetherian Y] [IsProper f]
    (J : Y.IdealSheafData) (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Nonempty (ProSeq.of (Stacks.Duality.idealPowerSystem
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf Γ(Y, ⊤)
          (J.ideal ⟨⊤, isAffineOpen_top Y⟩) (f ≫ Y.isoSpec.hom)) F ⋙
        (Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)) ≅
      ProSeq.of (Stacks.Duality.idealPowerSystem J
        (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F))) := by
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have hFq : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let I₀ := J.ideal ⟨⊤, isAffineOpen_top Y⟩
  let X' : Over (Spec (.of Γ(Y, ⊤))) := Over.mk (f ≫ Y.isoSpec.hom)
  have hX : IsProper X'.hom := by
    show IsProper (f ≫ Y.isoSpec.hom)
    infer_instance
  obtain ⟨-, -, -, -, -, -, ⟨p02⟩⟩ := exists_uniform_bound_cohomology_of_isProper I₀ X' F hX i
  let G := ((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F
  have hGq : G.IsQuasicoherent :=
    ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus f F hFq i
  let S := Stacks.Duality.idealPowerSystem
    (Stacks.Cohomology.FormalFunctions.baseIdealSheaf Γ(Y, ⊤) I₀ (f ≫ Y.isoSpec.hom)) F
  have hS₀ : ∀ n, (S.obj n).IsQuasicoherent := fun n =>
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent _ n.unop F
  have hS : ∀ n,
      ((S ⋙ (Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj n).IsQuasicoherent :=
    fun n => ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus f _ (hS₀ n) i
  have hT : ∀ n, ((Stacks.Duality.idealPowerSystem J G).obj n).IsQuasicoherent := fun n =>
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent J n.unop G
  let eF : ModuleCat.of Γ(Y, ⊤) (cohomology X' F i) ≅
      (AlgebraicGeometry.moduleGlobalSections Y).obj G :=
    (ModuleCat.restrictScalarsCongr (baseRingToSections_isoSpec f)).app
        (((AlgebraicGeometry.moduleGlobalSections X).rightDerived i).obj F) ≪≫
      (cohomologyIsoSectionsHigherDirectImage f i).app ⟨F, hFq⟩
  let N₁ : S ⋙ (Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ) ⋙
      AlgebraicGeometry.moduleGlobalSections Y ≅ cohomologyIdealPowerFunctor I₀ X' F i :=
    (Functor.isoWhiskerLeft ((SheafOfModules.isQuasicoherent X.ringCatSheaf).lift S hS₀)
      (cohomologyIsoSectionsHigherDirectImage f i)).symm ≪≫
      (cohomologyIdealPowerFunctorIso f I₀ F i).symm
  let N₂ : Stacks.RingTheory.idealPowerSmulSystem I₀ (cohomology X' F i) ≅
      Stacks.Duality.idealPowerSystem J G ⋙ AlgebraicGeometry.moduleGlobalSections Y :=
    Stacks.RingTheory.idealPowerSmulSystemCongr I₀ eF.toLinearEquiv ≪≫
      idealPowerSmulSystemIsoSections J G
  exact ⟨ProSeq.isoOfProIso (proIsoOfModuleGlobalSections hS hT
    (Pro.proIsoTrans (Pro.proIsoOfNatIso N₁) (Pro.proIsoTrans p02 (Pro.proIsoOfNatIso N₂))))⟩

end AlgebraicGeometry
