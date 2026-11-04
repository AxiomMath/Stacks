module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of the pullback of a quasi-coherent module to an affine scheme

Let `φ : R ⟶ T` be a morphism of commutative rings and let `F` be a quasi-coherent
`𝒪_{Spec R}`-module. This file identifies the pullback of `F` along `Spec.map φ` with the
module obtained from `F` by base change along `φ`, and in particular identifies the global
sections of that pullback with `T ⊗_R Γ(F, ⊤)`.

## Main definitions

* `pullbackSections` is the functor sending an `𝒪_{Spec T}`-module to the `R`-module of global
  sections of its direct image along `Spec.map φ`.
* `sectionsRestrictScalars` is the functor sending an `𝒪_{Spec T}`-module to its `T`-module of
  global sections, with scalars restricted along `φ`.
* `pullbackSectionsIso` identifies these two functors.
* `tildePullbackIso` is the main comparison: pulling back `M^~` along `Spec.map φ` gives
  `(T ⊗_R M)^~`, naturally in the `R`-module `M`.
* `tildeSectionsPullbackIso` and `sectionsPullbackIso` are the resulting identifications of
  global sections, for a module of the form `M^~` and for an arbitrary quasi-coherent module.

## Main results

* `isQuasicoherent_pullback_specMap`: the pullback of a quasi-coherent module along a morphism
  of spectra is quasi-coherent.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.SectionsColimit

/-! ### Two definitional facts about module structures on sections -/

/-- The `Γ(Y, U)`-module structure on the sections of a direct image is obtained from the
`Γ(X, f ⁻¹ᵁ U)`-module structure on the sections of the original module by restriction of
scalars along `f.app U`. -/
theorem pushforward_app_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : X.Modules) (U : Y.Opens) (r : Γ(Y, U)) (x : Γ(N, f ⁻¹ᵁ U)) :
    (f.app U r) • x = (r • (show Γ((Scheme.Modules.pushforward f).obj N, U) from x)) := rfl

/-- The `R`-module structure on the global sections of an `𝒪_{Spec R}`-module is obtained from
the `Γ(Spec R, ⊤)`-module structure by restriction of scalars along `(ΓSpecIso R).inv`. -/
theorem moduleSpecΓ_smul {R : CommRingCat.{u}} (M : (Spec R).Modules) (r : R) (x : Γ(M, ⊤)) :
    ((Scheme.ΓSpecIso R).inv.hom r) • x = (r • (show (moduleSpecΓFunctor.obj M) from x)) := rfl

variable {R T : CommRingCat.{u}} (φ : R ⟶ T)

/-! ### The comparison of the two right adjoints -/

/-- The `R`-module of global sections of the direct image along `Spec.map φ`. -/
def pullbackSections : (Spec T).Modules ⥤ ModuleCat R :=
  Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor

/-- The `T`-module of global sections, with scalars restricted along `φ`. -/
def sectionsRestrictScalars : (Spec T).Modules ⥤ ModuleCat R :=
  moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom

/-- The two `R`-module structures on `Γ(N, ⊤)` coming from `pullbackSections φ` and from
`sectionsRestrictScalars φ` agree. -/
theorem smul_pullbackSections_eq (N : (Spec T).Modules) (r : R) (x : Γ(N, ⊤)) :
    (show Γ(N, ⊤) from (r • (show ((pullbackSections φ).obj N) from x)))
      = (show Γ(N, ⊤) from (r • (show ((sectionsRestrictScalars φ).obj N) from x))) := by
  change ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv.hom r)) • x
      = ((Scheme.ΓSpecIso T).inv.hom (φ.hom r)) • x
  rw [elementwise_of% (Scheme.ΓSpecIso_inv_naturality φ)]

/-- The identity of `Γ(N, ⊤)`, as an `R`-linear equivalence from `(pullbackSections φ).obj N`
to `(sectionsRestrictScalars φ).obj N`. -/
def pullbackSectionsEquiv (N : (Spec T).Modules) :
    ((pullbackSections φ).obj N) ≃ₗ[R] ((sectionsRestrictScalars φ).obj N) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' := smul_pullbackSections_eq φ N
  left_inv _ := rfl
  right_inv _ := rfl

/-- Global sections of the direct image along `Spec.map φ` are the global sections with
scalars restricted along `φ`. -/
def pullbackSectionsIso : pullbackSections φ ≅ sectionsRestrictScalars φ :=
  NatIso.ofComponents (fun N ↦ (pullbackSectionsEquiv φ N).toModuleIso) (fun _ ↦ rfl)

/-! ### Base change for the pullback of a quasi-coherent module -/

/-- `tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ)` is left adjoint to
`pullbackSections φ`. -/
def tildePullbackAdjunction :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣ pullbackSections φ :=
  tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))

/-- `ModuleCat.extendScalars φ.hom ⋙ tilde.functor T` is also left adjoint to
`pullbackSections φ`. -/
def extendScalarsTildeAdjunction :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor T ⊣ pullbackSections φ :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (pullbackSectionsIso φ).symm

/-- **Base change for quasi-coherent modules on affine schemes.** The pullback of `M^~` along
`Spec.map φ` is `(T ⊗_R M)^~`, naturally in the `R`-module `M`. -/
def tildePullbackIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor T :=
  (tildePullbackAdjunction φ).leftAdjointUniq (extendScalarsTildeAdjunction φ)

/-- The global sections of the pullback of `M^~` along `Spec.map φ` are `T ⊗_R M`. -/
def tildeSectionsPullbackIso (M : ModuleCat R) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj ((tilde.functor R).obj M))
      ≅ (ModuleCat.extendScalars φ.hom).obj M :=
  moduleSpecΓFunctor.mapIso ((tildePullbackIso φ).app M) ≪≫
    (tilde.toTildeΓNatIso.app ((ModuleCat.extendScalars φ.hom).obj M)).symm

/-- The global sections of the pullback of a quasi-coherent `𝒪_{Spec R}`-module `F` along
`Spec.map φ` are `T ⊗_R Γ(F, ⊤)`. -/
def sectionsPullbackIso (F : (Spec R).Modules) [F.IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj F)
      ≅ (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj F) :=
  moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullback (Spec.map φ)).mapIso
    (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓNatTrans.app F)
      (show IsIso (Scheme.Modules.fromTildeΓ F) from inferInstance)).symm) ≪≫
    tildeSectionsPullbackIso φ _

/-- The pullback of a quasi-coherent module along a morphism of spectra is quasi-coherent. -/
instance isQuasicoherent_pullback_specMap (F : (Spec R).Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj F).IsQuasicoherent := by
  have e : (Scheme.Modules.pullback (Spec.map φ)).obj F ≅
      (tilde.functor T).obj ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj F)) :=
    (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso (Scheme.Modules.fromTildeΓ F)).symm ≪≫
      (tildePullbackIso φ).app _
  exact (SheafOfModules.isQuasicoherent (Spec T).ringCatSheaf).prop_of_iso e.symm inferInstance

end Stacks.AlgebraicGeometry.SectionsColimit
