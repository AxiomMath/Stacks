module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackTilde
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0GAB with the source's `p^*(M^∨)`: the map `can`, its functoriality, kernel and cokernel

Let `R = A/Iⁿ` and let `M` be an `R`-module.
[Stacks, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB) writes `p^*M` for the pullback of the
quasi-coherent module `M~` on `Spec(A/Iⁿ)`, sets `M^∨ = Hom_{A/Iⁿ}(M, A/Iⁿ)` and
`F^∨ = SheafHom(F, 𝒪)`, and introduces the canonical map

`can : p^*(M^∨) ⟶ (p^*M)^∨`,

functorial in `M`, an isomorphism at a finite free module, and, for an `(A, n, c)`-module `M`,
with kernel and cokernel annihilated by every `a ∈ I^c`.

This file states all of that with the source's own source `p^*(M^∨) = f^*((M^∨)~)`, for an
arbitrary morphism of ringed sites `f : X ⟶ Spec(A/Iⁿ)` in place of `p`.  The sheaf-level map
`Stacks.SheafOfModules.PullbackDual.pullbackDualMap` of
`StacksFrontier.AlgebraicGeometry.Duality.PullbackOfDualSheaf` has source `f^*((M~)^∨)`; the two are
bridged by a comparison `(M^∨)~ ⟶ (M~)^∨` constructed here, natural in `M` and an isomorphism
for `M` of finite presentation (in particular for a finite module over the Noetherian ring of
the source).

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.dualTilde`: the comparison `(M^∨)~ ⟶ (M~)^∨` on
  `Spec R`, adjoint under `~ ⊣ Γ` to `M^∨ → Γ(Spec R, (M~)^∨)`, `φ ↦ φ~`;
  `dualTildeNatTrans` is the same as a natural transformation and `dualTildeIso` the inverse
  for `M` finitely presented.
* `Stacks.LocalCohomology.UniformityIII.pullbackModuleDualMap`: **the map `can` of Tag 0GAB**,
  `f^*((M^∨)~) ⟶ (f^*(M~))^∨`, which is `f^*` of the comparison followed by the sheaf-level
  `pullbackDualMap`; `pullbackModuleDualNatTrans` is `can` as a natural transformation of
  functors `Mod(R)ᵒᵖ ⥤ Mod(𝒪_X)`.
* `Stacks.LocalCohomology.UniformityIII.specLinear`: the `R`-linear structure on
  `𝒪_{Spec R}`-modules, `a ∈ R` acting by multiplication by the global section it defines.

## Main results

* `Stacks.LocalCohomology.UniformityIII.specTilde_map_smul_id` and `specTilde_map_smul`:
  `M ↦ M~` is `R`-linear, `(a • 𝟙 M)~ = a • 𝟙 (M~)`.
* `Stacks.LocalCohomology.UniformityIII.dualTilde_naturality` and `isIso_dualTilde`: the
  comparison `(M^∨)~ ⟶ (M~)^∨` is natural, and invertible for `M` of finite presentation.
* `Stacks.LocalCohomology.UniformityIII.pullbackModuleDualMap_naturality`: `can` is functorial
  in `M`.
* `Stacks.LocalCohomology.UniformityIII.isIso_pullbackModuleDualMap_finFree`: `can` is an
  isomorphism at a finite free module.
* `Stacks.LocalCohomology.UniformityIII.IsANCModule.kernel_map_pullbackModuleDualMap_eq_zero`
  and `IsANCModule.cokernel_map_pullbackModuleDualMap_eq_zero`: for an `(A, n, c)`-module `M`
  and `a ∈ I^c`, multiplication by `a` annihilates the kernel and the cokernel of `can`.

## Implementation notes

The comparison `(M^∨)~ ⟶ (M~)^∨` is the transpose under `~ ⊣ Γ` of the `R`-linear map
`M^∨ → Γ(Spec R, (M~)^∨)` sending `φ` to `φ~ : M~ ⟶ R~ = 𝒪`, read as a global section of the
internal Hom by `Stacks.Algebraization.internalHomSectionsTopMapAddEquiv`.  That map is bijective
for every `M` (`~` is fully faithful), so the comparison is invertible exactly where the counit
of `~ ⊣ Γ` is, which is at quasi-coherent modules; `(M~)^∨` is quasi-coherent when `M` is of
finite presentation by `AlgebraicGeometry.sheafHom_isQuasicoherent`.  Its `R`-linearity is
`(a • 𝟙 M)~ = a • 𝟙 (M~)`, which is why that equation is proved first.

The source builds `can` from a presentation `R^{⊕s} → R^{⊕r} → M → 0`, as the map between the
kernels of the dualized presentation and of its pullback.  Here `can` is a natural
transformation which is invertible at `R^{⊕r}`, and its naturality square at the surjection
`R^{⊕r} → M` is exactly the square that construction is defined by.

"`a` annihilates the kernel of `can`" is stated as the vanishing of the endomorphism of
`ker(can_M)` induced by multiplication by `a` on the source `f^*((M^∨)~)` — the pullback of
`a • 𝟙 ((M^∨)~)` — and on the target `(f^*(M~))^∨` — the dual of the pullback of
`a • 𝟙 (M~)`; the square they form with `can` is `pullbackModuleDualMap_smul_naturality`.  The
`R`-linear structure is the one on sheaves on `Spec R`, where `a` lives; the sheaves on `X` are
reached only through `f^*`.  The source's reading of the conclusion, "scheme theoretically
supported on `Y_c`", is not formalized.

Two spellings of the modules on `Spec R` are in play, `(Spec R).Modules` and the sheaves of
modules on the ringed site `specRingedSite R`; they are the same type.  The comparison is built
in the first, where `~ ⊣ Γ` lives, and transported to the second, where `can` lives, by
re-ascription (`dualTilde`).

## References

* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.InternalHom Stacks.SheafOfModules.PullbackDual

universe u

namespace Stacks.LocalCohomology.UniformityIII

variable {R : CommRingCat.{u}}

/-- On sections, `(a • 𝟙 M)~` is multiplication by `a`. -/
theorem tilde_map_smul_id_val_app (M : ModuleCat.{u} R) (a : R) (U : (Spec R).Opens)
    (x : Γ(tilde M, U)) :
    (tilde.map (a • 𝟙 M)).val.app (op U) x = a • x := by
  apply Subtype.ext
  funext p
  show LocalizedModule.map p.val.asIdeal.primeCompl (a • LinearMap.id) (x.val p) =
    (algebraMap R (Localization.AtPrime p.val.asIdeal) a) • x.val p
  rw [algebraMap_smul]
  induction x.val p using LocalizedModule.induction_on with
  | h m s =>
    simp [LocalizedModule.smul'_mk]

/-- `(a • 𝟙 M)~` is multiplication by the global section of `𝒪_{Spec R}` that `a` defines. -/
theorem tilde_map_smul_id (M : ModuleCat.{u} R) (a : R) :
    tilde.map (a • 𝟙 M) =
      (Stacks.SheafOfModules.terminalSectionToEnd (Spec R).ringCatSheaf ⊤ isTerminalTop
        ((Scheme.ΓSpecIso R).inv a)).app (tilde M) := by
  ext U x
  exact tilde_map_smul_id_val_app M a U x

variable (R) in
/-- The structure sheaf of `Spec R`, as an object of `(Spec R).Modules`. -/
noncomputable abbrev specUnit : (Spec R).Modules :=
  _root_.SheafOfModules.unit (Spec R).ringCatSheaf

/-- `(M~)^∨` on `Spec R`, in the spelling of `(Spec R).Modules`. -/
noncomputable abbrev tildeDual (M : ModuleCat.{u} R) : (Spec R).Modules :=
  (Stacks.Algebraization.sheafHomFunctor (Spec R) (tilde M)).obj (specUnit R)

/-- A linear form `φ : M → R` as the morphism `φ~ : M~ ⟶ 𝒪_{Spec R}`. -/
noncomputable def tildeForm {M : ModuleCat.{u} R} (φ : Module.Dual R M) :
    tilde M ⟶ specUnit R :=
  tilde.map (ModuleCat.ofHom φ) ≫ tildeSelf.hom

/-- `φ ↦ φ~` is additive. -/
theorem tildeForm_add {M : ModuleCat.{u} R} (φ ψ : Module.Dual R M) :
    tildeForm (φ + ψ) = tildeForm φ + tildeForm ψ := by
  rw [tildeForm, tildeForm, tildeForm, ModuleCat.ofHom_add, tilde.map_add, Preadditive.add_comp]

variable (R) in
/-- Multiplication by `a ∈ R` on an `𝒪_{Spec R}`-module: multiplication by the global section
of `𝒪_{Spec R}` that `a` defines. -/
noncomputable abbrev specSmul (a : R) :
    End (𝟭 (_root_.SheafOfModules.{u} (Spec R).ringCatSheaf)) :=
  Stacks.SheafOfModules.terminalSectionToEnd (Spec R).ringCatSheaf ⊤ isTerminalTop
    ((Scheme.ΓSpecIso R).inv a)

/-- `(a • φ)~` is `φ~` after multiplication by `a`. -/
theorem tildeForm_smul {M : ModuleCat.{u} R} (a : R) (φ : Module.Dual R M) :
    tildeForm (a • φ) = (specSmul R a).app (tilde M) ≫ tildeForm φ := by
  have h : ModuleCat.ofHom (a • φ) = (a • 𝟙 M) ≫ ModuleCat.ofHom φ := by
    ext m
    exact (φ.map_smul a m).symm
  rw [tildeForm, tildeForm, h, tilde.map_comp, tilde_map_smul_id]
  exact Category.assoc _ _ _

/-- The `R`-linear map `M^∨ → Γ(Spec R, (M~)^∨)`, `φ ↦ φ~`. -/
noncomputable def dualToSectionsTop (M : ModuleCat.{u} R) :
    Module.Dual R M →ₗ[R] moduleSpecΓFunctor.obj (tildeDual M) where
  toFun φ := Stacks.Algebraization.internalHomSectionsTopMapAddEquiv (tilde M) (specUnit R)
    (tildeForm φ)
  map_add' φ ψ := (congrArg _ (tildeForm_add φ ψ)).trans (map_add _ _ _)
  map_smul' a φ := by
    have h1 : Stacks.Algebraization.internalHomSectionsTopMapAddEquiv (tilde M) (specUnit R)
        (tildeForm (a • φ)) =
          (Stacks.Algebraization.topOverForget (Spec R)).map ((specSmul R a).app (tilde M)) ≫
            (Stacks.Algebraization.topOverForget (Spec R)).map (tildeForm φ) := by
      rw [tildeForm_smul]
      exact (Stacks.Algebraization.topOverForget (Spec R)).map_comp _ _
    rw [h1]
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    refine ((((Stacks.Algebraization.topOverForget (Spec R)).map (tildeForm φ)).app V).hom.map_smul
      _ x).trans ?_
    refine congrArg (fun c => c •
      (((Stacks.Algebraization.topOverForget (Spec R)).map (tildeForm φ)).app V).hom x) ?_
    change ((Spec R).presheaf.map V.unop.hom.op) ((Scheme.ΓSpecIso R).inv a) =
      ((Spec R).presheaf.map V.unop.hom.op)
        (((Spec R).presheaf.map (𝟙 (op ⊤))) ((Scheme.ΓSpecIso R).inv a))
    rw [(Spec R).presheaf.map_id]
    rfl

/-- `dualToSectionsTop M φ` is `φ~` read on the slice site over `⊤`. -/
theorem dualToSectionsTop_apply (M : ModuleCat.{u} R) (φ : Module.Dual R M) :
    dualToSectionsTop M φ = (Stacks.Algebraization.topOverForget (Spec R)).map (tildeForm φ) :=
  rfl

/-- `φ ↦ φ~` identifies `M^∨` with the global sections of `(M~)^∨`, for every module `M`. -/
theorem dualToSectionsTop_bijective (M : ModuleCat.{u} R) :
    Function.Bijective (dualToSectionsTop M) := by
  have hA : Function.Bijective
      (fun φ : Module.Dual R M => (ModuleCat.ofHom φ : M ⟶ ModuleCat.of R R)) :=
    ⟨fun φ ψ h => congrArg ModuleCat.Hom.hom h, fun g => ⟨g.hom, rfl⟩⟩
  have hB := (tilde.fullyFaithfulFunctor (R := R)).map_bijective M (ModuleCat.of R R)
  have hC : Function.Bijective
      (fun g : tilde M ⟶ tilde (ModuleCat.of R R) => g ≫ tildeSelf.hom) :=
    ((Iso.refl _).homCongr tildeSelf).bijective
  exact (AddEquiv.bijective _).comp (hC.comp (hB.comp hA))

/-- `φ ↦ φ~` as a morphism of `R`-modules. -/
noncomputable abbrev dualToSectionsTopHom (M : ModuleCat.{u} R) :
    (moduleDual R).obj (op M) ⟶ moduleSpecΓFunctor.obj (tildeDual M) :=
  ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj (tildeDual M)) (dualToSectionsTop M)

/-- The comparison `(M^∨)~ ⟶ (M~)^∨` on `Spec R`, adjoint to `φ ↦ φ~`. -/
noncomputable def dualTildeSpec (M : ModuleCat.{u} R) :
    (tilde.functor R).obj ((moduleDual R).obj (op M)) ⟶ tildeDual M :=
  (tilde.adjunction.homEquiv _ (tildeDual M)).symm (dualToSectionsTopHom M)

/-- `(φ ∘ g)~ = g~ ≫ φ~`. -/
theorem tildeForm_comp {M N : ModuleCat.{u} R} (g : M ⟶ N) (φ : Module.Dual R N) :
    tildeForm (φ ∘ₗ g.hom) = tilde.map g ≫ tildeForm φ := by
  rw [tildeForm, tildeForm, show ModuleCat.ofHom (φ ∘ₗ g.hom) = g ≫ ModuleCat.ofHom φ from rfl,
    tilde.map_comp]
  exact Category.assoc _ _ _

/-- `(g~)^∨ : (N~)^∨ ⟶ (M~)^∨`, in the spelling of `(Spec R).Modules`. -/
noncomputable def tildeDualMap {M N : ModuleCat.{u} R} (g : M ⟶ N) : tildeDual N ⟶ tildeDual M :=
  dualModuleSheafMap (specRingedSite R) ((specTilde R).map g)

/-- `(g~)^∨` is precomposition with `g~` in the internal Hom. -/
theorem tildeDualMap_eq {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    tildeDualMap g = (sheafInternalHomMapLeft (specRingedSite R).J (specRingedSite R).O
      ((specTilde R).map g) : tildeDual N ⟶ tildeDual M) :=
  internalHomPre_app_eq_sheafInternalHomMapLeft (specRingedSite R).O _ _

/-- The comparison `(M^∨)~ ⟶ (M~)^∨` is natural in `M`. -/
theorem dualTildeSpec_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (tilde.functor R).map ((moduleDual R).map g.op) ≫ dualTildeSpec M =
      dualTildeSpec N ≫ tildeDualMap g := by
  apply (tilde.adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, dualTildeSpec,
    dualTildeSpec, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext φ
  show (Stacks.Algebraization.topOverForget (Spec R)).map
      (tildeForm ((show Module.Dual R N from φ) ∘ₗ g.hom)) =
    (moduleSpecΓFunctor.map (tildeDualMap g)).hom
      ((Stacks.Algebraization.topOverForget (Spec R)).map
        (tildeForm (show Module.Dual R N from φ)))
  rw [tildeForm_comp]
  refine ((Stacks.Algebraization.topOverForget (Spec R)).map_comp _ _).trans ?_
  rw [tildeDualMap_eq]
  rfl

/-- **`(M^∨)~ ≅ (M~)^∨` for a finitely presented module.** The comparison is invertible: its
adjoint `φ ↦ φ~` is bijective for every `M`, and for `M` of finite presentation `(M~)^∨` is
quasi-coherent, so the counit of `~ ⊣ Γ` is invertible at it. -/
theorem isIso_dualTildeSpec (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    IsIso (dualTildeSpec M) := by
  have : (tilde M).IsFinitePresentation := (tilde_isFinitePresentation_iff M).2 inferInstance
  have : (specUnit R).IsQuasicoherent :=
    inferInstanceAs (tilde (ModuleCat.of R R)).IsQuasicoherent
  have : (tildeDual M).IsQuasicoherent := sheafHom_isQuasicoherent (tilde M) (specUnit R)
  have : IsIso (tilde.adjunction.counit.app (tildeDual M)) :=
    (inferInstance : IsIso (Scheme.Modules.fromTildeΓ (tildeDual M)))
  have : IsIso (dualToSectionsTopHom M) :=
    (LinearEquiv.ofBijective _ (dualToSectionsTop_bijective M)).toModuleIso.isIso_hom
  rw [dualTildeSpec, Adjunction.homEquiv_counit]
  infer_instance

/-! ### The comparison on the ringed site `Spec R` -/

attribute [local instance] specTilde_additive

/-- **The comparison `(M^∨)~ ⟶ (M~)^∨`** on the ringed site `Spec R`: `dualTildeSpec`, re-ascribed
to the sheaves of modules on `specRingedSite R`. -/
noncomputable def dualTilde (M : ModuleCat.{u} R) :
    (specTilde R).obj ((moduleDual R).obj (op M)) ⟶
      dualModuleSheaf (specRingedSite R) ((specTilde R).obj M) :=
  dualTildeSpec M

/-- The comparison is natural in `M`. -/
theorem dualTilde_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (specTilde R).map ((moduleDual R).map g.op) ≫ dualTilde M =
      dualTilde N ≫ dualModuleSheafMap (specRingedSite R) ((specTilde R).map g) :=
  dualTildeSpec_naturality g

/-- The comparison `(M^∨)~ ⟶ (M~)^∨` as a natural transformation of functors
`Mod(R)ᵒᵖ ⥤ Mod(𝒪_{Spec R})`. -/
noncomputable def dualTildeNatTrans (R : CommRingCat.{u}) :
    moduleDual R ⋙ specTilde R ⟶ (specTilde R).op ⋙ dualSheafFunctor (specRingedSite R) where
  app M := dualTilde M.unop
  naturality _ _ g := dualTilde_naturality g.unop

/-- The comparison `(M^∨)~ ⟶ (M~)^∨` is invertible for `M` of finite presentation. -/
theorem isIso_dualTilde (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    IsIso (dualTilde M) :=
  isIso_dualTildeSpec M

/-- **`(M^∨)~ ≅ (M~)^∨` for a finitely presented `R`-module `M`**, natural in `M` by
`dualTilde_naturality`. -/
noncomputable def dualTildeIso (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    (specTilde R).obj ((moduleDual R).obj (op M)) ≅
      dualModuleSheaf (specRingedSite R) ((specTilde R).obj M) :=
  have := isIso_dualTilde M
  asIso (dualTilde M)

/-! ### The canonical map `can : p^*(M^∨) ⟶ (p^*M)^∨` -/

variable {X : RingedSite.{u, u, u}} (f : RingedSite.Hom X (specRingedSite R))

/-- **Tag 0GAB, the canonical map `can : p^*(M^∨) ⟶ (p^*M)^∨`.**  For a morphism of ringed sites
`f : X ⟶ Spec R` and an `R`-module `M`, with `p^*N = f^*(N~)`: the pullback of the comparison
`(M^∨)~ ⟶ (M~)^∨`, followed by the canonical map `f^*((M~)^∨) ⟶ (f^*(M~))^∨` of
`Stacks.SheafOfModules.PullbackDual.pullbackDualMap`. -/
@[stacks 0GAB "the canonical map can : p^*(M^∨) ⟶ (p^*M)^∨"]
noncomputable def pullbackModuleDualMap (M : ModuleCat.{u} R) :
    (ringedSitePullback f).obj ((specTilde R).obj ((moduleDual R).obj (op M))) ⟶
      dualModuleSheaf X ((ringedSitePullback f).obj ((specTilde R).obj M)) :=
  (ringedSitePullback f).map (dualTilde M) ≫ pullbackDualMap f ((specTilde R).obj M)

/-- **Tag 0GAB, the construction of `can` is functorial in `M`.**  For `g : M ⟶ N` the square
formed by `can` at `M` and at `N`, by `p^*(g^∨)` and by `(p^*g)^∨` commutes. -/
@[stacks 0GAB "the construction of can is functorial in M"]
theorem pullbackModuleDualMap_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (ringedSitePullback f).map ((specTilde R).map ((moduleDual R).map g.op)) ≫
        pullbackModuleDualMap f M =
      pullbackModuleDualMap f N ≫
        dualModuleSheafMap X ((ringedSitePullback f).map ((specTilde R).map g)) := by
  unfold pullbackModuleDualMap
  rw [← Category.assoc, ← Functor.map_comp, dualTilde_naturality, Functor.map_comp,
    Category.assoc, Category.assoc, pullbackDualMap_naturality]

/-- `can` as a natural transformation `(-)^∨ ⋙ p^* ⟶ (p^*)ᵒᵖ ⋙ (-)^∨` of functors
`Mod(R)ᵒᵖ ⥤ Mod(𝒪_X)`. -/
noncomputable def pullbackModuleDualNatTrans :
    moduleDual R ⋙ specTilde R ⋙ ringedSitePullback f ⟶
      (specTilde R ⋙ ringedSitePullback f).op ⋙ dualSheafFunctor X where
  app M := pullbackModuleDualMap f M.unop
  naturality _ _ g := pullbackModuleDualMap_naturality f g.unop

/-- The component of `pullbackModuleDualNatTrans` at `M` is `can` at `M`. -/
theorem pullbackModuleDualNatTrans_app (M : ModuleCat.{u} R) :
    (pullbackModuleDualNatTrans f).app (op M) = pullbackModuleDualMap f M := rfl

/-- **Tag 0GAB: `can` is an isomorphism at a finite free module `R^{⊕r}`.**  The comparison is
invertible there, `R^{⊕r}` being of finite presentation, and so is the sheaf-level `can` at
`(R^{⊕r})~`, `M ↦ M~` being additive with `R~ = 𝒪`. -/
@[stacks 0GAB "can is an isomorphism at a finite free A/Iⁿ-module"]
theorem isIso_pullbackModuleDualMap_finFree (r : ℕ) :
    IsIso (pullbackModuleDualMap f (finFreeModule R r)) := by
  have := isIso_dualTilde (finFreeModule R r)
  have := isIso_pullbackDualMap_realization_finFree f (specTilde R) (specTildeUnitIso R) r
  unfold pullbackModuleDualMap
  infer_instance

/-- The kernel and cokernel halves of the annihilation of `can` by an endomorphism factoring
through a finite free module. -/
private theorem kernel_ι_and_cokernel_π_pullbackModuleDualMap {M : ModuleCat.{u} R} (e : M ⟶ M)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    kernel.ι (pullbackModuleDualMap f M) ≫
        (ringedSitePullback f).map ((specTilde R).map ((moduleDual R).map e.op)) = 0 ∧
      dualModuleSheafMap X ((ringedSitePullback f).map ((specTilde R).map e)) ≫
        cokernel.π (pullbackModuleDualMap f M) = 0 := by
  obtain ⟨r, α, β, rfl⟩ := he
  have : IsIso ((pullbackModuleDualNatTrans f).app (op (finFreeModule R r))) :=
    isIso_pullbackModuleDualMap_finFree f r
  exact ⟨kernel_ι_comp_map_eq_zero (pullbackModuleDualNatTrans f) β.op α.op,
    map_comp_cokernel_π_eq_zero (pullbackModuleDualNatTrans f) β.op α.op⟩

/-- An endomorphism of `M` which factors through a finite free module is killed, on the source
of `can`, by the kernel inclusion of `can`. -/
theorem kernel_ι_pullbackModuleDualMap_comp_eq_zero {M : ModuleCat.{u} R} (e : M ⟶ M)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    kernel.ι (pullbackModuleDualMap f M) ≫
      (ringedSitePullback f).map ((specTilde R).map ((moduleDual R).map e.op)) = 0 :=
  (kernel_ι_and_cokernel_π_pullbackModuleDualMap f e he).1

/-- An endomorphism of `M` which factors through a finite free module, carried to the target of
`can`, kills the cokernel projection of `can`. -/
theorem pullbackModuleDualMap_comp_cokernel_π_eq_zero {M : ModuleCat.{u} R} (e : M ⟶ M)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    dualModuleSheafMap X ((ringedSitePullback f).map ((specTilde R).map e)) ≫
      cokernel.π (pullbackModuleDualMap f M) = 0 :=
  (kernel_ι_and_cokernel_π_pullbackModuleDualMap f e he).2

/-- An endomorphism of `M` which factors through a finite free module annihilates the kernel of
`can` at `M`: the endomorphism of `ker(can_M)` it induces is zero. -/
theorem kernel_map_pullbackModuleDualMap_eq_zero {M : ModuleCat.{u} R} (e : M ⟶ M)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    kernel.map (pullbackModuleDualMap f M) (pullbackModuleDualMap f M)
        ((ringedSitePullback f).map ((specTilde R).map ((moduleDual R).map e.op)))
        (dualModuleSheafMap X ((ringedSitePullback f).map ((specTilde R).map e)))
        (pullbackModuleDualMap_naturality f e).symm = 0 := by
  rw [← cancel_mono (kernel.ι (pullbackModuleDualMap f M)), kernel.lift_ι]
  exact (kernel_ι_pullbackModuleDualMap_comp_eq_zero f e he).trans zero_comp.symm

/-- An endomorphism of `M` which factors through a finite free module annihilates the cokernel
of `can` at `M`. -/
theorem cokernel_map_pullbackModuleDualMap_eq_zero {M : ModuleCat.{u} R} (e : M ⟶ M)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = e) :
    cokernel.map (pullbackModuleDualMap f M) (pullbackModuleDualMap f M)
        ((ringedSitePullback f).map ((specTilde R).map ((moduleDual R).map e.op)))
        (dualModuleSheafMap X ((ringedSitePullback f).map ((specTilde R).map e)))
        (pullbackModuleDualMap_naturality f e).symm = 0 := by
  rw [← cancel_epi (cokernel.π (pullbackModuleDualMap f M)), cokernel.π_desc, comp_zero]
  exact pullbackModuleDualMap_comp_cokernel_π_eq_zero f e he

/-! ### Multiplication by `a ∈ R`, and the annihilation of the kernel and cokernel -/

/-- The rings of sections of the structure sheaf of `Spec R`, read on the ringed site, are
commutative. -/
local instance isMulCommutative_specRingSheaf (U : (specRingedSite R).Cᵒᵖ) :
    IsMulCommutative (((Stacks.SheafOfModules.Tensor.ringSheaf (J := (specRingedSite R).J))
      (specRingedSite R).O).obj.obj U) :=
  inferInstanceAs (IsMulCommutative ((Spec R).presheaf.obj U))

variable (R) in
/-- The `R`-linear structure on `𝒪_{Spec R}`-modules: `a ∈ R` acts by multiplication by the global
section of `𝒪_{Spec R}` it defines. -/
noncomputable abbrev specLinear :
    Linear R (_root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (specRingedSite R).J))
        (specRingedSite R).O)) :=
  Stacks.SheafOfModules.linearOfTerminalSection _ R ⊤ isTerminalTop
    (Scheme.ΓSpecIso R).inv.hom

/-- **`M ↦ M~` is `R`-linear on multiplication by a scalar**: `(a • 𝟙 M)~ = a • 𝟙 (M~)`. -/
theorem specTilde_map_smul_id (M : ModuleCat.{u} R) (a : R) :
    letI := specLinear R
    (specTilde R).map (a • 𝟙 M) = a • 𝟙 ((specTilde R).obj M) := by
  let _ := specLinear R
  exact (tilde_map_smul_id M a).trans (Category.comp_id _).symm

/-- **`M ↦ M~` is `R`-linear**: `(a • g)~ = a • g~`. -/
theorem specTilde_map_smul (a : R) {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    letI := specLinear R
    (specTilde R).map (a • g) = a • (specTilde R).map g := by
  let _ := specLinear R
  have h : a • g = (a • 𝟙 M) ≫ g := by rw [Linear.smul_comp, Category.id_comp]
  rw [h, CategoryTheory.Functor.map_comp, specTilde_map_smul_id, Linear.smul_comp,
    Category.id_comp]

/-- `kernel.map` depends only on its two maps, not on the proof of commutation. -/
theorem kernel_map_congr {C : Type*} [Category C] [HasZeroMorphisms C] [HasKernels C]
    {X₁ X₂ Y₁ Y₂ : C} (u : X₁ ⟶ Y₁) (v : X₂ ⟶ Y₂) {p p' : X₁ ⟶ X₂} {q q' : Y₁ ⟶ Y₂}
    (hp : p = p') (hq : q = q') (w : u ≫ q = p ≫ v) (w' : u ≫ q' = p' ≫ v) :
    kernel.map u v p q w = kernel.map u v p' q' w' := by
  subst hp hq
  rfl

/-- `cokernel.map` depends only on its two maps, not on the proof of commutation. -/
theorem cokernel_map_congr {C : Type*} [Category C] [HasZeroMorphisms C] [HasCokernels C]
    {X₁ X₂ Y₁ Y₂ : C} (u : X₁ ⟶ Y₁) (v : X₂ ⟶ Y₂) {p p' : X₁ ⟶ X₂} {q q' : Y₁ ⟶ Y₂}
    (hp : p = p') (hq : q = q') (w : u ≫ q = p ≫ v) (w' : u ≫ q' = p' ≫ v) :
    cokernel.map u v p q w = cokernel.map u v p' q' w' := by
  subst hp hq
  rfl

/-- The naturality square of `can` at multiplication by `a` on `M`, read as multiplication by `a`
on `(M^∨)~` and on `M~`. -/
theorem pullbackModuleDualMap_smul_naturality (M : ModuleCat.{u} R) (a : R) :
    letI := specLinear R
    pullbackModuleDualMap f M ≫
        dualModuleSheafMap X ((ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj M))) =
      (ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj ((moduleDual R).obj (op M)))) ≫
        pullbackModuleDualMap f M := by
  let _ := specLinear R
  rw [← specTilde_map_smul_id, ← specTilde_map_smul_id, ← moduleDual_map_op_smul_id]
  exact (pullbackModuleDualMap_naturality f (a • 𝟙 M)).symm

/-- Multiplication by `a` on the source of `can` is `p^*` of the dual of multiplication by `a`
on `M`. -/
theorem pullbackModuleDualMap_map_smul_source (M : ModuleCat.{u} R) (a : R) :
    letI := specLinear R
    (ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj ((moduleDual R).obj (op M)))) =
      (ringedSitePullback f).map ((specTilde R).map ((moduleDual R).map (a • 𝟙 M).op)) := by
  let _ := specLinear R
  rw [moduleDual_map_op_smul_id, specTilde_map_smul_id]

/-- Multiplication by `a` on the target of `can` is the dual of `p^*` of multiplication by `a`
on `M`. -/
theorem pullbackModuleDualMap_map_smul_target (M : ModuleCat.{u} R) (a : R) :
    letI := specLinear R
    dualModuleSheafMap X ((ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj M))) =
      dualModuleSheafMap X ((ringedSitePullback f).map ((specTilde R).map (a • 𝟙 M))) := by
  let _ := specLinear R
  rw [specTilde_map_smul_id]

/-- If multiplication by `a ∈ R` on `M` factors through a finite free module, then `a`
annihilates the kernel of `can` at `M`. -/
theorem kernel_map_pullbackModuleDualMap_smul_eq_zero (M : ModuleCat.{u} R) (a : R)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = a • 𝟙 M) :
    letI := specLinear R
    kernel.map (pullbackModuleDualMap f M) (pullbackModuleDualMap f M)
        ((ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj ((moduleDual R).obj (op M)))))
        (dualModuleSheafMap X ((ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj M))))
        (pullbackModuleDualMap_smul_naturality f M a) = 0 := by
  rw [kernel_map_congr _ _ (pullbackModuleDualMap_map_smul_source f M a)
    (pullbackModuleDualMap_map_smul_target f M a) _
    (pullbackModuleDualMap_naturality f (a • 𝟙 M)).symm]
  exact kernel_map_pullbackModuleDualMap_eq_zero f _ he

/-- If multiplication by `a ∈ R` on `M` factors through a finite free module, then `a`
annihilates the cokernel of `can` at `M`. -/
theorem cokernel_map_pullbackModuleDualMap_smul_eq_zero (M : ModuleCat.{u} R) (a : R)
    (he : ∃ (r : ℕ) (α : M ⟶ finFreeModule R r) (β : finFreeModule R r ⟶ M), α ≫ β = a • 𝟙 M) :
    letI := specLinear R
    cokernel.map (pullbackModuleDualMap f M) (pullbackModuleDualMap f M)
        ((ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj ((moduleDual R).obj (op M)))))
        (dualModuleSheafMap X ((ringedSitePullback f).map (a • 𝟙 ((specTilde R).obj M))))
        (pullbackModuleDualMap_smul_naturality f M a) = 0 := by
  rw [cokernel_map_congr _ _ (pullbackModuleDualMap_map_smul_source f M a)
    (pullbackModuleDualMap_map_smul_target f M a) _
    (pullbackModuleDualMap_naturality f (a • 𝟙 M)).symm]
  exact cokernel_map_pullbackModuleDualMap_eq_zero f _ he

end Stacks.LocalCohomology.UniformityIII

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] {I : Ideal A} {n c : ℕ}

/-- **Tag 0GAB, the kernel of `can`.**  Let `M` be an `(A, n, c)`-module, `a ∈ I^c` and
`f : X ⟶ Spec(A/Iⁿ)` any morphism of ringed sites.  Then `a` annihilates the kernel of
`can : p^*(M^∨) ⟶ (p^*M)^∨`: the endomorphism of `ker(can)` induced by multiplication by `a` on
`p^*(M^∨)` and on `(p^*M)^∨` is zero.  The source's reason is the proof: `a : M → M` factors
through a finite free `A/Iⁿ`-module (`IsANCModule.exists_finFree_factorization`), at which
`can` is an isomorphism. -/
@[stacks 0GAB "for an (A,n,c)-module M, every a ∈ I^c annihilates the kernel of can"]
theorem IsANCModule.kernel_map_pullbackModuleDualMap_eq_zero {X : RingedSite.{u, u, u}}
    (f : RingedSite.Hom X (specRingedSite (CommRingCat.of (A ⧸ I ^ n))))
    {M : ModuleCat.{u} (A ⧸ I ^ n)} (hM : IsANCModule I n c M) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    letI := specLinear (CommRingCat.of (A ⧸ I ^ n))
    kernel.map (pullbackModuleDualMap f M) (pullbackModuleDualMap f M)
        ((ringedSitePullback f).map (a • 𝟙 ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj
          ((moduleDual (CommRingCat.of (A ⧸ I ^ n))).obj (op M)))))
        (dualModuleSheafMap X ((ringedSitePullback f).map
          (a • 𝟙 ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M))))
        (pullbackModuleDualMap_smul_naturality f M a) = 0 :=
  kernel_map_pullbackModuleDualMap_smul_eq_zero f M a (hM.exists_finFree_factorization ha)

/-- **Tag 0GAB, the cokernel of `can`.**  For an `(A, n, c)`-module `M`, `a ∈ I^c` and any
morphism of ringed sites `f : X ⟶ Spec(A/Iⁿ)`, `a` annihilates the cokernel of
`can : p^*(M^∨) ⟶ (p^*M)^∨`. -/
@[stacks 0GAB "for an (A,n,c)-module M, every a ∈ I^c annihilates the cokernel of can"]
theorem IsANCModule.cokernel_map_pullbackModuleDualMap_eq_zero {X : RingedSite.{u, u, u}}
    (f : RingedSite.Hom X (specRingedSite (CommRingCat.of (A ⧸ I ^ n))))
    {M : ModuleCat.{u} (A ⧸ I ^ n)} (hM : IsANCModule I n c M) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    letI := specLinear (CommRingCat.of (A ⧸ I ^ n))
    cokernel.map (pullbackModuleDualMap f M) (pullbackModuleDualMap f M)
        ((ringedSitePullback f).map (a • 𝟙 ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj
          ((moduleDual (CommRingCat.of (A ⧸ I ^ n))).obj (op M)))))
        (dualModuleSheafMap X ((ringedSitePullback f).map
          (a • 𝟙 ((specTilde (CommRingCat.of (A ⧸ I ^ n))).obj M))))
        (pullbackModuleDualMap_smul_naturality f M a) = 0 :=
  cokernel_map_pullbackModuleDualMap_smul_eq_zero f M a (hM.exists_finFree_factorization ha)

end Stacks.LocalCohomology.UniformityIII

end
