module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangePushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsOverAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerCohomologyReesFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialLargeSite

/-!
# Sections of a higher direct image over an affine chart, as modules over the chart

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`,
let `F` be a quasi-coherent `𝒪_X`-module and let `V` be an affine object of `Y_étale`, with
`f' : X_V = V ×_Y X ⟶ V` the base change.  Stacks 08EX identifies the sections over `V` of
`R^q f_*F` with `H^q(X_V, F|_{X_V})`.  Both sides are modules over `Γ(V, 𝒪_V)`: the first as
sections of an `𝒪_Y`-module over `V`, the second through `f'^♯ : Γ(V, 𝒪_V) ⟶ Γ(X_V, 𝒪)`.  This
file proves that the identification is one of `Γ(V, 𝒪_V)`-modules.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardSectionsLinearEquiv`: for `f : X ⟶ Z` and a ring
  `A` acting compatibly on the global functions of both, `Γ(Z, f_*M) ≃ Γ(X, M)` as `A`-modules.
* `AlgebraicGeometry.Space.globalSectionsPushforwardRestrictIso`: the same, as a natural
  isomorphism of functors to `A`-modules.
* `AlgebraicGeometry.Space.rightDerivedPushforwardGlobalSectionsLinearEquiv`: the derived
  version, `R^q Γ(Z, f_* −)(F) ≃ H^q(X, F)` as `A`-modules.
* `AlgebraicGeometry.Space.globalSectionsIdEtaleChartLinearEquiv` and
  `AlgebraicGeometry.Space.etaleModulePullbackChartSectionsLinearEquiv`: global sections on an
  object `T` of the site are sections over its identity chart, and those of the restriction of
  an `𝒪_Y`-module to an étale chart `V` are its sections over `V`, linearly over `Γ(T, 𝒪_T)`.
* `AlgebraicGeometry.Space.chartSectionsHigherDirectImageLinearEquiv`: **Stacks 08EX as an
  isomorphism of `Γ(V, 𝒪_V)`-modules**.

## Implementation notes

The cohomology `H^q(X_V, F)` is `AlgebraicGeometry.Space.cohomologyRes` along
`AlgebraicGeometry.Space.baseFunctionsToGlobalSections`, the form in which the flat base change
of Stacks 073K, part (2), and the theorem on formal functions over an affine base are stated.
The comparison with Stacks 08EX is a chain of isomorphisms of `Γ(V, 𝒪_V)`-modules, each an
isomorphism in a category of modules, so that linearity is never checked by hand except for
`Γ(Z, f_*M) ≃ Γ(X, M)`, where it is the naturality of that identification with respect to
multiplication by a pulled-back function.

## References

* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Pushforward

variable {X Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) {A : Type u} [CommRing A]
  (ρ : A →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))
  (φ : A →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  (hφ : ∀ (a : A) (M : Modules.{u, u} B S hS X.1 X.2),
    (modulePushforward B S hS f).map (globalSmul _ (φ a) M) =
      globalSmul _ (ρ a) ((modulePushforward B S hS f).obj M))

include hφ in
/-- **`Γ(Z, f_*M) ≃ Γ(X, M)` as `A`-modules**, for `f : X ⟶ Z` and ring maps `ρ` and `φ` from
`A` to the global functions on `Z` and on `X` such that the direct image of multiplication by
`φ a` is multiplication by `ρ a`. -/
def modulePushforwardSectionsLinearEquiv (M : Modules.{u, u} B S hS X.1 X.2) :
    (ModuleCat.restrictScalars ρ).obj
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj
            ((modulePushforward B S hS f).obj M))
      ≃ₗ[A] (ModuleCat.restrictScalars φ).obj
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj
            M) :=
  AddEquiv.toLinearEquiv
    ((globalSectionsModulePushforwardIso B S hS f).app M).addCommGroupIsoToAddEquiv
    fun r s => by
      have h := modulePushforwardSectionsEquiv_naturality B S hS f (globalSmul _ (φ r) M) s
      rwa [hφ] at h

include hφ in
/-- `Γ(Z, f_* −) ≅ Γ(X, −)` as functors to `A`-modules. -/
def globalSectionsPushforwardRestrictIso :
    modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) ⋙
      ModuleCat.restrictScalars ρ ≅
    globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
      ModuleCat.restrictScalars φ :=
  NatIso.ofComponents (fun M => (modulePushforwardSectionsLinearEquiv f ρ φ hφ M).toModuleIso)
    fun {M N} q => by
      ext s
      exact modulePushforwardSectionsEquiv_naturality B S hS f q s

include hφ in
/-- **`R^q Γ(Z, f_* −)(F) ≃ H^q(X, F)` as `A`-modules**: the derived functors of the two sides
of `AlgebraicGeometry.Space.globalSectionsPushforwardRestrictIso`. -/
def rightDerivedPushforwardGlobalSectionsLinearEquiv (F : Modules.{u, u} B S hS X.1 X.2)
    (q : ℕ) :
    (ModuleCat.restrictScalars ρ).obj
        (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Z.1 Z.2).O)).rightDerived q).obj F)
      ≃ₗ[A] (ModuleCat.restrictScalars φ).obj (spaceCohomology B S hS X q |>.obj F) :=
  have := modulePushforward_additive B S hS f
  (((Functor.rightDerivedCompIso
      (modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))
      (ModuleCat.restrictScalars ρ) q).app F).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (globalSectionsPushforwardRestrictIso f ρ φ hφ) q).app F ≪≫
    (Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (ModuleCat.restrictScalars φ) q).app F).toLinearEquiv

end Pushforward

end AlgebraicGeometry.Space



namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For an object `T` of the site, the map from `Γ(T, 𝒪_T)` to the global functions of the
small étale site of `T` induced by the identity of `T`, followed by evaluation at the identity
chart of `T`, is the identity of `Γ(T, 𝒪_T)`. -/
theorem globalSectionEval_comp_baseFunctionsToGlobalSections_id (T : BigFppfOver B S hS) :
    (globalSectionEval (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O)
        (op (idEtaleChart B S hS T))).comp
        (baseFunctionsToGlobalSections B S hS (𝟙 (schemeSpace T))) = RingHom.id _ := by
  refine RingHom.ext fun r => ?_
  have h : yoneda.preimage ((idEtaleChart B S hS T).1.hom ≫
      (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom) = 𝟙 T :=
    yoneda.map_injective (by rw [Functor.map_preimage]; ext; rfl)
  show (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
    ((idEtaleChart B S hS T).1.hom ≫
      (𝟙 (schemeSpace (B := B) (S := S) (hS := hS) T) :
        schemeSpace T ⟶ schemeSpace T).hom))))).hom r = r
  rw [h]
  exact (congrArg (fun g : (BigFppfOver.toScheme B S hS).obj T ⟶ _ => g.appTop.hom r)
    ((BigFppfOver.toScheme B S hS).map_id T)).trans (by simp)

/-- Sections over the identity chart of an object `T` of the site, as global sections of a
module on `T`, linearly over `Γ(T, 𝒪_T)`. -/
def globalSectionsIdEtaleChartLinearEquiv (T : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2) :
    letI : Module Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
        (M.val.obj (op (idEtaleChart B S hS T))) :=
      inferInstanceAs (Module (chartRing B S hS (schemeSpace T).1 (schemeSpace T).2
        (idEtaleChart B S hS T)) _)
    (ModuleCat.restrictScalars (baseFunctionsToGlobalSections B S hS (𝟙 (schemeSpace T)))).obj
        ((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O)).obj M)
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
      (M.val.obj (op (idEtaleChart B S hS T)) : Type u) :=
  globalSectionsLinearEquivOfIsInitial _ M (op (idEtaleChart B S hS T))
    (isTerminalIdEtaleChart B S hS T).op _
    (RingHom.id Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (globalSectionEval_comp_baseFunctionsToGlobalSections_id T)

variable {X Y : AlgebraicSpaces B S hS}

/-- The sections over the identity chart of `V` of the restriction of an `𝒪_Y`-module `G` to an
étale chart `V` of `Y` are the sections of `G` over `V`, linearly over `Γ(V, 𝒪_V)`. -/
def etaleModulePullbackChartSectionsLinearEquiv (V : SmallEtale B S hS Y.1)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    letI : Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
        (((etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).obj G).val.obj
            (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))) :=
      inferInstanceAs (Module (chartRing B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))) _)
    letI : Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
        (G.val.obj (op V)) := inferInstanceAs (Module (chartRing B S hS Y.1 Y.2 V) _)
    (((etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).obj G).val.obj
            (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))) : Type u)
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)]
      (G.val.obj (op V) : Type u) :=
  letI : Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
      (((etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).obj G).val.obj
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))) :=
    inferInstanceAs (Module (chartRing B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))) _)
  letI : Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
      (G.val.obj (op V)) := inferInstanceAs (Module (chartRing B S hS Y.1 Y.2 V) _)
  { toFun x := x
    invFun x := x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    left_inv _ := rfl
    right_inv _ := rfl }

/-- **Stacks 08EX as an isomorphism of `Γ(V, 𝒪_V)`-modules.**  Let `f : X ⟶ Y` be quasi-compact
and quasi-separated, `F` a quasi-coherent `𝒪_X`-module and `V` an affine object of `Y_étale`,
with `f' : X_V = V ×_Y X ⟶ V` the base change.  Then `H^q(X_V, F|_{X_V})`, a module over the
functions on `V` through `f'`, is isomorphic to the sections of `R^q f_*F` over `V`. -/
def chartSectionsHigherDirectImageLinearEquiv (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    letI : Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
        ((((modulePushforward B S hS f).rightDerived q).obj F).val.obj (op V)) :=
      inferInstanceAs (Module (chartRing B S hS Y.1 Y.2 V) _)
    cohomologyRes (baseFunctionsToGlobalSections B S hS
        (chartBaseChangeProjection B S hS f V :
          chartBaseChangeSpace B S hS f V ⟶ schemeSpace ((SmallEtale.toOver B S hS Y.1).obj V)))
        q ((chartBaseChangeModulePullback B S hS f V).obj F)
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)]
      ((((modulePushforward B S hS f).rightDerived q).obj F).val.obj (op V) : Type u) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
    (chartBaseChangeSpace B S hS f V).2
  have := enoughInjectives_modules B S hS (chartBaseChangeTarget B S hS V).1
    (chartBaseChangeTarget B S hS V).2
  let G := ((modulePushforward B S hS f).rightDerived q).obj F
  let G' := (etaleModulePullback B S hS (chartToSpace B S hS Y V)
    (isEtale_chartToSpace B S hS Y V)).obj G
  let ρ := ModuleCat.restrictScalars
    (baseFunctionsToGlobalSections B S hS (𝟙 (schemeSpace ((SmallEtale.toOver B S hS Y.1).obj V))))
  let e₁ := rightDerivedPushforwardGlobalSectionsLinearEquiv (chartBaseChangeProjection B S hS f V)
    (baseFunctionsToGlobalSections B S hS (𝟙 (schemeSpace ((SmallEtale.toOver B S hS Y.1).obj V))))
    (baseFunctionsToGlobalSections B S hS (chartBaseChangeProjection B S hS f V :
      chartBaseChangeSpace B S hS f V ⟶ schemeSpace ((SmallEtale.toOver B S hS Y.1).obj V)))
    (fun a M => modulePushforward_map_globalSmul_pullbackToGlobalFunctions B S hS
      (chartBaseChangeProjection B S hS f V :
        chartBaseChangeSpace B S hS f V ⟶ schemeSpace ((SmallEtale.toOver B S hS Y.1).obj V))
      (𝟙 _) M a)
    ((chartBaseChangeModulePullback B S hS f V).obj F) q
  let e₂ := (ρ.mapIso (cohomologyAffineChartIsoSectionsHigherDirectImage B S hS f hfqc hfqs F
    inferInstance V hV q)).toLinearEquiv
  let e₃ := globalSectionsIdEtaleChartLinearEquiv ((SmallEtale.toOver B S hS Y.1).obj V) G'
  let e₄ := etaleModulePullbackChartSectionsLinearEquiv V G
  letI : Module Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
      (G'.val.obj (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V)))) :=
    inferInstanceAs (Module (chartRing B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))) _)
  e₁.symm.trans (e₂.trans (e₃.trans e₄))

end AlgebraicGeometry.Space
end
