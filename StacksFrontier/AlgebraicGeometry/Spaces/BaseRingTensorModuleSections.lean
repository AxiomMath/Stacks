module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback

/-!
# The sections `1 ⊗ m` of `𝒪_X ⊗_R M`

For an algebraic space `X`, a base-ring datum `φ : R →+* Γ(X, 𝒪_X)` and an `R`-module `M`, every
`m ∈ M` gives the global section `1 ⊗ m` of the module `𝒪_X ⊗_R M` of [Stacks Project, Tag 0D3F]
(`AlgebraicGeometry.Space.baseRingTensorModule`): the image of `m` under the unit of the mapping
property `AlgebraicGeometry.Space.baseRingTensorModuleAdjunction`, read as a morphism
`𝒪_X ⟶ 𝒪_X ⊗_R M` (`AlgebraicGeometry.Space.baseRingTensorSection`).

This file records how these sections move along the identifications between such modules:
along `𝒪_X ⊗_R g` they go to the sections of `g m`; along the change of rings
`𝒪_X ⊗_{R'} (R' ⊗_R M) ≅ 𝒪_X ⊗_R M` and, for surjective `R ⟶ R'`, `𝒪_X ⊗_R N ≅ 𝒪_X ⊗_{R'} N`
they are preserved; and the pullback along `f : X ⟶ T` of the section `1 ⊗ m` of
`𝒪_T ⊗_R M` is the section `1 ⊗ m` of `f^*(𝒪_T ⊗_R M) ≅ 𝒪_X ⊗_R M`. A morphism out of
`𝒪_X ⊗_R M` is determined by its values on these sections.

## Main definitions

* `AlgebraicGeometry.Space.baseRingTensorSection`: the section `1 ⊗ m` of `𝒪_X ⊗_R M`.

## Main results

* `AlgebraicGeometry.Space.baseRingTensorSection_map`,
  `AlgebraicGeometry.Space.baseRingTensorSection_compIso_hom`,
  `AlgebraicGeometry.Space.baseRingTensorSection_restrictScalarsIso_hom`,
  `AlgebraicGeometry.Space.baseRingTensorSection_pullbackIso_hom`: the sections along the
  identifications.
* `AlgebraicGeometry.Space.baseRingTensorModule_hom_ext`: morphisms out of `𝒪_X ⊗_R M` agreeing
  on the sections `1 ⊗ m` are equal.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- **The section `1 ⊗ m` of `𝒪_X ⊗_R M`**: the image of `m` under the unit of the mapping
property of `𝒪_X ⊗_R -`, read as a morphism `𝒪_X ⟶ 𝒪_X ⊗_R M`. -/
def baseRingTensorSection (M : ModuleCat.{u} R) (m : M) :
    unitModule B S hS X.2 ⟶ (baseRingTensorModule B S hS X φ).obj M :=
  modelSectionsHomEquiv B S hS X φ _
    (((baseRingTensorModuleAdjunction B S hS X φ).unit.app M).hom m)

/-- A morphism `k` out of `𝒪_X ⊗_R M` sends `1 ⊗ m` to the section corresponding to the image of
`1 ⊗ m` under the right adjoint of `k`. -/
private theorem baseRingTensorSection_comp_eq {M : ModuleCat.{u} R}
    {F : Modules.{u, u} B S hS X.1 X.2} {k : (baseRingTensorModule B S hS X φ).obj M ⟶ F} (m : M)
    {s : (baseRingGlobalSectionsModule B S hS X φ).obj F}
    (h : (baseRingGlobalSectionsModule B S hS X φ).map k
      (((baseRingTensorModuleAdjunction B S hS X φ).unit.app M).hom m) = s) :
    baseRingTensorSection B S hS X φ M m ≫ k = modelSectionsHomEquiv B S hS X φ F s := by
  rw [baseRingTensorSection, ← modelSectionsHomEquiv_naturality, h]

/-- The sections `1 ⊗ m` move along `𝒪_X ⊗_R g` to the sections `1 ⊗ g(m)`. -/
theorem baseRingTensorSection_map {M N : ModuleCat.{u} R} (g : M ⟶ N) (m : M) :
    baseRingTensorSection B S hS X φ M m ≫ (baseRingTensorModule B S hS X φ).map g =
      baseRingTensorSection B S hS X φ N (g.hom m) := by
  exact baseRingTensorSection_comp_eq B S hS X φ m
    (congrArg (fun k => k.hom m)
      ((baseRingTensorModuleAdjunction B S hS X φ).unit.naturality g)).symm

/-- **Morphisms out of `𝒪_X ⊗_R M` are determined by the sections `1 ⊗ m`.** -/
theorem baseRingTensorModule_hom_ext {M : ModuleCat.{u} R}
    {F : Modules.{u, u} B S hS X.1 X.2} {a b : (baseRingTensorModule B S hS X φ).obj M ⟶ F}
    (h : ∀ m : M, baseRingTensorSection B S hS X φ M m ≫ a =
      baseRingTensorSection B S hS X φ M m ≫ b) : a = b := by
  apply ((baseRingTensorModuleAdjunction B S hS X φ).homEquiv _ _).injective
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (modelSectionsHomEquiv B S hS X φ F).injective <|
    (modelSectionsHomEquiv_naturality B S hS X φ a _).trans <|
      (h m).trans (modelSectionsHomEquiv_naturality B S hS X φ b _).symm

section ChangeOfRings

variable {R' : Type u} [CommRing R'] (ψ : R →+* R') (φ' : R' →+* modelGlobalFunctions B S hS X)

/-- **The sections `1 ⊗ m` under change of rings**: the section `1 ⊗ (1 ⊗ m)` of
`𝒪_X ⊗_{R'} (R' ⊗_R M)` is carried to the section `1 ⊗ m` of `𝒪_X ⊗_R M`. -/
theorem baseRingTensorSection_compIso_hom (M : ModuleCat.{u} R) (m : M) :
    baseRingTensorSection B S hS X φ' ((ModuleCat.extendScalars.{u, u, u} ψ).obj M)
        ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).unit.app M).hom m)) ≫
        (baseRingTensorModuleCompIso B S hS X ψ φ').hom.app M =
      baseRingTensorSection B S hS X (φ'.comp ψ) M m := by
  exact (baseRingTensorSection_comp_eq B S hS X φ' _
    (congrArg (fun k => k.hom m) (Adjunction.unit_leftAdjointUniq_hom_app
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).comp
        (baseRingTensorModuleAdjunction B S hS X φ'))
      ((baseRingTensorModuleAdjunction B S hS X (φ'.comp ψ)).ofNatIsoRight
        (baseRingGlobalSectionsModuleCompIso B S hS X ψ φ')) M))).trans rfl

variable {ψ} in
/-- **The sections `1 ⊗ n` along `𝒪_X ⊗_R N ≅ 𝒪_X ⊗_{R'} N`**, for surjective `ψ : R ⟶ R'` and an
`R'`-module `N` read as an `R`-module. -/
theorem baseRingTensorSection_restrictScalarsIso_hom (hψ : Function.Surjective ψ)
    (N : ModuleCat.{u} R') (n : N) :
    baseRingTensorSection B S hS X (φ'.comp ψ) ((ModuleCat.restrictScalars.{u} ψ).obj N) n ≫
        (baseRingTensorModuleRestrictScalarsIso B S hS X ψ φ' hψ).hom.app N =
      baseRingTensorSection B S hS X φ' N n := by
  have : Fact (Function.Surjective ψ) := ⟨hψ⟩
  have e : (baseRingTensorModuleRestrictScalarsIso B S hS X ψ φ' hψ).hom.app N =
      (baseRingTensorModuleCompIso B S hS X ψ φ').inv.app
          ((ModuleCat.restrictScalars.{u} ψ).obj N) ≫
        (baseRingTensorModule B S hS X φ').map
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).counit.app N) := by
    simp [baseRingTensorModuleRestrictScalarsIso]
  rw [e]
  refine (congrArg (· ≫ _ ≫ _) (baseRingTensorSection_compIso_hom B S hS X ψ φ'
    ((ModuleCat.restrictScalars.{u} ψ).obj N) n).symm).trans ?_
  rw [Category.assoc, Iso.hom_inv_id_app_assoc]
  refine (baseRingTensorSection_map B S hS X φ' _ _).trans ?_
  exact congrArg (baseRingTensorSection B S hS X φ' N)
    (congrArg (fun k => k.hom n)
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).right_triangle_components N))

end ChangeOfRings

section Pullback

variable {X} {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)

/-- **The pullback of the section `1 ⊗ m`** of `𝒪_T ⊗_R M`, `R = Γ(T, 𝒪_T)`, along `f : X ⟶ T` is
the section `1 ⊗ m` of `f^*(𝒪_T ⊗_R M) ≅ 𝒪_X ⊗_R M`. -/
theorem baseRingTensorSection_pullbackIso_hom (M : ModuleCat.{u} (baseRing B S hS T)) (m : M) :
    (modulePullbackUnitIso B S hS f).inv ≫
        (modulePullback B S hS f).map (baseRingTensorSection B S hS (schemeSpace T)
          (baseRingHomOfMap (𝟙 (schemeSpace T))) M m) ≫
        (baseRingTensorModulePullbackIso B S hS f).hom.app M =
      baseRingTensorSection B S hS X (baseRingHomOfMap f) M m := by
  have h := congrArg (fun k => k.hom m) (Adjunction.unit_leftAdjointUniq_hom_app
    ((baseRingTensorModuleAdjunction B S hS (schemeSpace T) _).comp
      (modulePullbackAdjunction B S hS f))
    ((baseRingTensorModuleAdjunction B S hS X (baseRingHomOfMap f)).ofNatIsoRight
      (pushforwardGlobalSectionsIso B S hS f).symm) M)
  have hP : pushforwardSectionsHomEquiv B S hS f _
      ((((baseRingTensorModuleAdjunction B S hS (schemeSpace T) _).comp
        (modulePullbackAdjunction B S hS f)).unit.app M).hom m) =
      (modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map
        (baseRingTensorSection B S hS (schemeSpace T)
          (baseRingHomOfMap (𝟙 (schemeSpace T))) M m) := by
    rw [pushforwardSectionsHomEquiv_apply, Adjunction.comp_unit_app, ModuleCat.comp_apply,
      modelSectionsHomEquiv_naturality, Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_counit]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·)
      ((modulePullbackAdjunction B S hS f).left_triangle_components _)).trans (Category.comp_id _))
  have hQ : pushforwardSectionsHomEquiv B S hS f _
      ((((baseRingTensorModuleAdjunction B S hS X (baseRingHomOfMap f)).ofNatIsoRight
        (pushforwardGlobalSectionsIso B S hS f).symm).unit.app M).hom m) =
      baseRingTensorSection B S hS X (baseRingHomOfMap f) M m :=
    (pushforwardSectionsHomEquiv B S hS f _).apply_symm_apply _
  rw [← hQ, ← h, ModuleCat.comp_apply]
  refine Eq.trans ?_ (pushforwardSectionsHomEquiv_naturality B S hS f _ _).symm
  rw [hP, Category.assoc]
  rfl

end Pullback

end AlgebraicGeometry.Space

end
