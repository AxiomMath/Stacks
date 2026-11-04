module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback

/-!
# Global sections over the test schemes, and their cohomology and base change

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S`, let `T` be a test scheme over `B`
and let `N` be an `𝒪_{X_T}`-module. For a morphism of test schemes `m : U ⟶ T` the module `N`
pulls back to `N_U` on `X_U`, and its global sections `Γ(X_U, N_U)` are a `Γ(U, 𝒪_U)`-module. A
further morphism `g : U' ⟶ U` restricts sections, `Γ(X_U, N_U) ⟶ Γ(X_{U'}, N_{U'})`.

The proof of Stacks 0D23 uses cohomology and base change (Stacks 0CTM) in the following form:
over an affine `T = Spec(A)`, for `N` invertible and `f` flat, proper and of finite
presentation, `Rf_{T,*}N` is a perfect object of `D(A)` of Tor amplitude in `[0, b]` whose
formation commutes with every base change; so it is represented by a complex `P` of finite
projective `A`-modules in degrees `[0, b]` (Stacks 0658), and for every affine `U = Spec(R')`
over `T`,

`Γ(X_U, N_U) = H⁰(P ⊗_A R') = Ker(d⁰ ⊗ 1 : P⁰ ⊗_A R' ⟶ P¹ ⊗_A R')`,

naturally in `U`. This file records that statement as data,
`AlgebraicGeometry.Space.PicardSituation.GlobalSectionsBaseChangeModel`; it is proved from
Stacks 0CTM elsewhere.

Sections are handled as morphisms out of the structure sheaf
(`AlgebraicGeometry.Space.modelSectionsHomEquiv`); restriction of a section `v : 𝒪 ⟶ N_U` along
`g` is `𝒪 ≅ g^*𝒪 ⟶ g^*N_U ≅ N_{U'}`.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.testModule`: `N_U` for `m : U ⟶ T`.
* `AlgebraicGeometry.Space.PicardSituation.testSections`: `Γ(X_U, F)` as a `Γ(U, 𝒪_U)`-module.
* `AlgebraicGeometry.Space.PicardSituation.restrictSectionHom`: restriction of a section, read as
  a morphism out of `𝒪`, along a morphism of test schemes.
* `AlgebraicGeometry.Space.PicardSituation.restrictSection`: the same on global sections.
* `AlgebraicGeometry.Space.PicardSituation.testRingHom`: `Γ(T, 𝒪_T) ⟶ Γ(U, 𝒪_U)` for `U ⟶ T`.
* `AlgebraicGeometry.Space.PicardSituation.extendScalarsTransition`: `R' ⊗_A M ⟶ R'' ⊗_A M` for a
  morphism of `A`-algebras.
* `AlgebraicGeometry.Space.PicardSituation.GlobalSectionsBaseChangeModel`: **cohomology and base
  change for the global sections of `N`** over an affine test scheme.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space.PicardSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : PicardSituation B S hS)

/-- The module `N_U = (X_U ⟶ X_T)^*N` on the base change along a morphism of test schemes
`m : U ⟶ T`. -/
abbrev testModule {U T : s.SchemesOver} (m : U ⟶ T)
    (N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2) :
    Modules.{u, u} B S hS (s.baseChange U).1 (s.baseChange U).2 :=
  (modulePullback B S hS (baseChangeMap s.f m)).obj N

/-- The global sections `Γ(X_U, F)` of an `𝒪_{X_U}`-module, as a module over `Γ(U, 𝒪_U)` through
the projection `X_U ⟶ U`. -/
abbrev testSections (U : s.SchemesOver)
    (F : Modules.{u, u} B S hS (s.baseChange U).1 (s.baseChange U).2) :
    ModuleCat.{u} (baseRing B S hS U.left) :=
  (baseRingGlobalSectionsModule B S hS (s.baseChange U)
    (baseRingHomOfMap (baseChangeInclusion s.f U))).obj F

/-- Global sections of an `𝒪_{X_U}`-module are the morphisms out of `𝒪_{X_U}`. -/
abbrev testSectionsHomEquiv (U : s.SchemesOver)
    (F : Modules.{u, u} B S hS (s.baseChange U).1 (s.baseChange U).2) :
    s.testSections U F ≃ (unitModule B S hS (s.baseChange U).2 ⟶ F) :=
  modelSectionsHomEquiv B S hS (s.baseChange U) (baseRingHomOfMap (baseChangeInclusion s.f U)) F

/-- **Restriction of a section along a morphism of test schemes**, for sections read as morphisms
out of the structure sheaf: for `g : U' ⟶ U` with `g ≫ m = m'`, the section `v : 𝒪_{X_U} ⟶ N_U`
goes to `𝒪_{X_{U'}} ≅ g^*𝒪_{X_U} ⟶ g^*N_U ≅ N_{U'}`. The composite `m'` is a parameter so that
equal composites need no rewriting. -/
def restrictSectionHom {T U U' : s.SchemesOver} (m : U ⟶ T) (m' : U' ⟶ T) (g : U' ⟶ U)
    (h : g ≫ m = m') (N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (v : unitModule B S hS (s.baseChange U).2 ⟶ s.testModule m N) :
    unitModule B S hS (s.baseChange U').2 ⟶ s.testModule m' N :=
  (modulePullbackUnitIso B S hS (baseChangeMap s.f g)).inv ≫
    (modulePullback B S hS (baseChangeMap s.f g)).map v ≫
      (modulePullbackTriangle B S hS
        ((baseChangeMap_comp s.f g m).symm.trans (congrArg (baseChangeMap s.f) h))).inv.app N

/-- **Restriction of global sections along a morphism of test schemes** `g : U' ⟶ U` with
`g ≫ m = m'`. -/
def restrictSection {T U U' : s.SchemesOver} (m : U ⟶ T) (m' : U' ⟶ T) (g : U' ⟶ U)
    (h : g ≫ m = m') (N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (v : s.testSections U (s.testModule m N)) : s.testSections U' (s.testModule m' N) :=
  (s.testSectionsHomEquiv U' _).symm
    (s.restrictSectionHom m m' g h N (s.testSectionsHomEquiv U _ v))

/-- The restriction of a section is an isomorphism exactly when the pullback of the section
is. -/
theorem isIso_restrictSectionHom_iff {T U U' : s.SchemesOver} (m : U ⟶ T) (m' : U' ⟶ T)
    (g : U' ⟶ U) (h : g ≫ m = m') (N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (v : unitModule B S hS (s.baseChange U).2 ⟶ s.testModule m N) :
    IsIso (s.restrictSectionHom m m' g h N v) ↔
      IsIso ((modulePullback B S hS (baseChangeMap s.f g)).map v) := by
  constructor
  · intro hi
    have h₁ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hi
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h₁
  · intro hv
    exact IsIso.comp_isIso' (inferInstance) (IsIso.comp_isIso' hv inferInstance)

/-- The ring map `Γ(T, 𝒪_T) ⟶ Γ(U, 𝒪_U)` of a morphism of test schemes `m : U ⟶ T`. -/
abbrev testRingHom {U T : s.SchemesOver} (m : U ⟶ T) :
    baseRing B S hS T.left →+* baseRing B S hS U.left :=
  (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.left).op).hom

/-- The ring map of a composite of morphisms of test schemes is the composite of the ring
maps. -/
theorem testRingHom_comp {V U T : s.SchemesOver} (g : V ⟶ U) (m : U ⟶ T) :
    s.testRingHom (g ≫ m) = (s.testRingHom g).comp (s.testRingHom m) := by
  simp only [testRingHom, CostructuredArrow.comp_left, Functor.map_comp, op_comp,
    CommRingCat.hom_comp]

/-- The transition `R' ⊗_A M ⟶ R'' ⊗_A M`, `r ⊗ x ↦ ψ(r) ⊗ x`, of a ring map `ψ : R' ⟶ R''`
compatible with given ring maps from `A`. -/
def extendScalarsTransition {A R' R'' : Type u} [CommRing A] [CommRing R'] [CommRing R'']
    (φ : A →+* R') (φ' : A →+* R'') (ψ : R' →+* R'') (h : ψ.comp φ = φ') (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars φ).obj M →+ (ModuleCat.extendScalars φ').obj M :=
  (TensorProduct.map (R := A)
    ({ toFun := fun (r : R') => (ψ r : R'')
       map_add' := fun a b => map_add ψ a b
       map_smul' := fun a (r : R') => by
         change ψ (φ a * r) = φ' a * ψ r
         rw [map_mul, ← h, RingHom.comp_apply] } :
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of R' R') →ₗ[A]
        (ModuleCat.restrictScalars φ').obj (ModuleCat.of R'' R''))
    (LinearMap.id : M →ₗ[A] M)).toAddMonoidHom

/-- The transition on a pure tensor. -/
theorem extendScalarsTransition_tmul {A R' R'' : Type u} [CommRing A] [CommRing R']
    [CommRing R''] (φ : A →+* R') (φ' : A →+* R'') (ψ : R' →+* R'') (h : ψ.comp φ = φ')
    (M : ModuleCat.{u} A) (r : R') (x : M) :
    extendScalarsTransition φ φ' ψ h M
        (r ⊗ₜ[A] x : (ModuleCat.restrictScalars φ).obj (ModuleCat.of R' R') ⊗[A] M) =
      ((ψ r : R'') ⊗ₜ[A] x : (ModuleCat.restrictScalars φ').obj (ModuleCat.of R'' R'') ⊗[A] M) :=
  rfl

/-- The kernel of `d ⊗ 1 : R' ⊗_A M ⟶ R' ⊗_A N` for a morphism `d` of `A`-modules. -/
abbrev extendScalarsKernel {A R' : Type u} [CommRing A] [CommRing R'] (φ : A →+* R')
    {M N : ModuleCat.{u} A} (d : M ⟶ N) : Submodule R' ((ModuleCat.extendScalars φ).obj M) :=
  LinearMap.ker ((ModuleCat.extendScalars φ).map d).hom

/-- **Cohomology and base change for the global sections of `N`, over an affine test scheme
`T = Spec(A)`.** A complex `P` of finite projective `A`-modules concentrated in degrees `[0, b]`
together with, for every affine test scheme `U = Spec(R')` over `T`, an `R'`-linear
identification

`Γ(X_U, N_U) ≅ H⁰(P ⊗_A R') = Ker(d⁰ ⊗ 1 : P⁰ ⊗_A R' ⟶ P¹ ⊗_A R')`,

natural in `U`: restriction of sections along `g : U' ⟶ U` corresponds to `r ⊗ x ↦ g^♯(r) ⊗ x`.

This is the form in which the proof of Stacks 0D23 uses Stacks 0CTM: `Rf_{T,*}N` is perfect
of Tor amplitude in `[0, b]` (there is no cohomology in negative degrees) and its formation
commutes with arbitrary base change, so it is represented by such a `P` (Stacks 0658) and its
degree zero cohomology after base change to `U` is `Γ(X_U, N_U)`. -/
structure GlobalSectionsBaseChangeModel (T : s.SchemesOver)
    (N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2) where
  /-- The representing complex. -/
  complex : CochainComplex (ModuleCat.{u} (baseRing B S hS T.left)) ℤ
  /-- The top degree of the complex. -/
  top : ℤ
  /-- The complex is concentrated in degrees `≥ 0`. -/
  isStrictlyGE : complex.IsStrictlyGE 0
  /-- The complex is concentrated in degrees `≤ top`. -/
  isStrictlyLE : complex.IsStrictlyLE top
  /-- Each term of the complex is a finite module. -/
  finite : ∀ i, Module.Finite (baseRing B S hS T.left) (complex.X i)
  /-- Each term of the complex is a projective module. -/
  projective : ∀ i, Module.Projective (baseRing B S hS T.left) (complex.X i)
  /-- The identification of the global sections over an affine test scheme over `T` with the
  degree zero cohomology of the base changed complex. -/
  sectionsEquiv : ∀ {U : s.SchemesOver} (m : U ⟶ T),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U.left) →
      (s.testSections U (s.testModule m N) ≃ₗ[baseRing B S hS U.left]
        extendScalarsKernel (s.testRingHom m) (complex.d 0 1))
  /-- The identification is natural in the affine test scheme. -/
  sectionsEquiv_naturality : ∀ {U U' : s.SchemesOver} (m : U ⟶ T) (m' : U' ⟶ T) (g : U' ⟶ U)
    (h : g ≫ m = m') (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.left))
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U'.left))
    (v : s.testSections U (s.testModule m N)),
    ((sectionsEquiv m' hU' (s.restrictSection m m' g h N v) :
        (ModuleCat.extendScalars (s.testRingHom m')).obj (complex.X 0))) =
      extendScalarsTransition (s.testRingHom m) (s.testRingHom m') (s.testRingHom g)
        (by rw [← h, s.testRingHom_comp]) (complex.X 0) (sectionsEquiv m hU v)

end AlgebraicGeometry.Space.PicardSituation

end
