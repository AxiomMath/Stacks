module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CompletionAssociatedPrimeDepth
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrum

/-!
# Left exactness of sections of a sheaf of modules on an affine scheme

This file proves that `Γ(U, -)` carries injections of `𝒪_{Spec R}`-modules to injections of
modules: an injection of `R`-modules `M ↪ N` induces an injection `Γ(M^~, U) ↪ Γ(N^~, U)` for
*every* open `U`, in particular over the punctured spectrum. Applied to the injection `R ⧸ 𝔭 ↪ R`
coming from an associated prime, the inclusion `𝒪_{V(𝔭)} ⊆ ℱ` of the sketch of
[Stacks, Tag 0AWC], it shows that the sections of the structure sheaf over the punctured spectrum
of a Noetherian local ring with a one-dimensional associated component are not a finite module.

## Main definitions

* `Stacks.LocalCohomology.appLinearMap`: the `R`-linear map on sections induced by a morphism of
  `𝒪_{Spec R}`-modules.
* `Stacks.LocalCohomology.sectionsTildeSelfLinearEquiv`: `Γ(R^~, U) ≅ Γ(Spec R, U)` as
  `R`-modules.
* `Stacks.LocalCohomology.sectionsTopPushforwardQuotientLinearEquiv`: the global sections of
  `(Spec φ)_*𝒪_{Spec (R ⧸ 𝔭)}` are `R ⧸ 𝔭`, for `φ : R ⟶ R ⧸ 𝔭`.
* `Stacks.LocalCohomology.tildeQuotientIsoPushforward`: `(R ⧸ 𝔭)^~ ≅ 𝒪_{V(𝔭)}`, i.e. the direct
  image of the structure sheaf of `Spec (R ⧸ 𝔭)`.

## Main results

* `Stacks.LocalCohomology.app_injective_of_app_basicOpen_injective`: a morphism of
  `𝒪_{Spec R}`-modules injective on sections over every basic open is injective on sections over
  every open.
* `Stacks.LocalCohomology.tilde_map_app_injective`: hence `M^~ ⟶ N^~` is injective on sections
  over every open as soon as `M ⟶ N` is injective.
* `Stacks.LocalCohomology.exists_injective_sections_tilde_of_isAssociatedPrimeStacks`: for `𝔭` an
  associated prime of `R` in the Stacks sense, an injective `R`-linear map
  `Γ((R ⧸ 𝔭)^~, U) →ₗ[R] Γ(R^~, U)` for every open `U`.
* `Stacks.LocalCohomology.not_module_finite_sections_puncturedSpectrum_of_injective`: the local
  content of [Stacks, Tag 0AWC] assembled — given an injection of `Frac(B ⧸ 𝔭)` into the sections
  of `(B ⧸ 𝔭)^~` over the punctured spectrum, the sections of the structure sheaf over the
  punctured spectrum of `B` are not a finite `B`-module.
* `Stacks.LocalCohomology.smul_sections_pushforward_unit`: the `R`-module structure on the
  sections of `(Spec φ)_*𝒪_{Spec S}` is the `S`-module structure restricted along `φ`.
* `Stacks.LocalCohomology.exists_injective_fractionRing_sections_pushforward` and
  `Stacks.LocalCohomology.exists_injective_fractionRing_sections_tilde_quotient`: the injection
  `Frac(R ⧸ 𝔭) ↪ Γ((R ⧸ 𝔭)^~, puncturedSpectrum R)`, which is the hypothesis of the previous item
  discharged.
* `Stacks.LocalCohomology.not_module_finite_sections_puncturedSpectrum`: hence, with no hypotheses
  beyond the local algebra, the sections of the structure sheaf over the punctured spectrum of a
  Noetherian local ring with a one-dimensional associated component are not a finite module.

## Implementation notes

Everything is phrased for `R : CommRingCat`: Mathlib's `Module R Γ(M, U)` and
`IsLocalization.Away f Γ(Spec R, -)` instances are keyed on the carrier of a `CommRingCat` and are
not found for a bare type. For the same reason
`exists_injective_fractionRing_sections_pushforward` is stated for a *variable* `S : CommRingCat`
and only applied at `CommRingCat.of (ToType R ⧸ 𝔭)`: for a concrete `CommRingCat.of A` the
instance `Algebra ↑(CommRingCat.of A) Γ(Spec (CommRingCat.of A), U)` is not found, because it is
keyed on the `CommRing` instance that `CommRingCat` carries and for `CommRingCat.of A` instance
search finds `A`'s own instead.

Two other places where a definitional equality has to be forced at default transparency rather
than at the `instances` transparency of instance search, both resolved by writing a term instead
of a tactic:

* the proof of `smul_sections_pushforward_unit` spells the action with `@Mul.mul` at the carrier
  of `Γ(Spec S, Spec φ ⁻¹ᵁ V)`. The two carriers are definitionally equal — that is
  `AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj` — but not syntactically equal, so the
  arithmetic elaborator cannot find the multiplication; and after the rewrite the goal is no
  longer type-correct at `instances` transparency, so `rw` cannot continue and the proof finishes
  with `Eq.trans` and `congrArg`.
* `tildeQuotientIsoPushforward` passes its `IsIso` instance positionally. Instance search compares
  the source of `AlgebraicGeometry.Scheme.Modules.fromTildeΓ` at `instances` transparency, where
  `(tilde.functor R).obj (moduleSpecΓFunctor.obj M)` and
  `tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))` disagree.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.LocalCohomology

variable {R : CommRingCat.{u}}

/-- **Left exactness of `Γ(U, -)` on `𝒪_{Spec R}`-modules.** A morphism of `𝒪_{Spec R}`-modules
that is injective on sections over every basic open is injective on sections over every open. -/
theorem app_injective_of_app_basicOpen_injective {M N : (Spec R).Modules} (α : M ⟶ N)
    (h : ∀ f : R, Function.Injective (α.app (PrimeSpectrum.basicOpen f))) (U : (Spec R).Opens) :
    Function.Injective (α.app U) := by
  have hbasis : ∀ x : Spec R,
      Function.Injective ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
        (modulesSpecToSheaf.map α).1) := by
    refine fun x => TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
      PrimeSpectrum.isBasis_basic_opens ?_ x
    rintro V ⟨f, rfl⟩
    exact h f
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
    (modulesSpecToSheaf.map α).1 U fun x _ => hbasis x

/-- An injection `M ⟶ N` of `R`-modules induces an injection on the sections of `M^~` and `N^~`
over every basic open. -/
theorem tilde_map_app_basicOpen_injective {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    (hφ : Function.Injective φ) (r : R) :
    Function.Injective ((tilde.map φ).app (PrimeSpectrum.basicOpen r)) := by
  have key : ((modulesSpecToSheaf.map (tilde.map φ)).1.app
        (op (PrimeSpectrum.basicOpen r))).hom =
      IsLocalizedModule.map (Submonoid.powers r)
        (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
        (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom φ.hom := by
    refine IsLocalizedModule.linearMap_ext (Submonoid.powers r)
      (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom ?_
    rw [IsLocalizedModule.map_comp]
    exact congr(ModuleCat.Hom.hom $(tilde.toOpen_map_app φ (PrimeSpectrum.basicOpen r)))
  show Function.Injective ((modulesSpecToSheaf.map (tilde.map φ)).1.app
    (op (PrimeSpectrum.basicOpen r))).hom
  rw [key]
  exact IsLocalizedModule.map_injective _ _ _ _ hφ

/-- **`M ↦ M^~` carries injections to injections on sections over every open.** -/
theorem tilde_map_app_injective {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    (hφ : Function.Injective φ) (U : (Spec R).Opens) :
    Function.Injective ((tilde.map φ).app U) :=
  app_injective_of_app_basicOpen_injective (tilde.map φ)
    (tilde_map_app_basicOpen_injective φ hφ) U

/-- The `R`-linear map on sections over an open induced by a morphism of `𝒪_{Spec R}`-modules.

The component `α.app U` is linear over `Γ(Spec R, U)`; this restricts the scalars to `R` along
`algebraMap R Γ(Spec R, U)`. -/
def appLinearMap {M N : (Spec R).Modules} (α : M ⟶ N) (U : (Spec R).Opens) :
    Γ(M, U) →ₗ[R] Γ(N, U) :=
  ((modulesSpecToSheaf.map α).1.app (op U)).hom

/-- `Stacks.LocalCohomology.appLinearMap α U` is the component `α.app U`. -/
@[simp]
theorem appLinearMap_apply {M N : (Spec R).Modules} (α : M ⟶ N) (U : (Spec R).Opens)
    (x : Γ(M, U)) : appLinearMap α U x = α.app U x := rfl

/-- **The sketch's inclusion `𝒪_{V(𝔭)} ⊆ ℱ` on sections.** An associated prime `𝔭` of `R` in the
Stacks sense gives, over every open `U` of `Spec R`, an injective `R`-linear map from the sections
of `(R ⧸ 𝔭)^~` to the sections of the structure sheaf. -/
theorem exists_injective_sections_tilde_of_isAssociatedPrimeStacks {p : Ideal (ToType R)}
    (hp : IsAssociatedPrimeStacks (ToType R) (ToType R) p) (U : (Spec R).Opens) :
    ∃ ψ : Γ(tilde (ModuleCat.of R (ToType R ⧸ p)), U) →ₗ[R]
      Γ(tilde (ModuleCat.of R (ToType R)), U), Function.Injective ψ := by
  obtain ⟨φ, hφ⟩ := exists_injective_quotient_of_isAssociatedPrimeStacks hp
  exact ⟨appLinearMap (tilde.map (ModuleCat.ofHom φ)) U, tilde_map_app_injective _ hφ U⟩

/-- **The local content of [Stacks, Tag 0AWC], assembled.**

Let `R` be a Noetherian local ring, `𝔭` an associated prime of `R` in the Stacks sense with
`dim(R ⧸ 𝔭) = 1`, and `K` a fraction field of `R ⧸ 𝔭`. Suppose given an injective `R`-linear map
`θ` from `K` into the sections of `(R ⧸ 𝔭)^~` over the punctured spectrum of `R`. Then the
sections of the structure sheaf over the punctured spectrum of `R` are *not* a finite
`R`-module. -/
theorem not_module_finite_sections_puncturedSpectrum_of_injective (R : CommRingCat.{u})
    [IsNoetherianRing R] [IsLocalRing R] {p : Ideal (ToType R)} [p.IsPrime]
    (hp : IsAssociatedPrimeStacks (ToType R) (ToType R) p)
    (hdim : ringKrullDim (ToType R ⧸ p) = 1)
    (K : Type u) [CommRing K] [Algebra (ToType R) K] [Algebra (ToType R ⧸ p) K]
    [IsScalarTower (ToType R) (ToType R ⧸ p) K] [IsFractionRing (ToType R ⧸ p) K]
    (θ : K →ₗ[R] Γ(tilde (ModuleCat.of R (ToType R ⧸ p)), puncturedSpectrum R))
    (hθ : Function.Injective θ) :
    ¬ Module.Finite (ToType R) Γ(tilde (ModuleCat.of R (ToType R)), puncturedSpectrum R) := by
  obtain ⟨ψ, hψ⟩ := exists_injective_sections_tilde_of_isAssociatedPrimeStacks hp
    (puncturedSpectrum R)
  exact not_module_finite_of_injective_of_ringKrullDim_quotient_eq_one p K hdim
    (ψ ∘ₗ θ) (hψ.comp hθ)

/-! ### Sections of `𝒪_{Spec R}` and of `R^~` -/

/-- **The two `R`-module structures on `Γ(Spec R, U)` agree.** `Γ(R^~, U)` and `Γ(Spec R, U)`
have the same carrier, and the identity is `R`-linear from the module structure of the sheaf of
modules `R^~` to that of the `R`-algebra `Γ(Spec R, U)`. -/
def sectionsTildeSelfLinearEquiv (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    Γ(tilde (ModuleCat.of R (ToType R)), U) ≃ₗ[R] Γ(Spec R, U) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' r x := (Algebra.smul_def (A := Γ(Spec R, U)) r x).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Stacks.LocalCohomology.sectionsTildeSelfLinearEquiv` is the identity on carriers. -/
@[simp]
theorem sectionsTildeSelfLinearEquiv_apply (R : CommRingCat.{u}) (U : (Spec R).Opens)
    (x : Γ(tilde (ModuleCat.of R (ToType R)), U)) :
    sectionsTildeSelfLinearEquiv R U x = x := rfl

/-- A morphism of `𝒪_{Spec R}`-modules which is an isomorphism is injective on sections over
every open. -/
theorem injective_appLinearMap_of_isIso {M N : (Spec R).Modules} (α : M ⟶ N) [IsIso α]
    (U : (Spec R).Opens) : Function.Injective (appLinearMap α U) := fun _ _ h =>
  (ConcreteCategory.bijective_of_isIso (α.app U)).1 h

/-! ### The direct image of the structure sheaf along the spectrum of a ring map -/

/-- **The two routes from `R` to `Γ(Spec S, Spec φ ⁻¹ᵁ V)` agree.** Restricting a global section
of `𝒪_{Spec R}` to `V` and pulling it back along `Spec φ` is the same as pushing it along `φ` and
restricting the resulting global section of `𝒪_{Spec S}` to `Spec φ ⁻¹ᵁ V`. -/
theorem ΓSpecIso_inv_map_leTop_app {R S : CommRingCat.{u}} (φ : R ⟶ S) (V : (Spec R).Opens) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map V.leTop.op ≫ (Spec.map φ).app V =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫
        (Spec S).presheaf.map (Spec.map φ ⁻¹ᵁ V).leTop.op := by
  have h : (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).app ⊤ = φ ≫ (Scheme.ΓSpecIso S).inv :=
    (Scheme.ΓSpecIso_inv_naturality φ).symm
  rw [(Spec.map φ).naturality V.leTop.op, ← Category.assoc, h]
  exact Category.assoc _ _ _

/-- **Scalars act on the sections of `(Spec φ)_*𝒪_{Spec S}` through `φ`.** The sections of the
direct image over `V` are, by definition
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`), the sections of `𝒪_{Spec S}` over
`Spec φ ⁻¹ᵁ V`, and the `R`-action obtained from the direct image is the `S`-action on those
sections restricted along `φ`. -/
theorem smul_sections_pushforward_unit {R S : CommRingCat.{u}} (φ : R ⟶ S) (V : (Spec R).Opens)
    (r : R) (x : Γ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit.{u} (Spec S).ringCatSheaf), V)) :
    (r • x : Γ((Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit.{u} (Spec S).ringCatSheaf), V)) =
      φ r • (show ToType Γ(Spec S, Spec.map φ ⁻¹ᵁ V) from x) := by
  have h := ConcreteCategory.congr_hom (ΓSpecIso_inv_map_leTop_app φ V) r
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  have hl : (r • x : Γ((Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit.{u} (Spec S).ringCatSheaf), V)) =
      @Mul.mul (ToType Γ(Spec S, Spec.map φ ⁻¹ᵁ V)) _
        ((Spec.map φ).app V ((Spec R).presheaf.map V.leTop.op ((Scheme.ΓSpecIso R).inv r))) x :=
    rfl
  rw [Algebra.smul_def]
  exact hl.trans (congrArg (fun t => @Mul.mul (ToType Γ(Spec S, Spec.map φ ⁻¹ᵁ V)) _ t x) h)

/-- **`Γ(Spec (R ⧸ 𝔭), ⊤)` is `R ⧸ 𝔭` as an `R`-module.** The global sections of the direct image
of `𝒪_{Spec (R ⧸ 𝔭)}` along `Spec (R ⧸ 𝔭) ⟶ Spec R` are `R ⧸ 𝔭`, `R`-linearly, through
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
def sectionsTopPushforwardQuotientLinearEquiv (R : CommRingCat.{u}) (p : Ideal (ToType R)) :
    Γ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p) : R ⟶
      CommRingCat.of (ToType R ⧸ p)))).obj (SheafOfModules.unit.{u} _),
        (⊤ : (Spec R).Opens)) ≃ₗ[R] (ToType R ⧸ p) :=
  have hnat : ∀ r : R, (Scheme.ΓSpecIso (CommRingCat.of (ToType R ⧸ p))).hom
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p) : R ⟶
        CommRingCat.of (ToType R ⧸ p))).appTop ((Scheme.ΓSpecIso R).inv r)) =
        algebraMap (ToType R) (ToType R ⧸ p) r := fun r => by
    have h := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk p) : R ⟶
        CommRingCat.of (ToType R ⧸ p))) ((Scheme.ΓSpecIso R).inv r)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    rw [h]
    simp [Ideal.Quotient.algebraMap_eq]
  { toFun x := (Scheme.ΓSpecIso (CommRingCat.of (ToType R ⧸ p))).hom
      (x : Γ(Spec (CommRingCat.of (ToType R ⧸ p)), ⊤))
    invFun y := ((Scheme.ΓSpecIso (CommRingCat.of (ToType R ⧸ p))).inv y :
      Γ(Spec (CommRingCat.of (ToType R ⧸ p)), ⊤))
    map_add' _ _ := map_add _ _ _
    map_smul' r x :=
      ((map_mul (Scheme.ΓSpecIso (CommRingCat.of (ToType R ⧸ p))).hom.hom
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p) : R ⟶
            CommRingCat.of (ToType R ⧸ p))).appTop ((Scheme.ΓSpecIso R).inv r)) x).trans
        (by rw [hnat])).trans (Algebra.smul_def r _).symm
    left_inv x := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of (ToType R ⧸ p))).hom_inv_id x
    right_inv y := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of (ToType R ⧸ p))).inv_hom_id y }

/-- **`(R ⧸ 𝔭)^~ ≅ 𝒪_{V(𝔭)}`.** The quasi-coherent module `(R ⧸ 𝔭)^~` on `Spec R` is the direct
image of the structure sheaf of `Spec (R ⧸ 𝔭)`. -/
def tildeQuotientIsoPushforward (R : CommRingCat.{u}) (p : Ideal (ToType R)) :
    tilde (ModuleCat.of R (ToType R ⧸ p)) ≅
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p) : R ⟶
        CommRingCat.of (ToType R ⧸ p)))).obj (SheafOfModules.unit.{u} _) :=
  (tilde.functor R).mapIso (sectionsTopPushforwardQuotientLinearEquiv R p).symm.toModuleIso ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p) : R ⟶
        CommRingCat.of (ToType R ⧸ p)))).obj (SheafOfModules.unit.{u} _)))
      (isIso_fromTildeΓ_pushforward _ _)

/-- **A fraction field of `S` embeds `R`-linearly into the sections of `(Spec φ)_*𝒪_{Spec S}`
over the punctured spectrum of `R`.**

Here `φ : R ⟶ S` is a surjection of local rings, `S` is a one-dimensional domain, and `K` is a
fraction field of `S` carrying an `R`-action through `φ`. -/
theorem exists_injective_fractionRing_sections_pushforward {R S : CommRingCat.{u}}
    [IsLocalRing R] [IsLocalRing S] [IsDomain S] (φ : R ⟶ S)
    (hφ : Function.Surjective φ.hom) (hS : ringKrullDim (ToType S) = 1)
    (K : Type u) [CommRing K] [Module R K] [Algebra (ToType S) K] [IsFractionRing (ToType S) K]
    (hsmul : ∀ (r : R) (k : K), r • k = φ r • k) :
    ∃ θ : K →ₗ[R] Γ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit.{u} (Spec S).ringCatSheaf), puncturedSpectrum R),
      Function.Injective θ := by
  have : IsFractionRing S Γ(Spec S, Spec.map φ ⁻¹ᵁ puncturedSpectrum R) :=
    isFractionRing_sections_preimage_puncturedSpectrum φ hφ hS
  let α := IsLocalization.algEquiv (nonZeroDivisors (ToType S)) K
    Γ(Spec S, Spec.map φ ⁻¹ᵁ puncturedSpectrum R)
  refine ⟨{ toFun k := α k
            map_add' a b := map_add α a b
            map_smul' r k := ?_ }, α.injective⟩
  rw [RingHom.id_apply, smul_sections_pushforward_unit φ (puncturedSpectrum R) r (α k), hsmul]
  exact map_smul α (φ r) k

/-- **The sheaf-level identification `Frac(R ⧸ 𝔭) ↪ Γ((R ⧸ 𝔭)^~, V)`.**

Let `R` be a local ring and `𝔭` a prime with `dim(R ⧸ 𝔭) = 1`, and let `K` be a fraction field of
`R ⧸ 𝔭`. Then `K` embeds `R`-linearly into the sections of `(R ⧸ 𝔭)^~` over the punctured
spectrum of `R`. -/
theorem exists_injective_fractionRing_sections_tilde_quotient (R : CommRingCat.{u})
    [IsLocalRing R] {p : Ideal (ToType R)} [p.IsPrime]
    (hdim : ringKrullDim (ToType R ⧸ p) = 1)
    (K : Type u) [CommRing K] [Algebra (ToType R) K] [Algebra (ToType R ⧸ p) K]
    [IsScalarTower (ToType R) (ToType R ⧸ p) K] [IsFractionRing (ToType R ⧸ p) K] :
    ∃ θ : K →ₗ[R] Γ(tilde (ModuleCat.of R (ToType R ⧸ p)), puncturedSpectrum R),
      Function.Injective θ := by
  have : IsLocalRing (ToType (CommRingCat.of (ToType R ⧸ p))) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  obtain ⟨θ₀, hθ₀⟩ := exists_injective_fractionRing_sections_pushforward
    (CommRingCat.ofHom (Ideal.Quotient.mk p) : R ⟶ CommRingCat.of (ToType R ⧸ p))
    Ideal.Quotient.mk_surjective hdim K fun r k => by
      rw [← IsScalarTower.algebraMap_smul (ToType R ⧸ p) r k, Algebra.smul_def, Algebra.smul_def]
      simp [Ideal.Quotient.algebraMap_eq]
  exact ⟨appLinearMap (tildeQuotientIsoPushforward R p).inv (puncturedSpectrum R) ∘ₗ θ₀,
    (injective_appLinearMap_of_isIso (tildeQuotientIsoPushforward R p).inv
      (puncturedSpectrum R)).comp hθ₀⟩

/-- **The local content of [Stacks, Tag 0AWC], with no hypotheses beyond the local algebra.**

For `R` a Noetherian local ring with an associated prime `𝔭` in the Stacks sense such that
`dim(R ⧸ 𝔭) = 1`, the sections of the structure sheaf over the punctured spectrum of `R` are not
a finite `R`-module. -/
theorem not_module_finite_sections_puncturedSpectrum (R : CommRingCat.{u}) [IsNoetherianRing R]
    [IsLocalRing R] {p : Ideal (ToType R)} [p.IsPrime]
    (hp : IsAssociatedPrimeStacks (ToType R) (ToType R) p)
    (hdim : ringKrullDim (ToType R ⧸ p) = 1) :
    ¬ Module.Finite (ToType R) Γ(Spec R, puncturedSpectrum R) := fun _ => by
  obtain ⟨θ, hθ⟩ := exists_injective_fractionRing_sections_tilde_quotient R hdim
    (FractionRing (ToType R ⧸ p))
  exact not_module_finite_sections_puncturedSpectrum_of_injective R hp hdim
    (FractionRing (ToType R ⧸ p)) θ hθ
    (Module.Finite.equiv (sectionsTildeSelfLinearEquiv R (puncturedSpectrum R)).symm)

end Stacks.LocalCohomology

end
