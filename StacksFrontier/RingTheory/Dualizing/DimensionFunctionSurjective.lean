module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.LocalProperties.Injective
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.FiniteDual
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.HomLocalizationSurjective
public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing

/-!
# The dimension function of `RHom_A(B, K)` along a surjection

Let `f : A → B` be a surjection of Noetherian rings, let `K` be a dualizing complex over `A`,
let `q` be a prime of `B` and let `p` be its contraction to `A`. Then `RHom_A(B, K)` is a
dualizing complex over `B`, and the two dimension functions are related by
`δ_{RHom_A(B, K)}(q) = δ_K(p)`.

The content is a compatibility of derived Hom along `f` with localization: the localization at
`q` of `RHom_A(B, K)` is `RHom_{A_p}(B_q, K_p)`, where `g : A_p → B_q` is the surjection of
local rings induced by `f`. Given that, the equality of the two shifts is the uniqueness of the
normalizing shift over `B_q`, because `RHom_{A_p}(B_q, -)` carries a normalized dualizing
complex to a normalized dualizing complex.

The compatibility is proved at the level of modules and then transported. Because `f` is
surjective, the surjection carries the complement of `p` onto the complement of `q`, so `B_q` is
simultaneously the localization of `B` at `q` and the localization of the `A`-module `B` at `p`;
and `B` is a finitely presented `A`-module, so `Hom_A(B, -)` commutes with that localization.
This gives a natural isomorphism of functors `Mod(A) ⥤ Mod(B_q)`

`B_q ⊗_B Hom_A(B, -) ≅ Hom_{A_p}(B_q, A_p ⊗_A -)`,

and applying it degreewise to a bounded complex of injectives representing `K` identifies the
two complexes computing the two derived Homs: the degreewise coextension of scalars is
K-injective on both sides, and the localized terms are again injective.

## Main definitions

* `Dualizing.coextendExtendScalarsIso` — the natural isomorphism
  `B_q ⊗_B Hom_A(B, -) ≅ Hom_{A_p}(B_q, A_p ⊗_A -)` for a surjection `A → B`.
* `Dualizing.betaNat` — the comparison map of `B`-modules whose adjoint transpose that
  isomorphism is.
* `Dualizing.derivedExtensionScalarsModelIso` — derived extension of scalars along a
  localization, computed degreewise on a cochain complex.

## Main results

* `Dualizing.dualizingDimension_derivedHom_of_surjective` — [Stacks, Tag 0A7Y]: for a
  surjection of Noetherian rings the dimension function of `RHom_A(B, K)` is the restriction of
  the dimension function of `K`.
* `Dualizing.isIso_thetaNat_app` — the comparison map is an isomorphism, because both of its
  sides are localizations of `Hom_A(B, -)` at the complement of `p`.
* `Dualizing.injective_extendScalars` — the localization of an injective module over a
  Noetherian ring is injective over the localized ring.

## Implementation notes

The carriers of `ModuleCat.extendScalars` and `ModuleCat.coextendScalars` carry the module
structures their definitions install — the left factor of the tensor product and the source of
the Hom are the restriction-of-scalars objects, whose actions are `Module.compHom` of the actions
upstairs. Those are not the module structures that instance search finds on the corresponding
plain types, so each comparison with a plain type is made by hand: `Dualizing.restrictSelfEquiv`,
`Dualizing.extendCarrierEquiv`, `Dualizing.extendSmulEquiv` and `Dualizing.coextendRestrictEquiv`
are identity maps whose linearity is `Algebra.smul_def` or `Dualizing.coextend_smul_eq`, and
everything downstream is phrased through them. For the same reason the pointwise identities below
are stated at the types that appear in the goals and are chained with `Eq.trans` rather than
rewritten into place.

Everything about the comparison map is derived from one uniqueness statement,
`Dualizing.zEquiv_symm_ext`: an `A_p`-linear map out of `B_q` is determined by its values on the
image of `B`. Its `B`-linearity, its naturality and the identification of its transpose with the
localization map are each a computation on those values.

## References

* [Stacks Project, Tag 0A7Y](https://stacks.math.columbia.edu/tag/0A7Y)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A7N](https://stacks.math.columbia.edu/tag/0A7N)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

section Bridge

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- `B` as an `A`-module by restriction of scalars. -/
abbrev restrictSelf : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)

/-- The identity is an `A`-linear equivalence from `B` to its restriction of scalars. -/
def restrictSelfEquiv : B ≃ₗ[A] ↑(restrictSelf A B) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change a • x = (algebraMap A B a) * x
    rw [Algebra.smul_def]

/-- The identity is a `B`-linear equivalence from `B` to its restriction of scalars along
`A → B`. -/
def restrictSelfEquivTop : B ≃ₗ[B] ↑(restrictSelf A B) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A B}

/-- Restriction of scalars along `A → B` is a tower over `B`. -/
instance isScalarTower_restrictScalars (Z : ModuleCat.{v} B) :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj Z) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

end Bridge

section Carriers

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The base-ring module structure on an extension of scalars: `B ⊗_A M` is an `A`-module by
restricting its `B`-action along `A → B`. -/
instance moduleBaseExtendScalars (M : ModuleCat.{max v u} A) :
    Module A ↑((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  ((ModuleCat.restrictScalars (algebraMap A B)).obj
    ((ModuleCat.extendScalars (algebraMap A B)).obj M)).isModule

/-- The base-ring structure of `Dualizing.moduleBaseExtendScalars` is a tower: `A` acts on
`B ⊗_A M` through `B`. -/
instance isScalarTowerExtendScalars (M : ModuleCat.{max v u} A) :
    IsScalarTower A B ↑((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The carrier of `ModuleCat.extendScalars` along `A → B` is the base change `B ⊗_A M`, with
its `B`-module structure. -/
def extendCarrierEquiv (M : ModuleCat.{max v u} A) :
    TensorProduct A B ↑M ≃ₗ[B] ↑((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  TensorProduct.AlgebraTensorModule.congr (restrictSelfEquivTop A B) (LinearEquiv.refl A ↑M)

/-- The two `A`-module structures on the carrier `B ⊗_A M` of an extension of scalars agree:
the base ring acting on the left factor, and the `B`-action restricted to `A`. The underlying
map is the identity, and the two actions are compared on generators. -/
def extendSmulEquiv (M : ModuleCat.{max v u} A) :
    TensorProduct A ↑(restrictSelf A B) ↑M ≃ₗ[A]
      ↑((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M)) where
  toFun t := t
  invFun t := t
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a t := by
    induction t using TensorProduct.induction_on with
    | zero =>
      have h1 : a • (0 : TensorProduct A ↑(restrictSelf A B) ↑M) = 0 := smul_zero a
      have h2 : a • (0 : ↑((ModuleCat.restrictScalars (algebraMap A B)).obj
          ((ModuleCat.extendScalars (algebraMap A B)).obj M))) = 0 := smul_zero a
      exact h1.trans h2.symm
    | tmul x m => rfl
    | add x y hx hy =>
      have h1 : a • (x + y) = a • x + a • y := smul_add a x y
      have h2 : a • (x + y : ↑((ModuleCat.restrictScalars (algebraMap A B)).obj
            ((ModuleCat.extendScalars (algebraMap A B)).obj M)))
          = a • x + a • y := smul_add a x y
      exact h1.trans ((congrArg₂ (· + ·) hx hy).trans h2.symm)

/-- The carrier of `ModuleCat.extendScalars` along `A → B` is the base change `B ⊗_A M`,
`A`-linearly for the base-ring structure of `Dualizing.moduleBaseExtendScalars`. -/
def extendCarrierEquivBase (M : ModuleCat.{max v u} A) :
    TensorProduct A B ↑M ≃ₗ[A]
      ↑((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M)) :=
  TensorProduct.congr (restrictSelfEquiv A B) (LinearEquiv.refl A ↑M) ≪≫ₗ extendSmulEquiv M

end Carriers

section Coextend

variable {R P T : Type u} [CommRing R] [CommRing P] [CommRing T]
  [Algebra R P] [Algebra P T] [Algebra R T] [IsScalarTower R P T]

/-- On `Hom_P(T, N)` for an `R`-module `N` lying in a tower `R → P → N`, the action of
`algebraMap R T r` by coextension of scalars along `P → T` is the action of `r` on the target.
Both send `h` to `x ↦ r • h x`, the left-hand side because `T` is commutative. -/
theorem coextend_smul_eq {N : Type max v u} [AddCommGroup N] [Module P N] [Module R N]
    [IsScalarTower R P N] (h : ↑(restrictSelf P T) →ₗ[P] N) (r : R) :
    (algebraMap R T r) • h = r • h := by
  refine LinearMap.ext fun x => ?_
  have h2 : (algebraMap R T r) • x = (algebraMap R P r) • x := by
    rw [IsScalarTower.algebraMap_apply R P T]
    exact rfl
  refine Eq.trans (congrArg (⇑h) (@mul_comm T _ x (algebraMap R T r))) ?_
  refine Eq.trans (congrArg (⇑h) h2) ?_
  refine (h.map_smul (algebraMap R P r) x).trans ?_
  exact IsScalarTower.algebraMap_smul P r (h x)

/-- The carrier of the coextension of scalars `Hom_P(T, N)` along `P → T`, with its `T`-action
restricted to `R` along `R → T`, is the module of `P`-linear maps `T → N` with `R` acting on the
target. The underlying map is the identity; `Dualizing.coextend_smul_eq` compares the actions. -/
def coextendRestrictEquiv (N : ModuleCat.{max v u} P) [Module R ↑N] [IsScalarTower R P ↑N] :
    ↑((ModuleCat.restrictScalars (algebraMap R T)).obj
        ((ModuleCat.coextendScalars (algebraMap P T)).obj N)) ≃ₗ[R]
      (↑(restrictSelf P T) →ₗ[P] ↑N) where
  toFun φ := ModuleCat.CoextendScalars.equiv (algebraMap P T) N φ
  invFun ψ := (ModuleCat.CoextendScalars.equiv (algebraMap P T) N).symm ψ
  left_inv φ := (ModuleCat.CoextendScalars.equiv (algebraMap P T) N).symm_apply_apply φ
  right_inv ψ := (ModuleCat.CoextendScalars.equiv (algebraMap P T) N).apply_symm_apply ψ
  map_add' φ₁ φ₂ := map_add (ModuleCat.CoextendScalars.equiv (algebraMap P T) N) φ₁ φ₂
  map_smul' r φ :=
    (map_smul (ModuleCat.CoextendScalars.equiv (algebraMap P T) N) (algebraMap R T r) φ).trans
      (coextend_smul_eq _ r)

end Coextend

section Carriers2

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The carrier of the coextension `Hom_A(B, M)` along `A → B`, with its `B`-action restricted
back to `A`, is the module `B →ₗ[A] M` of `A`-linear maps with `A` acting on the target. -/
def coextendCarrierEquiv (M : ModuleCat.{max v u} A) :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((ModuleCat.coextendScalars (algebraMap A B)).obj M)) ≃ₗ[A] (B →ₗ[A] ↑M) :=
  coextendRestrictEquiv M ≪≫ₗ
    (LinearEquiv.arrowCongr (restrictSelfEquiv A B) (LinearEquiv.refl A ↑M)).symm

end Carriers2

section ZSide

variable {A Ap Bq : Type u} [CommRing A] [CommRing Ap] [CommRing Bq]
  [Algebra A Ap] [Algebra Ap Bq] [Algebra A Bq] [IsScalarTower A Ap Bq]

/-- The module `Hom_{Ap}(Bq, Ap ⊗_A M)` is the carrier of the coextension along `Ap → Bq` of the
extension of scalars of `M` along `A → Ap`, `A`-linearly for the `Bq`-action restricted to `A`. -/
def zEquiv (M : ModuleCat.{max v u} A) :
    (Bq →ₗ[Ap] TensorProduct A Ap ↑M) ≃ₗ[A]
      ↑((ModuleCat.restrictScalars (algebraMap A Bq)).obj
        ((ModuleCat.coextendScalars (algebraMap Ap Bq)).obj
          ((ModuleCat.extendScalars (algebraMap A Ap)).obj M))) :=
  (LinearEquiv.restrictScalars A
      (LinearEquiv.arrowCongr (restrictSelfEquiv Ap Bq) (extendCarrierEquiv M))) ≪≫ₗ
    (coextendRestrictEquiv ((ModuleCat.extendScalars (algebraMap A Ap)).obj M)).symm

end ZSide

section Comparison

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
  (Ap Bq : Type u) [CommRing Ap] [CommRing Bq] [Algebra A Ap] [Algebra B Bq] [Algebra A Bq]
  [Algebra Ap Bq] [IsScalarTower A B Bq] [IsScalarTower A Ap Bq]
  (hf : Function.Surjective (algebraMap A B)) (q : PrimeSpectrum B)
  [IsLocalization (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl Ap]
  [IsLocalization q.asIdeal.primeCompl Bq]

/-- A choice of the comparison isomorphism
`Ap ⊗_A Hom_A(B, M) ≅ Hom_{Ap}(Bq, Ap ⊗_A M)` of
`Dualizing.exists_linearEquiv_hom_localization_of_surjective`, for a surjection `A → B` of
commutative rings with `A` Noetherian. -/
def homLocalizationEquiv (M : ModuleCat.{max v u} A) :
    TensorProduct A Ap (B →ₗ[A] ↑M) ≃ₗ[A] (Bq →ₗ[Ap] TensorProduct A Ap ↑M) :=
  (exists_linearEquiv_hom_localization_of_surjective hf q Ap Bq ↑M).choose

/-- The comparison map `Hom_A(B, M) ⟶ Hom_{Ap}(Bq, Ap ⊗_A M)`: the localization map
`φ ↦ 1 ⊗ φ` followed by `Dualizing.homLocalizationEquiv`. It carries `φ` to the unique
`Ap`-linear map taking the image of `b` to `1 ⊗ φ b`. -/
def betaNice (M : ModuleCat.{max v u} A) :
    (B →ₗ[A] ↑M) →ₗ[A] (Bq →ₗ[Ap] TensorProduct A Ap ↑M) :=
  (homLocalizationEquiv Ap Bq hf q M).toLinearMap ∘ₗ TensorProduct.mk A Ap (B →ₗ[A] ↑M) 1

/-- The defining formula for `Dualizing.betaNice`: it sends `φ` to the `Ap`-linear map whose
value at the image of `b` in `Bq` is `1 ⊗ φ b`. -/
theorem betaNice_apply (M : ModuleCat.{max v u} A) (φ : B →ₗ[A] ↑M) (b : B) :
    betaNice Ap Bq hf q M φ (algebraMap B Bq b) = (1 : Ap) ⊗ₜ[A] φ b :=
  (exists_linearEquiv_hom_localization_of_surjective hf q Ap Bq ↑M).choose_spec φ b

/-- `Dualizing.betaNice` exhibits `Hom_{Ap}(Bq, Ap ⊗_A M)` as the localization of
`Hom_A(B, M)` at the complement of the contracted prime. -/
theorem isLocalizedModule_betaNice (M : ModuleCat.{max v u} A) :
    IsLocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
      (betaNice Ap Bq hf q M) :=
  IsLocalizedModule.of_linearEquiv _ (TensorProduct.mk A Ap (B →ₗ[A] ↑M) 1)
    (homLocalizationEquiv Ap Bq hf q M)

end Comparison

section BqLinear

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (Bq : Type u) [CommRing Bq] [Algebra B Bq] [Algebra A Bq] [IsScalarTower A B Bq]

/-- The localization map `B → Bq`, read as a map of `A`-modules. -/
def bqLinear : B →ₗ[A] Bq := (Algebra.linearMap B Bq).restrictScalars A

/-- For a surjection `A → B`, the localization map `B → Bq` exhibits `Bq` as the localization
of the `A`-module `B` at the complement of the contracted prime: the surjection carries that
complement onto the complement of `q`. -/
theorem isLocalizedModule_bqLinear (hf : Function.Surjective (algebraMap A B))
    (q : PrimeSpectrum B) [IsLocalization q.asIdeal.primeCompl Bq] :
    IsLocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
      (bqLinear (A := A) (B := B) Bq) := by
  have hS := isLocalization_algebraMapSubmonoid_primeCompl hf q Bq
  exact IsLocalizedModule.restrictScalars _ (Algebra.linearMap B Bq)

end BqLinear

section Pointwise

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (Ap Bq : Type u) [CommRing Ap] [CommRing Bq] [Algebra A Ap] [Algebra B Bq] [Algebra A Bq]
  [Algebra Ap Bq] [IsScalarTower A B Bq] [IsScalarTower A Ap Bq]

/-- Two elements of `Hom_{Ap}(Bq, Ap ⊗_A M)` agreeing on the image of `B` are equal, because
`Bq` is the localization of the `A`-module `B` and the target is an `Ap`-module. This is the
uniqueness statement that pins every map constructed below. -/
theorem zEquiv_symm_ext [IsNoetherianRing A] (hf : Function.Surjective (algebraMap A B))
    (q : PrimeSpectrum B)
    [IsLocalization (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl Ap]
    [IsLocalization q.asIdeal.primeCompl Bq] (M : ModuleCat.{max v u} A)
    {χ₁ χ₂ : ↑((ModuleCat.restrictScalars (algebraMap A Bq)).obj
      ((ModuleCat.coextendScalars (algebraMap Ap Bq)).obj
        ((ModuleCat.extendScalars (algebraMap A Ap)).obj M)))}
    (h : ∀ b : B, (zEquiv M).symm χ₁ (algebraMap B Bq b)
      = (zEquiv M).symm χ₂ (algebraMap B Bq b)) :
    χ₁ = χ₂ := by
  have hL := isLocalizedModule_bqLinear (A := A) (B := B) Bq hf q
  refine (zEquiv M).symm.injective (LinearMap.restrictScalars_injective A ?_)
  exact IsLocalizedModule.ext (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
    (bqLinear (A := A) (B := B) Bq)
    (fun x => IsLocalizedModule.map_units (TensorProduct.mk A Ap ↑M 1) x) (LinearMap.ext h)

/-- Scalars pass from the coextension action to the argument: the value of `c • χ` at `y` is
the value of `χ` at `y * c`. -/
theorem zEquiv_symm_smul (M : ModuleCat.{max v u} A)
    (χ : ↑((ModuleCat.restrictScalars (algebraMap A Bq)).obj
      ((ModuleCat.coextendScalars (algebraMap Ap Bq)).obj
        ((ModuleCat.extendScalars (algebraMap A Ap)).obj M)))) (c y : Bq) :
    (zEquiv M).symm (c • χ) y = (zEquiv M).symm χ (y * c) := rfl

/-- The coextension action on `Hom_A(B, M)` reindexes the argument: the value of `b • φ` at `b'`
is the value of `φ` at `b' * b`. -/
theorem coextendCarrierEquiv_smul (M : ModuleCat.{max v u} A)
    (φ : ↑((ModuleCat.coextendScalars (algebraMap A B)).obj M)) (b b' : B) :
    coextendCarrierEquiv M (b • φ) b' = coextendCarrierEquiv M φ (b' * b) := rfl

/-- Coextension of scalars acts on `Hom_A(B, M)` by postcomposition. -/
theorem coextendCarrierEquiv_map {M M' : ModuleCat.{max v u} A} (ξ : M ⟶ M')
    (φ : ↑((ModuleCat.coextendScalars (algebraMap A B)).obj M)) (b : B) :
    coextendCarrierEquiv M' ((ModuleCat.coextendScalars (algebraMap A B)).map ξ φ) b
      = ξ.hom (coextendCarrierEquiv M φ b) := rfl

/-- Extension of scalars acts on the base change `Ap ⊗_A M` as the base change of the map. -/
theorem extendCarrierEquiv_baseChange {M M' : ModuleCat.{max v u} A} (ξ : M ⟶ M')
    (s : TensorProduct A Ap ↑M) :
    (ModuleCat.extendScalars (algebraMap A Ap)).map ξ (extendCarrierEquiv M s)
      = extendCarrierEquiv M' (LinearMap.baseChange Ap ξ.hom s) := by
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul p m => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- Coextension of scalars along `Ap → Bq` of a base-changed map acts on
`Hom_{Ap}(Bq, Ap ⊗_A M)` by postcomposition with that base change. -/
theorem zEquiv_symm_coextendMap {M M' : ModuleCat.{max v u} A} (ξ : M ⟶ M')
    (χ : ↑((ModuleCat.restrictScalars (algebraMap A Bq)).obj
      ((ModuleCat.coextendScalars (algebraMap Ap Bq)).obj
        ((ModuleCat.extendScalars (algebraMap A Ap)).obj M)))) (y : Bq) :
    (zEquiv M').symm ((ModuleCat.coextendScalars (algebraMap Ap Bq)).map
        ((ModuleCat.extendScalars (algebraMap A Ap)).map ξ) χ) y
      = LinearMap.baseChange Ap ξ.hom ((zEquiv M).symm χ y) := by
  have hkey := extendCarrierEquiv_baseChange Ap ξ ((extendCarrierEquiv M).symm
    (ModuleCat.CoextendScalars.equiv (algebraMap Ap Bq)
      ((ModuleCat.extendScalars (algebraMap A Ap)).obj M) χ (restrictSelfEquiv Ap Bq y)))
  rw [LinearEquiv.apply_symm_apply] at hkey
  show (extendCarrierEquiv M').symm ((ModuleCat.extendScalars (algebraMap A Ap)).map ξ
    (ModuleCat.CoextendScalars.equiv (algebraMap Ap Bq) _ χ (restrictSelfEquiv Ap Bq y))) = _
  rw [hkey, LinearEquiv.symm_apply_apply]
  exact rfl

end Pointwise

section UnitBase

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (Bq : Type u) [CommRing Bq] [Algebra B Bq] [Algebra A Bq] [IsScalarTower A B Bq]
  (hf : Function.Surjective (algebraMap A B)) (q : PrimeSpectrum B)
  [IsLocalization q.asIdeal.primeCompl Bq]

/-- The localization map `Hom_A(B, M) ⟶ Bq ⊗_B Hom_A(B, M)`, read as a map of `A`-modules: the
unit of the extension–restriction adjunction along `B → Bq`, restricted to `A`. -/
def unitBase (M : ModuleCat.{max v u} A) :
    (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A B)).obj
        ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M) ⟶
      (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A Bq)).obj
        ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq)).obj
          ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)) :=
  (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A B)).map
      ((ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} (algebraMap B Bq)).unit.app
        ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)) ≫
    (ModuleCat.restrictScalarsComp'App (algebraMap A B) (algebraMap B Bq) (algebraMap A Bq)
      (IsScalarTower.algebraMap_eq A B Bq) _).inv

include hf in
/-- `Dualizing.unitBase` exhibits `Bq ⊗_B Hom_A(B, M)` as the localization of the `A`-module
`Hom_A(B, M)` at the complement of the contracted prime: it is the localization of the
`B`-module `Hom_A(B, M)` at the image of that complement, which is the complement of `q`. -/
theorem isLocalizedModule_unitBase (M : ModuleCat.{max v u} A) :
    IsLocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
      (unitBase (B := B) Bq M).hom := by
  have hS := isLocalization_algebraMapSubmonoid_primeCompl hf q Bq
  let uAsc : ↑((ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A B)).obj
        ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)) →ₗ[B]
      ↑((ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A B)).obj
        ((ModuleCat.restrictScalars.{max v u, u, u} (algebraMap B Bq)).obj
          ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq)).obj
            ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)))) :=
    ((ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} (algebraMap B Bq)).unit.app
      ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)).hom
  have heq : (extendCarrierEquivBase (A := B) (B := Bq)
        ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)).toLinearMap ∘ₗ
      TensorProduct.mk B Bq
        ↑((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M) 1
      = uAsc :=
    LinearMap.ext fun _ => rfl
  have h1 : IsLocalizedModule (Algebra.algebraMapSubmonoid B
      (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl) uAsc := by
    have hmk : IsLocalizedModule (Algebra.algebraMapSubmonoid B
        (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl)
        (TensorProduct.mk B Bq
          ↑((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M) 1) :=
      IsLocalization.tensorProduct_isLocalizedModule _ Bq
    rw [← heq]
    exact IsLocalizedModule.of_linearEquiv _ _ _ (hf := hmk)
  exact IsLocalizedModule.of_linearEquiv _ (uAsc.restrictScalars A)
    ((ModuleCat.restrictScalarsComp'App (algebraMap A B) (algebraMap B Bq) (algebraMap A Bq)
      (IsScalarTower.algebraMap_eq A B Bq)
      ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq)).obj
        ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M))).symm.toLinearEquiv)
    (hf := IsLocalizedModule.restrictScalars _ uAsc)

end UnitBase

section Theta

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
  (Ap Bq : Type u) [CommRing Ap] [CommRing Bq] [Algebra A Ap] [Algebra B Bq] [Algebra A Bq]
  [Algebra Ap Bq] [IsScalarTower A B Bq] [IsScalarTower A Ap Bq]
  (hf : Function.Surjective (algebraMap A B)) (q : PrimeSpectrum B)
  [IsLocalization (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl Ap]
  [IsLocalization q.asIdeal.primeCompl Bq]

/-- The comparison map of `Dualizing.betaNice`, transported to the carriers of the two
change-of-rings functors and read as a map of `A`-modules. -/
def betaBase (M : ModuleCat.{max v u} A) :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((ModuleCat.coextendScalars (algebraMap A B)).obj M)) →ₗ[A]
      ↑((ModuleCat.restrictScalars (algebraMap A Bq)).obj
        ((ModuleCat.coextendScalars (algebraMap Ap Bq)).obj
          ((ModuleCat.extendScalars (algebraMap A Ap)).obj M))) :=
  (zEquiv M).toLinearMap ∘ₗ betaNice Ap Bq hf q M ∘ₗ (coextendCarrierEquiv M).toLinearMap

/-- The defining formula for `Dualizing.betaBase`: its value at `φ`, evaluated at the image of
`b` in `Bq`, is `1 ⊗ φ b`. -/
theorem betaBase_apply (M : ModuleCat.{max v u} A)
    (φ : ↑((ModuleCat.coextendScalars (algebraMap A B)).obj M)) (b : B) :
    (zEquiv M).symm (betaBase Ap Bq hf q M φ) (algebraMap B Bq b)
      = (1 : Ap) ⊗ₜ[A] coextendCarrierEquiv M φ b := by
  have hz : (zEquiv M).symm (betaBase Ap Bq hf q M φ)
      = betaNice Ap Bq hf q M (coextendCarrierEquiv M φ) :=
    (zEquiv M).symm_apply_apply _
  rw [hz, betaNice_apply]

/-- `Dualizing.betaBase` is a localization map at the complement of the contracted prime. -/
theorem isLocalizedModule_betaBase (M : ModuleCat.{max v u} A) :
    IsLocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
      (betaBase Ap Bq hf q M) := by
  have h1 := isLocalizedModule_betaNice Ap Bq hf q M
  have h2 : IsLocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
      (betaNice Ap Bq hf q M ∘ₗ (coextendCarrierEquiv M).toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ (coextendCarrierEquiv M)
  exact IsLocalizedModule.of_linearEquiv _ _ (zEquiv M)

/-- The comparison map of `Dualizing.betaBase` as a morphism of `B`-modules
`Hom_A(B, M) ⟶ Hom_{Ap}(Bq, Ap ⊗_A M)`. Its `B`-linearity is the identity
`β(b • φ)(y) = β(φ)(y · b)`, checked on the image of `B` in `Bq`. -/
def betaApp (M : ModuleCat.{max v u} A) :
    (ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M ⟶
      (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap B Bq)).obj
        ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq)).obj
          ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap)).obj M)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)
    (Y := (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap B Bq)).obj
      ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq)).obj
        ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap)).obj M)))
    { toFun := fun φ => betaBase Ap Bq hf q M φ
      map_add' := fun φ₁ φ₂ => map_add (betaBase Ap Bq hf q M) φ₁ φ₂
      map_smul' := fun b φ => by
        refine zEquiv_symm_ext Ap Bq hf q M fun b' => ?_
        have e1 := betaBase_apply Ap Bq hf q M (b • φ) b'
        have e2 := coextendCarrierEquiv_smul M φ b b'
        have e3 := betaBase_apply Ap Bq hf q M φ (b' * b)
        have e4 := zEquiv_symm_smul Ap Bq M (betaBase Ap Bq hf q M φ)
          (algebraMap B Bq b) (algebraMap B Bq b')
        exact e1.trans ((congrArg (fun t => (1 : Ap) ⊗ₜ[A] t) e2).trans
          (e3.symm.trans ((congrArg (fun y => (zEquiv M).symm (betaBase Ap Bq hf q M φ) y)
            (map_mul (algebraMap B Bq) b' b)).trans e4.symm))) }

/-- `Dualizing.betaApp` is natural in the module: both sides of the naturality square are
determined by their values on the image of `B` in `Bq`, where each is `1 ⊗ ξ (φ b)`. -/
def betaNat :
    ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B) ⟶
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap) ⋙
          ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq)) ⋙
        ModuleCat.restrictScalars.{max v u, u, u} (algebraMap B Bq) where
  app M := betaApp Ap Bq hf q M
  naturality M M' ξ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    refine zEquiv_symm_ext Ap Bq hf q M' fun b => ?_
    have e1 := betaBase_apply Ap Bq hf q M'
      ((ModuleCat.coextendScalars (algebraMap A B)).map ξ φ) b
    have e2 := coextendCarrierEquiv_map ξ φ b
    have e3 := betaBase_apply Ap Bq hf q M φ b
    have e4 := zEquiv_symm_coextendMap Ap Bq ξ (betaBase Ap Bq hf q M φ) (algebraMap B Bq b)
    have e5 := LinearMap.baseChange_tmul (ModuleCat.Hom.hom ξ) (1 : Ap)
      (coextendCarrierEquiv M φ b)
    exact e1.trans ((congrArg (fun t => (1 : Ap) ⊗ₜ[A] t) e2).trans
      (e5.symm.trans ((congrArg (fun t => LinearMap.baseChange Ap (ModuleCat.Hom.hom ξ) t)
        e3.symm).trans e4.symm)))

/-- The comparison natural transformation
`Bq ⊗_B Hom_A(B, -) ⟶ Hom_{Ap}(Bq, Ap ⊗_A -)`,
the transpose of `Dualizing.betaNat` under the extension–restriction adjunction along
`B → Bq`. -/
def thetaNat :
    ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B) ⋙
        ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq) ⟶
      ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap) ⋙
        ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq) :=
  Functor.whiskerRight (betaNat Ap Bq hf q)
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq)) ≫
    Functor.whiskerLeft (ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap) ⋙
        ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq))
      (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} (algebraMap B Bq)).counit

/-- `Dualizing.thetaNat` is, at each module, the transpose of `Dualizing.betaApp`: extension of
scalars applied to it, followed by the counit. -/
theorem thetaNat_app_eq (M : ModuleCat.{max v u} A) :
    (thetaNat Ap Bq hf q).app M
      = (ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq)).map
          (betaApp Ap Bq hf q M) ≫
        (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} (algebraMap B Bq)).counit.app
          ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq)).obj
            ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap)).obj M)) :=
  rfl

/-- The transposition identity: the unit of the adjunction followed by the restriction of
`Dualizing.thetaNat` is `Dualizing.betaApp`. -/
theorem unit_comp_thetaNat (M : ModuleCat.{max v u} A) :
    (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} (algebraMap B Bq)).unit.app
        ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M) ≫
      (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap B Bq)).map
        ((thetaNat Ap Bq hf q).app M)
      = betaApp Ap Bq hf q M := by
  have h1 := ((ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} (algebraMap B Bq)).homEquiv
    ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B)).obj M)
    ((ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq)).obj
      ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap)).obj M))).apply_symm_apply
        (betaApp Ap Bq hf q M)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h1
  rw [thetaNat_app_eq]
  exact h1

/-- Reading the transposition identity on underlying maps of `A`-modules: the localization map
`Dualizing.unitBase` followed by `Dualizing.thetaNat` is `Dualizing.betaBase`. -/
theorem unitBase_comp (M : ModuleCat.{max v u} A) :
    (unitBase (B := B) Bq M ≫ (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A Bq)).map
        ((thetaNat Ap Bq hf q).app M)).hom = betaBase Ap Bq hf q M := by
  refine LinearMap.ext fun φ => ?_
  have h2 := LinearMap.congr_fun
    (ModuleCat.hom_ext_iff.mp (unit_comp_thetaNat Ap Bq hf q M)) φ
  exact h2

/-- Every component of `Dualizing.thetaNat` is an isomorphism. Both `Dualizing.unitBase` and
its composite with the component are localization maps of the same `A`-module at the same
multiplicative set, so the component becomes invertible after restriction of scalars to `A`,
and restriction of scalars reflects isomorphisms. -/
theorem isIso_thetaNat_app (M : ModuleCat.{max v u} A) :
    IsIso ((thetaNat Ap Bq hf q).app M) := by
  have h1 : IsLocalizedModule (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
      ((unitBase (B := B) Bq M ≫ (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A Bq)).map
        ((thetaNat Ap Bq hf q).app M)).hom) := by
    rw [unitBase_comp]
    exact isLocalizedModule_betaBase Ap Bq hf q M
  have h2 : IsIso ((ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A Bq)).map
      ((thetaNat Ap Bq hf q).app M)) :=
    ModuleCat.isIso_of_isLocalizedModule_comp (isLocalizedModule_unitBase (B := B) Bq hf q M) h1
  exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars.{max v u, u, u} (algebraMap A Bq))

/-- **Coextension of scalars along a surjection commutes with localization.** For a surjection
`A → B` of commutative rings with `A` Noetherian, a prime `q` of `B` with contraction `p`, and
localizations `Ap` of `A` at `p` and `Bq` of `B` at `q`, there is a natural isomorphism of
functors `Mod(A) ⥤ Mod(Bq)`

`Bq ⊗_B Hom_A(B, -) ≅ Hom_{Ap}(Bq, Ap ⊗_A -)`.

The map is the transpose of the comparison
`Dualizing.betaApp`, and it is an isomorphism because both of its sides are localizations of
`Hom_A(B, -)` at the complement of `p`. -/
def coextendExtendScalarsIso :
    ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B) ⋙
        ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq) ≅
      ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap) ⋙
        ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq) := by
  have h : ∀ M, IsIso ((thetaNat Ap Bq hf q).app M) :=
    fun M => isIso_thetaNat_app Ap Bq hf q M
  have : IsIso (thetaNat Ap Bq hf q) := NatIso.isIso_of_isIso_app _
  exact asIso (thetaNat Ap Bq hf q)

end Theta

section Model

open CategoryTheory.Limits

/-- A universe lift of modules that does not change the universe induces the identity on the
derived category: on cochain complexes it is degreewise `ULift.moduleEquiv`, and
`Functor.mapDerivedCategory` is determined by its factorisation through `DerivedCategory.Q`. -/
noncomputable def uliftSelfIso (R : Type u) [CommRing R] :
    (ModuleCat.uliftFunctor.{u, max v u} R).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{max v u} R)) := by
  let U := ModuleCat.uliftFunctor.{u, max v u} R
  let Uc := U.mapHomologicalComplex (ComplexShape.up ℤ)
  let ηc : Uc ≅ 𝟭 (CochainComplex (ModuleCat.{max v u} R) ℤ) :=
    NatIso.ofComponents (fun K =>
      HomologicalComplex.Hom.isoOfComponents
        (fun _ => ULift.moduleEquiv.toModuleIso)
        (by intro i j hij; rfl)) (by
      intro K L f
      ext i x
      rfl)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ U.mapDerivedCategory) (DerivedCategory.Q ⋙ 𝟭 _)
    U.mapDerivedCategory (𝟭 _)
    (U.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight ηc DerivedCategory.Q ≪≫ Functor.leftUnitor _)

section Localized

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A)
  [IsLocalization S B]

include S in
/-- For a localization `A → B` the comparison from derived to degreewise extension of scalars
is an isomorphism at every cochain complex: a localization is flat, so degreewise extension of
scalars preserves homology, hence inverts quasi-isomorphisms, and a left derived functor of a
functor inverting the relevant morphisms agrees with it. -/
theorem comparison_isIso_of_isLocalization
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, max v u}
      (algebraMap A B)).comparison.app J) := by
  have hflat : (algebraMap A B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)
  let F := CochainComplex.DerivedTensor.extensionScalars.{u, u, max v u} (algebraMap A B)
  have : F.PreservesHomology :=
    CochainComplex.DerivedTensor.extensionScalars_preservesHomology.{u, u, max v u}
      (algebraMap A B) hflat
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, max v u}
    (algebraMap A B)
  have : IsIso D.comparison := by
    apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts D.functor D.comparison
      (W := HomologicalComplex.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))
    intro X Y g hg
    have : QuasiIso g := hg
    show IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g))
    infer_instance
  infer_instance

include S in
/-- At a localization `A → B`, derived extension of scalars is computed degreewise: the value
at the class of a cochain complex `J` is the class of the degreewise extension of scalars of
`J`. The universe lift inside `StacksDraft.PseudoCoherence.derivedExtensionScalars` is the
identity here, since the two rings and the module carrier share a universe. -/
noncomputable def derivedExtensionScalarsModelIso
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj
        ((DerivedCategory.Q (C := ModuleCat.{max v u} A)).obj J) ≅
      (DerivedCategory.Q (C := ModuleCat.{max v u} B)).obj
        (((ModuleCat.extendScalars.{u, u, max v u} (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J) := by
  have h := comparison_isIso_of_isLocalization (B := B) S J
  unfold StacksDraft.PseudoCoherence.derivedExtensionScalars
  refine Iso.trans ?_ (@asIso _ _ _ _
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, max v u}
      (algebraMap A B)).comparison.app J) h)
  exact (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, max v u}
      (algebraMap A B)).functor.mapIso
    ((uliftSelfIso.{u, v} A).app ((DerivedCategory.Q (C := ModuleCat.{max v u} A)).obj J))

include S in
/-- The localization of an injective module over a Noetherian ring is injective over the
localized ring: `B ⊗_A M` is the localization of `M`, and localizations of injective modules
over a Noetherian ring are injective. -/
theorem injective_extendScalars [IsNoetherianRing A] (M : ModuleCat.{max v u} A)
    [Injective M] :
    Injective ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap A B)).obj M) := by
  have hMinj : Module.Injective A ↑M :=
    (Module.injective_iff_injective_object A ↑M).mpr inferInstance
  have hloc : IsLocalizedModule S (TensorProduct.mk A B ↑M 1) :=
    IsLocalization.tensorProduct_isLocalizedModule S B
  have hT : Module.Injective B (TensorProduct A B ↑M) :=
    Module.injective_of_isLocalizedModule S (TensorProduct.mk A B ↑M 1)
  have hobj : Injective (ModuleCat.of B (TensorProduct A B ↑M)) :=
    (Module.injective_iff_injective_object B (TensorProduct A B ↑M)).mp hT
  exact Injective.of_iso (extendCarrierEquiv M).toModuleIso hobj

end Localized

end Model

section Main

open CategoryTheory.Limits

variable {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Stacks 0A7Y.** For a surjection `f : A → B` of Noetherian rings and a dualizing complex
`K` over `A`, the dimension function of the dualizing complex `RHom_A(B, K)` over `B` is the
restriction of the dimension function of `K` along the induced closed immersion
`Spec B → Spec A`.

The hypothesis of
`Dualizing.dualizingDimension_derivedHom_of_surjective_of_localizationComparison` is discharged
here: the localization at `q` of `RHom_A(B, K)` is `RHom_{A_p}(B_q, K_p)`, where `g : A_p → B_q`
is the surjection of local rings induced by `f`. Both sides are computed by one and the same
complex of `B_q`-modules, namely the degreewise localization of the degreewise coextension of
scalars of a bounded complex of injectives representing `K`; the identification of the two
complexes is `Dualizing.coextendExtendScalarsIso`. -/
@[stacks 0A7Y]
theorem dualizingDimension_derivedHom_of_surjective
    (f : A →+* B) (hf : Function.Surjective f)
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (q : PrimeSpectrum B) :
    dualizingDimension.{u, v} ((derivedHom.{u, v} f).obj K) q
      = dualizingDimension.{u, v} K (PrimeSpectrum.comap f q) := by
  let Ap := Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  let instAB : Algebra A B := f.toAlgebra
  have hfA : Function.Surjective (algebraMap A B) := hf
  have hApLoc : IsLocalization
      (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl Ap :=
    Localization.isLocalization
  have hmap : Submonoid.map f (PrimeSpectrum.comap f q).asIdeal.primeCompl
      = q.asIdeal.primeCompl := map_primeCompl_comap_of_surjective hfA q
  have hmapLoc : IsLocalization
      (Submonoid.map f (PrimeSpectrum.comap f q).asIdeal.primeCompl) Bq := by
    rw [hmap]
    infer_instance
  let g : Ap →+* Bq := IsLocalization.map Bq f
    (M := (PrimeSpectrum.comap f q).asIdeal.primeCompl)
    (T := Submonoid.map f (PrimeSpectrum.comap f q).asIdeal.primeCompl)
    (Submonoid.le_comap_map _)
  have hg : Function.Surjective g :=
    IsLocalization.map_surjective_of_surjective _ _ _ hf
  let instABq : Algebra A Bq := ((algebraMap B Bq).comp f).toAlgebra
  let instApBq : Algebra Ap Bq := g.toAlgebra
  have twr1 : @IsScalarTower A B Bq (@Algebra.toSMul A B _ _ instAB)
      (@Algebra.toSMul B Bq _ _ _) (@Algebra.toSMul A Bq _ _ instABq) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have twr2 : @IsScalarTower A Ap Bq (@Algebra.toSMul A Ap _ _ _)
      (@Algebra.toSMul Ap Bq _ _ instApBq) (@Algebra.toSMul A Bq _ _ instABq) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (RingHom.congr_fun
        (IsLocalization.map_comp (M := (PrimeSpectrum.comap f q).asIdeal.primeCompl)
          (S := Ap) (Q := Bq)
          (T := Submonoid.map f (PrimeSpectrum.comap f q).asIdeal.primeCompl)
          (Submonoid.le_comap_map _)) x).symm
  obtain ⟨a, b, I, hGE, hLE, hIinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
  have hIGE : I.IsStrictlyGE a := hGE
  have hIinjInst : ∀ n, Injective (I.X n) := hIinj
  have hIK : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let IAp : CochainComplex (ModuleCat.{max v u} Ap) ℤ :=
    ((ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
  have hIApGE : IAp.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff IAp a).2 fun i hi =>
    Functor.map_isZero (ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap))
      ((CochainComplex.isStrictlyGE_iff I a).1 hGE i hi)
  have hIApInj : ∀ n, Injective (IAp.X n) := fun n =>
    injective_extendScalars (B := Ap)
      (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl (I.X n)
  have hIApK : IAp.IsKInjective := CochainComplex.isKInjective_of_injective IAp a
  let ecomplex :=
    (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.coextendScalars.{u, u, max v u} (algebraMap A B) ⋙
          ModuleCat.extendScalars.{u, u, max v u} (algebraMap B Bq)))
        (ComplexShape.up ℤ)).app I ≪≫
      (NatIso.mapHomologicalComplex (coextendExtendScalarsIso.{u, v} Ap Bq hfA q)
        (ComplexShape.up ℤ)).app I ≪≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.extendScalars.{u, u, max v u} (algebraMap A Ap) ⋙
          ModuleCat.coextendScalars.{u, u, max v u} (algebraMap Ap Bq)))
        (ComplexShape.up ℤ)).app I).symm
  refine dualizingDimension_derivedHom_of_surjective_of_localizationComparison.{u, v}
    f hf K hK q g hg ⟨?_⟩
  exact (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap B Bq)).mapIso
      ((derivedHom.{u, v} f).mapIso eI ≪≫ derivedHomObjIsoCoextend.{u, v} f I hIK) ≪≫
    derivedExtensionScalarsModelIso (B := Bq) q.asIdeal.primeCompl
      ((coextendComplex.{u, u, v} f).obj I) ≪≫
    DerivedCategory.Q.mapIso ecomplex ≪≫
    (derivedHomObjIsoCoextend.{u, v} g IAp hIApK).symm ≪≫
    (derivedHom.{u, v} g).mapIso
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A Ap)).mapIso eI ≪≫
        derivedExtensionScalarsModelIso (B := Ap)
          (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl I).symm

end Main

end Dualizing

end
