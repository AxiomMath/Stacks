module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.Localization.BaseChange

@[expose] public section

/-!
# The décalage functor: the submodule substrate

Let `A` be a commutative ring, `S ⊆ A` a multiplicative submonoid and `u` a unit of the
localization `Localization S`.  For an `A`-linear map `d : M → N` the *décalage* of `d`
with respect to `u` is the `ℤ`-indexed family of submodules of `LocalizedModule S M`

`(η_u)^i = { x ∈ u ^ i • P | d x ∈ u ^ (i + 1) • Q }`,

where `P ⊆ LocalizedModule S M` and `Q ⊆ LocalizedModule S N` are given submodules and `d`
is extended to the localizations by `LocalizedModule.map`.  Taking `S = Submonoid.powers f`,
`u` the unit of `Localization S` given by `f`, and `P`, `Q` the images of `M`, `N` recovers
the classical `η_f`; keeping `u`, `P` and `Q` arbitrary is what allows `η` to be iterated.

## Main definitions

* `Eta.locMap`: an `A`-linear map extended to the localizations, as an `A`-linear map.
* `Eta.zpowEquiv`: the `A`-linear automorphism `x ↦ u ^ i • x` of `LocalizedModule S M`.
* `Eta.zsmulSub`: the submodule `u ^ i • N` of `LocalizedModule S M`.
* `Eta.etaTerm`: the degree-`i` term of the décalage.

## Main results

* `Eta.zsmulSub_zsmulSub`, `Eta.zsmulSub_inf`, `Eta.zsmulSub_comap`: scaling by a unit power
  is multiplicative in the unit and commutes with intersections and with taking preimages
  along a localized map.  Together with `Eta.mem_zsmulSub` these reduce identities between
  iterated décalages to lattice manipulations.
* `Eta.locMap_etaTerm_mem`: the décalage of a composable pair of maps is a subcomplex.
-/

namespace Eta

variable {A : Type*} [CommRing A] (S : Submonoid A)

/-! ## Localized maps -/

/-- `d` extended to the localizations, as an `A`-linear map. -/
noncomputable def locMap {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) :
    LocalizedModule S M →ₗ[A] LocalizedModule S N :=
  (LocalizedModule.map S d).restrictScalars A

variable {M N K : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup K] [Module A K]

/-- `locMap` commutes with the `Localization S`-action. -/
theorem locMap_smul (d : M →ₗ[A] N) (c : Localization S) (x : LocalizedModule S M) :
    locMap S d (c • x) = c • locMap S d x :=
  map_smul (LocalizedModule.map S d) c x

/-- `locMap` commutes with the action of the units of `Localization S`. -/
theorem locMap_units_smul (d : M →ₗ[A] N) (w : (Localization S)ˣ) (x : LocalizedModule S M) :
    locMap S d (w • x) = w • locMap S d x :=
  locMap_smul S d (w : Localization S) x

/-- `locMap` on the localization of an element is the localization of its image. -/
theorem locMap_mk (d : M →ₗ[A] N) (m : M) (s : S) :
    locMap S d (LocalizedModule.mk m s) = LocalizedModule.mk (d m) s :=
  LocalizedModule.map_mk S d m s

/-- `locMap` intertwines the localization maps: `locMap d ∘ mk = mk ∘ d`. -/
theorem locMap_mkLinearMap (d : M →ₗ[A] N) (m : M) :
    locMap S d (LocalizedModule.mkLinearMap S M m) =
      LocalizedModule.mkLinearMap S N (d m) :=
  locMap_mk S d m 1

/-- If `e ∘ₗ d = 0`, then the localized `e` kills the image of every element under the
localized `d`. -/
theorem locMap_locMap_eq_zero (d : M →ₗ[A] N) (e : N →ₗ[A] K) (h : e ∘ₗ d = 0)
    (x : LocalizedModule S M) : locMap S e (locMap S d x) = 0 := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [locMap_mk, locMap_mk, show e (d m) = (e ∘ₗ d) m from rfl, h]
    simp

/-- A composable pair of maps composing to zero still composes to zero after localization:
`locMap S e ∘ₗ locMap S d = 0`. -/
theorem locMap_comp_locMap (d : M →ₗ[A] N) (e : N →ₗ[A] K) (h : e ∘ₗ d = 0) :
    locMap S e ∘ₗ locMap S d = 0 :=
  LinearMap.ext (locMap_locMap_eq_zero S d e h)

/-! ## Scaling by an integer power of a unit -/

/-- The `A`-linear automorphism `x ↦ u ^ i • x` of `LocalizedModule S M`, for `u` a unit of
`Localization S` and `i : ℤ`.  For `i < 0` this uses that `u` is invertible. -/
noncomputable def zpowEquiv (M : Type*) [AddCommGroup M] [Module A M]
    (u : (Localization S)ˣ) (i : ℤ) : LocalizedModule S M ≃ₗ[A] LocalizedModule S M :=
  DistribMulAction.toLinearEquiv A (LocalizedModule S M) (u ^ i)

/-- `zpowEquiv S M u i` is scaling by `u ^ i`. -/
@[simp]
theorem zpowEquiv_apply (u : (Localization S)ˣ) (i : ℤ) (x : LocalizedModule S M) :
    zpowEquiv S M u i x = (u ^ i) • x := rfl

/-- Scaling by `u ^ i` is injective. -/
theorem zpowEquiv_injective (u : (Localization S)ˣ) (i : ℤ) :
    Function.Injective (zpowEquiv S M u i) := (zpowEquiv S M u i).injective

/-- `u ^ i • N`, for `u` a unit of `Localization S` and `i : ℤ`. -/
noncomputable def zsmulSub {M : Type*} [AddCommGroup M] [Module A M]
    (u : (Localization S)ˣ) (i : ℤ) (N : Submodule A (LocalizedModule S M)) :
    Submodule A (LocalizedModule S M) :=
  N.map (DistribMulAction.toLinearEquiv A _ (u ^ i)).toLinearMap

/-- `u ^ i • P` is the image of `P` under `zpowEquiv`. -/
theorem zsmulSub_eq_map_zpowEquiv (u : (Localization S)ˣ) (i : ℤ)
    (P : Submodule A (LocalizedModule S M)) :
    zsmulSub S u i P = P.map (zpowEquiv S M u i).toLinearMap := rfl

/-- The elements of `u ^ i • P` are the `u ^ i • x` with `x ∈ P`. -/
theorem mem_zsmulSub (u : (Localization S)ˣ) (i : ℤ) (P : Submodule A (LocalizedModule S M))
    (y : LocalizedModule S M) : y ∈ zsmulSub S u i P ↔ ∃ x ∈ P, (u ^ i) • x = y :=
  Iff.rfl

/-- Scaling by the zeroth power of a unit does nothing. -/
@[simp]
theorem zsmulSub_zero (u : (Localization S)ˣ) (P : Submodule A (LocalizedModule S M)) :
    zsmulSub S u 0 P = P := by
  ext y
  simp [mem_zsmulSub]

/-- Scaling twice by the same power scales by the product of the units. -/
theorem zsmulSub_zsmulSub (u v : (Localization S)ˣ) (i : ℤ)
    (P : Submodule A (LocalizedModule S M)) :
    zsmulSub S u i (zsmulSub S v i P) = zsmulSub S (u * v) i P := by
  ext y
  simp only [mem_zsmulSub]
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by rw [mul_zpow, mul_smul]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨v ^ i • z, ⟨z, hz, rfl⟩, by rw [mul_zpow, mul_smul]⟩

/-- Scaling by a unit power commutes with intersection. -/
theorem zsmulSub_inf (u : (Localization S)ˣ) (i : ℤ)
    (P Q : Submodule A (LocalizedModule S M)) :
    zsmulSub S u i (P ⊓ Q) = zsmulSub S u i P ⊓ zsmulSub S u i Q :=
  Submodule.map_inf _ (LinearEquiv.injective _)

/-- Scaling by a unit power commutes with taking the preimage along a localized map. -/
theorem zsmulSub_comap (d : M →ₗ[A] N) (u : (Localization S)ˣ) (i : ℤ)
    (R : Submodule A (LocalizedModule S N)) :
    zsmulSub S u i (R.comap (locMap S d)) = (zsmulSub S u i R).comap (locMap S d) := by
  ext y
  simp only [mem_zsmulSub, Submodule.mem_comap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [locMap_units_smul]
    exact ⟨locMap S d x, hx, rfl⟩
  · rintro ⟨p, hp, hpy⟩
    refine ⟨((u ^ i : (Localization S)ˣ))⁻¹ • y, ?_, by rw [smul_smul]; simp⟩
    rw [locMap_units_smul, ← hpy, smul_smul]
    simpa using hp

/-- Scaling by a unit power is injective on submodules. -/
theorem zsmulSub_injective (u : (Localization S)ˣ) (i : ℤ) :
    Function.Injective (zsmulSub S (M := M) u i) :=
  Submodule.map_injective_of_injective (LinearEquiv.injective _)

/-- `u ^ i • P` is zero exactly when `P` is. -/
@[simp]
theorem zsmulSub_eq_zero_iff (u : (Localization S)ˣ) (i : ℤ)
    (P : Submodule A (LocalizedModule S M)) : zsmulSub S u i P = ⊥ ↔ P = ⊥ :=
  Submodule.map_eq_bot_iff (e := DistribMulAction.toLinearEquiv A _ (u ^ i))

/-- Scaling the range of a map by a unit power gives the range of the scaled map.  This is
what identifies `u ^ i • (image of M)` with the range of `x ↦ u ^ i • mk x`. -/
theorem zsmulSub_range {P : Type*} [AddCommGroup P] [Module A P]
    (g : P →ₗ[A] LocalizedModule S M) (u : (Localization S)ˣ) (i : ℤ) :
    zsmulSub S u i (LinearMap.range g) =
      LinearMap.range ((zpowEquiv S M u i).toLinearMap ∘ₗ g) :=
  (LinearMap.range_comp _ _).symm

/-! ## The décalage -/

/-- `(η_u)^i = { x ∈ u ^ i • P | d x ∈ u ^ (i + 1) • Q }`, the degree-`i` term of the
décalage of `d : M →ₗ[A] N` with respect to the unit `u`, relative to submodules
`P ⊆ LocalizedModule S M` and `Q ⊆ LocalizedModule S N`. -/
noncomputable def etaTerm {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (u : (Localization S)ˣ) (d : M →ₗ[A] N) (i : ℤ)
    (P : Submodule A (LocalizedModule S M)) (Q : Submodule A (LocalizedModule S N)) :
    Submodule A (LocalizedModule S M) :=
  zsmulSub S u i P ⊓ (zsmulSub S u (i + 1) Q).comap (locMap S d)

/-- An element lies in the degree-`i` décalage term exactly when it lies in `u ^ i • P` and its
image under the localized `d` lies in `u ^ (i + 1) • Q`. -/
theorem mem_etaTerm (u : (Localization S)ˣ) (d : M →ₗ[A] N) (i : ℤ)
    (P : Submodule A (LocalizedModule S M)) (Q : Submodule A (LocalizedModule S N))
    (x : LocalizedModule S M) :
    x ∈ etaTerm S u d i P Q ↔ x ∈ zsmulSub S u i P ∧ locMap S d x ∈ zsmulSub S u (i + 1) Q :=
  Iff.rfl

/-- **The décalage of a complex is a complex.** If `e ∘ₗ d = 0` then the localized `d` carries
the degree-`i` décalage term of `d` into the degree-`(i + 1)` décalage term of `e`. -/
theorem locMap_etaTerm_mem (u : (Localization S)ˣ) (d : M →ₗ[A] N) (e : N →ₗ[A] K)
    (h : e ∘ₗ d = 0) (i : ℤ) (P : Submodule A (LocalizedModule S M))
    (Q : Submodule A (LocalizedModule S N)) (R : Submodule A (LocalizedModule S K))
    {x : LocalizedModule S M} (hx : x ∈ etaTerm S u d i P Q) :
    locMap S d x ∈ etaTerm S u e (i + 1) Q R := by
  rw [mem_etaTerm] at hx ⊢
  refine ⟨hx.2, ?_⟩
  rw [locMap_locMap_eq_zero S d e h]
  exact Submodule.zero_mem _

end Eta
