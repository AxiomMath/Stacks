module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Nagata.Shrink
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universally Japanese rings, Nagata rings, and Japanese schemes

Throughout, "ring" means commutative ring with unit, and "domain" means integral
domain. For a domain `R` we write `K = Frac(R)` for its fraction field. The integral
closure of `R` in a field `L` (with `K ⊆ L`) means the subring
`{x ∈ L | x is integral over R}` of `L`.

These are the algebra and scheme-theoretic notions underlying Stacks Tags 032R, 0BI1,
and 033R (Lemma 28.13.7).

## Definitions

* Definition 1 (N-1, N-2 / Japanese rings — Stacks 0BI0). For a domain `R` with
  fraction field `K`:
  - `R` is N-1 if the integral closure of `R` in `K` is a finite `R`-module.
  - `R` is N-2 (Japanese) if for every finite field extension `L / K` the integral
    closure of `R` in `L` is a finite `R`-module.

* Definition 2 (universally Japanese / Nagata rings — Stacks 032R). For a ring `R`:
  - `R` is universally Japanese if for any finite-type ring map `R → S` with `S` a
    domain, `S` is N-2.
  - `R` is a Nagata ring if `R` is Noetherian and for every prime ideal `p ⊆ R` the
    quotient `R / p` (a domain) is N-2.

* Definition 3 (Japanese scheme — Stacks 033S). An integral scheme `X` is Japanese if
  for every point `x ∈ X` there is an affine open neighbourhood `x ∈ U ⊆ X` whose ring
  `O_X(U)` (a domain, since `X` is integral) is Japanese.

* Definition 4 (Nagata scheme — Stacks 033T). A scheme `X` is Nagata if for every
  point `x ∈ X` there is an affine open neighbourhood `x ∈ U ⊆ X` whose ring `O_X(U)`
  is a Nagata ring.

* Definition 5 (integral closed subscheme). A closed subscheme `Z ⊆ X` is an integral
  closed subscheme if the closed immersion `Z ↪ X` exhibits `Z` as an integral scheme.
  We model such a subscheme by a scheme `Z` together with a closed immersion
  `f : Z ⟶ X` and an `IsIntegral Z` hypothesis (up to isomorphism this is exactly the
  bijective correspondence with irreducible closed subsets given the reduced induced
  structure).

## Main results
* Statement 1 (Stacks Tag 033R, Lemma 28.13.7). Let `X` be a locally Noetherian
  scheme. Then `X` is Nagata if and only if every integral closed subscheme `Z ⊆ X` is
  Japanese.

## Notes

* Finiteness convention: "finite `R`-module" means finitely generated as an `R`-module
  (module-finite), which is `Module.Finite R _`.
* Mathlib does not currently provide the predicates "N-1", "N-2 / Japanese ring",
  "universally Japanese", "Nagata ring", "Japanese scheme", or "Nagata scheme"; these
  are introduced here.
* The integral closure of `R` in an `R`-algebra `A` is `integralClosure R A`, a
  `Subalgebra R A`; here `A` is the relevant field `L`.
* Definitions 3 and 4 are taken in the "exists affine open neighbourhood" form of
  Stacks Definition 28.13.1; by Stacks Lemmas 28.13.4 and 28.13.6 this is equivalent to
  the "for all affine opens" form.
-/

@[expose] public section

open AlgebraicGeometry
open scoped nonZeroDivisors
universe u v

-- Shared helper for both directions.

/-- Module-finiteness of an algebra transfers along a ring isomorphism of the base. -/
private theorem module_finite_of_ringEquiv_algebraMap {K K' L : Type*} [CommRing K] [CommRing K']
    [CommRing L] [Algebra K L] [Algebra K' L] (e : K ≃+* K')
    (h : ∀ k, algebraMap K L k = algebraMap K' L (e k)) (hfin : Module.Finite K' L) :
    Module.Finite K L := by
  rw [← RingHom.finite_algebraMap,
    show algebraMap K L = (algebraMap K' L).comp e.toRingHom from RingHom.ext h]
  exact (RingHom.finite_algebraMap.mpr hfin).comp (RingEquiv.finite e)

/-- Integral closure commutes with localization at `g` (Stacks 0307): the integral closure of
`Ag` in `L` is the localized module of the integral closure of `A` in `L`. -/
private theorem exists_isLocalizedModule_integralClosure {A Ag L : Type*} [CommRing A]
    [CommRing Ag] [CommRing L] [Algebra A Ag] [Algebra A L] [Algebra Ag L] [IsScalarTower A Ag L]
    (g : A) [IsLocalization.Away g Ag] (hg : IsUnit (algebraMap A L g)) :
    ∃ f : integralClosure A L →ₗ[A] integralClosure Ag L,
      IsLocalizedModule (Submonoid.powers g) f := by
  have : IsLocalization.Away (algebraMap A L g) L :=
    IsLocalization.of_le_isUnit (Submonoid.powers_le.mpr hg)
  have hsub : integralClosure A L ≤ Subalgebra.restrictScalars A (integralClosure Ag L) :=
    fun _ hx => hx.tower_top
  let _ : Algebra (integralClosure A L) (integralClosure Ag L) :=
    (Subalgebra.inclusion hsub).toAlgebra
  have : IsScalarTower (integralClosure A L) (integralClosure Ag L) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A (integralClosure A L) (integralClosure Ag L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hIClocM : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L)
      (Submonoid.powers g)) (integralClosure Ag L) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact IsLocalization.Away.integralClosure g
  exact ⟨IsScalarTower.toAlgHom A (integralClosure A L) (integralClosure Ag L) |>.toLinearMap,
    isLocalizedModule_iff_isLocalization.mpr hIClocM⟩

/-- **N-2 is invariant under a ring isomorphism, across universes.** -/
lemma IsJapaneseRing.of_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] (e : R ≃+* S) (hR : IsJapaneseRing R) : IsJapaneseRing S := by
  refine { finite := fun L _ _ _ _ hfin => ?_ }
  let e' : FractionRing R ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv e
  let _ : Algebra R L := ((algebraMap S L).comp e.toRingHom).toAlgebra
  let _ : Algebra (FractionRing R) L :=
    ((algebraMap (FractionRing S) L).comp e'.toRingHom).toAlgebra
  have hRL : ∀ r : R, (algebraMap R L) r = (algebraMap S L) (e r) := fun _ => rfl
  have hKRL : ∀ k : FractionRing R,
      (algebraMap (FractionRing R) L) k = (algebraMap (FractionRing S) L) (e' k) := fun _ => rfl
  have he' : ∀ r : R, e' (algebraMap R (FractionRing R) r)
      = algebraMap S (FractionRing S) (e r) :=
    fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap e r
  have htower : IsScalarTower R (FractionRing R) L := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [hRL r, hKRL (algebraMap R (FractionRing R) r), he' r,
      ← IsScalarTower.algebraMap_apply S (FractionRing S) L (e r)]
  have hfinR : Module.Finite (FractionRing R) L := by
    exact module_finite_of_ringEquiv_algebraMap e' hKRL hfin
  exact Module.Finite.integralClosure_of_ringEquiv e rfl
    (module_finite_integralClosure_of_isJapaneseRing hR (FractionRing R) L)

/-- Ring Lemma 1 (Stacks 0BIM, localization preserves N-2). If `A` is a Japanese domain
and `g ∈ A` is nonzero, then the away-localization `A_g = Localization.Away g` is again a
Japanese domain.

Argument (Step 2). `A_g` is a domain with the same
fraction field `K = Frac(A_g) = Frac(A)` (a localization of a domain at a nonzero element
has the same fraction field). For a finite extension `L / K`, the integral closure
`integralClosure A_g L` equals the away-localization `(integralClosure A L)_g` inside `L`
(Stacks 0307, integral closure commutes with localization). Since `A` is Japanese,
`integralClosure A L` is a finite `A`-module; localizing a finite module keeps it finite,
so `(integralClosure A L)_g` is a finite `A_g`-module. Hence `A_g` is Japanese.

KEY INPUTS: `IsLocalization.integralClosure` / `IsIntegralClosure.isLocalization`
(Stacks 0307 = `IsLocalization.integralClosure`); localization of a finite module is finite
(`Module.Finite` base-change / surjection); `IsFractionRing` of a localization equals
`Frac A`; algebra/fraction-field bookkeeping as in `IsJapaneseRing.of_ringEquiv`. The
`IsDomain (Localization.Away g)` instance comes from `IsLocalization.isDomain_localization`
(powers of `g ≠ 0` lie in `nonZeroDivisors`). -/
lemma isJapaneseRing_localizationAway {A : Type u} [CommRing A] [IsDomain A]
    (hA : IsJapaneseRing A) (g : A) (hg : g ≠ 0) :
    haveI : IsDomain (Localization.Away g) :=
      IsLocalization.isDomain_localization
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg))
    IsJapaneseRing (Localization.Away g) := by
  have : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_localization
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg))
  have hle : Submonoid.powers g ≤ nonZeroDivisors A :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg)
  refine { finite := fun L _ _ _ _ hfin => ?_ }
  -- Algebra A L via composition A → Ag → L
  let algAL : Algebra A L :=
    (RingHom.comp (algebraMap (Localization.Away g) L)
        (algebraMap A (Localization.Away g))).toAlgebra
  have tower_A_Ag_L : IsScalarTower A (Localization.Away g) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Build Algebra Ag (FractionRing A) and IsFractionRing Ag (FractionRing A).
  have hmap : ∀ y : Submonoid.powers g, IsUnit ((algebraMap A (FractionRing A)) (y : A)) :=
    fun y => IsLocalization.map_units (FractionRing A) ⟨(y : A), hle y.property⟩
  let algAgFracA : Algebra (Localization.Away g) (FractionRing A) :=
    (IsLocalization.lift (S := Localization.Away g) hmap).toAlgebra
  have tower_A_Ag_FracA : IsScalarTower A (Localization.Away g) (FractionRing A) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show (algebraMap A (FractionRing A)) x = _
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq]
  have isFR : IsFractionRing (Localization.Away g) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isLocalization (M := Submonoid.powers g) (Localization.Away g)
      (FractionRing A) hle
  -- Algebra iso between the two fraction rings of Ag.
  let e : FractionRing (Localization.Away g) ≃ₐ[Localization.Away g] FractionRing A :=
    FractionRing.algEquiv (Localization.Away g) (FractionRing A)
  -- Algebra (FractionRing A) L via e.symm then algebraMap (FractionRing Ag) L.
  let algFracAL : Algebra (FractionRing A) L :=
    (RingHom.comp (algebraMap (FractionRing (Localization.Away g)) L) e.symm.toRingHom).toAlgebra
  have tower_A_FracA_L : IsScalarTower A (FractionRing A) L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change (algebraMap A L) x = (algebraMap (FractionRing A) L) ((algebraMap A (FractionRing A)) x)
    have hRHS :
      (algebraMap (FractionRing A) L) ((algebraMap A (FractionRing A)) x) =
        (algebraMap (FractionRing (Localization.Away g)) L)
          (e.symm ((algebraMap A (FractionRing A)) x)) := by
      rw [RingHom.algebraMap_toAlgebra]
      rfl
    rw [hRHS, IsScalarTower.algebraMap_apply A (Localization.Away g) (FractionRing A) x,
      AlgEquiv.commutes e.symm,
      ← IsScalarTower.algebraMap_apply (Localization.Away g) (FractionRing (Localization.Away g)) L,
      ← IsScalarTower.algebraMap_apply A (Localization.Away g) L x]
  -- L is finite over FractionRing A (via e.symm).
  have hfinA : Module.Finite (FractionRing A) L := by
    exact module_finite_of_ringEquiv_algebraMap e.symm.toRingEquiv (fun _ => rfl) hfin
  -- A is Japanese ⟹ integralClosure A L is A-finite.
  have hICAfin : Module.Finite A (integralClosure A L) :=
    @IsJapaneseRing.finite A _ _ hA L _ _ _ _ hfinA
  -- g is a unit in L.
  have hg_unit_L : IsUnit ((algebraMap A L) g) :=
    (IsLocalization.Away.algebraMap_isUnit g).map (algebraMap (Localization.Away g) L)
  -- Localization of integral closure (Stacks 0307) + finiteness of localized module.
  obtain ⟨f, hf⟩ := exists_isLocalizedModule_integralClosure (Ag := Localization.Away g) g hg_unit_L
  exact Module.Finite.of_isLocalizedModule (Submonoid.powers g) f

/-- Ring Lemma 2 (Japanese-ness is local on a basic-open cover). If `B` is a domain, `t` a
finite set generating the unit ideal, and for each `g ∈ t` there is an away-localization
`Bg g hg` of `B` (an `IsLocalization.Away g` domain `B`-algebra) that is Japanese, then `B`
itself is Japanese. (The localizations are passed abstractly via `IsLocalization.Away` to
avoid threading the `g ≠ 0` domain instance through `Localization.Away g`.)

Argument (Step 3). Let `L / Frac(B)` be a finite
extension and `C := integralClosure B L`. For each `g ∈ t`, integral closure commutes with
localization (Stacks 0307), so `C_g = integralClosure (Bg g hg) L`; as `Bg g hg` is
Japanese (and `Frac(Bg) = Frac(B)`), `C_g` is a finite `Bg`-module. Since
`Ideal.span t = ⊤`, `Module.Finite.of_localizationSpan'` (with `M = C`, the localized
modules being the `C_g`) yields `Module.Finite B C`. Hence `B` is Japanese.

KEY INPUTS: `Module.Finite.of_localizationSpan` / `…_finite'` / `…_finite`;
`IsLocalization.integralClosure` (Stacks 0307); the `IsLocalizedModule` structure on the
integral closure localized at `g`; `Frac(Bg) = Frac(B)`. -/
lemma isJapaneseRing_of_localizationSpan {B : Type u} [CommRing B] [IsDomain B] (t : Finset B)
    (ht : Ideal.span (t : Set B) = ⊤) (Bg : ∀ g ∈ t, Type u)
    [∀ (g) (hg : g ∈ t), CommRing (Bg g hg)] [∀ (g) (hg : g ∈ t), IsDomain (Bg g hg)]
    [∀ (g) (hg : g ∈ t), Algebra B (Bg g hg)] [∀ (g) (hg : g ∈ t), IsLocalization.Away g (Bg g hg)]
    (H : ∀ (g) (hg : g ∈ t), IsJapaneseRing (Bg g hg)) : IsJapaneseRing B := by
  refine { finite := fun L _ _ _ _ hfin => ?_ }
  -- Each `g ∈ t` is nonzero: an away-localization at `0` of a domain is subsingleton.
  have hg_ne : ∀ (g : B), g ∈ t → g ≠ 0 := by
    intro g hg hzero
    subst hzero
    have : Subsingleton (Bg 0 hg) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : B)) (S := Bg 0 hg)
        (Submonoid.mem_powers _)
    exact false_of_nontrivial_of_subsingleton (Bg 0 hg)
  -- Each `g ∈ t` is a unit in the field `L`.
  have hg_unit_L : ∀ (g : B), g ∈ t → IsUnit ((algebraMap B L) g) := by
    intro g hg
    rw [IsScalarTower.algebraMap_apply B (FractionRing B) L]
    apply IsUnit.map
    rw [isUnit_iff_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
    exact hg_ne g hg
  have hle : ∀ (gt : ↥t), Submonoid.powers gt.val ≤ B⁰ := fun gt =>
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (hg_ne gt.val gt.property))
  -- Algebra `Bg gt → L` (lift of `B → L`, sending the powers of `g` to units).
  let algBgL : ∀ (gt : ↥t), Algebra (Bg gt.val gt.property) L := fun gt =>
    (IsLocalization.lift (S := Bg gt.val gt.property) (M := Submonoid.powers gt.val) (g :=
        algebraMap B L)
        (by
          rintro ⟨y, n, rfl⟩
          rw [map_pow]
          exact (hg_unit_L gt.val gt.property).pow n)).toAlgebra
  have towerBgL : ∀ (gt : ↥t), IsScalarTower B (Bg gt.val gt.property) L := fun gt => by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change (algebraMap B L) x = (IsLocalization.lift _) _
    rw [IsLocalization.lift_eq]
  -- Algebra `Bg gt → FractionRing B` and the fraction-ring identification.
  let algBgFracB : ∀ (gt : ↥t), Algebra (Bg gt.val gt.property) (FractionRing B) := fun gt =>
    (IsLocalization.lift (S := Bg gt.val gt.property) (M := Submonoid.powers gt.val) (g :=
        algebraMap B (FractionRing B))
        (fun y =>
          IsLocalization.map_units (FractionRing B) ⟨(y : B), hle gt y.property⟩)).toAlgebra
  have towerBgFracB : ∀ (gt : ↥t), IsScalarTower B (Bg gt.val gt.property) (FractionRing B) :=
    fun gt => by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change (algebraMap B (FractionRing B)) x = (IsLocalization.lift _) _
    rw [IsLocalization.lift_eq]
  have isFR : ∀ (gt : ↥t), IsFractionRing (Bg gt.val gt.property) (FractionRing B) := fun gt =>
    IsFractionRing.isFractionRing_of_isLocalization (M := Submonoid.powers gt.val)
      (Bg gt.val gt.property) (FractionRing B) (hle gt)
  -- For each `g ∈ t`, `integralClosure (Bg gt) L` is `Bg gt`-finite (Bg gt is Japanese).
  have keyfin :
    ∀ (gt : ↥t),
      Module.Finite (Bg gt.val gt.property) (integralClosure (Bg gt.val gt.property) L) := by
    intro gt
    have towerBgtFracBL : IsScalarTower (Bg gt.val gt.property) (FractionRing B) L := by
      apply IsScalarTower.of_algebraMap_eq'
      apply IsLocalization.ringHom_ext (Submonoid.powers gt.val)
      ext x
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply B (Bg gt.val gt.property) L x,
        ← IsScalarTower.algebraMap_apply B (Bg gt.val gt.property) (FractionRing B) x,
        ← IsScalarTower.algebraMap_apply B (FractionRing B) L x]
    let e : FractionRing (Bg gt.val gt.property) ≃ₐ[Bg gt.val gt.property] FractionRing B :=
      FractionRing.algEquiv (Bg gt.val gt.property) (FractionRing B)
    let algFracBgtL : Algebra (FractionRing (Bg gt.val gt.property)) L :=
      (RingHom.comp (algebraMap (FractionRing B) L) e.toRingHom).toAlgebra
    have tower1 :
      IsScalarTower (Bg gt.val gt.property) (FractionRing (Bg gt.val gt.property)) L := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change
        (algebraMap (Bg gt.val gt.property) L) x =
          (algebraMap (FractionRing B) L)
            (e (algebraMap (Bg gt.val gt.property) (FractionRing (Bg gt.val gt.property)) x))
      rw [AlgEquiv.commutes e x,
        ← IsScalarTower.algebraMap_apply (Bg gt.val gt.property) (FractionRing B) L x]
    have hfinBgt : Module.Finite (FractionRing (Bg gt.val gt.property)) L := by
      exact module_finite_of_ringEquiv_algebraMap e.toRingEquiv (fun _ => rfl) hfin
    exact @IsJapaneseRing.finite (Bg gt.val gt.property) _ _ (H gt.val gt.property)
      L _ _ _ _ hfinBgt
  -- The canonical scalar tower `B → Bg gt → integralClosure (Bg gt) L`.
  have towerBgIC :
    ∀ (gt : ↥t),
      IsScalarTower B (Bg gt.val gt.property) (integralClosure (Bg gt.val gt.property) L) :=
    fun gt =>
    IsScalarTower.of_algebraMap_eq
      (fun b => by
        apply Subtype.ext
        change
          (algebraMap B L b) =
            (algebraMap (Bg gt.val gt.property) L) ((algebraMap B (Bg gt.val gt.property)) b)
        rw [← IsScalarTower.algebraMap_apply B (Bg gt.val gt.property) L b])
  -- The `B`-linear maps `C → integralClosure (Bg gt) L` are the localized modules (Stacks 0307).
  choose fLM hLM using fun gt : ↥t =>
    haveI := towerBgL gt
    exists_isLocalizedModule_integralClosure (Ag := Bg gt.val gt.property) gt.val
      (hg_unit_L gt.val gt.property)
  -- Finiteness is local on the basic-open cover `t`.
  exact
    @Module.Finite.of_localizationSpan_finite' B _ (integralClosure B L) _ _ t ht
      (fun gt => integralClosure (Bg gt.val gt.property) L) _ _ (fun gt => Bg gt.val gt.property) _
      _ _ _ towerBgIC fLM hLM keyfin

/-- Helper: any away-localization (in the abstract `IsLocalization.Away` sense) of a
Japanese domain at a nonzero element is again Japanese. Combines
`isJapaneseRing_localizationAway` with transport across the canonical `A`-algebra iso
`Localization.Away h ≃ₐ S` and `IsJapaneseRing.of_ringEquiv`. -/
lemma isJapaneseRing_of_isLocalizationAway {A : Type u} [CommRing A] [IsDomain A]
    (hA : IsJapaneseRing A) (h : A) (hh : h ≠ 0) (S : Type u) [CommRing S] [IsDomain S]
    [Algebra A S] [IsLocalization.Away h S] : IsJapaneseRing S := by
  have : IsDomain (Localization.Away h) :=
    IsLocalization.isDomain_localization
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hh))
  have hLoc : IsJapaneseRing (Localization.Away h) := isJapaneseRing_localizationAway hA h hh
  let e : Localization.Away h ≃ₐ[A] S :=
    IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h) S
  exact IsJapaneseRing.of_ringEquiv e.toRingEquiv hLoc

/-- Scheme glue (Stacks 28.13.4, the cover-and-localize step). For an integral scheme `Z`
that is Japanese in the "exists affine neighbourhood" sense and a nonempty affine open `W`,
there is a finite set `t` of elements of `B := Γ(Z, W)` generating the unit ideal together
with, for each `g ∈ t`, an away-localization `Bg g hg` (`IsLocalization.Away g`, a domain
`B`-algebra) that is a Japanese ring.

Argument (Step 4). Each point `w ∈ W` has a Japanese
affine chart `U_w` (from `hZ`); choose a basic open `D(g_w)` of `W` with
`w ∈ D(g_w) ⊆ W ∩ U_w`, so that `Γ(Z, D(g_w)) ≅ B_{g_w}` (`IsAffineOpen.isLocalization_basicOpen`)
is *also* a localization at one element of the Japanese ring `Γ(Z, U_w)`; hence
`B_{g_w}` is Japanese by `isJapaneseRing_localizationAway`. The affine `W ≅ Spec B` is
quasi-compact, so finitely many `D(g_i)` cover `W`, equivalently
`Ideal.span {g_i} = ⊤` (`PrimeSpectrum.iSup_basicOpen_eq_top_iff` / span-eq-top dictionary).
Take `Bg g hg := Γ(Z, D(g))` with its `IsLocalization.Away g` structure as the witnesses.

KEY INPUTS: `IsJapaneseScheme` hypothesis `hZ`; basic opens form a basis
(`PrimeSpectrum.isBasis_basic_opens`, `IsAffineOpen.basicOpen`);
`IsAffineOpen.isLocalization_basicOpen` (ring of a basic open is the principal localization);
`isJapaneseRing_localizationAway` (Lemma 1) to land Japanese-ness on each `B_{g_i}`;
quasi-compactness of the affine `W` (`PrimeSpectrum.compactSpace`); the dictionary
`⋃ D(gᵢ) = Spec B ↔ Ideal.span {gᵢ} = ⊤`. -/
lemma exists_japanese_localizationSpan_cover
    (Z : Scheme.{u}) [IsIntegral Z] (hZ : IsJapaneseScheme Z)
    (W : Z.affineOpens) [Nonempty W.1] :
    haveI : IsDomain Γ(Z, W.val) := IsIntegral.component_integral W.val
    ∃ (t : Finset Γ(Z, W.val))
      (Bg : ∀ g ∈ t, Type u) (_ : ∀ (g) (hg : g ∈ t), CommRing (Bg g hg))
      (_ : ∀ (g) (hg : g ∈ t), IsDomain (Bg g hg))
      (_ : ∀ (g) (hg : g ∈ t), Algebra Γ(Z, W.val) (Bg g hg))
      (_ : ∀ (g) (hg : g ∈ t), IsLocalization.Away g (Bg g hg)),
      Ideal.span (t : Set Γ(Z, W.val)) = ⊤ ∧
      ∀ (g) (hg : g ∈ t), IsJapaneseRing (Bg g hg) := by
  classical
  have : IsDomain Γ(Z, W.val) := IsIntegral.component_integral W.val
  -- Helper: for an integral (hence reduced) scheme, a nonzero section has nonempty
  -- basic open.
  have hne_of_ne : ∀ {U : Z.Opens} (s : Γ(Z, U)), s ≠ 0 → Nonempty (Z.basicOpen s) := by
    intro U s hs
    have hbne : Z.basicOpen s ≠ ⊥ := fun hbot => hs ((basicOpen_eq_bot_iff s).mp hbot)
    rw [Ne, TopologicalSpace.Opens.ext_iff, TopologicalSpace.Opens.coe_bot] at hbne
    exact (Set.nonempty_iff_ne_empty.mpr hbne).to_subtype
  -- The "good set" `S`: nonzero elements `g ∈ B` whose basic open is a basic open of
  -- some Japanese affine chart `Uw`.
  set S : Set Γ(Z, W.val) :=
    { g | g ≠ 0 ∧ ∃ (Uw : Z.affineOpens) (_ : Nonempty Uw.val) (h : Γ(Z, Uw.val)),
        (have : IsDomain Γ(Z, Uw.val) := IsIntegral.component_integral Uw.val;
          IsJapaneseRing Γ(Z, Uw.val)) ∧ Z.basicOpen g = Z.basicOpen h } with hS
  -- The basic opens of elements of `S` cover `W`.
  have hcover : W.val ≤ ⨆ f : S, Z.basicOpen (f : Γ(Z, W.val)) := by
    intro x hx
    -- `x ∈ W`; find a Japanese chart `Uw ∋ x` and a common basic open.
    obtain ⟨Uw, hxUw, hjap⟩ := hZ x
    have hUwne : Nonempty Uw.val := ⟨⟨x, hxUw⟩⟩
    obtain ⟨gf, h, hbeq, hxg⟩ :=
      exists_basicOpen_le_affine_inter W.property Uw.property x ⟨hx, hxUw⟩
    -- `gf ≠ 0` since its basic open contains `x`.
    have hgf_ne : gf ≠ 0 := by
      intro h0
      rw [h0, Scheme.basicOpen_zero] at hxg
      simp at hxg
    have hgfS : gf ∈ S := ⟨hgf_ne, Uw, hUwne, h, hjap, hbeq⟩
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨gf, hgfS⟩, hxg⟩
  -- Translate the cover into `Ideal.span S = ⊤`.
  have hspanS : Ideal.span (S : Set Γ(Z, W.val)) = ⊤ :=
    (W.property.self_le_iSup_basicOpen_iff).mp hcover
  -- Extract a finite subset `t ⊆ S` with `Ideal.span t = ⊤`.
  obtain ⟨t, htS, htspan⟩ := (Ideal.span_eq_top_iff_finite S).mp hspanS
  -- Every `g ∈ t` is in `S`, hence nonzero, hence has nonempty basic open.
  have hgne : ∀ (g) (hg : g ∈ t), Nonempty (Z.basicOpen g) :=
    fun g hg => hne_of_ne g (htS hg).left
  -- Build the witnesses.
  refine ⟨t, fun g _ => Γ(Z, Z.basicOpen g), fun g hg => inferInstance,
    fun g hg => have := hgne g hg; IsIntegral.component_integral (Z.basicOpen g),
    fun g hg => inferInstance, fun g hg => W.property.isLocalization_basicOpen g, htspan, ?_⟩
  -- Japanese-ness of each `Γ(Z, Z.basicOpen g)`.
  intro g hg
  have : Nonempty (Z.basicOpen g) := hgne g hg
  -- `g ∈ S`, so we have a Japanese chart `Uw` and `h : Γ(Z, Uw)` with the basicOpens equal.
  obtain ⟨hgne0, Uw, hUwne, h, hjap, hbeq⟩ := htS hg
  have hUwne' : Nonempty Uw.val := hUwne
  have : IsDomain Γ(Z, Uw.val) := IsIntegral.component_integral Uw.val
  have : IsDomain Γ(Z, Z.basicOpen g) := IsIntegral.component_integral (Z.basicOpen g)
  have hbgle : Z.basicOpen g ≤ Uw.val := hbeq ▸ Z.basicOpen_le h
  -- The restriction algebra `Γ(Z, Uw) → Γ(Z, basicOpen g)` and away-localization.
  let algV : Algebra Γ(Z, Uw.val) Γ(Z, Z.basicOpen g) :=
    (Z.presheaf.map (hbgle.hom).op).hom.toAlgebra
  have hLoc : IsLocalization.Away h Γ(Z, Z.basicOpen g) :=
    Uw.property.isLocalization_of_eq_basicOpen h (hbgle.hom) hbeq
  -- `h ≠ 0`: otherwise `Z.basicOpen g = Z.basicOpen h = ⊥`, contradicting `Nonempty`.
  have hh : h ≠ 0 := by
    intro h0
    have hbot : Z.basicOpen g = (⊥ : Z.Opens) := by rw [hbeq, h0, Scheme.basicOpen_zero]
    obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty (Z.basicOpen g))
    rw [hbot] at hx
    simp at hx
  exact isJapaneseRing_of_isLocalizationAway hjap h hh Γ(Z, Z.basicOpen g)

/-- Descent helper (Claim E, **Stacks Tag 28.13.4 / 0BAH**, the equivalence of the
"exists affine neighbourhood" and "for all affine opens" forms of a Japanese scheme).
For an integral scheme `Z` satisfying the "exists neighbourhood" definition
`IsJapaneseScheme Z` and *any* nonempty affine open `W ⊆ Z`, the domain `Γ(Z, W)` is a
Japanese ring.

The argument is: cover `W` by basic opens whose section rings
are away-localizations of Japanese charts (`exists_japanese_localizationSpan_cover`, using
Lemma 1 `isJapaneseRing_localizationAway`), then glue Japanese-ness up the cover
(`isJapaneseRing_of_localizationSpan`, Lemma 2). This body is COMPLETE (no open goals);
the remaining content lives in the three sub-lemmas above. -/
lemma isJapaneseScheme_forall_affineOpens (Z : Scheme.{u}) [IsIntegral Z] (hZ : IsJapaneseScheme Z)
    (W : Z.affineOpens) [Nonempty W.1] :
    haveI : IsDomain Γ(Z, W.val) := IsIntegral.component_integral W.val
    IsJapaneseRing Γ(Z, W.val) := by
  have : IsDomain Γ(Z, W.val) := IsIntegral.component_integral W.val
  obtain ⟨t, Bg, hcr, hd, halg, hloc, hspan, hjap⟩ := exists_japanese_localizationSpan_cover Z hZ W
  exact isJapaneseRing_of_localizationSpan t hspan Bg hjap

-- needed: `nagata_backward_quotient_japanese` rewrites under `IsAffineOpen.fromSpec`, whose
-- proof-argument coercion only matches the rewrite pattern at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- Core engine of the backward direction (Stacks 033R ⇐, Claims A–E): for an affine
open `V` of a locally Noetherian scheme `X` all of
whose integral closed subschemes are Japanese, every quotient `Γ(X,V) ⧸ p` by a prime
`p` is a Japanese ring.

Argument (Part (2), Claims A–E).
Let `R = Γ(X,V)` and `p ⊆ R` prime. Let `ι_V = V.fromSpec : Spec R → X` be the canonical
homeomorphism onto `V`.
* Claim A: `T := closure (ι_V '' zeroLocus p) ⊆ X` is an irreducible closed subset
  (`zeroLocus p` is irreducible since `p` is prime — `PrimeSpectrum.isIrreducible_zeroLocus_iff`;
  continuous image + closure preserve irreducibility), and `ι_V ⁻¹' T = zeroLocus p`
  (since `ι_V '' zeroLocus p` is closed *in* `V`).
* Claim B: equip `T` with its reduced induced closed subscheme structure
  (`Scheme.IdealSheafData` / reduced-induced); the resulting scheme `Z` with closed
  immersion `j : Z ↪ X` is integral (reduced + irreducible).
* Claim C: `W := j ⁻¹ V` is a nonempty affine open of `Z` with
  `Γ(Z,W) ≅ R ⧸ p` (`IdealSheafData.subschemeObjIso`; the vanishing ideal of `T`
  restricted to `V` is `p` because `p` is radical:
  `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`,
  `hp.radical`).
* Claim D: `hZ Z j hj inferInstance` gives `IsJapaneseScheme Z`.
* Claim E: by the "for all affine opens" form of Japanese-scheme (Stacks 28.13.4,
  assumable cited infrastructure), `Γ(Z,W)` is a Japanese ring; transport along the
  iso `Γ(Z,W) ≅ R ⧸ p` (`IsJapaneseRing.of_ringEquiv`) to conclude `R ⧸ p` Japanese.

KEY INPUTS: `PrimeSpectrum.isIrreducible_zeroLocus_iff`; reduced-induced closed subscheme
API (`Scheme.IdealSheafData`, `IdealSheafData.vanishingIdeal`, `IdealSheafData.subscheme`,
`IdealSheafData.subschemeObjIso`); `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`,
`Ideal.IsPrime.radical`; the "all affine opens" form of `IsJapaneseScheme`
(Stacks 28.13.4 — assumable); `IsJapaneseRing.of_ringEquiv`. -/
lemma nagata_backward_quotient_japanese (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hZ :
      ∀ (Z : Scheme.{u}) (f : Z ⟶ X), IsClosedImmersion f → [IsIntegral Z] → IsJapaneseScheme Z)
    (V : X.affineOpens) (p : Ideal Γ(X, V.1)) [hp : p.IsPrime] :
    IsJapaneseRing (Γ(X, V.val) ⧸ p) := by
  -- Claim A: the irreducible closed set `T = closure (fromSpec '' zeroLocus p)`.
  set Zp : Set (Spec Γ(X, V.val)) := PrimeSpectrum.zeroLocus (p : Set Γ(X, V.val)) with hZp
  set Tset : Set X := closure (V.property.fromSpec '' Zp) with hT
  have hTirr : IsIrreducible Tset := by
    refine IsIrreducible.closure (IsIrreducible.image ?_ _ ?_)
    · exact (PrimeSpectrum.isIrreducible_zeroLocus_iff p).mpr (by rwa [hp.radical])
    · exact V.property.fromSpec.continuous.continuousOn
  set Tcl : TopologicalSpace.Closeds X := ⟨Tset, isClosed_closure⟩ with hTcl
  set I := Scheme.IdealSheafData.vanishingIdeal Tcl with hI
  -- the preimage of `T` under `fromSpec` is `zeroLocus p` (Claim A, A1).
  have hpre : (V.property.fromSpec) ⁻¹' (Tcl : Set X) = Zp := by
    change (V.property.fromSpec) ⁻¹' Tset = Zp
    rw [hT, hZp]
    have hemb : Topology.IsEmbedding (V.property.fromSpec) :=
      (V.property.fromSpec.isOpenEmbedding (H := V.property.isOpenImmersion_fromSpec)).isEmbedding
    rw [← hemb.closure_eq_preimage_closure_image]
    exact (PrimeSpectrum.isClosed_zeroLocus _).closure_eq
  -- Claim C (C1): the vanishing ideal of `T` restricted to `V` equals `p`.
  have hvanZp : PrimeSpectrum.vanishingIdeal Zp = p := by
    rw [hZp, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hp.radical]
  have hidealV : I.ideal V = p :=
    (Scheme.IdealSheafData.vanishingIdeal_ideal Tcl V).trans
      ((congrArg PrimeSpectrum.vanishingIdeal hpre).trans hvanZp)
  -- Claim B: `Z := I.subscheme` with closed immersion `j := I.subschemeι` is integral.
  have hrange : Set.range I.subschemeι = Tset := by
    rw [I.range_subschemeι, hI]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal Tcl
  have hred : IsReduced I.subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Tcl
  have hirr : IrreducibleSpace I.subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.irreducibleSpace_subscheme X I
      (by rwa [hrange])
  have hZint : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  -- Claim C: `W := j ⁻¹ V` is a nonempty affine open of `Z`.
  set W : (I.subscheme).Opens := I.subschemeι ⁻¹ᵁ V.val with hW
  have hWaff : IsAffineOpen W := V.property.preimage I.subschemeι
  -- `W` is nonempty: `zeroLocus p` is nonempty (since `p ≠ ⊤`), and its `fromSpec`-image
  -- lies in `V ∩ T = V ∩ range j`, hence is hit by `j`.
  have hZpne : Zp.Nonempty := by
    rw [hZp, Set.nonempty_iff_ne_empty]
    intro hempty
    have : (p : Ideal Γ(X, V.val)) = ⊤ := by rwa [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]
    exact hp.ne_top this
  have hWne : Nonempty (W : Type u) := by
    obtain ⟨x₀, hx₀⟩ := hZpne
    -- fromSpec x₀ ∈ V ∩ T ⊆ range j
    have hmemT : V.property.fromSpec x₀ ∈ Tset := subset_closure ⟨x₀, hx₀, rfl⟩
    have hmemrange : V.property.fromSpec x₀ ∈ Set.range I.subschemeι := by rwa [hrange]
    obtain ⟨w, hw⟩ := hmemrange
    have hmemV : V.property.fromSpec x₀ ∈ V.val := by
      have : V.property.fromSpec x₀ ∈ Set.range V.property.fromSpec := ⟨x₀, rfl⟩
      rwa [V.property.range_fromSpec] at this
    refine ⟨⟨w, ?_⟩⟩
    change I.subschemeι.base w ∈ V.val
    rwa [hw]
  -- ring iso `Γ(Z, W) ≃+* Γ(X,V) ⧸ p`.
  have hringiso : Γ(I.subscheme, W) ≃+* (Γ(X, V.val) ⧸ p) := by
    have e1 := (I.subschemeObjIso V).commRingCatIsoToRingEquiv
    rwa [hidealV] at e1
  -- Claim D: `Z` is a Japanese scheme.
  have hZjap : IsJapaneseScheme I.subscheme := hZ I.subscheme I.subschemeι inferInstance
  -- Claim E: descend Japanese-ness to the affine open `W`, then transport.
  have : IsDomain Γ(I.subscheme, W) := IsIntegral.component_integral W
  have hWjap : IsJapaneseRing Γ(I.subscheme, W) :=
    @isJapaneseScheme_forall_affineOpens I.subscheme _ hZjap ⟨W, hWaff⟩ hWne
  -- transport along the iso `Γ(Z,W) ≃+* Γ(X,V) ⧸ p`.
  exact IsJapaneseRing.of_ringEquiv hringiso hWjap

-- Sub-lemmas for the two directions of Statement 1.

/-- Forward direction of Stacks 033R (Lemma 28.13.7): a Nagata scheme `X` has every
integral closed subscheme `Z` Japanese.

Argument (direction ⇒).
Let `Z ↪ X` be an integral closed subscheme (so `Z` is integral) and let `z ∈ Z` be a
point.  Its image `x = f.base z ∈ X` lies, by the Nagata hypothesis on `X`, in some
affine open `V ⊆ X` whose ring `R = Γ(X, V)` is a Nagata ring.  Pulling `V` back along
the closed immersion `f` gives an open `f⁻¹ V` of `Z` containing `z`; shrinking to an
affine open `U ⊆ f⁻¹ V ⊆ Z` containing `z` (affine opens form a basis), the restriction
of the closed immersion to `U → V` is, on rings, a *surjection* `R = Γ(X,V) ↠ Γ(Z,U)`
(closed immersions are locally `Spec` of a quotient, Stacks 01IG /
`AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk`).  Hence `Γ(Z,U) ≅ R ⧸ p`
where `p = ker(R ↠ Γ(Z,U))`.  Because `Z` is integral, `Γ(Z,U)` is a domain, so `p` is a
prime ideal of `R`.  As `R` is a Nagata ring, `R ⧸ p` is a Japanese ring by definition
(`IsNagataRing.isJapaneseRing_quotient`); transporting along the iso `Γ(Z,U) ≅ R ⧸ p`,
`Γ(Z,U)` is Japanese.
This exhibits, for the arbitrary point `z`, an affine open neighbourhood with Japanese
ring of sections, i.e. `Z` is a Japanese scheme.

KEY INPUTS (cited Mathlib): closed immersion locally a quotient
(`IsClosedImmersion.spec_of_quotient_mk` / `IsClosedImmersion.Spec_iff`); quotient by a
prime is a domain / kernel of a surjection onto a domain is prime
(`Ideal.Quotient.isDomain_iff_prime` or `RingHom.ker` + `Ideal.IsPrime`); transport of
`IsJapaneseRing` across a ring isomorphism (a small helper lemma to be proved, since
`IsJapaneseRing` is bundled with `FractionRing`/`integralClosure` data); affine opens are
a basis (`AlgebraicGeometry.Scheme.affineOpens` / `Opens.isBasis`). -/
theorem nagata_scheme_forward (X : Scheme.{u}) (hX : IsNagataScheme X) (Z : Scheme.{u}) (f : Z ⟶ X)
    (hf : IsClosedImmersion f) [IsIntegral Z] : IsJapaneseScheme Z := by
  intro z
  -- The image point `x = f.base z` lies in a Nagata affine open `V` of `X`.
  obtain ⟨V, hxV, hNagata⟩ := hX (f.base z)
  obtain ⟨hNoeth, hJap⟩ := hNagata
  -- `U := f ⁻¹ V` is an affine open of `Z` containing `z` (closed immersions are affine).
  set U : Z.Opens := f ⁻¹ᵁ V.val with hU
  have hzU : z ∈ U := hxV
  have hUaff : IsAffineOpen U := V.property.preimage f
  have hUne : Nonempty (U : Type u) := ⟨⟨z, hzU⟩⟩
  have hUdom : IsDomain Γ(Z, U) := IsIntegral.component_integral U
  -- The ring map `Γ(X,V) → Γ(Z,U)` is surjective (closed immersion).
  have hsurj : Function.Surjective ⇑(f.app V.val).hom := f.app_surjective V.val V.property
  -- Its kernel `p` is prime, since the quotient `Γ(X,V) ⧸ p ≅ Γ(Z,U)` is a domain.
  set p : Ideal Γ(X, V.val) := RingHom.ker (f.app V.val).hom with hp
  let e : (Γ(X, V.val) ⧸ p) ≃+* Γ(Z, U) := RingHom.quotientKerEquivOfSurjective hsurj
  have hqdom : IsDomain (Γ(X, V.val) ⧸ p) := MulEquiv.isDomain Γ(Z, U) e.toMulEquiv
  have hpprime : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).mp hqdom
  -- `Γ(X,V)` Nagata ⟹ `Γ(X,V) ⧸ p` Japanese; transport along `e` to `Γ(Z,U)`.
  exact ⟨⟨U, hUaff⟩, hzU, IsJapaneseRing.of_ringEquiv e (hJap p)⟩

/-- Backward direction of Stacks 033R (Lemma 28.13.7): if every integral closed
subscheme of a locally Noetherian scheme `X` is Japanese, then `X` is Nagata.

Argument (direction ⇐).
Fix `x ∈ X`.  Since `X` is locally Noetherian choose an affine open `V ∋ x` with
`R = Γ(X, V)` Noetherian (`IsLocallyNoetherian.component_noetherian`, Stacks 01OW).  We
must show `R` is a Nagata ring, i.e. (i) `R` Noetherian — done — and (ii) for every
prime `p ⊆ R`, `R ⧸ p` is a Japanese ring.

For (ii): let `p ⊆ R` be prime.  Inside `V = Spec R` the vanishing locus `V(p)` is an
irreducible closed subset (its closure in `X`, `T := closure (image of V(p))`, is
irreducible closed in `X`).  Equip `T` with its reduced induced closed subscheme
structure (`Scheme.IdealSheafData.subscheme` / reduced-induced, Stacks 01J3); call the
resulting scheme `Z` with closed immersion `g : Z ↪ X`.  Then `Z` is integral (reduced +
irreducible), so by hypothesis `Z` is a Japanese scheme.  The intersection `Z ∩ V` is an
affine open of `Z` with ring of sections `R ⧸ p` (the reduced induced structure on `V(p)`
inside `Spec R` is `Spec (R ⧸ p)` since `p` is already radical, being prime; Stacks 01J2 /
`affine_isReduced_iff`, `PrimeSpectrum.zeroLocus_radical`).  Applying the "for all affine
opens" form of Japanese-scheme (Stacks 28.13.4, available as cited infrastructure) — or
directly producing the neighbourhood — gives that `R ⧸ p` is a Japanese ring.

Since `R` is Noetherian and `R ⧸ p` is Japanese for every prime `p`, `R` is a Nagata
ring.  Thus every `x` has an affine open neighbourhood with Nagata ring of sections, so
`X` is a Nagata scheme.

KEY INPUTS (cited Mathlib): `IsLocallyNoetherian.component_noetherian`
(01OW); reduced-induced closed subscheme of an irreducible closed subset is integral
(reduced via 01J1/`IsReduced.component_reduced`, irreducible by construction);
identification of the reduced induced structure on `V(p) ⊆ Spec R` with `Spec (R ⧸ p)`
(01J2 `affine_isReduced_iff`, `PrimeSpectrum.zeroLocus_radical`,
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus` 00E5); the equivalence of the
"exists nbhd" and "for all affine opens" forms of Japanese (Stacks 28.13.4) to descend
the Japanese-ring property to the specific affine open `Spec (R ⧸ p)`; transport of
`IsJapaneseRing` across a ring isomorphism. -/
theorem nagata_scheme_backward (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hZ :
      ∀ (Z : Scheme.{u}) (f : Z ⟶ X), IsClosedImmersion f → [IsIntegral Z] → IsJapaneseScheme Z) :
    IsNagataScheme X := by
  intro x
  -- Pick an affine open neighbourhood `V ∋ x` (affine opens form a basis).
  obtain ⟨V, hVaff, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (Set.mem_univ x)
  refine ⟨⟨V, hVaff⟩, hxV, ?_⟩
  -- `Γ(X,V)` is a Nagata ring: Noetherian + every quotient by a prime is Japanese.
  refine ⟨?_, ?_⟩
  · -- (i) Noetherian, since `X` is locally Noetherian
    -- (`IsLocallyNoetherian.component_noetherian`).
    exact IsLocallyNoetherian.component_noetherian ⟨V, hVaff⟩
  · -- (ii) for every prime `p`, `Γ(X,V) ⧸ p` is Japanese — the core engine (Claims A–E).
    intro p hp
    exact nagata_backward_quotient_japanese X hZ ⟨V, hVaff⟩ p

/-- Let `X` be a locally Noetherian
scheme. Then `X` is Nagata if and only if every integral closed subscheme `Z ⊆ X` is
Japanese. An integral closed subscheme is modelled as a scheme `Z` with a closed
immersion `f : Z ⟶ X` and `IsIntegral Z`.

The two directions are isolated as `nagata_scheme_forward` and
`nagata_scheme_backward`; here we just assemble them. -/
theorem nagata_iff_integral_closed_subschemes_japanese (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsNagataScheme X ↔
      ∀ (Z : Scheme.{u}) (f : Z ⟶ X),
        IsClosedImmersion f → [IsIntegral Z] → IsJapaneseScheme Z := by
  constructor
  · intro hX Z f hf _
    exact nagata_scheme_forward X hX Z f hf
  · intro hZ
    exact nagata_scheme_backward X hZ
