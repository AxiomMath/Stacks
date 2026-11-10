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
# A localization of a Nagata ring is a Nagata ring

Throughout, all rings are commutative with unit. For an integral domain `R` we write
`Frac(R)` for its field of fractions. For an `R`-algebra `R → L`, "the integral closure
of `R` in `L`" means the subring of `L` consisting of all elements integral over the
image of `R`. "Finite over `R`" means finitely generated as an `R`-module.

These definitions follow the Stacks project (Tag 032E and Tag 0BI1 / Section 10.161).

## Definitions

* (N-1, "Japanese" for a domain) Let `R` be an integral domain with fraction field
  `K = Frac(R)`. `R` is N-1 if the integral closure of `R` in `K` is module-finite over `R`.

* (N-2 / Japanese for a domain) Let `R` be an integral domain with fraction field
  `K = Frac(R)`. `R` is N-2 if for every finite field extension `L / K`, the integral
  closure of `R` in `L` is module-finite over `R`. (Note: N-2 implies N-1, taking `L = K`.)

* (Nagata ring) A ring `R` is a Nagata ring if `R` is Noetherian and for every prime
  ideal `p ⊆ R`, the quotient domain `R / p` is N-2.

* (Localization) An `R`-algebra `T` is a localization of `R` if there is a multiplicative
  submonoid `M ⊆ R` such that `R → T` realizes `T` as `M⁻¹R`. In Mathlib terms this is
  expressed by `IsLocalization M T` for the given `R`-algebra structure on `T`.

## Main results
Let `R` be a Nagata ring. Let `M ⊆ R` be a multiplicative submonoid, and let `T = M⁻¹R`
be the localization of `R` at `M`. Then `T` is a Nagata ring.
-/

-- ===== merged from Sec162/Tag032U =====

@[expose] public section

open AlgebraicGeometry
open scoped nonZeroDivisors
universe u v

-- Background:
-- The Stacks proof is short ("clear from Lemma 10.161.3", Tag 032G). The two ingredients
-- are: (1) Noetherianity is preserved under localization (`IsLocalization.isNoetherianRing`);
-- (2) the N-2 (Japanese) property passes to localizations of a domain (Tag 032G), because
-- forming the integral closure commutes with localization (Tag 0307, available in Mathlib
-- as `IsLocalization.integralClosure`).
--
-- Universe convention: we quantify finite field extensions `L` of `K = Frac(R)` over the
-- same universe as `R`. This is harmless since any finite extension of `K` may be realized
-- in this universe, and it makes the N-2 condition apply uniformly to quotients `R / p`
-- (which live in the same universe as `R`) and to localizations `T` of `R`.

open scoped nonZeroDivisors

/-- A field which is a localization of a domain `D` (with injective structure map) is a
fraction field of `D`. -/
theorem isFractionRing_of_field_isLocalization (D : Type u) [CommRing D] [IsDomain D] (F : Type u)
    [Field F] [Algebra D F] (N : Submonoid D) [IsLocalization N F]
    (hinj : Function.Injective (algebraMap D F)) : IsFractionRing D F := by
  have hN : N ≤ D⁰ := by
    intro a ha
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    have : IsUnit ((algebraMap D F) (0 : D)) := IsLocalization.map_units F ⟨0, ha⟩
    rw [map_zero] at this
    exact not_isUnit_zero this
  refine IsLocalization.of_le N D⁰ hN ?_
  intro a ha
  rw [isUnit_iff_ne_zero]
  intro h
  have h0 : (algebraMap D F) a = (algebraMap D F) 0 := by simpa using h
  apply hinj at h0
  rw [h0] at ha
  have : (1 : D) = 0 := (mem_nonZeroDivisors_iff.mp ha).left 1 (by simp)
  exact one_ne_zero this

/-- (Stacks Tag 032G, key step) The N-2 (Japanese) property passes to localizations of a
domain. If `D` is an N-2 domain and `S = N⁻¹ D` is a localization at a submonoid `N` of
nonzerodivisors (so `S` is again a domain with the same fraction field), then `S` is N-2.

Informal proof.
Let `L` be a finite field extension of `K_S = Frac(S)`. We must show the integral closure
of `S` in `L` is module-finite over `S`.

Step 1 (same fraction field). Since `S = N⁻¹ D` with `N ≤ D⁰`, the structure map `D → S` is
injective and `Frac(S) ≅ Frac(D) =: K_D` canonically (a localization of a domain at
nonzerodivisors has the same field of fractions). Concretely `S` and `D` share the fraction
field; this is the content of the already-proven helper_032u
`isFractionRing_of_field_isLocalization` (a field that is a localization of a domain is its
fraction field). Hence `L`, a finite extension of `Frac(S)`, is also (via this identification)
a finite extension of `K_D = Frac(D)`, of the same degree.

Step 2 (N-2 of D supplies finiteness over D). Because `D` is N-2, the integral closure
`C_D := integralClosure D L` is module-finite over `D`.

Step 3 (integral closure commutes with localization, Stacks Tag 0307 = Mathlib
`IsLocalization.integralClosure`). The integral closure of `S` in `L` is the localization of
`C_D` at (the image of) `N`: `integralClosure S L ≅ N⁻¹ C_D = (algebraMapSubmonoid C_D N)⁻¹ C_D`.
Equivalently, `integralClosure S L` is an `IsLocalization (Algebra.algebraMapSubmonoid C_D N)`
of `C_D`.

Step 4 (finiteness transfers under localization). A localization of a module-finite algebra
is module-finite over the localized base: from `Module.Finite D C_D` and the localization
`S = N⁻¹D`, `integralClosure S L = N⁻¹ C_D` is module-finite over `S`. (Use
`Module.Finite` transfer: a generating set of `C_D` over `D` maps to a generating set of
`N⁻¹C_D` over `S = N⁻¹D`; cf. `Module.Finite.of_isLocalization` / scaling generators.)

Formalization route: pick `L`; introduce `K_D = FractionRing D`; transport the
`Frac(S)`-algebra and scalar-tower instances on `L` to `K_D`-algebra/scalar-tower instances
(via the fraction-field iso), establishing `FiniteDimensional K_D L`; obtain
`Module.Finite D (integralClosure D L)` from `hD`; feed this and `IsLocalization N S` into
`IsLocalization.integralClosure`/finiteness-transfer to conclude
`Module.Finite S (integralClosure S L)`. -/
theorem isN2_of_isLocalization_domain (D : Type u) [CommRing D] [IsDomain D] (N : Submonoid D)
    (S : Type u) [CommRing S] [IsDomain S] [Algebra D S] [IsLocalization N S] (hN : N ≤ D⁰)
    (hD : IsN2_032u D) : IsN2_032u S := by
  intro L _ _ _ _ _
  -- Step 1: `Frac(S)` is also a fraction field of `D`.
  have hloc :
    IsLocalization (IsLocalization.localizationLocalizationSubmodule N S⁰) (FractionRing S) :=
    IsLocalization.localization_localization_isLocalization N S⁰ (FractionRing S)
  have hDFS : IsFractionRing D (FractionRing S) := by
    apply
      isFractionRing_of_field_isLocalization D (FractionRing S)
        (IsLocalization.localizationLocalizationSubmodule N S⁰)
    rw [IsScalarTower.algebraMap_eq D S (FractionRing S)]
    exact (IsFractionRing.injective S (FractionRing S)).comp (IsLocalization.injective S hN)
  -- `D`-algebra structure on `L` via the tower `D → S → L`.
  let : Algebra D L := ((algebraMap S L).comp (algebraMap D S)).toAlgebra
  have : IsScalarTower D S L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hDFSL : IsScalarTower D (FractionRing S) L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply D S (FractionRing S), ←
      IsScalarTower.algebraMap_apply S (FractionRing S) L, ← IsScalarTower.algebraMap_apply D S L]
  -- Transport the `Frac(S)`-algebra structure to a `Frac(D)`-algebra structure via the
  -- canonical isomorphism `Frac(D) ≃ₐ[D] Frac(S)`.
  let e : FractionRing D ≃ₐ[D] FractionRing S := FractionRing.algEquiv D (FractionRing S)
  let : Algebra (FractionRing D) L := ((algebraMap (FractionRing S) L).comp e.toRingHom).toAlgebra
  have htower : IsScalarTower D (FractionRing D) L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap D L x = (algebraMap (FractionRing S) L) (e (algebraMap D (FractionRing D) x))
    rw [e.commutes x, ← IsScalarTower.algebraMap_apply D (FractionRing S) L]
  have hfd : FiniteDimensional (FractionRing D) L := by
    change Module.Finite (FractionRing D) L
    apply Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L)
    ext y
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_refl, RingHom.id_comp]
    change (algebraMap (FractionRing S) L) (e (e.symm y)) = _
    simp [AlgEquiv.apply_symm_apply]
  -- Step 2: `D` is N-2, so `integralClosure D L` is module-finite over `D`.
  have hfin : Module.Finite D (integralClosure D L) := hD L
  -- Step 3: the image of `N` in `L` consists of units, so `L` localizes at it to itself.
  have hLloc : IsLocalization (Algebra.algebraMapSubmonoid L N) L := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨n, hn, rfl⟩
    rw [IsScalarTower.algebraMap_apply D S L]
    exact (IsLocalization.map_units S ⟨n, hn⟩).map _
  -- The integral closure of `D` in `L` sits inside the integral closure of `S` in `L`.
  have hle : (integralClosure D L).toSubring ≤ (integralClosure S L).toSubring := by
    intro x hx
    simp only [Subalgebra.mem_toSubring, mem_integralClosure_iff] at *
    exact hx.tower_top
  let algIC : Algebra ↥(integralClosure D L) ↥(integralClosure S L) :=
    (Subring.inclusion hle).toAlgebra
  have : IsScalarTower (↥(integralClosure D L)) (↥(integralClosure S L)) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower D (↥(integralClosure D L)) (↥(integralClosure S L)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Step 3 (cont.): integral closure commutes with localization (Tag 0307).
  have := IsLocalization.integralClosure (R := D) (S := L) (Rf := S) (Sf := L) N
  -- Step 4: finiteness transfers to the localization.
  exact Module.Finite.of_isLocalization D (integralClosure D L) N

/-- (Stacks Tag 032U) A localization of a Nagata ring is a Nagata ring.

Here `T` is an arbitrary `R`-algebra realizing `T = M⁻¹R` for a submonoid `M ⊆ R`
(`IsLocalization M T`), which is exactly Definition 4 of a localization. The single-element
case `R_f` (`M = {1, f, f², …}`) and the prime case `R_p` (`M = R ∖ p`) are special cases.

Proof structure (Stacks: "clear from Tag 032G"):
* Noetherianity of `T` is `IsLocalization.isNoetherianRing M T hR.isNoetherianRing`.
* For a prime `q ⊆ T`, set `p := q.comap (R → T)` (prime by `Ideal.comap_isPrime`). Then
  `R/p` is N-2 (`hR.isJapaneseRing_quotient p`), and `T/q ≅ M̄⁻¹(R/p)` is a localization of the
  domain `R/p` at the image `M̄` of `M`, which lies in the nonzerodivisors of `R/p`. By
  `isN2_of_isLocalization_domain`, `T/q` is N-2. Hence `T` is Nagata. -/
@[stacks 032U, ega "IV 7.7.2"]
theorem isNagata_of_isLocalization (R : Type u) [CommRing R] (M : Submonoid R) (T : Type u)
    [CommRing T] [Algebra R T] [IsLocalization M T] (hR : IsNagataRing R) :
    IsNagataRing T := by
  refine ⟨IsLocalization.isNoetherianRing M T hR.isNoetherianRing, ?_⟩
  intro q hq
  -- Contract `q` to a prime `p` of `R`.
  set p : Ideal R := q.comap (algebraMap R T) with hp
  have hpprime : p.IsPrime := Ideal.comap_isPrime (algebraMap R T) q
  -- `R ⧸ p` is N-2 since `R` is Nagata.
  have hN2p : IsN2_032u (R ⧸ p) :=
    fun L _ _ _ _ _ => (hR.isJapaneseRing_quotient p).finite L
  -- Give `T ⧸ q` the `R ⧸ p`-algebra structure induced by `algebraMap R T` (well-defined
  -- because `p = q.comap (algebraMap R T)`, so `algebraMap R T` maps `p` into `q`).
  let : Algebra (R ⧸ p) (T ⧸ q) := (Ideal.quotientMap q (algebraMap R T) (le_refl _)).toAlgebra
  -- KEY COMMUTATION: `T ⧸ q` is the localization of `R ⧸ p` at the image `M̄` of `M`.
  -- Build via `IsLocalization.of_surjective M T (Quotient.mk p) (surj) (Quotient.mk q) (surj)`
  -- with the compatibility square `(mk q) ∘ (R→T) = (R/p → T/q) ∘ (mk p)` (holds by
  -- `Ideal.quotientMap` definition / `rfl`/`simp`) and the kernel inclusion
  -- `ker (mk q) = q ≤ map (R→T) (ker (mk p)) = map (R→T) p`. The latter holds because
  -- `q` lies over `p` in a localization: every element of `q` is, up to a unit of the image
  -- of `M`, in the image of `p` (Tag for primes of a localization, e.g. via
  -- `IsLocalization.mem_map_algebraMap_iff` / the prime correspondence
  -- `IsLocalization.orderIsoOfPrime`). This is the quotient-commutes-with-localization step.
  have hloc : IsLocalization (M.map (Ideal.Quotient.mk p)) (T ⧸ q) := by
    apply
      IsLocalization.of_surjective M T (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
        (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    · -- compatibility square
      ext x
      simp only [RingHom.comp_apply]
      exact (Ideal.quotientMap_mk).symm
    · -- kernel inclusion
      rw [Ideal.mk_ker, Ideal.mk_ker]
      have := IsLocalization.map_under M T q
      rw [← this]
  -- `M̄ = image of M` consists of nonzerodivisors of the domain `R ⧸ p`.
  -- Since `T ⧸ q` is a domain (q prime) and is the localization of `R ⧸ p` at `M̄` via the
  -- INJECTIVE map `R/p → T/q` (injective: `Ideal.quotientMap_injective`, as `p = comap`),
  -- any element of `M̄` mapping to `0` would force `0` to be a unit in the nonzero domain
  -- `T ⧸ q`, impossible; hence `M̄ ≤ (R ⧸ p)⁰`. (Equivalently: a localization map of a domain
  -- that is injective localizes at a submonoid of nonzerodivisors.)
  have hMle : M.map (Ideal.Quotient.mk p) ≤ (R ⧸ p)⁰ := by
    have : p.IsPrime := hpprime
    have : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    rw [Ideal.Quotient.eq_zero_iff_mem] at hzero
    rw [hp, Ideal.mem_comap] at hzero
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q hzero (IsLocalization.map_units T ⟨m, hm⟩))
  -- Apply the N-2 transfer lemma (Tag 032G).
  exact { finite := isN2_of_isLocalization_domain (R ⧸ p) (M.map (Ideal.Quotient.mk p))
            (T ⧸ q) hMle hN2p }

-- Correctness statement(s) characterizing the definitions.

/-- N-2 implies N-1 (take the trivial extension `L = K = Frac(R)`). This is the sanity
check noted alongside the definitions. -/
theorem isN1_of_isN2 (R : Type u) [CommRing R] [IsDomain R] (h : IsN2_032u R) : IsN1 R :=
  h (FractionRing R)
