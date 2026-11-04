module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local maps essentially of finite presentation as colimits: definitions and Tag 00QT

This file holds the definitions `Algebra.EssFinitePresentation`,
`RingHom.EssFinitePresentation` and `IsLocalizationAtPrimeOfBaseChange`, and the presentation of a
local ring as a filtered colimit of local rings essentially of finite type over `ℤ`
(`tag_00QT`). It was split from
`StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation`; the remaining
parts are `QuotientColimit`, `LocalizationColimit` and `BaseChangeLocalization`.

Stacks Project Tag 00QV (Lemma 10.127.11), Commutative Algebra, Section 10.127.

Throughout, all rings are commutative with `1`, and ring homomorphisms send `1` to `1`.

Let `φ : R → S` be a local homomorphism of local rings and assume that `S` is essentially of
finite presentation over `R`. Then there exist a directed set `(Λ, ≤)` and a system of local
homomorphisms of local rings `ψ_λ : R_λ → S_λ`, with transition maps that are again local
homomorphisms, such that:

1. the colimit of the system `R_λ → S_λ` is `R → S`;
2. each `R_λ` is essentially of finite type over `ℤ`;
3. each `S_λ` is essentially of finite type over `R_λ` (via `ψ_λ`);
4. for each `λ ≤ μ` the canonical map `S_λ ⊗_{R_λ} R_μ → S_μ` presents `S_μ` as the
   localization of `S_λ ⊗_{R_λ} R_μ` at a prime ideal.

## Background

* A ring `R` is *local* if it has a unique maximal ideal `m_R`, and a ring map `φ : R → S`
  between local rings is a *local homomorphism* if `φ(m_R) ⊆ m_S`, equivalently
  `φ⁻¹(m_S) = m_R`. In Mathlib these are `IsLocalRing` and `IsLocalHom`.
* `R → S` is *essentially of finite type* if `S` is isomorphic, as an `R`-algebra, to a
  localization of an `R`-algebra of finite type (`Algebra.EssFiniteType`), and *essentially of
  finite presentation* if `S` is isomorphic to a localization of an `R`-algebra of finite
  presentation. Mathlib has only the finite-type notion, so `Algebra.EssFinitePresentation` is
  introduced here.
* A *directed set* `(Λ, ≤)` is a nonempty preorder which is directed
  (`IsDirected Λ (· ≤ ·)`); a directed system of rings is a family `(R_λ)` with transition maps
  `R_λ → R_μ` for `λ ≤ μ` satisfying the coherence conditions of `DirectedSystem`, and its
  colimit is `Ring.DirectLimit`.
* For `λ ≤ μ` the *base-change map* is the canonical `R_μ`-algebra map `S_λ ⊗_{R_λ} R_μ → S_μ`
  induced by `S_λ → S_μ` and `R_μ → S_μ`, that is, `Algebra.TensorProduct.productMap` of the
  two structure maps.
* For a ring `T` and a prime `q ⊂ T`, the *localization at `q`* is the localization at the
  multiplicative set `T ∖ q`, in Mathlib `IsLocalization.AtPrime`.

## Main definitions

* `Algebra.EssFinitePresentation` and `RingHom.EssFinitePresentation`: essentially of finite
  presentation.
* `IsLocalizationAtPrimeOfBaseChange`: condition (4) above for a single comparison `i ≤ j`.

## Main results

* `tag_00QT` (Lemma 10.127.9): every local ring is the filtered colimit of a directed system of
  local rings essentially of finite type over `ℤ`, with local transition maps.
* `main_theorem_00qv` (Lemma 10.127.11): the statement above.

In the finite-type version (Lemma 10.127.10, Tag 00QU) the transition maps present `S_μ` only as
a localization of a *quotient* of `S_λ ⊗_{R_λ} R_μ`; the stronger finite-presentation hypothesis
used here yields a localization at a prime of `S_λ ⊗_{R_λ} R_μ` itself.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.cdot false

open scoped TensorProduct

universe u


/-- An `R`-algebra `S` is *essentially of finite presentation* if `S` is
isomorphic, as an `R`-algebra, to a localization of an `R`-algebra of finite presentation.

We package this as: there is an intermediate `R`-algebra `T` of finite presentation over `R`,
together with a submonoid `M ≤ T` realizing `S` as the localization `T[M⁻¹]` (compatibly with
the `R`-algebra structures, i.e. `R → T → S` equals `R → S`). -/
def Algebra.EssFinitePresentation (R : Type u) (S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] : Prop :=
  ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S) (_ : IsScalarTower R T S),
    Algebra.FinitePresentation R T ∧ ∃ M : Submonoid T, IsLocalization M S

/-- A ring map `f : R →+* S` is *essentially of finite presentation* if `S` is essentially of
finite presentation as an `R`-algebra via `f`. -/
def RingHom.EssFinitePresentation {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.EssFinitePresentation R S

/-- Condition (4) for a single comparison `i ≤ j`: with the algebra structures coming
from the local maps `ψ_i : R_i → S_i`, the transition maps `R_i → R_j`, `S_i → S_j`, and
`ψ_j : R_j → S_j`, the canonical base-change map
`S_i ⊗_{R_i} R_j → S_j` (the `R_i`-algebra map sending `s ⊗ r ↦ (S_i → S_j)(s) · (R_j → S_j)(r)`)
presents `S_j` as the localization of `S_i ⊗_{R_i} R_j` at a prime ideal. -/
def IsLocalizationAtPrimeOfBaseChange
    {Λ : Type u} [Preorder Λ]
    {Robj : Λ → Type u} {Sobj : Λ → Type u}
    [∀ i, CommRing (Robj i)] [∀ i, CommRing (Sobj i)]
    (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
    (fS : ∀ i j, i ≤ j → Sobj i →+* Sobj j)
    (ψ : ∀ i, Robj i →+* Sobj i)
    (comm : ∀ i j (hij : i ≤ j), (ψ j).comp (fR i j hij) = (fS i j hij).comp (ψ i))
    (i j : Λ) (hij : i ≤ j) : Prop :=
  letI : Algebra (Robj i) (Sobj i) := (ψ i).toAlgebra
  letI : Algebra (Robj i) (Robj j) := (fR i j hij).toAlgebra
  letI : Algebra (Robj i) (Sobj j) := ((ψ j).comp (fR i j hij)).toAlgebra
  letI : Algebra (Sobj i) (Sobj j) := (fS i j hij).toAlgebra
  letI : Algebra (Robj j) (Sobj j) := (ψ j).toAlgebra
  haveI : IsScalarTower (Robj i) (Sobj i) (Sobj j) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      show ((ψ j).comp (fR i j hij)) x = (fS i j hij) ((ψ i) x)
      rw [comm i j hij]; rfl)
  haveI : IsScalarTower (Robj i) (Robj j) (Sobj j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the structure maps `S_i → S_j` and `R_j → S_j` as `R_i`-algebra maps
  let g1 : Sobj i →ₐ[Robj i] Sobj j := IsScalarTower.toAlgHom _ _ _
  let g2 : Robj j →ₐ[Robj i] Sobj j := IsScalarTower.toAlgHom _ _ _
  -- the canonical base-change map `S_i ⊗_{R_i} R_j → S_j`
  let can : (Sobj i) ⊗[Robj i] (Robj j) →ₐ[Robj i] Sobj j :=
    Algebra.TensorProduct.productMap g1 g2
  letI : Algebra ((Sobj i) ⊗[Robj i] (Robj j)) (Sobj j) := can.toRingHom.toAlgebra
  ∃ (p : Ideal ((Sobj i) ⊗[Robj i] (Robj j))) (_ : p.IsPrime),
    IsLocalization.AtPrime (Sobj j) p

/-!
### Outline of the argument

Since `S` is essentially of finite presentation over `R`, there is an `R`-algebra
`T = R[x₁, …, xₙ]/I` of finite presentation, with `I` generated by finitely many elements
`f₁, …, f_m`, and a prime `q ⊂ T` with `T_q ≅ S` as `R`-algebras. Write `R = colim_λ R_λ` with
each `R_λ` local and essentially of finite type over `ℤ` (Lemma 10.127.9, `tag_00QT` below).
For `λ ≥ λ₀` the generators `f_j` descend to `f_{j,λ} ∈ R_λ[x]`; put
`T_λ = R_λ[x]/(f_{j,λ})`, let `q_λ` be the preimage of `q`, and set `S_λ = (T_λ)_{q_λ}`.
Restricted to `{λ ≥ λ₀}`, the system `ψ_λ : R_λ → S_λ` is a system of local homomorphisms of
local rings satisfying (1)–(4). Condition (4) uses that base change commutes with
`R_λ[x]/(finitely generated ideal)`, so `S_λ ⊗_{R_λ} R_μ` is a localization of
`R_μ[x]/(f_{j,μ})` and localizing further at `q_μ` recovers `S_μ`.

### The colimit presentation of a local ring

For `tag_00QT` the index set is `Λ = Finset R`, the finite subsets of `R` ordered by inclusion.
For `s : Finset R`:

* `Asub R s = Subring.closure ↑s` is the finitely generated subring generated by `s`;
* `Pcon R s = (Asub R s).subtype⁻¹ 𝔪_R` is the contraction of `𝔪_R`, a prime ideal;
* `Robj R s = Localization.AtPrime (Pcon R s)` is the local ring `(A_s)_{p_s}`.

The transition maps `fR R h : Robj R s → Robj R t` for `s ≤ t` come from the subring inclusion
`Ainc R h : A_s ↪ A_t` together with the contraction-compatibility `Pcon_comap`. The statement
is then assembled from `Pcon_comap`, `fR_directedSystem`, `fR_isLocalHom`,
`Robj_essFiniteType`, the colimit isomorphism `colimEquiv : colim_s Robj R s ≃+* R`, and
`colimEquiv_isLocalHom`.
-/

namespace Stacks.EssentialFiniteness.LocalRingColimit

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The finitely-generated subring of `R` generated by a finite set `s`. -/
def Asub (s : Finset R) : Subring R := Subring.closure (s : Set R)

/-- The contraction of `𝔪_R` to `Asub R s`, a prime ideal. -/
def Pcon (s : Finset R) : Ideal (Asub R s) :=
  Ideal.comap (Asub R s).subtype (IsLocalRing.maximalIdeal R)

/-- `Pcon R s` is a prime ideal, being the contraction of a prime ideal. -/
instance Pcon_isPrime (s : Finset R) : (Pcon R s).IsPrime :=
  Ideal.comap_isPrime _ _

/-- The local ring `R_s = (A_s)_{p_s}`. -/
def Robj (s : Finset R) : Type u := Localization.AtPrime (Pcon R s)

/-- The commutative ring structure on `Robj R s`, that of the localization `(A_s)_{p_s}`. -/
noncomputable instance (s : Finset R) : CommRing (Robj R s) :=
  inferInstanceAs (CommRing (Localization.AtPrime (Pcon R s)))

/-- `Robj R s` is a local ring, being a localization at a prime ideal. -/
instance (s : Finset R) : IsLocalRing (Robj R s) :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime (Pcon R s)))

/-- For `s ⊆ t`, the inclusion of subrings `A_s ↪ A_t`. -/
def Ainc {s t : Finset R} (h : s ≤ t) : Asub R s →+* Asub R t :=
  Subring.inclusion (Subring.closure_mono (by exact_mod_cast Finset.coe_subset.mpr h))

/-- Contraction compatibility: `p_s = (A_s ↪ A_t)⁻¹ p_t`, since both ideals equal
`A_s ∩ 𝔪_R`. -/
lemma Pcon_comap {s t : Finset R} (h : s ≤ t) :
    Pcon R s = Ideal.comap (Ainc R h) (Pcon R t) := by
  ext a
  simp only [Pcon, Ideal.mem_comap, Subring.coe_subtype]
  rw [show ((Ainc R h a : Asub R t) : R) = (a : R) from Subring.coe_inclusion _ a]

/-- The transition map `R_s → R_t` for `s ≤ t` (localization of the subring inclusion). -/
noncomputable def fR {s t : Finset R} (h : s ≤ t) : Robj R s →+* Robj R t :=
  Localization.localRingHom (Pcon R s) (Pcon R t) (Ainc R h) (Pcon_comap R h)

private noncomputable instance (s : Finset R) : Algebra (Asub R s) (Robj R s) :=
  inferInstanceAs (Algebra (Asub R s) (Localization.AtPrime (Pcon R s)))

private instance (s : Finset R) : IsLocalization (Pcon R s).primeCompl (Robj R s) :=
  inferInstanceAs (IsLocalization (Pcon R s).primeCompl (Localization.AtPrime (Pcon R s)))

/-- `fR h ∘ ℓ_s = ℓ_t ∘ (A_s ↪ A_t)`: `fR` intertwines the localization maps. -/
private theorem fR_algebraMap {s t : Finset R} (h : s ≤ t) (a : Asub R s) :
    fR R h (algebraMap (Asub R s) (Robj R s) a)
      = algebraMap (Asub R t) (Robj R t) (Ainc R h a) :=
  Localization.localRingHom_to_map (Pcon R s) (Pcon R t) (Ainc R h) (Pcon_comap R h) a

/-- The transition maps `fR` form a `DirectedSystem`: functoriality of
`Localization.localRingHom` together with the fact that the subring inclusions `Ainc` compose to
inclusions and that `Ainc _ (le_refl _)` is the identity. -/
lemma fR_directedSystem :
    DirectedSystem (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) := by
  refine ⟨fun i x => ?_, fun {i j k} hij hjk x => ?_⟩
  · -- `map_self`: `fR (le_refl i) = id`, proven by agreement on the localization map.
    have hmap : fR R (le_refl i) = RingHom.id (Robj R i) := by
      apply IsLocalization.ringHom_ext (Pcon R i).primeCompl
      apply RingHom.ext; intro a
      show fR R (le_refl i) (algebraMap (Asub R i) (Robj R i) a)
          = RingHom.id (Robj R i) (algebraMap (Asub R i) (Robj R i) a)
      have hAinc : Ainc R (le_refl i) a = a := Subtype.ext (Subring.coe_inclusion _ a)
      rw [fR_algebraMap, hAinc, RingHom.id_apply]
    have := DFunLike.congr_fun hmap x
    simpa using this
  · -- `map_map`: `fR hjk ∘ fR hij = fR (le_trans hij hjk)`, by agreement on the localization map.
    have hmap : (fR R hjk).comp (fR R hij) = fR R (le_trans hij hjk) := by
      apply IsLocalization.ringHom_ext (Pcon R k).primeCompl
      apply RingHom.ext; intro a
      show (fR R hjk) (fR R hij (algebraMap (Asub R k) (Robj R k) a))
          = fR R (le_trans hij hjk) (algebraMap (Asub R k) (Robj R k) a)
      have hAinc : Ainc R hjk (Ainc R hij a) = Ainc R (le_trans hij hjk) a :=
        Subtype.ext ((Subring.coe_inclusion _ (Ainc R hij a)).trans
          ((Subring.coe_inclusion _ a).trans (Subring.coe_inclusion _ a).symm))
      rw [fR_algebraMap, fR_algebraMap, fR_algebraMap, hAinc]
    have := DFunLike.congr_fun hmap x
    simpa using this

/-- Each transition map `fR R h` is a local homomorphism: it is the `localRingHom` of the
inclusion `Ainc R h` for the contraction-compatible primes `p_s`, `p_t`, and the preimage of the
maximal ideal of `(A_t)_{p_t}` is the maximal ideal of `(A_s)_{p_s}`. -/
lemma fR_isLocalHom {s t : Finset R} (h : s ≤ t) : IsLocalHom (fR R h) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (Pcon R s).primeCompl x
  rw [IsLocalization.AtPrime.isUnit_mk'_iff (Robj R s) (Pcon R s) n d]
  have hmem_iff : ∀ a : Asub R s, a ∈ Pcon R s ↔ Ainc R h a ∈ Pcon R t := by
    intro a
    rw [Pcon_comap R h, Ideal.mem_comap]
  have hd : Ainc R h (d : Asub R s) ∈ (Pcon R t).primeCompl := by
    intro hc
    exact d.property ((hmem_iff (d : Asub R s)).mpr hc)
  have hval : fR R h (IsLocalization.mk' (Robj R s) n d)
      = IsLocalization.mk' (Robj R t) (Ainc R h n) ⟨Ainc R h d, hd⟩ := by
    rw [fR]
    exact Localization.localRingHom_mk' (Pcon R s) (Pcon R t) (Ainc R h) (Pcon_comap R h) n d
  rw [hval,
    IsLocalization.AtPrime.isUnit_mk'_iff (Robj R t) (Pcon R t) (Ainc R h n) ⟨Ainc R h d, hd⟩]
      at hx
  intro hmem
  exact hx ((hmem_iff n).mp hmem)

/-- Each `Robj R s` is essentially of finite type over `ℤ`: the subring
`Asub R s = Subring.closure ↑s` is of finite type over `ℤ` because `s` is finite, and
`Robj R s = Localization.AtPrime (Pcon R s)` is a localization of `Asub R s`. -/
lemma Robj_essFiniteType (s : Finset R) : Algebra.EssFiniteType ℤ (Robj R s) := by
  -- Step 1: `Asub R s = Subring.closure ↑s` is of finite type over ℤ.
  have hFT : Algebra.FiniteType ℤ (Asub R s) := by
    have hFG : (Algebra.adjoin ℤ (s : Set R)).FG := ⟨s, rfl⟩
    rw [Subalgebra.fg_iff_finiteType, Algebra.adjoin_int] at hFG
    exact hFG
  have : Algebra.FiniteType ℤ (Asub R s) := hFT
  -- hence essentially of finite type over ℤ.
  have hZA : Algebra.EssFiniteType ℤ (Asub R s) :=
    Algebra.EssFiniteType.of_finiteType ℤ (Asub R s)
  -- Step 2: `Robj R s = Localization.AtPrime (Pcon R s)` is a localization of `Asub R s`.
  have hAR : Algebra.EssFiniteType (Asub R s) (Robj R s) :=
    Algebra.EssFiniteType.of_isLocalization (Robj R s) (Pcon R s).primeCompl
  -- Step 3: the ℤ-scalar tower (both ℤ-algebra maps are `Int.cast`).
  have : IsScalarTower ℤ (Asub R s) (Robj R s) :=
    IsScalarTower.of_algebraMap_eq (fun n => by simp)
  -- Step 4: compose.
  exact (Algebra.EssFiniteType.comp_iff ℤ (Asub R s) (Robj R s)).mpr hAR

/-! ### The colimit isomorphism `colim_s (A_s)_{p_s} ≃+* R` -/

/-- The canonical `Asub R s`-algebra structure on `Robj R s` (it is `Localization.AtPrime`). -/
noncomputable instance Robj_algebra (s : Finset R) : Algebra (Asub R s) (Robj R s) :=
  inferInstanceAs (Algebra (Asub R s) (Localization.AtPrime (Pcon R s)))

/-- `Robj R s` is the localization of `Asub R s` at the prime `Pcon R s`. -/
instance Robj_isLocalization (s : Finset R) :
    IsLocalization (Pcon R s).primeCompl (Robj R s) :=
  inferInstanceAs (IsLocalization (Pcon R s).primeCompl (Localization.AtPrime (Pcon R s)))

/-- The inclusion `A_s ↪ A_t` is compatible with the ambient inclusions into `R`. -/
lemma Ainc_apply_coe {s t : Finset R} (h : s ≤ t) (a : Asub R s) :
    ((Ainc R h a : Asub R t) : R) = (a : R) := by
  rw [Ainc]
  exact Subring.coe_inclusion _ a

/-- Each element of `M_s = A_s ∖ p_s` maps to a unit of `R`: in a local ring `x` is a unit iff
`x ∉ 𝔪_R`, and `b ∈ (Pcon R s).primeCompl` means `(b : R) ∉ 𝔪_R`. -/
lemma gR_unit (s : Finset R) (b : (Pcon R s).primeCompl) :
    IsUnit ((Asub R s).subtype (b : Asub R s)) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hb
  exact b.property (Ideal.mem_comap.mpr hb)

/-- The localization-lift `g_s : R_s → R` of the subring inclusion `(Asub R s).subtype`. -/
noncomputable def gR (s : Finset R) : Robj R s →+* R :=
  IsLocalization.lift (M := (Pcon R s).primeCompl) (g := (Asub R s).subtype)
    (fun y => gR_unit R s y)

/-- `g_s ∘ ℓ_s = ι_s`: on the image of `algebraMap`, `g_s` is the subring inclusion. -/
lemma gR_lift_eq (s : Finset R) (a : Asub R s) :
    gR R s (algebraMap (Asub R s) (Robj R s) a) = (a : R) := by
  rw [gR]
  exact IsLocalization.lift_eq _ a

/-- `f^R_{st} ∘ ℓ_s = ℓ_t ∘ (A_s ↪ A_t)`: the transition map intertwines the localization maps. -/
lemma fR_comp_algebraMap {s t : Finset R} (h : s ≤ t) (a : Asub R s) :
    fR R h (algebraMap (Asub R s) (Robj R s) a)
      = algebraMap (Asub R t) (Robj R t) (Ainc R h a) :=
  fR_algebraMap R h a

/-- Cocone compatibility: `g_t ∘ f^R_{st} = g_s` (uniqueness in the universal property of
localization, reduced to the subring inclusions composing). -/
lemma gR_compat {s t : Finset R} (h : s ≤ t) : (gR R t).comp (fR R h) = gR R s := by
  apply IsLocalization.ringHom_ext (Pcon R s).primeCompl
  apply RingHom.ext
  intro a
  show (gR R t) (fR R h (algebraMap (Asub R s) (Robj R s) a)) = gR R s (algebraMap _ _ a)
  rw [fR_comp_algebraMap, gR_lift_eq, gR_lift_eq, Ainc_apply_coe]

/-- Each `g_s` is injective: by `IsLocalization.lift_injective_iff` it reduces to the injectivity
of the subring inclusion `(Asub R s).subtype`. -/
lemma gR_injective (s : Finset R) : Function.Injective (gR R s) := by
  rw [gR, IsLocalization.lift_injective_iff]
  intro x y
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (gR R s) h
    rw [gR_lift_eq, gR_lift_eq] at this
    exact this
  · rw [Subtype.val_injective h]

/-- The induced map `Φ : colim_s R_s → R` from the compatible family `(g_s)`. -/
noncomputable def Phi :
    Ring.DirectLimit (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) →+* R :=
  Ring.DirectLimit.lift (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) R (gR R)
    (fun s t h x => congrFun (congrArg DFunLike.coe (gR_compat R h)) x)

/-- `Φ ∘ (of s) = g_s`. -/
lemma Phi_of (s : Finset R) (x : Robj R s) :
    Phi R (Ring.DirectLimit.of (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) s x)
      = gR R s x := by
  rw [Phi]
  exact Ring.DirectLimit.lift_of _ _ _ _ _

/-- `Φ` is surjective: `r = Φ (of {r} (ℓ ⟨r, _⟩))` since `r ∈ Asub R {r}`. -/
lemma Phi_surjective : Function.Surjective (Phi R) := by
  intro r
  refine ⟨Ring.DirectLimit.of (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) {r}
    (algebraMap (Asub R {r}) (Robj R {r}) ⟨r, Subring.subset_closure (by simp)⟩), ?_⟩
  rw [Phi_of, gR_lift_eq]

/-- `Φ` is injective: every element is `of s x`; `Φ (of s x) = g_s x` and each `g_s` is injective,
so `Φ z = 0` forces `x = 0`, hence `z = of s 0 = 0`. -/
lemma Phi_injective : Function.Injective (Phi R) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨s, x, rfl⟩ := Ring.DirectLimit.exists_of z
  rw [Phi_of] at hz
  have hx : x = 0 := gR_injective R s (by rw [hz, map_zero])
  rw [hx, map_zero]

/-- The direct limit of the system `(Robj R s, fR)` is isomorphic to `R`.

For each `s` the inclusion `(Asub R s).subtype : Asub R s →+* R` sends `M_s = A_s ∖ p_s` into the
units of `R`, since in a local ring `x` is a unit exactly when `x ∉ 𝔪_R`, so the universal
property of the localization gives `g_s : Robj R s →+* R` with `g_s ∘ ℓ_s = subtype`. The `g_s`
are compatible with the transition maps and hence induce `Φ : colim → R`, which is:

* surjective, because `r = g_{​{r}} (ℓ ⟨r, _⟩)` as `r ∈ Asub R {r}`;
* injective, because every element of the colimit is of the form `of s x`, and
  `g_s (ℓ_s a) = (a : R)` with `(Asub R s).subtype` injective, so `Φ (of s x) = 0` forces
  `x = 0`. -/
@[ega "IV 5.13.3" "(iii), special case"]
noncomputable def colimEquiv :
    Ring.DirectLimit (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) ≃+* R :=
  RingEquiv.ofBijective (Phi R) ⟨Phi_injective R, Phi_surjective R⟩

/-- `g_s : R_s → R` is a local homomorphism: its preimage of `𝔪_R` is
`p_s · (A_s)_{p_s} = IsLocalRing.maximalIdeal (Robj R s)`, because `p_s = A_s ∩ 𝔪_R`. -/
lemma gR_isLocalHom (s : Finset R) : IsLocalHom (gR R s) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (Pcon R s).primeCompl x
  rw [IsLocalization.AtPrime.isUnit_mk'_iff (Robj R s) (Pcon R s) n d]
  rw [gR, IsLocalization.lift_mk'] at hx
  have hn : IsUnit ((Asub R s).subtype n) := (IsUnit.mul_iff.mp hx).left
  intro hmem
  rw [← IsLocalRing.notMem_maximalIdeal] at hn
  exact hn hmem

/-- Each structural map `Robj R s → colim → R` of the colimit presentation is a local
homomorphism; it agrees with `gR R s`. -/
lemma colimEquiv_isLocalHom (s : Finset R) :
    IsLocalHom (((colimEquiv R).toRingHom).comp
      (Ring.DirectLimit.of (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) s)) := by
  refine ⟨fun x hx => ?_⟩
  have hcomp : (((colimEquiv R).toRingHom).comp
      (Ring.DirectLimit.of (Robj R) (fun s t h => (fR R h : Robj R s → Robj R t)) s)) x
      = gR R s x := by
    show (colimEquiv R) (Ring.DirectLimit.of (Robj R)
      (fun s t h => (fR R h : Robj R s → Robj R t)) s x) = gR R s x
    exact Phi_of R s x
  rw [hcomp] at hx
  exact (gR_isLocalHom R s).map_nonunit x hx

end Stacks.EssentialFiniteness.LocalRingColimit

/-- **Stacks Tag 00QT (Lemma 10.127.9).** Every local ring `R` is a filtered colimit of a
directed system of local rings `R_λ`, each essentially of finite type over `ℤ`, with *local*
transition maps, such that the colimit recovers `R`.

Index `Λ` by pairs `(A, p)` where `A ⊆ R` is a subring
generated over `ℤ` by finitely many elements (so `A` is of finite type over `ℤ`, hence `A` is
Noetherian) and `p = A ∩ 𝔪_R` is the (prime) contraction of the maximal ideal of `R`; set
`R_{(A,p)} = A_p`, the localization of `A` at `p`, which is a local ring essentially of finite
type over `ℤ`, with `IsLocalRing.maximalIdeal = p·A_p`. Order by inclusion of subrings (with the
compatible localization maps `A_p → B_q` for `A ⊆ B`, `q = B ∩ 𝔪_R ⊇ p`). The set of finitely
generated subrings of `R` is directed (the subring generated by `A ∪ B` dominates both) and its
union is `R` (`Subring.closure` of any finite set is finite type; every element lies in some such
subring), so `colim_λ A_λ = R`. Localization is exact / commutes with filtered colimits, and the
contractions `p_λ` are compatible, so `colim_λ (A_λ)_{p_λ} = R_{𝔪_R} = R` (as `R` is already
local). Each transition map `(A_λ)_{p_λ} → (A_μ)_{p_μ}` is local because `p_μ ∩ A_λ = p_λ`, and
the colimit map to `R` is local because `p_λ = A_λ ∩ 𝔪_R`. -/
@[sga "3 X 4.4" "partial"]
theorem tag_00QT (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Robj : Λ → Type u) (_ : ∀ i, CommRing (Robj i)) (_ : ∀ i, IsLocalRing (Robj i))
      (fR : ∀ i j, i ≤ j → Robj i →+* Robj j),
      (DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j))) ∧
      (∀ i j (hij : i ≤ j), IsLocalHom (fR i j hij)) ∧
      (∀ i, Algebra.EssFiniteType ℤ (Robj i)) ∧
      (∃ (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R),
        ∀ i, IsLocalHom ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i))) := by
  -- Assemble from the `Stacks.EssentialFiniteness.LocalRingColimit` decomposition above:
  -- Λ = `Finset R`, `Robj`/`fR` as defined, and the six sub-lemmas; the colimit isomorphism is
  -- `Stacks.EssentialFiniteness.LocalRingColimit.colimEquiv`.
  exact
    ⟨Finset R, inferInstance, ⟨∅⟩, inferInstance, Stacks.EssentialFiniteness.LocalRingColimit.Robj
      R, inferInstance,
    inferInstance, fun s t h => Stacks.EssentialFiniteness.LocalRingColimit.fR R h,
      Stacks.EssentialFiniteness.LocalRingColimit.fR_directedSystem R,
    fun s t h => Stacks.EssentialFiniteness.LocalRingColimit.fR_isLocalHom R h,
      Stacks.EssentialFiniteness.LocalRingColimit.Robj_essFiniteType R,
    Stacks.EssentialFiniteness.LocalRingColimit.colimEquiv R,
      Stacks.EssentialFiniteness.LocalRingColimit.colimEquiv_isLocalHom R⟩

end
