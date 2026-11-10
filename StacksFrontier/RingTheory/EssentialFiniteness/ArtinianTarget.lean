module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.SimpleRing.Principal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ring maps into an Artinian local ring, tested on the residue field

Let `f : R → S` be a homomorphism of commutative rings with `S` an Artinian local ring with
maximal ideal `m`, and let `π : S → S/m` be the residue map. Each of the three properties
finite, of finite type, and essentially of finite type holds for `f` if and only if it holds
for the composite `π ∘ f : R → S/m`. This is Stacks tag 07DT.

The properties are Mathlib's: `f` is *finite* (`RingHom.Finite f`) if `S`, as an `R`-module via
`f`, is finitely generated; *of finite type* (`RingHom.FiniteType f`) if `S` is a finitely
generated `R`-algebra; and *essentially of finite type* (`RingHom.EssFiniteType f`) if `S` is a
localization of a finite-type `R`-subalgebra. For a local ring `S` the residue field is `S/m`,
with residue map `IsLocalRing.residue S : S →+* IsLocalRing.ResidueField S`. Locality of `S` is
`IsLocalRing S`, Artinian-ness is `IsArtinianRing S`, and `m` is `IsLocalRing.maximalIdeal S`.

The forward directions follow because the residue map `π` is surjective and each of the three
properties is preserved under composition and passes to quotients. The content is in the
reverse directions, which use that `S` is Artinian local: the maximal ideal `m` is nilpotent
and the successive quotients `m^i / m^(i+1)` are finite-dimensional `S/m`-vector spaces. That
gives a finite filtration of `S` whose graded pieces are controlled by the residue field,
transferring the finiteness property from `S/m` back to `S`.
-/

@[expose] public section

/-! ## The Artinian-local core

These three lemmas encapsulate the "transfer finiteness through the residue field" argument
that powers all the reverse directions. They are stated at the `Module`/`Algebra` level over an
arbitrary base ring `R` acting on `S` via an `Algebra R S` instance, which makes them directly
reusable with `R` replaced by a finite-type subalgebra of `S` in the finite-type and
essentially-finite-type cases. -/

open IsLocalRing in
/-- A finitely generated `S`-module annihilated by the maximal ideal is a finite
`R`-module, provided the residue field is finite over `R`. -/
private lemma finite_of_torsionBySet_maximalIdeal
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Finite R (ResidueField S)]
    (h : Module.IsTorsionBySet S N (maximalIdeal S)) : Module.Finite R N := by
  let : Module (ResidueField S) N := h.module
  have hst : IsScalarTower S (ResidueField S) N := h.isScalarTower
  have : Module.Finite (ResidueField S) N :=
    Module.Finite.of_restrictScalars_finite S (ResidueField S) N
  have : IsScalarTower R (ResidueField S) N := by
    refine ⟨fun r x n => ?_⟩
    have hx : r • x = (algebraMap R S r) • x := by
      rw [algebraMap_smul]
    rw [hx, smul_assoc, algebraMap_smul]
  exact Module.Finite.trans (ResidueField S) N

open IsLocalRing in
/-- Induction on the nilpotency power of the maximal ideal: if some power of `m`
annihilates the `S`-module `M` (which is finite over `S`), then `M` is finite
over `R`. -/
private lemma finite_of_pow_smul_eq_bot
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    [Algebra R S] [Module.Finite R (ResidueField S)] :
    ∀ (n : ℕ) (M : Type _) [AddCommGroup M] [Module R M] [Module S M]
      [IsScalarTower R S M] [Module.Finite S M],
      (maximalIdeal S) ^ n • (⊤ : Submodule S M) = ⊥ → Module.Finite R M := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _ _ h
    rw [pow_zero, Submodule.one_smul] at h
    have : Subsingleton M := ⟨fun a b => by
      have : ∀ x : M, x = 0 := fun x => (Submodule.mem_bot S).mp (h ▸ Submodule.mem_top)
      rw [this a, this b]⟩
    infer_instance
  | succ k ih =>
    intro M _ _ _ _ _ h
    set N : Submodule S M := (maximalIdeal S) • (⊤ : Submodule S M) with hN
    have : Module.Finite S N := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
    have : Module.Finite R (M ⧸ N) := by
      apply finite_of_torsionBySet_maximalIdeal R S (M ⧸ N)
      rw [Module.isTorsionBySet_iff_torsionBySet_eq_top, eq_top_iff]
      rintro q -
      induction q using Submodule.Quotient.induction_on with
      | _ a =>
        rw [Submodule.mem_torsionBySet_iff]
        rintro ⟨x, hx⟩
        have : x • a ∈ N := by
          rw [hN]
          exact Submodule.smul_mem_smul hx Submodule.mem_top
        change x • Submodule.Quotient.mk a = 0
        rw [← Submodule.Quotient.mk_smul]
        exact (Submodule.Quotient.mk_eq_zero N).mpr this
    have : Module.Finite R N := by
      refine ih N (Submodule.map_injective_of_injective (f := N.subtype) Subtype.coe_injective ?_)
      rw [Submodule.map_smul'', Submodule.map_subtype_top, Submodule.map_bot, hN,
        ← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ, h]
    exact @Module.Finite.of_submodule_quotient R M _ _ _ (N.restrictScalars R)
      ‹Module.Finite R N› ‹Module.Finite R (M ⧸ N)›

open IsLocalRing in
/-- **Crux of the reverse direction (finite case).** If `S` is Artinian local and
the residue field is finite over `R`, then `S` is a finite `R`-module. -/
private lemma finite_of_residueField_finite
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    [Algebra R S] [Module.Finite R (ResidueField S)] : Module.Finite R S := by
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal S) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  exact finite_of_pow_smul_eq_bot R S n S (by simp [hn])

/-! ## Reverse directions for finite type and essentially finite type

These are the genuine Artinian-local content beyond the finite case. Each is stated at the
`Algebra` level, so that the main theorems below reduce to them through the `f.toAlgebra`
bridge. -/

open IsLocalRing in
/-- A finite set of elements of the residue field lifts to a finite set `s ⊆ S` such that
`R[s]` is of finite type over `R` and its image in the residue field contains the
`R`-subalgebra generated by the given set. -/
lemma exists_finiteType_adjoin_le_range
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (t : Set (ResidueField S)) (ht : t.Finite) :
    ∃ s : Set S, Algebra.FiniteType R (Algebra.adjoin R s) ∧
      Algebra.adjoin R t ≤
        (IsScalarTower.toAlgHom R (Algebra.adjoin R s) (ResidueField S)).range := by
  obtain ⟨g, hg⟩ := (residue_surjective : Function.Surjective (residue S)).hasRightInverse
  refine ⟨g '' t, ⟨(Subalgebra.fg_top _).mpr (Subalgebra.fg_def.mpr ⟨_, ht.image g, rfl⟩)⟩, ?_⟩
  rw [Algebra.adjoin_le_iff]
  intro x hx
  exact ⟨⟨g x, Algebra.subset_adjoin (Set.mem_image_of_mem g hx)⟩, hg x⟩

/-- If `κ` is the localization of an `R`-subalgebra `B` at `M`, every element of `B` comes
from `A`, and the elements of `A` that become units in `κ` are already units in `T`, then
`T → κ` is surjective. -/
lemma surjective_algebraMap_of_isLocalization_of_subset_range
    {R A T κ : Type*} [CommRing R] [CommRing A] [CommRing T] [Field κ] [Algebra R κ]
    [Algebra A T] [Algebra A κ] [Algebra T κ] [IsScalarTower A T κ]
    (B : Subalgebra R κ) (M : Submonoid B) [IsLocalization M κ]
    (hB : (B : Set κ) ⊆ Set.range (algebraMap A κ))
    (hu : ∀ a : A, IsUnit (algebraMap A κ a) → IsUnit (algebraMap A T a)) :
    Function.Surjective (algebraMap T κ) := by
  intro z
  obtain ⟨⟨b, m⟩, hbm⟩ := IsLocalization.surj M z
  simp only at hbm
  have hmem : ∀ x : B, algebraMap B κ x ∈ (B : Set κ) := fun x => x.property
  obtain ⟨a₁, ha₁⟩ := hB (hmem b)
  obtain ⟨a₂, ha₂⟩ := hB (hmem m)
  have hmunit : IsUnit (algebraMap B κ (m : B)) := IsLocalization.map_units κ m
  obtain ⟨w, hw⟩ := hu a₂ (ha₂ ▸ hmunit)
  have hwκ : algebraMap T κ (↑w) = algebraMap B κ (m : B) := by
    rw [hw, ← IsScalarTower.algebraMap_apply A T κ a₂, ha₂]
  have hwκunit : IsUnit (algebraMap T κ (↑w)) := hwκ ▸ hmunit
  refine ⟨algebraMap A T a₁ * ↑w⁻¹, ?_⟩
  have hinvmul : algebraMap T κ (↑w⁻¹) * algebraMap T κ (↑w) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, ← IsScalarTower.algebraMap_apply A T κ a₁, ha₁]
  apply mul_right_cancel₀ hwκunit.ne_zero
  rw [mul_assoc, hinvmul, mul_one, hwκ, ← hbm]

open IsLocalRing in
/-- **Reverse direction, finite type.** If `S` is Artinian local and the residue
field `S/m` is of finite type over `R`, then `S` is of finite type over `R`.

Let `κ = S/m` and `π : S → κ` the residue map.  Since `κ` is of finite type
over `R`, choose finitely many elements `ȳ₁,…,ȳₙ ∈ κ` generating `κ` as an
`R`-algebra, and lift them to `y₁,…,yₙ ∈ S` (π surjective).  Let
`A := Algebra.adjoin R {y₁,…,yₙ} ⊆ S`.  Then:
  • `R → A` is of finite type (adjoin of a finite set).
  • The composite `A → S → κ` is **surjective**: its image is an `R`-subalgebra of
    `κ` containing every `ȳᵢ`, hence is all of `κ = R[ȳ₁,…,ȳₙ]`.  Concretely
    `A`, viewed as acting on `κ` through `π ∘ (A ↪ S)`, has `κ` as a cyclic
    (in fact monogenic, generated by `1`) module, so `Module.Finite A κ`
    (`Module.Finite.of_surjective (Algebra.linearMap A κ) …`).
  • `S` is Artinian local with the SAME maximal ideal `m` and residue field `κ`,
    now regarded as an `A`-algebra via `A ↪ S`.  Since `Module.Finite A κ`,
    `finite_of_residueField_finite A S` gives `Module.Finite A S`, i.e. `A → S`
    is finite, hence of finite type.
  • Compose: `R → A` finite type and `A → S` finite type ⇒ `R → S` finite type
    (`Algebra.FiniteType.trans`). -/
private lemma finiteType_of_residueField_finiteType
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    [Algebra R S] (h : Algebra.FiniteType R (ResidueField S)) :
    Algebra.FiniteType R S := by
  -- Adjoin lifts `y₁..yₙ` of the `κ`-generators to get `A ⊆ S` of finite type over `R` with
  -- `A ↠ κ`, so `Module.Finite A κ`; the crux lemma `finite_of_residueField_finite A S` then
  -- gives `Module.Finite A S`, hence `Algebra.FiniteType A S`, and we compose with
  -- `Algebra.FiniteType R A`. The reduction is to the finite-MODULE case over `A`, using that
  -- `κ` is cyclic over `A`, rather than to finiteness of the graded pieces `mⁱ/mⁱ⁺¹`.
  obtain ⟨t, htfin, htadj⟩ := Subalgebra.fg_def.mp h.out
  obtain ⟨s, hRA, hle⟩ := exists_finiteType_adjoin_le_range R S t htfin
  have hsurjA : Function.Surjective (algebraMap (Algebra.adjoin R s) (ResidueField S)) := by
    intro x
    obtain ⟨a, ha⟩ := hle (htadj ▸ Algebra.mem_top : x ∈ Algebra.adjoin R t)
    exact ⟨a, ha⟩
  have hfin : Module.Finite (Algebra.adjoin R s) (ResidueField S) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) hsurjA
  have : Module.Finite (Algebra.adjoin R s) S :=
    @finite_of_residueField_finite (Algebra.adjoin R s) S _ _ _ _ _ hfin
  exact hRA.trans (Module.Finite.finiteType S)

open IsLocalRing in
/-- **Reverse direction, essentially finite type.** If `S` is Artinian local and
the residue field `S/m` is essentially of finite type over `R`, then `S` is
essentially of finite type over `R`.

Let `κ = S/m`, `π : S → κ`.  `κ` essentially of finite type over `R` means there
is a finite subset `Σ̄ ⊆ κ` such that `κ` is the localization of the finite-type
`R`-subalgebra `R[Σ̄] ⊆ κ` at the multiplicative set of its elements that become
units in `κ` (here all nonzero elements, as `κ` is a field).  Equivalently there
are finitely many `ḡⱼ ∈ κ` and generators such that `κ = R[ȳ₁,…,ȳₙ][ḡ⁻¹]` for a
single `ḡ ≠ 0` (clearing denominators).

Lift `ȳᵢ` and `ḡ` to `y₁,…,yₙ, g ∈ S` (π surjective).  Set
`A := Algebra.adjoin R {y₁,…,yₙ, g} ⊆ S`, a finite-type `R`-subalgebra of `S`.
Let `T := localization of A at the elements of A that are units in S`; then
`R → A → T` is essentially of finite type and `T → S` is well defined (every
element of `A` inverted in `T` is already a unit in `S`).  The key claim is that
`T → S` is **finite**: indeed `T` is again local Artinian-compatible and the
composite `T → S → κ` is surjective with `κ` finite over `T`, so
`finite_of_residueField_finite T S` (after the appropriate localization
bookkeeping) yields `Module.Finite T S`, i.e. `T → S` finite, hence essentially
of finite type.  Composing the ess-finite-type maps `R → T` (localization of a
finite-type algebra) and `T → S` (finite) via `Algebra.EssFiniteType.comp` gives
`R → S` essentially of finite type.

The route taken below instead reduces to the finite-type lemma. `κ`
essentially of finite type over `R` gives a finite-type
`R`-subalgebra `B ⊆ κ` and a prime/multiplicative localization with `κ = B_𝔭`.
Pull back the localization to `S`: localizing `S` at the preimage multiplicative
set does not change `S` (every element of `S∖m` is already a unit, since `S` is
local with maximal ideal `m`).  Hence `S` itself is the localization, and the
finite-type subalgebra lifts as in `finiteType_of_residueField_finiteType`,
reducing this lemma to the finite-type case plus `Algebra.EssFiniteType.comp`
with a localization map (`Algebra.EssFiniteType.of_isLocalization`). -/
private lemma essFiniteType_of_residueField_essFiniteType
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    [Algebra R S] (h : Algebra.EssFiniteType R (ResidueField S)) :
    Algebra.EssFiniteType R S := by
  set κ := ResidueField S
  set B := Algebra.EssFiniteType.subalgebra R κ
  set M := Algebra.EssFiniteType.submonoid R κ
  have : IsLocalization M κ := Algebra.EssFiniteType.isLocalization R κ
  set fs : Set κ := ↑(Algebra.EssFiniteType.finset R κ)
  obtain ⟨s, hRA, hle⟩ :=
    exists_finiteType_adjoin_le_range R S fs (Algebra.EssFiniteType.finset R κ).finite_toSet
  set A := Algebra.adjoin R s
  have : Algebra.EssFiniteType R A := Algebra.EssFiniteType.of_finiteType R A
  set MA : Submonoid A := Submonoid.comap (A.val.toMonoidHom) (IsUnit.submonoid S)
  have hunit : ∀ y : MA, IsUnit (algebraMap A S y) := fun y =>
    (IsUnit.mem_submonoid_iff _).mp y.property
  let T := Localization MA
  let φ : T →+* S := IsLocalization.lift (g := algebraMap A S) hunit
  let : Algebra T S := φ.toAlgebra
  have hφeq : ∀ x : A, (algebraMap T S) (algebraMap A T x) = algebraMap A S x :=
    fun x => IsLocalization.lift_eq hunit x
  have hRTS : ∀ r : R, (algebraMap R S) r = (algebraMap T S) ((algebraMap R T) r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R A T r, hφeq, ← IsScalarTower.algebraMap_apply R A S r]
  have : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq hRTS
  have : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_isLocalization T MA
  have : Algebra.EssFiniteType R T := Algebra.EssFiniteType.comp R A T
  have hBrange : (B : Set κ) ⊆ Set.range (algebraMap A κ) := fun _ hx => hle hx
  have : IsScalarTower A T κ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A S κ a,
      IsScalarTower.algebraMap_apply T S κ (algebraMap A T a), hφeq a]
  have hunitlift : ∀ a : A, IsUnit (algebraMap A κ a) → IsUnit (algebraMap A T a) := by
    intro a hau
    have heq : algebraMap A κ a = residue S (algebraMap A S a) := by
      rw [IsScalarTower.algebraMap_apply A S κ a]
      rfl
    have hSunit : IsUnit (algebraMap A S a) :=
      (residue_ne_zero_iff_isUnit _).mp (heq ▸ hau.ne_zero)
    have haMA : a ∈ MA := Submonoid.mem_comap.mpr ((IsUnit.mem_submonoid_iff _).mpr hSunit)
    exact IsLocalization.map_units T (⟨a, haMA⟩ : MA)
  have hfin : Module.Finite T κ := Module.Finite.of_surjective (Algebra.linearMap T κ)
    (surjective_algebraMap_of_isLocalization_of_subset_range B M hBrange hunitlift)
  have : Module.Finite T S := finite_of_residueField_finite T S
  have : Algebra.FiniteType T S := Module.Finite.finiteType S
  have : Algebra.EssFiniteType T S := Algebra.EssFiniteType.of_finiteType T S
  exact Algebra.EssFiniteType.comp R T S

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [IsArtinianRing S]

/-- `f : R → S` is finite if and only if the composite `π ∘ f : R → S/m` is finite. -/
@[stacks 07DT "(1)"]
theorem finite_iff_residue_finite (f : R →+* S) :
    f.Finite ↔ ((IsLocalRing.residue S).comp f).Finite :=
  ⟨(RingHom.Finite.of_surjective _ IsLocalRing.residue_surjective).comp, fun h => by
    let := f.toAlgebra
    have : Module.Finite R (IsLocalRing.ResidueField S) := h
    exact (finite_of_residueField_finite R S : Module.Finite R S)⟩

/-- `f : R → S` is of finite type if and only if the composite `π ∘ f : R → S/m`
is of finite type. -/
@[stacks 07DT "(2)", ega "I 6.4.11" "special case"]
theorem finiteType_iff_residue_finiteType (f : R →+* S) :
    f.FiniteType ↔ ((IsLocalRing.residue S).comp f).FiniteType :=
  ⟨(RingHom.Finite.of_surjective _ IsLocalRing.residue_surjective).to_finiteType.comp,
    fun h => by
      let := f.toAlgebra
      exact (finiteType_of_residueField_finiteType R S h : Algebra.FiniteType R S)⟩

/-- `f : R → S` is essentially of finite type if and only if the composite
`π ∘ f : R → S/m` is essentially of finite type. -/
@[stacks 07DT "(3)", ega "I 6.4.11" "special case"]
theorem essFiniteType_iff_residue_essFiniteType (f : R →+* S) :
    f.EssFiniteType ↔ ((IsLocalRing.residue S).comp f).EssFiniteType :=
  ⟨fun h => h.comp
      (RingHom.Finite.of_surjective _ IsLocalRing.residue_surjective).to_finiteType.essFiniteType,
    fun h => by
      let := f.toAlgebra
      exact (essFiniteType_of_residueField_essFiniteType R S h : Algebra.EssFiniteType R S)⟩
