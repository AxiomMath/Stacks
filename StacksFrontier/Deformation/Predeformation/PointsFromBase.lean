module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts

/-!
# Points of a complete local algebra whose adic truncations come from the base

Let `Λ` be a local ring with residue field identified with `k`, and let `R` be an object of
`\widehat{𝒞}_Λ` with the property that `Λ` induces an isomorphism
`Λ ⧸ 𝔪_Λ ^ n ≅ R ⧸ 𝔪_Λ ^ n R` on every adic truncation — `HasBaseTruncations` below. Then for
every `A` in `𝒞_Λ` there is exactly one point `R ⟶ A`: the maximal ideal of `A` is nilpotent,
so a point must kill `𝔪_Λ ^ n R` for `n` large, and `Λ` surjects onto the quotient by that
ideal, which pins the point down and also builds it.

## Why this is stated in this generality

The hypothesis is the only thing the proof uses, and it is satisfied by `Λ` itself, by the
`𝔪_Λ`-adic completion of `Λ`, and by every quotient of either. Nothing in the argument is
special to the completion.

The statement matters because `Deformation.restrictedRepresentableMap_isSmooth_iff_projection`
carries exactly this conclusion as an unfilled hypothesis, so every caller of that lemma needs
an instance of it. The only proof of it in this repository is private and covers only the case
`L ≅ Λ` — it is built for `L := Shrink Λ` with `e : Shrink Λ ≃ₐ[Λ] Λ` inside the private
`Deformation.smooth_iff_powerSeries_of_small_base` — and that argument cannot reach a
completion, since a Noetherian local ring is not in general isomorphic to its completion.

Note also what is *not* enough for this: `Deformation.exists_factorThroughAdicTruncation`
factors a point one already has through an adic truncation, and
`Deformation.factorThroughAdicTruncation_unique` says that factorization is unique. Neither
produces a point of `R` at a given `A`, which is what a lifting argument needs.

## Main definitions

* `Deformation.HasBaseTruncations`: `Λ ⧸ 𝔪_Λ ^ n ≅ R ⧸ 𝔪_Λ ^ n R` for every `n`.

## Main results

* `Deformation.nonempty_subsingleton_hom_of_hasBaseTruncations`: there is exactly one point
  `R ⟶ A` for every `A` in `𝒞_Λ`.
* `Deformation.residueEquiv_algebraMap` and
  `Deformation.isLocalHom_algebraMap_of_residueEquiv`: the two facts about residue-field
  identifications the proof needs, which exist in this repository only as private lemmas of
  `StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra`.
-/

@[expose] public noncomputable section

namespace Deformation

open CategoryTheory IsLocalRing

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue-field identification of a local `Λ`-algebra sends the residue of a scalar to
its image in `k`. -/
public theorem residueEquiv_algebraMap {R : Type v} [CommRing R] [Algebra Λ R] [IsLocalRing R]
    (e : ResidueField R ≃ₐ[Λ] k) (a : Λ) :
    e (residue R (algebraMap Λ R a)) = algebraMap Λ k a := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply Λ R (ResidueField R)]
  exact e.commutes a

/-- The structure morphism of a local `Λ`-algebra whose residue field is identified with `k`,
over a local `Λ` whose residue field is identified with `k`, is a local homomorphism. -/
public theorem isLocalHom_algebraMap_of_residueEquiv [IsLocalRing Λ] {A : Type v} [CommRing A]
    [IsLocalRing A] [Algebra Λ A] (eΛ : ResidueField Λ ≃ₐ[Λ] k)
    (eA : ResidueField A ≃ₐ[Λ] k) : IsLocalHom (algebraMap Λ A) := by
  refine ⟨fun a ha => ?_⟩
  apply (residue_ne_zero_iff_isUnit a).mp
  intro hz
  have hzero : algebraMap Λ k a = 0 := by
    rw [← residueEquiv_algebraMap eΛ a]
    simpa using congrArg eΛ hz
  have hzA : residue A (algebraMap Λ A a) = 0 := by
    apply eA.injective
    simpa only [map_zero, residueEquiv_algebraMap] using hzero
  exact (residue_ne_zero_iff_isUnit _).mpr ha hzA

variable [IsLocalRing Λ]

/-- **The base induces an isomorphism on every adic truncation.** For an object `R` of
`\widehat{𝒞}_Λ`, the canonical map `Λ ⧸ 𝔪_Λ ^ n → R ⧸ 𝔪_Λ ^ n R` is bijective for every `n`. -/
public def HasBaseTruncations (R : CompleteLocalAlgCat.{u, v, w} Λ k) : Prop :=
  ∀ n : ℕ, Function.Bijective
    (IsScalarTower.toAlgHom Λ (Λ ⧸ maximalIdeal Λ ^ n)
      (R ⧸ Ideal.map (algebraMap Λ R) (maximalIdeal Λ ^ n)))

section

variable (eΛ : ResidueField Λ ≃ₐ[Λ] k) (R : CompleteLocalAlgCat.{u, v, w} Λ k)
  (A : ArtinianLocalAlgCat.{u, v, w} Λ k)

/-- The image of a power of `𝔪_Λ` lies in the same power of the maximal ideal of a local
`Λ`-algebra with local structure map. -/
private theorem map_pow_maximalIdeal_le {S : Type v} [CommRing S] [IsLocalRing S] [Algebra Λ S]
    [IsLocalHom (algebraMap Λ S)] (N : ℕ) :
    Ideal.map (algebraMap Λ S) (maximalIdeal Λ ^ N) ≤ maximalIdeal S ^ N := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (algebraMap Λ S)) _

include eΛ in
/-- The image of a high enough power of `𝔪_Λ` in an Artinian local `Λ`-algebra vanishes. -/
private theorem exists_map_pow_eq_bot :
    ∃ N : ℕ, 1 ≤ N ∧ Ideal.map (algebraMap Λ A) (maximalIdeal Λ ^ N) = ⊥ := by
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_eq_bot A
  have : IsLocalHom (algebraMap Λ (A : Type v)) :=
    isLocalHom_algebraMap_of_residueEquiv eΛ A.residueEquiv
  exact ⟨n + 1, Nat.le_add_left 1 n,
    le_antisymm (hn ▸ map_pow_maximalIdeal_le (S := (A : Type v)) _) bot_le⟩

/-- Every element of `R` differs from a scalar by an element of `𝔪_Λ ^ N R`. -/
private theorem exists_sub_mem_of_hasBaseTruncations (hR : HasBaseTruncations R) (N : ℕ)
    (x : R) : ∃ a : Λ, x - algebraMap Λ R a ∈
      Ideal.map (algebraMap Λ R) (maximalIdeal Λ ^ N) := by
  obtain ⟨z, hz⟩ := (hR N).2 (Ideal.Quotient.mk _ x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact hz.symm

include eΛ in
private theorem map_pow_le_maximalIdeal {N : ℕ} (hN : 1 ≤ N) :
    Ideal.map (algebraMap Λ R) (maximalIdeal Λ ^ N) ≤ maximalIdeal R := by
  have : IsLocalHom (algebraMap Λ (R : Type v)) :=
    isLocalHom_algebraMap_of_residueEquiv eΛ R.residueEquiv
  exact (map_pow_maximalIdeal_le (S := (R : Type v)) N).trans (Ideal.pow_le_self (by omega))

/-- Once `𝔪_Λ ^ N` vanishes in `A`, a `Λ`-algebra map `R → A` takes the value of a scalar on
every element congruent to it modulo `𝔪_Λ ^ N R`. -/
private theorem algHom_apply_eq_of_sub_mem {N : ℕ}
    (hN : Ideal.map (algebraMap Λ (A : Type v)) (maximalIdeal Λ ^ N) = ⊥)
    (f : R →ₐ[Λ] (A : Type v)) {x : R} {a : Λ}
    (hx : x - algebraMap Λ R a ∈ Ideal.map (algebraMap Λ R) (maximalIdeal Λ ^ N)) :
    f x = algebraMap Λ (A : Type v) a := by
  have hle : Ideal.map (algebraMap Λ R) (maximalIdeal Λ ^ N) ≤
      RingHom.ker (f : R →+* (A : Type v)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change f (algebraMap Λ R b) = 0
    rw [f.commutes b]
    exact Ideal.mem_bot.mp (hN ▸ Ideal.mem_map_of_mem (algebraMap Λ (A : Type v)) hb)
  have h : f (x - algebraMap Λ R a) = 0 := hle hx
  rwa [map_sub, sub_eq_zero, f.commutes a] at h

include eΛ in
/-- Every `Λ`-algebra map from `R` to an Artinian local `Λ`-algebra is local, as soon as `Λ`
induces an isomorphism on the adic truncations of `R`. -/
private theorem isLocalHom_of_hasBaseTruncations (hR : HasBaseTruncations R)
    (f : R →ₐ[Λ] (A : Type v)) : IsLocalHom f.toRingHom := by
  obtain ⟨N, hN1, hNbot⟩ := exists_map_pow_eq_bot eΛ A
  have : IsLocalHom (algebraMap Λ (A : Type v)) :=
    isLocalHom_algebraMap_of_residueEquiv eΛ A.residueEquiv
  have : IsLocalHom (algebraMap Λ (R : Type v)) :=
    isLocalHom_algebraMap_of_residueEquiv eΛ R.residueEquiv
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  obtain ⟨a, ha⟩ := exists_sub_mem_of_hasBaseTruncations R hR N x
  have ham : algebraMap Λ R a ∈ maximalIdeal R := by
    rw [show algebraMap Λ R a = x - (x - algebraMap Λ R a) by ring]
    exact Ideal.sub_mem _ ((mem_maximalIdeal x).mpr hxu) (map_pow_le_maximalIdeal eΛ R hN1 ha)
  have haΛ : a ∈ maximalIdeal Λ := (mem_maximalIdeal a).mpr fun hu =>
    mem_nonunits_iff.mp ham (hu.map (algebraMap Λ (R : Type v)))
  have hxu' : IsUnit (f x) := hx
  rw [algHom_apply_eq_of_sub_mem R A hNbot f ha] at hxu'
  exact mem_nonunits_iff.mp
    (IsLocalRing.map_maximalIdeal_le (algebraMap Λ (A : Type v))
      (Ideal.mem_map_of_mem _ haΛ)) hxu'

include eΛ in
/-- Every `Λ`-algebra map from `R` to an Artinian local `Λ`-algebra is compatible with the
identifications of the residue fields, as soon as `Λ` induces an isomorphism on the adic
truncations of `R`. -/
private theorem residue_comm_of_hasBaseTruncations (hR : HasBaseTruncations R)
    (f : R →ₐ[Λ] (A : Type v)) (x : R) :
    (artinianToComplete.obj A).residueEquiv (residue _ (f x)) =
      R.residueEquiv (residue R x) := by
  obtain ⟨N, hN1, hNbot⟩ := exists_map_pow_eq_bot eΛ A
  obtain ⟨a, ha⟩ := exists_sub_mem_of_hasBaseTruncations R hR N x
  have hres : residue R x = residue R (algebraMap Λ R a) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr (map_pow_le_maximalIdeal eΛ R hN1 ha)
  rw [algHom_apply_eq_of_sub_mem R A hNbot f ha, hres]
  exact (residueEquiv_algebraMap (artinianToComplete.obj A).residueEquiv a).trans
    (residueEquiv_algebraMap R.residueEquiv a).symm

include eΛ in
/-- There is a point of `R` at every Artinian local `Λ`-algebra, as soon as `Λ` induces an
isomorphism on the adic truncations of `R`. -/
private theorem nonempty_hom_of_hasBaseTruncations (hR : HasBaseTruncations R) :
    Nonempty (R ⟶ artinianToComplete.obj A) := by
  obtain ⟨N, -, hNbot⟩ := exists_map_pow_eq_bot eΛ A
  have hzero : ∀ a : Λ, a ∈ maximalIdeal Λ ^ N → algebraMap Λ (A : Type v) a = 0 := fun a ha =>
    Ideal.mem_bot.mp (hNbot ▸ Ideal.mem_map_of_mem (algebraMap Λ (A : Type v)) ha)
  let J : Ideal R := Ideal.map (algebraMap Λ R) (maximalIdeal Λ ^ N)
  let e : (Λ ⧸ maximalIdeal Λ ^ N) ≃ₐ[Λ] (R ⧸ J) := AlgEquiv.ofBijective _ (hR N)
  let q : (Λ ⧸ maximalIdeal Λ ^ N) →ₐ[Λ] (A : Type v) :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId Λ (A : Type v)) hzero
  let hom : R →ₐ[Λ] (A : Type v) := q.comp (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Λ J))
  exact ⟨{ hom := hom
           isLocal := isLocalHom_of_hasBaseTruncations eΛ R A hR hom
           residue_comm := residue_comm_of_hasBaseTruncations eΛ R A hR hom }⟩

include eΛ in
/-- There is at most one point of `R` at every Artinian local `Λ`-algebra, as soon as `Λ`
induces an isomorphism on the adic truncations of `R`. -/
private theorem subsingleton_hom_of_hasBaseTruncations (hR : HasBaseTruncations R) :
    Subsingleton (R ⟶ artinianToComplete.obj A) := by
  obtain ⟨N, -, hNbot⟩ := exists_map_pow_eq_bot eΛ A
  refine ⟨fun f g => CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun x => ?_)⟩
  obtain ⟨a, ha⟩ := exists_sub_mem_of_hasBaseTruncations R hR N x
  rw [algHom_apply_eq_of_sub_mem R A hNbot f.hom ha, algHom_apply_eq_of_sub_mem R A hNbot g.hom ha]

end

/-- **There is exactly one point of `R` at every Artinian local `Λ`-algebra**, as soon as `Λ`
induces an isomorphism on the adic truncations of `R`. The maximal ideal of `A` is nilpotent,
so the image of `𝔪_Λ ^ N` in `A` vanishes for some `N`; a point of `R` therefore kills
`𝔪_Λ ^ N R`, and `Λ` surjects onto `R ⧸ 𝔪_Λ ^ N R`, which both pins the point down and
constructs it. -/
public theorem nonempty_subsingleton_hom_of_hasBaseTruncations
    (eΛ : ResidueField Λ ≃ₐ[Λ] k) (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hR : HasBaseTruncations R) (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    Nonempty (R ⟶ artinianToComplete.obj A) ∧
      Subsingleton (R ⟶ artinianToComplete.obj A) :=
  ⟨nonempty_hom_of_hasBaseTruncations eΛ R A hR, subsingleton_hom_of_hasBaseTruncations eΛ R A hR⟩

end Deformation

end
