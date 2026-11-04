module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import StacksFrontier.RingTheory.CompleteLocalRing.AdicIsoCriterion

/-!
# Sections of a monomorphism over a complete local base

Let `R` be a ring, `I ⊆ R` a maximal ideal with `R` `I`-adically complete, and let
`g : T ⟶ Spec R` be a **monomorphism** of schemes. If `g` admits a section over every
truncation `Spec (R / Iⁿ)`, then it admits a section over `Spec R` itself.

This is the engine of the injectivity half of
[Stacks, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH) — *maps from the spectrum of a
complete local Noetherian ring to an algebraic space are detected on the truncations*. There
`T` is the fibre product `Spec R ×_{(x, x'), X ×_S X, Δ} X` of two points `x`, `x'` of the
algebraic space `X`, which is a scheme because the diagonal of `X` is representable, and
`g : T ⟶ Spec R` is a monomorphism by Stacks 02X4/03HK. Two points of `X` over `Spec R` are
equal exactly when `g` has a section, and they agree on the truncations exactly when `g` has
a section over each `Spec (R / mⁿ)`.

## Main results

* `PrimeSpectrum.subsingleton_quotient_pow_of_isMaximal`: the spectrum of `R / Iⁿ` has at
  most one point when `I` is maximal.
* `AlgebraicGeometry.exists_section_of_mono_of_forall_section_quotient_pow`: the section
  criterion above.
* `AlgebraicGeometry.exists_section_of_mono_of_forall_section_quotient_maximalIdeal_pow`: the
  same for a local ring complete for its maximal ideal, which is the form Stacks 0AQH uses.

## Implementation notes

The Stacks proof of 0AQH runs the injectivity step through the local ring `𝒪_{T,t}`: it
shows that `R → 𝒪_{T,t}` induces an isomorphism on every truncation and concludes
`R = 𝒪_{T,t}` because a Noetherian local ring injects into its completion. That route needs
`T` to be locally Noetherian, hence needs `T → Spec R` to be locally of finite type
(Stacks 03HK part (2)) and `Spec R` to be locally Noetherian (Stacks 01T6), and it needs
Krull's intersection theorem (Stacks 00IP).

None of that is necessary, and the proof here does without it. Only two things are used:

* `Spec (R / Iⁿ)` has at most one point, because `I` is maximal — so each given section
  factors through *any* open neighbourhood of the common image point, in particular through
  one affine open `V`, for all `n` at once;
* `g` is a monomorphism — so the given sections are automatically compatible with the
  truncation maps, and the induced ring maps `Γ(V, ⊤) → R / Iⁿ` form a compatible family.

`RingHom.exists_rightInverse_of_compatible_quotientHom` then assembles that family into a
retraction `Γ(V, ⊤) → R` of the structure map, which is the required section. So the
hypotheses of Stacks 0AQH's injectivity step reduce to the monomorphism part of 03HK
(part (3)) together with adic completeness: parts (2), (4) and (5) of 03HK, and the inputs
01T6 and 00IP, are not needed for it.

The passage between schemes and rings is `AlgebraicGeometry.Spec.preimage`, the inverse of
the fully faithful `Spec`; `V.isoSpec` identifies the affine open `V` with `Spec Γ(V, ⊤)`.
The index `n = 0` is not excluded: there `I ^ 0 = ⊤`, the ring `R / I ^ 0` is trivial and its
spectrum is empty, so the hypothesis at `n = 0` carries no information and is not used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-- The spectrum of `R / I ^ 0` is empty, as the ring is trivial. -/
private theorem isEmpty_primeSpectrum_quotient_pow_zero {R : Type u} [CommRing R] (I : Ideal R) :
    IsEmpty (PrimeSpectrum (R ⧸ I ^ 0)) :=
  PrimeSpectrum.isEmpty_iff_subsingleton.2
    (Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top]))

/-- The spectrum of `R / Iⁿ` has at most one point when `I` is a maximal ideal: every prime
of `R / Iⁿ` pulls back to a prime of `R` containing `Iⁿ`, hence containing `I`, hence equal
to `I`. For `n = 0` the quotient is the zero ring and the spectrum is empty. -/
theorem PrimeSpectrum.subsingleton_quotient_pow_of_isMaximal {R : Type u} [CommRing R]
    {I : Ideal R} (hI : I.IsMaximal) (n : ℕ) : Subsingleton (PrimeSpectrum (R ⧸ I ^ n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := isEmpty_primeSpectrum_quotient_pow_zero I
    infer_instance
  · have key : ∀ P : PrimeSpectrum (R ⧸ I ^ n),
        PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n)) P = ⟨I, hI.isPrime⟩ := by
      intro P
      have hle : I ^ n ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n)) P).asIdeal := by
        intro x hx
        rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
          Ideal.Quotient.eq_zero_iff_mem.2 hx]
        exact P.asIdeal.zero_mem
      exact PrimeSpectrum.ext (hI.eq_of_le (PrimeSpectrum.comap _ P).isPrime.ne_top
        ((Ideal.IsPrime.pow_le_iff hn.ne').mp hle)).symm
    exact ⟨fun P Q => PrimeSpectrum.comap_injective_of_surjective _
      Ideal.Quotient.mk_surjective (by rw [key P, key Q])⟩

namespace AlgebraicGeometry

/-- **A monomorphism over an adically complete base with sections on all truncations has a
section.** Let `I` be a maximal ideal of `R` with `R` `I`-adically complete and let
`g : T ⟶ Spec R` be a monomorphism of schemes. If for every `n` the closed immersion
`Spec (R / Iⁿ) ⟶ Spec R` factors through `g`, then so does the identity of `Spec R`. -/
theorem exists_section_of_mono_of_forall_section_quotient_pow {R : Type u} [CommRing R]
    {I : Ideal R} (hI : I.IsMaximal) [IsAdicComplete I R] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of R)) [Mono g]
    (s : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ n)) ⟶ T)
    (hs : ∀ n : ℕ, s n ≫ g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ T, σ ≫ g = 𝟙 _ := by
  -- the truncation maps compose to the quotient maps
  have hfac : ∀ {k n : ℕ} (h : k ≤ n),
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)) ≫
          CommRingCat.ofHom (Ideal.Quotient.factorPow I h) =
        CommRingCat.ofHom (Ideal.Quotient.mk (I ^ k)) := by
    intro k n h
    have hr : (Ideal.Quotient.factorPow I h).comp (Ideal.Quotient.mk (I ^ n)) =
        Ideal.Quotient.mk (I ^ k) := by
      ext x
      simp [Ideal.Quotient.factorPow]
    rw [← CommRingCat.ofHom_comp, hr]
  -- the given sections are compatible, because `g` is a monomorphism
  have htr : ∀ {k n : ℕ} (h : k ≤ n),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)) ≫ s n = s k := by
    intro k n h
    rw [← cancel_mono g, Category.assoc, hs n, hs k, ← Spec.map_comp, hfac h]
  -- all the sections hit one and the same point of `T`
  have hmne : I ^ 1 ≠ ⊤ := by rw [pow_one]; exact hI.ne_top
  have hnt : Nontrivial (R ⧸ I ^ 1) := Submodule.Quotient.nontrivial_iff.mpr hmne
  obtain ⟨p⟩ : Nonempty ↥(Spec (CommRingCat.of (R ⧸ I ^ 1))) :=
    PrimeSpectrum.instNonemptyOfNontrivial
  have hpt : ∀ (n : ℕ) (x : ↥(Spec (CommRingCat.of (R ⧸ I ^ n)))),
      (s n).base x = (s 1).base p := by
    intro n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ((isEmpty_primeSpectrum_quotient_pow_zero I).false x).elim
    · have hsub : Subsingleton ↥(Spec (CommRingCat.of (R ⧸ I ^ n))) :=
        PrimeSpectrum.subsingleton_quotient_pow_of_isMaximal hI n
      rw [Subsingleton.elim x ((Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factorPow I hn))).base p), ← htr hn]
      exact (Scheme.Hom.comp_apply _ _ p).symm
  -- an affine open neighbourhood of that point, through which every section factors
  obtain ⟨V, ι, hVaff, hιopen, htV⟩ :
      ∃ (V : Scheme.{u}) (ι : V ⟶ T), IsAffine V ∧ IsOpenImmersion ι ∧
        (s 1).base p ∈ Set.range ι.base :=
    ⟨T.affineCover.X _, T.affineCover.f _, inferInstance, inferInstance,
      T.affineCover.covers _⟩
  have := hVaff
  have := hιopen
  have hrange : ∀ n : ℕ, Set.range (s n).base ⊆ Set.range ι.base := by
    intro n x hx
    obtain ⟨y, rfl⟩ := hx
    rw [hpt n y]
    exact htV
  have hlf : ∀ n : ℕ, IsOpenImmersion.lift ι (s n) (hrange n) ≫ ι = s n := fun n =>
    IsOpenImmersion.lift_fac ι (s n) (hrange n)
  -- the corresponding compatible family of ring maps out of `Γ(V, ⊤)`
  let eV := V.isoSpec
  let φ : CommRingCat.of R ⟶ Γ(V, ⊤) := Spec.preimage (eV.inv ≫ ι ≫ g)
  let ψ : ∀ n : ℕ, Γ(V, ⊤) ⟶ CommRingCat.of (R ⧸ I ^ n) := fun n =>
    Spec.preimage (IsOpenImmersion.lift ι (s n) (hrange n) ≫ eV.hom)
  have hmapφ : Spec.map φ = eV.inv ≫ ι ≫ g := Spec.map_preimage _
  have hmapψ : ∀ n : ℕ,
      Spec.map (ψ n) = IsOpenImmersion.lift ι (s n) (hrange n) ≫ eV.hom := fun n =>
    Spec.map_preimage _
  have hψφ : ∀ n : ℕ, φ ≫ ψ n = CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)) := by
    intro n
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hmapφ, hmapψ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hlf n, hs n]
  have hψc : ∀ {k n : ℕ} (h : k ≤ n),
      ψ n ≫ CommRingCat.ofHom (Ideal.Quotient.factorPow I h) = ψ k := by
    intro k n h
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hmapψ, hmapψ, ← Category.assoc, cancel_mono,
      ← cancel_mono ι, Category.assoc, hlf n, hlf k]
    exact htr h
  have hcompat : ∀ {k n : ℕ} (h : k ≤ n),
      (Ideal.Quotient.factorPow I h).comp ((ψ n).hom) = (ψ k).hom := by
    intro k n h
    rw [← hψc h, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hsplit : ∀ n : ℕ, ((ψ n).hom).comp φ.hom = Ideal.Quotient.mk (I ^ n) := by
    intro n
    rw [← CommRingCat.hom_comp, hψφ n, CommRingCat.hom_ofHom]
  -- assemble the retraction and read it back as a section
  obtain ⟨χ, hχ⟩ := RingHom.exists_rightInverse_of_compatible_quotientHom (I := I)
    φ.hom (fun n => (ψ n).hom) hcompat hsplit
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ eV.inv ≫ ι, ?_⟩
  calc (Spec.map (CommRingCat.ofHom χ) ≫ eV.inv ≫ ι) ≫ g
      = Spec.map (CommRingCat.ofHom χ) ≫ Spec.map φ := by
        rw [hmapφ]; simp only [Category.assoc]
    _ = Spec.map (φ ≫ CommRingCat.ofHom χ) := (Spec.map_comp _ _).symm
    _ = 𝟙 _ := by
      rw [← CommRingCat.ofHom_hom φ, ← CommRingCat.ofHom_comp, hχ, CommRingCat.ofHom_id,
        Spec.map_id]

/-- **The form used by Stacks 0AQH.** For `R` a local ring, complete for its maximal ideal
`m`, a monomorphism `g : T ⟶ Spec R` with a section over every `Spec (R / mⁿ)` has a section
over `Spec R`. No Noetherian hypothesis is needed. -/
theorem exists_section_of_mono_of_forall_section_quotient_maximalIdeal_pow {R : Type u}
    [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R)) [Mono g]
    (s : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ n)) ⟶ T)
    (hs : ∀ n : ℕ, s n ≫ g =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n)))) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ T, σ ≫ g = 𝟙 _ :=
  exists_section_of_mono_of_forall_section_quotient_pow
    (IsLocalRing.maximalIdeal.isMaximal R) g s hs

end AlgebraicGeometry

end
