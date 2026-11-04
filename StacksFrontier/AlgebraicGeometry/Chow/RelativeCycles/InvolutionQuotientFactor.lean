module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Morphisms invariant under an involution factor through the invariants locally

Let `R` be a domain with an involution `σ` and let `B ⊆ R` be the subring of `σ`-invariants.
A morphism `Φ : Spec R ⟶ Y` to an arbitrary scheme with `Φ ∘ Spec σ = Φ` factors, near any
`σ`-fixed point `x` of `Spec R`, through `Spec R ⟶ Spec B`: there is an invariant `h ∈ B` not
vanishing at `x` and a morphism `ψ : Spec B_h ⟶ Y` with `ψ ∘ (Spec R_h ⟶ Spec B_h) = Φ|_{D(h)}`.

This is the step of the characteristic `2` example of Stacks Remark 0H5Y which passes from a
`σ`-invariant morphism `W ⟶ M` to a morphism from the quotient `W/⟨σ⟩ = Sym²(A²)`, near the
generic point of the image of the diagonal, which is all the argument of the source needs.

## Main results

* `AlgebraicGeometry.exists_factor_specAway_of_comp_eq` — the local factorization.

## Implementation notes

Since `x` is fixed, `h = g σ(g)` is invariant for any `g` with `x ∈ D(g)`, and choosing `D(g)`
inside the preimage of an affine open `V ∋ Φ x` makes `Φ|_{D(h)}` a morphism of affine schemes
`Spec R_h ⟶ V`, given by a ring map `Γ(V) ⟶ R_h` whose image is fixed by the involution induced on
`R_h`. In a domain the invariants of `R_h` are the localization `B_h`, which gives the
factorization.

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k R : Type u} [CommRing k] [CommRing R] [IsDomain R] [Algebra k R]

/-- The involution induced by an invariant-preserving automorphism on the localization at an
invariant element. -/
def awayInvolution (σ : R ≃ₐ[k] R) (h : R) (hh : σ h = h) :
    Localization.Away h →+* Localization.Away h :=
  IsLocalization.Away.lift h (g := (algebraMap R (Localization.Away h)).comp σ.toRingHom)
    (by simpa [hh] using IsLocalization.Away.algebraMap_isUnit h)

omit [IsDomain R] in
/-- The involution `awayInvolution σ h hh` sends the image of `r : R` in `R_h` to the image of
`σ r`. -/
theorem awayInvolution_algebraMap (σ : R ≃ₐ[k] R) (h : R) (hh : σ h = h) (r : R) :
    awayInvolution σ h hh (algebraMap R _ r) = algebraMap R _ (σ r) :=
  IsLocalization.Away.lift_eq h _ r

/-- **The invariants of `R_h` are `B_h`.** In a domain, an element of `R_h` fixed by the induced
involution comes from the localization of the invariant subring. -/
theorem mem_range_awayMap_of_awayInvolution (B : Subalgebra k R) (σ : R ≃ₐ[k] R)
    (hB : ∀ x : R, x ∈ B ↔ σ x = x) (h : B) (hh0 : algebraMap B R h ≠ 0)
    (z : Localization.Away (algebraMap B R h))
    (hz : awayInvolution σ (algebraMap B R h) ((hB h).mp h.2) z = z) :
    z ∈ (Localization.awayMap (algebraMap B R) h).range := by
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B R h)) z
  simp only at hr
  have hinj : Function.Injective (algebraMap R (Localization.Away (algebraMap B R h))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hh0)
  have hσh : σ (algebraMap B R h) = algebraMap B R h := (hB h).mp h.2
  have hσr : σ r = r := by
    apply hinj
    have h1 := congrArg (awayInvolution σ (algebraMap B R h) hσh) hr
    rw [map_mul, hz, awayInvolution_algebraMap, awayInvolution_algebraMap, map_pow, hσh,
      hr] at h1
    exact h1.symm
  have hrB : r ∈ B := (hB r).mpr hσr
  refine ⟨IsLocalization.mk' (Localization.Away h) (⟨r, hrB⟩ : B)
    (⟨h ^ n, n, rfl⟩ : Submonoid.powers h), ?_⟩
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  symm
  refine (IsLocalization.eq_mk'_iff_mul_eq).mpr ?_
  exact hr

/-- **Local factorization through the invariants.** Let `σ` be an involution of the domain `R`
with invariant subalgebra `B`, let `Φ : Spec R ⟶ Y` satisfy `Φ ∘ Spec σ = Φ` and let `x` be a point
of `Spec R` fixed by `σ`. Then there are an invariant `h ∈ B` with `h(x) ≠ 0` and a morphism
`ψ : Spec B_h ⟶ Y` such that `ψ ∘ (Spec R_h ⟶ Spec B_h) = Φ ∘ (Spec R_h ⟶ Spec R)`. -/
theorem exists_factor_specAway_of_comp_eq (B : Subalgebra k R) (σ : R ≃ₐ[k] R)
    (hσσ : ∀ r, σ (σ r) = r) (hB : ∀ x : R, x ∈ B ↔ σ x = x) {Y : Scheme.{u}}
    (Φ : Spec (.of R) ⟶ Y) (hΦ : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Φ = Φ)
    (x : Spec (.of R)) (hx : ∀ r, σ r ∈ x.asIdeal ↔ r ∈ x.asIdeal) :
    ∃ h : B, (h : R) ∉ x.asIdeal ∧ ∃ ψ : Spec (.of (Localization.Away h)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap B R) h)) ≫ ψ =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (algebraMap B R h)))) ≫ Φ := by
  classical
  -- an affine open around `Φ x` and a basic open around `x` inside its preimage
  obtain ⟨_, ⟨V, hV₀, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (Φ x)) isOpen_univ
  have hV : IsAffineOpen V := hV₀
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show x ∈ (Φ ⁻¹ᵁ V : Set (Spec (.of R))) from hxV) (Φ ⁻¹ᵁ V).isOpen
  -- the invariant `h = g σ(g)`
  have hhB : g * σ g ∈ B := by
    rw [hB, map_mul, hσσ, mul_comm]
  set h : B := ⟨g * σ g, hhB⟩
  have hgx : g ∉ x.asIdeal := hxg
  have hhx : (h : R) ∉ x.asIdeal := by
    change g * σ g ∉ x.asIdeal
    exact fun hm => (x.isPrime.mem_or_mem hm).elim hgx (fun h' => hgx ((hx g).mp h'))
  have hh0 : (h : R) ≠ 0 := fun h0 => hhx (h0 ▸ x.asIdeal.zero_mem)
  refine ⟨h, hhx, ?_⟩
  set Rh := Localization.Away (algebraMap B R h)
  set loc : CommRingCat.of R ⟶ CommRingCat.of Rh := CommRingCat.ofHom (algebraMap R Rh)
  -- `Φ` restricted to `D(h)` lands in `V`
  have hrange : Set.range (Spec.map loc ≫ Φ) ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have hy : (Spec.map loc).base y ∈
        (PrimeSpectrum.basicOpen (algebraMap B R h) : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range Rh (algebraMap B R h)]
      exact ⟨y, rfl⟩
    have hyg : (Spec.map loc).base y ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
      intro hm
      exact hy (Ideal.mul_mem_right _ _ hm)
    exact hgV hyg
  set ℓ := IsOpenImmersion.lift hV.fromSpec (Spec.map loc ≫ Φ) hrange
  have hℓ : ℓ ≫ hV.fromSpec = Spec.map loc ≫ Φ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨θ, hθ⟩ := Spec.map_surjective ℓ
  -- the ring map is invariant
  have hσh : σ (algebraMap B R h) = algebraMap B R h := (hB h).mp h.2
  set σh := awayInvolution σ (algebraMap B R h) hσh
  have hcomm : CommRingCat.ofHom σ.toRingHom ≫ loc = loc ≫ CommRingCat.ofHom σh := by
    ext r
    exact (awayInvolution_algebraMap σ (algebraMap B R h) hσh r).symm
  have h1 : Spec.map (CommRingCat.ofHom σh) ≫ Spec.map loc ≫ Φ = Spec.map loc ≫ Φ := by
    have h2 : Spec.map (CommRingCat.ofHom σh) ≫ Spec.map loc =
        Spec.map loc ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
      rw [← Spec.map_comp, ← Spec.map_comp, hcomm]
    rw [← Category.assoc, h2, Category.assoc, hΦ]
  have hinv : θ ≫ CommRingCat.ofHom σh = θ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, ← cancel_mono hV.fromSpec, Category.assoc, hℓ, h1]
  -- so it factors through `B_h`
  have hmem : ∀ c, θ c ∈ (Localization.awayMap (algebraMap B R) h).range := by
    intro c
    refine mem_range_awayMap_of_awayInvolution B σ hB h hh0 (θ c) ?_
    exact congrArg (fun m : _ ⟶ CommRingCat.of Rh => m c) hinv
  have hinj : Function.Injective (Localization.awayMap (algebraMap B R) h) := by
    rw [Localization.awayMap_injective_iff]
    intro a ha
    exact ⟨0, by rw [pow_zero, one_mul]; exact Subtype.ext ha⟩
  let e : Localization.Away h ≃+* (Localization.awayMap (algebraMap B R) h).range :=
    RingEquiv.ofBijective (Localization.awayMap (algebraMap B R) h).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab),
        (Localization.awayMap (algebraMap B R) h).rangeRestrict_surjective⟩
  let θ' : Γ(Y, V) ⟶ CommRingCat.of (Localization.Away h) :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (θ.hom.codRestrict _ hmem))
  have hθ' : θ' ≫ CommRingCat.ofHom (Localization.awayMap (algebraMap B R) h) = θ := by
    ext c
    change (Localization.awayMap (algebraMap B R) h) (e.symm ⟨θ c, hmem c⟩) = θ c
    exact congrArg Subtype.val (e.apply_symm_apply (⟨θ c, hmem c⟩ :
      (Localization.awayMap (algebraMap B R) h).range))
  refine ⟨Spec.map θ' ≫ hV.fromSpec, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hθ', hθ, hℓ]

end AlgebraicGeometry

end
