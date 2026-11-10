module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField

/-!
# Artinian approximation data at a prime of a geometrically regular algebra

Let `k` be a field of characteristic `p > 0`, let `Λ` be a Noetherian geometrically regular
`k`-algebra, let `𝔮` be a prime of `Λ` and let `n ≥ 1`. Writing `Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮`, the data
assembled here are: a finite subset `E ⊆ Λ̄` consisting of the images of a `k`-algebra generating
family of a finite-type `k`-algebra `A` mapping to `Λ`; a polynomial ring `k[y_1, …, y_m]` and a
`k`-algebra map `φ` from it to `Λ` through which `Λ̄` receives a factorization
`k[y_1, …, y_m]_𝔭/𝔭^n → D → Λ̄` by local Artinian rings with `E ⊆ D`; a regular system of
parameters `π_1, …, π_d` of `k[y_1, …, y_m]_𝔭` coming from `𝔭`, where `d = dim Λ_𝔮`; and the
polynomial ring `R = k[y_1, …, y_m, t_1, …, t_d]` with its elements `γ_i = π_i t_i`.

## Main definitions

* `Stacks.Smoothing.parameterScalingRing`: the polynomial ring `R = k[y_1, …, y_m, t_1, …, t_d]`.
* `Stacks.Smoothing.parameterScalingGen`: the element `γ_i = π_i t_i` of `R`.

## Main results

* `Stacks.Smoothing.exists_finset_primePowerQuotient_eq_image_generators`: the images in `Λ̄` of a
  `k`-algebra generating family of `A` form a finite subset of `Λ̄`.
* `Stacks.Smoothing.exists_mvPolynomial_localArtinianFactorization_mem`: the factorization
  `k[y_1, …, y_m]_𝔭/𝔭^n → D → Λ̄` by local Artinian rings, with the first map essentially smooth,
  the second flat, `E ⊆ D`, and `k[y_1, …, y_m]_𝔭 → Λ_𝔮` flat with `𝔭Λ_𝔮 = 𝔮Λ_𝔮`.
* `Stacks.Smoothing.exists_fin_mem_span_eq_maximalIdeal_of_flat`: `dim k[y_1, …, y_m]_𝔭 = d`
  together with `d` elements of `𝔭` whose images form a regular system of parameters of
  `k[y_1, …, y_m]_𝔭`.

## Implementation notes

`Λ̄` is `Stacks.Smoothing.primePowerQuotient 𝔮 n`, and the subring `D` of the factorization is a
`Subring Λ̄`, so that the containment `E ⊆ D` of the source is membership in a subring and the
second map of the factorization is `Subring.subtype`.

`R` is `MvPolynomial (Fin m ⊕ Fin d) k`, with `y_j = X (Sum.inl j)` and `t_i = X (Sum.inr i)`.

## References

* [Stacks Project, Tag 07FS](https://stacks.math.columbia.edu/tag/07FS)
* [Stacks Project, Tag 07FT](https://stacks.math.columbia.edu/tag/07FT)
* [Stacks Project, Tag 07FU](https://stacks.math.columbia.edu/tag/07FU)
* [Stacks Project, Tag 07FV](https://stacks.math.columbia.edu/tag/07FV)
-/

@[expose] public section

open IsLocalRing

namespace Stacks.Smoothing

universe u v w

/-! ### The images in `Λ_𝔮/𝔮^nΛ_𝔮` of a generating family -/

/-- The composite `Λ → Λ_𝔮 → Λ_𝔮/𝔮^nΛ_𝔮`. -/
noncomputable def toPrimePowerQuotient {Λ : Type*} [CommRing Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime]
    (n : ℕ) : Λ →+* primePowerQuotient 𝔮 n :=
  (Ideal.Quotient.mk _).comp (algebraMap Λ (Localization.AtPrime 𝔮))

/-- **Stacks 07FS.** Let `A` be a `k`-algebra of finite type mapping to a ring `Λ` with a prime
`𝔮`, and let `n` be an exponent. Then `A` has a finite `k`-algebra generating family whose image
in `Λ_𝔮/𝔮^nΛ_𝔮` is a finite subset of that ring. -/
@[stacks 07FS "Item 8 of the proof of Stacks 07FJ. `E` is produced as a `Finset` of
`Λ_𝔮/𝔮^nΛ_𝔮`, which is the shape in which clause (3) of Stacks 07FH consumes it; the generating
family of `A` is a `Finset` because `A` is of finite type over `k`."]
theorem exists_finset_primePowerQuotient_eq_image_generators (k : Type u) (A : Type v)
    (Λ : Type w) [CommRing k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing Λ]
    [Algebra A Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) :
    ∃ (s : Finset A) (E : Finset (primePowerQuotient 𝔮 n)),
      Algebra.adjoin k (s : Set A) = ⊤ ∧
      (E : Set (primePowerQuotient 𝔮 n)) =
        toPrimePowerQuotient 𝔮 n '' (algebraMap A Λ '' (s : Set A)) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  refine ⟨s, s.image fun a => toPrimePowerQuotient 𝔮 n (algebraMap A Λ a), hs, ?_⟩
  rw [Finset.coe_image, Set.image_image]

/-! ### The factorization by local Artinian rings -/

/-- The ideal `𝔭^n R_𝔭` is the `n`-th power of the maximal ideal of `R_𝔭`. -/
private theorem ideal_map_pow_eq_maximalIdeal_pow {R : Type*} [CommRing R] (𝔭 : Ideal R)
    [𝔭.IsPrime] (n : ℕ) :
    Ideal.map (algebraMap R (Localization.AtPrime 𝔭)) (𝔭 ^ n)
      = maximalIdeal (Localization.AtPrime 𝔭) ^ n := by
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]

/-- `R_𝔭/𝔭^nR_𝔭` is a local ring for `n ≥ 1`. -/
private theorem isLocalRing_primePowerQuotient_of_one_le {R : Type*} [CommRing R] (𝔭 : Ideal R)
    [𝔭.IsPrime] {n : ℕ} (hn : 1 ≤ n) : IsLocalRing (primePowerQuotient 𝔭 n) := by
  have hne : Ideal.map (algebraMap R (Localization.AtPrime 𝔭)) (𝔭 ^ n) ≠ ⊤ := by
    rw [ideal_map_pow_eq_maximalIdeal_pow]
    exact fun h => (maximalIdeal.isMaximal (Localization.AtPrime 𝔭)).ne_top <|
      top_le_iff.mp <| h.ge.trans (Ideal.pow_le_self (by omega))
  have : Nontrivial (primePowerQuotient 𝔭 n) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- `R_𝔭/𝔭^nR_𝔭` is an Artinian ring when `R` is Noetherian. -/
private theorem isArtinianRing_primePowerQuotient_of_one_le {R : Type*} [CommRing R]
    [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime] {n : ℕ}
    [IsLocalRing (primePowerQuotient 𝔭 n)] : IsArtinianRing (primePowerQuotient 𝔭 n) := by
  refine (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr ⟨n, ?_⟩
  rw [Ideal.zero_eq_bot, ← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.AtPrime 𝔭)) (𝔭 ^ n)))
      Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, ← ideal_map_pow_eq_maximalIdeal_pow, Ideal.map_quotient_self]

/-- **Stacks 07FT.** Let `k` be a field of characteristic `p > 0`, let `Λ` be a Noetherian
geometrically regular `k`-algebra, let `𝔮` be a prime of `Λ`, let `n ≥ 1` and let `E` be a finite
subset of `Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮`. Then there are `m` and a `k`-algebra map `φ : k[y_1, …, y_m] → Λ`
such that, with `𝔭 = φ^{-1}(𝔮)`, the induced local map `g : k[y_1, …, y_m]_𝔭 → Λ_𝔮` is flat with
`𝔭Λ_𝔮 = 𝔮Λ_𝔮`, and the map `u : k[y_1, …, y_m]_𝔭/𝔭^n → Λ̄` induced by `g` factors as
`D.subtype ∘ a` through a subring `D` of `Λ̄` containing `E`, with `a` essentially smooth and
`D.subtype` flat. All three rings of the factorization are local Artinian.

"Essentially smooth" is `RingHom.IsEssentiallySmooth`: essentially of finite presentation
(Tag 00QM (2)) and formally smooth; see
`StacksFrontier/RingTheory/Smoothing/EssentiallySmooth.lean`. -/
@[stacks 07FT "Item 9 of the proof of Stacks 07FJ, stated for the class of objects on which
clauses (2) and (3) of Stacks 07FH are available in this repository: `Λ` Noetherian and
geometrically regular over the field `k` of characteristic `p > 0`, with the residue field
`κ(𝔮)` of `Λ_𝔮` essentially of finite type over `k`, equivalently a finitely generated field
extension of `k`. That restriction on the objects is the one recorded by
`exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat`, which this theorem repackages;
outside it clause (2) is open in this repository, the source's choice of `λ_1, …, λ_t` being
unjustified as written and the natural repair provably destroying the flatness the argument needs
— for the counterexample `k = 𝐅_p`, `Λ̄ = k(v)[ε]/ε²` see
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField`. Clause (1), the flat `g` with
`𝔭Λ_𝔮 = 𝔮Λ_𝔮`, needs no such restriction and is repeated here because the item states it. WHAT
IS PROVED: the source's `m`, `φ : k[y_1, …, y_m] → Λ`, `𝔭 = φ^{-1}(𝔮)`, the flat
`g : k[y]_𝔭 → Λ_𝔮` compatible with `φ`, the ideal identity `𝔭Λ_𝔮 = 𝔮Λ_𝔮`, and the factorization
of the induced `u : k[y]_𝔭/𝔭^n → Λ̄` as the equation `D.subtype ∘ a = u` of ring maps, with `a`
essentially smooth, `D.subtype` flat and each of `k[y]_𝔭/𝔭^n`, `D` and `Λ̄` local Artinian, which
is the source's `factorization by local Artinian rings`. The source's `E ⊆ D mod 𝔮^nΛ_𝔮` is
`∀ e ∈ E, e ∈ D`, `E` being a finite subset of `Λ_𝔮/𝔮^nΛ_𝔮` already."]
theorem exists_mvPolynomial_localArtinianFactorization_mem {k Λ : Type u} [Field k] [CommRing Λ]
    [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ)
    [𝔮.IsPrime] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra.EssFiniteType k (ResidueField (Localization.AtPrime 𝔮))] {n : ℕ} (hn : 1 ≤ n)
    (E : Finset (primePowerQuotient 𝔮 n)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
      (u : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* primePowerQuotient 𝔮 n)
      (D : Subring (primePowerQuotient 𝔮 n))
      (a : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* D),
      Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮 ∧
      (∀ f, g (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) ∧
      g.Flat ∧
      (∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
              (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
              (Ideal.comap φ.toRingHom 𝔮 ^ n)) y)
          = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))
            (g y)) ∧
      D.subtype.comp a = u ∧
      (∀ e ∈ E, e ∈ D) ∧
      ∃ (_ : IsLocalRing (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n))
        (_ : IsArtinianRing (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n))
        (_ : IsLocalRing (primePowerQuotient 𝔮 n))
        (_ : IsArtinianRing (primePowerQuotient 𝔮 n))
        (_ : IsLocalRing D) (_ : IsArtinianRing D),
        a.IsEssentiallySmooth ∧ D.subtype.Flat := by
  obtain ⟨m, φ, g, u, D, a, hmap, hg, hgflat, hu, ha, hE, hlocD, hartD, hess, hflat⟩ :=
    exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat (k := k) 𝔮 p hn E
  have hlocP : IsLocalRing (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n) :=
    isLocalRing_primePowerQuotient_of_one_le _ hn
  have hlocQ : IsLocalRing (primePowerQuotient 𝔮 n) :=
    isLocalRing_primePowerQuotient_of_one_le _ hn
  exact ⟨m, φ, g, u, D, a, hmap, hg, hgflat, hu, RingHom.ext ha, hE, hlocP,
    isArtinianRing_primePowerQuotient_of_one_le _, hlocQ,
    isArtinianRing_primePowerQuotient_of_one_le _, hlocD, hartD, hess, hflat⟩

/-! ### A regular system of parameters of `k[y_1, …, y_m]_𝔭` coming from `𝔭` -/

/-- Every element of the maximal ideal of `R_𝔭` becomes, after multiplication by a unit, the
image of an element of `𝔭`. -/
private theorem exists_mem_isUnit_mul_eq_algebraMap_atPrime {R : Type*} [CommRing R]
    (𝔭 : Ideal R) [𝔭.IsPrime] {z : Localization.AtPrime 𝔭}
    (hz : z ∈ maximalIdeal (Localization.AtPrime 𝔭)) :
    ∃ b : R, b ∈ 𝔭 ∧ ∃ w : Localization.AtPrime 𝔭, IsUnit w ∧
      algebraMap R (Localization.AtPrime 𝔭) b = w * z := by
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
  have heq : algebraMap R (Localization.AtPrime 𝔭) (s : R) * z
      = algebraMap R (Localization.AtPrime 𝔭) b := by
    rw [← hbs, mul_comm]
    exact IsLocalization.mk'_spec _ b s
  have hmem : algebraMap R (Localization.AtPrime 𝔭) b
      ∈ maximalIdeal (Localization.AtPrime 𝔭) := by
    rw [← heq]
    exact Ideal.mul_mem_left _ _ hz
  refine ⟨b, ?_, algebraMap R (Localization.AtPrime 𝔭) (s : R),
    IsLocalization.map_units _ s, heq.symm⟩
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 b).mp hmem

/-- The maximal ideal of `R_𝔭` is generated by the images of as many elements of `𝔭` as its own
minimal number of generators. -/
private theorem exists_fin_mem_span_eq_maximalIdeal_atPrime {R : Type*} [CommRing R]
    [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ (r : ℕ) (π : Fin r → R), (∀ i, π i ∈ 𝔭) ∧
      Ideal.span (Set.range fun i => algebraMap R (Localization.AtPrime 𝔭) (π i))
        = maximalIdeal (Localization.AtPrime 𝔭) ∧
      (maximalIdeal (Localization.AtPrime 𝔭)).spanFinrank = r := by
  classical
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime 𝔭)))
  have hmem : ∀ z : s, (z : Localization.AtPrime 𝔭) ∈ maximalIdeal (Localization.AtPrime 𝔭) :=
    fun z => hspan ▸ Ideal.subset_span z.2
  choose b hb w hw hbw using fun z : s => exists_mem_isUnit_mul_eq_algebraMap_atPrime 𝔭 (hmem z)
  refine ⟨s.card, fun i => b (s.equivFin.symm i), fun i => hb _, ?_, hcard.symm⟩
  have hrange : (Set.range fun i : Fin s.card =>
        algebraMap R (Localization.AtPrime 𝔭) (b (s.equivFin.symm i)))
      = Set.range fun z : s => algebraMap R (Localization.AtPrime 𝔭) (b z) := by
    ext y
    simp only [Set.mem_range]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨i, hi⟩ := h
      exact ⟨s.equivFin.symm i, hi⟩
    · obtain ⟨z, hz⟩ := h
      refine ⟨s.equivFin z, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact hz
  rw [hrange, ← hspan]
  refine le_antisymm (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun z => ?_))
    (Ideal.span_le.mpr fun y hy => ?_)
  · change algebraMap R (Localization.AtPrime 𝔭) (b z)
      ∈ Ideal.span (s : Set (Localization.AtPrime 𝔭))
    rw [hbw z]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr z.2))
  · change y ∈ Ideal.span (Set.range fun z : s => algebraMap R (Localization.AtPrime 𝔭) (b z))
    have hys : y ∈ s := Finset.mem_coe.mp hy
    rw [← Ideal.unit_mul_mem_iff_mem _ (hw ⟨y, hys⟩), ← hbw ⟨y, hys⟩]
    exact Ideal.subset_span ⟨⟨y, hys⟩, rfl⟩

/-- **Stacks 07FU.** Let `𝔮` be a prime of a Noetherian ring `Λ`, let `𝔭` be the contraction of
`𝔮` along a `k`-algebra map `φ : k[y_1, …, y_m] → Λ` and suppose the induced map
`g : k[y_1, …, y_m]_𝔭 → Λ_𝔮` is flat with `𝔭Λ_𝔮 = 𝔮Λ_𝔮`. If `d = dim Λ_𝔮`, then
`dim k[y_1, …, y_m]_𝔭 = d` and there are `π_1, …, π_d ∈ 𝔭` whose images generate the maximal
ideal of `k[y_1, …, y_m]_𝔭`, that is, form a regular system of parameters of it. -/
@[stacks 07FU "Item 10 of the proof of Stacks 07FJ. `d` is `dim Λ_𝔮` of item 07FM, and the first
thing proved is that it is also `dim k[y_1, …, y_m]_𝔭`: `𝔭Λ_𝔮 = 𝔮Λ_𝔮` makes the fibre of `g`
over the closed point a field, and `g` is flat, hence satisfies going down, so Stacks 00ON gives
`height 𝔮Λ_𝔮 = height 𝔭k[y]_𝔭 + 0`. A polynomial ring over a field is regular, so `k[y]_𝔭` is a
regular local ring and its maximal ideal is generated by `dim k[y]_𝔭` elements; each may be taken
to be the image of an element of `𝔭`, because an element of the maximal ideal of a localization is
a unit multiple of such an image. `d` elements of `𝔭` whose images generate the maximal ideal of
the `d`-dimensional regular local ring `k[y]_𝔭` is exactly a regular system of parameters of
`k[y]_𝔭`, and the dimension equality is part of the conclusion so that this reading is pinned
down. The hypotheses are the part of item 07FT that the step uses: `φ`, the flat `g` compatible
with `φ`, and the ideal identity."]
theorem exists_fin_mem_span_eq_maximalIdeal_of_flat {k : Type u} [Field k] {Λ : Type v}
    [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime] {m : ℕ}
    (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
    (hmap : Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮)
    (hg : ∀ f, g (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
        = algebraMap Λ (Localization.AtPrime 𝔮) (φ f))
    (hgflat : g.Flat) {d : ℕ}
    (hd : ringKrullDim (Localization.AtPrime 𝔮) = (d : WithBot ℕ∞)) :
    ringKrullDim (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) = (d : WithBot ℕ∞) ∧
      ∃ π : Fin d → MvPolynomial (Fin m) k, (∀ i, π i ∈ Ideal.comap φ.toRingHom 𝔮) ∧
        Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) (π i))
          = maximalIdeal (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) := by
  set 𝔭 : Ideal (MvPolynomial (Fin m) k) := Ideal.comap φ.toRingHom 𝔮 with h𝔭
  algebraize [g]
  have hgalg : algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮) = g :=
    RingHom.algebraMap_toAlgebra g
  -- the maximal ideal of `Λ_𝔮` is the extension of the maximal ideal of `k[y]_𝔭`
  have hmaxmap : Ideal.map (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮))
      (maximalIdeal (Localization.AtPrime 𝔭)) = maximalIdeal (Localization.AtPrime 𝔮) := by
    rw [hgalg, ← Localization.AtPrime.map_eq_maximalIdeal (I := 𝔭), Ideal.map_map,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 (Localization.AtPrime 𝔮), ← hmap]
    exact congrArg (Ideal.map · 𝔭) (RingHom.ext fun f => hg f)
  -- the closed point of `Λ_𝔮` lies over the closed point of `k[y]_𝔭`
  have hlies : (maximalIdeal (Localization.AtPrime 𝔮)).LiesOver
      (maximalIdeal (Localization.AtPrime 𝔭)) := by
    refine ⟨(maximalIdeal.isMaximal (Localization.AtPrime 𝔭)).eq_of_le ?_ ?_⟩
    · intro htop
      refine (maximalIdeal.isMaximal (Localization.AtPrime 𝔮)).ne_top
        ((Ideal.eq_top_iff_one _).mpr ?_)
      simpa using (Ideal.eq_top_iff_one _).mp htop
    · rw [← Ideal.map_le_iff_le_comap, hmaxmap]
  -- Stacks 00ON for the flat, hence going-down, algebra `k[y]_𝔭 → Λ_𝔮`
  have hheight : (maximalIdeal (Localization.AtPrime 𝔮)).height
      = (maximalIdeal (Localization.AtPrime 𝔭)).height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal (Localization.AtPrime 𝔭)) (maximalIdeal (Localization.AtPrime 𝔮)), hmaxmap]
    have : Field (Localization.AtPrime 𝔮 ⧸ maximalIdeal (Localization.AtPrime 𝔮)) :=
      Ideal.Quotient.field _
    rw [Ideal.map_quotient_self, Ideal.height_eq_zero_iff_eq_bot.mpr rfl, add_zero]
  have hdimeq : ringKrullDim (Localization.AtPrime 𝔭) = (d : WithBot ℕ∞) := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← hheight, maximalIdeal_height_eq_ringKrullDim, hd]
  refine ⟨hdimeq, ?_⟩
  -- `k[y]_𝔭` is regular local, so its maximal ideal is generated by `d` elements of `𝔭`
  have : IsRegularRing (MvPolynomial (Fin m) k) := MvPolynomial.isRegularRing_of_isRegularRing k
  have hreg : IsRegularLocalRing (Localization.AtPrime 𝔭) := inferInstance
  obtain ⟨r, π, hπ, hspan, hrank⟩ := exists_fin_mem_span_eq_maximalIdeal_atPrime 𝔭
  have hrd : r = d := by
    have hsf := hreg.spanFinrank_maximalIdeal
    rw [hrank, hdimeq] at hsf
    exact_mod_cast hsf
  subst hrd
  exact ⟨π, hπ, hspan⟩

/-! ### The polynomial ring `R = k[y_1, …, y_m, t_1, …, t_d]` and the elements `γ_i = π_i t_i` -/

/-- The polynomial ring `R = k[y_1, …, y_m, t_1, …, t_d]`, with `y_j = X (Sum.inl j)` the
variables of the polynomial ring of Stacks 07FT and `t_i = X (Sum.inr i)` one new variable for
each member of the regular system of parameters of Stacks 07FU. -/
@[stacks 07FV "Item 11 of the proof of Stacks 07FJ, with one correction: the source writes
`R = k[y_1, …, y_m, t_1, …, t_m]`, but the `t`-block has `d` members, not `m`. Every later use of
`R` in the proof writes `k[y_1, …, y_m, t_1, …, t_d]` — items 07FZ, 07G3 and 07G9, and repeatedly
in the justifications — and `γ_i = π_i t_i` is defined only for `i = 1, …, d`, the `π_i` being the
`d` elements supplied by item 07FU, with `I = (γ_1^e, …, γ_d^e)` in item 07G1. `R` is
`MvPolynomial (Fin m ⊕ Fin d) k` with `y_j = X (Sum.inl j)` and `t_i = X (Sum.inr i)`; the
`k`-algebra map `k[y_1, …, y_m] → R` of the source is `MvPolynomial.rename Sum.inl`."]
abbrev parameterScalingRing (k : Type u) [CommRing k] (m d : ℕ) : Type u :=
  MvPolynomial (Fin m ⊕ Fin d) k

/-- The element `γ_i = π_i t_i` of `R = k[y_1, …, y_m, t_1, …, t_d]`: the `i`-th member of a
family `π_1, …, π_d` in `k[y_1, …, y_m]`, scaled by the new variable `t_i`. -/
@[stacks 07FV "Item 11 of the proof of Stacks 07FJ; see `parameterScalingRing` for the correction
to the source's `R`. `γ_i` is defined for `i = 1, …, d`, matching the `d` elements `π_i` of item
07FU."]
noncomputable def parameterScalingGen {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (i : Fin d) : parameterScalingRing k m d :=
  MvPolynomial.rename Sum.inl (π i) * MvPolynomial.X (Sum.inr i)

/-- Evaluating `γ_i = π_i t_i` gives the product of the value of `π_i` at the images of
`y_1, …, y_m` with the image of `t_i`. -/
@[simp]
lemma aeval_parameterScalingGen {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) {S : Type v} [CommRing S] [Algebra k S]
    (f : Fin m ⊕ Fin d → S) (i : Fin d) :
    MvPolynomial.aeval f (parameterScalingGen π i)
      = MvPolynomial.aeval (fun j => f (Sum.inl j)) (π i) * f (Sum.inr i) := by
  rw [parameterScalingGen, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X]
  rfl

end Stacks.Smoothing

end
