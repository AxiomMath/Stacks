module

public import StacksFrontier.RingTheory.ArtinRees.SameDenominator

/-!
# The denominator criterion is independent of the ambient presentation

Let `D` be a commutative ring and `m` an ideal of it, and let `Q`, `Q'` be two `D`-algebras —
in Stacks 0CAY the two base changes `B ⊗_{C,σ} D` and `B ⊗_{C,σ'} D` of one chart of `Y`. Each
presentation of the pair, that is each `D`-algebra `A` with surjections `A ↠ Q` and `A ↠ Q'`,
gives a reading `Stacks.ArtinRees.SameDenominator (m A) (ker π) (ker ρ)` of the condition that the
two conormal algebras agree. This file proves that the reading does not depend on the
presentation, provided the two presentations are compared by a *pair* of maps — one over `Q` and
one over `Q'` — which agree modulo `m`.

That proviso is what makes the statement usable and is not a technicality. A map between two
presentations over `Q` has no reason to be one over `Q'`: lifting a generator of one presentation
through the other mentions the structure map `C → D`, which is `σ` on one side and `σ'` on the
other. What the two liftings share is that they are the *same* `C`-rational expression in the
generators specialised along `σ` and along `σ'`, so they differ by an element of `m A` — and a
difference in `m A` is all the argument needs, because the criterion at degree `n` only ever
compares elements modulo `m^(n+1) A`.

## Main results

* `Stacks.ArtinRees.sub_mem_map_pow_succ`: two `D`-algebra maps agreeing modulo `m` agree modulo
  `m^(n+1)` on `m^n`.
* `Stacks.ArtinRees.mem_sup_pow_iff_of_comp`: a surjection factoring through another one
  identifies the two `n`-th denominators.
* `Stacks.ArtinRees.SameDenominator.ofComp`: **the criterion transfers along a pair of comparison
  maps agreeing modulo `m`.**

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public section

universe u v

namespace Stacks.ArtinRees

variable {D : Type u} [CommRing D]

section Ker

variable {A Q : Type*} [CommRing A] [CommRing Q]

/-- **Membership in the `n`-th denominator, read in the target of a surjection**: for a surjective
ring map `π`, an element lies in `K + ker π` exactly when its image lies in the image of `K`. -/
theorem mem_sup_ker_iff (π : A →+* Q) (hπ : Function.Surjective π) (K : Ideal A) (z : A) :
    z ∈ K ⊔ RingHom.ker π ↔ π z ∈ K.map π := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective π hπ]
  rfl

end Ker

/-- An element of `I ^ n` is sent by a ring map `f` into `(I.map f) ^ n`. -/
private theorem map_mem_map_pow {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {I : Ideal R} {n : ℕ} {x : R} (hx : x ∈ I ^ n) : f x ∈ (I.map f) ^ n :=
  Ideal.map_pow f I n ▸ Ideal.mem_map_of_mem f hx

/-- **The image of the `n`-th power of the ideal `m` generates in a `D`-algebra is the `n`-th
power of the ideal it generates in the target**, for any `D`-algebra map. This is the reason the
two sides of a comparison of presentations have the same `n`-th denominator in the target. -/
theorem map_pow_map_algebraMap {A Q : Type*} [CommRing A] [CommRing Q] [Algebra D A] [Algebra D Q]
    (m : Ideal D) (π : A →ₐ[D] Q) (n : ℕ) :
    ((m.map (algebraMap D A)) ^ n).map (π : A →+* Q) = (m ^ n).map (algebraMap D Q) := by
  rw [← Ideal.map_pow, Ideal.map_map, π.comp_algebraMap]

/-- **Two `D`-algebra maps agreeing modulo `m` agree modulo `m^(n+1)` on `m^n`.** The `n`-th power
of the ideal `m` generates is spanned over `D` by the products `c • x` with `c ∈ m^n`, and on such
a product the two maps differ by `c • (h x - h' x)`, which lies in `m^n · m`. -/
theorem sub_mem_map_pow_succ {A₁ A₂ : Type*} [CommRing A₁] [CommRing A₂]
    [Algebra D A₁] [Algebra D A₂] (m : Ideal D) (h h' : A₂ →ₐ[D] A₁)
    (hcong : ∀ x, h x - h' x ∈ m.map (algebraMap D A₁)) (n : ℕ) {z : A₂}
    (hz : z ∈ (m.map (algebraMap D A₂)) ^ n) :
    h z - h' z ∈ (m.map (algebraMap D A₁)) ^ (n + 1) := by
  rw [← Ideal.map_pow] at hz
  have hz' : z ∈ (m ^ n) • (⊤ : Submodule D A₂) := by
    rwa [Ideal.smul_top_eq_map]
  refine Submodule.smul_induction_on hz' (fun c hc x _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, map_smul, ← smul_sub, Algebra.smul_def, pow_succ]
    exact Ideal.mul_mem_mul (map_mem_map_pow (algebraMap D A₁) hc) (hcong x)
  · rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hx hy

/-- **A surjection factoring through another one identifies the two `n`-th denominators.** If
`π₂ = π₁ ∘ h` with `π₁`, `π₂` surjective `D`-algebra maps onto a common `Q`, then an element of
`A₂` lies in `m^n A₂ + ker π₂` exactly when its image under `h` lies in `m^n A₁ + ker π₁`: both
say that the common image in `Q` lies in `m^n Q`. -/
theorem mem_sup_pow_iff_of_comp {A₁ A₂ Q : Type*} [CommRing A₁] [CommRing A₂] [CommRing Q]
    [Algebra D A₁] [Algebra D A₂] [Algebra D Q] (m : Ideal D)
    {π₁ : A₁ →ₐ[D] Q} (hπ₁ : Function.Surjective π₁)
    {π₂ : A₂ →ₐ[D] Q} (hπ₂ : Function.Surjective π₂)
    {h : A₂ →ₐ[D] A₁} (hh : ∀ x, π₁ (h x) = π₂ x) (n : ℕ) (z : A₂) :
    z ∈ (m.map (algebraMap D A₂)) ^ n ⊔ RingHom.ker (π₂ : A₂ →+* Q) ↔
      h z ∈ (m.map (algebraMap D A₁)) ^ n ⊔ RingHom.ker (π₁ : A₁ →+* Q) := by
  rw [mem_sup_ker_iff (π₂ : A₂ →+* Q) hπ₂, mem_sup_ker_iff (π₁ : A₁ →+* Q) hπ₁,
    map_pow_map_algebraMap m π₂ n, map_pow_map_algebraMap m π₁ n,
    show (π₁ : A₁ →+* Q) (h z) = (π₂ : A₂ →+* Q) z from hh z]

/-- **The denominator criterion transfers along a pair of comparison maps agreeing modulo `m`.**
Let `π₁ : A₁ ↠ Q` and `π₂ : A₂ ↠ Q` be surjections of `D`-algebras onto one `D`-algebra, and
`ρ₁ : A₁ ↠ Q'`, `ρ₂ : A₂ ↠ Q'` onto another. Let `h, h' : A₂ → A₁` be `D`-algebra maps with
`π₁ ∘ h = π₂` and `ρ₁ ∘ h' = ρ₂`, differing by an element of `m A₁` at every argument. Then the
criterion for the presentation `A₁` implies the criterion for the presentation `A₂`.

The two comparison maps are allowed to differ because no single map can be asked to commute with
both pairs of surjections: in Stacks 0CAY `h` lifts the generators of the second presentation
along `σ` and `h'` lifts them along `σ'`. They agree modulo `m` because the lift is the same
`C`-rational expression on both sides. -/
theorem SameDenominator.ofComp {A₁ A₂ Q Q' : Type*} [CommRing A₁] [CommRing A₂] [CommRing Q]
    [CommRing Q'] [Algebra D A₁] [Algebra D A₂] [Algebra D Q] [Algebra D Q'] (m : Ideal D)
    {π₁ : A₁ →ₐ[D] Q} (hπ₁ : Function.Surjective π₁)
    {π₂ : A₂ →ₐ[D] Q} (hπ₂ : Function.Surjective π₂)
    {ρ₁ : A₁ →ₐ[D] Q'} (hρ₁ : Function.Surjective ρ₁)
    {ρ₂ : A₂ →ₐ[D] Q'} (hρ₂ : Function.Surjective ρ₂)
    {h h' : A₂ →ₐ[D] A₁} (hh : ∀ x, π₁ (h x) = π₂ x) (hh' : ∀ x, ρ₁ (h' x) = ρ₂ x)
    (hcong : ∀ x, h x - h' x ∈ m.map (algebraMap D A₁))
    (hden : SameDenominator (m.map (algebraMap D A₁)) (RingHom.ker (π₁ : A₁ →+* Q))
      (RingHom.ker (ρ₁ : A₁ →+* Q'))) :
    SameDenominator (m.map (algebraMap D A₂)) (RingHom.ker (π₂ : A₂ →+* Q))
      (RingHom.ker (ρ₂ : A₂ →+* Q')) := by
  intro n z hz
  have hhz : h z ∈ (m.map (algebraMap D A₁)) ^ n := by
    simpa [Ideal.map_map, h.comp_algebraMap] using map_mem_map_pow (h : A₂ →+* A₁) hz
  have hdiff : h z - h' z ∈ (m.map (algebraMap D A₁)) ^ (n + 1) :=
    sub_mem_map_pow_succ m h h' hcong n hz
  calc z ∈ (m.map (algebraMap D A₂)) ^ (n + 1) ⊔ RingHom.ker (π₂ : A₂ →+* Q)
      ↔ h z ∈ (m.map (algebraMap D A₁)) ^ (n + 1) ⊔ RingHom.ker (π₁ : A₁ →+* Q) :=
        mem_sup_pow_iff_of_comp m hπ₁ hπ₂ hh (n + 1) z
    _ ↔ h z ∈ (m.map (algebraMap D A₁)) ^ (n + 1) ⊔ RingHom.ker (ρ₁ : A₁ →+* Q') :=
        hden n (h z) hhz
    _ ↔ h' z ∈ (m.map (algebraMap D A₁)) ^ (n + 1) ⊔ RingHom.ker (ρ₁ : A₁ →+* Q') :=
        ⟨fun hmem => by simpa using Ideal.sub_mem _ hmem (Ideal.mem_sup_left hdiff),
          fun hmem => by simpa using Ideal.add_mem _ hmem (Ideal.mem_sup_left hdiff)⟩
    _ ↔ z ∈ (m.map (algebraMap D A₂)) ^ (n + 1) ⊔ RingHom.ker (ρ₂ : A₂ →+* Q') :=
        (mem_sup_pow_iff_of_comp m hρ₁ hρ₂ hh' (n + 1) z).symm

end Stacks.ArtinRees

end
