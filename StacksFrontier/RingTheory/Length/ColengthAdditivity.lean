module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Additivity of colength along a composite, and the colength of a local ring in a product

Let `A` be a commutative ring. The *colength* of a linear map `f : M →ₗ[A] N` is
`Module.length A (N ⧸ LinearMap.range f)`. This file proves that colength is additive along a
composite whose second factor is injective,

`colength (g ∘ₗ f) = colength f + colength g`,

in `ℕ∞` and with no finiteness hypothesis, and that the colength of a ring homomorphism out of a
local ring into a product with two nontrivial factors is positive.

## Main results

* `Module.length_quotient_range_comp`: colength is additive along a composite with injective
  second factor.
* `Module.length_quotient_range_pos`: a map that is not surjective has positive colength.
* `RingHom.not_surjective_pi_of_isLocalRing`: a ring homomorphism from a local ring to a product
  with two nontrivial factors is not surjective.
* `Module.length_quotient_range_eq_zero_of_length_comp_eq_one`: if the composite has colength one
  and the first factor is not surjective, the second factor has colength zero.

## Implementation notes

The additivity is the short exact sequence

`0 → N ⧸ range f → P ⧸ range (g ∘ₗ f) → P ⧸ range g → 0`,

whose first map is `Submodule.mapQ … g` and whose second is `Submodule.mapQ … .id`; the first
map is injective because `g` is. The length identity is then `Module.length_eq_add_of_exact`,
which holds in `ℕ∞` without finiteness.

The non-surjectivity is the idempotent argument. If `φ a` is `Pi.single i 1`, the idempotent that
is `1` in the `i`-th factor and `0` elsewhere, then `a` or `1 - a` is a unit in the local ring
`A`; the first makes `0` a unit in the `j`-th factor and the second makes `0` a unit in the
`i`-th, so both contradict nontriviality.
-/

@[expose] public section

universe u

namespace Module

variable {A : Type*} [CommRing A]
variable {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

/-- **Colength is additive along a composite whose second factor is injective.** For
`f : M →ₗ[A] N` and an injective `g : N →ₗ[A] P`, the length of `P ⧸ range (g ∘ₗ f)` is the
length of `N ⧸ range f` plus the length of `P ⧸ range g`. No finiteness is needed: the identity
holds in `ℕ∞`, both sides being `⊤` together. -/
public theorem length_quotient_range_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hg : Function.Injective g) :
    Module.length A (P ⧸ LinearMap.range (g ∘ₗ f)) =
      Module.length A (N ⧸ LinearMap.range f) +
        Module.length A (P ⧸ LinearMap.range g) := by
  have hle : LinearMap.range (g ∘ₗ f) ≤ LinearMap.range g := LinearMap.range_comp_le_range f g
  have hu : LinearMap.range f ≤ Submodule.comap g (LinearMap.range (g ∘ₗ f)) := by
    intro n hn
    rw [Submodule.mem_comap, LinearMap.range_comp]
    exact Submodule.mem_map_of_mem hn
  have hv : LinearMap.range (g ∘ₗ f) ≤
      Submodule.comap (LinearMap.id (R := A) (M := P)) (LinearMap.range g) := hle
  set u := Submodule.mapQ (LinearMap.range f) (LinearMap.range (g ∘ₗ f)) g hu with hudef
  set v := Submodule.mapQ (LinearMap.range (g ∘ₗ f)) (LinearMap.range g)
    (LinearMap.id (R := A) (M := P)) hv with hvdef
  have hinj : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot]
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range f) x
    have hmem : g n ∈ LinearMap.range (g ∘ₗ f) := by
      have : u (Submodule.Quotient.mk n) = 0 := hx
      rwa [hudef, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at this
    rw [LinearMap.range_comp] at hmem
    obtain ⟨m, hm, hgm⟩ := hmem
    have : n = m := hg (hgm.symm ▸ rfl)
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, this]
    exact hm
  have hsurj : Function.Surjective v := by
    intro y
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range g) y
    exact ⟨Submodule.Quotient.mk p, by rw [hvdef, Submodule.mapQ_apply]; rfl⟩
  have hexact : Function.Exact u v := by
    rw [LinearMap.exact_iff, hudef, hvdef]
    simp [Submodule.ker_mapQ, Submodule.range_mapQ]
  exact Module.length_eq_add_of_exact u v hinj hsurj hexact

/-- **A map that is not surjective has positive colength.** -/
public theorem length_quotient_range_pos (f : M →ₗ[A] N) (hf : ¬ Function.Surjective f) :
    0 < Module.length A (N ⧸ LinearMap.range f) := by
  have hne : LinearMap.range f ≠ ⊤ := fun h => hf (LinearMap.range_eq_top.mp h)
  exact Module.length_pos_iff.mpr (Submodule.Quotient.nontrivial_iff.mpr hne)

end Module

namespace RingHom

/-- **A ring homomorphism from a local ring to a product with two nontrivial factors is not
surjective.** -/
public theorem not_surjective_pi_of_isLocalRing {A : Type*} [CommRing A] [IsLocalRing A]
    {ι : Type*} {B : ι → Type*} [∀ i, CommRing (B i)]
    (φ : A →+* ∀ i, B i) (i j : ι) (hij : i ≠ j)
    [Nontrivial (B i)] [Nontrivial (B j)] :
    ¬ Function.Surjective φ := by
  classical
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (Pi.single i 1)
  have key : ∀ (k : ι) [Nontrivial (B k)] (x : A), IsUnit x → φ x k = 0 → False :=
    fun k _ x h h0 => not_isUnit_zero (M₀ := B k)
      (by simpa [h0] using (h.map φ).map (Pi.evalRingHom B k))
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · exact key j a h (by rw [ha]; exact Pi.single_eq_of_ne (Ne.symm hij) _)
  · exact key i (1 - a) h (by simp [ha])

end RingHom

namespace Module

variable {A : Type*} [CommRing A]
variable {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

/-- **A colength-one composite whose first factor is not surjective has a second factor of
colength zero.** -/
public theorem length_quotient_range_eq_zero_of_length_comp_eq_one
    (f : M →ₗ[A] N) (g : N →ₗ[A] P) (hg : Function.Injective g)
    (hf : ¬ Function.Surjective f)
    (h : Module.length A (P ⧸ LinearMap.range (g ∘ₗ f)) = 1) :
    Module.length A (P ⧸ LinearMap.range g) = 0 := by
  rw [length_quotient_range_comp f g hg] at h
  have hfpos : (1 : ℕ∞) ≤ Module.length A (N ⧸ LinearMap.range f) :=
    ENat.one_le_iff_ne_zero.mpr (length_quotient_range_pos f hf).ne'
  by_contra hb
  have htwo := add_le_add hfpos (ENat.one_le_iff_ne_zero.mpr hb)
  rw [h] at htwo
  norm_num at htwo

end Module

end
