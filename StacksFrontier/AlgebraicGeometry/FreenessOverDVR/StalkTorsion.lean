module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Basis.Basic
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.CyclicSummands

/-!
# A uniform torsion exponent for a global function on the stalks of a Noetherian scheme

Let `X` be a Noetherian scheme and `t` a global function on `X`. On each affine open `U` the
`t`-power torsion of the Noetherian ring `Γ(X, U)` is killed by a single power of `t`, and taking
the largest exponent over a finite affine cover gives an exponent `k` that works at every stalk:
an element of `𝒪_{X, x}` killed by some power of `t` is killed by `t ^ k`. The same exponent then
works for every free module over a local ring of `X`, coordinatewise.

This is the uniformity behind the integer of [Stacks, Tag 0EXF]: the `π`-power torsion of the
structure sheaf of a proper scheme over a discrete valuation ring has a bounded exponent, which
does not depend on any module.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `exists_forall_pow_mul_eq_zero_of_isNoetherianRing`: the uniform exponent in a Noetherian ring.
* `pow_mul_eq_zero_of_isLocalization`: such an exponent passes to every localization.
* `exists_forall_germ_pow_mul_eq_zero`: **the uniform exponent at the stalks** of a Noetherian
  scheme.
* `pow_smul_eq_zero_of_free`: the exponent passes from a ring to every free module over it.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

/-- **A uniform torsion exponent in a Noetherian ring.** The `t`-power torsion of a Noetherian
ring is killed by a single power of `t`. -/
theorem exists_forall_pow_mul_eq_zero_of_isNoetherianRing {R : Type u} [CommRing R]
    [IsNoetherianRing R] (t : R) :
    ∃ e : ℕ, ∀ (r : R) (j : ℕ), t ^ j * r = 0 → t ^ e * r = 0 := by
  obtain ⟨e, he⟩ := exists_forall_pow_smul_torsionBy_eq_bot (A := R) (H := R) t
  refine ⟨e, fun r j hr => ?_⟩
  have hmem : t ^ e • r ∈ Ideal.span {t} ^ e • Submodule.torsionBy R R (t ^ j) := by
    refine Submodule.smul_mem_smul ?_ ((Submodule.mem_torsionBy_iff _ r).2 hr)
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [he j] at hmem
  exact (Submodule.mem_bot _).1 hmem

/-- **A uniform torsion exponent passes to localizations.** If every element of `R` killed by a
power of `t` is killed by `t ^ e`, the same holds for the image of `t` in a localization. -/
theorem pow_mul_eq_zero_of_isLocalization {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] {t : R} {e : ℕ}
    (he : ∀ (r : R) (j : ℕ), t ^ j * r = 0 → t ^ e * r = 0) (a : S) (j : ℕ)
    (ha : algebraMap R S t ^ j * a = 0) : algebraMap R S t ^ e * a = 0 := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M a
  rw [← map_pow, ← IsLocalization.mk'_one (M := M) (S := S) (t ^ j),
    ← IsLocalization.mk'_mul, one_mul, IsLocalization.mk'_eq_zero_iff] at ha
  obtain ⟨c, hc⟩ := ha
  have hc' : t ^ j * (c * r) = 0 := by rw [← hc]; ring
  have h := he (c * r) j hc'
  rw [← map_pow, ← IsLocalization.mk'_one (M := M) (S := S) (t ^ e),
    ← IsLocalization.mk'_mul, one_mul, IsLocalization.mk'_eq_zero_iff]
  exact ⟨c, by rw [← h]; ring⟩

/-- **A uniform torsion exponent passes to free modules**, coordinatewise. -/
theorem pow_smul_eq_zero_of_free {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M]
    [Module S M] [Module.Free S M] {t : S} {e : ℕ}
    (he : ∀ (a : S) (j : ℕ), t ^ j * a = 0 → t ^ e * a = 0) (m : M) (j : ℕ)
    (hm : t ^ j • m = 0) : t ^ e • m = 0 := by
  let b := Module.Free.chooseBasis S M
  refine b.repr.injective ?_
  ext i
  have hi : t ^ j * b.repr m i = 0 := by
    have := congrArg (fun z => b.repr z i) hm
    simpa using this
  simpa using he _ j hi

variable {X : Scheme.{u}}

/-- **The uniform torsion exponent at the stalks of a Noetherian scheme.** For a global function
`t` on a Noetherian scheme `X` there is one exponent `k` such that, at every point `x`, an element
of the local ring `𝒪_{X, x}` killed by a power of the germ of `t` is killed by its `k`-th power.

On each affine open the exponent of the Noetherian ring of sections works at every point of it,
the local ring being a localization of that ring, and finitely many affine opens cover `X`. -/
theorem exists_forall_germ_pow_mul_eq_zero [IsNoetherian X] (t : Γ(X, ⊤)) :
    ∃ k : ℕ, ∀ (x : X) (a : X.presheaf.stalk x) (j : ℕ),
      (X.presheaf.Γgerm x).hom t ^ j * a = 0 → (X.presheaf.Γgerm x).hom t ^ k * a = 0 := by
  classical
  have hloc : ∀ U : X.affineOpens, ∃ e : ℕ, ∀ x (hx : x ∈ U.1) (a : X.presheaf.stalk x)
      (j : ℕ), (X.presheaf.Γgerm x).hom t ^ j * a = 0 → (X.presheaf.Γgerm x).hom t ^ e * a = 0 := by
    intro U
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨e, he⟩ := exists_forall_pow_mul_eq_zero_of_isNoetherianRing
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t)
    refine ⟨e, fun x hx a j ha => ?_⟩
    let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
    have hL : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hx⟩).asIdeal :=
      U.2.isLocalization_stalk ⟨x, hx⟩
    have hgerm : algebraMap Γ(X, U.1) (X.presheaf.stalk x)
        (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t) = (X.presheaf.Γgerm x).hom t :=
      X.presheaf.Γgerm_res_apply x hx t
    rw [← hgerm] at ha ⊢
    exact pow_mul_eq_zero_of_isLocalization (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl he a j
      ha
  choose e he using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := (X.isBasis_affineOpens).exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  refine ⟨s.sup e, fun x a j ha => ?_⟩
  obtain ⟨U, hUs, hxU⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  have h := he U x hxU a j ha
  rw [← Nat.sub_add_cancel (Finset.le_sup hUs : e U ≤ s.sup e), pow_add, mul_assoc, h,
    mul_zero]

end Stacks.AlgebraicGeometry.FreenessOverDVR
