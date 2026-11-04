module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineFibre

/-!
# When the support of a principal divisor in a fibre is not a union of components

Stacks 053R concludes that the support of a locally principal closed subscheme inside a fibre is
set-theoretically a union of irreducible components of that fibre. The last paragraph of the
source's proof reduces the general case to the Noetherian case by descending an affine situation
`A ⊆ B`, `g ∈ B`, `𝔭 ⊆ A` to a finitely generated `ℤ`-algebra, and the contradiction it then
derives is between that conclusion and two of the five conditions carried along the descent:

* (4) the image of `g` in `κ(𝔭) ⊗[A] B` is not a unit, and
* (5) the image of `g` in `κ(𝔭) ⊗[A] B` lies in no minimal prime of `κ(𝔭) ⊗[A] B`.

This file supplies that contradiction. Condition (4) says the support of `g` in the fibre is
nonempty and condition (5) says no irreducible component of the fibre is contained in it, so the
union of the components it contains is empty and cannot be the support. The statement is given
both for the fibre ring (`PrimeSpectrum.zeroLocus_singleton_ne_sUnion_irreducibleComponents`) and,
through the affine fibre dictionary, for the scheme-theoretic fibre in the shape 053R's
conclusion takes
(`AlgebraicGeometry.fiberι_preimage_zeroLocus_ne_sUnion_irreducibleComponents`).

Conditions (2) and (4) of the source are the same assertion at two different primes — at `𝔭 = ⊥`
and at `𝔭` itself — and `PrimeSpectrum.not_isUnit_algebraMap_fiber_iff` is that assertion in
`PrimeSpectrum` terms: the image of `g` in `κ(𝔭) ⊗[A] B` fails to be a unit exactly when some
prime of `B` lying over `𝔭` contains `g`.

## Main results

* `Homeomorph.image_mem_irreducibleComponents`,
  `Homeomorph.image_irreducibleComponents` and
  `Homeomorph.eq_sUnion_irreducibleComponents_image` transport irreducible components, and the
  shape of 053R's conclusion, along a homeomorphism.
* `PrimeSpectrum.nonempty_zeroLocus_singleton_iff`: the support of `g` is nonempty exactly when
  `g` is not a unit. This is condition (4) read as a statement about the support.
* `PrimeSpectrum.exists_mem_irreducibleComponents_subset_zeroLocus_singleton_iff`: an irreducible
  component is contained in the support of `g` exactly when some minimal prime contains `g`. This
  is condition (5) read the same way.
* `PrimeSpectrum.not_isUnit_algebraMap_fiber_iff`: conditions (2) and (4) in `PrimeSpectrum`
  terms.
* `PrimeSpectrum.zeroLocus_singleton_ne_sUnion_irreducibleComponents`: **the contradiction.**
  Under (4) and (5) the support of `g` is not a union of irreducible components.
* `AlgebraicGeometry.fiberι_preimage_zeroLocus_ne_sUnion_irreducibleComponents`: the same
  statement about the scheme-theoretic fibre of `Spec B ⟶ Spec A`, in the exact shape of 053R's
  conclusion.
* `PrimeSpectrum.exists_not_isUnit_forall_notMem_minimalPrimes`: conditions (4) and (5) are
  jointly satisfiable — `X` in `ℚ[X]` satisfies both — so the contradiction above is not derived
  from an empty hypothesis set.

## Implementation notes

The algebra structure of `κ(𝔭) ⊗[A] B` over `B` is `Algebra.TensorProduct.rightAlgebra`, enabled
here by `attribute [local instance]` as in
`StacksFrontier.AlgebraicGeometry.FibreDimension.AffineFibre`; enable it the same way to use the
statements mentioning `algebraMap B (𝔭.asIdeal.Fiber B)`.

`Homeomorph.eq_sUnion_irreducibleComponents_image` is stated as a transport of the *equation*
rather than of the family of components, because that is how it is consumed: the conclusion of
053R is an equation between a set and the union of the components it contains, and both sides
move at once.

## References

* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
-/

@[expose] public section

open CategoryTheory

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Transport along a homeomorphism -/

/-- Homeomorphisms carry irreducible components to irreducible components. -/
public theorem Homeomorph.image_mem_irreducibleComponents {α : Type u} {β : Type v}
    [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) {Z : Set α}
    (hZ : Z ∈ irreducibleComponents α) : e '' Z ∈ irreducibleComponents β := by
  rw [irreducibleComponents_eq_maximals_closed] at hZ ⊢
  refine ⟨⟨e.isClosed_image.mpr hZ.1.1, hZ.1.2.image e e.continuous.continuousOn⟩, ?_⟩
  rintro C ⟨hCcl, hCirr⟩ hle
  have hsub : Z ⊆ e.symm '' C := fun z hz => ⟨e z, hle ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩
  have h2 : e.symm '' C ⊆ Z :=
    hZ.2 ⟨e.symm.isClosed_image.mpr hCcl, hCirr.image _ e.symm.continuous.continuousOn⟩ hsub
  exact fun y hy => ⟨e.symm y, h2 ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

/-- The irreducible components of homeomorphic spaces correspond. -/
public theorem Homeomorph.image_irreducibleComponents {α : Type u} {β : Type v}
    [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) :
    (fun Z => e '' Z) '' irreducibleComponents α = irreducibleComponents β := by
  refine Set.Subset.antisymm ?_ fun C hC => ?_
  · rintro _ ⟨Z, hZ, rfl⟩
    exact e.image_mem_irreducibleComponents hZ
  · exact ⟨e.symm '' C, e.symm.image_mem_irreducibleComponents hC,
      by simp only [Set.image_image, Homeomorph.apply_symm_apply, Set.image_id']⟩

/-- Being the union of the ambient irreducible components it contains — the shape of the
conclusion of Stacks 053R — is a homeomorphism invariant. -/
public theorem Homeomorph.eq_sUnion_irreducibleComponents_image {α : Type u} {β : Type v}
    [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) {W : Set α}
    (h : W = ⋃₀ {Z : Set α | Z ∈ irreducibleComponents α ∧ Z ⊆ W}) :
    e '' W = ⋃₀ {Z : Set β | Z ∈ irreducibleComponents β ∧ Z ⊆ e '' W} := by
  refine Set.Subset.antisymm ?_ (Set.sUnion_subset fun _ hZ => hZ.2)
  rintro _ ⟨x, hx, rfl⟩
  rw [h] at hx
  obtain ⟨Z, ⟨hZ, hZW⟩, hxZ⟩ := hx
  exact ⟨e '' Z, ⟨e.image_mem_irreducibleComponents hZ, Set.image_mono hZW⟩, ⟨x, hxZ, rfl⟩⟩

/-- Being the union of the ambient irreducible components it contains transports forward along a
homeomorphism carrying the one set to the other. -/
public theorem Homeomorph.eq_sUnion_irreducibleComponents_of_image {α : Type u} {β : Type v}
    [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) {W : Set α} {V : Set β}
    (hWV : e '' W = V)
    (h : W = ⋃₀ {Z : Set α | Z ∈ irreducibleComponents α ∧ Z ⊆ W}) :
    V = ⋃₀ {Z : Set β | Z ∈ irreducibleComponents β ∧ Z ⊆ V} :=
  hWV ▸ e.eq_sUnion_irreducibleComponents_image h

/-- A set that fails to be the union of the ambient irreducible components it contains has that
failure transported back along a homeomorphism carrying it to the given set. -/
public theorem Homeomorph.ne_sUnion_irreducibleComponents_of_image {α : Type u} {β : Type v}
    [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) {W : Set α} {V : Set β}
    (hWV : e '' W = V)
    (hV : V ≠ ⋃₀ {Z : Set β | Z ∈ irreducibleComponents β ∧ Z ⊆ V}) :
    W ≠ ⋃₀ {Z : Set α | Z ∈ irreducibleComponents α ∧ Z ⊆ W} :=
  fun h => hV (hWV ▸ e.eq_sUnion_irreducibleComponents_image h)

namespace PrimeSpectrum

/-! ### The support of a single element of a ring -/

variable {C : Type u} [CommRing C]

/-- The support of an element is nonempty exactly when the element is not a unit. This is
condition (4) of the last paragraph of the proof of Stacks 053R, read as a statement about the
support. -/
public theorem nonempty_zeroLocus_singleton_iff (g : C) :
    (zeroLocus {g} : Set (PrimeSpectrum C)).Nonempty ↔ ¬ IsUnit g := by
  rw [Set.nonempty_iff_ne_empty, ← Ideal.span_singleton_eq_top (α := C) (x := g),
    ← zeroLocus_span]
  exact not_congr zeroLocus_empty_iff_eq_top

/-- The closed set cut out by a prime ideal lies in the support of `g` exactly when the prime
contains `g`. -/
public theorem zeroLocus_subset_zeroLocus_singleton_iff_mem {Q : Ideal C} (hQ : Q.IsPrime)
    (g : C) : zeroLocus (Q : Set C) ⊆ zeroLocus {g} ↔ g ∈ Q := by
  rw [← zeroLocus_span {g}, zeroLocus_subset_zeroLocus_iff, hQ.radical, Ideal.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe]

/-- An irreducible component of `Spec C` lies in the support of `g` exactly when some minimal
prime of `C` contains `g`. This is condition (5) of the last paragraph of the proof of
Stacks 053R, read as a statement about the support. -/
public theorem exists_mem_irreducibleComponents_subset_zeroLocus_singleton_iff (g : C) :
    (∃ Z ∈ irreducibleComponents (PrimeSpectrum C), Z ⊆ zeroLocus {g}) ↔
      ∃ Q ∈ minimalPrimes C, g ∈ Q := by
  rw [← zeroLocus_minimalPrimes]
  constructor
  · rintro ⟨Z, ⟨Q, hQ, rfl⟩, hZ⟩
    exact ⟨Q, hQ, (zeroLocus_subset_zeroLocus_singleton_iff_mem hQ.1.1 g).mp hZ⟩
  · rintro ⟨Q, hQ, hgQ⟩
    exact ⟨zeroLocus (Q : Set C), ⟨Q, hQ, rfl⟩,
      (zeroLocus_subset_zeroLocus_singleton_iff_mem hQ.1.1 g).mpr hgQ⟩

/-- **The contradiction that closes the reduction of Stacks 053R to the Noetherian case.** If `g`
is not a unit of `C` and lies in no minimal prime of `C`, then the support of `g` in `Spec C` is
*not* the union of the irreducible components of `Spec C` contained in it: it is nonempty by the
first hypothesis, while by the second no irreducible component is contained in it, so that union
is empty. -/
public theorem zeroLocus_singleton_ne_sUnion_irreducibleComponents (g : C)
    (hunit : ¬ IsUnit g) (hmin : ∀ Q ∈ minimalPrimes C, g ∉ Q) :
    (zeroLocus {g} : Set (PrimeSpectrum C)) ≠
      ⋃₀ {Z : Set (PrimeSpectrum C) | Z ∈ irreducibleComponents (PrimeSpectrum C) ∧
        Z ⊆ zeroLocus {g}} := by
  intro h
  obtain ⟨x, hx⟩ := (nonempty_zeroLocus_singleton_iff g).mpr hunit
  rw [h] at hx
  obtain ⟨Z, ⟨hZ, hZg⟩, -⟩ := hx
  obtain ⟨Q, hQ, hgQ⟩ :=
    (exists_mem_irreducibleComponents_subset_zeroLocus_singleton_iff g).mp ⟨Z, hZ, hZg⟩
  exact hmin Q hQ hgQ

/-- In a domain the only minimal prime is `⊥`, so every nonzero element lies in no minimal
prime. -/
public theorem forall_notMem_minimalPrimes_of_ne_zero [IsDomain C] {g : C} (hg : g ≠ 0) :
    ∀ Q ∈ minimalPrimes C, g ∉ Q :=
  fun _ hQ hgQ => hg (Ideal.mem_bot.mp (hQ.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le hgQ))

/-- **Non-vacuity.** The two hypotheses of
`PrimeSpectrum.zeroLocus_singleton_ne_sUnion_irreducibleComponents` — conditions (4) and (5) of
the last paragraph of the proof of Stacks 053R — are jointly satisfiable: the variable `X` of
`ℚ[X]` is not a unit and, `ℚ[X]` being a domain, lies in no minimal prime. So that theorem is not
derived from contradictory hypotheses, and the shape it refutes is a genuine constraint. -/
public theorem exists_not_isUnit_forall_notMem_minimalPrimes :
    ∃ (D : Type) (_ : CommRing D) (g : D), ¬ IsUnit g ∧ ∀ Q ∈ minimalPrimes D, g ∉ Q :=
  ⟨Polynomial ℚ, inferInstance, Polynomial.X,
    Polynomial.not_isUnit_X, forall_notMem_minimalPrimes_of_ne_zero Polynomial.X_ne_zero⟩

/-! ### The fibre ring -/

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A)

/-- **Conditions (2) and (4) of the last paragraph of the proof of Stacks 053R.** The image of
`g ∈ B` in the fibre ring `κ(𝔭) ⊗[A] B` fails to be a unit exactly when some prime of `B` lying
over `𝔭` contains `g`, i.e. exactly when the closed subscheme cut out by `g` meets the fibre
over `𝔭`.

At `𝔭 = ⊥` for `A` a domain this is condition (2), that `g ⊗ 1` is invertible in `B ⊗_A K`; at a
general `𝔭` it is condition (4). -/
public theorem not_isUnit_algebraMap_fiber_iff (g : B) :
    ¬ IsUnit (algebraMap B (p.asIdeal.Fiber B) g) ↔
      ∃ 𝔮 : PrimeSpectrum B, comap (algebraMap A B) 𝔮 = p ∧ g ∈ 𝔮.asIdeal := by
  rw [← nonempty_zeroLocus_singleton_iff]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨comap (algebraMap B (p.asIdeal.Fiber B)) q,
      (exists_comap_eq_iff_comap_algebraMap_eq A B p _).mp ⟨q, rfl⟩,
      (mem_zeroLocus _ _).mp hq (Set.mem_singleton _)⟩
  · rintro ⟨𝔮, h𝔮, hg⟩
    obtain ⟨q, hq⟩ := (exists_comap_eq_iff_comap_algebraMap_eq A B p 𝔮).mpr h𝔮
    exact ⟨q, (mem_zeroLocus _ _).mpr (Set.singleton_subset_iff.mpr
      (hq ▸ hg : g ∈ (comap (algebraMap B (p.asIdeal.Fiber B)) q).asIdeal))⟩

end PrimeSpectrum

namespace AlgebraicGeometry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A)

/-- The support of `g ∈ B` inside the scheme-theoretic fibre of `Spec B ⟶ Spec A` over `𝔭` is,
under `AlgebraicGeometry.fiberSpecHomeo`, the support of the image of `g` in the fibre ring
`κ(𝔭) ⊗[A] B`. -/
public theorem fiberSpecHomeo_image_preimage_zeroLocus (g : B) :
    fiberSpecHomeo A B p ''
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ⁻¹'
          (PrimeSpectrum.zeroLocus {g} : Set (PrimeSpectrum B))) =
      (PrimeSpectrum.zeroLocus {algebraMap B (p.asIdeal.Fiber B) g} :
        Set (PrimeSpectrum (p.asIdeal.Fiber B))) :=
  (fiberSpecHomeo_image_preimage A B p _).trans <| by
    rw [PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton]

/-- **The far end of the reduction of Stacks 053R to the Noetherian case, for an affine
morphism.** Let `g ∈ B` and let `𝔭` be a prime of `A`. If the image of `g` in the fibre ring
`κ(𝔭) ⊗[A] B` is not a unit and lies in no minimal prime of that ring — conditions (4) and (5)
of the last paragraph of the source's proof — then the support of `g` inside the scheme-theoretic
fibre of `Spec B ⟶ Spec A` over `𝔭` is *not* the union of the irreducible components of that
fibre contained in it.

This is the negation of the conclusion of Stacks 053R in the affine chart, so it is what
contradicts the Noetherian case once the descent has been carried out. -/
public theorem fiberι_preimage_zeroLocus_ne_sUnion_irreducibleComponents (g : B)
    (hunit : ¬ IsUnit (algebraMap B (p.asIdeal.Fiber B) g))
    (hmin : ∀ Q ∈ minimalPrimes (p.asIdeal.Fiber B),
      algebraMap B (p.asIdeal.Fiber B) g ∉ Q) :
    ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ⁻¹'
        (PrimeSpectrum.zeroLocus {g} : Set (PrimeSpectrum B))) ≠
      ⋃₀ {Z : Set ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber p) |
        Z ∈ irreducibleComponents ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber p) ∧
        Z ⊆ (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ⁻¹'
          (PrimeSpectrum.zeroLocus {g} : Set (PrimeSpectrum B))} :=
  (fiberSpecHomeo A B p).ne_sUnion_irreducibleComponents_of_image
    (fiberSpecHomeo_image_preimage_zeroLocus A B p g)
    (PrimeSpectrum.zeroLocus_singleton_ne_sUnion_irreducibleComponents _ hunit hmin)

end AlgebraicGeometry

end
