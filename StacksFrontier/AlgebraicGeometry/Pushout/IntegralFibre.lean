module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Separating the fibre of an integral morphism by a basic open

Let `Z ⟶ Y` be an integral morphism of schemes and let `y` be a point of `Y`.  The construction
of the pushout of [Stacks Project, Tag 0E25] rests on [Stacks Project, Tag 0ECJ], which needs
the following: if the fibre `j ⁻¹' {y}` is contained in an open `W` of an affine open of `Z`,
then it is already contained in a *basic* open contained in `W`.

The source proves this by appealing to [Stacks Project, Tag 0E21], a lemma about a scheme
carrying an ample invertible sheaf whose proof writes the scheme as a limit of schemes of finite
type over `ℤ`.  That machinery is not needed for the affine case, which is the only case Tag
0ECJ uses: this file proves it outright and elementarily.

The mathematical content is the ring-theoretic statement
`Stacks.Pushout.exists_mem_isUnit_of_map_eq_top`.  Given a ring map `φ : R →+* A` whose target is
integral over a field and an ideal `J` of `R` generating the unit ideal of `A`, *some single
element of `J`* already has unit image.  The hypothesis cannot be dropped to "the image of `J`
generates the unit ideal pointwise": the witnesses must be combined, and the combination has to
have coefficients in `R`, which is why the proof passes to a finite subalgebra of `A` and then
uses prime avoidance.

## Main results

* `Stacks.Pushout.exists_mem_isUnit_of_map_eq_top`: the ring-theoretic core.
* `Stacks.Pushout.exists_basicOpen_range_comap`: for `φ : R →+* A` with `A` integral over a
  field, the image of `Spec A` in `Spec R` is contained in a basic open contained in any given
  open containing it.
* `Stacks.Pushout.exists_basicOpen_image_fibre`: the form used by Tag 0ECJ, where the image is
  that of a fibre of an integral algebra.
* `Stacks.Pushout.exists_basicOpen_fibre`: the special case where no further ring map
  intervenes.

## Implementation notes

The fibre of `Spec S → Spec R` over a prime `p` is Mathlib's `Ideal.Fiber`, that is
`κ(p) ⊗[R] S`, and `PrimeSpectrum.preimageEquivFiber` identifies its prime spectrum with the
set-theoretic fibre.  Only the *inverse* direction of that equivalence is used, namely that it is
`PrimeSpectrum.comap Algebra.TensorProduct.includeRight`; this makes
`Stacks.Pushout.range_comap_includeRight` a statement about a range of `comap`, which is the
shape `Stacks.Pushout.exists_basicOpen_range_comap` consumes.

Being integral over a *field* is what makes the finite subalgebra artinian, hence with finitely
many maximal ideals, hence amenable to prime avoidance.  Integrality over the field is used
nowhere else, and the base could be any artinian ring.

The results are not tagged.  `Stacks.Pushout.exists_basicOpen_range_comap` is the case of Tag
0E21 in which the scheme is affine and the invertible sheaf is the structure sheaf; Tag 0E21
itself asserts more (an arbitrary scheme with an ample invertible sheaf, and a section of a
tensor power) and its proof needs the limit machinery of the Limits chapter, so claiming the tag
here would overstate what is proved.

## References

* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECJ](https://stacks.math.columbia.edu/tag/0ECJ)
-/

@[expose] public section

open PrimeSpectrum

namespace Stacks.Pushout

/-- **The ring-theoretic core.**  Let `φ : R →+* A` be a ring map whose target is integral over a
field `k`, and let `J` be an ideal of `R` whose image generates the unit ideal of `A`.  Then a
single element of `J` has unit image.

The element is produced by prime avoidance inside the subring of `R` mapping into a finite
`k`-subalgebra `B` of `A` large enough to contain a finite generating family: `B` is artinian, so
it has finitely many maximal ideals, and going up supplies for each of them a prime of `A` above
it which some member of the family avoids. -/
theorem exists_mem_isUnit_of_map_eq_top {k A R : Type*} [Field k] [CommRing A] [CommRing R]
    (ι : k →+* A) (hι : ι.IsIntegral) (φ : R →+* A) {J : Ideal R} (hJ : J.map φ = ⊤) :
    ∃ f ∈ J, IsUnit (φ f) := by
  classical
  let _ : Algebra k A := ι.toAlgebra
  have : Algebra.IsIntegral k A := ⟨fun x => hι x⟩
  -- A finite family in the image of `J` generating the unit ideal of `A`.
  have h1 : (1 : A) ∈ Ideal.span (φ '' (J : Set R)) := by
    rw [show Ideal.span (φ '' (J : Set R)) = J.map φ from rfl, hJ]
    trivial
  obtain ⟨t, hts, h1t⟩ := Submodule.mem_span_finite_of_mem_span h1
  have htop : Ideal.span (t : Set A) = ⊤ := Ideal.eq_top_of_isUnit_mem _ h1t isUnit_one
  -- An artinian `k`-subalgebra of `A` containing that family.
  have : Module.Finite k (Algebra.adjoin k (t : Set A)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
      fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨B, hBart, hBt⟩ : ∃ B : Subalgebra k A, IsArtinianRing B ∧ (t : Set A) ⊆ (B : Set A) :=
    ⟨Algebra.adjoin k (t : Set A), IsArtinianRing.of_finite k _, Algebra.subset_adjoin⟩
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.tower_top (R := k)
  -- Every maximal ideal of `B` is avoided by a member of the family.
  have key : ∀ q : Ideal B, q.IsMaximal → ∃ a ∈ t, ∃ ha : a ∈ B, (⟨a, ha⟩ : B) ∉ q := by
    intro q hq
    have hle : Ideal.comap (algebraMap B A) ⊥ ≤ q := by
      intro x hx
      simp only [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [show x = 0 from Subtype.ext hx]
      exact q.zero_mem
    obtain ⟨Q, -, hQp, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := A) q ⊥ hle
    obtain ⟨a, hat, haQ⟩ := Set.not_subset.mp fun h : (t : Set A) ⊆ (Q : Set A) =>
      hQp.ne_top (top_le_iff.mp (htop ▸ Ideal.span_le.mpr h))
    refine ⟨a, hat, hBt hat, fun hmem => haQ ?_⟩
    simpa using (hQq.symm ▸ hmem : (⟨a, hBt hat⟩ : B) ∈ Q.under B)
  -- Prime avoidance in the subring of `R` mapping into `B`.
  let R₀ : Subring R := Subring.comap φ B.toSubring
  let ψ : R₀ →+* B :=
    { toFun := fun r => ⟨φ r.1, r.2⟩
      map_one' := Subtype.ext φ.map_one
      map_mul' := fun _ _ => Subtype.ext (φ.map_mul _ _)
      map_zero' := Subtype.ext φ.map_zero
      map_add' := fun _ _ => Subtype.ext (φ.map_add _ _) }
  let s : Finset (Ideal B) := (IsArtinianRing.setOfPred_isMaximal_finite _).toFinset
  have hmem_s : ∀ q : Ideal B, q ∈ s ↔ q.IsMaximal := fun q => by simp [s]
  let T : Ideal R₀ := Ideal.comap R₀.subtype J
  have hprime : ∀ q ∈ s, q ≠ ⊥ → q ≠ ⊥ → (Ideal.comap ψ q).IsPrime := fun q hq _ _ =>
    have : q.IsPrime := ((hmem_s q).mp hq).isPrime
    Ideal.comap_isPrime ψ q
  have hnotle : ¬ ∃ q ∈ s, T ≤ Ideal.comap ψ q := by
    rintro ⟨q, hq, hle⟩
    obtain ⟨a, hat, ha, haq⟩ := key q ((hmem_s q).mp hq)
    obtain ⟨f, hfJ, hfa⟩ := hts hat
    have hfR₀ : f ∈ R₀ := by
      show φ f ∈ B.toSubring
      rwa [hfa]
    exact haq (by simpa [ψ, hfa] using hle (show (⟨f, hfR₀⟩ : R₀) ∈ T from hfJ))
  have hiff := Ideal.subset_union_prime (f := fun q : Ideal B => Ideal.comap ψ q) (s := s)
    ⊥ ⊥ hprime (I := T)
  obtain ⟨x, hxT, hx⟩ := Set.not_subset.mp fun h => hnotle (hiff.mp h)
  have hunit : IsUnit (ψ x) := by
    by_contra hu
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {ψ x})
      fun h => hu (Ideal.span_singleton_eq_top.mp h)
    exact hx (Set.mem_biUnion ((hmem_s M).mpr hM)
      (show x ∈ Ideal.comap ψ M from hle (Ideal.mem_span_singleton_self _)))
  exact ⟨(x : R), hxT, by simpa [ψ] using hunit.map (Subalgebra.val B)⟩

/-- A basic open of `Spec R` is contained in an open `W` exactly when the element lies in the
ideal of functions vanishing on the complement of `W`. -/
theorem basicOpen_subset_iff_mem_vanishingIdeal {R : Type*} [CommRing R]
    (W : Set (PrimeSpectrum R)) (f : R) :
    (basicOpen f : Set (PrimeSpectrum R)) ⊆ W ↔ f ∈ vanishingIdeal Wᶜ := by
  rw [← Set.compl_subset_compl (s := W), basicOpen_eq_zeroLocus_compl, compl_compl,
    subset_zeroLocus_iff_subset_vanishingIdeal]
  simp

/-- **A basic open separating the image of a spectrum integral over a field.**  Let
`φ : R →+* A` with `A` integral over a field, and let `W` be an open of `Spec R` containing the
image of `Spec A`.  Then that image is contained in a basic open contained in `W`.

This is the affine case of [Stacks Project, Tag 0E21] with the structure sheaf as the ample
invertible sheaf; see the module documentation for why the tag is not claimed. -/
theorem exists_basicOpen_range_comap {k A R : Type*} [Field k] [CommRing A] [CommRing R]
    (ι : k →+* A) (hι : ι.IsIntegral) (φ : R →+* A) {W : Set (PrimeSpectrum R)} (hW : IsOpen W)
    (hr : Set.range (comap φ) ⊆ W) :
    ∃ f : R, Set.range (comap φ) ⊆ (basicOpen f : Set (PrimeSpectrum R)) ∧
      (basicOpen f : Set (PrimeSpectrum R)) ⊆ W := by
  have htop : (vanishingIdeal Wᶜ).map φ = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hp : comap φ ⟨M, hM.isPrime⟩ ∉ zeroLocus (vanishingIdeal Wᶜ) := by
      rw [zeroLocus_vanishingIdeal_eq_closure, hW.isClosed_compl.closure_eq]
      simpa using hr ⟨⟨M, hM.isPrime⟩, rfl⟩
    rw [mem_zeroLocus] at hp
    obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp hp
    exact hfp (hle (Ideal.mem_map_of_mem φ hfI))
  obtain ⟨f, hfI, hfu⟩ := exists_mem_isUnit_of_map_eq_top ι hι φ htop
  refine ⟨f, ?_, (basicOpen_subset_iff_mem_vanishingIdeal W f).mpr hfI⟩
  rintro p ⟨q, rfl⟩
  simp only [SetLike.mem_coe, mem_basicOpen, comap_asIdeal, Ideal.mem_comap]
  exact fun h => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hfu)

/-- The image of the prime spectrum of the fibre `κ(p) ⊗[R] S` in `Spec S` is the set-theoretic
fibre of `Spec S → Spec R` over `p`.  Only the inverse of `PrimeSpectrum.preimageEquivFiber` is
used, which is `PrimeSpectrum.comap Algebra.TensorProduct.includeRight`. -/
theorem range_comap_includeRight {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) :
    Set.range (comap (Algebra.TensorProduct.includeRight
        (R := R) (A := p.asIdeal.ResidueField) (B := S)).toRingHom) =
      comap (algebraMap R S) ⁻¹' {p} := by
  refine Set.eq_of_subset_of_subset ?_ fun q hq => ⟨preimageEquivFiber R S p ⟨q, hq⟩, ?_⟩
  · rintro q ⟨q', rfl⟩
    exact ((preimageEquivFiber R S p).symm q').2
  · exact congrArg Subtype.val ((preimageEquivFiber R S p).symm_apply_apply ⟨q, hq⟩)

/-- **The form used by [Stacks Project, Tag 0ECJ].**  Let `S` be integral over `R`, let `p` be a
prime of `R`, and let `ψ : T →+* S` be any ring map — in the application `Spec S` is an affine
open of the source of the integral morphism, `T` is the ring of a larger affine open containing
it, and `ψ` is the restriction map.  If an open `W` of `Spec T` contains the image of the fibre
of `Spec S → Spec R` over `p`, then that image lies in a basic open contained in `W`. -/
theorem exists_basicOpen_image_fibre {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra.IsIntegral R S] (p : PrimeSpectrum R) (ψ : T →+* S)
    {W : Set (PrimeSpectrum T)} (hW : IsOpen W)
    (hr : comap ψ '' (comap (algebraMap R S) ⁻¹' {p}) ⊆ W) :
    ∃ f : T, comap ψ '' (comap (algebraMap R S) ⁻¹' {p}) ⊆
        (basicOpen f : Set (PrimeSpectrum T)) ∧
      (basicOpen f : Set (PrimeSpectrum T)) ⊆ W := by
  let A := p.asIdeal.Fiber S
  let φ : T →+* A := (Algebra.TensorProduct.includeRight
    (R := R) (A := p.asIdeal.ResidueField) (B := S)).toRingHom.comp ψ
  have hrange : Set.range (comap φ) =
      comap ψ '' (comap (algebraMap R S) ⁻¹' {p}) := by
    rw [← range_comap_includeRight p, ← Set.range_comp]
    exact congrArg Set.range (comap_comp _ _)
  obtain ⟨f, hf₁, hf₂⟩ := exists_basicOpen_range_comap
    (algebraMap p.asIdeal.ResidueField A) (Algebra.IsIntegral.isIntegral (R := _)) φ hW
    (hrange ▸ hr)
  exact ⟨f, hrange ▸ hf₁, hf₂⟩

/-- The special case of `Stacks.Pushout.exists_basicOpen_image_fibre` in which the fibre is
separated inside `Spec S` itself. -/
theorem exists_basicOpen_fibre {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : PrimeSpectrum R) {W : Set (PrimeSpectrum S)} (hW : IsOpen W)
    (hr : comap (algebraMap R S) ⁻¹' {p} ⊆ W) :
    ∃ f : S, comap (algebraMap R S) ⁻¹' {p} ⊆ (basicOpen f : Set (PrimeSpectrum S)) ∧
      (basicOpen f : Set (PrimeSpectrum S)) ⊆ W := by
  simpa using exists_basicOpen_image_fibre p (RingHom.id S) hW (by simpa using hr)

end Stacks.Pushout

end
