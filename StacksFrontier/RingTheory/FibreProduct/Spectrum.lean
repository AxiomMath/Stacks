module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import StacksFrontier.RingTheory.FibreProduct

/-!
# Prime spectra of a fibre product of rings

Let `B → A` be a ring map and let `A' → A` be a surjection.  The prime spectrum of the fibre
product `B ×_A A'` is the pushout of `Spec B` and `Spec A'` over `Spec A`, taken in the category
of topological spaces.  Set-theoretically this says that a prime of `B ×_A A'` is either a prime
of `B` or a prime of `A'`, glued along the primes of `A`.

## Main results

* `RingFibreProduct.primeSpectrum_isPushout` is Stacks Tag 0B7J: the canonical square of prime
  spectra attached to a fibre product situation is a pushout square in `TopCat`.

## Implementation notes

The conclusion is phrased with `CategoryTheory.IsPushout`, which records the canonical maps and
the full universal property without choosing a particular pushout object; pushouts in `TopCat`
come from the standard colimit construction.  The proof identifies the underlying set of
`Spec (B ×_A A')` with the set-theoretic pushout and then checks that the resulting bijection is
a quotient map, using that the second projection `B ×_A A' → A'` is surjective and that the
first has the kernel of `A' → A` as its image.

## References

* [Stacks Project, Tag 0B7J](https://stacks.math.columbia.edu/tag/0B7J)
-/

section

section
open CategoryTheory CategoryTheory.Limits

namespace RingFibreProduct
universe u

private lemma sumElim_eq_of_sumElim_eq
    {W X Y P : TopCat.{u}} {f : W ⟶ X} {g : W ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (hi : Function.Injective i)
    (hcross : ∀ x y, i x = j y → ∃ w, f w = x ∧ g w = y)
    (hself : ∀ y y', j y = j y' → y = y' ∨
      ∃ w w', g w = y ∧ g w' = y' ∧ f w = f w')
    (s : PushoutCocone f g) (z z' : X ⊕ Y) (h : Sum.elim i j z = Sum.elim i j z') :
    Sum.elim s.inl s.inr z = Sum.elim s.inl s.inr z' := by
  rcases z with x | y <;> rcases z' with x' | y'
  · simp [hi h]
  · obtain ⟨w, hw, hw'⟩ := hcross x y' h
    simpa [← hw, ← hw', ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom s.condition w
  · obtain ⟨w, hw, hw'⟩ := hcross x' y h.symm
    simpa [← hw, ← hw', ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom s.condition w).symm
  · rcases hself y y' h with rfl | ⟨w, w', hw, hw', heq⟩
    · rfl
    · calc
        s.inr y = s.inl (f w) := by
          rw [← hw]
          exact (ConcreteCategory.congr_hom s.condition w).symm
        _ = s.inl (f w') := by rw [heq]
        _ = s.inr y' := by
          rw [← hw']
          exact ConcreteCategory.congr_hom s.condition w'

private lemma isPushout_of_quotientMap_sum
    {W X Y P : TopCat.{u}} {f : W ⟶ X} {g : W ⟶ Y}
    {i : X ⟶ P} {j : Y ⟶ P}
    (sq : f ≫ i = g ≫ j)
    (hi : Function.Injective i)
    (hcross : ∀ x y, i x = j y → ∃ w, f w = x ∧ g w = y)
    (hself : ∀ y y', j y = j y' → y = y' ∨
      ∃ w w', g w = y ∧ g w' = y' ∧ f w = f w')
    (hq : Topology.IsQuotientMap (Sum.elim i j)) : IsPushout f g i j := by
  apply IsPushout.of_isColimit' ⟨sq⟩
  refine PushoutCocone.isColimitAux' _ (fun s ↦ ?_)
  let q : X ⊕ Y → P := Sum.elim i j
  let e : P → X ⊕ Y := Function.Surjective.hasRightInverse hq.surjective |>.choose
  let d : P → s.pt := Sum.elim s.inl s.inr ∘ e
  have he : Function.RightInverse e q :=
    Function.Surjective.hasRightInverse hq.surjective |>.choose_spec
  have hdq : d ∘ q = Sum.elim s.inl s.inr := by
    funext z
    exact sumElim_eq_of_sumElim_eq hi hcross hself s _ _ (he (q z))
  refine ⟨TopCat.ofHom ⟨d, hq.continuous_iff.mpr ?_⟩, ?_, ?_, ?_⟩
  · rw [hdq]
    exact Continuous.sumElim s.inl.hom.continuous s.inr.hom.continuous
  · ext x
    exact congr_fun hdq (.inl x)
  · ext y
    exact congr_fun hdq (.inr y)
  · intro m hm hn
    apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨x, rfl⟩ := hq.surjective z
    rcases x with x | y
    · calc
        m (i x) = s.inl x := by
          change i ≫ m = s.inl at hm
          exact (ConcreteCategory.comp_apply i m x).symm.trans (ConcreteCategory.congr_hom hm x)
        _ = d (i x) := (congr_fun hdq (.inl x)).symm
    · calc
        m (j y) = s.inr y := by
          change j ≫ m = s.inr at hn
          exact (ConcreteCategory.comp_apply j m y).symm.trans (ConcreteCategory.congr_hom hn y)
        _ = d (j y) := (congr_fun hdq (.inr y)).symm

private lemma exists_isPrime_forall_mem_iff
    {R S : Type*} [CommRing R] [CommRing S] (P : Ideal R) (hP : P.IsPrime) {k : R}
    (hk : k ∉ P) (e : S → R) (e_zero : e 0 = 0) (e_add : ∀ x y, e (x + y) = e x + e y)
    (e_one : e 1 = k) (emul : ∀ x y, e (x * y) * k = e x * e y) :
    ∃ Q : Ideal S, Q.IsPrime ∧ ∀ x, x ∈ Q ↔ e x ∈ P := by
  let Q : Ideal S :=
    { carrier := {x | e x ∈ P}
      zero_mem' := by
        change e 0 ∈ P
        rw [e_zero]
        exact P.zero_mem
      add_mem' := by
        intro x y hx hy
        change e (x + y) ∈ P
        rw [e_add]
        exact P.add_mem hx hy
      smul_mem' := fun c x hx => by
        have := P.mul_mem_left (e c) hx
        rw [← emul] at this
        exact (hP.mem_or_mem this).resolve_right hk }
  refine ⟨Q, ⟨?_, ?_⟩, fun _ ↦ Iff.rfl⟩
  · intro htop
    have : (1 : S) ∈ Q := htop.symm ▸ Set.mem_univ 1
    change e 1 ∈ P at this
    rw [e_one] at this
    exact hk this
  · intro x y hxy
    have hprod : e x * e y ∈ P := by
      rw [← emul]
      exact P.mul_mem_right k hxy
    exact hP.mem_or_mem hprod

private lemma mem_range_comap_pullbackSnd_of_not_ker_le
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (q : PrimeSpectrum (f.pullback g))
    (hker : ¬ RingHom.ker (f.pullbackFst g) ≤ q.asIdeal) :
    q ∈ Set.range (PrimeSpectrum.comap (f.pullbackSnd g)) := by
  let R := f.pullback g
  let p₁ : R →+* B := f.pullbackFst g
  let p₂ : R →+* A' := f.pullbackSnd g
  change ¬ RingHom.ker p₁ ≤ q.asIdeal at hker
  obtain ⟨k, hk0, hk⟩ := Set.not_subset.mp hker
  have hgk : g (p₂ k) = 0 := by
    have hcompat : f (p₁ k) = g (p₂ k) := k.property
    rw [hk0, map_zero] at hcompat
    exact hcompat.symm
  let e : A' → R := fun x ↦ ⟨(0, p₂ k * x), by
    change f 0 = g (p₂ k * x)
    simp [hgk]⟩
  have e_zero : e 0 = 0 := by
    apply Subtype.ext
    apply Prod.ext <;> simp [e]
  have e_add (x y : A') : e (x + y) = e x + e y := by
    apply Subtype.ext
    apply Prod.ext <;> simp [e, mul_add]
  have e_one : e 1 = k := by
    apply Subtype.ext
    apply Prod.ext
    · change (0 : B) = p₁ k
      exact hk0.symm
    · change p₂ k * 1 = p₂ k
      simp
  have emul (x y : A') : e (x * y) * k = e x * e y := by
    apply Subtype.ext
    apply Prod.ext
    · change (0 : B) * p₁ k = (0 : B) * 0
      simp
    · change (p₂ k * (x * y)) * p₂ k = (p₂ k * x) * (p₂ k * y)
      ring
  have ep₂ (r : R) : e (p₂ r) = k * r := by
    apply Subtype.ext
    apply Prod.ext
    · change (0 : B) = p₁ k * p₁ r
      rw [hk0, zero_mul]
    · rfl
  obtain ⟨Q, hQ, hQe⟩ :=
    exists_isPrime_forall_mem_iff q.asIdeal q.isPrime hk e e_zero e_add e_one emul
  refine ⟨⟨Q, hQ⟩, PrimeSpectrum.ext ?_⟩
  ext r
  change p₂ r ∈ Q ↔ r ∈ q.asIdeal
  rw [hQe, ep₂]
  exact ⟨fun h ↦ (q.isPrime.mem_or_mem h).resolve_left hk, q.asIdeal.mul_mem_left k⟩

-- The elementary prime-ideal classification for a fibre product along a surjection.
private lemma spectrum_pullback_data
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g) :
    Function.Injective (PrimeSpectrum.comap (f.pullbackFst g)) ∧
      ∀ q : PrimeSpectrum (f.pullback g),
        q ∈ Set.range (PrimeSpectrum.comap (f.pullbackFst g)) ∨
          q ∈ Set.range (PrimeSpectrum.comap (f.pullbackSnd g)) := by
  let R := f.pullback g
  let p₁ : R →+* B := f.pullbackFst g
  let p₂ : R →+* A' := f.pullbackSnd g
  have hp₁ : Function.Surjective p₁ := RingHom.surjective_pullbackFst_of_surjective f g hg
  have hcover : ∀ q : PrimeSpectrum R,
      q ∈ Set.range (PrimeSpectrum.comap p₁) ∨
        q ∈ Set.range (PrimeSpectrum.comap p₂) := by
    intro q
    by_cases hker : RingHom.ker p₁ ≤ q.asIdeal
    · left
      rw [PrimeSpectrum.mem_range_comap_iff, Ideal.comap_map_of_surjective p₁ hp₁]
      exact sup_eq_left.mpr (by simpa only [RingHom.ker_eq_comap_bot] using hker)
    · exact .inr (mem_range_comap_pullbackSnd_of_not_ker_le f g q hker)
  exact ⟨PrimeSpectrum.comap_injective_of_surjective p₁ hp₁, hcover⟩

private lemma mem_range_comap_of_ker_le
    {A A' : Type u} [CommRing A] [CommRing A'] {g : A' →+* A} (hg : Function.Surjective g)
    {y : PrimeSpectrum A'} (h : RingHom.ker g ≤ y.asIdeal) :
    y ∈ Set.range (PrimeSpectrum.comap g) := by
  rw [range_comap_of_surjective A g hg, PrimeSpectrum.mem_zeroLocus]
  exact h

private lemma ker_pullbackFst_le_comap_iff
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (y : PrimeSpectrum A') :
    RingHom.ker (f.pullbackFst g) ≤ y.asIdeal.comap (f.pullbackSnd g) ↔
      RingHom.ker g ≤ y.asIdeal := by
  constructor
  · intro h a ha
    let r : f.pullback g := ⟨(0, a), by
      change f 0 = g a
      simpa using ha.symm⟩
    exact h (show (f.pullbackFst g) r = 0 from rfl)
  · intro h r hr
    have hc : f ((f.pullbackFst g) r) = g ((f.pullbackSnd g) r) := r.property
    have hr0 : (f.pullbackFst g) r = 0 := hr
    rw [hr0, map_zero] at hc
    exact h hc.symm

private lemma comap_pullbackSnd_mem_range_pullbackFst_iff
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g)
    (y : PrimeSpectrum A') :
    PrimeSpectrum.comap (f.pullbackSnd g) y ∈
        Set.range (PrimeSpectrum.comap (f.pullbackFst g)) ↔
      RingHom.ker g ≤ y.asIdeal := by
  let p₁ : f.pullback g →+* B := f.pullbackFst g
  have hp₁ : Function.Surjective p₁ :=
    RingHom.surjective_pullbackFst_of_surjective f g hg
  change PrimeSpectrum.comap (f.pullbackSnd g) y ∈
    Set.range (PrimeSpectrum.comap p₁) ↔ RingHom.ker g ≤ y.asIdeal
  rw [range_comap_of_surjective B p₁ hp₁,
    PrimeSpectrum.mem_zeroLocus]
  exact ker_pullbackFst_le_comap_iff f g y

private lemma comap_pullback_comm
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (w : PrimeSpectrum A) :
    PrimeSpectrum.comap (f.pullbackFst g) (PrimeSpectrum.comap f w) =
      PrimeSpectrum.comap (f.pullbackSnd g) (PrimeSpectrum.comap g w) := by
  calc
    _ = PrimeSpectrum.comap (f.comp (f.pullbackFst g)) w :=
      (PrimeSpectrum.comap_comp_apply (f.pullbackFst g) f w).symm
    _ = PrimeSpectrum.comap (g.comp (f.pullbackSnd g)) w := by
      rw [RingHom.pullback_comm_sq]
    _ = _ := PrimeSpectrum.comap_comp_apply (f.pullbackSnd g) g w

private lemma pullback_spectrum_cross
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g)
    (x : PrimeSpectrum B) (y : PrimeSpectrum A')
    (h : PrimeSpectrum.comap (f.pullbackFst g) x =
      PrimeSpectrum.comap (f.pullbackSnd g) y) :
    ∃ w : PrimeSpectrum A,
      PrimeSpectrum.comap f w = x ∧ PrimeSpectrum.comap g w = y := by
  obtain ⟨w, hw⟩ := mem_range_comap_of_ker_le hg
    ((comap_pullbackSnd_mem_range_pullbackFst_iff f g hg y).mp ⟨x, h⟩)
  refine ⟨w, ?_, hw⟩
  apply PrimeSpectrum.comap_injective_of_surjective (f.pullbackFst g)
    (RingHom.surjective_pullbackFst_of_surjective f g hg)
  rw [comap_pullback_comm f g w, hw]
  exact h.symm

private lemma pullback_spectrum_snd_fiber
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g)
    (y y' : PrimeSpectrum A')
    (h : PrimeSpectrum.comap (f.pullbackSnd g) y =
      PrimeSpectrum.comap (f.pullbackSnd g) y') :
    y = y' ∨ ∃ w w' : PrimeSpectrum A,
      PrimeSpectrum.comap g w = y ∧ PrimeSpectrum.comap g w' = y' ∧
        PrimeSpectrum.comap f w = PrimeSpectrum.comap f w' := by
  by_cases hyker : RingHom.ker g ≤ y.asIdeal
  · right
    have hy'ker : RingHom.ker g ≤ y'.asIdeal := by
      have hr := (comap_pullbackSnd_mem_range_pullbackFst_iff f g hg y).mpr hyker
      rw [h] at hr
      exact (comap_pullbackSnd_mem_range_pullbackFst_iff f g hg y').mp hr
    obtain ⟨w, hw⟩ := mem_range_comap_of_ker_le hg hyker
    obtain ⟨w', hw'⟩ := mem_range_comap_of_ker_le hg hy'ker
    refine ⟨w, w', hw, hw', ?_⟩
    apply PrimeSpectrum.comap_injective_of_surjective (f.pullbackFst g)
      (RingHom.surjective_pullbackFst_of_surjective f g hg)
    rw [comap_pullback_comm f g w, comap_pullback_comm f g w', hw, hw']
    exact h
  · left
    obtain ⟨k, hkker, hky⟩ := Set.not_subset.mp hyker
    have hgk : g k = 0 := hkker
    have heqmem (a' : A') : k * a' ∈ y.asIdeal ↔ k * a' ∈ y'.asIdeal := by
      let r : f.pullback g := ⟨(0, k * a'), by
        change f 0 = g (k * a')
        simp [hgk]⟩
      have hr := congrArg (fun q : PrimeSpectrum (f.pullback g) =>
        r ∈ q.asIdeal) h
      change (k * a' ∈ y.asIdeal) = (k * a' ∈ y'.asIdeal) at hr
      exact Iff.of_eq hr
    have hky' : k ∉ y'.asIdeal := fun hk' ↦
      hky (by simpa using (heqmem 1).mpr (by simpa using hk'))
    refine PrimeSpectrum.ext (Ideal.ext fun a' ↦ ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩)
    · exact (y'.isPrime.mem_or_mem ((heqmem a').mp (y.asIdeal.mul_mem_left k ha))).resolve_left
        hky'
    · exact (y.isPrime.mem_or_mem ((heqmem a').mpr (y'.asIdeal.mul_mem_left k ha))).resolve_left
        hky

private lemma zeroLocus_map_ideal
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal R) :
    PrimeSpectrum.zeroLocus (J.map f : Set S) =
      PrimeSpectrum.comap f ⁻¹' PrimeSpectrum.zeroLocus (J : Set R) := by
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    Ideal.map_le_iff_le_comap, Set.mem_preimage, PrimeSpectrum.comap_asIdeal]

private lemma mem_zeroLocus_of_comap_pullbackFst_mem
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g) {JB : Ideal B} {JA : Ideal A'}
    (hrad : (JB.map f).radical = (JA.map g).radical) (x : PrimeSpectrum B)
    (hx : PrimeSpectrum.comap (f.pullbackFst g) x ∈ PrimeSpectrum.zeroLocus
      ((JB.comap (f.pullbackFst g) ⊓ JA.comap (f.pullbackSnd g) : Ideal (f.pullback g)) :
        Set (f.pullback g))) :
    x ∈ PrimeSpectrum.zeroLocus (JB : Set B) := by
  rw [PrimeSpectrum.mem_zeroLocus] at hx ⊢
  intro b hb
  have hfb : f b ∈ (JB.map f).radical := Ideal.le_radical (Ideal.mem_map_of_mem f hb)
  rw [hrad, Ideal.mem_radical_iff] at hfb
  obtain ⟨n, hn⟩ := hfb
  have hpowJA : f (b ^ (n + 1)) ∈ JA.map g := by
    simpa only [map_pow, pow_succ, map_mul] using (JA.map g).mul_mem_right (f b) hn
  obtain ⟨a, ha, hga⟩ := (Ideal.mem_map_iff_of_surjective g hg).mp hpowJA
  let r : f.pullback g := ⟨(b ^ (n + 1), a), by
    change f (b ^ (n + 1)) = g a
    simpa only [map_pow] using hga.symm⟩
  have hrK : r ∈ JB.comap (f.pullbackFst g) ⊓ JA.comap (f.pullbackSnd g) := by
    change b ^ (n + 1) ∈ JB ∧ a ∈ JA
    exact ⟨by simpa only [pow_succ] using JB.mul_mem_left (b ^ n) hb, ha⟩
  exact x.isPrime.mem_of_pow_mem (n + 1) (hx hrK : b ^ (n + 1) ∈ x.asIdeal)

private lemma mem_zeroLocus_of_comap_pullbackSnd_mem
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) {JB : Ideal B} {JA : Ideal A'} (y : PrimeSpectrum A')
    (hyker : ¬ RingHom.ker g ≤ y.asIdeal)
    (hy : PrimeSpectrum.comap (f.pullbackSnd g) y ∈ PrimeSpectrum.zeroLocus
      ((JB.comap (f.pullbackFst g) ⊓ JA.comap (f.pullbackSnd g) : Ideal (f.pullback g)) :
        Set (f.pullback g))) :
    y ∈ PrimeSpectrum.zeroLocus (JA : Set A') := by
  obtain ⟨k, hk, hky⟩ := Set.not_subset.mp hyker
  have hgk : g k = 0 := hk
  change JA ≤ y.asIdeal
  intro a ha
  let r : f.pullback g := ⟨(0, k * a), by
    change f 0 = g (k * a)
    simp [hgk]⟩
  have hrK : r ∈ JB.comap (f.pullbackFst g) ⊓ JA.comap (f.pullbackSnd g) :=
    ⟨JB.zero_mem, JA.mul_mem_left k ha⟩
  have hka : k * a ∈ y.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hy hrK
  exact (y.isPrime.mem_or_mem hka).resolve_left hky

private lemma eq_zeroLocus_inf_comap_of_preimage_eq
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g)
    (C : Set (PrimeSpectrum (f.pullback g))) {JB : Ideal B} {JA : Ideal A'}
    (hJB : PrimeSpectrum.comap (f.pullbackFst g) ⁻¹' C = PrimeSpectrum.zeroLocus (JB : Set B))
    (hJA : PrimeSpectrum.comap (f.pullbackSnd g) ⁻¹' C =
      PrimeSpectrum.zeroLocus (JA : Set A')) :
    C = PrimeSpectrum.zeroLocus
      ((JB.comap (f.pullbackFst g) ⊓ JA.comap (f.pullbackSnd g) : Ideal (f.pullback g)) :
        Set (f.pullback g)) := by
  let R := f.pullback g
  let p₁ : R →+* B := f.pullbackFst g
  let p₂ : R →+* A' := f.pullbackSnd g
  change PrimeSpectrum.comap p₁ ⁻¹' C = _ at hJB
  change PrimeSpectrum.comap p₂ ⁻¹' C = _ at hJA
  have hdata := spectrum_pullback_data f g hg
  have hcompat : PrimeSpectrum.zeroLocus (JB.map f : Set A) =
      PrimeSpectrum.zeroLocus (JA.map g : Set A) := by
    rw [zeroLocus_map_ideal f JB, zeroLocus_map_ideal g JA]
    ext w
    have hsquare := comap_pullback_comm f g w
    change (PrimeSpectrum.comap f w ∈ PrimeSpectrum.zeroLocus (JB : Set B)) ↔
      (PrimeSpectrum.comap g w ∈ PrimeSpectrum.zeroLocus (JA : Set A'))
    rw [← hJB, ← hJA]
    exact Iff.of_eq (congrArg (fun z : PrimeSpectrum R ↦ z ∈ C) hsquare)
  have hBmem := mem_zeroLocus_of_comap_pullbackFst_mem f g hg
    (PrimeSpectrum.zeroLocus_eq_iff.mp hcompat)
  refine Set.ext fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · rcases hdata.2 z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · have hxC : x ∈ PrimeSpectrum.zeroLocus (JB : Set B) := hJB ▸ hz
      rw [PrimeSpectrum.mem_zeroLocus] at hxC ⊢
      intro r hr
      exact hxC hr.1
    · have hyC : y ∈ PrimeSpectrum.zeroLocus (JA : Set A') := hJA ▸ hz
      rw [PrimeSpectrum.mem_zeroLocus] at hyC ⊢
      intro r hr
      exact hyC hr.2
  · rcases hdata.2 z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact (Set.ext_iff.mp hJB x).mpr (hBmem x hz)
    by_cases hyker : RingHom.ker g ≤ y.asIdeal
    · obtain ⟨w, hw⟩ := mem_range_comap_of_ker_le hg hyker
      rw [← hw, ← comap_pullback_comm f g w] at hz ⊢
      exact (Set.ext_iff.mp hJB _).mpr (hBmem _ hz)
    · exact (Set.ext_iff.mp hJA y).mpr (mem_zeroLocus_of_comap_pullbackSnd_mem f g y hyker hz)

private lemma isQuotientMap_spectrum_pullback
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g) :
    Topology.IsQuotientMap
      (Sum.elim (PrimeSpectrum.comap (f.pullbackFst g))
        (PrimeSpectrum.comap (f.pullbackSnd g))) := by
  let R := f.pullback g
  let p₁ : R →+* B := f.pullbackFst g
  let p₂ : R →+* A' := f.pullbackSnd g
  let q : PrimeSpectrum B ⊕ PrimeSpectrum A' → PrimeSpectrum R :=
    Sum.elim (PrimeSpectrum.comap p₁) (PrimeSpectrum.comap p₂)
  have hsurj : Function.Surjective q := by
    intro z
    rcases (spectrum_pullback_data f g hg).2 z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr y, rfl⟩
  apply Topology.isQuotientMap_iff_isClosed.mpr
  refine ⟨hsurj, fun C ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · exact h.preimage <| (PrimeSpectrum.continuous_comap p₁).sumElim
      (PrimeSpectrum.continuous_comap p₂)
  · have hB : IsClosed ((PrimeSpectrum.comap p₁) ⁻¹' C) := by
      have hi : Continuous (Sum.inl : PrimeSpectrum B → PrimeSpectrum B ⊕ PrimeSpectrum A') :=
        continuous_inl
      exact IsClosed.preimage hi h
    have hA : IsClosed ((PrimeSpectrum.comap p₂) ⁻¹' C) := by
      have hi : Continuous (Sum.inr : PrimeSpectrum A' → PrimeSpectrum B ⊕ PrimeSpectrum A') :=
        continuous_inr
      exact IsClosed.preimage hi h
    obtain ⟨JB, hJB⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hB
    obtain ⟨JA, hJA⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hA
    exact (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mpr
      ⟨_, eq_zeroLocus_inf_comap_of_preimage_eq f g hg C hJB hJA⟩

/-- **Stacks 0B7J.** The prime spectrum of `B ×_A A'`, where `A' → A` is surjective,
is the pushout of `Spec(B)` and `Spec(A')` over `Spec(A)` as a topological space. -/
@[stacks 0B7J]
public theorem primeSpectrum_isPushout
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (s : Situation toBase surjection I) :
    IsPushout
      (TopCat.ofHom ⟨PrimeSpectrum.comap toBase, PrimeSpectrum.continuous_comap toBase⟩)
      (TopCat.ofHom ⟨PrimeSpectrum.comap surjection, PrimeSpectrum.continuous_comap surjection⟩)
      (TopCat.ofHom ⟨PrimeSpectrum.comap s.pullbackCone.fst.hom,
        PrimeSpectrum.continuous_comap s.pullbackCone.fst.hom⟩)
      (TopCat.ofHom ⟨PrimeSpectrum.comap s.pullbackCone.snd.hom,
        PrimeSpectrum.continuous_comap s.pullbackCone.snd.hom⟩) := by
  change IsPushout
    (TopCat.ofHom ⟨PrimeSpectrum.comap toBase,
      PrimeSpectrum.continuous_comap toBase⟩)
    (TopCat.ofHom ⟨PrimeSpectrum.comap surjection,
      PrimeSpectrum.continuous_comap surjection⟩)
    (TopCat.ofHom ⟨PrimeSpectrum.comap (toBase.pullbackFst surjection),
      PrimeSpectrum.continuous_comap (toBase.pullbackFst surjection)⟩)
    (TopCat.ofHom ⟨PrimeSpectrum.comap (toBase.pullbackSnd surjection),
      PrimeSpectrum.continuous_comap (toBase.pullbackSnd surjection)⟩)
  apply isPushout_of_quotientMap_sum
  · exact ConcreteCategory.hom_ext _ _ (comap_pullback_comm toBase surjection)
  · exact (spectrum_pullback_data toBase surjection s.surjective_surjection).1
  · exact pullback_spectrum_cross toBase surjection s.surjective_surjection
  · exact pullback_spectrum_snd_fiber toBase surjection s.surjective_surjection
  · exact isQuotientMap_spectrum_pullback toBase surjection s.surjective_surjection

end RingFibreProduct
end

end
