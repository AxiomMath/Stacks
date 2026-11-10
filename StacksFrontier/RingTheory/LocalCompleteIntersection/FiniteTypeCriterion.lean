module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.LocalCompleteIntersection.CompletionCriterion
public import StacksFrontier.RingTheory.Sequence.Regular.Basic

/-!
# Local complete intersection maps of finite type

Let `A` be a Noetherian ring and let `A → B` be of finite type.  Then `A → B` is a local complete
intersection exactly when, for every prime `𝔮` of `B` lying over `𝔭`, the induced homomorphism
`(A_𝔭)^ → (B_𝔮)^` between the completions of the local rings is a complete intersection
homomorphism.

Both directions go through a presentation `R = A[x₁, …, x_n] ↠ B` with kernel `I`.  Localizing at
a prime `𝔮` of `B` and its contraction `𝔔` to `R` produces a good factorization
`A_𝔭 → R_𝔔 → B_𝔮`, since `A → R` is flat with regular fibres and localization preserves this, so
the criterion for a good factorization applies at every prime.  Koszul-regularity of `I` is a
local condition on `Spec R`, and over a Noetherian local ring it agrees with generation by a
regular sequence; passing between the local statement and a statement on a basic open
neighbourhood is what turns the pointwise criterion into the presentation-level one.

## Main results

* `LocalCompleteIntersection.isLocalCompleteIntersection_iff_forall_isCompleteIntersectionHom`:
  the local-completion criterion for a finite-type local complete intersection map.

## Implementation notes

The local homomorphism at a prime `𝔮` is the canonical map `Localization.localRingHom` from the
localization at the contraction of `𝔮` to the localization at `𝔮`, and its completion map is
`adicCompletionMap` at the maximal ideals.

## References

* [Stacks Project, Tag 09QE](https://stacks.math.columbia.edu/tag/09QE)
-/

@[expose] public section

namespace LocalCompleteIntersection

universe u

private theorem polynomial_atPrime_goodFactorization
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) {n : ℕ}
    (π : MvPolynomial (Fin n) A →+* B) (hπ : Function.Surjective π)
    (hπbase : π.comp (algebraMap A (MvPolynomial (Fin n) A)) = f)
    (q : Ideal B) [q.IsPrime] :
    letI := f.toAlgebra
    let p := q.comap f
    let Q := q.comap π
    let h := Localization.localRingHom p q f rfl
    let f' := Localization.localRingHom p Q (algebraMap A (MvPolynomial (Fin n) A)) (by
      ext a
      change f a ∈ q ↔ π (algebraMap A (MvPolynomial (Fin n) A) a) ∈ q
      rw [← DFunLike.congr_fun hπbase a]
      simp only [RingHom.comp_apply])
    let g' := Localization.localRingHom Q q π rfl
    IsGoodFactorization h f' g' := by
  let : Algebra A B := f.toAlgebra
  let P := MvPolynomial (Fin n) A
  let p : Ideal A := q.comap f
  let Q : Ideal P := q.comap π
  let hAQ : p = Q.comap (algebraMap A P) := by
    ext a
    change f a ∈ q ↔ π (algebraMap A P a) ∈ q
    rw [← DFunLike.congr_fun hπbase a]
    simp only [RingHom.comp_apply, P]
  let h : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q f rfl
  let f' : Localization.AtPrime p →+* Localization.AtPrime Q :=
    Localization.localRingHom p Q (algebraMap A P) hAQ
  let g' : Localization.AtPrime Q →+* Localization.AtPrime q :=
    Localization.localRingHom Q q π rfl
  have hcomp : g'.comp f' = h := by
    dsimp [g', f', h]
    rw [← Localization.localRingHom_comp]
    congr 1
  have hf' : f'.Flat :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) Q p hAQ
  have hsurj : Function.Surjective g' := by
    intro y
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    obtain ⟨x, rfl⟩ := hπ b
    obtain ⟨t, ht⟩ := hπ s.1
    have htQ : t ∉ Q := by
      change π t ∉ q
      rw [ht]
      exact s.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime Q) x
      (⟨t, htQ⟩ : Q.primeCompl), ?_⟩
    simp [g', Localization.localRingHom_mk', ht]
  have hreg : IsRegularLocalRing
      (Localization.AtPrime Q ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map f') := by
    have hmax :
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map f' =
          (Q.under A).map (algebraMap A (Localization.AtPrime Q)) := by
      have hfa : f'.comp (algebraMap A (Localization.AtPrime p)) =
          algebraMap A (Localization.AtPrime Q) := by
        ext a
        simpa [f', Localization.localRingHom_to_map] using
          (IsScalarTower.algebraMap_apply A P (Localization.AtPrime Q) a).symm
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p),
        Ideal.map_map, hfa, hAQ]
    rw [hmax]
    exact Ideal.isRegularLocalRing_fiberRing_mvPolynomial (R := A) Q
  exact ⟨hcomp, Localization.isLocalHom_localRingHom p Q _ hAQ,
    Localization.isLocalHom_localRingHom Q q _ rfl, hsurj, hf', hreg⟩

private theorem kernel_localized_polynomial_presentation
    {P B : Type u} [CommRing P] [CommRing B] (π : P →+* B)
    (hπ : Function.Surjective π) (q : Ideal B) [q.IsPrime] :
    let Q := q.comap π
    RingHom.ker (Localization.localRingHom Q q π rfl) =
      (RingHom.ker π).map (algebraMap P (Localization.AtPrime Q)) := by
  let Q : Ideal P := q.comap π
  have hcompl : Submonoid.map π Q.primeCompl = q.primeCompl :=
    Submonoid.map_comap_eq_of_surjective hπ q.primeCompl
  let g' := Localization.localRingHom Q q π rfl
  let g'' : Localization.AtPrime Q →+* Localization.AtPrime q :=
    IsLocalization.map (Localization.AtPrime q) π
      (hcompl.symm ▸ Q.primeCompl.le_comap_map)
  have heq : g' = g'' := by
    ext x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    simp [g', g'', Localization.localRingHom_mk', IsLocalization.map_mk']
  change RingHom.ker g' =
    (RingHom.ker π).map (algebraMap P (Localization.AtPrime Q))
  rw [heq]
  exact IsLocalization.ker_map (Q := Localization.AtPrime q) π hcompl

private theorem exists_away_mul_mem_of_atPrime_map_le
    {R : Type u} [CommRing R]
    (I K : Ideal R) (hI : I.FG) (p : Ideal R) [p.IsPrime]
    (hIK : I.map (algebraMap R (Localization.AtPrime p)) ≤
      K.map (algebraMap R (Localization.AtPrime p))) :
    ∃ g : R, g ∉ p ∧ ∀ x ∈ I, g * x ∈ K := by
  classical
  obtain ⟨n, a, ha⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hrep (i : Fin n) : ∃ s : R, s ∈ p.primeCompl ∧ s * a i ∈ K := by
    have hai : a i ∈ I := by rw [← ha]; exact Submodule.subset_span ⟨i, rfl⟩
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) K (a i)).mp (hIK (Ideal.mem_map_of_mem _ hai))
  choose s hs hsa using hrep
  let gs : p.primeCompl := ∏ i : Fin n, (⟨s i, hs i⟩ : p.primeCompl)
  have hmul (i : Fin n) : (gs : R) * a i ∈ K := by
    let u : p.primeCompl := ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      (⟨s j, hs j⟩ : p.primeCompl)
    have hg : (gs : R) = s i * (u : R) :=
      congrArg Subtype.val (Finset.mul_prod_erase Finset.univ
        (fun j : Fin n => (⟨s j, hs j⟩ : p.primeCompl)) (Finset.mem_univ i)).symm
    rw [hg]
    convert K.mul_mem_left (u : R) (hsa i) using 1
    ring
  refine ⟨gs, gs.property, fun x hx => ?_⟩
  rw [← ha] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hmul i
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using K.add_mem hx hy
  | smul r x _ hx =>
      convert K.mul_mem_left r hx using 1
      ring

private theorem exists_away_eq_of_atPrime_eq
    {R : Type u} [CommRing R]
    (I K : Ideal R) (hI : I.FG) (hK : K.FG) (p : Ideal R) [p.IsPrime]
    (heq : I.map (algebraMap R (Localization.AtPrime p)) =
      K.map (algebraMap R (Localization.AtPrime p))) :
    ∃ g : R, g ∉ p ∧ (∀ x ∈ I, g * x ∈ K) ∧ (∀ x ∈ K, g * x ∈ I) := by
  obtain ⟨g₁, hg₁, h₁⟩ := exists_away_mul_mem_of_atPrime_map_le I K hI p (le_of_eq heq)
  obtain ⟨g₂, hg₂, h₂⟩ := exists_away_mul_mem_of_atPrime_map_le K I hK p (le_of_eq heq.symm)
  refine ⟨g₁ * g₂, fun hgp => (Ideal.IsPrime.mem_or_mem (I := p) ‹p.IsPrime› hgp).elim hg₁ hg₂,
    fun x hx => ?_, fun x hx => ?_⟩
  · convert K.mul_mem_left g₂ (h₁ x hx) using 1
    ring
  · convert I.mul_mem_left g₁ (h₂ x hx) using 1
    ring

private theorem regular_sequence_localize_away_of_atPrime_mul
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (xs : List R)
    (hp : RingTheory.Sequence.IsRegular (LocalizedModule p.primeCompl R)
      (xs.map (algebraMap R (Localization.AtPrime p))))
    (a : R) (ha : a ∉ p) :
    ∃ g : R, g ∉ p ∧ a ∣ g ∧
      RingTheory.Sequence.IsRegular (LocalizedModule (Submonoid.powers g) R)
        (xs.map (algebraMap R (Localization.Away g))) := by
  obtain ⟨g₀, hg₀, hker₀, _⟩ := L_choose_g p xs hp
  let g := a * g₀
  have hg : g ∈ p.primeCompl := mul_mem ha hg₀
  have hker : ∀ i (hi : i < xs.length),
      Subsingleton (LocalizedModule (Submonoid.powers g)
        (LinearMap.ker (LinearMap.lsmul R
          (R ⧸ (Ideal.ofList (xs.take i) • ⊤ : Submodule R R)) xs[i]))) := by
    intro i hi
    have hsub := hker₀ i hi
    rw [LocalizedModule.subsingleton_iff] at hsub ⊢
    intro m
    obtain ⟨r, ⟨k, rfl⟩, hr⟩ := hsub m
    refine ⟨g ^ k, ⟨k, rfl⟩, ?_⟩
    change g ^ k • m = 0
    rw [show g = g₀ * a by simp [g, mul_comm], mul_pow, mul_smul,
      smul_comm (g₀ ^ k) (a ^ k) m, hr, smul_zero]
  have htop :
      (⊤ : Submodule (Localization.Away g) (LocalizedModule (Submonoid.powers g) R)) ≠
        Ideal.ofList (xs.map (algebraMap R (Localization.Away g))) • ⊤ := by
    rw [ne_comm, ne_eq, ← Submodule.Quotient.subsingleton_iff]
    intro hsubg
    have hQg : Subsingleton
        (LocalizedModule (Submonoid.powers g)
          (R ⧸ (Ideal.ofList xs • ⊤ : Submodule R R))) := by
      obtain ⟨e⟩ := nonempty_localizedModule_quotient_ofList_equiv
        (M := R) xs (Submonoid.powers g)
      exact (Equiv.subsingleton_congr e.toEquiv).mpr hsubg
    have hQp : Subsingleton
        (LocalizedModule p.primeCompl
          (R ⧸ (Ideal.ofList xs • ⊤ : Submodule R R))) := by
      rw [LocalizedModule.subsingleton_iff] at hQg ⊢
      intro m
      obtain ⟨r, hrmem, hr⟩ := hQg m
      exact ⟨r, (Submonoid.powers_le.mpr hg) hrmem, hr⟩
    obtain ⟨e⟩ := nonempty_localizedModule_quotient_ofList_equiv
      (M := R) xs p.primeCompl
    have hp' := hp.top_ne_smul
    rw [ne_comm, ne_eq, ← Submodule.Quotient.subsingleton_iff] at hp'
    exact hp' ((Equiv.subsingleton_congr e.toEquiv).mp hQp)
  refine ⟨g, hg, ⟨g₀, rfl⟩, ?_, htop⟩
  rw [RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (Localization.Away g)]
  exact L_weaklyRegular_of_kernels_away g xs hker

private theorem exists_away_koszulRegular_generators_of_atPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (p : Ideal R) [p.IsPrime]
    (hgen : ∃ rs : List (Localization.AtPrime p),
      RingTheory.Sequence.IsRegular (Localization.AtPrime p) rs ∧
        Ideal.ofList rs = I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ g : R, g ∉ p ∧ ∃ n : ℕ, ∃ xs : Fin n → Localization.Away g,
      Koszul.IsKoszulRegular xs ∧
        I.map (algebraMap R (Localization.Away g)) = Ideal.span (Set.range xs) := by
  classical
  obtain ⟨rs, hrs, hspan⟩ := hgen
  let n := rs.length
  let x : Fin n → Localization.AtPrime p := fun i => rs.get i
  have hxlist : List.ofFn x = rs := List.ofFn_get rs
  let rep : Fin n → R × p.primeCompl := fun i =>
    Classical.choose (IsLocalization.surj p.primeCompl (x i))
  let num : Fin n → R := fun i => (rep i).1
  let den : Fin n → R := fun i => (rep i).2
  let F : Fin n → R := fun i => num i *
    ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, den j
  let dprod : p.primeCompl := ∏ i, (rep i).2
  let D : Localization.AtPrime p := algebraMap R (Localization.AtPrime p) dprod
  have hD : IsUnit D := IsLocalization.map_units (Localization.AtPrime p) dprod
  have hnum (i : Fin n) : algebraMap R (Localization.AtPrime p) (num i) =
      algebraMap R (Localization.AtPrime p) (den i) * x i := by
    simpa [num, den, mul_comm] using
      (Classical.choose_spec (IsLocalization.surj p.primeCompl (x i))).symm
  have hF (i : Fin n) : algebraMap R (Localization.AtPrime p) (F i) = D * x i := by
    dsimp only [F, D, num, den]
    have hpSubtype : (rep i).2 *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (rep j).2 = dprod := by
      dsimp [dprod]
      exact Finset.mul_prod_erase Finset.univ (fun j : Fin n => (rep j).2)
        (Finset.mem_univ i)
    have hp : (rep i).2 *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((rep j).2 : R) =
          (dprod : R) := by
      simpa using congrArg (fun s : p.primeCompl => (s : R)) hpSubtype
    have hprodMap : algebraMap R (Localization.AtPrime p) ((rep i).2 : R) *
        algebraMap R (Localization.AtPrime p)
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((rep j).2 : R)) =
        algebraMap R (Localization.AtPrime p) (dprod : R) := by
      calc
        _ = algebraMap R (Localization.AtPrime p)
            ((rep i).2 * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
              ((rep j).2 : R)) := by simp only [map_mul]
        _ = _ := by rw [hp]
    calc
      _ = algebraMap R (Localization.AtPrime p) ((rep i).1) *
          algebraMap R (Localization.AtPrime p)
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((rep j).2 : R)) := by
              rw [map_mul]
      _ = (algebraMap R (Localization.AtPrime p) ((rep i).2 : R) * x i) *
          algebraMap R (Localization.AtPrime p)
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((rep j).2 : R)) := by rw [hnum]
      _ = algebraMap R (Localization.AtPrime p) ((rep i).2 : R) *
          algebraMap R (Localization.AtPrime p)
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((rep j).2 : R)) * x i := by
              ring
      _ = algebraMap R (Localization.AtPrime p) (dprod : R) * x i := by rw [hprodMap]
      _ = D * x i := rfl
  have hscaled : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (List.ofFn (fun i : Fin n => D * x i)) := by
    have hl : rs.map (D * ·) = List.ofFn (fun i : Fin n => D * x i) := by
      rw [← hxlist]
      simp [Function.comp_def]
    exact hl ▸ hrs.map_mul_unit hD
  let xs : List R := List.ofFn F
  have hregAt : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (xs.map (algebraMap R (Localization.AtPrime p))) := by
    simpa only [xs, List.map_ofFn, Function.comp_def, hF] using hscaled
  have hspanAt : I.map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span (Set.range (fun i : Fin n => algebraMap R (Localization.AtPrime p) (F i))) := by
    calc
      I.map (algebraMap R (Localization.AtPrime p)) = Ideal.ofList rs := hspan.symm
      _ = Ideal.ofList (rs.map (D * ·)) :=
        (Ideal.ofList_map_mul_unit hD rs).symm
      _ = Ideal.ofList (List.ofFn (fun i : Fin n => D * x i)) := by
        rw [← hxlist]
        simp [Function.comp_def]
      _ = Ideal.span (Set.range (fun i : Fin n =>
          algebraMap R (Localization.AtPrime p) (F i))) := by
        simp only [hF, Ideal.ofList]
        congr 1
        ext z
        simp [List.mem_ofFn]
  let e : LocalizedModule p.primeCompl R ≃ₗ[Localization.AtPrime p]
      Localization.AtPrime p :=
    LinearEquiv.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
      (IsLocalizedModule.linearEquiv p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl R)
        (Algebra.linearMap R (Localization.AtPrime p)))
  have hregM : RingTheory.Sequence.IsRegular (LocalizedModule p.primeCompl R)
      (xs.map (algebraMap R (Localization.AtPrime p))) :=
    (e.isRegular_congr _).2 hregAt
  let K : Ideal R := Ideal.span (Set.range F)
  have hspanAt' : I.map (algebraMap R (Localization.AtPrime p)) =
      K.map (algebraMap R (Localization.AtPrime p)) := by
    simpa only [K, Ideal.map_span, ← Set.range_comp, Function.comp_def] using hspanAt
  obtain ⟨d, hd, hdI, hdK⟩ := exists_away_eq_of_atPrime_eq I K
    (IsNoetherian.noetherian I) (IsNoetherian.noetherian K) p hspanAt'
  obtain ⟨c, hc, hcd, hregMc⟩ :=
    regular_sequence_localize_away_of_atPrime_mul p xs hregM d hd
  let eAway : LocalizedModule (Submonoid.powers c) R ≃ₗ[Localization.Away c]
      Localization.Away c :=
    LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers c) (Localization.Away c)
      (IsLocalizedModule.linearEquiv (Submonoid.powers c)
        (LocalizedModule.mkLinearMap (Submonoid.powers c) R)
        (Algebra.linearMap R (Localization.Away c)))
  have hregAway : RingTheory.Sequence.IsRegular (Localization.Away c)
      (xs.map (algebraMap R (Localization.Away c))) :=
    (eAway.isRegular_congr _).1 hregMc
  let xsAway : Fin n → Localization.Away c := fun i => algebraMap R _ (F i)
  have hregAway' : RingTheory.Sequence.IsRegular (Localization.Away c) (List.ofFn xsAway) := by
    convert hregAway using 1
    simp [xs, xsAway, List.map_ofFn, Function.comp_def]
  have hkos : Koszul.IsKoszulRegular xsAway :=
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
      (R := Localization.Away c) (M := Localization.Away c)
      (f := xsAway)).2.2 hregAway'
  have hKmap : K.map (algebraMap R (Localization.Away c)) =
      Ideal.span (Set.range xsAway) := by
    simp [K, xsAway, Ideal.map_span, ← Set.range_comp, Function.comp_def]
  have hspanAway : I.map (algebraMap R (Localization.Away c)) =
      Ideal.span (Set.range xsAway) := by
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro y hy
      have hmem : c * y ∈ K := by
        obtain ⟨k, rfl⟩ := hcd
        convert K.mul_mem_left k (hdI y hy) using 1
        ring
      have hmap := Ideal.mem_map_of_mem (algebraMap R (Localization.Away c)) hmem
      rw [hKmap] at hmap
      obtain ⟨u, hu⟩ : IsUnit (algebraMap R (Localization.Away c) c) :=
        IsLocalization.Away.algebraMap_isUnit c
      simpa [← hu, ← mul_assoc] using
        (Ideal.span (Set.range xsAway)).mul_mem_left
          (↑u⁻¹ : Localization.Away c) hmap
    · rw [Ideal.span_le]
      rintro y ⟨i, rfl⟩
      have hmem : c * F i ∈ I := by
        obtain ⟨k, rfl⟩ := hcd
        convert I.mul_mem_left k (hdK (F i) (Ideal.subset_span ⟨i, rfl⟩)) using 1
        ring
      have hmap := Ideal.mem_map_of_mem (algebraMap R (Localization.Away c)) hmem
      obtain ⟨u, hu⟩ : IsUnit (algebraMap R (Localization.Away c) c) :=
        IsLocalization.Away.algebraMap_isUnit c
      simpa [← hu, ← mul_assoc] using
        (I.map (algebraMap R (Localization.Away c))).mul_mem_left
          (↑u⁻¹ : Localization.Away c) hmap
  exact ⟨c, hc, n, xsAway, hkos, hspanAway⟩

private theorem exists_regular_generators_of_koszulRegularIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (hI : Ideal.IsKoszulRegular I) (p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    ∃ fs : List (Localization.AtPrime p),
      RingTheory.Sequence.IsRegular (Localization.AtPrime p) fs ∧
        Ideal.ofList fs = I.map (algebraMap R (Localization.AtPrime p)) := by
  obtain ⟨g, hgp, r, v, hv, hspan⟩ := hI ⟨p, inferInstance⟩ hp
  let A := Localization.Away g
  let B := Localization.AtPrime p
  have hle : Submonoid.powers g ≤ p.primeCompl := Submonoid.powers_le.mpr hgp
  let : Algebra A B := IsLocalization.localizationAlgebraOfSubmonoidLe A B
    (Submonoid.powers g) p.primeCompl hle
  let : IsScalarTower R A B :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A B
      (Submonoid.powers g) p.primeCompl hle
  let : IsLocalization (p.primeCompl.map (algebraMap R A)) B :=
    IsLocalization.isLocalization_of_submonoid_le A B (Submonoid.powers g) p.primeCompl hle
  have : Module.Flat A B := IsLocalization.flat B (p.primeCompl.map (algebraMap R A))
  let w : Fin r → B := fun i => algebraMap A B (v i)
  have hspan' : Ideal.span (Set.range w) = I.map (algebraMap R B) := by
    calc
      Ideal.span (Set.range w) = (Ideal.span (Set.range v)).map (algebraMap A B) := by
        simp [w, Ideal.map_span, ← Set.range_comp, Function.comp_def]
      _ = (I.map (algebraMap R A)).map (algebraMap A B) := by rw [hspan.symm]
      _ = I.map (algebraMap R B) := by
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A B]
  have hmem (i : Fin r) : w i ∈ IsLocalRing.maximalIdeal B := by
    have hImax := Ideal.map_mono hp (f := algebraMap R B)
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal p B] at hImax
    exact hImax (hspan' ▸ Ideal.subset_span ⟨i, rfl⟩)
  have hwH1 : Koszul.IsH1Regular w := by
    have hon : Koszul.IsH1RegularOn w (TensorProduct A B A) :=
      KoszulC.isH1Regular_baseChange v A
        ((Koszul.isH1RegularOn_self_iff v).2 hv.isH1Regular)
    have hon' : Koszul.IsH1RegularOn w B :=
      Koszul.isH1RegularOn_of_linearEquiv w (TensorProduct.AlgebraTensorModule.rid A B B) hon
    exact (Koszul.isH1RegularOn_self_iff w).1 hon'
  have hreg : RingTheory.Sequence.IsRegular B (List.ofFn w) :=
    ((Koszul.regular_koszulRegular_h1Regular_quasiRegular_tfae
      (M := B) w hmem).2.out 3 1).mp hwH1
  refine ⟨List.ofFn w, hreg, ?_⟩
  have hlist : Ideal.ofList (List.ofFn w) = Ideal.span (Set.range w) := by
    unfold Ideal.ofList
    congr 1
    ext x
    simp [List.mem_ofFn]
  exact hlist.trans hspan'

/-- A finite-type map from a Noetherian ring is a local complete intersection exactly when,
at each target prime, the map between the completions of the corresponding local rings is a
complete intersection homomorphism. -/
@[stacks 09QE]
public theorem isLocalCompleteIntersection_iff_forall_isCompleteIntersectionHom
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hf : f.FiniteType) :
    f.IsLocalCompleteIntersection ↔
      letI := f.toAlgebra
      letI : Algebra.FiniteType A B := hf
      letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
      ∀ (q : Ideal B) [q.IsPrime],
        let p := q.comap f
        let h := Localization.localRingHom p q f rfl
        letI : IsLocalHom h := Localization.isLocalHom_localRingHom p q f rfl
        IsCompleteIntersectionHom
          (adicCompletionMap h (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (IsLocalRing.maximalIdeal (Localization.AtPrime q))
            (IsLocalRing.map_maximalIdeal_le h)) := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.FiniteType A B := hf
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  classical
  constructor
  · intro hLCI q hq
    let : q.IsPrime := hq
    rcases hLCI with ⟨_, n, π, hπ, hker⟩
    let P := MvPolynomial (Fin n) A
    have hbase : π.toRingHom.comp (algebraMap A P) = f := by
      ext a
      exact π.commutes a
    let p : Ideal A := q.comap f
    let Q : Ideal P := q.comap π.toRingHom
    have : Q.IsPrime := Ideal.comap_isPrime π.toRingHom q
    have hQI : RingHom.ker π.toRingHom ≤ Q := Ideal.ker_le_comap _
    obtain ⟨rs, hreg, hgen⟩ :=
      exists_regular_generators_of_koszulRegularIdeal
        (RingHom.ker π.toRingHom) hker Q hQI
    let h := Localization.localRingHom p q f rfl
    let f' := Localization.localRingHom p Q (algebraMap A P) (by
      ext a
      change f a ∈ q ↔ π (algebraMap A P a) ∈ q
      rw [← DFunLike.congr_fun hbase a]
      rfl)
    let g' := Localization.localRingHom Q q π.toRingHom rfl
    have : IsLocalHom h := Localization.isLocalHom_localRingHom p q f rfl
    exact (isGeneratedByRegularSequence_ker_iff_isCompleteIntersectionHom h f' g'
      (polynomial_atPrime_goodFactorization f π.toRingHom hπ hbase q)).1
      ⟨rs, hreg, hgen.trans (kernel_localized_polynomial_presentation π.toRingHom hπ q).symm⟩
  · intro hcomp
    obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
    let P := MvPolynomial (Fin n) A
    have hbase : π.toRingHom.comp (algebraMap A P) = f := by
      ext a
      exact π.commutes a
    have hI : Ideal.IsKoszulRegular (RingHom.ker π.toRingHom) := by
      intro z hz
      let Q₀ : Ideal P := z.asIdeal
      let q : Ideal B := Q₀.map π.toRingHom
      have : q.IsPrime := Ideal.map_isPrime_of_surjective hπ hz
      have hQeq : q.comap π.toRingHom = Q₀ := by
        rw [Ideal.comap_map_of_surjective π.toRingHom hπ Q₀,
          ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hz]
      let Q : Ideal P := q.comap π.toRingHom
      have : Q.IsPrime := Ideal.comap_isPrime π.toRingHom q
      let p : Ideal A := q.comap f
      let h := Localization.localRingHom p q f rfl
      let f' := Localization.localRingHom p Q (algebraMap A P) (by
        ext a
        change f a ∈ q ↔ π (algebraMap A P a) ∈ q
        rw [← DFunLike.congr_fun hbase a]
        rfl)
      let g' := Localization.localRingHom Q q π.toRingHom rfl
      have : IsLocalHom h := Localization.isLocalHom_localRingHom p q f rfl
      obtain ⟨rs, hreg, hgen⟩ :=
        (isGeneratedByRegularSequence_ker_iff_isCompleteIntersectionHom h f' g'
          (polynomial_atPrime_goodFactorization f π.toRingHom hπ hbase q)).2 (hcomp q)
      obtain ⟨g, hg, r, seq, hseq, hspan⟩ :=
        exists_away_koszulRegular_generators_of_atPrime (RingHom.ker π.toRingHom) Q
          ⟨rs, hreg, hgen.trans (kernel_localized_polynomial_presentation π.toRingHom hπ q)⟩
      change g ∉ q.comap π.toRingHom at hg
      rw [hQeq] at hg
      exact ⟨g, hg, r, seq, hseq, hspan⟩
    exact ⟨hf, n, π, hπ, hI⟩

end LocalCompleteIntersection

end
