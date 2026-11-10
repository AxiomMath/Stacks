module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TotallySplit
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Factoring through a smooth algebra using the singular ideal

For an `R`-algebra `A` of finite presentation, the *singular ideal* `H_{A/R}` is the radical
ideal of `A` cutting out the non-smooth locus of `Spec(A) → Spec(R)`.  This file proves that, for
a further algebra `Λ` over `A`, the condition `H_{A/R} Λ = Λ` forces the map `A → Λ` to factor
through an `A`-algebra `B` that is smooth over `R`.

The intermediate algebra is explicit: writing `1 = ∑ cᵢ fᵢ` in `Λ` with `fᵢ ∈ H_{A/R}`, one
takes `B = A[xᵢ] / (∑ fᵢ xᵢ - 1)` and sends `xᵢ ↦ cᵢ`.  Smoothness of `B` over `R` is checked
Zariski-locally on `Spec(B)`: the images of the `fᵢ` generate the unit ideal of `B`, and
inverting `fⱼ` in `B` solves the defining relation for `xⱼ`, exhibiting `B_{fⱼ}` as a
polynomial ring over the localization `A_{fⱼ}`, which is smooth over `R` because
`fⱼ ∈ H_{A/R}`.

## Main definitions

* `SingularIdealVarElim.elimEquiv`: the variable-elimination isomorphism
  `K[xᵢ] / (∑ cᵢ xᵢ - 1) ≃ₐ[K] K[xᵢ : i ≠ j]`, available whenever `c j` is a unit of `K`.

## Main results

* `smooth_of_span_eq_top_away`: smoothness is Zariski-local on the target.
* `exists_smooth_factorization_of_singularIdeal_map_eq_top`: the factorization `A → B → Λ`
  with `B` smooth over `R`.

## Implementation notes

The singular ideal itself is `Stacks.Smoothing.singularIdeal`; the only property of it used here
is `Stacks.Smoothing.smooth_localization_away_of_mem_singularIdeal`, that `A_f` is smooth over `R`
for `f ∈ H_{A/R}` and `A` of finite presentation over `R`.

## References

* [Stacks Project, Tag 07EU](https://stacks.math.columbia.edu/tag/07EU)
* [Stacks Project, Tag 07C5](https://stacks.math.columbia.edu/tag/07C5)
-/

open Algebra PrimeSpectrum Stacks.Smoothing

universe u v w

/-- **Smoothness is Zariski-local on the target.**
If a family of elements `s ⊆ S` generates the unit ideal `Ideal.span s = ⊤`, and
for each `g ∈ s` the localization `S_g = Localization.Away g` is smooth over `R`,
then `S` is smooth over `R`.

Mathlib packages this as the meta-property
`RingHom.Smooth.ofLocalizationSpanTarget : OfLocalizationSpanTarget RingHom.Smooth`, which is
stated for a ring map and therefore forces `R` and `S` into the same universe.  The proof here
runs the underlying argument on the smooth locus instead, so `R` and `S` may lie in independent
universes: finite presentation descends from the principal localizations
(`Algebra.FinitePresentation.of_span_eq_top_target`), and their basic opens cover the spectrum
and lie in the smooth locus. -/
@[ega "IV 17.3.2" "smooth case", sga "3 XIX 2.1" "special case", sga "4 IV 8.5.5" "special case"]
theorem smooth_of_span_eq_top_away
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (hs : Ideal.span s = ⊤)
    (H : ∀ g : s, Algebra.Smooth R (Localization.Away (g : S))) :
    Algebra.Smooth R S := by
  have : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_span_eq_top_target s hs fun r hr =>
      (H ⟨r, hr⟩).finitePresentation
  refine ⟨?_, ‹_›⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, ← Set.univ_subset_iff,
    ← TopologicalSpace.Opens.coe_top, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  exact fun r hr => H ⟨r, hr⟩

/- Variable-elimination machinery: over a base ring `K`, with a relation
`rel c = (∑ C(c i) X i) - 1` in `MvPolynomial ι K` whose `j`-th coefficient `c j`
is a unit, the quotient `MvPolynomial ι K ⧸ span {rel c}` is `K`-isomorphic to the
polynomial ring `MvPolynomial {i // i ≠ j} K` (eliminating the variable `X j`). -/
namespace SingularIdealVarElim
variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The value to which `X j` is sent in the eliminated polynomial ring:
`c j⁻¹ (1 - ∑_{i ≠ j} c i X i)`. -/
noncomputable def xjval (j : ι) (c : ι → K) : MvPolynomial {i // i ≠ j} K :=
  (Ring.inverse (c j)) • (1 - ∑ i : {i // i ≠ j}, MvPolynomial.C (c i.1) * MvPolynomial.X i)

/-- The substitution `X i ↦ xjval` (for `i = j`) or `X i ↦ X ⟨i, _⟩` (for `i ≠ j`). -/
noncomputable def gmap (j : ι) (c : ι → K) : ι → MvPolynomial {i // i ≠ j} K :=
  fun i => if h : i = j then xjval j c else MvPolynomial.X ⟨i, h⟩

/-- The forward algebra hom `MvPolynomial ι K → MvPolynomial {i ≠ j} K`. -/
noncomputable def fwdHom (j : ι) (c : ι → K) :
    MvPolynomial ι K →ₐ[K] MvPolynomial {i // i ≠ j} K :=
  MvPolynomial.aeval (gmap j c)

/-- The defining relation `(∑ C(c i) X i) - 1`. -/
noncomputable def rel (c : ι → K) : MvPolynomial ι K :=
  (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) - 1

/-- The quotient ring `MvPolynomial ι K ⧸ span {rel c}`. -/
abbrev Quo (c : ι → K) := MvPolynomial ι K ⧸ Ideal.span {rel c}

open MvPolynomial in
/-- The forward map `fwdHom j c` kills the relation `rel c` when `c j` is a unit. -/
theorem fwdHom_rel (j : ι) (c : ι → K) (hj : IsUnit (c j)) : fwdHom j c (rel c) = 0 := by
  unfold fwdHom rel
  rw [map_sub, map_one, map_sum]
  simp only [map_mul, aeval_C, aeval_X, gmap]
  rw [sub_eq_zero]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  rw [dite_eq_left rfl]
  have hsum_erase : ∑ x ∈ Finset.univ.erase j, (algebraMap K (MvPolynomial {i // i ≠ j} K)) (c x) *
      (if h : x = j then xjval j c else X ⟨x, h⟩)
      = ∑ i : {i // i ≠ j}, C (c i.1) * X i := by
    rw [← Finset.sum_attach (Finset.univ.erase j)]
    apply Finset.sum_nbij' (i := fun x => (⟨x.1, (Finset.mem_erase.mp x.2).1⟩ : {i // i ≠ j}))
      (j := fun (i : {i // i ≠ j}) =>
        (⟨i.1, Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩⟩ : {x // x ∈ Finset.univ.erase j}))
    · intro a ha; simp
    · intro a ha; simp
    · intro a ha; rfl
    · intro a ha; rfl
    · intro a ha
      obtain ⟨x, hx⟩ := a
      rw [Finset.mem_erase] at hx
      rw [dite_eq_right hx.1, algebraMap_eq]
  rw [hsum_erase]
  unfold xjval
  rw [algebraMap_eq, smul_eq_C_mul]
  rw [← mul_assoc, ← C_mul]
  rw [show c j * Ring.inverse (c j) = 1 from by rw [Ring.mul_inverse_cancel _ hj]]
  rw [C_1, one_mul]
  ring

/-- The forward map descends to the quotient. -/
noncomputable def fwd (j : ι) (c : ι → K) (hj : IsUnit (c j)) :
    Quo c →ₐ[K] MvPolynomial {i // i ≠ j} K :=
  Ideal.Quotient.liftₐ (Ideal.span {rel c}) (fwdHom j c) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨d, rfl⟩ := ha
    rw [map_mul, fwdHom_rel j c hj, zero_mul])

/-- The backward map `MvPolynomial {i ≠ j} K → Quo c`, sending `X i ↦ mk (X i.1)`. -/
noncomputable def bwd (j : ι) (c : ι → K) :
    MvPolynomial {i // i ≠ j} K →ₐ[K] Quo c :=
  MvPolynomial.aeval
    (fun i : {i // i ≠ j} => Ideal.Quotient.mk (Ideal.span {rel c}) (MvPolynomial.X i.1))

omit [DecidableEq ι] in
/-- The relation `rel c` vanishes in the quotient `Quo c`. -/
theorem mk_rel_zero (c : ι → K) :
    Ideal.Quotient.mk (Ideal.span {rel c}) (rel c) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl

open MvPolynomial in
/-- The forward map is a left inverse of the backward map: `fwd ∘ bwd` is the identity of
`MvPolynomial {i // i ≠ j} K`. -/
theorem fwd_bwd (j : ι) (c : ι → K) (hj : IsUnit (c j)) :
    (fwd j c hj).comp (bwd j c) = AlgHom.id K (MvPolynomial {i // i ≠ j} K) := by
  apply MvPolynomial.algHom_ext
  intro i
  change fwd j c hj (bwd j c (X i)) = X i
  unfold bwd
  rw [aeval_X]
  change fwd j c hj (Ideal.Quotient.mk _ (X i.1)) = X i
  unfold fwd
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  change fwdHom j c (X i.1) = X i
  unfold fwdHom
  rw [aeval_X]
  unfold gmap
  rw [dite_eq_right i.2]

open MvPolynomial in
/-- The backward map is a left inverse of the forward map: `bwd ∘ fwd` is the identity of
`Quo c`. -/
theorem bwd_fwd (j : ι) (c : ι → K) (hj : IsUnit (c j)) :
    (bwd j c).comp (fwd j c hj) = AlgHom.id K (Quo c) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change bwd j c (fwd j c hj (Ideal.Quotient.mk _ (X i))) = Ideal.Quotient.mk _ (X i)
  unfold fwd
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  change bwd j c (fwdHom j c (X i)) = Ideal.Quotient.mk _ (X i)
  unfold fwdHom
  rw [aeval_X]
  unfold gmap
  by_cases h : i = j
  · subst h
    rw [dite_eq_left rfl]
    set Mk := Ideal.Quotient.mk (Ideal.span {rel c}) with hMk
    have hrel : ∑ k, algebraMap K (Quo c) (c k) * Mk (X k) = 1 := by
      have hh := mk_rel_zero c
      unfold rel at hh
      rw [map_sub, map_one, map_sum, sub_eq_zero] at hh
      refine (Finset.sum_congr rfl fun k _ => ?_).trans hh
      rw [map_mul]
      congr 1
    unfold xjval bwd
    rw [map_smul, map_sub, map_one, map_sum]
    simp only [map_mul, aeval_C, aeval_X]
    have hsplit : ∑ k, algebraMap K (Quo c) (c k) * Mk (X k)
        = algebraMap K (Quo c) (c i) * Mk (X i) +
          ∑ x : {x // x ≠ i}, algebraMap K (Quo c) (c x.1) * Mk (X x.1) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      rw [← Finset.sum_attach (Finset.univ.erase i)]
      apply Finset.sum_nbij' (i := fun x => (⟨x.1, (Finset.mem_erase.mp x.2).1⟩ : {x // x ≠ i}))
        (j := fun (y : {x // x ≠ i}) =>
          (⟨y.1, Finset.mem_erase.mpr ⟨y.2, Finset.mem_univ _⟩⟩ : {x // x ∈ Finset.univ.erase i}))
      · intro a ha; simp
      · intro a ha; simp
      · intro a ha; rfl
      · intro a ha; rfl
      · intro a ha; rfl
    rw [hsplit] at hrel
    have key : (1 : Quo c) - ∑ x : {x // x ≠ i}, algebraMap K (Quo c) (c x.1) * Mk (X x.1)
        = algebraMap K (Quo c) (c i) * Mk (X i) := by
      rw [← hrel]; ring
    rw [key, Algebra.smul_def (A := Quo c), ← mul_assoc, ← map_mul,
      Ring.inverse_mul_cancel _ hj, map_one, one_mul]
  · rw [dite_eq_right h]
    show bwd j c (X ⟨i, h⟩) = _
    unfold bwd
    rw [aeval_X]

/-- **Variable elimination isomorphism.** -/
noncomputable def elimEquiv (j : ι) (c : ι → K) (hj : IsUnit (c j)) :
    Quo c ≃ₐ[K] MvPolynomial {i // i ≠ j} K :=
  AlgEquiv.ofAlgHom (fwd j c hj) (bwd j c) (fwd_bwd j c hj) (bwd_fwd j c hj)

omit [DecidableEq ι] in
/-- `Quo c` is smooth over the base `K` when `c j` is a unit: it is `K`-isomorphic
(via `elimEquiv`) to a finitely-many-variable polynomial ring over `K`, which is
smooth. -/
theorem smooth_Quo (j : ι) (c : ι → K) (hj : IsUnit (c j)) :
    Algebra.Smooth K (Quo c) := by
  classical
  have hfp : Algebra.FinitePresentation K (MvPolynomial {i // i ≠ j} K) :=
    Algebra.FinitePresentation.mvPolynomial K K {i // i ≠ j}
  refine ⟨?_, ?_⟩
  · exact Algebra.FormallySmooth.of_equiv (elimEquiv j c hj).symm
  · exact Algebra.FinitePresentation.equiv (elimEquiv j c hj).symm

end SingularIdealVarElim

-- instance synthesis here needs more than the default heartbeat budget
/-- Localizing `B` away from the image `algebraMap A B (f j)` is, after transporting through a
presentation `hB : B ≃ₐ[A] MvPolynomial ι A ⧸ span {rel f}` and base changing along
`A → Aⱼ := Localization.Away (f j)`, the quotient `SingularIdealVarElim.Quo cⱼ`, where
`cⱼ i = algebraMap A Aⱼ (f i)`.

The chain of identifications is: localization is functorial along the presentation, which
replaces `algebraMap A B (f j)` by `bⱼ = mk (C (f j))`; localization commutes with polynomial
rings (`MvPolynomial.isLocalization`) and with quotients, so
`MvPolynomial ι Aⱼ ⧸ (span {rel f}).map _` is the localization of `MvPolynomial ι A ⧸ span
{rel f}` at the powers of `bⱼ`; and the image of `rel f` under `MvPolynomial.map (algebraMap A
Aⱼ)` is `rel cⱼ`, so that quotient is `Quo cⱼ`.  Uniqueness of localizations then supplies the
`A`-algebra equivalence, which restricts to an `R`-algebra equivalence along `R → A`. -/
theorem connectionEquiv
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] (f : ι → A)
    (B : Type*) [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hB : Nonempty (B ≃ₐ[A] MvPolynomial ι A ⧸
      Ideal.span {(∑ i, MvPolynomial.C (f i) * MvPolynomial.X i) - 1}))
    (j : ι) :
    Nonempty (Localization.Away (algebraMap A B (f j)) ≃ₐ[R]
      SingularIdealVarElim.Quo (fun i => algebraMap A (Localization.Away (f j)) (f i))) := by
  classical
  set Aj := Localization.Away (f j) with hAj
  set cj : ι → Aj := fun i => algebraMap A Aj (f i) with hcj
  let algMvP : Algebra (MvPolynomial ι A) (MvPolynomial ι Aj) := MvPolynomial.algebraMvPolynomial
  have hloc : IsLocalization
      (Submonoid.map (MvPolynomial.C : A →+* MvPolynomial ι A) (Submonoid.powers (f j)))
      (MvPolynomial ι Aj) := MvPolynomial.isLocalization (Submonoid.powers (f j)) Aj
  set rf : MvPolynomial ι A := (∑ i, MvPolynomial.C (f i) * MvPolynomial.X i) - 1 with hrf
  set I : Ideal (MvPolynomial ι A) := Ideal.span {rf} with hI
  set Quof := MvPolynomial ι A ⧸ I with hQuof
  obtain ⟨φ⟩ := hB
  set bj : Quof := algebraMap A Quof (f j) with hbj
  have hφ : φ (algebraMap A B (f j)) = bj := by rw [hbj]; exact φ.commutes (f j)
  have hmapeq : Submonoid.map φ (Submonoid.powers (algebraMap A B (f j)))
      = Submonoid.powers bj := by rw [Submonoid.map_powers]; rw [hφ]
  -- Localization is functorial across `φ`.
  have e0 : Localization.Away (algebraMap A B (f j)) ≃ₐ[A] Localization.Away bj :=
    IsLocalization.algEquivOfAlgEquiv (A := A)
      (R := B) (S := Localization.Away (algebraMap A B (f j)))
      (P := Quof) (Q := Localization.Away bj) φ hmapeq
  set Imapped : Ideal (MvPolynomial ι Aj) :=
    I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι Aj)) with hImapped
  set Qmid := MvPolynomial ι Aj ⧸ Imapped with hQmid
  -- `Qmid` is a localization of `Quof` at `powers bj`.
  have hsubeq : Algebra.algebraMapSubmonoid Quof
        (Submonoid.map (MvPolynomial.C : A →+* MvPolynomial ι A) (Submonoid.powers (f j)))
      = Submonoid.powers bj := by
    unfold Algebra.algebraMapSubmonoid
    rw [Submonoid.map_powers, Submonoid.map_powers]; congr 1
  have hquot : IsLocalization (Submonoid.powers bj) Qmid := by rw [← hsubeq]; infer_instance
  -- Uniqueness of localizations.
  have e1 : Localization.Away bj ≃ₐ[Quof] Qmid :=
    IsLocalization.algEquiv (Submonoid.powers bj) (Localization.Away bj) Qmid
  -- compatibility of the scalar towers `A → Quof → Qmid` and `A → Aj → Qmid`.
  have htower : ∀ a : A, algebraMap A Qmid a = algebraMap Quof Qmid (algebraMap A Quof a) := by
    intro a
    have lhs : algebraMap Aj Qmid (algebraMap A Aj a)
        = Ideal.Quotient.mk Imapped (MvPolynomial.C (algebraMap A Aj a)) := by
      rw [IsScalarTower.algebraMap_apply Aj (MvPolynomial ι Aj) Qmid, MvPolynomial.algebraMap_eq];
          rfl
    have rhs : algebraMap Quof Qmid (algebraMap A Quof a)
        = Ideal.Quotient.mk Imapped (MvPolynomial.C (algebraMap A Aj a)) := by
      rw [IsScalarTower.algebraMap_apply A (MvPolynomial ι A) Quof a, MvPolynomial.algebraMap_eq]
      rw [show (algebraMap (MvPolynomial ι A) Quof) (MvPolynomial.C a)
            = Ideal.Quotient.mk I (MvPolynomial.C a) from rfl]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      rw [show (algebraMap (MvPolynomial ι A) (MvPolynomial ι Aj)) (MvPolynomial.C a)
            = MvPolynomial.C (algebraMap A Aj a) from by
          rw [show (algebraMap (MvPolynomial ι A) (MvPolynomial ι Aj))
                = (MvPolynomial.map (algebraMap A Aj) : MvPolynomial ι A →+* MvPolynomial ι Aj)
                    from rfl,
              MvPolynomial.map_C]]
    rw [IsScalarTower.algebraMap_apply A Aj Qmid a, lhs, rhs]
  -- upgrade `e1` to an `A`-algebra equivalence.
  have e1' : Localization.Away bj ≃ₐ[A] Qmid :=
    AlgEquiv.ofRingEquiv (f := e1.toRingEquiv) (by
      intro a
      change e1 (algebraMap A (Localization.Away bj) a) = algebraMap A Qmid a
      rw [IsScalarTower.algebraMap_apply A Quof (Localization.Away bj) a]
      rw [e1.commutes (algebraMap A Quof a)]
      rw [htower])
  -- The extended relation is `rel cj`, so `Qmid` is `Quo cj`.
  have hidealeq : Imapped
      = Ideal.span {(∑ i, MvPolynomial.C (cj i) * MvPolynomial.X i) - 1} := by
    rw [hImapped, hI, Ideal.map_span]
    congr 1
    rw [Set.image_singleton]; congr 1
    change (algebraMap (MvPolynomial ι A) (MvPolynomial ι Aj)) rf = _
    have hae : (algebraMap (MvPolynomial ι A) (MvPolynomial ι Aj)) rf
        = MvPolynomial.map (algebraMap A Aj) rf := rfl
    rw [hae, hrf]
    simp only [map_sub, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, map_one, hcj]
  -- `e2 : Qmid ≃ₐ[Aj] Quo cj`.
  have e2 : Qmid ≃ₐ[Aj] SingularIdealVarElim.Quo cj := Ideal.quotientEquivAlgOfEq Aj hidealeq
  have e2' : Qmid ≃ₐ[A] SingularIdealVarElim.Quo cj := e2.restrictScalars A
  -- Compose the three identifications and restrict scalars to `R`.
  exact ⟨((e0.trans (e1'.trans e2')).restrictScalars R)⟩

/-- Let `B` be an `A`-algebra presented as `MvPolynomial ι A ⧸ span {∑ C (f i) * X i - 1}` for
a finite family `f : ι → A`, inside a scalar tower `R → A → B`.  If every localization
`A_{f j}` is smooth over `R`, then so is the localization of `B` away from the image of `f j`.

Indeed, inverting `f j` in `B` makes the defining relation solvable for `x j`, exhibiting
`B_{f j}` as a polynomial ring over `A_{f j}` in the remaining variables, so `A_{f j} → B_{f j}`
is smooth and the composite `R → A_{f j} → B_{f j}` is smooth as well. -/
theorem smooth_localizationAway_image_of_smooth_localizationAway
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] (f : ι → A)
    (B : Type*) [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hB : Nonempty (B ≃ₐ[A] MvPolynomial ι A ⧸
      Ideal.span {(∑ i, MvPolynomial.C (f i) * MvPolynomial.X i) - 1}))
    (hAf : ∀ j, Algebra.Smooth R (Localization.Away (f j)))
    (j : ι) :
    Algebra.Smooth R (Localization.Away (algebraMap A B (f j))) := by
  -- `DecidableEq ι` is needed for the variable-elimination machinery.
  classical
  set Aj := Localization.Away (f j) with hAj
  set cj : ι → Aj := fun i => algebraMap A Aj (f i) with hcj
  -- `cⱼ j` is a unit in `Aⱼ` since `Aⱼ` inverts `f j`.
  have hunit : IsUnit (cj j) := by
    rw [hcj]
    exact IsLocalization.Away.algebraMap_isUnit (f j)
  have hconn : Nonempty
      (Localization.Away (algebraMap A B (f j)) ≃ₐ[R] SingularIdealVarElim.Quo cj) :=
    connectionEquiv R A f B hB j
  -- `Quo cⱼ` is smooth over `Aⱼ` by variable elimination, and `R → Aⱼ` is smooth by `hAf j`.
  have hsmoothAjQuo : Algebra.Smooth Aj (SingularIdealVarElim.Quo cj) :=
    SingularIdealVarElim.smooth_Quo j cj hunit
  have hsmoothRQuo : Algebra.Smooth R (SingularIdealVarElim.Quo cj) := by
    have hRAj : Algebra.Smooth R Aj := hAf j
    exact Algebra.Smooth.comp R Aj (SingularIdealVarElim.Quo cj)
  -- Transport smoothness back across the connection isomorphism.
  obtain ⟨e⟩ := hconn
  exact ⟨Algebra.FormallySmooth.of_equiv e.symm,
    Algebra.FinitePresentation.equiv e.symm⟩

/-- Given ring maps `R → A → Λ` with `A` of finite presentation over `R`, if the image of the
singular ideal `H_{A/R}` generates the unit ideal of `Λ`, then `A → Λ` factors as
`A → B → Λ` with `B` smooth over `R`. -/
@[stacks 07EU]
theorem exists_smooth_factorization_of_singularIdeal_map_eq_top
    (R : Type u) (A : Type v) (Λ : Type w) [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra A Λ] [Algebra R Λ] [IsScalarTower R A Λ]
    [Algebra.FinitePresentation R A]
    (h : Ideal.map (algebraMap A Λ) (singularIdeal R A) = ⊤) :
    ∃ (B : Type (max v w)) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra A B)
      (_ : Algebra B Λ),
      IsScalarTower R A B ∧ IsScalarTower A B Λ ∧ IsScalarTower R B Λ ∧ Algebra.Smooth R B := by
  classical
  -- Extract a finite combination `∑ c x • x = 1` in Λ with each preimage in H_{A/R}.
  have h1 : (1 : Λ) ∈ Ideal.map (algebraMap A Λ) (singularIdeal R A) := by rw [h]; trivial
  rw [Ideal.map] at h1
  have h2 : (1 : Λ) ∈ Submodule.span Λ (⇑(algebraMap A Λ) '' ↑(singularIdeal R A)) := h1
  rw [Submodule.mem_span_set] at h2
  obtain ⟨c, hcsub, hcsum⟩ := h2
  have hpre : ∀ y : {x // x ∈ c.support}, ∃ a, a ∈ singularIdeal R A ∧ algebraMap A Λ a = y.1 := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, hay⟩ := hcsub (Finset.mem_coe.2 hy)
    exact ⟨a, ha, hay⟩
  choose f hf hfval using hpre
  -- The polynomial ring P = A[X i] over the (finite) index set of the support.
  set P := MvPolynomial {x // x ∈ c.support} A with hP
  -- The relation `w = ∑ f i • X i - 1`.
  set w : P := (∑ i, MvPolynomial.C (f i) * MvPolynomial.X i) - 1 with hw
  set J : Ideal P := Ideal.span {w} with hJ
  set B := P ⧸ J with hB
  -- The A-algebra map P → Λ sending `X i ↦ c i` kills `w`.
  let φ : P →ₐ[A] Λ := MvPolynomial.aeval (fun i => c i.1)
  have hφw : φ w = 0 := by
    rw [hw]
    simp only [map_sub, map_sum, map_mul, map_one, φ]
    rw [sub_eq_zero]
    rw [Finsupp.sum] at hcsum
    rw [← hcsum, ← Finset.sum_attach c.support (fun x => c x • x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_X, smul_eq_mul, mul_comm (c ↑x)]
    congr 1
    exact hfval x
  -- Hence φ factors through B = P/J as an A-algebra map ψ : B →ₐ[A] Λ.
  have hker' : ∀ a ∈ J, φ a = 0 := fun a ha =>
    RingHom.mem_ker.1 ((Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 hφw) ha)
  let ψ : B →ₐ[A] Λ := Ideal.Quotient.liftₐ J φ hker'
  -- Equip Λ with the B-algebra structure coming from ψ.
  let algBΛ : Algebra B Λ := ψ.toRingHom.toAlgebra
  have hψalg : algebraMap B Λ = ψ.toRingHom := rfl
  refine ⟨B, inferInstance, inferInstance, inferInstance, algBΛ, inferInstance, ?_, ?_, ?_⟩
  · -- IsScalarTower A B Λ
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [hψalg]
    change _ = ψ (algebraMap A B a)
    rw [AlgHom.commutes]
  · -- IsScalarTower R B Λ
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [hψalg]
    change algebraMap R Λ r = ψ (algebraMap R B r)
    rw [IsScalarTower.algebraMap_apply R A B r, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply R A Λ r]
  · -- `Algebra.Smooth R B`, checked Zariski-locally on `Spec(B)` along the cover by the
    -- principal opens `D(bᵢ)`, where `bᵢ := algebraMap A B (f i)`.
    have hAf : ∀ i, Algebra.Smooth R (Localization.Away (f i)) := fun i =>
      smooth_localization_away_of_mem_singularIdeal R A (hf i)
    -- `B = P ⧸ J` is definitionally `MvPolynomial _ A ⧸ span {w}`, so the presentation
    -- witness is the identity equivalence.
    have hBpres : Nonempty (B ≃ₐ[A] MvPolynomial {x // x ∈ c.support} A ⧸
        Ideal.span {(∑ i, MvPolynomial.C (f i) * MvPolynomial.X i) - 1}) :=
      ⟨AlgEquiv.refl⟩
    have hsmoothAway : ∀ i : {x // x ∈ c.support},
        Algebra.Smooth R (Localization.Away (algebraMap A B (f i))) := fun i =>
      smooth_localizationAway_image_of_smooth_localizationAway R A f B hBpres hAf i
    -- In `B` one has `∑ i (algebraMap A B (f i)) * xᵢ = 1`, with `xᵢ` the image of `X i`, so
    -- the family `{ algebraMap A B (f i) }` spans the unit ideal of `B`.
    set sB : Set B := Set.range (fun i : {x // x ∈ c.support} => algebraMap A B (f i)) with hsB
    have hspan : Ideal.span sB = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have key : (1 : B) = ∑ i, algebraMap A B (f i) * (Ideal.Quotient.mk J (MvPolynomial.X
          i)) := by
        have h0 : Ideal.Quotient.mk J ((∑ i, MvPolynomial.C (f i) * MvPolynomial.X i) - 1) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
        rw [map_sub, map_one, sub_eq_zero] at h0
        rw [← h0, map_sum]
        apply Finset.sum_congr rfl
        intro i _; rw [map_mul]; rfl
      rw [key]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
    refine smooth_of_span_eq_top_away R B sB hspan ?_
    rintro ⟨_, i, rfl⟩
    exact hsmoothAway i
