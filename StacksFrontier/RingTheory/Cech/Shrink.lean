module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.LinearAlgebra.DFinsupp
public import StacksFrontier.RingTheory.Cech.BaseChange
public import StacksFrontier.RingTheory.Cech.Cohomology
public import StacksFrontier.RingTheory.Cech.Substrate

@[expose] public section

/-!
# The extended alternating Čech complex in a free module universe

Let `R` be a commutative ring in `Type u`, let `f : Fin r → R` and let `M` be a `v`-small
`R`-module. Each Čech localization `Cech.cechMod f M s` is `v`-small, and replacing every term of
`Cech.cechComplex f M` by its canonical `Shrink` model gives a complex `Cech.cechComplexShrink`
in `ModuleCat.{v} R`, degreewise `R`-linearly equivalent to `Cech.cechComplex f M` compatibly with
the differentials. Its cohomology agrees with that of `Cech.cechComplex f M`, and it satisfies the
conclusions of Stacks 0G6K.

## Main definitions

* `Cech.cechTermShrink`, `Cech.cechDShrink`, `Cech.cechComplexShrink`: the extended alternating
  Čech complex in the module universe `v`.
* `Cech.cechTermShrinkEquiv`: the degreewise linear equivalence with `Cech.cechTerm`.
* `Cech.extendedCechComplexShrink`: the same complex in integer degrees.

## Main results

* `Cech.small_submonoidPowers` and `Cech.small_localizedModule`: a Čech localization of a
  `v`-small module is `v`-small.
* `Cech.cechTermShrinkEquiv_cechDShrink`: the equivalence commutes with the differentials.
* `Cech.nonempty_homology_cechComplexShrink_linearEquiv`,
  `Cech.nonempty_homology_extendedCechComplexShrink_linearEquiv`: the cohomology of
  `Cech.cechComplexShrink` is linearly equivalent to that of `Cech.cechComplex`, in natural and in
  integer degrees.
* `Cech.cechComplexShrink_homology_torsion_support_vanishes`: the cohomology is concentrated in
  degrees `0, …, r`, every `f i` acts locally nilpotently on it, its support lies in the common
  zero locus of the `f i`, and it vanishes when some element of `(f₁, …, f_r)` acts invertibly on
  `M`.
* `Cech.isUnit_algebraMap_cechModCatShrink`: on the summand indexed by `s`, every `f i` with
  `i ∈ s` acts invertibly.
* `Cech.subsingleton_cechTermShrink_of_lt`: the terms vanish above degree `r`.

## References

* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

universe v w u

namespace Cech

variable {R : Type u} [CommRing R] {r : ℕ}

/-! ### Smallness of the Čech localizations -/

/-- The powers of a single element are the image of `ℕ`, hence small in every universe. -/
instance small_submonoidPowers (g : R) : Small.{v} (Submonoid.powers g) :=
  small_of_surjective (f := fun n : ℕ => (⟨g ^ n, n, rfl⟩ : Submonoid.powers g))
    (fun x => by obtain ⟨n, hn⟩ := x.2; exact ⟨n, Subtype.ext hn⟩)

/-- A localization of a `v`-small module at a `v`-small submonoid is `v`-small: it is a quotient
of `M × S`. -/
instance small_localizedModule (S : Submonoid R) [Small.{v} S] (M : Type w)
    [AddCommGroup M] [Module R M] [Small.{v} M] : Small.{v} (LocalizedModule S M) :=
  small_of_surjective (f := fun p : M × S => LocalizedModule.mk p.1 p.2)
    (fun x => LocalizedModule.induction_on (fun m s => ⟨(m, s), rfl⟩) x)

/-! ### Linear equivalences and cohomology -/

/-- A complex of modules whose term in degree `i` is zero has no cohomology in degree `i`. -/
private theorem subsingleton_homology_of_isZero_X {S : Type*} [CommRing S] {ι : Type*}
    {cs : ComplexShape ι} (K : HomologicalComplex (ModuleCat S) cs) (i : ι)
    (h : CategoryTheory.Limits.IsZero (K.X i)) : Subsingleton (K.homology i) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact CategoryTheory.Limits.IsZero.of_epi (K.homologyπ i)
    (CategoryTheory.Limits.IsZero.of_mono (K.iCycles i) h)

/-- If `g` acts invertibly on `B` and `A ≃ₗ[S] B`, then `g` acts invertibly on `A`. -/
private theorem isUnit_algebraMap_of_linearEquiv {S : Type*} [CommRing S] {A : Type*} {B : Type*}
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] (e : A ≃ₗ[S] B) (g : S)
    (h : IsUnit (algebraMap S (Module.End S B) g)) :
    IsUnit (algebraMap S (Module.End S A) g) := by
  rw [Module.End.isUnit_iff] at h ⊢
  refine ⟨fun a b hab => e.injective (h.1 ?_), fun b => ?_⟩
  · simpa only [Module.algebraMap_end_apply, map_smul] using congrArg e hab
  · obtain ⟨c, hc⟩ := h.2 (e b)
    refine ⟨e.symm c, ?_⟩
    apply e.injective
    simpa only [Module.algebraMap_end_apply, map_smul, LinearEquiv.apply_symm_apply] using hc

/-- The unique linear equivalence between two trivial modules, possibly in different
universes. -/
private noncomputable def linearEquivOfSubsingleton {S : Type*} [CommRing S] {A : Type*}
    {B : Type*} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [Subsingleton A] [Subsingleton B] : A ≃ₗ[S] B where
  toFun _ := 0
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

variable (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M] [Small.{v} M]

/-! ### The small model of the complex -/

/-- The `v`-small model of the Čech localization `M_{∏ i ∈ s, f i}`. -/
abbrev cechModShrink (s : Finset (Fin r)) : Type v := Shrink.{v} (cechMod f M s)

/-- The `v`-small model of the degree-`p` term of the extended alternating Čech complex. -/
abbrev cechTermShrink (p : ℕ) : Type v :=
  DirectSum {s : Finset (Fin r) // s.card = p} fun s => cechModShrink.{v} f M s.1

/-- The `R`-linear equivalence between the `v`-small model of the degree-`p` term and
`Cech.cechTerm f M p`. -/
noncomputable def cechTermShrinkEquiv (p : ℕ) :
    cechTermShrink.{v} f M p ≃ₗ[R] cechTerm f M p :=
  DFinsupp.mapRange.linearEquiv fun s => Shrink.linearEquiv R (cechMod f M s.1)

/-- The differential of the small model: the Čech differential, conjugated by
`Cech.cechTermShrinkEquiv`. -/
noncomputable def cechDShrink (p : ℕ) :
    cechTermShrink.{v} f M p →ₗ[R] cechTermShrink.{v} f M (p + 1) :=
  (cechTermShrinkEquiv.{v} f M (p + 1)).symm.toLinearMap ∘ₗ (cechD f M p) ∘ₗ
    (cechTermShrinkEquiv.{v} f M p).toLinearMap

/-- `Cech.cechTermShrinkEquiv` commutes with the differentials. -/
theorem cechTermShrinkEquiv_cechDShrink (p : ℕ) (x : cechTermShrink.{v} f M p) :
    cechTermShrinkEquiv.{v} f M (p + 1) (cechDShrink.{v} f M p x) =
      cechD f M p (cechTermShrinkEquiv.{v} f M p x) := by
  simp [cechDShrink]

/-- The differentials of the small model square to zero. -/
theorem cechDShrink_comp_cechDShrink (p : ℕ) :
    (cechDShrink.{v} f M (p + 1)).comp (cechDShrink.{v} f M p) = 0 := by
  refine LinearMap.ext fun x => (cechTermShrinkEquiv.{v} f M (p + 1 + 1)).injective ?_
  rw [LinearMap.comp_apply, cechTermShrinkEquiv_cechDShrink, cechTermShrinkEquiv_cechDShrink,
    LinearMap.zero_apply, map_zero, ← LinearMap.comp_apply, cechD_comp_cechD,
    LinearMap.zero_apply]

/-- The extended alternating Čech complex `C^•(f₁, …, f_r; M)` in `ModuleCat.{v} R`: its
degree-`p` term is the canonical `v`-small model of `⨁_{#s = p} M_{∏ i ∈ s, f i}`. -/
noncomputable def cechComplexShrink : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (cechTermShrink.{v} f M p))
    (fun p => ModuleCat.ofHom (cechDShrink.{v} f M p))
    (fun p => ModuleCat.hom_ext (cechDShrink_comp_cechDShrink.{v} f M p))

/-- The differential of the small model in adjacent degrees. -/
theorem cechComplexShrink_d (p : ℕ) :
    (cechComplexShrink.{v} f M).d p (p + 1) = ModuleCat.ofHom (cechDShrink.{v} f M p) :=
  CochainComplex.of_d (fun p => ModuleCat.of R (cechTermShrink.{v} f M p))
    (fun p => ModuleCat.ofHom (cechDShrink.{v} f M p)) p

/-! ### Cohomology of the small model -/

/-- The degree-`p` linear equivalence between the terms of `Cech.cechComplexShrink f M` and of
`Cech.cechComplex f M`. -/
noncomputable def cechComplexShrinkXEquiv (p : ℕ) :
    ((cechComplexShrink.{v} f M).X p) ≃ₗ[R] ((cechComplex f M).X p) :=
  cechTermShrinkEquiv.{v} f M p

/-- `Cech.cechComplexShrinkXEquiv` commutes with the differentials `d n m` of both complexes, for
all `n m`. -/
theorem cechComplexShrinkXEquiv_d (n m : ℕ) (x : (cechComplexShrink.{v} f M).X n) :
    cechComplexShrinkXEquiv.{v} f M m (((cechComplexShrink.{v} f M).d n m).hom x) =
      ((cechComplex f M).d n m).hom (cechComplexShrinkXEquiv.{v} f M n x) := by
  by_cases h : n + 1 = m
  · subst h
    rw [cechComplexShrink_d, cechComplex_d]
    exact cechTermShrinkEquiv_cechDShrink.{v} f M n x
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape _ _ _ h]
    simp

/-- In every natural degree, the cohomology of `Cech.cechComplexShrink f M` is linearly
equivalent to that of `Cech.cechComplex f M`. -/
theorem nonempty_homology_cechComplexShrink_linearEquiv (p : ℕ) :
    Nonempty ((cechComplexShrink.{v} f M).homology p ≃ₗ[R] (cechComplex f M).homology p) :=
  KoszulC.homologyTransport_of_degreewiseEquiv (fun n => cechComplexShrinkXEquiv.{v} f M n)
    (fun n m x => cechComplexShrinkXEquiv_d.{v} f M n m x) p

/-! ### The terms of the small model -/

/-- Above degree `r` the terms of the small model are trivial. -/
theorem subsingleton_cechTermShrink_of_lt {p : ℕ} (h : r < p) :
    Subsingleton (cechTermShrink.{v} f M p) :=
  ⟨fun _ _ => DFinsupp.ext fun s =>
    absurd s.2 ((s.1.card_le_univ.trans_eq (Fintype.card_fin r)).trans_lt h).ne⟩

/-- The small model of the Čech localization `M_{∏ i ∈ s, f i}`, as an object of
`ModuleCat.{v} R`. -/
noncomputable def cechModCatShrink (s : Finset (Fin r)) : ModuleCat.{v} R :=
  ModuleCat.of R (cechModShrink.{v} f M s)

/-- The linear equivalence between the small model of the Čech localization and the localization
itself. -/
noncomputable def cechModCatShrinkEquiv (s : Finset (Fin r)) :
    (cechModCatShrink.{v} f M s : Type v) ≃ₗ[R] cechMod f M s :=
  Shrink.linearEquiv R (cechMod f M s)

/-- On the small model of `M_{∏ i ∈ s, f i}` every `f i` with `i ∈ s` acts invertibly. -/
theorem isUnit_algebraMap_cechModCatShrink {s : Finset (Fin r)} {i : Fin r} (hi : i ∈ s) :
    IsUnit (algebraMap R (Module.End R (cechModCatShrink.{v} f M s)) (f i)) :=
  isUnit_algebraMap_of_linearEquiv (cechModCatShrinkEquiv.{v} f M s) (f i)
    (isUnit_algebraMap f M (Finset.singleton_subset_iff.mpr hi)
      (LocalizedModule.mkLinearMap (cechSub f s) M) ⟨f i, by simp [cechSub]⟩)

/-! ### The complex in integer degrees -/

/-- The extended alternating Čech complex in `ModuleCat.{v} R`, in integer degrees. -/
noncomputable abbrev extendedCechComplexShrink : CochainComplex (ModuleCat.{v} R) ℤ :=
  (cechComplexShrink.{v} f M).extend ComplexShape.embeddingUpNat

/-- The extension to integer degrees of a complex indexed by `ℕ` vanishes in negative degrees. -/
private theorem isZero_extend_X_of_neg {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] [CategoryTheory.Limits.HasZeroObject C]
    (K : CochainComplex C ℕ) {q : ℤ} (hq : q < 0) :
    CategoryTheory.Limits.IsZero ((K.extend ComplexShape.embeddingUpNat).X q) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ fun n hn => ?_
  rw [ComplexShape.embeddingUpNat_f] at hn
  omega

/-- In negative degrees the integer-indexed small model vanishes. -/
theorem isZero_extendedCechComplexShrink_X_of_neg {q : ℤ} (hq : q < 0) :
    CategoryTheory.Limits.IsZero ((extendedCechComplexShrink.{v} f M).X q) :=
  isZero_extend_X_of_neg _ hq

/-- In every integer degree, the cohomology of `Cech.extendedCechComplexShrink f M` is linearly
equivalent to that of the integer-indexed `Cech.cechComplex f M`. -/
theorem nonempty_homology_extendedCechComplexShrink_linearEquiv (q : ℤ) :
    Nonempty ((extendedCechComplexShrink.{v} f M).homology q ≃ₗ[R]
      ((cechComplex f M).extend ComplexShape.embeddingUpNat).homology q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, by omega⟩
    obtain ⟨e⟩ := nonempty_homology_cechComplexShrink_linearEquiv.{v} f M n
    exact ⟨((HomologicalComplex.extendHomologyIso (cechComplexShrink.{v} f M)
        ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp)).toLinearEquiv.trans
      (e.trans (HomologicalComplex.extendHomologyIso (cechComplex f M)
        ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp)).toLinearEquiv.symm))⟩
  · have h₁ : Subsingleton ((extendedCechComplexShrink.{v} f M).homology q) :=
      subsingleton_homology_of_isZero_X _ q
        (isZero_extendedCechComplexShrink_X_of_neg.{v} f M (lt_of_not_ge hq))
    have h₂ : Subsingleton
        (((cechComplex f M).extend ComplexShape.embeddingUpNat).homology q) :=
      subsingleton_homology_of_isZero_X _ q
        (isZero_extend_X_of_neg _ (lt_of_not_ge hq))
    exact ⟨linearEquivOfSubsingleton⟩

/-! ### Torsion, support and vanishing of the cohomology -/

/-- The cohomology of `Cech.extendedCechComplexShrink f M` is concentrated in degrees `0, …, r`;
every `f i` acts locally nilpotently on every cohomology class; the support lies in the common
zero locus of the `f i`; and all cohomology vanishes as soon as some element of the ideal they
generate acts invertibly on `M`. -/
theorem cechComplexShrink_homology_torsion_support_vanishes (q : ℤ) :
    ((q < 0 ∨ (r : ℤ) < q) →
        Subsingleton ((extendedCechComplexShrink.{v} f M).homology q)) ∧
      (∀ (i : Fin r) (x : (extendedCechComplexShrink.{v} f M).homology q),
        ∃ n : ℕ, 0 < n ∧ f i ^ n • x = 0) ∧
      Module.support R ((extendedCechComplexShrink.{v} f M).homology q) ⊆
        PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) ∧
      ((∃ g ∈ Ideal.span (Set.range f), IsUnit (algebraMap R (Module.End R M) g)) →
        Subsingleton ((extendedCechComplexShrink.{v} f M).homology q)) := by
  obtain ⟨e⟩ := nonempty_homology_extendedCechComplexShrink_linearEquiv.{v} f M q
  obtain ⟨hvan, htors, hsupp, hunit⟩ := cechComplex_homology_torsion_support_vanishes f M q
  refine ⟨fun h => e.toEquiv.subsingleton_congr.mpr (hvan h), fun i x => ?_,
    e.support_eq.trans_subset hsupp, fun h => e.toEquiv.subsingleton_congr.mpr (hunit h)⟩
  obtain ⟨n, hn, hkill⟩ := htors i (e x)
  exact ⟨n, hn, e.injective (by rw [map_smul, hkill, map_zero])⟩

end Cech
