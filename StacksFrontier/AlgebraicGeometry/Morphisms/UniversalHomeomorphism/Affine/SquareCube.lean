module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Subalgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Powers
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.RingTheory.Support.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A square and a cube in a subring

Let `A` be a subring of a commutative ring `B`. If the induced morphism from the spectrum of
`B` to the spectrum of `A` is a universal homeomorphism and induces isomorphisms on all
residue fields, then any such proper extension contains an element outside `A` whose square
and cube belong to `A`.

## Main definitions

None.

## Main results

* `exists_not_mem_and_sq_mem_and_cube_mem_of_universalHomeomorphism_of_residueFieldMap_isIso`
  produces the required element.

## Implementation notes

The inclusion `A ⊆ B` is represented by `A : Subring B`; the condition that the extension is
proper is consequently written `A ≠ ⊤`, and the assertion about residue fields uses the
canonical residue-field map of the induced morphism of affine schemes. The argument localizes
at a minimal prime of the support of `C / A`, where `C` is a finite intermediate algebra, and
then clears denominators; the supporting statements about that localization are the private
lemmas below.

## References

* [Stacks Project, Tag 0CNB](https://stacks.math.columbia.edu/tag/0CNB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private theorem exists_stalk_residue_representative
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : Spec (CommRingCat.of C))
    (hres : IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap q))
    (c : C) :
    ∃ a : (Scheme.Spec.obj (Opposite.op (CommRingCat.of A))).presheaf.stalk
        ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) q),
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op).stalkMap q a -
        (Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).presheaf.germ ⊤ q trivial
          ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)) ∈
      IsLocalRing.maximalIdeal
        ((Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).presheaf.stalk q) := by
  let f : Scheme.Spec.obj (Opposite.op (CommRingCat.of C)) ⟶
      Scheme.Spec.obj (Opposite.op (CommRingCat.of A)) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op
  have : IsIso (f.residueFieldMap q) := hres
  let e := asIso (f.residueFieldMap q)
  let rC := (Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).residue q
    ((Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).presheaf.germ ⊤ q trivial
      ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c))
  let rA := e.inv rC
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective rA
  refine ⟨a, ?_⟩
  have hm : f.residueFieldMap q
      ((Scheme.Spec.obj (Opposite.op (CommRingCat.of A))).residue (f q) a) = rC := by
    calc
      _ = f.residueFieldMap q rA := congrArg (f.residueFieldMap q) ha
      _ = rC := by simp [rA, e]
  have hval : (Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).residue q
      (f.stalkMap q a) = rC := by
    have h := congrArg (fun φ => φ a) (Scheme.residue_residueFieldMap f q)
    change f.residueFieldMap q
        ((Scheme.Spec.obj (Opposite.op (CommRingCat.of A))).residue (f q) a) =
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).residue q (f.stalkMap q a) at h
    exact h.symm.trans hm
  rw [← IsLocalRing.residue_eq_zero_iff]
  show (Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).residue q
      (f.stalkMap q a) -
    (Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).residue q
      ((Scheme.Spec.obj (Opposite.op (CommRingCat.of C))).presheaf.germ ⊤ q trivial
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)) = 0
  rw [hval]
  simp [rC]

private theorem exists_localRingHom_sub_mem_maximalIdeal
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : Spec (CommRingCat.of C)) [q.asIdeal.IsPrime]
    (hres : IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap q))
    (c : C) :
    ∃ aLoc : Localization.AtPrime (q.comap (algebraMap A C)).asIdeal,
      Localization.localRingHom (q.comap (algebraMap A C)).asIdeal q.asIdeal (algebraMap A C)
          rfl aLoc - algebraMap C (Localization.AtPrime q.asIdeal) c ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum A := q.comap (algebraMap A C)
  let f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of A) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A C))
  obtain ⟨aSt, haSt⟩ := exists_stalk_residue_representative q hres c
  let iA := Spec.stalkIso (CommRingCat.of A) p
  let iC := Spec.stalkIso (CommRingCat.of C) q
  let eC := iC.commRingCatIsoToRingEquiv
  let aLoc : Localization.AtPrime p.asIdeal := iA.hom.hom aSt
  let g : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap A C) rfl
  let d := f.stalkMap q aSt -
    (Spec (CommRingCat.of C)).presheaf.germ ⊤ q trivial
      ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)
  have hdSt : d ∈ IsLocalRing.maximalIdeal
      ((Spec (CommRingCat.of C)).presheaf.stalk q) := haSt
  have hdLoc : eC d ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
    have h := Ideal.mem_map_of_mem eC hdSt
    rwa [IsLocalRing.map_ringEquiv_maximalIdeal eC] at h
  have hEq : iC.inv.hom (g aLoc) = f.stalkMap q aSt :=
    congrArg (fun k : (Spec (CommRingCat.of A)).presheaf.stalk p ⟶
      (Spec (CommRingCat.of C)).presheaf.stalk q => k.hom aSt)
      (Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom (algebraMap A C)) q)
  have hst : iC.hom.hom (f.stalkMap q aSt) = g aLoc := by
    rw [← hEq]
    simp
  have hgerm : iC.hom.hom ((Spec (CommRingCat.of C)).presheaf.germ ⊤ q trivial
      ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)) =
      algebraMap C (Localization.AtPrime q.asIdeal) c := by
    have h := congrArg
      (fun k : CommRingCat.of Γ(Spec (CommRingCat.of C), ⊤) ⟶
        CommRingCat.of (Localization.AtPrime q.asIdeal) =>
          k.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c))
      (Spec.germ_stalkMapIso_hom (R := CommRingCat.of C) q)
    simpa [iC, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h
  have heq : eC d = g aLoc - algebraMap C (Localization.AtPrime q.asIdeal) c := by
    show iC.hom.hom d = _
    dsimp [d]
    rw [map_sub, hst, hgerm]
  exact ⟨aLoc, by rwa [← heq]⟩

private theorem exists_numerator_mem_prime_of_residueFieldMap_isIso
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : Spec (CommRingCat.of C)) [q.asIdeal.IsPrime]
    (hres : IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap q))
    (c : C) :
    ∃ (s : A) (a : A), s ∉ (q.comap (algebraMap A C)).asIdeal ∧
      algebraMap A C s * c - algebraMap A C a ∈ q.asIdeal := by
  let p : PrimeSpectrum A := q.comap (algebraMap A C)
  let g : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap A C) rfl
  obtain ⟨aLoc, hdiff⟩ := exists_localRingHom_sub_mem_maximalIdeal q hres c
  change g aLoc - algebraMap C (Localization.AtPrime q.asIdeal) c ∈ _ at hdiff
  obtain ⟨a, s, has⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl aLoc
  let sC : q.asIdeal.primeCompl := ⟨algebraMap A C s, s.property⟩
  have hrep : g aLoc = IsLocalization.mk' (Localization.AtPrime q.asIdeal)
      (algebraMap A C a) sC := by
    rw [← has]
    simpa [g, sC] using Localization.localRingHom_mk' p.asIdeal q.asIdeal
      (algebraMap A C) rfl a s
  have hcancel : algebraMap C (Localization.AtPrime q.asIdeal)
      (algebraMap A C s) * g aLoc =
        algebraMap C (Localization.AtPrime q.asIdeal) (algebraMap A C a) := by
    rw [hrep, mul_comm]
    exact IsLocalization.mk'_spec (Localization.AtPrime q.asIdeal) (algebraMap A C a) sC
  refine ⟨s, a, s.property, ?_⟩
  have hneg : algebraMap C (Localization.AtPrime q.asIdeal) c - g aLoc ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
    simpa using (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).neg_mem hdiff
  have hmul := (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).mul_mem_left
    (algebraMap C (Localization.AtPrime q.asIdeal) (algebraMap A C s)) hneg
  have hfinal : algebraMap C (Localization.AtPrime q.asIdeal)
        (algebraMap A C s * c - algebraMap A C a) =
      algebraMap C (Localization.AtPrime q.asIdeal) (algebraMap A C s) *
        (algebraMap C (Localization.AtPrime q.asIdeal) c - g aLoc) := by
    rw [map_sub, map_mul, ← hcancel]
    ring
  rw [← hfinal] at hmul
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (S := Localization.AtPrime q.asIdeal) q.asIdeal
      (algebraMap A C s * c - algebraMap A C a)).mp hmul

private theorem support_localized_at_minimal_prime
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hmin : ∀ q, q ∈ Module.support R M → q.asIdeal ≤ p.asIdeal → q = p) :
    Module.support (Localization p.asIdeal.primeCompl)
        (LocalizedModule p.asIdeal.primeCompl M) =
      {IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)} := by
  let S := p.asIdeal.primeCompl
  let Rₚ := Localization S
  have hc : PrimeSpectrum.comap (algebraMap R Rₚ)
      (IsLocalRing.closedPoint Rₚ) = p := by
    ext x
    show algebraMap R Rₚ x ∈ IsLocalRing.maximalIdeal Rₚ ↔ x ∈ p.asIdeal
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (S := Rₚ) p.asIdeal x
  ext q
  rw [IsBaseChange.support_eq_preimage_comap
    (IsLocalizedModule.isBaseChange S Rₚ (LocalizedModule.mkLinearMap S M))]
  constructor
  · intro hq
    have hle : (PrimeSpectrum.comap (algebraMap R Rₚ) q).asIdeal ≤ p.asIdeal :=
      (Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.2.ne_top)).trans
        (congrArg PrimeSpectrum.asIdeal hc).le
    exact PrimeSpectrum.localization_comap_injective Rₚ S ((hmin _ hq hle).trans hc.symm)
  · rintro rfl
    show PrimeSpectrum.comap (algebraMap R Rₚ) (IsLocalRing.closedPoint Rₚ) ∈
      Module.support R M
    rwa [hc]

private theorem exists_pow_smul_eq_zero_of_support_singleton
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (m : PrimeSpectrum R)
    (hsupp : Module.support R M = {m})
    {x : R} (hx : x ∈ m.asIdeal) :
    ∃ n : ℕ, ∀ z : M, x ^ n • z = 0 := by
  have hxrad : x ∈ (Module.annihilator R M).radical := by
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun I hI => ?_
    let q : PrimeSpectrum R := ⟨I, hI.2⟩
    have hq : q ∈ Module.support R M := by
      rw [Module.support_eq_zeroLocus]
      exact (PrimeSpectrum.mem_zeroLocus q ↑(Module.annihilator R M)).mpr hI.1
    have hqm : q = m := by simpa [hsupp] using hq
    show x ∈ q.asIdeal
    rwa [hqm]
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxrad
  exact ⟨n, Module.mem_annihilator.mp hn⟩

private theorem exists_mul_mem_range_of_algebraMap_mem_range
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (S : Submonoid A) (z : C)
    (hz : algebraMap C (Localization (S.map (algebraMap A C))) z ∈ Set.range
      (IsLocalization.map (M := S) (S := Localization S) (T := S.map (algebraMap A C))
        (Localization (S.map (algebraMap A C))) (algebraMap A C) S.le_comap_map)) :
    ∃ s : S, algebraMap A C s.1 * z ∈ Set.range (algebraMap A C) := by
  let R := Localization S
  let T := S.map (algebraMap A C)
  let D := Localization T
  let φ : R →+* D := IsLocalization.map (M := S) (S := R) (T := T) D
    (algebraMap A C) S.le_comap_map
  change algebraMap C D z ∈ Set.range φ at hz
  obtain ⟨w, hw⟩ := hz
  obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj S w
  have heq : algebraMap C D (z * algebraMap A C t.1) =
      algebraMap C D (algebraMap A C a) := by
    have h := congrArg φ ht
    rw [map_mul, show φ w = algebraMap C D z from hw] at h
    simpa [φ, IsLocalization.map_eq S.le_comap_map, map_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists T D).mp heq
  obtain ⟨s, hs, hds⟩ := d.property
  refine ⟨⟨s, hs⟩ * t, ⟨s * a, ?_⟩⟩
  simpa [hds, map_mul, mul_assoc, mul_comm, mul_left_comm] using hd.symm

/-- The image in a localization of an element of `A` lies in the localized subring. -/
private theorem algebraMap_algebraMap_mem_range_map
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (S : Submonoid A) (a : A) :
    algebraMap C (Localization (S.map (algebraMap A C))) (algebraMap A C a) ∈ Set.range
      (IsLocalization.map (M := S) (S := Localization S) (T := S.map (algebraMap A C))
        (Localization (S.map (algebraMap A C))) (algebraMap A C) S.le_comap_map) :=
  ⟨algebraMap A (Localization S) a, IsLocalization.map_eq S.le_comap_map a⟩

/-- Clearing the denominator in a fraction representation `x = y / s`. -/
private theorem mul_algebraMap_eq_of_eq_mk'
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (S : Submonoid A)
    (x : Localization (S.map (algebraMap A C))) (y : C) (s : S)
    (hrep : x = IsLocalization.mk' (Localization (S.map (algebraMap A C))) y
      ⟨algebraMap A C s.1, Submonoid.mem_map_of_mem (algebraMap A C) s.2⟩) :
    x * algebraMap C (Localization (S.map (algebraMap A C))) (algebraMap A C s.1) =
      algebraMap C (Localization (S.map (algebraMap A C))) y := by
  simpa using (hrep.symm ▸ IsLocalization.mk'_spec (Localization (S.map (algebraMap A C))) y
    ⟨algebraMap A C s.1, Submonoid.mem_map_of_mem (algebraMap A C) s.2⟩)

private theorem algebraMap_mul_pow_mem_range_of_eq_mk'
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (S : Submonoid A)
    (x : Localization (S.map (algebraMap A C))) (b y : C) (s : S) (k : ℕ)
    (hrep : x = IsLocalization.mk' (Localization (S.map (algebraMap A C))) y
      ⟨algebraMap A C s.1, Submonoid.mem_map_of_mem (algebraMap A C) s.2⟩)
    (hb : algebraMap C (Localization (S.map (algebraMap A C))) b * x ^ k ∈
      Set.range (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map)) :
    algebraMap C (Localization (S.map (algebraMap A C))) (b * y ^ k) ∈
      Set.range (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map) := by
  let R := Localization S
  let T := S.map (algebraMap A C)
  let D := Localization T
  let φ : R →+* D := IsLocalization.map (M := S) (S := R) (T := T) D
    (algebraMap A C) S.le_comap_map
  have hspec := mul_algebraMap_eq_of_eq_mk' S x y s hrep
  have hpow : x ^ k * algebraMap C D ((algebraMap A C s.1) ^ k) = algebraMap C D (y ^ k) := by
    simpa [mul_pow, map_pow] using congrArg (fun z : D => z ^ k) hspec
  have hden : algebraMap C D ((algebraMap A C s.1) ^ k) ∈ Set.range φ := by
    rw [← map_pow]
    exact algebraMap_algebraMap_mem_range_map S _
  rcases hb with ⟨u, hu⟩
  rcases hden with ⟨v, hv⟩
  have heq : algebraMap C D (b * y ^ k) =
      (algebraMap C D b * x ^ k) * algebraMap C D ((algebraMap A C s.1) ^ k) := by
    rw [map_mul, ← hpow]
    ring
  exact ⟨u * v, by rw [map_mul, hu, hv, ← heq]⟩

private theorem mk'_eq_mk'_algebraMap_mul
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (S : Submonoid A) (y : C)
    (d s : S) :
    IsLocalization.mk' (Localization (S.map (algebraMap A C))) y
        ⟨algebraMap A C s.1, Submonoid.mem_map_of_mem (algebraMap A C) s.2⟩ =
      IsLocalization.mk' (Localization (S.map (algebraMap A C))) (algebraMap A C d.1 * y)
        ⟨algebraMap A C (d * s).1, Submonoid.mem_map_of_mem (algebraMap A C) (d * s).2⟩ := by
  calc
    _ = IsLocalization.mk' (Localization (S.map (algebraMap A C))) (algebraMap A C d.1)
          ⟨algebraMap A C d.1, Submonoid.mem_map_of_mem (algebraMap A C) d.2⟩ *
        IsLocalization.mk' (Localization (S.map (algebraMap A C))) y
          ⟨algebraMap A C s.1, Submonoid.mem_map_of_mem (algebraMap A C) s.2⟩ := by
      simp
    _ = _ := by
      rw [← IsLocalization.mk'_mul]
      congr 1
      apply Subtype.ext
      simp [map_mul]

private theorem exists_numerator_not_mem_of_localization_ringHom_with_representation
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (S : Submonoid A) (b : Fin 2 → C)
    (x : Localization (S.map (algebraMap A C))) (y₀ : C) (s₀ : S)
    (hrep : x = IsLocalization.mk' (Localization (S.map (algebraMap A C))) y₀
      ⟨algebraMap A C s₀.1, Submonoid.mem_map_of_mem (algebraMap A C) s₀.2⟩)
    (hx : x ∉ Set.range
      (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map))
    (hbx : ∀ i : Fin 2,
      algebraMap C (Localization (S.map (algebraMap A C))) (b i) * x ^ (i.val + 1) ∈
        Set.range (IsLocalization.map (M := S) (S := Localization S)
          (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
          (algebraMap A C) S.le_comap_map)) :
    ∃ (s₁ : S) (y : C) (c : A),
      x = IsLocalization.mk' (Localization (S.map (algebraMap A C))) y
        ⟨algebraMap A C s₁.1, Submonoid.mem_map_of_mem (algebraMap A C) s₁.2⟩ ∧
      y = algebraMap A C c * y₀ ∧ y ∉ Set.range (algebraMap A C) ∧
      ∀ i : Fin 2, b i * y ^ (i.val + 1) ∈ Set.range (algebraMap A C) := by
  let R := Localization S
  let T := S.map (algebraMap A C)
  let D := Localization T
  let φ : R →+* D := IsLocalization.map (M := S) (S := R) (T := T) D
    (algebraMap A C) S.le_comap_map
  let den (s : S) : T :=
    ⟨algebraMap A C s.1, Submonoid.mem_map_of_mem (algebraMap A C) s.2⟩
  have hfin (F : Finset (Fin 2)) :
      ∃ (s : S) (y : C) (c : S), x = IsLocalization.mk' D y (den s) ∧
        y = algebraMap A C c.1 * y₀ ∧
        ∀ i ∈ F, b i * y ^ (i.val + 1) ∈ Set.range (algebraMap A C) := by
    induction F using Finset.induction_on with
    | empty =>
        exact ⟨s₀, y₀, 1, by simpa [den] using hrep, by simp, by simp⟩
    | @insert i F hi ih =>
        obtain ⟨s, y, c₀, hrep', hfac, hprev⟩ := ih
        let k := i.val + 1
        have hz := algebraMap_mul_pow_mem_range_of_eq_mk' S x (b i) y s k hrep' (hbx i)
        obtain ⟨d, hd⟩ := exists_mul_mem_range_of_algebraMap_mem_range S (b i * y ^ k) hz
        refine ⟨d * s, algebraMap A C d.1 * y, d * c₀, ?_, ?_, ?_⟩
        · exact hrep'.trans (mk'_eq_mk'_algebraMap_mul S y d s)
        · rw [hfac, Submonoid.coe_mul, map_mul]
          ring
        · intro j hj
          rcases Finset.mem_insert.mp hj with hji | hj
          · subst j
            rcases hd with ⟨a, ha⟩
            refine ⟨d.1 ^ i.val * a, ?_⟩
            rw [map_mul, map_pow, ha]
            simp [k, pow_succ, mul_pow, mul_assoc, mul_comm, mul_left_comm]
          · rcases hprev j hj with ⟨a, ha⟩
            refine ⟨d.1 ^ (j.val + 1) * a, ?_⟩
            rw [map_mul, map_pow, ha]
            simp [mul_pow, mul_assoc, mul_comm]
  obtain ⟨s₁, y, c₀, hrep', hfac, hycond⟩ := hfin Finset.univ
  have hyNot : y ∉ Set.range (algebraMap A C) := by
    intro hy
    apply hx
    rw [hrep']
    rcases hy with ⟨a, rfl⟩
    refine ⟨IsLocalization.mk' R a s₁, ?_⟩
    rw [IsLocalization.map_mk']
  refine ⟨s₁, y, c₀.1, ?_, hfac, hyNot, fun i => hycond i (Finset.mem_univ i)⟩
  simpa [den] using hrep'

/-- An ideal that annihilates a module kills every multiple of its image. If
`I ≤ Module.annihilator R M` then, for every `z` in the ideal generated by the image of `I`
in an `R`-algebra `D` and every `d : D`, an `R`-linear map `ψ : D →ₗ[R] M` sends `z * d` to
zero. This is the step of Tag 0CNB that exhibits a power of the chosen element as a kernel
element, pulled out of the main argument so that it elaborates on its own. -/
private lemma map_ideal_mul_apply_eq_zero {R D M : Type u} [CommRing R] [CommRing D]
    [Algebra R D] [AddCommGroup M] [Module R M] (ψ : D →ₗ[R] M) (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    ∀ z ∈ Ideal.map (algebraMap R D) I, ∀ d : D, ψ (z * d) = 0 := by
  intro z hz
  change z ∈ Submodule.span D (algebraMap R D '' (↑I : Set R)) at hz
  exact Submodule.span_induction
    (s := algebraMap R D '' (↑I : Set R))
    (p := fun z _ => ∀ d : D, ψ (z * d) = 0)
    (fun z hz => by
      rcases hz with ⟨r, hr, rfl⟩
      intro d
      calc
        ψ (algebraMap R D r * d) = ψ (r • d) := by simp [Algebra.smul_def]
        _ = r • ψ d := map_smul ψ r d
        _ = 0 := Module.mem_annihilator.mp (hI hr) (ψ d))
    (fun d => by simp)
    (fun z₁ z₂ hz₁ hz₂ h₁ h₂ d => by
      rw [add_mul, map_add, h₁ d, h₂ d, add_zero])
    (fun r z hz h d => by
      simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h (r * d))
    hz

/-- The localized cokernel map of `A ⊆ C`, and its kernel.

Let `R` be a localization of `A` at `S` and let `D` be a localization of `C` at the image of
`S`. Localizing the quotient map `C → C ⧸ A` produces an `R`-linear map `ψ` from `D` to the
localized cokernel, which sends the image of `d : C` to the class of `d` and whose kernel is
exactly the image of `R` in `D`.

This is the kernel computation of Tag 0CNB, stated over abstract localizations presented by
`IsLocalization` hypotheses rather than over the concrete `Localization` types the tagged
theorem builds, so that it elaborates against these binders. -/
private lemma exists_localizedCokernel_map
    {A C R D N : Type u} [CommRing A] [CommRing C] [CommRing R] [CommRing D]
    [Algebra A C] [Algebra A R] [Algebra C D] [Algebra R D] [Algebra A D]
    [IsScalarTower A R D] [IsScalarTower A C D]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower A R N]
    (S : Submonoid A) [IsLocalization S R]
    [IsLocalization (S.map (algebraMap A C)) D]
    (fM : (C ⧸ (Algebra.linearMap A C).range) →ₗ[A] N) [IsLocalizedModule S fM] :
    ∃ ψ : D →ₗ[R] N,
      (∀ d : C, ψ (algebraMap C D d) =
        fM (Submodule.mkQ ((Algebra.linearMap A C).range) d)) ∧
      ∀ z : D, ψ z = 0 ↔ z ∈ Set.range (algebraMap R D) := by
  let fC : C →ₗ[A] D := (IsScalarTower.toAlgHom A C D).toLinearMap
  have : IsLocalizedModule S fC := by
    rw [isLocalizedModule_iff_isLocalization]
    show IsLocalization (S.map (algebraMap A C)) D
    infer_instance
  let π : C →ₗ[A] (C ⧸ (Algebra.linearMap A C).range) :=
    Submodule.mkQ ((Algebra.linearMap A C).range)
  let ψ₀ := IsLocalizedModule.map S fC fM π
  let ψ := ψ₀.extendScalarsOfIsLocalization S R
  refine ⟨ψ, fun d => ?_, fun z => ?_⟩
  · show ψ (fC d) = fM (π d)
    rw [show fC d = IsLocalizedModule.mk' fC d 1 from
      (IsLocalizedModule.mk'_one S fC d).symm]
    simp [ψ, ψ₀]
  · let gA : A →ₗ[A] R := Algebra.linearMap A R
    have : IsLocalizedModule S gA :=
      (isLocalizedModule_iff_isLocalization' S R).mpr inferInstance
    let ι : A →ₗ[A] C := Algebra.linearMap A C
    let ψI₀ := IsLocalizedModule.map S gA fC ι
    let ψI := ψI₀.extendScalarsOfIsLocalization S R
    have hψI₀comp : ψI₀ ∘ₗ gA =
        (Algebra.linearMap R D).restrictScalars A ∘ₗ gA := by
      refine LinearMap.ext fun a => ?_
      show ψI₀ (gA a) = Algebra.linearMap R D (gA a)
      rw [IsLocalizedModule.map_apply]
      calc
        fC (ι a) = algebraMap C D (algebraMap A C a) := rfl
        _ = algebraMap A D a := (IsScalarTower.algebraMap_apply A C D a).symm
        _ = Algebra.linearMap R D (gA a) := IsScalarTower.algebraMap_apply A R D a
    have hψI₀ : ψI₀ = (Algebra.linearMap R D).restrictScalars A :=
      IsLocalizedModule.ext S gA (fun x => IsLocalizedModule.map_units fC x) hψI₀comp
    have hψI : ψI = Algebra.linearMap R D := by
      show ψI₀.extendScalarsOfIsLocalization S R = Algebra.linearMap R D
      rw [hψI₀]
      rfl
    have hkerπ : π.ker = ι.range := Submodule.ker_mkQ _
    have hkerEq : ψ.ker = (Algebra.linearMap R D).range := by
      calc
        ψ.ker = (π.ker).localized' R S fC :=
          (LinearMap.localized'_ker_eq_ker_localizedMap (S := R) S fC fM π).symm
        _ = (ι.range).localized' R S fC := by rw [hkerπ]
        _ = ψI.range :=
          LinearMap.localized'_range_eq_range_localizedMap (S := R) S gA fC ι
        _ = (Algebra.linearMap R D).range := by rw [hψI]
    rw [← LinearMap.mem_ker, hkerEq, LinearMap.mem_range]
    exact Iff.rfl

/-- Two consecutive powers of `w` are killed by `ψ`, once some power of `w` lies in the ideal
generated by the maximal ideal of a local base `R` whose only support point for `M` is the
closed point.

The exponents in the maximal ideal that witness `w ^ k` span a finitely generated ideal `J`
of `R`, each of whose generators acts nilpotently on `M`; a power of `J` therefore annihilates
`M`, and the corresponding power of `w` is swallowed by `ψ`. This is the localized half of
Tag 0CNB, stated over an abstract algebra `R → D` rather than the concrete localizations the
tagged theorem builds, so that it elaborates against these binders instead of the tagged
proof's ambient chain of local definitions. -/
private lemma exists_pow_apply_eq_zero_of_pow_mem_map_maximalIdeal
    {R D M : Type u} [CommRing R] [IsLocalRing R] [CommRing D] [Algebra R D]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hsupp : Module.support R M = {IsLocalRing.closedPoint R})
    (ψ : D →ₗ[R] M) (w : D) {k : ℕ}
    (hw : w ^ k ∈ Ideal.map (algebraMap R D) (IsLocalRing.maximalIdeal R)) :
    ∃ n : ℕ, 2 ≤ n ∧ ψ (w ^ n) = 0 ∧ ψ (w ^ (n + 1)) = 0 := by
  classical
  have hspan : w ^ k ∈
      Submodule.span D (algebraMap R D '' (↑(IsLocalRing.maximalIdeal R) : Set R)) := hw
  obtain ⟨g, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hspan
  have hpre (d : {x : D // x ∈ t}) :
      ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ algebraMap R D x = d.1 := ht d.2
  choose coeff hcoeff hcoeffMap using hpre
  let J : Ideal R := Ideal.span (Set.range coeff)
  have hJrad : J ≤ (Module.annihilator R M).radical := by
    apply Ideal.span_le.2
    rintro x ⟨d, rfl⟩
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_support_singleton
      (IsLocalRing.closedPoint R) hsupp (hcoeff d)
    exact Ideal.mem_radical_iff.mpr ⟨m, Module.mem_annihilator.mpr hm⟩
  obtain ⟨N, hJN⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hJrad (Submodule.fg_span (Set.finite_range coeff))
  obtain ⟨N₁, hN₂, hNN₁⟩ : ∃ N₁, 2 ≤ N₁ ∧ N ≤ N₁ := ⟨max N 2, le_max_right _ _, le_max_left _ _⟩
  have hwkJ : w ^ k ∈ Ideal.map (algebraMap R D) J := by
    rw [← hsum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hgen : algebraMap R D (coeff ⟨d, hd⟩) ∈ Ideal.map (algebraMap R D) J :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨d, hd⟩, rfl⟩)
    rw [hcoeffMap ⟨d, hd⟩] at hgen
    exact (Ideal.map (algebraMap R D) J).smul_mem (g d) hgen
  have hsucc {I : Ideal D} {n : ℕ} (h : w ^ n ∈ I) : w ^ (n + 1) ∈ I := by
    rw [pow_succ]
    exact I.mul_mem_right w h
  have hpow : w ^ ((k + 1) * N₁) ∈ Ideal.map (algebraMap R D) (J ^ N₁) := by
    rw [Ideal.map_pow, pow_mul]
    exact Ideal.pow_mem_pow (hsucc hwkJ) N₁
  have hkill : ∀ z ∈ Ideal.map (algebraMap R D) (J ^ N₁), ∀ d : D, ψ (z * d) = 0 :=
    map_ideal_mul_apply_eq_zero ψ (J ^ N₁) ((Ideal.pow_le_pow_right hNN₁).trans hJN)
  refine ⟨(k + 1) * N₁, ?_, ?_, ?_⟩
  · nlinarith
  · simpa using hkill _ hpow 1
  · simpa using hkill _ (hsucc hpow) 1

private lemma exists_sq_cube_mem_of_subalgebra
    {B : Type u} [CommRing B] {A : Subring B} {C : Subalgebra A B} {y : C}
    (hyNot : y ∉ Set.range (algebraMap A C)) (hy2 : y ^ 2 ∈ Set.range (algebraMap A C))
    (hy3 : y ^ 3 ∈ Set.range (algebraMap A C)) :
    ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A := by
  have hmem {n : ℕ} (hn : y ^ n ∈ Set.range (algebraMap A C)) : y.1 ^ n ∈ A := by
    obtain ⟨a, ha⟩ := hn
    have hv : algebraMap A B a = y.1 ^ n := by
      simpa using congrArg (fun z : C => z.1) ha
    exact hv ▸ a.property
  exact ⟨y.1, fun hb => hyNot ⟨⟨y.1, hb⟩, Subtype.ext rfl⟩, hmem hy2, hmem hy3⟩

/-- The denominator-clearing half of Tag 0CNB. An element of the localization of an
intermediate algebra `C` which lies outside the localized subring, but whose square and cube
lie inside it, has a numerator witnessing the same three conditions before localization, and
that numerator gives the element of `B` the tag asks for. Separated from the main argument so
that each elaborates on its own. -/
private lemma exists_sq_cube_mem_of_localization_witness
    {B : Type u} [CommRing B] (A : Subring B) (C : Subalgebra A B) (S : Submonoid A)
    (x : Localization (S.map (algebraMap A C)))
    (hxNot : x ∉ (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map).range)
    (hx2 : x ^ 2 ∈ (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map).range)
    (hx3 : x ^ 3 ∈ (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map).range) :
    ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A := by
  let T : Submonoid C := S.map (algebraMap A C)
  let D := Localization T
  let R := Localization S
  let φ : R →+* D := IsLocalization.map (M := S) (S := R) (T := T) D
    (algebraMap A C) S.le_comap_map
  obtain ⟨y₀, t, hrep⟩ := IsLocalization.exists_mk'_eq T x
  obtain ⟨s, hs, hst⟩ := t.property
  let s₀ : S := ⟨s, hs⟩
  have hden : (⟨algebraMap A C s₀, Submonoid.mem_map_of_mem (algebraMap A C) s₀.2⟩ : T) = t :=
    Subtype.ext (by simpa [s₀] using hst)
  have hrep₀ : x = IsLocalization.mk' D y₀
      ⟨algebraMap A C s₀, Submonoid.mem_map_of_mem (algebraMap A C) s₀.2⟩ := by
    rw [hden]
    exact hrep.symm
  have hspec := mul_algebraMap_eq_of_eq_mk' S x y₀ s₀ hrep₀
  have hsD := algebraMap_algebraMap_mem_range_map (C := C) S s₀.1
  have hxNot' : x ∉ Set.range φ := by
    simpa using hxNot
  have hbx : ∀ i : Fin 2, algebraMap C D y₀ * x ^ (i.val + 1) ∈ Set.range φ := by
    intro i
    obtain ⟨u, hu⟩ : x ^ (i.val + 2) ∈ Set.range φ := by
      fin_cases i
      · simpa using hx2
      · simpa using hx3
    obtain ⟨v, hv⟩ := hsD
    refine ⟨u * v, ?_⟩
    rw [map_mul, hu, hv, ← hspec]
    ring
  obtain ⟨s₁, y, c, hrep₁, hfac, hyNot, hycond⟩ :=
    exists_numerator_not_mem_of_localization_ringHom_with_representation
      S (fun _ : Fin 2 => y₀) x y₀ s₀ hrep₀ hxNot' hbx
  have hsucc (n : ℕ) (h : y₀ * y ^ n ∈ Set.range (algebraMap A C)) :
      y ^ (n + 1) ∈ Set.range (algebraMap A C) := by
    obtain ⟨a, ha⟩ := h
    refine ⟨c * a, ?_⟩
    rw [map_mul, ha, hfac]
    ring
  exact exists_sq_cube_mem_of_subalgebra hyNot (hsucc 1 (by simpa using hycond 0))
    (hsucc 2 (by simpa using hycond 1))

/-- Two consecutive powers of an element of the localization lying in the localized subring,
with the element itself outside it, already produce the element of `B` that Tag 0CNB asks for:
pass to a square-and-cube witness in the localization and then clear denominators. -/
private lemma exists_sq_cube_mem_of_pow_mem_range
    {B : Type u} [CommRing B] (A : Subring B) (C : Subalgebra A B) (S : Submonoid A)
    (z : Localization (S.map (algebraMap A C))) {n : ℕ} (hn : 2 ≤ n)
    (hzNot : z ∉ Set.range (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map))
    (hpow : z ^ n ∈ Set.range (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map))
    (hpow' : z ^ (n + 1) ∈ Set.range (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map)) :
    ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A := by
  obtain ⟨x, hxNot, hx2, hx3⟩ :=
    Subring.exists_not_mem_and_sq_mem_and_cube_mem_of_pow_mem_of_succ_pow_mem
      (IsLocalization.map (M := S) (S := Localization S)
        (T := S.map (algebraMap A C)) (Localization (S.map (algebraMap A C)))
        (algebraMap A C) S.le_comap_map).range hzNot hn hpow hpow'
  exact exists_sq_cube_mem_of_localization_witness A C S x hxNot hx2 hx3

private lemma exists_minimal_mem_support {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hM : ¬ Subsingleton M) :
    ∃ p : PrimeSpectrum R, p ∈ Module.support R M ∧
      ∀ r, r ∈ Module.support R M → r.asIdeal ≤ p.asIdeal → r = p := by
  obtain ⟨p', hp'⟩ : (Module.support R M).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun he => hM (Module.support_eq_empty_iff.mp he)
  obtain ⟨pI, hpI, -⟩ :=
    Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hp')
  refine ⟨⟨pI, hpI.isPrime⟩, Module.mem_support_iff_of_finite.mpr hpI.1.2, fun r hr hrp => ?_⟩
  exact PrimeSpectrum.ext
    (le_antisymm hrp (hpI.2 ⟨r.2, Module.mem_support_iff_of_finite.mp hr⟩ hrp))

private lemma eq_map_of_map_le_of_comap_injective
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (hinj : Function.Injective (PrimeSpectrum.comap (algebraMap A C)))
    {p : PrimeSpectrum A} {q : PrimeSpectrum C} (hq : PrimeSpectrum.comap (algebraMap A C) q = p)
    {I : Ideal (Localization (p.asIdeal.primeCompl.map (algebraMap A C)))}
    (hI : Ideal.map (algebraMap A (Localization (p.asIdeal.primeCompl.map (algebraMap A C))))
      p.asIdeal ≤ I) (hIp : I.IsPrime) :
    I = Ideal.map (algebraMap C (Localization (p.asIdeal.primeCompl.map (algebraMap A C))))
      q.asIdeal := by
  let S := p.asIdeal.primeCompl
  let T := S.map (algebraMap A C)
  let D := Localization T
  let z : PrimeSpectrum D := ⟨I, hIp⟩
  let rC : PrimeSpectrum C := PrimeSpectrum.comap (algebraMap C D) z
  let rA : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A D) z
  have hcomp (a : A) : algebraMap A D a = algebraMap C D (algebraMap A C a) :=
    IsScalarTower.algebraMap_apply A C D a
  have hdisj : Disjoint (↑T : Set C) rC.asIdeal := by
    have hrange : rC ∈ Set.range (PrimeSpectrum.comap (algebraMap C D)) := ⟨z, rfl⟩
    rwa [PrimeSpectrum.localization_comap_range D T] at hrange
  have hrA_le : rA.asIdeal ≤ p.asIdeal := by
    intro x hx
    by_contra hxp
    refine Set.disjoint_left.mp hdisj
      (Submonoid.mem_map_of_mem _ (Ideal.mem_primeCompl_iff.mpr hxp)) ?_
    show algebraMap C D (algebraMap A C x) ∈ I
    rw [← hcomp x]
    exact hx
  have hrA : rA = p :=
    PrimeSpectrum.ext (le_antisymm hrA_le (Ideal.map_le_iff_le_comap.mp hI))
  have hrC : rC = q := by
    apply hinj
    have hc : PrimeSpectrum.comap (algebraMap A C) rC = rA := by
      ext x
      show algebraMap C D (algebraMap A C x) ∈ I ↔ algebraMap A D x ∈ I
      rw [← hcomp x]
    rw [hc, hrA, hq]
  rw [← IsLocalization.map_under T D I]
  show Ideal.map (algebraMap C D) rC.asIdeal = Ideal.map (algebraMap C D) q.asIdeal
  rw [hrC]

private lemma exists_sq_cube_mem_of_mem_radical
    {B : Type u} [CommRing B] (A : Subring B) (C : Subalgebra A B) [Module.Finite A C]
    (p : PrimeSpectrum A) (hp : p ∈ Module.support A (C ⧸ (Algebra.linearMap A C).range))
    (hmin : ∀ r, r ∈ Module.support A (C ⧸ (Algebra.linearMap A C).range) →
      r.asIdeal ≤ p.asIdeal → r = p) (y : C)
    (hrad : algebraMap C (Localization (p.asIdeal.primeCompl.map (algebraMap A C))) y ∈
      (Ideal.map (algebraMap A (Localization (p.asIdeal.primeCompl.map (algebraMap A C))))
        p.asIdeal).radical)
    (hy : LocalizedModule.mkLinearMap p.asIdeal.primeCompl (C ⧸ (Algebra.linearMap A C).range)
      (Submodule.mkQ (Algebra.linearMap A C).range y) ≠ 0) :
    ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A := by
  let M := C ⧸ (Algebra.linearMap A C).range
  have : Module.Finite A M := Module.Finite.quotient A _
  let S := p.asIdeal.primeCompl
  let R := Localization S
  let T : Submonoid C := S.map (algebraMap A C)
  let D := Localization T
  let φ : R →+* D := IsLocalization.map (M := S) (S := R) (T := T) D
    (algebraMap A C) S.le_comap_map
  have hmapAD : algebraMap A D = φ.comp (algebraMap A R) := by
    ext x
    calc
      algebraMap A D x = algebraMap C D (algebraMap A C x) :=
        IsScalarTower.algebraMap_apply A C D x
      _ = φ (algebraMap A R x) := (IsLocalization.map_eq S.le_comap_map x).symm
  let : Algebra R D := φ.toAlgebra
  let : IsScalarTower A R D := IsScalarTower.of_algebraMap_eq fun a => RingHom.congr_fun hmapAD a
  have halgφ : (algebraMap R D : R →+* D) = φ := RingHom.algebraMap_toAlgebra φ
  obtain ⟨ψ, hψmk, hkerRange₀⟩ := exists_localizedCokernel_map (A := A) (C := C) (R := R)
    (D := D) S (LocalizedModule.mkLinearMap S M)
  have hkerRange (z : D) : ψ z = 0 ↔ z ∈ Set.range φ := by
    rw [← halgφ]
    exact hkerRange₀ z
  have hrad' : algebraMap C D y ∈ (Ideal.map (algebraMap A D) p.asIdeal).radical := hrad
  rw [hmapAD, ← Ideal.map_map, IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal R,
    ← halgφ] at hrad'
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hrad'
  obtain ⟨n, hn, hzero, hzero'⟩ := exists_pow_apply_eq_zero_of_pow_mem_map_maximalIdeal
    (support_localized_at_minimal_prime p hp hmin) ψ (algebraMap C D y) hk
  exact exists_sq_cube_mem_of_pow_mem_range A C S (algebraMap C D y) hn
    (fun h => hy ((hψmk y).symm.trans ((hkerRange _).mpr h)))
    ((hkerRange _).mp hzero) ((hkerRange _).mp hzero')

private lemma exists_sq_cube_mem_of_finite_subalgebra
    {B : Type u} [CommRing B] (A : Subring B) (C : Subalgebra A B) [Module.Finite A C]
    [UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)]
    (hres : ∀ x : Spec (.of C),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap x))
    (hM : ¬ Subsingleton (C ⧸ (Algebra.linearMap A C).range)) :
    ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A := by
  have : Module.Finite A (C ⧸ (Algebra.linearMap A C).range) := Module.Finite.quotient A _
  obtain ⟨p, hp, hmin⟩ := exists_minimal_mem_support (R := A) hM
  have hhomeo := universalHomeomorphism_isHomeomorph
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)
  obtain ⟨q, hq⟩ := hhomeo.surjective p
  change PrimeSpectrum.comap (algebraMap A C) q = p at hq
  have : q.asIdeal.IsPrime := q.2
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hp
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective ((Algebra.linearMap A C).range) m
  obtain ⟨s, a, hs, hy⟩ := exists_numerator_mem_prime_of_residueFieldMap_isIso q (hres q) c
  refine exists_sq_cube_mem_of_mem_radical A C p hp hmin
    (algebraMap A C s * c - algebraMap A C a) ?_ fun h => ?_
  · rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun I hI => ?_
    rw [eq_map_of_map_le_of_comap_injective hhomeo.injective hq hI.1 hI.2]
    exact Ideal.mem_map_of_mem _ hy
  · obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl _).mp h
    have haa : Submodule.mkQ (Algebra.linearMap A C).range (algebraMap A C a) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩
    rw [map_sub, haa, sub_zero, ← Algebra.smul_def, map_smul, Submodule.mkQ_apply] at ht
    exact hm (t.1 * s) (Ideal.mem_primeCompl_iff.mp (p.asIdeal.primeCompl.mul_mem t.2
      (Ideal.mem_primeCompl_iff.mpr (hq ▸ hs)))) ((mul_smul t.1 s _).trans ht)

/-- A proper subring extension which is a universal homeomorphism on spectra
and induces isomorphisms on residue fields contains an element outside the
subring whose square and cube are in the subring. -/
@[stacks 0CNB]
theorem exists_not_mem_and_sq_mem_and_cube_mem_of_universalHomeomorphism_of_residueFieldMap_isIso
    {B : Type u} [CommRing B] (A : Subring B)
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom A.subtype).op)]
    (hres : ∀ x : Spec (CommRingCat.of B),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom A.subtype).op).residueFieldMap x))
    (hA : A ≠ ⊤) :
    ∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A := by
  have : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
    show UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom A.subtype).op)
    infer_instance
  have : Algebra.IsIntegral A B := universalHomeomorphism_algebra_isIntegral
  obtain ⟨b, hb⟩ : ∃ b : B, b ∉ A := by
    by_contra! hc
    exact hA (eq_top_iff.mpr fun x _ => hc x)
  let C : Subalgebra A B := Algebra.adjoin A ({b} : Set B)
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.of_injective C.val Subtype.val_injective
  have : Algebra.FiniteType A C :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton b)
  have : Module.Finite A C := Algebra.IsIntegral.finite
  have := universalHomeomorphism_specMap_subalgebra C
  let bC : C := ⟨b, Algebra.subset_adjoin (Set.mem_singleton b)⟩
  have hbC : bC ∉ (Algebra.linearMap A C).range := by
    rintro ⟨a, ha⟩
    have hv : A.subtype a = b := congrArg C.val ha
    exact hb (hv ▸ a.property)
  exact exists_sq_cube_mem_of_finite_subalgebra A C
    (isIso_residueFieldMap_specMap_subalgebra hres C) fun hs =>
      hbC ((Submodule.Quotient.mk_eq_zero _).mp (@Subsingleton.elim _ hs _ _))

end AlgebraicGeometry

end
