module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The formal glueing pair of finitely many maximal ideals

Let `A` be a commutative ring and let `m i`, for `i` in a finite index type, be pairwise distinct
maximal ideals of `A`.  Write `A' = ∏ i, A_{m i}` for the product of the localizations and
`I = ⨅ i, m i` for their intersection.  This file proves that `A → A'` together with `I` is a
*formal glueing pair*: the map is flat, and the induced map `A / I → A' / I A'` is bijective.
Both are identifications of the residue algebra `∏ i, κ(m i)` obtained from the Chinese remainder
theorem, and together with the finite generation of `I` over a Noetherian `A` they are exactly the
hypotheses under which the formal glueing results of Stacks 05ER and Stacks 0ALK apply to this
pair.

The file also records the two elementary facts that make the identification work: each `m i` is
comaximal with the others, so that some element lies in every `m j` with `j ≠ i` and outside
`m i`; and consequently `I A_{m i}` is already the maximal ideal of `A_{m i}`, so that no
information is lost by replacing `m i` with the smaller ideal `I`.

## Main results

* `Stacks.RingHomGluing.isCoprime_of_pairwise_ne` — pairwise distinct maximal ideals are
  pairwise comaximal.
* `Stacks.RingHomGluing.exists_mem_forall_ne_notMem` — prime avoidance for the family: an element
  of every `m j` with `j ≠ i` which avoids `m i`.
* `Stacks.RingHomGluing.map_iInf_eq_maximalIdeal` — `(⨅ j, m j) A_{m i}` is the maximal ideal of
  the localization `A_{m i}`.
* `Stacks.RingHomGluing.map_iInf_eq_piMaximalIdeal` — `(⨅ j, m j) A'` consists of the elements of
  `A'` all of whose components are non-units.
* `Stacks.RingHomGluing.flat_pi_localizationAtPrime` — `A → A'` is flat.
* `Stacks.RingHomGluing.quotientMap_bijective` — `A / (⨅ j, m j) → A' / (⨅ j, m j) A'` is
  bijective.
* `Stacks.RingHomGluing.isLocalizationMap_of_isLocalizedModule` — a ring map which localizes an
  algebra as a module at a submonoid of the base exhibits its target as a localization of its
  source at the image submonoid.

## References

* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
* [Stacks Project, Tag 0ALK](https://stacks.math.columbia.edu/tag/0ALK)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.RingHomGluing

variable {A : Type u} [CommRing A] {ι : Type w} [Finite ι] (m : ι → Ideal A)
  [∀ i, (m i).IsMaximal]

/-! ### Comaximality and prime avoidance -/

omit [Finite ι] in
/-- Pairwise distinct maximal ideals are pairwise comaximal. -/
theorem isCoprime_of_pairwise_ne (hm : Pairwise fun i j ↦ m i ≠ m j) :
    Pairwise (Function.onFun IsCoprime m) := by
  have hmax : ∀ i, (m i).IsMaximal := fun i ↦ inferInstance
  intro i j hij
  rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
  by_contra h
  have h1 : m i = m i ⊔ m j := (hmax i).eq_of_le h le_sup_left
  have h2 : m j ≤ m i := h1 ▸ le_sup_right
  exact hm hij ((hmax j).eq_of_le (hmax i).ne_top h2).symm

/-- Prime avoidance for a finite family of pairwise distinct maximal ideals: for every index `i`
there is an element lying in all the other members of the family and outside `m i`. -/
theorem exists_mem_forall_ne_notMem (hm : Pairwise fun i j ↦ m i ≠ m j) (i : ι) :
    ∃ u : A, (∀ j, j ≠ i → u ∈ m j) ∧ u ∉ m i := by
  classical
  have hmax : ∀ i, (m i).IsMaximal := fun i ↦ inferInstance
  have : Fintype ι := Fintype.ofFinite ι
  have hone : (1 : A) ∉ m i := fun h ↦
    (hmax i).ne_top (Ideal.eq_top_iff_one _ |>.mpr h)
  have hex : ∀ j : ι, ∃ x : A, (j ≠ i → x ∈ m j) ∧ x ∉ m i := by
    intro j
    by_cases hj : j = i
    · exact ⟨1, fun h ↦ absurd hj h, hone⟩
    · have hnle : ¬ m j ≤ m i := fun hle ↦
        hm hj ((hmax j).eq_of_le (hmax i).ne_top hle)
      obtain ⟨x, hx, hx'⟩ := Set.not_subset.mp hnle
      exact ⟨x, fun _ ↦ hx, hx'⟩
  choose x hx hx' using hex
  refine ⟨∏ j ∈ Finset.univ.erase i, x j, fun j hj ↦ ?_, fun hmem ↦ ?_⟩
  · rw [← Finset.mul_prod_erase _ x (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
    exact Ideal.mul_mem_right _ _ (hx j hj)
  · obtain ⟨j, -, hj'⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hx' j hj'

/-- In a localization at a prime, an ideal containing `z * s` with `s` outside the prime contains
`z`. -/
private theorem mem_of_mul_algebraMap_mem {p : Ideal A} [p.IsPrime]
    (J : Ideal (Localization.AtPrime p)) {s : A} (hs : s ∉ p) {z : Localization.AtPrime p}
    (h : z * algebraMap A _ s ∈ J) : z ∈ J := by
  obtain ⟨c, hc⟩ := ((IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime p) p s).mpr hs).exists_right_inv
  simpa [mul_assoc, hc] using J.mul_mem_right c h

/-! ### The intersection generates the maximal ideal of each localization -/

/-- The intersection `⨅ j, m j` generates the maximal ideal of the localization `A_{m i}`: the
other members of the family become invertible there, so passing from `m i` to the smaller ideal
`⨅ j, m j` loses nothing. -/
theorem map_iInf_eq_maximalIdeal (hm : Pairwise fun i j ↦ m i ≠ m j) (i : ι) :
    (⨅ j, m j).map (algebraMap A (Localization.AtPrime (m i))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (m i)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  refine le_antisymm (Ideal.map_mono (iInf_le _ _)) ?_
  rw [Ideal.map_le_iff_le_comap]
  intro w hw
  obtain ⟨u, hu, hu'⟩ := exists_mem_forall_ne_notMem m hm i
  have hmul : u * w ∈ ⨅ j, m j := by
    refine Ideal.mem_iInf.mpr fun j ↦ ?_
    by_cases hj : j = i
    · exact hj ▸ Ideal.mul_mem_left _ _ hw
    · exact Ideal.mul_mem_right _ _ (hu j hj)
  rw [Ideal.mem_comap]
  refine mem_of_mul_algebraMap_mem _ hu' ?_
  rw [← map_mul, mul_comm]
  exact Ideal.mem_map_of_mem _ hmul

/-! ### Flatness of the product of the localizations -/

/-- The product of the localizations of `A` at finitely many primes is a flat `A`-algebra. -/
theorem flat_pi_localizationAtPrime :
    Module.Flat A (∀ i, Localization.AtPrime (m i)) := by
  have : Fintype ι := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype A ι fun i ↦ Localization.AtPrime (m i)).symm

/-! ### The extended ideal and the Chinese remainder identification -/

/-- The ideal of `∏ i, A_{m i}` consisting of the tuples all of whose components are non-units,
that is, lie in the maximal ideal of their factor. -/
def piMaximalIdeal : Ideal (∀ i, Localization.AtPrime (m i)) where
  carrier := {x | ∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (m i))}
  add_mem' hx hy i := Ideal.add_mem _ (hx i) (hy i)
  zero_mem' _ := Ideal.zero_mem _
  smul_mem' _ _ hx i := Ideal.mul_mem_left _ _ (hx i)

omit [Finite ι] in
/-- A tuple lies in `piMaximalIdeal m` exactly when each of its components lies in the maximal
ideal of its factor. -/
@[simp] theorem mem_piMaximalIdeal_iff {x : ∀ i, Localization.AtPrime (m i)} :
    x ∈ piMaximalIdeal m ↔
      ∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (m i)) :=
  Iff.rfl

/-- The ideal generated by `⨅ j, m j` in the product of the localizations is the ideal of tuples
with all components non-units.  In particular the extended ideal is a product of maximal ideals,
one in each factor. -/
theorem map_iInf_eq_piMaximalIdeal (hm : Pairwise fun i j ↦ m i ≠ m j) :
    (⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))) = piMaximalIdeal m := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rw [Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ Ideal.mem_comap.mpr fun i ↦
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (m i) a).mpr (Ideal.mem_iInf.mp ha i)
  · have key : ∀ (i : ι) (z : Localization.AtPrime (m i)),
        z ∈ (⨅ j, m j).map (algebraMap A (Localization.AtPrime (m i))) →
        Pi.single i z ∈ (⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))) := by
      intro i z hz
      refine Submodule.span_induction
        (p := fun z _ ↦ Pi.single i z ∈
          (⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))))
        ?_ ?_ ?_ ?_ hz
      · rintro z ⟨a, ha, rfl⟩
        have hsingle : Pi.single i (algebraMap A (Localization.AtPrime (m i)) a)
            = Pi.single (M := fun i ↦ Localization.AtPrime (m i)) i 1
              * algebraMap A (∀ i, Localization.AtPrime (m i)) a := by
          ext j
          obtain rfl | h := eq_or_ne j i
          · simp
          · simp [Pi.single_eq_of_ne h]
        rw [hsingle]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)
      · simp
      · intro z w _ _ ihz ihw
        rw [Pi.single_add]
        exact Ideal.add_mem _ ihz ihw
      · intro c z _ ih
        have hsmul : Pi.single (M := fun i ↦ Localization.AtPrime (m i)) i (c • z)
            = Pi.single i c * Pi.single i z := by
          rw [smul_eq_mul, Pi.single_mul]
        rw [hsmul]
        exact Ideal.mul_mem_left _ _ ih
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ ↦ key i (x i) ?_
    rw [map_iInf_eq_maximalIdeal m hm i]
    exact hx i

/-- Every element of the product of the localizations is congruent, modulo the ideal generated by
`⨅ j, m j`, to an element of `A`.  This is the Chinese remainder theorem for the family `m`:
the residue of the tuple is prescribed in each residue field `κ(m i)` separately. -/
theorem exists_sub_mem_map_iInf (hm : Pairwise fun i j ↦ m i ≠ m j)
    (x : ∀ i, Localization.AtPrime (m i)) :
    ∃ a : A, x - algebraMap A (∀ i, Localization.AtPrime (m i)) a ∈
      (⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))) := by
  classical
  have hsurj : ∀ i, ∃ p : A × ((m i).primeCompl),
      IsLocalization.mk' (Localization.AtPrime (m i)) p.1 p.2 = x i :=
    fun i ↦ IsLocalization.mk'_surjective _ (x i)
  choose p hp using hsurj
  have hmax : ∀ i, (m i).IsMaximal := fun i ↦ inferInstance
  have hinv : ∀ i, ∃ t : A, ∃ y ∈ m i, t * ((p i).2 : A) + y = 1 :=
    fun i ↦ (hmax i).exists_inv (p i).2.property
  choose t y hy ht using hinv
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal (isCoprime_of_pairwise_ne m hm)
    fun i ↦ (p i).1 * t i
  refine ⟨a, ?_⟩
  rw [map_iInf_eq_piMaximalIdeal m hm]
  intro i
  have hnum : (p i).1 - a * ((p i).2 : A) ∈ m i := by
    have hyi : y i = 1 - t i * ((p i).2 : A) := by rw [← ht i]; ring
    have hrw : (p i).1 - a * ((p i).2 : A)
        = (p i).1 * y i - (a - (p i).1 * t i) * ((p i).2 : A) := by
      rw [hyi]; ring
    rw [hrw]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hy i)) (Ideal.mul_mem_right _ _ (ha i))
  have hmuls : (x - algebraMap A (∀ i, Localization.AtPrime (m i)) a) i
      * algebraMap A (Localization.AtPrime (m i)) ((p i).2 : A)
      = algebraMap A (Localization.AtPrime (m i)) ((p i).1 - a * ((p i).2 : A)) := by
    have hspec : x i * algebraMap A (Localization.AtPrime (m i)) ((p i).2 : A)
        = algebraMap A (Localization.AtPrime (m i)) (p i).1 := by
      rw [← hp i]
      exact IsLocalization.mk'_spec _ _ _
    simp only [Pi.sub_apply, sub_mul, map_sub, map_mul, hspec]
    rfl
  refine mem_of_mul_algebraMap_mem _ (p i).2.property ?_
  rw [hmuls]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (m i) _).mpr hnum

/-- **The formal glueing pair of a finite family of maximal ideals.** The map from `A` to the
product of the localizations at finitely many pairwise distinct maximal ideals induces a
bijection `A / (⨅ j, m j) → (∏ i, A_{m i}) / (⨅ j, m j) (∏ i, A_{m i})`; both sides are the
product of the residue fields `κ(m i)`. -/
theorem quotientMap_bijective (hm : Pairwise fun i j ↦ m i ≠ m j) :
    Function.Bijective (Ideal.quotientMap
      ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))))
      (algebraMap A (∀ i, Localization.AtPrime (m i))) Ideal.le_comap_map) := by
  constructor
  · refine Ideal.quotientMap_injective' fun a ha ↦ ?_
    rw [Ideal.mem_comap, map_iInf_eq_piMaximalIdeal m hm] at ha
    exact Ideal.mem_iInf.mpr fun i ↦
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (m i) a).mp (ha i)
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := exists_sub_mem_map_iInf m hm x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    simpa using neg_mem ha

/-- Finite generation, flatness and the Chinese remainder identification together: the three
hypotheses under which the formal glueing results of Stacks 05ER and Stacks 0ALK apply to the
pair `A → ∏ i, A_{m i}` and the ideal `⨅ j, m j`. -/
theorem fg_flat_and_quotientMap_bijective [IsNoetherianRing A]
    (hm : Pairwise fun i j ↦ m i ≠ m j) :
    (⨅ j, m j).FG ∧ Module.Flat A (∀ i, Localization.AtPrime (m i)) ∧
      Function.Bijective (Ideal.quotientMap
        ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i))))
        (algebraMap A (∀ i, Localization.AtPrime (m i))) Ideal.le_comap_map) :=
  ⟨IsNoetherian.noetherian _, flat_pi_localizationAtPrime m, quotientMap_bijective m hm⟩

/-! ### Localization of algebras as a localization of rings -/

/-- A ring map between `A`-algebras which realizes its target as the localization of its source
as a module, at a submonoid `S` of the base ring `A`, realizes it as a localization of rings at
the image of `S`.  This is the form in which the localization clause of Stacks 0EAE is stated:
a ring map `g : B →+* C` with `Submonoid.IsLocalizationMap (S.map (algebraMap A B)) g`. -/
theorem isLocalizationMap_of_isLocalizedModule {B : Type v} {C : Type*} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (S : Submonoid A)
    [IsLocalizedModule S (IsScalarTower.toAlgHom A B C).toLinearMap] :
    (S.map (algebraMap A B)).IsLocalizationMap (algebraMap B C) :=
  (isLocalization_iff_isLocalizationMap _ _).mp (isLocalizedModule_iff_isLocalization.mp ‹_›)

end Stacks.RingHomGluing

end
