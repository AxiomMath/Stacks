module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.DedekindDomain.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# A flat surjective family that is not an fpqc covering

Let `k` be a field and let `φ : ∐_{x ∈ 𝐀¹_k} Spec 𝒪_{𝐀¹_k, x} ⟶ 𝐀¹_k` be the morphism whose
component at a point `x` is the canonical map `Spec 𝒪_{𝐀¹_k, x} ⟶ 𝐀¹_k`. It is flat, because
each component is, and surjective, because `x` lies in the image of its own component. The
one-member family `{φ}` is nevertheless not an fpqc covering: a compact open of a coproduct of
schemes is covered by finitely many of its components, so the image of such an open under `φ`
is contained in finitely many sets `{y | y ⤳ x}`. On the affine line each of those sets is
finite, consisting of `x` and the generic point, because a nonzero prime of `k[T]` is maximal;
and the affine line has infinitely many points. So no compact open of the coproduct surjects
onto `𝐀¹_k`, which is what being an fpqc covering would demand of the affine open `𝐀¹_k`.

## Main results

* `AlgebraicGeometry.flat_sigmaFromSpecStalk` and
  `AlgebraicGeometry.surjective_sigmaFromSpecStalk` say that `φ` is flat and surjective, for an
  arbitrary scheme in place of the affine line.
* `AlgebraicGeometry.flat_and_surjective_sigmaFromSpecStalk_polynomial` records that conjunction
  over the affine line itself, which is the object the source names.
* `AlgebraicGeometry.singleton_sigmaFromSpecStalk_notMem_fpqcPrecoverage` says that the
  one-member family `{φ}` is not an fpqc covering of the affine line.
* `AlgebraicGeometry.not_quasiCompact_sigmaFromSpecStalk_polynomial` says that `φ` is not
  quasi-compact over the affine line.

## Implementation notes

The affine line is spelled `Spec k[T]`, as in the source. The morphism `φ` is
`AlgebraicGeometry.sigmaFromSpecStalk`, which already exists for an arbitrary scheme; its
coproduct is indexed by the points of the scheme itself, a type in the same universe.

## References

* [Stacks Project, Tag 03NY](https://stacks.math.columbia.edu/tag/03NY)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The component of `∐_{x ∈ X} Spec 𝒪_{X, x} ⟶ X` at `x` is the canonical morphism
`Spec 𝒪_{X, x} ⟶ X`. -/
@[simp]
lemma sigmaι_comp_sigmaFromSpecStalk (X : Scheme.{u}) (x : X) :
    Sigma.ι (fun x : X ↦ Spec (X.presheaf.stalk x)) x ≫ sigmaFromSpecStalk X =
      X.fromSpecStalk x :=
  Sigma.ι_desc _ _

/-- `∐_{x ∈ X} Spec 𝒪_{X, x} ⟶ X` is flat, since each `Spec 𝒪_{X, x} ⟶ X` is. -/
@[stacks 03NY "local_spectra_counterexample"]
instance flat_sigmaFromSpecStalk (X : Scheme.{u}) : Flat (sigmaFromSpecStalk X) :=
  have (x : X) : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  inferInstanceAs (Flat (Sigma.desc _))

/-- `∐_{x ∈ X} Spec 𝒪_{X, x} ⟶ X` is surjective, since `x` is in the image of the component
at `x`. -/
@[stacks 03NY "local_spectra_counterexample"]
instance surjective_sigmaFromSpecStalk (X : Scheme.{u}) : Surjective (sigmaFromSpecStalk X) := by
  rw [surjective_iff]
  intro x
  obtain ⟨y, hy⟩ : x ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  refine ⟨Sigma.ι (fun x : X ↦ Spec (X.presheaf.stalk x)) x y, ?_⟩
  rw [← Scheme.Hom.comp_apply, sigmaι_comp_sigmaFromSpecStalk]
  exact hy

/-- A compact subset of a coproduct of schemes meets only finitely many of the components. -/
lemma exists_finite_subset_range_sigmaι {σ : Type u} (g : σ → Scheme.{u})
    {V : Set ↥(∐ g)} (hV : IsCompact V) :
    ∃ s : Set σ, s.Finite ∧ V ⊆ ⋃ i ∈ s, Set.range (Sigma.ι g i).base := by
  have hcover : ∀ z : ↥(∐ g), z ∈ ⋃ i, Set.range (Sigma.ι g i).base := by
    intro z
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk g).surjective z
    exact Set.mem_iUnion.2 ⟨i, y, by simp⟩
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun i : σ ↦ Set.range (Sigma.ι g i).base)
    (fun i ↦ (Sigma.ι g i).isOpenEmbedding.isOpen_range) fun z _ ↦ hcover z
  exact ⟨t, t.finite_toSet, by simpa using ht⟩

section AffineLine

variable (k : Type u) [Field k]

/-- **Stacks Project, Tag 03NY.** The morphism `φ : ∐_{x ∈ 𝐀¹_k} Spec 𝒪_{𝐀¹_k, x} ⟶ 𝐀¹_k`,
where `k` is a field, is flat and surjective. This is the positive half of the example; the
morphism is nevertheless not quasi-compact and `{φ}` is not an fpqc covering. -/
@[stacks 03NY "local_spectra_counterexample"]
theorem flat_and_surjective_sigmaFromSpecStalk_polynomial :
    Flat (sigmaFromSpecStalk (Spec (.of (Polynomial k)))) ∧
      Surjective (sigmaFromSpecStalk (Spec (.of (Polynomial k)))) :=
  ⟨inferInstance, inferInstance⟩

/-- Every maximal ideal of a polynomial ring over a field contains a polynomial of positive
degree. -/
private theorem exists_mem_natDegree_pos_of_isMaximal {k : Type u} [Field k]
    {m : Ideal (Polynomial k)} (hm : m.IsMaximal) : ∃ f ∈ m, 0 < f.natDegree := by
  have hspan : (Ideal.span {(Polynomial.X : Polynomial k)}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    simp [Polynomial.isUnit_iff_degree_eq_zero]
  have hmbot : m ≠ ⊥ := by
    intro h
    have hXmem : (Polynomial.X : Polynomial k) ∈ m := by
      rw [hm.eq_of_le hspan (h ▸ bot_le)]
      exact Ideal.mem_span_singleton_self _
    rw [h, Ideal.mem_bot] at hXmem
    exact Polynomial.X_ne_zero hXmem
  obtain ⟨f, hfm, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  refine ⟨f, hfm, Polynomial.natDegree_pos_iff_degree_pos.2 ?_⟩
  have hunit : ¬ IsUnit f := fun h ↦ hm.ne_top (m.eq_top_of_isUnit_mem hfm h)
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hunit
  exact lt_of_le_of_ne (Polynomial.zero_le_degree_iff.2 hf0) (Ne.symm hunit)

/-- The spectrum of a polynomial ring over a field has infinitely many points: were there
finitely many, hence finitely many maximal ideals, an element of positive degree chosen in each
would have a product `g` lying in every maximal ideal, while `1 + g` has positive degree and so
also lies in one of them. -/
@[ega "IV 5.5.3" "special case"]
private theorem infinite_primeSpectrum_polynomial :
    Infinite (PrimeSpectrum (Polynomial k)) := by
  classical
  rw [← not_finite_iff_infinite]
  intro hfin
  have : Finite {m : Ideal (Polynomial k) // m.IsMaximal} :=
    .of_injective (fun m ↦ (⟨m.1, m.2.isPrime⟩ : PrimeSpectrum (Polynomial k)))
      fun _ _ h ↦ Subtype.ext (congrArg PrimeSpectrum.asIdeal h)
  let _ : Fintype {m : Ideal (Polynomial k) // m.IsMaximal} := Fintype.ofFinite _
  choose F hFmem hFdeg using fun m : {m : Ideal (Polynomial k) // m.IsMaximal} ↦
    exists_mem_natDegree_pos_of_isMaximal m.2
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal (Polynomial k)
  have hgpos : 0 < (∏ m, F m).natDegree := by
    rw [Polynomial.natDegree_prod _ _ fun m _ ↦
      Polynomial.ne_zero_of_natDegree_gt (hFdeg m)]
    exact Finset.sum_pos' (fun m _ ↦ Nat.zero_le _)
      ⟨⟨m₀, hm₀⟩, Finset.mem_univ _, hFdeg ⟨m₀, hm₀⟩⟩
  have hgdeg : 0 < (∏ m, F m).degree := Polynomial.natDegree_pos_iff_degree_pos.1 hgpos
  have hunit : ¬ IsUnit (1 + ∏ m, F m) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      Polynomial.degree_add_eq_right_of_degree_lt (by simpa using hgdeg)]
    exact ne_of_gt hgdeg
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 + ∏ m, F m})
    fun h ↦ hunit (Ideal.span_singleton_eq_top.1 h)
  have h2 : (∏ m, F m) ∈ m := by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem F (Finset.mem_univ ⟨m, hm⟩)
    rw [hc]
    exact Ideal.mul_mem_right _ _ (hFmem ⟨m, hm⟩)
  exact hm.ne_top (m.eq_top_of_isUnit_mem
    (by simpa using m.sub_mem (hle (Ideal.mem_span_singleton_self _)) h2) isUnit_one)

/-- On the spectrum of a polynomial ring over a field, only finitely many points specialize to
a given point: such a point is either the generic point or the point itself, because a nonzero
prime of `k[T]` is maximal. -/
private theorem finite_specializes_polynomial (x : PrimeSpectrum (Polynomial k)) :
    {y : PrimeSpectrum (Polynomial k) | y ⤳ x}.Finite := by
  refine Set.Finite.subset (Set.Finite.union (Set.Subsingleton.finite ?_)
    (Set.finite_singleton x)) (s := {y : PrimeSpectrum (Polynomial k) | y.asIdeal = ⊥} ∪ {x}) ?_
  · exact fun a ha b hb ↦ PrimeSpectrum.ext (ha.trans hb.symm)
  · intro y hy
    rcases eq_or_ne y.asIdeal ⊥ with h | h
    · exact Or.inl h
    · refine Or.inr (PrimeSpectrum.ext ?_)
      exact (Ideal.IsPrime.isMaximal y.isPrime h).eq_of_le x.isPrime.ne_top
        ((PrimeSpectrum.asIdeal_le_asIdeal y x).2 ((PrimeSpectrum.le_iff_specializes y x).2 hy))

/-- **Stacks Project, Tag 03NY.** Over the affine line, the family consisting of the single
morphism `∐_{x ∈ 𝐀¹_k} Spec 𝒪_{𝐀¹_k, x} ⟶ 𝐀¹_k` is not an fpqc covering, although that
morphism is flat and surjective. -/
@[stacks 03NY "local_spectra_counterexample"]
theorem singleton_sigmaFromSpecStalk_notMem_fpqcPrecoverage :
    Presieve.singleton (sigmaFromSpecStalk (Spec (.of (Polynomial k)))) ∉
      Scheme.fpqcPrecoverage (Spec (.of (Polynomial k))) := by
  intro hmem
  have hqc : QuasiCompactCover
      (PreZeroHypercover.singleton.{0} (sigmaFromSpecStalk (Spec (.of (Polynomial k))))) := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff, PreZeroHypercover.presieve₀_singleton]
    exact hmem.1
  have hcov := IsAffineOpen.isCompactOpenCovered
    (PreZeroHypercover.singleton.{0} (sigmaFromSpecStalk (Spec (.of (Polynomial k)))))
    (isAffineOpen_top (Spec (.of (Polynomial k))))
  rw [IsCompactOpenCovered.iff_of_unique] at hcov
  obtain ⟨V, hVc, hVeq⟩ := hcov
  simp only [Opens.coe_top] at hVeq
  obtain ⟨s, hsfin, hsub⟩ := exists_finite_subset_range_sigmaι _ hVc
  have hfin : (Set.univ : Set ↥(Spec (CommRingCat.of (Polynomial k)))).Finite := by
    refine Set.Finite.subset (hsfin.biUnion fun x _ ↦ finite_specializes_polynomial k x) ?_
    rw [← hVeq]
    refine Set.image_subset_iff.2 fun z hz ↦ ?_
    obtain ⟨x, hxs, w, rfl⟩ := Set.mem_iUnion₂.1 (hsub hz)
    refine Set.mem_iUnion₂.2 ⟨x, hxs, ?_⟩
    show (sigmaFromSpecStalk (Spec (CommRingCat.of (Polynomial k))))
      (Sigma.ι (fun y : ↥(Spec (CommRingCat.of (Polynomial k))) ↦
        Spec ((Spec (CommRingCat.of (Polynomial k))).presheaf.stalk y)) x w) ⤳ x
    rw [← Scheme.Hom.comp_apply, sigmaι_comp_sigmaFromSpecStalk]
    exact (Scheme.range_fromSpecStalk (x := x)).le ⟨w, rfl⟩
  exact Set.infinite_univ_iff.2 (infinite_primeSpectrum_polynomial k) hfin

/-- **Stacks Project, Tag 03NY.** The morphism `∐_{x ∈ 𝐀¹_k} Spec 𝒪_{𝐀¹_k, x} ⟶ 𝐀¹_k` is not
quasi-compact: it is flat and surjective, so a quasi-compact such morphism would give an fpqc
covering. -/
@[stacks 03NY "local_spectra_counterexample"]
theorem not_quasiCompact_sigmaFromSpecStalk_polynomial :
    ¬ QuasiCompact (sigmaFromSpecStalk (Spec (.of (Polynomial k)))) := fun _ ↦
  singleton_sigmaFromSpecStalk_notMem_fpqcPrecoverage k
    (Scheme.Hom.singleton_mem_fpqcPrecoverage _)

end AffineLine

end AlgebraicGeometry
