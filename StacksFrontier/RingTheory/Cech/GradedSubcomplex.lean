module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.RingTheory.Cech.GradedComplex

/-!
# The degree-`e` subcomplex of the extended Čech complex of homogeneous elements

Let `S = ⨁_{i ≥ 0} 𝒜 i` be a graded ring, `M = ⨁_{j ∈ ℤ} 𝒨 j` a `ℤ`-graded `S`-module and
`f₀, …, f_{r-1}` homogeneous elements of `S`. Each term of the extended alternating Čech complex
`Cech.cechComplex f M` is a direct sum of localizations of `M` at homogeneous elements, hence
`ℤ`-graded (`Stacks.GradedLocalization.gradedPiece`), and the differential preserves those degrees
(`Cech.mem_gradedPiece_cechι`, in `StacksFrontier.RingTheory.Cech.GradedComplex`).

This file builds the degree-`e` subcomplex itself and the decomposition of the Čech complex as the
direct sum of those subcomplexes:

* `Cech.gradedCechTerm` is the degree-`e` part of the degree-`p` term — the elements all of whose
  components are homogeneous of degree `e`;
* `Cech.cechD_mem_gradedCechTerm` says the differential carries it into the degree-`e` part of the
  next term, so `Cech.gradedCechComplex` is a complex;
* `Cech.exists_sum_mem_gradedCechTerm` and `Cech.eq_zero_of_sum_mem_gradedCechTerm_eq_zero` are
  the two halves of the decomposition `C^p = ⨁_{e ∈ ℤ} C^p(e)`, packaged as
  `Cech.isInternal_gradedCechTerm`.

The payoff is `Cech.exactAt_gradedCechComplex_of_exactAt`: because each term decomposes and the
differential respects the decomposition, **exactness of the whole Čech complex in a degree implies
exactness of every degree-`e` subcomplex in that degree**. Applied to the variables of a
polynomial ring, where the Čech complex has cohomology only in the top degree
(`MvPolynomial.cechComplex_homology_X_isZero`), this gives
`Cech.isZero_homology_gradedCechComplex` — the vanishing of the degree-`e` cohomology in every
degree but the top one, **for every `e` at once and with no computation of the graded pieces**. For
`𝒜 = R[T₀, …, Tₙ]` and the variables that is `H^q(ℙⁿ_R, 𝒪(e)) = 0` for `0 < q < n`
([Stacks, Tag 01XT]); the degrees `q = 0` and `q = n` are genuinely graded and do not follow this
way.

## Main definitions

* `Cech.gradedCechTerm` — the degree-`e` part of the degree-`p` term of the Čech complex.
* `Cech.gradedCechD` — the differential restricted to it.
* `Cech.gradedCechComplex` — the degree-`e` subcomplex, as a cochain complex of abelian groups.

## Main results

* `Cech.eq_zero_of_sum_mem_gradedCechTerm_eq_zero` — **independence**: a vanishing finite sum of
  homogeneous elements of distinct degrees has vanishing summands.
* `Cech.exists_sum_mem_gradedCechTerm` — **spanning**: every element of a term is a finite sum of
  homogeneous ones.
* `Cech.isInternal_gradedCechTerm` — hence each term **is** the direct sum of its degree-`e`
  parts.
* `Cech.exists_eq_cechD_mem_gradedCechTerm` — **the graded lift of a coboundary**: a homogeneous
  cocycle that is a coboundary is the coboundary of a homogeneous element of the same degree.
* `Cech.exactAt_gradedCechComplex_of_exactAt` and `Cech.isZero_homology_gradedCechComplex` — the
  degree-`e` subcomplex is exact wherever the Čech complex is.

## Implementation notes

**Abelian groups, not `S`-modules.** A graded piece is not an `S`-submodule — multiplication by a
homogeneous element of positive degree shifts the degree — so the degree-`e` subcomplex cannot be
a complex of `S`-modules, and `Cech.gradedCechComplex` is a complex in `ModuleCat ℤ`, i.e. of
abelian groups. Nothing is lost: the vanishing of a cohomology object is the vanishing of its
underlying group, and the implication in
`Cech.exactAt_gradedCechComplex_of_exactAt` is proved through the elementary
characterisation `CategoryTheory.ShortComplex.moduleCat_exact_iff` of exactness on both sides, so
no comparison of homology across a forgetful functor is needed.

**No projection operator is named.** The graded lift of a coboundary is obtained from the two
halves of the decomposition directly: write the preimage as a finite sum of homogeneous elements,
push it through the differential, and use independence in the next term to discard every degree
but `e`. Naming the degree-`e` projection would require carrying a `DirectSum.Decomposition`
instance that depends on a proof of homogeneity of the denominator, which is exactly what
`Stacks.GradedLocalization.isInternal_gradedPiece` lets us avoid.

## What is not done

No `@[stacks]` attribute is attached. The statements here are about the *algebraic* extended Čech
complex; identifying it with the Čech complex of the standard cover of `ℙⁿ_R` for `𝒪(e)` — which
is [Stacks, Tag 01M6] on each term together with the comparison of Čech and derived cohomology,
[Stacks, Tag 01XD] with [Stacks, Tags 01FJ and 01FM] — is not performed here, so the vanishing
`H^q(ℙⁿ_R, 𝒪(e)) = 0` referred to above is the content this transports, not a statement proved in
this file.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
-/

@[expose] public section

universe u v w t

open CategoryTheory Finset

-- The grading action of a non-negative ring degree on an integer module degree, taken from
-- `StacksFrontier.RingTheory.HomogeneousLocalization.GradedLocalizedModule` rather than declared
-- again here; `StacksFrontier.RingTheory.Cech.GradedComplex`, whose graded statements this file
-- applies, activates the same one.
attribute [local instance] instVAddNatIntGradedLocalizedModule

namespace Cech

section Defs

variable {R : Type u} [CommRing R] {r : ℕ} {σ : Type w} {τ : Type t}
  [SetLike σ R] (𝒜 : ℕ → σ)
  {M : Type v} [AddCommGroup M] [Module R M]
  [SetLike τ M] (𝒨 : ℤ → τ)
  (f : Fin r → R)

/-! ### The degree-`e` part of a term -/

/-- The degree-`e` part of the degree-`p` term of the extended Čech complex: the elements each of
whose components, a fraction in the localization of `M` at `∏_{i ∈ s} f i`, is homogeneous of
degree `e`. -/
def gradedCechTerm (e : ℤ) (p : ℕ) : AddSubgroup (cechTerm f M p) where
  carrier := {z | ∀ s : {s : Finset (Fin r) // s.card = p},
    z s ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 (∏ i ∈ s.1, f i) e}
  zero_mem' := fun s => by
    rw [DFinsupp.zero_apply]
    exact zero_mem _
  add_mem' := fun {_ _} ha hb s => by
    rw [DFinsupp.add_apply]
    exact add_mem (ha s) (hb s)
  neg_mem' := fun {_} ha s => by
    rw [DFinsupp.neg_apply]
    exact neg_mem (ha s)

variable {𝒜 𝒨 f}

/-- Membership in the degree-`e` part is homogeneity of every component. -/
theorem mem_gradedCechTerm {e : ℤ} {p : ℕ} {z : cechTerm f M p} :
    z ∈ gradedCechTerm 𝒜 𝒨 f e p ↔ ∀ s : {s : Finset (Fin r) // s.card = p},
      z s ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 (∏ i ∈ s.1, f i) e :=
  Iff.rfl

/-- A homogeneous fraction, placed in a single summand, is homogeneous of the same degree. -/
theorem lof_mem_gradedCechTerm {e : ℤ} {p : ℕ} (s : {s : Finset (Fin r) // s.card = p})
    {x : cechMod f M s.1}
    (hx : x ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 (∏ i ∈ s.1, f i) e) :
    DirectSum.lof R {t : Finset (Fin r) // t.card = p} (fun t => cechMod f M t.1) s x ∈
      gradedCechTerm 𝒜 𝒨 f e p := by
  classical
  refine mem_gradedCechTerm.2 fun s' => ?_
  by_cases h : s' = s
  · subst h
    rwa [DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ h]
    exact zero_mem _

end Defs

section Graded

variable {R : Type u} [CommRing R] {r : ℕ} {σ : Type w} {τ : Type t}
  [SetLike σ R] [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {M : Type v} [AddCommGroup M] [Module R M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]
  (f : Fin r → R)

/-! ### The differential preserves the degree -/

omit [DirectSum.Decomposition 𝒨] in
/-- **The Čech differential preserves the grading.** If every `f i` is homogeneous then the
differential carries the degree-`e` part of the degree-`p` term into the degree-`e` part of the
degree-`p + 1` term: on a summand it is a signed sum of the transition maps, each of which
preserves the degree by `Cech.mem_gradedPiece_cechι`. -/
theorem cechD_mem_gradedCechTerm {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ) (p : ℕ)
    {z : cechTerm f M p} (hz : z ∈ gradedCechTerm 𝒜 𝒨 f e p) :
    cechD f M p z ∈ gradedCechTerm 𝒜 𝒨 f e (p + 1) := by
  classical
  rw [← DirectSum.sum_support_of z, map_sum]
  refine AddSubgroup.sum_mem _ fun s _ => ?_
  rw [← DirectSum.lof_eq_of R, cechD_lof]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _
    (lof_mem_gradedCechTerm _ (mem_gradedPiece_cechι 𝒜 𝒨 f hc _ e (mem_gradedCechTerm.1 hz s))) _

/-! ### The two halves of the decomposition -/

/-- The inclusion of a direct sum of subgroups is the sum of its nonzero components. -/
private theorem coeAddMonoidHom_eq_sum_support {ι : Type*} {N : Type*} {S : Type*}
    [DecidableEq ι] [AddCommGroup N] [SetLike S N] [AddSubgroupClass S N] (A : ι → S)
    [∀ (i) (x : ↥(A i)), Decidable (x ≠ 0)] (ξ : DirectSum ι fun i => ↥(A i)) :
    DirectSum.coeAddMonoidHom A ξ = ∑ i ∈ DFinsupp.support ξ, ((ξ i : ↥(A i)) : N) := by
  conv_lhs => rw [← DirectSum.sum_support_of ξ]
  simp only [map_sum, DirectSum.coeAddMonoidHom_of]

/-- **Independence of the degrees.** A vanishing finite sum of homogeneous elements of distinct
degrees in a term of the Čech complex has vanishing summands: the statement is checked one
summand of the direct sum at a time, where it is
`Stacks.GradedLocalization.eq_zero_of_sum_eq_zero`. -/
theorem eq_zero_of_sum_mem_gradedCechTerm_eq_zero {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i))
    (p : ℕ) (t : Finset ℤ) (y : ℤ → cechTerm f M p)
    (hy : ∀ e ∈ t, y e ∈ gradedCechTerm 𝒜 𝒨 f e p)
    (hsum : (∑ e ∈ t, y e) = 0) {e₀ : ℤ} (he₀ : e₀ ∈ t) : y e₀ = 0 := by
  classical
  refine DFinsupp.ext fun s => ?_
  have hfs : (∏ i ∈ s.1, f i) ∈ 𝒜 (∑ i ∈ s.1, c i) :=
    SetLike.prod_mem_graded 𝒜 c f fun i _ => hc i
  refine Stacks.GradedLocalization.eq_zero_of_sum_eq_zero 𝒜 𝒨 hfs t (fun e => y e s)
    (fun e he => mem_gradedCechTerm.1 (hy e he) s) ?_ he₀
  rw [← DFinsupp.finsetSum_apply t y s, hsum, DFinsupp.zero_apply]

/-- **Every element of a term is a finite sum of homogeneous ones.** Each component of the direct
sum decomposes by `Stacks.GradedLocalization.isInternal_gradedPiece`, and the degree-`e` parts of
the components assemble into the degree-`e` part of the term. -/
theorem exists_sum_mem_gradedCechTerm {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (p : ℕ)
    (x : cechTerm f M p) :
    ∃ (t : Finset ℤ) (y : ℤ → cechTerm f M p),
      (∀ e, y e ∈ gradedCechTerm 𝒜 𝒨 f e p) ∧ (∀ e ∉ t, y e = 0) ∧ (∑ e ∈ t, y e) = x := by
  classical
  have hsurj : ∀ s : {s : Finset (Fin r) // s.card = p},
      ∃ ξ : DirectSum ℤ fun e =>
          ↥(Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 (∏ i ∈ s.1, f i) e),
        DirectSum.coeAddMonoidHom
          (Stacks.GradedLocalization.gradedPiece 𝒜 𝒨 (∏ i ∈ s.1, f i)) ξ = x s :=
    fun s => (Stacks.GradedLocalization.isInternal_gradedPiece 𝒜 𝒨
      (SetLike.prod_mem_graded 𝒜 c f fun i _ => hc i)).2 (x s)
  choose ξ hξ using hsurj
  have hval : ∀ s : {s : Finset (Fin r) // s.card = p},
      (∑ e ∈ DFinsupp.support (ξ s), ((ξ s e : cechMod f M s.1))) = x s := fun s => by
    rw [← hξ s, coeAddMonoidHom_eq_sum_support]
  refine ⟨(DFinsupp.support x).biUnion fun s => DFinsupp.support (ξ s),
    fun e => ∑ s ∈ DFinsupp.support x,
      DirectSum.lof R {t : Finset (Fin r) // t.card = p} (fun t => cechMod f M t.1) s
        ((ξ s e : cechMod f M s.1)), fun e => ?_, fun e he => ?_, ?_⟩
  · exact AddSubgroup.sum_mem _ fun s _ => lof_mem_gradedCechTerm s (ξ s e).2
  · refine Finset.sum_eq_zero fun s hs => ?_
    rw [DFinsupp.notMem_support_iff.1 fun hmem => he (Finset.mem_biUnion.2 ⟨s, hs, hmem⟩)]
    simp
  · rw [Finset.sum_comm]
    have hinner : ∀ s ∈ DFinsupp.support x,
        (∑ e ∈ (DFinsupp.support x).biUnion fun s => DFinsupp.support (ξ s),
            DirectSum.lof R {t : Finset (Fin r) // t.card = p} (fun t => cechMod f M t.1) s
              ((ξ s e : cechMod f M s.1))) =
          DirectSum.lof R {t : Finset (Fin r) // t.card = p} (fun t => cechMod f M t.1) s
            (x s) := by
      intro s hs
      have hsub : DFinsupp.support (ξ s) ⊆
          (DFinsupp.support x).biUnion fun s => DFinsupp.support (ξ s) :=
        fun e he => Finset.mem_biUnion.2 ⟨s, hs, he⟩
      have hz : ∀ e ∈ (DFinsupp.support x).biUnion fun s => DFinsupp.support (ξ s),
          e ∉ DFinsupp.support (ξ s) → ((ξ s e : cechMod f M s.1)) = 0 := by
        intro e _ hne
        rw [DFinsupp.notMem_support_iff.1 hne]
        simp
      rw [← map_sum, ← Finset.sum_subset hsub hz, hval s]
    rw [Finset.sum_congr rfl hinner]
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of x

/-- **Each term of the Čech complex is the direct sum of its homogeneous parts.** -/
theorem isInternal_gradedCechTerm {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (p : ℕ) :
    DirectSum.IsInternal fun e : ℤ => gradedCechTerm 𝒜 𝒨 f e p := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ζ hζ
    refine DFinsupp.ext fun e => ?_
    by_cases he : e ∈ DFinsupp.support ζ
    · refine Subtype.ext (eq_zero_of_sum_mem_gradedCechTerm_eq_zero 𝒜 𝒨 f hc p
        (DFinsupp.support ζ) (fun e => ((ζ e : cechTerm f M p))) (fun e _ => (ζ e).2) ?_ he)
      rwa [← coeAddMonoidHom_eq_sum_support]
    · exact DFinsupp.notMem_support_iff.1 he
  · intro x
    obtain ⟨t, y, hy, -, hsum⟩ := exists_sum_mem_gradedCechTerm 𝒜 𝒨 f hc p x
    refine ⟨∑ e ∈ t, DirectSum.of _ e (⟨y e, hy e⟩ :
      ↥(gradedCechTerm 𝒜 𝒨 f e p)), ?_⟩
    simp only [map_sum, DirectSum.coeAddMonoidHom_of, hsum]

/-! ### The graded lift of a coboundary -/

/-- **A homogeneous coboundary is the coboundary of a homogeneous element of the same degree.**
Decompose a preimage into homogeneous parts; the differential sends the degree-`j` part into
degree `j`, so independence in the next term forces every part but the degree-`e` one to
contribute nothing. This is what makes the degree-`e` subcomplex a *direct summand* of the Čech
complex rather than merely a subcomplex. -/
theorem exists_eq_cechD_mem_gradedCechTerm {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ)
    (p : ℕ) {z : cechTerm f M (p + 1)} (hz : z ∈ gradedCechTerm 𝒜 𝒨 f e (p + 1))
    {w : cechTerm f M p} (hw : cechD f M p w = z) :
    ∃ w' ∈ gradedCechTerm 𝒜 𝒨 f e p, cechD f M p w' = z := by
  classical
  obtain ⟨t, y, hy, hzero, hsum⟩ := exists_sum_mem_gradedCechTerm 𝒜 𝒨 f hc p w
  refine ⟨y e, hy e, ?_⟩
  set u : ℤ → cechTerm f M (p + 1) :=
    fun j => cechD f M p (y j) - (if j = e then z else 0) with hu
  have humem : ∀ j ∈ insert e t, u j ∈ gradedCechTerm 𝒜 𝒨 f j (p + 1) := by
    intro j _
    refine sub_mem (cechD_mem_gradedCechTerm 𝒜 𝒨 f hc j p (hy j)) ?_
    split_ifs with hj
    · exact hj ▸ hz
    · exact zero_mem _
  have hyins : (∑ j ∈ insert e t, y j) = w := by
    by_cases he : e ∈ t
    · rwa [Finset.insert_eq_self.2 he]
    · rwa [Finset.sum_insert he, hzero e he, zero_add]
  have husum : (∑ j ∈ insert e t, u j) = 0 := by
    simp only [hu, Finset.sum_sub_distrib]
    rw [← map_sum, hyins, hw, Finset.sum_ite_eq' (insert e t) e fun _ => z,
      ite_eq_left (Finset.mem_insert_self e t), sub_self]
  simpa only [hu, ite_true, sub_eq_zero] using
    eq_zero_of_sum_mem_gradedCechTerm_eq_zero 𝒜 𝒨 f hc (p + 1) (insert e t) u humem husum
      (Finset.mem_insert_self e t)

/-! ### The degree-`e` subcomplex -/

/-- The Čech differential restricted to the degree-`e` parts, as a map of abelian groups. -/
noncomputable def gradedCechD {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ) (p : ℕ) :
    gradedCechTerm 𝒜 𝒨 f e p →ₗ[ℤ] gradedCechTerm 𝒜 𝒨 f e (p + 1) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun w => ⟨cechD f M p w.1, cechD_mem_gradedCechTerm 𝒜 𝒨 f hc e p w.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }

omit [DirectSum.Decomposition 𝒨] in
/-- The restricted differential is the Čech differential on underlying elements. -/
@[simp]
theorem coe_gradedCechD {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ) (p : ℕ)
    (w : gradedCechTerm 𝒜 𝒨 f e p) :
    ((gradedCechD 𝒜 𝒨 f hc e p w : gradedCechTerm 𝒜 𝒨 f e (p + 1)) :
      cechTerm f M (p + 1)) = cechD f M p w.1 := rfl

/-- **The degree-`e` subcomplex of the extended Čech complex**, as a cochain complex of abelian
groups. It is a complex because the differential preserves the grading
(`Cech.cechD_mem_gradedCechTerm`), and by `Cech.isInternal_gradedCechTerm` the Čech complex is
degreewise the direct sum of these subcomplexes over `e ∈ ℤ`. -/
noncomputable def gradedCechComplex {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ) :
    CochainComplex (ModuleCat.{max u v} ℤ) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of ℤ (gradedCechTerm 𝒜 𝒨 f e p))
    (fun p => ModuleCat.ofHom (gradedCechD 𝒜 𝒨 f hc e p))
    (fun p => by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun w => Subtype.ext ?_
      exact LinearMap.congr_fun (cechD_comp_cechD f M p) w.1)

omit [DirectSum.Decomposition 𝒨] in
/-- The differential of the degree-`e` subcomplex in the degrees where it is nonzero. -/
theorem gradedCechComplex_d {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ) (p : ℕ) :
    (gradedCechComplex 𝒜 𝒨 f hc e).d p (p + 1) =
      ModuleCat.ofHom (gradedCechD 𝒜 𝒨 f hc e p) :=
  CochainComplex.of_d (fun q => ModuleCat.of ℤ (gradedCechTerm 𝒜 𝒨 f e q))
    (fun q => ModuleCat.ofHom (gradedCechD 𝒜 𝒨 f hc e q)) p

/-! ### Exactness in a fixed degree -/

/-- Exactness of the Čech complex in a degree, read as the elementary statement that every
cocycle is a coboundary. -/
theorem exists_eq_cechD_of_exactAt_cechComplex (p : ℕ)
    (hex : (cechComplex f M).ExactAt (p + 1))
    {z : cechTerm f M (p + 1)} (hdz : cechD f M (p + 1) z = 0) :
    ∃ w : cechTerm f M p, cechD f M p w = z := by
  rw [(cechComplex f M).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp),
    CategoryTheory.ShortComplex.moduleCat_exact_iff] at hex
  have hg : ((cechComplex f M).sc' p (p + 1) (p + 2)).g =
      ModuleCat.ofHom (cechD f M (p + 1)) := cechComplex_d f M (p + 1)
  have hf : ((cechComplex f M).sc' p (p + 1) (p + 2)).f =
      ModuleCat.ofHom (cechD f M p) := cechComplex_d f M p
  obtain ⟨w, hw⟩ := hex z (by rwa [hg])
  exact ⟨w, by rwa [hf] at hw⟩

/-- **A degree-`e` cocycle in a degree where the Čech complex is exact is a degree-`e`
coboundary.** Exactness of the whole complex produces some preimage, and
`Cech.exists_eq_cechD_mem_gradedCechTerm` replaces it by a homogeneous one of the same degree. -/
theorem exists_eq_cechD_of_exactAt {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ) (p : ℕ)
    (hex : (cechComplex f M).ExactAt (p + 1))
    {z : cechTerm f M (p + 1)} (hz : z ∈ gradedCechTerm 𝒜 𝒨 f e (p + 1))
    (hdz : cechD f M (p + 1) z = 0) :
    ∃ w ∈ gradedCechTerm 𝒜 𝒨 f e p, cechD f M p w = z := by
  obtain ⟨w, hw⟩ := exists_eq_cechD_of_exactAt_cechComplex f p hex hdz
  exact exists_eq_cechD_mem_gradedCechTerm 𝒜 𝒨 f hc e p hz hw

/-- **The degree-`e` subcomplex is exact wherever the Čech complex is.** -/
theorem exactAt_gradedCechComplex_of_exactAt {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ)
    (p : ℕ) (hex : (cechComplex f M).ExactAt (p + 1)) :
    (gradedCechComplex 𝒜 𝒨 f hc e).ExactAt (p + 1) := by
  have hg : ((gradedCechComplex 𝒜 𝒨 f hc e).sc' p (p + 1) (p + 1 + 1)).g =
      ModuleCat.ofHom (gradedCechD 𝒜 𝒨 f hc e (p + 1)) := gradedCechComplex_d 𝒜 𝒨 f hc e (p + 1)
  have hf : ((gradedCechComplex 𝒜 𝒨 f hc e).sc' p (p + 1) (p + 1 + 1)).f =
      ModuleCat.ofHom (gradedCechD 𝒜 𝒨 f hc e p) := gradedCechComplex_d 𝒜 𝒨 f hc e p
  rw [(gradedCechComplex 𝒜 𝒨 f hc e).exactAt_iff' p (p + 1) (p + 1 + 1) (by simp) (by simp),
    CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro w hw
  rw [hg] at hw
  let w' : ↥(gradedCechTerm 𝒜 𝒨 f e (p + 1)) := w
  have h2 : gradedCechD 𝒜 𝒨 f hc e (p + 1) w' = 0 := hw
  obtain ⟨v, hv, hvz⟩ := exists_eq_cechD_of_exactAt 𝒜 𝒨 f hc e p hex w'.2
    (by simpa using congrArg Subtype.val h2)
  refine ⟨⟨v, hv⟩, ?_⟩
  rw [hf]
  exact Subtype.ext hvz

/-- **The cohomology of the degree-`e` subcomplex vanishes wherever that of the Čech complex
does.** With `MvPolynomial.cechComplex_homology_X_isZero` this is the algebraic form of the
vanishing `H^q(ℙⁿ_R, 𝒪(e)) = 0` for `0 < q < n`, for every `e` at once and with no computation of
graded pieces; it becomes that vanishing once the Čech complex of the standard cover is identified
with this one ([Stacks, Tag 01XT]). -/
theorem isZero_homology_gradedCechComplex {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) (e : ℤ)
    (p : ℕ) (h : CategoryTheory.Limits.IsZero ((cechComplex f M).homology (p + 1))) :
    CategoryTheory.Limits.IsZero ((gradedCechComplex 𝒜 𝒨 f hc e).homology (p + 1)) :=
  ((gradedCechComplex 𝒜 𝒨 f hc e).exactAt_iff_isZero_homology (p + 1)).1
    (exactAt_gradedCechComplex_of_exactAt 𝒜 𝒨 f hc e p
      (((cechComplex f M).exactAt_iff_isZero_homology (p + 1)).2 h))

end Graded

end Cech

end
