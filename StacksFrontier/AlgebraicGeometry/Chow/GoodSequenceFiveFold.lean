module

public import Mathlib.RingTheory.KrullDimension.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthMinimalPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthOnePrimeSupport

/-!
# Five sequences with prime successive quotients for a two-periodic complex

Let `(M, φ, ψ)` be a `(2, 1)`-periodic complex of finite modules over a Noetherian local ring
whose cohomology has finite length, and let `q` be a prime of the support other than the closed
point. The multiplicity formula for such a complex is computed from five sequences with
successive quotients `R / q`: one spanning a submodule of `ker φ`, one spanning a submodule of
`ker ψ`, one inside each of those two spans coming from the image of the other differential, and
one inside the span of each of the two concatenations of a kernel sequence with a sequence of
lifts. This file produces those five sequences.

## Main results

* `AlgebraicGeometry.exists_sequences_of_support_subset_pair`: the five sequences exist, together
  with every property the multiplicity formula consumes.
* `AlgebraicGeometry.isFiniteLength_localizedModule_of_support_subset_pair`: the localization of
  the module at such a prime has finite length.
* `AlgebraicGeometry.ringKrullDim_quotient_eq_one_of_supportDim_eq_one`: a nonclosed point of the
  support of a module whose support has dimension one has one-dimensional residue ring.

## Implementation notes

Sequences are presented as in Tags 02QB and 02QC, by the successive subquotients of the spans of
their initial segments. Four transport lemmas move such a presentation around: along an
injective linear map (`Module.FiniteLength.primeFiltration_map_of_injective`), along a
reindexing (`Module.FiniteLength.primeFiltration_cast`), from a quotient by the span of a first
block to a concatenation (`Module.FiniteLength.primeFiltration_append_of_mkQ`), and along a
differential killing the first block
(`Module.FiniteLength.primeFiltration_map_of_le_ker`). The last of these is the heart of the
construction: it identifies the ideal of scalars moving one entry into the span of its
predecessors as `q` on both sides, which is the content of the adjustment by an element `d`
outside `q` in the source. Throughout, "finite colength at `q`" is carried in the concrete form
`∃ d ∉ q, ∀ m, d • m ∈ N`, which composes multiplicatively and converts to and from
`IsFiniteLength` of the quotient.

The sequence spanning a submodule of `ker ψ` is taken to be the image under `φ` of the sequence
of lifts, which is admissible and makes the two colength identities match up without an extra
length computation.

## References

* [Stacks Project, Tag 02QB](https://stacks.math.columbia.edu/tag/02QB)
* [Stacks Project, Tag 02QC](https://stacks.math.columbia.edu/tag/02QC)
* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/

@[expose] public section

noncomputable section

universe u v w

namespace Module.FiniteLength

/-! ### Colength at a prime in the concrete form -/

/-- A submodule whose quotient has finite length absorbs the whole module after multiplication
by a single element outside a prime other than the maximal ideal. -/
theorem exists_notMem_smul_mem_of_isFiniteLength_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R) (N : Submodule R M)
    (h : IsFiniteLength R (M ⧸ N)) :
    ∃ d : R, d ∉ q ∧ ∀ m : M, d • m ∈ N := by
  obtain ⟨d, hdq, hd⟩ := exists_notMem_smul_eq_zero_of_isFiniteLength h q hq
  refine ⟨d, hdq, fun m ↦ ?_⟩
  have hm := hd (Submodule.Quotient.mk m)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm

/-- A prime outside which a submodule absorbs the whole module is absent from the support of the
quotient. -/
theorem notMem_support_quotient_of_smul_mem
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (Q : PrimeSpectrum R) (N : Submodule R M) {d : R} (hdq : d ∉ Q.asIdeal)
    (hd : ∀ m : M, d • m ∈ N) :
    Q ∉ Module.support R (M ⧸ N) := by
  rw [Module.notMem_support_iff']
  intro c
  induction c using Submodule.Quotient.induction_on with
  | H m =>
    refine ⟨d, hdq, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hd m

/-- A module whose support meets no prime other than the closed point and `Q`, and which `Q`
misses, has finite length. -/
theorem isFiniteLength_of_support_subset_pair_of_notMem
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (Q : PrimeSpectrum R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, Q})
    (hQ : Q ∉ Module.support R M) :
    IsFiniteLength R M := by
  rcases subsingleton_or_nontrivial M with _ | _
  · exact IsFiniteLength.of_subsingleton
  · refine isFiniteLength_of_support (Set.Subset.antisymm (fun p hp ↦ ?_) (fun p hp ↦ ?_))
    · rcases Set.mem_insert_iff.mp (hsupp hp) with hpc | hpq
      · exact hpc
      · exact absurd (Set.mem_singleton_iff.mp hpq ▸ hp) hQ
    · exact Set.mem_singleton_iff.mp hp ▸ IsLocalRing.closedPoint_mem_support R M

/-- A submodule absorbing the whole module after multiplication by an element outside `Q` has
finite-length quotient, when the support meets no prime other than the closed point and `Q`. -/
theorem isFiniteLength_quotient_of_smul_mem
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (Q : PrimeSpectrum R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, Q}) (N : Submodule R M)
    {d : R} (hdq : d ∉ Q.asIdeal) (hd : ∀ m : M, d • m ∈ N) :
    IsFiniteLength R (M ⧸ N) :=
  isFiniteLength_of_support_subset_pair_of_notMem Q
    ((Module.support_subset_of_surjective N.mkQ (Submodule.mkQ_surjective N)).trans hsupp)
    (notMem_support_quotient_of_smul_mem Q N hdq hd)

/-- The relative version of `Module.FiniteLength.isFiniteLength_quotient_of_smul_mem`: a
submodule absorbing a larger one after multiplication by an element outside `Q` has
finite-length colength in it. -/
theorem isFiniteLength_quotient_submoduleOf_of_smul_mem
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (Q : PrimeSpectrum R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, Q}) (A B : Submodule R M)
    {d : R} (hdq : d ∉ Q.asIdeal) (hd : ∀ m ∈ A, d • m ∈ B) :
    IsFiniteLength R (↥A ⧸ B.submoduleOf A) :=
  isFiniteLength_quotient_of_smul_mem (M := ↥A) Q
    ((support_submodule_subset A).trans hsupp) (B.submoduleOf A) hdq
    (fun m ↦ hd (m : M) m.2)

/-! ### Transport of a filtration with prime successive quotients -/

/-- A sequence whose successive quotients are copies of `R / q` keeps them after transport along
an injective linear map. -/
theorem primeFiltration_map_of_injective {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (hf : Function.Injective f) {l : ℕ} (q : Ideal R) (x : Fin l → N)
    (y : Fin l → M) (hy : ∀ j, y j = f (x j))
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R N) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R N).subtype) ≃ₗ[R]
          R ⧸ q)) :
    ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R M) ⧸
            (spanBefore (R := R) y i).comap
              (spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q) := by
  obtain rfl : y = fun j ↦ f (x j) := funext hy
  intro i
  have hB : (spanBefore (R := R) x i).map f =
      spanBefore (R := R) (fun j ↦ f (x j)) i := (spanBefore_comp x f i).symm
  have hA : (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R N).map f =
      (spanBefore (R := R) (fun j ↦ f (x j)) i ⊔ R ∙ f (x i) : Submodule R M) := by
    rw [Submodule.map_sup, hB, Submodule.map_span, Set.image_singleton]
  exact ⟨(subquotEquivOfMapEq f hf le_sup_left hA hB).symm.trans (hxf i).some⟩

/-- Reindexing a sequence along an equality of lengths keeps its successive quotients. -/
theorem primeFiltration_cast {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n m : ℕ} (h : n = m) (q : Ideal R) (g : Fin m → M)
    (hgf : ∀ i : Fin m,
      Nonempty
        (((spanBefore (R := R) g i ⊔ R ∙ g i : Submodule R M) ⧸
            (spanBefore (R := R) g i).comap
              (spanBefore (R := R) g i ⊔ R ∙ g i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q)) :
    ∀ j : Fin n,
      Nonempty
        (((spanBefore (R := R) (fun k : Fin n ↦ g (Fin.cast h k)) j ⊔
              R ∙ g (Fin.cast h j) : Submodule R M) ⧸
            (spanBefore (R := R) (fun k : Fin n ↦ g (Fin.cast h k)) j).comap
              (spanBefore (R := R) (fun k : Fin n ↦ g (Fin.cast h k)) j ⊔
                R ∙ g (Fin.cast h j) : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q) := by
  intro j
  rw [spanBefore_cast h g j]
  exact hgf (Fin.cast h j)

/-! ### Spans of a concatenation -/

/-- The span of the entries of a concatenation is the join of the spans of its two blocks. -/
theorem span_range_fin_append {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] {n m : ℕ} (u : Fin n → M) (c : Fin m → M) :
    Submodule.span R (Set.range (Fin.append u c)) =
      Submodule.span R (Set.range u) ⊔ Submodule.span R (Set.range c) := by
  have h : Set.range (Fin.append u c) = Set.range u ∪ Set.range c := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      cases k using Fin.addCases <;> simp
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Fin.castAdd m i, by simp⟩
      · exact ⟨Fin.natAdd n j, by simp⟩
  rw [h, Submodule.span_union]

/-- Reindexing a sequence along an equality of lengths does not change the span of its
entries. -/
theorem span_range_cast {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n m : ℕ} (h : n = m) (g : Fin m → M) :
    Submodule.span R (Set.range (fun k : Fin n ↦ g (Fin.cast h k))) =
      Submodule.span R (Set.range g) := by
  subst h
  simp

/-- The span of the entries of a concatenation preceding an index in the first block is the span
of the preceding entries of that block. -/
theorem spanBefore_append_left {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] {n m : ℕ} (u : Fin n → M) (c : Fin m → M) (i : Fin n) :
    spanBefore (R := R) (Fin.append u c) (Fin.castAdd m i) = spanBefore (R := R) u i := by
  have hi := i.isLt
  have himg : Fin.append u c '' Set.Iio (Fin.castAdd m i) = u '' Set.Iio i := by
    ext w
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine Fin.addCases (motive := fun k ↦ k ∈ Set.Iio (Fin.castAdd m i) →
        Fin.append u c k ∈ u '' Set.Iio i) (fun k' hk' ↦ ?_) (fun k' hk' ↦ ?_) k hk
      · refine ⟨k', ?_, by simp⟩
        have h1 : (Fin.castAdd m k').val < (Fin.castAdd m i).val := hk'
        exact Fin.lt_def.mpr (by simpa using h1)
      · exfalso
        have h1 : (Fin.natAdd n k').val < (Fin.castAdd m i).val := hk'
        simp only [Fin.natAdd, Fin.castAdd, Fin.castLE] at h1
        omega
    · rintro ⟨k', hk', rfl⟩
      refine ⟨Fin.castAdd m k', ?_, by simp⟩
      exact Fin.lt_def.mpr (by simpa using (show k'.val < i.val from hk'))
  rw [spanBefore, himg, spanBefore]

/-- A sequence with successive quotients `R / q` concatenated with a sequence whose image in the
quotient by the span of the first block also has successive quotients `R / q` again has
successive quotients `R / q`. -/
theorem primeFiltration_append_of_mkQ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] {n m : ℕ} (q : Ideal R) (u : Fin n → M) (c : Fin m → M)
    (huf : ∀ i : Fin n,
      Nonempty
        (((spanBefore (R := R) u i ⊔ R ∙ u i : Submodule R M) ⧸
            (spanBefore (R := R) u i).comap
              (spanBefore (R := R) u i ⊔ R ∙ u i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hcf : ∀ i : Fin m,
      Nonempty
        (((spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i ⊔
              R ∙ (Submodule.span R (Set.range u)).mkQ (c i) :
            Submodule R (M ⧸ Submodule.span R (Set.range u))) ⧸
            (spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i).comap
              (spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i ⊔
                R ∙ (Submodule.span R (Set.range u)).mkQ (c i) :
              Submodule R (M ⧸ Submodule.span R (Set.range u))).subtype) ≃ₗ[R]
          R ⧸ q)) :
    ∀ k : Fin (n + m),
      Nonempty
        (((spanBefore (R := R) (Fin.append u c) k ⊔ R ∙ Fin.append u c k : Submodule R M) ⧸
            (spanBefore (R := R) (Fin.append u c) k).comap
              (spanBefore (R := R) (Fin.append u c) k ⊔
                R ∙ Fin.append u c k : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q) := by
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_)
  · rw [spanBefore_append_left, Fin.append_left]
    exact huf i
  · have hBdown : spanBefore (R := R)
        (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) j =
        (spanBefore (R := R) c j).map (Submodule.span R (Set.range u)).mkQ :=
      spanBefore_comp c (Submodule.span R (Set.range u)).mkQ j
    have hB : (Submodule.span R (Set.range u) ⊔ spanBefore (R := R) c j).map
        (Submodule.span R (Set.range u)).mkQ =
        spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) j := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, hBdown]
    have hA : ((Submodule.span R (Set.range u) ⊔ spanBefore (R := R) c j) ⊔ R ∙ c j).map
        (Submodule.span R (Set.range u)).mkQ =
        (spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) j ⊔
          R ∙ (Submodule.span R (Set.range u)).mkQ (c j)) := by
      rw [Submodule.map_sup, hB, Submodule.map_span, Set.image_singleton]
    rw [spanBefore_append_natAdd, Fin.append_right]
    exact ⟨(subquotEquivMapMkQ (Submodule.span R (Set.range u)) le_sup_left hA hB).trans
      (hcf j).some⟩

/-! ### The ideal of scalars moving one entry into a submodule -/

/-- The quotient of a submodule enlarged by one element by that submodule is the quotient of `R`
by the ideal of scalars carrying the element into it. -/
def subquotSpanSingletonEquiv {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (U : Submodule R M) (z : M) :
    (↥(U ⊔ R ∙ z : Submodule R M) ⧸
        U.comap (U ⊔ R ∙ z : Submodule R M).subtype) ≃ₗ[R]
      R ⧸ U.comap (LinearMap.toSpanSingleton R M z) := by
  have hz : z ∈ (U ⊔ R ∙ z : Submodule R M) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  set g : R →ₗ[R] (↥(U ⊔ R ∙ z : Submodule R M) ⧸
      U.comap (U ⊔ R ∙ z : Submodule R M).subtype) :=
    (U.comap (U ⊔ R ∙ z : Submodule R M).subtype).mkQ ∘ₗ
      LinearMap.toSpanSingleton R ↥(U ⊔ R ∙ z : Submodule R M) ⟨z, hz⟩ with hg
  have hsurj : Function.Surjective g := by
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨p, hp, w₂, hw₂, hsum⟩ := Submodule.mem_sup.mp w.2
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw₂
      refine ⟨r, ?_⟩
      rw [hg, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
        Submodule.mem_comap]
      have hcoe : ((LinearMap.toSpanSingleton R ↥(U ⊔ R ∙ z : Submodule R M) ⟨z, hz⟩ r -
          w : ↥(U ⊔ R ∙ z : Submodule R M)) : M) = r • z - (w : M) := by
        simp [LinearMap.toSpanSingleton_apply]
      rw [Submodule.subtype_apply, hcoe, hr, ← hsum]
      simpa using Submodule.neg_mem U hp
  have hker : LinearMap.ker g = U.comap (LinearMap.toSpanSingleton R M z) := by
    ext r
    rw [LinearMap.mem_ker, hg, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.subtype_apply]
    constructor <;> intro h <;> simpa [LinearMap.toSpanSingleton_apply] using h
  exact (LinearMap.quotKerEquivOfSurjective g hsurj).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)

/-- Two ideals with linearly isomorphic quotients are equal. -/
theorem eq_of_quotient_linearEquiv {R : Type u} [CommRing R] {I J : Ideal R}
    (e : (R ⧸ I) ≃ₗ[R] R ⧸ J) : I = J :=
  (Ideal.annihilator_quotient (I := I)).symm.trans
    (e.annihilator_eq.trans Ideal.annihilator_quotient)

/-- If the quotient cut out by one entry over a submodule is `R / q`, then `q` is exactly the
ideal of scalars carrying the entry into the submodule. -/
theorem comap_toSpanSingleton_eq_of_quotEquiv {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (U : Submodule R M) (z : M) (q : Ideal R)
    (e : (↥(U ⊔ R ∙ z : Submodule R M) ⧸
      U.comap (U ⊔ R ∙ z : Submodule R M).subtype) ≃ₗ[R] R ⧸ q) :
    U.comap (LinearMap.toSpanSingleton R M z) = q :=
  eq_of_quotient_linearEquiv ((subquotSpanSingletonEquiv U z).symm.trans e)

/-- Conversely, if `q` is the ideal of scalars carrying an entry into a submodule, the quotient
cut out by that entry is `R / q`. -/
theorem quotEquiv_of_comap_toSpanSingleton_eq {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (U : Submodule R M) (z : M) (q : Ideal R)
    (h : U.comap (LinearMap.toSpanSingleton R M z) = q) :
    Nonempty ((↥(U ⊔ R ∙ z : Submodule R M) ⧸
      U.comap (U ⊔ R ∙ z : Submodule R M).subtype) ≃ₗ[R] R ⧸ q) :=
  ⟨(subquotSpanSingletonEquiv U z).trans (Submodule.quotEquivOfEq _ _ h)⟩

/-- **The adjustment by an element outside `q`.** Let `φ` be an endomorphism and `X ≤ ker φ` a
submodule absorbing `ker φ` after multiplication by an element outside `q`. If a sequence `c`
has successive quotients `R / q` over `X`, then its image under `φ` has successive quotients
`R / q`. -/
theorem primeFiltration_map_of_le_ker {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] M) (q : Ideal R) [q.IsPrime] {X : Submodule R M}
    (hXK : X ≤ LinearMap.ker φ) {d : R} (hdq : d ∉ q)
    (hd : ∀ w ∈ LinearMap.ker φ, d • w ∈ X) {m : ℕ} (c : Fin m → M) (y : Fin m → M)
    (hy : ∀ j, y j = φ (c j))
    (hcf : ∀ j : Fin m,
      Nonempty
        (((X ⊔ spanBefore (R := R) c j ⊔ R ∙ c j : Submodule R M) ⧸
            (X ⊔ spanBefore (R := R) c j : Submodule R M).comap
              (X ⊔ spanBefore (R := R) c j ⊔ R ∙ c j : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q)) :
    ∀ j : Fin m,
      Nonempty
        (((spanBefore (R := R) y j ⊔ R ∙ y j : Submodule R M) ⧸
            (spanBefore (R := R) y j).comap
              (spanBefore (R := R) y j ⊔ R ∙ y j : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q) := by
  obtain rfl : y = fun j ↦ φ (c j) := funext hy
  intro j
  have hI := comap_toSpanSingleton_eq_of_quotEquiv
    (X ⊔ spanBefore (R := R) c j : Submodule R M) (c j) q (hcf j).some
  have hB : spanBefore (R := R) (fun k ↦ φ (c k)) j =
      (spanBefore (R := R) c j).map φ := spanBefore_comp c φ j
  refine quotEquiv_of_comap_toSpanSingleton_eq
    (spanBefore (R := R) (fun k ↦ φ (c k)) j) (φ (c j)) q ?_
  rw [hB]
  refine le_antisymm (fun r hr ↦ ?_) (fun r hr ↦ ?_)
  · rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply] at hr
    obtain ⟨v, hv, hvr⟩ := hr
    have hker : r • c j - v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hvr, sub_self]
    have hsplit : (d * r) • c j = d • (r • c j - v) + d • v := by
      rw [smul_sub, mul_smul]
      abel
    have hmem : (d * r) • c j ∈ (X ⊔ spanBefore (R := R) c j : Submodule R M) := by
      rw [hsplit]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hd _ hker))
        (Submodule.mem_sup_right (Submodule.smul_mem _ d hv))
    have hdr : d * r ∈ q := by
      refine hI.le ?_
      rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      exact hmem
    exact (‹q.IsPrime›.mem_or_mem hdr).resolve_left hdq
  · have h1 : r • c j ∈ (X ⊔ spanBefore (R := R) c j : Submodule R M) := by
      have := hI.ge hr
      rwa [Submodule.mem_comap, LinearMap.toSpanSingleton_apply] at this
    have h2 : φ (r • c j) ∈ (X ⊔ spanBefore (R := R) c j : Submodule R M).map φ :=
      Submodule.mem_map_of_mem h1
    rw [Submodule.map_sup, LinearMap.le_ker_iff_map.mp hXK, bot_sup_eq] at h2
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
    rwa [map_smul] at h2

/-! ### Localized length from a sequence of finite colength -/

/-- For a sequence with successive quotients `R / q` whose span has finite-length colength, the
localized length of the module at `q` is the number of its terms. -/
theorem localized_length_eq_of_isFiniteLength_quotient_span {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R)
    {l : ℕ} (x : Fin l → M)
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hfin : IsFiniteLength R (M ⧸ Submodule.span R (Set.range x))) :
    Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl M) = l := by
  have e : LocalizedModule q.primeCompl ↥(Submodule.span R (Set.range x))
      ≃ₗ[Localization.AtPrime q] LocalizedModule q.primeCompl M :=
    LinearEquiv.ofBijective _
      (AlgebraicGeometry.bijective_map_subtype_of_isFiniteLength_quotient q hq
        (Submodule.span R (Set.range x)) hfin)
  rw [← e.length_eq, ← spanPrefix_length x]
  exact localized_length_spanPrefix q x hxf l le_rfl

end Module.FiniteLength

namespace AlgebraicGeometry

open Module.FiniteLength

/-! ### The dimension of the residue ring at a nonclosed point of the support -/

/-- A nonclosed point of the support of a module whose support has dimension one cuts out a
one-dimensional residue ring. -/
theorem ringKrullDim_quotient_eq_one_of_supportDim_eq_one {R : Type u} [CommRing R]
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hM : Module.supportDim R M = 1) {Q : PrimeSpectrum R}
    (hQM : Q ∈ Module.support R M) (hQ : Q ≠ IsLocalRing.closedPoint R) :
    ringKrullDim (R ⧸ Q.asIdeal) = 1 := by
  rw [← Module.supportDim_quotient_eq_ringKrullDim]
  have hQQ : Q ∈ Module.support R (R ⧸ Q.asIdeal) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl
  have hsub : Module.support R (R ⧸ Q.asIdeal) ⊆ Module.support R M := by
    intro p hp
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient] at hp
    exact Module.mem_support_mono hp hQM
  have hlt : Q < IsLocalRing.closedPoint R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Q.isPrime.ne_top) hQ
  refine le_antisymm ((supportDim_le_of_support_subset hsub).trans hM.le) ?_
  change (1 : WithBot ℕ∞) ≤ Order.krullDim (Module.support R (R ⧸ Q.asIdeal))
  exact Order.one_le_krullDim_iff.mpr
    ⟨⟨Q, hQQ⟩, ⟨IsLocalRing.closedPoint R, Module.mem_support_mono hlt.le hQQ⟩, hlt⟩

/-! ### The sequences produced by Tag 02QC, read in the ambient module -/

/-- **Tag 02QC for a submodule.** A submodule of a finite module whose support meets no prime
other than the closed point and `Q` carries a sequence with successive quotients `R / Q`, read
in the ambient module, whose span absorbs the submodule after multiplication by an element
outside `Q`. -/
theorem exists_primeFiltration_submodule {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (Q : PrimeSpectrum R) (hQ : Q ≠ IsLocalRing.closedPoint R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, Q}) (P : Submodule R M) :
    ∃ (l : ℕ) (x : Fin l → M), (∀ i, x i ∈ P) ∧
      (∀ i : Fin l,
        Nonempty
          (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
              (spanBefore (R := R) x i).comap
                (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      ∃ d : R, d ∉ Q.asIdeal ∧ ∀ w ∈ P, d • w ∈ Submodule.span R (Set.range x) := by
  have hqm : Q.asIdeal ≠ IsLocalRing.maximalIdeal R := fun h ↦ hQ (PrimeSpectrum.ext h)
  have hsuppP : Module.support R ↥P ⊆ {IsLocalRing.closedPoint R, Q} :=
    (support_submodule_subset P).trans hsupp
  obtain ⟨l, x₀, hnot, hx₀f, -⟩ :=
    exists_sequence_with_successive_quotients_of_support_subset (N := ↥P) Q hsuppP
  have hfin : IsFiniteLength R (↥P ⧸ Submodule.span R (Set.range x₀)) :=
    isFiniteLength_of_support_subset_pair_of_notMem Q
      ((Module.support_subset_of_surjective _
        (Submodule.mkQ_surjective _)).trans hsuppP) hnot
  obtain ⟨d, hdq, hd⟩ := exists_notMem_smul_mem_of_isFiniteLength_quotient Q.asIdeal hqm _ hfin
  refine ⟨l, fun i ↦ (x₀ i : M), fun i ↦ (x₀ i).2, ?_, d, hdq, fun w hw ↦ ?_⟩
  · exact primeFiltration_map_of_injective P.subtype (Submodule.subtype_injective P)
      Q.asIdeal x₀ _ (fun _ ↦ rfl) hx₀f
  · have hmap : Submodule.span R (Set.range (fun i ↦ ((x₀ i : M)))) =
        (Submodule.span R (Set.range x₀)).map P.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap]
    exact ⟨d • (⟨w, hw⟩ : ↥P), hd _, rfl⟩

/-- **Tag 02QC for a quotient of a submodule.** For submodules `U` and `P` of a module whose
support meets no prime other than the closed point and `Q`, there is a sequence in `P` whose
image in `M ⧸ U` has successive quotients `R / Q` and whose span together with `U` absorbs `P`
after multiplication by an element outside `Q`. -/
theorem exists_primeFiltration_quotient {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (Q : PrimeSpectrum R) (hQ : Q ≠ IsLocalRing.closedPoint R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, Q})
    (U P : Submodule R M) :
    ∃ (l : ℕ) (c : Fin l → M), (∀ i, c i ∈ P) ∧
      (∀ i : Fin l,
        Nonempty
          (((spanBefore (R := R) (fun k ↦ U.mkQ (c k)) i ⊔ R ∙ U.mkQ (c i) :
              Submodule R (M ⧸ U)) ⧸
              (spanBefore (R := R) (fun k ↦ U.mkQ (c k)) i).comap
                (spanBefore (R := R) (fun k ↦ U.mkQ (c k)) i ⊔ R ∙ U.mkQ (c i) :
                  Submodule R (M ⧸ U)).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      ∃ d : R, d ∉ Q.asIdeal ∧
        ∀ w ∈ P, d • w ∈ U ⊔ Submodule.span R (Set.range c) := by
  classical
  have hqm : Q.asIdeal ≠ IsLocalRing.maximalIdeal R := fun h ↦ hQ (PrimeSpectrum.ext h)
  have hsuppP : Module.support R ↥P ⊆ {IsLocalRing.closedPoint R, Q} :=
    (support_submodule_subset P).trans hsupp
  have hsuppN : Module.support R (↥P ⧸ U.submoduleOf P) ⊆ {IsLocalRing.closedPoint R, Q} :=
    (Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)).trans hsuppP
  obtain ⟨l, c₀, hnot, hc₀f, -⟩ :=
    exists_sequence_with_successive_quotients_of_support_subset
      (N := ↥P ⧸ U.submoduleOf P) Q hsuppN
  have hfin : IsFiniteLength R ((↥P ⧸ U.submoduleOf P) ⧸ Submodule.span R (Set.range c₀)) :=
    isFiniteLength_of_support_subset_pair_of_notMem Q
      ((Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)).trans hsuppN) hnot
  obtain ⟨d, hdq, hd⟩ := exists_notMem_smul_mem_of_isFiniteLength_quotient Q.asIdeal hqm _ hfin
  choose c₁ hc₁ using fun i ↦ Submodule.mkQ_surjective (U.submoduleOf P) (c₀ i)
  have hle : U.submoduleOf P ≤ U.comap P.subtype := le_rfl
  have hfinj : Function.Injective (Submodule.mapQ (U.submoduleOf P) U P.subtype hle) := by
    rw [← LinearMap.ker_eq_bot]
    refine le_antisymm (fun v hv ↦ ?_) bot_le
    induction v using Submodule.Quotient.induction_on with
    | H w =>
      rw [LinearMap.mem_ker] at hv
      have h : (Submodule.Quotient.mk ((w : M)) : M ⧸ U) = 0 := hv
      rw [Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact h
  refine ⟨l, fun i ↦ ((c₁ i : M)), fun i ↦ (c₁ i).2, ?_, d, hdq, fun w hw ↦ ?_⟩
  · refine primeFiltration_map_of_injective _ hfinj Q.asIdeal c₀ _ (fun j ↦ ?_) hc₀f
    rw [← hc₁ j]
    rfl
  · have hc₀fun : c₀ = (U.submoduleOf P).mkQ ∘ c₁ := funext fun i ↦ (hc₁ i).symm
    have hcmap : Submodule.span R (Set.range c₀) =
        (Submodule.span R (Set.range c₁)).map (U.submoduleOf P).mkQ := by
      rw [hc₀fun, Submodule.map_span, ← Set.range_comp]
    have hstep : d • (⟨w, hw⟩ : ↥P) ∈
        U.submoduleOf P ⊔ Submodule.span R (Set.range c₁) := by
      have h0 := hd ((U.submoduleOf P).mkQ (⟨w, hw⟩ : ↥P))
      rw [hcmap, ← map_smul] at h0
      rw [← Submodule.comap_map_mkQ (U.submoduleOf P) (Submodule.span R (Set.range c₁))]
      exact h0
    obtain ⟨v₁, hv₁, v₂, hv₂, hsum⟩ := Submodule.mem_sup.mp hstep
    have hv₂' : ((v₂ : M)) ∈ Submodule.span R (Set.range (fun i ↦ ((c₁ i : M)))) := by
      have hmem := Submodule.mem_map_of_mem (f := P.subtype) hv₂
      rw [Submodule.map_span, ← Set.range_comp] at hmem
      exact hmem
    have hw' : d • w = ((v₁ : M)) + ((v₂ : M)) := by
      rw [← Submodule.coe_add, hsum]
      rfl
    rw [hw']
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hv₁ : (v₁ : M) ∈ U))
      (Submodule.mem_sup_right hv₂')

/-! ### The five sequences -/

/-- The localization at a nonclosed point of the support of a finite module whose support meets
no other prime has finite length. -/
theorem isFiniteLength_localizedModule_of_support_subset_pair {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (Q : PrimeSpectrum R) (hQ : Q ≠ IsLocalRing.closedPoint R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, Q}) :
    IsFiniteLength (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl M) := by
  have hqm : Q.asIdeal ≠ IsLocalRing.maximalIdeal R := fun h ↦ hQ (PrimeSpectrum.ext h)
  obtain ⟨l, x, -, hxf, d, hdq, hd⟩ := exists_primeFiltration_submodule Q hQ hsupp ⊤
  have hfin : IsFiniteLength R (M ⧸ Submodule.span R (Set.range x)) :=
    isFiniteLength_quotient_of_smul_mem Q hsupp _ hdq (fun m ↦ hd m Submodule.mem_top)
  rw [← Module.length_ne_top_iff,
    localized_length_eq_of_isFiniteLength_quotient_span Q.asIdeal hqm x hxf hfin]
  exact ENat.natCast_ne_top l

/-- If every `d • m` lies in the span of a concatenation `u ++ c` with `u` killed by `f`, then
`d * e` carries any `w` with `e • w ∈ range f` into the span of `f ∘ c`. -/
private theorem smul_mem_span_map_append_of_le_ker {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) {n m : ℕ} (u : Fin n → M) (c : Fin m → M)
    (hu : Submodule.span R (Set.range u) ≤ LinearMap.ker f) {d e : R}
    (hd : ∀ v : M, d • v ∈ Submodule.span R (Set.range (Fin.append u c))) {w : M}
    (hw : e • w ∈ LinearMap.range f) :
    (d * e) • w ∈ Submodule.span R (Set.range (fun j ↦ f (c j))) := by
  obtain ⟨v, hv⟩ := hw
  have h := Submodule.mem_map_of_mem (f := f) (hd v)
  rw [span_range_fin_append, Submodule.map_sup, LinearMap.le_ker_iff_map.mp hu, bot_sup_eq,
    Submodule.map_span, ← Set.range_comp, Function.comp_def, map_smul, hv, smul_smul] at h
  exact h

/-- **The five sequences of Tag 02QD.** Let `(M, φ, ψ)` be a `(2, 1)`-periodic complex of finite
modules over a Noetherian local ring whose cohomology has finite length, and let `Q` be a
nonclosed point meeting the whole support of `M` apart from the closed point. Then there are
sequences with successive quotients `R / Q`: one spanning a submodule of `ker φ`, one spanning a
submodule of `ker ψ`, one inside each of those two spans coming from the image of the other
differential together with a sequence of lifts, the two concatenations of a kernel sequence with
the lifts, and one inside the span of both concatenations — all of them of finite colength where
the multiplicity formula needs it. -/
theorem exists_sequences_of_support_subset_pair {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (Q : PrimeSpectrum R) (hQ : Q ≠ IsLocalRing.closedPoint R)
    (hsupp : Module.support R M ⊆ {IsLocalRing.closedPoint R, Q})
    (hfin : HasFiniteLengthHomology (twoPeriodicComplex φ ψ hφψ hψφ)) :
    ∃ (b a : ℕ) (x : Fin b → M) (t y : Fin a → M) (s : Fin b → M) (xt : Fin a → M)
      (st : Fin b → M) (wφ wψ z : Fin (b + a) → M),
      (∀ i, y i = φ (xt i)) ∧
      (∀ i, s i = ψ (st i)) ∧
      (∀ j, wφ j = Fin.append x xt j) ∧
      (∀ j, wψ j = Fin.append t st (Fin.cast (Nat.add_comm b a) j)) ∧
      (∀ i : Fin b,
        Nonempty
          (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
              (spanBefore (R := R) x i).comap
                (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      (∀ i : Fin a,
        Nonempty
          (((spanBefore (R := R) t i ⊔ R ∙ t i : Submodule R M) ⧸
              (spanBefore (R := R) t i).comap
                (spanBefore (R := R) t i ⊔ R ∙ t i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      (∀ i : Fin a,
        Nonempty
          (((spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R M) ⧸
              (spanBefore (R := R) y i).comap
                (spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      (∀ i : Fin b,
        Nonempty
          (((spanBefore (R := R) s i ⊔ R ∙ s i : Submodule R M) ⧸
              (spanBefore (R := R) s i).comap
                (spanBefore (R := R) s i ⊔ R ∙ s i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      (∀ i : Fin (b + a),
        Nonempty
          (((spanBefore (R := R) wφ i ⊔ R ∙ wφ i : Submodule R M) ⧸
              (spanBefore (R := R) wφ i).comap
                (spanBefore (R := R) wφ i ⊔ R ∙ wφ i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      (∀ i : Fin (b + a),
        Nonempty
          (((spanBefore (R := R) wψ i ⊔ R ∙ wψ i : Submodule R M) ⧸
              (spanBefore (R := R) wψ i).comap
                (spanBefore (R := R) wψ i ⊔ R ∙ wψ i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      (∀ i : Fin (b + a),
        Nonempty
          (((spanBefore (R := R) z i ⊔ R ∙ z i : Submodule R M) ⧸
              (spanBefore (R := R) z i).comap
                (spanBefore (R := R) z i ⊔ R ∙ z i : Submodule R M).subtype) ≃ₗ[R]
            R ⧸ Q.asIdeal)) ∧
      Submodule.span R (Set.range x) ≤ LinearMap.ker φ ∧
      Submodule.span R (Set.range t) ≤ LinearMap.ker ψ ∧
      Submodule.span R (Set.range s) ≤ Submodule.span R (Set.range x) ∧
      Submodule.span R (Set.range y) ≤ Submodule.span R (Set.range t) ∧
      Submodule.span R (Set.range z) ≤ Submodule.span R (Set.range wφ) ∧
      Submodule.span R (Set.range z) ≤ Submodule.span R (Set.range wψ) ∧
      Module.length R (↥(LinearMap.ker φ) ⧸
        (Submodule.span R (Set.range s)).submoduleOf (LinearMap.ker φ)) ≠ ⊤ ∧
      Module.length R (↥(LinearMap.ker ψ) ⧸
        (Submodule.span R (Set.range y)).submoduleOf (LinearMap.ker ψ)) ≠ ⊤ ∧
      Module.length R (↥(LinearMap.ker φ) ⧸
        (Submodule.span R (Set.range x)).submoduleOf (LinearMap.ker φ)) ≠ ⊤ ∧
      Module.length R (↥(LinearMap.ker ψ) ⧸
        (Submodule.span R (Set.range t)).submoduleOf (LinearMap.ker ψ)) ≠ ⊤ ∧
      Module.length R (M ⧸ Submodule.span R (Set.range z)) ≠ ⊤ := by
  classical
  have hqm : Q.asIdeal ≠ IsLocalRing.maximalIdeal R := fun h ↦ hQ (PrimeSpectrum.ext h)
  have hmemφ : ∀ w : M, ψ w ∈ LinearMap.ker φ := fun w ↦ LinearMap.congr_fun hφψ w
  have hmemψ : ∀ w : M, φ w ∈ LinearMap.ker ψ := fun w ↦ LinearMap.congr_fun hψφ w
  have hH0 := (isFiniteLength_homology_zero_iff φ ψ hφψ hψφ hmemφ).mp (hfin 0)
  rw [range_codRestrict_eq_comap] at hH0
  have hH1 := (isFiniteLength_homology_one_iff φ ψ hφψ hψφ hmemψ).mp (hfin 1)
  rw [range_codRestrict_eq_comap] at hH1
  obtain ⟨e0, he0q, he0⟩ := exists_notMem_smul_mem_of_isFiniteLength_quotient
    (M := ↥(LinearMap.ker φ)) Q.asIdeal hqm _ hH0
  obtain ⟨e1, he1q, he1⟩ := exists_notMem_smul_mem_of_isFiniteLength_quotient
    (M := ↥(LinearMap.ker ψ)) Q.asIdeal hqm _ hH1
  have hd0 : ∀ w ∈ LinearMap.ker φ, e0 • w ∈ LinearMap.range ψ := fun w hw ↦ he0 ⟨w, hw⟩
  have hd1 : ∀ w ∈ LinearMap.ker ψ, e1 • w ∈ LinearMap.range φ := fun w hw ↦ he1 ⟨w, hw⟩
  obtain ⟨b, x, hxP, hxf, dX, hdXq, hdX⟩ :=
    exists_primeFiltration_submodule Q hQ hsupp (LinearMap.ker φ)
  have hXK : Submodule.span R (Set.range x) ≤ LinearMap.ker φ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hxP)
  have hfinX : Module.length R (↥(LinearMap.ker φ) ⧸
      (Submodule.span R (Set.range x)).submoduleOf (LinearMap.ker φ)) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_submoduleOf_of_smul_mem Q hsupp _ _ hdXq hdX)
  obtain ⟨a, xt, -, hxtf, dVφ, hdVφq, hdVφ⟩ :=
    exists_primeFiltration_quotient Q hQ hsupp (Submodule.span R (Set.range x)) ⊤
  have hwφf := primeFiltration_append_of_mkQ Q.asIdeal x xt hxf hxtf
  have hVφ : Submodule.span R (Set.range (Fin.append x xt)) =
      Submodule.span R (Set.range x) ⊔ Submodule.span R (Set.range xt) :=
    span_range_fin_append x xt
  have hdVφ' : ∀ m : M, dVφ • m ∈ Submodule.span R (Set.range (Fin.append x xt)) := by
    intro m
    rw [hVφ]
    exact hdVφ m Submodule.mem_top
  have hyf := primeFiltration_map_of_le_ker φ Q.asIdeal hXK hdXq hdX xt
    (fun j ↦ φ (xt j)) (fun _ ↦ rfl) (fun j ↦ by
      have h := hwφf (Fin.natAdd b j)
      rwa [spanBefore_append_natAdd, Fin.append_right] at h)
  have hTK : Submodule.span R (Set.range (fun j ↦ φ (xt j))) ≤ LinearMap.ker ψ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ hmemψ (xt j))
  have hdYq : dVφ * e1 ∉ Q.asIdeal := Q.isPrime.mul_notMem hdVφq he1q
  have hdY : ∀ w ∈ LinearMap.ker ψ, (dVφ * e1) • w ∈
      Submodule.span R (Set.range (fun j ↦ φ (xt j))) := fun w hw ↦
    smul_mem_span_map_append_of_le_ker φ x xt hXK hdVφ' (hd1 w hw)
  have hfinψ : Module.length R (↥(LinearMap.ker ψ) ⧸
      (Submodule.span R (Set.range (fun j ↦ φ (xt j)))).submoduleOf (LinearMap.ker ψ)) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_submoduleOf_of_smul_mem Q hsupp _ _ hdYq hdY)
  obtain ⟨b', st, hstW, hstf, dVψ', hdVψ'q, hdVψ'⟩ :=
    exists_primeFiltration_quotient Q hQ hsupp
      (Submodule.span R (Set.range (fun j ↦ φ (xt j))))
      ((Submodule.span R (Set.range x)).comap ψ)
  have hwψ0f := primeFiltration_append_of_mkQ Q.asIdeal (fun j ↦ φ (xt j)) st hyf hstf
  have hVψ : Submodule.span R (Set.range (Fin.append (fun j ↦ φ (xt j)) st)) =
      Submodule.span R (Set.range (fun j ↦ φ (xt j))) ⊔ Submodule.span R (Set.range st) :=
    span_range_fin_append _ st
  have hdW : ∀ m : M, dX • m ∈ (Submodule.span R (Set.range x)).comap ψ := by
    intro m
    rw [Submodule.mem_comap, map_smul]
    exact hdX (ψ m) (hmemφ m)
  have hdVψq : dVψ' * dX ∉ Q.asIdeal := Q.isPrime.mul_notMem hdVψ'q hdXq
  have hdVψ : ∀ m : M, (dVψ' * dX) • m ∈
      Submodule.span R (Set.range (Fin.append (fun j ↦ φ (xt j)) st)) := by
    intro m
    rw [hVψ, mul_smul]
    exact hdVψ' (dX • m) (hdW m)
  have hsf := primeFiltration_map_of_le_ker ψ Q.asIdeal hTK hdYq hdY st
    (fun i ↦ ψ (st i)) (fun _ ↦ rfl) (fun j ↦ by
      have h := hwψ0f (Fin.natAdd a j)
      rwa [spanBefore_append_natAdd, Fin.append_right] at h)
  have hSX : Submodule.span R (Set.range (fun i ↦ ψ (st i))) ≤
      Submodule.span R (Set.range x) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hstW)
  have hdSq : dVψ' * dX * e0 ∉ Q.asIdeal := Q.isPrime.mul_notMem hdVψq he0q
  have hdS : ∀ w ∈ LinearMap.ker φ, (dVψ' * dX * e0) • w ∈
      Submodule.span R (Set.range (fun i ↦ ψ (st i))) := fun w hw ↦
    smul_mem_span_map_append_of_le_ker ψ _ st hTK hdVψ (hd0 w hw)
  have hfinφ : Module.length R (↥(LinearMap.ker φ) ⧸
      (Submodule.span R (Set.range (fun i ↦ ψ (st i)))).submoduleOf (LinearMap.ker φ)) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_submoduleOf_of_smul_mem Q hsupp _ _ hdSq hdS)
  have hfinVφ : IsFiniteLength R (M ⧸ Submodule.span R (Set.range (Fin.append x xt))) :=
    isFiniteLength_quotient_of_smul_mem Q hsupp _ hdVφq hdVφ'
  have hfinVψ : IsFiniteLength R
      (M ⧸ Submodule.span R (Set.range (Fin.append (fun j ↦ φ (xt j)) st))) :=
    isFiniteLength_quotient_of_smul_mem Q hsupp _ hdVψq hdVψ
  have hlenφ : Module.length (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl M) = b + a :=
    localized_length_eq_of_isFiniteLength_quotient_span Q.asIdeal hqm _ hwφf hfinVφ
  have hlenψ : Module.length (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl M) = a + b' :=
    localized_length_eq_of_isFiniteLength_quotient_span Q.asIdeal hqm _ hwψ0f hfinVψ
  obtain rfl : b = b' := by
    have h : b + a = a + b' := by exact_mod_cast hlenφ.symm.trans hlenψ
    omega
  obtain ⟨c, z, hzP, hzf, dZ, hdZq, hdZ⟩ :=
    exists_primeFiltration_submodule Q hQ hsupp
      (Submodule.span R (Set.range (Fin.append x xt)) ⊓
        Submodule.span R (Set.range (Fin.append (fun j ↦ φ (xt j)) st)))
  have hdPq : dVφ * (dVψ' * dX) ∉ Q.asIdeal := Q.isPrime.mul_notMem hdVφq hdVψq
  have hdP : ∀ m : M, (dVφ * (dVψ' * dX)) • m ∈
      Submodule.span R (Set.range (Fin.append x xt)) ⊓
        Submodule.span R (Set.range (Fin.append (fun j ↦ φ (xt j)) st)) := by
    intro m
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact hdVφ' _
    · rw [mul_comm, mul_smul]
      exact hdVψ _
  have hdZMq : dZ * (dVφ * (dVψ' * dX)) ∉ Q.asIdeal := Q.isPrime.mul_notMem hdZq hdPq
  have hdZM : ∀ m : M, (dZ * (dVφ * (dVψ' * dX))) • m ∈ Submodule.span R (Set.range z) := by
    intro m
    rw [mul_smul]
    exact hdZ _ (hdP m)
  have hfinZ' : IsFiniteLength R (M ⧸ Submodule.span R (Set.range z)) :=
    isFiniteLength_quotient_of_smul_mem Q hsupp _ hdZMq hdZM
  have hlenZ : Module.length (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl M) = c :=
    localized_length_eq_of_isFiniteLength_quotient_span Q.asIdeal hqm z hzf hfinZ'
  obtain rfl : c = b + a := by exact_mod_cast hlenZ.symm.trans hlenφ
  have hwψf := primeFiltration_cast (Nat.add_comm b a) Q.asIdeal
    (Fin.append (fun j ↦ φ (xt j)) st) hwψ0f
  have hZφ : Submodule.span R (Set.range z) ≤
      Submodule.span R (Set.range (Fin.append x xt)) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (hzP i).1)
  have hZψ : Submodule.span R (Set.range z) ≤
      Submodule.span R (Set.range (fun j : Fin (b + a) ↦
        Fin.append (fun k ↦ φ (xt k)) st (Fin.cast (Nat.add_comm b a) j))) := by
    rw [span_range_cast]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (hzP i).2)
  exact ⟨b, a, x, (fun j ↦ φ (xt j)), (fun j ↦ φ (xt j)), (fun i ↦ ψ (st i)), xt, st,
    Fin.append x xt,
    (fun j ↦ Fin.append (fun k ↦ φ (xt k)) st (Fin.cast (Nat.add_comm b a) j)), z,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl,
    hxf, hyf, hyf, hsf, hwφf, hwψf, hzf,
    hXK, hTK, hSX, le_rfl, hZφ, hZψ,
    hfinφ, hfinψ, hfinX, hfinψ, Module.length_ne_top_iff.mpr hfinZ'⟩

end AlgebraicGeometry

end

end
