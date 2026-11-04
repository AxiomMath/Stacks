module

public import StacksFrontier.RingTheory.Sequence.RegularLocus
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
public import StacksFrontier.RingTheory.RelativeDimension.BaseChange
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.Syntomic.Morphisms
public import StacksFrontier.RingTheory.MvPolynomial.MaximalIdeal
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.QuasiFinite.Locus
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence

/-!
# Descent of complete intersections and syntomic maps along directed colimits

This file proves descent theorems for an arbitrary directed system `(A_i → B_i)` of finitely
presented ring maps with cartesian transition squares and colimit `R → S`, used for
Lemma 0C33:

* if `R → S` is a relative global complete intersection, then so is some `A_i → B_i`. A
  presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` descends to a finitely presented model `T` over
  some `A_j`, and `B_μ = A_μ ⊗_{A_j} T` for `μ` large. What must be shown is that the fibres of
  `A_μ → B_μ` have dimension `n - c`. They have dimension at least `n - c` by Krull's height
  theorem. The locus where `dim_𝔮(B_i/A_i) ≤ n - c` is open (Lemma 00QH), is compatible with
  base change (Lemma 00QI) and contains the image of `Spec(S)`; its complement is cut out by an
  ideal generating the unit ideal of `S`, hence of some `B_μ`, over which the bound then holds
  everywhere;
* if `R → S` is syntomic, then it is a relative global complete intersection on a finite
  covering of `Spec(S)` by principal opens `D(g_j)` (Lemma 00SY). The localized systems
  `(A_i → (B_i)_{g_j})` satisfy the same hypotheses, so each `(B_i)_{g_j}` is eventually a
  relative global complete intersection, the `g_j` eventually generate the unit ideal of `B_i`,
  and `A_i → B_i` is then syntomic.

## Main results

* `Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_relativeDimensionAt_add_le`: a
  presentation with `n` variables and `c` relations whose relative dimensions are at most
  `n - c` is a relative global complete intersection.
* `Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_of_directed`,
  `Algebra.Syntomic.exists_stage_of_directed`: descent along cartesian directed systems.

## References

* [Stacks Project, Tag 0C33](https://stacks.math.columbia.edu/tag/0C33)
-/

@[expose] public section

universe u

open scoped TensorProduct

/-! ### Fibre dimensions of presentations -/

/-- **Fibres of a presentation have dimension at least `n - c`.** If a nonzero algebra `T` over a
field `K` is presented as `K[x_1, …, x_n]/(f_1, …, f_c)`, then `n ≤ dim T + c`: a maximal ideal of
`K[x_1, …, x_n]` containing the `f_k` has height `n`, and by Krull's height theorem its image in
the quotient has height at least `n - c`. -/
theorem Algebra.Presentation.natCast_le_ringKrullDim_add_natCard {K T : Type*} [Field K]
    [CommRing T] [Algebra K T] [Nontrivial T] {n : ℕ} {σ : Type*} [Finite σ]
    (P : Algebra.Presentation K T (Fin n) σ) :
    (n : WithBot ℕ∞) ≤ ringKrullDim T + Nat.card σ := by
  have : Nontrivial (P.Ring ⧸ P.ker) := P.quotientEquiv.symm.injective.nontrivial
  have hker : P.ker ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hker
  have h1 := Ideal.height_le_ringKrullDim_quotient_add_encard (p := m) (Set.range P.relation)
    (by rwa [← Ideal.span_le, P.span_range_relation_eq_ker])
  rw [height_maximal_ideal_eq n m hm, P.span_range_relation_eq_ker,
    ringKrullDim_eq_of_ringEquiv P.quotientEquiv.toRingEquiv] at h1
  refine h1.trans (add_le_add_right ?_ _)
  have : (Set.range P.relation).encard ≤ Nat.card σ := by
    rw [← ENat.card_eq_coe_natCard]
    rw [← Set.image_univ, ← Set.encard_univ]
    exact Set.encard_image_le _ _
  exact_mod_cast this

/-- **A criterion for a relative global complete intersection.** A presentation
`S = R[x_1, …, x_n]/(f_1, …, f_c)` is a relative global complete intersection as soon as
`dim_𝔮(S/R) + c ≤ n` at every prime `𝔮` of `S`: the fibres then have dimension at most `n - c`,
and every nonempty fibre has dimension at least `n - c` by Krull's height theorem. -/
theorem Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_relativeDimensionAt_add_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n c : ℕ}
    (P : Algebra.Presentation R S (Fin n) (Fin c))
    (h : ∀ (q : Ideal S) [q.IsPrime], Algebra.relativeDimensionAt R q + c ≤ n) :
    P.IsRelativeGlobalCompleteIntersection := by
  refine ⟨fun p _ hnt => le_antisymm ?_ ?_⟩
  · obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (p.Fiber S)
    set q := Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S)
    have hunder : q.under R = p := by
      refine Eq.trans ?_ (Ideal.over_def Q p).symm
      ext r
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
        AlgHom.commutes]
    have hcn : c ≤ n := by
      have h0 : (0 : WithBot ℕ∞) ≤ Algebra.relativeDimensionAt R q := by
        rw [Algebra.relativeDimensionAt, topologicalKrullDimAt]
        refine le_iInf fun U ↦ ?_
        have hne : topologicalKrullDim U ≠ ⊥ := by
          rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
          exact fun h ↦ h.elim ⟨_, U.2.1⟩
        obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hne
        rw [← hy]
        exact WithBot.coe_le_coe.mpr zero_le
      have := (add_le_add_left h0 (c : WithBot ℕ∞)).trans (h q)
      rw [zero_add] at this
      exact_mod_cast this
    have hle := Algebra.ringKrullDim_fiber_le_of_relativeDimensionAt_le (S := S) p
      (N := ((n - c : ℕ) : WithBot ℕ∞)) fun q _ _ => WithBot.le_natCast_sub_of_add_le (h q)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
    calc ringKrullDim (p.Fiber S) + c ≤ ((n - c : ℕ) : WithBot ℕ∞) + c := by gcongr
      _ = n := by norm_cast; omega
  · have := (P.baseChange p.ResidueField).natCast_le_ringKrullDim_add_natCard
    simpa [Nat.card_eq_fintype_card, Fintype.card_fin] using this

/-- A polynomial over a directed colimit of rings comes from a polynomial over some stage. -/
theorem MvPolynomial.exists_map_eq_of_directed {ι σ : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] {A : ι → Type*} [∀ i, CommRing (A i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) {R : Type*} [CommRing R] (ρ : ∀ i, A i →+* R)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hρs : ∀ r, ∃ i x, ρ i x = r)
    (p : MvPolynomial σ R) : ∃ i, ∃ q : MvPolynomial σ (A i), MvPolynomial.map (ρ i) q = p := by
  have hmap (i j : ι) (h : i ≤ j) (q : MvPolynomial σ (A i)) :
      MvPolynomial.map (ρ j) (MvPolynomial.map (a i j h) q) = MvPolynomial.map (ρ i) q := by
    rw [MvPolynomial.map_map, show (ρ j).comp (a i j h) = ρ i from RingHom.ext (hρ i j h)]
  induction p using MvPolynomial.induction_on with
  | C r =>
    obtain ⟨i, x, rfl⟩ := hρs r
    exact ⟨i, MvPolynomial.C x, by simp⟩
  | add p q hp hq =>
    obtain ⟨i, p', rfl⟩ := hp
    obtain ⟨j, q', rfl⟩ := hq
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨k, MvPolynomial.map (a i k hik) p' + MvPolynomial.map (a j k hjk) q', by
      rw [map_add, hmap, hmap]⟩
  | mul_X p s hp =>
    obtain ⟨i, p', rfl⟩ := hp
    exact ⟨i, p' * MvPolynomial.X s, by simp⟩

/-- If an ideal of a stage of a directed system becomes the unit ideal in the colimit, it already
is the unit ideal at some later stage. -/
private theorem exists_map_eq_top_of_directed {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] {B : ι → Type*} [∀ i, CommRing (B i)] (b : ∀ i j, i ≤ j → B i →+* B j)
    [DirectedSystem B fun i j h => b i j h] {S : Type*} [CommRing S] (σ : ∀ i, B i →+* S)
    (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x) (hσs : ∀ s, ∃ i x, σ i x = s)
    (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0) {μ : ι} (J : Ideal (B μ))
    (hJ : J.map (σ μ) = ⊤) : ∃ ν, ∃ h : μ ≤ ν, J.map (b μ ν h) = ⊤ := by
  classical
  obtain ⟨k, s, x, hx⟩ := Submodule.mem_span_set'.mp (hJ ▸ Submodule.mem_top (x := (1 : S)))
  choose x' hx'J hx' using fun t => (x t).2
  choose ν' hμν' y hy using fun t =>
    Module.Flat.DirectedModel.exists_ge_rep b σ hσ hσs μ (s t)
  obtain ⟨ν, hν⟩ := (insert μ (Finset.univ.image ν')).exists_le
  have hμν : μ ≤ ν := hν μ (Finset.mem_insert_self _ _)
  have hν'ν (t : Fin k) : ν' t ≤ ν :=
    hν _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
  let z : B ν := ∑ t, b (ν' t) ν (hν'ν t) (y t) * b μ ν hμν (x' t)
  have hz : σ ν (z - 1) = 0 := by
    simp only [z, map_sub, map_sum, map_mul, hσ, hy, map_one, hx', ← hx, smul_eq_mul, sub_self]
  obtain ⟨ν₁, hνν₁, hν₁⟩ := hσz ν _ hz
  refine ⟨ν₁, hμν.trans hνν₁, (Ideal.eq_top_iff_one _).mpr ?_⟩
  rw [map_sub, map_one, sub_eq_zero] at hν₁
  rw [← hν₁]
  simp only [z, map_sum, map_mul]
  refine Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ ?_
  rw [DirectedSystem.map_map' (fun i j h => b i j h)]
  exact Ideal.mem_map_of_mem _ (hx'J t)

open Module.Flat.DirectedModel in
/-- **Relative global complete intersections descend along directed colimits.** Let
`(A_i → B_i)` be a directed system of finitely presented ring maps with cartesian transition
squares (`B_j = A_j ⊗_{A_i} B_i`), whose colimit is `R → S`. If `R → S` is a relative global
complete intersection, then so is some `A_i → B_i`.

A presentation of `S` with `n` variables and `c` relations descends to a presentation of a
finitely presented `A_j`-algebra `T` with `S = R ⊗_{A_j} T`, and `B_μ = A_μ ⊗_{A_j} T` for `μ`
large. The locus where `dim_𝔮(B_i/A_i) + c ≤ n` is open (Lemma 00QH), is compatible with base
change (Lemma 00QI) and contains the image of `Spec(S)`, so it is all of `Spec(B_μ)` for `μ`
large, and the presentation of `B_μ` is then a relative global complete intersection. -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_of_directed
    {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {A B : ι → Type u} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
    [DirectedSystem A fun i j h => a i j h] [DirectedSystem B fun i j h => b i j h]
    (hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
    (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)
    (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) = (algebraMap R S).comp (ρ i))
    (hρs : ∀ r, ∃ i x, ρ i x = r) (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    (hσs : ∀ s, ∃ i x, σ i x = s) (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0)
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    (hfp : ∀ i, Algebra.FinitePresentation (A i) (B i))
    [Algebra.IsRelativeGlobalCompleteIntersection R S] :
    ∃ i, Algebra.IsRelativeGlobalCompleteIntersection (A i) (B i) := by
  classical
  obtain ⟨n, c, P, hP⟩ := ‹Algebra.IsRelativeGlobalCompleteIntersection R S›.out
  -- the fibres of `R → S` have dimension `n - c`
  have hcol (q : Ideal S) [q.IsPrime] : Algebra.relativeDimensionAt R q + c ≤ n := by
    have hnt : Nontrivial ((q.under R).Fiber S) := by
      obtain ⟨Q, hQ, -⟩ := Ideal.Fiber.exists_comap_includeRight_eq q (q.under R) rfl
      exact ⟨0, 1, fun h => hQ.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ Q.zero_mem))⟩
    have h := hP.ringKrullDim_fiber_add_card_eq_card (q.under R) hnt
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    calc _ ≤ ringKrullDim ((q.under R).Fiber S) + c := by
          gcongr; exact Algebra.relativeDimensionAt_le_ringKrullDim_fiber q
      _ = n := h
  -- relative dimension is preserved along the cartesian transition maps
  have htr {μ ν : ι} (h : μ ≤ ν) (q : PrimeSpectrum (B ν)) :
      Algebra.relativeDimensionAt (A ν) q.asIdeal =
        Algebra.relativeDimensionAt (A μ) (Ideal.comap (b μ ν h) q.asIdeal) := by
    let := algebraA a h
    let := algebraB b h
    let := algebraAB (B := B) a h
    have : IsScalarTower (A μ) (A ν) (B ν) := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower (A μ) (B μ) (B ν) := .of_algebraMap_eq' (hab μ ν h).symm
    have : Algebra.IsPushout (A μ) (A ν) (B μ) (B ν) :=
      CommRingCat.isPushout_iff_isPushout.mp (hpush μ ν h)
    have : Algebra.IsPushout (A μ) (B μ) (A ν) (B ν) := this.symm
    have := hfp μ
    exact (Algebra.IsPushout.relativeDimensionAt_comap_eq (A μ) (B μ) (A ν) (B ν) q).symm
  -- and from a stage to the colimit
  have htrS (μ : ι) (q : PrimeSpectrum S) :
      Algebra.relativeDimensionAt R q.asIdeal =
        Algebra.relativeDimensionAt (A μ) (Ideal.comap (σ μ) q.asIdeal) := by
    let : Algebra (A μ) R := (ρ μ).toAlgebra
    let : Algebra (B μ) S := (σ μ).toAlgebra
    let : Algebra (A μ) S := ((algebraMap R S).comp (ρ μ)).toAlgebra
    have : IsScalarTower (A μ) R S := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower (A μ) (B μ) S := .of_algebraMap_eq' (hρσ μ).symm
    have : Algebra.IsPushout (A μ) R (B μ) S :=
      isPushout_colimit a b hab ρ σ hρ hσ hpush hρσ hρs hσs hσz μ rfl rfl
    have : Algebra.IsPushout (A μ) (B μ) R S := this.symm
    have := hfp μ
    exact (Algebra.IsPushout.relativeDimensionAt_comap_eq (A μ) (B μ) R S q).symm
  -- the bound on relative dimensions at a stage
  let Bd : ι → Prop := fun ν =>
    ∀ q : PrimeSpectrum (B ν), Algebra.relativeDimensionAt (A ν) q.asIdeal + c ≤ n
  have hBd_mono {μ ν : ι} (h : μ ≤ ν) (hμ : Bd μ) : Bd ν := fun q => by
    rw [htr h q]
    exact hμ (PrimeSpectrum.comap (b μ ν h) q)
  have hBd : ∃ ν, Bd ν := by
    obtain ⟨μ⟩ := ‹Nonempty ι›
    have := hfp μ
    set U := {q : PrimeSpectrum (B μ) | Algebra.relativeDimensionAt (A μ) q.asIdeal + c ≤ n}
    have hU : IsOpen U := Algebra.isOpen_setOf_relativeDimensionAt_add_le c n
    let J := PrimeSpectrum.vanishingIdeal Uᶜ
    have hZ : PrimeSpectrum.zeroLocus J = Uᶜ := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.isClosed_compl.closure_eq]
    have hJ : J.map (σ μ) = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      have h1 : PrimeSpectrum.comap (σ μ) ⟨m, hm.isPrime⟩ ∈ PrimeSpectrum.zeroLocus J :=
        Ideal.map_le_iff_le_comap.mp hle
      rw [hZ] at h1
      apply h1
      show Algebra.relativeDimensionAt (A μ) (Ideal.comap (σ μ) m) + c ≤ n
      rw [← htrS μ ⟨m, hm.isPrime⟩]
      exact hcol m
    obtain ⟨ν, hμν, hJ₁⟩ := exists_map_eq_top_of_directed b σ hσ hσs hσz J hJ
    refine ⟨ν, fun q => ?_⟩
    rw [htr hμν q]
    by_contra hq
    have h1 : PrimeSpectrum.comap (b μ ν hμν) q ∈ PrimeSpectrum.zeroLocus J := by
      rwa [hZ]
    have h2 : J.map (b μ ν hμν) ≤ q.asIdeal := Ideal.map_le_iff_le_comap.mpr h1
    exact q.2.ne_top (top_le_iff.mp (hJ₁ ▸ h2))
  -- descend the presentation to a stage `j`
  choose i' f' hf' using fun k => MvPolynomial.exists_map_eq_of_directed a ρ hρ hρs (P.relation k)
  obtain ⟨j, hj⟩ := (Finset.univ.image i').exists_le
  have hij (k : Fin c) : i' k ≤ j := hj _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  let f : Fin c → MvPolynomial (Fin n) (A j) := fun k =>
    MvPolynomial.map (a (i' k) j (hij k)) (f' k)
  have hf (k : Fin c) : MvPolynomial.map (ρ j) (f k) = P.relation k := by
    rw [← hf' k, MvPolynomial.map_map,
      show (ρ j).comp (a (i' k) j (hij k)) = ρ (i' k) from RingHom.ext (hρ _ _ _)]
  let T := MvPolynomial (Fin n) (A j) ⧸ Ideal.span (Set.range f)
  let : Algebra (A j) R := (ρ j).toAlgebra
  let : Algebra (A j) S := ((algebraMap R S).comp (ρ j)).toAlgebra
  have : IsScalarTower (A j) R S := .of_algebraMap_eq fun _ => rfl
  let φT : T →+* S := Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (algebraMap (A j) S) P.val)
    (by
      intro p hp
      refine (Ideal.span_le.mpr ?_ : Ideal.span (Set.range f) ≤ RingHom.ker _) hp
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom,
        show algebraMap (A j) S = (algebraMap R S).comp (ρ j) from rfl, ← MvPolynomial.eval₂_map,
        hf k]
      exact P.aeval_val_relation k)
  let : Algebra T S := φT.toAlgebra
  have : @IsScalarTower (A j) T S Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun x => (MvPolynomial.eval₂_C _ _ _).symm
  have hpushT : Algebra.IsPushout (A j) R T S :=
    P.isPushout_quotient_of_map_eq f hf fun _ => MvPolynomial.eval₂_X _ _ _
  have : Algebra.FinitePresentation (A j) T :=
    (Algebra.Presentation.naive (v := f)).finitePresentation_of_isFinite
  obtain ⟨i₁, hji₁, χ₁, hχS, hχA⟩ :=
    exists_lift_stage a b hab ρ σ hρ hσ hρσ hσs hσz T (i₀ := j) fun _ => rfl
  obtain ⟨ν, hν⟩ := hBd
  obtain ⟨i₂, hi₁₂, hν₂⟩ := exists_ge_ge i₁ ν
  let χ₂ := (b i₁ i₂ hi₁₂).comp χ₁
  have hχS₂ : (σ i₂).comp χ₂ = algebraMap T S := by
    rw [← hχS]
    exact RingHom.ext fun x => hσ _ _ _ _
  have hχA₂ : χ₂.comp (algebraMap (A j) T) =
      (algebraMap (A i₂) (B i₂)).comp (a j i₂ (hji₁.trans hi₁₂)) := by
    refine RingHom.ext fun x => ?_
    have h1 := DFunLike.congr_fun hχA x
    have h2 := DFunLike.congr_fun (hab i₁ i₂ hi₁₂) (a j i₁ hji₁ x)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    show b i₁ i₂ hi₁₂ (χ₁ (algebraMap (A j) T x)) = _
    rw [h1, h2, DirectedSystem.map_map' (fun i j h => a i j h)]
  obtain ⟨μ, hμ, hmodel⟩ := exists_isStageModel a b hab ρ σ hρ hσ hρσ hσs hσz hρs hρz hpush hfp
    T rfl (hji₁.trans hi₁₂) χ₂ hχS₂ hχA₂
  refine ⟨μ, ?_⟩
  let := algebraA a ((hji₁.trans hi₁₂).trans hμ)
  let := algebraAB (B := B) a ((hji₁.trans hi₁₂).trans hμ)
  let := ((b i₂ μ hμ).comp χ₂).toAlgebra
  have : IsScalarTower (A j) (A μ) (B μ) := .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower (A j) T (B μ) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun x => by
      have h1 := DFunLike.congr_fun hχA₂ x
      have h2 := DFunLike.congr_fun (hab i₂ μ hμ) (a j i₂ (hji₁.trans hi₁₂) x)
      simp only [RingHom.comp_apply] at h1 h2
      show _ = b i₂ μ hμ (χ₂ (algebraMap (A j) T x))
      rw [h1, h2, DirectedSystem.map_map' (fun i j h => a i j h)]
      rfl
  have : Algebra.IsPushout (A j) (A μ) T (B μ) := hmodel
  let P' := ((Algebra.Presentation.naive (v := f)).baseChange (A μ)).ofAlgEquiv
    (Algebra.IsPushout.equiv (A j) (A μ) T (B μ))
  have := P'.isRelativeGlobalCompleteIntersection_of_relativeDimensionAt_add_le
    fun q _ => hBd_mono (hν₂.trans hμ) hν ⟨q, inferInstance⟩
  exact .of_presentation P'

/-- Localization away from an element is compatible with pushout squares. -/
theorem Algebra.IsPushout.localizationAway {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R S R' S']
    (g : S) (Sg S'g : Type*) [CommRing Sg] [CommRing S'g] [Algebra S Sg] [IsLocalization.Away g Sg]
    [Algebra S' S'g] [IsLocalization.Away (algebraMap S S' g) S'g] [Algebra Sg S'g]
    [Algebra S S'g] [IsScalarTower S Sg S'g] [IsScalarTower S S' S'g] [Algebra R Sg]
    [IsScalarTower R S Sg] [Algebra R' S'g] [Algebra R S'g] [IsScalarTower R' S' S'g]
    [IsScalarTower R Sg S'g] [IsScalarTower R R' S'g] [IsScalarTower R S' S'g] :
    Algebra.IsPushout R Sg R' S'g := by
  have : IsLocalization (Algebra.algebraMapSubmonoid S' (Submonoid.powers g)) S'g := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact ‹IsLocalization.Away (algebraMap S S' g) S'g›
  have h1 : Algebra.IsPushout S S' Sg S'g :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers g) Sg).mp this
  exact (Algebra.IsPushout.comp_iff R S R' (T := Sg) (S' := S') (T' := S'g)).mpr h1.symm

/-- In a directed system with cartesian transition squares, localizing away from `g` and from its
image `g'` again gives a pushout square. -/
private theorem isPushout_away_map {ι : Type*} [Preorder ι] {A B : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
    (hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    {μ ν : ι} (h : μ ≤ ν) (g : B μ) (g' : B ν) (hg : b μ ν h g = g')
    (hle : Submonoid.powers g ≤ (Submonoid.powers g').comap (b μ ν h)) :
    CategoryTheory.IsPushout (CommRingCat.ofHom (a μ ν h))
      (CommRingCat.ofHom (algebraMap (A μ) (Localization.Away g)))
      (CommRingCat.ofHom (algebraMap (A ν) (Localization.Away g')))
      (CommRingCat.ofHom (IsLocalization.map (Localization.Away g') (b μ ν h) hle)) := by
  let := Module.Flat.DirectedModel.algebraA a h
  let := Module.Flat.DirectedModel.algebraB b h
  let := Module.Flat.DirectedModel.algebraAB (B := B) a h
  have : @IsScalarTower (A μ) (A ν) (B ν) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower (A μ) (B μ) (B ν) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq' (hab μ ν h).symm
  have : Algebra.IsPushout (A μ) (B μ) (A ν) (B ν) :=
    (CommRingCat.isPushout_iff_isPushout.mp (hpush μ ν h)).symm
  let : Algebra (Localization.Away g) (Localization.Away g') :=
    (IsLocalization.map (Localization.Away g') (b μ ν h) hle).toAlgebra
  have : @IsScalarTower (B μ) (Localization.Away g) (Localization.Away g')
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun x => (IsLocalization.map_eq hle x).symm
  have : @IsScalarTower (B μ) (B ν) (Localization.Away g') Algebra.toSMul Algebra.toSMul
      Algebra.toSMul := .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower (A μ) (A ν) (Localization.Away g') Algebra.toSMul Algebra.toSMul
      Algebra.toSMul := .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower (A μ) (Localization.Away g) (Localization.Away g')
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := .of_algebraMap_eq fun x => by
    change _ = IsLocalization.map _ (b μ ν h) hle
      (algebraMap (B μ) (Localization.Away g) (algebraMap (A μ) (B μ) x))
    rw [IsLocalization.map_eq]
    exact congrArg (algebraMap (B ν) _) (DFunLike.congr_fun (hab μ ν h) x).symm
  have : @IsScalarTower (A μ) (B ν) (Localization.Away g') Algebra.toSMul Algebra.toSMul
      Algebra.toSMul := .of_algebraMap_eq fun _ => rfl
  have : IsLocalization.Away (algebraMap (B μ) (B ν) g) (Localization.Away g') := by
    rw [show algebraMap (B μ) (B ν) g = g' from hg]
    infer_instance
  exact CommRingCat.isPushout_iff_isPushout.mpr
    (Algebra.IsPushout.localizationAway (R := A μ) (S := B μ) (R' := A ν) (S' := B ν) g _ _).symm

open Module.Flat.DirectedModel in
/-- **Descent for principal localizations.** In the situation of
`Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_of_directed`, let `g ∈ B_{i₁}`. If
`S_g` is a relative global complete intersection over `R`, then so is `(B_μ)_g` over `A_μ` for
some `μ ≥ i₁`: the localized system `(A_i → (B_i)_g)` again satisfies the hypotheses. -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_away_of_directed
    {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {A B : ι → Type u} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
    [DirectedSystem A fun i j h => a i j h] [DirectedSystem B fun i j h => b i j h]
    (hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
    (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)
    (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) = (algebraMap R S).comp (ρ i))
    (hρs : ∀ r, ∃ i x, ρ i x = r) (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    (hσs : ∀ s, ∃ i x, σ i x = s) (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0)
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    (hfp : ∀ i, Algebra.FinitePresentation (A i) (B i)) {i₁ : ι} (g : B i₁)
    [Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away (σ i₁ g))] :
    ∃ μ, ∃ h : i₁ ≤ μ,
      Algebra.IsRelativeGlobalCompleteIntersection (A μ) (Localization.Away (b i₁ μ h g)) := by
  classical
  let gg (j : Tail i₁) : B j.1 := b i₁ j.1 j.2 g
  have hgg {j k : Tail i₁} (h : j ≤ k) : b j.1 k.1 h (gg j) = gg k :=
    DirectedSystem.map_map' (fun i j h => b i j h) j.2 h g
  have hle {j k : Tail i₁} (h : j ≤ k) :
      Submonoid.powers (gg j) ≤ (Submonoid.powers (gg k)).comap (b j.1 k.1 h) := by
    rw [Submonoid.powers_le]
    exact ⟨1, by simp [hgg h]⟩
  let b' (j k : Tail i₁) (h : j ≤ k) :
      Localization.Away (gg j) →+* Localization.Away (gg k) :=
    IsLocalization.map _ (b j.1 k.1 h) (hle h)
  have hb'alg {j k : Tail i₁} (h : j ≤ k) (x : B j.1) :
      b' j k h (algebraMap (B j.1) _ x) = algebraMap (B k.1) _ (b j.1 k.1 h x) :=
    IsLocalization.map_eq _ _
  have : DirectedSystem (fun j : Tail i₁ => Localization.Away (gg j)) fun j k h => b' j k h := by
    constructor
    · intro j x
      exact DFunLike.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (gg j))
        (j := b' j j le_rfl) (k := RingHom.id _) (RingHom.ext fun y => by
          simp [hb'alg, DirectedSystem.map_self' (fun i j h => b i j h)])) x
    · intro l k j hjk hkl x
      exact DFunLike.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (gg j))
        (j := (b' k l hkl).comp (b' j k hjk)) (k := b' j l (hjk.trans hkl)) (RingHom.ext fun y => by
          simp [hb'alg, DirectedSystem.map_map' (fun i j h => b i j h)])) x
  let Sg := Localization.Away (σ i₁ g)
  have hσg (j : Tail i₁) : σ j.1 (gg j) = σ i₁ g := hσ _ _ _ g
  have hleσ (j : Tail i₁) :
      Submonoid.powers (gg j) ≤ (Submonoid.powers (σ i₁ g)).comap (σ j.1) := by
    rw [Submonoid.powers_le]
    exact ⟨1, by simp [hσg j]⟩
  let σ' (j : Tail i₁) : Localization.Away (gg j) →+* Sg := IsLocalization.map _ (σ j.1) (hleσ j)
  have hσ'alg (j : Tail i₁) (x : B j.1) :
      σ' j (algebraMap (B j.1) _ x) = algebraMap S Sg (σ j.1 x) := IsLocalization.map_eq _ _
  have halgA (j : Tail i₁) (x : A j.1) : algebraMap (A j.1) (Localization.Away (gg j)) x =
      algebraMap (B j.1) _ (algebraMap (A j.1) (B j.1) x) := IsScalarTower.algebraMap_apply _ _ _ _
  have hab' (j k : Tail i₁) (h : j ≤ k) :
      (b' j k h).comp (algebraMap (A j.1) (Localization.Away (gg j))) =
        (algebraMap (A k.1) (Localization.Away (gg k))).comp (a j.1 k.1 h) :=
      RingHom.ext fun x => by
    simp only [RingHom.comp_apply, halgA, hb'alg]
    rw [← RingHom.comp_apply (b j.1 k.1 h), hab]
    rfl
  have hσ' (j k : Tail i₁) (h : j ≤ k) (x : Localization.Away (gg j)) :
      σ' k (b' j k h x) = σ' j x := by
    have := IsLocalization.ringHom_ext (Submonoid.powers (gg j))
      (j := (σ' k).comp (b' j k h)) (k := σ' j) (RingHom.ext fun y => by
        simp [hb'alg, hσ'alg, hσ])
    exact DFunLike.congr_fun this x
  have hρσ' (j : Tail i₁) : (σ' j).comp (algebraMap (A j.1) (Localization.Away (gg j))) =
      (algebraMap R Sg).comp (ρ j.1) := RingHom.ext fun x => by
    simp only [RingHom.comp_apply, halgA, hσ'alg]
    rw [← RingHom.comp_apply (σ j.1), hρσ, IsScalarTower.algebraMap_apply R S Sg]
    rfl
  have hρs' (r : R) : ∃ (j : Tail i₁) (x : A j.1), ρ j.1 x = r := by
    obtain ⟨j, hj, x, hx⟩ := exists_ge_rep a ρ hρ hρs i₁ r
    exact ⟨⟨j, hj⟩, x, hx⟩
  have hρz' (j : Tail i₁) (x : A j.1) (hx : ρ j.1 x = 0) :
      ∃ (k : Tail i₁) (h : j ≤ k), a j.1 k.1 h x = 0 := by
    obtain ⟨k, hk, hk'⟩ := hρz j.1 x hx
    exact ⟨⟨k, j.2.trans hk⟩, hk, hk'⟩
  have hσs' (s : Sg) : ∃ (j : Tail i₁) (x : Localization.Away (gg j)), σ' j x = s := by
    obtain ⟨⟨y, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (σ i₁ g)) s
    obtain ⟨j, hj, y', rfl⟩ := exists_ge_rep b σ hσ hσs i₁ y
    refine ⟨⟨j, hj⟩,
      IsLocalization.mk' _ y' ⟨gg ⟨j, hj⟩ ^ m, pow_mem (Submonoid.mem_powers _) m⟩, ?_⟩
    rw [IsLocalization.map_mk']
    congr 1
    apply Subtype.ext
    show σ j (gg ⟨j, hj⟩ ^ m) = σ i₁ g ^ m
    rw [map_pow, hσg ⟨j, hj⟩]
  have hσz' (j : Tail i₁) (x : Localization.Away (gg j)) (hx : σ' j x = 0) :
      ∃ (k : Tail i₁) (h : j ≤ k), b' j k h x = 0 := by
    obtain ⟨⟨y, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (gg j)) x
    rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨_, e, rfl⟩, he⟩ := hx
    have : σ j.1 (gg j ^ e * y) = 0 := by simpa [hσg] using he
    obtain ⟨k, hk, hk'⟩ := hσz j.1 _ this
    refine ⟨⟨k, j.2.trans hk⟩, hk, ?_⟩
    rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨_, e, rfl⟩, ?_⟩
    rwa [map_mul, map_pow, hgg (k := ⟨k, j.2.trans hk⟩) hk] at hk'
  have hpush' (j k : Tail i₁) (h : j ≤ k) : CategoryTheory.IsPushout
      (CommRingCat.ofHom (a j.1 k.1 h))
      (CommRingCat.ofHom (algebraMap (A j.1) (Localization.Away (gg j))))
      (CommRingCat.ofHom (algebraMap (A k.1) (Localization.Away (gg k))))
      (CommRingCat.ofHom (b' j k h)) :=
    isPushout_away_map a b hab hpush h (gg j) (gg k) (hgg h) (hle h)
  have hfp' (j : Tail i₁) : Algebra.FinitePresentation (A j.1) (Localization.Away (gg j)) := by
    have := hfp j.1
    exact Algebra.FinitePresentation.trans (A j.1) (B j.1) _
  have : DirectedSystem (fun j : Tail i₁ => A j.1) fun j k h => a j.1 k.1 h :=
    ⟨fun _ x => DirectedSystem.map_self' (fun i j h => a i j h) x,
      fun _ _ _ hjk hkl x => DirectedSystem.map_map' (fun i j h => a i j h) hjk hkl x⟩
  obtain ⟨j, hj⟩ := Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_of_directed
    (A := fun j : Tail i₁ => A j.1) (B := fun j => Localization.Away (gg j))
    (fun j k h => a j.1 k.1 h) b' hab' (R := R) (S := Sg) (fun j => ρ j.1) σ'
    (fun j k h x => hρ j.1 k.1 h x) hσ' hρσ' hρs' hρz' hσs' hσz' hpush' hfp'
  exact ⟨j.1, j.2, hj⟩
open Module.Flat.DirectedModel in
/-- In a directed system with cartesian transition squares, if `(B_μ)_g` is a relative global
complete intersection over `A_μ`, then so is `(B_ν)_g` over `A_ν` for `ν ≥ μ`, by base change
(Lemma 00SS). -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.away_of_le
    {ι : Type*} [Preorder ι] {A B : ι → Type u} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra (A i) (B i)] (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
    (hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    {μ ν : ι} (h : μ ≤ ν) (g : B μ)
    [Algebra.IsRelativeGlobalCompleteIntersection (A μ) (Localization.Away g)] :
    Algebra.IsRelativeGlobalCompleteIntersection (A ν) (Localization.Away (b μ ν h g)) := by
  let := algebraA a h
  let := algebraAB (B := B) a h
  have hle : Submonoid.powers g ≤ (Submonoid.powers (b μ ν h g)).comap (b μ ν h) := by
    rw [Submonoid.powers_le]; exact ⟨1, by simp⟩
  let φ : Localization.Away g →+* Localization.Away (b μ ν h g) := IsLocalization.map _ _ hle
  let : Algebra (Localization.Away g) (Localization.Away (b μ ν h g)) := φ.toAlgebra
  have : @IsScalarTower (A μ) (A ν) (Localization.Away (b μ ν h g)) Algebra.toSMul Algebra.toSMul
      Algebra.toSMul := .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower (A μ) (Localization.Away g) (Localization.Away (b μ ν h g)) Algebra.toSMul
      Algebra.toSMul Algebra.toSMul := .of_algebraMap_eq fun x => by
    change _ = φ (algebraMap (B μ) (Localization.Away g) (algebraMap (A μ) (B μ) x))
    rw [IsLocalization.map_eq]
    exact congrArg (algebraMap (B ν) _) (DFunLike.congr_fun (hab μ ν h) x).symm
  have : Algebra.IsPushout (A μ) (Localization.Away g) (A ν) (Localization.Away (b μ ν h g)) :=
    (CommRingCat.isPushout_iff_isPushout.mp
      (isPushout_away_map a b hab hpush h g _ rfl hle)).symm
  exact Algebra.IsRelativeGlobalCompleteIntersection.baseChange (A μ) (Localization.Away g) (A ν) _

open Module.Flat.DirectedModel in
/-- **Syntomic ring maps descend along directed colimits.** In the situation of
`Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_of_directed`, if `R → S` is syntomic,
then so is some `A_i → B_i`: cover `S` by principal opens `D(g_j)` over which it is a relative
global complete intersection (Lemma 00SY), descend each of them, and conclude by locality. -/
theorem Algebra.Syntomic.exists_stage_of_directed
    {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {A B : ι → Type u} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) (b : ∀ i j, i ≤ j → B i →+* B j)
    [DirectedSystem A fun i j h => a i j h] [DirectedSystem B fun i j h => b i j h]
    (hab : ∀ i j (h : i ≤ j),
      (b i j h).comp (algebraMap (A i) (B i)) = (algebraMap (A j) (B j)).comp (a i j h))
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
    (hσ : ∀ i j (h : i ≤ j) x, σ j (b i j h x) = σ i x)
    (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) = (algebraMap R S).comp (ρ i))
    (hρs : ∀ r, ∃ i x, ρ i x = r) (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    (hσs : ∀ s, ∃ i x, σ i x = s) (hσz : ∀ i x, σ i x = 0 → ∃ j, ∃ h : i ≤ j, b i j h x = 0)
    (hpush : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
      (CommRingCat.ofHom (algebraMap (A i) (B i))) (CommRingCat.ofHom (algebraMap (A j) (B j)))
      (CommRingCat.ofHom (b i j h)))
    (hfp : ∀ i, Algebra.FinitePresentation (A i) (B i)) [Algebra.Syntomic R S] :
    ∃ i, Algebra.Syntomic (A i) (B i) := by
  classical
  obtain ⟨m, c, x, hx⟩ := Submodule.mem_span_set'.mp
    (Algebra.Syntomic.span_setOf_isRelativeGlobalCompleteIntersection_eq_top (R := R) (S := S) ▸
      Submodule.mem_top (x := (1 : S)))
  choose νg g hg using fun t => hσs (x t).1
  obtain ⟨i₁, hi₁⟩ := (Finset.univ.image νg).exists_le
  have hg₁ (t : Fin m) : νg t ≤ i₁ :=
    hi₁ _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  let ĝ (t : Fin m) : B i₁ := b (νg t) i₁ (hg₁ t) (g t)
  have hĝ (t : Fin m) : σ i₁ (ĝ t) = (x t).1 := (hσ _ _ _ _).trans (hg t)
  have hJ : (Ideal.span (Set.range ĝ)).map (σ i₁) = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    rw [← hx]
    refine Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ ?_
    rw [← hĝ t]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨t, rfl⟩)
  obtain ⟨i₂, hi₁₂, hi₂⟩ := exists_map_eq_top_of_directed b σ hσ hσs hσz _ hJ
  have hμ (t : Fin m) : ∃ μ, ∃ h : i₁ ≤ μ,
      Algebra.IsRelativeGlobalCompleteIntersection (A μ) (Localization.Away (b i₁ μ h (ĝ t))) := by
    have : Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away (σ i₁ (ĝ t))) := by
      rw [hĝ t]; exact (x t).2
    exact Algebra.IsRelativeGlobalCompleteIntersection.exists_stage_away_of_directed a b hab ρ σ
      hρ hσ hρσ hρs hρz hσs hσz hpush hfp (ĝ t)
  choose μ hμ₁ hμ using hμ
  obtain ⟨ν, hν⟩ := (insert i₂ (Finset.univ.image μ)).exists_le
  have hi₂ν : i₂ ≤ ν := hν _ (Finset.mem_insert_self _ _)
  have hμν (t : Fin m) : μ t ≤ ν :=
    hν _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
  refine ⟨ν, Algebra.Syntomic.of_span_eq_top_of_isRelativeGlobalCompleteIntersection
    (Set.range fun t => b i₁ ν (hi₁₂.trans hi₂ν) (ĝ t)) ?_ ?_⟩
  · have h1 := congrArg (Ideal.map (b i₂ ν hi₂ν)) hi₂
    rw [Ideal.map_map, Ideal.map_top, Ideal.map_span, ← Set.range_comp] at h1
    simpa [Function.comp_def, DirectedSystem.map_map' (fun i j h => b i j h)] using h1
  · rintro _ ⟨t, rfl⟩
    have := hμ t
    have := Algebra.IsRelativeGlobalCompleteIntersection.away_of_le a b hab hpush (hμν t)
      (b i₁ (μ t) (hμ₁ t) (ĝ t))
    rwa [DirectedSystem.map_map' (fun i j h => b i j h)] at this
