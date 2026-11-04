module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.CandidateIdeal
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.DepthLocus
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.CandidateIdeal
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationDepthCollapse

/-!
# Uniform annihilation and the existence of the stabilizing data of Stacks 0EFI

Claim III of Stacks 0EFI, the uniform annihilation, through Faltings' annihilator theorem
Stacks 0EFC; the existence of a stabilizing pair given hypotheses (1)–(4) and `0 ≤ d`; and what
the conclusion of Stacks 0EFI amounts to, including the case `d < 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Topology TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-! ### Claim III of Stacks 0EFI: uniform annihilation -/

/-- Annihilators transport along an isomorphism of modules. -/
private theorem annihilator_le_of_isIso {A : Type u} [CommRing A] {X Y : ModuleCat.{w} A}
    (f : X ⟶ Y) [IsIso f] : Module.annihilator A X ≤ Module.annihilator A Y :=
  LinearMap.annihilator_le_of_injective (inv f).hom
    ((ModuleCat.mono_iff_injective (inv f)).mp inferInstance)

/-- The arithmetic step of Claim III: if the relative dimension is positive and `0 ≤ d`, then
`depth ≥ s` or `depth + dim > d + s` gives `depth + dim > s`. -/
private theorem depth_add_dimension_gt_of_depth_or_dimension_bound
    (s d : ℤ) (dep dimension : EInt) (hd : 0 ≤ d)
    (hdimension : (0 : EInt) < dimension)
    (h : dep ≥ (s : EInt) ∨ dep + dimension > ((d + s : ℤ) : EInt)) :
    dep + dimension > (s : EInt) := by
  have htop (a b : WithTop ℤ) (h : a = ⊤ ∨ b = ⊤) :
      (WithBot.some a : EInt) + WithBot.some b = ⊤ := by
    change WithBot.some (a + b) = _
    rcases h with rfl | rfl <;> simp
  cases dep using WithBotTop.rec with
  | bot =>
      rcases h with h | h
      · simp at h
      · simp at h
  | top =>
      cases dimension using WithBotTop.rec with
      | bot => simp at hdimension
      | coe n =>
          exact lt_of_lt_of_eq (lt_top_iff_ne_top.mpr (by simp)) (htop ⊤ n (Or.inl rfl)).symm
      | top =>
          exact lt_of_lt_of_eq (lt_top_iff_ne_top.mpr (by simp)) (htop ⊤ ⊤ (Or.inl rfl)).symm
  | coe x =>
      cases dimension using WithBotTop.rec with
      | bot => simp at hdimension
      | top =>
          exact lt_of_lt_of_eq (lt_top_iff_ne_top.mpr (by simp)) (htop x ⊤ (Or.inr rfl)).symm
      | coe y =>
          have hy : 0 < y := by
            change (0 : EInt) < (y : EInt) at hdimension
            exact WithBotTop.coe_lt_coe.mp hdimension
          show ((x + y : ℤ) : EInt) > (s : EInt)
          refine WithBotTop.coe_lt_coe.mpr ?_
          rcases h with h | h
          · have hx : (s : ℤ) ≤ x := WithBotTop.coe_le_coe.mp (by
              change (s : EInt) ≤ (x : EInt) at h
              exact h)
            omega
          · have hds : d + s < x + y := WithBotTop.coe_lt_coe.mp h
            omega

/-- **The hypothesis of Faltings' annihilator theorem, from hypotheses (3) and (4) of Stacks
0EFI.** For `𝔭` outside `T ∪ V(I)` and `𝔮 ∈ T` above `𝔭`, one has
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > s`.

If `depth(M_𝔭) ≥ s` this is the positivity of the relative dimension at a strict specialization.
If not, hypothesis (4) bounds `depth(M_𝔭) + dim((A/𝔭)_{𝔮'}) > d + s` along every
`𝔮' ∈ V(𝔭) ∩ V(J) ∩ V(I)`; one takes `𝔮' = 𝔮` when `𝔮 ∈ V(I)`, and in the other case the
specialization
supplied by hypothesis (3) at `𝔮`, whose relative dimension over `𝔮` is at most `d`. The
dimension function turns the comparison of the three relative dimensions into arithmetic. -/
private theorem depth_add_dimension_gt_of_stabilizationHypotheses
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega)
    (hd : 0 ≤ d) (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (p q : PrimeSpectrum A)
    (hp : p ∉ associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A))
    (hq : q ∈ associatedSubset I J) (hpq : p.asIdeal ≤ q.asIdeal) :
    enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) +
      krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt) := by
  have hpT : p ∉ associatedSubset I J := fun h => hp (Or.inl h)
  have hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A) := fun h => hp (Or.inr h)
  have hpne : p ≠ q := fun h => hpT (h ▸ hq)
  have hδpq : δ q < δ p :=
    δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes p q).mp hpq) hpne
  rw [krullDimToEInt_localization_quotient_eq_dimensionFunction δ p q hpq]
  by_cases hdepth : (s : EInt) ≤ enatToEInt
      (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M))
  · refine depth_add_dimension_gt_of_depth_or_dimension_bound s 0 _ _ le_rfl ?_ (Or.inl hdepth)
    exact WithBotTop.coe_lt_coe.mpr (by omega)
  have hdepth' := lt_of_not_ge hdepth
  obtain ⟨n, hn, -⟩ := (enatToEInt_le_intCast_iff _ s).mp hdepth'.le
  rw [hn]
  show (s : EInt) < (((n : ℤ) + (δ p - δ q) : ℤ) : EInt)
  refine WithBotTop.coe_lt_coe.mpr ?_
  have hbound := (H.depthOrDimensionBound p hpI hpT).resolve_left hdepth
  by_cases hqI : q ∈ PrimeSpectrum.zeroLocus (I : Set A)
  · have hqJ := (hq ⟨(show q.asIdeal ≤ q.asIdeal from le_rfl), hqI⟩).1
    have hb := hbound q ⟨⟨hpq, hqJ⟩, hqI⟩
    rw [hn, krullDimToEInt_localization_quotient_eq_dimensionFunction δ p q hpq] at hb
    have hb' : d + s < (n : ℤ) + (δ p - δ q) := WithBotTop.coe_lt_coe.mp hb
    omega
  · obtain ⟨r, hr, hrdim⟩ := H.dimensionBound q hqI hq
    have hpr : p.asIdeal ≤ r.asIdeal := hpq.trans hr.1.1
    have hb := hbound r ⟨⟨hpr, hr.1.2⟩, hr.2⟩
    rw [hn, krullDimToEInt_localization_quotient_eq_dimensionFunction δ p r hpr] at hb
    rw [krullDimToEInt_localization_quotient_eq_dimensionFunction δ q r hr.1.1] at hrdim
    have hb' : d + s < (n : ℤ) + (δ p - δ r) := WithBotTop.coe_lt_coe.mp hb
    have hr' : δ q - δ r ≤ d := WithBotTop.coe_le_coe.mp hrdim
    omega

/-- The closure of the part of a closed set outside `V(I)` stays inside a
specialization-stable set containing the closed set up to `V(I)`.

A closed subset of the spectrum minus a closed subset is closed in the constructible topology, so
every point of its closure specializes from a point of the set itself. -/
private theorem closure_diff_zeroLocus_subset
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I Q : Ideal A) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T)
    (hQ : PrimeSpectrum.zeroLocus (Q : Set A) ⊆
      T ∪ PrimeSpectrum.zeroLocus (I : Set A)) :
    closure (PrimeSpectrum.zeroLocus (Q : Set A) \
      PrimeSpectrum.zeroLocus (I : Set A)) ⊆ T := by
  have hIc := PrimeSpectrum.isClosed_zeroLocus (I : Set A)
  have hQc := PrimeSpectrum.isClosed_zeroLocus (Q : Set A)
  have hclosed : IsClosed[constructibleTopology (PrimeSpectrum A)]
      (PrimeSpectrum.zeroLocus (Q : Set A) \ PrimeSpectrum.zeroLocus (I : Set A)) := by
    apply @IsClosed.inter (PrimeSpectrum A) _ _ (constructibleTopology _)
    · exact hQc.isClosed_constructibleTopology
    · exact ((NoetherianSpace.isCompact _).isClopen_constructibleTopology
        hIc.isOpen_compl).1
  intro x hx
  obtain ⟨y, hy, hyx⟩ :=
    mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology hclosed hx
  exact hT hyx ((hQ hy.1).resolve_right hy.2)

/-- **The ideal juggling of Claim III.** Given an ideal `Q` whose zero locus lies in `T ∪ V(I)`,
there is an admissible shrinking `L` of `J₀` and an exponent `n` with `(L I) ^ n ≤ Q`.

One takes `L = J₀ ⊓ I(C)` for `C` the closure of `V(Q) \ V(I)`, which lies in `T` by
`closure_diff_zeroLocus_subset`; then `V(L I) = V(J₀) ∪ C ∪ V(I)` contains `V(Q)`, so `L I` lies
in the radical of `Q` and a power of it lies in `Q`. -/
private theorem exists_subideal_pow_mul_le_of_zeroLocus_subset
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J J₀ Q : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hQ : PrimeSpectrum.zeroLocus (Q : Set A) ⊆
      associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ (L : Ideal A) (n : ℕ), L ≤ J₀ ∧
      PrimeSpectrum.zeroLocus (L : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
      (L * I) ^ n ≤ Q := by
  let C := closure (PrimeSpectrum.zeroLocus (Q : Set A) \
    PrimeSpectrum.zeroLocus (I : Set A))
  have hCT : C ⊆ associatedSubset I J :=
    closure_diff_zeroLocus_subset I Q _ (associatedSubset_stableUnderSpecialization I J) hQ
  let L := J₀ ⊓ PrimeSpectrum.vanishingIdeal C
  have hL : PrimeSpectrum.zeroLocus (L : Set A) =
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∪ C := by
    simp only [L, PrimeSpectrum.zeroLocus_inf,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, C, closure_closure]
  have hLzero : PrimeSpectrum.zeroLocus (L : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro r ⟨hr, hrI⟩
      rw [hL] at hr
      rcases hr with hr | hr
      · exact hzero.subset ⟨hr, hrI⟩
      · exact hCT hr ⟨(show r.asIdeal ≤ r.asIdeal from le_rfl), hrI⟩
    · intro r hr
      exact ⟨hL.symm ▸ Or.inl (hzero.symm.subset hr).1, hr.2⟩
  have hrad : L * I ≤ Q.radical := by
    refine (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff Q (L * I)).mp ?_
    intro r hr
    rw [PrimeSpectrum.zeroLocus_mul, hL]
    by_cases hrI : r ∈ PrimeSpectrum.zeroLocus (I : Set A)
    · exact Or.inr hrI
    · exact Or.inl (Or.inr (subset_closure ⟨hr, hrI⟩))
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (L * I).fg_of_isNoetherianRing
  exact ⟨L, n, inf_le_left, hLzero, hn⟩

/-- `T ∪ V(I)` is stable under specialization. -/
private theorem associatedSubset_union_zeroLocus_stableUnderSpecialization
    {A : Type u} [CommRing A] (I J : Ideal A) :
    StableUnderSpecialization
      (associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A)) := by
  intro r t hrt hr
  rcases hr with hr | hr
  · exact Or.inl (associatedSubset_stableUnderSpecialization I J hrt hr)
  · exact Or.inr ((PrimeSpectrum.isClosed_zeroLocus (I : Set A)).stableUnderSpecialization
      hrt hr)

/-- **Faltings' annihilator theorem applied to Claim III.** For `0 ≤ s`, an ideal `J₀` cutting out
a subset of `T`, and the depth-dimension inequality of Stacks 0EFC along `V(J₀)`, there is an
ideal `Q` with `V(Q) ⊆ T ∪ V(I)` which annihilates `H^i_{J₀}(M)` in all degrees `i ≤ s`.

Stacks 0EFC is applied to the closed subset `V(J₀) ⊆ T ∪ V(I)`. Because `V(J₀)` is the zero locus
of an ideal, the local cohomology supported in it is `H^i_{J₀}(M)` through the comparison of the
two models, and no passage to a colimit over the ideals cutting out `T` is needed. -/
private theorem exists_annihilator_of_depth_add_dim_gt
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J J₀ : Ideal A) (s : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex omega) (hs : 0 ≤ s)
    (hJ₀T : PrimeSpectrum.zeroLocus (J₀ : Set A) ⊆ associatedSubset I J)
    (hgt : ∀ p q : PrimeSpectrum A,
      p ∉ associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A) →
      q ∈ PrimeSpectrum.zeroLocus (J₀ : Set A) → p.asIdeal ≤ q.asIdeal →
      enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt)) :
    ∃ Q : Ideal A,
      PrimeSpectrum.zeroLocus (Q : Set A) ⊆
        associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ i : ℤ, i ≤ s → Q ≤ Module.annihilator A
        (Stacks.LocalCohomology.localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing
          (ModuleCat.of A M) i) := by
  obtain ⟨Q, hQ, hQann⟩ :=
    (Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff A M
      (PrimeSpectrum.zeroLocus (J₀ : Set A))
      (associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A))
      (hJ₀T.trans Set.subset_union_left)
      (PrimeSpectrum.isClosed_zeroLocus (J₀ : Set A)).stableUnderSpecialization
      (associatedSubset_union_zeroLocus_stableUnderSpecialization I J)
      s hs omega homega).mpr hgt
  refine ⟨Q, hQ, fun i hi => (hQann i hi).trans ?_⟩
  exact annihilator_le_of_isIso
    (localCohomologyWithSupportInIsoObj.{u, u} A J₀ J₀.fg_of_isNoetherianRing
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i).hom

/-- **Faltings' annihilator theorem applied to Claim III.** For `0 ≤ s` and `0 ≤ d`, there is an
ideal `Q` with `V(Q) ⊆ T ∪ V(I)` which annihilates `H^i_{J₀}(M)` in all degrees `i ≤ s`.

Stacks 0EFC is applied to the closed subset `V(J₀) ⊆ T ∪ V(I)`; its hypothesis is
`depth_add_dimension_gt_of_stabilizationHypotheses`. Because `V(J₀)` is the zero locus of an
ideal, the local cohomology supported in it is `H^i_{J₀}(M)` through the comparison of the two
models, and no passage to a colimit over the ideals cutting out `T` is needed. -/
private theorem exists_annihilator_of_stabilizationHypotheses
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J J₀ : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hJ₀T : PrimeSpectrum.zeroLocus (J₀ : Set A) ⊆ associatedSubset I J) :
    ∃ Q : Ideal A,
      PrimeSpectrum.zeroLocus (Q : Set A) ⊆
        associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ i : ℤ, i ≤ s → Q ≤ Module.annihilator A
        (Stacks.LocalCohomology.localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing
          (ModuleCat.of A M) i) :=
  exists_annihilator_of_depth_add_dim_gt I J J₀ s omega H.dualizing hs hJ₀T
    (fun r t hr ht hrt => depth_add_dimension_gt_of_stabilizationHypotheses I J s d omega H hd
      (Dualizing.dualizingDimensionFunction omega H.dualizing) r t hr (hJ₀T ht) hrt)

/-! ### The existence statement in general -/

/-- **The three claims of Stacks 0EFI, assembled.** Given Claim I for the candidate ideal
`J₀ = J ⊓ I(B)` and the depth-dimension inequality of Faltings' annihilator theorem along `V(J₀)`,
a stabilizing pair exists.

Claim II needs no hypothesis, and Claim III is `exists_annihilator_of_depth_add_dim_gt` followed by
the ideal juggling of `exists_subideal_pow_mul_le_of_zeroLocus_subset`. -/
private theorem exists_isStabilizingData_of_depth_add_dim_gt
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) (hs : 0 ≤ s)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (hzero : PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hgt : ∀ p q : PrimeSpectrum A,
      p ∉ associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A) →
      q ∈ PrimeSpectrum.zeroLocus
        (stabilizingIdealCandidate (M := M) I J s : Set A) → p.asIdeal ≤ q.asIdeal →
      enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt)) :
    ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p := by
  have hbad := badLocus_subset_zeroLocus_stabilizingIdealCandidate (M := M) I J s
  have hJ₀T : PrimeSpectrum.zeroLocus
      (stabilizingIdealCandidate (M := M) I J s : Set A) ⊆ associatedSubset I J := fun r hr =>
    mem_associatedSubset_of_mem_zeroLocus_inter I J _ hzero r hr
  obtain ⟨Q, hQ, hQann⟩ := exists_annihilator_of_depth_add_dim_gt I J
    (stabilizingIdealCandidate (M := M) I J s) s omega homega hs hJ₀T hgt
  obtain ⟨L, n, hLJ₀, hLzero, hLQ⟩ := exists_subideal_pow_mul_le_of_zeroLocus_subset I J
    (stabilizingIdealCandidate (M := M) I J s) Q hzero hQ
  refine ⟨(L, n), hLJ₀.trans (stabilizingIdealCandidate_le I J s), hLzero, ?_, ?_⟩
  · exact isIso_localCohomologyComparison_of_badLocus_subset I J L s hLzero
      (hbad.trans (PrimeSpectrum.zeroLocus_anti_mono_ideal hLJ₀))
  · intro J' hJ'L hV i hi
    have hJ'J₀ : J' ≤ stabilizingIdealCandidate (M := M) I J s := hJ'L.trans hLJ₀
    have := isIso_localCohomologyComparison_of_badLocus_subset I J
      (stabilizingIdealCandidate (M := M) I J s) s hzero hbad J' hJ'J₀ hV i hi
    exact hLQ.trans ((hQann i hi).trans (annihilator_le_of_isIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (localCohomologyComparison A (stabilizingIdealCandidate (M := M) I J s) J'
          (stabilizingIdealCandidate (M := M) I J s).fg_of_isNoetherianRing
          J'.fg_of_isNoetherianRing hJ'J₀
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))))))

/-- **Stacks 0EFI.** Let `I` and `J` be ideals of a Noetherian ring `A`, let `M` be a finite
`A`-module, and let `s` and `d` be integers with `0 ≤ d`. Under hypotheses (1)–(4) of the source
there is a pair `(J₀, n)` with the stabilization property: `J₀ ≤ J` and
`V(J₀) ∩ V(I) = V(J) ∩ V(I)`, every further ideal `J' ≤ J₀` with `V(J') ∩ V(I) = V(J) ∩ V(I)` has
`RΓ_{J₀}(M) → RΓ_{J'}(M)` an isomorphism on cohomology in degrees `≤ s`, and `(J₀ I) ^ n`
annihilates all of those cohomology modules.

The proof is the source's. The ideal is `J ⊓ I(B)` for `B` the set of primes outside `V(I)` lying
in `T` at which the depth of `M` is at most `s`, shrunk once more at the end to absorb the
annihilator ideal; Claim I is the semicontinuity of `depth + δ`, Claim II the comparison criterion
Stacks 0DWV, and Claim III Faltings' annihilator theorem Stacks 0EFC.

`0 ≤ d` belongs to the statement of 0EFI: the source's wording omits it, uses it silently in
Claim III, and is false without it, by the counterexample
`Stacks.Algebraization.not_forall_exists_isStabilizingData_of_neg`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/StabilizationCounterexample.lean:451`). It is not
recorded by `Stacks.Algebraization.StabilizationHypotheses` and does not follow from it. See
`Stacks.Algebraization.exists_isStabilizingData_iff_of_neg` for what the conclusion amounts to
when `d < 0`, and the module docstring for the erratum. -/
@[stacks 0EFI "the existence of the stabilizing data, given hypotheses (1)-(4) and 0 ≤ d"]
public theorem exists_isStabilizingData
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ) (hd : 0 ≤ d)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p := by
  by_cases hs : s < 0
  · exact exists_isStabilizingData_of_nonpos I J s (le_of_lt hs)
  refine exists_isStabilizingData_of_depth_add_dim_gt I J s (le_of_not_gt hs) omega H.dualizing
    (zeroLocus_stabilizingIdealCandidate_inter I J s d omega H) fun p q hp hq hpq =>
      depth_add_dimension_gt_of_stabilizationHypotheses I J s d omega H hd
        (Dualizing.dualizingDimensionFunction omega H.dualizing) p q hp
        (zeroLocus_stabilizingIdealCandidate_subset_associatedSubset I J s d omega H hq) hpq

/-! ### What the conclusion of Stacks 0EFI amounts to, and the case `d < 0` -/

/-- **The conclusion of Stacks 0EFI forces the hypothesis of Faltings' annihilator theorem.**
If some pair has the stabilization property of Stacks 0EFI, then
`depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > s` for every `𝔭 ∉ T ∪ V(I)` and every `𝔮 ∈ V(J)` above it.

For a stabilizing pair `(J₀, n)` the ideal `(J₀ I) ^ n` is supported in `V(J₀) ∪ V(I) ⊆ T ∪ V(I)`
— each prime of `V(J₀)` lies in `T` because `V(J₀) ∩ V(I) = V(J) ∩ V(I)` — and annihilates
`H^i_{J₀}(M)`, hence `H^i_{V(J₀)}(M)`, for every `i ≤ s`. So the criterion Stacks 0EFC, which is
an equivalence, returns the inequality along `V(J₀) ⊇ V(J)`.

This is why the hypothesis `0 ≤ d` of `Stacks.Algebraization.exists_isStabilizingData` cannot be
dropped: the inequality is the content of the lemma, not an artifact of the route taken to it,
hypotheses (3) and (4) deliver it only through `depth + dim > d + s`, and at a negative `d` it
can fail — which is how the counterexample
`Stacks.Algebraization.not_forall_exists_isStabilizingData_of_neg` refutes the source's
unrestricted wording. -/
public theorem depth_add_dim_gt_of_isStabilizingData
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) (hs : 0 ≤ s)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (h : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p)
    (p q : PrimeSpectrum A)
    (hp : p ∉ associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A))
    (hq : q ∈ PrimeSpectrum.zeroLocus (J : Set A)) (hpq : p.asIdeal ≤ q.asIdeal) :
    enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) +
      krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt) := by
  obtain ⟨⟨J₀, n⟩, hdata⟩ := h
  have hJ₀T : PrimeSpectrum.zeroLocus (J₀ : Set A) ⊆ associatedSubset I J := fun r hr =>
    mem_associatedSubset_of_mem_zeroLocus_inter I J J₀ hdata.zeroLocus_inter r hr
  have hQ : PrimeSpectrum.zeroLocus (((J₀ * I) ^ n : Ideal A) : Set A) ⊆
      associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A) := by
    have hpow : PrimeSpectrum.zeroLocus (((J₀ * I) ^ n : Ideal A) : Set A) ⊆
        PrimeSpectrum.zeroLocus ((J₀ * I : Ideal A) : Set A) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact (PrimeSpectrum.zeroLocus_pow (J₀ * I) (by omega)).le
    refine (hpow.trans ?_)
    rw [PrimeSpectrum.zeroLocus_mul]
    exact Set.union_subset_union_left _ hJ₀T
  refine (Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff A M
      (PrimeSpectrum.zeroLocus (J₀ : Set A))
      (associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A))
      (hJ₀T.trans Set.subset_union_left)
      (PrimeSpectrum.isClosed_zeroLocus (J₀ : Set A)).stableUnderSpecialization
      (associatedSubset_union_zeroLocus_stableUnderSpecialization I J)
      s hs omega homega).mp ⟨(J₀ * I) ^ n, hQ, fun i hi => ?_⟩ p q hp
    ((show J₀ ≤ J from hdata.le).trans hq) hpq
  refine (hdata.pow_mul_le_annihilator J₀ le_rfl hdata.zeroLocus_inter i hi).trans (le_of_eq ?_)
  exact ((Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule A J₀
    J₀.fg_of_isNoetherianRing (ModuleCat.of A M) i).toLinearEquiv.annihilator_eq).symm

/-- **Stacks 0EFI for `d < 0`.** Under hypotheses (1)–(4) with a negative `d`, a stabilizing pair
exists exactly when `depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > s` for every `𝔭 ∉ T ∪ V(I)` and every
`𝔮 ∈ V(J)` above it.

At a negative `d` hypothesis (3) says that `T ⊆ V(I)`
(`associatedSubset_subset_zeroLocus_of_neg`), so the set `B` of the source is empty, the candidate
ideal cuts out `V(J)` exactly, and Claims I and II of the source hold with nothing assumed. What
remains is Claim III, and the displayed inequality is exactly what Faltings' annihilator theorem
needs for it; by `depth_add_dim_gt_of_isStabilizingData` it is also implied by the conclusion, so
no weaker condition would do.

The inequality does not follow from (1)–(4) when `d < 0`, since (4) then only bounds
`depth + dim` below by `d + s < s`, and it genuinely fails for some such data:
`Stacks.Algebraization.not_depth_add_dim_gt_semilocalLine`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/StabilizationCounterexample.lean:385`). This is
the obstruction described in the module docstring. -/
public theorem exists_isStabilizingData_iff_of_neg
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ) (hd : d < 0)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    (∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p) ↔
      ∀ p q : PrimeSpectrum A,
        p ∉ associatedSubset I J ∪ PrimeSpectrum.zeroLocus (I : Set A) →
        q ∈ PrimeSpectrum.zeroLocus (J : Set A) → p.asIdeal ≤ q.asIdeal →
        enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
          krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt) := by
  have hcand := zeroLocus_stabilizingIdealCandidate_of_neg I J s d hd omega H
  by_cases hs : s < 0
  · refine iff_of_true (exists_isStabilizingData_of_nonpos I J s (le_of_lt hs))
      fun p q _ _ hpq => ?_
    refine lt_enatToEInt_add_krullDimToEInt (Or.inl ⟨intCast_lt_enatToEInt_of_neg _ hs, ?_⟩)
    rw [ringKrullDim_localization_quotient_eq_height p q hpq]
    exact WithBot.coe_ne_bot
  refine ⟨fun h p q hp hq hpq => depth_add_dim_gt_of_isStabilizingData I J s (le_of_not_gt hs)
    omega H.dualizing h p q hp hq hpq, fun hgt => ?_⟩
  refine exists_isStabilizingData_of_depth_add_dim_gt I J s (le_of_not_gt hs) omega H.dualizing
    (by rw [hcand]) fun p q hp hq hpq => hgt p q hp (hcand ▸ hq) hpq

end Stacks.Algebraization

end
