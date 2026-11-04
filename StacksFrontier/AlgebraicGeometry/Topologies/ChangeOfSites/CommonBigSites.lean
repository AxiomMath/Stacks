module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.BigSite
public import StacksCore.Tactic.StacksAttribute

/-!
# A set-sized family of big sites has a common enlargement

A big Zariski, étale or fppf site is cut out of schemes by a size cutoff, and its covering
families are cut out by a further cardinal bound on their index types. Given a set-sized family
of such sites, both bounds can be enlarged simultaneously: there is a single big site of the
same kind whose cutoff and covering bound dominate those of every member of the family.

In particular that one site contains every object of every member, and every bounded covering
family of a member remains a bounded covering family in it.

## Main results

* `AlgebraicGeometry.exists_common_bigZariskiSite`,
  `AlgebraicGeometry.exists_common_bigEtaleSite`,
  `AlgebraicGeometry.exists_common_bigFppfSite` — a common enlargement, for each of the three
  topologies.
* `AlgebraicGeometry.isSite_etaleCutoff` — the étale covering families of the schemes below a
  size cutoff satisfy the site axioms.

## Implementation notes

The cutoff is produced by applying the size-cutoff construction to a cardinal dominating all
the given cutoffs; since the indexing type of the family is set-sized at the universe of the
schemes, that dominating cardinal can be taken to be a sum over a small model of the index
type, which is what `smallSumCardinal` is for. The covering bound is then the maximum of the
bound supplied by the set-sized-covering construction and the analogous sum of the given
bounds, and `covBounded_isSite_of_isSite` says that imposing a bound at least `ℵ₀` on a class
of covering families satisfying the site axioms leaves them satisfied.

The three site axioms for the covering families of a cutoff category are proved once, in
`isSite_of_cutoff_precoverage`, for the families whose image in schemes lies in a precoverage
with isomorphisms that is stable under composition and base change;
`AlgebraicGeometry.isSite_and_precoverage` is the general step, taken from
`StacksFrontier/AlgebraicGeometry/Topologies/ChangeOfSites/ChosenEtaleSite.lean`, and the three
topology-specific lemmas only supply those stability properties for the Zariski, étale and fppf
precoverages. The fibre products the base-change axiom needs come from the cutoff being closed
under them.

## References

* [Stacks Project, Tag 022J](https://stacks.math.columbia.edu/tag/022J)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace AlgebraicGeometry

/-- A cardinal dominating a family of cardinals indexed by a type that is small at the
universe of those cardinals: the sum over a small model of the index type. -/
private noncomputable def smallSumCardinal {ι : Type v} [Small.{u} ι]
    (f : ι → Cardinal.{u}) : Cardinal.{u} :=
  sum fun j : Shrink ι => f ((equivShrink ι).symm j)

private lemma le_smallSumCardinal {ι : Type v} [Small.{u} ι]
    (f : ι → Cardinal.{u}) (i : ι) : f i ≤ smallSumCardinal f := by
  show f i ≤ sum (fun j : Shrink ι => f ((equivShrink ι).symm j))
  simpa only [Equiv.symm_apply_apply] using
    (le_sum (fun j : Shrink ι => f ((equivShrink ι).symm j)) (equivShrink ι i))

private lemma sigma_card_le_of_le {κ : Cardinal.{u + 1}}
    (hκ : Cardinal.aleph0.{u + 1} ≤ κ)
    {I : Type (u + 1)} (hI : #I ≤ κ) {J : I → Type (u + 1)}
    (hJ : ∀ i, #(J i) ≤ κ) : #(Σ i, J i) ≤ κ := by
  calc
    #(Σ i, J i) = sum fun i => #(J i) := mk_sigma J
    _ ≤ #I * κ := (sum_le_sum _ _ hJ).trans (by simp [sum_const])
    _ ≤ κ * κ := mul_le_mul' hI le_rfl
    _ = κ := mul_eq_self hκ

/-- Imposing an infinite cardinal bound on the index types of a class of covering families
satisfying the site axioms leaves the axioms satisfied. -/
private lemma covBounded_isSite_of_isSite {C : Type (u + 1)} [Category.{u} C]
    {IsCov : Covering.{u + 1, u, u + 1} C → Prop} {κ : Cardinal.{u + 1}}
    (hsite : IsSite IsCov) (hκ : Cardinal.aleph0.{u + 1} ≤ κ) :
    IsSite (CovBounded IsCov κ) := by
  rcases hsite with ⟨hIso, hComp, hBC⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    refine ⟨hIso f, ?_⟩
    show #(PUnit.{u + 2}) ≤ κ
    rw [mk_punit]
    exact Cardinal.one_le_aleph0.trans hκ
  · intro 𝒰 h𝒰 𝒱 h𝒱 htargets
    choose h𝒱cov h𝒱card using h𝒱
    exact ⟨hComp 𝒰 h𝒰.1 𝒱 h𝒱cov htargets,
      sigma_card_le_of_le hκ h𝒰.2 h𝒱card⟩
  · intro 𝒰 h𝒰 V g
    obtain ⟨P, p₁, p₂, hp, hcov⟩ := hBC 𝒰 h𝒰.1 V g
    exact ⟨P, p₁, p₂, hp, hcov, h𝒰.2⟩

private lemma trivial_isSite {C : Type u} [Category.{v} C] [HasPullbacks C] :
    IsSite (fun _ : Covering.{u, v, max u v} C => True) := by
  refine ⟨fun _ => trivial, fun _ _ _ _ _ => trivial, ?_⟩
  intro 𝒰 _ V g
  refine ⟨fun i => pullback (𝒰.2.f i) g,
    (fun i => pullback.fst (𝒰.2.f i) g),
    (fun i => pullback.snd (𝒰.2.f i) g),
    (fun i => IsPullback.of_hasPullback (𝒰.2.f i) g), trivial⟩

/-- The families of a size-bounded category of schemes whose image lies in a precoverage with
isomorphisms, stable under composition and base change, satisfy the site axioms. -/
private lemma isSite_of_cutoff_precoverage {Q : Precoverage Scheme.{u}}
    [Precoverage.HasIsos Q] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    (κ : Cardinal.{u}) :
    IsSite (fun E : Covering.{u + 1, u, u + 1}
      (AlgebraicGeometry.SchemeBelow κ) =>
        (E.2.map (AlgebraicGeometry.schemeBelowInclusion κ)).presieve₀ ∈
          Q ((AlgebraicGeometry.schemeBelowInclusion κ).obj E.1)) := by
  have h := isSite_and_precoverage
    (AlgebraicGeometry.schemeBelowInclusion κ) (fun _ : Covering _ => True) Q
    trivial_isSite
  simpa using h

/-- A set-sized family of size cutoffs is dominated by one size cutoff. -/
private lemma exists_common_schemeCutoff {ι : Type v} [Small.{u} ι]
    (κ : ι → Cardinal.{u}) :
    ∃ K : Cardinal.{u}, ℵ₀ < K ∧ Cardinal.IsStrongPrelimit K ∧
      ℵ₀ < K.ord.cof ∧ ∀ i, κ i < K := by
  obtain ⟨K, hK, hstrong, hcof⟩ :=
    Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof
      (max ℵ₀ (smallSumCardinal κ))
  refine ⟨K, lt_of_le_of_lt (le_max_left _ _) hK, hstrong, hcof, fun i => ?_⟩
  exact lt_of_le_of_lt
    (le_trans (le_smallSumCardinal κ i) (le_max_right _ _)) hK

private lemma isSite_zariskiCutoff (κ : Cardinal.{u}) :
    IsSite (IsZariskiCovering (κ := κ)) := by
  let P : MorphismProperty Scheme.{u} := @IsOpenImmersion
  let Q := Scheme.zariskiPretopology.toPrecoverage
  have : MorphismProperty.IsStableUnderComposition P :=
    (inferInstance : MorphismProperty.IsMultiplicative P).toIsStableUnderComposition
  have : Q.IsStableUnderComposition :=
    schemePrecoverage_stableUnderComposition P
  have : Q.IsStableUnderBaseChange :=
    schemePrecoverage_stableUnderBaseChange P
  have : Precoverage.HasIsos Q := ⟨fun f _ ↦ Scheme.zariskiPretopology.has_isos f⟩
  have h := isSite_of_cutoff_precoverage (Q := Q) κ
  show IsSite (fun E =>
    (E.2.map (AlgebraicGeometry.schemeBelowInclusion κ)).presieve₀ ∈
      Scheme.zariskiPretopology E.1.1)
  simpa [Q, Scheme.zariskiPretopology] using h

/-- The étale covering families of the schemes of size below `κ` satisfy the site axioms. -/
public theorem isSite_etaleCutoff (κ : Cardinal.{u}) :
    IsSite (AlgebraicGeometry.IsEtaleCovering (κ := κ)) := by
  let P : MorphismProperty Scheme.{u} := @Etale
  have : MorphismProperty.IsStableUnderComposition P :=
    (inferInstance : MorphismProperty.IsMultiplicative P).toIsStableUnderComposition
  have : Scheme.etalePrecoverage.IsStableUnderComposition :=
    schemePrecoverage_stableUnderComposition P
  have : Scheme.etalePrecoverage.IsStableUnderBaseChange :=
    schemePrecoverage_stableUnderBaseChange P
  have : Precoverage.HasIsos Scheme.etalePrecoverage :=
    ⟨fun f _ ↦ Scheme.etalePretopology.has_isos f⟩
  have h := isSite_of_cutoff_precoverage (Q := Scheme.etalePrecoverage) κ
  show IsSite (fun E : Covering (AlgebraicGeometry.SchemeBelow κ) =>
    (E.2.map (AlgebraicGeometry.schemeBelowInclusion κ)).presieve₀ ∈
      Scheme.etalePrecoverage
        ((AlgebraicGeometry.schemeBelowInclusion κ).obj E.1))
  simpa [AlgebraicGeometry.IsEtaleCovering] using h

/-- The fppf covering families of `Sch_κ` satisfy the site axioms of Stacks 000X: the fppf
precoverage of schemes has isomorphisms, is stable under composition and under base change, so
its comap along the inclusion of `Sch_κ` — which is `AlgebraicGeometry.IsFppfCovering` — does
too.

Public because it is the input to every construction of a big fppf site with a prescribed
cutoff, not only to `AlgebraicGeometry.exists_common_bigFppfSite` below; see
`AlgebraicGeometry.BigFppfSite.exists_containing`. -/
public lemma isSite_fppfCutoff (κ : Cardinal.{u}) :
    IsSite (AlgebraicGeometry.IsFppfCovering (κ := κ)) := by
  let P : MorphismProperty Scheme.{u} :=
    @Flat ⊓ @LocallyOfFinitePresentation
  have : MorphismProperty.IsStableUnderBaseChange (@Flat) := inferInstance
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation) := inferInstance
  have : MorphismProperty.IsStableUnderBaseChange P := ⟨by
    intro X Y Y' S f g f' g' sq hg
    exact ⟨(inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@Flat)).of_isPullback sq hg.1,
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation)).of_isPullback sq hg.2⟩⟩
  have : MorphismProperty.IsStableUnderComposition P := ⟨fun f g hf hg =>
    ⟨MorphismProperty.comp_mem @Flat f g hf.1 hg.1,
      MorphismProperty.comp_mem @LocallyOfFinitePresentation f g hf.2 hg.2⟩⟩
  have : MorphismProperty.ContainsIdentities P := ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩⟩
  have : Precoverage.HasIsos Scheme.fppfPrecoverage := by
    unfold Scheme.fppfPrecoverage
    infer_instance
  have : Scheme.fppfPrecoverage.IsStableUnderComposition :=
    schemePrecoverage_stableUnderComposition P
  have : Scheme.fppfPrecoverage.IsStableUnderBaseChange :=
    schemePrecoverage_stableUnderBaseChange P
  have h := isSite_of_cutoff_precoverage (Q := Scheme.fppfPrecoverage) κ
  show IsSite (fun E : Covering (AlgebraicGeometry.SchemeBelow κ) =>
    E.2.presieve₀ ∈ Scheme.fppfPrecoverage.comap
      (AlgebraicGeometry.schemeBelowInclusion κ) E.1)
  simpa [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, PreZeroHypercover.map] using h

/-- A site of covering families of a cutoff category has a bounded refinement whose bound
dominates a given set-sized family of cardinals. -/
private theorem exists_covBounded_common_bound {ι : Type v} [Small.{u} ι] {κ : Cardinal.{u}}
    {IsCov : Covering.{u + 1, u, u + 1} (SchemeBelow κ) → Prop} (hsite : IsSite IsCov)
    (b : ι → Cardinal.{u + 1}) :
    ∃ (κcov : Cardinal.{u + 1}) (α : Ordinal.{u + 1}), Order.IsSuccLimit α ∧
      (∀ i, b i ≤ κcov) ∧ IsSite (CovBounded IsCov κcov) ∧
      ∀ U : Covering (SchemeBelow κ), IsCov U →
        ∃ U', CovBounded IsCov κcov U' ∧ Covering.CombEquiv U U' := by
  have : Small.{u + 1} ι := small_lift.{v, u + 1, u} ι
  obtain ⟨κ₀, α, hα, _, _, hrep⟩ := exists_covBounded_isSite IsCov hsite
    (∅ : Set (Covering.{u + 1, u, u + 1} (SchemeBelow κ))) (by intro U hU; cases hU)
  refine ⟨max ℵ₀ (max κ₀ (smallSumCardinal b)), α, hα,
    fun i => (le_smallSumCardinal b i).trans ((le_max_right _ _).trans (le_max_right _ _)),
    covBounded_isSite_of_isSite hsite (le_max_left _ _), fun U hU => ?_⟩
  exact (hrep U hU).imp fun _ ⟨hU', hcomb⟩ =>
    ⟨⟨hU'.1, hU'.2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩, hcomb⟩

/-- A set-sized family of big Zariski sites admits a common enlargement of both its scheme
cutoffs and covering-family bounds. -/
@[stacks 022J "big Zariski sites"]
public theorem exists_common_bigZariskiSite {ι : Type v} [Small.{u} ι]
    (B : ι → BigZariskiSite.{u}) :
    ∃ C : BigZariskiSite.{u},
      ∀ i, (B i).schemeCardinal ≤ C.schemeCardinal ∧
        (B i).coveringCardinal ≤ C.coveringCardinal := by
  classical
  obtain ⟨κ, hℵκ, hstrong, hcof, hκ⟩ :=
    exists_common_schemeCutoff (fun i => (B i).schemeCardinal)
  let IsCov := IsZariskiCovering (κ := κ)
  have hsite : IsSite IsCov := isSite_zariskiCutoff κ
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1}
      (AlgebraicGeometry.SchemeBelow κ)) := ∅
  obtain ⟨κcov, α, hα, hb, hcovsite, hrep'⟩ :=
    exists_covBounded_common_bound.{u, v} hsite fun i => (B i).coveringCardinal
  let C : BigZariskiSite :=
    { initialSchemes := ∅
      initialSchemes_small := inferInstance
      schemeCardinal := κ
      aleph0_lt_schemeCardinal := hℵκ
      schemeCardinal_isStrongPrelimit := hstrong
      aleph0_lt_schemeCardinal_cof := hcof
      initialSchemes_size_lt := by simp
      initialCoverings := Cov₀
      initialCoverings_small := inferInstance
      initialCoverings_among_initialSchemes := by simp [Cov₀]
      coveringCardinal := κcov
      coveringOrdinal := α
      coveringOrdinal_isSuccLimit := hα
      initialCoverings_mem := by simp [Cov₀]
      coverings_isSite := hcovsite
      covering_representative := hrep' }
  exact ⟨C, fun i => ⟨(hκ i).le, hb i⟩⟩

/-- A set-sized family of big fppf sites admits a common enlargement of both its scheme
cutoffs and covering-family bounds. -/
@[stacks 022J "big fppf sites"]
public theorem exists_common_bigFppfSite {ι : Type v} [Small.{u} ι]
    (B : ι → AlgebraicGeometry.BigFppfSite.{u}) :
    ∃ C : AlgebraicGeometry.BigFppfSite.{u},
      ∀ i, (B i).cutoff ≤ C.cutoff ∧ (B i).coveringBound ≤ C.coveringBound := by
  classical
  obtain ⟨κ, hℵκ, hstrong, hcof, hκ⟩ :=
    exists_common_schemeCutoff (fun i => (B i).cutoff)
  let IsCov := AlgebraicGeometry.IsFppfCovering (κ := κ)
  have hsite : IsSite IsCov := isSite_fppfCutoff κ
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1}
      (AlgebraicGeometry.SchemeBelow κ)) := ∅
  obtain ⟨κcov, α, hα, hb, hcovsite, hrep'⟩ :=
    exists_covBounded_common_bound.{u, v} hsite fun i => (B i).coveringBound
  let C : AlgebraicGeometry.BigFppfSite :=
    { initialSchemes := ∅
      initialSchemes_small := inferInstance
      cutoff := κ
      aleph0_lt_cutoff := hℵκ
      cutoff_isStrongPrelimit := hstrong
      aleph0_lt_cutoff_cof := hcof
      initialSchemes_mem := by simp
      initialCoverings := Cov₀
      initialCoverings_small := inferInstance
      initialCoverings_supported := by simp [Cov₀]
      coveringBound := κcov
      coveringOrdinal := α
      coveringOrdinal_isSuccLimit := hα
      initialCoverings_mem := by simp [Cov₀]
      coverings_isSite := hcovsite
      fppf_has_representative := hrep' }
  exact ⟨C, fun i => ⟨(hκ i).le, hb i⟩⟩

/-- A set-sized family of big étale sites admits a common enlargement of both its scheme
cutoffs and covering-family bounds. -/
@[stacks 022J "big étale sites"]
public theorem exists_common_bigEtaleSite {ι : Type v} [Small.{u} ι]
    (B : ι → AlgebraicGeometry.BigEtaleSite.{u}) :
    ∃ C : AlgebraicGeometry.BigEtaleSite.{u},
      ∀ i, (B i).cutoff ≤ C.cutoff ∧ (B i).coveringBound ≤ C.coveringBound := by
  classical
  obtain ⟨κ, hℵκ, hstrong, hcof, hκ⟩ :=
    exists_common_schemeCutoff (fun i => (B i).cutoff)
  let IsCov := AlgebraicGeometry.IsEtaleCovering (κ := κ)
  have hsite : IsSite IsCov := isSite_etaleCutoff κ
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1}
      (AlgebraicGeometry.SchemeBelow κ)) := ∅
  obtain ⟨κcov, α, hα, hb, hcovsite, hrep'⟩ :=
    exists_covBounded_common_bound.{u, v} hsite fun i => (B i).coveringBound
  let C : AlgebraicGeometry.BigEtaleSite :=
    { S₀ := ∅
      small_S₀ := inferInstance
      cutoff := κ
      aleph0_lt_cutoff := hℵκ
      cutoff_isStrongPrelimit := hstrong
      aleph0_lt_cutoff_cof := hcof
      mem_cutoff_of_mem := by simp
      initialCoverings := Cov₀
      small_initialCoverings := inferInstance
      initial_objects_mem := by simp [Cov₀]
      initialCoverings_etale := by simp [Cov₀]
      coveringBound := κcov
      coveringOrdinal := α
      coveringOrdinal_isSuccLimit := hα
      initialCoverings_bounded := by simp [Cov₀]
      coverings_isSite := hcovsite
      exists_covering_rep := hrep' }
  exact ⟨C, fun i => ⟨(hκ i).le, hb i⟩⟩

end AlgebraicGeometry
