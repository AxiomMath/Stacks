module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Valuative.Specialization
public import StacksFrontier.Examples.Scheme.PuncturedAxes

/-!
# A quasi-compact quasi-separated scheme with no separated quasi-compact dense open

Glue two copies of the spectrum of the coordinate ring of the countable union of coordinate axes
along the basic open where the zeroth coordinate is invertible. The result is quasi-compact and
quasi-separated, but it has no open subscheme that is at once separated, quasi-compact and
dense.

Indeed, a dense quasi-compact open either omits one of the two images of the origin — and then
it cuts out a quasi-compact dense open of a punctured spectrum of the union of the axes, which
does not exist — or it contains both, and then it is not separated: the two charts agree on the
glueing locus, so the valuation ring witnessing the specialization of the generic point of the
zeroth axis to the origin maps into the open in two ways that agree on a dense open subscheme
of its spectrum yet differ at its closed point.

## Main results

* `Stacks.Examples.exists_qcqs_without_separated_quasiCompact_dense_open`: such a scheme.

## Implementation notes

Quasi-compactness of a scheme is `CompactSpace` and quasi-separatedness is
`QuasiSeparatedSpace`; for an open subscheme `V`, `IsCompact (V : Set X)` is its
quasi-compactness and `Scheme.IsSeparated V` its separatedness. The glueing data has two charts
indexed by `ULift (Fin 2)`, with no triple overlaps to specify, so it is given as a
`CategoryTheory.GlueData'` and converted. The equations describing the resulting `V`, `f` and
`t` on a two-element index set are recorded as the lemmas `glueData_V_eq_chart`,
`glueData_V_eq_U`, `glueData_f_eq` and `glueData_t_comp_eqToHom`, and the inclusion of the
glueing locus into a chart is given the name `chartInc`, so that every composite below is
syntactically well typed rather than only well typed up to unfolding the conversion. The
construction lives in the namespace `Stacks.Examples.DoubledAxes`.

## References

* [Stacks Project, Tag 086I](https://stacks.math.columbia.edu/tag/086I)
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Examples.DoubledAxes

open Stacks.Examples

/-- The basic open of the spectrum of the union of the axes where the zeroth coordinate is
invertible; the two copies are glued along it. -/
private noncomputable def puncturedAxisChart (k : Type u) [Field k] :
    (Spec (.of (puncturedAxisRing k))).Opens :=
  PrimeSpectrum.basicOpen (axisQuotientMap k (MvPolynomial.X 0))

private lemma noThreeDistinctCharts (i j l : ULift.{u} (Fin 2))
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  rcases l with ⟨l⟩
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

/-- The glueing data of two copies of the spectrum of the union of the axes, in the form that
prescribes the intersections only for distinct indices. -/
private noncomputable def preGlueData (k : Type u) [Field k] :
    CategoryTheory.GlueData' Scheme.{u} where
  J := ULift.{u} (Fin 2)
  U _ := Spec (.of (puncturedAxisRing k))
  V _ _ _ := (puncturedAxisChart k).toScheme
  f _ _ _ := (puncturedAxisChart k).ι
  f_hasPullback := by intros; infer_instance
  t _ _ _ := 𝟙 _
  t' i j l hij hil hjl := (noThreeDistinctCharts i j l hij hil hjl).elim
  t_fac i j l hij hil hjl := (noThreeDistinctCharts i j l hij hil hjl).elim
  t_inv := by intros; simp
  cocycle i j l hij hil hjl := (noThreeDistinctCharts i j l hij hil hjl).elim

/-- The glueing data of two copies of the spectrum of the union of the axes, glued along the
chart where the zeroth coordinate is invertible. -/
private noncomputable def glueData (k : Type u) [Field k] : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (preGlueData k)
  f_open i j := by
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', preGlueData]
    split_ifs <;> infer_instance

/-- At distinct indices the intersection of the glueing data is the glueing locus. -/
private lemma glueData_V_eq_chart (k : Type u) [Field k] {i j : (glueData k).J} (hij : i ≠ j) :
    (glueData k).V (i, j) = (puncturedAxisChart k).toScheme :=
  dite_eq_right hij

/-- At equal indices the intersection of the glueing data is the whole chart. -/
private lemma glueData_V_eq_U (k : Type u) [Field k] (i : (glueData k).J) :
    (glueData k).V (i, i) = Spec (.of (puncturedAxisRing k)) :=
  dite_eq_left rfl

/-- The inclusion of the glueing locus into the `i`-th chart of the glueing data. -/
private noncomputable def chartInc (k : Type u) [Field k] (i : (glueData k).J) :
    (puncturedAxisChart k).toScheme ⟶ (glueData k).U i := (puncturedAxisChart k).ι

private lemma glueData_f_eq (k : Type u) [Field k] {i j : (glueData k).J} (hij : i ≠ j) :
    (glueData k).f i j = eqToHom (glueData_V_eq_chart k hij) ≫ chartInc k i :=
  dite_eq_right hij

private lemma glueData_t_eq (k : Type u) [Field k] {i j : (glueData k).J} (hij : i ≠ j) :
    (glueData k).t i j = eqToHom (glueData_V_eq_chart k hij) ≫ 𝟙 _ ≫
      eqToHom (glueData_V_eq_chart k hij.symm).symm :=
  dite_eq_right hij

private lemma glueData_t_comp_eqToHom (k : Type u) [Field k] {i j : (glueData k).J}
    (hij : i ≠ j) :
    (glueData k).t i j ≫ eqToHom (glueData_V_eq_chart k hij.symm) =
      eqToHom (glueData_V_eq_chart k hij) := by
  rw [glueData_t_eq k hij]
  simp

/-- The index of the `i`-th chart in the glueing data. -/
private noncomputable def chartIdx (k : Type u) [Field k] (i : Fin 2) : (glueData k).J :=
  ULift.up i

private lemma chartIdx_down (k : Type u) [Field k] (i : Fin 2) :
    ULift.down (chartIdx k i) = i := rfl

private lemma chartIdx_injective (k : Type u) [Field k] {i j : Fin 2}
    (h : chartIdx k i = chartIdx k j) : i = j :=
  congrArg ULift.down h

private lemma chartIdx_ne (k : Type u) [Field k] : chartIdx k 0 ≠ chartIdx k 1 :=
  fun h => absurd (chartIdx_injective k h) (by decide)

/-- The scheme obtained by glueing two copies of the spectrum of the union of the axes. -/
private noncomputable abbrev scheme (k : Type u) [Field k] : Scheme.{u} := (glueData k).glued

/-- The `i`-th of the two charts of the glued scheme. -/
private noncomputable def chart (k : Type u) [Field k] (i : Fin 2) :
    Spec (.of (puncturedAxisRing k)) ⟶ scheme k := (glueData k).ι (chartIdx k i)

private instance chart_isOpenImmersion (k : Type u) [Field k] (i : Fin 2) :
    IsOpenImmersion (chart k i) := (glueData k).ι_isOpenImmersion (chartIdx k i)

private lemma charts_agree_aux (k : Type u) [Field k] :
    chartInc k (chartIdx k 0) ≫ (glueData k).ι (chartIdx k 0) =
      chartInc k (chartIdx k 1) ≫ (glueData k).ι (chartIdx k 1) := by
  have hidx := chartIdx_ne k
  have htransition : (glueData k).t (chartIdx k 0) (chartIdx k 1) ≫
      (glueData k).f (chartIdx k 1) (chartIdx k 0) =
      eqToHom (glueData_V_eq_chart k hidx) ≫ chartInc k (chartIdx k 1) := by
    rw [glueData_f_eq k hidx.symm, ← Category.assoc, glueData_t_comp_eqToHom k hidx]
  have hcancel : eqToHom (glueData_V_eq_chart k hidx) ≫
      chartInc k (chartIdx k 1) ≫ (glueData k).ι (chartIdx k 1) =
      eqToHom (glueData_V_eq_chart k hidx) ≫
        chartInc k (chartIdx k 0) ≫ (glueData k).ι (chartIdx k 0) := by
    rw [← Category.assoc, ← htransition, Category.assoc,
      (glueData k).glue_condition (chartIdx k 0) (chartIdx k 1), glueData_f_eq k hidx,
      Category.assoc]
  exact ((cancel_epi (eqToHom (glueData_V_eq_chart k hidx))).1 hcancel).symm

/-- The two charts of the glued scheme agree on the glueing locus. -/
private lemma charts_agree_as_morphisms (k : Type u) [Field k] :
    (puncturedAxisChart k).ι ≫ chart k 0 = (puncturedAxisChart k).ι ≫ chart k 1 :=
  charts_agree_aux k

/-- The two images of the origin in the glued scheme are distinct. -/
private lemma origins_ne (k : Type u) [Field k] :
    chart k 0 (axisOrigin k) ≠ chart k 1 (axisOrigin k) := by
  have hidx := chartIdx_ne k
  intro h
  obtain ⟨z, hz, -⟩ := ((glueData k).ι_eq_iff (chartIdx k 0) (chartIdx k 1)
    (axisOrigin k) (axisOrigin k)).mp h
  rw [glueData_f_eq k hidx] at hz
  have hz' : (puncturedAxisChart k).ι (eqToHom (glueData_V_eq_chart k hidx) z) =
      axisOrigin k := hz
  have hmem : axisOrigin k ∈ puncturedAxisChart k := by
    rw [← hz']
    exact (eqToHom (glueData_V_eq_chart k hidx) z).property
  exact axisOrigin_notMem_basicOpen k 0 hmem

private lemma puncturedAxisChart_compact (k : Type u) [Field k] :
    CompactSpace ((puncturedAxisChart k).toScheme) := by
  change CompactSpace
    (↑(puncturedAxisChart k : Set (Spec (.of (puncturedAxisRing k)))))
  exact isCompact_iff_compactSpace.mp (PrimeSpectrum.isCompact_basicOpen _)

private lemma chart_intersection_compact (k : Type u) [Field k] (i j : Fin 2) :
    IsCompact (((chart k i).opensRange : Set (scheme k)) ∩
      ((chart k j).opensRange : Set (scheme k))) := by
  have hcompact : CompactSpace ((glueData k).V (chartIdx k i, chartIdx k j)) := by
    by_cases hij : i = j
    · subst j
      rw [glueData_V_eq_U k (chartIdx k i)]
      infer_instance
    · have hne : chartIdx k i ≠ chartIdx k j := fun h => hij (chartIdx_injective k h)
      rw [glueData_V_eq_chart k hne]
      exact puncturedAxisChart_compact k
  have hrange : IsCompact (Set.range ((glueData k).f (chartIdx k i) (chartIdx k j) ≫
      (glueData k).ι (chartIdx k i))) := isCompact_range (Scheme.Hom.continuous _)
  have hset : Set.range ((glueData k).f (chartIdx k i) (chartIdx k j) ≫
      (glueData k).ι (chartIdx k i)) =
      (((glueData k).ι (chartIdx k i)).opensRange : Set (scheme k)) ∩
        (((glueData k).ι (chartIdx k j)).opensRange : Set (scheme k)) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨(glueData k).f (chartIdx k i) (chartIdx k j) z, rfl⟩,
        ⟨(glueData k).f (chartIdx k j) (chartIdx k i)
          ((glueData k).t (chartIdx k i) (chartIdx k j) z), ?_⟩⟩
      have hg := congrArg (fun f => f z)
        ((glueData k).glue_condition (chartIdx k i) (chartIdx k j))
      change (glueData k).ι (chartIdx k j) ((glueData k).f (chartIdx k j) (chartIdx k i)
        ((glueData k).t (chartIdx k i) (chartIdx k j) z)) =
        (glueData k).ι (chartIdx k i)
          ((glueData k).f (chartIdx k i) (chartIdx k j) z) at hg
      simpa only [Scheme.Hom.comp_apply] using hg
    · rintro ⟨⟨xi, hxi⟩, ⟨xj, hxj⟩⟩
      obtain ⟨z, hfz, -⟩ := ((glueData k).ι_eq_iff (chartIdx k i) (chartIdx k j) xi xj).mp
        (hxi.trans hxj.symm)
      exact ⟨z, by rw [Scheme.Hom.comp_apply, hfz, hxi]⟩
  exact hset ▸ hrange

private lemma scheme_compact (k : Type u) [Field k] : CompactSpace (scheme k) := by
  have hcover : (Set.univ : Set (scheme k)) =
      Set.range (chart k 0) ∪ Set.range (chart k 1) := by
    ext x
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    obtain ⟨⟨i⟩, y, hy⟩ := (glueData k).ι_jointly_surjective x
    fin_cases i
    exacts [Or.inl ⟨y, hy⟩, Or.inr ⟨y, hy⟩]
  exact isCompact_univ_iff.mp (hcover ▸ (isCompact_range (Scheme.Hom.continuous (chart k 0))).union
    (isCompact_range (Scheme.Hom.continuous (chart k 1))))

private lemma scheme_quasiSeparated (k : Type u) [Field k] :
    QuasiSeparatedSpace (scheme k) := by
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun i : Fin 2 => (chart k i).opensRange) ?_
    (fun i => isAffineOpen_opensRange (chart k i)) (chart_intersection_compact k)
  apply Opens.ext
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨⟨i⟩, y, hy⟩ := (glueData k).ι_jointly_surjective x
  simp only [Opens.coe_iSup, Set.mem_iUnion]
  exact ⟨i, y, hy⟩

private lemma separated_not_contains_both_origins (k : Type u) [Field k]
    (V : (scheme k).Opens) (hV : Scheme.IsSeparated V) :
    ¬ (chart k 0 (axisOrigin k) ∈ V ∧ chart k 1 (axisOrigin k) ∈ V) := by
  let X := scheme k
  let p : PrimeSpectrum (puncturedAxisRing k) := axisPoint k 0
  rintro ⟨hx₀, hx₁⟩
  let S := Spec (.of (puncturedAxisRing k))
  let c₀ := chart k 0
  let c₁ := chart k 1
  let K : Type u := ↑(S.residueField p)
  let : Field K := AlgebraicGeometry.Scheme.instFieldCarrierResidueField S p
  obtain ⟨A, hAcomm, hAdomain, hAvaluation, f, e, hη, hclosed, _hres⟩ :=
    AlgebraicGeometry.exists_valuation_ring_of_specializes S
      (axisPoint_specializes_axisOrigin k 0) K
      (CommRingCat.ofHom (RingEquiv.refl (S.residueField p)).toRingHom)
  let : CommRing A := hAcomm
  let : IsDomain A := hAdomain
  let : ValuationRing A := hAvaluation
  let ASpec := Spec (.of A)
  have hpre (c : S ⟶ X) (hc : c (axisOrigin k) ∈ V) :
      (⊤ : ASpec.Opens) ≤ (f ≫ c) ⁻¹ᵁ V := by
    intro z _
    have hz := (IsLocalRing.specializes_closedPoint
      (R := ↑(CommRingCat.of A)) z).map (Scheme.Hom.continuous (f ≫ c))
    apply specializes_iff_forall_open.mp hz (V : Set X) V.2
    change c (f (IsLocalRing.closedPoint A)) ∈ V
    rwa [hclosed]
  have hlift (c : S ⟶ X) (hc : c (axisOrigin k) ∈ V) : ∃ g : ASpec ⟶ V, g ≫ V.ι = f ≫ c :=
    ⟨ASpec.topIso.inv ≫ (f ≫ c).resLE V ⊤ (hpre c hc), by simp [Scheme.Hom.resLE_comp_ι]⟩
  have hpt {c : S ⟶ X} {g : ASpec ⟶ V} (h : g ≫ V.ι = f ≫ c) :
      V.ι (g (IsLocalRing.closedPoint A)) = c (axisOrigin k) := by
    rw [← hclosed]
    exact congrArg (fun q => q (IsLocalRing.closedPoint A)) h
  obtain ⟨g₀, hcomp₀⟩ := hlift c₀ hx₀
  obtain ⟨g₁, hcomp₁⟩ := hlift c₁ hx₁
  have hneq : g₀ (IsLocalRing.closedPoint A) ≠ g₁ (IsLocalRing.closedPoint A) := fun h =>
    origins_ne k ((hpt hcomp₀).symm.trans ((congrArg V.ι h).trans (hpt hcomp₁)))
  let O : ASpec.Opens := f ⁻¹ᵁ puncturedAxisChart k
  have hOη : genericPoint ASpec ∈ O := by
    change f (genericPoint ASpec) ∈ puncturedAxisChart k
    rw [hη]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 (axisQuotientMap_X_notMem_axisPoint k 0)
  have hOdense : Dense (O : Set ASpec) := by
    have hdense : Dense ({genericPoint ASpec} : Set ASpec) := by
      rw [dense_iff_closure_eq, genericPoint_closure]
    exact hdense.mono (by simpa using hOη)
  let fO : O.toScheme ⟶ (puncturedAxisChart k).toScheme :=
    f.resLE (puncturedAxisChart k) O le_rfl
  have hfO : fO ≫ (puncturedAxisChart k).ι = O.ι ≫ f := by
    simp [fO]
  have hOeq : O.ι ≫ f ≫ c₀ = O.ι ≫ f ≫ c₁ := by
    simpa only [← Category.assoc, hfO] using
      congrArg (fun q => fO ≫ q) (charts_agree_as_morphisms k)
  have hOeqV : O.ι ≫ g₀ = O.ι ≫ g₁ := by
    apply (cancel_mono V.ι).1
    simpa only [Category.assoc, hcomp₀, hcomp₁] using hOeq
  have : Scheme.IsSeparated (V : Scheme.{u}) := hV
  have : IsDominant O.ι := by
    constructor
    change Dense (Set.range O.ι)
    rwa [Scheme.Opens.range_ι]
  exact hneq (congrArg (fun g => g (IsLocalRing.closedPoint A))
    (AlgebraicGeometry.ext_of_isDominant O.ι hOeqV))

private lemma no_compact_dense_open_omitting_origin (k : Type u) [Field k]
    (i : Fin 2) (V : (scheme k).Opens)
    (hVcompact : IsCompact (V : Set (scheme k)))
    (hVdense : Dense (V : Set (scheme k)))
    (hmiss : chart k i (axisOrigin k) ∉ V) : False := by
  let S := Spec (.of (puncturedAxisRing k))
  let c := chart k i
  let U : Set S := c ⁻¹' (V : Set (scheme k))
  let P : Set S := {x | x ≠ axisOrigin k}
  let Q : Set P := {x | c x.1 ∈ V}
  have : QuasiSeparatedSpace (scheme k) := scheme_quasiSeparated k
  have hinter : IsCompact ((V : Set (scheme k)) ∩ Set.range c) :=
    QuasiSeparatedSpace.inter_isCompact _ _ V.2 hVcompact c.isOpenEmbedding.isOpen_range
      (isCompact_range (Scheme.Hom.continuous c))
  have himageCompact : IsCompact (c '' U) := by
    rwa [show c '' U = (V : Set (scheme k)) ∩ Set.range c by
      simp [U, Set.image_preimage_eq_inter_range]]
  have hUcompact : IsCompact U := c.isOpenEmbedding.isInducing.isCompact_iff.mpr himageCompact
  have hUdense : Dense U := hVdense.preimage c.isOpenEmbedding.isOpenMap
  have hmiss' : axisOrigin k ∉ U := hmiss
  have himage : ((↑) '' Q : Set S) = U := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hy
    · exact ⟨⟨x, fun heq => hmiss' (heq ▸ hx)⟩, hx, rfl⟩
  have hQopen : IsOpen Q := by
    change IsOpen ((fun x : P => c x.1) ⁻¹' (V : Set (scheme k)))
    exact V.2.preimage (by fun_prop)
  have hQcompact : IsCompact Q := by rwa [Subtype.isCompact_iff, himage]
  have hQdense : Dense Q := by
    rw [Subtype.dense_iff, himage]
    exact fun x _ => hUdense x
  exact puncturedAxisRing_has_no_quasiCompact_dense_open k ⟨Q, hQopen, hQcompact, hQdense⟩

end Stacks.Examples.DoubledAxes

namespace Stacks.Examples

open DoubledAxes

/-- **Stacks 086I.** There is a quasi-compact quasi-separated scheme with no separated
quasi-compact dense open. -/
@[stacks 086I]
theorem exists_qcqs_without_separated_quasiCompact_dense_open :
    ∃ X : Scheme.{u}, CompactSpace X ∧ QuasiSeparatedSpace X ∧
      ¬ ∃ V : X.Opens, IsCompact (V : Set X) ∧ Dense (V : Set X) ∧
        Scheme.IsSeparated V := by
  let k : Type u := ULift.{u} ℚ
  refine ⟨scheme k, scheme_compact k, scheme_quasiSeparated k, ?_⟩
  rintro ⟨V, hVcompact, hVdense, hVsep⟩
  exact (not_and_or.mp (separated_not_contains_both_origins k V hVsep)).elim
    (no_compact_dense_open_omitting_origin k 0 V hVcompact hVdense)
    (no_compact_dense_open_omitting_origin k 1 V hVcompact hVdense)

end Stacks.Examples

end
