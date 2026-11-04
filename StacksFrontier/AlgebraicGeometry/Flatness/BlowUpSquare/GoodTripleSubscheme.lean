module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.AffineChartRestrict
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartHomologyFreeness
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.LocallyFreeLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.IdealSheafFiniteType.Basic
public import StacksFrontier.Homology.Eta.Perfect.TotalDirectSumIdeal
public import StacksCore.Tactic.StacksAttribute

/-!
# The closed subscheme of the divisor cut out by the obstruction ideals

Let `(X, D, M)` be a good triple as in Situation 0F8S: a scheme `X`, an effective Cartier
divisor `D ⊂ X` with ideal sheaf `I`, a perfect object `M` of `D(𝒪_X)`, and every point of `D`
lying in an affine chart `(U, A, f, M^•)` all of whose determinantal ideals `I_i(M^•, f)` are
principal.  More on Flatness, Tag 0GTZ asserts the existence of a closed immersion `i : T → D`
of finite presentation which scheme-theoretically contains `D ∩ W`, where `W ⊂ X` is the maximal
open over which the cohomology sheaves of `M` are locally free, and over which the cohomology
sheaves of `Li^*Lη_I M` are locally free of the expected ranks.

On a good affine chart that closed subscheme is cut out by the total obstruction ideal
`J(M^•, f) ⊆ A ⧸ fA` of More on Algebra, Tag 0F81, which is
`Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal`.  This file transports that ideal to the
structure sheaf of `D`, as `AffineChart.obstructionIdeal`, and proves the two properties of
Tag 0GTZ that the chart-local statement supports: finite presentation of the closed immersion,
and part (1).

A closed subscheme of `D` is given by `AlgebraicGeometry.Scheme.IdealSheafData` on
`D.subscheme`, whose associated inclusion is automatically a closed immersion.  The theorems of
this file take that subscheme as a variable `T` together with the requirement that its ideal
over `D ∩ U` be `AffineChart.obstructionIdeal` for every good chart; the subscheme satisfying
that requirement is glued from the obstruction ideals in
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence`, which
assembles the two statements into the existential assertion of the tag.  See "The existence of
`T`" below.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.divisorAffineOpen`: the affine open
  `D ∩ U` of `D` cut out by an affine chart.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.divisorQuotEquiv`: the
  identification of the coordinate ring of `D ∩ U` with `A ⧸ fA`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.obstructionIdeal`: the total
  obstruction ideal `J(M^•, f)` of Tag 0F81, read as an ideal of the coordinate ring of `D ∩ U`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation`
  `.locallyOfFinitePresentation_and_comap_eq_bot_of_ideal_eq_obstructionIdeal`: **Tag 0GTZ, the
  finite presentation of `i : T → D` and part (1)**, at a closed subscheme `T ⊆ D` cutting out
  the obstruction ideal on every good chart.  The existential form of the tag, with `T`
  constructed, is
  `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isGoodChartOpen_ideal_eq_obstructionIdeal`
  of `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.obstructionIdeal_fg` and
  `AffineChart.obstructionIdeal_eq_bot_of_le_locallyFreeLocus`: the two chart-local inputs — the
  obstruction ideal is finitely generated, and it vanishes on a chart contained in the locally
  free locus `W`.  The latter is part (1) over a chart: at a prime containing `f` the cohomology
  of `M^•` is free, by
  `AffineChart.free_localizedModule_homology_of_subset_cohomologyFiniteFreeLocus`, so `J(M^•, f)`
  localizes to zero there by Tag 0F81, while at a prime not containing `f` the whole of `A ⧸ fA`
  localizes to zero.
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_good_chart_mem_preimage` and
  `exists_good_chart_le_locallyFreeLocus`: the good charts cover `D`, and the ones contained in
  `W` cover `D ∩ W`; the second shrinks a chart to a standard open inside `W` with
  `AffineChart.restrictBasicOpen`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isAffineOpen_preimage_subschemeι`,
  `mem_supportSet_subschemeι`, `ideal_eq_bot_of_forall_basicOpen_eq_bot` and
  `ideal_eq_bot_of_cover_eq_bot`: the general facts about ideal sheaves used along the way —
  the inverse image of an affine open in the closed subscheme is affine, that subscheme maps
  into the support, and vanishing of an ideal sheaf over an affine open is local on that open.

## The existence of `T`

The *existence* of `T` is the gluing of the local closed subschemes cut out by the ideals
`J(M^•, f)` along a cover of `D` by good charts, and is
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_isGoodChartOpen_ideal_eq_obstructionIdeal`
of `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence`.  Its
three inputs are: the restriction of a good chart to a standard open is a good chart
(`AffineChart.restrictBasicOpen` with `AffineChart.isPrincipal_restrict_determinantalIdeal`);
the agreement of the obstruction ideals of two charts on a common standard open, which rests on
the derived comparison of their base-changed complexes there feeding Tag 0GSW
(`Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_derived_iso`) and is
`AffineChart.map_etaTotalDirectSumIdeal_eq` of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartObstructionIdeal`; and the
constructor `AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily` of
`StacksFrontier.AlgebraicGeometry.IdealSheafFromAffineFamily`, which turns ideals prescribed on
the members of an affine open cover closed under passing to standard opens into the unique
quasi-coherent sheaf of ideals inducing them.

Parts (2) and (3) of Tag 0GTZ, about the cohomology sheaves of `Li^*Lη_I M` and their ranks,
rest on identifying `Li^*Lη_I M` over a good chart with the chart-local décalage `η_f M^•` of
`Stacks.Decalage.DirectSumIdeal.finite_projective_etaHomology_quotient_etaTotalDirectSumIdeal`,
base-changed along `A ⧸ fA → C`.  Both affine inputs of that identification are available: the
derived décalage `Lη_I` is `Stacks.IdealTorsion.Eta.derivedEta`, and the comparison of a derived
pullback with termwise base change, Stacks Tag 08DW, is proved in both its parts — part (1) in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback`, part (2) there
and in `StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSchemePullbackComparison`.  What
the chart-level identification adds to those is the passage of the décalage comparison from a
spectrum to an affine *open* of a general scheme, which is the content recorded as
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage` in
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect`.  Two of its three
identifications are named declarations — `Lη_I` commutes with restriction along an open
immersion (`Stacks.Divisors.Eta.derivedEtaRestrictOpenObjIso`) and the transport along
`U ≅ Spec Γ(X, U)` (`Stacks.AffineTilde.transportTildeComplexIsoRestrict`) — and the module
documentation there states the remaining affine step exactly.

Part (3) is not a second piece of chart-level work.  The source deduces it from Cohomology,
Lemma 20.55.10, which is [Stacks, Tag 0GTA]: the derived décalage leaves the rank of a finite
free cohomology stalk unchanged.  That tag is proved, both halves, as
`Stacks.IdealTorsion.Eta.isFiniteFreeStalkOfRank_homology_derivedEtaOfRegular` and
`Stacks.IdealTorsion.Eta.rank_homology_derivedEtaOfRegular_eq` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafStalk.lean`, so part (3) is to be read
off from it rather than proved again.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0GSW](https://stacks.math.columbia.edu/tag/0GSW)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect Stacks.Decalage.DirectSumIdeal

universe u d

namespace AlgebraicGeometry

/-! ### Affine opens and vanishing of an ideal sheaf -/

/-- The inverse image of an affine open of `X` in the closed subscheme cut out by an ideal
sheaf is affine: it is the range of the member of
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeCover` at that open. -/
theorem Scheme.IdealSheafData.isAffineOpen_preimage_subschemeι {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) : IsAffineOpen (I.subschemeι ⁻¹ᵁ U.1) := by
  rw [← I.opensRange_subschemeCover_map U]
  exact isAffineOpen_opensRange (H := I.subschemeCover.map_prop U) _

/-- A point of the closed subscheme cut out by an ideal sheaf maps into the support of that
ideal sheaf. -/
theorem Scheme.IdealSheafData.mem_supportSet_subschemeι {X : Scheme.{u}}
    (I : X.IdealSheafData) (z : I.subscheme) : I.subschemeι z ∈ I.supportSet := by
  have h1 : I.subschemeι z ∈ Set.range I.subschemeι := Set.mem_range_self z
  rw [I.range_subschemeι] at h1
  exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr h1

/-- **Vanishing of an ideal sheaf over an affine open may be checked on a basic-open cover of
that open**: the ideal over a basic open is the localization of the ideal above it, so
`Submodule.eq_bot_of_isLocalized₀_span` applies. -/
theorem Scheme.IdealSheafData.ideal_eq_bot_of_forall_basicOpen_eq_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) (A : X.affineOpens) (s : Set Γ(X, A.1))
    (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, I.ideal (X.affineBasicOpen (g : Γ(X, A.1))) = ⊥) : I.ideal A = ⊥ := by
  have inst := A.2.isLocalization_basicOpen
  refine Submodule.eq_bot_of_isLocalized₀_span s hs
    (fun g ↦ Γ(X, X.basicOpen (g : Γ(X, A.1))))
    (fun g ↦ Algebra.linearMap Γ(X, A.1) Γ(X, X.basicOpen (g : Γ(X, A.1)))) fun g ↦ ?_
  have hbase : Ideal.map
      (algebraMap Γ(X, A.1) Γ(X, X.basicOpen (g : Γ(X, A.1)))) (I.ideal A) = ⊥ := by
    rw [show (algebraMap Γ(X, A.1) Γ(X, X.basicOpen (g : Γ(X, A.1)))) =
        (X.presheaf.map (homOfLE (X.basicOpen_le (g : Γ(X, A.1)))).op).hom from rfl,
      I.map_ideal_basicOpen A (g : Γ(X, A.1))]
    exact h g
  rw [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen (g : Γ(X, A.1))),
    Ideal.localized'_eq_map, hbase, Submodule.restrictScalars_bot]

/-- **Vanishing of an ideal sheaf is a local condition.** An ideal sheaf which vanishes over
each member of a family of affine opens covering an affine open `A` vanishes over `A`. -/
theorem Scheme.IdealSheafData.ideal_eq_bot_of_cover_eq_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) {ι : Type*} (V : ι → X.affineOpens) (A : X.affineOpens)
    (hV : ∀ x : A.1, ∃ i : ι, x.1 ∈ (V i).1) (h : ∀ i, I.ideal (V i) = ⊥) :
    I.ideal A = ⊥ := by
  have hex : ∀ x : A.1, ∃ (i : ι) (r : Γ(X, A.1)) (rV : Γ(X, (V i).1)),
      X.basicOpen r = X.basicOpen rV ∧ x.1 ∈ X.basicOpen r := by
    intro x
    obtain ⟨i, hi⟩ := hV x
    exact ⟨i, exists_basicOpen_le_affine_inter A.2 (V i).2 _ ⟨x.2, hi⟩⟩
  choose i r rV e hxr using hex
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    rw [← A.2.self_le_iSup_basicOpen_iff]
    exact fun x hxA ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxA⟩⟩
  refine I.ideal_eq_bot_of_forall_basicOpen_eq_bot A (Set.range r) hspan ?_
  rintro ⟨-, x, rfl⟩
  have heq : X.affineBasicOpen (U := A) (r x) = X.affineBasicOpen (U := V (i x)) (rV x) :=
    Subtype.ext (e x)
  rw [heq, ← I.map_ideal_basicOpen (V (i x)) (rV x), h (i x)]
  exact Ideal.map_bot

namespace ComplexAndDivisorSituation

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-! ### The obstruction ideal of a chart, read on the divisor -/

/-- The affine open `D ∩ U` of the divisor cut out by an affine chart `(U, A, f, M^•)`. -/
def divisorAffineOpen (C : AffineChart S) : S.D.subscheme.affineOpens :=
  ⟨S.D.subschemeι ⁻¹ᵁ C.U.1, S.D.isAffineOpen_preimage_subschemeι C.U⟩

/-- The coordinate ring of `D ∩ U` is `A ⧸ fA`: the sections of `𝒪_D` over the inverse image of
`U` are `Γ(X, U)` modulo the ideal of `D` there, which the chart's equation generates. -/
def divisorQuotEquiv (C : AffineChart S) :
    Γ(S.D.subscheme, S.D.subschemeι ⁻¹ᵁ C.U.1) ≃+* (Γ(S.X, C.U) ⧸ Ideal.span {C.f}) :=
  (S.D.subschemeObjIso C.U).commRingCatIsoToRingEquiv.trans
    (Ideal.quotEquivOfEq C.divisor_ideal)

/-- **The obstruction ideal of an affine chart, as an ideal of `𝒪_D` over `D ∩ U`.**  This is
the total obstruction ideal `J(M^•, f) ⊆ A ⧸ fA` of More on Algebra, Tag 0F81 transported along
the identification of `A ⧸ fA` with the coordinate ring of `D ∩ U`.  It is the ideal that cuts
out the closed subscheme `T` of More on Flatness, Tag 0GTZ over the chart. -/
def obstructionIdeal (C : AffineChart S) :
    Ideal Γ(S.D.subscheme, S.D.subschemeι ⁻¹ᵁ C.U.1) :=
  (etaTotalDirectSumIdeal C.complex C.f).map (C.divisorQuotEquiv.symm : _ →+* _)

/-- The obstruction ideal of a chart with principal determinantal ideals is finitely generated,
the total obstruction ideal of Tag 0F81 being so. -/
theorem obstructionIdeal_fg (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) : C.obstructionIdeal.FG :=
  (etaTotalDirectSumIdeal_fg C.complex C.f C.regular hI).map _

/-! ### Vanishing over the locally free locus -/

/-- The equation of the divisor annihilates every element of the total obstruction ideal, that
ideal living in `A ⧸ fA`. -/
private theorem smul_eq_zero_of_mem_etaTotalDirectSumIdeal (C : AffineChart S)
    (y : (etaTotalDirectSumIdeal C.complex C.f)) : C.f • y = 0 := by
  refine Submodule.coe_eq_zero.mp ?_
  rw [Submodule.coe_smul_of_tower, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self C.f), zero_mul]

/-- Away from the divisor the total obstruction ideal localizes to zero: the equation of the
divisor is invertible there and kills the ideal. -/
private theorem subsingleton_localizedModule_etaTotal_of_notMem (C : AffineChart S)
    (P : Ideal Γ(S.X, C.U)) [P.IsPrime] (hfP : C.f ∈ P.primeCompl) :
    Subsingleton (LocalizedModule P.primeCompl (etaTotalDirectSumIdeal C.complex C.f)) := by
  rw [subsingleton_iff_forall_eq 0]
  intro z
  induction z using LocalizedModule.induction_on with
  | _ y s =>
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    exact ⟨⟨C.f, hfP⟩, by
      simpa using C.smul_eq_zero_of_mem_etaTotalDirectSumIdeal y⟩

/-- **More on Flatness, Tag 0GTZ part (1), over an affine chart.**  On a chart whose affine open
lies in the locally free locus `W` the total obstruction ideal of Tag 0F81 is zero: at a prime
containing the equation of the divisor the cohomology of the chart complex is free, by
`AffineChart.free_localizedModule_homology_of_subset_cohomologyFiniteFreeLocus`, so the ideal
localizes to zero there, and at a prime not containing the equation the whole of `A ⧸ fA`
localizes to zero. -/
theorem etaTotalDirectSumIdeal_eq_bot_of_le_locallyFreeLocus (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hW : (C.U.1 : S.X.Opens) ≤ S.locallyFreeLocus) :
    etaTotalDirectSumIdeal C.complex C.f = ⊥ := by
  have hCW : (C.U.1 : Set S.X) ⊆ RingedSpace.cohomologyFiniteFreeLocus S.M := fun x hx ↦ hW hx
  have hsub : ∀ (P : Ideal Γ(S.X, C.U)) [P.IsMaximal],
      Subsingleton (LocalizedModule P.primeCompl (etaTotalDirectSumIdeal C.complex C.f)) := by
    intro P hP
    by_cases hfP : C.f ∈ P
    · let x : C.U.1.toScheme := C.U.2.isoSpec.inv ⟨P, inferInstance⟩
      have hx : C.U.2.primeIdealOf x = ⟨P, inferInstance⟩ := by
        change (C.U.2.isoSpec.inv ≫ C.U.2.isoSpec.hom) ⟨P, inferInstance⟩ = _
        rw [Iso.inv_hom_id]
        rfl
      have hfree : ∀ i : ℤ, Module.Free (Localization.AtPrime P)
          (LocalizedModule P.primeCompl (C.complex.toCochainComplex.homology i)) := by
        intro i
        have := C.free_localizedModule_homology_of_subset_cohomologyFiniteFreeLocus hCW x i
        rwa [hx] at this
      exact subsingleton_localizedModule_etaTotal_of_free_homology C.complex C.f C.regular hI
        P hfP
        (Stacks.DeterminantalIdeal.FreeHomology.free_homology_baseChange_of_free_localizedModule
          P.primeCompl C.complex hfree)
    · exact C.subsingleton_localizedModule_etaTotal_of_notMem P hfP
  have hss : Subsingleton (etaTotalDirectSumIdeal C.complex C.f) :=
    Module.subsingleton_of_localization_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl (etaTotalDirectSumIdeal C.complex C.f))
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl _) fun P _ ↦ hsub P
  exact Submodule.eq_bot_of_subsingleton

/-- **More on Flatness, Tag 0GTZ part (1), over an affine chart.**  The obstruction ideal of a
chart whose affine open lies in the locally free locus `W` is zero, so the closed subscheme it
cuts out in `D ∩ U` is all of `D ∩ U`. -/
theorem obstructionIdeal_eq_bot_of_le_locallyFreeLocus (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hW : (C.U.1 : S.X.Opens) ≤ S.locallyFreeLocus) : C.obstructionIdeal = ⊥ := by
  rw [obstructionIdeal, C.etaTotalDirectSumIdeal_eq_bot_of_le_locallyFreeLocus hI hW,
    Ideal.map_bot]

end AffineChart

/-! ### Good charts cover the divisor -/

/-- Every point of the closed subscheme `D` lies in the inverse image of the affine open of a
chart with principal determinantal ideals: that is the good-triple condition read on `D`. -/
theorem exists_good_chart_mem_preimage (S : ComplexAndDivisorSituation.{u, d})
    (hS : S.IsGoodTriple) (z : S.D.subscheme) :
    ∃ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) ∧
      z ∈ S.D.subschemeι ⁻¹ᵁ C.U.1 := by
  obtain ⟨C, hmem, hI⟩ := hS _ (S.D.mem_supportSet_subschemeι z)
  exact ⟨C, hI, hmem⟩

/-- Every point of `D ∩ W` lies in the affine open of a chart with principal determinantal
ideals which is itself contained in the locally free locus `W`: a chart at the point is shrunk
to a standard open inside `W`, and principality of the determinantal ideals is inherited by that
restriction. -/
theorem exists_good_chart_le_locallyFreeLocus (S : ComplexAndDivisorSituation.{u, d})
    (hS : S.IsGoodTriple) (x : S.X) (hxD : x ∈ S.D.supportSet)
    (hxW : x ∈ S.locallyFreeLocus) :
    ∃ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) ∧
      x ∈ (C.U.1 : Set S.X) ∧ (C.U.1 : S.X.Opens) ≤ S.locallyFreeLocus := by
  obtain ⟨C, hmem, hI⟩ := hS x hxD
  obtain ⟨g, hgle, hxg⟩ :=
    C.U.2.exists_basicOpen_le (V := S.locallyFreeLocus) ⟨x, hxW⟩ hmem
  exact ⟨C.restrictBasicOpen g,
    fun i ↦ C.isPrincipal_restrict_determinantalIdeal _ (S.X.basicOpen_le g) (hI i), hxg, hgle⟩

/-! ### The closed subscheme of Tag 0GTZ -/

section Subscheme

variable (S : ComplexAndDivisorSituation.{u, d}) (hS : S.IsGoodTriple)
  (T : S.D.subscheme.IdealSheafData)
  (hT : ∀ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
    T.ideal C.divisorAffineOpen = C.obstructionIdeal)

include hS hT

/-- **More on Flatness, Tag 0GTZ: the closed immersion `i : T → D` is of finite
presentation.**  A closed subscheme of `D` whose ideal over `D ∩ U` is the total obstruction
ideal `J(M^•, f)` of Tag 0F81, for every affine chart `(U, A, f, M^•)` with principal
determinantal ideals, is of finite presentation over `D`: those obstruction ideals are finitely
generated, the good charts of a good triple cover `D`, and finite generation of an ideal sheaf
is local. -/
theorem locallyOfFinitePresentation_subschemeι_of_ideal_eq_obstructionIdeal :
    LocallyOfFinitePresentation T.subschemeι := by
  refine (Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff T).mpr fun A ↦ ?_
  refine Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover T
    (fun C : {C : AffineChart S // ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal} ↦
      C.1.divisorAffineOpen) ?_ (fun C ↦ ?_) A
  · rw [eq_top_iff]
    intro z _
    obtain ⟨C, hI, hz⟩ := S.exists_good_chart_mem_preimage hS z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨C, hI⟩, hz⟩
  · rw [hT C.1 C.2]
    exact C.1.obstructionIdeal_fg C.2

/-- **More on Flatness, Tag 0GTZ part (1), affine-locally.**  The ideal of `T` vanishes over
every affine open of `D` lying over the locally free locus `W`: each point of `D ∩ W` lies in a
good chart contained in `W`, over which the obstruction ideal is zero, and vanishing of an ideal
sheaf is local. -/
theorem ideal_eq_bot_of_le_preimage_locallyFreeLocus (V : S.D.subscheme.affineOpens)
    (hV : (V.1 : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ S.locallyFreeLocus) :
    T.ideal V = ⊥ := by
  refine T.ideal_eq_bot_of_cover_eq_bot
    (fun C : {C : AffineChart S //
        (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) ∧
          (C.U.1 : S.X.Opens) ≤ S.locallyFreeLocus} ↦ C.1.divisorAffineOpen) V
    (fun z ↦ ?_) fun C ↦ ?_
  · obtain ⟨C, hI, hxC, hCW⟩ :=
      S.exists_good_chart_le_locallyFreeLocus hS (S.D.subschemeι z.1)
        (S.D.mem_supportSet_subschemeι z.1) (hV z.2)
    exact ⟨⟨C, hI, hCW⟩, hxC⟩
  · rw [hT C.1 C.2.1]
    exact C.1.obstructionIdeal_eq_bot_of_le_locallyFreeLocus C.2.1 C.2.2

/-- **More on Flatness, Tag 0GTZ: the finite presentation of the closed immersion and part
(1).**  Let `(X, D, M)` be a good triple as in Situation 0F8S and let `T ⊆ D` be a closed
subscheme whose ideal over `D ∩ U` is the total obstruction ideal `J(M^•, f)` of Tag 0F81 for
every affine chart `(U, A, f, M^•)` with principal determinantal ideals.  Then the closed
immersion `i : T → D` is locally of finite presentation, and `T` scheme-theoretically contains
`D ∩ W`, where `W ⊆ X` is the maximal open over which the cohomology sheaves of `M` are locally
free: the inverse image of the ideal sheaf of `T` on `D ∩ W` is zero.

`T` is a variable of this statement; the subscheme itself is glued from the local closed
subschemes cut out by `J(M^•, f)` along a cover of `D` by good charts in
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_isGoodChartOpen_ideal_eq_obstructionIdeal`,
which combines with this theorem into the existential assertion of the tag. -/
@[stacks 0GTZ "the finite presentation of the closed immersion `i : T → D` and part (1), at a \
closed subscheme `T` of `D` cutting out the obstruction ideal of Tag 0F81 on every good affine \
chart; such a `T` is constructed, and the tag stated existentially, in \
AlgebraicGeometry.ComplexAndDivisorSituation.exists_isGoodChartOpen_ideal_eq_obstructionIdeal of \
GoodTripleSubschemeExistence.lean. Parts (2) and (3), which concern `Li^*Lη_I M`, rest on \
identifying it over a good chart with the chart-local décalage, for which the affine comparison \
of Tag 08DW is proved and the remaining ingredient is the chart-level form of Tag 0GTV's second \
assertion recorded as AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage"]
theorem locallyOfFinitePresentation_and_comap_eq_bot_of_ideal_eq_obstructionIdeal :
    LocallyOfFinitePresentation T.subschemeι ∧
      T.comap (S.D.subschemeι ⁻¹ᵁ S.locallyFreeLocus).ι = ⊥ := by
  refine ⟨S.locallyOfFinitePresentation_subschemeι_of_ideal_eq_obstructionIdeal hS T hT,
    Scheme.IdealSheafData.ext (funext fun V ↦ ?_)⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    S.ideal_eq_bot_of_le_preimage_locallyFreeLocus hS T hT _
      (Scheme.Opens.ι_image_le _ V.1),
    ← RingHom.ker_eq_comap_bot]
  exact RingHom.ker_coe_equiv
    (((S.D.subschemeι ⁻¹ᵁ S.locallyFreeLocus).ι.appIso V.1).symm).commRingCatIsoToRingEquiv

end Subscheme

end ComplexAndDivisorSituation

end AlgebraicGeometry

end
