module

public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.LocalDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartNormalizedCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.IdealSheafFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.IdealSheafFromAffineFamily

/-!
# Stacks tag 0GTY: the morphism is a `W \ D`-admissible blowup over a quasi-compact open

Let `(X, D, M)` be a triple as in Situation 0F8S and let `b : X' ⟶ X` be the morphism of Stacks
tag 0GTY.  The last assertion of that tag is that for a quasi-compact open `W ⊂ X` the
restriction `b|_{b⁻¹(W)} : b⁻¹(W) ⟶ W` is a `W \ D`-admissible blowing up.

This file proves it.  The centre is glued from the *normalized* centres of the charts of a finite
cover of `W`, as in the source's last paragraph.

## Main results

* `ComplexAndDivisorSituation.exists_finset_chart_cover`: a quasi-compact open is covered by
  finitely many chart domains contained in it.
* `ComplexAndDivisorSituation.exists_window_bound`: those finitely many charts admit a finite
  degree window `s` containing the degrees in which their complexes are nonzero, and a bound `q`
  on the tail Euler characteristics in those degrees.
* `ComplexAndDivisorSituation.gluedNormalizedCentre`: the glued centre on `W`.
* `ComplexAndDivisorSituation.finitePresentation_subschemeι_gluedNormalizedCentre` and
  `ComplexAndDivisorSituation.disjoint_support_gluedNormalizedCentre`: it is of finite
  presentation and supported on the divisor.
* `ComplexAndDivisorSituation.isAdmissibleBlowup_morphismRestrict_goodBlowupToBase`: **Stacks
  tag 0GTY, the quasi-compact-open admissibility assertion.**

## The degree window, and what the source asserts

The source takes `N_i = max_t χ_i(M_t^•)`, where `χ_i(M_t^•) = ∑_{j ≥ i} (-1)^{j-i} rk(M_t^j)`,
forms `I_{t,i} = f_t^{N_i - χ_i(M_t^•)} I_i(M_t^•, f_t)` on the charts of a finite cover
`W = U_1 ∪ … ∪ U_T`, glues these into ideals `ℐ_i ⊆ 𝒪_W`, and asserts that *all but finitely many
`ℐ_i` are `𝒪_W`*, so that the product over all `i ∈ ℤ` makes sense.

That last assertion fails as stated.  Below the supports of all the `M_t^•` one has
`rk(M_t^i) = 0`, hence `I_i(M_t^•, f_t) = A_t` and `χ_i(M_t^•) = -χ_{i+1}(M_t^•)`, so `χ_i(M_t^•)`
alternates between `±χ` for a constant `χ` depending on the chart.  Two charts of the cover whose
domains are disjoint — possible as soon as `W` is disconnected — may have different such
constants, and then `N_i ≠ χ_i(M_t^•)` for infinitely many `i ≪ 0` for one of them, making
`I_{t,i} = (f_t^{N_i - χ_i(M_t^•)})` a proper ideal in infinitely many degrees.

The repair is to take the product over a *finite degree window* `s` containing the degrees in
which the complexes of the finitely many chosen charts are nonzero, which is what
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_window_bound` supplies.  This changes
nothing about the conclusion the tag asserts: every omitted factor is `I_i(M_t^•, f_t) = A_t`
times a power of the equation of the effective Cartier divisor `D ∩ U_t`, and by Stacks tag 080H
part (1) multiplying a centre by an effective Cartier divisor leaves the blowup unchanged as a
scheme over the base
(`AffineChart.nonempty_overIso_blowUpToBase_normalizedCentreIdealSheaf`).  For the same reason a
single bound `q` works in place of the per-degree maxima `N_i`: all the gluing needs is that the
two exponents at a degree `i` differ by `χ_i(N^•) - χ_i(M^•)`, which is the hypothesis of Stacks
tag 0GSS.

## Implementation notes

The glued centre is built with `AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily` from the
affine opens of `W` lying inside the domain of one of the chosen charts.  The ideal attached to
such an open is written as an infimum over all the dominating charts, so that no choice is made;
`AlgebraicGeometry.ComplexAndDivisorSituation.famIdeal_eq` collapses the infimum at any one of
them, using the chart independence of the normalized centre.

Finite presentation is `Stacks.Flatness.finitePresentation_subschemeι_iff` together with
`Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover`, which spreads finite generation from the
covering family to every affine open.  The identification over a chart with the blowing up of
tag 0GTY is `AffineChart.existsUnique_iso_preimage_blowUp` for `b`, Stacks tag 0805 for the
glued centre, and Stacks tag 080H part (1) to pass between the two centres; the descent to `W` is
`AlgebraicGeometry.nonempty_overIso_blowUpToBase_of_openCover`.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0GSS](https://stacks.math.columbia.edu/tag/0GSS)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 080H](https://stacks.math.columbia.edu/tag/080H)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

attribute [local instance 10000] HasDerivedCategory.standard

universe u d
namespace AlgebraicGeometry.ComplexAndDivisorSituation

/-! ### A finite cover of a quasi-compact open by chart domains -/

/-- **A quasi-compact open is covered by finitely many chart domains contained in it.**  The
chart domains form a basis of the topology, so they cover `W` by opens inside `W`, and
quasi-compactness extracts a finite subcover. -/
theorem exists_finset_chart_cover (S : ComplexAndDivisorSituation.{u, d}) (W : S.X.Opens)
    (hW : IsCompact (W : Set S.X)) :
    ∃ t : Finset {C : AffineChart S // (C.U : S.X.Opens) ≤ W},
      ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X) := by
  classical
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (ι := {C : AffineChart S // (C.U : S.X.Opens) ≤ W})
    (fun C => ((C.1.U : S.X.Opens) : Set S.X))
    (fun C => (C.1.U : S.X.Opens).isOpen)
    (by
      intro x hx
      obtain ⟨C, hxC, hCW⟩ := S.exists_chart_mem_le x W hx
      exact Set.mem_iUnion.mpr ⟨⟨C, hCW⟩, hxC⟩)
  refine ⟨t, fun x hx => ?_⟩
  obtain ⟨C, hCt, hxC⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact ⟨C, hCt, hxC⟩

/-- A finite family of integers has a natural-number upper bound. -/
private theorem exists_nat_upper_bound {α : Type*} (t : Finset α) (f : α → ℤ) :
    ∃ q : ℕ, ∀ a ∈ t, f a ≤ (q : ℤ) := by
  classical
  refine ⟨t.sup fun a => (f a).toNat, fun a ha => ?_⟩
  have h := Finset.le_sup (f := fun a => (f a).toNat) ha
  omega

/-- **A finite family of charts admits a degree window and a common bound on the tail Euler
characteristics.**  The window `s` is the union of the degrees in which the charts' complexes are
nonzero, and `q` bounds the finitely many tail Euler characteristics in those degrees. -/
theorem exists_window_bound (S : ComplexAndDivisorSituation.{u, d}) (W : S.X.Opens)
    (t : Finset {C : AffineChart S // (C.U : S.X.Opens) ≤ W}) :
    ∃ (s : Finset ℤ) (q : ℕ), (∀ C ∈ t, C.1.complex.bounded.toFinset ⊆ s) ∧
      ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ) := by
  classical
  set s : Finset ℤ := t.biUnion fun C => C.1.complex.bounded.toFinset with hs
  obtain ⟨q, hq⟩ := exists_nat_upper_bound (t.product s)
    fun p => p.1.1.complex.tailEulerCharacteristic p.2
  refine ⟨s, q, fun C hC => ?_, fun C hC i hi => ?_⟩
  · rw [hs]
    exact Finset.subset_biUnion_of_mem (fun C => C.1.complex.bounded.toFinset) hC
  · exact hq (C, i) (Finset.mem_product.mpr ⟨hC, hi⟩)

/-! ### The glued normalized centre on a quasi-compact open -/

section Glue

variable (S : ComplexAndDivisorSituation.{u, d}) (W : S.X.Opens)
  (t : Finset {C : AffineChart S // (C.U : S.X.Opens) ≤ W}) (s : Finset ℤ) (q : ℕ)

/-- The affine opens of `W` that lie inside the domain of one of the chosen charts. -/
def Dominated (U : W.toScheme.affineOpens) : Prop :=
  ∃ C ∈ t, (U : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ (C.1.U : S.X.Opens)

/-- The candidate ideal on an affine open of `W`: the normalized centre of any chosen chart
dominating it, extended to that open.  It is written as an infimum so that no choice of chart is
made; `AlgebraicGeometry.ComplexAndDivisorSituation.famIdeal_eq` says the infimum is attained at
every dominating chart. -/
def famIdeal (U : W.toScheme.affineOpens) : Ideal Γ(W.toScheme, (U : W.toScheme.Opens)) :=
  ⨅ C ∈ t, ⨅ h : (U : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ (C.1.U : S.X.Opens),
    (C.1.normalizedCentre s q).map (C.1.pullbackRingHom W.ι U h).hom

/-- **The candidate ideal is the normalized centre of any dominating chart.**  Two dominating
charts give the same extended ideal, by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.map_normalizedCentre_eq`. -/
theorem famIdeal_eq
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    {U : W.toScheme.affineOpens}
    {C : {C : AffineChart S // (C.U : S.X.Opens) ≤ W}} (hC : C ∈ t)
    (h : (U : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ (C.1.U : S.X.Opens)) :
    famIdeal S W t s q U
      = (C.1.normalizedCentre s q).map (C.1.pullbackRingHom W.ι U h).hom := by
  refine le_antisymm (iInf_le_of_le C (iInf_le_of_le hC (iInf_le _ h))) ?_
  refine le_iInf fun D => le_iInf fun hD => le_iInf fun hDU => ?_
  exact le_of_eq (C.1.map_normalizedCentre_eq D.1 W.ι (S.isPullbackDefined_ι W) U h hDU s q
    (hbound C hC) (hbound D hD))

/-- The dominated affine opens are stable under passing to a standard open. -/
theorem famIdeal_basic (U : W.toScheme.affineOpens)
    (g : Γ(W.toScheme, (U : W.toScheme.Opens))) (hU : Dominated S W t U) :
    Dominated S W t (W.toScheme.affineBasicOpen g) := by
  obtain ⟨C, hC, h⟩ := hU
  exact ⟨C, hC, (W.toScheme.basicOpen_le g).trans h⟩

/-- The candidate ideals are compatible with restriction between dominated affine opens: both are
extensions of the normalized centre of one chart dominating the larger open. -/
theorem famIdeal_compat
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (U V : W.toScheme.affineOpens) (h : V ≤ U) (hU : Dominated S W t U)
    (_hV : Dominated S W t V) :
    (famIdeal S W t s q U).map (W.toScheme.presheaf.map (homOfLE h).op).hom
      = famIdeal S W t s q V := by
  obtain ⟨C, hC, hUC⟩ := hU
  rw [famIdeal_eq S W t s q hbound hC hUC,
    famIdeal_eq S W t s q hbound hC ((show (V : W.toScheme.Opens) ≤ (U : W.toScheme.Opens)
      from h).trans hUC), Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

/-- The dominated affine opens cover `W`: every point of `W` lies in a chart domain contained in
`W`, whose inverse image in `W` is affine. -/
theorem famIdeal_cover (ht : ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X))
    (x : W.toScheme) :
    ∃ U : W.toScheme.affineOpens, Dominated S W t U ∧ x ∈ (U : W.toScheme.Opens) := by
  obtain ⟨C, hC, hxC⟩ := ht (W.ι.base x) x.2
  exact ⟨⟨W.ι ⁻¹ᵁ (C.1.U : S.X.Opens),
    C.1.U.2.preimage_of_isOpenImmersion W.ι (by simpa using C.2)⟩, ⟨C, hC, le_rfl⟩, hxC⟩

/-- **The glued normalized centre on a quasi-compact open.**  The quasi-coherent sheaf of ideals
on `W` whose ideal over an affine open inside the domain of one of the chosen charts is the
normalized centre of that chart, extended to the open.  It is well defined because two charts
give the same extended ideal there. -/
def gluedNormalizedCentre
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (ht : ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X)) :
    W.toScheme.IdealSheafData :=
  Scheme.IdealSheafData.ofAffineFamily (Dominated S W t) (famIdeal S W t s q)
    (famIdeal_cover S W t ht) (famIdeal_basic S W t) (famIdeal_compat S W t s q hbound)

/-- The glued normalized centre has, over an affine open inside a chart domain, the normalized
centre of that chart. -/
theorem ideal_gluedNormalizedCentre
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (ht : ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X))
    {U : W.toScheme.affineOpens}
    {C : {C : AffineChart S // (C.U : S.X.Opens) ≤ W}} (hC : C ∈ t)
    (h : (U : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ (C.1.U : S.X.Opens)) :
    (gluedNormalizedCentre S W t s q hbound ht).ideal U
      = (C.1.normalizedCentre s q).map (C.1.pullbackRingHom W.ι U h).hom := by
  rw [gluedNormalizedCentre, Scheme.IdealSheafData.ideal_ofAffineFamily _ _ _ _ _ ⟨C, hC, h⟩,
    famIdeal_eq S W t s q hbound hC h]

/-- The glued normalized centre is of finite presentation: on each member of the covering family
it is an extension of the finitely generated normalized centre of a chart, and finite generation
spreads from a covering family to every affine open. -/
theorem finitePresentation_subschemeι_gluedNormalizedCentre
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (ht : ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X)) :
    FinitePresentation (gluedNormalizedCentre S W t s q hbound ht).subschemeι := by
  classical
  rw [Stacks.Flatness.finitePresentation_subschemeι_iff]
  refine Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover _
    (ι := {U : W.toScheme.affineOpens // Dominated S W t U}) (fun U => U.1) ?_ (fun U => ?_)
  · refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨U, hU, hxU⟩ := famIdeal_cover S W t ht x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  · obtain ⟨C, hC, h⟩ := U.2
    rw [ideal_gluedNormalizedCentre S W t s q hbound ht hC h]
    exact (C.1.normalizedCentre_fg s q).map _

/-- **The glued normalized centre restricts on a chart to the chart's normalized centre.**  Over
the domain of one of the chosen charts the glued ideal sheaf is, by construction, the extension
of that chart's normalized centre; the domain being affine, that identifies the two ideal sheaves
there. -/
theorem comap_gluedNormalizedCentre
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (ht : ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X))
    {C : {C : AffineChart S // (C.U : S.X.Opens) ≤ W}} (hC : C ∈ t) :
    (gluedNormalizedCentre S W t s q hbound ht).comap (S.X.homOfLE C.2)
      = C.1.normalizedCentreIdealSheaf s q := by
  let : IsAffine (C.1.U : S.X.Opens).toScheme := C.1.U.2
  set UC : W.toScheme.affineOpens := ⟨W.ι ⁻¹ᵁ (C.1.U : S.X.Opens),
    C.1.U.2.preimage_of_isOpenImmersion W.ι (by simpa using C.2)⟩ with hUC
  have hle : (⊤ : (C.1.U : S.X.Opens).toScheme.Opens) ≤
      S.X.homOfLE C.2 ⁻¹ᵁ (UC : W.toScheme.Opens) := by
    intro z _
    change W.ι.base ((S.X.homOfLE C.2).base z) ∈ (C.1.U : S.X.Opens)
    have h1 : W.ι.base ((S.X.homOfLE C.2).base z)
        = (C.1.U : S.X.Opens).ι.base z := by
      have hcomp := Scheme.homOfLE_ι (X := S.X) (U := (C.1.U : S.X.Opens)) (V := W) C.2
      have h2 := congrArg (fun m : (C.1.U : S.X.Opens).toScheme ⟶ S.X => m.base z) hcomp
      simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using h2
    rw [h1]
    exact z.2
  have hring : W.ι.appLE (C.1.U : S.X.Opens) (UC : W.toScheme.Opens) le_rfl ≫
      (S.X.homOfLE C.2).appLE (UC : W.toScheme.Opens) ⊤ hle
        = (C.1.U : S.X.Opens).ι.appLE (C.1.U : S.X.Opens) ⊤ (by simp) := by
    calc W.ι.appLE (C.1.U : S.X.Opens) (UC : W.toScheme.Opens) le_rfl ≫
          (S.X.homOfLE C.2).appLE (UC : W.toScheme.Opens) ⊤ hle
        = (S.X.homOfLE C.2 ≫ W.ι).appLE (C.1.U : S.X.Opens) ⊤ (by
            simp [Scheme.homOfLE_ι]) :=
          Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
      _ = (C.1.U : S.X.Opens).ι.appLE (C.1.U : S.X.Opens) ⊤ (by simp) := by
          simp only [Scheme.homOfLE_ι]
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [Stacks.IdealSheaf.ideal_comap_appLE _ (S.X.homOfLE C.2) UC
      ⟨⊤, isAffineOpen_top (C.1.U : S.X.Opens).toScheme⟩ hle,
    ideal_gluedNormalizedCentre S W t s q hbound ht hC le_rfl, Ideal.map_map,
    ← CommRingCat.hom_comp, hring, Scheme.Opens.ι_appLE_top, AffineChart.normalizedCentreIdealSheaf]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rw [CommRingCat.hom_id, Ideal.map_id]

/-- **The glued normalized centre is supported on the divisor.**  Over a chart it contains a
positive power of the equation of `D ∩ U`, so its support meets no point off `D`; hence it is a
`W \ D`-admissible centre. -/
theorem disjoint_support_gluedNormalizedCentre
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (ht : ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X)) :
    Disjoint ((W.ι ⁻¹ᵁ S.D.support.compl : W.toScheme.Opens) : Set W.toScheme)
      ((gluedNormalizedCentre S W t s q hbound ht).support : Set W.toScheme) := by
  classical
  refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
  obtain ⟨C, hC, hzC⟩ := ht (W.ι.base z) z.2
  set U : W.toScheme.affineOpens := ⟨W.ι ⁻¹ᵁ (C.1.U : S.X.Opens),
    C.1.U.2.preimage_of_isOpenImmersion W.ι (by simpa using C.2)⟩ with hUdef
  have hzU : z ∈ (U : W.toScheme.Opens) := hzC
  set φ := (C.1.pullbackRingHom W.ι U le_rfl).hom with hφ
  set n : ℕ := (∑ i ∈ s, (C.1.complex.normalizedExponent q i + C.1.complex.rank i)) + 1 with hn
  -- the glued centre contains a positive power of the equation of the divisor on `U`
  have hpow : φ (C.1.f) ^ n ∈ (gluedNormalizedCentre S W t s q hbound ht).ideal U := by
    rw [ideal_gluedNormalizedCentre S W t s q hbound ht hC le_rfl, ← map_pow]
    refine Ideal.mem_map_of_mem _ ?_
    rw [hn, pow_succ']
    exact Ideal.mul_mem_left _ _ (C.1.pow_mem_normalizedCentre s q)
  -- so no point of the support of the glued centre lies in the nonvanishing locus of `f`
  have hzbasic : z ∉ W.toScheme.basicOpen (φ (C.1.f)) := by
    have h0 := (Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := U) hzU).mp
      (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr hz2)
    rw [Scheme.mem_zeroLocus_iff] at h0
    have h1 := h0 _ hpow
    rwa [Scheme.basicOpen_pow _ _ (by omega)] at h1
  -- but `z` lies off the divisor, whose ideal on `U` is generated by `f`
  have hzD : z ∈ (S.D.comap W.ι).supportSet := by
    refine (Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := U) hzU).mpr ?_
    rw [Scheme.mem_zeroLocus_iff, C.1.comap_ideal_eq_span W.ι U le_rfl]
    intro g hg
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
    rw [Scheme.basicOpen_mul]
    exact fun hmem => hzbasic hmem.2
  have hzD' := Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hzD
  rw [Scheme.IdealSheafData.support_comap] at hzD'
  exact hz1 hzD'

/-- The second projection of a chosen pullback is isomorphic over the base to that of any
pullback square. -/
private theorem nonempty_overIso_pullback_snd {X Y Z P : Scheme} {f : X ⟶ Z} {g : Y ⟶ Z}
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (h : IsPullback p₁ p₂ f g) :
    Nonempty (Over.mk (Limits.pullback.snd f g) ≅ Over.mk p₂) :=
  ⟨Over.isoMk (IsPullback.isoIsPullback _ _ (IsPullback.of_hasPullback f g) h)
    (IsPullback.isoIsPullback_hom_snd _ _ _ _)⟩

/-- **The restriction of the morphism of Stacks tag 0GTY over a chart is the blowing up of the
chart in its normalized centre.**  Over the domain of one of the chosen charts the restriction of
`b` is the blowing up of that chart in the product of its determinantal ideals, by the
affine-chart clause of tag 0GTY; that blowing up is the blowing up in the normalized centre, by
Stacks tag 080H part (1); and the normalized centre is the restriction of the glued centre, so
Stacks tag 0805 identifies the latter's blowup with the base change of the blowup of `W`. -/
theorem nonempty_overIso_pullback_snd_gluedNormalizedCentre
    (hbound : ∀ C ∈ t, ∀ i ∈ s, C.1.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (ht : ∀ x ∈ (W : Set S.X), ∃ C ∈ t, x ∈ (C.1.U : Set S.X))
    {C : {C : AffineChart S // (C.U : S.X.Opens) ≤ W}} (hC : C ∈ t)
    (hs : C.1.complex.bounded.toFinset ⊆ s) :
    Nonempty (Over.mk (Limits.pullback.snd (S.goodBlowupToBase ∣_ W) (S.X.homOfLE C.2)) ≅
      Over.mk (Limits.pullback.snd
        (AlgebraicGeometry.blowUpToBase (gluedNormalizedCentre S W t s q hbound ht))
        (S.X.homOfLE C.2))) := by
  have hpre : S.goodBlowupToBase ⁻¹ᵁ (C.1.U : S.X.Opens) ≤ S.goodBlowupToBase ⁻¹ᵁ W :=
    S.goodBlowupToBase.preimage_mono C.2
  have h1 : S.goodBlowup.homOfLE hpre ≫ (S.goodBlowupToBase ⁻¹ᵁ W).ι
      = (S.goodBlowupToBase ⁻¹ᵁ (C.1.U : S.X.Opens)).ι := Scheme.homOfLE_ι _ _
  have h2 : S.X.homOfLE C.2 ≫ W.ι = (C.1.U : S.X.Opens).ι := Scheme.homOfLE_ι _ _
  have hmid : (S.goodBlowupToBase ∣_ (C.1.U : S.X.Opens)) ≫ S.X.homOfLE C.2
      = S.goodBlowup.homOfLE hpre ≫ (S.goodBlowupToBase ∣_ W) := by
    rw [← cancel_mono W.ι, Category.assoc, h2, morphismRestrict_ι, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, h1]
  have hbig : IsPullback (S.goodBlowupToBase ∣_ (C.1.U : S.X.Opens))
      (S.goodBlowup.homOfLE hpre ≫ (S.goodBlowupToBase ⁻¹ᵁ W).ι)
      (S.X.homOfLE C.2 ≫ W.ι) S.goodBlowupToBase := by
    rw [h1, h2]
    exact isPullback_morphismRestrict S.goodBlowupToBase (C.1.U : S.X.Opens)
  have hsq : IsPullback (S.goodBlowupToBase ∣_ (C.1.U : S.X.Opens))
      (S.goodBlowup.homOfLE hpre) (S.X.homOfLE C.2) (S.goodBlowupToBase ∣_ W) :=
    IsPullback.of_bot hbig hmid (isPullback_morphismRestrict S.goodBlowupToBase W)
  -- the glued centre restricts to the normalized centre of the chart
  obtain ⟨hmap, hP⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap (S.X.homOfLE C.2)
    (gluedNormalizedCentre S W t s q hbound ht)
  -- the base change of `b ∣_ W` over the chart is `b ∣_ U`, the blowing up of the chart in its
  -- centre, and so in its normalized centre
  obtain ⟨E₁⟩ := nonempty_overIso_pullback_snd hsq.flip
  obtain ⟨E₄⟩ := nonempty_overIso_pullback_snd hP.flip
  obtain ⟨e₂, he₂, -⟩ := C.1.existsUnique_iso_preimage_blowUp
  let E₂ : Over.mk (S.goodBlowupToBase ∣_ (C.1.U : S.X.Opens)) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase C.1.blowupCentreIdealSheaf) := Over.isoMk e₂ he₂
  obtain ⟨e₃⟩ := C.1.nonempty_overIso_blowUpToBase_normalizedCentreIdealSheaf q hs
  exact ⟨E₁ ≪≫ E₂ ≪≫ e₃ ≪≫
    eqToIso (congrArg (fun I : (C.1.U : S.X.Opens).toScheme.IdealSheafData =>
      Over.mk (AlgebraicGeometry.blowUpToBase I))
      (comap_gluedNormalizedCentre S W t s q hbound ht hC).symm) ≪≫ E₄.symm⟩

/-- **Stacks tag 0GTY, the quasi-compact-open admissibility assertion.**  In Situation 0F8S let
`b : X' ⟶ X` be the morphism of tag 0GTY and let `W ⊂ X` be a quasi-compact open.  Then
`b|_{b⁻¹(W)} : b⁻¹(W) ⟶ W` is a `W \ D`-admissible blowing up.

The centre is `AlgebraicGeometry.ComplexAndDivisorSituation.gluedNormalizedCentre`, glued from
the normalized centres of the charts of a finite cover of `W` by chart domains; it is of finite
presentation and supported on the divisor, and over each chart of the cover the restriction of
`b` is the blowing up in it, so the identification descends to `W`. -/
@[stacks 0GTY "the quasi-compact-open admissibility assertion: for a quasi-compact open \
`W ⊂ X` the restriction `b|_{b^{-1}(W)} : b^{-1}(W) ⟶ W` of the morphism of the tag is a \
`W \\ D`-admissible blowing up. The centre is glued from the normalized determinantal products \
of the charts of a finite cover of `W`, with the product taken over a finite degree window \
containing the supports of those finitely many charts' complexes"]
theorem isAdmissibleBlowup_morphismRestrict_goodBlowupToBase
    (S : ComplexAndDivisorSituation.{u, d}) (W : S.X.Opens) (hW : IsCompact (W : Set S.X)) :
    Stacks.Blowup.IsAdmissibleBlowup (W.ι ⁻¹ᵁ S.D.support.compl)
      (S.goodBlowupToBase ∣_ W) := by
  classical
  obtain ⟨t, ht⟩ := S.exists_finset_chart_cover W hW
  obtain ⟨s, q, hwin, hbound⟩ := exists_window_bound S W t
  refine (Stacks.Blowup.isAdmissibleBlowup_iff _ _).mpr
    ⟨gluedNormalizedCentre S W t s q hbound ht,
      finitePresentation_subschemeι_gluedNormalizedCentre S W t s q hbound ht,
      disjoint_support_gluedNormalizedCentre S W t s q hbound ht, ?_⟩
  obtain ⟨e⟩ := AlgebraicGeometry.nonempty_overIso_blowUpToBase_of_openCover
    (gluedNormalizedCentre S W t s q hbound ht) (S.goodBlowupToBase ∣_ W)
    (Scheme.Cover.mkOfCovers {C : {C : AffineChart S // (C.U : S.X.Opens) ≤ W} // C ∈ t}
      (fun C => (C.1.1.U : S.X.Opens).toScheme) (fun C => S.X.homOfLE C.1.2) (by
        intro x
        obtain ⟨C, hCt, hxC⟩ := ht (W.ι.base x) x.2
        exact ⟨⟨C, hCt⟩, ⟨W.ι.base x, hxC⟩, Subtype.ext (S.X.homOfLE_apply _ _)⟩))
    fun i => nonempty_overIso_pullback_snd_gluedNormalizedCentre S W t s q hbound ht i.2
      (hwin i.1 i.2)
  have heIso : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  exact ⟨asIso e.hom.left, e.hom.w⟩

end Glue

end AlgebraicGeometry.ComplexAndDivisorSituation

end
