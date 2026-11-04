module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartObstructionIdeal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme
public import StacksFrontier.AlgebraicGeometry.IdealSheafFromAffineFamily

/-!
# The closed subscheme of the divisor of Tag 0GTZ

Let `(X, D, M)` be a good triple as in Situation 0F8S.  More on Flatness, Tag 0GTZ asserts the
existence of a closed immersion `i : T ⟶ D` of finite presentation which scheme-theoretically
contains `D ∩ W`, where `W ⊆ X` is the maximal open over which the cohomology sheaves of `M` are
locally free.  This file constructs `T`.

On a good affine chart `(U, A, f, M^•)` the subscheme is cut out by the total obstruction ideal
`J(M^•, f) ⊆ A ⧸ fA` of More on Algebra, Tag 0F81, read on `D ∩ U` as
`AffineChart.obstructionIdeal`.  The affine opens `D ∩ U` of the good charts cover `D` and are
closed under passing to standard opens, and the obstruction ideals are compatible with
restriction, so `AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily` glues them into a
quasi-coherent sheaf of ideals on `D`, whose closed subscheme is `T`.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodChartOpen`: the affine opens of `D` of the
  form `D ∩ U` for a chart `(U, A, f, M^•)` with principal determinantal ideals.
* `AlgebraicGeometry.ComplexAndDivisorSituation.goodChartObstructionIdeal`: the family of ideals
  glued by `ofAffineFamily`, taken over an arbitrary affine open `V` of `D` to be the infimum of
  the extensions to `V` of the obstruction ideals of the good charts whose open contains `V`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.map_obstructionIdeal_eq`: **the
  obstruction ideals of two good charts are compatible with restriction in `D`.**  The
  compatibility proved at the ring level in
  `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartObstructionIdeal` is for two charts
  nested in `X`; here only `D ∩ U' ⊆ D ∩ U` is given, and the two are bridged by the locality of
  an equality of ideals over an affine open (`AlgebraicGeometry.IsAffineOpen.ideal_ext_iff`).
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isGoodChartOpen_ideal_eq_obstructionIdeal`:
  **More on Flatness, Tag 0GTZ, the existence of the closed immersion `i : T ⟶ D` of finite
  presentation together with part (1).**

## The naturality square

`ofAffineFamily` asks for the compatibility of the ideals along the restriction maps of `𝒪_D`,
whereas `AffineChart.restrictQuotMap` is the reduction `A ⧸ fA → A' ⧸ f'A'` of the restriction
map of `𝒪_X` modulo the equations of two charts.  The two are identified across
`AffineChart.divisorQuotEquiv` by
`AffineChart.presheaf_map_comp_divisorQuotEquiv_symm`, which comes from the naturality of
`AlgebraicGeometry.Scheme.Hom.app` at the inclusion `i_D : D ⟶ X` together with Mathlib's
description `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app` of that map over an affine
open as the quotient map followed by `subschemeObjIso`.

## Parts (2) and (3)

Parts (2) and (3) of Tag 0GTZ concern the cohomology sheaves of `Li^*Lη_I M`, and rest on
identifying `Li^*Lη_I M` over a good chart with the chart-local décalage of
`Stacks.Decalage.DirectSumIdeal.finite_projective_etaHomology_quotient_etaTotalDirectSumIdeal`;
the ingredient they need beyond the affine comparison of Tag 08DW is recorded as
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage` in
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect`.  Part (3) is read
off Cohomology, Lemma 20.55.10 — [Stacks, Tag 0GTA], formalized in both halves as
`Stacks.IdealTorsion.Eta.isFiniteFreeStalkOfRank_homology_derivedEtaOfRegular` and
`Stacks.IdealTorsion.Eta.rank_homology_derivedEtaOfRegular_eq` — combined with part (1): the
rank statement of Tag 0GTA is about `Lη_I M` at a point of `X`, and part (1) turns it into one
about `Li^*Lη_I M` at a point of `T`, the closed immersion `i` being an isomorphism over
`D ∩ W`.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0GTA](https://stacks.math.columbia.edu/tag/0GTA)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect Stacks.Decalage.DirectSumIdeal

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-! ### The naturality square -/

/-- The affine open `D ∩ U'` of a chart whose open is contained in that of another chart is
contained in the affine open `D ∩ U` of the latter: taking inverse images is monotone. -/
theorem divisorAffineOpen_mono {C C' : AffineChart S}
    (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    S.D.subschemeι ⁻¹ᵁ (C'.U : S.X.Opens) ≤ S.D.subschemeι ⁻¹ᵁ (C.U : S.X.Opens) :=
  fun _ hz ↦ hle hz

/-- **The inverse of `divisorQuotEquiv` on a representative is the restriction map of the closed
immersion `D ⟶ X`.**  Over the affine open `U` that map sends a section to its class modulo the
ideal of `D`, by `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app`, and
`AffineChart.divisorQuotEquiv` is the resulting identification of `Γ(D, D ∩ U)` with `A ⧸ fA`. -/
theorem divisorQuotEquiv_symm_mk (C : AffineChart S) (a : Γ(S.X, C.U)) :
    C.divisorQuotEquiv.symm (Ideal.Quotient.mk (Ideal.span {C.f}) a) =
      S.D.subschemeι.app (C.U : S.X.Opens) a := by
  rw [S.D.subschemeι_app C.U, CommRingCat.comp_apply]
  rfl

/-- **The naturality square of the obstruction ideals.**  For two charts `(U, A, f, M^•)` and
`(U', A', f', N^•)` with `U' ⊆ U`, the restriction map of `𝒪_D` from `D ∩ U` to `D ∩ U'` is the
reduction `A ⧸ fA → A' ⧸ f'A'` of the restriction map of `𝒪_X`, read across the identifications
`AffineChart.divisorQuotEquiv` of the coordinate rings of `D ∩ U` and `D ∩ U'` with `A ⧸ fA` and
`A' ⧸ f'A'`.

This is the square which turns the ring-level compatibility of the obstruction ideals,
`AffineChart.map_etaTotalDirectSumIdeal_eq`, into the compatibility along the restriction maps
of `𝒪_D` that `AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily` asks for.  It is the
naturality of `AlgebraicGeometry.Scheme.Hom.app` at `i_D : D ⟶ X`, written out through
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app`. -/
theorem presheaf_map_comp_divisorQuotEquiv_symm (C C' : AffineChart S)
    (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    (S.D.subscheme.presheaf.map (homOfLE (divisorAffineOpen_mono hle)).op).hom.comp
        (C.divisorQuotEquiv.symm : _ →+* _) =
      ((C'.divisorQuotEquiv.symm : _ →+* _)).comp (restrictQuotMap C C' hle) := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hq : restrictQuotMap C C' hle (Ideal.Quotient.mk (Ideal.span {C.f}) a) =
      Ideal.Quotient.mk (Ideal.span {C'.f}) ((S.X.presheaf.map (homOfLE hle).op) a) := rfl
  simp only [RingHom.comp_apply, RingHom.coe_coe, hq, divisorQuotEquiv_symm_mk]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, S.D.subschemeι.naturality]
  rfl

/-! ### Compatibility of the obstruction ideals with restriction -/

/-- **The obstruction ideals of two good charts nested in `X` are compatible with restriction.**
If the open of a chart `C'` is contained in that of a chart `C`, both with principal
determinantal ideals, the obstruction ideal of `C` extends along the restriction map of `𝒪_D`
from `D ∩ U` to `D ∩ U'` to the obstruction ideal of `C'`.

This is the ring-level compatibility `AffineChart.map_etaTotalDirectSumIdeal_eq` read across the
naturality square `AffineChart.presheaf_map_comp_divisorQuotEquiv_symm`. -/
theorem map_obstructionIdeal_presheaf_map (C C' : AffineChart S)
    (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens))
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hI' : ∀ i : ℤ, (C'.determinantalIdeal i).IsPrincipal) :
    C.obstructionIdeal.map
        (S.D.subscheme.presheaf.map (homOfLE (divisorAffineOpen_mono hle)).op).hom =
      C'.obstructionIdeal := by
  rw [obstructionIdeal, Ideal.map_map, presheaf_map_comp_divisorQuotEquiv_symm C C' hle,
    ← Ideal.map_map, map_etaTotalDirectSumIdeal_eq C C' hle hI hI', obstructionIdeal]

/-- **The obstruction ideals of two good charts are compatible with restriction in `D`.**  If
the affine open `D ∩ U'` of a chart `C'` is contained in the affine open `D ∩ U` of a chart `C`,
both with principal determinantal ideals, the obstruction ideal of `C` extends along the
restriction map of `𝒪_D` to the obstruction ideal of `C'`.

Containment of `D ∩ U'` in `D ∩ U` does not give containment of `U'` in `U`, so
`AffineChart.map_obstructionIdeal_presheaf_map` does not apply directly.  An equality of ideals
over an affine open is local (`AlgebraicGeometry.IsAffineOpen.ideal_ext_iff`), and every point of
`D ∩ U'` lies in a standard open `D(g') ⊆ U ∩ U'` of `U'`; the restriction of `C'` to `D(g')` is
a good chart nested in both `C` and `C'`, over which the two sides agree. -/
theorem map_obstructionIdeal_eq (C C' : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hI' : ∀ i : ℤ, (C'.determinantalIdeal i).IsPrincipal)
    (h : S.D.subschemeι ⁻¹ᵁ (C'.U : S.X.Opens) ≤ S.D.subschemeι ⁻¹ᵁ (C.U : S.X.Opens)) :
    C.obstructionIdeal.map (S.D.subscheme.presheaf.map (homOfLE h).op).hom =
      C'.obstructionIdeal := by
  refine (S.D.isAffineOpen_preimage_subschemeι C'.U).ideal_ext_iff.mpr fun z hz ↦ ?_
  obtain ⟨g', g, he, hzg'⟩ :=
    exists_basicOpen_le_affine_inter C'.U.2 C.U.2 (S.D.subschemeι z) ⟨hz, h hz⟩
  set C₁ := C'.restrictBasicOpen g'
  have hle₁ : (C₁.U : S.X.Opens) ≤ (C'.U : S.X.Opens) := S.X.basicOpen_le g'
  have hle₂ : (C₁.U : S.X.Opens) ≤ (C.U : S.X.Opens) := he.le.trans (S.X.basicOpen_le g)
  have hI₁ : ∀ i : ℤ, (C₁.determinantalIdeal i).IsPrincipal :=
    fun i ↦ C'.isPrincipal_restrict_determinantalIdeal _ _ (hI' i)
  have hzW : z ∈ S.D.subschemeι ⁻¹ᵁ (C₁.U : S.X.Opens) := hzg'
  have hgerm : S.D.subscheme.presheaf.map (homOfLE (divisorAffineOpen_mono hle₁)).op ≫
      S.D.subscheme.presheaf.germ (S.D.subschemeι ⁻¹ᵁ (C₁.U : S.X.Opens)) z hzW =
      S.D.subscheme.presheaf.germ (S.D.subschemeι ⁻¹ᵁ (C'.U : S.X.Opens)) z hz :=
    S.D.subscheme.presheaf.germ_res' _ z hzW
  have key : ∀ K : Ideal Γ(S.D.subscheme, S.D.subschemeι ⁻¹ᵁ (C'.U : S.X.Opens)),
      K.map (S.D.subscheme.presheaf.germ
          (S.D.subschemeι ⁻¹ᵁ (C'.U : S.X.Opens)) z hz).hom =
        (K.map (S.D.subscheme.presheaf.map
            (homOfLE (divisorAffineOpen_mono hle₁)).op).hom).map
          (S.D.subscheme.presheaf.germ (S.D.subschemeι ⁻¹ᵁ (C₁.U : S.X.Opens)) z hzW).hom :=
    fun K ↦ by rw [Ideal.map_map, ← CommRingCat.hom_comp, hgerm]
  have h1 : (C.obstructionIdeal.map (S.D.subscheme.presheaf.map (homOfLE h).op).hom).map
      (S.D.subscheme.presheaf.map (homOfLE (divisorAffineOpen_mono hle₁)).op).hom =
        C₁.obstructionIdeal := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]
    exact C.map_obstructionIdeal_presheaf_map C₁ hle₂ hI hI₁
  rw [key, key, h1, C'.map_obstructionIdeal_presheaf_map C₁ hle₁ hI' hI₁]

end AffineChart

/-! ### The glued sheaf of ideals -/

variable (S : ComplexAndDivisorSituation.{u, d})

/-- The affine opens of `D` that the good affine charts cut out: those of the form `D ∩ U` for a
chart `(U, A, f, M^•)` all of whose determinantal ideals are principal.  This is the family along
which the closed subscheme of Tag 0GTZ is glued. -/
def IsGoodChartOpen (V : S.D.subscheme.affineOpens) : Prop :=
  ∃ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) ∧
    C.divisorAffineOpen = V

/-- The family of ideals on the affine opens of `D` glued into the sheaf of ideals of Tag 0GTZ:
over an affine open `V` of `D` it is the infimum of the extensions to `V` of the obstruction
ideals of the good charts whose affine open `D ∩ U` contains `V`.  Over `D ∩ U` itself it is the
obstruction ideal of the chart (`goodChartObstructionIdeal_divisorAffineOpen`). -/
def goodChartObstructionIdeal (V : S.D.subscheme.affineOpens) :
    Ideal Γ(S.D.subscheme, V.1) :=
  ⨅ (C : AffineChart S) (_ : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (h : (V.1 : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ (C.U : S.X.Opens)),
      C.obstructionIdeal.map (S.D.subscheme.presheaf.map (homOfLE h).op).hom

/-- **Over the affine open of a good chart the glued family is the obstruction ideal of that
chart.**  The chart itself is one of the charts the infimum runs over, and every other good chart
whose open contains `D ∩ U` contributes the same ideal, by
`AffineChart.map_obstructionIdeal_eq`. -/
theorem goodChartObstructionIdeal_divisorAffineOpen (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) :
    S.goodChartObstructionIdeal C.divisorAffineOpen = C.obstructionIdeal := by
  refine le_antisymm (iInf_le_of_le C (iInf_le_of_le hI (iInf_le_of_le le_rfl
    (C.map_obstructionIdeal_eq C hI hI le_rfl).le))) ?_
  exact le_iInf fun C₂ ↦ le_iInf fun hI₂ ↦ le_iInf fun h ↦
    (C₂.map_obstructionIdeal_eq C hI₂ hI h).ge

/-- The good affine charts cover `D`: the good-triple condition read on `D`,
`exists_good_chart_mem_preimage`. -/
theorem exists_isGoodChartOpen_mem (hS : S.IsGoodTriple) (z : S.D.subscheme) :
    ∃ V : S.D.subscheme.affineOpens, S.IsGoodChartOpen V ∧ z ∈ (V.1 : S.D.subscheme.Opens) := by
  obtain ⟨C, hI, hz⟩ := S.exists_good_chart_mem_preimage hS z
  exact ⟨C.divisorAffineOpen, ⟨C, hI, rfl⟩, hz⟩

/-- The family of the affine opens `D ∩ U` of the good charts is closed under passing to standard
opens: a standard open of `D ∩ U` is `D ∩ D(g)` for a section `g` over `U`
(`AffineChart.exists_basicOpen_eq_preimage_restrictBasicOpen`), and the restriction of a good
chart to `D(g)` is a good chart. -/
theorem isGoodChartOpen_affineBasicOpen (V : S.D.subscheme.affineOpens)
    (t : Γ(S.D.subscheme, V.1)) (hV : S.IsGoodChartOpen V) :
    S.IsGoodChartOpen (S.D.subscheme.affineBasicOpen t) := by
  obtain ⟨C, hI, rfl⟩ := hV
  obtain ⟨g, hg⟩ := C.exists_basicOpen_eq_preimage_restrictBasicOpen t
  exact ⟨C.restrictBasicOpen g, fun i ↦ C.isPrincipal_restrict_determinantalIdeal _ _ (hI i),
    Subtype.ext hg.symm⟩

/-- The obstruction ideals are compatible with the restriction maps of `𝒪_D`, which is the
compatibility `AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily` asks of the family
`goodChartObstructionIdeal`. -/
theorem map_goodChartObstructionIdeal_eq (V W : S.D.subscheme.affineOpens) (h : W ≤ V)
    (hV : S.IsGoodChartOpen V) (hW : S.IsGoodChartOpen W) :
    (S.goodChartObstructionIdeal V).map
        (S.D.subscheme.presheaf.map (homOfLE h).op).hom = S.goodChartObstructionIdeal W := by
  obtain ⟨C, hI, rfl⟩ := hV
  obtain ⟨C', hI', rfl⟩ := hW
  rw [S.goodChartObstructionIdeal_divisorAffineOpen C hI,
    S.goodChartObstructionIdeal_divisorAffineOpen C' hI']
  exact C.map_obstructionIdeal_eq C' hI hI' h

/-! ### The closed subscheme of Tag 0GTZ -/

/-- **More on Flatness, Tag 0GTZ: the closed subscheme `T` of the divisor.**  For a good triple
`(X, D, M)` as in Situation 0F8S this is the quasi-coherent sheaf of ideals on `D` whose ideal
over the affine open `D ∩ U` of every affine chart `(U, A, f, M^•)` with principal determinantal
ideals is the total obstruction ideal `J(M^•, f)` of More on Algebra, Tag 0F81
(`ideal_goodChartSubscheme`).  The closed subscheme it cuts out is the `T` of the tag, and the
closed immersion `i : T ⟶ D` is
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`. -/
def goodChartSubscheme (hS : S.IsGoodTriple) : S.D.subscheme.IdealSheafData :=
  Scheme.IdealSheafData.ofAffineFamily (S.IsGoodChartOpen) (S.goodChartObstructionIdeal)
    (fun z ↦ S.exists_isGoodChartOpen_mem hS z)
    (fun V t hV ↦ S.isGoodChartOpen_affineBasicOpen V t hV)
    (fun V W h hV hW ↦ S.map_goodChartObstructionIdeal_eq V W h hV hW)

/-- **The ideal of the closed subscheme of Tag 0GTZ over a good affine chart is the obstruction
ideal of that chart.** -/
theorem ideal_goodChartSubscheme (hS : S.IsGoodTriple) (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) :
    (S.goodChartSubscheme hS).ideal C.divisorAffineOpen = C.obstructionIdeal := by
  rw [goodChartSubscheme, Scheme.IdealSheafData.ideal_ofAffineFamily _ _ _ _ _ ⟨C, hI, rfl⟩,
    S.goodChartObstructionIdeal_divisorAffineOpen C hI]

/-- **More on Flatness, Tag 0GTZ: the closed subscheme `T` of `D` exists, the closed immersion
`i : T ⟶ D` is of finite presentation, and `T` contains `D ∩ W` scheme-theoretically.**  Let
`(X, D, M)` be a good triple as in Situation 0F8S.  There is a closed subscheme `T ⊆ D` whose
ideal over `D ∩ U` is the total obstruction ideal `J(M^•, f)` of More on Algebra, Tag 0F81 for
every affine chart `(U, A, f, M^•)` with principal determinantal ideals; the closed immersion
`i : T ⟶ D` is locally of finite presentation; and the inverse image on `D ∩ W` of the ideal
sheaf of `T` is zero, where `W ⊆ X` is the maximal open over which the cohomology sheaves of `M`
are locally free.

`T` is `goodChartSubscheme`, glued from the chart-local obstruction ideals by
`AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily`; the two properties are
`locallyOfFinitePresentation_and_comap_eq_bot_of_ideal_eq_obstructionIdeal`. -/
@[stacks 0GTZ "the existence of the closed immersion `i : T ⟶ D` of finite presentation, and \
part (1). `T` is glued from the obstruction ideals of Tag 0F81 on the good affine charts by \
AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily. Parts (2) and (3) concern \
`Li^*Lη_I M`: over and above the affine comparison of Tag 08DW they need the chart-level \
comparison AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage, and part (3) then reads \
off Tag 0GTA --- formalized in both halves in \
StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafStalk --- at the points part (1) supplies, \
`i` being an isomorphism over `D` intersected with the locally free locus"]
theorem exists_isGoodChartOpen_ideal_eq_obstructionIdeal (hS : S.IsGoodTriple) :
    ∃ T : S.D.subscheme.IdealSheafData,
      (∀ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
          T.ideal C.divisorAffineOpen = C.obstructionIdeal) ∧
        LocallyOfFinitePresentation T.subschemeι ∧
          T.comap (S.D.subschemeι ⁻¹ᵁ S.locallyFreeLocus).ι = ⊥ :=
  ⟨S.goodChartSubscheme hS, fun C hI ↦ S.ideal_goodChartSubscheme hS C hI,
    S.locallyOfFinitePresentation_and_comap_eq_bot_of_ideal_eq_obstructionIdeal hS _
      fun C hI ↦ S.ideal_goodChartSubscheme hS C hI⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
