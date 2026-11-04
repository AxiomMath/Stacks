module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.EquationDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.AffineChartRestrict
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPrincipalityTransfer
public import StacksFrontier.Homology.Eta.Perfect.TotalDirectSumIdeal

/-!
# The obstruction ideals of two affine charts agree where their domains meet

Let `(X, D, M)` be a triple as in Situation 0F8S and let `(U, A, f, M^•)` and `(U', A', f', N^•)`
be two affine charts for it with `U' ⊆ U`, both with principal determinantal ideals.  The
obstruction ideal `J_i(M^•, f) ⊆ A ⧸ fA` of More on Algebra, Tag 0F81 extends along the
reduction `A ⧸ fA → A' ⧸ f'A'` of the restriction map to the obstruction ideal
`J_i(N^•, f') ⊆ A' ⧸ f'A'`.

This is the compatibility on overlaps that the gluing of the closed subschemes of More on
Flatness, Tag 0GTZ needs, and it was the last of the three inputs listed as missing in the
module headers of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme`,
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.BlowupSubscheme`,
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDivisorSubscheme` and
`StacksFrontier.Homology.Eta.Perfect.TotalDirectSumIdeal`.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.restrictQuotMap`: the reduction
  `A ⧸ fA → A' ⧸ f'A'` of the restriction map `Γ(X, U) → Γ(X, U')` modulo the equations of the
  two charts.  It is defined because the restriction of `f` generates the ideal of the divisor
  on `U'`, as does `f'`.

## Main results

* `Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_quotientMap_id`: the obstruction ideal is
  carried to the obstruction ideal by the identification of the quotients by two generators of
  one principal ideal with nonzerodivisor generator.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.map_etaDirectSumIdeal_eq` and
  `map_etaTotalDirectSumIdeal_eq`: **the obstruction ideals of two charts agree**, degreewise
  and in total.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.map_etaDirectSumIdeal_presheaf_map`
  and `etaDirectSumIdeal_baseChange_eq`: the two steps those rest on.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart`
  `.exists_basicOpen_eq_preimage_restrictBasicOpen`: the family of the opens `D ∩ U` of the
  charts is closed under passing to standard opens.

## The three steps

Write `ρ : A → A'` for the restriction map and `C|_{U'}` for the restriction of the chart `C` to
`U'` (`AffineChart.restrict`, Tag 0F8T), whose equation is `ρ f` and whose complex is the base
change `M^• ⊗_A A'`.

1. `J_i(M^•, f) · (A' ⧸ ρ(f)A') = J_i(M^• ⊗_A A', ρ f)`: the obstruction ideal extends along a
   flat ring map, `Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_eq_baseChange`, and `ρ`
   is flat, being the ring map of an open immersion of spectra.
2. `J_i(M^• ⊗_A A', ρ f) = J_i(N^•, ρ f)`: the two charts `C|_{U'}` and `C'` represent the same
   object of `D(𝒪_{U'})`, so their complexes are isomorphic in `D(A')` by the affine derived
   equivalence of Tag 06Z0 (`Stacks.Duality.nonempty_iso_of_nonempty_iso_tilde` at the two
   `AffineChart.representsDerivedIso`), and the obstruction ideal only depends on that object,
   which is Tag 0GSW.
3. `J_i(N^•, ρ f) = J_i(N^•, f')` across `A' ⧸ ρ(f)A' ≃+* A' ⧸ f'A'`: the two equations generate
   the ideal of the divisor on `U'`, hence differ by a unit, and the obstruction ideal is
   unit-invariant (`Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_unit_mul_eq`).

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0GSW](https://stacks.math.columbia.edu/tag/0GSW)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect Stacks.Decalage.DirectSumIdeal

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace Stacks.Decalage.DirectSumIdeal

/-- **The obstruction ideal is carried along the identification of the quotients by two
generators of one principal ideal.**  If `a` and `g` generate the same ideal of `B` and `g` is a
nonzerodivisor whose determinantal ideals for `N^•` are principal, then the canonical map
`B ⧸ aB → B ⧸ gB` carries `J_i(N^•, a)` to `J_i(N^•, g)`.

The two generators differ by a unit (`Stacks.LogPoles.exists_unit_mul_of_span_singleton_eq`),
and the obstruction ideal at a unit multiple of the equation is the one at the equation
(`Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_unit_mul_eq`). -/
public theorem map_etaDirectSumIdeal_quotientMap_id {B : Type u} [CommRing B]
    (N : BoundedComplex B) (g : B) (hg : IsRegular g)
    (hI : ∀ i : ℤ, (idealI N g i).IsPrincipal) (a : B)
    (hspan : Ideal.span {a} = Ideal.span {g})
    (h : Ideal.span {a} ≤ Ideal.comap (RingHom.id B) (Ideal.span {g})) (i : ℤ) :
    Ideal.map (Ideal.quotientMap (Ideal.span {g}) (RingHom.id B) h)
        (etaDirectSumIdeal N a i) = etaDirectSumIdeal N g i := by
  obtain ⟨u, hu⟩ :=
    Stacks.LogPoles.exists_unit_mul_of_span_singleton_eq hg.left.isSMulRegular hspan
  subst hu
  have he : Ideal.quotientMap (Ideal.span {g}) (RingHom.id B) h
      = (quotEquivUnitMul g u : B ⧸ Ideal.span {(u : B) * g} →+* B ⧸ Ideal.span {g}) := by
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  rw [he]
  exact map_etaDirectSumIdeal_unit_mul_eq N g hg hI u i

end Stacks.Decalage.DirectSumIdeal

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 100000] modulesHasDerivedCategory

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- The restriction of the equation of a chart to a smaller affine open generates the ideal of
the divisor there: that ideal is cut out by the equation of the restricted chart of Tag 0F8T. -/
theorem span_presheaf_map_f (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    Ideal.span {(S.X.presheaf.map (homOfLE hle).op) C.f} = S.D.ideal V :=
  (C.restrict V hle).divisor_ideal.symm

/-- The restriction map between the coordinate rings of two nested affine opens is flat: it is
the ring map of an open immersion of spectra. -/
theorem flat_presheaf_map_of_le (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    letI : Algebra Γ(S.X, C.U) Γ(S.X, V) :=
      (S.X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    Module.Flat Γ(S.X, C.U) Γ(S.X, V) := by
  let : Algebra Γ(S.X, C.U) Γ(S.X, V) :=
    (S.X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have hoi : IsOpenImmersion (Spec.map (S.X.presheaf.map (homOfLE hle).op)) :=
    isOpenImmersion_SpecMap_presheaf_map C.U.2 V.2 hle
  exact AlgebraicGeometry.Flat.SpecMap_iff.1 inferInstance

/-- **Step 1: the obstruction ideal extends along the restriction of a chart.**  The degreewise
obstruction ideal of a chart extends, along the reduction of the restriction map modulo the
equation, to the obstruction ideal of the base change of the chart complex at the restricted
equation.  This is flat base change of the obstruction ideal, the restriction map between the
coordinate rings of two nested affine opens being flat. -/
theorem map_etaDirectSumIdeal_presheaf_map (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens))
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (i : ℤ) :
    Ideal.map (quotientSpanMap (S.X.presheaf.map (homOfLE hle).op).hom C.f)
        (etaDirectSumIdeal C.complex C.f i)
      = etaDirectSumIdeal (C.complex.baseChange (S.X.presheaf.map (homOfLE hle).op).hom)
          ((S.X.presheaf.map (homOfLE hle).op) C.f) i := by
  let : Algebra Γ(S.X, C.U) Γ(S.X, V) :=
    (S.X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  let := C.flat_presheaf_map_of_le V hle
  exact map_etaDirectSumIdeal_eq_baseChange C.complex C.f C.regular hI i

/-- **Step 2: two charts over one affine open have the same obstruction ideal.**  If the domain
of a chart `C'` is contained in that of `C`, the restriction of `C` to the domain of `C'` and
`C'` itself represent the same object of `D(𝒪_{U'})`, so their complexes are isomorphic in
`D(Γ(X, U'))` by the affine derived equivalence of Tag 06Z0 and their obstruction ideals at the
restricted equation of `C` agree, by Tag 0GSW. -/
theorem etaDirectSumIdeal_baseChange_eq (C C' : AffineChart S)
    (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens))
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (i : ℤ) :
    etaDirectSumIdeal (C.complex.baseChange (S.X.presheaf.map (homOfLE hle).op).hom)
        ((S.X.presheaf.map (homOfLE hle).op) C.f) i
      = etaDirectSumIdeal C'.complex ((S.X.presheaf.map (homOfLE hle).op) C.f) i :=
  etaDirectSumIdeal_eq_of_derived_iso ((S.X.presheaf.map (homOfLE hle).op) C.f)
    (C.restrict C'.U hle).regular
    (C.complex.baseChange (S.X.presheaf.map (homOfLE hle).op).hom) C'.complex
    (Stacks.Duality.nonempty_iso_of_nonempty_iso_tilde C'.U.2
      (representsDerivedIso (C.restrict C'.U hle)) (representsDerivedIso C'))
    (fun j => C.isPrincipal_restrict_determinantalIdeal C'.U hle (hI j)) i

/-- **The reduction of the restriction map modulo the equations of two charts.**  For two charts
`(U, A, f, M^•)` and `(U', A', f', N^•)` with `U' ⊆ U`, the restriction map `A → A'` carries `f`
into `f'A'` — both generate the ideal of the divisor on `U'` — and so induces a ring map
`A ⧸ fA → A' ⧸ f'A'`.  This is the map along which the two obstruction ideals are compared, and
it is the reduction of the restriction map of `𝒪_X` that the ideal sheaf of Tag 0GTZ must
respect. -/
def restrictQuotMap (C C' : AffineChart S) (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    Γ(S.X, C.U) ⧸ Ideal.span {C.f} →+* Γ(S.X, C'.U) ⧸ Ideal.span {C'.f} :=
  Ideal.quotientMap (Ideal.span {C'.f}) (S.X.presheaf.map (homOfLE hle).op).hom
    (Ideal.span_le.2 (Set.singleton_subset_iff.2
      (Ideal.mem_comap.mpr (by
        rw [← C'.divisor_ideal, ← C.span_presheaf_map_f C'.U hle]
        exact Ideal.mem_span_singleton_self _))))

/-- **The obstruction ideals of two affine charts agree.**  Let `(U, A, f, M^•)` and
`(U', A', f', N^•)` be affine charts of a triple as in Situation 0F8S with `U' ⊆ U` and with
principal determinantal ideals.  Then the degreewise obstruction ideal `J_i(M^•, f)` of More on
Algebra, Tag 0F81 extends along the reduction `A ⧸ fA → A' ⧸ f'A'` of the restriction map to
`J_i(N^•, f')`.

This is the compatibility on overlaps that the closed subscheme of More on Flatness, Tag 0GTZ
needs in order to be glued from its chart-local descriptions.  The three steps are flat base
change of the obstruction ideal, Tag 0GSW for the two representatives of `M|_{U'}`, and
unit-invariance of the obstruction ideal; see the module documentation. -/
theorem map_etaDirectSumIdeal_eq (C C' : AffineChart S)
    (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens))
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hI' : ∀ i : ℤ, (C'.determinantalIdeal i).IsPrincipal) (i : ℤ) :
    Ideal.map (restrictQuotMap C C' hle) (etaDirectSumIdeal C.complex C.f i)
      = etaDirectSumIdeal C'.complex C'.f i := by
  have hspan : Ideal.span {(S.X.presheaf.map (homOfLE hle).op) C.f} = Ideal.span {C'.f} := by
    rw [C.span_presheaf_map_f C'.U hle, C'.divisor_ideal]
  have hcomap : Ideal.span {(S.X.presheaf.map (homOfLE hle).op) C.f} ≤
      Ideal.comap (RingHom.id Γ(S.X, C'.U)) (Ideal.span {C'.f}) := by
    rw [Ideal.comap_id]
    exact hspan.le
  have hcomp : restrictQuotMap C C' hle =
      (Ideal.quotientMap (Ideal.span {C'.f}) (RingHom.id Γ(S.X, C'.U)) hcomap).comp
        (quotientSpanMap (S.X.presheaf.map (homOfLE hle).op).hom C.f) := by
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  rw [hcomp, ← Ideal.map_map, C.map_etaDirectSumIdeal_presheaf_map C'.U hle hI i,
    C.etaDirectSumIdeal_baseChange_eq C' hle hI i]
  exact map_etaDirectSumIdeal_quotientMap_id C'.complex C'.f C'.regular hI' _ hspan hcomap i

/-- **The total obstruction ideals of two affine charts agree**: the ideal `J(M^•, f)` of More on
Algebra, Tag 0F81 extends along the reduction of the restriction map to `J(N^•, f')`.  This is
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.map_etaDirectSumIdeal_eq` summed over
the degrees, the extension of ideals commuting with suprema. -/
theorem map_etaTotalDirectSumIdeal_eq (C C' : AffineChart S)
    (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens))
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hI' : ∀ i : ℤ, (C'.determinantalIdeal i).IsPrincipal) :
    Ideal.map (restrictQuotMap C C' hle) (etaTotalDirectSumIdeal C.complex C.f)
      = etaTotalDirectSumIdeal C'.complex C'.f := by
  rw [etaTotalDirectSumIdeal, etaTotalDirectSumIdeal, Ideal.map_iSup]
  exact iSup_congr fun i => C.map_etaDirectSumIdeal_eq C' hle hI hI' i

/-- **Every standard open of `D ∩ U` is `D ∩ D(g)` for a section `g` over `U`.**  A section of
`𝒪_D` over `D ∩ U` is the image of a section of `𝒪_X` over `U`, the inclusion of a closed
subscheme being surjective on sections over an affine open
(`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective`), and the standard open it
cuts out in `D ∩ U` is the inverse image of the standard open `D(g)` of `U`.

This is the closure of the family of the opens `D ∩ U` of the charts under passing to standard
opens, which is the hypothesis `hbasic` of
`AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily`; the chart over `D(g)` is
`AffineChart.restrictBasicOpen g`, whose determinantal ideals stay principal by
`AffineChart.isPrincipal_restrict_determinantalIdeal`. -/
theorem exists_basicOpen_eq_preimage_restrictBasicOpen (C : AffineChart S)
    (h : Γ(S.D.subscheme, S.D.subschemeι ⁻¹ᵁ C.U.1)) :
    ∃ g : Γ(S.X, C.U), S.D.subscheme.basicOpen h =
      S.D.subschemeι ⁻¹ᵁ ((C.restrictBasicOpen g).U : S.X.Opens) := by
  obtain ⟨g, rfl⟩ := S.D.subschemeι_app_surjective C.U h
  exact ⟨g, (Scheme.preimage_basicOpen S.D.subschemeι g).symm⟩

end AffineChart

end AlgebraicGeometry.ComplexAndDivisorSituation

end
