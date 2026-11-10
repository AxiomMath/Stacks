module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPrincipalityTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence
public import StacksFrontier.AlgebraicGeometry.IdealSheafFromAffineFamily
public import StacksFrontier.Homology.Eta.Perfect.DirectSumIdealUnitChange

/-!
# The obstruction subscheme of a good triple

Let `(X, D, M)` be a good triple as in Situation 0F8S.  On every affine chart `(U, A, f, M^•)`
with principal determinantal ideals, the total obstruction ideal `J(M^•, f) ⊆ A ⧸ fA` of More on
Algebra, Tag 0F81 cuts out a closed subscheme of `D ∩ U`.  This file shows that these ideals do
not depend on the chart, so that they glue to a quasi-coherent ideal sheaf on `D`: the ideal
sheaf of the closed subscheme `T ⊆ D` of More on Flatness, Tag 0GTZ.

Chart independence has three ingredients: restricting a chart to a smaller affine open base
changes its obstruction ideal along the (flat) restriction map
(`map_etaDirectSumIdeal_eq_baseChange`); two charts over the same affine open have complexes
isomorphic in `D(A)`, so their degreewise obstruction ideals agree for a common equation
(Tag 0GSW); and the two equations of the divisor differ by a unit, which the obstruction ideals
do not see (`etaTotalDirectSumIdeal_unit_mul`).

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.obstructionFamily`: the obstruction ideal over an
  affine open of `D` lying under a good chart.
* `AlgebraicGeometry.ComplexAndDivisorSituation.obstructionIdealSheaf`: the glued ideal sheaf of
  `T ⊆ D`.

## Main results

* `AffineChart.map_obstructionIdeal_restrict`: restriction of a chart and of its obstruction
  ideal.
* `AffineChart.obstructionIdeal_heq_of_U_eq`: two good charts on the same affine open have the
  same obstruction ideal.
* `AffineChart.map_obstructionIdeal_eq_of_le_affineOpen`: two good charts have the same
  obstruction ideal on every common affine open of `D`.
* `ComplexAndDivisorSituation.ideal_obstructionIdealSheaf`: on every good chart the glued ideal
  sheaf is the obstruction ideal of the chart.
* `ComplexAndDivisorSituation.locallyOfFinitePresentation_and_comap_eq_bot_obstructionIdealSheaf`:
  the closed immersion `T ⟶ D` is of finite presentation and part (1) of Tag 0GTZ holds.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0GSW](https://stacks.math.columbia.edu/tag/0GSW)
* [Stacks Project, Tag 0GST](https://stacks.math.columbia.edu/tag/0GST)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect Stacks.Decalage.DirectSumIdeal

universe u d

namespace AlgebraicGeometry

/-- Restricting an ideal to a smaller open and then taking germs at a point is taking germs at
that point directly. -/
private theorem map_germ_map_presheaf_map {Y : Scheme.{u}} {V W : Y.Opens} (h : V ≤ W)
    (K : Ideal Γ(Y, W)) (y : Y) (hy : y ∈ V) :
    (K.map (Y.presheaf.map (homOfLE h).op).hom).map (Y.presheaf.germ V y hy).hom =
      K.map (Y.presheaf.germ W y (h hy)).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res]

namespace ComplexAndDivisorSituation.AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- **The obstruction ideal of a chart restricted to a smaller affine open.**  Restricting the
obstruction ideal `J(M^•, f)` of a chart with principal determinantal ideals from `D ∩ U` to
`D ∩ V` gives the obstruction ideal of the chart restricted to `V`: the restriction of rings
`Γ(X, U) → Γ(X, V)` is flat, so the obstruction ideals base change along it
(`map_etaDirectSumIdeal_eq_baseChange`). -/
theorem map_obstructionIdeal_restrict (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    C.obstructionIdeal.map (S.D.subscheme.presheaf.map
        (homOfLE (S.D.subschemeι.preimage_mono hle)).op).hom =
      (C.restrict V hle).obstructionIdeal := by
  let φ := (S.X.presheaf.map (homOfLE hle).op).hom
  let : Algebra Γ(S.X, C.U) Γ(S.X, V) := φ.toAlgebra
  have hoi := isOpenImmersion_SpecMap_presheaf_map C.U.2 V.2 hle
  have : Module.Flat Γ(S.X, C.U) Γ(S.X, V) := AlgebraicGeometry.Flat.SpecMap_iff.1 inferInstance
  -- the restriction of `D` read on the two quotients is the reduction of `φ` modulo `f`
  have hsq : (S.D.subscheme.presheaf.map
        (homOfLE (S.D.subschemeι.preimage_mono hle)).op).hom.comp
          (C.divisorQuotEquiv.symm : _ →+* _) =
      ((C.restrict V hle).divisorQuotEquiv.symm.toRingHom).comp
        (quotientSpanMap φ C.f : _ →+*
          Γ(S.X, (C.restrict V hle).U) ⧸ Ideal.span {(C.restrict V hle).f}) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    change (S.D.subscheme.presheaf.map (homOfLE (S.D.subschemeι.preimage_mono hle)).op).hom
        (C.divisorQuotEquiv.symm (Ideal.Quotient.mk _ a)) =
      (C.restrict V hle).divisorQuotEquiv.symm (Ideal.Quotient.mk _ (φ a))
    rw [divisorQuotEquiv_symm_mk C a, divisorQuotEquiv_symm_mk (C.restrict V hle) (φ a)]
    exact (congrArg (fun g => (CommRingCat.Hom.hom g) a)
      (S.D.subschemeι.naturality (homOfLE hle).op)).symm
  have key : ∀ i, (etaDirectSumIdeal C.complex C.f i).map (quotientSpanMap φ C.f) =
      etaDirectSumIdeal (C.complex.baseChange φ) (φ C.f) i := fun i =>
    map_etaDirectSumIdeal_eq_baseChange (B := Γ(S.X, V)) C.complex C.f C.regular hI i
  have hJ : etaTotalDirectSumIdeal (C.restrict V hle).complex (C.restrict V hle).f =
      (etaTotalDirectSumIdeal C.complex C.f).map (quotientSpanMap φ C.f) := by
    change etaTotalDirectSumIdeal (C.complex.baseChange φ) (φ C.f) = _
    rw [etaTotalDirectSumIdeal, etaTotalDirectSumIdeal, Ideal.map_iSup]
    exact iSup_congr fun i => (key i).symm
  rw [obstructionIdeal, obstructionIdeal, Ideal.map_map, hJ]
  exact (congrArg (fun g => Ideal.map g (etaTotalDirectSumIdeal C.complex C.f)) hsq).trans
    (Ideal.map_map _ _).symm

/-- Two generators of one principal ideal, the first a nonzerodivisor, differ by a unit. -/
private theorem exists_unit_mul_eq_of_span_eq {R : Type*} [CommRing R] {f g : R}
    (hf : IsRegular f) (h : Ideal.span {f} = Ideal.span {g}) : ∃ u : Rˣ, g = u * f := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self g :
    g ∈ Ideal.span {f})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (h.symm ▸ Ideal.mem_span_singleton_self f :
    f ∈ Ideal.span {g})
  have hab : b * a = 1 := hf.2 (show b * a * f = 1 * f by rw [one_mul, mul_assoc, ha, hb])
  exact ⟨⟨a, b, by rw [mul_comm, hab], hab⟩, ha.symm⟩

/-- **The obstruction ideal of a chart depends only on its affine open.**  Two affine charts of a
triple with the same affine open `U`, the first with principal determinantal ideals, have the
same obstruction ideal in the coordinate ring of `D ∩ U`.  Their complexes are isomorphic in
`D(Γ(X, U))`, both representing `M|_U` (Tag 06Z0), so their degreewise obstruction ideals agree
for a common equation by Tag 0GSW; and their two equations generate the ideal of `D` on `U`, so
they differ by a unit, which the obstruction ideals do not see
(`etaTotalDirectSumIdeal_unit_mul`).  The two ideals live over the coordinate rings of `D ∩ U`
for the two copies of `U`, hence the heterogeneous equality. -/
theorem obstructionIdeal_heq_of_U_eq (C C' : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (hU : C.U = C'.U) :
    HEq C.obstructionIdeal C'.obstructionIdeal := by
  obtain ⟨U, f, hf, hD, M, hM⟩ := C
  obtain ⟨U', f', hf', hD', M', hM'⟩ := C'
  obtain rfl : U = U' := hU
  apply heq_of_eq
  let C : AffineChart S := ⟨U, f, hf, hD, M, hM⟩
  let C' : AffineChart S := ⟨U, f', hf', hD', M', hM'⟩
  have hiso := Stacks.Duality.nonempty_iso_of_nonempty_iso_tilde U.2
    (representsDerivedIso C) (representsDerivedIso C')
  obtain ⟨v, rfl⟩ := exists_unit_mul_eq_of_span_eq hf (hD.symm.trans hD')
  have hI' : ∀ i : ℤ, (idealI M' f i).IsPrincipal := fun i =>
    Stacks.Eta.DeterminantalIdeal.isPrincipal_idealI_of_derived_iso f hf.mem_nonZeroDivisors
      M M' i hiso (hI i)
  have hJ : etaTotalDirectSumIdeal M f = etaTotalDirectSumIdeal M' f :=
    iSup_congr (etaDirectSumIdeal_eq_of_derived_iso f hf M M' hiso hI)
  have hsq : (C'.divisorQuotEquiv.symm.toRingHom).comp (quotSpanUnitMulEquiv f v : _ →+* _) =
      C.divisorQuotEquiv.symm.toRingHom := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    change C'.divisorQuotEquiv.symm (Ideal.Quotient.mk _ a) =
      C.divisorQuotEquiv.symm (Ideal.Quotient.mk _ a)
    rw [divisorQuotEquiv_symm_mk, divisorQuotEquiv_symm_mk]
  change (etaTotalDirectSumIdeal M f).map C.divisorQuotEquiv.symm.toRingHom =
    (etaTotalDirectSumIdeal M' ((v : Γ(S.X, U)) * f)).map C'.divisorQuotEquiv.symm.toRingHom
  rw [etaTotalDirectSumIdeal_unit_mul M' hf hI' v, Ideal.map_map, hsq, hJ]

/-- **Two good charts have the same obstruction ideal near every common point of the divisor.**
At a point `z` of `D` lying over both affine opens, the stalks of the two obstruction ideals at `z`
agree: both are the stalks of the obstruction ideal of either chart restricted to a common
affine neighbourhood `V` of `z` in `U₁ ∩ U₂` (`map_obstructionIdeal_restrict`), and the two
restricted charts share their affine open `V` (`obstructionIdeal_heq_of_U_eq`). -/
theorem map_germ_obstructionIdeal_eq (C₁ C₂ : AffineChart S)
    (hI₁ : ∀ i : ℤ, (C₁.determinantalIdeal i).IsPrincipal)
    (hI₂ : ∀ i : ℤ, (C₂.determinantalIdeal i).IsPrincipal) (z : S.D.subscheme)
    (h₁ : z ∈ S.D.subschemeι ⁻¹ᵁ C₁.U.1) (h₂ : z ∈ S.D.subschemeι ⁻¹ᵁ C₂.U.1) :
    C₁.obstructionIdeal.map (S.D.subscheme.presheaf.germ _ z h₁).hom =
      C₂.obstructionIdeal.map (S.D.subscheme.presheaf.germ _ z h₂).hom := by
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hzV, hVsub⟩ :=
    S.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show S.D.subschemeι z ∈ ((C₁.U.1 ⊓ C₂.U.1 : S.X.Opens) : Set S.X) from ⟨h₁, h₂⟩)
      (C₁.U.1 ⊓ C₂.U.1).isOpen
  let V' : S.X.affineOpens := ⟨V, hVaff⟩
  have hz : z ∈ S.D.subschemeι ⁻¹ᵁ (V' : S.X.Opens) := hzV
  have hle₁ : (V' : S.X.Opens) ≤ C₁.U.1 := fun x hx => (hVsub hx).1
  have hle₂ : (V' : S.X.Opens) ≤ C₂.U.1 := fun x hx => (hVsub hx).2
  rw [← map_germ_map_presheaf_map (S.D.subschemeι.preimage_mono hle₁) _ z hz,
    ← map_germ_map_presheaf_map (S.D.subschemeι.preimage_mono hle₂) _ z hz,
    map_obstructionIdeal_restrict C₁ hI₁ V' hle₁, map_obstructionIdeal_restrict C₂ hI₂ V' hle₂,
    eq_of_heq (obstructionIdeal_heq_of_U_eq (C₁.restrict V' hle₁)
    (C₂.restrict V' hle₂) (fun i => C₁.isPrincipal_restrict_determinantalIdeal V' hle₁ (hI₁ i))
    rfl)]

/-- **Two good charts have the same obstruction ideal on every common affine open of the
divisor.**  The obstruction ideals of two charts with principal determinantal ideals, restricted
to an affine open `W` of `D` lying over both affine opens, agree: equality of ideals of an affine
open is checked on stalks (`AlgebraicGeometry.IsAffineOpen.ideal_ext_iff`), where it is
`map_germ_obstructionIdeal_eq`. -/
theorem map_obstructionIdeal_eq_of_le_affineOpen (C₁ C₂ : AffineChart S)
    (hI₁ : ∀ i : ℤ, (C₁.determinantalIdeal i).IsPrincipal)
    (hI₂ : ∀ i : ℤ, (C₂.determinantalIdeal i).IsPrincipal) (W : S.D.subscheme.affineOpens)
    (h₁ : (W : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ C₁.U.1)
    (h₂ : (W : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ C₂.U.1) :
    C₁.obstructionIdeal.map (S.D.subscheme.presheaf.map (homOfLE h₁).op).hom =
      C₂.obstructionIdeal.map (S.D.subscheme.presheaf.map (homOfLE h₂).op).hom := by
  refine W.2.ideal_ext_iff.mpr fun z hz => ?_
  rw [map_germ_map_presheaf_map, map_germ_map_presheaf_map]
  exact map_germ_obstructionIdeal_eq C₁ C₂ hI₁ hI₂ z (h₁ hz) (h₂ hz)

end ComplexAndDivisorSituation.AffineChart

namespace ComplexAndDivisorSituation

variable (S : ComplexAndDivisorSituation.{u, d})

/-- An affine open of the divisor `D` *lies under a good chart* if it is contained in `D ∩ U` for
an affine chart `(U, A, f, M^•)` all of whose determinantal ideals are principal. -/
def IsUnderGoodChart (W : S.D.subscheme.affineOpens) : Prop :=
  ∃ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) ∧
    (W : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ C.U.1

/-- The obstruction ideal over an affine open of the divisor: the restriction of the obstruction
ideal `J(M^•, f)` of any good chart lying over it.  It is written as the infimum over all such
charts, so that no chart has to be chosen; by `obstructionFamily_eq` the infimum is each of its
members. -/
def obstructionFamily (W : S.D.subscheme.affineOpens) : Ideal Γ(S.D.subscheme, W) :=
  ⨅ (C : {C : AffineChart S // ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal})
    (h : (W : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ C.1.U.1),
    C.1.obstructionIdeal.map (S.D.subscheme.presheaf.map (homOfLE h).op).hom

variable {S}

/-- Over an affine open of the divisor lying under a good chart, the obstruction family is the
restriction of the obstruction ideal of that chart. -/
theorem obstructionFamily_eq (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (W : S.D.subscheme.affineOpens)
    (h : (W : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ C.U.1) :
    S.obstructionFamily W =
      C.obstructionIdeal.map (S.D.subscheme.presheaf.map (homOfLE h).op).hom :=
  le_antisymm
    (iInf₂_le (⟨C, hI⟩ : {C : AffineChart S // ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal}) h)
    (le_iInf₂ fun C' h' =>
      (AffineChart.map_obstructionIdeal_eq_of_le_affineOpen C C'.1 hI C'.2 W h h').le)

/-- The obstruction family is compatible with restriction between affine opens lying under good
charts. -/
theorem map_obstructionFamily (U V : S.D.subscheme.affineOpens) (hVU : V ≤ U)
    (hU : S.IsUnderGoodChart U) :
    (S.obstructionFamily U).map (S.D.subscheme.presheaf.map (homOfLE hVU).op).hom =
      S.obstructionFamily V := by
  obtain ⟨C, hI, hUC⟩ := hU
  rw [obstructionFamily_eq C hI U hUC, obstructionFamily_eq C hI V (le_trans hVU hUC),
    Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

variable (S) in
/-- **The ideal sheaf of the closed subscheme `T ⊆ D` of More on Flatness, Tag 0GTZ.**  For a
good triple `(X, D, M)`, the obstruction ideals `J(M^•, f)` of the good affine charts glue to a
quasi-coherent ideal sheaf on `D`: they agree on overlaps
(`map_obstructionIdeal_eq_of_le_affineOpen`), and the affine opens of `D` lying under good
charts cover `D`, the triple being good. -/
def obstructionIdealSheaf (hS : S.IsGoodTriple) : S.D.subscheme.IdealSheafData :=
  Scheme.IdealSheafData.ofAffineFamily S.IsUnderGoodChart S.obstructionFamily
    (fun z => by
      obtain ⟨C, hI, hz⟩ := S.exists_good_chart_mem_preimage hS z
      exact ⟨C.divisorAffineOpen, ⟨C, hI, le_rfl⟩, hz⟩)
    (fun U f ⟨C, hI, hUC⟩ =>
      ⟨C, hI, le_trans (S.D.subscheme.basicOpen_le f) hUC⟩)
    (fun U V hVU hU _ => map_obstructionFamily U V hVU hU)

/-- **On every good chart the glued ideal sheaf is the obstruction ideal.**  The ideal of
`obstructionIdealSheaf` over `D ∩ U` is the total obstruction ideal `J(M^•, f)` of Tag 0F81, for
every affine chart `(U, A, f, M^•)` of the good triple with principal determinantal ideals. -/
theorem ideal_obstructionIdealSheaf (hS : S.IsGoodTriple) (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) :
    (S.obstructionIdealSheaf hS).ideal C.divisorAffineOpen = C.obstructionIdeal := by
  have hle : (C.divisorAffineOpen : S.D.subscheme.Opens) ≤ S.D.subschemeι ⁻¹ᵁ C.U.1 :=
    fun _ hx => hx
  have hid : S.D.subscheme.presheaf.map (homOfLE hle).op = 𝟙 _ :=
    S.D.subscheme.presheaf.map_id _
  rw [obstructionIdealSheaf, Scheme.IdealSheafData.ideal_ofAffineFamily _ _ _ _ _
    ⟨C, hI, hle⟩, obstructionFamily_eq C hI C.divisorAffineOpen hle, hid]
  exact Ideal.map_id _

/-- **More on Flatness, Tag 0GTZ, the closed immersion and part (1).**  For a good triple
`(X, D, M)` the closed immersion `i : T → D` cut out by the glued obstruction ideal sheaf is of
finite presentation, and `T` scheme-theoretically contains `D ∩ W`, where `W ⊆ X` is the maximal
open over which the cohomology sheaves of `M` are locally free. -/
theorem locallyOfFinitePresentation_and_comap_eq_bot_obstructionIdealSheaf
    (hS : S.IsGoodTriple) :
    LocallyOfFinitePresentation (S.obstructionIdealSheaf hS).subschemeι ∧
      (S.obstructionIdealSheaf hS).comap (S.D.subschemeι ⁻¹ᵁ S.locallyFreeLocus).ι = ⊥ :=
  S.locallyOfFinitePresentation_and_comap_eq_bot_of_ideal_eq_obstructionIdeal hS
    (S.obstructionIdealSheaf hS) fun C hI => ideal_obstructionIdealSheaf hS C hI

end ComplexAndDivisorSituation

end AlgebraicGeometry

end
