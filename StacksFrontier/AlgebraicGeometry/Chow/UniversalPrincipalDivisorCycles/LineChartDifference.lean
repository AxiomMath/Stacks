module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Transition
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.FibreDifference

/-!
# The fibre difference of an arbitrary morphism to the relative projective line

Part (4) of Stacks Tag 02RQ identifies, on the closure `Y` of the graph of a rational function,
the principal divisor of that function with the difference `[Y₀]_{n-1} - [Y_∞]_{n-1}` of the
cycles of the two distinguished fibres. The graph closure plays no role in that identification:
what it supplies is a morphism `q : Y ⟶ ℙ¹_S` whose generic point lies on both affine charts, and
the rational function is the coordinate of the first chart pulled back along `q`.

This file proves the identification for an arbitrary integral `A` locally of finite type over the
base of a Chow situation and an arbitrary morphism `q : A ⟶ ℙ¹_S` whose generic point avoids both
distinguished divisors:

  `div_A(t) = [q⁻¹D₀]_{n-1} - [q⁻¹D_∞]_{n-1}`,

where `t` is the pullback along `q` of the coordinate of the first chart. Part (4) is the case
where `q` is the second projection of the graph closure.

The relation `t · t⁻¹ = 1` used here is the gluing relation of `ℙ¹_S`: the two chart coordinates
are inverse on the overlap of the charts, and the overlap is the image of the relative punctured
line.

## Main definitions

* `Stacks.Chow.chartOpen`, `Stacks.Chow.yChartOpen` — the two chart opens of `ℙ¹_S`.
* `Stacks.Chow.lineChartFunction`, `Stacks.Chow.lineYChartFunction` — the two chart coordinates
  pulled back along `q`, as rational functions on `A`.

## Main results

* `Stacks.Chow.range_puncturedComparison` — the image of the punctured line in `ℙ¹_S` is the
  intersection of the two charts.
* `Stacks.Chow.germ_lineChartCoordinate_mul` — the gluing relation of `ℙ¹_S`, as germs: at a
  point of the overlap the germs of the two chart coordinates are inverse.
* `Stacks.Chow.lineChartFunction_mul_lineYChartFunction` — consequently the two rational
  functions on `A` are inverse.
* `Stacks.Chow.principalDivisorCycle_eq_sub_lineFibreCycles` — the fibre-difference identity.

## Implementation notes

The memberships of the generic point of `A` in the two chart preimages are taken as hypotheses
rather than derived from the two divisor hypotheses: they say that `A` does not map into either
distinguished section.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace Opposite

universe u

namespace Stacks.Chow

/-! ### Germ generalities -/

/-- Pulling a global section back to the whole source is `Scheme.Hom.appTop`. -/
private theorem appLE_top_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    (f.appLE ⊤ ⊤ le_rfl) s = f.appTop s := by
  have h : (f.appLE ⊤ (⊤ : X.Opens) le_rfl) =
      f.appTop ≫ X.presheaf.map (𝟙 (op (⊤ : X.Opens))) := rfl
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### The two chart opens of `ℙ¹_S` -/

/-- The open of `ℙ¹_S` covered by the first affine chart. -/
abbrev chartOpen (S : Scheme.{u}) : (relativeProjectiveLine S).Opens := affineChart S ''ᵁ ⊤

/-- The open of `ℙ¹_S` covered by the second affine chart. -/
abbrev yChartOpen (S : Scheme.{u}) : (relativeProjectiveLine S).Opens := affineYChart S ''ᵁ ⊤

/-- The punctured line maps into the first chart of `ℙ¹_S`. -/
theorem top_le_preimage_chartOpen (S : Scheme.{u}) :
    (⊤ : (puncturedLineOver S).Opens) ≤
      (puncturedChartOver S ≫ affineChart S) ⁻¹ᵁ chartOpen S := fun y _ =>
  ⟨puncturedChartOver S y, trivial, by rw [Scheme.Hom.comp_base]; rfl⟩

/-- The punctured line maps into the second chart of `ℙ¹_S`. -/
theorem top_le_preimage_yChartOpen (S : Scheme.{u}) :
    (⊤ : (puncturedLineOver S).Opens) ≤
      (puncturedYChartOver S ≫ affineYChart S) ⁻¹ᵁ yChartOpen S := fun y _ =>
  ⟨puncturedYChartOver S y, trivial, by rw [Scheme.Hom.comp_base]; rfl⟩

/-- A chart coordinate of `ℙ¹_S` pulls back along a chart-composite to the pullback of the affine
coordinate. -/
private theorem appLE_comp_lineChartCoordinate {S : Scheme.{u}}
    (e : puncturedLineOver S ⟶ affineLineOver S) (h : affineLineOver S ⟶ relativeProjectiveLine S)
    [IsOpenImmersion h] (hle : ⊤ ≤ (e ≫ h) ⁻¹ᵁ (h ''ᵁ ⊤)) :
    (e ≫ h).appLE (h ''ᵁ ⊤) ⊤ hle (lineChartCoordinate h) = e.appTop (affineCoordinate S) := by
  rw [← Scheme.Hom.appLE_comp_appLE e h (h ''ᵁ ⊤) ⊤ ⊤ (h.preimage_image_eq ⊤).ge le_rfl,
    ConcreteCategory.comp_apply, appLE_lineChartCoordinate, appLE_top_apply]

/-- The coordinate of the first chart pulls back to the affine coordinate of the punctured
line. -/
theorem appLE_lineChartCoordinate_chart (S : Scheme.{u}) :
    (puncturedChartOver S ≫ affineChart S).appLE (chartOpen S) ⊤
        (top_le_preimage_chartOpen S) (lineChartCoordinate (affineChart S)) =
      (puncturedChartOver S).appTop (affineCoordinate S) :=
  appLE_comp_lineChartCoordinate _ _ _

/-- The coordinate of the second chart pulls back to the inverse affine coordinate of the
punctured line. -/
theorem appLE_lineChartCoordinate_ychart (S : Scheme.{u}) :
    (puncturedYChartOver S ≫ affineYChart S).appLE (yChartOpen S) ⊤
        (top_le_preimage_yChartOpen S) (lineChartCoordinate (affineYChart S)) =
      (puncturedYChartOver S).appTop (affineCoordinate S) :=
  appLE_comp_lineChartCoordinate _ _ _

/-! ### The punctured line is the overlap of the two charts -/

/-- The stalk map of a chart-composite sends the germ of a chart coordinate to the germ of the
pullback of the affine coordinate. -/
private theorem stalkMap_germ_lineChartCoordinate {S : Scheme.{u}}
    (e : puncturedLineOver S ⟶ affineLineOver S) (h : affineLineOver S ⟶ relativeProjectiveLine S)
    [IsOpenImmersion h] (hle : ⊤ ≤ (e ≫ h) ⁻¹ᵁ (h ''ᵁ ⊤))
    (δ : puncturedLineOver S ⟶ relativeProjectiveLine S) (hδ : δ = e ≫ h)
    (w : puncturedLineOver S) (h1 : δ w ∈ h ''ᵁ ⊤) :
    (δ.stalkMap w) ((relativeProjectiveLine S).presheaf.germ (h ''ᵁ ⊤) (δ w) h1
        (lineChartCoordinate h)) =
      (puncturedLineOver S).presheaf.germ ⊤ w trivial (e.appTop (affineCoordinate S)) := by
  subst hδ
  rw [← appLE_comp_lineChartCoordinate e h hle, appLE_germ_eq (e ≫ h) hle w trivial]

/-- The comparison of the punctured line with `ℙ¹_S` is the base change of its model over the
integers. -/
theorem isPullback_puncturedComparison (S : Scheme.{u}) :
    IsPullback (puncturedChartOver S ≫ affineChart S)
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))))
      (pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))))
      (projectiveLinePuncturedChart (ULift.{u} ℤ) ≫ projectiveLineXChart (ULift.{u} ℤ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ)))) ?_ ?_ (IsPullback.of_hasPullback _ _)
  · rw [show (puncturedChartOver S ≫ affineChart S) ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveLine (ULift.{u} ℤ))) =
        pullback.fst (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec
            (.of (LaurentPolynomial (ULift.{u} ℤ))))) from by
        rw [Category.assoc, show affineChart S ≫ pullback.fst (terminal.from S)
            (terminal.from (projectiveLine (ULift.{u} ℤ))) = pullback.fst _ _ from
          affineChart_comp S, puncturedChartOver_fst],
      show (projectiveLinePuncturedChart (ULift.{u} ℤ) ≫
            projectiveLineXChart (ULift.{u} ℤ)) ≫ terminal.from (projectiveLine (ULift.{u} ℤ)) =
          terminal.from (AlgebraicGeometry.Spec
            (.of (LaurentPolynomial (ULift.{u} ℤ)))) from terminal.hom_ext _ _]
    exact IsPullback.of_hasPullback _ _
  · rw [Category.assoc, (isPullback_affineChart S).w, ← Category.assoc,
      puncturedChartOver_snd, Category.assoc]

/-- The two charts of `ℙ¹_ℤ` meet exactly along the punctured line. -/
theorem range_projectiveLinePuncturedChart_comp (k : Type u) [CommRing k] :
    Set.range (projectiveLinePuncturedChart k ≫ projectiveLineXChart k).base =
      Set.range (projectiveLineXChart k).base ∩ Set.range (projectiveLineYChart k).base := by
  have h := isPullback_projectiveLineCharts k
  rw [show projectiveLinePuncturedChart k = h.isoPullback.hom ≫
      pullback.fst (projectiveLineXChart k) (projectiveLineYChart k) from
    h.isoPullback_hom_fst.symm, Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, (surjective_of_isIso h.isoPullback.hom).range_eq, Set.image_univ]
  exact IsOpenImmersion.range_pullback_to_base_of_left _ _

/-- **The image of the punctured line in `ℙ¹_S` is the intersection of the two charts.** -/
theorem range_puncturedComparison (S : Scheme.{u}) :
    Set.range (puncturedChartOver S ≫ affineChart S).base =
      Set.range (affineChart S).base ∩ Set.range (affineYChart S).base := by
  have h := isPullback_puncturedComparison S
  rw [show (puncturedChartOver S ≫ affineChart S) = h.isoPullback.hom ≫
      pullback.fst (pullback.snd (terminal.from S)
        (terminal.from (projectiveLine (ULift.{u} ℤ))))
        (projectiveLinePuncturedChart (ULift.{u} ℤ) ≫
          projectiveLineXChart (ULift.{u} ℤ)) from h.isoPullback_hom_fst.symm,
    range_comp_scheme, (surjective_of_isIso h.isoPullback.hom).range_eq, Set.image_univ,
    Scheme.Pullback.range_fst, range_projectiveLinePuncturedChart_comp, Set.preimage_inter,
    range_affineChart, range_affineYChart]

/-! ### The gluing relation, as germs -/

private theorem germ_lineChartCoordinate_mul_of_mem_range (S : Scheme.{u})
    (w : puncturedLineOver S)
    (h1 : (puncturedChartOver S ≫ affineChart S) w ∈ chartOpen S)
    (h2 : (puncturedChartOver S ≫ affineChart S) w ∈ yChartOpen S) :
    (relativeProjectiveLine S).presheaf.germ (chartOpen S)
          ((puncturedChartOver S ≫ affineChart S) w) h1
          (lineChartCoordinate (affineChart S)) *
        (relativeProjectiveLine S).presheaf.germ (yChartOpen S)
          ((puncturedChartOver S ≫ affineChart S) w) h2
          (lineChartCoordinate (affineYChart S)) = 1 := by
  have hbij : Function.Bijective
      ((puncturedChartOver S ≫ affineChart S).stalkMap w).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine hbij.1 ?_
  rw [map_mul, map_one,
    stalkMap_germ_lineChartCoordinate _ _ (top_le_preimage_chartOpen S) _ rfl w h1,
    stalkMap_germ_lineChartCoordinate _ _ (top_le_preimage_yChartOpen S) _
      (puncturedChartOver_comp_affineChart S) w h2,
    ← map_mul, puncturedChartOver_appTop_affineCoordinate_mul, map_one]

/-- **The gluing relation of `ℙ¹_S`, as germs.** At a point lying on both affine charts the
germs of the two chart coordinates are inverse to each other. -/
theorem germ_lineChartCoordinate_mul (S : Scheme.{u}) (z : relativeProjectiveLine S)
    (h1 : z ∈ chartOpen S) (h2 : z ∈ yChartOpen S) :
    (relativeProjectiveLine S).presheaf.germ (chartOpen S) z h1
          (lineChartCoordinate (affineChart S)) *
        (relativeProjectiveLine S).presheaf.germ (yChartOpen S) z h2
          (lineChartCoordinate (affineYChart S)) = 1 := by
  have hz : z ∈ Set.range (puncturedChartOver S ≫ affineChart S).base := by
    rw [range_puncturedComparison]
    obtain ⟨y₁, -, hy₁⟩ := h1
    obtain ⟨y₂, -, hy₂⟩ := h2
    exact ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
  obtain ⟨w, rfl⟩ := hz
  exact germ_lineChartCoordinate_mul_of_mem_range S w h1 h2


/-! ### The two chart coordinates as rational functions on `A` -/

section Fibres

variable {S A : Scheme.{u}} [IsIntegral A] (q : A ⟶ relativeProjectiveLine S)

/-- The coordinate of the first chart of `ℙ¹_S`, pulled back along `q` and read as a rational
function on `A`. -/
def lineChartFunction (hη : genericPoint A ∈ q ⁻¹ᵁ chartOpen S) : A.functionField :=
  A.presheaf.germ (q ⁻¹ᵁ chartOpen S) (genericPoint A) hη
    (q.appLE (chartOpen S) (q ⁻¹ᵁ chartOpen S) le_rfl (lineChartCoordinate (affineChart S)))

/-- The coordinate of the second chart of `ℙ¹_S`, pulled back along `q` and read as a rational
function on `A`. -/
def lineYChartFunction (hη : genericPoint A ∈ q ⁻¹ᵁ yChartOpen S) : A.functionField :=
  A.presheaf.germ (q ⁻¹ᵁ yChartOpen S) (genericPoint A) hη
    (q.appLE (yChartOpen S) (q ⁻¹ᵁ yChartOpen S) le_rfl (lineChartCoordinate (affineYChart S)))

/-- **The two rational functions are inverse.** This is the gluing relation of `ℙ¹_S` read on
`A`. -/
theorem lineChartFunction_mul_lineYChartFunction
    (hη1 : genericPoint A ∈ q ⁻¹ᵁ chartOpen S) (hη2 : genericPoint A ∈ q ⁻¹ᵁ yChartOpen S) :
    lineChartFunction q hη1 * lineYChartFunction q hη2 = 1 := by
  rw [lineChartFunction, lineYChartFunction,
    appLE_germ_eq q le_rfl (genericPoint A) hη1 (lineChartCoordinate (affineChart S)),
    appLE_germ_eq q le_rfl (genericPoint A) hη2 (lineChartCoordinate (affineYChart S)),
    ← map_mul, germ_lineChartCoordinate_mul S (q (genericPoint A)) hη1 hη2, map_one]

end Fibres

/-! ### The coefficients of the fibre cycles -/

section Coefficients

variable (C : ChowSituation.{u}) {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  [IsIntegral A] [IsLocallyNoetherian A] (q : A ⟶ relativeProjectiveLine C.S)

private theorem ord_chartCoordinate_eq_cycle_apply
    {n : ℤ} (hdim : schemeDeltaDimension C sA = (n : EInt))
    (h : affineLineOver C.S ⟶ relativeProjectiveLine C.S) [IsOpenImmersion h]
    (I : (relativeProjectiveLine C.S).IdealSheafData)
    (hI : ∀ V : (affineLineOver C.S).affineOpens, (I.comap h).ideal V =
      Ideal.span {(affineLineOver C.S).presheaf.map (homOfLE le_top).op (affineCoordinate C.S)})
    (hsupp : (I.support : Set (relativeProjectiveLine C.S)) ⊆ Set.range h.base)
    (hη : genericPoint A ∈ q ⁻¹ᵁ (h ''ᵁ ⊤))
    (htne : A.presheaf.germ (q ⁻¹ᵁ (h ''ᵁ ⊤)) (genericPoint A) hη
      (q.appLE (h ''ᵁ ⊤) (q ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h)) ≠ 0)
    (hgen : genericPoint A ∉ Set.range (I.comap q).subschemeι.base)
    {ξ : A} (hco : coheight ξ = 1) (hξ : ξ ∈ Set.range (I.comap q).subschemeι.base) :
    A.ord (A.presheaf.germ (q ⁻¹ᵁ (h ''ᵁ ⊤)) (genericPoint A) hη
        (q.appLE (h ''ᵁ ⊤) (q ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h))) ξ =
      (cycleAssociatedToClosedSubscheme C sA (I.comap q).subschemeι (n - 1)).1 ξ := by
  have hξA : ξ ∈ q ⁻¹ᵁ (h ''ᵁ ⊤) := by
    have hsup : ξ ∈ (((I.comap q).support : TopologicalSpace.Closeds A) : Set A) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact hξ
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] at hsup
    obtain ⟨y, hy⟩ := hsupp hsup
    exact ⟨y, trivial, hy⟩
  have : Nonempty (q ⁻¹ᵁ (h ''ᵁ ⊤)) := ⟨⟨ξ, hξA⟩⟩
  refine (principalDivisorCycle_apply C sA hdim _ ξ).symm.trans
    (principalDivisorCycle_apply_eq_cycleAssociatedToClosedSubscheme_apply C sA hdim
      (I.comap q) hgen hco hξ hξA _ ?_ ?_)
  · intro h0
    exact htne (by rw [h0, map_zero])
  · exact idealStalk_comap_eq_span_germ_lineChartCoordinate h I hI q ξ hξA

private theorem ord_chartCoordinate_eq_zero_of_notMem
    (h : affineLineOver C.S ⟶ relativeProjectiveLine C.S) [IsOpenImmersion h]
    (I : (relativeProjectiveLine C.S).IdealSheafData)
    (hI : ∀ V : (affineLineOver C.S).affineOpens, (I.comap h).ideal V =
      Ideal.span {(affineLineOver C.S).presheaf.map (homOfLE le_top).op (affineCoordinate C.S)})
    (hη : genericPoint A ∈ q ⁻¹ᵁ (h ''ᵁ ⊤))
    (htne : A.presheaf.germ (q ⁻¹ᵁ (h ''ᵁ ⊤)) (genericPoint A) hη
      (q.appLE (h ''ᵁ ⊤) (q ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h)) ≠ 0)
    {ξ : A} (hco : coheight ξ = 1) (hξA : ξ ∈ q ⁻¹ᵁ (h ''ᵁ ⊤))
    (hξ : ξ ∉ Set.range (I.comap q).subschemeι.base) :
    A.ord (A.presheaf.germ (q ⁻¹ᵁ (h ''ᵁ ⊤)) (genericPoint A) hη
        (q.appLE (h ''ᵁ ⊤) (q ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h))) ξ = 0 := by
  have : Nonempty (q ⁻¹ᵁ (h ''ᵁ ⊤)) := ⟨⟨ξ, hξA⟩⟩
  have hstalk := idealStalk_comap_eq_span_germ_lineChartCoordinate h I hI q ξ hξA
  have htop : IdealSheafData.stalk (I.comap q) ξ = ⊤ := by
    refine idealStalk_eq_top_of_notMem_support _ ?_
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact hξ
  have hunit : IsUnit ((A.presheaf.germ (q ⁻¹ᵁ (h ''ᵁ ⊤)) ξ hξA)
      (q.appLE (h ''ᵁ ⊤) (q ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h))) :=
    Ideal.span_singleton_eq_top.mp (hstalk.symm.trans htop)
  have hzero := ord_eq_ringOrd_germ (Y := A) hco hξA
    (q.appLE (h ''ᵁ ⊤) (q ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h))
    (fun h0 => htne (by rw [h0, map_zero])) (n := 0)
    (by rw [Ring.ord_of_isUnit hunit]; rfl)
  simpa using hzero

end Coefficients

/-! ### The fibre-difference identity -/

/-- The two distinguished fibres of `q` are disjoint. -/
theorem disjoint_support_comap_lineZeroDivisor_lineInfinityDivisor {S A : Scheme.{u}}
    (q : A ⟶ relativeProjectiveLine S) :
    Disjoint (((lineZeroDivisor S).comap q).support : Set A)
      (((lineInfinityDivisor S).comap q).support : Set A) := by
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, TopologicalSpace.Closeds.coe_preimage]
  exact Disjoint.preimage _ (disjoint_support_lineZeroDivisor_lineInfinityDivisor S)

/-- **The fibre-difference identity for an arbitrary morphism to `ℙ¹_S`**, the general form of
part (4) of Stacks Tag 02RQ. For an integral `A` of delta-dimension `n` locally of finite type
over the base and a morphism `q : A ⟶ ℙ¹_S` whose generic point lies on both affine charts and
outside both distinguished divisors, the principal divisor of the first chart coordinate pulled
back along `q` is the difference of the cycles of the two fibres `q⁻¹D₀` and `q⁻¹D_∞`. -/
theorem principalDivisorCycle_eq_sub_lineFibreCycles (C : ChowSituation.{u}) {A : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] [IsIntegral A] [IsLocallyNoetherian A]
    (q : A ⟶ relativeProjectiveLine C.S) {n : ℤ}
    (hdim : schemeDeltaDimension C sA = (n : EInt))
    (hη1 : genericPoint A ∈ q ⁻¹ᵁ chartOpen C.S)
    (hη2 : genericPoint A ∈ q ⁻¹ᵁ yChartOpen C.S)
    (hgen0 : genericPoint A ∉ Set.range ((lineZeroDivisor C.S).comap q).subschemeι.base)
    (hgenInf : genericPoint A ∉ Set.range ((lineInfinityDivisor C.S).comap q).subschemeι.base) :
    principalDivisorCycle C sA hdim (lineChartFunction q hη1) =
      cycleAssociatedToClosedSubscheme C sA ((lineZeroDivisor C.S).comap q).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C sA
          ((lineInfinityDivisor C.S).comap q).subschemeι (n - 1) := by
  have hmul := lineChartFunction_mul_lineYChartFunction q hη1 hη2
  have h0ne : lineChartFunction q hη1 ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hinfne : lineYChartFunction q hη2 ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun ξ => ?_)
  change A.ord (lineChartFunction q hη1) ξ =
    (cycleAssociatedToClosedSubscheme C sA
        ((lineZeroDivisor C.S).comap q).subschemeι (n - 1)).1 ξ -
      (cycleAssociatedToClosedSubscheme C sA
        ((lineInfinityDivisor C.S).comap q).subschemeι (n - 1)).1 ξ
  have hzero : ∀ Z : A.IdealSheafData, ξ ∉ Set.range Z.subschemeι.base →
      (cycleAssociatedToClosedSubscheme C sA Z.subschemeι (n - 1)).1 ξ = 0 :=
    fun Z hZ => cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C sA
      Z.subschemeι (n - 1) hZ
  by_cases hco : coheight ξ = 1
  · by_cases h0 : ξ ∈ Set.range ((lineZeroDivisor C.S).comap q).subschemeι.base
    · have hinf : ξ ∉ Set.range ((lineInfinityDivisor C.S).comap q).subschemeι.base := by
        intro hc
        exact Set.disjoint_left.mp
          (disjoint_support_comap_lineZeroDivisor_lineInfinityDivisor q)
          (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact h0)
          (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact hc)
      rw [hzero _ hinf, sub_zero]
      exact ord_chartCoordinate_eq_cycle_apply C sA q hdim (affineChart C.S)
        (lineZeroDivisor C.S) (zeroDivisor_ideal_comap_affineChart C.S)
        (support_lineZeroDivisor_subset_range_affineChart C.S) hη1 h0ne hgen0 hco h0
    · by_cases hinf : ξ ∈ Set.range ((lineInfinityDivisor C.S).comap q).subschemeι.base
      · rw [hzero _ h0, zero_sub]
        have key : A.ord (lineYChartFunction q hη2) ξ =
            (cycleAssociatedToClosedSubscheme C sA
              ((lineInfinityDivisor C.S).comap q).subschemeι (n - 1)).1 ξ :=
          ord_chartCoordinate_eq_cycle_apply C sA q hdim (affineYChart C.S)
            (lineInfinityDivisor C.S) (infinityDivisor_ideal_comap_affineYChart C.S)
            (support_lineInfinityDivisor_subset_range_affineYChart C.S) hη2 hinfne hgenInf hco
            hinf
        rw [← key, ord_inv_eq_neg h0ne hinfne hmul ξ, neg_neg]
      · rw [hzero _ h0, hzero _ hinf, sub_zero]
        by_cases hA : ξ ∈ q ⁻¹ᵁ chartOpen C.S
        · exact ord_chartCoordinate_eq_zero_of_notMem C q (affineChart C.S)
            (lineZeroDivisor C.S) (zeroDivisor_ideal_comap_affineChart C.S) hη1 h0ne hco hA h0
        · have hA2 : q ξ ∉ Set.range (affineChart C.S).base := by
            intro hc
            obtain ⟨y, hy⟩ := hc
            exact hA ⟨y, trivial, hy⟩
          have hmem : q ξ ∈ Set.range (affineYChart C.S).base := by
            have hmem0 : q ξ ∈ Set.range (affineChart C.S).base ∪
                Set.range (affineYChart C.S).base := by
              rw [range_affineChart_union_range_affineYChart C.S]; trivial
            exact hmem0.resolve_left hA2
          obtain ⟨y, hy⟩ := hmem
          have key := ord_chartCoordinate_eq_zero_of_notMem C q (affineYChart C.S)
            (lineInfinityDivisor C.S) (infinityDivisor_ideal_comap_affineYChart C.S) hη2 hinfne
            hco ⟨y, trivial, hy⟩ hinf
          have key2 : A.ord (lineYChartFunction q hη2) ξ = 0 := key
          rw [ord_inv_eq_neg h0ne hinfne hmul ξ] at key2
          omega
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hco]
    have hzz : ∀ Z : A.IdealSheafData,
        (cycleAssociatedToClosedSubscheme C sA Z.subschemeι (n - 1)).1 ξ = 0 := by
      intro Z
      refine cycleAssociatedToClosedSubscheme_apply_eq_zero C sA Z.subschemeι (n - 1) ξ ?_
      rintro ⟨η, -, hd⟩
      exact hco ((relativeDimension_eq_sub_one_iff_coheight_eq_one C sA hdim ξ).mp hd)
    rw [hzz, hzz, sub_zero]

end Stacks.Chow

end
