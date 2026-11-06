module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDivisorPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.LineChartDifference
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.Basic

/-!
# The fibre difference of a morphism to `ℙ¹_S` at an arbitrary point of the affine chart

`Stacks.Chow.principalDivisorCycle_eq_sub_lineFibreCycles` computes, for an integral `A` locally
of finite type over the base of a Chow situation and a morphism `q : A ⟶ ℙ¹_S`, the principal
divisor of the coordinate `z` of the first chart pulled back along `q`:

  `div_A(z) = [q⁻¹D₀]_{n-1} - [q⁻¹D_∞]_{n-1}`.

This file does the same for `z - t`, where `t : Γ(S, ⊤)` is an arbitrary `S`-point of the affine
chart `𝔸¹_S ⊆ ℙ¹_S`:

  `div_A(z - t) = [q⁻¹D_t]_{n-1} - [q⁻¹D_∞]_{n-1}`,

with `D_t = (lineSection S t).ker` the divisor cut out by the section of `ℙ¹_S ⟶ S` at `t`. At
`t = 0` this is the statement above, `Stacks.Chow.lineSection_zero` identifying the two divisors.

Two inputs are new. The first is the local equation of `D_t` on the affine chart: it is cut out
there by `z - t`, which is `Stacks.Chow.lineSectionKer_ideal_comap_affineChart`. That is read off
the translation `z ↦ z + t` of `𝔸¹_S` built in
`StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier`: the section at `t`
is the zero section translated, so its ideal is the ideal of the zero section transported along
the inverse translation, which carries `z` to `z - t`.

The second is the behaviour at infinity, and it is where this file differs in shape from the
`t = 0` case. There the function `z` and the coordinate `w` of the *second* chart are inverse, so
the order of vanishing of `z` at a point over `∞` is read off the local equation of `D_∞` in that
chart. For `z - t` no such local equation is needed, because

  `z - t = z · (1 - t w)`

and `1 - t w` is a *unit* at every point over `∞`: there `w` lies in the maximal ideal, being a
local equation for `D_∞`. So the order of vanishing of `z - t` over `∞` is that of `z`, which the
`t = 0` case already supplies. In particular no local equation for `D_t` in the second chart —
which would be `1 - t w`, and would need `t` inverted to be recognised as a point — ever appears.

## Main definitions

* `Stacks.Chow.linePointCoordinate` — the section `z - t` of the first chart open of `ℙ¹_S`.
* `Stacks.Chow.linePointFunction` — that section pulled back along `q`, as a rational function
  on `A`.
* `Stacks.Chow.lineBaseFunction` — a global function on `S` read as a rational function on `A`.
* `Stacks.Chow.lineYChartUnitSection` and `Stacks.Chow.lineYChartUnitFunction` — the section
  `1 - t w` of the second chart open, and the rational function it gives on `A`.

## Main results

* `Stacks.Chow.idealStalk_eq_span_germ_of_comap_ideal_eq` and
  `Stacks.Chow.idealStalk_comap_eq_span_germ_of_comap_ideal_eq` — a section of an open which cuts
  out an ideal sheaf there is a local equation for it, before and after pullback. These are
  `Stacks.Chow.idealStalk_eq_span_germ_lineChartCoordinate` and its companion with the chart
  coordinate replaced by an arbitrary section.
* `Stacks.Chow.idealStalk_ne_top_of_mem_support` — on the support of an ideal sheaf its stalk is
  a proper ideal, the converse of `Stacks.Chow.idealStalk_eq_top_of_notMem_support`.
* `Stacks.Chow.lineSectionKer_ideal_comap_affineChart` — **in the coordinate of the first chart,
  `D_t` is cut out by `z - t`.**
* `Stacks.Chow.linePointFunction_eq_mul` — the factorisation `z - t = z · (1 - t w)`.
* `Stacks.Chow.notMem_preimage_yChartOpen_of_genericPoint_notMem` — if the generic point misses
  the second chart then every point does.
* `Stacks.Chow.linePointFunction_ne_zero` — `z - t` is a nonzero rational function.
* `Stacks.Chow.principalDivisorCycle_eq_sub_linePointFibreCycles` — **the fibre-difference
  identity at `t`.**

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Local equations read at the stalk -/

/-- An isomorphism of rings induces an injection on ideals. -/
private theorem ideal_map_cancel_of_isIso {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsIso φ]
    {I J : Ideal R} (h : I.map φ.hom = J.map φ.hom) : I = J := by
  have hbij : Function.Bijective φ.hom := ConcreteCategory.bijective_of_isIso _
  have hker : RingHom.ker φ.hom = ⊥ := (RingHom.injective_iff_ker_eq_bot φ.hom).mp hbij.1
  have := congrArg (Ideal.comap φ.hom) h
  rwa [Ideal.comap_map_of_surjective _ hbij.2, Ideal.comap_map_of_surjective _ hbij.2,
    ← RingHom.ker_eq_comap_bot, hker, sup_bot_eq, sup_bot_eq] at this

/-- Pulling a global section back to the whole source is `Scheme.Hom.appTop`. -/
private theorem appLE_top_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) (s : Γ(Y, ⊤)) : f.appLE ⊤ ⊤ e s = f.appTop s := by
  have h : f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e =
      f.appTop ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) :=
    congrArg (fun φ => f.appTop ≫ X.presheaf.map φ) (Subsingleton.elim _ _)
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **A section of an open which cuts out an ideal sheaf there is a local equation for it.** If
the inverse image of `I` along an open immersion `h` has, on every affine open, the restriction
of `h.appLE s` as a generator, then at every point of the image of `h` the stalk of `I` is
generated by the germ of `s`.

This is `Stacks.Chow.idealStalk_eq_span_germ_lineChartCoordinate` with the coordinate of a chart
of `ℙ¹_S` replaced by an arbitrary section on the image of an arbitrary open immersion. -/
theorem idealStalk_eq_span_germ_of_comap_ideal_eq {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsOpenImmersion h] (I : Y.IdealSheafData) (s : Γ(Y, h ''ᵁ ⊤))
    (hI : ∀ V : X.affineOpens, (I.comap h).ideal V =
      Ideal.span
        {X.presheaf.map (homOfLE le_top).op
          (h.appLE (h ''ᵁ ⊤) ⊤ (h.preimage_image_eq ⊤).ge s)})
    (z : Y) (hz : z ∈ h ''ᵁ ⊤) :
    IdealSheafData.stalk I z = Ideal.span {(Y.presheaf.germ (h ''ᵁ ⊤) z hz) s} := by
  have hzr : z ∈ Set.range h.base := by
    simpa [Scheme.Hom.image_top_eq_opensRange] using hz
  obtain ⟨y, rfl⟩ := hzr
  obtain ⟨V, hyV⟩ := Stacks.Divisors.exists_affineOpens_mem y
  have hgerm : (X.presheaf.germ ⊤ y trivial)
      (h.appLE (h ''ᵁ ⊤) ⊤ (h.preimage_image_eq ⊤).ge s) =
      (h.stalkMap y) ((Y.presheaf.germ (h ''ᵁ ⊤) (h y) hz) s) :=
    appLE_germ_eq h (h.preimage_image_eq ⊤).ge y trivial s
  refine ideal_map_cancel_of_isIso (h.stalkMap y) ?_
  rw [← AlgebraicGeometry.IdealSheafData.stalk_comap I h y,
    AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ (I.comap h) y V hyV, hI V, Ideal.map_span,
    Set.image_singleton, X.presheaf.germ_res_apply (homOfLE le_top) y hyV _, hgerm,
    Ideal.map_span, Set.image_singleton]

/-- The same, pulled back along a morphism to `Y`. -/
theorem idealStalk_comap_eq_span_germ_of_comap_ideal_eq {X Y A : Scheme.{u}} (h : X ⟶ Y)
    [IsOpenImmersion h] (I : Y.IdealSheafData) (s : Γ(Y, h ''ᵁ ⊤))
    (hI : ∀ V : X.affineOpens, (I.comap h).ideal V =
      Ideal.span
        {X.presheaf.map (homOfLE le_top).op
          (h.appLE (h ''ᵁ ⊤) ⊤ (h.preimage_image_eq ⊤).ge s)})
    (q : A ⟶ Y) (ξ : A) (hξ : ξ ∈ q ⁻¹ᵁ (h ''ᵁ ⊤)) :
    IdealSheafData.stalk (I.comap q) ξ =
      Ideal.span
        {(A.presheaf.germ (q ⁻¹ᵁ (h ''ᵁ ⊤)) ξ hξ)
          (q.appLE (h ''ᵁ ⊤) (q ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl s)} := by
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap I q ξ,
    idealStalk_eq_span_germ_of_comap_ideal_eq h I s hI (q ξ) hξ, Ideal.map_span,
    Set.image_singleton, appLE_germ_eq q le_rfl ξ hξ s]

/-- **On the support of an ideal sheaf its stalk is a proper ideal**, the converse of
`Stacks.Chow.idealStalk_eq_top_of_notMem_support`. On an affine open the ideal consists of
sections vanishing at the point, so their germs are non-units and the stalk is contained in the
maximal ideal. -/
theorem idealStalk_ne_top_of_mem_support {Y : Scheme.{u}} (I : Y.IdealSheafData) {ξ : Y}
    (hξ : ξ ∈ (I.support : Set Y)) : IdealSheafData.stalk I ξ ≠ ⊤ := by
  obtain ⟨V, hξV⟩ := Stacks.Divisors.exists_affineOpens_mem ξ
  have hzl := (Scheme.IdealSheafData.mem_support_iff_of_mem hξV).mp hξ
  rw [Scheme.mem_zeroLocus_iff] at hzl
  have hle : IdealSheafData.stalk I ξ ≤ IsLocalRing.maximalIdeal (Y.presheaf.stalk ξ) := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I ξ V hξV, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hzl a ha ((Y.mem_basicOpen a ξ hξV).mpr hu)
  exact fun htop => (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk ξ)).ne_top
    (top_le_iff.mp (htop ▸ hle))

/-! ### The divisor at `t` in the coordinate of the first chart -/

/-- The inverse of a translation of `𝔸¹_S` is the translation by the negative. -/
theorem affineTranslation_inv (S : Scheme.{u}) (t : Γ(S, ⊤)) :
    inv (affineTranslation S t) = affineTranslation S (-t) :=
  IsIso.inv_eq_of_hom_inv_id (by
    rw [affineTranslation_comp, add_neg_cancel, affineTranslation_zero])

/-- The divisor cut out on `𝔸¹_S` by the section at `t` is the inverse image of the divisor cut
out by the zero section along the inverse translation. -/
theorem ker_affineLineSection_eq_comap_affineTranslation (S : Scheme.{u}) (t : Γ(S, ⊤)) :
    (affineLineSection S t).ker =
      (affineLineConstantSection S integralAffineZeroSection).ker.comap
        (inv (affineTranslation S t)) := by
  refine AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
    (b := 𝟙 S) (i := affineLineConstantSection S integralAffineZeroSection)
    (IsPullback.of_vert_isIso_mono ⟨?_⟩)
  rw [Category.id_comp, affineLineSection, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **In the coordinate of the first chart, the divisor at `t` is cut out by `z - t`.** The
translation by `t` carries the zero-section divisor to it, and the inverse translation carries
the coordinate `z` to `z - t`.

This is the arbitrary-point analogue of `Stacks.Chow.zeroDivisor_ideal_comap_affineChart`, which
is the case `t = 0`. -/
theorem lineSectionKer_ideal_comap_affineChart (S : Scheme.{u}) (t : Γ(S, ⊤))
    (V : (affineLineOver S).affineOpens) :
    ((lineSection S t).ker.comap (affineChart S)).ideal V =
      Ideal.span
        {(affineLineOver S).presheaf.map (homOfLE le_top).op
          (affineCoordinate S - (affineLineOverHom S).appTop t)} := by
  set τ := inv (affineTranslation S t) with hτ
  have hA : IsAffineOpen (τ ''ᵁ (V : (affineLineOver S).Opens)) :=
    V.2.image_of_isOpenImmersion τ
  have hle : (V : (affineLineOver S).Opens) ≤ τ ⁻¹ᵁ (τ ''ᵁ (V : (affineLineOver S).Opens)) :=
    (τ.preimage_image_eq _).ge
  have hzero : (affineLineConstantSection S integralAffineZeroSection).ker.ideal
      ⟨τ ''ᵁ (V : (affineLineOver S).Opens), hA⟩ =
      Ideal.span {(affineLineOver S).presheaf.map (homOfLE le_top).op (affineCoordinate S)} := by
    rw [← comap_lineZeroDivisor_affineChart S]
    exact zeroDivisor_ideal_comap_affineChart S ⟨_, hA⟩
  rw [← ker_affineLineSection_eq_comap, ker_affineLineSection_eq_comap_affineTranslation S t,
    Stacks.IdealSheaf.ideal_comap_appLE _ τ ⟨_, hA⟩ V hle, hzero, Ideal.map_span,
    Set.image_singleton]
  have hinv : τ.appTop (affineCoordinate S) =
      affineCoordinate S - (affineLineOverHom S).appTop t := by
    rw [hτ, affineTranslation_inv, affineTranslation_appTop_affineCoordinate, map_neg,
      ← sub_eq_add_neg]
  congr 1
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE, ← hinv]
  rfl

/-- The divisor at `t` and the divisor at infinity are disjoint: the first lies in the first
affine chart and the second is its complement. -/
theorem disjoint_support_comap_ker_lineSection_lineInfinityDivisor {S A : Scheme.{u}}
    (q : A ⟶ relativeProjectiveLine S) (t : Γ(S, ⊤)) :
    Disjoint (((lineSection S t).ker.comap q).support : Set A)
      (((lineInfinityDivisor S).comap q).support : Set A) := by
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, TopologicalSpace.Closeds.coe_preimage]
  refine Disjoint.preimage _ ?_
  rw [Set.disjoint_left]
  intro z hz hzinf
  rw [coe_support_lineInfinityDivisor, ← compl_range_affineChart] at hzinf
  exact hzinf (supportSet_ker_lineSection_subset S t hz)

/-! ### The shifted chart coordinate as a rational function -/

/-- **The section `z - t` of the first chart open of `ℙ¹_S`**, for `t` a global function on the
base: the coordinate of the first chart minus the pullback of `t`. -/
def linePointCoordinate (S : Scheme.{u}) (t : Γ(S, ⊤)) :
    Γ(relativeProjectiveLine S, chartOpen S) :=
  lineChartCoordinate (affineChart S) -
    (relativeProjectiveLine S ↘ S).appLE ⊤ (chartOpen S) (by simp) t

/-- Read in the coordinate of the first chart, `z - t` is `z - t`. -/
theorem appLE_linePointCoordinate (S : Scheme.{u}) (t : Γ(S, ⊤)) :
    (affineChart S).appLE (chartOpen S) ⊤ ((affineChart S).preimage_image_eq ⊤).ge
        (linePointCoordinate S t) =
      affineCoordinate S - (affineLineOverHom S).appTop t := by
  rw [linePointCoordinate, map_sub, appLE_lineChartCoordinate]
  congr 1
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_top_apply,
    affineChart_comp, ← affineLineOverHom]

/-- The local-equation hypothesis for the divisor at `t` on the first chart, in the form
`Stacks.Chow.idealStalk_comap_eq_span_germ_of_comap_ideal_eq` consumes. -/
theorem comap_ideal_eq_span_appLE_linePointCoordinate (S : Scheme.{u}) (t : Γ(S, ⊤))
    (V : (affineLineOver S).affineOpens) :
    ((lineSection S t).ker.comap (affineChart S)).ideal V =
      Ideal.span
        {(affineLineOver S).presheaf.map (homOfLE le_top).op
          ((affineChart S).appLE (chartOpen S) ⊤ ((affineChart S).preimage_image_eq ⊤).ge
            (linePointCoordinate S t))} := by
  rw [appLE_linePointCoordinate]
  exact lineSectionKer_ideal_comap_affineChart S t V

/-- **The section `1 - t w` of the second chart open of `ℙ¹_S`.** -/
def lineYChartUnitSection (S : Scheme.{u}) (t : Γ(S, ⊤)) :
    Γ(relativeProjectiveLine S, yChartOpen S) :=
  1 - (relativeProjectiveLine S ↘ S).appLE ⊤ (yChartOpen S) (by simp) t *
    lineChartCoordinate (affineYChart S)

/-- The local-equation hypothesis for `D_∞` on the second chart, in the same form. -/
theorem comap_ideal_eq_span_appLE_lineChartCoordinate_affineYChart (S : Scheme.{u})
    (V : (affineLineOver S).affineOpens) :
    ((lineInfinityDivisor S).comap (affineYChart S)).ideal V =
      Ideal.span
        {(affineLineOver S).presheaf.map (homOfLE le_top).op
          ((affineYChart S).appLE (yChartOpen S) ⊤ ((affineYChart S).preimage_image_eq ⊤).ge
            (lineChartCoordinate (affineYChart S)))} := by
  rw [appLE_lineChartCoordinate]
  exact infinityDivisor_ideal_comap_affineYChart S V

section Functions

variable {S A : Scheme.{u}} [IsIntegral A] (q : A ⟶ relativeProjectiveLine S) (t : Γ(S, ⊤))

/-- A global function on the base, read as a rational function on `A` through the structure
morphism of `ℙ¹_S`. -/
def lineBaseFunction : A.functionField :=
  A.presheaf.germ ⊤ (genericPoint A) trivial
    ((q ≫ (relativeProjectiveLine S ↘ S)).appTop t)

/-- **The section `z - t`, pulled back along `q` and read as a rational function on `A`.** -/
def linePointFunction (hη : genericPoint A ∈ q ⁻¹ᵁ chartOpen S) : A.functionField :=
  A.presheaf.germ (q ⁻¹ᵁ chartOpen S) (genericPoint A) hη
    (q.appLE (chartOpen S) (q ⁻¹ᵁ chartOpen S) le_rfl (linePointCoordinate S t))

/-- That section pulled back along `q`, as a rational function on `A`. -/
def lineYChartUnitFunction (hη : genericPoint A ∈ q ⁻¹ᵁ yChartOpen S) : A.functionField :=
  A.presheaf.germ (q ⁻¹ᵁ yChartOpen S) (genericPoint A) hη
    (q.appLE (yChartOpen S) (q ⁻¹ᵁ yChartOpen S) le_rfl (lineYChartUnitSection S t))

/-- The pullback of a global function on the base, read on any open of `ℙ¹_S` through which the
generic point of `A` passes, is the same rational function on `A`. -/
theorem germ_appLE_appLE_eq_lineBaseFunction (U : (relativeProjectiveLine S).Opens)
    (hU : U ≤ (relativeProjectiveLine S ↘ S) ⁻¹ᵁ ⊤) (hη : genericPoint A ∈ q ⁻¹ᵁ U) :
    A.presheaf.germ (q ⁻¹ᵁ U) (genericPoint A) hη
        (q.appLE U (q ⁻¹ᵁ U) le_rfl
          ((relativeProjectiveLine S ↘ S).appLE ⊤ U hU t)) =
      lineBaseFunction q t := by
  rw [show q.appLE U (q ⁻¹ᵁ U) le_rfl ((relativeProjectiveLine S ↘ S).appLE ⊤ U hU t) =
      ((relativeProjectiveLine S ↘ S).appLE ⊤ U hU ≫
        q.appLE U (q ⁻¹ᵁ U) le_rfl) t from (ConcreteCategory.comp_apply _ _ t).symm,
    Scheme.Hom.appLE_comp_appLE]
  exact A.presheaf.germ_res_apply (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)) (genericPoint A) hη _

/-- `z - t` as a rational function is the difference of `z` and of `t`. -/
theorem linePointFunction_eq_sub (hη : genericPoint A ∈ q ⁻¹ᵁ chartOpen S) :
    linePointFunction q t hη = lineChartFunction q hη - lineBaseFunction q t := by
  rw [linePointFunction, linePointCoordinate, map_sub, map_sub, lineChartFunction,
    germ_appLE_appLE_eq_lineBaseFunction q t (chartOpen S) (by simp) hη]

/-- `1 - t w` as a rational function. -/
theorem lineYChartUnitFunction_eq (hη : genericPoint A ∈ q ⁻¹ᵁ yChartOpen S) :
    lineYChartUnitFunction q t hη =
      1 - lineBaseFunction q t * lineYChartFunction q hη := by
  rw [lineYChartUnitFunction, lineYChartUnitSection, map_sub, map_sub, map_one, map_one, map_mul,
    map_mul, lineYChartFunction,
    germ_appLE_appLE_eq_lineBaseFunction q t (yChartOpen S) (by simp) hη]

/-- **The factorisation `z - t = z · (1 - t w)`** in the function field of `A`. The two chart
coordinates are inverse there, so the right-hand side is `z - t · (z · w) = z - t`. -/
theorem linePointFunction_eq_mul (hη1 : genericPoint A ∈ q ⁻¹ᵁ chartOpen S)
    (hη2 : genericPoint A ∈ q ⁻¹ᵁ yChartOpen S) :
    linePointFunction q t hη1 =
      lineChartFunction q hη1 * lineYChartUnitFunction q t hη2 := by
  have hmul := lineChartFunction_mul_lineYChartFunction q hη1 hη2
  rw [linePointFunction_eq_sub, lineYChartUnitFunction_eq, mul_sub, mul_one,
    show lineChartFunction q hη1 * (lineBaseFunction q t * lineYChartFunction q hη2) =
      lineBaseFunction q t * (lineChartFunction q hη1 * lineYChartFunction q hη2) from by ring,
    hmul, mul_one]

end Functions

/-! ### The fibre-difference identity at an arbitrary point of the chart -/

/-- **If the generic point of `A` misses the second affine chart then no point of `A` meets
it.** The complement of the second chart is the image of the zero section, which is closed, so
it contains the closure of the generic point, which is all of `A`.

This is what makes the hypothesis "the generic point lies on the second chart" — i.e. `A` is not
carried into the zero section — unnecessary below: where it would be used, the point under
consideration lies over infinity, hence on the second chart, which this rules out. -/
theorem notMem_preimage_yChartOpen_of_genericPoint_notMem {S A : Scheme.{u}} [IsIntegral A]
    (q : A ⟶ relativeProjectiveLine S) (hη : genericPoint A ∉ q ⁻¹ᵁ yChartOpen S) (ξ : A) :
    ξ ∉ q ⁻¹ᵁ yChartOpen S := by
  have hclosed : IsClosed (Set.range (lineZeroSection S)) := by
    rw [← coe_support_lineZeroDivisor S]
    exact (lineZeroDivisor S).support.2
  have hη' : q (genericPoint A) ∈ Set.range (lineZeroSection S) := by
    rw [← compl_range_affineYChart S]
    intro hc
    obtain ⟨y, hy⟩ := hc
    exact hη ⟨y, trivial, hy⟩
  have hsub : closure ({genericPoint A} : Set A) ⊆
      q.base ⁻¹' (Set.range (lineZeroSection S)) :=
    (hclosed.preimage q.base.hom.continuous).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hη')
  have hall : q ξ ∈ Set.range (lineZeroSection S) :=
    hsub (by rw [(genericPoint_spec A).def]; trivial)
  rw [← compl_range_affineYChart S] at hall
  intro hcon
  obtain ⟨y, -, hy⟩ := hcon
  exact hall ⟨y, hy⟩

/-- The germ of `z - t` is a unit at a point of the first chart outside the divisor at `t`: there
the stalk of that divisor is the unit ideal, and the germ of `z - t` generates it. -/
private theorem isUnit_germ_linePointCoordinate {S A : Scheme.{u}}
    (q : A ⟶ relativeProjectiveLine S) (t : Γ(S, ⊤)) {ξ : A} (hξ : ξ ∈ q ⁻¹ᵁ chartOpen S)
    (hT : ξ ∉ Set.range ((lineSection S t).ker.comap q).subschemeι.base) :
    IsUnit ((A.presheaf.germ (q ⁻¹ᵁ chartOpen S) ξ hξ)
      (q.appLE (chartOpen S) (q ⁻¹ᵁ chartOpen S) le_rfl (linePointCoordinate S t))) := by
  have htop : IdealSheafData.stalk ((lineSection S t).ker.comap q) ξ = ⊤ :=
    idealStalk_eq_top_of_notMem_support _
      (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact hT)
  exact Ideal.span_singleton_eq_top.mp
    ((idealStalk_comap_eq_span_germ_of_comap_ideal_eq (affineChart S) (lineSection S t).ker
      (linePointCoordinate S t) (comap_ideal_eq_span_appLE_linePointCoordinate S t) q ξ
      hξ).symm.trans htop)

/-- A section whose germ at a codimension-one point `ξ` is a unit gives a rational function of
order zero there. -/
private theorem ord_germ_eq_zero_of_isUnit_germ {A : Scheme.{u}} [IsIntegral A]
    [IsLocallyNoetherian A] {ξ : A} (hco : coheight ξ = 1) {V : A.Opens} [Nonempty V]
    (hξ : ξ ∈ V) (η : genericPoint A ∈ V) (s : Γ(A, V)) (hs : s ≠ 0)
    (hu : IsUnit ((A.presheaf.germ V ξ hξ) s)) :
    A.ord (A.presheaf.germ V (genericPoint A) η s) ξ = 0 := by
  have h := ord_eq_ringOrd_germ (Y := A) hco hξ s hs (n := 0)
    (by rw [Ring.ord_of_isUnit hu]; rfl)
  simpa using h

/-- **`z - t` is a nonzero rational function on `A`** as soon as the generic point of `A` misses
the divisor at `t`: there the stalk of that divisor is the unit ideal, and the germ of `z - t`
generates it. -/
theorem linePointFunction_ne_zero {S A : Scheme.{u}} [IsIntegral A]
    (q : A ⟶ relativeProjectiveLine S) (t : Γ(S, ⊤))
    (hη1 : genericPoint A ∈ q ⁻¹ᵁ chartOpen S)
    (hgenT : genericPoint A ∉ Set.range ((lineSection S t).ker.comap q).subschemeι.base) :
    linePointFunction q t hη1 ≠ 0 :=
  (isUnit_germ_linePointCoordinate q t hη1 hgenT).ne_zero

/-- **The fibre-difference identity at an arbitrary point of the affine chart.** For an integral
`A` of delta-dimension `n` locally of finite type over the base and a morphism `q : A ⟶ ℙ¹_S`
whose generic point lies on the first affine chart and outside both the divisor at `t` and the
divisor at infinity, the principal divisor of `z - t` pulled back along `q` is the difference of
the cycles of the two fibres `q⁻¹D_t` and `q⁻¹D_∞`.

This is `Stacks.Chow.principalDivisorCycle_eq_sub_lineFibreCycles` with the distinguished point
`0` replaced by the point attached to an arbitrary global function `t` on the base. Its
hypotheses are the two of that statement which concern the divisors appearing in the conclusion;
the third, that the generic point lie on the *second* chart, is **not** assumed, so nothing is
required of `A` relative to the zero section.

The proof is coefficientwise, in four cases. At a point of codimension other than one every
coefficient vanishes. At a codimension-one point of `q⁻¹D_t` the section `z - t` is a local
equation of `q⁻¹D_t` — that is `Stacks.Chow.lineSectionKer_ideal_comap_affineChart` — so its
order of vanishing is the multiplicity, and the infinity coefficient vanishes because the two
divisors are disjoint. At a codimension-one point of `q⁻¹D_∞` the factorisation
`z - t = z · (1 - t w)` of `Stacks.Chow.linePointFunction_eq_mul` applies: the second factor is a
unit there, since `w` is a local equation for `D_∞` and hence lies in the maximal ideal, and the
order of vanishing of `z` is the negative of that of `w`, which is the multiplicity of `q⁻¹D_∞`.
That factorisation needs the generic point on the second chart, and if it is not there then no
point of `A` is, by `Stacks.Chow.notMem_preimage_yChartOpen_of_genericPoint_notMem`, so this case
does not arise. At a codimension-one point of neither divisor the point lies on the first chart —
the complement of that chart is the support of `D_∞` — and there the local equation generates the
unit ideal, so `z - t` is a unit. -/
theorem principalDivisorCycle_eq_sub_linePointFibreCycles (C : ChowSituation.{u})
    {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] [IsIntegral A]
    [IsLocallyNoetherian A] (q : A ⟶ relativeProjectiveLine C.S) (t : Γ(C.S, ⊤)) {n : ℤ}
    (hdim : schemeDeltaDimension C sA = (n : EInt))
    (hη1 : genericPoint A ∈ q ⁻¹ᵁ chartOpen C.S)
    (hgenT : genericPoint A ∉ Set.range ((lineSection C.S t).ker.comap q).subschemeι.base)
    (hgenInf : genericPoint A ∉ Set.range ((lineInfinityDivisor C.S).comap q).subschemeι.base) :
    principalDivisorCycle C sA hdim (linePointFunction q t hη1) =
      cycleAssociatedToClosedSubscheme C sA
          ((lineSection C.S t).ker.comap q).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C sA
          ((lineInfinityDivisor C.S).comap q).subschemeι (n - 1) := by
  have _ : Nonempty (q ⁻¹ᵁ chartOpen C.S) := ⟨⟨genericPoint A, hη1⟩⟩
  have hgdef : linePointFunction q t hη1 =
      A.presheaf.germ (q ⁻¹ᵁ chartOpen C.S) (genericPoint A) hη1
        (q.appLE (chartOpen C.S) (q ⁻¹ᵁ chartOpen C.S) le_rfl (linePointCoordinate C.S t)) :=
    rfl
  have hgne : linePointFunction q t hη1 ≠ 0 := linePointFunction_ne_zero q t hη1 hgenT
  have hsecne : q.appLE (chartOpen C.S) (q ⁻¹ᵁ chartOpen C.S) le_rfl
      (linePointCoordinate C.S t) ≠ 0 :=
    fun h0 => hgne (by rw [hgdef, h0, map_zero])
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun ξ => ?_)
  show A.ord (linePointFunction q t hη1) ξ =
    (cycleAssociatedToClosedSubscheme C sA
        ((lineSection C.S t).ker.comap q).subschemeι (n - 1)).1 ξ -
      (cycleAssociatedToClosedSubscheme C sA
        ((lineInfinityDivisor C.S).comap q).subschemeι (n - 1)).1 ξ
  have hzero : ∀ Z : A.IdealSheafData, ξ ∉ Set.range Z.subschemeι.base →
      (cycleAssociatedToClosedSubscheme C sA Z.subschemeι (n - 1)).1 ξ = 0 :=
    fun Z hZ => cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C sA
      Z.subschemeι (n - 1) hZ
  by_cases hco : coheight ξ = 1
  · by_cases hT : ξ ∈ Set.range ((lineSection C.S t).ker.comap q).subschemeι.base
    · have hTs : ξ ∈ (((lineSection C.S t).ker.comap q).support : Set A) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact hT
      have hinf : ξ ∉ Set.range ((lineInfinityDivisor C.S).comap q).subschemeι.base := fun hc =>
        Set.disjoint_left.mp
          (disjoint_support_comap_ker_lineSection_lineInfinityDivisor q t) hTs
          (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact hc)
      have hξA : ξ ∈ q ⁻¹ᵁ chartOpen C.S := by
        have h := hTs
        rw [Scheme.IdealSheafData.support_comap,
          TopologicalSpace.Closeds.coe_preimage] at h
        obtain ⟨y, hy⟩ := supportSet_ker_lineSection_subset C.S t h
        exact ⟨y, trivial, hy⟩
      rw [hzero _ hinf, sub_zero]
      exact (principalDivisorCycle_apply C sA hdim _ ξ).symm.trans
        (principalDivisorCycle_apply_eq_cycleAssociatedToClosedSubscheme_apply C sA hdim
          ((lineSection C.S t).ker.comap q) hgenT hco hT hξA _ hsecne
          (idealStalk_comap_eq_span_germ_of_comap_ideal_eq (affineChart C.S)
            (lineSection C.S t).ker (linePointCoordinate C.S t)
            (comap_ideal_eq_span_appLE_linePointCoordinate C.S t) q ξ hξA))
    · by_cases hinf : ξ ∈ Set.range ((lineInfinityDivisor C.S).comap q).subschemeι.base
      · have hinfs : ξ ∈ (((lineInfinityDivisor C.S).comap q).support : Set A) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact hinf
        have hξY : ξ ∈ q ⁻¹ᵁ yChartOpen C.S := by
          have h := hinfs
          rw [Scheme.IdealSheafData.support_comap,
            TopologicalSpace.Closeds.coe_preimage, coe_support_lineInfinityDivisor] at h
          obtain ⟨y, hy⟩ := range_lineInfinitySection_subset_range_affineYChart C.S h
          exact ⟨y, trivial, hy⟩
        by_cases hη2 : genericPoint A ∈ q ⁻¹ᵁ yChartOpen C.S
        · have hmulXY := lineChartFunction_mul_lineYChartFunction q hη1 hη2
          have hXne : lineChartFunction q hη1 ≠ 0 := left_ne_zero_of_mul_eq_one hmulXY
          have hYne : lineYChartFunction q hη2 ≠ 0 := right_ne_zero_of_mul_eq_one hmulXY
          have _ : Nonempty (q ⁻¹ᵁ yChartOpen C.S) := ⟨⟨genericPoint A, hη2⟩⟩
          have hudef : lineYChartUnitFunction q t hη2 =
              A.presheaf.germ (q ⁻¹ᵁ yChartOpen C.S) (genericPoint A) hη2
                (q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
                  (lineYChartUnitSection C.S t)) :=
            rfl
          have hwdef : lineYChartFunction q hη2 =
              A.presheaf.germ (q ⁻¹ᵁ yChartOpen C.S) (genericPoint A) hη2
                (q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
                  (lineChartCoordinate (affineYChart C.S))) :=
            rfl
          have hune : lineYChartUnitFunction q t hη2 ≠ 0 := by
            intro h0
            rw [linePointFunction_eq_mul q t hη1 hη2, h0, mul_zero] at hgne
            exact hgne rfl
          have hwsecne : q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
              (lineChartCoordinate (affineYChart C.S)) ≠ 0 :=
            fun h0 => hYne (by rw [hwdef, h0, map_zero])
          have hspanInf := idealStalk_comap_eq_span_germ_of_comap_ideal_eq (affineYChart C.S)
            (lineInfinityDivisor C.S) (lineChartCoordinate (affineYChart C.S))
            (comap_ideal_eq_span_appLE_lineChartCoordinate_affineYChart C.S) q ξ hξY
          have hwmem : (A.presheaf.germ (q ⁻¹ᵁ yChartOpen C.S) ξ hξY)
              (q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
                (lineChartCoordinate (affineYChart C.S))) ∈
              IsLocalRing.maximalIdeal (A.presheaf.stalk ξ) := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            exact fun hu => idealStalk_ne_top_of_mem_support _ hinfs
              (hspanInf.trans (Ideal.span_singleton_eq_top.mpr hu))
          have hsec : (A.presheaf.germ (q ⁻¹ᵁ yChartOpen C.S) ξ hξY)
              (q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
                (lineYChartUnitSection C.S t)) =
              1 - (A.presheaf.germ (q ⁻¹ᵁ yChartOpen C.S) ξ hξY)
                  (q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
                    ((relativeProjectiveLine C.S ↘ C.S).appLE ⊤ (yChartOpen C.S) (by simp) t)) *
                (A.presheaf.germ (q ⁻¹ᵁ yChartOpen C.S) ξ hξY)
                  (q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
                    (lineChartCoordinate (affineYChart C.S))) := by
            rw [lineYChartUnitSection, map_sub, map_sub, map_one, map_one, map_mul, map_mul]
          have hunit : IsUnit ((A.presheaf.germ (q ⁻¹ᵁ yChartOpen C.S) ξ hξY)
              (q.appLE (yChartOpen C.S) (q ⁻¹ᵁ yChartOpen C.S) le_rfl
                (lineYChartUnitSection C.S t))) := by
            rw [hsec]
            exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
              ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ hwmem))
          have horu : A.ord (lineYChartUnitFunction q t hη2) ξ = 0 := by
            rw [hudef]
            exact ord_germ_eq_zero_of_isUnit_germ hco hξY hη2 _
              (fun h0 => hune (by rw [hudef, h0, map_zero])) hunit
          have hordW : A.ord (lineYChartFunction q hη2) ξ =
              (cycleAssociatedToClosedSubscheme C sA
                ((lineInfinityDivisor C.S).comap q).subschemeι (n - 1)).1 ξ :=
            (principalDivisorCycle_apply C sA hdim _ ξ).symm.trans
              (principalDivisorCycle_apply_eq_cycleAssociatedToClosedSubscheme_apply C sA hdim
                ((lineInfinityDivisor C.S).comap q) hgenInf hco hinf hξY _ hwsecne hspanInf)
          have hXord : A.ord (lineChartFunction q hη1) ξ =
              -(cycleAssociatedToClosedSubscheme C sA
                ((lineInfinityDivisor C.S).comap q).subschemeι (n - 1)).1 ξ := by
            have h := ord_inv_eq_neg hXne hYne hmulXY ξ
            rw [hordW] at h
            omega
          rw [hzero _ hT, zero_sub, linePointFunction_eq_mul q t hη1 hη2,
            Scheme.ord_mul hXne hune, horu, add_zero, hXord]
        · exact absurd hξY (notMem_preimage_yChartOpen_of_genericPoint_notMem q hη2 ξ)
      · rw [hzero _ hT, hzero _ hinf, sub_zero]
        have hξA : ξ ∈ q ⁻¹ᵁ chartOpen C.S := by
          have hnot : q ξ ∉ Set.range (lineInfinitySection C.S) := by
            intro hc
            refine hinf ?_
            rw [Scheme.IdealSheafData.range_subschemeι,
              Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
              coe_support_lineInfinityDivisor]
            exact hc
          have hmem : q ξ ∈ Set.range (affineChart C.S).base := by
            by_contra hcc
            exact hnot (by rw [← compl_range_affineChart C.S]; exact hcc)
          obtain ⟨y, hy⟩ := hmem
          exact ⟨y, trivial, hy⟩
        rw [hgdef]
        exact ord_germ_eq_zero_of_isUnit_germ hco hξA hη1 _ hsecne
          (isUnit_germ_linePointCoordinate q t hξA hT)
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
