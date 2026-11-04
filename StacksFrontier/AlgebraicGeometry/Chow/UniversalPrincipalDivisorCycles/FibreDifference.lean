module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSections
import all StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.Basic
import all StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSections

/-!
# The principal divisor of a rational function is the difference of the two fibre cycles

This file proves the identity of part (4) of Tag 02RQ. Let `X` be integral and locally of finite
type over the base of a Chow situation, let `g` be a unit section on an open `U ⊆ X`, let `Y` be the
closure of the graph of the attached morphism `U ⟶ ℙ¹_S` inside `X ×_S ℙ¹_S` and let `f` be the
rational function on `Y` that `g` induces. With `Y₀ = q⁻¹D₀` and `Y_∞ = q⁻¹D_∞` the two
distinguished fibres and `dim_δ(Y) = n`,

  `div_Y(f) = [Y₀]_{n-1} - [Y_∞]_{n-1}`.

The identity is checked coefficient by coefficient. At a point `ξ` of codimension other than one
both sides vanish: the left side by `AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one`,
the right side because a point carrying a nonzero coefficient of an `(n-1)`-cycle has relative
dimension `n - 1`, which by `Stacks.Chow.relativeDimension_eq_sub_one_iff_coheight_eq_one` happens
only in codimension one.

At a point of codimension one there are three cases, and all three are the same computation run on
one of the two affine charts of `ℙ¹_S`. The chart coordinate `T`, read as a section on the image
of the chart in `ℙ¹_S` and pulled back along `q`, is a local equation for the fibre over that
chart's divisor — that is the content of
`Stacks.Chow.idealStalk_comap_eq_span_germ_lineChartCoordinate` — and on `p⁻¹(U)` it restricts to
the pullback of the section, so the rational function it represents is `f` on the first chart and
`f⁻¹` on the second. Hence
`Stacks.Chow.principalDivisorCycle_apply_eq_cycleAssociatedToClosedSubscheme_apply` applies and
gives `ord_ξ(f) = [Y₀]_{n-1}(ξ)` on `Y₀`, and `ord_ξ(f⁻¹) = [Y_∞]_{n-1}(ξ)` on `Y_∞`; the two
fibres are disjoint, so the other coefficient vanishes there. Off both fibres the local equation
generates the unit ideal of the local ring, so the germ is a unit and the order of vanishing is
zero, while both coefficients vanish.

The new geometric input is the description of the morphism `U ⟶ ℙ¹_S` in the *second* chart:
`Stacks.Chow.sectionToAffineLine_inv_comp_affineYChart` says that the morphism attached to a unit
section `g` is the second-chart morphism attached to `g⁻¹`. This is the gluing relation of Tag
01JE made concrete. It is obtained by factoring the chart morphism of a unit section through the
punctured line `Spec ℤ[T, T⁻¹]`, where `T` may be sent to a unit by
`LaurentPolynomial.eval₂`, and then using that the transition of the two-chart gluing is
`LaurentPolynomial.invert`; composing `LaurentPolynomial.invert` with the evaluation at `g` is the
evaluation at `g⁻¹`, which is checked on `C r` and `T n` by `AddMonoidAlgebra.ringHom_ext`.

## Main results

* `Stacks.Chow.appLE_germ_eq` — the germ of a pulled-back section is the image of the germ under
  the stalk map.
* `Stacks.Chow.ord_inv_eq_neg` — the order of vanishing of the inverse of a nonzero rational
  function is the negative of its order of vanishing.
* `Stacks.Chow.sectionToAffineLine_inv_comp_affineYChart` — the morphism `U ⟶ ℙ¹_S` of a unit
  section, read in the second chart, has the inverse section as its coordinate.
* `Stacks.Chow.lineChartCoordinate` — the coordinate of an affine chart of `ℙ¹_S`, as a section on
  the image of that chart.
* `Stacks.Chow.idealStalk_eq_span_germ_lineChartCoordinate` and
  `Stacks.Chow.idealStalk_comap_eq_span_germ_lineChartCoordinate` — a divisor of `ℙ¹_S` cut out on
  a chart by the coordinate has the germ of the chart coordinate as a local equation, before and
  after pullback along a morphism to `ℙ¹_S`.
* `Stacks.Chow.res_appLE_lineChartCoordinate` — that pulled-back coordinate restricts on `p⁻¹(U)`
  to the pullback of the section whose chart morphism factors through the chart.
* `Stacks.Chow.ord_eq_cycleAssociatedToClosedSubscheme_apply_of_chart` and
  `Stacks.Chow.ord_eq_zero_of_notMem_support_of_chart` — the coefficient computation at a
  codimension-one point, on and off the fibre.
* `Stacks.Chow.principalDivisorCycle_graphClosure_eq_sub` — the identity of part (4) of Tag 02RQ;
  the statement in a Chow situation is
  `Stacks.Chow.principalDivisorCycle_graphClosure_eq_fibreCycles_sub`.

## Implementation notes

Every statement about the graph is made for `U ⟶ X` quasi-compact, as in
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles`; it enters through
`Stacks.Chow.range_graphInclusion`, which is what identifies `p⁻¹(U)` with the image of the graph
and hence makes the chart coordinate restrict correctly. In a Chow situation it is automatic, see
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.GraphConstruction`.

Tag 02RQ states part (4) for the unit `graphRationalFunction` of `Stacks.Chow.rationalFunctions`,
while `Stacks.Chow.principalDivisorCycle` is stated on
`AlgebraicGeometry.Scheme.functionField`, because it is built on
`AlgebraicGeometry.Scheme.ord`. The two are identified by
`Stacks.Chow.rationalFunctionsEquivFunctionField` of Tag 01RV, exactly as part (5) does.

No affine open of `Y` is chosen: the stalk of an inverse-image ideal sheaf is the image of the
stalk upstairs, so the local equation is produced at the stalk and the only affine open in the
argument sits inside the existing computation of `D₀` and `D_∞` on `𝔸¹_S`. The stalk of an
ideal sheaf on an affine open is read off with the public
`AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ`, while the stalk of an inverse image is a
`private` helper of another module, reached with `import all` rather than re-ported; the gluing
relation of the projective line is reached the same way.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Generalities about germs, ideals and orders of vanishing -/

/-- The germ of a pulled-back section is the image of the germ under the stalk map. -/
theorem appLE_germ_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (x : X) (hxV : x ∈ V) (s : Γ(Y, U)) :
    (X.presheaf.germ V x hxV) (f.appLE U V e s) =
      (f.stalkMap x) ((Y.presheaf.germ U (f x) (e hxV)) s) := by
  rw [show f.appLE U V e s = (X.presheaf.map (homOfLE e).op) ((f.app U) s) from rfl,
    X.presheaf.germ_res_apply (homOfLE e) x hxV]
  exact (Scheme.Hom.germ_stalkMap_apply f U x (e hxV) s).symm

/-- A bijective ring homomorphism induces an injection on ideals. -/
private theorem ideal_map_cancel {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) {I J : Ideal R} (h : I.map φ = J.map φ) : I = J := by
  have hker : RingHom.ker φ = ⊥ := (RingHom.injective_iff_ker_eq_bot φ).mp hφ.1
  have := congrArg (Ideal.comap φ) h
  rwa [Ideal.comap_map_of_surjective _ hφ.2, Ideal.comap_map_of_surjective _ hφ.2,
    ← RingHom.ker_eq_comap_bot, hker, sup_bot_eq, sup_bot_eq] at this

/-- Off the support of an ideal sheaf its stalk is the unit ideal. -/
theorem idealStalk_eq_top_of_notMem_support {Y : Scheme.{u}} (I : Y.IdealSheafData) {ξ : Y}
    (hξ : ξ ∉ (I.support : Set Y)) : IdealSheafData.stalk I ξ = ⊤ := by
  obtain ⟨V, hξV⟩ := Stacks.Divisors.exists_affineOpens_mem ξ
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I ξ V hξV]
  have hξ' : ¬ ∀ a ∈ (I.ideal V : Set Γ(Y, (V : Y.Opens))), ξ ∉ Y.basicOpen a := fun hh =>
    hξ ((Scheme.IdealSheafData.mem_support_iff_of_mem hξV).mpr
      ((Y.mem_zeroLocus_iff _ ξ).mpr hh))
  obtain ⟨a, ha, hmem⟩ := by simpa using hξ'
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
    ((Y.mem_basicOpen a ξ hξV).mp hmem)

/-- The order of vanishing of the inverse of a nonzero rational function. -/
theorem ord_inv_eq_neg {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {a b : Y.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b = 1) (ξ : Y) :
    Y.ord b ξ = -Y.ord a ξ := by
  have hone : Y.ord (1 : Y.functionField) ξ = 0 := by
    have h := Y.ord_mul (x := ξ) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [one_mul] at h
    omega
  have h := Y.ord_mul (x := ξ) ha hb
  rw [hab, hone] at h
  omega

/-! ### The second chart of the projective line and the inverse coordinate -/

/-- The ring map `ℤ ⟶ Γ(U, ⊤)` used to evaluate integral polynomials at a section. -/
def integralCastToSections {X : Scheme.{u}} (U : X.Opens) : ULift.{u} ℤ →+* Γ(U.toScheme, ⊤) :=
  (Int.castRingHom Γ(U.toScheme, ⊤)).comp ULift.ringEquiv.toRingHom

/-- A unit section of `U`, read as a unit of the global sections of `U` as a scheme. -/
def sectionTopUnit {X : Scheme.{u}} (U : X.Opens) (g : (Γ(X, U))ˣ) : (Γ(U.toScheme, ⊤))ˣ :=
  Units.map U.topIso.inv.hom.toMonoidHom g

/-- The morphism `U ⟶ Spec ℤ[T, T⁻¹]` attached to a unit section of `U`: the coordinate `T`
goes to the section. -/
def sectionLaurentHom {X : Scheme.{u}} (U : X.Opens) (g : (Γ(X, U))ˣ) :
    U.toScheme ⟶ Spec (.of (LaurentPolynomial (ULift.{u} ℤ))) :=
  U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.eval₂ (integralCastToSections U) ↑(sectionTopUnit U g)))

/-- Followed by the punctured chart, the Laurent morphism of a unit section is the affine-chart
morphism of that section. -/
theorem sectionLaurentHom_comp_puncturedChart {X : Scheme.{u}} (U : X.Opens)
    (g : (Γ(X, U))ˣ) :
    sectionLaurentHom U g ≫ projectiveLinePuncturedChart (ULift.{u} ℤ) =
      sectionChartHom U ↑g := by
  have key : CommRingCat.ofHom (Polynomial.toLaurent (R := ULift.{u} ℤ)) ≫
      CommRingCat.ofHom
        (LaurentPolynomial.eval₂ (integralCastToSections U) ↑(sectionTopUnit U g)) =
      CommRingCat.ofHom
        (Polynomial.eval₂RingHom (integralCastToSections U) ↑(sectionTopUnit U g)) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun p => ?_
    change LaurentPolynomial.eval₂ _ _ (Polynomial.toLaurent p) = _
    rw [LaurentPolynomial.eval₂_toLaurent]
    rfl
  rw [sectionLaurentHom, sectionChartHom, Category.assoc]
  exact congrArg (fun z => U.toScheme.toSpecΓ ≫ z)
    ((Spec.map_comp _ _).symm.trans (congrArg Spec.map key))

/-- Inversion on the punctured line replaces a unit section by its inverse. -/
theorem sectionLaurentHom_comp_inversionIso {X : Scheme.{u}} (U : X.Opens)
    (g : (Γ(X, U))ˣ) :
    sectionLaurentHom U g ≫ (projectiveLineInversionIso (ULift.{u} ℤ)).hom =
      sectionLaurentHom U g⁻¹ := by
  have key : CommRingCat.ofHom
        (LaurentPolynomial.invert (R := ULift.{u} ℤ)).toRingEquiv.toRingHom ≫
      CommRingCat.ofHom
        (LaurentPolynomial.eval₂ (integralCastToSections U) ↑(sectionTopUnit U g)) =
      CommRingCat.ofHom
        (LaurentPolynomial.eval₂ (integralCastToSections U) ↑(sectionTopUnit U g⁻¹)) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    have hinv : sectionTopUnit U g⁻¹ = (sectionTopUnit U g)⁻¹ := by
      rw [sectionTopUnit, sectionTopUnit, map_inv]
    rw [hinv]
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.invert (LaurentPolynomial.C r)) = _
      simp
    · change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.invert (LaurentPolynomial.T m)) = _
      simp [zpow_neg]
  rw [sectionLaurentHom, sectionLaurentHom, Category.assoc]
  exact congrArg (fun z => U.toScheme.toSpecΓ ≫ z)
    ((Spec.map_comp _ _).symm.trans (congrArg Spec.map key))

/-- The morphism `U ⟶ ℙ¹_ℤ` attached to a unit section is also the morphism of the second chart
attached to the inverse section: the gluing of the projective line inverts the coordinate. -/
theorem sectionChartHom_comp_projectiveLineYChart {X : Scheme.{u}} (U : X.Opens)
    (g : (Γ(X, U))ˣ) :
    sectionChartHom U ↑g⁻¹ ≫ projectiveLineYChart (ULift.{u} ℤ) =
      sectionChartHom U ↑g ≫ projectiveLineXChart (ULift.{u} ℤ) := by
  rw [← sectionLaurentHom_comp_puncturedChart U g⁻¹, ← sectionLaurentHom_comp_inversionIso,
    ← sectionLaurentHom_comp_puncturedChart U g, Category.assoc, Category.assoc,
    AlgebraicGeometry.projectiveLineInversion_comp_charts]
  exact (Category.assoc _ _ _).symm

/-- **The morphism `U ⟶ ℙ¹_S` attached to a unit section, read in the second chart, has the
inverse section as its coordinate.** -/
theorem sectionToAffineLine_inv_comp_affineYChart {X S : Scheme.{u}} (sX : X ⟶ S)
    (U : X.Opens) (g : (Γ(X, U))ˣ) :
    sectionToAffineLine sX U ↑g⁻¹ ≫ affineYChart S = sectionToLine sX U ↑g := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc,
      show affineYChart S ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveLine (ULift.{u} ℤ))) = pullback.fst _ _ from
        affineYChart_comp S,
      sectionToAffineLine, pullback.lift_fst]
    exact (sectionToLine_comp sX U ↑g).symm
  · rw [Category.assoc, affineYChart, pullback.lift_snd, ← Category.assoc,
      sectionToAffineLine, pullback.lift_snd, sectionToLine, Category.assoc, affineChart,
      pullback.lift_snd, ← Category.assoc, sectionToAffineLine, pullback.lift_snd]
    exact sectionChartHom_comp_projectiveLineYChart U g

/-- `D₀` lies in the first affine chart. -/
theorem support_lineZeroDivisor_subset_range_affineChart (S : Scheme.{u}) :
    ((lineZeroDivisor S).support : Set (relativeProjectiveLine S)) ⊆
      Set.range (affineChart S) := by
  rw [coe_support_lineZeroDivisor,
    show lineZeroSection S =
      affineLineConstantSection S integralAffineZeroSection ≫ affineChart S from by
      rw [affineLineConstantSection_comp_affineChart,
        integralAffineZeroSection_comp_projectiveLineXChart],
    range_comp_scheme]
  exact Set.image_subset_range _ _

/-- `D_∞` lies in the second affine chart. -/
theorem support_lineInfinityDivisor_subset_range_affineYChart (S : Scheme.{u}) :
    ((lineInfinityDivisor S).support : Set (relativeProjectiveLine S)) ⊆
      Set.range (affineYChart S) := by
  rw [coe_support_lineInfinityDivisor]
  exact range_lineInfinitySection_subset_range_affineYChart S

/-! ### The coordinate of a chart as a section of `ℙ¹_S` -/

/-- The coordinate of an affine chart of `ℙ¹_S`, read as a section on the image of the chart. -/
def lineChartCoordinate {S : Scheme.{u}} (h : affineLineOver S ⟶ relativeProjectiveLine S)
    [IsOpenImmersion h] : Γ(relativeProjectiveLine S, h ''ᵁ ⊤) :=
  (h.appIso ⊤).inv (affineCoordinate S)

/-- The chart coordinate pulls back along the chart to the affine coordinate. -/
theorem appLE_lineChartCoordinate {S : Scheme.{u}}
    (h : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion h] :
    h.appLE (h ''ᵁ ⊤) ⊤ (h.preimage_image_eq ⊤).ge (lineChartCoordinate h) =
      affineCoordinate S := by
  rw [lineChartCoordinate, ← Scheme.Hom.appIso_hom' h ⊤]
  exact (h.appIso ⊤).inv_hom_id_apply _

/-- A divisor of `ℙ¹_S` cut out on a chart by the coordinate has, at every point of that chart,
the germ of the chart coordinate as a local equation. -/
theorem idealStalk_eq_span_germ_lineChartCoordinate {S : Scheme.{u}}
    (h : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion h]
    (I : (relativeProjectiveLine S).IdealSheafData)
    (hI : ∀ V : (affineLineOver S).affineOpens, (I.comap h).ideal V =
      Ideal.span {(affineLineOver S).presheaf.map (homOfLE le_top).op (affineCoordinate S)})
    (z : relativeProjectiveLine S) (hz : z ∈ h ''ᵁ ⊤) :
    IdealSheafData.stalk I z =
      Ideal.span {((relativeProjectiveLine S).presheaf.germ (h ''ᵁ ⊤) z hz)
        (lineChartCoordinate h)} := by
  have hzr : z ∈ Set.range h.base := by
    simpa [Scheme.Hom.image_top_eq_opensRange] using hz
  obtain ⟨y, rfl⟩ := hzr
  obtain ⟨V, hyV⟩ := Stacks.Divisors.exists_affineOpens_mem y
  have hbij : Function.Bijective (h.stalkMap y).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hgerm : ((affineLineOver S).presheaf.germ ⊤ y trivial) (affineCoordinate S) =
      (h.stalkMap y) (((relativeProjectiveLine S).presheaf.germ (h ''ᵁ ⊤) (h y) hz)
        (lineChartCoordinate h)) := by
    rw [← appLE_lineChartCoordinate h]
    exact appLE_germ_eq h (h.preimage_image_eq ⊤).ge y trivial (lineChartCoordinate h)
  refine ideal_map_cancel (h.stalkMap y).hom hbij ?_
  rw [← AlgebraicGeometry.IdealSheafData.stalk_comap I h y,
    AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ (I.comap h) y V hyV, hI V, Ideal.map_span,
    Set.image_singleton,
    (affineLineOver S).presheaf.germ_res_apply (homOfLE le_top) y hyV (affineCoordinate S), hgerm,
    Ideal.map_span, Set.image_singleton]

/-- The same, pulled back along a morphism to `ℙ¹_S`. -/
theorem idealStalk_comap_eq_span_germ_lineChartCoordinate {S Y : Scheme.{u}}
    (h : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion h]
    (I : (relativeProjectiveLine S).IdealSheafData)
    (hI : ∀ V : (affineLineOver S).affineOpens, (I.comap h).ideal V =
      Ideal.span {(affineLineOver S).presheaf.map (homOfLE le_top).op (affineCoordinate S)})
    (k : Y ⟶ relativeProjectiveLine S) (ξ : Y) (hξ : ξ ∈ k ⁻¹ᵁ (h ''ᵁ ⊤)) :
    IdealSheafData.stalk (I.comap k) ξ =
      Ideal.span {(Y.presheaf.germ (k ⁻¹ᵁ (h ''ᵁ ⊤)) ξ hξ)
        (k.appLE (h ''ᵁ ⊤) (k ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h))} := by
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap I k ξ,
    idealStalk_eq_span_germ_lineChartCoordinate h I hI (k ξ) hξ, Ideal.map_span,
    Set.image_singleton, appLE_germ_eq k le_rfl ξ hξ (lineChartCoordinate h)]

/-! ### The chart coordinate on the graph closure -/

section Graph

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (g : (Γ(X, U))ˣ) [QuasiCompact U.ι]

/-- Pulling a section of `U` back along a morphism that *is* the open immersion of `U` gives the
section read on `U` as a scheme. The morphism is taken as a variable together with the equation
identifying it, because the proof obligation of `Scheme.Hom.appLE` depends on it and so cannot be
rewritten. -/
private theorem appLE_eq_topIso_inv_of_eq_ι {X : Scheme.{u}} (U : X.Opens)
    (φ : U.toScheme ⟶ X) (hφ : φ = U.ι) (e : (⊤ : (U.toScheme).Opens) ≤ φ ⁻¹ᵁ U)
    (t : Γ(X, U)) : φ.appLE U ⊤ e t = U.topIso.inv t := by
  subst hφ
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg (fun ψ => (X.presheaf.map ψ) t) (Subsingleton.elim _ _)

/-- Pulling the chart coordinate back along a morphism that factors through the chart with
coordinate `t` gives `t`. As above, the morphism is a variable with its defining equation. -/
private theorem appLE_lineChartCoordinate_of_eq {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (h : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion h] (t : Γ(X, U))
    (φ : U.toScheme ⟶ relativeProjectiveLine S) (hφ : φ = sectionToAffineLine sX U t ≫ h)
    (e : (⊤ : (U.toScheme).Opens) ≤ φ ⁻¹ᵁ (h ''ᵁ ⊤)) :
    φ.appLE (h ''ᵁ ⊤) ⊤ e (lineChartCoordinate h) = U.topIso.inv t := by
  subst hφ
  have e₁ : (⊤ : (affineLineOver S).Opens) ≤ h ⁻¹ᵁ (h ''ᵁ ⊤) := (h.preimage_image_eq ⊤).ge
  have e₂ : (⊤ : (U.toScheme).Opens) ≤ sectionToAffineLine sX U t ⁻¹ᵁ ⊤ := le_top
  rw [show (sectionToAffineLine sX U t ≫ h).appLE (h ''ᵁ ⊤) ⊤ e =
      h.appLE (h ''ᵁ ⊤) ⊤ e₁ ≫ (sectionToAffineLine sX U t).appLE ⊤ ⊤ e₂ from
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e₁ e₂).symm,
    ConcreteCategory.comp_apply, appLE_lineChartCoordinate h,
    show (sectionToAffineLine sX U t).appLE (⊤ : (affineLineOver S).Opens) ⊤ e₂ =
      (sectionToAffineLine sX U t).appTop from Scheme.Hom.appLE_eq_app _,
    sectionToAffineLine_appTop_affineCoordinate]

/-- `p⁻¹(U)` is the image of `U` under the graph. -/
theorem graphPreimage_eq_image_graphInclusion :
    graphPreimage sX U ↑g = graphInclusion sX U ↑g ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact TopologicalSpace.Opens.ext (range_graphInclusion sX U ↑g).symm

omit [QuasiCompact U.ι] in
/-- The graph lands in `p⁻¹(U)`. -/
theorem top_le_preimage_graphPreimage :
    (⊤ : (U.toScheme).Opens) ≤ graphInclusion sX U ↑g ⁻¹ᵁ graphPreimage sX U ↑g := by
  intro x _
  change graphProjection sX U ↑g ((graphInclusion sX U ↑g) x) ∈ U
  rw [← Scheme.Hom.comp_apply, graphInclusion_comp_graphProjection]
  exact x.2

/-- Sections on `p⁻¹(U)` are determined by their pullback to `U`. -/
theorem injective_appLE_graphInclusion :
    Function.Injective ((graphInclusion sX U ↑g).appLE (graphPreimage sX U ↑g) ⊤
      (top_le_preimage_graphPreimage sX U g)) := by
  have hiso : IsIso ((graphInclusion sX U ↑g).appLE (graphInclusion sX U ↑g ''ᵁ ⊤) ⊤
      ((graphInclusion sX U ↑g).preimage_image_eq ⊤).ge) := by
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  refine (Scheme.Hom.appLE_congr (graphInclusion sX U ↑g) _
    (graphPreimage_eq_image_graphInclusion sX U g) rfl
    (fun {_ _} φ => Function.Injective φ)).mpr ?_
  exact (ConcreteCategory.bijective_of_isIso _).1

omit [QuasiCompact U.ι] in
/-- The pullback of a section along the graph is the pullback along the open immersion of `U`. -/
theorem appLE_graphInclusion_app_graphProjection (t : Γ(X, U)) :
    (graphInclusion sX U ↑g).appLE (graphPreimage sX U ↑g) ⊤
        (top_le_preimage_graphPreimage sX U g) (((graphProjection sX U ↑g).app U) t) =
      U.topIso.inv t := by
  rw [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_topIso_inv_of_eq_ι U _ (graphInclusion_comp_graphProjection sX U ↑g) _ t

/-- **The chart coordinate pulled back to `Y` restricts on `p⁻¹(U)` to the pullback of the
section whose chart morphism factors through that chart.** -/
theorem res_appLE_lineChartCoordinate
    (h : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion h] (t : Γ(X, U))
    (hfac : sectionToAffineLine sX U t ≫ h = sectionToLine sX U ↑g)
    (hWA : graphPreimage sX U ↑g ≤ graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) :
    (graphClosure sX U ↑g).presheaf.map (homOfLE hWA).op
        ((graphLineProjection sX U ↑g).appLE (h ''ᵁ ⊤)
          (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h)) =
      ((graphProjection sX U ↑g).app U) t := by
  refine injective_appLE_graphInclusion sX U g ?_
  rw [appLE_graphInclusion_app_graphProjection,
    show (graphClosure sX U ↑g).presheaf.map (homOfLE hWA).op
        ((graphLineProjection sX U ↑g).appLE (h ''ᵁ ⊤)
          (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h)) =
      (graphLineProjection sX U ↑g).appLE (h ''ᵁ ⊤) (graphPreimage sX U ↑g) hWA
        (lineChartCoordinate h) from by
      rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map],
    ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_lineChartCoordinate_of_eq sX U h t _
    ((graphInclusion_comp_graphLineProjection sX U ↑g).trans hfac.symm) _

/-- The image of `p⁻¹(U)` under `q` lies in the chart through which the section factors. -/
theorem graphPreimage_le_preimage_image_chart
    (h : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion h] (t : Γ(X, U))
    (hfac : sectionToAffineLine sX U t ≫ h = sectionToLine sX U ↑g) :
    graphPreimage sX U ↑g ≤ graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤) := by
  intro y hy
  have hy' : y ∈ Set.range (graphInclusion sX U ↑g).base := by
    rw [range_graphInclusion sX U ↑g]; exact hy
  obtain ⟨x, rfl⟩ := hy'
  change graphLineProjection sX U ↑g ((graphInclusion sX U ↑g) x) ∈ h ''ᵁ ⊤
  rw [← Scheme.Hom.comp_apply, graphInclusion_comp_graphLineProjection, ← hfac,
    Scheme.Hom.comp_apply]
  exact ⟨sectionToAffineLine sX U t x, trivial, rfl⟩

/-- On the function field, the pulled-back section equals the pulled-back chart coordinate. -/
private theorem germToFunctionField_eq_chart [IsIntegral (graphClosure sX U ↑g)]
    [Nonempty (graphPreimage sX U ↑g)]
    (hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g)
    (h : affineLineOver S ⟶ relativeProjectiveLine S) [IsOpenImmersion h] (t : Γ(X, U))
    (hfac : sectionToAffineLine sX U t ≫ h = sectionToLine sX U ↑g)
    [Nonempty (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤))] :
    (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
        (((graphProjection sX U ↑g).app U) t) =
      (graphClosure sX U ↑g).germToFunctionField
        (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤))
        ((graphLineProjection sX U ↑g).appLE (h ''ᵁ ⊤)
          (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h)) := by
  have hWA := graphPreimage_le_preimage_image_chart sX U g h t hfac
  rw [← res_appLE_lineChartCoordinate sX U g h t hfac hWA]
  exact (graphClosure sX U ↑g).presheaf.germ_res_apply (homOfLE hWA)
    (genericPoint (graphClosure sX U ↑g)) hηW _

end Graph

/-! ### The two fibre cycles -/

section Fibre

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens) (g : (Γ(X, U))ˣ) [QuasiCompact U.ι]
  [IsIntegral (graphClosure sX U ↑g)] [LocallyOfFiniteType (graphBaseMorphism sX U ↑g)]
  [IsLocallyNoetherian (graphClosure sX U ↑g)] [Nonempty (graphPreimage sX U ↑g)]

omit [LocallyOfFiniteType sX] [IsIntegral X] in
/-- At a codimension-one point of the fibre of a chart divisor, the order of vanishing of the
pulled-back section is the coefficient of the cycle of that fibre. -/
theorem ord_eq_cycleAssociatedToClosedSubscheme_apply_of_chart
    {n : ℤ} (hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt))
    (hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g)
    (h : affineLineOver C.S ⟶ relativeProjectiveLine C.S) [IsOpenImmersion h]
    (I : (relativeProjectiveLine C.S).IdealSheafData)
    (hI : ∀ V : (affineLineOver C.S).affineOpens, (I.comap h).ideal V =
      Ideal.span {(affineLineOver C.S).presheaf.map (homOfLE le_top).op (affineCoordinate C.S)})
    (hsupp : (I.support : Set (relativeProjectiveLine C.S)) ⊆ Set.range h.base)
    (t : Γ(X, U)) (hfac : sectionToAffineLine sX U t ≫ h = sectionToLine sX U ↑g)
    (htne : (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
      (((graphProjection sX U ↑g).app U) t) ≠ 0)
    (hgen : genericPoint (graphClosure sX U ↑g) ∉
      Set.range (I.comap (graphLineProjection sX U ↑g)).subschemeι.base)
    {ξ : graphClosure sX U ↑g} (hco : coheight ξ = 1)
    (hξ : ξ ∈ Set.range (I.comap (graphLineProjection sX U ↑g)).subschemeι.base) :
    (graphClosure sX U ↑g).ord ((graphClosure sX U ↑g).germToFunctionField
        (graphPreimage sX U ↑g) (((graphProjection sX U ↑g).app U) t)) ξ =
      (cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
        (I.comap (graphLineProjection sX U ↑g)).subschemeι (n - 1)).1 ξ := by
  have hξA : ξ ∈ graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤) := by
    have hsup : ξ ∈ (((I.comap (graphLineProjection sX U ↑g)).support :
        TopologicalSpace.Closeds (graphClosure sX U ↑g)) : Set (graphClosure sX U ↑g)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact hξ
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] at hsup
    obtain ⟨y, hy⟩ := hsupp hsup
    exact ⟨y, trivial, hy⟩
  have : Nonempty (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) := ⟨⟨ξ, hξA⟩⟩
  have hgf := germToFunctionField_eq_chart sX U g hηW h t hfac
  rw [hgf] at htne ⊢
  refine (principalDivisorCycle_apply C (graphBaseMorphism sX U ↑g) hYdim _ ξ).symm.trans
    (principalDivisorCycle_apply_eq_cycleAssociatedToClosedSubscheme_apply C
      (graphBaseMorphism sX U ↑g) hYdim (I.comap (graphLineProjection sX U ↑g)) hgen hco hξ hξA
      _ ?_ ?_)
  · intro h0
    exact htne (by rw [h0, map_zero])
  · exact idealStalk_comap_eq_span_germ_lineChartCoordinate h I hI
      (graphLineProjection sX U ↑g) ξ hξA

omit [LocallyOfFiniteType sX] [IsIntegral X] [LocallyOfFiniteType (graphBaseMorphism sX U ↑g)] in
/-- Away from the fibre of a chart divisor the pulled-back section is a unit, so its order of
vanishing is zero. -/
theorem ord_eq_zero_of_notMem_support_of_chart
    (hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g)
    (h : affineLineOver C.S ⟶ relativeProjectiveLine C.S) [IsOpenImmersion h]
    (I : (relativeProjectiveLine C.S).IdealSheafData)
    (hI : ∀ V : (affineLineOver C.S).affineOpens, (I.comap h).ideal V =
      Ideal.span {(affineLineOver C.S).presheaf.map (homOfLE le_top).op (affineCoordinate C.S)})
    (t : Γ(X, U)) (hfac : sectionToAffineLine sX U t ≫ h = sectionToLine sX U ↑g)
    (htne : (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
      (((graphProjection sX U ↑g).app U) t) ≠ 0)
    {ξ : graphClosure sX U ↑g} (hco : coheight ξ = 1)
    (hξA : ξ ∈ graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤))
    (hξ : ξ ∉ Set.range (I.comap (graphLineProjection sX U ↑g)).subschemeι.base) :
    (graphClosure sX U ↑g).ord ((graphClosure sX U ↑g).germToFunctionField
      (graphPreimage sX U ↑g) (((graphProjection sX U ↑g).app U) t)) ξ = 0 := by
  have : Nonempty (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) := ⟨⟨ξ, hξA⟩⟩
  have hgf := germToFunctionField_eq_chart sX U g hηW h t hfac
  have hstalk := idealStalk_comap_eq_span_germ_lineChartCoordinate h I hI
    (graphLineProjection sX U ↑g) ξ hξA
  have htop : IdealSheafData.stalk (I.comap (graphLineProjection sX U ↑g)) ξ = ⊤ := by
    refine idealStalk_eq_top_of_notMem_support _ ?_
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact hξ
  have hunit : IsUnit (((graphClosure sX U ↑g).presheaf.germ
      (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) ξ hξA)
      ((graphLineProjection sX U ↑g).appLE (h ''ᵁ ⊤)
        (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h))) :=
    Ideal.span_singleton_eq_top.mp (hstalk.symm.trans htop)
  rw [hgf] at htne ⊢
  have hzero := ord_eq_ringOrd_germ (Y := graphClosure sX U ↑g) hco hξA
    ((graphLineProjection sX U ↑g).appLE (h ''ᵁ ⊤)
      (graphLineProjection sX U ↑g ⁻¹ᵁ (h ''ᵁ ⊤)) le_rfl (lineChartCoordinate h))
    (fun h0 => htne (by rw [h0, map_zero])) (n := 0)
    (by rw [Ring.ord_of_isUnit hunit]; rfl)
  simpa using hzero

end Fibre

/-! ### Part (4) -/

/-- On `Y` the principal divisor of the rational
function induced by a unit section on `U` is the difference of the cycles of the two
distinguished fibres `Y₀` and `Y_∞`.

The rational function is the one of Tag 01RU, carried to
`AlgebraicGeometry.Scheme.functionField` by `Stacks.Chow.rationalFunctionsEquivFunctionField`,
as in part (5). -/
theorem principalDivisorCycle_graphClosure_eq_sub (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens) (g : (Γ(X, U))ˣ)
    [QuasiCompact U.ι] (n : ℤ) (hd : GraphPreimageDense sX U ↑g)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g)) :
    letI : IsIntegral (graphClosure sX U ↑g) := hYint
    letI : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) := hYft
    ∀ hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt),
      principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
          ((rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
            ↑(graphRationalFunction sX U g hd)) =
        cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
            (graphZeroFiber sX U ↑g).subschemeι (n - 1) -
          cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
            (graphInfinityFiber sX U ↑g).subschemeι (n - 1) := by
  intro hYdim
  have := hYint
  have := hYft
  have hLN : IsLocallyNoetherian (graphClosure sX U ↑g) :=
    LocallyOfFiniteType.isLocallyNoetherian (graphBaseMorphism sX U ↑g)
  have hWne : Nonempty (graphPreimage sX U ↑g) := Set.nonempty_coe_sort.mpr hd.nonempty
  have hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g :=
    ((genericPoint_spec (graphClosure sX U ↑g)).mem_open_set_iff
      (graphPreimage sX U ↑g).2).mpr (by simpa using hd.nonempty)
  have hUne : Nonempty U.toScheme := by
    obtain ⟨y, hy⟩ := hd.nonempty
    exact ⟨⟨graphProjection sX U ↑g y, hy⟩⟩
  set f0 := (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
    (((graphProjection sX U ↑g).app U) (↑g : Γ(X, U))) with hf0def
  set finf := (graphClosure sX U ↑g).germToFunctionField (graphPreimage sX U ↑g)
    (((graphProjection sX U ↑g).app U) (↑g⁻¹ : Γ(X, U))) with hfinfdef
  have hmul : f0 * finf = 1 := by
    rw [hf0def, hfinfdef, ← map_mul, ← map_mul, g.mul_inv, map_one, map_one]
  have hf0ne : f0 ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hfinfne : finf ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  have hfeq : (rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
      ↑(graphRationalFunction sX U g hd) = f0 := by
    rw [show (↑(graphRationalFunction sX U g hd) : rationalFunctions (graphClosure sX U ↑g)) =
        ofSection (graphClosure sX U ↑g) ⟨graphPreimage sX U ↑g, hd⟩
          (((graphProjection sX U ↑g).app U).hom ↑g) from ofSectionRingHom_apply _ _ _]
    exact (rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).2
      ⟨graphPreimage sX U ↑g, hd⟩ _ hηW
  have hgen0 : genericPoint (graphClosure sX U ↑g) ∉
      Set.range (graphZeroFiber sX U ↑g).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact notMem_support_graphZeroFiber_genericPoint sX U g
  have hgeninf : genericPoint (graphClosure sX U ↑g) ∉
      Set.range (graphInfinityFiber sX U ↑g).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact notMem_support_graphInfinityFiber_genericPoint sX U g
  rw [hfeq]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun ξ => ?_)
  change (graphClosure sX U ↑g).ord f0 ξ =
    (cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
        (graphZeroFiber sX U ↑g).subschemeι (n - 1)).1 ξ -
      (cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
        (graphInfinityFiber sX U ↑g).subschemeι (n - 1)).1 ξ
  have hzero : ∀ Z : (graphClosure sX U ↑g).IdealSheafData,
      ξ ∉ Set.range Z.subschemeι.base →
      (cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g) Z.subschemeι
        (n - 1)).1 ξ = 0 :=
    fun Z hZ => cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C
      (graphBaseMorphism sX U ↑g) Z.subschemeι (n - 1) hZ
  by_cases hco : coheight ξ = 1
  · by_cases h0 : ξ ∈ Set.range (graphZeroFiber sX U ↑g).subschemeι.base
    · have hinf : ξ ∉ Set.range (graphInfinityFiber sX U ↑g).subschemeι.base := by
        intro hc
        exact Set.disjoint_left.mp
          (disjoint_support_graphZeroFiber_graphInfinityFiber sX U ↑g)
          (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact h0)
          (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact hc)
      rw [hzero _ hinf, sub_zero]
      exact ord_eq_cycleAssociatedToClosedSubscheme_apply_of_chart C sX U g hYdim hηW
        (affineChart C.S) (lineZeroDivisor C.S) (zeroDivisor_ideal_comap_affineChart C.S)
        (support_lineZeroDivisor_subset_range_affineChart C.S) ↑g rfl hf0ne hgen0 hco h0
    · by_cases hinf : ξ ∈ Set.range (graphInfinityFiber sX U ↑g).subschemeι.base
      · rw [hzero _ h0, zero_sub]
        have key := ord_eq_cycleAssociatedToClosedSubscheme_apply_of_chart C sX U g hYdim hηW
          (affineYChart C.S) (lineInfinityDivisor C.S)
          (infinityDivisor_ideal_comap_affineYChart C.S)
          (support_lineInfinityDivisor_subset_range_affineYChart C.S) ↑g⁻¹
          (sectionToAffineLine_inv_comp_affineYChart sX U g) hfinfne hgeninf hco hinf
        have key2 : (graphClosure sX U ↑g).ord finf ξ =
            (cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g)
              (graphInfinityFiber sX U ↑g).subschemeι (n - 1)).1 ξ := key
        rw [← key2, ord_inv_eq_neg hf0ne hfinfne hmul ξ, neg_neg]
      · rw [hzero _ h0, hzero _ hinf, sub_zero]
        by_cases hA : graphLineProjection sX U ↑g ξ ∈ (affineChart C.S) ''ᵁ ⊤
        · exact ord_eq_zero_of_notMem_support_of_chart C sX U g hηW (affineChart C.S)
            (lineZeroDivisor C.S) (zeroDivisor_ideal_comap_affineChart C.S) ↑g rfl hf0ne hco
            hA h0
        · have hA2 : graphLineProjection sX U ↑g ξ ∉ Set.range (affineChart C.S).base := by
            intro hc
            obtain ⟨y, hy⟩ := hc
            exact hA ⟨y, trivial, hy⟩
          have hmem : graphLineProjection sX U ↑g ξ ∈ Set.range (affineYChart C.S).base := by
            have hmem0 : graphLineProjection sX U ↑g ξ ∈
                Set.range (affineChart C.S).base ∪ Set.range (affineYChart C.S).base := by
              rw [Stacks.Chow.range_affineChart_union_range_affineYChart C.S]; trivial
            exact hmem0.resolve_left hA2
          obtain ⟨y, hy⟩ := hmem
          have key := ord_eq_zero_of_notMem_support_of_chart C sX U g hηW (affineYChart C.S)
            (lineInfinityDivisor C.S) (infinityDivisor_ideal_comap_affineYChart C.S) ↑g⁻¹
            (sectionToAffineLine_inv_comp_affineYChart sX U g) hfinfne hco
            ⟨y, trivial, hy⟩ hinf
          rw [ord_inv_eq_neg hf0ne hfinfne hmul ξ] at key
          omega
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hco]
    have hzz : ∀ Z : (graphClosure sX U ↑g).IdealSheafData,
        (cycleAssociatedToClosedSubscheme C (graphBaseMorphism sX U ↑g) Z.subschemeι
          (n - 1)).1 ξ = 0 := by
      intro Z
      refine cycleAssociatedToClosedSubscheme_apply_eq_zero C (graphBaseMorphism sX U ↑g)
        Z.subschemeι (n - 1) ξ ?_
      rintro ⟨η, -, hdim⟩
      exact hco ((relativeDimension_eq_sub_one_iff_coheight_eq_one C
        (graphBaseMorphism sX U ↑g) hYdim ξ).mp hdim)
    rw [hzz, hzz, sub_zero]

end Stacks.Chow

end
