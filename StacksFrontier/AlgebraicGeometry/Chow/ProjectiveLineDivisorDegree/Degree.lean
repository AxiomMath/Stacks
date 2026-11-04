module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.AffineLineIso
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Chart
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Transition
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GraphLineProjectionFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
import all StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree of a principal divisor on the projective line over a field

Let `k` be a field. This file proves that the degree of a principal divisor on `ℙ¹_k` vanishes:
for every nonzero rational function `h` on `ℙ¹_k`,

  `∑_x ord_x(h) · [κ(x) : k] = 0`.

This is the projective-line case of Stacks 02RU, in the geometric form that the reduction of
Stacks 02RU to the projective line consumes.

The proof is the dictionary between `ℙ¹_k` and the arithmetic of `RatFunc k`:

* the complement of the first affine chart is the single point at infinity
  (`Stacks.Chow.compl_range_affineChart_eq_singleton`), where the residue degree is one, so the
  sum splits as the chart contribution plus the order at infinity;
* the chart contribution is the integer degree of the rational function read in the chart
  coordinate (`Stacks.Chow.finsum_mem_range_ord_mul_residueDegree`);
* the point at infinity is the origin of the *second* chart, so the order there is
  `Stacks.Chow.ordAt Polynomial.X` of the rational function read in the second chart coordinate;
* the two chart readings differ by the inversion of the coordinate — this is the gluing relation
  of `ℙ¹`, `Stacks.Chow.puncturedChartOver_appTop_affineCoordinate_mul` — and for the inversion
  `Stacks.Chow.ordAt_X_eq_neg_intDegree` says that order is minus the integer degree.

## Main definitions

* `Stacks.Chow.lineChartX`, `Stacks.Chow.lineChartY` — the two affine charts of `ℙ¹_k`, presented
  as morphisms out of `Spec k[T]`.
* `Stacks.Chow.lineCoordinateX`, `Stacks.Chow.lineCoordinateY` — the two chart coordinates as
  rational functions on `ℙ¹_k`.

## Main results

* `Stacks.Chow.compactSpace_lineOver` — `ℙ¹_k` is compact.
* `Stacks.Chow.lineCoordinateX_mul_lineCoordinateY` — the two chart coordinates are inverse to
  each other.
* `Stacks.Chow.principalDivisorDegree_lineOver_eq_zero` — **the degree of a principal divisor on
  `ℙ¹_k` is zero.**

## Implementation notes

### The three compatibilities of the chart identification

The two charts are presented as morphisms out of `Spec k[T]` by composing the isomorphism
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoSpecPolynomial` with
`Stacks.Chow.affineChart` and `Stacks.Chow.affineYChart`. Three compatibilities of that
isomorphism are taken as hypotheses: that it is an isomorphism over the base, that it carries `T`
to the affine coordinate, and that it carries the origin to the point of `T`. This file does not
depend on how they are proved; they are supplied by
`StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.AffineLineIso`.

### Why the function-field maps are compared through a third scheme

Neither chart reading of a rational function is computable from the other directly: the
comparison happens on the punctured line, where both charts restrict and where the two pullbacks
of the affine coordinate are inverse. `Stacks.Chow.dominantFunctionFieldMap_congr` is what lets
the two factorisations of the one morphism from the punctured line be used interchangeably,
`AlgebraicGeometry.dominantFunctionFieldMap` taking its dominance as an instance argument.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace Polynomial

universe u

namespace Stacks.Chow

/-! ### Two generalities -/

/-- The top open of a nonempty scheme is nonempty. -/
instance nonempty_opens_top (X : Scheme.{u}) [Nonempty X] :
    Nonempty ((⊤ : X.Opens) : Type u) :=
  ⟨⟨‹Nonempty X›.some, trivial⟩⟩

/-- The function-field map of a dominant morphism of integral schemes carries the germ at the
generic point of a global section to the germ of its pullback. -/
theorem dominantFunctionFieldMap_germToFunctionField {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (s : Γ(Y, ⊤)) :
    dominantFunctionFieldMap f (Y.germToFunctionField ⊤ s)
      = X.germToFunctionField ⊤ (f.appTop s) := by
  have h := DFunLike.congr_fun (appLE_germToFunctionField_commutes f ⊤ ⊤ le_top) s
  have h2 : Scheme.Hom.appLE f ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f (U := ⊤)
  rw [h2] at h
  exact h.symm

/-! ### The two charts of the projective line over a field -/

variable (k : Type u) [Field k]

/-- The base of the relative projective line over a field. -/
abbrev lineBase : Scheme.{u} := AlgebraicGeometry.Spec (CommRingCat.of k)

/-- The relative projective line over a field. -/
abbrev lineOver : Scheme.{u} := relativeProjectiveLine (lineBase k)

/-- The first affine chart of `ℙ¹_k`, as a morphism from `Spec k[T]`. -/
def lineChartX : specPolynomial k ⟶ lineOver k :=
  (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv ≫ affineChart (lineBase k)

/-- The second affine chart of `ℙ¹_k`, as a morphism from `Spec k[T]`. -/
def lineChartY : specPolynomial k ⟶ lineOver k :=
  (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv ≫ affineYChart (lineBase k)

/-- The first chart `Spec k[T] ⟶ ℙ¹_k` is an open immersion. -/
instance isOpenImmersion_lineChartX : IsOpenImmersion (lineChartX k) :=
  inferInstanceAs (IsOpenImmersion ((affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv ≫
    affineChart (lineBase k)))

/-- The second chart `Spec k[T] ⟶ ℙ¹_k` is an open immersion. -/
instance isOpenImmersion_lineChartY : IsOpenImmersion (lineChartY k) :=
  inferInstanceAs (IsOpenImmersion ((affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv ≫
    affineYChart (lineBase k)))

/-- The first affine chart of `ℙ¹_k` is dominant. -/
instance isDominant_affineChart : IsDominant (affineChart (lineBase k)) :=
  isDominant_of_isOpenImmersion _

/-- The second affine chart of `ℙ¹_k` is dominant. -/
instance isDominant_affineYChart : IsDominant (affineYChart (lineBase k)) :=
  isDominant_of_isOpenImmersion _

/-- The first chart `Spec k[T] ⟶ ℙ¹_k` is dominant. -/
instance isDominant_lineChartX : IsDominant (lineChartX k) :=
  isDominant_of_isOpenImmersion _

/-- The second chart `Spec k[T] ⟶ ℙ¹_k` is dominant. -/
instance isDominant_lineChartY : IsDominant (lineChartY k) :=
  isDominant_of_isOpenImmersion _

/-- The image of the first chart out of `Spec k[T]` is the image of the first affine chart. -/
theorem range_lineChartX :
    Set.range (lineChartX k).base = Set.range (affineChart (lineBase k)).base := by
  rw [lineChartX, range_comp_scheme, (surjective_of_isIso _).range_eq, Set.image_univ]

/-- The image of the second chart out of `Spec k[T]` is the image of the second affine chart. -/
theorem range_lineChartY :
    Set.range (lineChartY k).base = Set.range (affineYChart (lineBase k)).base := by
  rw [lineChartY, range_comp_scheme, (surjective_of_isIso _).range_eq, Set.image_univ]

/-- **`ℙ¹_k` is compact**: it is covered by the images of the two charts, each the image of the
compact `Spec k[T]`. -/
instance compactSpace_lineOver : CompactSpace (lineOver k) where
  isCompact_univ := by
    rw [← range_affineChart_union_range_affineYChart (lineBase k), ← range_lineChartX,
      ← range_lineChartY]
    exact (isCompact_range (lineChartX k).continuous).union
      (isCompact_range (lineChartY k).continuous)

/-! ### The two chart coordinates as rational functions -/

/-- The coordinate of the first chart, as a rational function on `ℙ¹_k`. -/
def lineCoordinateX : (lineOver k).functionField :=
  (chartFunctionFieldEquiv k (lineChartX k)).symm RatFunc.X

/-- The coordinate of the second chart, as a rational function on `ℙ¹_k`. -/
def lineCoordinateY : (lineOver k).functionField :=
  (chartFunctionFieldEquiv k (lineChartY k)).symm RatFunc.X

/-- The affine coordinate of `𝔸¹_k`, as an element of its function field. -/
def affineCoordinateFunction : (affineLineOver (lineBase k)).functionField :=
  (affineLineOver (lineBase k)).germToFunctionField ⊤ (affineCoordinate (lineBase k))

/-- The two charts lie over the base: they are the structure morphism of `Spec k[T]`. -/
theorem lineChartX_comp : lineChartX k ≫ (lineOver k ↘ lineBase k) = specPolynomialOver k := by
  rw [lineChartX, Category.assoc, affineChart_comp]
  exact affineLineOverIsoSpecPolynomial_inv_comp (CommRingCat.of k)

/-- The second chart lies over the base as well. -/
theorem lineChartY_comp : lineChartY k ≫ (lineOver k ↘ lineBase k) = specPolynomialOver k := by
  rw [lineChartY, Category.assoc, affineYChart_comp]
  exact affineLineOverIsoSpecPolynomial_inv_comp (CommRingCat.of k)

/-- The identification of the function field of `Spec k[T]` with `RatFunc k` carries the
coordinate `T` to `RatFunc.X`. -/
theorem ratFuncEquivFunctionField_symm_X :
    (ratFuncEquivFunctionField k).symm RatFunc.X
      = specAlgebraMap (CommRingCat.of (Polynomial k)) Polynomial.X := by
  rw [RingEquiv.symm_apply_eq,
    specFunctionFieldEquiv_specAlgebraMap (CommRingCat.of (Polynomial k)) (RatFunc k)]
  exact RatFunc.algebraMap_X.symm

/-- The chart identification of the affine line with `Spec k[T]` carries the affine coordinate to
the coordinate `T`. -/
theorem dominantFunctionFieldMap_isoInv_affineCoordinateFunction :
    dominantFunctionFieldMap (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv
        (affineCoordinateFunction k)
      = specAlgebraMap (CommRingCat.of (Polynomial k)) Polynomial.X := by
  have key : (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv.appTop
        (affineCoordinate (lineBase k))
      = (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X := by
    rw [← appTop_affineLineOverIsoSpecPolynomial_hom (CommRingCat.of k),
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    rfl
  rw [affineCoordinateFunction, dominantFunctionFieldMap_germToFunctionField, key,
    germToFunctionField_eq_specAlgebraMap]

/-- The function-field map of a chart factoring through the affine line, factored. -/
private theorem dominantFunctionFieldMap_chart_comp
    (j : specPolynomial k ⟶ lineOver k) (g : affineLineOver (lineBase k) ⟶ lineOver k)
    [IsOpenImmersion j] [IsDominant j] [IsDominant g]
    (hj : j = (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv ≫ g) :
    dominantFunctionFieldMap j
      = (dominantFunctionFieldMap (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv).comp
        (dominantFunctionFieldMap g) := by
  rw [dominantFunctionFieldMap_congr j _ hj]
  exact dominantFunctionFieldMap_comp _ _

/-- The function-field map of the first chart out of `Spec k[T]`, factored. -/
theorem dominantFunctionFieldMap_lineChartX :
    dominantFunctionFieldMap (lineChartX k)
      = (dominantFunctionFieldMap (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv).comp
        (dominantFunctionFieldMap (affineChart (lineBase k))) :=
  dominantFunctionFieldMap_chart_comp k _ _ rfl

/-- The function-field map of the second chart out of `Spec k[T]`, factored. -/
theorem dominantFunctionFieldMap_lineChartY :
    dominantFunctionFieldMap (lineChartY k)
      = (dominantFunctionFieldMap (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv).comp
        (dominantFunctionFieldMap (affineYChart (lineBase k))) :=
  dominantFunctionFieldMap_chart_comp k _ _ rfl

/-- A chart `Spec k[T] ⟶ ℙ¹_k` factoring through the affine line carries its coordinate to the
affine coordinate there. -/
private theorem dominantFunctionFieldMap_chart_coordinate
    (j : specPolynomial k ⟶ lineOver k) (g : affineLineOver (lineBase k) ⟶ lineOver k)
    [IsOpenImmersion j] [IsDominant j] [IsDominant g]
    (hj : j = (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv ≫ g) :
    dominantFunctionFieldMap g ((chartFunctionFieldEquiv k j).symm RatFunc.X)
      = affineCoordinateFunction k := by
  refine (dominantFunctionFieldMap
    (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv).injective ?_
  rw [dominantFunctionFieldMap_isoInv_affineCoordinateFunction, ← RingHom.comp_apply,
    ← dominantFunctionFieldMap_chart_comp k j g hj,
    dominantFunctionFieldMap_chartFunctionFieldEquiv_symm, ratFuncEquivFunctionField_symm_X]

/-- The first chart coordinate restricts to the affine coordinate on the affine line. -/
theorem dominantFunctionFieldMap_affineChart_lineCoordinateX :
    dominantFunctionFieldMap (affineChart (lineBase k)) (lineCoordinateX k)
      = affineCoordinateFunction k :=
  dominantFunctionFieldMap_chart_coordinate k (lineChartX k) _ rfl

/-- The second chart coordinate restricts to the affine coordinate on the affine line. -/
theorem dominantFunctionFieldMap_affineYChart_lineCoordinateY :
    dominantFunctionFieldMap (affineYChart (lineBase k)) (lineCoordinateY k)
      = affineCoordinateFunction k :=
  dominantFunctionFieldMap_chart_coordinate k (lineChartY k) _ rfl

/-! ### The two chart coordinates are inverse to each other -/

/-- **The gluing relation of `ℙ¹_k`, read on rational functions.** The two chart coordinates,
read as rational functions on `ℙ¹_k`, are inverse to each other. Both restrict to the affine
coordinate on their chart, and the two restrictions of the affine coordinate to the punctured
line are inverse (`Stacks.Chow.puncturedChartOver_appTop_affineCoordinate_mul`). -/
theorem lineCoordinateX_mul_lineCoordinateY : lineCoordinateX k * lineCoordinateY k = 1 := by
  have _ : IsDominant (puncturedChartOver (lineBase k)) := isDominant_of_isOpenImmersion _
  have _ : IsDominant (puncturedYChartOver (lineBase k)) := isDominant_of_isOpenImmersion _
  have h1 : dominantFunctionFieldMap (puncturedChartOver (lineBase k) ≫ affineChart (lineBase k))
        (lineCoordinateX k)
      = (puncturedLineOver (lineBase k)).germToFunctionField ⊤
        ((puncturedChartOver (lineBase k)).appTop (affineCoordinate (lineBase k))) := by
    rw [dominantFunctionFieldMap_comp, RingHom.comp_apply,
      dominantFunctionFieldMap_affineChart_lineCoordinateX, affineCoordinateFunction,
      dominantFunctionFieldMap_germToFunctionField]
  have h2 : dominantFunctionFieldMap
        (puncturedYChartOver (lineBase k) ≫ affineYChart (lineBase k)) (lineCoordinateY k)
      = (puncturedLineOver (lineBase k)).germToFunctionField ⊤
        ((puncturedYChartOver (lineBase k)).appTop (affineCoordinate (lineBase k))) := by
    rw [dominantFunctionFieldMap_comp, RingHom.comp_apply,
      dominantFunctionFieldMap_affineYChart_lineCoordinateY, affineCoordinateFunction,
      dominantFunctionFieldMap_germToFunctionField]
  have hcong := dominantFunctionFieldMap_congr
    (puncturedChartOver (lineBase k) ≫ affineChart (lineBase k))
    (puncturedYChartOver (lineBase k) ≫ affineYChart (lineBase k))
    (puncturedChartOver_comp_affineChart (lineBase k))
  refine (dominantFunctionFieldMap
    (puncturedChartOver (lineBase k) ≫ affineChart (lineBase k))).injective ?_
  rw [map_mul, map_one, h1, hcong, h2, ← map_mul,
    puncturedChartOver_appTop_affineCoordinate_mul, map_one]

/-! ### The transition automorphism of the field of rational functions -/

/-- The change of chart, as an automorphism of `RatFunc k`: read a rational function in the first
chart, then read the result in the second. -/
def lineTransition : RatFunc k ≃+* RatFunc k :=
  (chartFunctionFieldEquiv k (lineChartX k)).symm.trans (chartFunctionFieldEquiv k (lineChartY k))

/-- The change of chart inverts the coordinate. -/
theorem lineTransition_X : lineTransition k RatFunc.X = (RatFunc.X : RatFunc k)⁻¹ := by
  have hY : chartFunctionFieldEquiv k (lineChartY k) (lineCoordinateY k) = RatFunc.X :=
    (chartFunctionFieldEquiv k (lineChartY k)).apply_symm_apply _
  have hprod : chartFunctionFieldEquiv k (lineChartY k) (lineCoordinateX k) * RatFunc.X
      = (1 : RatFunc k) := by
    rw [← hY, ← map_mul, lineCoordinateX_mul_lineCoordinateY, map_one]
  show chartFunctionFieldEquiv k (lineChartY k) (lineCoordinateX k) = _
  exact eq_inv_of_mul_eq_one_left hprod

/-- A chart of `ℙ¹_k` carries the constant rational function of a scalar to the corresponding
constant polynomial: the chart lies over the base. -/
theorem dominantFunctionFieldMap_chart_constant
    (j : specPolynomial k ⟶ lineOver k) [IsOpenImmersion j] [IsDominant j]
    (hj : j ≫ (lineOver k ↘ lineBase k) = specPolynomialOver k) (x : k) :
    dominantFunctionFieldMap j ((lineOver k).germToFunctionField ⊤
        ((lineOver k ↘ lineBase k).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv x)))
      = specAlgebraMap (CommRingCat.of (Polynomial k)) (Polynomial.C x) := by
  have hnat := congrArg (fun m : CommRingCat.of k ⟶ Γ(specPolynomial k, ⊤) => m.hom x)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
  have happ : j.appTop ((lineOver k ↘ lineBase k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv x))
      = (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv (Polynomial.C x) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hj]
    exact hnat.symm
  rw [dominantFunctionFieldMap_germToFunctionField, happ,
    germToFunctionField_eq_specAlgebraMap]

/-- The change of chart fixes the constants: both charts lie over the base. -/
theorem lineTransition_algebraMap (x : k) :
    lineTransition k (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x := by
  have hconst : ∀ (j : specPolynomial k ⟶ lineOver k) (_ : IsOpenImmersion j)
      (_ : IsDominant j), j ≫ (lineOver k ↘ lineBase k) = specPolynomialOver k →
      chartFunctionFieldEquiv k j ((lineOver k).germToFunctionField ⊤
          ((lineOver k ↘ lineBase k).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv x)))
        = algebraMap k (RatFunc k) x := by
    intro j _ _ hj
    rw [chartFunctionFieldEquiv_apply, dominantFunctionFieldMap_chart_constant k j hj x,
      specFunctionFieldEquiv_specAlgebraMap (CommRingCat.of (Polynomial k)) (RatFunc k),
      ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
  have hX := hconst (lineChartX k) inferInstance inferInstance (lineChartX_comp k)
  have hY := hconst (lineChartY k) inferInstance inferInstance (lineChartY_comp k)
  have key : (chartFunctionFieldEquiv k (lineChartX k)).symm (algebraMap k (RatFunc k) x)
      = (lineOver k).germToFunctionField ⊤ ((lineOver k ↘ lineBase k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv x)) := by
    rw [← hX, RingEquiv.symm_apply_apply]
  show chartFunctionFieldEquiv k (lineChartY k)
    ((chartFunctionFieldEquiv k (lineChartX k)).symm (algebraMap k (RatFunc k) x)) = _
  rw [key]
  exact hY

/-! ### The point at infinity -/

/-- The point at infinity of `ℙ¹_k`, the image of the infinity section. -/
@[ega "II 7.4.14"]
def lineInfinityPoint : lineOver k :=
  (lineInfinitySection (lineBase k)).base (Classical.arbitrary (lineBase k))

/-- The complement of the first chart of `ℙ¹_k` is the point at infinity. -/
theorem compl_range_lineChartX :
    (Set.range (lineChartX k).base)ᶜ = {lineInfinityPoint k} := by
  rw [range_lineChartX]
  exact compl_range_affineChart_eq_singleton (lineBase k)

/-- The point at infinity is the origin of the second chart. -/
theorem lineInfinityPoint_eq :
    lineInfinityPoint k
      = (lineChartY k).base
        (irreduciblePoint (CommRingCat.of (Polynomial k)) (Polynomial.irreducible_X)) := by
  have horigin := asIdeal_affineLineOverIsoSpecPolynomial_hom_base_origin (CommRingCat.of k)
    (Field.toIsField k) (Classical.arbitrary (lineBase k))
  have hpt : (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).hom.base
        ((affineLineConstantSection (lineBase k) integralAffineZeroSection).base
          (Classical.arbitrary (lineBase k)))
      = irreduciblePoint (CommRingCat.of (Polynomial k)) (Polynomial.irreducible_X) :=
    PrimeSpectrum.ext horigin
  have hinv : (affineLineOverIsoSpecPolynomial (CommRingCat.of k)).inv.base
        (irreduciblePoint (CommRingCat.of (Polynomial k)) (Polynomial.irreducible_X))
      = (affineLineConstantSection (lineBase k) integralAffineZeroSection).base
        (Classical.arbitrary (lineBase k)) := by
    rw [← hpt]
    simp
  rw [lineInfinityPoint, ← lineInfinitySection_eq (lineBase k), lineChartY]
  exact congrArg (affineYChart (lineBase k)).base hinv.symm

/-- The residue degree of the structure morphism of `ℙ¹_k` at the point at infinity is one. -/
theorem residueDegree_lineInfinityPoint :
    (lineOver k ↘ lineBase k).residueDegree (lineInfinityPoint k) = 1 :=
  residueDegree_eq_one_of_lineConstantSection (lineBase k) integralInfinitySection
    (Classical.arbitrary (lineBase k))

/-! ### The degree of a principal divisor on the projective line -/

/-- **The degree of a principal divisor on `ℙ¹_k` is zero.** This is the projective-line case of
Stacks 02RU.

The sum splits as the contribution of the first chart, which is the integer degree of the
rational function read there, plus the contribution of the point at infinity, which is the order
of vanishing there because the residue degree is one. The point at infinity is the origin of the
second chart, so that order is `Stacks.Chow.ordAt Polynomial.X` of the rational function read in
the second chart; the two readings differ by the inversion of the coordinate, for which that
order is minus the integer degree. -/
theorem principalDivisorDegree_lineOver_eq_zero (h : (lineOver k).functionField) (hh : h ≠ 0) :
    principalDivisorDegree (lineOver k ↘ lineBase k) h = 0 := by
  classical
  have hfin : (Function.support fun x : lineOver k => (lineOver k).ord h x
      * ((lineOver k ↘ lineBase k).residueDegree x : ℤ)).Finite :=
    (finite_support_ord h).subset fun x hx => (mul_ne_zero_iff.mp hx).1
  have hsplit : principalDivisorDegree (lineOver k ↘ lineBase k) h
      = (∑ᶠ x ∈ Set.range (lineChartX k).base, (lineOver k).ord h x
          * ((lineOver k ↘ lineBase k).residueDegree x : ℤ))
        + (lineOver k).ord h (lineInfinityPoint k)
          * ((lineOver k ↘ lineBase k).residueDegree (lineInfinityPoint k) : ℤ) := by
    rw [principalDivisorDegree, ← finsum_mem_univ,
      ← Set.union_compl_self (Set.range (lineChartX k).base),
      finsum_mem_union' disjoint_compl_right (hfin.inter_of_right _) (hfin.inter_of_right _),
      compl_range_lineChartX, finsum_mem_singleton]
  have hchart := finsum_mem_range_ord_mul_residueDegree k (lineChartX k)
    (lineOver k ↘ lineBase k) (lineChartX_comp k) h hh
  have hinf : (lineOver k).ord h (lineInfinityPoint k)
      = ordAt (Polynomial.X : Polynomial k) (chartFunctionFieldEquiv k (lineChartY k) h) := by
    rw [lineInfinityPoint_eq]
    exact ord_chart_irreduciblePoint k (lineChartY k) Polynomial.irreducible_X Polynomial.monic_X
      h hh
  have htrans : chartFunctionFieldEquiv k (lineChartY k) h
      = lineTransition k (chartFunctionFieldEquiv k (lineChartX k) h) := by
    rw [lineTransition]
    show _ = chartFunctionFieldEquiv k (lineChartY k)
      ((chartFunctionFieldEquiv k (lineChartX k)).symm
        (chartFunctionFieldEquiv k (lineChartX k) h))
    rw [RingEquiv.symm_apply_apply]
  have hord : ordAt (Polynomial.X : Polynomial k)
      (lineTransition k (chartFunctionFieldEquiv k (lineChartX k) h))
      = -(chartFunctionFieldEquiv k (lineChartX k) h).intDegree :=
    ordAt_X_eq_neg_intDegree (lineTransition k).toRingHom (lineTransition_algebraMap k)
      (lineTransition_X k) _ ((chartFunctionFieldEquiv k (lineChartX k)).map_ne_zero_iff.2 hh)
  rw [hsplit, hchart, hinf, htrans, residueDegree_lineInfinityPoint, hord]
  ring

end Stacks.Chow

end

