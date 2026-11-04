module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationChart
public import StacksFrontier.AlgebraicGeometry.Stacks.InvariantSubschemeSubstack
public import StacksFrontier.Topology.Stratification.Defs

/-!
# The strata of the weighted multiplicative-group quotient

Let `k` be a commutative ring, `U = Spec k[x_0, x_1, …]` with the action of `𝐆_m` in which `x_i`
has weight `p^i`, and `𝒳 = [U/𝐆_m]` the weighted quotient stack of **Stacks 06RE**
(`AlgebraicGeometry.PPowerWeighted.weightedQuotientStack`), with its smooth surjective chart
`a : U ⟶ 𝒳` (`AlgebraicGeometry.PPowerWeighted.chart`). This file constructs the strata of `𝒳`:
`𝒳_i`, where `x_0 = ⋯ = x_{i-1} = 0` and `x_i` is invertible, and `𝒳_∞`, where all the
coordinates vanish.

## Main definitions

* `AlgebraicGeometry.PPowerWeighted.stratumProperty`: the objects of `𝒳_a`, for `a : WithTop ℕ`:
  every lift to `U` of a base change of the object lies in the stratum `X_a` of `U`.
* `AlgebraicGeometry.PPowerWeighted.stratumPoints`: the image `|𝒳_a|` in `|𝒳|` of the stratum
  `X_a` of the spectrum (`AlgebraicGeometry.PPowerWeighted.stratumSet`).
* `AlgebraicGeometry.PPowerWeighted.stratification`: the stratification of `|𝒳|` by the `|𝒳_a|`,
  indexed by `WithTop ℕ` in the opposite order.

## Main results

* `AlgebraicGeometry.PPowerWeighted.chartObj_mem_stratumProperty_iff`: `a(h)` lies in `𝒳_a`
  exactly when `h` lies in `X_a`; the strata of `U` are invariant, two lifts of one object being
  related by the action of a unit (`AlgebraicGeometry.PPowerWeighted.chartVerticalEquiv`).
* `AlgebraicGeometry.PPowerWeighted.mem_stratumPoints_iff`: the strata of the spectrum are
  saturated for `|a| : |U| ⟶ |𝒳|`, because two points of `U` with the same image in `|𝒳|` are
  images of one point of the spectrum of a field under two points of `U` in one orbit
  (`AlgebraicGeometry.PPowerWeighted.exists_actMap_eq_of_chartPointMap_eq`).
* `AlgebraicGeometry.PPowerWeighted.isLocallyClosedSubstack_stratumProperty`,
  `AlgebraicGeometry.PPowerWeighted.isReducedStack_stratumProperty` and
  `AlgebraicGeometry.PPowerWeighted.range_pointsMap_stratumProperty`: each `𝒳_a` is a locally
  closed substack, reduced over a domain, with `|𝒳_a|` as its points. `𝒳_∞` is cut out by the
  invariant closed subscheme `X_∞` of `U`, and `𝒳_i` is the closed substack cut out by `X_i` in
  the open substack on the image of the basic open `D(x_i)`.
* `AlgebraicGeometry.PPowerWeighted.isLocallyClosed_stratumPoints`,
  `AlgebraicGeometry.PPowerWeighted.stratumPoints_nonempty` and
  `AlgebraicGeometry.PPowerWeighted.stratumPoints_injective`: each `|𝒳_a|` is locally closed, and
  over a field the strata are nonempty and pairwise distinct.

## References

* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.PPowerWeighted

/-- The base `Spec ℤ` of the site. -/
local macro "𝒵" : term => `(Spec (CommRingCat.of (ULift ℤ)))

variable (𝒞 : BigFppfSite.{u}) (k : Type u) [CommRing k] (p : ℕ)
  (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))

/-- The underlying topological space of `U` is the prime spectrum of `k[x_0, x_1, …]`. -/
def totalHomeomorph :
    (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (totalSiteObject 𝒞 k hU) ≃ₜ
      PrimeSpectrum (MvPolynomial ℕ k) :=
  Homeomorph.refl _

/-- The stratum `X_a` of `U` as an immersed subscheme. -/
def stratumSubscheme : WithTop ℕ →
    Subobject ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU))
  | ⊤ => stratumTopSubobject hU
  | (i : ℕ) => stratumImmersedSubobject hU i

variable {𝒞 k hU}

/-- The strata of `U` are immersed subschemes. -/
theorem isImmersion_stratumSubscheme_arrow (a : WithTop ℕ) :
    IsImmersion (stratumSubscheme 𝒞 k hU a).arrow := by
  induction a using WithTop.recTopCoe with
  | top =>
    have := isClosedImmersion_stratumTopSubobject_arrow (hU := hU)
    exact (inferInstance : IsImmersion (stratumTopSubobject hU).arrow)
  | coe i => exact isImmersion_stratumImmersedSubobject_arrow i

/-- The points of the immersed subscheme `X_a` are the points of the stratum `X_a`. -/
theorem subschemePoints_stratumSubscheme (a : WithTop ℕ) :
    Space.subschemePoints 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (stratumSubscheme 𝒞 k hU a) =
      stratumSubfunctor hU a := by
  induction a using WithTop.recTopCoe with
  | top => exact subschemePoints_stratumTopSubobject
  | coe i => exact subschemePoints_stratumImmersedSubobject i

/-- A vertical morphism between chart objects is the action of a unit. -/
theorem exists_actMap_eq_of_isHomLift {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU} (θ : chartObj.{u, w} p h ⟶ chartObj.{u, w} p h')
    (hθ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ) :
    ∃ γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ,
      actMap p γ h = h' :=
  ⟨(chartVerticalEquiv.{u, w} p h h' ⟨θ, hθ⟩).1, (chartVerticalEquiv.{u, w} p h h' ⟨θ, hθ⟩).2⟩

/-- The strata of `U` are invariant under the relation `U ×_𝒳 U`. -/
theorem isChartInvariantSubscheme_stratumSubscheme (a : WithTop ℕ) :
    Stack.IsChartInvariantSubscheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (chart.{u, w} 𝒞 k p hU) (stratumSubscheme 𝒞 k hU a) := by
  intro W h h' θ hθ hh
  rw [subschemePoints_stratumSubscheme] at hh ⊢
  obtain ⟨γ, rfl⟩ := exists_actMap_eq_of_isHomLift p θ hθ
  exact (actMap_mem_stratumSubfunctor_iff p a γ h).2 hh

variable (𝒞 k hU) in
/-- **The strata of the weighted quotient stack.** An object `x` of `𝒳 = [U/𝐆_m]` lies in the
stratum `𝒳_a` when every lift of a base change of `x` to the chart `U ⟶ 𝒳` is a point of the
stratum `X_a` of `U`. -/
def stratumProperty (a : WithTop ℕ) :
    ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj := fun x =>
  ∀ (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) (h : W ⟶ totalSiteObject 𝒞 k hU),
    (chartObj.{u, w} p h ⟶ x) → h ∈ (stratumSubfunctor hU a).obj (Opposite.op W)

/-- `𝒳_a` is the property cut out by the invariant subscheme `X_a` of the chart. -/
theorem stratumProperty_eq (a : WithTop ℕ) :
    stratumProperty.{u, w} 𝒞 k p hU a =
      Stack.invariantSubschemeProperty 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (chart.{u, w} 𝒞 k p hU) (stratumSubscheme 𝒞 k hU a) := by
  funext x
  simp [stratumProperty, Stack.invariantSubschemeProperty, subschemePoints_stratumSubscheme]

/-- The strata are inherited along morphisms. -/
theorem stratumProperty_of_hom {a : WithTop ℕ}
    {x y : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (φ : x ⟶ y)
    (hy : stratumProperty.{u, w} 𝒞 k p hU a y) : stratumProperty.{u, w} 𝒞 k p hU a x :=
  fun W h ψ => hy W h (ψ ≫ φ)

/-- The strata are closed under isomorphism. -/
instance (a : WithTop ℕ) : (stratumProperty.{u, w} 𝒞 k p hU a).IsClosedUnderIsomorphisms :=
  ⟨fun e hx => stratumProperty_of_hom p e.inv hx⟩

/-- **The chart object of a `W`-point of `U` lies in `𝒳_a` exactly when the point lies in
`X_a`.** -/
theorem chartObj_mem_stratumProperty_iff (a : WithTop ℕ)
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (h : W ⟶ totalSiteObject 𝒞 k hU) :
    stratumProperty.{u, w} 𝒞 k p hU a (chartObj.{u, w} p h) ↔
      h ∈ (stratumSubfunctor hU a).obj (Opposite.op W) := by
  rw [stratumProperty_eq, Stack.invariantSubschemeProperty_iff 𝒞 𝒵 _
      (isChartInvariantSubscheme_stratumSubscheme p a) h (𝟙 _)
      (IsHomLift.id (Functor.congr_obj (chart.{u, w} 𝒞 k p hU).hom.hom.w (Over.mk h))),
    subschemePoints_stratumSubscheme]

/-! ### Points of `U` and coordinates -/

section PointCoordinates

/-- A function `f` on `U` does not vanish at the image of a point `x` of `W` under `h : W ⟶ U`
exactly when its pullback along `h` does not vanish at `x`. -/
theorem notMem_asIdeal_iff_mem_basicOpen {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (x : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W)
    (f : MvPolynomial ℕ k) :
    f ∉ (totalHomeomorph 𝒞 k hU
        (((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h).base x)).asIdeal ↔
      x ∈ ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W).basicOpen
        (((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h).appTop
          ((Scheme.ΓSpecIso (.of (MvPolynomial ℕ k))).inv f)) := by
  have e := Scheme.preimage_basicOpen_top (Y := Spec (.of (MvPolynomial ℕ k)))
    ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h)
    ((Scheme.ΓSpecIso (.of (MvPolynomial ℕ k))).inv f)
  rw [basicOpen_eq_of_affine] at e
  rw [← e]
  exact Iff.rfl

/-- On a scheme whose ring of global functions is a field, a basic open is everything or nothing,
according to whether the function is nonzero. -/
theorem mem_basicOpen_iff_ne_zero {X : Scheme.{u}} (hX : IsField Γ(X, ⊤)) (x : X)
    (f : Γ(X, ⊤)) : x ∈ X.basicOpen f ↔ f ≠ 0 := by
  constructor
  · rintro hx rfl
    rw [Scheme.basicOpen_zero] at hx
    exact hx
  · intro hf
    obtain ⟨g, hg⟩ := hX.mul_inv_cancel hf
    rw [Scheme.basicOpen_of_isUnit X (IsUnit.of_mul_eq_one g hg)]
    trivial

/-- **The coordinates of a point of `U` with values in a field.** If `Γ(W)` is a field, the
`j`-th coordinate of a `W`-point `h` of `U` vanishes exactly when `x_j` vanishes at the image of
any point of `W`. -/
theorem X_mem_asIdeal_iff {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (hW : IsField Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (x : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W) (j : ℕ) :
    (MvPolynomial.X j : MvPolynomial ℕ k) ∈ (totalHomeomorph 𝒞 k hU
        (((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h).base x)).asIdeal ↔
      coord h j = 0 := by
  rw [← not_iff_not, notMem_asIdeal_iff_mem_basicOpen, mem_basicOpen_iff_ne_zero hW]
  rfl

/-- The action of a unit does not change which coordinates vanish. -/
theorem coord_actMap_eq_zero_iff {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) (j : ℕ) :
    coord (actMap p γ h) j = 0 ↔ coord h j = 0 := by
  rw [coord_actMap]
  exact ((Units.isUnit γ).pow _).mul_right_eq_zero

/-- The ring of global functions of a scheme isomorphic to the spectrum of a field is a field. -/
theorem isField_of_iso_spec {X : Scheme.{u}} {K : Type u} [Field K] (e : X ≅ Spec (.of K)) :
    IsField Γ(X, ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    ((Scheme.ΓSpecIso (.of K)).symm ≪≫
      Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.symm.toMulEquiv

/-- A scheme isomorphic to the spectrum of a field has at most one point. -/
theorem subsingleton_of_iso_spec {X : Scheme.{u}} {K : Type u} [Field K] (e : X ≅ Spec (.of K)) :
    Subsingleton X :=
  ⟨fun _ _ => e.schemeIsoToHomeo.injective (Subsingleton.elim _ _)⟩

end PointCoordinates

/-! ### Two points of `U` with the same image in `|𝒳|` -/

section Saturation

/-- **The image in `|𝒳|` of a point of `U` with values in a field.** If `W` is the spectrum of a
field `K`, the image in `|𝒳|` of the image of a point of `W` under `h : W ⟶ U` is the class of the
`K`-valued point `a(h)` of `𝒳`. -/
theorem chartPointMap_base_eq {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} {K : Type u}
    [Field K] (e : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W ≅ Spec (.of K))
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (x : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU)
        (((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h).base x) =
      Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        { carrier := K
          base := W
          isSpec := e
          obj := chartObj.{u, w} p (𝟙 W ≫ h)
          «over» := Functor.congr_obj (chart.{u, w} 𝒞 k p hU).hom.hom.w (Over.mk (𝟙 W ≫ h)) } := by
  let _ := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (Stack.schemeFibredCategory 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W)
  have hsub := subsingleton_of_iso_spec e
  rw [← Function.comp_apply (f := Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 _ _ _ _),
    ← Stack.chartPointMap_schemeStackMap_comp]
  have hq : (Stack.pointsHomeomorphScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W).symm x =
      Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        { carrier := K
          base := W
          isSpec := e
          obj := Over.mk (𝟙 W)
          «over» := rfl } :=
    (Stack.pointsHomeomorphScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W).injective
      (Subsingleton.elim _ _)
  simp only [Stack.AlgebraicStacks.chartPointMap, Function.comp_apply, hq]
  rfl

/-- Every point of `U` is the image of the point of the spectrum of a field, namely of its
residue field. -/
theorem exists_fieldPoint_base_eq
    (z : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (totalSiteObject 𝒞 k hU)) :
    ∃ (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) (K : Type u) (_ : Field K)
      (_ : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W ≅ Spec (.of K))
      (h : W ⟶ totalSiteObject 𝒞 k hU)
      (x : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W),
      ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h).base x = z := by
  have hz := 𝒞.residueField_spec_contains (totalSiteObject 𝒞 k hU).left.property z
  exact ⟨Space.residueFieldObject 𝒞 𝒵 _ _ z hz,
    (totalSiteObject 𝒞 k hU).left.1.residueField z, inferInstance, Iso.refl _,
    Space.residueFieldMap 𝒞 𝒵 _ _ z hz, IsLocalRing.closedPoint _,
    Scheme.fromSpecResidueField_apply _ _⟩

/-- A morphism `ψ : x ⟶ a(g)` to a chart object is, up to a morphism over the identity, the
image of a morphism of the site `j` into the base of `g`. -/
theorem exists_isHomLift_id_of_hom_chartObj {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {x : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (g : W ⟶ totalSiteObject 𝒞 k hU)
    (ψ : x ⟶ chartObj.{u, w} p g) :
    ∃ j : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x ⟶ W,
      (∃ θ : x ⟶ chartObj.{u, w} p (j ≫ g),
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
          (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x)) θ) ∧
      (∃ θ : chartObj.{u, w} p (j ≫ g) ⟶ x,
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
          (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x)) θ) := by
  have hw : (chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor ⋙
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p = Over.forget (totalSiteObject 𝒞 k hU) :=
    (chart.{u, w} 𝒞 k p hU).hom.hom.w
  have hdom : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj (chartObj.{u, w} p g) = W :=
    Functor.congr_obj hw (Over.mk g)
  set j := (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map ψ ≫ eqToHom hdom with hj
  have hψ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift j ψ := by
    rw [hj]
    infer_instance
  have hm : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift j
      ((chart.{u, w} 𝒞 k p hU).hom.hom.toFunctor.map
        (Over.homMk j rfl : Over.mk (j ≫ g) ⟶ Over.mk g)) :=
    PresheafOfCategories.isHomLift_map_of_comp hw j _ (IsHomLift.of_fac' _ _ _ rfl rfl (by simp))
  obtain ⟨θ₁, hθ₁, -⟩ := Stack.exists_isHomLift_id_comp_eq 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.property j ψ _ hψ hm
  obtain ⟨θ₂, hθ₂, -⟩ := Stack.exists_isHomLift_id_comp_eq 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.property j _ ψ hm hψ
  exact ⟨j, ⟨θ₁, hθ₁⟩, ⟨θ₂, hθ₂⟩⟩

/-- The base of a field-valued point of `𝒳` is isomorphic to the spectrum of its field. -/
private def fieldPointIso
    (r : Stack.FieldValuedPoint 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val) :
    (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj r.obj) ≅ Spec (.of r.carrier) :=
  (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).mapIso (eqToIso r.over) ≪≫ r.isSpec

/-- Pulling a point back along a morphism of the site into a point of a field-valued base does
not change its image in `U`. -/
private theorem map_comp_id_comp_base_eq {W W' : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {K : Type u} [Field K]
    (e : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W ≅ Spec (.of K))
    (j : W' ⟶ W) (h : W ⟶ totalSiteObject 𝒞 k hU)
    (y : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W')
    (x : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W) :
    ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map (j ≫ 𝟙 W ≫ h)).base y =
      ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h).base x := by
  have := subsingleton_of_iso_spec e
  rw [Category.id_comp, Functor.map_comp, Scheme.Hom.comp_apply]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **Two points of `U` with the same image in `|𝒳|` are in one orbit over a field.** They are the
images of one point of the spectrum of a field `R` under two `R`-points of `U` which differ by
the action of a unit of `Γ(R)`. -/
theorem exists_actMap_eq_of_chartPointMap_eq
    {z₁ z₂ : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU)}
    (he : Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) z₁ =
      Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) z₂) :
    ∃ (R : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
      (_ : IsField Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj R, ⊤))
      (x : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj R)
      (h₁ h₂ : R ⟶ totalSiteObject 𝒞 k hU)
      (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj R, ⊤))ˣ),
      actMap p γ h₁ = h₂ ∧
        ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h₁).base x = z₁ ∧
        ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h₂).base x = z₂ := by
  obtain ⟨W₁, K₁, _, e₁, h₁, x₁, rfl⟩ := exists_fieldPoint_base_eq z₁
  obtain ⟨W₂, K₂, _, e₂, h₂, x₂, rfl⟩ := exists_fieldPoint_base_eq z₂
  rw [chartPointMap_base_eq p e₁, chartPointMap_base_eq p e₂,
    Stack.class_eq_class_iff_hasCommonExtension] at he
  obtain ⟨r, ⟨ψ₁⟩, ⟨ψ₂⟩⟩ := he
  obtain ⟨j₁, -, ⟨θ₁, hθ₁⟩⟩ := exists_isHomLift_id_of_hom_chartObj p (𝟙 W₁ ≫ h₁) ψ₁
  obtain ⟨j₂, ⟨θ₂, hθ₂⟩, -⟩ := exists_isHomLift_id_of_hom_chartObj p (𝟙 W₂ ≫ h₂) ψ₂
  have hθ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj r.obj)) (θ₁ ≫ θ₂) := by
    have := hθ₁
    have := hθ₂
    have := (inferInstance : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj r.obj) ≫
        𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj r.obj)) (θ₁ ≫ θ₂))
    rwa [Category.comp_id] at this
  obtain ⟨γ, hγ⟩ := exists_actMap_eq_of_isHomLift p (θ₁ ≫ θ₂) hθ
  exact ⟨_, isField_of_iso_spec (fieldPointIso p r),
    (fieldPointIso p r).inv (IsLocalRing.closedPoint r.carrier), _, _, γ, hγ,
    map_comp_id_comp_base_eq e₁ _ _ _ _, map_comp_id_comp_base_eq e₂ _ _ _ _⟩

/-- **Two points of `U` with the same image in `|𝒳|` have the same vanishing coordinates.** -/
theorem X_mem_asIdeal_iff_of_chartPointMap_eq
    {z₁ z₂ : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU)}
    (he : Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) z₁ =
      Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) z₂) (j : ℕ) :
    (MvPolynomial.X j : MvPolynomial ℕ k) ∈ (totalHomeomorph 𝒞 k hU z₁).asIdeal ↔
      (MvPolynomial.X j : MvPolynomial ℕ k) ∈ (totalHomeomorph 𝒞 k hU z₂).asIdeal := by
  obtain ⟨R, hR, x, h₁, h₂, γ, rfl, rfl, rfl⟩ := exists_actMap_eq_of_chartPointMap_eq p he
  rw [X_mem_asIdeal_iff hR, X_mem_asIdeal_iff hR, coord_actMap_eq_zero_iff]

/-- **Saturation.** A set of points of `U` defined by conditions on which coordinates vanish is
the preimage of its image in `|𝒳|`. -/
theorem preimage_image_chartPointMap (A : Set (PrimeSpectrum (MvPolynomial ℕ k)))
    (hA : ∀ z₁ z₂ : PrimeSpectrum (MvPolynomial ℕ k),
      (∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₁.asIdeal ↔
        (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₂.asIdeal) → z₁ ∈ A → z₂ ∈ A) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) ⁻¹'
      (Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) '' (totalHomeomorph 𝒞 k hU ⁻¹' A)) =
      totalHomeomorph 𝒞 k hU ⁻¹' A := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro z ⟨z', hz', he⟩
  exact hA _ _ (X_mem_asIdeal_iff_of_chartPointMap_eq p he) hz'

end Saturation

/-! ### The strata of `U` and their images in `|𝒳|` -/

section StratumPoints

variable (k) in
/-- The stratum `X_a` of the spectrum of `k[x_0, x_1, …]`: it is
`AlgebraicGeometry.PPowerWeighted.stratum` for `a = i` and
`AlgebraicGeometry.PPowerWeighted.stratumInf` for `a = ⊤`. -/
def stratumSet : WithTop ℕ → Set (PrimeSpectrum (MvPolynomial ℕ k))
  | ⊤ => stratumInf k
  | (i : ℕ) => stratum k i

/-- The stratum `X_∞` of the spectrum. -/
@[simp]
theorem stratumSet_top : stratumSet k ⊤ = stratumInf k :=
  rfl

/-- The stratum `X_i` of the spectrum. -/
@[simp]
theorem stratumSet_coe (i : ℕ) : stratumSet k i = stratum k i :=
  rfl

/-- Membership in `X_a` only depends on which coordinates vanish. -/
theorem mem_stratumSet_iff_of_forall_iff {z₁ z₂ : PrimeSpectrum (MvPolynomial ℕ k)}
    (h : ∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₁.asIdeal ↔
      (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₂.asIdeal) (a : WithTop ℕ) :
    z₁ ∈ stratumSet k a ↔ z₂ ∈ stratumSet k a := by
  induction a using WithTop.recTopCoe with
  | top => exact forall_congr' h
  | coe i => exact and_congr (forall₂_congr fun j _ => h j) (not_congr (h i))

/-- **The strata of `U` with values in a field.** If `Γ(W)` is a field, a `W`-point of `U` lies in
the stratum `X_a` exactly when the image of a point of `W` lies in the stratum `X_a` of the
spectrum. -/
theorem mem_stratumSubfunctor_iff_of_isField {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (hW : IsField Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (x : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W) (a : WithTop ℕ) :
    h ∈ (stratumSubfunctor hU a).obj (Opposite.op W) ↔
      totalHomeomorph 𝒞 k hU
        (((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h).base x) ∈
          stratumSet k a := by
  have hz := fun j => (X_mem_asIdeal_iff hW h x j).symm
  have : Nontrivial Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤) :=
    ⟨hW.exists_pair_ne⟩
  have hu : ∀ c : Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤),
      IsUnit c ↔ c ≠ 0 := fun c =>
    ⟨IsUnit.ne_zero, fun hc => IsUnit.of_mul_eq_one _ (hW.mul_inv_cancel hc).choose_spec⟩
  induction a using WithTop.recTopCoe with
  | top => exact (mem_stratumSubfunctor_top_iff h).trans (forall_congr' hz)
  | coe i =>
    exact (mem_stratumSubfunctor_coe_iff i h).trans
      (and_congr (forall₂_congr fun j _ => hz j) ((hu _).trans (not_congr (hz i))))

variable (𝒞 k hU) in
/-- **The strata of `|𝒳|`**: the image of the stratum `X_a` of `U` in the space of points of the
weighted quotient stack `𝒳 = [U/𝐆_m]`. -/
def stratumPoints (a : WithTop ℕ) :
    Set (Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU)) :=
  Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
    (chart.{u, w} 𝒞 k p hU) '' (totalHomeomorph 𝒞 k hU ⁻¹' stratumSet k a)

/-- Every point of `|𝒳|` is the image of a point of `U`. -/
private theorem surjective_chartPointMap_chart :
    Function.Surjective (Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵
      (Space.contains_specULiftZ 𝒞) _ _ (chart.{u, w} 𝒞 k p hU)) :=
  Stack.AlgebraicStacks.surjective_chartPointMap 𝒞 𝒵 _ _ _ _ (isSurjective_chart 𝒞 k p hU)

/-- The preimage in `U` of the stratum `|𝒳_a|` is the stratum `X_a`. -/
theorem preimage_stratumPoints (a : WithTop ℕ) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) ⁻¹' stratumPoints.{u, w} 𝒞 k p hU a =
      totalHomeomorph 𝒞 k hU ⁻¹' stratumSet k a :=
  preimage_image_chartPointMap p _ fun _ _ h hz => (mem_stratumSet_iff_of_forall_iff h a).1 hz

/-- **The strata of `U` are saturated.** A point of `U` maps into the stratum `|𝒳_a|` exactly when
it lies in the stratum `X_a` of `U`. -/
theorem mem_stratumPoints_iff (a : WithTop ℕ) (z : PrimeSpectrum (MvPolynomial ℕ k)) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) ((totalHomeomorph 𝒞 k hU).symm z) ∈
          stratumPoints.{u, w} 𝒞 k p hU a ↔ z ∈ stratumSet k a := by
  rw [← Set.mem_preimage, preimage_stratumPoints, Set.mem_preimage, Homeomorph.apply_symm_apply]

/-- `AlgebraicGeometry.PPowerWeighted.mem_stratumPoints_iff` for the stratum `X_i`. -/
theorem mem_stratumPoints_coe_iff (i : ℕ) (z : PrimeSpectrum (MvPolynomial ℕ k)) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) ((totalHomeomorph 𝒞 k hU).symm z) ∈
          stratumPoints.{u, w} 𝒞 k p hU i ↔ z ∈ stratum k i :=
  mem_stratumPoints_iff p i z

/-- `AlgebraicGeometry.PPowerWeighted.mem_stratumPoints_iff` for the stratum `X_∞`. -/
theorem mem_stratumPoints_top_iff (z : PrimeSpectrum (MvPolynomial ℕ k)) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) ((totalHomeomorph 𝒞 k hU).symm z) ∈
          stratumPoints.{u, w} 𝒞 k p hU ⊤ ↔ z ∈ stratumInf k :=
  mem_stratumPoints_iff p ⊤ z

/-- **The points of `|𝒳|` represented by an object of `𝒳_a`.** A point of `U` maps to the class
of a field-valued point of `𝒳` lying in `𝒳_a` exactly when it lies in `X_a`. -/
theorem exists_pointClass_stratumProperty_iff (a : WithTop ℕ)
    (z : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU)) :
    (∃ q : Stack.FieldValuedPoint 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val,
      Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _ q =
          Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
            (chart.{u, w} 𝒞 k p hU) z ∧
        stratumProperty.{u, w} 𝒞 k p hU a q.obj) ↔ totalHomeomorph 𝒞 k hU z ∈ stratumSet k a := by
  obtain ⟨W, K, _, e, h, x, rfl⟩ := exists_fieldPoint_base_eq z
  rw [chartPointMap_base_eq p e h x]
  constructor
  · rintro ⟨q, hq, hP⟩
    obtain ⟨r, ⟨ψ₁⟩, ⟨ψ₂⟩⟩ := (Stack.class_eq_class_iff_hasCommonExtension _ _ _ _ _ _ _).1 hq
    obtain ⟨j, -, ⟨θ, -⟩⟩ := exists_isHomLift_id_of_hom_chartObj p (𝟙 W ≫ h) ψ₂
    have hj := stratumProperty_of_hom p ψ₁ hP _ _ θ
    rwa [mem_stratumSubfunctor_iff_of_isField (isField_of_iso_spec (fieldPointIso p r)) _
      ((fieldPointIso p r).inv (IsLocalRing.closedPoint r.carrier)),
      map_comp_id_comp_base_eq e _ _ _ x] at hj
  · intro hz
    refine ⟨_, rfl, (chartObj_mem_stratumProperty_iff p a _).2 ?_⟩
    rw [Category.id_comp]
    exact (mem_stratumSubfunctor_iff_of_isField (isField_of_iso_spec e) h x a).2 hz

/-- The points of the full subcategory on a property of the objects of `𝒳` are the classes of
the field-valued points of `𝒳` with that property. -/
theorem range_pointsMap_fullSubcategoryInclusion
    (P : ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj)
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU) P)) :
    Set.range (Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (Stack.fullSubcategoryInclusion (weightedQuotientStack.{u, w} 𝒞 k p hU) P hP)) =
      {ξ | ∃ q : Stack.FieldValuedPoint 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
          (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val,
        Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _ q = ξ ∧ P q.obj} := by
  ext ξ
  constructor
  · rintro ⟨ζ, rfl⟩
    induction ζ using Quotient.inductionOn with
    | h q => exact ⟨_, rfl, q.obj.property⟩
  · rintro ⟨q, rfl, hq⟩
    exact ⟨Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
      { carrier := q.carrier
        base := q.base
        isSpec := q.isSpec
        obj := ⟨q.obj, hq⟩
        «over» := q.over }, rfl⟩

/-- **The points of the substack `𝒳_a` form the stratum `|𝒳_a|`.** -/
theorem range_pointsMap_stratumProperty (a : WithTop ℕ)
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a))) :
    Set.range (Stack.AlgebraicStacks.pointsMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (Stack.fullSubcategoryInclusion (weightedQuotientStack.{u, w} 𝒞 k p hU)
          (stratumProperty.{u, w} 𝒞 k p hU a) hP)) =
      stratumPoints.{u, w} 𝒞 k p hU a := by
  rw [range_pointsMap_fullSubcategoryInclusion]
  ext ξ
  obtain ⟨z, rfl⟩ := surjective_chartPointMap_chart.{u, w} p ξ
  exact (exists_pointClass_stratumProperty_iff p a z).trans
    (Set.ext_iff.1 (preimage_stratumPoints p a) z).symm

end StratumPoints

/-! ### The last stratum is a closed substack -/

section Top

/-- **`𝒳_∞` is a closed substack**: it is cut out by the invariant closed subscheme `X_∞` of
`U`. -/
theorem isClosedSubstack_stratumProperty_top :
    Stack.IsClosedSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU)
      (stratumProperty.{u, w} 𝒞 k p hU ⊤) := by
  rw [stratumProperty_eq]
  exact Stack.isClosedSubstack_invariantSubschemeProperty 𝒞 𝒵 _
    (isChartInvariantSubscheme_stratumSubscheme p ⊤) isClosedImmersion_stratumTopSubobject_arrow
    (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU) (hasRelativeProperty_smooth_chart 𝒞 k p hU)
    (isSurjective_chart 𝒞 k p hU)

/-- `𝒳_∞` is reduced, `X_∞` being reduced over a domain. -/
theorem isReducedStack_stratumProperty_top [IsDomain k]
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU ⊤))) :
    Stack.IsReducedStack 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU ⊤) hP) := by
  revert hP
  rw [stratumProperty_eq]
  intro hP
  have : IsReduced (stratumSubscheme 𝒞 k hU ⊤ : Scheme.{u}) := isReduced_stratumTopSubobject
  exact Stack.isReducedStack_invariantSubschemeProperty 𝒞 𝒵 _
    (isChartInvariantSubscheme_stratumSubscheme p ⊤) (isImmersion_stratumSubscheme_arrow ⊤) hP
    (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU) (hasRelativeProperty_smooth_chart 𝒞 k p hU)
    (hasRelativeProperty_surjective_chart 𝒞 k p hU)

end Top

/-! ### The strata `𝒳_i` are locally closed substacks -/

section Coe

/-- The basic open `D(x_i)` of `U` is the locus where `x_i` does not vanish. -/
theorem range_basicOpenι (i : ℕ) :
    Set.range ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map
        (basicOpenι hU i)).base =
      totalHomeomorph 𝒞 k hU ⁻¹'
        (PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial ℕ k) : Set _) :=
  PrimeSpectrum.localization_away_comap_range (basicOpenRing k i) _

variable (𝒞 k hU) in
/-- The image `Ω_i` in `|𝒳|` of the basic open `D(x_i)` of `U`. -/
def basicOpenPoints (i : ℕ) :
    Set (Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU)) :=
  Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
    (chart.{u, w} 𝒞 k p hU) ''
      Set.range ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map
        (basicOpenι hU i)).base

/-- The basic open `D(x_i)` of `U` is saturated: it is the preimage of its image `Ω_i`. -/
theorem preimage_basicOpenPoints (i : ℕ) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) ⁻¹' basicOpenPoints.{u, w} 𝒞 k p hU i =
      Set.range ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map
        (basicOpenι hU i)).base := by
  rw [basicOpenPoints, range_basicOpenι]
  exact preimage_image_chartPointMap p _ fun _ _ h hz => (not_congr (h i)).1 hz

/-- `Ω_i` is open in `|𝒳|`. -/
theorem isOpen_basicOpenPoints (i : ℕ) :
    @IsOpen _ (Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val) (basicOpenPoints.{u, w} 𝒞 k p hU i) :=
  Stack.isOpen_of_preimage_chartPointMap_eq 𝒞 𝒵 _ (chart.{u, w} 𝒞 k p hU) (basicOpenι hU i) _
    (isSmooth_chart 𝒞 k p hU) (isSurjective_chart 𝒞 k p hU) (isOpenImmersion_basicOpenι i)
    (preimage_basicOpenPoints p i)

variable (𝒞 k hU) in
/-- The open substack of `𝒳` on `Ω_i`, the image of `D(x_i)`. -/
def basicOpenSubstack (i : ℕ) : Stack.OpenSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU) :=
  Stack.pointsWithinOpenSubstack 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
    (isOpen_basicOpenPoints.{u, w} p i)

variable (𝒞 k hU) in
/-- The chart `D(x_i) ⟶ 𝒳_{Ω_i}` of the open substack on `Ω_i`. -/
def basicOpenChart (i : ℕ) :
    Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (basicOpenSiteObject hU i) ⟶
      Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (basicOpenSubstack.{u, w} 𝒞 k p hU i).property
        (basicOpenSubstack.{u, w} 𝒞 k p hU i).isAlgebraic :=
  Stack.openRestrictedChart 𝒞 𝒵 _ (chart.{u, w} 𝒞 k p hU) (basicOpenι hU i) _
    (isOpenImmersion_basicOpenι i) (preimage_basicOpenPoints p i) (isOpen_basicOpenPoints p i)

/-- The basic open `D(x_i)` is a monomorphism into `U`. -/
theorem mono_basicOpenι (i : ℕ) : Mono (basicOpenι hU i) :=
  Stack.mono_of_isOpenImmersion_toScheme_map 𝒞 𝒵 _ _ (isOpenImmersion_basicOpenι i)

/-- A point of `D(x_i)` is a point of the closed subscheme `X_i` of `D(x_i)` exactly when it is a
point of the stratum `X_i` of `U`. -/
theorem mem_subschemePoints_stratumSubobject_iff_comp (i : ℕ)
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (h : W ⟶ basicOpenSiteObject hU i) :
    h ∈ (Space.subschemePoints 𝒞 𝒵 _ (stratumSubobject hU i)).obj (Opposite.op W) ↔
      h ≫ basicOpenι hU i ∈ (stratumSubfunctor hU i).obj (Opposite.op W) := by
  rw [mem_stratumSubfunctor_coe_iff_exists]
  constructor
  · exact fun hh => ⟨h, rfl, hh⟩
  · rintro ⟨h', he, hm⟩
    have := mono_basicOpenι (hU := hU) i
    rwa [← cancel_mono (basicOpenι hU i) |>.1 he]

/-- **`X_i` is an invariant subscheme of the chart `D(x_i) ⟶ 𝒳_{Ω_i}`.** -/
theorem isChartInvariantSubscheme_stratumSubobject (i : ℕ) :
    Stack.IsChartInvariantSubscheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (basicOpenChart.{u, w} 𝒞 k p hU i) (stratumSubobject hU i) := by
  intro W h h' θ hθ hh
  rw [mem_subschemePoints_stratumSubobject_iff_comp] at hh ⊢
  have hθ' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ.hom := by
    have := hθ
    exact IsHomLift.of_fac' (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p (𝟙 W) θ.hom
      (IsHomLift.domain_eq (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (basicOpenSubstack.{u, w} 𝒞 k p hU i).property).p (𝟙 W) θ)
      (IsHomLift.codomain_eq (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (basicOpenSubstack.{u, w} 𝒞 k p hU i).property).p (𝟙 W) θ)
      (IsHomLift.fac' (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (basicOpenSubstack.{u, w} 𝒞 k p hU i).property).p (𝟙 W) θ)
  obtain ⟨γ, hγ⟩ := exists_actMap_eq_of_isHomLift.{u, w} p (h := h ≫ basicOpenι hU i)
    (h' := h' ≫ basicOpenι hU i) θ.hom hθ'
  rw [← hγ]
  exact (actMap_mem_stratumSubfunctor_iff p i γ _).2 hh

variable (𝒞 k hU) in
/-- The closed substack `X_i / 𝐆_m` of the open substack `𝒳_{Ω_i}`, cut out by the invariant
closed subscheme `X_i` of the chart `D(x_i)`. -/
def stratumOpenProperty (i : ℕ) :
    ObjectProperty (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
      (basicOpenSubstack.{u, w} 𝒞 k p hU i).property
      (basicOpenSubstack.{u, w} 𝒞 k p hU i).isAlgebraic).val.val.obj :=
  Stack.invariantSubschemeProperty 𝒞 𝒵 _ (basicOpenChart.{u, w} 𝒞 k p hU i)
    (stratumSubobject hU i)

/-- `stratumProperty` at `i` is contained in `Ω_i`. -/
theorem pointsWithin_of_stratumProperty_coe (i : ℕ)
    {x : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    (hx : stratumProperty.{u, w} 𝒞 k p hU i x) :
    (basicOpenSubstack.{u, w} 𝒞 k p hU i).property x := by
  intro q φ
  have hq : Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _ q ∈
      stratumPoints.{u, w} 𝒞 k p hU i := by
    obtain ⟨z, hz⟩ := surjective_chartPointMap_chart.{u, w} p
      (Stack.pointClass 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _ q)
    rw [← hz]
    exact (Set.ext_iff.1 (preimage_stratumPoints p (i : WithTop ℕ)) z).2
      ((exists_pointClass_stratumProperty_iff p i z).1
        ⟨q, hz.symm, stratumProperty_of_hom p φ hx⟩)
  obtain ⟨z, hz, he⟩ := hq
  refine ⟨z, ?_, he⟩
  rw [range_basicOpenι]
  exact hz.2

/-- **`𝒳_i` is a closed substack of the open substack on `Ω_i`.** -/
theorem stratumProperty_coe_eq (i : ℕ) :
    stratumProperty.{u, w} 𝒞 k p hU i =
      Stack.openClosedProperty (basicOpenSubstack.{u, w} 𝒞 k p hU i)
        (stratumOpenProperty.{u, w} 𝒞 k p hU i) := by
  funext x
  apply propext
  constructor
  · intro hx
    refine ⟨pointsWithin_of_stratumProperty_coe p i hx, fun W h ψ => ?_⟩
    rw [mem_subschemePoints_stratumSubobject_iff_comp]
    exact hx W _ ψ.hom
  · rintro ⟨hx, hQ⟩ W h ψ
    obtain ⟨g, rfl⟩ := (Stack.pointsWithin_obj_iff_exists_comp 𝒞 𝒵 _ (chart.{u, w} 𝒞 k p hU)
      (basicOpenι hU i) _ (isOpenImmersion_basicOpenι i) (preimage_basicOpenPoints p i) W h).1
      (Stack.pointsWithin_of_hom _ _ ψ hx)
    exact (mem_subschemePoints_stratumSubobject_iff_comp i g).1 (hQ W g (ObjectProperty.homMk ψ))

/-- The chart `D(x_i) ⟶ 𝒳_{Ω_i}` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_basicOpenChart (i : ℕ) :
    Stack.IsRepresentableByAlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (basicOpenChart.{u, w} 𝒞 k p hU i).hom.hom :=
  Stack.isRepresentableByAlgebraicSpaces_openRestrictedChart 𝒞 𝒵 _ _ _ _ _ _ _
    (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU)

/-- The chart `D(x_i) ⟶ 𝒳_{Ω_i}` inherits the relative properties of the chart `U ⟶ 𝒳` which are
stable under base change and fppf local on the target. -/
theorem hasRelativeProperty_basicOpenChart (i : ℕ)
    (Q : MorphismProperty (AlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)))
    [Q.IsStableUnderBaseChange]
    [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))]
    (hQ : Stack.HasRelativeProperty.{u, u, u + 1, u} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) Q
      (chart.{u, w} 𝒞 k p hU).hom (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU)) :
    Stack.HasRelativeProperty.{u, u, u + 1, u} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) Q
      (basicOpenChart.{u, w} 𝒞 k p hU i).hom
      (isRepresentableByAlgebraicSpaces_basicOpenChart p i) :=
  have : (Stack.pointsWithin (weightedQuotientStack.{u, w} 𝒞 k p hU)
      (basicOpenPoints.{u, w} 𝒞 k p hU i)).IsClosedUnderIsomorphisms :=
    ⟨fun e hx => Stack.pointsWithin_of_hom _ _ e.inv hx⟩
  Stack.hasRelativeProperty_restrictedChart 𝒞 𝒵 _ (chart.{u, w} 𝒞 k p hU) _ _ (basicOpenι hU i)
    (Stack.pointsWithin_obj_iff_exists_comp 𝒞 𝒵 _ (chart.{u, w} 𝒞 k p hU) (basicOpenι hU i) _
      (isOpenImmersion_basicOpenι i) (preimage_basicOpenPoints p i))
    (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU) (mono_basicOpenι i) Q hQ

/-- The chart `D(x_i) ⟶ 𝒳_{Ω_i}` is surjective. -/
theorem isSurjective_basicOpenChart (i : ℕ) :
    Stack.IsSurjective 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (basicOpenChart.{u, w} 𝒞 k p hU i) :=
  (Stack.isSmooth_and_isSurjective_openRestrictedChart 𝒞 𝒵 _ _ _ _ _ _ _
    (isRepresentableByAlgebraicSpaces_chart 𝒞 k p hU) (hasRelativeProperty_smooth_chart 𝒞 k p hU)
    (hasRelativeProperty_surjective_chart 𝒞 k p hU)).2

/-- `X_i / 𝐆_m` is a closed substack of `𝒳_{Ω_i}`. -/
theorem isClosedSubstack_stratumOpenProperty (i : ℕ) :
    Stack.IsClosedSubstack _ (stratumOpenProperty.{u, w} 𝒞 k p hU i) :=
  Stack.isClosedSubstack_invariantSubschemeProperty 𝒞 𝒵 _
    (isChartInvariantSubscheme_stratumSubobject p i) (isClosedImmersion_stratumSubobject_arrow i)
    (isRepresentableByAlgebraicSpaces_basicOpenChart p i)
    (hasRelativeProperty_basicOpenChart p i _ (hasRelativeProperty_smooth_chart 𝒞 k p hU))
    (isSurjective_basicOpenChart p i)

/-- **`𝒳_i` is a locally closed substack of `𝒳`**: it is the closed substack `X_i / 𝐆_m` of the
open substack on `Ω_i`. -/
theorem isLocallyClosedSubstack_stratumProperty_coe (i : ℕ) :
    Stack.IsLocallyClosedSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU)
      (stratumProperty.{u, w} 𝒞 k p hU i) := by
  rw [stratumProperty_coe_eq]
  exact Stack.isLocallyClosedSubstack_openClosedProperty _ _
    (isClosedSubstack_stratumOpenProperty p i)

/-- `𝒳_i` is reduced, `X_i` being reduced over a domain. -/
theorem isReducedStack_stratumProperty_coe [IsDomain k] (i : ℕ)
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU i))) :
    Stack.IsReducedStack 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU i) hP) := by
  revert hP
  rw [stratumProperty_coe_eq]
  intro hP
  obtain ⟨-, hQ, -⟩ := isClosedSubstack_stratumOpenProperty.{u, w} (𝒞 := 𝒞) (k := k) (hU := hU) p i
  have : IsReduced (stratumSubobject hU i : Scheme.{u}) := isReduced_stratumSubobject (hU := hU) i
  have := isClosedImmersion_stratumSubobject_arrow (hU := hU) i
  exact Stack.isReducedStack_openClosedProperty _ _ hQ hP
    (Stack.isReducedStack_invariantSubschemeProperty 𝒞 𝒵 _
      (isChartInvariantSubscheme_stratumSubobject p i) inferInstance hQ
      (isRepresentableByAlgebraicSpaces_basicOpenChart p i)
      (hasRelativeProperty_basicOpenChart p i _ (hasRelativeProperty_smooth_chart 𝒞 k p hU))
      (hasRelativeProperty_basicOpenChart p i _ (hasRelativeProperty_surjective_chart 𝒞 k p hU)))

end Coe

/-! ### The substacks `𝒳_a` -/

section Substacks

/-- **Stacks 06RE: each `𝒳_a` is a locally closed substack of `𝒳`.** For `a = i` it is the closed
substack `X_i / 𝐆_m` of the open substack on the image of `D(x_i)`; `𝒳_∞` is even closed. -/
theorem isLocallyClosedSubstack_stratumProperty (a : WithTop ℕ) :
    Stack.IsLocallyClosedSubstack (weightedQuotientStack.{u, w} 𝒞 k p hU)
      (stratumProperty.{u, w} 𝒞 k p hU a) := by
  induction a using WithTop.recTopCoe with
  | top =>
    obtain ⟨h₁, hP, h₂⟩ := isClosedSubstack_stratumProperty_top.{u, w} (𝒞 := 𝒞) (k := k)
      (hU := hU) p
    exact ⟨h₁, hP, h₂.1, fun V y hy F hF he =>
      Space.isImmersion_of_isClosedImmersion 𝒞 𝒵 _ (h₂.2 V y hy F hF he)⟩
  | coe i => exact isLocallyClosedSubstack_stratumProperty_coe p i

/-- **Stacks 06RE: each `𝒳_a` is reduced** over a domain, in particular over a field. -/
theorem isReducedStack_stratumProperty [IsDomain k] (a : WithTop ℕ)
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a))) :
    Stack.IsReducedStack 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a) hP) := by
  induction a using WithTop.recTopCoe with
  | top => exact isReducedStack_stratumProperty_top p hP
  | coe i => exact isReducedStack_stratumProperty_coe p i hP

end Substacks

/-! ### The stratification of `|𝒳|` -/

section Stratification

variable (k) in
/-- The closed subset `V(x_j : j < a)` of the spectrum, containing the stratum `X_a`. -/
def stratumClosure (a : WithTop ℕ) : Set (PrimeSpectrum (MvPolynomial ℕ k)) :=
  PrimeSpectrum.zeroLocus (MvPolynomial.X '' {j : ℕ | (j : WithTop ℕ) < a})

/-- Membership in `V(x_j : j < a)`. -/
theorem mem_stratumClosure_iff {a : WithTop ℕ} {z : PrimeSpectrum (MvPolynomial ℕ k)} :
    z ∈ stratumClosure k a ↔
      ∀ j : ℕ, (j : WithTop ℕ) < a → (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z.asIdeal := by
  rw [stratumClosure, PrimeSpectrum.mem_zeroLocus, Set.image_subset_iff]
  rfl

/-- Membership in `V(x_j : j < a)` only depends on which coordinates vanish. -/
theorem mem_stratumClosure_of_forall_iff {z₁ z₂ : PrimeSpectrum (MvPolynomial ℕ k)}
    (h : ∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₁.asIdeal ↔
      (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₂.asIdeal) {a : WithTop ℕ}
    (hz : z₁ ∈ stratumClosure k a) : z₂ ∈ stratumClosure k a :=
  mem_stratumClosure_iff.2 fun j hj => (h j).1 (mem_stratumClosure_iff.1 hz j hj)

/-- `V(x_j : j < a)` is closed. -/
theorem isClosed_stratumClosure (a : WithTop ℕ) : IsClosed (stratumClosure k a) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- The stratum `X_a` lies in `V(x_j : j < a)`. -/
theorem stratumSet_subset_stratumClosure (a : WithTop ℕ) :
    stratumSet k a ⊆ stratumClosure k a := by
  induction a using WithTop.recTopCoe with
  | top => exact fun z hz => mem_stratumClosure_iff.2 fun j _ => hz j
  | coe i => exact fun z hz => mem_stratumClosure_iff.2 fun j hj => hz.1 j (WithTop.coe_lt_coe.1 hj)

/-- Every point of the spectrum lies in one of the strata. -/
theorem exists_mem_stratumSet (z : PrimeSpectrum (MvPolynomial ℕ k)) :
    ∃ a, z ∈ stratumSet k a := by
  have hz : z ∈ (⋃ i, stratum k i) ∪ stratumInf k := by
    rw [iUnion_stratum_union_stratumInf]
    trivial
  rcases hz with hz | hz
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    exact ⟨i, hi⟩
  · exact ⟨⊤, hz⟩

/-- The closed set `V(x_j : j < a)` is the union of the strata `X_b` with `a ≤ b`. -/
theorem exists_mem_stratumSet_of_mem_stratumClosure {a : WithTop ℕ}
    {z : PrimeSpectrum (MvPolynomial ℕ k)} (hz : z ∈ stratumClosure k a) :
    ∃ b, a ≤ b ∧ z ∈ stratumSet k b := by
  obtain ⟨b, hb⟩ := exists_mem_stratumSet z
  refine ⟨b, le_of_not_gt fun hba => ?_, hb⟩
  induction b using WithTop.recTopCoe with
  | top => exact not_top_lt hba
  | coe m => exact hb.2 (mem_stratumClosure_iff.1 hz m hba)

/-- Distinct strata of the spectrum are disjoint. -/
theorem disjoint_stratumSet {a b : WithTop ℕ} (hab : a ≠ b) :
    Disjoint (stratumSet k a) (stratumSet k b) := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd rfl hab
    | coe j => exact (disjoint_stratum_stratumInf k j).symm
  | coe i =>
    induction b using WithTop.recTopCoe with
    | top => exact disjoint_stratum_stratumInf k i
    | coe j => exact disjoint_stratum k fun h => hab (h ▸ rfl)

/-- Over a field, every stratum of the spectrum is nonempty. -/
theorem stratumSet_nonempty {K : Type u} [Field K] (a : WithTop ℕ) :
    (stratumSet K a).Nonempty := by
  induction a using WithTop.recTopCoe with
  | top =>
    exact ⟨⟨RingHom.ker (MvPolynomial.eval (0 : ℕ → K)), RingHom.ker_isPrime _⟩,
      (mem_stratumInf_ker_iff K _).2 fun j => by simp⟩
  | coe i =>
    exact ⟨⟨RingHom.ker (MvPolynomial.eval (basisPoint K i)), RingHom.ker_isPrime _⟩,
      (mem_stratum_ker_iff K _ i).2 (by
        simpa only [MvPolynomial.eval_X] using isPointInStratum_basisPoint K i)⟩

/-- A point of `U` maps into the image of a set defined by conditions on which coordinates vanish
exactly when it lies in that set. -/
theorem mem_image_chartPointMap_iff (A : Set (PrimeSpectrum (MvPolynomial ℕ k)))
    (hA : ∀ z₁ z₂ : PrimeSpectrum (MvPolynomial ℕ k),
      (∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₁.asIdeal ↔
        (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₂.asIdeal) → z₁ ∈ A → z₂ ∈ A)
    (z : (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU)) :
    Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) z ∈
      Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) '' (totalHomeomorph 𝒞 k hU ⁻¹' A) ↔
      totalHomeomorph 𝒞 k hU z ∈ A :=
  Set.ext_iff.1 (preimage_image_chartPointMap p A hA) z

/-- The image in `|𝒳|` of an open subset of `U` is open. -/
theorem isOpen_image_chartPointMap {A : Set (PrimeSpectrum (MvPolynomial ℕ k))} (hA : IsOpen A) :
    @IsOpen _ (Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val)
      (Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) '' (totalHomeomorph 𝒞 k hU ⁻¹' A)) :=
  Stack.AlgebraicStacks.isOpenMap_chartPointMap 𝒞 𝒵 _ _ _ _ (isSmooth_chart 𝒞 k p hU) _
    (hA.preimage (totalHomeomorph 𝒞 k hU).continuous)

/-- The image in `|𝒳|` of a closed subset of `U` defined by conditions on which coordinates vanish
is closed: its complement is the image of the complement. -/
theorem isClosed_image_chartPointMap {A : Set (PrimeSpectrum (MvPolynomial ℕ k))}
    (hA : ∀ z₁ z₂ : PrimeSpectrum (MvPolynomial ℕ k),
      (∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₁.asIdeal ↔
        (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₂.asIdeal) → z₁ ∈ A → z₂ ∈ A)
    (hc : IsClosed A) :
    @IsClosed _ (Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val)
      (Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) '' (totalHomeomorph 𝒞 k hU ⁻¹' A)) := by
  let := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val
  have he : (Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) '' (totalHomeomorph 𝒞 k hU ⁻¹' A))ᶜ =
      Stack.AlgebraicStacks.chartPointMap 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) _ _
        (chart.{u, w} 𝒞 k p hU) '' (totalHomeomorph 𝒞 k hU ⁻¹' Aᶜ) := by
    ext ξ
    obtain ⟨z, rfl⟩ := surjective_chartPointMap_chart.{u, w} p ξ
    rw [Set.mem_compl_iff, mem_image_chartPointMap_iff p A hA,
      mem_image_chartPointMap_iff p Aᶜ fun z₁ z₂ h hz hz₂ =>
        hz (hA z₂ z₁ (fun j => (h j).symm) hz₂)]
    rfl
  rw [← isOpen_compl_iff, he]
  exact isOpen_image_chartPointMap p hc.isOpen_compl

/-- Distinct strata of `|𝒳|` are disjoint. -/
theorem disjoint_stratumPoints {a b : WithTop ℕ} (hab : a ≠ b) :
    Disjoint (stratumPoints.{u, w} 𝒞 k p hU a) (stratumPoints.{u, w} 𝒞 k p hU b) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ hb
  exact Set.disjoint_left.1 (disjoint_stratumSet hab) hz
    ((Set.ext_iff.1 (preimage_stratumPoints p b) z).1 hb)

/-- The strata of `|𝒳|` cover `|𝒳|`. -/
theorem iUnion_stratumPoints : ⋃ a, stratumPoints.{u, w} 𝒞 k p hU a = Set.univ := by
  refine Set.eq_univ_of_forall fun ξ => ?_
  obtain ⟨z, rfl⟩ := surjective_chartPointMap_chart.{u, w} p ξ
  obtain ⟨a, ha⟩ := exists_mem_stratumSet (totalHomeomorph 𝒞 k hU z)
  exact Set.mem_iUnion.2 ⟨a, z, ha, rfl⟩

/-- **The closure of a stratum of `|𝒳|` lies in the union of the later strata**: the closure of
`|𝒳_a|` is contained in the union of the `|𝒳_b|` with `a ≤ b`, the image of the closed set
`V(x_j : j < a)`. -/
theorem closure_stratumPoints_subset (a : WithTop ℕ) :
    letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val
    closure (stratumPoints.{u, w} 𝒞 k p hU a) ⊆
      ⋃ (b : WithTop ℕ) (_ : a ≤ b), stratumPoints.{u, w} 𝒞 k p hU b := by
  let := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val
  refine (closure_minimal (Set.image_mono (Set.preimage_mono (stratumSet_subset_stratumClosure a)))
    (isClosed_image_chartPointMap p (fun _ _ h hz => mem_stratumClosure_of_forall_iff h hz)
      (isClosed_stratumClosure a))).trans ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨b, hab, hb⟩ := exists_mem_stratumSet_of_mem_stratumClosure hz
  exact Set.mem_iUnion₂.2 ⟨b, hab, z, hb, rfl⟩

/-- **Each stratum of `|𝒳|` is locally closed**: `|𝒳_i|` is the intersection of the image of
`D(x_i)`, which is open, with the image of `V(x_j : j < i)`, which is closed, and `|𝒳_∞|` is
closed. -/
theorem isLocallyClosed_stratumPoints (a : WithTop ℕ) :
    letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val
    IsLocallyClosed (stratumPoints.{u, w} 𝒞 k p hU a) := by
  let := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val
  have hC : ∀ z₁ z₂ : PrimeSpectrum (MvPolynomial ℕ k),
      (∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₁.asIdeal ↔
        (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₂.asIdeal) →
        z₁ ∈ stratumClosure k a → z₂ ∈ stratumClosure k a :=
    fun _ _ h hz => mem_stratumClosure_of_forall_iff h hz
  have hCc := isClosed_image_chartPointMap.{u, w} (𝒞 := 𝒞) (hU := hU) p hC
    (isClosed_stratumClosure a)
  induction a using WithTop.recTopCoe with
  | top =>
    have he : stratumSet k ⊤ = stratumClosure k ⊤ := by
      ext z
      rw [mem_stratumClosure_iff]
      exact ⟨fun h j _ => h j, fun h j => h j (WithTop.coe_lt_top j)⟩
    refine IsClosed.isLocallyClosed ?_
    rw [stratumPoints, he]
    exact hCc
  | coe i =>
    have hD : ∀ z₁ z₂ : PrimeSpectrum (MvPolynomial ℕ k),
        (∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₁.asIdeal ↔
          (MvPolynomial.X j : MvPolynomial ℕ k) ∈ z₂.asIdeal) →
          z₁ ∈ (PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial ℕ k) : Set _) →
          z₂ ∈ (PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial ℕ k) : Set _) :=
      fun z₁ z₂ h hz => (not_congr (h i)).1 hz
    refine ⟨_, _, isOpen_image_chartPointMap p
      (PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial ℕ k)).isOpen, hCc, ?_⟩
    ext ξ
    obtain ⟨z, rfl⟩ := surjective_chartPointMap_chart.{u, w} p ξ
    rw [Set.mem_inter_iff, stratumPoints,
      mem_image_chartPointMap_iff p _ (fun _ _ h hz => (mem_stratumSet_iff_of_forall_iff h _).1 hz),
      mem_image_chartPointMap_iff p _ hD, mem_image_chartPointMap_iff p _ hC,
      mem_stratumClosure_iff]
    exact ⟨fun hz => ⟨hz.2, fun j hj => hz.1 j (WithTop.coe_lt_coe.1 hj)⟩,
      fun hz => ⟨fun j hj => hz.2 j (WithTop.coe_lt_coe.2 hj), hz.1⟩⟩

/-- Over a field, every stratum of `|𝒳|` is nonempty. -/
theorem stratumPoints_nonempty {K : Type u} [Field K]
    (hK : 𝒞.Contains (Spec (.of (MvPolynomial ℕ K)))) (a : WithTop ℕ) :
    (stratumPoints.{u, w} 𝒞 K p hK a).Nonempty := by
  obtain ⟨z, hz⟩ := stratumSet_nonempty (K := K) a
  exact ⟨_, (mem_stratumPoints_iff p a z).2 hz⟩

/-- Over a field, the strata of `|𝒳|` are pairwise distinct. -/
theorem stratumPoints_injective {K : Type u} [Field K]
    (hK : 𝒞.Contains (Spec (.of (MvPolynomial ℕ K)))) :
    Function.Injective (stratumPoints.{u, w} 𝒞 K p hK) := by
  intro a b hab
  by_contra hne
  obtain ⟨ξ, hξ⟩ := stratumPoints_nonempty.{u, w} p hK a
  exact Set.disjoint_left.1 (disjoint_stratumPoints p hne) hξ (hab ▸ hξ)

variable (𝒞 k hU) in
/-- **Stacks 06RE: the stratification of `|𝒳|`.** The strata `|𝒳_a|`, indexed by `a : WithTop ℕ`
in the opposite order, form a stratification of the space of points of `𝒳 = [U/𝐆_m]`: they are
disjoint, cover `|𝒳|`, and the closure of `|𝒳_i|` lies in `|𝒳_i| ∪ |𝒳_{i+1}| ∪ … ∪ |𝒳_∞|`. -/
def stratification :
    letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val
    Stratification (Stack.AlgebraicStacks.points 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU)) (WithTop ℕ)ᵒᵈ :=
  letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val
  { strata := fun a => stratumPoints.{u, w} 𝒞 k p hU (OrderDual.ofDual a)
    pairwiseDisjoint := fun _ _ hab => disjoint_stratumPoints p fun h => hab h
    iUnion_eq_univ :=
      (OrderDual.ofDual.surjective.iUnion_comp (stratumPoints.{u, w} 𝒞 k p hU)).trans
        (iUnion_stratumPoints p)
    closure_subset_iUnion_le := fun j => (closure_stratumPoints_subset p (OrderDual.ofDual j)).trans
      fun ξ hξ => by
        obtain ⟨b, hab, hb⟩ := Set.mem_iUnion₂.1 hξ
        exact Set.mem_iUnion₂.2 ⟨OrderDual.toDual b, hab, hb⟩ }

/-- The strata of `AlgebraicGeometry.PPowerWeighted.stratification` are the `|𝒳_a|`. -/
theorem stratification_strata (a : WithTop ℕ) :
    letI := Stack.pointTopology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val
    (stratification.{u, w} 𝒞 k p hU).strata (OrderDual.toDual a) =
      stratumPoints.{u, w} 𝒞 k p hU a :=
  rfl

end Stratification

end AlgebraicGeometry.PPowerWeighted

end
