module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.BaseChangeChartGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.EtaleResidueFieldComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldPointReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.MinimalPrimeResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChartStalk
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic

/-!
# Readings at a generic point of the base-change chart of a prime divisor

Let `X` be an algebraic space, `Z ⊂ X` a prime divisor, `V` an étale chart of `X` and
`W' = V ×_X Z` the base-change chart of `Z`.  The key formula of Stacks 0EQV reads orders along
`Z` at a point `y` of `W'` through the chart readings `R(Z) → Q(𝒪_{W', y})`
(`AlgebraicGeometry.Space.chartPointRationalFunctionMap`) and `𝒦_Z(W') → Q(𝒪_{W', y})`
(`AlgebraicGeometry.Space.chartPointMeromorphicMap`), while the restriction to `Z` reads the same
functions in the residue field `κ(q')` of a point `q'` of `W'` over the generic point of `Z`.
This file connects the two: for `q' ⤳ y`, with the prime of `q'` in `𝒪_{W', y}` minimal
and `𝒪_{W', q'}` a field, the chart readings followed by
`AlgebraicGeometry.Scheme.totalFractionToResidueFieldOfSpecializes` are the readings at `q'`.

## Main definitions

* `AlgebraicGeometry.Scheme.totalFractionRingToResidueField`: the reading `Q(Γ(T, 𝒪_T)) → κ(t)`
  at a point of an affine scheme whose local ring is a field.
* `AlgebraicGeometry.Space.chartPointResidueReading`: the reading `𝒦_Y(W) → κ(w)` of meromorphic
  functions on an affine chart at such a point.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartSectionCoefficient` and
  `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartSectionReading`: the coefficient in
  `𝒦_Z(W')` of a meromorphic section of `ℒ|_Z` against the restriction of a free generator of
  `ℒ` over `V`, and its value in `κ(q')`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isField_stalk_baseChangeChart`: `𝒪_{W', q'}` is a field
  for `q'` over the generic point of `Z`.
* `AlgebraicGeometry.Space.evalRingHom_eq_rationalFunctionsToTotalFractionRing`: evaluation at a
  field point through `Spec Q(Γ(U, 𝒪_U))`.
* In the namespace `AlgebraicGeometry.Space`,
  `PrimeDivisor.totalFractionToResidueFieldOfSpecializes_chartPointRationalFunctionMap` and
  `totalFractionToResidueFieldOfSpecializes_chartPointMeromorphicMap`: the chart readings
  followed by `totalFractionToResidueFieldOfSpecializes` are the readings at `q'`, for rational
  functions and for meromorphic functions.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} [IsAffine T] (t : T) (ht : IsField (T.presheaf.stalk t))

include ht in
/-- At a point whose local ring is a field, a nonzerodivisor of the global sections has a nonzero,
hence invertible, residue. -/
theorem isUnit_residue_germ_of_mem_nonZeroDivisors {a : Γ(T, ⊤)} (ha : a ∈ (Γ(T, ⊤))⁰) :
    IsUnit (T.residue t (T.presheaf.germ ⊤ t trivial a)) := by
  refine isUnit_iff_ne_zero.mpr fun h0 ↦ ?_
  have hb := (bijective_residue_of_isField ht).1 (h0.trans (map_zero (T.residue t).hom).symm)
  exact nonZeroDivisors.ne_zero (T.nonZeroDivisors_le_comap_germ_top t ha) hb

/-- **The reading `Q(Γ(T, 𝒪_T)) → κ(t)` at a point whose local ring is a field**, induced by the
germ followed by the residue map. -/
def totalFractionRingToResidueField : FractionRing Γ(T, ⊤) →+* T.residueField t :=
  IsLocalization.lift (M := (Γ(T, ⊤))⁰)
    (g := (T.residue t).hom.comp (T.presheaf.germ ⊤ t trivial).hom)
    fun a ↦ isUnit_residue_germ_of_mem_nonZeroDivisors t ht a.2

/-- The reading `Q(Γ(T, 𝒪_T)) → κ(t)` on a global function is its residue at `t`. -/
theorem totalFractionRingToResidueField_algebraMap (a : Γ(T, ⊤)) :
    totalFractionRingToResidueField t ht (algebraMap _ _ a) =
      T.residue t (T.presheaf.germ ⊤ t trivial a) :=
  IsLocalization.lift_eq _ _

/-- **`Spec κ(t) → T` factors through `Spec Q(Γ(T, 𝒪_T))`** at a point whose local ring is a
field, by the reading `Q(Γ(T, 𝒪_T)) → κ(t)`. -/
theorem fromSpecResidueField_eq_SpecMap_comp_fromSpecTotalFractionRing :
    T.fromSpecResidueField t =
      Spec.map (CommRingCat.ofHom (totalFractionRingToResidueField t ht)) ≫
        T.fromSpecTotalFractionRing := by
  have h : CommRingCat.ofHom (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))) ≫
      CommRingCat.ofHom (totalFractionRingToResidueField t ht) =
      T.presheaf.germ ⊤ t trivial ≫ T.residue t := by
    ext a
    exact totalFractionRingToResidueField_algebraMap t ht a
  rw [fromSpecTotalFractionRing, ← Category.assoc, ← Spec.map_comp, h, Spec.map_comp,
    Category.assoc, fromSpecResidueField,
    ← (isAffineOpen_top T).fromSpecStalk_eq_fromSpecStalk (x := t) trivial]
  delta IsAffineOpen.fromSpecStalk
  rw [IsAffineOpen.fromSpec_top]

/-- A ring map `K → Q(𝒪_{T, y})` and a ring map `K → κ(z)` from a localization of `R` at its
nonzerodivisors, which on `R` are the germ at `y` and the residue of the germ at `z`, are
related by the reading `Q(𝒪_{T, y}) → κ(z)`. -/
private theorem totalFractionToResidueFieldOfSpecializes_apply_of_algebraMap
    {T : Scheme.{u}} {y z : T} (h : z ⤳ y) (hz : IsField (T.presheaf.stalk z))
    {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsLocalization R⁰ K]
    (g : R →+* Γ(T, ⊤)) (F : K →+* FractionRing (T.presheaf.stalk y)) (G : K →+* T.residueField z)
    (hF : ∀ a, F (algebraMap R K a) = algebraMap _ _ (T.presheaf.germ ⊤ y trivial (g a)))
    (hG : ∀ a, G (algebraMap R K a) = T.residue z (T.presheaf.germ ⊤ z trivial (g a)))
    (c : K) :
    totalFractionToResidueFieldOfSpecializes h hz (FractionRing (T.presheaf.stalk y)) (F c) =
      G c := by
  have key : (totalFractionToResidueFieldOfSpecializes h hz
      (FractionRing (T.presheaf.stalk y))).comp F = G := by
    refine IsLocalization.ringHom_ext R⁰ (RingHom.ext fun a ↦ ?_)
    change totalFractionToResidueFieldOfSpecializes h hz _ (F (algebraMap R K a)) =
      G (algebraMap R K a)
    rw [hF, hG, totalFractionToResidueFieldOfSpecializes_algebraMap]
    exact congrArg (T.residue z).hom
      (ConcreteCategory.congr_hom (T.presheaf.germ_stalkSpecializes (U := ⊤) trivial h) (g a))
  exact RingHom.congr_fun key c

/-- **The reading at a generization agrees with the reading at the generic point**: for `z ⤳ y`
with `𝒪_{T, z}` a field, `Q(Γ(T, 𝒪_T)) → Q(𝒪_{T, y}) → κ(z)` is the reading at `z`. -/
theorem totalFractionToResidueFieldOfSpecializes_totalFractionRingToStalkFractionRing
    {y : T} (h : t ⤳ y) (f : FractionRing Γ(T, ⊤)) :
    totalFractionToResidueFieldOfSpecializes h ht (FractionRing (T.presheaf.stalk y))
        (T.totalFractionRingToStalkFractionRing y f) =
      totalFractionRingToResidueField t ht f := by
  exact totalFractionToResidueFieldOfSpecializes_apply_of_algebraMap h ht (RingHom.id _) _ _
    (fun a ↦ totalFractionRingToStalkFractionRing_algebraMap T y a)
    (fun a ↦ totalFractionRingToResidueField_algebraMap t ht a) f

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Evaluation at a field point factoring through `Spec Q(Γ(U, 𝒪_U))`.**  If a field-valued
representative `p` of the generic point of an integral algebraic space `Y` factors through the
spectrum of the total ring of fractions of an affine étale chart `U` by a morphism which is
`Spec ρ` on schemes, then evaluating a rational function at `p` is `ρ` of its image in
`Q(Γ(U, 𝒪_U))` (Stacks 0ENK). -/
theorem evalRingHom_eq_rationalFunctionsToTotalFractionRing
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hInt : IsIntegralSpace B S hS Y) (U : BigFppfOver B S hS) [IsAffine U.left.1]
    [IsReduced U.left.1] [IsLocallyNoetherian U.left.1] (c : yoneda.obj U ⟶ Y)
    (hc : IsEtale B S hS c) (p : FieldValuedPoint B S hS Y)
    (hp : p.class B S hS Y = genericPoint B S hS hY hInt)
    (ρ : FractionRing Γ(U.left.1, ⊤) →+* p.carrier)
    (g : p.siteObject B S hS Y ⟶ totalFractionObject B S hS U)
    (hgS : (BigFppfOver.toScheme B S hS).map g = Spec.map (CommRingCat.ofHom ρ))
    (hg : yoneda.map (g ≫ totalFractionObjectMap B S hS U) ≫ c = fieldMorphism B S hS Y p)
    (x : rationalFunctions B S hS hY) :
    evalRingHom B S hS hY hInt p hp x =
      ρ (rationalFunctionsToTotalFractionRing B S hS hY U c hc x) := by
  obtain ⟨f, rfl⟩ := RationalMap.exists_rep B S hS x
  set hm := factorsThroughDenseOpens_totalFractionObject B S hS hY U c hc
  set j := denseOpenLift B S hS hY hm f.dense_open_domain
  have hj : yoneda.map g ≫ j.1 ≫ f.domain.ι = fieldMorphism B S hS Y p := by
    rw [j.2, ← Category.assoc, ← yoneda.map_comp]
    exact hg
  have h2 : rationalFunctionsToTotalFractionRing B S hS hY U c hc (f.toRationalMap B S hS) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).hom.hom
        (affineLineCoordinate B S hS (op (totalFractionObject B S hS U))
          (yonedaEquiv (j.1 ≫ f.hom))) :=
    congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).hom.hom
      (evalSiteRingHom_eq B S hS hY hm f j.1 j.2)
  refine (evalRingHom_eq_appTop B S hS hY hInt p hp f _ j.1 g hj).trans ?_
  rw [h2]
  have key : ∀ (k : Spec (CommRingCat.of p.carrier) ⟶
      Spec (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))) (_ : k = Spec.map (CommRingCat.ofHom ρ))
      (a : Γ(Spec (CommRingCat.of (FractionRing Γ(U.left.1, ⊤))), ⊤)),
      (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom (k.appTop a) =
        ρ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).hom.hom a) := by
    rintro k rfl a
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ)) a
  exact key _ hgS _

/-! ### Reading meromorphic functions of a chart at a point whose local ring is a field -/

section Meromorphic

attribute [local instance] chartMeromorphicFunctionAlgebra

variable (Y : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Y.1) (hW : IsAffine (chartScheme W))
    (hK : IsFractionRing ((structurePresheaf B S hS Y.1).obj (op W))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W)))
    (w : chartScheme W) (hw : IsField ((chartScheme W).presheaf.stalk w))

/-- **The reading `𝒦_Y(W) → κ(w)` of meromorphic functions on an affine chart at a point whose
local ring is a field** (a generic point of a reduced chart): `𝒦_Y(W)` is the total ring of
fractions of `𝒪_Y(W)`, whose nonzerodivisors have nonzero residues at `w`. -/
def chartPointResidueReading :
    (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W) →+* (chartScheme W).residueField w :=
  haveI := hW
  haveI := hK
  IsLocalization.lift (M := ((structurePresheaf B S hS Y.1).obj (op W))⁰)
    (g := ((chartScheme W).residue w).hom.comp ((chartScheme W).presheaf.germ ⊤ w trivial).hom)
    fun a ↦ Scheme.isUnit_residue_germ_of_mem_nonZeroDivisors (T := chartScheme W) w hw a.2

/-- The reading at `w` of a regular function is its residue at `w`. -/
theorem chartPointResidueReading_algebraMap (a : (structurePresheaf B S hS Y.1).obj (op W)) :
    chartPointResidueReading B S hS Y W hW hK w hw
        (algebraMap ((structurePresheaf B S hS Y.1).obj (op W))
          ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W)) a) =
      (chartScheme W).residue w ((chartScheme W).presheaf.germ ⊤ w trivial a) :=
  have := hW
  have := hK
  IsLocalization.lift_eq _ _

/-- **(B4, meromorphic functions)**: for `w ⤳ y` with `𝒪_{W, w}` a field, the reading
`𝒦_Y(W) → Q(𝒪_{W, y})` of `AlgebraicGeometry.Space.chartPointMeromorphicMap` (the one of the
order computation of Stacks 0EQV), followed by `Q(𝒪_{W, y}) → κ(w)`, is the reading at `w`. -/
theorem totalFractionToResidueFieldOfSpecializes_chartPointMeromorphicMap {y : chartScheme W}
    (h : w ⤳ y) (c : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W)) :
    Scheme.totalFractionToResidueFieldOfSpecializes h hw
        (FractionRing ((chartScheme W).presheaf.stalk y))
        (chartPointMeromorphicMap B S hS Y W hW hK y c) =
      chartPointResidueReading B S hS Y W hW hK w hw c := by
  have := hW
  have := hK
  exact Scheme.totalFractionToResidueFieldOfSpecializes_apply_of_algebraMap h hw
    (R := (structurePresheaf B S hS Y.1).obj (op W)) (RingHom.id _) _ _
    (fun a ↦ chartPointMeromorphicMap_algebraMap B S hS Y W hW hK y a)
    (fun a ↦ chartPointResidueReading_algebraMap B S hS Y W hW hK w hw a) c

end Meromorphic

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : PrimeDivisor B S hS X) (V : SmallEtale B S hS X)
    (q' : chartScheme (Z.baseChangeChart B S hS hX V))
    (hq' : chartSchemeToPoints B S hS X V (Z.baseChangeChartProj B S hS hX V q') =
      Z.genericPoint B S hS X)

include hq' in
/-- **The local ring of `W' = V ×_X Z` at a point over the generic point of `Z` is a field**:
`W'` is reduced and such a point is a generic point of an irreducible component of it. -/
theorem PrimeDivisor.isField_stalk_baseChangeChart :
    IsField ((Z.baseChangeChart B S hS hX V).obj.left.left.1.presheaf.stalk q') := by
  have := Z.isReduced_chartScheme_baseChangeChart B S hS hX V
  refine isField_stalk_of_isMax (X := chartScheme (Z.baseChangeChart B S hS hX V)) ?_
  refine Order.coheight_eq_zero.mp ((Z.coheight_eq_zero_iff_baseChangeChart B S hS hX V q').mpr ?_)
  exact Z.class_baseChangeChartFieldPoint B S hS hX V q' hq'

variable [IsAffine (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    [IsReduced (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    [IsLocallyNoetherian (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    (hz : IsField ((Z.baseChangeChart B S hS hX V).obj.left.left.1.presheaf.stalk q'))

/-- **(B4, rational functions, first half): the value at `q'` of a rational function of `Z` is
the reading at `q'` of its image in `Q(Γ(W', 𝒪))`**, `W' = V ×_X Z`, `𝒪_{W', q'}` a field. -/
theorem PrimeDivisor.baseChangeChartRationalReading_eq_totalFractionRingToResidueField
    (f : rationalFunctions B S hS Z.closed.1) :
    Z.baseChangeChartRationalReading B S hS hX V q' hq' f =
      Scheme.totalFractionRingToResidueField
        (T := (Z.baseChangeChart B S hS hX V).obj.left.left.1) q' hz
        (rationalFunctionsToTotalFractionRing B S hS Z.closed.1
          (Z.baseChangeChart B S hS hX V).obj.left (Z.baseChangeChart B S hS hX V).obj.hom
          ((isEtale_iff_presheaf_of_yoneda B S hS (Z.baseChangeChart B S hS hX V).obj.hom).2
            (Z.baseChangeChart B S hS hX V).property) f) := by
  have hfac := Scheme.fromSpecResidueField_eq_SpecMap_comp_fromSpecTotalFractionRing
    (T := (Z.baseChangeChart B S hS hX V).obj.left.left.1) q' hz
  have hw : Spec.map (CommRingCat.ofHom
      (Scheme.totalFractionRingToResidueField
        (T := (Z.baseChangeChart B S hS hX V).obj.left.left.1) q' hz)) ≫
      B.inclusion.map (totalFractionObject B S hS (Z.baseChangeChart B S hS hX V).obj.left).hom =
      B.inclusion.map ((Z.baseChangeChartFieldPoint B S hS hX V q').siteObject B S hS
        Z.subspace.toFunctor).hom := by
    have e3 : B.inclusion.map ((Z.baseChangeChartFieldPoint B S hS hX V q').siteObject B S hS
        Z.subspace.toFunctor).hom =
        (Z.baseChangeChart B S hS hX V).obj.left.left.1.fromSpecResidueField q' ≫
          B.inclusion.map (Z.baseChangeChart B S hS hX V).obj.left.hom :=
      (Functor.map_comp _ _ _).trans (congrArg (· ≫ _) (map_siteMapOfSchemeMap B S hS _ _ _))
    refine Eq.trans ?_ e3.symm
    refine Eq.trans ?_
      (congrArg (· ≫ B.inclusion.map (Z.baseChangeChart B S hS hX V).obj.left.hom) hfac.symm)
    exact (Category.assoc _ _ _).symm
  obtain ⟨g, hg⟩ := exists_siteHom_toScheme_map_eq B S hS
    (A := (Z.baseChangeChartFieldPoint B S hS hX V q').siteObject B S hS Z.subspace.toFunctor)
    (A' := totalFractionObject B S hS (Z.baseChangeChart B S hS hX V).obj.left) _ hw
  refine evalRingHom_eq_rationalFunctionsToTotalFractionRing B S hS Z.closed.1 Z.integral
    (Z.baseChangeChart B S hS hX V).obj.left (Z.baseChangeChart B S hS hX V).obj.hom _ _ _ _ g hg
    ?_ f
  have hsite : g ≫ totalFractionObjectMap B S hS (Z.baseChangeChart B S hS hX V).obj.left =
      (canonicalSiteFieldPoint B S hS _ q').siteHom := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
    refine (congrArg (· ≫ _) hg).trans ?_
    exact hfac.symm.trans (map_siteFieldPointOfSchemeMap_value_left B S hS _ _ _).symm
  refine (congrArg (fun k ↦ yoneda.map k ≫ (Z.baseChangeChart B S hS hX V).obj.hom) hsite).trans ?_
  exact (fieldMorphism_map_yoneda B S hS _ _ _).symm

/-- **(B4, rational functions)**: for a point `y` of `W' = V ×_X Z` specializing from a point
`q'` over the generic point of `Z` with `𝒪_{W', q'}` a field, the chart reading
`R(Z) → Q(𝒪_{W', y})` of `AlgebraicGeometry.Space.chartPointRationalFunctionMap` (the one of the
order computation of Stacks 0EQV on `Z`), followed by `Q(𝒪_{W', y}) → κ(q')`, is the value at
`q'`. -/
theorem PrimeDivisor.totalFractionToResidueFieldOfSpecializes_chartPointRationalFunctionMap
    {y : (Z.baseChangeChart B S hS hX V).obj.left.left.1} (h : q' ⤳ y)
    (f : rationalFunctions B S hS Z.closed.1) :
    Scheme.totalFractionToResidueFieldOfSpecializes
        (T := (Z.baseChangeChart B S hS hX V).obj.left.left.1) h hz
        (FractionRing ((Z.baseChangeChart B S hS hX V).obj.left.left.1.presheaf.stalk y))
        (chartPointRationalFunctionMap B S hS Z.closed.1 (Z.baseChangeChart B S hS hX V) y f) =
      Z.baseChangeChartRationalReading B S hS hX V q' hq' f :=
  (Scheme.totalFractionToResidueFieldOfSpecializes_totalFractionRingToStalkFractionRing
    (T := (Z.baseChangeChart B S hS hX V).obj.left.left.1) q' hz h _).trans
    (Z.baseChangeChartRationalReading_eq_totalFractionRingToResidueField B S hS hX V q' hq' hz
      f).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology chartMeromorphicFunctionAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : PrimeDivisor B S hS X) (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) (V : SmallEtale B S hS X)
    (e : (W' : SmallEtale B S hS X) → (W' ⟶ V) → L.val.obj (op W'))
    (hcompat : ∀ (W₁ W₂ : SmallEtale B S hS X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
    (hfree : ∀ (W₁ : SmallEtale B S hS X) (k : W₁ ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W₁ ↦ r • e W₁ k)

/-- **The coefficient of a meromorphic section of `ℒ|_Z` against the restricted generator** over
`W' = V ×_X Z`: the meromorphic function `c` on `W'` with `σ = c · e|_{W'}` there. -/
def PrimeDivisor.baseChangeChartSectionCoefficient
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    (meromorphicFunctionSheaf B S hS (Z.space B S hS).1 (Z.space B S hS).2).obj.obj
      (op (Z.baseChangeChart B S hS hX V)) :=
  chartRatio B S hS Z.subspace.toFunctor Z.closed.1 (Z.restrictModule B S hS hX L)
    (Z.baseChangeChart B S hS hX V) (Z.baseChangeChartGenerator B S hS hX L V e)
    (Z.baseChangeChartGenerator_compat B S hS hX L V e hcompat)
    (Z.bijective_smul_baseChangeChartGenerator B S hS hX L hL V e hcompat hfree) σ

/-- **The reading at a point `q'` of `W'` (with `𝒪_{W', q'}` a field) of a meromorphic section
of `ℒ|_Z` against the restricted generator**: the value in `κ(q')` of its coefficient. -/
def PrimeDivisor.baseChangeChartSectionReading
    (hW : IsAffine (chartScheme (Z.baseChangeChart B S hS hX V)))
    (hK : @IsFractionRing ((structurePresheaf B S hS (Z.space B S hS).1).obj
        (op (Z.baseChangeChart B S hS hX V))) _
      ((meromorphicFunctionSheaf B S hS (Z.space B S hS).1 (Z.space B S hS).2).obj.obj
        (op (Z.baseChangeChart B S hS hX V))) _
      (chartMeromorphicFunctionAlgebra B S hS (X := Z.space B S hS)
        (Z.baseChangeChart B S hS hX V)))
    (q' : chartScheme (Z.baseChangeChart B S hS hX V))
    (hz : IsField ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk q'))
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    (chartScheme (Z.baseChangeChart B S hS hX V)).residueField q' :=
  chartPointResidueReading B S hS (Z.space B S hS) (Z.baseChangeChart B S hS hX V) hW hK q' hz
    (Z.baseChangeChartSectionCoefficient B S hS hX L hL V e hcompat hfree σ)

end AlgebraicGeometry.Space

end
