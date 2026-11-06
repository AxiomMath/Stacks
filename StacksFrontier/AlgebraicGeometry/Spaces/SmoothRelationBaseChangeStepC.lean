module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeClosedFibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothRelationBaseChangeDimension

/-!
# Step C of Stacks 0DS9, with its two base-change hypotheses discharged

`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChange` builds the doubled base change
`R' = (U' ×_{h, U, t} R) ×_{s, U} U'` of a pair of morphisms `s, t : R ⟶ U` along `h : U' ⟶ U`
inside the category `AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over `S`, and its two
legs

* `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeFst : R' ⟶ A`, the base change of
  `h` along `s ∘ pr₂ : A ⟶ U`, and
* `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeSnd : A ⟶ R`, the base change of
  `h` along `t : R ⟶ U`,

are the fibre-product projections of that category.
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq` is
the Step C identity of **Stacks 0DS9** REDUCED to two dimension equalities, one for each leg,
which it takes as the hypotheses `hfst` and `hsnd`: each says that the closed fibre of a leg has
the dimension of the closed fibre of `h` itself. Those equalities are proved, under closedness of
the point in its fibre, in
`StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean` — but for a cartesian
square of PRESHEAVES on the big fppf site, and at the two `U'`-coordinates of the point, which
are different points of `U'` in general. This file bridges both gaps and discharges `hfst` and
`hsnd` at the call site. The reduction itself is left untouched.

## Main definitions

* `AlgebraicGeometry.Space.HasClosedChartFibreSquare`: the closedness input of the closed-fibre
  comparison, packaged together with the chart square it is a condition on.
* `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeRight`: the other projection
  `R' ⟶ U'` of the outer fibre product, the second `U'`-coordinate of a point of `R'`.
* `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeMidFst`: the projection `A ⟶ U'` of
  the inner fibre product, the first `U'`-coordinate.
* `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeMidUnitHom`,
  `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeUnitHom` and
  `AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeUnit`: the identity arrow
  `U' ⟶ R'` determined by a unit section `e : U ⟶ R` of the pair `(s, t)`.

## Main results

* `AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_relationBaseChangeFst` and
  `AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_relationBaseChangeSnd`: each leg sits in a
  cartesian square of presheaves exhibiting it as a base change of `h`.
* `AlgebraicGeometry.Space.AlgebraicSpaces.geometricPointMap_relationBaseChangeUnit_right` and
  `AlgebraicGeometry.Space.AlgebraicSpaces.geometricPointMap_relationBaseChangeUnit_midFst`: at a
  point of the identity arrow BOTH `U'`-coordinates are the given geometric point of `U'`. This is
  the diagonal specialisation that lets a single geometric point of `U'` serve both legs.
* `AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_closedFibre_relationBaseChangeFst_eq` and
  `AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_closedFibre_relationBaseChangeSnd_eq`: the
  two dimension equalities `hfst` and `hsnd`, proved from the closedness input.
* `AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_isClosed`: the
  Step C identity whose hypotheses are the closedness inputs and the identification of the two
  `U'`-coordinates, rather than the two dimension equalities.
* `AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_unit_of_isClosed`:
  the same along the identity arrow, where the identification of the two coordinates is automatic
  and only the closedness remains.

## What is still assumed, and why it cannot be removed

Closedness of the chart point in its chart fibres. The closed-fibre comparison is FALSE without
it — the repository holds the refutation at
`AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_eq` (**Stacks 02FY**,
`local_ring_differences`) — and the counterexample recorded in the docstring of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq` lies
on the diagonal, so the diagonal specialisation below does not supply it. It is the hypothesis the
whole of **Stacks 0DS9** turns on, and the source offers the same curve-with-generic-point
counterexample for it. The results below therefore carry it, one condition for each leg, as
`AlgebraicGeometry.Space.HasClosedChartFibreSquare`.

## The diagonal specialisation, and why it is needed

The two `U'`-coordinates of a point `(u'₁, ρ, u'₂)` of `R'` are different points of `U'` in
general, and the closed fibre of the first leg is compared with the closed fibre of `h` at `u'₂`
while that of the second leg is compared with the closed fibre of `h` at `u'₁`. The Step C
identity of **Stacks 0DS9**, which is
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`,
has room for only ONE geometric point of `U'` and so needs the two coordinates to agree. They
agree along the identity arrow: a *unit section* `e : U ⟶ R` with `e ≫ s = 𝟙 U` and
`e ≫ t = 𝟙 U` — which the self-intersection `R = U ×_𝒳 U` of Stacks 0DS9 has, its diagonal —
induces a section `U' ⟶ R'` both of whose `U'`-coordinates are the identity of `U'`.

No groupoid structure is used: only the two identities `e ≫ s = 𝟙 U` and `e ≫ t = 𝟙 U`, which
is all that "`e` is the identity arrow" contributes here.

## Implementation notes

Fibre products in `AlgebraicGeometry.AlgebraicSpaces` are computed in presheaves
(`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`, Stacks 02X2), and the resulting
transfer of a cartesian square to the underlying presheaves is
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`. Nothing beyond that is needed here: the
inclusion of algebraic spaces into presheaves preserves these limits because the object property
`AlgebraicGeometry.Space.algebraicSpaceProperty` is closed under them
(`AlgebraicGeometry.Space.algebraicSpaceProperty_isClosedUnderLimitsOfShape_walkingCospan`).

The second leg is the base change of `h` along `t`, so its cartesian square is the FLIP of the
defining square of `A = U' ×_{h, U, t} R`: the projection that is a base change of `h` is the
second one, `pr₂ : A ⟶ R`, not the first.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A chart square whose chart points are closed in their chart fibres -/

/-- **The closedness input of the closed-fibre comparison, as a property of the data it is
about.** For `h : U' ⟶ U` and a morphism `π₁ : Z ⟶ W` with a second coordinate `π₂ : Z ⟶ U'`,
this says that the closed fibre of `π₁` at the geometric point `a` is computed by SOME pointed
square of étale charts as in
`AlgebraicGeometry.Space.ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed`, and that
the chart point of that square is closed in both of the chart fibres which the comparison needs
it to be closed in.

The conjuncts other than the last two are exactly the conclusion of
`AlgebraicGeometry.Space.exists_pointed_chart_square_of_isPullback`, so for a `π₁` which is a
base change of `h` — one for which `CategoryTheory.IsPullback π₁ π₂ k h` holds for some `k` —
such a square always exists and the only thing a caller has to supply is the two closedness
conjuncts.

THE CLOSEDNESS IS NOT REMOVABLE, and it is a condition on the CHART point rather than on `a`:
the dimension of the closed fibre of a map of étale local rings is read off a square of étale
scheme charts, and that is the only place the condition can live. The module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean` records the
counterexamples to the unconditional statement; the docstring of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`
records a second one which lies on the diagonal, so the diagonal specialisation does not help. -/
def HasClosedChartFibreSquare {W U U' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : U' ⟶ U)
    (π₁ : Z ⟶ W) (π₂ : Z ⟶ U') (a : GeometricPoint B S hS Z) : Prop :=
  ∃ (M : SmallEtaleNeighborhood a)
    (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
    (P : SmallEtaleNeighborhood (geometricPointMap π₂ a))
    (Q : SmallEtaleNeighborhood (geometricPointMap h (geometricPointMap π₂ a)))
    (gfst : M.chart.obj.left ⟶ N.chart.obj.left)
    (gsnd : M.chart.obj.left ⟶ P.chart.obj.left)
    (gh : P.chart.obj.left ⟶ Q.chart.obj.left)
    (gk : N.chart.obj.left ⟶ Q.chart.obj.left),
    IsAffine (chartScheme N.chart) ∧ IsAffine (chartScheme Q.chart) ∧
      M.chart.obj.hom ≫ π₁ = yoneda.map gfst ≫ N.chart.obj.hom ∧
        P.chart.obj.hom ≫ h = yoneda.map gh ≫ Q.chart.obj.hom ∧
          M.point ≫ gfst = N.point ∧ P.point ≫ gh = Q.point ∧
            M.point ≫ gsnd = P.point ∧
              IsPullback ((BigFppfOver.toScheme B S hS).map gsnd)
                  ((BigFppfOver.toScheme B S hS).map gfst)
                  ((BigFppfOver.toScheme B S hS).map gh)
                  ((BigFppfOver.toScheme B S hS).map gk) ∧
                IsClosed ({((BigFppfOver.toScheme B S hS).map gfst).asFiber
                             ((chartGeometricPoint M).hom (IsLocalRing.closedPoint
                               (chartGeometricPoint M).residueField))} : Set _) ∧
                  IsClosed ({((BigFppfOver.toScheme B S hS).map gh).asFiber
                               (((BigFppfOver.toScheme B S hS).map gsnd)
                                 ((chartGeometricPoint M).hom (IsLocalRing.closedPoint
                                   (chartGeometricPoint M).residueField)))} : Set _)

/-- **The closed fibre of a base change has the dimension of the closed fibre of the original
morphism, once the closedness input is available.** This is
`AlgebraicGeometry.Space.ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed` with its
chart square and its two closedness hypotheses packaged into
`AlgebraicGeometry.Space.HasClosedChartFibreSquare`, so that a consumer which has to carry the
condition through several applications does not have to carry the square along with it. -/
theorem ringKrullDim_closedFibre_eq_of_hasClosedChartFibreSquare
    {W U U' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hU : IsAlgebraicSpace B S hS U) (hU' : IsAlgebraicSpace B S hS U') (h : U' ⟶ U)
    (π₁ : Z ⟶ W) (π₂ : Z ⟶ U') (hZ : IsAlgebraicSpace B S hS Z)
    (hh : IsLocallyOfFiniteType B S hS h) (a : GeometricPoint B S hS Z)
    (hcl : HasClosedChartFibreSquare B S hS h π₁ π₂ a) :
    ringKrullDim (closedFibreEtaleLocalRing B S hS hZ π₁ a) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS hU' h (geometricPointMap π₂ a)) := by
  obtain ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hcomm₂, hpoint₁, hpoint₂,
    hmp, hsq, hcl₁, hcl₂⟩ := hcl
  exact ringKrullDim_closedFibre_eq_of_chart_isPullback_of_isClosed B S hS hW hU hU' h π₁ π₂
    hZ hh a M N gfst hcomm₁ hpoint₁ hNaff P Q gh hcomm₂ hpoint₂ hQaff gsnd gk hsq hmp hcl₁ hcl₂

/-- **Closedness is the only thing a caller has to supply.** For `π₁` a base change of `h` —
a cartesian square `IsPullback π₁ π₂ k h` of presheaves — there is a pointed square of étale
charts at every geometric point `a`, by
`AlgebraicGeometry.Space.exists_pointed_chart_square_of_isPullback`, and closedness of its chart
point in the two chart fibres gives
`AlgebraicGeometry.Space.HasClosedChartFibreSquare`. The square is returned rather than discarded
precisely so that a caller can establish the closedness for the charts it is actually given.

This is where the closedness enters and the only place it can: it is NOT derivable, by the
counterexamples recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean`. -/
theorem exists_chart_square_hasClosedChartFibreSquare_of_isPullback
    {W U U' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hU : IsAlgebraicSpace B S hS U) (hU' : IsAlgebraicSpace B S hS U') (k : W ⟶ U)
    (h : U' ⟶ U) (π₁ : Z ⟶ W) (π₂ : Z ⟶ U') (hsq₀ : IsPullback π₁ π₂ k h)
    (hZ : IsAlgebraicSpace B S hS Z) (a : GeometricPoint B S hS Z) :
    ∃ (M : SmallEtaleNeighborhood a)
      (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
      (P : SmallEtaleNeighborhood (geometricPointMap π₂ a))
      (Q : SmallEtaleNeighborhood (geometricPointMap h (geometricPointMap π₂ a)))
      (gfst : M.chart.obj.left ⟶ N.chart.obj.left)
      (gsnd : M.chart.obj.left ⟶ P.chart.obj.left)
      (gh : P.chart.obj.left ⟶ Q.chart.obj.left),
      IsClosed ({((BigFppfOver.toScheme B S hS).map gfst).asFiber
                   ((chartGeometricPoint M).hom (IsLocalRing.closedPoint
                     (chartGeometricPoint M).residueField))} : Set _) →
        IsClosed ({((BigFppfOver.toScheme B S hS).map gh).asFiber
                     (((BigFppfOver.toScheme B S hS).map gsnd)
                       ((chartGeometricPoint M).hom (IsLocalRing.closedPoint
                         (chartGeometricPoint M).residueField)))} : Set _) →
          HasClosedChartFibreSquare B S hS h π₁ π₂ a := by
  obtain ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hcomm₂, hpoint₁, hpoint₂,
    hmp, hsq⟩ :=
    exists_pointed_chart_square_of_isPullback B S hS hW hU hU' k h π₁ π₂ hsq₀ hZ a
  exact ⟨M, N, P, Q, gfst, gsnd, gh, fun hcl₁ hcl₂ =>
    ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hcomm₂, hpoint₁, hpoint₂, hmp, hsq,
      hcl₁, hcl₂⟩⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.AlgebraicSpaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U' R : AlgebraicSpaces B S hS}

/-- The **second `U'`-coordinate** of the doubled base change: the projection `R' ⟶ U'` of the
outer fibre product `R' = A ×_{s ∘ pr₂, U, h} U'`, the leg of that fibre product which is not
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeFst`. On points
`R' = {(u'₁, ρ, u'₂)}` this is `(u'₁, ρ, u'₂) ↦ u'₂`. -/
noncomputable def relationBaseChangeRight (h : U' ⟶ U) (s t : R ⟶ U) :
    relationBaseChange B S hS h s t ⟶ U' :=
  pullback.snd (pullback.snd h t ≫ s) h

/-- The **first `U'`-coordinate** of the doubled base change: the projection `A ⟶ U'` of the
intermediate fibre product `A = U' ×_{h, U, t} R`, the leg of that fibre product which is not
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeSnd`. On points this is
`(u'₁, ρ) ↦ u'₁`. -/
noncomputable def relationBaseChangeMidFst (h : U' ⟶ U) (s t : R ⟶ U) :
    relationBaseChangeMid B S hS h s t ⟶ U' :=
  pullback.fst h t

/-- **The first leg of the doubled base change is a base change of `h`, on the underlying
presheaves.** The square

```
R' --- pr₂ ---> U'
|               |
pr₁             h
↓               ↓
A --- s ∘ pr₂ -> U
```

is cartesian as a square of presheaves on the big fppf site of `S`, `pr₁` being
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeFst` and `pr₂` being
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeRight`.

This is the form in which
`AlgebraicGeometry.Space.exists_pointed_chart_square_of_isPullback` and
`AlgebraicGeometry.Space.exists_chart_square_ringKrullDim_closedFibre_eq_of_isPullback` can be
applied to the first leg: those are stated for an arbitrary cartesian square of presheaves, and
the doubled base change is built in the category of algebraic spaces instead. -/
theorem isPullback_relationBaseChangeFst (h : U' ⟶ U) (s t : R ⟶ U) :
    IsPullback (relationBaseChangeFst B S hS h s t).hom
      (relationBaseChangeRight B S hS h s t).hom
      ((relationBaseChangeSnd B S hS h s t).hom ≫ s.hom) h.hom :=
  _root_.AlgebraicGeometry.AlgebraicSpaces.isPullback_hom B S hS
    (IsPullback.of_hasPullback (pullback.snd h t ≫ s) h)

/-- **The second leg of the doubled base change is a base change of `h`, on the underlying
presheaves.** The square

```
A --- pr₁ ---> U'
|              |
pr₂            h
↓              ↓
R ---- t ----> U
```

is cartesian as a square of presheaves on the big fppf site of `S`, `pr₂` being
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeSnd` and `pr₁` being
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeMidFst`.

The square is the flip of the defining square of `A = U' ×_{h, U, t} R`, since it is the second
projection of that fibre product which is a base change of `h`. -/
theorem isPullback_relationBaseChangeSnd (h : U' ⟶ U) (s t : R ⟶ U) :
    IsPullback (relationBaseChangeSnd B S hS h s t).hom
      (relationBaseChangeMidFst B S hS h s t).hom t.hom h.hom :=
  _root_.AlgebraicGeometry.AlgebraicSpaces.isPullback_hom B S hS
    (IsPullback.of_hasPullback h t).flip

/-! ### The identity arrow, and the diagonal specialisation -/

/-- The **identity arrow of the intermediate stage** `A = U' ×_{h, U, t} R` attached to a unit
section `e : U ⟶ R` of `t`, read on the underlying presheaves: the morphism `U' ⟶ A` with
coordinates `𝟙 U'` and `h ≫ e`. On points it is `u' ↦ (u', e(h(u')))`. -/
noncomputable def relationBaseChangeMidUnitHom (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (het : e ≫ t = 𝟙 U) :
    U'.obj ⟶ (relationBaseChangeMid B S hS h s t).obj :=
  (isPullback_relationBaseChangeSnd B S hS h s t).lift (h.hom ≫ e.hom) (𝟙 U'.obj) (by
    have het' : e.hom ≫ t.hom = 𝟙 U.obj := congrArg (fun k => k.hom) het
    rw [Category.assoc, het', Category.comp_id, Category.id_comp])

/-- The identity arrow of the intermediate stage has first `U'`-coordinate the identity. -/
theorem relationBaseChangeMidUnitHom_comp_midFst (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (het : e ≫ t = 𝟙 U) :
    relationBaseChangeMidUnitHom B S hS h s t e het ≫
        (relationBaseChangeMidFst B S hS h s t).hom = 𝟙 U'.obj :=
  (isPullback_relationBaseChangeSnd B S hS h s t).lift_snd _ _ _

/-- The identity arrow of the intermediate stage lies over the identity arrow of `R`. -/
theorem relationBaseChangeMidUnitHom_comp_snd (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (het : e ≫ t = 𝟙 U) :
    relationBaseChangeMidUnitHom B S hS h s t e het ≫
        (relationBaseChangeSnd B S hS h s t).hom = h.hom ≫ e.hom :=
  (isPullback_relationBaseChangeSnd B S hS h s t).lift_fst _ _ _

/-- The **identity arrow of the doubled base change** attached to a unit section `e : U ⟶ R` of
the pair `(s, t)`, that is, to a morphism with `e ≫ s = 𝟙 U` and `e ≫ t = 𝟙 U`, read on the
underlying presheaves. On points it is `u' ↦ (u', e(h(u')), u')`: BOTH `U'`-coordinates are `u'`
itself, which is what makes the diagonal specialisation of the Step C identity of
**Stacks 0DS9** available.

When `R = U ×_𝒳 U` is a presented self-intersection with `s` and `t` its two projections, `e` is
the diagonal of `U` over `𝒳` and this is the identity section of the corresponding
self-intersection of `U'`. -/
noncomputable def relationBaseChangeUnitHom (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U) :
    U'.obj ⟶ (relationBaseChange B S hS h s t).obj :=
  (isPullback_relationBaseChangeFst B S hS h s t).lift
    (relationBaseChangeMidUnitHom B S hS h s t e het) (𝟙 U'.obj) (by
      have hes' : e.hom ≫ s.hom = 𝟙 U.obj := congrArg (fun k => k.hom) hes
      rw [← Category.assoc, relationBaseChangeMidUnitHom_comp_snd, Category.assoc, hes',
        Category.comp_id, Category.id_comp])

/-- The identity arrow of the doubled base change has second `U'`-coordinate the identity. -/
theorem relationBaseChangeUnitHom_comp_right (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U) :
    relationBaseChangeUnitHom B S hS h s t e hes het ≫
        (relationBaseChangeRight B S hS h s t).hom = 𝟙 U'.obj :=
  (isPullback_relationBaseChangeFst B S hS h s t).lift_snd _ _ _

/-- The identity arrow of the doubled base change lies over the identity arrow of the
intermediate stage. -/
theorem relationBaseChangeUnitHom_comp_fst (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U) :
    relationBaseChangeUnitHom B S hS h s t e hes het ≫
        (relationBaseChangeFst B S hS h s t).hom
      = relationBaseChangeMidUnitHom B S hS h s t e het :=
  (isPullback_relationBaseChangeFst B S hS h s t).lift_fst _ _ _

/-- The **identity arrow of the doubled base change**, as a morphism of algebraic spaces. Its
underlying morphism of presheaves is
`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChangeUnitHom`, which is where it is
constructed: a morphism of presheaves between two algebraic spaces is a morphism of algebraic
spaces, the category of algebraic spaces being a full subcategory. -/
noncomputable def relationBaseChangeUnit (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U) :
    U' ⟶ relationBaseChange B S hS h s t :=
  ObjectProperty.homMk (relationBaseChangeUnitHom B S hS h s t e hes het)

/-- The underlying morphism of presheaves of `relationBaseChangeUnit` is
`relationBaseChangeUnitHom`. -/
@[simp]
theorem relationBaseChangeUnit_hom (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U) :
    (relationBaseChangeUnit B S hS h s t e hes het).hom
      = relationBaseChangeUnitHom B S hS h s t e hes het :=
  rfl

/-- A geometric point is fixed by a morphism followed by a retraction of it. -/
private theorem geometricPointMap_comp_eq_self {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ F) (hfg : f ≫ g = 𝟙 F) (x : GeometricPoint B S hS F) :
    geometricPointMap g (geometricPointMap f x) = x :=
  congrArg (fun k => geometricPointMap k x) hfg

/-- **The second `U'`-coordinate of a point of the identity arrow is the point itself.** This is
one half of the diagonal specialisation: the closed fibre of the first leg of the doubled base
change at `relationBaseChangeUnit(x̄')` is compared by
`AlgebraicGeometry.Space.exists_chart_square_ringKrullDim_closedFibre_eq_of_isPullback` with the
closed fibre of `h` at the second `U'`-coordinate, and here that coordinate is `x̄'`. -/
theorem geometricPointMap_relationBaseChangeUnit_right (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U) (x' : GeometricPoint B S hS U'.obj) :
    geometricPointMap (relationBaseChangeRight B S hS h s t).hom
        (geometricPointMap (relationBaseChangeUnit B S hS h s t e hes het).hom x') = x' := by
  exact geometricPointMap_comp_eq_self B S hS _ _
    (relationBaseChangeUnitHom_comp_right B S hS h s t e hes het) x'

/-- **The first `U'`-coordinate of a point of the identity arrow is the point itself.** This is
the other half of the diagonal specialisation: the closed fibre of the second leg of the doubled
base change, taken at the image of `relationBaseChangeUnit(x̄')` in the intermediate stage, is
compared with the closed fibre of `h` at the first `U'`-coordinate, and here that coordinate is
again `x̄'`. The two halves together are what let a SINGLE geometric point of `U'` discharge both
hypotheses of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`. -/
theorem geometricPointMap_relationBaseChangeUnit_midFst (h : U' ⟶ U) (s t : R ⟶ U) (e : U ⟶ R)
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U) (x' : GeometricPoint B S hS U'.obj) :
    geometricPointMap (relationBaseChangeMidFst B S hS h s t).hom
        (geometricPointMap (relationBaseChangeFst B S hS h s t).hom
          (geometricPointMap (relationBaseChangeUnit B S hS h s t e hes het).hom x')) = x' := by
  refine geometricPointMap_comp_eq_self B S hS (relationBaseChangeUnitHom B S hS h s t e hes het)
    ((relationBaseChangeFst B S hS h s t).hom ≫ (relationBaseChangeMidFst B S hS h s t).hom) ?_ x'
  rw [← Category.assoc, relationBaseChangeUnitHom_comp_fst,
    relationBaseChangeMidUnitHom_comp_midFst]


/-! ### Step C of Stacks 0DS9, with its two base-change hypotheses discharged -/

/-- **The closed fibre of the first leg has the dimension of the closed fibre of `h`.** The first
leg `pr₁ : R' ⟶ A` of the doubled base change is a base change of `h`
(`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_relationBaseChangeFst`), so the comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean` applies to it: at a
geometric point of `R'` whose chart point is closed in its chart fibres, its closed fibre has the
dimension of the closed fibre of `h` at the second `U'`-coordinate of that point.

This is the hypothesis `hfst` of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`, with
`x'` taken to be that second coordinate. -/
theorem ringKrullDim_closedFibre_relationBaseChangeFst_eq (h : U' ⟶ U) (s t : R ⟶ U)
    (hlft : IsLocallyOfFiniteType B S hS h.hom)
    (r : GeometricPoint B S hS (relationBaseChange B S hS h s t).obj)
    (hcl : HasClosedChartFibreSquare B S hS h.hom
      (relationBaseChangeFst B S hS h s t).hom (relationBaseChangeRight B S hS h s t).hom r) :
    ringKrullDim (closedFibreEtaleLocalRing B S hS (relationBaseChange B S hS h s t).property
        (relationBaseChangeFst B S hS h s t).hom r) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS U'.property h.hom
        (geometricPointMap (relationBaseChangeRight B S hS h s t).hom r)) :=
  ringKrullDim_closedFibre_eq_of_hasClosedChartFibreSquare B S hS
    (relationBaseChangeMid B S hS h s t).property U.property U'.property h.hom
    (relationBaseChangeFst B S hS h s t).hom (relationBaseChangeRight B S hS h s t).hom
    (relationBaseChange B S hS h s t).property hlft r hcl

/-- **The closed fibre of the second leg has the dimension of the closed fibre of `h`.** The
second leg `pr₂ : A ⟶ R` of the doubled base change is a base change of `h`
(`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_relationBaseChangeSnd`), so at a geometric
point of `A` whose chart point is closed in its chart fibres its closed fibre has the dimension of
the closed fibre of `h` at the first `U'`-coordinate of that point.

This is the hypothesis `hsnd` of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`, with
`x'` taken to be that first coordinate. -/
theorem ringKrullDim_closedFibre_relationBaseChangeSnd_eq (h : U' ⟶ U) (s t : R ⟶ U)
    (hlft : IsLocallyOfFiniteType B S hS h.hom)
    (a : GeometricPoint B S hS (relationBaseChangeMid B S hS h s t).obj)
    (hcl : HasClosedChartFibreSquare B S hS h.hom
      (relationBaseChangeSnd B S hS h s t).hom (relationBaseChangeMidFst B S hS h s t).hom a) :
    ringKrullDim (closedFibreEtaleLocalRing B S hS (relationBaseChangeMid B S hS h s t).property
        (relationBaseChangeSnd B S hS h s t).hom a) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS U'.property h.hom
        (geometricPointMap (relationBaseChangeMidFst B S hS h s t).hom a)) :=
  ringKrullDim_closedFibre_eq_of_hasClosedChartFibreSquare B S hS
    R.property U.property U'.property h.hom
    (relationBaseChangeSnd B S hS h s t).hom (relationBaseChangeMidFst B S hS h s t).hom
    (relationBaseChangeMid B S hS h s t).property hlft a hcl

/-- **The Step C identity of Stacks 0DS9, with its two base-change hypotheses discharged.** In
the subtraction-free form

`dim(𝒪_{U', ū'}) + dim(𝒪_{U', ū'}) + dim(𝒪_{R, p(r)})
    = dim(𝒪_{U, ū}) + dim(𝒪_{U, ū}) + dim(𝒪_{R', r})`,

this is
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq` with
its hypotheses `hfst` and `hsnd` — the two dimension equalities for the closed fibres of the two
legs — replaced by the closedness inputs they are deduced from. That theorem is unchanged; the two
equalities are supplied here, at the call site, from
`StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean`.

THE HYPOTHESES THAT REMAIN ARE EXACTLY TWO KINDS, and neither is removable.

`hxfst` and `hxsnd` are the DIAGONAL SPECIALISATION: the closed fibre of the first leg is
compared with the closed fibre of `h` at the second `U'`-coordinate of `r` and that of the second
leg with the closed fibre of `h` at the first `U'`-coordinate, and these are different points of
`U'` in general, whereas the conclusion has room for only one. Along the identity arrow of a
relation they agree, which is
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_unit_of_isClosed`.

`hcl₁` and `hcl₂` are the CLOSEDNESS of the chart point in its chart fibres, one for each leg.
These are caller-supplied: the comparison of closed fibres is FALSE without them, the repository
holds the refutation at `AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_eq` (Stacks 02FY,
`local_ring_differences`), and the counterexample of the docstring of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq` lies
on the diagonal, so the specialisation above does not supply them either. Closedness is the
hypothesis the whole of **Stacks 0DS9** turns on. -/
theorem ringKrullDim_etaleLocalRing_stepC_of_isClosed (h : U' ⟶ U) (s t : R ⟶ U)
    (hh : IsSmooth B S hS h.hom)
    (hNU : HasEtaleLocalProperty B S hS U.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNR : HasEtaleLocalProperty B S hS R.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (r : GeometricPoint B S hS (relationBaseChange B S hS h s t).obj)
    (x' : GeometricPoint B S hS U'.obj)
    (hxfst : geometricPointMap (relationBaseChangeRight B S hS h s t).hom r = x')
    (hxsnd : geometricPointMap (relationBaseChangeMidFst B S hS h s t).hom
      (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r) = x')
    (hcl₁ : HasClosedChartFibreSquare B S hS h.hom
      (relationBaseChangeFst B S hS h s t).hom (relationBaseChangeRight B S hS h s t).hom r)
    (hcl₂ : HasClosedChartFibreSquare B S hS h.hom
      (relationBaseChangeSnd B S hS h s t).hom (relationBaseChangeMidFst B S hS h s t).hom
      (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r)) :
    ringKrullDim (etaleLocalRing B S hS U'.obj x') +
          ringKrullDim (etaleLocalRing B S hS U'.obj x') +
        ringKrullDim (etaleLocalRing B S hS R.obj
          (geometricPointMap (relationBaseChangeSnd B S hS h s t).hom
            (geometricPointMap (relationBaseChangeFst B S hS h s t).hom r))) =
      ringKrullDim (etaleLocalRing B S hS U.obj (geometricPointMap h.hom x')) +
            ringKrullDim (etaleLocalRing B S hS U.obj (geometricPointMap h.hom x')) +
        ringKrullDim (etaleLocalRing B S hS (relationBaseChange B S hS h s t).obj r) := by
  have hlft : IsLocallyOfFiniteType B S hS h.hom := isLocallyOfFiniteType_of_isSmooth B S hS hh
  refine ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq B S hS h s t hh hNU hNR r x' ?_ ?_
  · rw [← hxfst]
    exact ringKrullDim_closedFibre_relationBaseChangeFst_eq B S hS h s t hlft r hcl₁
  · rw [← hxsnd]
    exact ringKrullDim_closedFibre_relationBaseChangeSnd_eq B S hS h s t hlft _ hcl₂

/-- **The Step C identity of Stacks 0DS9 along the identity arrow of a relation.** This is
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_isClosed` at the
point `r = e(ū')` of the identity arrow attached to a unit section `e : U ⟶ R` of the pair
`(s, t)`, where the diagonal specialisation is automatic: both `U'`-coordinates of such a point
are `ū'` itself.

What is left is the closedness of the chart point in its chart fibres, one condition for each leg,
and that is caller-supplied and not removable — see the docstring of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_isClosed`.

When `R = U ×_𝒳 U` is a presented self-intersection with `s` and `t` its two projections, `e` is
the diagonal of `U` over `𝒳` and this is the Step C identity of Stacks 0DS9 in the situation in
which the source states it. -/
theorem ringKrullDim_etaleLocalRing_stepC_unit_of_isClosed (h : U' ⟶ U) (s t : R ⟶ U)
    (e : U ⟶ R) (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U)
    (hh : IsSmooth B S hS h.hom)
    (hNU : HasEtaleLocalProperty B S hS U.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNR : HasEtaleLocalProperty B S hS R.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x' : GeometricPoint B S hS U'.obj)
    (hcl₁ : HasClosedChartFibreSquare B S hS h.hom
      (relationBaseChangeFst B S hS h s t).hom (relationBaseChangeRight B S hS h s t).hom
      (geometricPointMap (relationBaseChangeUnit B S hS h s t e hes het).hom x'))
    (hcl₂ : HasClosedChartFibreSquare B S hS h.hom
      (relationBaseChangeSnd B S hS h s t).hom (relationBaseChangeMidFst B S hS h s t).hom
      (geometricPointMap (relationBaseChangeFst B S hS h s t).hom
        (geometricPointMap (relationBaseChangeUnit B S hS h s t e hes het).hom x'))) :
    ringKrullDim (etaleLocalRing B S hS U'.obj x') +
          ringKrullDim (etaleLocalRing B S hS U'.obj x') +
        ringKrullDim (etaleLocalRing B S hS R.obj
          (geometricPointMap (relationBaseChangeSnd B S hS h s t).hom
            (geometricPointMap (relationBaseChangeFst B S hS h s t).hom
              (geometricPointMap (relationBaseChangeUnit B S hS h s t e hes het).hom x')))) =
      ringKrullDim (etaleLocalRing B S hS U.obj (geometricPointMap h.hom x')) +
            ringKrullDim (etaleLocalRing B S hS U.obj (geometricPointMap h.hom x')) +
        ringKrullDim (etaleLocalRing B S hS (relationBaseChange B S hS h s t).obj
          (geometricPointMap (relationBaseChangeUnit B S hS h s t e hes het).hom x')) :=
  ringKrullDim_etaleLocalRing_stepC_of_isClosed B S hS h s t hh hNU hNR
    (geometricPointMap (relationBaseChangeUnit B S hS h s t e hes het).hom x') x'
    (geometricPointMap_relationBaseChangeUnit_right B S hS h s t e hes het x')
    (geometricPointMap_relationBaseChangeUnit_midFst B S hS h s t e hes het x')
    hcl₁ hcl₂

end AlgebraicGeometry.Space.AlgebraicSpaces

end
