module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CoordinateAxesEtaleRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.FunctionFieldEmbedding

/-!
# The quotient of the coordinate axes by the swap away from the origin

Let `k` be a field, let `U = Spec (k[x, y]/(xy))` be the union of the coordinate axes, and let
`R = Δ(U) ⨿ Δ'(U ∖ {0_U})` be the relation which is the diagonal on the first summand and the
graph of the coordinate swap on the punctured axes. **Stacks 0ENU** asserts that `R` is an étale
equivalence relation and that the quotient `X = U/R` is an algebraic space. This file proves the
second assertion, places `U` in a big fppf site containing `Spec k`, and describes the
`T`-valued points of `U` as pairs `(a, b)` of global functions of `T` with `ab = 0`.

## Main definitions

* `AlgebraicGeometry.CoordinateAxesQuotient.axesChart` is `U` as an object of the site.
* `AlgebraicGeometry.CoordinateAxesQuotient.quotientSpace` is the quotient sheaf `X = U/R`.
* `AlgebraicGeometry.CoordinateAxesQuotient.sumMap` is the morphism `X ⟶ 𝔸¹_k` descended from
  `(x, y) ↦ x + y`.
* `AlgebraicGeometry.CoordinateAxesQuotient.axesPoint` is the `T`-point of `U` with prescribed
  coordinates.

## Main results

* `AlgebraicGeometry.CoordinateAxesQuotient.isEtaleEquivalenceRelation`: the relation is an
  étale equivalence relation, as an instance.
* `AlgebraicGeometry.CoordinateAxesQuotient.isAlgebraicSpace_quotientSpace`: **Stacks 0ENU**,
  the quotient is an algebraic space, for every field `k`.
* `AlgebraicGeometry.CoordinateAxesQuotient.quotientMap_comp_sumMap`: the descended sum
  map restricts to `(x, y) ↦ x + y` along the projection `U ⟶ X`.
* `AlgebraicGeometry.CoordinateAxesQuotient.axes_hom_ext`: a `T`-point of `U` is determined by
  its two coordinates.

## Implementation notes

The relation of this file is `AlgebraicGeometry.CoordinateAxesQuotient.relationPreRelation`,
the one the sum map is descended along. Its étale-equivalence-relation property is
`AlgebraicGeometry.Space.EtaleRelation.isEtaleEquivalenceRelation`, stated for the setup of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.CoordinateAxes`; the two setups package the same
field and build the same relation by the same definitions, so the two relations are
definitionally equal and the instance is a direct transfer.

The chart `U` is affine, so the effective-descent hypotheses of Stacks 0265 are discharged by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional`. No
hypothesis on the characteristic of `k` is needed anywhere: the swap fixes only the origin over
any field.

## References

* [Stacks Project, Tag 0ENU](https://stacks.math.columbia.edu/tag/0ENU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedChangeOfRings

universe u

namespace AlgebraicGeometry.CoordinateAxesQuotient

/-- **Stacks 0ENU.** The relation `R = Δ(U) ⨿ Δ'(U ∖ {0_U})` is an étale equivalence relation
on the coordinate axes. This is
`AlgebraicGeometry.Space.EtaleRelation.isEtaleEquivalenceRelation`, whose relation is
definitionally the one of this file. -/
instance isEtaleEquivalenceRelation (S : Setup.{u}) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (relationPreRelation S) :=
  Space.EtaleRelation.isEtaleEquivalenceRelation ⟨S.k, S.field⟩

/-- The coordinate axes are locally of finite type over `Spec k`. -/
instance (S : Setup.{u}) : LocallyOfFiniteType (baseMap S) := by
  rw [baseMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap S.k (NodalRing S.k)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-! ### The `T`-valued points of the coordinate axes -/

variable (S : Setup.{u})

/-- The structure ring map `k → Γ(T, ⊤)` of a scheme over `Spec k`. -/
noncomputable def structureRingHom (T : Over (Spec (.of S.k))) : S.k →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.k)).inv ≫ T.hom.appTop).hom

/-- The ring map `k[x, y]/(xy) → Γ(T, ⊤)` sending `x` to `a` and `y` to `b`, for `ab = 0`. -/
noncomputable def axesRingHom {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤)) (h : a * b = 0) :
    NodalRing S.k →+* Γ(T.left, ⊤) :=
  Ideal.Quotient.lift (nodalRelationIdeal S.k)
    (MvPolynomial.eval₂Hom (structureRingHom S T) (fun i => cond i b a)) (by
      intro p hp
      rw [← RingHom.mem_ker]
      refine (Ideal.span_le.mpr ?_) hp
      rintro _ rfl
      simp [RingHom.mem_ker, xVariable, yVariable, h])

/-- The ring map `axesRingHom S a b h` sends `x` to `a`. -/
@[simp]
theorem axesRingHom_xClass {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤)) (h : a * b = 0) :
    axesRingHom S a b h (xClass S.k) = a := by
  simp [axesRingHom, xClass, xVariable]

/-- The ring map `axesRingHom S a b h` sends `y` to `b`. -/
@[simp]
theorem axesRingHom_yClass {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤)) (h : a * b = 0) :
    axesRingHom S a b h (yClass S.k) = b := by
  simp [axesRingHom, yClass, yVariable]

/-- The ring map `axesRingHom S a b h` restricts to the structure map `k → Γ(T, ⊤)` on `k`. -/
theorem axesRingHom_algebraMap {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤))
    (h : a * b = 0) (r : S.k) :
    axesRingHom S a b h (algebraMap S.k (NodalRing S.k) r) = structureRingHom S T r := by
  rw [← Ideal.Quotient.mk_algebraMap, axesRingHom, Ideal.Quotient.lift_mk,
    MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C]

/-- For a ring map `φ : A → Γ(T, ⊤)`, the composite `T ⟶ Spec Γ(T, ⊤) ⟶ Spec A` acts on global
sections as `φ`. -/
theorem toSpecΓ_comp_specMap_appTop (T : Scheme.{u}) {A : CommRingCat.{u}}
    (φ : A ⟶ Γ(T, ⊤)) (a : A) :
    (T.toSpecΓ ≫ Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) = φ a := by
  rw [Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
    Category.comp_id]


/-- The `T`-point of the coordinate axes with coordinates `(a, b)`, for `ab = 0`. -/
noncomputable def axesPoint {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤)) (h : a * b = 0) :
    T ⟶ axesOver S :=
  Over.homMk (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (axesRingHom S a b h))) (by
    apply ext_of_isAffine
    ext r
    change (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (axesRingHom S a b h))).appTop
        ((baseMap S).appTop r) = T.hom.appTop r
    obtain ⟨r, rfl⟩ := (Scheme.ΓSpecIso (.of S.k)).commRingCatIsoToRingEquiv.symm.surjective r
    have hb : (baseMap S).appTop ((Scheme.ΓSpecIso (.of S.k)).inv r) =
        (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (algebraMap S.k (NodalRing S.k) r) := by
      rw [baseMap, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    change (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (axesRingHom S a b h))).appTop
        ((baseMap S).appTop ((Scheme.ΓSpecIso (.of S.k)).inv r)) =
      T.hom.appTop ((Scheme.ΓSpecIso (.of S.k)).inv r)
    rw [hb, toSpecΓ_comp_specMap_appTop]
    exact axesRingHom_algebraMap S a b h r)

/-- The `T`-point `axesPoint S a b h` pulls back `ΓSpecIso.inv c` to the image of `c` under
`axesRingHom S a b h`. -/
private theorem appTop_axesPoint {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤))
    (h : a * b = 0) (c : NodalRing S.k) :
    (axesPoint S a b h).left.appTop ((Scheme.ΓSpecIso (.of (NodalRing S.k))).inv c) =
      axesRingHom S a b h c :=
  toSpecΓ_comp_specMap_appTop _ (CommRingCat.ofHom (axesRingHom S a b h)) c

/-- The `x`-coordinate of the `T`-point `axesPoint S a b h` is `a`. -/
@[simp]
theorem axesPoint_xSection {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤)) (h : a * b = 0) :
    (axesPoint S a b h).left.appTop (xSection S) = a := by
  exact (appTop_axesPoint S a b h _).trans (axesRingHom_xClass S a b h)

/-- The `y`-coordinate of the `T`-point `axesPoint S a b h` is `b`. -/
@[simp]
theorem axesPoint_ySection {T : Over (Spec (.of S.k))} (a b : Γ(T.left, ⊤)) (h : a * b = 0) :
    (axesPoint S a b h).left.appTop (ySection S) = b := by
  exact (appTop_axesPoint S a b h _).trans (axesRingHom_yClass S a b h)

/-- The coordinate functions `x` and `y` on the coordinate axes multiply to zero. -/
theorem xSection_mul_ySection : xSection S * ySection S = 0 := by
  rw [xSection, ySection, ← map_mul]
  change (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv
    (Ideal.Quotient.mk (nodalRelationIdeal S.k) (xVariable S.k * yVariable S.k)) = 0
  have h0 : Ideal.Quotient.mk (nodalRelationIdeal S.k) (xVariable S.k * yVariable S.k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [h0, map_zero]

/-- The two coordinates of a `T`-point of the coordinate axes multiply to zero. -/
theorem appTop_xSection_mul_appTop_ySection {T : Over (Spec (.of S.k))} (a : T ⟶ axesOver S) :
    a.left.appTop (xSection S) * a.left.appTop (ySection S) = 0 := by
  rw [← map_mul, xSection_mul_ySection, map_zero]

/-- The coordinate axes form an affine scheme. -/
instance : IsAffine (axesOver S).left := inferInstanceAs (IsAffine (Spec _))

/-- Two `T`-points of the coordinate axes agree as soon as their coordinates agree. -/
theorem axes_hom_ext {T : Over (Spec (.of S.k))} {a b : T ⟶ axesOver S}
    (hx : a.left.appTop (xSection S) = b.left.appTop (xSection S))
    (hy : a.left.appTop (ySection S) = b.left.appTop (ySection S)) : a = b := by
  refine Over.OverMorphism.ext (ext_of_isAffine ?_)
  have hiso : ∀ φ ψ : Γ(coordinateAxes S, ⊤) ⟶ Γ(T.left, ⊤),
      (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv ≫ φ =
        (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv ≫ ψ → φ = ψ := fun φ ψ h => by
    simpa using congrArg ((Scheme.ΓSpecIso (.of (NodalRing S.k))).hom ≫ ·) h
  apply hiso
  ext1
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · have hw : (baseMap S).appTop ≫ a.left.appTop = (baseMap S).appTop ≫ b.left.appTop := by
      have wa : a.left ≫ baseMap S = T.hom := Over.w a
      have wb : b.left ≫ baseMap S = T.hom := Over.w b
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, wa, wb]
    have := congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of S.k)).inv r)) hw
    simp only [CommRingCat.comp_apply] at this
    have hb : (baseMap S).appTop ((Scheme.ΓSpecIso (.of S.k)).inv r) =
        (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (algebraMap S.k (NodalRing S.k) r) := by
      rw [baseMap, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    rw [hb] at this
    exact this
  · cases i
    · exact hx
    · exact hy

/-- A global function on the coordinate axes pulled back along `g ≫ a` is its pullback along `a`
pulled back along `g`. -/
theorem comp_appTop_section {T T' : Over (Spec (.of S.k))} (g : T' ⟶ T) (a : T ⟶ axesOver S)
    (s : Γ(coordinateAxes S, ⊤)) :
    (g ≫ a).left.appTop s = g.left.appTop (a.left.appTop s) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The coordinate of the image of a point of the coordinate axes under the sum map is the sum
of its two coordinates. -/
theorem comp_coordinateSumMap_coord {T : Over (Spec (.of S.k))} (a : T ⟶ axesOver S) :
    (a ≫ coordinateSumMap S).left.appTop (AffineSpace.coord (Spec (.of S.k)) PUnit.unit) =
      a.left.appTop (xSection S) + a.left.appTop (ySection S) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change a.left.appTop ((AffineSpace.homOfVector _ _).appTop _) = _
  rw [AffineSpace.homOfVector_appTop_coord, map_add]

/-- The `x`-coordinate of a point composed with the swap is the `y`-coordinate of the point. -/
theorem comp_coordinateSwap_xSection {T : Scheme.{u}} (a : T ⟶ coordinateAxes S) :
    (a ≫ coordinateSwap S).appTop (xSection S) = a.appTop (ySection S) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinateSwap_appTop_xSection]

/-- The `y`-coordinate of a point composed with the swap is the `x`-coordinate of the point. -/
theorem comp_coordinateSwap_ySection {T : Scheme.{u}} (a : T ⟶ coordinateAxes S) :
    (a ≫ coordinateSwap S).appTop (ySection S) = a.appTop (xSection S) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinateSwap_appTop_ySection]

/-! ### The quotient as an algebraic space -/

section Site

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of S.k)))

/-- The coordinate axes as an object of a big fppf site containing `Spec k`. -/
noncomputable def axesChart : BigFppfOver B (Spec (.of S.k)) hS :=
  Over.mk (ObjectProperty.homMk (baseMap S) :
    B.obj (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (baseMap S) hS) ⟶ B.obj hS)

/-- The underlying scheme over `Spec k` of `axesChart S B hS` is the coordinate axes. -/
@[simp]
theorem axesChart_post : (Over.post B.inclusion).obj (axesChart S B hS) = axesOver S := rfl

/-- The underlying scheme of `axesChart S B hS` is affine. -/
instance isAffine_axesChart :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of S.k)) hS).obj (axesChart S B hS)) :=
  inferInstanceAs (IsAffine (Spec _))

variable [HasSheafify (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u)]

/-- **Stacks 0ENU.** The quotient `X = U/R` of the coordinate axes by the relation identifying
each point of the punctured axes with its image under the swap. -/
noncomputable abbrev quotientSpace : Sheaf (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u) :=
  Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
    (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)

/-- The projection `U ⟶ X` onto the quotient, on functors of points. -/
noncomputable abbrev quotientMap :
    Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (axesOver S) ⟶
      (quotientSpace S B hS).obj :=
  Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
    (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)

/-- **Stacks 0ENU.** The quotient `X = U/R` is an algebraic space over `k`, for every field
`k`. -/
theorem isAlgebraicSpace_quotientSpace :
    IsAlgebraicSpace B (Spec (.of S.k)) hS (quotientSpace S B hS).obj :=
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation (R := relationOver S)
      (U := (Over.post B.inclusion).obj (axesChart S B hS)) (relationPreRelation S) :=
    isEtaleEquivalenceRelation S
  Space.isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional B (Spec (.of S.k)) hS
    (axesChart S B hS) (relationPreRelation S)

/-- The morphism `X ⟶ 𝔸¹_k` descended from `(x, y) ↦ x + y`. -/
noncomputable def sumMap :
    (quotientSpace S B hS).obj ⟶
      Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
        (AffineLineInvolution.affineLine S.k) :=
  (quotientSumMap B S hS).1

/-- The descended sum map restricts to `(x, y) ↦ x + y` along the projection `U ⟶ X`. -/
theorem quotientMap_comp_sumMap :
    quotientMap S B hS ≫ sumMap S B hS =
      (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (coordinateSumMap S)) :=
  (quotientSumMap B S hS).2

/-- The descended sum map on a point of `X` coming from a `T`-point of `U`. -/
theorem sumMap_app_quotientMap (T : BigFppfOver B (Spec (.of S.k)) hS)
    (a : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ axesOver S) :
    (sumMap S B hS).app (Opposite.op T) ((quotientMap S B hS).app (Opposite.op T) a) =
      a ≫ coordinateSumMap S :=
  congrArg (fun α => α.app (Opposite.op T) a) (quotientMap_comp_sumMap S B hS)

end Site

end AlgebraicGeometry.CoordinateAxesQuotient

end
