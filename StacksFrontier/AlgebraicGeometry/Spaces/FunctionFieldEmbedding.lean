module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.Homology.Tor.ChangeOfRings

/-!
# The coordinate-axes quotient and its sum map

Over a field `k`, let `U = Spec (k[x, y]/(xy))` be the union of the two coordinate axes and
let `R = U ⨿ (U ∖ {0})` map to `U ×_k U` by the diagonal on the first summand and by the
graph of the coordinate interchange on the second.  This file constructs that setup, the
morphism `U ⟶ 𝔸¹_k` given by `x + y`, and shows that it descends to the quotient sheaf
`X = U/R`.

## Main definitions

* `AlgebraicGeometry.CoordinateAxesQuotient.Setup` packages the ground field.
* `AlgebraicGeometry.CoordinateAxesQuotient.coordinateAxes` is `Spec (k[x, y]/(xy))` and
  `AlgebraicGeometry.CoordinateAxesQuotient.coordinateSwapIso` interchanges its two axes.
* `AlgebraicGeometry.CoordinateAxesQuotient.relationScheme` and
  `AlgebraicGeometry.CoordinateAxesQuotient.relationMap` are the relation and its map to
  `U ×_k U`, and `AlgebraicGeometry.CoordinateAxesQuotient.relationPreRelation` packages it
  as a pre-relation of schemes over `Spec k`.
* `AlgebraicGeometry.CoordinateAxesQuotient.coordinateSumMap` is `x + y : U ⟶ 𝔸¹_k`.
* `AlgebraicGeometry.CoordinateAxesQuotient.quotientSumMap` is its descent to the quotient
  sheaf, together with the equation characterising it.

## Main results

* `AlgebraicGeometry.CoordinateAxesQuotient.coordinateSumMap_invariant`: the coordinate sum is
  invariant under the relation.

## References

* [Stacks Project, Tag 0ENU](https://stacks.math.columbia.edu/tag/0ENU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CommRingCat
open CochainComplex.DerivedChangeOfRings

universe u

namespace AlgebraicGeometry

namespace CoordinateAxesQuotient

/-- The ground field for the coordinate-axes quotient construction. -/
structure Setup where
  /-- The ground field. -/
  k : Type u
  /-- The field structure on the ground field. -/
  field : Field k

/-- The ground field of a setup is a field. -/
instance (S : Setup.{u}) : Field S.k := S.field

/-- The automorphism of `k[x, y]` interchanging `x` and `y`. -/
noncomputable def swapPolynomialEquiv (S : Setup.{u}) :
    PolynomialRing S.k ≃ₐ[S.k] PolynomialRing S.k :=
  MvPolynomial.renameEquiv S.k (Equiv.swap false true)

/-- The automorphism of `k[x, y] / (xy)` induced by interchanging `x` and `y`. -/
noncomputable def swapRingEquiv (S : Setup.{u}) :
    NodalRing S.k ≃ₐ[S.k] NodalRing S.k :=
  Ideal.quotientEquivAlg (nodalRelationIdeal S.k) (nodalRelationIdeal S.k)
    (swapPolynomialEquiv S) (by
      simp [nodalRelationIdeal, xVariable, yVariable, swapPolynomialEquiv,
        Ideal.map_span, mul_comm])

/-- The union `U = Spec(k[x, y] / (xy))` of the coordinate axes. -/
noncomputable abbrev coordinateAxes (S : Setup.{u}) : Scheme.{u} :=
  Spec (.of (NodalRing S.k))

/-- The structure morphism `U ⟶ Spec k`. -/
noncomputable def baseMap (S : Setup.{u}) :
    coordinateAxes S ⟶ Spec (.of S.k) :=
  Spec.map (CommRingCat.ofHom (algebraMap S.k (NodalRing S.k)))

/-- The automorphism of `U` which interchanges its two coordinate axes. -/
noncomputable def coordinateSwapIso (S : Setup.{u}) :
    coordinateAxes S ≅ coordinateAxes S :=
  Scheme.Spec.mapIso (swapRingEquiv S).toCommRingCatIso.op

/-- The morphism underlying the automorphism interchanging the two coordinate axes. -/
noncomputable abbrev coordinateSwap (S : Setup.{u}) :
    coordinateAxes S ⟶ coordinateAxes S :=
  (coordinateSwapIso S).hom

/-- Evaluation at `(0, 0)` on `k[x, y]`. -/
noncomputable def originPolynomialMap (S : Setup.{u}) :
    PolynomialRing S.k →+* S.k :=
  MvPolynomial.eval₂Hom (RingHom.id S.k) 0

/-- Evaluation at the origin on `k[x, y] / (xy)`. -/
noncomputable def originRingMap (S : Setup.{u}) :
    NodalRing S.k →+* S.k :=
  Ideal.Quotient.lift (nodalRelationIdeal S.k) (originPolynomialMap S) (by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
        obtain rfl := hp
        simp [originPolynomialMap]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul a b _ hb => rw [smul_eq_mul, map_mul, hb, mul_zero])

/-- The origin `0_U` of the coordinate axes. -/
noncomputable def origin (S : Setup.{u}) : coordinateAxes S :=
  Spec.map (CommRingCat.ofHom (originRingMap S)) default

/-- The global section of `U` given by the first coordinate. -/
noncomputable def xSection (S : Setup.{u}) : Γ(coordinateAxes S, ⊤) :=
  (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (xClass S.k)

/-- The global section of `U` given by the second coordinate. -/
noncomputable def ySection (S : Setup.{u}) : Γ(coordinateAxes S, ⊤) :=
  (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (yClass S.k)

/-- The punctured coordinate axes `U \ {0_U}`, written as `D(x) ∪ D(y)`. -/
noncomputable def puncturedCoordinateAxes (S : Setup.{u}) :
    (coordinateAxes S).Opens :=
  (coordinateAxes S).basicOpen (xSection S) ⊔
    (coordinateAxes S).basicOpen (ySection S)

/-- The fibre product `U ×ₖ U`. -/
noncomputable abbrev selfProduct (S : Setup.{u}) : Scheme.{u} :=
  pullback (baseMap S) (baseMap S)

/-- The diagonal `U ⟶ U ×ₖ U`. -/
noncomputable def diagonal (S : Setup.{u}) :
    coordinateAxes S ⟶ selfProduct S :=
  pullback.diagonal (baseMap S)

/-- The coordinate interchange is a morphism over the ground field. -/
theorem coordinateSwap_comp_baseMap (S : Setup.{u}) :
    coordinateSwap S ≫ baseMap S = baseMap S := by
  dsimp [baseMap, coordinateSwap, coordinateSwapIso]
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp [swapRingEquiv, swapPolynomialEquiv]

/-- The graph `u ↦ (u, σ(u))` of the coordinate-swap automorphism. -/
noncomputable def twistedDiagonal (S : Setup.{u}) :
    coordinateAxes S ⟶ selfProduct S :=
  pullback.lift (𝟙 _) (coordinateSwap S) (by
    rw [Category.id_comp, coordinateSwap_comp_baseMap])

/-- The scheme `R = U ⨿ (U \ {0_U})` underlying the relation. -/
noncomputable abbrev relationScheme (S : Setup.{u}) : Scheme.{u} :=
  coordinateAxes S ⨿ puncturedCoordinateAxes S

/-- The map `R ⟶ U ×ₖ U`, equal to the diagonal on `U` and to the graph of the
coordinate swap on `U \ {0_U}`. -/
noncomputable def relationMap (S : Setup.{u}) :
    relationScheme S ⟶ selfProduct S :=
  coprod.desc (diagonal S)
    ((puncturedCoordinateAxes S).ι ≫ twistedDiagonal S)

/-- The first projection `R ⟶ U`. -/
noncomputable def relationLeft (S : Setup.{u}) :
    relationScheme S ⟶ coordinateAxes S :=
  relationMap S ≫ pullback.fst _ _

/-- The second projection `R ⟶ U`. -/
noncomputable def relationRight (S : Setup.{u}) :
    relationScheme S ⟶ coordinateAxes S :=
  relationMap S ≫ pullback.snd _ _

/-- The coordinate axes as a scheme over the ground field. -/
noncomputable abbrev axesOver (S : Setup.{u}) :
    Over (Spec (.of S.k)) := Over.mk (baseMap S)

/-- The two-component relation scheme over the ground field. -/
noncomputable abbrev relationOver (S : Setup.{u}) :
    Over (Spec (.of S.k)) := Over.mk (relationLeft S ≫ baseMap S)

/-- The first projection of the relation, as a morphism over the ground field. -/
noncomputable def relationLeftOver (S : Setup.{u}) : relationOver S ⟶ axesOver S :=
  Over.homMk (relationLeft S)

/-- The second projection of the relation, as a morphism over the ground field. -/
noncomputable def relationRightOver (S : Setup.{u}) : relationOver S ⟶ axesOver S :=
  Over.homMk (relationRight S) (by
    dsimp [relationRight, relationLeft]
    rw [Category.assoc, Category.assoc, pullback.condition])

/-- The underlying morphism of `relationLeftOver` is `relationLeft`. -/
@[simp]
theorem relationLeftOver_left (S : Setup.{u}) :
    (relationLeftOver S).left = relationLeft S := rfl

/-- The underlying morphism of `relationRightOver` is `relationRight`. -/
@[simp]
theorem relationRightOver_left (S : Setup.{u}) :
    (relationRightOver S).left = relationRight S := rfl

/-- The diagonal and twisted diagonal give a pre-relation on the coordinate axes. -/
noncomputable def relationPreRelation (S : Setup.{u}) :
    Stacks.Groupoids.PreRelation (relationOver S) (axesOver S) :=
  prod.lift (relationLeftOver S) (relationRightOver S)

/-- The target of `relationPreRelation` is the first projection `relationLeftOver`. -/
@[simp]
theorem relationPreRelation_target (S : Setup.{u}) :
    (relationPreRelation S).target = relationLeftOver S := by
  simp [relationPreRelation, Stacks.Groupoids.PreRelation.target]

/-- The source of `relationPreRelation` is the second projection `relationRightOver`. -/
@[simp]
theorem relationPreRelation_source (S : Setup.{u}) :
    (relationPreRelation S).source = relationRightOver S := by
  simp [relationPreRelation, Stacks.Groupoids.PreRelation.source]

/-! ### The coordinate-sum map -/

/-- The coordinate interchange is `Spec` of the ring automorphism `swapRingEquiv`. -/
theorem coordinateSwap_eq (S : Setup.{u}) :
    coordinateSwap S = Spec.map (swapRingEquiv S).toCommRingCatIso.hom := rfl

/-- Interchanging the coordinates sends the class of `x` to the class of `y`. -/
@[simp]
theorem swapRingEquiv_xClass (S : Setup.{u}) :
    swapRingEquiv S (xClass S.k) = yClass S.k := by
  simp [swapRingEquiv, xClass, yClass, nodalRingMap, xVariable, yVariable,
    swapPolynomialEquiv]

/-- Interchanging the coordinates sends the class of `y` to the class of `x`. -/
@[simp]
theorem swapRingEquiv_yClass (S : Setup.{u}) :
    swapRingEquiv S (yClass S.k) = xClass S.k := by
  simp [swapRingEquiv, xClass, yClass, nodalRingMap, xVariable, yVariable,
    swapPolynomialEquiv]

/-- The map `(x,y) ↦ x+y` from the coordinate axes to the affine line. -/
noncomputable def coordinateSumMap (S : Setup.{u}) :
    axesOver S ⟶ AffineLineInvolution.affineLine S.k :=
  Over.homMk
    (AffineSpace.homOfVector (baseMap S)
      (fun _ : PUnit.{u + 1} => xSection S + ySection S))
    (AffineSpace.homOfVector_over _ _)

/-- The coordinate interchange acts on global sections of `U` as `swapRingEquiv`. -/
private theorem coordinateSwap_appTop_ΓSpecIso_inv (S : Setup.{u}) (a : NodalRing S.k) :
    (coordinateSwap S).appTop ((Scheme.ΓSpecIso (.of (NodalRing S.k))).inv a) =
      (Scheme.ΓSpecIso (.of (NodalRing S.k))).inv (swapRingEquiv S a) := by
  rw [coordinateSwap_eq, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  rfl

/-- Pulling back along the coordinate interchange sends the section `x` to the section `y`. -/
theorem coordinateSwap_appTop_xSection (S : Setup.{u}) :
    (coordinateSwap S).appTop (xSection S) = ySection S := by
  rw [xSection, ySection, coordinateSwap_appTop_ΓSpecIso_inv, swapRingEquiv_xClass]

/-- Pulling back along the coordinate interchange sends the section `y` to the section `x`. -/
theorem coordinateSwap_appTop_ySection (S : Setup.{u}) :
    (coordinateSwap S).appTop (ySection S) = xSection S := by
  rw [xSection, ySection, coordinateSwap_appTop_ΓSpecIso_inv, swapRingEquiv_yClass]

/-- The coordinate interchange fixes the sum of the two coordinates. -/
theorem coordinateSwap_comp_coordinateSumMap (S : Setup.{u}) :
    coordinateSwap S ≫ (coordinateSumMap S).left = (coordinateSumMap S).left := by
  show coordinateSwap S ≫ AffineSpace.homOfVector _ _ = AffineSpace.homOfVector _ _
  rw [AffineSpace.comp_homOfVector, coordinateSwap_comp_baseMap]
  refine congrArg _ ?_
  funext _
  simp only [Function.comp_apply, map_add, coordinateSwap_appTop_xSection,
    coordinateSwap_appTop_ySection]
  exact add_comm _ _

/-! ### Invariance of the coordinate sum -/

/-- On the summand `U` of `R`, the first projection is the identity. -/
@[simp]
theorem inl_relationLeft (S : Setup.{u}) :
    coprod.inl ≫ relationLeft S = 𝟙 (coordinateAxes S) := by
  rw [relationLeft, ← Category.assoc, relationMap, coprod.inl_desc, diagonal,
    pullback.diagonal_fst]

/-- On the summand `U` of `R`, the second projection is the identity. -/
@[simp]
theorem inl_relationRight (S : Setup.{u}) :
    coprod.inl ≫ relationRight S = 𝟙 (coordinateAxes S) := by
  rw [relationRight, ← Category.assoc, relationMap, coprod.inl_desc, diagonal,
    pullback.diagonal_snd]

/-- On the summand `U \ {0_U}` of `R`, the first projection is the inclusion into `U`. -/
@[simp]
theorem inr_relationLeft (S : Setup.{u}) :
    coprod.inr ≫ relationLeft S = (puncturedCoordinateAxes S).ι := by
  rw [relationLeft, ← Category.assoc, relationMap, coprod.inr_desc, Category.assoc,
    twistedDiagonal, pullback.lift_fst, Category.comp_id]

/-- On the summand `U \ {0_U}` of `R`, the second projection is the inclusion into `U` followed by
the coordinate interchange. -/
@[simp]
theorem inr_relationRight (S : Setup.{u}) :
    coprod.inr ≫ relationRight S = (puncturedCoordinateAxes S).ι ≫ coordinateSwap S := by
  rw [relationRight, ← Category.assoc, relationMap, coprod.inr_desc, Category.assoc,
    twistedDiagonal, pullback.lift_snd]

/-- The coordinate-sum map is invariant under the relation: it has the same composite with the
source and the target of `relationPreRelation`. -/
@[stacks 0ENU "quotient_map_exists"]
theorem coordinateSumMap_invariant (S : Setup.{u}) :
    (relationPreRelation S).target ≫ coordinateSumMap S =
      (relationPreRelation S).source ≫ coordinateSumMap S := by
  rw [relationPreRelation_target, relationPreRelation_source]
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, Over.comp_left, relationLeftOver_left, relationRightOver_left]
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, inl_relationLeft, inl_relationRight]
  · rw [← Category.assoc, ← Category.assoc, inr_relationLeft, inr_relationRight,
      Category.assoc, coordinateSwap_comp_coordinateSumMap]

/-! ### Descent of the coordinate sum to the quotient sheaf -/

variable (B : BigFppfSite.{u}) (S : Setup.{u}) (hS : B.Contains (Spec (.of S.k)))

/-- The functor of points of the affine line over the ground field is a sheaf on the big
fppf site of that field. -/
theorem isSheaf_points_affineLine :
    Presheaf.IsSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
      (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
        (AffineLineInvolution.affineLine S.k)) :=
  BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (Spec (.of S.k)) hS
    (AffineLineInvolution.affineLine S.k)

/-- The functor of points of the affine line over the ground field, as a sheaf on the big
fppf site of that field. -/
noncomputable def pointsAffineLineSheaf :
    Sheaf (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u) :=
  ⟨Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
      (AffineLineInvolution.affineLine S.k),
    isSheaf_points_affineLine B S hS⟩

/-- The coordinate sum, read on the functors of points, identifies related points. -/
theorem sourceMap_comp_points_coordinateSumMap :
    Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion)
        (relationPreRelation S) ≫
      (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (coordinateSumMap S)) =
      Stacks.Groupoids.targetMap (Over.post (X := B.obj hS) B.inclusion)
        (relationPreRelation S) ≫
      (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (coordinateSumMap S)) := by
  rw [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap,
    ← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, ← yoneda.map_comp,
    ← yoneda.map_comp, coordinateSumMap_invariant]

/-- The morphism from the quotient sheaf to the affine line through which the coordinate-sum map
factors, together with the equation expressing that factorisation. -/
@[stacks 0ENU "quotient_map_exists"]
noncomputable def quotientSumMap
    [HasSheafify (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u)] :
    { f : (Stacks.Groupoids.quotientSheaf
          (BigFppfOver.topology B (Spec (.of S.k)) hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (relationPreRelation S)).obj ⟶
        Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
          (AffineLineInvolution.affineLine S.k) //
      Stacks.Groupoids.toQuotientSheaf
          (BigFppfOver.topology B (Spec (.of S.k)) hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (relationPreRelation S) ≫ f =
        (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map (coordinateSumMap S)) } :=
  ⟨(Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B (Spec (.of S.k)) hS)
      (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)
      (pointsAffineLineSheaf B S hS) _
      (sourceMap_comp_points_coordinateSumMap B S hS)).hom,
    Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc _ _ _ _ _ _⟩

end CoordinateAxesQuotient

end AlgebraicGeometry

end
