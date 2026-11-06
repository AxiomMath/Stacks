module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria

/-!
# Morphisms of algebraic spaces with integral geometric fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. The *geometric fibres* of
`f` are the fibres `X ×_Y Spec(k)` over the geometric points `Spec(k) ⟶ Y` of `Y`, those whose
field `k` is algebraically closed, and `f` *has integral geometric fibres* when each of them is
an integral algebraic space (Stacks 0AD4).

The fibre over an arbitrary field-valued point `Spec(k) ⟶ Y` is then integral as well: the
fibre over the geometric point `Spec(k̄) ⟶ Spec(k) ⟶ Y` given by an algebraic closure is the
base change of the fibre over `Spec(k)` along `Spec(k̄) ⟶ Spec(k)`, and integrality descends
along that flat, surjective, quasi-compact morphism.

## Main definitions

* `AlgebraicGeometry.Space.HasIntegralGeometricFibres`: the geometric fibres of a morphism are
  integral.

## Main results

* `AlgebraicGeometry.Space.isIntegralSpace_fieldFibre_of_hasIntegralGeometricFibres`: if the
  geometric fibres of a morphism of algebraic spaces are integral, then so is its fibre over
  every field-valued point of the target.

## Implementation notes

The fibre over a field-valued point is `AlgebraicGeometry.Space.fieldFibre`, the presheaf
fibre product with the morphism represented by the point, and geometric points are
`AlgebraicGeometry.Space.GeometricPoint`. Geometric points range over the algebraically closed
fields whose spectra belong to the chosen big fppf site; this loses nothing, since the algebraic
closure of a field of the site belongs to the site
(`AlgebraicGeometry.Space.contains_specAlgebraicClosure`).

The three conditions of integrality descend separately along the comparison
`X ×_Y Spec(k̄) ⟶ X ×_Y Spec(k)`: reducedness along a flat surjective morphism (Stacks 06MI),
decency along a surjective quasi-compact morphism, and irreducibility of the space of points
along the continuous surjection it induces. Surjectivity on points is Stacks 03H4 together with
the fact that the spectrum of a field has a single point.

## References

* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 06MI](https://stacks.math.columbia.edu/tag/06MI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_integralGeometricFibres :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_integralGeometricFibres
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_integralGeometricFibres B S hS).has_limit _

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` *has integral geometric fibres* when
for every geometric point `ȳ : Spec(k) ⟶ Y`, with `k` algebraically closed, the fibre
`X ×_Y Spec(k)` is an integral algebraic space. -/
def HasIntegralGeometricFibres (f : X ⟶ Y) : Prop :=
  ∀ y : GeometricPoint B S hS Y, IsIntegralSpace B S hS (fieldFibre B S hS f y.val)

attribute [local instance] pointTopology in
/-- **The fibres over all field-valued points of a morphism with integral geometric fibres are
integral.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose geometric fibres
are integral. Then for every field-valued point `Spec(k) ⟶ Y` the fibre `X ×_Y Spec(k)` is an
integral algebraic space: it receives a flat, surjective, quasi-compact morphism from the
fibre over the geometric point `Spec(k̄) ⟶ Y`, `k̄` an algebraic closure of `k`, and
reducedness, decency and irreducibility descend along it. -/
theorem isIntegralSpace_fieldFibre_of_hasIntegralGeometricFibres
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : HasIntegralGeometricFibres B S hS f) (p : FieldValuedPoint B S hS Y) :
    IsIntegralSpace B S hS (fieldFibre B S hS f p) := by
  let k := p.carrier
  let K := AlgebraicClosure k
  have hK : B.Contains (Spec (.of K)) := contains_specAlgebraicClosure B k p.contained
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let U : BigFppfOver B S hS := Over.mk (⟨g ≫ p.toBase⟩ : B.obj hK ⟶ B.obj hS)
  let e : U ⟶ p.siteObject := Over.homMk (ObjectProperty.homMk g)
  -- the geometric point `Spec(k̄) ⟶ Spec(k) ⟶ Y`
  let q : FieldValuedPoint B S hS Y :=
    { carrier := K
      contained := hK
      toBase := g ≫ p.toBase
      value := Y.map e.op p.value }
  let y₀ : GeometricPoint B S hS Y := ⟨q, inferInstanceAs (IsAlgClosed K)⟩
  obtain ⟨hred, hdec, _⟩ := hf y₀
  let gp := yonedaEquiv.symm p.value
  let gq := yonedaEquiv.symm q.value
  have hcomp : yoneda.map e ≫ gp = gq := (yonedaEquiv_symm_map e.op p.value).symm
  -- the comparison `X ×_Y Spec(k̄) ⟶ X ×_Y Spec(k)` and its cartesian square
  let m : pullback f gq ⟶ pullback f gp :=
    pullback.lift (pullback.fst f gq) (pullback.snd f gq ≫ yoneda.map e)
      (by rw [Category.assoc, hcomp, pullback.condition])
  have sq : IsPullback m (pullback.snd f gq) (pullback.snd f gp) (yoneda.map e) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f gp)
    rw [pullback.lift_fst, hcomp]
    exact IsPullback.of_hasPullback f gq
  have hyp := isAlgebraicSpace_yoneda B S hS p.siteObject
  have hyq := isAlgebraicSpace_yoneda B S hS U
  have hPp : IsAlgebraicSpace B S hS (pullback f gp) :=
    isAlgebraicSpace_pullback B S hS f gp hX hyp hY
  have hPq : IsAlgebraicSpace B S hS (pullback f gq) :=
    isAlgebraicSpace_pullback B S hS f gq hX hyq hY
  -- `Spec(k̄) ⟶ Spec(k)` is flat and quasi-compact, hence so is its base change `m`
  have hflat_e : IsFlat B S hS (yoneda.map e) :=
    isFlat_yoneda_map B S hS e
      (inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  have hqc_e : IsQuasiCompact B S hS (yoneda.map e) :=
    quasiCompact_schemeMap_isQuasiCompact B S hS e
      (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  have hflat : IsFlat B S hS m :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_homMk B S hS hyq hPp hyp hPq sq.flip) hflat_e
  have hqc : IsQuasiCompact B S hS m := isQuasiCompact_of_isPullback B S hS sq.flip hqc_e
  -- `m` is surjective on points, the spectrum of `k` having a single point
  have hsurj : IsSurjective B S hS m := fun z =>
    (exists_points_of_isPullback B S hS sq z
      ((FieldValuedPoint.tautological B S hS q).class B S hS _)
      ((subsingleton_points_yoneda_siteObject B S hS p).elim _ _)).imp fun _ => And.left
  exact ⟨isReduced_of_flat_of_surjective B S hS hPq hPp m hflat hsurj hred,
    isDecentSpace_of_surjective_isQuasiCompact B S hS hPq hPp m hqc hsurj hdec,
    Function.Surjective.irreducibleSpace (continuous_pointsMap B S hS m) hsurj⟩

end AlgebraicGeometry.Space

end
