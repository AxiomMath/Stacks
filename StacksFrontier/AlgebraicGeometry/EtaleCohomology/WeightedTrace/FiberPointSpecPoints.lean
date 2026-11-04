module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk

/-!
# Points of a geometric fibre as points of the base change

Let `f : X ⟶ Y` be a morphism of a big étale site, let `s̄` be a geometric point of `Y`, let `V`
be an object of the small étale site of `Y` and let `ū` be a lift of `s̄` to `V`. A point of the
geometric fibre of `f` above `s̄` is a lift of `s̄` through `f`, and the universal property of the
fibre product turns such a lift into a morphism `s̄ ⟶ X_V = V ×_Y X` lying over `ū`. This file
records that the assignment is a bijection: the points of the geometric fibre are exactly the
`s̄`-points of `X_V` over `ū`, with inverse given by the second projection of the fibre product.

The source of a geometric point is the spectrum of a field, so its space is a single point; a
morphism out of it whose image lies in a Zariski open therefore factors uniquely through that
open. Combining the two facts describes the points of the geometric fibre which lift into a
chosen open of `X_V` as the `s̄`-points of that open over `ū`. Applied to the canonical open
attached to a support finite over `V`, this is the description of `HasFiberLift` used when
counting the points of the geometric fibre that a supported section sees.

## Main definitions

* `AlgebraicGeometry.SmallEtale.openPointLift` — the factorisation of a morphism out of the
  source of a geometric point through a Zariski open containing its image point.
* `AlgebraicGeometry.SmallEtale.fiberPointLiftEquiv` — points of the geometric fibre are the
  `s̄`-points of the base change `X_V` over the chosen lift of `s̄` to `V`.
* `AlgebraicGeometry.SmallEtale.fiberPointLiftOpenEquiv` — the same bijection restricted to a
  Zariski open of `X_V`.
* `AlgebraicGeometry.SmallEtale.fiberPointHasFiberLiftEquiv` — the restricted bijection at the
  canonical open of a support finite over `V`, which is the `HasFiberLift` phrasing.

## Main results

* `AlgebraicGeometry.SmallEtale.fiberPointLiftEquiv_apply` and
  `AlgebraicGeometry.SmallEtale.fiberPointLiftEquiv_symm_apply` compute the bijection and its
  inverse: the first is `AlgebraicGeometry.SmallEtale.fiberPointLift`, the second is composition
  with the second projection of the fibre product.
* `AlgebraicGeometry.SmallEtale.fiberPointLift_symm_apply` — the lift attached to the point of
  the geometric fibre produced by a point of `X_V` is that point.
* `AlgebraicGeometry.SmallEtale.fiberPointLiftOpenEquiv_apply_comp_ι` and
  `AlgebraicGeometry.SmallEtale.fiberPointHasFiberLiftEquiv_apply_comp_ι` — the restricted
  bijections are the unrestricted one followed by the open immersion.

## Implementation notes

Both round trips of `AlgebraicGeometry.SmallEtale.fiberPointLiftEquiv` are instances of the
uniqueness half of the universal property of the fibre product, applied to the square
`(IsPullback.of_hasPullback V.obj.hom f).map B.inclusion` that defines
`AlgebraicGeometry.SmallEtale.fiberPointLift`. The open version adds nothing beyond the unique
factorisation through an open immersion, whose uniqueness is monomorphy of the inclusion, so it
is obtained from the unrestricted bijection rather than rebuilt.

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section OpenPointLift

variable {S : Scheme.{u}} (t : GeometricPoint S) {Z : Scheme.{u}} (W : Z.Opens)
  (q : t.source ⟶ Z) (hq : q.base default ∈ (W : Set Z))

/-- The factorisation through a Zariski open of a morphism out of the source of a geometric
point whose image point lies in that open. The source is the spectrum of a field, so its space
is a single point and the containment of the whole image in the open follows from that of the
single point. -/
public def openPointLift : t.source ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι q (by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default, Scheme.Opens.range_ι]
    exact hq)

/-- The factorisation through a Zariski open composed with the open immersion is the original
morphism. -/
@[simp]
public theorem openPointLift_comp_ι : openPointLift t W q hq ≫ W.ι = q :=
  IsOpenImmersion.lift_fac _ _ _

end OpenPointLift

section FiberPointSpecPoints

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)
  (V : SmallEtale B Y.obj Y.property)
  (u : (geometricPointFiber B Y.obj Y.property s).obj V)

/-- The points of the geometric fibre of `f` above `s̄` are the `s̄`-points of the base change
`X_V = V ×_Y X` lying over the chosen lift `ū` of `s̄` to `V`. The bijection sends a point of the
geometric fibre to the lift `AlgebraicGeometry.SmallEtale.fiberPointLift` given by the universal
property of the fibre product, and back along the second projection. -/
public def fiberPointLiftEquiv :
    GeometricFiberPoint B f s ≃
      {q : s.source ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) //
        q ≫ B.inclusion.map (pullback.fst V.obj.hom f) = u.1} where
  toFun x := ⟨fiberPointLift B f s V u x, fiberPointLift_comp_fst B f s V u x⟩
  invFun q := ⟨q.1 ≫ B.inclusion.map (pullback.snd V.obj.hom f), by
    have hsq : IsPullback (B.inclusion.map (pullback.fst V.obj.hom f))
        (B.inclusion.map (pullback.snd V.obj.hom f)) (B.inclusion.map V.obj.hom)
        (B.inclusion.map f) := (IsPullback.of_hasPullback V.obj.hom f).map B.inclusion
    exact (Category.assoc _ _ _).trans <| (congrArg (q.1 ≫ ·) hsq.w.symm).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) q.2).trans u.2⟩
  left_inv x := Subtype.ext (fiberPointLift_comp_snd B f s V u x)
  right_inv q := Subtype.ext
    (((IsPullback.of_hasPullback V.obj.hom f).map B.inclusion).hom_ext
      ((fiberPointLift_comp_fst B f s V u _).trans q.2.symm)
      (fiberPointLift_comp_snd B f s V u _))

/-- The bijection with the `s̄`-points of the base change is the lift given by the universal
property of the fibre product. -/
public theorem fiberPointLiftEquiv_apply (x : GeometricFiberPoint B f s) :
    (fiberPointLiftEquiv B f s V u x).1 = fiberPointLift B f s V u x :=
  rfl

/-- The inverse of the bijection with the `s̄`-points of the base change is composition with the
second projection of the fibre product. -/
public theorem fiberPointLiftEquiv_symm_apply
    (q : {q : s.source ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) //
      q ≫ B.inclusion.map (pullback.fst V.obj.hom f) = u.1}) :
    ((fiberPointLiftEquiv B f s V u).symm q).1 =
      q.1 ≫ B.inclusion.map (pullback.snd V.obj.hom f) :=
  rfl

/-- The lift of the point of the geometric fibre attached to an `s̄`-point of the base change is
that `s̄`-point. -/
public theorem fiberPointLift_symm_apply
    (q : {q : s.source ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) //
      q ≫ B.inclusion.map (pullback.fst V.obj.hom f) = u.1}) :
    fiberPointLift B f s V u ((fiberPointLiftEquiv B f s V u).symm q) = q.1 := by
  rw [← fiberPointLiftEquiv_apply B f s V u ((fiberPointLiftEquiv B f s V u).symm q),
    Equiv.apply_symm_apply]

/-- The points of the geometric fibre whose lift to the base change `X_V` meets a Zariski open
`W` of `X_V` are the `s̄`-points of `W` lying over the chosen lift `ū` of `s̄` to `V`. -/
public def fiberPointLiftOpenEquiv
    (W : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens) :
    {x : GeometricFiberPoint B f s // (fiberPointLift B f s V u x).base default ∈
        (W : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)))} ≃
      {q : s.source ⟶ W.toScheme //
        q ≫ W.ι ≫ B.inclusion.map (pullback.fst V.obj.hom f) = u.1} where
  toFun x := ⟨openPointLift s W (fiberPointLift B f s V u x.1) x.2, by
    rw [← Category.assoc, openPointLift_comp_ι, fiberPointLift_comp_fst]⟩
  invFun q :=
    ⟨(fiberPointLiftEquiv B f s V u).symm ⟨q.1 ≫ W.ι, (Category.assoc _ _ _).trans q.2⟩, by
      rw [fiberPointLift_symm_apply, ← Scheme.Opens.range_ι]
      exact Set.mem_range_self _⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    change (openPointLift s W (fiberPointLift B f s V u x.1) x.2 ≫ W.ι) ≫
      B.inclusion.map (pullback.snd V.obj.hom f) = x.1.1
    rw [openPointLift_comp_ι, fiberPointLift_comp_snd]
  right_inv q := by
    refine Subtype.ext ?_
    rw [← cancel_mono W.ι, openPointLift_comp_ι, fiberPointLift_symm_apply]

/-- The bijection with the `s̄`-points of a Zariski open of the base change is the unrestricted
bijection followed by the open immersion. -/
public theorem fiberPointLiftOpenEquiv_apply_comp_ι
    (W : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens)
    (x : {x : GeometricFiberPoint B f s // (fiberPointLift B f s V u x).base default ∈
      (W : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)))}) :
    (fiberPointLiftOpenEquiv B f s V u W x).1 ≫ W.ι = fiberPointLift B f s V u x.1 :=
  openPointLift_comp_ι s W (fiberPointLift B f s V u x.1) x.2

/-- The points of the geometric fibre lifting into the canonical open of a support finite over
`V` are the `s̄`-points of that open lying over the chosen lift `ū` of `s̄` to `V`. -/
public def fiberPointHasFiberLiftEquiv (E : FiniteSupport B f V) :
    {x : GeometricFiberPoint B f s // HasFiberLift B f s V u E x} ≃
      {q : s.source ⟶ (finiteSupportOpen B f V E).toScheme //
        q ≫ (finiteSupportOpen B f V E).ι ≫ B.inclusion.map (pullback.fst V.obj.hom f) = u.1} :=
  fiberPointLiftOpenEquiv B f s V u (finiteSupportOpen B f V E)

/-- The bijection with the `s̄`-points of the canonical open of a support finite over `V` is the
unrestricted bijection followed by the open immersion. -/
public theorem fiberPointHasFiberLiftEquiv_apply_comp_ι (E : FiniteSupport B f V)
    (x : {x : GeometricFiberPoint B f s // HasFiberLift B f s V u E x}) :
    (fiberPointHasFiberLiftEquiv B f s V u E x).1 ≫ (finiteSupportOpen B f V E).ι =
      fiberPointLift B f s V u x.1 :=
  fiberPointLiftOpenEquiv_apply_comp_ι B f s V u (finiteSupportOpen B f V E) x

end FiberPointSpecPoints

end AlgebraicGeometry.SmallEtale

end
