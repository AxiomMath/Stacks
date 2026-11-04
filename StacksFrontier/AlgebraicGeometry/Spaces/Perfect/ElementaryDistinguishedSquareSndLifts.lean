module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareLiftCounts
import StacksCore.Tactic.StacksAttribute

/-!
# Lifts along the second projection of an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V` be its intersection.  The second projection `P ⟶ V` is the base
change of the open immersion `U ⊆ X` along `j_V`, so it is again an open immersion; concretely, a
geometric point of `V` lifts to `P` exactly when its image in `X` lies in `U`, and then uniquely.

This is the count that makes the comparison `j_{P!}(F|_P) ⟶ j_{V!}(F|_V)` of the square
invertible on the stalk at a geometric point of `U`: by Equation 08GU that stalk is a direct sum
over the lifts of the point to `V`, and each lift of a point of `U` lifts uniquely to `P`.

## Main results

* `AlgebraicGeometry.Space.isPullback_edsInter_app`: the cartesian square of the elementary
  distinguished square is cartesian on sections over every object of the big site, fibre
  products of algebraic spaces being presheaf fibre products and evaluation preserving limits.
* `AlgebraicGeometry.Space.unique_geometricPointLift_edsSnd_of_mem`: a geometric point of `V`
  whose image in `X` lies in the open subspace has exactly one lift to the intersection.
* `AlgebraicGeometry.Space.geometricPointMap_liftGeometricPoint`: the image of the geometric
  point attached to a lift is the point that was lifted.

## Implementation notes

Uniqueness and existence are both read off the cartesian square of *sets* obtained by evaluating
the cartesian square of presheaves at the field spectrum carried by the point.  Uniqueness is
`CategoryTheory.IsPullback.hom_ext` applied to the two maps out of a one-point set determined by
two lifts, together with the injectivity of the open immersion on sections; existence is
`CategoryTheory.IsPullback.lift` applied to the one-point set, the lift to the open subspace
supplied by the hypothesis and the point itself.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The image of the geometric point attached to a lift is the point that was lifted.**  The
two differ only in the section defining them, and the defining property of a lift says those
sections agree. -/
theorem geometricPointMap_liftGeometricPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {x : GeometricPoint B S hS Y.1} (t : GeometricPointLift B S hS f.hom x) :
    geometricPointMap f.hom (liftGeometricPoint B S hS f t) = x :=
  congrArg (fun v : Y.1.obj (op (x.val.siteObject B S hS Y.1)) =>
    (⟨{ carrier := x.val.carrier
        field := x.val.field
        contained := x.val.contained
        toBase := x.val.toBase
        value := v }, x.2⟩ : GeometricPoint B S hS Y.1)) t.2

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The sections of the intersection of an elementary distinguished square over an object of
the big site are the pairs of a section of the open subspace and a section of the étale
algebraic space with the same image, the intersection being the presheaf fibre product. -/
def edsInterAtEquiv (T : (BigFppfOver B S hS)ᵒᵖ) :
    (edsInter B S hS hsq).1.obj T ≃
      FiberBaseChange.Obj ((edsOpenHom B S hS hsq).hom.app T)
        ((edsEtaleHom B S hS hsq).hom.app T) :=
  fiberProductAtEquiv (edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq) T

/-- The first component of a section of the intersection is its image in the open subspace. -/
theorem edsInterAtEquiv_fst (T : (BigFppfOver B S hS)ᵒᵖ) (p : (edsInter B S hS hsq).1.obj T) :
    (edsInterAtEquiv B S hS hsq T p).val.1 = (edsFst B S hS hsq).hom.app T p :=
  fiberProductAtEquiv_fst (edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq) T p

/-- The second component of a section of the intersection is its image in the étale algebraic
space. -/
theorem edsInterAtEquiv_snd (T : (BigFppfOver B S hS)ᵒᵖ) (p : (edsInter B S hS hsq).1.obj T) :
    (edsInterAtEquiv B S hS hsq T p).val.2 = (edsSnd B S hS hsq).hom.app T p :=
  fiberProductAtEquiv_snd (edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq) T p

/-- A geometric point of the étale algebraic space of an elementary distinguished square has at
most one lift to the intersection, the open immersion being injective on sections. -/
theorem subsingleton_geometricPointLift_edsSnd
    (y : GeometricPoint B S hS (edsEtale B S hS hsq).1) :
    Subsingleton (GeometricPointLift B S hS (edsSnd B S hS hsq).hom y) := by
  have hinj : Function.Injective ((edsOpenHom B S hS hsq).hom.app
      (op (y.val.siteObject B S hS (edsEtale B S hS hsq).1))) := by
    rw [← mono_iff_injective]
    exact (NatTrans.mono_iff_mono_app Uo.ι).1 inferInstance _
  refine ⟨fun p₁ p₂ => Subtype.ext ?_⟩
  refine (edsInterAtEquiv B S hS hsq
    (op (y.val.siteObject B S hS (edsEtale B S hS hsq).1))).injective (Subtype.ext ?_)
  have hsnd : (edsInterAtEquiv B S hS hsq _ p₁.1).val.2 =
      (edsInterAtEquiv B S hS hsq _ p₂.1).val.2 := by
    rw [edsInterAtEquiv_snd, edsInterAtEquiv_snd, p₁.2, p₂.2]
  have hfst : (edsInterAtEquiv B S hS hsq _ p₁.1).val.1 =
      (edsInterAtEquiv B S hS hsq _ p₂.1).val.1 := by
    refine hinj ?_
    rw [(edsInterAtEquiv B S hS hsq _ p₁.1).2, (edsInterAtEquiv B S hS hsq _ p₂.1).2, hsnd]
  exact Prod.ext hfst hsnd

/-- **A geometric point of the étale algebraic space of an elementary distinguished square whose
image lies in the open subspace has exactly one lift to the intersection.** -/
@[instance_reducible]
def unique_geometricPointLift_edsSnd_of_mem
    (y : GeometricPoint B S hS (edsEtale B S hS hsq).1)
    (hy : (geometricPointMap (edsEtaleHom B S hS hsq).hom y).image ∈
      Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    Unique (GeometricPointLift B S hS (edsSnd B S hS hsq).hom y) := by
  haveI := subsingleton_geometricPointLift_edsSnd B S hS hsq y
  have hne := (nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 Uo
    hsq.isOpenSubspace (geometricPointMap (edsEtaleHom B S hS hsq).hom y)).2 hy
  refine uniqueOfSubsingleton
    (⟨(edsInterAtEquiv B S hS hsq
        (op (y.val.siteObject B S hS (edsEtale B S hS hsq).1))).symm
        ⟨(hne.some.1, y.val.value), hne.some.2⟩, ?_⟩ :
      GeometricPointLift B S hS (edsSnd B S hS hsq).hom y)
  rw [← edsInterAtEquiv_snd, Equiv.apply_symm_apply]

end Square

end AlgebraicGeometry.Space

end
