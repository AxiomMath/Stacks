module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesFunctor

/-!
# The functor of quadruples of Stacks 084A on an arbitrary test object

In Situation 0849 the source defines the functor `F` of quadruples on a quasi-compact test scheme
`T` as the union over `d ≥ 1` of the classes of quadruples `(d, f : T → X, ℒ, ψ)`, and on an
arbitrary test scheme as the limit

`F(T) = lim_{V ⊆ T quasi-compact open} F(V)`.

Over a restriction datum `ρ` (`AlgebraicGeometry.Space.GradedAlgebraRestriction`) the union is
the presheaf `AlgebraicGeometry.Space.GradedAlgebraRestriction.functor`.  This file constructs
the limit, as the presheaf `AlgebraicGeometry.Space.GradedAlgebraRestriction.limFunctor` on the
big fppf site, and shows that on a quasi-compact test object it is the union.

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.LimPoint`: a point of `F(T)` for an arbitrary
  test object `T` — a `T`-point `f` of `X` together with a compatible family of classes of
  quadruples, one over every restriction of `f` to a test object with quasi-compact scheme mapping
  to `T`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.limFunctor`: the presheaf of these points.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.limEquiv`: on a test object whose scheme is
  quasi-compact, a point of the limit is a point of the union.

## Implementation notes

**The index of the limit.**  As in `AlgebraicGeometry.Scheme.QcExtension`, the limit is indexed
by all morphisms `W ⟶ T` out of test objects with quasi-compact scheme rather than by the
quasi-compact opens of `T` only, which makes the restriction along a morphism `T' ⟶ T` a
reindexing.  The quasi-compact opens of `T` are objects of the site
(`AlgebraicGeometry.Space.opensObject`) and every morphism out of a quasi-compact scheme factors
through one of them, so the two limits agree; it is that agreement which the comparison with the
relative homogeneous spectrum of Stacks 084B uses.

**The point of `X` is recorded.**  A family of points of `F` over the quasi-compact test objects
of `T` lies over a compatible family of points of `X`, and since `X` is a sheaf those glue to a
point of `X` over `T`, which is the source's morphism `F(T) ⟶ X(T)`.  Here the glued point is
part of the datum and the family is a family of points of the *fibres* over its restrictions:
that is the same set, because a point of `X` over `T` is determined by its restrictions to the
quasi-compact opens of `T`, and it spares the construction of the morphism to `X` the gluing.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {r : GradedAlgebraPoints B S hS X} (ρ : GradedAlgebraRestriction r)

/-- **A point of the functor of quadruples of Stacks 084A on an arbitrary test object `T`.**

A `T`-point `f` of `X` together with, for every morphism `w : W ⟶ T` out of a test object whose
scheme is quasi-compact, a point of the fibre of `F(W)` over the restricted point `w^*f` — a class
of quadruples `(d, w^*f, ℒ, ψ)` — compatibly with the restriction maps of `F`.  This is the limit
`lim F(V)` over the quasi-compact opens `V` of `T` by which the source defines `F(T)`, indexed by
all quasi-compact test objects over `T`. -/
structure LimPoint (T : BigFppfOver B S hS) where
  /-- The point of `X` the family lies over. -/
  point : yoneda.obj T ⟶ X
  /-- The point of the fibre of `F(W)` recorded at `w : W ⟶ T`. -/
  val (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (w : W ⟶ T) : GradedAlgebraPoints.F.fibre r W (yoneda.map w ≫ point)
  /-- The recorded points are compatible with the restriction maps of `F`. -/
  compat (W W' : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (hW' : CompactSpace ((BigFppfOver.toScheme B S hS).obj W')) (h : W' ⟶ W) (w : W ⟶ T) :
    ρ.fibreRestrict h (yoneda.map w ≫ point) (yoneda.map (h ≫ w) ≫ point) rfl (val W hW w) =
      val W' hW' (h ≫ w)

namespace LimPoint

variable {ρ}

/-- Two points of the limit are equal as soon as they lie over the same point of `X` and record
the same classes. -/
theorem ext' {T : BigFppfOver B S hS} {ξ η : LimPoint ρ T} (hp : ξ.point = η.point)
    (hv : ∀ (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
      (w : W ⟶ T), HEq (ξ.val W hW w) (η.val W hW w)) : ξ = η := by
  obtain ⟨p, v, c⟩ := ξ
  obtain ⟨p', v', c'⟩ := η
  obtain rfl : p = p' := hp
  obtain rfl : v = v' := funext fun W => funext fun hW => funext fun w => eq_of_heq (hv W hW w)
  rfl

/-- **The restriction of a point of the limit along a morphism of test objects**: the point of
`X` is restricted and the family is reindexed. -/
def restrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (ξ : LimPoint ρ T) : LimPoint ρ T' where
  point := yoneda.map τ ≫ ξ.point
  val W hW w := ξ.val W hW (w ≫ τ)
  compat W W' hW hW' h w := ξ.compat W W' hW hW' h (w ≫ τ)

/-- The point of `X` under a restriction is the restricted point. -/
@[simp] theorem restrict_point {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (ξ : LimPoint ρ T) :
    (ξ.restrict τ).point = yoneda.map τ ≫ ξ.point := rfl

/-- The class recorded by a restriction at `w` is the class recorded at `w ≫ τ`. -/
theorem restrict_val {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (ξ : LimPoint ρ T)
    (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (w : W ⟶ T') : (ξ.restrict τ).val W hW w = ξ.val W hW (w ≫ τ) := rfl

/-- Restricting along the identity changes nothing. -/
theorem restrict_id {T : BigFppfOver B S hS} (ξ : LimPoint ρ T) : ξ.restrict (𝟙 T) = ξ := rfl

/-- Restricting along a composite is restricting along the two factors in turn. -/
theorem restrict_comp {T T' T'' : BigFppfOver B S hS} (τ : T' ⟶ T) (τ' : T'' ⟶ T')
    (ξ : LimPoint ρ T) : ξ.restrict (τ' ≫ τ) = (ξ.restrict τ).restrict τ' := rfl

end LimPoint

/-- **Stacks 084A: the functor of quadruples on the big fppf site, for every test object**, its
value on `T` being the limit of the unions over the quasi-compact test objects over `T`. -/
def limFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj T := LimPoint ρ T.unop
  map τ := TypeCat.ofHom (LimPoint.restrict τ.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The value of `limFunctor` on `T` is the type of points of the limit over `T`. -/
@[simp] theorem limFunctor_obj (T : (BigFppfOver B S hS)ᵒᵖ) :
    ρ.limFunctor.obj T = LimPoint ρ T.unop := rfl

/-- The map of `limFunctor` along `τ` is restriction along `τ.unop`. -/
@[simp] theorem limFunctor_map {T T' : (BigFppfOver B S hS)ᵒᵖ} (τ : T ⟶ T')
    (ξ : LimPoint ρ T.unop) : ρ.limFunctor.map τ ξ = ξ.restrict τ.unop := rfl

/-! ### On a quasi-compact test object the limit is the union -/

/-- The point of the limit attached to a point of the union `F(T)`: its restrictions. -/
def toLimPoint {T : BigFppfOver B S hS} (ξ : r.F T) : LimPoint ρ T where
  point := GradedAlgebraPoints.F.point r ξ
  val _ _ w := (ρ.FRestrict w ξ).2
  compat _ _ _ _ h w := (ρ.fibreRestrict_comp w h ξ.1 ξ.2).symm

/-- **On a test object with quasi-compact scheme the limit is the union**: the identity of `T` is
a terminal object of the index, so a compatible family is its value there. -/
def limEquiv (T : BigFppfOver B S hS) (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    LimPoint ρ T ≃ r.F T where
  toFun ξ := ⟨ξ.point, ξ.val T hT (𝟙 T)⟩
  invFun ξ := ρ.toLimPoint ξ
  left_inv ξ := LimPoint.ext' rfl fun W hW w => heq_of_eq (ξ.compat T W hT hW w (𝟙 T))
  right_inv ξ := ρ.FRestrict_id ξ

/-- The identification of the limit with the union on a quasi-compact test object is natural. -/
theorem limEquiv_restrict {T T' : BigFppfOver B S hS}
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : CompactSpace ((BigFppfOver.toScheme B S hS).obj T')) (τ : T' ⟶ T)
    (ξ : LimPoint ρ T) :
    ρ.limEquiv T' hT' (ξ.restrict τ) = ρ.FRestrict τ (ρ.limEquiv T hT ξ) :=
  Sigma.ext rfl (heq_of_eq (ξ.compat T T' hT hT' τ (𝟙 T)).symm)

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
