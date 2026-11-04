module

public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonCocone
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonFullyFaithfulStack
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FlatBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Uniqueness of cocones at flat base changes of a square of condition (RS*)

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` with representable
diagonal, and let `Q` be a commutative square of the site whose four corners are affine, whose
square of global sections is cartesian and whose second map is a thickening — a square of the
kind condition (RS*) of [Stacks Project, Tag 07Y8] quantifies over. For every flat morphism
`V ⟶ Q.Z` from an affine object, cocones over spans of `𝒳` at the base change of `Q` to `V` are
unique up to unique isomorphism: the base-changed square is again a thickening pushout
(`Deformation.Artin.isPushout_of_flat_baseChange`), at which the comparison functor is fully
faithful (`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal`).

## Main results

* `Deformation.Artin.isPushout_toScheme_baseChange_of_flat`
* `Deformation.Artin.hasUniqueSquareCocones_baseChange_of_flat`
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u v t

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- **A flat affine base change of a square of condition (RS*) is again a pushout of schemes.**
For a square `Q` of the site with affine corners, cartesian square of global sections and a
thickening as second map, and a flat morphism `h : V ⟶ Q.Z` from an affine object, the image in
schemes of the base change of `Q` along `h` is a pushout. -/
public theorem isPushout_toScheme_baseChange_of_flat (Q : BaseSquare (BigFppfOver B S hS))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.Z)]
    (hΓ : IsPullback ((BigFppfOver.toScheme B S hS).map Q.i).appTop
      ((BigFppfOver.toScheme B S hS).map Q.j).appTop
      ((BigFppfOver.toScheme B S hS).map Q.f).appTop
      ((BigFppfOver.toScheme B S hS).map Q.g).appTop)
    (hg : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map Q.g))
    {V : BigFppfOver B S hS} (h : V ⟶ Q.Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Flat ((BigFppfOver.toScheme B S hS).map h)] :
    IsPushout ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).f)
      ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).g)
      ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).i)
      ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).j) := by
  let T := BigFppfOver.toScheme B S hS
  let QB := Q.baseChange h
  let a := Q.baseChangeHom h
  have sY : IsPullback (T.map QB.i) (T.map a.aV) (T.map h) (T.map Q.i) :=
    (Q.isPullback_baseChange_i h).map T
  have sX' : IsPullback (T.map QB.j) (T.map a.aW) (T.map h) (T.map Q.j) :=
    (Q.isPullback_baseChange_j h).map T
  have sX : IsPullback (T.map QB.f) (T.map a.aU) (T.map a.aV) (T.map Q.f) :=
    (Q.isPullback_baseChange_f h).map T
  have sX'' : IsPullback (T.map QB.g) (T.map a.aU) (T.map a.aW) (T.map Q.g) :=
    (Q.isPullback_baseChange_g h).map T
  have hcomm : T.map QB.f ≫ T.map QB.i = T.map QB.g ≫ T.map QB.j := by
    rw [← T.map_comp, QB.w, T.map_comp]
  have : IsClosedImmersion (T.map Q.g) := hg.1
  exact isPushout_of_flat_baseChange (T.map Q.f) (T.map Q.g) (T.map Q.i) (T.map Q.j)
    (T.map h) (T.map QB.i) (T.map a.aV) (T.map QB.j) (T.map a.aW) (T.map QB.f) (T.map QB.g)
    (T.map a.aU) hΓ sY sX' sX sX'' hcomm

/-- **Uniqueness of cocones at a flat base change of a square of condition (RS*).** -/
public theorem hasUniqueSquareCocones_baseChange_of_flat
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳) (Q : BaseSquare (BigFppfOver B S hS))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.Z)]
    (hΓ : IsPullback ((BigFppfOver.toScheme B S hS).map Q.i).appTop
      ((BigFppfOver.toScheme B S hS).map Q.j).appTop
      ((BigFppfOver.toScheme B S hS).map Q.f).appTop
      ((BigFppfOver.toScheme B S hS).map Q.g).appTop)
    (hg : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map Q.g))
    {V : BigFppfOver B S hS} (h : V ⟶ Q.Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Flat ((BigFppfOver.toScheme B S hS).map h)] :
    HasUniqueSquareCocones 𝒳.val.p (Q.baseChange h).f (Q.baseChange h).g (Q.baseChange h).i
      (Q.baseChange h).j := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let T := BigFppfOver.toScheme B S hS
  let QB := Q.baseChange h
  let a := Q.baseChangeHom h
  have sY : IsPullback (T.map QB.i) (T.map a.aV) (T.map h) (T.map Q.i) :=
    (Q.isPullback_baseChange_i h).map T
  have sX : IsPullback (T.map QB.f) (T.map a.aU) (T.map a.aV) (T.map Q.f) :=
    (Q.isPullback_baseChange_f h).map T
  have sX'' : IsPullback (T.map QB.g) (T.map a.aU) (T.map a.aW) (T.map Q.g) :=
    (Q.isPullback_baseChange_g h).map T
  have : IsAffine (T.obj QB.V) := IsAffine.of_isPullback sY
  have : IsAffine (T.obj QB.U) := IsAffine.of_isPullback sX
  have hthick : Stacks.Thickenings.IsThickening (T.map QB.g) :=
    Stacks.Thickenings.isThickening_of_isPullback sX'' hg
  exact hasUniqueSquareCocones_of_fullyFaithful 𝒳.isFiberedInGroupoids (chosenPullbacks _)
    QB.f QB.g QB.i QB.j QB.w
    (fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal B S hS 𝒳 hdiag QB.g QB.f
      QB.j QB.i QB.w.symm hthick (isPushout_toScheme_baseChange_of_flat B S hS Q hΓ hg h).flip)

end Deformation.Artin
