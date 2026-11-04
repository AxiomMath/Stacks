module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueFieldDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeMonotone

/-!
# The generic point, the δ-dimension and the degree of an integral closed image

Let `f : X ⟶ Y` be a morphism of good algebraic spaces over the fixed base of the theory of
cycles and let `Z ⊂ X` be an integral closed subspace, with integral closed image `Z' ⊂ Y`.
The generic point of `Z'` is the image of the generic point of `Z`; consequently the
δ-dimension of `Z'` is at most that of `Z`, taking the integral closed image is functorial in
`f`, and the degree of the residue field extension of `Z` over `Z'` — the degree `deg(Z/Z')` of
Spaces over Fields, read at the generic points — is multiplicative along a composite.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.degreeOverClosureImage`: the degree of an
  integral closed subspace over its integral closed image.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.isGenericPoint_pointsMap_ambientGenericPoint`:
  the image of the generic point is a generic point of the integral closed image.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_closureImage_le`: the
  δ-dimension of the integral closed image is at most the δ-dimension of the subspace.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_closureImage`: taking the
  integral closed image is functorial.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.degreeOverClosureImage_comp`: degrees over
  integral closed images multiply along a composite.

## Implementation notes

The degree `deg(Z/Z')` is formed as the degree of the residue field extension of `f` itself at
the generic point of `|Z|`, `AlgebraicGeometry.Space.residueDegree`, rather than inside `Z` and
`Z'`: the residue field of an integral closed subspace at a point is the residue field of the
ambient space at the image of that point, the inclusion being a monomorphism, so the two readings
agree, and this one needs no morphism `Z ⟶ Z'` as data. The existence of such a morphism is
Stacks 0EEG, an existential, so taking it as data would require a choice.

The δ-dimension inequality is the only place where the base enters. The two generic points have
the same image in the base, because `f` is a morphism over the base, so the inequality is exactly
the monotonicity of the relative transcendence degree,
`AlgebraicGeometry.Space.inducedDimensionValue_le_of_comp`. It is an inequality and not an
equality: the δ-dimension drops by the transcendence degree of the residue field extension.

## References

* [Stacks Project, Tag 030H](https://stacks.math.columbia.edu/tag/030H)
* [Stacks Project, Tag 0AD6](https://stacks.math.columbia.edu/tag/0AD6)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENH](https://stacks.math.columbia.edu/tag/0ENH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section OverBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image of the generic point of an integral closed subspace `W` is a generic point of the
point set of the integral closed image of `W`: that point set is the closure of the image of
`|W|`, and `|W|` is the closure of the generic point. -/
theorem IntegralClosedSubspace.isGenericPoint_pointsMap_ambientGenericPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y) (W : IntegralClosedSubspace B S hS X) :
    IsGenericPoint (pointsMap B S hS X f (W.ambientGenericPoint B S hS))
      (subspacePointSet B S hS Y
        (IntegralClosedSubspace.closureImage B S hS hY hYdec f W).subspace) := by
  have hW := IntegralClosedSubspace.isGenericPoint_ambientGenericPoint B S hS hX W
  change closure _ = _
  rw [IntegralClosedSubspace.subspacePointSet_closureImage B S hS hY hYdec f W, ← hW,
    ← Set.image_singleton, closure_image_closure (continuous_pointsMap B S hS f)]

/-- Taking the integral closed image is functorial: the integral closed image under `g` of the
integral closed image under `f` is the integral closed image under `f ≫ g`. On point sets this
is that the closure of the image of a closure is the closure of the image. -/
theorem IntegralClosedSubspace.closureImage_closureImage
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hZdec : IsDecentSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : IntegralClosedSubspace B S hS X) :
    IntegralClosedSubspace.closureImage B S hS hZ hZdec g
        (IntegralClosedSubspace.closureImage B S hS hY hYdec f W) =
      IntegralClosedSubspace.closureImage B S hS hZ hZdec (f ≫ g) W := by
  refine injective_integralClosedSubspaceSupport B S hS hZ (IrreducibleCloseds.ext ?_)
  calc subspacePointSet B S hS Z
          (IntegralClosedSubspace.closureImage B S hS hZ hZdec g
            (IntegralClosedSubspace.closureImage B S hS hY hYdec f W)).subspace
      = closure (pointsMap B S hS Y g ''
          closure (pointsMap B S hS X f '' subspacePointSet B S hS X W.subspace)) := by
        rw [IntegralClosedSubspace.subspacePointSet_closureImage B S hS hZ hZdec g,
          IntegralClosedSubspace.subspacePointSet_closureImage B S hS hY hYdec f W]
    _ = closure (pointsMap B S hS Y g ''
          (pointsMap B S hS X f '' subspacePointSet B S hS X W.subspace)) :=
        closure_image_closure (continuous_pointsMap B S hS g)
    _ = closure ((pointsMap B S hS Y g ∘ pointsMap B S hS X f) ''
          subspacePointSet B S hS X W.subspace) := by rw [Set.image_comp]
    _ = closure (pointsMap B S hS X (f ≫ g) '' subspacePointSet B S hS X W.subspace) := by
        rw [← pointsMap_comp]
    _ = subspacePointSet B S hS Z
          (IntegralClosedSubspace.closureImage B S hS hZ hZdec (f ≫ g) W).subspace :=
        (IntegralClosedSubspace.subspacePointSet_closureImage B S hS hZ hZdec (f ≫ g) W).symm

/-- **The degree of an integral closed subspace over its integral closed image.** This is the
degree `deg(W/W')` of Spaces over Fields, Definition 0AD6: the degree of the extension of the
residue field at the generic point of `W'` by the residue field at the generic point of `W`. -/
noncomputable def IntegralClosedSubspace.degreeOverClosureImage
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y) (W : IntegralClosedSubspace B S hS X) : ℕ :=
  residueDegree B S hS X Y hY hXdec hYdec f (W.ambientGenericPoint B S hS)

/-- Degrees over integral closed images multiply along a composite: the three generic points
form a tower of residue fields, and degrees of field extensions multiply in a tower. -/
theorem IntegralClosedSubspace.degreeOverClosureImage_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (hZdec : IsDecentSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : IntegralClosedSubspace B S hS X) :
    IntegralClosedSubspace.degreeOverClosureImage B S hS hZ hXdec hZdec (f ≫ g) W =
      IntegralClosedSubspace.degreeOverClosureImage B S hS hZ hYdec hZdec g
          (IntegralClosedSubspace.closureImage B S hS hY hYdec f W) *
        IntegralClosedSubspace.degreeOverClosureImage B S hS hY hXdec hYdec f W := by
  have hagp : (IntegralClosedSubspace.closureImage B S hS hY hYdec f W).ambientGenericPoint
        B S hS = pointsMap B S hS X f (W.ambientGenericPoint B S hS) :=
    (eq_pointsMap_genericPoint_of_isGenericPoint B S hS hY _ _
      (IntegralClosedSubspace.isGenericPoint_pointsMap_ambientGenericPoint B S hS hX hY hYdec
        f W)).symm
  rw [IntegralClosedSubspace.degreeOverClosureImage,
    IntegralClosedSubspace.degreeOverClosureImage,
    IntegralClosedSubspace.degreeOverClosureImage, hagp,
    residueDegree_comp B S hS X Y Z hY hZ hXdec hYdec hZdec f g]

end OverBase

section Situation

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The δ-dimension of the integral closed image of an integral closed subspace is at most the
δ-dimension of that subspace. The two generic points have the same image in the base, so the
only difference is the relative transcendence degree, which can only grow upwards. -/
theorem IntegralClosedSubspace.deltaDimension_closureImage_le (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY) f W) ≤ deltaDimension D sX W := by
  subst hfB
  rw [deltaDimension_eq_of_isGenericPoint D sY hY.1 _
    (pointsMap D.site D.base D.base_mem X f (W.ambientGenericPoint D.site D.base D.base_mem))
    (IntegralClosedSubspace.isGenericPoint_pointsMap_ambientGenericPoint D.site D.base D.base_mem
      hX.1 hY.1 (isDecentSpace_of_isGood D sY hY) f W)]
  exact inducedDimensionValue_le_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace
    D.delta.toFun f sY hX.2.2 hY.2.2 (W.ambientGenericPoint D.site D.base D.base_mem)

end Situation

end AlgebraicGeometry.Space

end
