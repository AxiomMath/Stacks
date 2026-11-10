module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Scheme.ClopenIdempotent
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# The idempotent global function of a clopen set of points

Let `F` be an algebraic space over a scheme `S` and `T` a clopen subset of its space of points
`|F|`.  On every étale chart `U` of `F` the points of the chart scheme lying over `T` form a
clopen subset, hence carry the idempotent regular function which is `1` there and `0` elsewhere
(`AlgebraicGeometry.Scheme.clopenIdempotent`).  These idempotents are compatible with the
morphisms of charts, because pullback of the idempotent of a clopen set is the idempotent of the
preimage, so they form a global regular function of `F`, idempotent and with support `T`.

This is the converse of `AlgebraicGeometry.Space.isClopen_sectionSupport`.  It is what turns
the computation `H⁰(X, 𝒪_X) = k` of Stacks 0D23 into connectedness information.

The file also records that an algebraic space with a nontrivial ring of global functions has a
point.

## Main definitions

* `AlgebraicGeometry.Space.chartClopenPart`: the part of an étale chart lying over a set of
  points.
* `AlgebraicGeometry.Space.clopenGlobalFunction`: the idempotent global function of a clopen set
  of points.

## Main results

* `AlgebraicGeometry.Space.isIdempotentElem_clopenGlobalFunction`: it is idempotent.
* `AlgebraicGeometry.Space.sectionSupport_clopenGlobalFunction`: its support is the clopen set.
* `AlgebraicGeometry.Space.nonempty_points_of_nontrivial_globalFunctions`: an algebraic space
  whose global functions form a nontrivial ring has a point.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The part of the scheme of an étale chart `U` of `F` lying over a set `T` of points of `F`:
the scheme points whose point of `F` lies in `T`. -/
def chartClopenPart (T : Set (points B S hS F)) (U : SmallEtale B S hS F) :
    Set ((BigFppfOver.toScheme B S hS).obj U.obj.left) :=
  (schemePointsHomeomorph B S hS U.obj.left).symm ⁻¹'
    (pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom ⁻¹' T)

/-- A point of a chart scheme lies over `T` exactly when the point of `F` it represents lies in
`T`. -/
theorem mem_chartClopenPart_iff (T : Set (points B S hS F)) (U : SmallEtale B S hS F)
    (p : points B S hS (yoneda.obj U.obj.left)) :
    pointsToScheme B S hS U.obj.left p ∈ chartClopenPart T U ↔
      pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom p ∈ T := by
  change pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
    ((schemePointsHomeomorph B S hS U.obj.left).symm
      (schemePointsHomeomorph B S hS U.obj.left p)) ∈ T ↔ _
  rw [Homeomorph.symm_apply_apply]

/-- The part of a chart lying over a clopen set of points is clopen: it is the preimage of that
set under the continuous map from the chart scheme to `|F|`. -/
theorem isClopen_chartClopenPart {T : Set (points B S hS F)} (hT : IsClopen T)
    (U : SmallEtale B S hS F) : IsClopen (chartClopenPart T U) :=
  (hT.preimage (continuous_pointsMap B S hS U.obj.hom)).preimage
    (schemePointsHomeomorph B S hS U.obj.left).symm.continuous

/-- The part of a chart lying over `T` pulls back along a morphism of charts to the part of the
source chart lying over `T`. -/
theorem preimage_chartClopenPart (T : Set (points B S hS F)) {U W : SmallEtale B S hS F}
    (g : W ⟶ U) :
    (BigFppfOver.toScheme B S hS).map g.hom.left ⁻¹' chartClopenPart T U =
      chartClopenPart T W := by
  ext z
  obtain ⟨q, rfl⟩ := surjective_pointsToScheme B S hS W.obj.left z
  rw [Set.mem_preimage, ← pointsToScheme_pointsMap_yoneda, mem_chartClopenPart_iff,
    mem_chartClopenPart_iff, pointsMap_chart_hom]

/-- **The idempotent global function of a clopen set of points.**  On each étale chart it is
the idempotent regular function of the part of the chart lying over the set. -/
def clopenGlobalFunction {T : Set (points B S hS F)} (hT : IsClopen T) :
    globalFunctions B S hS F :=
  ⟨fun U => Scheme.clopenIdempotent (chartClopenPart T U.unop)
      (isClopen_chartClopenPart hT U.unop), by
    intro U W g
    change ((BigFppfOver.toScheme B S hS).map g.unop.hom.left).appTop
      (Scheme.clopenIdempotent (chartClopenPart T U.unop) (isClopen_chartClopenPart hT U.unop)) =
        Scheme.clopenIdempotent (chartClopenPart T W.unop) (isClopen_chartClopenPart hT W.unop)
    rw [Scheme.appTop_clopenIdempotent]
    congr 1
    exact preimage_chartClopenPart T g.unop⟩

/-- The value of the idempotent global function of a clopen set on an étale chart. -/
theorem clopenGlobalFunction_val {T : Set (points B S hS F)} (hT : IsClopen T)
    (U : SmallEtale B S hS F) :
    (clopenGlobalFunction hT).val (op U) =
      Scheme.clopenIdempotent (chartClopenPart T U) (isClopen_chartClopenPart hT U) :=
  rfl

/-- The global function of a clopen set of points is idempotent, being so on every chart. -/
theorem isIdempotentElem_clopenGlobalFunction {T : Set (points B S hS F)} (hT : IsClopen T) :
    IsIdempotentElem (clopenGlobalFunction hT) :=
  Subtype.ext (funext fun U =>
    (Scheme.isIdempotentElem_clopenIdempotent (chartClopenPart T U.unop)
      (isClopen_chartClopenPart hT U.unop)).eq)

/-- **The support of the global function of a clopen set of points is that set.** -/
theorem sectionSupport_clopenGlobalFunction (hF : IsAlgebraicSpace B S hS F)
    {T : Set (points B S hS F)} (hT : IsClopen T) :
    sectionSupport B S hS F (clopenGlobalFunction hT) = T := by
  ext x
  obtain ⟨U, p, rfl⟩ := exists_chart_point B S hS F hF x
  rw [mem_sectionSupport_iff]
  change pointsToScheme B S hS U.obj.left p ∈
      (((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen
        (Scheme.clopenIdempotent (chartClopenPart T U) (isClopen_chartClopenPart hT U)) :
          Set ((BigFppfOver.toScheme B S hS).obj U.obj.left)) ↔ _
  rw [Scheme.coe_basicOpen_clopenIdempotent, mem_chartClopenPart_iff]

/-- **An algebraic space with a nontrivial ring of global functions has a point.**  Without
points every chart scheme is empty, so every regular function on a chart is zero. -/
theorem nonempty_points_of_nontrivial_globalFunctions
    [Nontrivial (globalFunctions B S hS F)] : Nonempty (points B S hS F) := by
  by_contra h
  rw [not_nonempty_iff] at h
  obtain ⟨a, b, hab⟩ := exists_pair_ne (globalFunctions B S hS F)
  refine hab (Subtype.ext (funext fun U => ?_))
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj U.unop.obj.left) :=
    ⟨fun z => by
      obtain ⟨p, -⟩ := surjective_pointsToScheme B S hS U.unop.obj.left z
      exact h.elim (pointsMap B S hS _ U.unop.obj.hom p)⟩
  exact Subsingleton.elim
    (α := Γ((BigFppfOver.toScheme B S hS).obj U.unop.obj.left, ⊤)) (a.val U) (b.val U)

end AlgebraicGeometry.Space

end
