module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre over a point whose local ring is a field, and the chart fibres of an algebraic space

Let `f : X ⟶ Y` be a morphism of schemes with `X` reduced and let `y` be a point of `Y` whose
local ring `𝒪_{Y, y}` is a field. Then the scheme-theoretic fibre `X_y = X ×_Y Spec κ(y)` is
reduced. For an algebraic space, the local ring of an étale chart at a point lying over a point
whose local ring has dimension zero is a field, so this applies to the fibres of morphisms of
charts over such points.

## Main results

* `AlgebraicGeometry.isReduced_fiber_of_isField_stalk`: the scheme-theoretic fibre of a morphism
  with reduced source over a point whose local ring is a field is reduced.
* `AlgebraicGeometry.Space.isField_stalk_chart_of_localRingDimension_eq_zero`: the local ring of
  an étale chart of a reduced algebraic space at a point over a point whose local ring has
  dimension zero is a field.
* `AlgebraicGeometry.Space.isReduced_toScheme_representedFibreObject_of_isField_stalk`: the fibre
  of a morphism of the big fppf category over the canonical field-valued representative of a
  point with field local ring has reduced underlying scheme, when the source does.
* `AlgebraicGeometry.Space.isReduced_appTop_representedFibreObject_of_isField_stalk`: the same,
  read on the ring of global sections.

## References

* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

namespace AlgebraicGeometry

/-- If `X` is reduced and the local ring of `Y` at `y` is a field, then the scheme-theoretic fibre
of `f : X ⟶ Y` over `y` is reduced. -/
theorem isReduced_fiber_of_isField_stalk {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] (y : Y)
    (hy : IsField (Y.presheaf.stalk y)) : IsReduced (f.fiber y) := by
  have hflat : Flat (Y.fromSpecResidueField y) := by
    rw [Flat.iff_flat_stalkMap]
    intro z
    exact RingHom.Flat.of_isField ((Scheme.fromSpecResidueField_apply y z).symm ▸ hy) _
  have : Flat (f.fiberι y) := inferInstanceAs (Flat (pullback.fst f (Y.fromSpecResidueField y)))
  have hst : ∀ z : f.fiber y, _root_.IsReduced ((f.fiber y).presheaf.stalk z) := by
    intro z
    have _ := isIso_stalkMap_of_flat_of_surjectiveOnStalks (f.fiberι y) z
    set e := (asIso (Scheme.Hom.stalkMap (f.fiberι y) z)).commRingCatIsoToRingEquiv
    refine ⟨fun x hx ↦ ?_⟩
    have h0 := _root_.IsReduced.eq_zero (e.symm x) (hx.map e.symm.toRingHom)
    simpa using congrArg e h0
  exact @isReduced_of_isReduced_stalk _ hst

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `F` be a reduced algebraic space, `x` a point of it whose local ring has dimension zero,
and `u` a point of an étale scheme chart `U` above `x`. Then `𝒪_{U, u}` is a field. -/
@[sga "3 VIA 2.5.4" "partial"]
theorem isField_stalk_chart_of_localRingDimension_eq_zero
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsReduced T))
    {x : points B S hS F} (hx : localRingDimension B S hS x = 0)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ F} (ha : IsEtale B S hS a)
    {u : (BigFppfOver.toScheme B S hS).obj U} (hu : ChartPoint B S hS U a u x) :
    IsField (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) :=
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS F (fun T : Scheme.{u} => IsReduced T) hF).mp hred U a
      ((isEtale_iff_presheaf_of_yoneda B S hS a).mp ha)
  isField_stalk_of_closure_mem_irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U) u
    ((localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hF x).mp hx U a u ha hu)

variable {W V : BigFppfOver B S hS} (α : W ⟶ V)

/-- If the scheme underlying `W` is reduced and the local ring of the scheme underlying `V` at `v`
is a field, then the scheme underlying the fibre product of `α : W ⟶ V` with the canonical
field-valued representative of `v` is reduced. -/
theorem isReduced_toScheme_representedFibreObject_of_isField_stalk
    [IsReduced ((BigFppfOver.toScheme B S hS).obj W)]
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : IsField (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj
      (representedFibreObject B S hS α (schemePointRepresentative B S hS V v))) := by
  have : IsReduced (((BigFppfOver.toScheme B S hS).map α).fiber v) :=
    isReduced_fiber_of_isField_stalk ((BigFppfOver.toScheme B S hS).map α) v hv
  exact isReduced_of_isOpenImmersion (residueFibreSchemeIso B S hS α v).hom

/-- If the scheme underlying `W` is reduced and the local ring of the scheme underlying `V` at `v`
is a field, then the ring of global sections of the fibre product of `α : W ⟶ V` with the
canonical field-valued representative of `v` is reduced. -/
theorem isReduced_appTop_representedFibreObject_of_isField_stalk
    [IsReduced ((BigFppfOver.toScheme B S hS).obj W)]
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : IsField (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)) :
    _root_.IsReduced Γ((BigFppfOver.toScheme B S hS).obj
      (representedFibreObject B S hS α (schemePointRepresentative B S hS V v)), ⊤) :=
  have := isReduced_toScheme_representedFibreObject_of_isField_stalk B S hS α v hv
  inferInstance

end Space

end AlgebraicGeometry

end
