module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety

/-!
# The constant abelian scheme attached to an abelian variety

Let `A` be an abelian variety over a field `k` and let `W` be a scheme over `Spec k`. The base
change `A_W = A ×_{Spec k} W` is an abelian scheme over `W`: it is a commutative group scheme over
`W`, flat, proper and of finite presentation, and its fibre over a point `w ∈ W` is the base
change of `A` to the residue field `κ(w)`, which is an abelian variety over `κ(w)` (Stacks 0BFB).

## Main definitions

* `AlgebraicGeometry.groupSchemeBaseChange`: the base change `A_W`, as a group object over `W`.

## Main results

* `AlgebraicGeometry.isAbelianScheme_groupSchemeBaseChange`: `A_W` is an abelian scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of k))

/-- The base change of a group scheme over `Spec k` to a scheme `W` over `Spec k`. -/
noncomputable abbrev groupSchemeBaseChange : Over W := (Over.pullback f).obj A

/-- The group structure on the base change of a group scheme. -/
noncomputable instance grpObjGroupSchemeBaseChange : GrpObj (groupSchemeBaseChange A f) :=
  ((Over.pullback f).mapGrp.obj (.mk A)).grp

/-- The base change of a commutative group scheme is commutative. -/
instance isCommMonObj_groupSchemeBaseChange [IsCommMonObj A] :
    IsCommMonObj (groupSchemeBaseChange A f) :=
  ((Over.pullback f).mapCommGrp.obj (.mk A)).comm

variable [IsAbelianVariety k A]

/-- The base change of an abelian variety over `k` to a point `w` of a scheme over `k`, formed in
two steps through `A_W`, is an abelian variety over the residue field `κ(w)`: the square
exhibiting it as the base change of `A` along `Spec κ(w) ⟶ Spec k` is a pullback, and all the
defining properties of an abelian variety are stable under base change. -/
theorem isAbelianVariety_groupSchemeBaseChange_fibre (x : W) :
    @IsAbelianVariety (W.residueField x) _
      ((Over.pullback (W.fromSpecResidueField x)).mapGrp.obj
        (.mk (groupSchemeBaseChange A f))).X
      ((Over.pullback (W.fromSpecResidueField x)).mapGrp.obj
        (.mk (groupSchemeBaseChange A f))).grp := by
  have hsq : IsPullback
      (pullback.fst (pullback.snd A.hom f) (W.fromSpecResidueField x) ≫ pullback.fst A.hom f)
      (pullback.snd (pullback.snd A.hom f) (W.fromSpecResidueField x)) A.hom
      (W.fromSpecResidueField x ≫ f) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  let P := ((Over.pullback (W.fromSpecResidueField x)).mapGrp.obj
    (.mk (groupSchemeBaseChange A f))).X
  have : IsIntegral P.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := A.hom) _ _ _ hsq
  have : IsProper P.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : GeometricallyIntegral P.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hsq inferInstance
  exact .mk (toIsProperVariety := .mk (toIsVariety := .mk))

/-- **The constant abelian scheme.** The base change `A_W` of an abelian variety `A` over a field
`k` to a scheme `W` over `Spec k` is an abelian scheme over `W`. -/
instance isAbelianScheme_groupSchemeBaseChange : IsAbelianScheme (groupSchemeBaseChange A f) := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have : IsProper (groupSchemeBaseChange A f).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom f))
  have : Flat (groupSchemeBaseChange A f).hom := inferInstanceAs (Flat (pullback.snd A.hom f))
  have : LocallyOfFinitePresentation (groupSchemeBaseChange A f).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd A.hom f))
  exact .mk (fibre_isAbelianVariety := isAbelianVariety_groupSchemeBaseChange_fibre A f)

end AlgebraicGeometry

end
