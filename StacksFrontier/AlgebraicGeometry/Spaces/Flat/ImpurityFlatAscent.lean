module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreWitness
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityAscent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Impurities go up along a flat base change

In the situation of Stacks 0CV6, an impurity of `F` above `y` gives an impurity of the
base-changed module above `y'`, for a morphism `(Y', y') ⟶ (Y, y)` of pointed algebraic spaces
which is flat at `y'`. The new impurity is witnessed over a test scheme étale over `Y' ×_Y T`.

## Main definitions

* `AlgebraicGeometry.Space.ImpurityDiagram.HasFibreWitnessAboveGeneralization`: the choice of
  field-valued representative that Stacks 05DC supplies.

## Main results

* `AlgebraicGeometry.Space.ImpurityDiagram.hasFibreWitnessAboveGeneralization`: that
  representative exists, by the algebraic space form of Stacks 05DC.
* `AlgebraicGeometry.Space.exists_flatImpurityAscentData_of_isFlatAt`: the ascent data of an
  impurity along a flat pointed base change, with the lifted point above `ξ` and in the
  relative weak assassin.
* `AlgebraicGeometry.Space.hasFlatImpurityAscentData_of_isFlatAt`: the same, in the form
  `AlgebraicGeometry.Space.HasFlatImpurityAscentData` which Stacks 0CVG consumes.
* `AlgebraicGeometry.Space.exists_isImpurity_baseChange_etale_of_isFlatAt`: **Stacks 0CVA.**
* `AlgebraicGeometry.Space.isPureAbove_of_isFlatAt`: **Stacks 0CVG, part (1).**
* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isFlatAt`: **Stacks 0CVG, part (2).**

## Implementation notes

The base change of the situation is `AlgebraicGeometry.Space.PointedOver.baseChange`, so the
new impurity is produced as an impurity diagram of that situation and its impurity is read off
from `AlgebraicGeometry.Space.PointedOver.isImpurity_alongBaseChange_iff`, which identifies it
with an impurity of the original situation over the test scheme `T₁`.

The test scheme is built as `T₁ = U ×_V (V ×_Y T)` from a pointed étale chart `U ⟶ V` of
`Y' ⟶ Y` at `y'`, so that `T₁ ⟶ T` is a base change of `U ⟶ V` followed by an étale morphism
and is therefore flat at the chosen point; the specialization is then lifted by Stacks 03HV in
the form `AlgebraicGeometry.exists_specializes_of_isFlatAt`.

The point `ξ₁` is produced by Stacks 0CV2, part (2), read at a field-valued representative of
`t₁'` over which `ξ` is witnessed. The source obtains that representative from a generic point
of `Spec(κ(t₁') ⊗_{κ(t')} κ(ξ))`, which is Stacks 05DC; for algebraic spaces it is
`AlgebraicGeometry.Space.exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq`,
recorded for the diagram as
`AlgebraicGeometry.Space.ImpurityDiagram.hasFibreWitnessAboveGeneralization`.

The proof produces `AlgebraicGeometry.Space.FlatImpurityAscentData`, the point-theoretic data
Stacks 0CVG consumes, and the impurity of the ascended diagram is then the closing step
`AlgebraicGeometry.Space.FlatImpurityAscentData.isImpurity_diagram`.

Finiteness of type and quasi-coherence of the base-changed module are hypotheses as in
Stacks 0CVE and Stacks 0CVF.

## References

* [Stacks Project, Tag 0CVA](https://stacks.math.columbia.edu/tag/0CVA)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03HV](https://stacks.math.columbia.edu/tag/03HV)
* [Stacks Project, Tag 05DC](https://stacks.math.columbia.edu/tag/05DC)
* [Stacks Project, Tag 0CVG](https://stacks.math.columbia.edu/tag/0CVG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_ImpurityFlatAscent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- Flatness at a point passes to the other leg of a cartesian square of schemes; this is
`AlgebraicGeometry.Space.isFlatAt_snd_of_isPullback`. -/
private alias isFlatAt_of_isPullback := isFlatAt_snd_of_isPullback

/-! ### An étale test scheme over a flat pointed base change -/

/-- **The test scheme of Stacks 0CVA**; this is
`AlgebraicGeometry.Space.exists_flatAscentChart_of_isFlatAt`. -/
private alias exists_etaleChart_specializes_of_isFlatAt := exists_flatAscentChart_of_isFlatAt

namespace ImpurityDiagram

variable {P : PrePureSituation.{u, u} B S hS}

/-- The projection `X_T ⟶ T` of the base change, as a morphism of algebraic spaces. -/
noncomputable abbrev toTSpace (D : ImpurityDiagram P) :
    D.baseChangeSpace ⟶ (⟨yoneda.obj D.T, isAlgebraicSpace_yoneda B S hS D.T⟩ :
      AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk D.toT

/-- **The field-valued representative supplied by Stacks 05DC.** For a morphism `T₁ ⟶ T` of
schemes over the base and a point of `T₁` above the generalization `t'`, the distinguished
point of the diagram has a witness for its membership in the relative weak assassin on the
fibre over the image of some field-valued representative of that point.

The source obtains this from a generic point of `Spec(κ(t₁') ⊗_{κ(t')} κ(ξ))`, which is
Stacks 05DC; that it holds whenever `ξ` lies in the relative weak assassin is
`AlgebraicGeometry.Space.ImpurityDiagram.hasFibreWitnessAboveGeneralization`. -/
def HasFibreWitnessAboveGeneralization (D : ImpurityDiagram P) : Prop :=
  ∀ (T₁ : BigFppfOver B S hS) (k : yoneda.obj T₁ ⟶ yoneda.obj D.T)
    (s : points B S hS (yoneda.obj T₁)),
    pointsMap B S hS (yoneda.obj T₁) k s = D.t' →
      ∃ q : FieldValuedPoint B S hS (yoneda.obj T₁),
        q.class B S hS (yoneda.obj T₁) = s ∧
          IsWeaklyAssociatedOnFibre B S hS D.toTSpace D.baseChangeModule
            (FieldValuedPoint.map B S hS (yoneda.obj T₁) k q) D.xi

/-- **The field-valued representative of Stacks 05DC exists.** If the distinguished point `ξ`
lies in the relative weak assassin `WeakAss_{X_T/T}(F_T)`, then for every morphism `T₁ ⟶ T` of
schemes over the base and every point of `T₁` above `t'` there is a field-valued
representative of that point over whose image the membership of `ξ` is witnessed.

This is the algebraic space form of Stacks 05DC,
`AlgebraicGeometry.Space.exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq`,
applied to `f_T : X_T ⟶ T` and to the quasi-coherent module `F_T`. -/
theorem hasFibreWitnessAboveGeneralization (D : ImpurityDiagram P)
    (hD : D.IsRelativeWeakAssassinPoint D.xi) : D.HasFibreWitnessAboveGeneralization := by
  intro T₁ k s hs
  exact exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq B S hS D.toTSpace
    D.baseChangeModule
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.toXSpace P.F
      P.moduleQuasicoherent) hD
    (ObjectProperty.homMk k : (⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj D.T, isAlgebraicSpace_yoneda B S hS D.T⟩)
    (hs.trans D.xi_liesOver.symm)

end ImpurityDiagram

/-! ### Stacks 0CVA -/

/-- **The ascent data of Stacks 0CVA.** Let `(Y', y') ⟶ (Y, y)` be a morphism of pointed
algebraic spaces over `S` with `Y' ⟶ Y` flat at `y'`, and let `D` be an impurity of `F` above
`y`. Then there is an étale chart `T₁` of `Y' ×_Y T` with a point `t₁` above `y'` and `t`, a
generalization `t₁' ⤳ t₁` above `t' ⤳ t` and a point `ξ₁` of `X_{T₁}` above `t₁'` and `ξ` which
lies in the relative weak assassin of `F_{T₁}`. This is
`AlgebraicGeometry.Space.FlatImpurityAscentData.exists_of_isFlatAt`. -/
alias exists_flatImpurityAscentData_of_isFlatAt := FlatImpurityAscentData.exists_of_isFlatAt

/-- **Stacks 0CVA, in the form Stacks 0CVG consumes.** If `Y' ⟶ Y` is flat at `y'`, then every
impurity of `F` above `y` admits ascent data along `(Y', y') ⟶ (Y, y)` whose lifted point lies
above `ξ` and in the relative weak assassin of `F_{T₁}`. -/
theorem hasFlatImpurityAscentData_of_isFlatAt (P : PrePureSituation.{u, u} B S hS)
    (c : PointedOver P) (hflat : IsFlatAt B S hS c.g c.y') : HasFlatImpurityAscentData c :=
  ⟨hflat, fun D hD => exists_flatImpurityAscentData_of_isFlatAt P c hflat D hD⟩

/-- **Stacks 0CVA.** Let `(Y', y') ⟶ (Y, y)` be a morphism of pointed algebraic spaces over `S`
with `Y' ⟶ Y` flat at `y'`. An impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `F` above `y` gives an
impurity `(T₁ ⟶ Y', t₁' ⤳ t₁, ξ₁)` of the pullback `F'` of `F` to `X' = Y' ×_Y X` above `y'`
such that `T₁` is étale over `Y' ×_Y T`: the structure morphism `T₁ ⟶ Y'` is an étale morphism
`T₁ ⟶ Y' ×_Y T` followed by the projection. -/
@[stacks 0CVA]
theorem exists_isImpurity_baseChange_etale_of_isFlatAt (P : PrePureSituation.{u, u} B S hS)
    (c : PointedOver P) (hflat : IsFlatAt B S hS c.g c.y')
    (D : ImpurityDiagram P) (hD : D.IsImpurity) :
    ∃ (E : ImpurityDiagram c.baseChange) (e : yoneda.obj E.T ⟶ pullback c.g D.g),
      IsEtale B S hS e ∧ e ≫ pullback.fst c.g D.g = E.g ∧ E.IsImpurity := by
  obtain ⟨d, hxi, hass⟩ := exists_flatImpurityAscentData_of_isFlatAt P c hflat D hD
  exact ⟨d.diagram, d.e, d.etale, rfl, d.isImpurity_diagram hxi hass hD⟩

/-- **Stacks 0CVA**, with the field-valued representative of Stacks 05DC as a hypothesis. That
hypothesis always holds, by
`AlgebraicGeometry.Space.ImpurityDiagram.hasFibreWitnessAboveGeneralization`, and is not used:
the statement is `AlgebraicGeometry.Space.exists_isImpurity_baseChange_etale_of_isFlatAt`. -/
@[stacks 0CVA "granting hwitness, the choice of field-valued representative that Stacks 05DC \
supplies; the binder is unused, that representative always existing by \
ImpurityDiagram.hasFibreWitnessAboveGeneralization"]
theorem exists_isImpurity_pointedBaseChange_of_isFlatAt (P : PrePureSituation.{u, u} B S hS)
    (c : PointedOver P) (hflat : IsFlatAt B S hS c.g c.y')
    (D : ImpurityDiagram P) (hD : D.IsImpurity)
    (hwitness : D.HasFibreWitnessAboveGeneralization) :
    ∃ (E : ImpurityDiagram c.baseChange) (e : yoneda.obj E.T ⟶ pullback c.g D.g),
      IsEtale B S hS e ∧ e ≫ pullback.fst c.g D.g = E.g ∧ E.IsImpurity := by
  clear hwitness
  exact exists_isImpurity_baseChange_etale_of_isFlatAt P c hflat D hD

/-! ### Descent of purity along a flat pointed base change -/

/-- **Stacks 0CVG, part (1).** In the situation of Stacks 0CV6, let `(Y₁, y₁) ⟶ (Y, y)` be a
morphism of pointed algebraic spaces with `Y₁ ⟶ Y` flat at `y₁`. If the base change `F_{Y₁}`
is pure above `y₁`, then `F` is pure above `y`. This is
`AlgebraicGeometry.Space.isPureAbove_of_isPureAbove_baseChange_of_isFlatAt`. -/
@[stacks 0CVG "part (1)"]
alias isPureAbove_of_isFlatAt := isPureAbove_of_isPureAbove_baseChange_of_isFlatAt

/-- **Stacks 0CVG, part (2).** In the situation of Stacks 0CV6, let `(Y₁, y₁) ⟶ (Y, y)` be a
morphism of pointed algebraic spaces with `Y₁ ⟶ Y` flat at `y₁`. If the base change `F_{Y₁}`
is universally pure above `y₁`, then `F` is universally pure above `y`. This is
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_isUniversallyPureAbove_baseChange_of_isFlatAt`.
-/
@[stacks 0CVG "part (2)"]
alias isUniversallyPureAbove_of_isFlatAt :=
  isUniversallyPureAbove_of_isUniversallyPureAbove_baseChange_of_isFlatAt

end AlgebraicGeometry.Space

end
