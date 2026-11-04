module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Impurities of a module on an algebraic space

Impurities of a quasi-coherent module are studied in a fixed situation: a morphism
`f : X ⟶ Y` of algebraic spaces over a base scheme `S` which is of finite type and decent, a
finite type quasi-coherent `𝒪_X`-module `F`, and a point `y` of `Y`. This module records that
data as a single structure, so that the statements about impurities take one argument instead
of eleven.

An impurity is defined from such a situation together with a further diagram: a scheme `T` over
the target, a specialization `t' ⤳ t` in `T` whose specialized point lies over the chosen point
of the target, and a point `ξ` of the base change `X_T = T ×_Y X` lying over the generalization
`t'`. Such a diagram defines an *impurity of `F` above `y`* when `ξ` is relatively associated
to the pullback `F_T` of `F` over `T`, while no specialization of `ξ` lies over `t`.

## Main definitions

* `AlgebraicGeometry.Space.PrePureSituation`: the data of the morphism, the module and the
  point, together with the finite type, decency, finite type and quasi-coherence hypotheses.
* `AlgebraicGeometry.Space.ImpurityDiagram`: the diagram from which an impurity is defined.
* `AlgebraicGeometry.Space.ImpurityDiagram.baseChange`: the base change `X_T = T ×_Y X`, with
  its two projections `AlgebraicGeometry.Space.ImpurityDiagram.toT` and
  `AlgebraicGeometry.Space.ImpurityDiagram.toX`.
* `AlgebraicGeometry.Space.ImpurityDiagram.baseChangeModule`: the pullback `F_T` of the module
  of the situation to the base change.
* `AlgebraicGeometry.Space.ImpurityDiagram.IsRelativeWeakAssassinPoint`: membership of a point
  of `X_T` in the relative weak assassin `WeakAss_{X_T/T}(F_T)`.
* `AlgebraicGeometry.Space.ImpurityDiagram.IsImpurity`: the diagram defines an impurity.

## Main results

* `AlgebraicGeometry.Space.ImpurityDiagram.isAlgebraicSpace_baseChange`: the base change
  `X_T` is again an algebraic space.
* `AlgebraicGeometry.Space.ImpurityDiagram.isDecentSpace_baseChange`: it is moreover a decent
  algebraic space, since the morphism of the situation is decent.
* `AlgebraicGeometry.Space.ImpurityDiagram.isImpurity_iff`: the second condition defining an
  impurity says that no specialization of `ξ` in `X_T` lies over `t`.

## Implementation notes

The module lives on the small étale ringed site of the source, so its finite type and
quasi-coherence conditions are `SheafOfModules.IsFiniteTypeOnSite` and
`SheafOfModules.IsQuasicoherentOnSite` for that site. Both are classes and are recorded as
instance-implicit fields, re-exported with `attribute [instance]` so that they are found by
synthesis from a term of this structure. The universe `m` of the module sections is
independent of the universe `u` of the schemes, as in
`AlgebraicGeometry.Space.Modules`. A point of the target is an equivalence class of
field-valued points, `AlgebraicGeometry.Space.points`.

The base change `X_T` of the diagram is the presheaf fibre product, so that the decency
hypothesis of the situation applies to it on the nose. Its distinguished point and the two
points of `T` are taken in `AlgebraicGeometry.Space.points`; the specialization between the
latter two is the specialization of their images in the representing scheme under the
comparison bijection `AlgebraicGeometry.Space.pointsToScheme` of Stacks 03BX, which is a
homeomorphism for the point topology. The closure appearing in the impurity condition is taken
for the point topology `AlgebraicGeometry.Space.pointTopology` of Stacks 03BY on `|X_T|`, and
the image of that closure is taken along `AlgebraicGeometry.Space.pointsMap` for the projection
`f_T`.

The relative weak assassin of a module along a morphism of algebraic spaces is not available
as a notion in its own right, so the impurity condition relies instead on
`IsRelativeWeakAssassinPoint`, which spells out the field-valued characterization of
Stacks 0CUZ for `f_T : X_T ⟶ T`: a point of `X_T` belongs to `WeakAss_{X_T/T}(F_T)` when some
field-valued representative of its image in `T` has, in the corresponding fibre of `f_T`, a
point above it which is weakly associated to the restriction of `F_T` there, weak association
being `AlgebraicGeometry.Space.IsWeaklyAssociatedPoint` of Stacks 0CTX. Since the morphism of
the situation is of finite type, so is `f_T`, so the fibres of `f_T` are locally Noetherian by
Stacks 0CUY and this set is the one the source writes `Ass_{X_T/T}(F_T)`.

The pullback of modules along the projections of the base change is
`AlgebraicGeometry.Space.modulePullback` of Stacks 03LU, which this library has at the module
universe of the structure rings only; the impurity condition is therefore stated for a
situation whose module universe is that of the schemes. Quasi-coherence of `F_T` is not needed
to form the condition, because weak association is defined for every module.

## References

* [Stacks Project, Tag 0CV6](https://stacks.math.columbia.edu/tag/0CV6)
* [Stacks Project, Tag 0CV7](https://stacks.math.columbia.edu/tag/0CV7)
* [Stacks Project, Tag 0CV8](https://stacks.math.columbia.edu/tag/0CV8)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

/-- **Stacks 0CV6.** The standing situation for impurities: a finite type, decent morphism
`f : X ⟶ Y` of algebraic spaces over `S`, a finite type quasi-coherent module `F` on the
source, and a point `y` of the target. -/
@[stacks 0CV6]
structure PrePureSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The source algebraic space. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target algebraic space. -/
  Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The source is an algebraic space. -/
  hX : IsAlgebraicSpace B S hS X
  /-- The target is an algebraic space. -/
  hY : IsAlgebraicSpace B S hS Y
  /-- The morphism of algebraic spaces. -/
  f : X ⟶ Y
  /-- The morphism is of finite type. -/
  finiteType : IsFiniteType B S hS f
  /-- The morphism is decent. -/
  decent : IsDecent B S hS f
  /-- A module on the source algebraic space. -/
  F : Modules.{u, m} B S hS X hX
  /-- The module is of finite type. -/
  [moduleFiniteType : SheafOfModules.IsFiniteTypeOnSite F]
  /-- The module is quasi-coherent. -/
  [moduleQuasicoherent : F.IsQuasicoherentOnSite]
  /-- The chosen point of the target. -/
  y : points B S hS Y

attribute [instance] PrePureSituation.moduleFiniteType PrePureSituation.moduleQuasicoherent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0CV7.** The diagram from which an impurity is defined: a scheme `T` with a
morphism `g : T ⟶ Y` to the target, a specialization `t' ⤳ t` in `T` whose specialized point
lies over the chosen point `y`, and a point `ξ` of the base change `X_T = T ×_Y X` lying over
the generalization `t'`. -/
@[stacks 0CV7]
structure ImpurityDiagram (P : PrePureSituation.{u, m} B S hS) where
  /-- The scheme along which the base is changed. -/
  T : BigFppfOver B S hS
  /-- The morphism from `T` to the target of the situation. -/
  g : yoneda.obj T ⟶ P.Y
  /-- The point of `T` specializing to the point above the chosen point of the target. -/
  t' : points B S hS (yoneda.obj T)
  /-- The point of `T` lying over the chosen point of the target. -/
  t : points B S hS (yoneda.obj T)
  /-- The specialization `t' ⤳ t`, taken in the scheme representing `T`. -/
  specializes : pointsToScheme B S hS T t' ⤳ pointsToScheme B S hS T t
  /-- The point `t` lies over the chosen point of the target. -/
  mapsToChosenPoint : pointsMap B S hS (yoneda.obj T) g t = P.y
  /-- The distinguished point of the base change `X_T`. -/
  xi : points B S hS (Limits.pullback g P.f)
  /-- The distinguished point of `X_T` lies over the generalization `t'`. -/
  xi_liesOver :
    pointsMap B S hS (Limits.pullback g P.f) (Limits.pullback.fst g P.f) xi = t'

namespace ImpurityDiagram

variable {P : PrePureSituation.{u, m} B S hS} (D : ImpurityDiagram P)

/-- The base change `X_T = T ×_Y X` of the source of the situation along the morphism `g`. -/
noncomputable abbrev baseChange : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := Limits.pullback D.g P.f

/-- The projection `X_T ⟶ T` of the base change, a base change of the morphism of the
situation. -/
noncomputable abbrev toT : D.baseChange ⟶ yoneda.obj D.T := Limits.pullback.fst D.g P.f

/-- The projection `X_T ⟶ X` of the base change onto the source of the situation. -/
noncomputable abbrev toX : D.baseChange ⟶ P.X := Limits.pullback.snd D.g P.f

/-- The distinguished point of `X_T` lies over the generalization `t'`, stated for the
projection `X_T ⟶ T`. -/
theorem pointsMap_toT_xi :
    pointsMap B S hS D.baseChange D.toT D.xi = D.t' := D.xi_liesOver

/-- **Stacks 02X2** for the diagram: the base change `X_T = T ×_Y X` is an algebraic space,
being a fibre product of algebraic spaces over one. -/
theorem isAlgebraicSpace_baseChange : IsAlgebraicSpace B S hS D.baseChange :=
  isAlgebraicSpace_pullback B S hS D.g P.f (isAlgebraicSpace_yoneda B S hS D.T) P.hX P.hY

/-- The base change `X_T` is a decent algebraic space, because the morphism of the situation
is decent. -/
theorem isDecentSpace_baseChange : IsDecentSpace B S hS D.baseChange :=
  P.decent D.T D.g

end ImpurityDiagram

/-! ### Impurities -/

section Impurity

attribute [local instance] pointTopology

variable {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P)

namespace ImpurityDiagram

/-- The base change `X_T` as an object of the category of algebraic spaces. -/
noncomputable abbrev baseChangeSpace : AlgebraicSpaces B S hS :=
  ⟨D.baseChange, D.isAlgebraicSpace_baseChange⟩

/-- The projection `X_T ⟶ X` onto the source of the situation, as a morphism in the category
of algebraic spaces. -/
noncomputable abbrev toXSpace :
    D.baseChangeSpace ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk D.toX

/-- The pullback `F_T` to the base change `X_T` of the module of the situation. -/
noncomputable abbrev baseChangeModule :
    Modules.{u, u} B S hS D.baseChangeSpace.1 D.baseChangeSpace.2 :=
  (modulePullback B S hS D.toXSpace).obj P.F

/-- The fibre of `f_T : X_T ⟶ T` over a field-valued point of `T`, that is the base change of
`f_T` along the morphism from the field spectrum that the point presents. -/
noncomputable abbrev fibreAt (p : FieldValuedPoint B S hS (yoneda.obj D.T)) :
    AlgebraicSpaces B S hS :=
  ⟨Limits.pullback D.toT (fieldMorphism B S hS (yoneda.obj D.T) p),
    isAlgebraicSpace_pullback B S hS D.toT (fieldMorphism B S hS (yoneda.obj D.T) p)
      D.isAlgebraicSpace_baseChange (isAlgebraicSpace_yoneda B S hS p.siteObject)
      (isAlgebraicSpace_yoneda B S hS D.T)⟩

/-- The projection to `X_T` from the fibre of `f_T` over a field-valued point of `T`. -/
noncomputable abbrev fibreProjection (p : FieldValuedPoint B S hS (yoneda.obj D.T)) :
    D.fibreAt p ⟶ D.baseChangeSpace :=
  ObjectProperty.homMk (Limits.pullback.fst D.toT (fieldMorphism B S hS (yoneda.obj D.T) p))

/-- A point `x` of `X_T` lies in the relative weak assassin `WeakAss_{X_T/T}(F_T)`: for some
field-valued representative of the image of `x` in `T`, the fibre of `f_T` over that
representative carries a point above `x` which is weakly associated to the restriction of
`F_T` to the fibre. -/
noncomputable def IsRelativeWeakAssassinPoint (x : points B S hS D.baseChange) : Prop :=
  ∃ p : FieldValuedPoint B S hS (yoneda.obj D.T),
    p.class B S hS (yoneda.obj D.T) = pointsMap B S hS D.baseChange D.toT x ∧
      ∃ θ : points B S hS (D.fibreAt p).1,
        pointsMap B S hS (D.fibreAt p).1 (D.fibreProjection p).hom θ = x ∧
          IsWeaklyAssociatedPoint B S hS (D.fibreAt p)
            ((modulePullback B S hS (D.fibreProjection p)).obj D.baseChangeModule) θ

/-- **Stacks 0CV8.** The diagram defines an *impurity of `F` above `y`* when the distinguished
point `ξ` of the base change `X_T` lies in the relative assassin `Ass_{X_T/T}(F_T)` and the
point `t` of `T` does not lie in the image under `f_T` of the closure of `{ξ}`. -/
@[stacks 0CV8]
noncomputable def IsImpurity : Prop :=
  D.IsRelativeWeakAssassinPoint D.xi ∧
    D.t ∉ pointsMap B S hS D.baseChange D.toT '' closure {D.xi}

/-- The image under `f_T` of the closure of the distinguished point of `X_T` contains `t`
exactly when some specialization of `ξ` in `X_T` lies over `t`. -/
theorem mem_image_closure_xi_iff :
    D.t ∈ pointsMap B S hS D.baseChange D.toT '' closure {D.xi} ↔
      ∃ θ, D.xi ⤳ θ ∧ pointsMap B S hS D.baseChange D.toT θ = D.t := by
  constructor
  · rintro ⟨θ, hθ, hmap⟩
    exact ⟨θ, specializes_iff_mem_closure.2 hθ, hmap⟩
  · rintro ⟨θ, hθ, hmap⟩
    exact ⟨θ, specializes_iff_mem_closure.1 hθ, hmap⟩

/-- A diagram defines an impurity exactly when `ξ` lies in the relative assassin of `F_T` and
no specialization of `ξ` in `X_T` lies over `t`. -/
theorem isImpurity_iff :
    D.IsImpurity ↔ D.IsRelativeWeakAssassinPoint D.xi ∧
      ∀ θ, D.xi ⤳ θ → pointsMap B S hS D.baseChange D.toT θ ≠ D.t := by
  unfold IsImpurity
  rw [D.mem_image_closure_xi_iff]
  constructor
  · rintro ⟨hass, hnot⟩
    exact ⟨hass, fun θ hθ hmap ↦ hnot ⟨θ, hθ, hmap⟩⟩
  · rintro ⟨hass, hnot⟩
    exact ⟨hass, fun h ↦ h.elim fun θ hθ ↦ hnot θ hθ.1 hθ.2⟩

end ImpurityDiagram

end Impurity

end AlgebraicGeometry.Space

end
