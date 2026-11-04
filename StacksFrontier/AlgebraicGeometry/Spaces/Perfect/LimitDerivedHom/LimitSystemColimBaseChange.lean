module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomConeChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.BaseChange
public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# Restriction functoriality of the base-changed system of Situation 09RH

In Situation 09RH let `g : W ⟶ X₀` be a morphism of algebraic spaces onto the chosen stage and
let `j : W' ⟶ W` be a further morphism.  The base-changed systems
`AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` of `g` and of `j ≫ g` are systems
over `W` and over `W'`; reading the latter over `W` through `j`, the projections
`W'_i = X_i ×_{X₀} W' ⟶ X_i ×_{X₀} W = W_i` form a morphism of systems over `W` in the sense of
`CategoryTheory.PullbackData.LimitSystem.Hom`.  That is the shape in which
`CategoryTheory.PullbackData.LimitSystem.Hom.isColim_iff` transfers the colimit statement from
one base to a smaller one.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.baseChangeRestrict`: the morphism
  `X_i ×_{X₀} W' ⟶ X_i ×_{X₀} W` of base-changed stages, and `baseChangeRestrictLimit` its
  companion on the vertices.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeSystemHom`: the morphism of systems.

## Main results

* `CategoryTheory.PullbackData.bijective_factorHom_of_isIso`: the map of morphism sets attached
  to a factorisation whose first morphism is an isomorphism is bijective.
* `CategoryTheory.PullbackData.LimitSystem.Hom.isColim_iff_of_isIso`: a morphism of systems
  whose components are isomorphisms transfers the colimit statement.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeRestrict_comp_toStage` and its companions:
  the morphism of base-changed stages lies over `X_i` and over `j`.

## Implementation notes

`CategoryTheory.PullbackData.LimitSystem.Hom` is a morphism between two systems over the *same*
base, so the system of `j ≫ g` is read over `W` by
`CategoryTheory.PullbackData.LimitSystem.comp`, whose structure morphisms are the composites
with `j`.  The change of base is then undone by
`CategoryTheory.PullbackData.LimitSystem.isColim_comp_iff`, exactly as in the scheme-level
`Stacks.LimitHomDescent.SchemeSystem.isColim_restrict_extensionRestriction_iff`.

Every identity between morphisms of base-changed stages is proved by
`AlgebraicGeometry.Space.DescentSituation.baseChange_hom_ext`, which reduces it to the two
projections, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom/BaseChange.lean`.

## References

* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.PullbackData

universe w v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {Dat : A → Type u₂} [∀ a, Category.{v₂} (Dat a)]
  (P : PullbackData A Dat)

/-- **The map of morphism sets attached to a factorisation whose first morphism is an
isomorphism is bijective**: it is conjugation by the comparison of the factorisation, which is a
bijection, composed with the action of the inverse image along an isomorphism, which is fully
faithful. -/
theorem bijective_factorHom_of_isIso {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (h : f ≫ g = k) [IsIso f] (X Y : Dat c) :
    Function.Bijective (P.factorHom h (X := X) (Y := Y)) := by
  exact (((P.triangle h).app X).symm.homCongr ((P.triangle h).app Y).symm).bijective.comp
    ((P.pullFullyFaithfulOfIso (asIso f)).map_bijective _ _)

namespace LimitSystem

variable {P} {b : A} {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)]
  {S S' : LimitSystem (A := A) b J}

omit [IsDirected J (· ≤ ·)] in
/-- **A morphism of systems whose components are isomorphisms transfers the colimit
statement.** -/
theorem Hom.isColim_iff_of_isIso (hP : P.IsCoherent) (α : Hom S' S) [∀ j, IsIso (α.app j)]
    [IsIso α.limitApp] (X Y : Dat b) : S.IsColim P X Y ↔ S'.IsColim P X Y :=
  α.isColim_iff X Y hP (fun j => P.bijective_factorHom_of_isIso (α.app_toBase j) X Y)
    (P.bijective_factorHom_of_isIso α.limitApp_toBase X Y)

end LimitSystem

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {W W' : AlgebraicSpaces B S hS}

/-- **The morphism `X_i ×_{X₀} W' ⟶ X_i ×_{X₀} W` of base-changed stages** attached to a
morphism `j : W' ⟶ W` over the chosen stage. -/
def baseChangeRestrict (g : W ⟶ D.stage D.base) (j : W' ⟶ W) (i : D.Stages) :
    baseChangeStage (j ≫ g) i ⟶ baseChangeStage g i :=
  ObjectProperty.homMk (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j.hom)
    (by rw [Category.assoc]; exact pullback.condition))

/-- **The morphism `X ×_{X₀} W' ⟶ X ×_{X₀} W` of base-changed vertices** attached to a morphism
`j : W' ⟶ W` over the chosen stage. -/
def baseChangeRestrictLimit (g : W ⟶ D.stage D.base) (j : W' ⟶ W) :
    baseChangeLimit (D := D) (j ≫ g) ⟶ baseChangeLimit (D := D) g :=
  ObjectProperty.homMk (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j.hom)
    (by rw [Category.assoc]; exact pullback.condition))

variable (g : W ⟶ D.stage D.base) (j : W' ⟶ W)

/-- The morphism of base-changed stages lies over `X_i`. -/
theorem baseChangeRestrict_comp_toStage (i : D.Stages) :
    baseChangeRestrict g j i ≫ baseChangeToStage g i = baseChangeToStage (j ≫ g) i :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The morphism of base-changed stages lies over `j`. -/
theorem baseChangeRestrict_comp_toBase (i : D.Stages) :
    baseChangeRestrict g j i ≫ baseChangeToBase g i = baseChangeToBase (j ≫ g) i ≫ j :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- The morphism of base-changed vertices lies over `X`. -/
theorem baseChangeRestrictLimit_comp_toLimitSpace :
    baseChangeRestrictLimit g j ≫ baseChangeToLimitSpace (D := D) g =
      baseChangeToLimitSpace (D := D) (j ≫ g) :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The morphism of base-changed vertices lies over `j`. -/
theorem baseChangeRestrictLimit_comp_toBase :
    baseChangeRestrictLimit g j ≫ baseChangeLimitToBase (D := D) g =
      baseChangeLimitToBase (D := D) (j ≫ g) ≫ j :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- **The morphisms of base-changed stages are compatible with the base changes of the
transition morphisms.** -/
theorem baseChangeRestrict_comp_transition {i i' : D.Stages} (h : i ≤ i') :
    baseChangeRestrict g j i' ≫ baseChangeTransition g h =
      baseChangeTransition (j ≫ g) h ≫ baseChangeRestrict g j i := by
  refine baseChange_hom_ext g ?_ ?_
  · rw [Category.assoc, baseChangeTransition_comp_toStage, ← Category.assoc,
      baseChangeRestrict_comp_toStage, Category.assoc, baseChangeRestrict_comp_toStage,
      baseChangeTransition_comp_toStage]
  · rw [Category.assoc, baseChangeTransition_comp_toBase, baseChangeRestrict_comp_toBase,
      Category.assoc, baseChangeRestrict_comp_toBase, ← Category.assoc,
      baseChangeTransition_comp_toBase]

/-- **The morphisms of base-changed stages are compatible with the base changes of the
projections.** -/
theorem baseChangeRestrictLimit_comp_projection (i : D.Stages) :
    baseChangeRestrictLimit g j ≫ baseChangeProjection g i =
      baseChangeProjection (j ≫ g) i ≫ baseChangeRestrict g j i := by
  refine baseChange_hom_ext g ?_ ?_
  · rw [Category.assoc, baseChangeProjection_comp_toStage, ← Category.assoc,
      baseChangeRestrictLimit_comp_toLimitSpace, Category.assoc,
      baseChangeRestrict_comp_toStage, baseChangeProjection_comp_toStage]
  · rw [Category.assoc, baseChangeProjection_comp_toBase, baseChangeRestrictLimit_comp_toBase,
      Category.assoc, baseChangeRestrict_comp_toBase, ← Category.assoc,
      baseChangeProjection_comp_toBase]

/-- **The morphism of base-changed systems attached to a morphism `j : W' ⟶ W` over the chosen
stage**: the system of `j ≫ g`, read over `W` through `j`, maps to the system of `g` by the
morphisms `X_i ×_{X₀} W' ⟶ X_i ×_{X₀} W` and `X ×_{X₀} W' ⟶ X ×_{X₀} W`. -/
def baseChangeSystemHom :
    PullbackData.LimitSystem.Hom ((baseChangeSystem (D := D) (j ≫ g)).comp j)
      (baseChangeSystem (D := D) g) where
  app i := baseChangeRestrict g j i
  app_toBase i := baseChangeRestrict_comp_toBase g j i
  app_transition h := baseChangeRestrict_comp_transition g j h
  limitApp := baseChangeRestrictLimit g j
  limitApp_toBase := baseChangeRestrictLimit_comp_toBase g j
  limitApp_proj i := baseChangeRestrictLimit_comp_projection g j i

/-- The component of `baseChangeSystemHom` at a stage is `baseChangeRestrict`. -/
@[simp]
theorem baseChangeSystemHom_app (i : D.Stages) :
    (baseChangeSystemHom g j).app i = baseChangeRestrict g j i := rfl

/-- The component of `baseChangeSystemHom` at the vertex is `baseChangeRestrictLimit`. -/
@[simp]
theorem baseChangeSystemHom_limitApp :
    (baseChangeSystemHom g j).limitApp = baseChangeRestrictLimit g j := rfl

end DescentSituation

end AlgebraicGeometry.Space

end
