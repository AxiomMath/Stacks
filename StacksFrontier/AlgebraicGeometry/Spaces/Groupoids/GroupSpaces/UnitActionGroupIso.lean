module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackHom

/-!
# Isomorphic group algebraic spaces have isomorphic trivial-action groupoids

Let `B` be an algebraic space over a scheme `S` of a big fppf site and let `G₁`, `G₂` be group
algebraic spaces over `B`, each acting on `B` itself, that is on the monoidal unit `𝟙_` of the
slice over `B`. The action groupoid of Stacks 0444 of such an action has object space `B` and arrow
space `G ×_B B`. A homomorphism `φ : G₁ ⟶ G₂` induces a morphism of these groupoids, the identity
on objects and `φ × id` on arrows; when `φ` is an isomorphism, so is the induced morphism. This
is what makes the quotient stack `[B/G]` of the trivial action depend on `G` only through its
isomorphism class as a group algebraic space over `B`.

## Main definitions

* `AlgebraicGeometry.Space.unitActionArrowsMap`: the map `φ × id : G₁ ×_B B ⟶ G₂ ×_B B` on arrow
  spaces.
* `AlgebraicGeometry.Space.unitActionGroupoidHom`: the induced morphism of action groupoids.
* `AlgebraicGeometry.Space.unitActionGroupoidIso`: for an isomorphism of group algebraic spaces,
  the induced isomorphism of action groupoids.

## Implementation notes

The construction is `AlgebraicGeometry.Stack.trivialActionGroupoidHom` of
`StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackHom` with the final algebraic space
replaced by an arbitrary base `B`, and with any action of the two groups on the monoidal unit:
the target morphism of the action groupoid is the action morphism, which lands in the final
object of the slice, so it is compatible with `φ × id` whatever the action is. The identity law
of the morphism of groupoids is not a clause, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'`.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
variable (B : AlgebraicSpaces C S hS) {G₁ G₂ G₃ : Over B.obj} [GrpObj G₁] [GrpObj G₂] [GrpObj G₃]
  [ModObj G₁ (𝟙_ (Over B.obj))] [ModObj G₂ (𝟙_ (Over B.obj))] [ModObj G₃ (𝟙_ (Over B.obj))]
  (hG₁ : IsAlgebraicSpace C S hS G₁.left) (hG₂ : IsAlgebraicSpace C S hS G₂.left)
  (hG₃ : IsAlgebraicSpace C S hS G₃.left)

/-- The action groupoid of Stacks 0444 of an action of a group algebraic space `G` over `B` on
`B` itself. -/
noncomputable abbrev unitActionGroupoid (G : Over B.obj) [GrpObj G] [ModObj G (𝟙_ (Over B.obj))]
    (hG : IsAlgebraicSpace C S hS G.left) : GroupoidInAlgebraicSpaces C S hS B :=
  (groupoidOfAction B G (𝟙_ (Over B.obj)) hG B.property).groupoid

/-- **The map on arrow spaces induced by a homomorphism `φ : G₁ ⟶ G₂`**: the morphism
`φ × id : G₁ ×_B B ⟶ G₂ ×_B B`. -/
noncomputable def unitActionArrowsMap (φ : G₁ ⟶ G₂) :
    (unitActionGroupoid B G₁ hG₁).arrows.obj ⟶ (unitActionGroupoid B G₂ hG₂).arrows.obj :=
  (φ ▷ 𝟙_ (Over B.obj)).left

variable {B hG₁ hG₂ hG₃}

/-- The second component of `φ × id` is the second component. -/
theorem unitActionArrowsMap_snd_app (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (unitActionGroupoid B G₁ hG₁).arrows.obj.obj T) :
    (snd G₂ (𝟙_ (Over B.obj))).left.app T ((unitActionArrowsMap B hG₁ hG₂ φ).app T a) =
      (snd G₁ (𝟙_ (Over B.obj))).left.app T a :=
  appApplyCongr (congrArg Over.Hom.left (whiskerRight_snd φ _)) T a

/-- The first component of `φ × id` is `φ` applied to the first component. -/
theorem unitActionArrowsMap_fst_app (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (unitActionGroupoid B G₁ hG₁).arrows.obj.obj T) :
    (fst G₂ (𝟙_ (Over B.obj))).left.app T ((unitActionArrowsMap B hG₁ hG₂ φ).app T a) =
      φ.left.app T ((fst G₁ (𝟙_ (Over B.obj))).left.app T a) :=
  appApplyCongr (congrArg Over.Hom.left (whiskerRight_fst φ _)) T a

/-- `φ × id` commutes with the sources of the two action groupoids. -/
theorem unitActionArrowsMap_source (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (unitActionGroupoid B G₁ hG₁).arrows.obj.obj T) :
    (unitActionGroupoid B G₂ hG₂).source.hom.app T ((unitActionArrowsMap B hG₁ hG₂ φ).app T a) =
      (unitActionGroupoid B G₁ hG₁).source.hom.app T a :=
  unitActionArrowsMap_snd_app φ T a

/-- `φ × id` commutes with the targets of the two action groupoids: both targets are the action
morphism, which lands in the final object of the slice. -/
theorem unitActionArrowsMap_target (φ : G₁ ⟶ G₂) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (unitActionGroupoid B G₁ hG₁).arrows.obj.obj T) :
    (unitActionGroupoid B G₂ hG₂).target.hom.app T ((unitActionArrowsMap B hG₁ hG₂ φ).app T a) =
      (unitActionGroupoid B G₁ hG₁).target.hom.app T a :=
  appApplyCongr (congrArg Over.Hom.left
    (toUnit_unique ((φ ▷ 𝟙_ (Over B.obj)) ≫ γ[G₂, 𝟙_ (Over B.obj)])
      γ[G₁, 𝟙_ (Over B.obj)])) T a

/-- `φ × id` commutes with the compositions of the two action groupoids, `φ` being a
homomorphism. -/
theorem unitActionArrowsMap_compose (φ : G₁ ⟶ G₂) [IsMonHom φ] (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (unitActionGroupoid B G₁ hG₁).arrows.obj.obj T)
    (h : (unitActionGroupoid B G₁ hG₁).source.hom.app T a =
      (unitActionGroupoid B G₁ hG₁).target.hom.app T b)
    (h' : (unitActionGroupoid B G₂ hG₂).source.hom.app T
        ((unitActionArrowsMap B hG₁ hG₂ φ).app T a) =
      (unitActionGroupoid B G₂ hG₂).target.hom.app T
        ((unitActionArrowsMap B hG₁ hG₂ φ).app T b)) :
    (unitActionGroupoid B G₂ hG₂).toGroupoidInFunctors.compose T
        ((unitActionArrowsMap B hG₁ hG₂ φ).app T a)
        ((unitActionArrowsMap B hG₁ hG₂ φ).app T b) h' =
      (unitActionArrowsMap B hG₁ hG₂ φ).app T
        ((unitActionGroupoid B G₁ hG₁).toGroupoidInFunctors.compose T a b h) := by
  let X := 𝟙_ (Over B.obj)
  have hpair : (actionComposeFstPair B G₂ X hG₂ B.property).app T
        ⟨((unitActionArrowsMap B hG₁ hG₂ φ).app T a,
          (unitActionArrowsMap B hG₁ hG₂ φ).app T b), h'⟩ =
      (φ ⊗ₘ φ).left.app T ((actionComposeFstPair B G₁ X hG₁ B.property).app T
        ⟨(a, b), h⟩) := by
    refine Stack.pullback_app_ext G₂.hom G₂.hom (T := T.unop) ?_ ?_
    · refine (actionComposeFstPair_fst_app T _).trans ?_
      refine (unitActionArrowsMap_fst_app φ T a).trans ?_
      refine Eq.trans ?_ (appApplyCongr (congrArg Over.Hom.left (tensorHom_fst φ φ)) T
        _).symm
      exact congrArg (φ.left.app T) (actionComposeFstPair_fst_app T ⟨(a, b), h⟩).symm
    · refine (actionComposeFstPair_snd_app T _).trans ?_
      refine (unitActionArrowsMap_fst_app φ T b).trans ?_
      refine Eq.trans ?_ (appApplyCongr (congrArg Over.Hom.left (tensorHom_snd φ φ)) T
        _).symm
      exact congrArg (φ.left.app T) (actionComposeFstPair_snd_app T ⟨(a, b), h⟩).symm
  refine Stack.pullback_app_ext G₂.hom X.hom (T := T.unop) ?_ ?_
  · refine (groupoidOfAction_fst_compose T _ _ h').trans ?_
    refine Eq.trans ?_ (unitActionArrowsMap_fst_app φ T _).symm
    refine Eq.trans ?_ (congrArg (φ.left.app T) (groupoidOfAction_fst_compose T a b h)).symm
    refine Eq.trans ?_ (appApplyCongr (congrArg Over.Hom.left (IsMonHom.mul_hom φ)) T
      _).symm
    exact congrArg (μ[G₂].left.app T) hpair
  · refine (groupoidOfAction_snd_compose T _ _ h').trans ?_
    refine (unitActionArrowsMap_snd_app φ T b).trans ?_
    refine Eq.trans ?_ (unitActionArrowsMap_snd_app φ T _).symm
    exact (groupoidOfAction_snd_compose T a b h).symm

/-- **The morphism of action groupoids induced by a homomorphism `φ : G₁ ⟶ G₂`** of group
algebraic spaces over `B` acting on `B`: the identity on the common object space `B` and
`φ × id : G₁ ×_B B ⟶ G₂ ×_B B` on arrow spaces. -/
noncomputable def unitActionGroupoidHom (φ : G₁ ⟶ G₂) [IsMonHom φ] :
    GroupoidInAlgebraicSpaces.Hom (unitActionGroupoid B G₁ hG₁) (unitActionGroupoid B G₂ hG₂) :=
  GroupoidInAlgebraicSpaces.Hom.mk' (𝟙 _) (unitActionArrowsMap B hG₁ hG₂ φ)
    (unitActionArrowsMap_source φ) (unitActionArrowsMap_target φ)
    (fun T a b h => unitActionArrowsMap_compose φ T a b h _) (Category.id_comp _)
    (Over.w (φ ▷ 𝟙_ (Over B.obj)))

/-- The map on object spaces of `AlgebraicGeometry.Space.unitActionGroupoidHom` is the
identity. -/
theorem unitActionGroupoidHom_mapObjects (φ : G₁ ⟶ G₂) [IsMonHom φ] :
    (unitActionGroupoidHom (hG₁ := hG₁) (hG₂ := hG₂) φ).toGroupoidHom.mapObjects = 𝟙 _ :=
  rfl

/-- The map on arrow spaces of `AlgebraicGeometry.Space.unitActionGroupoidHom` is `φ × id`. -/
theorem unitActionGroupoidHom_mapArrows (φ : G₁ ⟶ G₂) [IsMonHom φ] :
    (unitActionGroupoidHom (hG₁ := hG₁) (hG₂ := hG₂) φ).toGroupoidHom.mapArrows =
      unitActionArrowsMap B hG₁ hG₂ φ :=
  rfl

/-- `φ × id` is compatible with composition of homomorphisms. -/
theorem unitActionArrowsMap_comp (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃) :
    unitActionArrowsMap B hG₁ hG₂ φ ≫ unitActionArrowsMap B hG₂ hG₃ ψ =
      unitActionArrowsMap B hG₁ hG₃ (φ ≫ ψ) :=
  (congrArg Over.Hom.left (comp_whiskerRight φ ψ (𝟙_ (Over B.obj)))).symm

/-- `id × id` is the identity. -/
theorem unitActionArrowsMap_id :
    unitActionArrowsMap B hG₁ hG₁ (𝟙 G₁) = 𝟙 _ :=
  congrArg Over.Hom.left (id_whiskerRight G₁ (𝟙_ (Over B.obj)))

/-- **An isomorphism of group algebraic spaces over `B` induces an isomorphism of the action
groupoids of their actions on `B`**: the identity on objects and `e × id` on arrows, with
inverse `e⁻¹ × id`. -/
noncomputable def unitActionGroupoidIso (e : G₁ ≅ G₂) [IsMonHom e.hom] :
    GroupoidInAlgebraicSpaces.Iso (unitActionGroupoid B G₁ hG₁) (unitActionGroupoid B G₂ hG₂) :=
  GroupoidInAlgebraicSpaces.Iso.mk' (unitActionGroupoidHom e.hom) (𝟙 _)
    (unitActionArrowsMap B hG₂ hG₁ e.inv) (Category.comp_id _) (Category.comp_id _)
    ((unitActionArrowsMap_comp e.hom e.inv).trans
      ((congrArg (unitActionArrowsMap B hG₁ hG₁) e.hom_inv_id).trans unitActionArrowsMap_id))
    ((unitActionArrowsMap_comp e.inv e.hom).trans
      ((congrArg (unitActionArrowsMap B hG₂ hG₂) e.inv_hom_id).trans unitActionArrowsMap_id))

/-- The forward morphism of `AlgebraicGeometry.Space.unitActionGroupoidIso` is the morphism
induced by the forward homomorphism. -/
theorem unitActionGroupoidIso_hom (e : G₁ ≅ G₂) [IsMonHom e.hom] :
    (unitActionGroupoidIso (hG₁ := hG₁) (hG₂ := hG₂) e).hom = unitActionGroupoidHom e.hom :=
  rfl

end AlgebraicGeometry.Space

end
