module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionGroupoidTerminalPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization

/-!
# The composition of an action groupoid, read on points

Stacks 0444 attaches to an action `a : G ×_B X ⟶ X` of a group algebraic space over `B` the
action groupoid, whose arrow space is `G ×_B X` and whose composition morphism is
`Stacks.Groupoids.ActionGroupoid.composition`. The composition morphism of
`AlgebraicGeometry.Space.groupoidOfAction` is that morphism, preceded by the comparison of the two
pullbacks of composable arrows; on points, the composite of two composable arrows has as group
component the product of theirs and as object component that of the second.

Over the base itself — `AlgebraicGeometry.Space.terminalSpace`, whose presheaf is final — the
arrow presheaf is `G ⊗ X` by `AlgebraicGeometry.Space.arrowsTerminalIso`, and under that
identification the law reads `(g, x) ∘ (h, y) = (g * h, y)`, which is the composition of
Stacks 05YP.

## Main definitions

* `AlgebraicGeometry.Space.actionComposeFstPair`: the pair of group components of a composable
  pair of arrows, as a point of `G ×_B G`.

## Main results

* `AlgebraicGeometry.Space.mul_groupOverStar_left_comp_snd`: the group law of `B ×_S G`, read on
  the group presheaf.
* `AlgebraicGeometry.Space.groupoidOfAction_comp_hom`: the composition morphism of the action
  groupoid, as an ordinary equality.
* `AlgebraicGeometry.Space.groupoidOfAction_fst_compose` and
  `AlgebraicGeometry.Space.groupoidOfAction_snd_compose`: the two components of a composite.
* `AlgebraicGeometry.Space.groupoidOfAction_terminal_compose`: **over the base itself, the
  composite of `(g, x)` and `(h, y)` is `(g * h, y)`.**

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

/-- Two equal morphisms of presheaves of types agree at every point of every test object. -/
theorem appApplyCongr {D : Type (u + 1)} [Category.{u} D] {A E : D ⥤ Type u}
    {f g : A ⟶ E} (e : f = g) (T : D) (x : A.obj T) : f.app T x = g.app T x := by
  rw [e]

/-! ### The group law over the base, read on the group presheaf -/

section GroupLaw

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
  (Bo : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u})

/-- The group law of `B ×_S G` is the lax monoidal comparison of `B ⨯ -` followed by the image
of the pointwise group law. -/
theorem mul_groupOverStar :
    μ[groupOverStar 𝒞 S hS Bo F] =
      Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) (F ⋙ forget GrpCat) (F ⋙ forget GrpCat) ≫
        (overStar 𝒞 S hS Bo).map μ[F ⋙ forget GrpCat] := rfl

/-- The underlying morphism of presheaves of the group law of `B ×_S G`. -/
theorem mul_groupOverStar_left :
    μ[groupOverStar 𝒞 S hS Bo F].left =
      (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo)
          (F ⋙ forget GrpCat) (F ⋙ forget GrpCat)).left ≫
        prod.map (𝟙 Bo) μ[F ⋙ forget GrpCat] :=
  (congrArg (fun z : groupOverStar 𝒞 S hS Bo F ⊗ groupOverStar 𝒞 S hS Bo F ⟶
      groupOverStar 𝒞 S hS Bo F => z.left) (mul_groupOverStar 𝒞 S hS Bo F)).trans
    (Over.comp_left _ _ _ _ _)

/-- **The group law of `B ×_S G`, read on the group presheaf.** A point of the source is a pair
of points of `B ⨯ G` over the same point of `B`; the law multiplies their group components. -/
theorem mul_groupOverStar_left_comp_snd :
    μ[groupOverStar 𝒞 S hS Bo F].left ≫
        (prod.snd : Bo ⨯ (F ⋙ forget GrpCat) ⟶ F ⋙ forget GrpCat) =
      lift (pullback.fst ((overStar 𝒞 S hS Bo).obj (F ⋙ forget GrpCat)).hom
              ((overStar 𝒞 S hS Bo).obj (F ⋙ forget GrpCat)).hom ≫ prod.snd)
          (pullback.snd ((overStar 𝒞 S hS Bo).obj (F ⋙ forget GrpCat)).hom
            ((overStar 𝒞 S hS Bo).obj (F ⋙ forget GrpCat)).hom ≫ prod.snd) ≫
        μ[F ⋙ forget GrpCat] :=
  (congrArg (fun z : (groupOverStar 𝒞 S hS Bo F ⊗ groupOverStar 𝒞 S hS Bo F).left ⟶
      Bo ⨯ (F ⋙ forget GrpCat) => z ≫ prod.snd)
      (mul_groupOverStar_left 𝒞 S hS Bo F)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z : (Bo ⨯ ((F ⋙ forget GrpCat) ⊗ (F ⋙ forget GrpCat))) ⟶
            F ⋙ forget GrpCat =>
          (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo)
            (F ⋙ forget GrpCat) (F ⋙ forget GrpCat)).left ≫ z)
        (prod.map_snd (𝟙 Bo) μ[F ⋙ forget GrpCat])).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z : (groupOverStar 𝒞 S hS Bo F ⊗ groupOverStar 𝒞 S hS Bo F).left ⟶
              (F ⋙ forget GrpCat) ⊗ (F ⋙ forget GrpCat) => z ≫ μ[F ⋙ forget GrpCat])
            (mu_overStar_left_comp_snd 𝒞 S hS Bo (F ⋙ forget GrpCat) (F ⋙ forget GrpCat))))))

end GroupLaw

/-! ### The composition of the action groupoid -/

section Composition

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} (B : AlgebraicSpaces C S hS)
  (G X : Over B.obj) [GrpObj G] [ModObj G X]
  (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)

/-- **The composition morphism of the action groupoid**, as an ordinary equality: the comparison
of the two pullbacks followed by the composition of Stacks 05YP. -/
theorem groupoidOfAction_comp_hom :
    (groupoidOfAction B G X hG hX).groupoid.comp.hom =
      (groupoidOfAction B G X hG hX).compositionDomainIso.hom ≫
        (Stacks.Groupoids.ActionGroupoid.composition G X).left :=
  eq_of_heq (groupoidOfAction B G X hG hX).comp_eq

/-- The pair of group components of a composable pair of arrows of the action groupoid, as a
point of `G ×_B G`. -/
noncomputable def actionComposeFstPair :
    Deformation.composableArrows
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.objects
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.arrows
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.source
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.target ⟶
      (G ⊗ G).left :=
  composableToPullback (snd G X).left γ[G, X].left ≫
    (groupoidOfAction B G X hG hX).compositionDomainIso.hom ≫
      (lift (pullback.fst (snd G X) γ[G, X] ≫ fst G X)
        (pullback.snd (snd G X) γ[G, X] ≫ fst G X)).left

variable {B G X hG hX}

/-- A morphism out of the arrow space, evaluated on a composite arrow. -/
private theorem app_compose_eq {Z : Over B.obj} (f : G ⊗ X ⟶ Z)
    (k : pullback (snd G X) γ[G,X] ⟶ Z)
    (e : Stacks.Groupoids.ActionGroupoid.composition G X ≫ f = k) (T a b h) :
    f.left.app T ((groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.compose T a b h) =
      k.left.app T ((groupoidOfAction B G X hG hX).compositionDomainIso.hom.app T
        ((composableToPullback (snd G X).left γ[G, X].left).app T ⟨(a, b), h⟩)) :=
  (congrArg (f.left.app T) (appApplyCongr (groupoidOfAction_comp_hom B G X hG hX) T _)).trans
    (appApplyCongr (congrArg Over.Hom.left e) T _)

/-- The second pullback projection of a composable pair is its second arrow. -/
private theorem pullback_snd_compositionDomainIso_app (T p) :
    (pullback.snd (snd G X) γ[G, X]).left.app T
        ((groupoidOfAction B G X hG hX).compositionDomainIso.hom.app T
          ((composableToPullback (snd G X).left γ[G, X].left).app T p)) = p.1.2 :=
  (appApplyCongr ((groupoidOfAction B G X hG hX).compositionDomainIso_snd) T _).trans
    (composableToPullback_snd_app C hS (snd G X).left γ[G, X].left T p)

/-- The first component of `AlgebraicGeometry.Space.actionComposeFstPair` is the group component
of the first arrow. -/
theorem actionComposeFstPair_fst_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.objects
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.arrows
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.source
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.target).obj T) :
    (fst G G).left.app T ((actionComposeFstPair B G X hG hX).app T p) =
      (fst G X).left.app T p.1.1 :=
  (appApplyCongr (congrArg Over.Hom.left (lift_fst
      (pullback.fst (snd G X) γ[G, X] ≫ fst G X)
      (pullback.snd (snd G X) γ[G, X] ≫ fst G X))) T _).trans
    (congrArg ((fst G X).left.app T)
      ((appApplyCongr ((groupoidOfAction B G X hG hX).compositionDomainIso_fst) T _).trans
        (composableToPullback_fst_app C hS (snd G X).left γ[G, X].left T p)))

/-- The second component of `AlgebraicGeometry.Space.actionComposeFstPair` is the group component
of the second arrow. -/
theorem actionComposeFstPair_snd_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.objects
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.arrows
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.source
        (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.target).obj T) :
    (snd G G).left.app T ((actionComposeFstPair B G X hG hX).app T p) =
      (fst G X).left.app T p.1.2 :=
  (appApplyCongr (congrArg Over.Hom.left (lift_snd
      (pullback.fst (snd G X) γ[G, X] ≫ fst G X)
      (pullback.snd (snd G X) γ[G, X] ≫ fst G X))) T _).trans
    (congrArg ((fst G X).left.app T) (pullback_snd_compositionDomainIso_app T p))

/-- **The group component of a composite arrow of the action groupoid** is the group law applied
to the group components of its two factors. -/
theorem groupoidOfAction_fst_compose (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.arrows.obj T)
    (h : (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.source.app T a =
      (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.target.app T b) :
    (fst G X).left.app T
        ((groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.compose T a b h) =
      μ[G].left.app T ((actionComposeFstPair B G X hG hX).app T ⟨(a, b), h⟩) :=
  app_compose_eq _ _ (Stacks.Groupoids.ActionGroupoid.composition_fst G X) T a b h

/-- **The object component of a composite arrow of the action groupoid** is the object component
of its second factor: the composite has the source of the second factor. -/
theorem groupoidOfAction_snd_compose (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.arrows.obj T)
    (h : (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.source.app T a =
      (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.target.app T b) :
    (snd G X).left.app T
        ((groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.compose T a b h) =
      (snd G X).left.app T b :=
  (app_compose_eq _ _ (Stacks.Groupoids.ActionGroupoid.composition_source G X) T a b h).trans
    (congrArg ((snd G X).left.app T) (pullback_snd_compositionDomainIso_app T ⟨(a, b), h⟩))

end Composition

/-! ### The composition over the base itself -/

section Terminal

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
  (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u})
  (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) [ModObj (F ⋙ forget GrpCat) P]
  (hG : IsAlgebraicSpace 𝒞 S hS
    (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F).left)
  (hX : IsAlgebraicSpace 𝒞 S hS
    (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P).left)

/-- **Over the base itself, the composite of `(g, x)` and `(h, y)` is `(g * h, y)`**, read
through `AlgebraicGeometry.Space.arrowsTerminalIso`: this is the composition law of the action
groupoid of Stacks 05YP. -/
theorem groupoidOfAction_terminal_compose (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a b : (groupoidOfAction (terminalSpace 𝒞 S hS)
        (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
        (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
        hG hX).groupoid.toGroupoidInFunctors.arrows.obj T)
    (h : (groupoidOfAction (terminalSpace 𝒞 S hS)
        (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
        (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
        hG hX).groupoid.toGroupoidInFunctors.source.app T a =
      (groupoidOfAction (terminalSpace 𝒞 S hS)
        (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
        (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
        hG hX).groupoid.toGroupoidInFunctors.target.app T b) :
    (arrowsTerminalIso 𝒞 S hS F P).hom.app T
        ((groupoidOfAction (terminalSpace 𝒞 S hS)
          (groupOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj F)
          (objectOverStar 𝒞 S hS (terminalSpace 𝒞 S hS).obj P)
          hG hX).groupoid.toGroupoidInFunctors.compose T a b h) =
      (((arrowsTerminalIso 𝒞 S hS F P).hom.app T a).1 *
          ((arrowsTerminalIso 𝒞 S hS F P).hom.app T b).1,
        ((arrowsTerminalIso 𝒞 S hS F P).hom.app T b).2) := by
  have ea := arrowsTerminalIso_hom 𝒞 S hS F P
  refine (appApplyCongr ea T _).trans (Prod.ext ?_ ?_)
  · refine (congrArg ((prod.snd : (terminalSpace 𝒞 S hS).obj ⨯ (F ⋙ forget GrpCat) ⟶ _).app T)
        (groupoidOfAction_fst_compose T a b h)).trans ?_
    refine (appApplyCongr (mul_groupOverStar_left_comp_snd 𝒞 S hS
        (terminalSpace 𝒞 S hS).obj F) T _).trans ?_
    refine (congrArg₂ (fun u v =>
        (prod.snd : (terminalSpace 𝒞 S hS).obj ⨯ (F ⋙ forget GrpCat) ⟶ _).app T u *
          (prod.snd : (terminalSpace 𝒞 S hS).obj ⨯ (F ⋙ forget GrpCat) ⟶ _).app T v)
      (actionComposeFstPair_fst_app T _) (actionComposeFstPair_snd_app T _)).trans ?_
    exact congrArg₂ (· * ·) (congrArg Prod.fst (appApplyCongr ea T a)).symm
      (congrArg Prod.fst (appApplyCongr ea T b)).symm
  · refine (congrArg ((prod.snd : (terminalSpace 𝒞 S hS).obj ⨯ P ⟶ P).app T)
      (groupoidOfAction_snd_compose T a b h)).trans ?_
    exact (congrArg Prod.snd (appApplyCongr ea T b)).symm

end Terminal

end AlgebraicGeometry.Space

end
