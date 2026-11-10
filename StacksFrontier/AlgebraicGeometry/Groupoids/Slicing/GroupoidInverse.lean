module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation

/-!
# The inverse map of a groupoid scheme

The inverse morphism of a groupoid scheme is an involution of its arrow scheme, and a morphism
of groupoid schemes commutes with the inverse morphisms. Both statements are consequences of
uniqueness of inverses in the groupoid of generalized points.

## Main results

* `AlgebraicGeometry.groupoidInverse_involutive`: the inverse morphism is an involution.
* `AlgebraicGeometry.groupoidInverse_left_isIso`: the inverse morphism is an isomorphism on
  underlying schemes.
* `AlgebraicGeometry.groupoidHom_map_inverse`: a morphism of groupoid schemes intertwines the
  two inverse morphisms.

## Implementation notes

A groupoid scheme carries no axiom asserting either statement; both are deduced from the
axioms by evaluating on the arrow scheme itself, where the identity arrow of the arrow scheme
is the generic arrow. Uniqueness of inverses in `Stacks.Groupoids.GroupoidScheme.Evaluation`
then forces the displayed equalities.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Composing the inverse with the identity arrow of the arrow scheme gives the identity at the
source. -/
private theorem compose_inverse_id_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (w : G.inverse ≫ G.source = (𝟙 G.arrows) ≫ G.target) :
    G.compose G.inverse (𝟙 G.arrows) w = G.source ≫ G.identity := by
  change pullback.lift G.inverse (𝟙 G.arrows) w ≫ G.comp = _
  simpa only [Category.id_comp] using
    G.left_inverse G.arrows (𝟙 G.arrows) G.source_inverse

/-- The inverse morphism of a groupoid scheme is an involution of its arrow scheme. -/
theorem groupoidInverse_involutive {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.inverse ≫ G.inverse = 𝟙 G.arrows := by
  let x : G.Evaluation G.arrows := G.source
  let y : G.Evaluation G.arrows := G.target
  let f : x ⟶ y := ⟨𝟙 G.arrows, Category.id_comp _, Category.id_comp _⟩
  let q : y ⟶ x := ⟨G.inverse, G.source_inverse, G.target_inverse⟩
  let q' : x ⟶ y := ⟨G.inverse ≫ G.inverse, by
    rw [Category.assoc, G.source_inverse, G.target_inverse], by
    rw [Category.assoc, G.target_inverse, G.source_inverse]⟩
  have hfq : f ≫ q = 𝟙 x := by
    apply GroupoidScheme.EvaluationHom.ext
    change G.compose ((𝟙 G.arrows) ≫ G.inverse) (𝟙 G.arrows) _ =
      G.source ≫ G.identity
    simpa only [Category.id_comp] using
      compose_inverse_id_eq G (by rw [Category.id_comp, G.source_inverse])
  have hq'q : q' ≫ q = 𝟙 x := by
    apply GroupoidScheme.EvaluationHom.ext
    change pullback.lift G.inverse (G.inverse ≫ G.inverse) _ ≫ G.comp =
      G.source ≫ G.identity
    simpa only [← Category.assoc, G.target_inverse] using
      G.right_inverse G.arrows G.inverse (by
        rw [Category.assoc, G.target_inverse, G.source_inverse])
  change q'.arrow = f.arrow
  rw [IsIso.eq_inv_of_inv_hom_id hq'q, IsIso.eq_inv_of_hom_inv_id hfq]
  simp

/-- The inverse morphism of a groupoid scheme is an isomorphism of the underlying schemes. -/
theorem groupoidInverse_left_isIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsIso G.inverse.left := by
  have h := congrArg Over.Hom.left (groupoidInverse_involutive G)
  exact ⟨⟨G.inverse.left, h, h⟩⟩

/-- A morphism of groupoid schemes intertwines the inverse morphisms of its source and
target. -/
theorem groupoidHom_map_inverse {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (F : GroupoidScheme.Hom G₁ G₂) :
    F.mapArrows ≫ G₂.inverse = G₁.inverse ≫ F.mapArrows := by
  have wsrc : G₁.inverse ≫ G₁.source = (𝟙 G₁.arrows) ≫ G₁.target := by
    rw [Category.id_comp, G₁.source_inverse]
  have w' : (G₁.inverse ≫ F.mapArrows) ≫ G₂.source =
      ((𝟙 G₁.arrows) ≫ F.mapArrows) ≫ G₂.target := by
    rw [Category.id_comp, Category.assoc, F.map_source, F.map_target, ← Category.assoc,
      G₁.source_inverse]
  let x : G₂.Evaluation G₁.arrows := G₁.source ≫ F.mapObjects
  let y : G₂.Evaluation G₁.arrows := G₁.target ≫ F.mapObjects
  let u : x ⟶ y := ⟨F.mapArrows, F.map_source, F.map_target⟩
  let v : y ⟶ x := ⟨G₁.inverse ≫ F.mapArrows, by
      rw [Category.assoc, F.map_source, ← Category.assoc, G₁.source_inverse], by
      rw [Category.assoc, F.map_target, ← Category.assoc, G₁.target_inverse]⟩
  have huv : u ≫ v = 𝟙 x := by
    apply GroupoidScheme.EvaluationHom.ext
    change G₂.compose (G₁.inverse ≫ F.mapArrows) ((𝟙 G₁.arrows) ≫ F.mapArrows) w' =
      (G₁.source ≫ F.mapObjects) ≫ G₂.identity
    rw [← F.map_comp G₁.arrows G₁.inverse (𝟙 G₁.arrows) wsrc w',
      compose_inverse_id_eq G₁ wsrc, Category.assoc, ← F.map_identity, Category.assoc]
  have harrow : (CategoryTheory.inv u).arrow = F.mapArrows ≫ G₂.inverse := by
    rw [← Groupoid.inv_eq_inv]
    rfl
  exact harrow.symm.trans
    (congrArg GroupoidScheme.EvaluationHom.arrow (IsIso.eq_inv_of_hom_inv_id huv).symm)

end AlgebraicGeometry

end
