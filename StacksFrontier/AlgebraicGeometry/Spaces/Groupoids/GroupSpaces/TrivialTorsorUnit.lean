module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TrivialTorsorWithMap

/-!
# The unit section of a trivial torsor and the equivariant map

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, acting on an algebraic space `X` over `B`.  The trivial torsor `G_U = U ×_{b, B} G` over an
object `U` of the site carries a unit section, and this file computes two composites with it: its
projection to `G` is the unit of `G` read at `b`, and, for `b = x ≫ X.hom` attached to a point
`x : U ⟶ X` of `X`, the equivariant map `h ↦ h · x` of
`AlgebraicGeometry.Space.trivialTorsorMap` carries the unit section back to `x` itself.

The second statement is what makes the comparison with the quotient stack faithful and full: a
morphism out of a trivial torsor is determined by its value on the unit section, and the value of
the equivariant map there is the point the trivial torsor came from.

## Main results

* `AlgebraicGeometry.Space.pullbackGroup_unit_left_comp_fst`: the unit section of `G_U` followed
  by the projection `G_U ⟶ G` is `b` followed by the unit of `G`.
* `AlgebraicGeometry.Space.trivialTorsorMap_unit`: the unit section of `G_U` followed by
  `h ↦ h · x` is `x`.

## Implementation notes

The group algebraic space `G_U` is the image of `G` under the monoidal pullback functor
`CategoryTheory.Over.pullback b`, so its unit is the transported unit and the first statement is
the projection formula `CategoryTheory.Over.ε_pullback_left` for the monoidal structure map of
that functor, exactly as the projection formula for the multiplication is used in
`AlgebraicGeometry.Space.pullbackGroup_mul_left_comp_fst`.  Granted that, the second statement is
the computation `1 · x = x` for the induced action on morphisms into `X` over `B`.

## References

* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)
  (G : GroupAlgebraicSpace 𝒞 S hS B hB)

-- The unit is transported along the same slice pullback as the multiplication.
/-- The unit section of the base change `G_U = U ×_{b, B} G`, followed by the projection
`G_U ⟶ G`, is `b` followed by the unit section of `G`. -/
theorem pullbackGroup_unit_left_comp_fst (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    (η[(pullbackGroup hB G U b).obj.X]).left ≫ pullback.fst G.obj.X.hom b =
      b ≫ (η[G.obj.X]).left := by
  show (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
    ((Over.pullback b).map (η[G.obj.X])).left ≫ pullback.fst G.obj.X.hom b = _
  show (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
    pullback.lift (pullback.fst (𝟙 B) b ≫ (η[G.obj.X]).left)
      (pullback.snd (𝟙 B) b) _ ≫ pullback.fst G.obj.X.hom b = _
  rw [pullback.lift_fst]
  show (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
    pullback.fst (𝟙 B) b ≫ (η[G.obj.X]).left = _
  have hc : pullback.fst (𝟙 B) b = pullback.snd (𝟙 B) b ≫ b := by
    simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 B) (g := b))
  rw [hc, Over.ε_pullback_left]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

section EquivariantMap

variable (X : Over B) [ModObj G.obj.X X]

/-- The unit section of the trivial torsor `G_U = U ×_{x ≫ X.hom, B} G` attached to a point
`x : U ⟶ X` of `X`, followed by the equivariant map `h ↦ h · x`, is `x`. -/
theorem trivialTorsorMap_unit (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    (η[(pullbackGroup hB G U (x ≫ X.hom)).obj.X]).left ≫ trivialTorsorMap hB G X U x = x := by
  let P := (pullbackGroup hB G U (x ≫ X.hom)).obj.X
  let UB : Over B := Over.mk (x ≫ X.hom)
  let x₀ : UB ⟶ X := Over.homMk x rfl
  have hcond : pullback.fst G.obj.X.hom (x ≫ X.hom) ≫ G.obj.X.hom =
      (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x) ≫ X.hom := by
    simpa only [Category.assoc] using
      pullback.condition (f := G.obj.X.hom) (g := x ≫ X.hom)
  have hfstL : (CartesianMonoidalCategory.lift (1 : UB ⟶ G.obj.X) x₀).left ≫
      pullback.fst G.obj.X.hom X.hom = (1 : UB ⟶ G.obj.X).left :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (1 : UB ⟶ G.obj.X) x₀)
  have hsndL : (CartesianMonoidalCategory.lift (1 : UB ⟶ G.obj.X) x₀).left ≫
      pullback.snd G.obj.X.hom X.hom = x :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (1 : UB ⟶ G.obj.X) x₀)
  have hlift : (η[P]).left ≫
        pullback.lift (pullback.fst G.obj.X.hom (x ≫ X.hom))
          (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x) hcond =
      (CartesianMonoidalCategory.lift (1 : UB ⟶ G.obj.X) x₀).left := by
    apply pullback.hom_ext
    · refine Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg ((η[P]).left ≫ ·) (pullback.lift_fst _ _ _)) ?_)
      exact Eq.trans (pullbackGroup_unit_left_comp_fst hB G U (x ≫ X.hom)) hfstL.symm
    · refine Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg ((η[P]).left ≫ ·) (pullback.lift_snd _ _ _)) ?_)
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact Eq.trans (Eq.trans (congrArg (· ≫ x) (η[P]).w) (Category.id_comp x)) hsndL.symm
  calc (η[P]).left ≫ trivialTorsorMap hB G X U x
      = ((η[P]).left ≫
            pullback.lift (pullback.fst G.obj.X.hom (x ≫ X.hom))
              (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ x) hcond) ≫
          (γ[G.obj.X, X]).left := (Category.assoc _ _ _).symm
    _ = (CartesianMonoidalCategory.lift (1 : UB ⟶ G.obj.X) x₀).left ≫
          (γ[G.obj.X, X]).left := by rw [hlift]
    _ = ((1 : UB ⟶ G.obj.X) • x₀).left := rfl
    _ = x := congrArg Over.Hom.left (one_smul _ x₀)

end EquivariantMap

end AlgebraicGeometry.Space

end
