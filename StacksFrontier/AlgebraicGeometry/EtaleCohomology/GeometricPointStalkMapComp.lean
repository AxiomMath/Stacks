module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap

/-!
# Composition of the stalk maps of morphisms of geometric points

A morphism `a : s ⟶ t` of geometric points of a scheme `S` induces the canonical map
`AlgebraicGeometry.geometricPointStalkMap` from the stalk functor at `t` to the stalk functor at
`s` ([Stacks, Tag 04FN]).  This file proves that these maps compose contravariantly: the map of a
composite `a ≫ b` is the map of `b` followed by the map of `a`.  In particular the action of a
power of an endomorphism of a geometric point on a stalk is the power of its action, which is how
the geometric Frobenius of a finite extension of a residue field, a power of the Frobenius of the
residue field, acts on stalks in the proof of [Stacks, Tag 03V0].

## Main definitions

* `AlgebraicGeometry.GeometricPoint.Hom.comp`: the composite of two morphisms of geometric points.

## Main results

* `AlgebraicGeometry.geometricPointStalkMap_comp`: the stalk maps compose contravariantly.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

/-- The composite of two morphisms of geometric points. -/
def GeometricPoint.Hom.comp {S : Scheme.{u}} {s t r : GeometricPoint S} (a : GeometricPoint.Hom s t)
    (b : GeometricPoint.Hom t r) : GeometricPoint.Hom s r where
  hom := a.hom ≫ b.hom
  comm := by rw [Category.assoc, b.comm, a.comm]

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {s t r : GeometricPoint S}

/-- The neighbourhood functors of `a ≫ b` and of `b` followed by `a` agree on objects. -/
lemma neighborhoodFunctor_comp_obj (a : GeometricPoint.Hom s t) (b : GeometricPoint.Hom t r)
    (U : (geometricPointFiber B S hS r).Elements) :
    (neighborhoodFunctor B S hS (a.comp b)).obj U =
      (neighborhoodFunctor B S hS a).obj ((neighborhoodFunctor B S hS b).obj U) := by
  exact congrArg (fun v => (Functor.Elements.mk (F := geometricPointFiber B S hS s)
    (obj := ((neighborhoodFunctor B S hS (a.comp b)).obj U).obj) v))
    (Subtype.ext (Category.assoc _ _ _))

/-- **The stalk maps of morphisms of geometric points compose contravariantly.** -/
theorem geometricPointStalkMap_comp (a : GeometricPoint.Hom s t) (b : GeometricPoint.Hom t r)
    (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS r).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS t).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A] :
    geometricPointStalkMap B S hS (a.comp b) A =
      geometricPointStalkMap B S hS b A ≫ geometricPointStalkMap B S hS a A := by
  ext F
  apply colimit.hom_ext
  intro U
  let G := (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F
  let Gt := (Functor.Elements.π (geometricPointFiber B S hS t)).op ⋙ F
  let f : (neighborhoodFunctor B S hS (a.comp b)).obj U.unop ⟶
      (neighborhoodFunctor B S hS a).obj ((neighborhoodFunctor B S hS b).obj U.unop) :=
    eqToHom (neighborhoodFunctor_comp_obj B S hS a b U.unop)
  have hw := colimit.w G f.op
  have hf : G.map f.op = 𝟙 _ := by
    simp only [G, f, Functor.comp_map, eqToHom_op, eqToHom_map]
    rfl
  rw [hf] at hw
  have h₁ := colimit.ι_pre G (neighborhoodFunctor B S hS (a.comp b)).op U
  have h₂ := colimit.ι_pre_assoc Gt (neighborhoodFunctor B S hS b).op U
    (colimit.pre G (neighborhoodFunctor B S hS a).op)
  have h₃ := colimit.ι_pre G (neighborhoodFunctor B S hS a).op
    ((neighborhoodFunctor B S hS b).op.obj U)
  change colimit.ι _ U ≫ colimit.pre G (neighborhoodFunctor B S hS (a.comp b)).op =
    colimit.ι _ U ≫ colimit.pre Gt (neighborhoodFunctor B S hS b).op ≫
      colimit.pre G (neighborhoodFunctor B S hS a).op
  exact h₁.trans (((Category.id_comp _).symm.trans hw).trans (h₂.trans h₃).symm)

end AlgebraicGeometry

end
