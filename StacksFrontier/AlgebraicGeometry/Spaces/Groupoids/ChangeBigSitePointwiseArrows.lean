module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientComparison

/-!
# The comparison of pointwise groupoid fibrations on arrows

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G` be
a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and write `i` for the
localized inclusion. `AlgebraicGeometry.Stack.changeBigSitePointwiseMap` is the map of pointwise
groupoid fibrations covering `i`, and
`AlgebraicGeometry.Stack.changeBigSitePointwiseMap_obj` records that on objects it sends a
`W`-point of the object space to the corresponding `i W`-point of the inverse image.

This file records what it does on *arrows*: an arrow of the groupoid of points at `W`, viewed as a
vertical morphism of the pointwise groupoid fibration through the fibre inclusion of the
Grothendieck construction, goes to the vertical morphism at `i W` given by the transported arrow.
The consequence that the arguments of Stacks 04WX consume is the resulting naturality square for
the 1-morphism `[U/R] ⟶ [f⁻¹U/f⁻¹R]`: the comparison of a presented object with the object
presented by the transported point is natural in the arrows of the groupoid of points.

## Main results

* `AlgebraicGeometry.Stack.changeBigSitePointwiseMap_map_ι`: the map of pointwise groupoid
  fibrations sends the vertical morphism of an arrow to the vertical morphism of the transported
  arrow.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientMap_map_pointwiseToQuotientStack`: the
  2-isomorphism exhibiting `[U/R] ⟶ [f⁻¹U/f⁻¹R]` on presented objects is natural in the arrows of
  the groupoid of points.

## Implementation notes

Both sides of the first result are vertical morphisms of a Grothendieck construction whose base
components agree on the nose, so they are compared through `CoGrothendieck.Hom.ext`. The fibre
components differ by the unit constraint of the presenting pseudofunctor and by the naturality
constraint of the map of pseudofunctors; the first is an `eqToIso` because the pseudofunctor comes
from an ordinary functor (`CategoryTheory.Functor.toPseudofunctor'`), and the second is an
`eqToIso` by the specification of `AlgebraicGeometry.Stack.pointwiseMapData`. The three private
lemmas below turn that into the statement that each constraint is a transport, after which the two
composites are transports between the same pair of objects and therefore equal. The identities are
applied in term mode, because the fibre of a pointwise groupoid fibration is reached through
`CategoryTheory.Functor.toPseudofunctor'` and the groupoid-to-category inclusion, which the
`implicit` transparency level does not unfold, so a rewrite whose pattern mentions a composite
fails to match.

## References

* [Stacks Project, Tag 044P](https://stacks.math.columbia.edu/tag/044P)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Deformation

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc BasedCategory.ofFunctor
  Grpd.forgetToCat Grpd.of

section Transports

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]

/-- A composite of two transports is the transport of the composite equality. -/
private theorem comp_eq_eqToHom {x y z : D} {f : x ⟶ y} {g : y ⟶ z} (hx : x = z)
    (hf : ∃ p : x = y, f = eqToHom p) (hg : ∃ q : y = z, g = eqToHom q) :
    f ≫ g = eqToHom hx := by
  obtain ⟨p, hfp⟩ := hf
  obtain ⟨q, hgq⟩ := hg
  exact (congrArg (fun t => t ≫ g) hfp).trans
    ((congrArg (fun t => eqToHom p ≫ t) hgq).trans (eqToHom_trans p q))

/-- The image of a transport under a functor is a transport. -/
private theorem exists_eqToHom_map (Ψ : C ⥤ D) {x y : C} {f : x ⟶ y}
    (hf : ∃ p : x = y, f = eqToHom p) :
    ∃ p : Ψ.obj x = Ψ.obj y, Ψ.map f = eqToHom p := by
  obtain ⟨p, hfp⟩ := hf
  exact ⟨congrArg Ψ.obj p, (congrArg Ψ.map hfp).trans (eqToHom_map Ψ p)⟩

variable {I : Type u} [Category.{v} I]

/-- The unit constraint of the pseudofunctor attached to an ordinary functor into a strict
bicategory is a transport, read at an object of a fibre. -/
private theorem exists_eqToHom_mapId_inv (K : I ⥤ Cat.{w, w}) (X : I) (x : K.obj X) :
    ∃ p : x = (K.toPseudofunctor'.map (𝟙 (⟨X⟩ : LocallyDiscrete I))).toFunctor.obj x,
      (K.toPseudofunctor'.mapId ⟨X⟩).inv.toNatTrans.app x = eqToHom p :=
  ⟨_, by rw [Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]⟩

end Transports

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **The map of pointwise groupoid fibrations on arrows.** An arrow of the groupoid of points of
`G` at `W`, read as a vertical morphism of the pointwise groupoid fibration, goes to the vertical
morphism at `i W` given by the transported arrow. -/
theorem changeBigSitePointwiseMap_map_ι (W : BigFppfOver B S hS)
    {a a' : G.toGroupoidInFunctors.Evaluation (op W)} (γ : a ⟶ a') :
    (changeBigSitePointwiseMap B B' h S hS G).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' W).map γ) =
      (CoGrothendieck.ι (evaluationGroupoidFunctor
            (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' ((inclusionOver h S hS).obj W)).map
        (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map γ) := by
  obtain ⟨hgeq, hnat⟩ := (pointwiseMapData (changeBigSiteGroupoidHom B B' h S hS G)).2.2
    (Quiver.Hom.toLoc (op (𝟙 W)))
  have key : ((changeBigSitePointwiseMap B B' h S hS G).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' W).map γ)).fiber =
      ((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map γ ≫
        (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map
            (((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor'.mapId ⟨op W⟩).inv.toNatTrans.app a') ≫
          ((pointwiseMapData (changeBigSiteGroupoidHom B B' h S hS G)).val.naturality
            (Quiver.Hom.toLoc (op (𝟙 W)))).hom.toNatTrans.app a') := by
    change ((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map
        (γ ≫ ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor'.mapId ⟨op W⟩).inv.toNatTrans.app a') ≫ _ = _
    rw [Functor.map_comp]
    exact Category.assoc _ _ _
  have key2 : ((CoGrothendieck.ι (evaluationGroupoidFunctor
            (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' ((inclusionOver h S hS).obj W)).map
          (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map γ)).fiber =
      ((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map γ ≫
        ((evaluationGroupoidFunctor (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor'.mapId
            ⟨op ((inclusionOver h S hS).obj W)⟩).inv.toNatTrans.app
          (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).obj a') := rfl
  have hA := exists_eqToHom_map ((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W))
    (exists_eqToHom_mapId_inv (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat) (op W) a')
  have hB : ∃ p, ((pointwiseMapData (changeBigSiteGroupoidHom B B' h S hS G)).val.naturality
      (Quiver.Hom.toLoc (op (𝟙 W)))).hom.toNatTrans.app a' = eqToHom p :=
    ⟨_, by rw [hnat, eqToIso.hom, Cat.eqToHom_app]⟩
  have hC := exists_eqToHom_mapId_inv (evaluationGroupoidFunctor
      (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat)
    (op ((inclusionOver h S hS).obj W))
    (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).obj a')
  refine CoGrothendieck.Hom.ext _ _ rfl ?_
  refine Eq.trans key (Eq.trans (Eq.trans ?_ key2.symm) (Category.comp_id _).symm)
  refine congrArg (fun t =>
    ((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map γ ≫ t) ?_
  obtain ⟨p1, h1⟩ := hA
  obtain ⟨p2, h2⟩ := hB
  obtain ⟨p3, h3⟩ := hC
  exact (comp_eq_eqToHom (p1.trans p2) ⟨p1, h1⟩ ⟨p2, h2⟩).trans h3.symm

/-- **The comparison of a presented object with the object presented by the transported point is
natural in the arrows of the groupoid of points.** This is the 2-isomorphism of
`AlgebraicGeometry.Stack.changeBigSiteQuotientMapUnit`, read at the vertical morphism of an arrow
and combined with `AlgebraicGeometry.Stack.changeBigSitePointwiseMap_map_ι`. -/
theorem changeBigSiteQuotientMap_map_pointwiseToQuotientStack (W : BigFppfOver B S hS)
    {a a' : G.toGroupoidInFunctors.Evaluation (op W)} (γ : a ⟶ a') :
    (changeBigSiteQuotientMap B B' h S hS G).map
          ((pointwiseToQuotientStack G).map
            ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' W).map γ)) ≫
        (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj
            ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' W).obj a')) =
      (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
          ((quotientPrestackEquivalence G).functor.obj
            ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' W).obj a)) ≫
        (pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)).map
          ((CoGrothendieck.ι (evaluationGroupoidFunctor
                (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' ((inclusionOver h S hS).obj W)).map
            (((changeBigSiteGroupoidHom B B' h S hS G).evaluation (op W)).map γ)) := by
  refine Eq.trans ((changeBigSiteQuotientMapUnit B B' h S hS G).hom.naturality
    ((quotientPrestackEquivalence G).functor.map
      ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' W).map γ))) ?_
  exact congrArg (fun t => (changeBigSiteQuotientMapUnit B B' h S hS G).hom.app
      ((quotientPrestackEquivalence G).functor.obj
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' W).obj a)) ≫
      (pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)).map t)
    (changeBigSitePointwiseMap_map_ι B B' h S hS G W γ)

end AlgebraicGeometry.Stack

end
