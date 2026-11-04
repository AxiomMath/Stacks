module

public import Mathlib.CategoryTheory.NatIso

/-!
# Rescaling a comparison isomorphism does not change the maps of Stacks 09RI

The maps of the directed system of Stacks 09RI,
`AlgebraicGeometry.Space.DescentSituation.homTransition` and
`AlgebraicGeometry.Space.DescentSituation.homProjection`, are *conjugations*: a morphism is
transported by a derived pullback and then read through a comparison isomorphism at the source and
at the target.  Such a conjugation is unchanged when both components of the comparison are
composed with the components of a central automorphism — one that commutes with every morphism
between the objects involved, which a natural automorphism of the identity functor does by
naturality.

**That is what this file proves.**  It matters because the affine base change isomorphism
`AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso`, out of which an affine
translation dictionary for Stacks 09RI has to be built, composes around a square only *up to a
unit* of the ring of global functions of the last corner:
`AlgebraicGeometry.Space.exists_representedAffineToposDerivedBaseChange_compat` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAffineDerivedBaseChangeComp.lean` produces a unit
`c` and `AlgebraicGeometry.Space.unitCentralIso` turns it into an automorphism of the identity
functor of the derived category.  A dictionary field such as
`AlgebraicGeometry.Space.DescentSituation.RingModel.stageEquiv_homTransition` asks for an equation
on the nose, so the unit would appear to obstruct it; the lemma below says it does not, the two
occurrences of the unit in a conjugation cancelling.

Nothing geometric is assumed: the statement is about four objects and two isomorphisms in an
arbitrary category.

## Main results

* `CategoryTheory.Iso.inv_comp_comp_hom_trans_eq_of_central`: a conjugation is unchanged when both
  comparison isomorphisms are composed with components of a central automorphism.
* `CategoryTheory.Iso.inv_comp_comp_hom_trans_eq_of_natIso`: the same with the central
  automorphism given as a natural automorphism of the identity functor, whose naturality is the
  centrality.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Iso

variable {D : Type*} [Category* D] {X X' Y Y' : D}

/-- **A conjugation is unchanged when both comparison isomorphisms are composed with components of
a central automorphism.**  The hypothesis `h` is centrality of the pair `(u, v)` at the one
morphism that matters, the conjugate itself. -/
theorem inv_comp_comp_hom_trans_eq_of_central (e : X ≅ X') (f : Y ≅ Y') (u : X' ≅ X')
    (v : Y' ≅ Y') (g : X ⟶ Y) (h : u.hom ≫ (e.inv ≫ g ≫ f.hom) = (e.inv ≫ g ≫ f.hom) ≫ v.hom) :
    (e ≪≫ u).inv ≫ g ≫ (f ≪≫ v).hom = e.inv ≫ g ≫ f.hom := by
  have hlhs : (e ≪≫ u).inv ≫ g ≫ (f ≪≫ v).hom =
      u.inv ≫ ((e.inv ≫ g ≫ f.hom) ≫ v.hom) := by
    simp only [trans_inv, trans_hom, Category.assoc]
  rw [hlhs, ← h, u.inv_hom_id_assoc]

/-- **A conjugation is unchanged when both comparison isomorphisms are composed with the
components of a natural automorphism of the identity functor.**  The naturality of `u` *is* the
centrality hypothesis of
`CategoryTheory.Iso.inv_comp_comp_hom_trans_eq_of_central`. -/
theorem inv_comp_comp_hom_trans_eq_of_natIso (e : X ≅ X') (f : Y ≅ Y') (u : 𝟭 D ≅ 𝟭 D)
    (g : X ⟶ Y) :
    (e ≪≫ u.app X').inv ≫ g ≫ (f ≪≫ u.app Y').hom = e.inv ≫ g ≫ f.hom :=
  inv_comp_comp_hom_trans_eq_of_central e f (u.app X') (u.app Y') g
    (u.hom.naturality (e.inv ≫ g ≫ f.hom)).symm

end CategoryTheory.Iso

end
