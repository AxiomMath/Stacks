module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageComparison
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquare

/-!
# The stage bridges carry the square comparison of restrictions to that of transitions

For a commutative square `q ≫ b = e ≫ z` of schemes in characteristic `p`, the commutations
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso` of the stage functors of [Stacks, Tag 0EXB]
with the transition functors of [Stacks, Tag 0EXE] carry the comparison
`AlgebraicGeometry.vectPullbackSquareIso` of the two composite restrictions of vector bundles to
the comparison `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` of the two composite
transition functors.  This is the single-stage coherence, in the general square form: it follows
from the compatibility with composition, `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_comp`,
at the two routes around the square, and from the compatibility of the bridges with a transport
along an equality of morphisms, `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_congr`.

## Main results

* `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_square`: the stage bridges intertwine the
  square comparison of the transition functors with that of the restrictions.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

variable {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- The stage bridges carry `vectPullbackSquareIso` to `frobeniusColimitVectorBundlesSquareIso`.
For a commutative square `q ≫ b = e ≫ z` of schemes in characteristic `p` and a finite locally
free `𝒪_X`-module `N`, the square comparison of the transition functors at the stage image of
`N`, followed by the bridges along `b` and then `q`, is the bridges along `z` and then `e`
followed by the stage functor applied to the square comparison of the restrictions. -/
theorem frobeniusStageFunctorPullbackIso_square (hw : q ≫ b = e ≫ z) (n : ℕ) (N : X.Vect) :
    (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
          ((frobeniusStageFunctor X p hX n).obj N) ≫
        (frobeniusColimitVectorBundlesPullback p q hE hX').map
          ((frobeniusStageFunctorPullbackIso p b hX' hX n).hom.app N) ≫
        (frobeniusStageFunctorPullbackIso p q hE hX' n).hom.app ((Scheme.Vect.pullback b).obj N) =
      (frobeniusColimitVectorBundlesPullback p e hE hZ).map
          ((frobeniusStageFunctorPullbackIso p z hZ hX n).hom.app N) ≫
        (frobeniusStageFunctorPullbackIso p e hE hZ n).hom.app ((Scheme.Vect.pullback z).obj N) ≫
        (frobeniusStageFunctor E p hE n).map ((vectPullbackSquareIso hw.symm).hom.app N) := by
  have hqb := frobeniusStageFunctorPullbackIso_comp p q b hE hX' hX n N
  have hez := frobeniusStageFunctorPullbackIso_comp p e z hE hZ hX n N
  have hc : _ = _ := frobeniusStageFunctorPullbackIso_congr p hX hE hw.symm n N
  rw [eqToIso.hom] at hc
  have hqb' : (frobeniusColimitVectorBundlesPullbackComp p q b hE hX' hX).inv.app
        ((frobeniusStageFunctor X p hX n).obj N) ≫
      (frobeniusColimitVectorBundlesPullback p q hE hX').map
          ((frobeniusStageFunctorPullbackIso p b hX' hX n).hom.app N) ≫
        (frobeniusStageFunctorPullbackIso p q hE hX' n).hom.app ((Scheme.Vect.pullback b).obj N) =
      (frobeniusStageFunctorPullbackIso p (q ≫ b) hE hX n).hom.app N ≫
        (frobeniusStageFunctor E p hE n).map ((Scheme.Vect.pullbackComp q b).inv.app N) := by
    rw [← cancel_mono ((frobeniusStageFunctor E p hE n).map
      ((Scheme.Vect.pullbackComp q b).hom.app N)), Category.assoc, Category.assoc,
      Category.assoc, ← hqb, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    exact (Iso.inv_hom_id_app_assoc _ _ _).trans (Category.comp_id _).symm
  have hV : (vectPullbackSquareIso hw.symm).hom.app N =
      (Scheme.Vect.pullbackComp e z).hom.app N ≫ (Scheme.Vect.pullbackCongr hw.symm).hom.app N ≫
        (Scheme.Vect.pullbackComp q b).inv.app N :=
    ObjectProperty.hom_ext _ rfl
  have hS : (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
        ((frobeniusStageFunctor X p hX n).obj N) =
      (frobeniusColimitVectorBundlesPullbackComp p e z hE hZ hX).hom.app
          ((frobeniusStageFunctor X p hX n).obj N) ≫
        (eqToHom (congrArg (fun g : E ⟶ X => frobeniusColimitVectorBundlesPullback p g hE hX)
          hw.symm)).app ((frobeniusStageFunctor X p hX n).obj N) ≫
        (frobeniusColimitVectorBundlesPullbackComp p q b hE hX' hX).inv.app
          ((frobeniusStageFunctor X p hX n).obj N) :=
    rfl
  rw [hS, hV, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, hqb', reassoc_of% hc, ← reassoc_of% hez]

end AlgebraicGeometry
