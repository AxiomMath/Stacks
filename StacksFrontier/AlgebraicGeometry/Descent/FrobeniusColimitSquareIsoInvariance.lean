module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundlesCube
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonCube

/-!
# The comparison functor of a square of schemes only depends on the square up to isomorphism

For a commutative square of schemes in characteristic `p`, the functor
`AlgebraicGeometry.frobeniusColimitVectorBundlesComparison` goes from the finite locally free
`colim_F 𝒪`-modules on the base into the categorical fibre product of those on the centre and on
the modification, taken over those on the exceptional corner. Stacks Tags 0EXC and 0EXD assert
that it is an equivalence for the squares of Examples 0EVG and 0EVH. Condition (3) of Stacks Tag
0EX9 ranges over squares that are only *isomorphic* to those model squares
(`AlgebraicGeometry.IsModelPairOverBase`), so the assertion has to be moved along isomorphisms of
squares. This file proves that it can be.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_symm`: the square comparison read
  across the other diagonal is the inverse.
* `AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesPullback`: the transition functor
  along an isomorphism of schemes is an equivalence.
* `AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_of_isIso`: **for two
  commutative squares joined by isomorphisms of their four corners, the comparison functor of the
  first is an equivalence as soon as that of the second is.**

## Implementation notes

The transport is `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.isEquivalence_of_cube`.
The vertical functors of the cube are the transition functors along the four isomorphisms, and its
side faces are square comparisons. Its coherence is the cube coherence
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app`, read with the top and bottom
faces across the other diagonal.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **The square comparison read across the other diagonal is the inverse.** -/
lemma frobeniusColimitVectorBundlesSquareIso_symm {X X' Z E : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z) :
    frobeniusColimitVectorBundlesSquareIso p z b e q hX hZ hX' hE hw.symm =
      (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).symm := by
  ext M
  simp [frobeniusColimitVectorBundlesSquareIso]

/-- **The transition functor along an isomorphism of schemes is an equivalence**, with inverse
the transition functor along the inverse isomorphism. -/
def frobeniusColimitVectorBundlesPullbackEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    frobeniusColimitVectorBundles Y p hY ≌ frobeniusColimitVectorBundles X p hX :=
  CategoryTheory.Equivalence.mk (frobeniusColimitVectorBundlesPullback p f hX hY)
    (frobeniusColimitVectorBundlesPullback p (inv f) hY hX)
    ((frobeniusColimitVectorBundlesPullbackId Y p hY).symm ≪≫
      eqToIso (congrArg (fun g : Y ⟶ Y => frobeniusColimitVectorBundlesPullback p g hY hY)
        (IsIso.inv_hom_id f).symm) ≪≫
      (frobeniusColimitVectorBundlesPullbackComp p (inv f) f hY hX hY).symm)
    (frobeniusColimitVectorBundlesPullbackComp p f (inv f) hX hY hX ≪≫
      eqToIso (congrArg (fun g : X ⟶ X => frobeniusColimitVectorBundlesPullback p g hX hX)
        (IsIso.hom_inv_id f)) ≪≫
      frobeniusColimitVectorBundlesPullbackId X p hX)

/-- **The transition functor along an isomorphism of schemes is an equivalence.** -/
instance isEquivalence_frobeniusColimitVectorBundlesPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    (frobeniusColimitVectorBundlesPullback p f hX hY).IsEquivalence :=
  (frobeniusColimitVectorBundlesPullbackEquivalence p f hX hY).isEquivalence_functor

/-- **The comparison functor of a square only depends on the square up to isomorphism.** Let
`q ≫ b = e ≫ z` and `q₂ ≫ b₂ = e₂ ≫ z₂` be two commutative squares of schemes in characteristic
`p`, with corners `X, X', Z, E` and `X₂, X'₂, Z₂, E₂`, and let `iX, iX', iZ, iE` be isomorphisms
from the corners of the first to those of the second making the four side faces commute. If the
comparison functor `𝒮_{X₂} ⟶ 𝒮_{Z₂} ×_{𝒮_{E₂}} 𝒮_{X'₂}` of the second square is an equivalence,
so is the comparison functor `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` of the first. -/
theorem isEquivalence_frobeniusColimitVectorBundlesComparison_of_isIso
    {X X' Z E X₂ X'₂ Z₂ E₂ : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
    (b₂ : X'₂ ⟶ X₂) (z₂ : Z₂ ⟶ X₂) (q₂ : E₂ ⟶ X'₂) (e₂ : E₂ ⟶ Z₂)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
    (hX₂ : IsInCharacteristic X₂ p) (hX'₂ : IsInCharacteristic X'₂ p)
    (hZ₂ : IsInCharacteristic Z₂ p) (hE₂ : IsInCharacteristic E₂ p)
    (hw : q ≫ b = e ≫ z) (hw₂ : q₂ ≫ b₂ = e₂ ≫ z₂)
    (iX : X ⟶ X₂) (iX' : X' ⟶ X'₂) (iZ : Z ⟶ Z₂) (iE : E ⟶ E₂)
    [IsIso iX] [IsIso iX'] [IsIso iZ] [IsIso iE]
    (sb : b ≫ iX = iX' ≫ b₂) (sz : z ≫ iX = iZ ≫ z₂) (sq : q ≫ iX' = iE ≫ q₂)
    (se : e ≫ iZ = iE ≫ e₂)
    (h : (frobeniusColimitVectorBundlesComparison p b₂ z₂ q₂ e₂ hX₂ hX'₂ hZ₂ hE₂
      hw₂).IsEquivalence) :
    (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).IsEquivalence :=
  CategoricalPullback.CatCommSqOver.isEquivalence_of_cube
    (frobeniusColimitVectorBundlesCatCommSqOver p b₂ z₂ q₂ e₂ hX₂ hX'₂ hZ₂ hE₂ hw₂)
    (frobeniusColimitVectorBundlesCatCommSqOver p b z q e hX hX' hZ hE hw)
    (frobeniusColimitVectorBundlesPullback p iX hX hX₂)
    (frobeniusColimitVectorBundlesPullback p iZ hZ hZ₂)
    (frobeniusColimitVectorBundlesPullback p iE hE hE₂)
    (frobeniusColimitVectorBundlesPullback p iX' hX' hX'₂)
    (frobeniusColimitVectorBundlesSquareIso p iX z₂ z iZ hX₂ hX hZ₂ hZ sz)
    (frobeniusColimitVectorBundlesSquareIso p iX b₂ b iX' hX₂ hX hX'₂ hX' sb)
    (frobeniusColimitVectorBundlesSquareIso p iZ e₂ e iE hZ₂ hZ hE₂ hE se)
    (frobeniusColimitVectorBundlesSquareIso p iX' q₂ q iE hX'₂ hX' hE₂ hE sq)
    (fun M => by
      have hc := frobeniusColimitVectorBundlesSquareIso_cube_app p b₂ z₂ q₂ e₂ b z q e
        iX iX' iZ iE hX₂ hX'₂ hZ₂ hE₂ hX hX' hZ hE hw₂ hw sb sz sq se M
      rw [frobeniusColimitVectorBundlesSquareIso_symm p b z q e hX hX' hZ hE hw,
        frobeniusColimitVectorBundlesSquareIso_symm p b₂ z₂ q₂ e₂ hX₂ hX'₂ hZ₂ hE₂ hw₂] at hc
      simp only [Iso.symm_hom] at hc
      dsimp [frobeniusColimitVectorBundlesCatCommSqOver]
      rw [← cancel_epi (inv ((frobeniusColimitVectorBundlesPullback p iE hE hE₂).map
          ((frobeniusColimitVectorBundlesSquareIso p b₂ z₂ q₂ e₂ hX₂ hX'₂ hZ₂ hE₂ hw₂).hom.app
            M))), IsIso.inv_hom_id_assoc]
      rw [← cancel_mono ((frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).inv.app
          ((frobeniusColimitVectorBundlesPullback p iX hX hX₂).obj M))]
      simp only [Category.assoc, Iso.hom_inv_id_app]
      rw [hc]
      congr 1
      · rw [← Functor.map_inv]
        congr 1
        exact (IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id_app _ M)).symm)
    h

end AlgebraicGeometry

end
