module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationLocallySurjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.BaseReesPullback

/-!
# The comparison `f^* B̃ ⟶ ⨁ₙ ℐⁿ` is degreewise locally surjective

Let `A` be a ring, `I ⊆ A` an ideal and `f : X ⟶ Spec A` a morphism of schemes. The comparison
`Φ : f^* B̃ ⟶ ⨁_{n ≥ 0} ℐⁿ` of `Stacks.Cohomology.FormalFunctions.baseReesPullbackHom` is
surjective on affine charts in every nonnegative degree, and is not an isomorphism in general.
This file shows that each homogeneous component of `Φ` is locally surjective. More generally,
for an arbitrary morphism `g : Z ⟶ X` with affine target, each homogeneous component of the
comparison `Stacks.Blowup.reesGradedPullbackHom g I` is locally surjective.

## Main results

* `Stacks.Blowup.surjective_reesGradedPullbackHom_app_val_app_of_isAffine`: over an affine base,
  each nonnegative-degree component of the comparison is surjective on the sections over every
  affine open.
* `Stacks.Blowup.isLocallySurjective_reesGradedPullbackHom_app_of_isAffine`: over an affine base,
  each homogeneous component of the comparison is locally surjective, for an arbitrary `g`;
  `Stacks.Blowup.isLocallySurjective_reesGradedPullbackHomOfEq_app` is the same for the
  comparison read along an equality of ideal sheaves.
* `Stacks.Cohomology.FormalFunctions.isLocallySurjective_baseReesPullbackHom_app`: each
  homogeneous component of `Φ : f^* B̃ ⟶ ⨁ₙ ℐⁿ` is locally surjective.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u


namespace Stacks.Blowup

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (I : X.IdealSheafData)

/-- Over an affine base `X`, each nonnegative-degree component of the comparison
`reesGradedPullbackHom g I` is surjective on the sections over every affine open of `Z`, for an
arbitrary `g`. -/
theorem surjective_reesGradedPullbackHom_app_val_app_of_isAffine [IsAffine X] (n : ℤ)
    (hn : 0 ≤ n) {V : Z.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (((reesGradedPullbackHom g I).app n).val.app (op V)) :=
  surjective_reesPullbackComparisonLinear g I n hn ⟨⊤, isAffineOpen_top X⟩ ⟨V, hV⟩ le_top

/-- Over an affine base `X`, each homogeneous component of the comparison
`reesGradedPullbackHom g I` is locally surjective, for an arbitrary `g`. -/
theorem isLocallySurjective_reesGradedPullbackHom_app_of_isAffine [IsAffine X] (n : ℤ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : TopCat))
      ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        ((reesGradedPullbackHom g I).app n).val) := by
  rcases lt_or_ge n 0 with hn | hn
  · refine Presheaf.isLocallySurjective_of_surjective _ _ fun W y => ⟨0, ?_⟩
    have hsub : Subsingleton ↥(((reesGradedAlgebra (I.comap g)).piece n).val.obj W) :=
      Stacks.subsingleton_of_isZero (reesPiece_negative_isZero (I.comap g) n hn) W
    exact @Subsingleton.elim _ hsub _ _
  · constructor
    intro W s
    refine (Opens.grothendieckTopology (Z : TopCat)).superset_covering
      ((Sieve.generate_le_iff _ _).2 fun V ι hV => ?_) (generate_affineOpensPresieve_mem Z W)
    exact surjective_reesGradedPullbackHom_app_val_app_of_isAffine g I n hn hV
      (((reesGradedAlgebra (I.comap g)).piece n).val.map ι.op s)

/-- Over an affine base `X`, each homogeneous component of the comparison
`reesGradedPullbackHomOfEq g I h`, read along an equality `h : L = I.comap g`, is locally
surjective. -/
theorem isLocallySurjective_reesGradedPullbackHomOfEq_app [IsAffine X]
    {L : Z.IdealSheafData} (h : L = I.comap g) (n : ℤ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Z : TopCat))
      ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
        ((reesGradedPullbackHomOfEq g I h).app n).val) := by
  subst h
  exact isLocallySurjective_reesGradedPullbackHom_app_of_isAffine g I n

end Stacks.Blowup

namespace Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- Each homogeneous component of `Φ : f^* B̃ ⟶ ⨁_{n ≥ 0} ℐⁿ` is locally surjective, for an
arbitrary `f : X ⟶ Spec A`. -/
theorem isLocallySurjective_baseReesPullbackHom_app (n : ℤ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X.left : TopCat))
      ((PresheafOfModules.toPresheaf X.left.ringCatSheaf.obj).map
        ((baseReesPullbackHom I X).app n).val) :=
  Stacks.Blowup.isLocallySurjective_reesGradedPullbackHomOfEq_app X.hom (specIdealSheaf I)
    (baseIdealSheaf_eq_comap_specIdealSheaf I X) n

end Stacks.Cohomology.FormalFunctions
end
