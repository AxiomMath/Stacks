module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamSourceChernSetup
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechPullback

/-!
# The projective bundle formula for the de Rham situation on qcqs schemes

Axiom (4) of Weil Cohomology Theories, Section 45.12 for `A(X) = ⨁_i H^{2i}_{dR}(X/B)` on
quasi-compact and quasi-separated schemes over `B` is the even-degree form of the de Rham
projective bundle formula, Proposition 0FMT. This file reduces the former to the latter read in
every even degree `2n`, in the form `(a_i)_i ↦ ∑_i c₁^{dR}(𝒪_P(1))^i ∪ p^*(a_i)` on
`𝐏(ℰ) = Stacks.Chow.bundle ℰ`.

## Main results

* `AlgebraicGeometry.SheafOfModules.reindexDeRhamCohomology_eq_eqToHom`: transport along an
  equality of degrees is the identification `eqToHom` of the two modules.
* `Stacks.WeilCohomology.QCQSScheme.twistClass_bundleObject`: the twist class of the clause-(3)(a)
  object is the class of `𝒪_{𝐏(ℰ)}(1)`.
* `Stacks.DeRhamChern.bundleFormula_of_degreewise`: axiom (4) from the degreewise formula.

## References

* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.WeilCohomology Stacks.DeRhamBaseChange

universe u

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- Transport of de Rham cohomology along an equality of degrees is the identification `eqToHom`
of the two modules. -/
theorem reindexDeRhamCohomology_eq_eqToHom {m n : ℤ} (h : m = n) (x : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D h x = (eqToHom (congrArg (deRhamCohomology B D) h)).hom x := by
  subst h
  rfl

end AlgebraicGeometry.SheafOfModules

namespace Stacks.WeilCohomology.QCQSScheme

variable {B : Scheme.{u}} (X : (QCQSScheme B).FullSubcategory) (E : ((toScheme B).obj X).Modules)
  (r : ℕ) (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))

/-- **The twist class of the clause-(3)(a) object is the class of `𝒪_{𝐏(ℰ)}(1)`**: the
identification of the object with `𝐏(ℰ)` is the identity. -/
theorem twistClass_bundleObject :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (r + 1) (hM := hE)
    (bundleObject X E r hE).toBundleDatum.twistClass =
      picardClassOf (Stacks.Chow.bundle E) (Stacks.Chow.bundleTwist E)
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
          (Stacks.Chow.isInvertible_bundleTwist E)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (r + 1) (hM := hE)
  have hid : (bundleObject X E r hE).iso.hom = 𝟙 _ := by
    simp only [BundleObject.iso, bundleObject, Iso.refl_hom]
    rfl
  exact picardClassOf_eq_of_iso _ _ _ _ _
    (eqToIso (BundleObject.twist_eq _) ≪≫ (Scheme.Modules.pullbackCongr hid).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _)

end Stacks.WeilCohomology.QCQSScheme

namespace Stacks.DeRhamChern

/-- **The degreewise bundle formula of the even-degree ring, written out** for the pullback along
`q : Y ⟶ X` over `B`: in degree `2n` it is `(a_i)_i ↦ ∑_i ξ^i ∪ q^*(a_i)` with the products read in
degree `2n` through `eqToHom`. -/
theorem degreewiseBundleFormula_eq_sum_cup {Y X B : Scheme.{u}} (q : Y ⟶ X) (p : X ⟶ B)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (q ≫ p))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (q ≫ p))) ((2 : ℕ) : ℤ))
    (N n : ℕ)
    (a : ∀ i : Fin N, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))
      (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ))) :
    AlgebraicGeometry.SheafOfModules.degreewiseBundleFormula _ _ _ _
        (deRhamPullbackSquare q (q ≫ p) p (𝟙 B) (Category.comp_id _).symm) ξ N n a =
      ∑ i : Fin N, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (q ≫ p))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (q ≫ p))))
          (add_sub_cancel ((2 * (i : ℕ) : ℕ) : ℤ) ((2 * n : ℕ) : ℤ)))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ ((2 * (i : ℕ) : ℕ) : ℤ)
          (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ))
          (SheafOfModules.deRhamCohomologyPow _ _ 2 ξ i)
          (DeRhamKatzOdaCech.deRhamPullbackModule q p
            (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ)) (a i))) := by
  rw [AlgebraicGeometry.SheafOfModules.degreewiseBundleFormula]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgebraicGeometry.SheafOfModules.reindexDeRhamCohomology_eq_eqToHom]
  rfl

variable {B : Scheme.{u}}

/-- **Axiom (4) of Section 45.12 for the de Rham situation from the degreewise projective bundle
formula.** If for every `n` the map `(a_i)_{i ≤ r} ↦ ∑_i c₁^{dR}(𝒪_P(1))^i ∪ p^*(a_i)`,
`a_i ∈ H^{2n - 2i}_{dR}(X/B)`, to `H^{2n}_{dR}(𝐏(ℰ)/B)` is bijective, then so is
`(a_i)_{i ≤ r} ↦ ∑_i c₁^A(𝒪_P(1))^i · p^*(a_i)` on `r + 1` copies of `A(X)`. -/
theorem bundleFormula_of_degreewise (X : (QCQSScheme B).FullSubcategory)
    (E : (((QCQSScheme B).ι ⋙ Over.forget B).obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (h : ∀ n : ℕ,
      letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
        (r + 1) (hM := hE)
      Function.Bijective (fun a : ∀ i : Fin (r + 1), SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras X.obj.hom)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras X.obj.hom))
          (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ)) =>
        ∑ i : Fin (r + 1), (eqToHom (congrArg (SheafOfModules.deRhamCohomology
            (Scheme.Hom.deRhamAlgebras (Stacks.Chow.bundleProj E ≫ X.obj.hom))
            (SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (Stacks.Chow.bundleProj E ≫ X.obj.hom))))
            (add_sub_cancel ((2 * (i : ℕ) : ℕ) : ℤ) ((2 * n : ℕ) : ℤ)))).hom
          (SheafOfModules.deRhamCohomologyCup _ _ ((2 * (i : ℕ) : ℕ) : ℤ)
            (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ))
            (SheafOfModules.deRhamCohomologyPow _ _ 2
              (deRhamFirstChernClassPicard (Stacks.Chow.bundleProj E ≫ X.obj.hom)
                (picardClassOf _ (Stacks.Chow.bundleTwist E)
                  ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
                    _ _ _).mp (Stacks.Chow.isInvertible_bundleTwist E)))) i)
            (DeRhamKatzOdaCech.deRhamPullbackModule (Stacks.Chow.bundleProj E) X.obj.hom
              (((2 * n : ℕ) : ℤ) - ((2 * (i : ℕ) : ℕ) : ℤ)) (a i))))) :
    Function.Bijective fun a : Fin (r + 1) → evenDeRhamRing ((QCQSScheme B).ι.obj X).hom =>
      ∑ i : Fin (r + 1),
        c₁ (QCQSScheme B).ι (QCQSScheme.bundleObject X E r hE).toBundleDatum.bundle
            (QCQSScheme.bundleObject X E r hE).toBundleDatum.twistClass ^ (i : ℕ) *
          pull (QCQSScheme B).ι (QCQSScheme.bundleObject X E r hE).toBundleDatum.proj (a i) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (r + 1) (hM := hE)
  refine bijective_bundleFormula_of_degreewise (QCQSScheme B).ι
    (QCQSScheme.bundleObject X E r hE).toBundleDatum.proj
    (QCQSScheme.bundleObject X E r hE).toBundleDatum.twistClass r fun n => ?_
  show Function.Bijective (AlgebraicGeometry.SheafOfModules.degreewiseBundleFormula _ _ _ _
    (deRhamPullbackSquare (Stacks.Chow.bundleProj E) (Stacks.Chow.bundleProj E ≫ X.obj.hom)
      X.obj.hom (𝟙 B) (Category.comp_id _).symm)
    (deRhamFirstChernClassPicard (Stacks.Chow.bundleProj E ≫ X.obj.hom)
      (QCQSScheme.bundleObject X E r hE).toBundleDatum.twistClass) (r + 1) n)
  rw [QCQSScheme.twistClass_bundleObject X E r hE]
  exact (congrArg Function.Bijective
    (funext (degreewiseBundleFormula_eq_sum_cup _ _ _ (r + 1) n))).mpr (h n)

end Stacks.DeRhamChern

end
