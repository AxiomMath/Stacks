module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilPullbackAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.CupFirstChernClassVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.SmoothDivisor

/-!
# Axiom (A4) for de Rham cohomology

Axiom (A4) of Weil Cohomology Theories, Section 0FID asks: for an effective Cartier divisor
`i : Y ⟶ X` with `X` and `Y` smooth projective over `k`, and `a ∈ H^*(X)` with `i^*a = 0`, one has
`a ∪ c₁(𝒪_X(Y)) = 0`. For de Rham cohomology over a field `k` this is Lemma 0FMX, the de Rham
complex of log poles being defined for `Y ⊆ X` by Lemma 0FMY since `X` and `Y` are smooth over
`k` (Section 0FWC).

## Main results

* `Stacks.DeRhamWeil.pullback_apply_component`: the pullback of `H^*_{dR}` is computed degree by
  degree.
* `Stacks.DeRhamBaseChange.deRhamPullbackSquare_injective_of_isIso`: pullback along an
  isomorphism over the identity of the base is injective.
* `Stacks.DeRhamWeil.divisorAxiom`: **axiom (A4)** for the data
  `Stacks.DeRhamWeil.deRhamFirstChernClassData`.

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FMX](https://stacks.math.columbia.edu/tag/0FMX)
* [Stacks Project, Tag 0FMY](https://stacks.math.columbia.edu/tag/0FMY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.DeRhamBaseChange

variable {X X' S : Scheme.{u}}

/-- **Pullback along an isomorphism is injective**: for an isomorphism `e : X' ⟶ X` over `S`,
`e^* : H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S)` has the left inverse `(e^{-1})^*`. -/
theorem deRhamPullbackSquare_injective_of_isIso (e : X' ⟶ X) [IsIso e] (f' : X' ⟶ S)
    (f : X ⟶ S) (w : e ≫ f = f' ≫ 𝟙 S) (m : ℤ) :
    Function.Injective (deRhamPullbackSquare e f' f (𝟙 S) w m) := by
  have hf' : f' = e ≫ f := by rw [w, Category.comp_id]
  have w' : inv e ≫ f' = f ≫ 𝟙 S := by rw [hf', IsIso.inv_hom_id_assoc, Category.comp_id]
  have key : ∀ z, deRhamPullbackSquare (inv e) f f' (𝟙 S) w' m
      (deRhamPullbackSquare e f' f (𝟙 S) w m z) = z := by
    intro z
    refine (deRhamPullbackSquare_comp e f' f (𝟙 S) w (inv e) f (𝟙 S) w'
      (by simp) m z).trans ?_
    refine (deRhamPullbackSquare_congr f f (IsIso.inv_hom_id e) (Category.comp_id _) _
      (by rw [Category.id_comp, Category.comp_id]) m z).trans ?_
    exact deRhamPullbackSquare_id f _ m z
  intro a b hab
  have h := congrArg (deRhamPullbackSquare (inv e) f f' (𝟙 S) w' m) hab
  rwa [key, key] at h

end Stacks.DeRhamBaseChange

namespace Stacks.DeRhamWeil

variable {k : Type u} [Field k]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory}

/-- **The pullback of `H^*_{dR}` is computed degree by degree**: the degree-`n` component of
`f^*a` is the pullback of the degree-`n` component of `a`. -/
theorem pullback_apply_component (f : X ⟶ Y) (a : cohomology Y) (n : ℤ) :
    pullback f a n = pullbackPiece f n (a n) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m x =>
    rw [pullback_of]
    by_cases h : m = n
    · subst h
      simp
    · rw [DirectSum.of_eq_of_ne m n _ (Ne.symm h), DirectSum.of_eq_of_ne m n _ (Ne.symm h),
        map_zero]
  | add a b ha hb => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, ha, hb, map_add]

/-- The product of a class of `H^*_{dR}` with a homogeneous class vanishes once its products with
every homogeneous component vanish. -/
theorem mul_of_eq_zero {X : (SmoothProjectiveScheme k).FullSubcategory} (a : cohomology X)
    {j : ℤ} (y : piece X j)
    (h : ∀ n, AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X)
      n j (a n) y = 0) :
    a * DirectSum.of (piece X) j y = 0 := by
  classical
  rw [← DirectSum.sum_support_of a, Finset.sum_mul]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [DirectSum.of_mul_of]
  exact (congrArg (DirectSum.of (piece X) (n + j)) (h n)).trans (map_zero _)

/-- **Axiom (A4) for de Rham cohomology**: for an effective Cartier divisor `i : Y ⟶ X` of smooth
projective schemes over `k` and `a ∈ H^*_{dR}(X/k)` with `i^*a = 0`,
`a ∪ c₁^{dR}(𝒪_X(Y)) = 0` (Lemmas 0FMX and 0FMY, as in Section 0FWC). -/
theorem divisorAxiom : (deRhamFirstChernClassData k).DivisorAxiom := by
  intro X Y i D hD e he (a : cohomology X) ha
  have := hD
  have : Stacks.Divisors.IsEffectiveCartierDivisor (X := X.obj.left) D := hD
  change pullback i a = 0 at ha
  -- The divisor is smooth over `k`.
  have hι : D.subschemeι = e.inv ≫ (toScheme k).map i := by rw [← he, Iso.inv_hom_id_assoc]
  have : Smooth (D.subschemeι ≫ X.obj.hom) := by
    rw [hι, Category.assoc, SmoothProjectiveScheme.w i]
    infer_instance
  have hlog : X.obj.hom.HasLogPolesDeRhamComplex D := by
    have h := Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth X.obj.hom (𝟙 _) D hD
    rwa [Category.comp_id] at h
  -- The components of `a` restrict to zero on the divisor.
  have hcomp : ∀ n, deRhamPullbackSquare D.subschemeι (D.subschemeι ≫ X.obj.hom) X.obj.hom (𝟙 _)
      (Category.comp_id _).symm n (a n) = 0 := by
    intro n
    have we : e.hom ≫ D.subschemeι ≫ X.obj.hom = Y.obj.hom ≫ 𝟙 _ := by
      rw [← Category.assoc, he, SmoothProjectiveScheme.w i, Category.comp_id]
    apply deRhamPullbackSquare_injective_of_isIso e.hom Y.obj.hom _ we n
    rw [map_zero]
    refine (deRhamPullbackSquare_comp D.subschemeι (D.subschemeι ≫ X.obj.hom) X.obj.hom (𝟙 _)
      (Category.comp_id _).symm e.hom Y.obj.hom (𝟙 _) we
      (by rw [Category.assoc, we]; simp) n (a n)).trans ?_
    refine (deRhamPullbackSquare_congr Y.obj.hom X.obj.hom he (Category.comp_id _) _
      (square_w i) n (a n)).trans ?_
    have h := congrArg (fun b => b n) ha
    simp only [pullback_apply_component, DirectSum.zero_apply] at h
    exact h
  -- Each component cups to zero with `c₁^{dR}(𝒪_X(Y))`.
  have hcup : ∀ n, AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X)
      (differential X) 2 n
      (AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass
        (X := ((toScheme k).obj X).toRingedSpace) (algebras X) (differential X)
        (Stacks.Divisors.invertibleSheaf' D) inferInstance) (a n) = 0 := by
    intro n
    refine Scheme.Hom.deRhamCohomologyCup_firstChernClass_eq_zero X.obj.hom D hlog n (a n) ?_
    have h := hcomp n
    rw [deRhamPullbackSquare_apply] at h
    have h' := congrArg (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras (D.subschemeι ≫ X.obj.hom))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (D.subschemeι ≫ X.obj.hom))) n).inv.hom h
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
      Iso.hom_inv_id_apply, map_zero] at h'
    exact h'
  -- Conclude in coordinates.
  show tateCupLeft (L := k) (LinearMap.mul k (cohomology X)) 1 a (firstChernClass X _) = 0
  apply (untwist (cohomology X) 1).injective
  rw [LinearEquiv.map_zero, untwist, tateTwistCoordinates_tateCupLeft, ← untwist]
  show a * untwist (cohomology X) 1 ((untwist (cohomology X) 1).symm
    (DirectSum.of (piece X) 2 _)) = 0
  rw [LinearEquiv.apply_symm_apply]
  refine mul_of_eq_zero a _ fun n => ?_
  have h0 : AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X) 2 n
      (firstChernClassPiece X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D))) (a n) = 0 :=
    (congrArg (fun c => AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X)
      (differential X) 2 n c (a n)) (firstChernClassPiece_picardClass X _ _)).trans (hcup n)
  rw [AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_comm, h0,
    AlgebraicGeometry.SheafOfModules.reindexDeRhamCohomology_zero, smul_zero]

end Stacks.DeRhamWeil

end
