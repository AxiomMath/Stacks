module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.ProjectiveJacobian
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowEtaleOfIsUnit
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor

/-!
# Stacks 0FH7

Let `k` be a field, `X` a smooth projective geometrically irreducible scheme over `k`, `x, x'`
two `k`-rational points and `n` an integer invertible in `k`. Then there is a finite separable
extension `K/k` and a zero-cycle class `δ` on `X_K` with `[x_K] - [x'_K] = n δ`
([Stacks, Tag 0FH7]).

Unqualified names are in `Stacks.WeilCohomology`. The proof is the source's, given
in `exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_projectiveJacobian` from two
inputs over the algebraic closure of the separable closure: surjectivity of `[n]` on an abelian
variety (`Stacks.Groupoids.surjective_zpow_id_left_of_isUnit`, [Stacks, Tag 03RP]) and the
Jacobian of a smooth projective curve (`hasProjectiveJacobianParametrizations_of`,
[Stacks, Tag 0BA0]).

## Main results

* `exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_claim`: the statement, from the
  claim of [Stacks, Tag 0B9X] over algebraically closed fields.
* `exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_isProjectiveMorphism`:
  [Stacks, Tag 0FH7], with the claim discharged (`cohomologyLocusDivisorExistence`,
  `cohomologyLocusDivisorUniqueness`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.WeilCohomology

/-- **[Stacks, Tag 0FH7], from the claim of [Stacks, Tag 0B9X].** -/
theorem exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_claim
    (hex : ∀ (K : Type u) [Field K] [IsAlgClosed K], CohomologyLocusDivisorExistence K)
    (hun : ∀ (K : Type u) [Field K] [IsAlgClosed K], CohomologyLocusDivisorUniqueness K)
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [Smooth f]
    [GeometricallyIrreducible f] (hproj : IsProjectiveMorphism f)
    (n : ℤ) (hn : IsUnit ((n : ℤ) : k)) (x x' : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
        (_ : Algebra.IsSeparable k K)
        (δ : chowGroup (fieldChowSituation K)
          (pullback.snd f (fieldExtensionBaseChangeSituation k K).g) 0),
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl f
          (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k K).g) 0
          (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx') = n • δ := by
  set K := AlgebraicClosure (SeparableClosure k)
  have hnK : IsUnit ((n : ℤ) : K) := by
    rw [← map_intCast (algebraMap k K) n]; exact hn.map _
  exact exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_projectiveJacobian k f hproj
    n hn (fun A _ _ => Stacks.Groupoids.surjective_zpow_id_left_of_isUnit A n hnK)
    (hasProjectiveJacobianParametrizations_of K n (hex K) (hun K)
      (prescribedCohomologyTranslate_of_isSepClosed K)) x x' hx hx'

/-- **[Stacks, Tag 0FH7].** Let `k` be a field, `X` a geometrically irreducible smooth projective
scheme over `k`, `x, x'` two `k`-rational points of `X` and `n` an integer invertible in `k`.
Then there is a finite separable extension `K/k` such that the pullback of `[x] - [x']` to `X_K`
is divisible by `n` in `CH_0(X_K)`. -/
@[stacks 0FH7]
theorem exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_isProjectiveMorphism
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [Smooth f]
    [GeometricallyIrreducible f] (hproj : IsProjectiveMorphism f)
    (n : ℤ) (hn : IsUnit ((n : ℤ) : k)) (x x' : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
        (_ : Algebra.IsSeparable k K)
        (δ : chowGroup (fieldChowSituation K)
          (pullback.snd f (fieldExtensionBaseChangeSituation k K).g) 0),
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl f
          (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k K).g) 0
          (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx') = n • δ :=
  exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_claim
    (fun K _ _ => cohomologyLocusDivisorExistence K)
    (fun K _ _ => cohomologyLocusDivisorUniqueness K)
    k f hproj n hn x x' hx hx'

end Stacks.WeilCohomology

end
