module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleChowBijective
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchChowInjective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BivariantDivision
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass

/-!
# Capping with the flat pullback class of a vector bundle is bijective

Let `(S, δ)` be as in chapter 42 of the Stacks Project, let `ℰ` be a finite locally free module of
constant rank `r` on a scheme `Y` locally of finite type over `S`, and let `p : 𝐕(ℰ) ⟶ Y` be its
vector bundle. Every base change of `p` is again the projection of a vector bundle, namely of the
pulled back module (`AlgebraicGeometry.Scheme.Modules.isPullback_vectorBundleBaseChangeMap`), so
flat pullback along it is bijective on Chow groups by Stacks 02TY. Consequently capping with the
flat pullback class `p^* ∈ A^{-r}(𝐕(ℰ) ⟶ Y)` of Stacks 0B78 is bijective on the Chow groups of
every test scheme, which is what makes `p^*` divisible
(`Stacks.Chow.bivariantQuotient`): this is the sentence "this works because `p^*` is always
bijective on chow groups by Lemma 02TY" of the proof of Stacks 0FBK.

## Main results

* `Stacks.Chow.flatPullbackChow_bijective_of_isPullback_vectorBundleToBase` — flat pullback along
  any base change of the projection of a vector bundle of constant rank is bijective.
* `Stacks.Chow.middleCap_bijective_vectorBundle` — capping with `p^*` on the middle fibre
  products `T ×_X 𝐕(ℰ)` is bijective, for any `g : Y ⟶ X` and test scheme `T ⟶ X`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Stacks 02TY for a base change of a vector bundle.** Flat pullback along any base change
`p : P ⟶ T` of the projection of a vector bundle `𝐕(ℰ) ⟶ Y` of constant rank `r` is bijective on
Chow groups: `P` is the vector bundle of the pullback of `ℰ` to `T`. -/
theorem flatPullbackChow_bijective_of_isPullback_vectorBundleToBase (C : ChowSituation.{u})
    {Y T P : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (E : Y.Modules) [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (g : T ⟶ Y) (p : P ⟶ T)
    [LocallyOfFiniteType p] [Flat p] (q : P ⟶ Scheme.Modules.vectorBundle Y E)
    (sq : IsPullback q p (Scheme.Modules.vectorBundleToBase Y E) g) (hbase : p ≫ sT = sP)
    (hp : AlgebraicGeometry.RelativeDimension p r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sP sT p hbase r hp k) :
    Function.Bijective (flatPullbackChow C sP sT p hbase r hp k hfac) := by
  let E' := (Scheme.Modules.pullback g).obj E
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E' r
  have : E'.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E'
  have sq' := Scheme.Modules.isPullback_vectorBundleBaseChangeMap g E
  let e : P ≅ Scheme.Modules.vectorBundle T E' := sq.isoIsPullback _ _ sq'
  have he : e.hom ≫ Scheme.Modules.vectorBundleToBase T E' = p := sq.isoIsPullback_hom_snd _ _ sq'
  have := locallyOfFiniteType_vectorBundleToBase E' r
  have := flat_vectorBundleToBase E' r
  have hq := relativeDimension_vectorBundleToBase E' r
  have hebase : e.hom ≫ (Scheme.Modules.vectorBundleToBase T E' ≫ sT) = sP := by
    rw [← Category.assoc, he, hbase]
  have hbij := flatPullbackChow_bijective_vectorBundleToBase C sT E' r (k := k)
  exact ⟨flatPullbackChow_injective_of_isIso_comp C sP _ sT e.hom _ p he hebase rfl hbase r hq hp k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) hfac hbij.1,
    flatPullbackChow_surjective_of_isIso_comp C sP _ sT e.hom _ p he hebase rfl hbase r hq hp k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) hfac hbij.2⟩

/-- **Capping with the flat pullback class of a vector bundle is bijective.** For a vector bundle
`q : 𝐕(ℰ) ⟶ Y` of constant rank `r`, any `g : Y ⟶ X` and any test scheme `t : T ⟶ X`, capping with
`q^* ∈ A^{-r}(𝐕(ℰ) ⟶ Y)` is a bijection `A_m(T ×_X Y) ⟶ A_{m+r}(T ×_X 𝐕(ℰ))`. -/
theorem middleCap_bijective_vectorBundle (C : ChowSituation.{u}) {Y X : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (E : Y.Modules) [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (g : Y ⟶ X)
    [LocallyOfFiniteType g] {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (m : ℤ) :
    letI := locallyOfFiniteType_vectorBundleToBase E r
    letI := flat_vectorBundleToBase E r
    Function.Bijective (middleCap C (gysinSystemOfInvertible C)
      (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y E) g
      rfl (-(r : ℤ))
      (flatPullbackBivariantClassOfInvertible C (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY
        (Scheme.Modules.vectorBundleToBase Y E) rfl r (relativeDimension_vectorBundleToBase E r))
      t m) := by
  let := locallyOfFiniteType_vectorBundleToBase E r
  let := flat_vectorBundleToBase E r
  set q := Scheme.Modules.vectorBundleToBase Y E
  refine (properChowPushforward_bijective_of_isIso C _ _ _ _ _
    (properPushforwardDescends C _ _ _ _ _)).comp ?_
  change Function.Bijective (flatPullbackBivariantCap C (q ≫ sY) sY q rfl r
    (relativeDimension_vectorBundleToBase E r) (flatPullbackDescends C) (pullback.fst g t) m)
  refine (chowGroupDegreeEquiv C _ _).bijective.comp ?_
  exact flatPullbackChow_bijective_of_isPullback_vectorBundleToBase C _ _ E r
    (pullback.fst g t) (pullback.snd q (pullback.fst g t)) (pullback.fst q (pullback.fst g t))
    (IsPullback.of_hasPullback _ _) _ _ m _

end Stacks.Chow

end
