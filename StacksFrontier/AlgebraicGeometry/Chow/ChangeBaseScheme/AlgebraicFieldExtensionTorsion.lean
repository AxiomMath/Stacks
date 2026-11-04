module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtensionFiniteStage
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FieldExtensionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFreeTorsion
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceSituation
public import StacksCore.Tactic.StacksAttribute

/-!
# The kernel of Chow base change along an algebraic field extension is torsion

Let `K/k` be an algebraic extension of fields and let `X` be a scheme of finite type over `k`.
The kernel of the map `CH_i(X) ⟶ CH_i(X_K)` is torsion.

## Main results

* `Stacks.Chow.nsmul_eq_zero_of_baseChangeChowPullback_eq_zero_of_finiteDimensional`: a class
  killed by base change along a finite extension `E/k` is killed by `[E : k]`.
* `Stacks.Chow.isOfFinAddOrder_of_baseChangeChowPullback_eq_zero`: a class killed by base change
  along an algebraic extension `K/k` has finite additive order.

## References

* [Stacks Project, Tag 0FH8](https://stacks.math.columbia.edu/tag/0FH8)
* [Stacks Project, Tag 0FH6](https://stacks.math.columbia.edu/tag/0FH6)
* [Stacks Project, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

/-- For a finite extension `E/k` and `X` locally of finite type over `k`, a Chow class on `X`
killed by base change to `X_E` is killed by the degree `[E : k]`. -/
@[sga "6 XIV 4.2" "more general"]
theorem nsmul_eq_zero_of_baseChangeChowPullback_eq_zero_of_finiteDimensional
    (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f] (i : ℤ)
    (α : chowGroup (fieldChowSituation k) f i)
    (hα : baseChangeChowPullback (fieldExtensionBaseChangeSituation k E) f i α = 0) :
    Module.finrank k E • α = 0 := by
  classical
  have hflf : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) (Module.finrank k E) :=
    isFiniteLocallyFreeOfRank_pullbackFst_fieldExtension k E f
  have hlft : LocallyOfFiniteType (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)
  have hfl : Flat (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) :=
    Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)
  have hrd : AlgebraicGeometry.RelativeDimension
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) 0 :=
    Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences (fieldChowSituation k) f i) α
  rw [baseChangeChowPullback_mk (fieldExtensionBaseChangeSituation k E) f i z] at hα
  have hmem := (QuotientAddGroup.eq_zero_iff _).1 hα
  have hdimall : ∀ (W : Scheme.{u})
      (j : W ⟶ (pullback f (fieldExtensionBaseChangeSituation k E).g : Scheme.{u}))
      [IsClosedImmersion j],
      relativeDimension (fieldChowSituation E).dimensionFunction
          (j ≫ pullback.snd f (fieldExtensionBaseChangeSituation k E).g) =
        relativeDimension (fieldChowSituation k).dimensionFunction
          (j ≫ (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f)) := by
    intro W j _
    funext w
    have hcomp : j ≫ (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) =
        (j ≫ pullback.snd f (fieldExtensionBaseChangeSituation k E).g) ≫
          (fieldExtensionBaseChangeSituation k E).g := by
      rw [pullback.condition, Category.assoc]
    rw [hcomp]
    exact (relativeDimension_comp_fieldExtension k E
      (j ≫ pullback.snd f (fieldExtensionBaseChangeSituation k E).g) w).symm
  have hre := (isRationallyEquivalentToZero_congr (fieldChowSituation E) (fieldChowSituation k)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g)
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) hdimall
      (i + ((0 : ℕ) : ℤ))
      (baseChangeCyclePullback (fieldExtensionBaseChangeSituation k E) f i z)
      (flatPullback (fieldChowSituation k)
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl 0 hrd i z)
      (val_baseChangeCyclePullback_eq_val_flatPullback k E f hrd i z)).1 hmem
  exact nsmul_cycleClass_eq_zero_of_isRationallyEquivalentToZero_flatPullback
    (fieldChowSituation k) (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
    (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) (Module.finrank k E) rfl i z hre

/-- Let `K/k` be an algebraic extension of fields and let `X` be a scheme of finite type over
`k`. The kernel of the map `CH_i(X) ⟶ CH_i(X_K)` is torsion: every class it kills has finite
additive order. -/
@[stacks 0FH8]
theorem isOfFinAddOrder_of_baseChangeChowPullback_eq_zero (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] (X : Over (fieldChowSituation k).S)
    [CompactSpace X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (i : ℤ)
    (α : chowGroup (fieldChowSituation k) X.hom i)
    (hα : baseChangeChowPullback (fieldExtensionBaseChangeSituation k K) X.hom i α = 0) :
    IsOfFinAddOrder α := by
  obtain ⟨E, hE⟩ := exists_finiteSubextension_baseChangeChowPullback_eq_zero k K X i α hα
  have hfd : FiniteDimensional k E.1 := E.2
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  exact ⟨Module.finrank k ↥E.1, Module.finrank_pos,
    nsmul_eq_zero_of_baseChangeChowPullback_eq_zero_of_finiteDimensional k ↥E.1 X.hom i α hE⟩

end Stacks.Chow

end
