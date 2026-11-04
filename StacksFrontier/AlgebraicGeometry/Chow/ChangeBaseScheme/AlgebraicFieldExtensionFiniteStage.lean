module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtension

/-!
# Descending the vanishing of a Chow class to a finite subextension

Let `K/k` be an algebraic extension of fields and let `X` be a quasi-compact scheme of finite
type over `k`. A `k`-cycle class on `X` whose base change to `X_K` vanishes already has
vanishing base change to `X_{k'}` for some finite subextension `K/k'/k`. This is the eventual
injectivity of Stacks 0FVQ, read through the presentation of `Spec K` as the limit of the
spectra of the finite subextensions.

## Main results

* `Stacks.Chow.stageChowPullback_baseChangeChowPullback` — base change from `k` to `K` factors
  through the stage of any finite subextension: the base change from `k` to `k'` followed by the
  comparison of that stage with the limit is the base change from `k` to `K`.
* `Stacks.Chow.transitionChowPullback_baseChangeChowPullback` — base change from `k` likewise
  commutes with the transitions of the system: the base change from `k` to `k''` followed by the
  transition `k' → k''` is the base change from `k` to `k'`.
* `Stacks.Chow.exists_finiteSubextension_baseChangeChowPullback_eq_zero` — a `k`-cycle class on
  `X` killed by the base-change homomorphism to `X_K` of Stacks 0FVJ is killed by the
  base-change homomorphism to `X_{k'}` for some finite subextension `K/k'/k`.

## Implementation notes

The system `Stacks.Chow.algebraicExtensionSystem` has one stage for every finite subextension,
and the eventual injectivity of Stacks 0FVQ applies to a class living on a stage, not to a class
on `X` itself. The stage of the trivial subextension `k' = ⊥` serves as the entry point: its
structure morphism `Spec ⊥ ⟶ Spec k` is an isomorphism, so the base change of the given class
there carries the same information, and the conclusion at a stage under `⊥` is a conclusion
about a finite subextension.

Both the passage into the system and the passage back out of it compare a composite of two
base-change homomorphisms with a single one, which is Stacks 0FVP. The composite of the base
changes `k → ⊥` and `⊥ → k'` is only propositionally the base change `k → k'`: the base-change
morphisms agree only after `AlgebraicGeometry.Spec.map_comp`, and the two cartesian squares
presenting the base change of `X` are different. So the comparison is made coefficientwise,
where the only datum of the base change entering a coefficient is the projection to `X` and the
multiplicity attached to it; the projections agree by the defining property of the projections
and transitions of the system, and the multiplicities agree by Stacks 0FVP part (2).

The dimension shift of a base change along a field extension vanishes, so the Chow groups
compared live in degrees `i` and `i + 0`; the two are propositionally but not definitionally
equal, and `Stacks.Chow.mem_rationalEquivalences_of_coeff_eq` transports membership in the
subgroup of rational equivalences between them.

The two factorizations are stated as equalities of classes rather than as that transport. What
makes this possible is that `Stacks.Chow.baseChangeChowPullbackOfIsPullback`, the base change
read through a chosen cartesian square, lands in the *unshifted* degree `i` — it composes
`Stacks.Chow.baseChangeChowPullback` with the degree identification `i + c = i` itself. Reading
the base changes out of `k` through the canonical square of
`CategoryTheory.Limits.pullback` therefore puts all three classes in degree `i`, where
`Stacks.Chow.baseChangeCyclePullbackOfIsPullback_hasPullback_apply` says their coefficients are
those of the base change of Stacks 0FVJ.

## References

* [Stacks Project, Tag 0FH8](https://stacks.math.columbia.edu/tag/0FH8)
* [Stacks Project, Tag 0FH6](https://stacks.math.columbia.edu/tag/0FH6)
* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 0FVP](https://stacks.math.columbia.edu/tag/0FVP)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Transporting rational equivalence between equal degrees -/

/-- A cycle with the same coefficients as a cycle rationally equivalent to zero is rationally
equivalent to zero, even when the two are presented in propositionally equal degrees. -/
theorem mem_rationalEquivalences_of_coeff_eq (D : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ D.S) [LocallyOfFiniteType q] {j l : ℤ} (hjl : j = l)
    {v : CycleGroup D q j} {w : CycleGroup D q l} (hvw : ∀ y, w.1 y = v.1 y)
    (hv : v ∈ rationalEquivalences D q j) : w ∈ rationalEquivalences D q l := by
  subst hjl
  rwa [show w = v from Subtype.ext (Function.locallyFinsuppWithin.ext hvw)]

/-! ### Coefficients of a composite of two base changes -/

/-- **Stacks Project, Tag 0FVP, part (2), as an identity of coefficients.** For two composable
flat base changes with vanishing dimension shifts and cartesian squares presenting them, the
coefficient of a cycle at the image point times the two multiplicities equals the coefficient at
the image point under the composite projection times the multiplicity for the composite.

Both base changes are read through `Stacks.Chow.baseChangeCyclePullbackSquare`, whose
coefficients are those of `Stacks.Chow.baseChangeCyclePullbackOfIsPullback` in the degree
shifted by the dimension shift; the shifts vanish, so the three resulting formulas are the three
products in the statement. -/
private theorem cycleCoeff_mul_flatPullbackWeight_comp (B : FlatBaseChangeSituation.{u})
    (hB : B.c = 0) (C : ChowSituation.{u}) (g' : C.S ⟶ B.baseChange.S) [Flat g']
    (hg' : ∀ (t : B.baseChange.S) (t' : genericPoints (g' ⁻¹' {t} : Set C.S)),
      C.dimensionFunction t'.1.1 = B.baseChange.dimensionFunction t + 0)
    {X Y Z : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f]
    {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q] (sq : IsPullback p q f B.g)
    {p' : Z ⟶ Y} {q' : Z ⟶ C.S} [LocallyOfFiniteType q'] (sq' : IsPullback p' q' q g')
    (j : ℤ) (z : CycleGroup B.base f j) (y : Z) :
    z.1 (p.base (p'.base y)) * flatPullbackWeight B.baseChange q p j (p'.base y) *
        flatPullbackWeight C q' p' j y =
      z.1 ((p' ≫ p).base y) * flatPullbackWeight C q' (p' ≫ p) j y := by
  have hcomp := baseChangeCyclePullbackSquare_comp_apply B C g' 0 hg' f sq sq' j z y
  rw [baseChangeCyclePullbackSquare_apply (FlatBaseChangeSituation.second B C g' 0 hg') q sq'
      (j + B.c) _ y,
    baseChangeCyclePullbackSquare_apply B f sq j z (p'.base y),
    baseChangeCyclePullbackSquare_apply (FlatBaseChangeSituation.comp B C g' 0 hg') f
      (sq'.paste_horiz sq) j z y] at hcomp
  simpa only [FlatBaseChangeSituation.second_baseChange, FlatBaseChangeSituation.second_c,
    FlatBaseChangeSituation.comp_baseChange, FlatBaseChangeSituation.comp_c, hB, add_zero,
    zero_add] using hcomp

/-- Base changing a cycle from `k` to an intermediate field `M` and then along a flat morphism
`Spec L ⟶ Spec M` gives, coefficientwise, the base change of the cycle from `k` to `L`, provided
the cartesian square presenting the second base change projects to the canonical one.

The two multiplicities multiply to the multiplicity of the composite by
`Stacks.Chow.cycleCoeff_mul_flatPullbackWeight_comp`, and the composite projection to `X` is the
canonical one by hypothesis. -/
private theorem baseChangeCycleCoeff_comp_eq (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] (h : (fieldChowSituation L).S ⟶ (fieldChowSituation M).S)
    [Flat h]
    (hdim : ∀ (t : (fieldChowSituation M).S)
        (t' : genericPoints (h ⁻¹' {t} : Set (fieldChowSituation L).S)),
      (fieldChowSituation L).dimensionFunction t'.1.1 =
        (fieldChowSituation M).dimensionFunction t + 0)
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    {r : (pullback f (fieldExtensionBaseChangeSituation k L).g : Scheme.{u}) ⟶
      (pullback f (fieldExtensionBaseChangeSituation k M).g : Scheme.{u})}
    (sq : IsPullback r (pullback.snd f (fieldExtensionBaseChangeSituation k L).g)
      (pullback.snd f (fieldExtensionBaseChangeSituation k M).g) h)
    (hr : r ≫ pullback.fst f (fieldExtensionBaseChangeSituation k M).g =
      pullback.fst f (fieldExtensionBaseChangeSituation k L).g)
    (j : ℤ) (z : CycleGroup (fieldChowSituation k) f j)
    (y : (pullback f (fieldExtensionBaseChangeSituation k L).g : Scheme.{u})) :
    (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k M) rfl f
          (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k M).g) j z).1
        (r.base y) *
      flatPullbackWeight (fieldChowSituation L)
        (pullback.snd f (fieldExtensionBaseChangeSituation k L).g) r j y =
      (baseChangeCyclePullback (fieldExtensionBaseChangeSituation k L) f j z).1 y := by
  rw [baseChangeCyclePullbackOfIsPullback_apply' (fieldExtensionBaseChangeSituation k M) rfl f
      (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k M).g) j z (r.base y),
    cycleCoeff_mul_flatPullbackWeight_comp (fieldExtensionBaseChangeSituation k M) rfl
      (fieldChowSituation L) h hdim f
      (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k M).g) sq j z y,
    hr, baseChangeCyclePullback_apply, fieldExtensionBaseChangeSituation_c, add_zero]

/-- The base change of a cycle read through the canonical cartesian square of
`CategoryTheory.Limits.pullback` has the coefficients of the base change of Stacks 0FVJ; the two
are presented in the degrees `j` and `j + B.c`, which agree because the dimension shift
vanishes. -/
private theorem baseChangeCyclePullbackOfIsPullback_hasPullback_apply
    (B : FlatBaseChangeSituation.{u}) (hc : B.c = 0) {X : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] (j : ℤ) (z : CycleGroup B.base f j)
    (y : (pullback f B.g : Scheme.{u})) :
    (baseChangeCyclePullbackOfIsPullback B hc f (IsPullback.of_hasPullback f B.g) j z).1 y =
      (baseChangeCyclePullback B f j z).1 y := by
  rw [baseChangeCyclePullbackOfIsPullback_apply' B hc f (IsPullback.of_hasPullback f B.g) j z y,
    baseChangeCyclePullback_apply B f j z y, hc, add_zero]

/-! ### Base change from the base factors through every stage -/

/-- Base changing a Chow class from `k` to `M` and then along a flat morphism `Spec L ⟶ Spec M`
is the base change from `k` to `L`, when both are read through canonical squares and the square
presenting the second base change projects to the canonical one. -/
private theorem baseChangeChowPullbackOfIsPullback_comp_eq (k L M : Type u) [Field k] [Field L]
    [Field M] [Algebra k L] [Algebra k M] (h : (fieldChowSituation L).S ⟶ (fieldChowSituation M).S)
    [Flat h]
    (hdim : ∀ (t : (fieldChowSituation M).S)
        (t' : genericPoints (h ⁻¹' {t} : Set (fieldChowSituation L).S)),
      (fieldChowSituation L).dimensionFunction t'.1.1 =
        (fieldChowSituation M).dimensionFunction t + 0)
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    {r : (pullback f (fieldExtensionBaseChangeSituation k L).g : Scheme.{u}) ⟶
      (pullback f (fieldExtensionBaseChangeSituation k M).g : Scheme.{u})}
    (sq : IsPullback r (pullback.snd f (fieldExtensionBaseChangeSituation k L).g)
      (pullback.snd f (fieldExtensionBaseChangeSituation k M).g) h)
    (hr : r ≫ pullback.fst f (fieldExtensionBaseChangeSituation k M).g =
      pullback.fst f (fieldExtensionBaseChangeSituation k L).g)
    (i : ℤ) (α : chowGroup (fieldChowSituation k) f i) :
    baseChangeChowPullbackOfIsPullback
        ⟨fieldChowSituation M, fieldChowSituation L, h, 0, hdim⟩ rfl
        (pullback.snd f (fieldExtensionBaseChangeSituation k M).g) sq i
        (baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k M) rfl f
          (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k M).g) i α) =
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl f
        (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k L).g) i α := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences (fieldChowSituation k) f i) α
  rw [baseChangeChowPullbackOfIsPullback_mk (fieldExtensionBaseChangeSituation k M) rfl f _ i z,
    baseChangeChowPullbackOfIsPullback_mk _ rfl _ sq i,
    baseChangeChowPullbackOfIsPullback_mk (fieldExtensionBaseChangeSituation k L) rfl f _ i z]
  refine congrArg (QuotientAddGroup.mk' _)
    (Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_))
  rw [baseChangeCyclePullbackOfIsPullback_apply' (B := ⟨fieldChowSituation M, fieldChowSituation L,
      h, 0, hdim⟩) rfl _ sq i _ y,
    baseChangeCycleCoeff_comp_eq k L M h hdim f sq hr i z y,
    baseChangeCyclePullbackOfIsPullback_hasPullback_apply
      (fieldExtensionBaseChangeSituation k L) rfl f i z y]

/-- **The base change of a Chow class from `k` to `K` factors through any finite subextension.**
The class base changed from `k` to a finite subextension `k'` and then compared to the limit
`K` by `Stacks.Chow.FilteredBaseChangeSystem.stageChowPullback` is the class base changed from
`k` to `K` directly.

Both base changes from `k` are read through the canonical cartesian square, so all three classes
live in degree `i` and the identity is an equality of classes rather than a transport along
`i + 0 = i`. Coefficientwise it is `Stacks.Chow.baseChangeCycleCoeff_comp_eq`, i.e. Stacks 0FVP
part (2) for the two base changes `k → k'` and `k' → K`. -/
theorem stageChowPullback_baseChangeChowPullback (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] (X : Over (fieldChowSituation k).S)
    [CompactSpace X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : (FiniteSubextension k K)ᵒᵖ) (i : ℤ)
    (α : chowGroup (fieldChowSituation k) X.hom i) :
    (algebraicExtensionSystem k K X).stageChowPullback a i
        (baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k a.unop.1) rfl
          X.hom (IsPullback.of_hasPullback X.hom
            (fieldExtensionBaseChangeSituation k a.unop.1).g) i α) =
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl X.hom
        (IsPullback.of_hasPullback X.hom (fieldExtensionBaseChangeSituation k K).g) i α := by
  let s : FilteredBaseChangeSystem.{u, u, u} (FiniteSubextension k K)ᵒᵖ :=
    algebraicExtensionSystem k K X
  have hflat : @Flat (fieldChowSituation K).S (fieldChowSituation a.unop.1).S
      (s.limitProjection a) := s.flat_limitProjection a
  exact baseChangeChowPullbackOfIsPullback_comp_eq k K a.unop.1 (s.limitProjection a)
    (s.stageToLimitBaseChange a).dimensionFunction_eq_add X.hom
    (s.isPullback_stageProjection a) (s.stageProjection_comp_fst a) i α

/-- **The base change of a Chow class from `k` to a finite subextension factors through any
larger finite subextension.** The class base changed from `k` to `k''` and then compared along
the transition `k' → k''` of `Stacks.Chow.algebraicExtensionSystem` is the class base changed
from `k` to `k'` directly.

As for `Stacks.Chow.stageChowPullback_baseChangeChowPullback`, the base changes from `k` are read
through the canonical cartesian square so that no degree transport is needed, and the identity is
`Stacks.Chow.baseChangeCycleCoeff_comp_eq` coefficientwise. -/
theorem transitionChowPullback_baseChangeChowPullback (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] (X : Over (fieldChowSituation k).S)
    [CompactSpace X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {a b : (FiniteSubextension k K)ᵒᵖ} (t : a ⟶ b) (i : ℤ)
    (α : chowGroup (fieldChowSituation k) X.hom i) :
    (algebraicExtensionSystem k K X).transitionChowPullback t i
        (baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k b.unop.1) rfl
          X.hom (IsPullback.of_hasPullback X.hom
            (fieldExtensionBaseChangeSituation k b.unop.1).g) i α) =
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k a.unop.1) rfl X.hom
        (IsPullback.of_hasPullback X.hom
          (fieldExtensionBaseChangeSituation k a.unop.1).g) i α := by
  let s : FilteredBaseChangeSystem.{u, u, u} (FiniteSubextension k K)ᵒᵖ :=
    algebraicExtensionSystem k K X
  have hflat : @Flat (fieldChowSituation a.unop.1).S (fieldChowSituation b.unop.1).S
      (s.diagram.map t) := s.transitionFlat t
  exact baseChangeChowPullbackOfIsPullback_comp_eq k a.unop.1 b.unop.1 (s.diagram.map t)
    (s.transitionBaseChange t).dimensionFunction_eq_add X.hom
    (s.isPullback_stageTransition t) (s.stageTransition_comp_fst t) i α

/-! ### Descent of a vanishing class to a finite subextension -/

/-- **A Chow class killed by base change along an algebraic extension is killed at a finite
stage.** Let `K/k` be an algebraic extension of fields, let `X` be a quasi-compact scheme of
finite type over `k`, and let `α` be a `k`-cycle class of dimension `i` on `X` whose base change
to `X_K` vanishes. Then there is a finite subextension `K/k'/k` whose base change already kills
`α`.

The class is the class of a cycle `z`. The base change of `z` to the trivial subextension `⊥` is
a cycle on the stage `X_⊥` of `Stacks.Chow.algebraicExtensionSystem`, and its base change to
`X_K` has the same coefficients as the base change of `z` to `X_K`, by
`Stacks.Chow.baseChangeCycleCoeff_comp_eq`; so its class on `X_⊥` is killed by the comparison
homomorphism to `CH_i(X_K)`. The eventual injectivity of Stacks 0FVQ provides a stage `k'` under
`⊥` whose transition homomorphism kills that class, and the same coefficient comparison,
applied now to the transition `X_{k'} ⟶ X_⊥`, identifies the transition of the cycle with the
base change of `z` to `X_{k'}`. -/
theorem exists_finiteSubextension_baseChangeChowPullback_eq_zero
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i : ℤ)
    (α : chowGroup (fieldChowSituation k) X.hom i)
    (hα : baseChangeChowPullback (fieldExtensionBaseChangeSituation k K) X.hom i α = 0) :
    ∃ E : FiniteSubextension k K,
      baseChangeChowPullback (fieldExtensionBaseChangeSituation k E.1) X.hom i α = 0 := by
  classical
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences (fieldChowSituation k) X.hom i) α
  rw [baseChangeChowPullback_mk (fieldExtensionBaseChangeSituation k K) X.hom i z] at hα
  have hmemK := (QuotientAddGroup.eq_zero_iff _).1 hα
  let s : FilteredBaseChangeSystem.{u, u, u} (FiniteSubextension k K)ᵒᵖ :=
    algebraicExtensionSystem k K X
  let E₀ : FiniteSubextension k K := ⟨⊥, inferInstance⟩
  let a₀ : (FiniteSubextension k K)ᵒᵖ := op E₀
  let z₀ : CycleGroup (s.stageSituation a₀) (pullback.snd s.X.hom (s.stageToBase a₀)) i :=
    baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k E₀.1) rfl X.hom
      (IsPullback.of_hasPullback X.hom (fieldExtensionBaseChangeSituation k E₀.1).g) i z
  have hflat : @Flat (fieldChowSituation K).S (fieldChowSituation E₀.1).S
      (s.limitProjection a₀) := s.flat_limitProjection a₀
  have hvanish : s.stageChowPullback a₀ i
      (QuotientAddGroup.mk' (rationalEquivalences (s.stageSituation a₀)
        (pullback.snd s.X.hom (s.stageToBase a₀)) i) z₀) = 0 := by
    rw [s.stageChowPullback_mk a₀ i z₀]
    refine (QuotientAddGroup.eq_zero_iff _).2
      (mem_rationalEquivalences_of_coeff_eq (fieldChowSituation K)
        (pullback.snd X.hom (fieldExtensionBaseChangeSituation k K).g) (add_zero i) ?_ hmemK)
    intro y
    exact (s.stageCyclePullback_apply a₀ i z₀ y).trans
      (baseChangeCycleCoeff_comp_eq k K E₀.1 (s.limitProjection a₀)
        (s.stageToLimitBaseChange a₀).dimensionFunction_eq_add X.hom
        (s.isPullback_stageProjection a₀) (s.stageProjection_comp_fst a₀) i z y)
  obtain ⟨a, t, ht⟩ := s.exists_transitionChowPullback_eq_zero a₀ i
    (QuotientAddGroup.mk' (rationalEquivalences (s.stageSituation a₀)
      (pullback.snd s.X.hom (s.stageToBase a₀)) i) z₀) hvanish
  refine ⟨a.unop, ?_⟩
  rw [s.transitionChowPullback_mk t i z₀] at ht
  have hmemE := (QuotientAddGroup.eq_zero_iff _).1 ht
  have hflat' : @Flat (fieldChowSituation a.unop.1).S (fieldChowSituation E₀.1).S
      (s.diagram.map t) := s.transitionFlat t
  rw [baseChangeChowPullback_mk (fieldExtensionBaseChangeSituation k a.unop.1) X.hom i z]
  refine (QuotientAddGroup.eq_zero_iff _).2
    (mem_rationalEquivalences_of_coeff_eq (fieldChowSituation a.unop.1)
      (pullback.snd X.hom (fieldExtensionBaseChangeSituation k a.unop.1).g)
      (add_zero i).symm ?_ hmemE)
  intro y
  exact (baseChangeCycleCoeff_comp_eq k a.unop.1 E₀.1 (s.diagram.map t)
    (s.transitionBaseChange t).dimensionFunction_eq_add X.hom
    (s.isPullback_stageTransition t) (s.stageTransition_comp_fst t) i z y).symm.trans
    (s.transitionCyclePullback_apply t i z₀ y).symm

end Stacks.Chow

end
