module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.RationalIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothComparison
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveGraphFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Pushforward and pullback of cycles by the graph of a morphism

Let `f : Y ⟶ X` be a morphism of smooth projective schemes over a field `k` and
`[Γ_f] ∈ Corr⁰(X, Y)` the class of its graph (Example 0FG1). Stacks 0FG5 computes the action of
`[Γ_f]` and of its transpose `[Γ_f]ᵗ` (Remark 0FG4) on Chow groups through the Gysin map and the
proper pushforward of `f`. This file proves the clauses of the lemma.

The computation is the source's, block by block on the parts `X_d × Y_e` of `X × Y` of
constant dimension. On a block the graph is a closed subscheme `γ : G ⟶ A × B` and every class of
the smooth scheme `B` is `c ∩ [B]` (Stacks 0FC2); then

  `[G] · pr₂^*(c ∩ [B]) = γ_*(res(c) ∩ [G])`

because `pr₂^*(c ∩ [B]) = res(c) ∩ [A × B]` (flat pullback commutes with bivariant classes), the
intersection product with `res(c) ∩ [A × B]` is capping with `res(c)` (Stacks 0FC2 again), and
capping commutes with proper pushforward. The class `res(c) ∩ [G]` is the restriction of
`c ∩ [B]` when `G ⟶ B` is an open immersion, and is `g^!(c ∩ [B])` for the Gysin map `g^!` of
the morphism `g : G ⟶ B` of smooth schemes (Stacks 0FF6, 0FF7) in general.

## Main definitions

* `Stacks.WeilCohomology.corrTranspose`: the transpose `Corrʳ(X, Y) ⟶ Corr^{d-e+r}(Y, X)` of
  Remark 0FG4 on the correspondences of Section 0FFZ between schemes of constant dimensions.
* `Stacks.WeilCohomology.transposeGraphCorr`,
  `Stacks.WeilCohomology.transposeGraphCorrespondenceSP`: the transposed graph
  `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)`.
* `Stacks.WeilCohomology.codimensionToCodimChow`,
  `Stacks.WeilCohomology.rationalCodimensionToCodimChow`: the identification
  `CH^i(X) ⊗ ℚ = ⊕_d CH_{d-i}(X_d) ⊗ ℚ` (bijective,
  `Stacks.WeilCohomology.rationalCodimensionToCodimChow_bijective`) between the Chow groups of
  Chapter 42 graded by codimension and the groups the correspondences of Section 0FFZ act on.

## Main results

* `Stacks.WeilCohomology.selfIntersectionProduct_properChowPushforward_fundamentalChowClass`:
  `γ_*[G] · (c ∩ [W]) = γ_*(res(c) ∩ [G])` for a closed subscheme `G` of a smooth `W`.
* `Stacks.WeilCohomology.pushforward_graphCorrespondenceSP`: **Stacks 0FG5 (1)**,
  `[Γ_f]_* = f^!` on `CH^*(X) ⊗ ℚ`.
* `Stacks.WeilCohomology.pullback_graphCorrespondenceSP`: **Stacks 0FG5 (2)**, `[Γ_f]^* = f_*`
  on `CH_*(Y) ⊗ ℚ`.
* `Stacks.WeilCohomology.pushforward_transposeGraphCorrespondenceSP`: **Stacks 0FG5 (3)(a)**,
  `([Γ_f]ᵗ)_* = f_*` for `X`, `Y` equidimensional.
* `Stacks.WeilCohomology.pullback_transposeGraphCorrespondenceSP`: **Stacks 0FG5 (3)(b)**,
  `([Γ_f]ᵗ)^* = f^!` for `X`, `Y` equidimensional.

The scheme-level forms are `pushforward_graphCorr_comp_rationalCodimensionToCodimChow`,
`pullback_graphCorr`, `pushforward_transposeGraphCorr_lof` and `pullback_transposeGraphCorr`.

## Implementation notes

The Gysin map is the one of Stacks 0FF3, `Stacks.Chow.lciGysinMap`: on classes graded by
codimension it is `Stacks.Chow.codimensionGysin` (for (1)), in a single degree
`Stacks.Chow.smoothGysinChow` (for (3)(b), the schemes being equidimensional there). The
intersection products are formed with the canonical Gysin classes of the diagonals,
`Stacks.WeilCohomology.canonicalDiagonalClassFamily`. "Equidimensional of dimension `d`" is
`RelativeDimension X.obj.hom d`.

## References

* [Stacks Project, Tag 0FG5](https://stacks.math.columbia.edu/tag/0FG5)
* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
* [Stacks Project, Tag 0FG4](https://stacks.math.columbia.edu/tag/0FG4)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.Chow

/-- **A Chow class is the sum of the pushforwards of its restrictions to the pieces** of a
decomposition into open and closed subschemes, over any finite set of indices containing those
of the nonempty pieces. -/
theorem sum_properChowPushforward_chowGroupRestrict_of_isClopenDecomposition
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {U : ℕ → X.Opens} (hU : IsClopenDecomposition U) (s : Finset ℕ)
    (hs : ∀ d, (U d : Set X).Nonempty → d ∈ s) (m : ℤ) (α : chowGroup C sX m) :
    ∑ d ∈ s, (haveI := hU.isProper_ι d
      properChowPushforward C ((U d).ι ≫ sX) sX (U d).ι rfl m
        (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict C sX ((U d).ι ≫ sX) (U d).ι rfl m α)) = α := by
  rw [← sub_eq_zero]
  refine eq_zero_of_chowGroupRestrict_eq_zero C sX (fun i : ULift.{u} ℕ ↦ (U i.down).ι ≫ sX)
    (fun i ↦ (U i.down).ι) (fun _ ↦ rfl) (hU.opensRange_ι_equiv Equiv.ulift) m _ fun i ↦ ?_
  rw [map_sub, map_sum, sub_eq_zero]
  by_cases hi : i.down ∈ s
  · rw [Finset.sum_eq_single i.down]
    · have := hU.isProper_ι i.down
      exact chowGroupRestrict_properChowPushforward_opens_self _ _ _ _ _ _
    · intro d _ hd
      have := hU.isProper_ι d
      exact chowGroupRestrict_properChowPushforward_opens_of_disjoint _ _ _ _
        (hU.disjoint d i.down hd) _ _ _
    · exact fun h ↦ (h hi).elim
  · have : IsEmpty (U i.down).toScheme := ⟨fun y ↦ hi (hs _ ⟨y.1, y.2⟩)⟩
    have := subsingleton_chowGroup_of_isEmpty C ((U i.down).ι ≫ sX) m
    exact Subsingleton.elim _ _

end Stacks.Chow

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **The intersection product with the class of a closed subscheme**, in cap form: for a closed
immersion `γ : G ⟶ W` into a scheme `W` smooth over `k` of constant dimension `n` and
`c ∈ A^p(W)`,

  `γ_*[G]_e · (c ∩ [W]_n) = γ_*(res(c) ∩ [G]_e)`. -/
theorem selfIntersectionProduct_properChowPushforward_fundamentalChowClass
    {W G : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    {n : ℕ} (hn : RelativeDimension sW n) (sG : G ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sG] (γ : G ⟶ W) [IsClosedImmersion γ] (hγ : γ ≫ sW = sG) (e p : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sW p) :
    selfIntersectionProduct (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k) (fieldGysinSystem k) sW n
        (canonicalDiagonalClassFamily k sW n hn) e ((n : ℤ) - p)
        (properChowPushforward (fieldChowSituation k) sG sW γ hγ e
          (properPushforwardDescends _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) sG e))
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sW n p c) =
      chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring)
        (properChowPushforward (fieldChowSituation k) sG sW γ hγ (e - p)
          (properPushforwardDescends _ _ _ _ _ _)
          (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sG e p
            (chowCohomologyRestrictionOfEq (fieldChowSituation k) sG sW hγ (fieldGysinSystem k)
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p c))) := by
  have hcap := canonicalDiagonalClassFamily_capEqProduct k sW n hn p c e
    (properChowPushforward (fieldChowSituation k) sG sW γ hγ e
      (properPushforwardDescends _ _ _ _ _ _) (fundamentalChowClass (fieldChowSituation k) sG e))
  rw [chowCohomologyCap_properChowPushforward_restriction _ _
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _),
    chowCohomologyCap_fundamentalChowClass] at hcap
  rw [canonicalDiagonalClassFamily_isSymmetric k sW n hn]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm
  rw [hcap]
  exact (chowGroupDegreeEquiv_heq _ _ _ _).symm

/-- **The cycle `c · pr₂^* β` of the pullback by a closed subscheme.** For a closed subscheme
`γ : G ⟶ A × B` of dimension `b - r`, `A`, `B` of dimensions `a`, `b`, and `β = c ∩ [B]_b`,

  `[G] · pr₂^*(c ∩ [B]_b) = γ_*(res(c) ∩ [G])`,

the restriction being along `γ ≫ pr₂ : G ⟶ B`. -/
theorem pullbackCycle_properChowPushforward_fundamentalChowClass_heq {A B G : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S)
    [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] {a b : ℕ}
    (hA : RelativeDimension sA a) (hB : RelativeDimension sB b)
    (sG : G ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sG] (γ : G ⟶ Limits.pullback sA sB)
    [IsClosedImmersion γ] (hγ : γ ≫ prodBase sA sB = sG) (hγB : (γ ≫ pullback.snd sA sB) ≫ sB = sG)
    (r p : ℤ) (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sB p) :
    pullbackCycle k sA sB (canonicalDiagonalClassFamily k) hA hB r ((b : ℤ) - p)
        (properChowPushforward (fieldChowSituation k) sG (prodBase sA sB) γ hγ ((b : ℤ) - r)
          (properPushforwardDescends _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) sG ((b : ℤ) - r)))
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sB b p c) ≍
      properChowPushforward (fieldChowSituation k) sG (prodBase sA sB) γ hγ ((b : ℤ) - r - p)
        (properPushforwardDescends _ _ _ _ _ _)
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sG
          ((b : ℤ) - r) p
          (chowCohomologyRestrictionOfEq (fieldChowSituation k) sG sB hγB (fieldGysinSystem k)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p c)) := by
  have hsnd : pullback.snd sA sB ≫ sB = prodBase sA sB := pullback.condition.symm
  have hpull := flatPullbackChow_chowCohomologyCapFundamentalClass' sB (prodBase sA sB)
    (pullback.snd sA sB) hsnd (relativeDimension_snd k sA sB hA) hB p c
  have hcore := selfIntersectionProduct_properChowPushforward_fundamentalChowClass
    (prodBase sA sB) (relativeDimension_prodBase k sA sB hA hB) sG γ hγ ((b : ℤ) - r) p
    (chowCohomologyRestrictionOfEq (fieldChowSituation k) (prodBase sA sB) sB hsnd
      (fieldGysinSystem k) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p c)
  rw [chowCohomologyRestrictionOfEq_restrictionOfEq sB (prodBase sA sB) sG
    (pullback.snd sA sB) γ hsnd hγ hγB] at hcore
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
    ((heq_of_eq hcore).trans (chowGroupDegreeEquiv_heq _ _ _ _)))
  refine selfIntersectionProduct_heq_of_heq _ _ _ rfl (by push_cast; ring) HEq.rfl
    (hpull.trans (chowCohomologyCapFundamentalClass_heq_of_eq _ (by push_cast; ring) _ _))

/-- **The cycle `c · pr₁^* α` of the pushforward by a closed subscheme.** For a closed subscheme
`γ : G ⟶ A × B` of dimension `b - r`, `A`, `B` of dimensions `a`, `b`, and `α = c ∩ [A]_a`,

  `[G] · pr₁^*(c ∩ [A]_a) = γ_*(res(c) ∩ [G])`,

the restriction being along `γ ≫ pr₁ : G ⟶ A`. -/
theorem pushforwardCycle_properChowPushforward_fundamentalChowClass_heq {A B G : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S)
    [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] {a b : ℕ}
    (hA : RelativeDimension sA a) (hB : RelativeDimension sB b)
    (sG : G ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sG] (γ : G ⟶ Limits.pullback sA sB)
    [IsClosedImmersion γ] (hγ : γ ≫ prodBase sA sB = sG) (hγA : (γ ≫ pullback.fst sA sB) ≫ sA = sG)
    (r p : ℤ) (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sA p) :
    pushforwardCycle k sA sB (canonicalDiagonalClassFamily k) hA hB r p
        (properChowPushforward (fieldChowSituation k) sG (prodBase sA sB) γ hγ ((b : ℤ) - r)
          (properPushforwardDescends _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) sG ((b : ℤ) - r)))
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sA a p c) ≍
      properChowPushforward (fieldChowSituation k) sG (prodBase sA sB) γ hγ ((b : ℤ) - r - p)
        (properPushforwardDescends _ _ _ _ _ _)
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sG
          ((b : ℤ) - r) p
          (chowCohomologyRestrictionOfEq (fieldChowSituation k) sG sA hγA (fieldGysinSystem k)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p c)) := by
  have hfst : pullback.fst sA sB ≫ sA = prodBase sA sB := rfl
  have hpull := flatPullbackChow_chowCohomologyCapFundamentalClass' sA (prodBase sA sB)
    (pullback.fst sA sB) hfst (relativeDimension_fst k sA sB hB) hA p c
  have hcore := selfIntersectionProduct_properChowPushforward_fundamentalChowClass
    (prodBase sA sB) (relativeDimension_prodBase k sA sB hA hB) sG γ hγ ((b : ℤ) - r) p
    (chowCohomologyRestrictionOfEq (fieldChowSituation k) (prodBase sA sB) sA hfst
      (fieldGysinSystem k) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p c)
  rw [chowCohomologyRestrictionOfEq_restrictionOfEq sA (prodBase sA sB) sG
    (pullback.fst sA sB) γ hfst hγ hγA] at hcore
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
    ((heq_of_eq hcore).trans (chowGroupDegreeEquiv_heq _ _ _ _)))
  refine selfIntersectionProduct_heq_of_heq _ _ _ rfl (by push_cast; ring) HEq.rfl
    (hpull.trans (chowCohomologyCapFundamentalClass_heq_of_eq _ (by push_cast; ring) _ _))

/-- The class of a closed subscheme is the pushforward of its fundamental class. -/
theorem mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward {T Z : Scheme.{u}}
    (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT]
    (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ] (ι : Z ⟶ T)
    [IsClosedImmersion ι] (hι : ι ≫ sT = sZ) (n : ℤ) :
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sT ι n) :
      chowGroup (fieldChowSituation k) sT n) =
      properChowPushforward (fieldChowSituation k) sZ sT ι hι n
        (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) sZ n) := by
  rw [fundamentalChowClass, properChowPushforward_mk,
    properPushforward_fundamentalCycle_of_isClosedImmersion]
  rfl

/-- **Pullback by the class of a closed subscheme**, on `c ∩ [B]_b`: for a closed subscheme
`γ : G ⟶ A × B` of dimension `b - r`, the pullback `[G]^*(c ∩ [B]_b)` is
`(γ ≫ pr₁)_*(res(c) ∩ [G])`, the restriction being along `γ ≫ pr₂ : G ⟶ B`. -/
theorem correspondencePullback_tmul_chowCohomologyCapFundamentalClass {A B G : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S)
    [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] [IsProper sB] {a b : ℕ}
    (hA : RelativeDimension sA a) (hB : RelativeDimension sB b)
    (sG : G ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sG] (γ : G ⟶ Limits.pullback sA sB)
    [IsClosedImmersion γ] (hγ : γ ≫ prodBase sA sB = sG)
    (hγB : (γ ≫ pullback.snd sA sB) ≫ sB = sG)
    [IsProper (γ ≫ pullback.fst sA sB)] (hγA : (γ ≫ pullback.fst sA sB) ≫ sA = sG)
    (r p : ℤ) (q : ℚ)
    (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sB p) :
    correspondencePullback k sA sB (canonicalDiagonalClassFamily k) hA hB r ((b : ℤ) - p)
        ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sA sB) γ ((b : ℤ) - r)))
        (q ⊗ₜ[ℤ] chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sB b
          p c) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) sA (by ring)
        (properChowPushforward (fieldChowSituation k) sG sA (γ ≫ pullback.fst sA sB) hγA
          ((b : ℤ) - r - p) (properPushforwardDescends _ _ _ _ _ _)
          (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sG
            ((b : ℤ) - r) p
            (chowCohomologyRestrictionOfEq (fieldChowSituation k) sG sB hγB (fieldGysinSystem k)
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p c))) := by
  rw [correspondencePullback, rationalBilin_tmul, one_mul]
  congr 1
  rw [LinearMap.compr₂_apply,
    mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward _ sG γ hγ]
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  have hgen := pullbackCycle_properChowPushforward_fundamentalChowClass_heq sA sB hA hB sG γ hγ hγB
    r p c
  refine (properChowPushforward_heq_congr _ _ _ (pullback.fst sA sB) rfl (by ring)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _
    hgen).trans ?_
  rw [properChowPushforward_comp_apply (fieldChowSituation k) sG (prodBase sA sB) sA γ
    (pullback.fst sA sB) (γ ≫ pullback.fst sA sB) rfl hγ rfl hγA _
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _)]

/-- **Pushforward by the class of a closed subscheme**, on `c ∩ [A]_a`: for a closed subscheme
`γ : G ⟶ A × B` of dimension `b - r`, the pushforward `[G]_*(c ∩ [A]_a)` is
`(γ ≫ pr₂)_*(res(c) ∩ [G])`, the restriction being along `γ ≫ pr₁ : G ⟶ A`. -/
theorem correspondencePushforward_tmul_chowCohomologyCapFundamentalClass {A B G : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S)
    [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] [IsProper sA] {a b : ℕ}
    (hA : RelativeDimension sA a) (hB : RelativeDimension sB b)
    (sG : G ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sG] (γ : G ⟶ Limits.pullback sA sB)
    [IsClosedImmersion γ] (hγ : γ ≫ prodBase sA sB = sG)
    (hγA : (γ ≫ pullback.fst sA sB) ≫ sA = sG)
    [IsProper (γ ≫ pullback.snd sA sB)] (hγB : (γ ≫ pullback.snd sA sB) ≫ sB = sG)
    (r p : ℤ) (q : ℚ)
    (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sA p) :
    correspondencePushforward k sA sB (canonicalDiagonalClassFamily k) hA hB r p
        ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sA sB) γ ((b : ℤ) - r)))
        (q ⊗ₜ[ℤ] chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sA a
          p c) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) sB (by ring)
        (properChowPushforward (fieldChowSituation k) sG sB (γ ≫ pullback.snd sA sB) hγB
          ((b : ℤ) - r - p) (properPushforwardDescends _ _ _ _ _ _)
          (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k) sG
            ((b : ℤ) - r) p
            (chowCohomologyRestrictionOfEq (fieldChowSituation k) sG sA hγA (fieldGysinSystem k)
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p c))) := by
  have hsnd : pullback.snd sA sB ≫ sB = prodBase sA sB := pullback.condition.symm
  rw [correspondencePushforward, rationalBilin_tmul, one_mul]
  congr 1
  rw [LinearMap.compr₂_apply,
    mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward _ sG γ hγ]
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  have hgen := pushforwardCycle_properChowPushforward_fundamentalChowClass_heq sA sB hA hB sG γ hγ
    hγA r p c
  refine (properChowPushforward_heq_congr _ _ _ (pullback.snd sA sB) hsnd (by ring)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _
    hgen).trans ?_
  rw [properChowPushforward_comp_apply (fieldChowSituation k) sG (prodBase sA sB) sB γ
    (pullback.snd sA sB) (γ ≫ pullback.snd sA sB) rfl hγ hsnd hγB _
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _)]

/-- **Pullback by the class of a closed subscheme projecting openly to the target.** For a
closed subscheme `γ : G ⟶ A × B` whose second projection `j = γ ≫ pr₂ : G ⟶ B` is an open
immersion, the pullback `[G]^* : CH_m(B) ⊗ ℚ ⟶ CH_m(A) ⊗ ℚ` is `β ↦ g_*(β|_G)`, for
`g = γ ≫ pr₁`. -/
theorem correspondencePullback_tmul_of_isOpenImmersion {A B G : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S)
    [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] [IsProper sB] {a b : ℕ}
    (hA : RelativeDimension sA a) (hB : RelativeDimension sB b)
    (sG : G ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sG] (γ : G ⟶ Limits.pullback sA sB)
    [IsClosedImmersion γ] (hγ : γ ≫ prodBase sA sB = sG)
    [IsOpenImmersion (γ ≫ pullback.snd sA sB)] (hγB : (γ ≫ pullback.snd sA sB) ≫ sB = sG)
    [IsProper (γ ≫ pullback.fst sA sB)] (hγA : (γ ≫ pullback.fst sA sB) ≫ sA = sG)
    (m : ℤ) (q : ℚ) (β : chowGroup (fieldChowSituation k) sB m) :
    correspondencePullback k sA sB (canonicalDiagonalClassFamily k) hA hB 0 m
        ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sA sB) γ ((b : ℤ) - 0))) (q ⊗ₜ[ℤ] β) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) sA (sub_zero m).symm
        (properChowPushforward (fieldChowSituation k) sG sA (γ ≫ pullback.fst sA sB) hγA m
          (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupRestrict (fieldChowSituation k) sB sG (γ ≫ pullback.snd sA sB) hγB m β)) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = (b : ℤ) - p := ⟨b - m, by ring⟩
  obtain ⟨c, rfl⟩ := capFundamentalClassSurjective k sB b hB p β
  rw [correspondencePullback_tmul_chowCohomologyCapFundamentalClass sA sB hA hB sG γ hγ hγB hγA
    0 p, chowGroupRestrict_chowCohomologyCapFundamentalClass_of_isOpenImmersion
    (fieldChowSituation k) (fieldGysinSystem k)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) sB p sG _ hγB b
    (schemeDeltaDimension_le_of_relativeDimension sB hB)]
  congr 1

/-- The part `X_d` is empty when `d` is not among the nonempty dimensions of `X`. -/
private theorem isEmpty_dimPart_of_notMem_nonemptyDimParts {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] [CompactSpace X] {d : ℕ}
    (hd : d ∉ nonemptyDimParts k sX) : IsEmpty (dimPart sX d).toScheme := by
  exact ⟨fun y ↦ hd ((mem_nonemptyDimParts k sX).2 ⟨_, y.2⟩)⟩

/-- The Chow groups of the part `X_d` vanish when `d` is not among the nonempty dimensions. -/
private theorem subsingleton_chowGroup_partBase_of_notMem_nonemptyDimParts {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] [CompactSpace X] {d : ℕ}
    (hd : d ∉ nonemptyDimParts k sX) (m : ℤ) :
    Subsingleton (chowGroup (fieldChowSituation k) (partBase sX d) m) := by
  have := isEmpty_dimPart_of_notMem_nonemptyDimParts sX hd
  exact subsingleton_chowGroup_of_isEmpty _ _ _

/-! ### Pullback by the graph -/

section GraphPullback

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
  {f : Y ⟶ X} (hf : f ≫ sX = sY)

include hf in
omit [Smooth sX] [Smooth sY] [IsSeparated sY] in
/-- A morphism from a proper scheme to a separated one over `k` is proper. -/
theorem isProper_of_comp_eq [IsProper sY] : IsProper f := by
  have : IsProper (f ≫ sX) := by rw [hf]; infer_instance
  exact IsProper.of_comp f sX

/-- The piece `Y_e ∩ f⁻¹(X_d)` of `Y`, the source of the `(d, e)` block of the graph. -/
abbrev graphPieceOpen (f : Y ⟶ X) (d e : ℕ) : (dimPart sY e).toScheme.Opens :=
  ((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d

/-- The inclusion of the piece `Y_e ∩ f⁻¹(X_d)` into `Y`. -/
abbrev graphPieceι (f : Y ⟶ X) (d e : ℕ) : (graphPieceOpen sX sY f d e).toScheme ⟶ Y :=
  (graphPieceOpen sX sY f d e).ι ≫ (dimPart sY e).ι

/-- The inclusion of the piece `Y_e ∩ f⁻¹(X_d)` into `Y` is an open immersion. -/
instance (f : Y ⟶ X) (d e : ℕ) : IsOpenImmersion (graphPieceι sX sY f d e) := by
  unfold graphPieceι; infer_instance

omit [IsSeparated sX] [IsSeparated sY] in
/-- The pieces `Y_e ∩ f⁻¹(X_d)`, `d ∈ ℕ`, decompose `Y_e` into open and closed subschemes. -/
theorem isClopenDecomposition_graphPieceOpen (f : Y ⟶ X) (e : ℕ) :
    IsClopenDecomposition fun d ↦ graphPieceOpen sX sY f d e :=
  (isClopenDecomposition_dimPart sX).preimage ((dimPart sY e).ι ≫ f)

/-- The inclusion of a piece `Y_e ∩ f⁻¹(X_d)` into `Y` is proper, the piece being closed. -/
instance isProper_graphPieceι (f : Y ⟶ X) (d e : ℕ) : IsProper (graphPieceι sX sY f d e) := by
  have := (isClopenDecomposition_graphPieceOpen sX sY f e).isProper_ι d
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  unfold graphPieceι; infer_instance

/-- **The `(d, e)` block of the pullback by the graph.** Pullback by the block of `[Γ_f]` on
`X_d × Y_e` sends `q ⊗ β` to `q ⊗ (f ∘ j)_*(j^*β)` for `j` the inclusion of
`Y_e ∩ f⁻¹(X_d)` into `Y`. -/
theorem pullback_lof_lof_graphBlock_tmul [IsProper sX] [IsProper sY] (m : ℤ) (d e : ℕ) (q : ℚ)
    (β : chowGroup (fieldChowSituation k) sY m) :
    haveI := isProper_of_comp_eq sX sY hf
    pullback k sX sY (canonicalDiagonalClassFamily k) 0 m
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (graphBlock k sX sY f hf d e))) (q ⊗ₜ[ℤ] β) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) sX (sub_zero m).symm
        (properChowPushforward (fieldChowSituation k)
          ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e) sX
          (graphPieceι sX sY f d e ≫ f) (by rw [Category.assoc, hf, Category.assoc]) m
          (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupRestrict (fieldChowSituation k) sY
            ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e)
            (graphPieceι sX sY f d e) (Category.assoc _ _ _) m β)) := by
  have := isProper_of_comp_eq sX sY hf
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  have : IsOpenImmersion (graphPiece k sX sY f hf d e ≫
      pullback.snd (partBase sX d) (partBase sY e)) := by
    rw [graphPiece_snd]; infer_instance
  have : IsProper (graphPiece k sX sY f hf d e ≫
      pullback.fst (partBase sX d) (partBase sY e)) := inferInstance
  rw [pullback_lof_lof, restrictPart, LinearMap.baseChange_tmul, graphBlock,
    correspondencePullback_tmul_of_isOpenImmersion (partBase sX d) (partBase sY e)
      (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) _
      (graphPiece k sX sY f hf d e) (graphPiece_prodBase k sX sY f hf d e)
      (by rw [graphPiece_snd]) (by rw [← graphPiece_prodBase k sX sY f hf d e, prodBase,
        Category.assoc])]
  rw [includePart, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.coe_toIntLinearMap,
    properChowPushforward_chowGroupDegreeEquiv (hfack := properPushforwardDescends _ _ _ _ _ _)]
  congr 2
  rw [chowGroupRestrict_comp, chowGroupRestrict_congr (j' := graphPieceι sX sY f d e)
      (hjj' := by rw [graphPiece_snd]) (hj' := Category.assoc _ _ _),
    ← properChowPushforward_comp_apply (fieldChowSituation k) _ (partBase sX d) sX _
      (dimPart sX d).ι (graphPieceι sX sY f d e ≫ f) (by
        rw [graphPiece_fst, morphismRestrict_ι, Category.assoc])]

omit [IsSeparated sX] [IsSeparated sY] in
/-- **The pieces `Y_e ∩ f⁻¹(X_d)` decompose `CH_*(Y)`**: a class is the sum over the nonempty
pieces of the pushforwards of its restrictions. -/
theorem sum_properChowPushforward_chowGroupRestrict_graphPieceι [IsProper sX] [IsProper sY]
    (m : ℤ) (β : chowGroup (fieldChowSituation k) sY m) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    ∑ d ∈ nonemptyDimParts k sX, ∑ e ∈ nonemptyDimParts k sY,
      properChowPushforward (fieldChowSituation k)
        ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e) sY (graphPieceι sX sY f d e)
        (Category.assoc _ _ _) m (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation k) sY
          ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e)
          (graphPieceι sX sY f d e) (Category.assoc _ _ _) m β) = β := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  rw [Finset.sum_comm]
  conv_rhs => rw [← sum_properChowPushforward_chowGroupRestrict_dimPart k sY m β]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  have hs : ∀ d, (graphPieceOpen sX sY f d e : Set (dimPart sY e).toScheme).Nonempty →
      d ∈ nonemptyDimParts k sX := fun d ⟨y, hy⟩ ↦
    (mem_nonemptyDimParts k sX).2 ⟨_, hy⟩
  rw [← sum_properChowPushforward_chowGroupRestrict_of_isClopenDecomposition (fieldChowSituation k)
    (partBase sY e) (isClopenDecomposition_graphPieceOpen sX sY f e) (nonemptyDimParts k sX) hs m
    (chowGroupRestrict (fieldChowSituation k) sY (partBase sY e) (dimPart sY e).ι rfl m β),
    map_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have := (isClopenDecomposition_graphPieceOpen sX sY f e).isProper_ι d
  rw [chowGroupRestrict_comp, properChowPushforward_comp_apply (fieldChowSituation k) _
    (partBase sY e) sY (graphPieceOpen sX sY f d e).ι (dimPart sY e).ι (graphPieceι sX sY f d e)
    rfl]

/-- **Stacks 0FG5 (2), for schemes**: pullback of cycles by the graph `[Γ_f] ∈ Corr⁰(X, Y)` of
`f : Y ⟶ X` is proper pushforward `f_* : CH_m(Y) ⊗ ℚ ⟶ CH_m(X) ⊗ ℚ`. -/
theorem pullback_graphCorr [IsProper sX] [IsProper sY] (m : ℤ) :
    haveI := isProper_of_comp_eq sX sY hf
    pullback k sX sY (canonicalDiagonalClassFamily k) 0 m (graphCorr k sX sY f hf) =
      ((chowGroupDegreeEquiv (fieldChowSituation k) sX (sub_zero m).symm).toAddMonoidHom.comp
        (properChowPushforward (fieldChowSituation k) sY sX f hf m
          (properPushforwardDescends _ _ _ _ _ _))).toIntLinearMap.baseChange ℚ := by
  have := isProper_of_comp_eq sX sY hf
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  rw [graphCorr_eq_sum k sX sY f hf (D := nonemptyDimParts k sX) (E := nonemptyDimParts k sY)
    (fun d ⟨y, hy⟩ ↦ (mem_nonemptyDimParts k sX).2 ⟨_, hy⟩)
    (fun e he ↦ (mem_nonemptyDimParts k sY).2 he)]
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul q β =>
    simp only [map_sum, LinearMap.sum_apply, pullback_lof_lof_graphBlock_tmul,
      ← TensorProduct.tmul_sum, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    congr 1
    conv_rhs => rw [← sum_properChowPushforward_chowGroupRestrict_graphPieceι sX sY (f := f) m β]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
    rw [properChowPushforward_comp_apply (fieldChowSituation k) _ sY sX (graphPieceι sX sY f d e) f
      _ rfl (Category.assoc _ _ _) hf]

omit [IsSeparated sX] [IsSeparated sY] in
/-- The piece `Y_e ∩ f⁻¹(X_d)` is empty when `X_d` is. -/
theorem isEmpty_graphPieceOpen_of_left (f : Y ⟶ X) {d : ℕ} (e : ℕ)
    (h : IsEmpty (dimPart sX d).toScheme) : IsEmpty (graphPieceOpen sX sY f d e).toScheme :=
  ⟨fun y ↦ h.false ⟨_, y.2⟩⟩

omit [IsSeparated sX] [IsSeparated sY] in
/-- The piece `Y_e ∩ f⁻¹(X_d)` is empty when `Y_e` is. -/
theorem isEmpty_graphPieceOpen_of_right (f : Y ⟶ X) (d : ℕ) {e : ℕ}
    (h : IsEmpty (dimPart sY e).toScheme) : IsEmpty (graphPieceOpen sX sY f d e).toScheme :=
  ⟨fun y ↦ h.false y.1⟩

omit [IsSeparated sX] [IsSeparated sY] in
/-- A term of the decomposition of `CH_*(Y)` by the pieces vanishes on an empty piece. -/
theorem properChowPushforward_chowGroupRestrict_graphPieceι_of_isEmpty (f : Y ⟶ X) (d e : ℕ)
    [IsEmpty (graphPieceOpen sX sY f d e).toScheme] (m : ℤ)
    (β : chowGroup (fieldChowSituation k) sY m) :
    properChowPushforward (fieldChowSituation k)
        ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e) sY (graphPieceι sX sY f d e)
        (Category.assoc _ _ _) m (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation k) sY
          ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e)
          (graphPieceι sX sY f d e) (Category.assoc _ _ _) m β) = 0 := by
  have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
    ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e) m
  rw [Subsingleton.elim (chowGroupRestrict _ _ _ _ _ _ β) 0, map_zero]

omit [IsSeparated sX] [IsSeparated sY] in
/-- **For `X` and `Y` of constant dimensions `d` and `e` the piece `Y_e ∩ f⁻¹(X_d)` is all of
`Y`**: pushing forward a restriction to it returns the class. -/
theorem properChowPushforward_chowGroupRestrict_graphPieceι_of_relativeDimension
    [IsProper sX] [IsProper sY] {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (m : ℤ) (β : chowGroup (fieldChowSituation k) sY m) :
    properChowPushforward (fieldChowSituation k)
        ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e) sY (graphPieceι sX sY f d e)
        (Category.assoc _ _ _) m (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation k) sY
          ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e)
          (graphPieceι sX sY f d e) (Category.assoc _ _ _) m β) = β := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  conv_rhs => rw [← sum_properChowPushforward_chowGroupRestrict_graphPieceι sX sY (f := f) m β]
  have hXd : ∀ d', d' ∉ nonemptyDimParts k sX ∨ d' ≠ d → IsEmpty (dimPart sX d').toScheme :=
    fun d' h ↦ h.elim (isEmpty_dimPart_of_notMem_nonemptyDimParts sX) (isEmpty_dimPart_of_ne sX hX)
  have hYe : ∀ e', e' ∉ nonemptyDimParts k sY ∨ e' ≠ e → IsEmpty (dimPart sY e').toScheme :=
    fun e' h ↦ h.elim (isEmpty_dimPart_of_notMem_nonemptyDimParts sY) (isEmpty_dimPart_of_ne sY hY)
  rw [Finset.sum_eq_single d, Finset.sum_eq_single e]
  · intro e' _ he'
    have := isEmpty_graphPieceOpen_of_right sX sY f d (hYe e' (Or.inr he'))
    exact properChowPushforward_chowGroupRestrict_graphPieceι_of_isEmpty sX sY f d e' m β
  · intro he
    have := isEmpty_graphPieceOpen_of_right sX sY f d (hYe e (Or.inl he))
    exact properChowPushforward_chowGroupRestrict_graphPieceι_of_isEmpty sX sY f d e m β
  · intro d' _ hd'
    refine Finset.sum_eq_zero fun e' _ ↦ ?_
    have := isEmpty_graphPieceOpen_of_left sX sY f e' (hXd d' (Or.inr hd'))
    exact properChowPushforward_chowGroupRestrict_graphPieceι_of_isEmpty sX sY f d' e' m β
  · intro hd
    refine Finset.sum_eq_zero fun e' _ ↦ ?_
    have := isEmpty_graphPieceOpen_of_left sX sY f e' (hXd d (Or.inl hd))
    exact properChowPushforward_chowGroupRestrict_graphPieceι_of_isEmpty sX sY f d e' m β

omit [IsSeparated sX] [IsSeparated sY] in
/-- The first projection of the graph piece is the restriction `f_{e,d} : Y_{e,d} ⟶ X_d` of `f` to
the piece `Y_{e,d} = Y_e ∩ f⁻¹(X_d)` on which the Gysin map of `f` is formed. -/
theorem graphPiece_fst_eq_dimPartPieceHom (d e : ℕ) :
    graphPiece k sX sY f hf d e ≫ pullback.fst (partBase sX d) (partBase sY e) =
      dimPartPieceHom sY sX f e d := by
  rw [graphPiece_fst, morphismRestrict_comp]

end GraphPullback

/-! ### Pushforward by the graph -/

section GraphPushforward

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]

variable (k) in
/-- **The class of `α ∈ CH^i(X)` in `CH^i(X) ⊗ ℚ`**, for `X` smooth and quasi-compact over `k`:
`α = (α_d)_d ∈ CH^i(X) = ∏_d CH_{d-i}(X_d)` (`Stacks.Chow.codimensionChowGroup`) goes to
`∑_d 1 ⊗ α_d ∈ ⊕_d CH_{d-i}(X_d) ⊗ ℚ` (`Stacks.WeilCohomology.CodimChow`), the sum over the
finitely many nonempty parts `X_d`. -/
def codimensionToCodimChow [CompactSpace X] (i : ℤ) :
    codimensionChowGroup k sX i →+ CodimChow k sX i where
  toFun a := ∑ d ∈ nonemptyDimParts k sX, DirectSum.lof ℚ ℕ (fun d : ℕ ↦
    TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))) d
      ((1 : ℚ) ⊗ₜ[ℤ] a d)
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

variable (k) in
/-- **The map `CH^i(X) ⊗ ℚ ⟶ ⊕_d CH_{d-i}(X_d) ⊗ ℚ`**, `q ⊗ α ↦ q ∑_d 1 ⊗ α_d`, through which the
correspondences of Section 0FFZ act on the Chow groups of Chapter 42 graded by codimension. -/
def rationalCodimensionToCodimChow [CompactSpace X] (i : ℤ) :
    TensorProduct ℤ ℚ (codimensionChowGroup k sX i) →ₗ[ℚ] CodimChow k sX i :=
  LinearMap.liftBaseChange ℚ (codimensionToCodimChow k sX i).toIntLinearMap

omit [IsSeparated sX] in
/-- `Stacks.WeilCohomology.rationalCodimensionToCodimChow` on a pure tensor. -/
theorem rationalCodimensionToCodimChow_tmul [CompactSpace X] (i : ℤ) (q : ℚ)
    (a : codimensionChowGroup k sX i) :
    rationalCodimensionToCodimChow k sX i (q ⊗ₜ[ℤ] a) = q • codimensionToCodimChow k sX i a := by
  rw [rationalCodimensionToCodimChow, LinearMap.liftBaseChange_tmul,
    AddMonoidHom.coe_toIntLinearMap]

omit [IsSeparated sX] in
/-- On a scheme with only finitely many nonempty parts, a class of `CH^i(X)` is the sum of its
components. -/
theorem sum_pi_single_codimensionChowGroup [CompactSpace X] (i : ℤ)
    (α : codimensionChowGroup k sX i) :
    ∑ d ∈ nonemptyDimParts k sX, Pi.single (M := fun d : ℕ ↦
      chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i)) d (α d) = α := by
  funext d
  rw [Finset.sum_apply, Finset.sum_pi_single]
  split_ifs with hd
  · rfl
  · have := subsingleton_chowGroup_partBase_of_notMem_nonemptyDimParts sX hd ((d : ℤ) - i)
    exact Subsingleton.elim _ _

variable (k) in
/-- The inverse of `Stacks.WeilCohomology.rationalCodimensionToCodimChow`:
`q ⊗ a ∈ CH_{d-i}(X_d) ⊗ ℚ` goes to `q ⊗ a`, with `a` read as a class of `CH^i(X)` concentrated
on `X_d`. -/
def codimChowToRationalCodimension (i : ℤ) :
    CodimChow k sX i →ₗ[ℚ] TensorProduct ℤ ℚ (codimensionChowGroup k sX i) :=
  DirectSum.toModule ℚ ℕ _ fun d ↦ (LinearMap.single ℤ (fun d : ℕ ↦
    chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i)) d).baseChange ℚ

omit [IsSeparated sX] in
/-- **`CH^i(X) ⊗ ℚ = ⊕_d CH_{d-i}(X_d) ⊗ ℚ`**: for `X` smooth and quasi-compact over `k` the map
`Stacks.WeilCohomology.rationalCodimensionToCodimChow` is an isomorphism, so the identities of
Stacks 0FG5 read through it are identities on `CH^i(X) ⊗ ℚ`. -/
theorem rationalCodimensionToCodimChow_bijective [CompactSpace X] (i : ℤ) :
    Function.Bijective (rationalCodimensionToCodimChow k sX i) := by
  refine Function.bijective_iff_has_inverse.2 ⟨codimChowToRationalCodimension k sX i, ?_, ?_⟩
  · intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul q α =>
      rw [rationalCodimensionToCodimChow_tmul, map_smul, codimensionToCodimChow,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum]
      simp only [codimChowToRationalCodimension, DirectSum.toModule_lof,
        LinearMap.baseChange_tmul, LinearMap.single_apply]
      rw [← TensorProduct.tmul_sum, sum_pi_single_codimensionChowGroup, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
  · intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | of d y =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
      | tmul q a =>
        rw [← DirectSum.lof_eq_of ℚ]
        simp only [codimChowToRationalCodimension, DirectSum.toModule_lof,
          LinearMap.baseChange_tmul, LinearMap.single_apply, rationalCodimensionToCodimChow_tmul,
          codimensionToCodimChow, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        by_cases hd : d ∈ nonemptyDimParts k sX
        · rw [Finset.sum_eq_single d (fun d' _ hd' ↦ by
              rw [Pi.single_eq_of_ne hd', TensorProduct.tmul_zero, map_zero])
            (fun h ↦ (h hd).elim), Pi.single_eq_same, ← map_smul, TensorProduct.smul_tmul',
            smul_eq_mul, mul_one]
        · have := subsingleton_chowGroup_partBase_of_notMem_nonemptyDimParts sX hd ((d : ℤ) - i)
          simp [Subsingleton.elim a 0]

omit [IsSeparated sX] in
/-- For `X` of constant dimension `d` the class of `α ∈ CH^i(X)` in `CH^i(X) ⊗ ℚ` is `1 ⊗ α_d`
in the summand `d`. -/
theorem codimensionToCodimChow_of_relativeDimension [CompactSpace X] {d : ℕ}
    (hX : RelativeDimension sX d) (i : ℤ) (α : codimensionChowGroup k sX i) :
    codimensionToCodimChow k sX i α =
      DirectSum.lof ℚ ℕ (fun d : ℕ ↦
        TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))) d
        ((1 : ℚ) ⊗ₜ[ℤ] α d) := by
  have hzero : ∀ d', IsEmpty (dimPart sX d').toScheme → α d' = 0 := fun d' _ ↦
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase sX d')
      ((d' : ℤ) - i)
    Subsingleton.elim _ _
  simp only [codimensionToCodimChow, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single d]
  · intro d' _ hd'
    rw [hzero d' (isEmpty_dimPart_of_ne sX hX hd'), TensorProduct.tmul_zero, map_zero]
  · intro hd
    rw [hzero d (isEmpty_dimPart_of_notMem_nonemptyDimParts sX hd), TensorProduct.tmul_zero,
      map_zero]

/-- **The `(d, e)` block of the pushforward by the graph**: for `a ∈ CH_{d-i}(X_d)`, pushforward by
the block of `[Γ_f]` on `X_d × Y_e` is `j_*(f^!a)` for the Gysin map `f^!` of `f` on the piece
`Y_{e,d} = Y_e ∩ f⁻¹(X_d)` and `j` its inclusion into `Y_e`. -/
theorem correspondencePushforward_graphBlock_tmul [IsProper sX] [IsProper sY] {f : Y ⟶ X}
    (hf : f ≫ sX = sY) (i : ℤ) (d e : ℕ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i)) :
    haveI := locallyOfFiniteType_of_comp_eq hf
    haveI : IsProper (dimPartPiece sY sX f e d).ι :=
      (isClopenDecomposition_graphPieceOpen sX sY f e).isProper_ι d
    correspondencePushforward k (partBase sX d) (partBase sY e) (canonicalDiagonalClassFamily k)
        (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) 0 i
        (graphBlock k sX sY f hf d e) ((1 : ℚ) ⊗ₜ[ℤ] a) =
      (1 : ℚ) ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) (partBase sY e) (by ring)
        (properChowPushforward (fieldChowSituation k) (dimPartPieceBase sY sX f e d)
          (partBase sY e) (dimPartPiece sY sX f e d).ι rfl ((e : ℤ) - i)
          (properPushforwardDescends _ _ _ _ _ _) (dimPartPieceGysin sY sX hf e d i a)) := by
  have := locallyOfFiniteType_of_comp_eq hf
  have : IsProper (((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d).ι :=
    (isClopenDecomposition_graphPieceOpen sX sY f e).isProper_ι d
  have : IsProper (dimPartPiece sY sX f e d).ι :=
    (isClopenDecomposition_graphPieceOpen sX sY f e).isProper_ι d
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  have : IsProper (graphPiece k sX sY f hf d e ≫
      pullback.snd (partBase sX d) (partBase sY e)) := by
    rw [graphPiece_snd]; infer_instance
  obtain ⟨c, rfl⟩ := capFundamentalClassSurjective k (partBase sX d) d
    (relativeDimension_partBase sX d) i a
  rw [graphBlock, correspondencePushforward_tmul_chowCohomologyCapFundamentalClass (partBase sX d)
    (partBase sY e) (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) _
    (graphPiece k sX sY f hf d e) (graphPiece_prodBase k sX sY f hf d e)
    (by rw [Category.assoc, graphPiece_fst_assoc, morphismRestrict_ι_assoc, Category.assoc, hf])
    (by rw [graphPiece_snd])]
  congr 1
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
    (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  rw [properChowPushforward_congr (fieldChowSituation k) _ _
    (graphPiece k sX sY f hf d e ≫ pullback.snd (partBase sX d) (partBase sY e))
    (graphPieceOpen sX sY f d e).ι (graphPiece_snd k sX sY f hf d e) _ rfl
    (hfacg := properPushforwardDescends _ _ _ _ _ _)]
  refine properChowPushforward_heq_congr _ _ _ _ _ (by ring) _ _ _ _ ?_
  refine (chowCohomologyCapFundamentalClass_heq_of_eq _ (by ring) _ _).trans ?_
  rw [@Stacks.Chow.chowCohomologyRestrictionOfEq_congr (fieldChowSituation k) _ _ (partBase sX d) _
    ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e) _ _ (dimPartPieceHom sY sX f e d) _
    (@locallyOfFiniteType_of_comp_eq _ _ _ _ _ _ (dimPartPieceHom_comp_partBase sY sX hf e d)
      (inferInstance : LocallyOfFiniteType (dimPartPieceBase sY sX f e d)))
    (graphPiece_fst_eq_dimPartPieceHom sX sY hf d e) _
    (dimPartPieceHom_comp_partBase sY sX hf e d)]
  exact (dimPartPieceGysin_chowCohomologyCapFundamentalClass sY sX hf e d i c).symm


omit [IsSeparated sY] in
/-- Pushforward by the graph of a class concentrated on the part `X_d`: only the blocks `(d, e)`
contribute. -/
theorem pushforward_graphCorr_lof [IsProper sX] [IsProper sY] {f : Y ⟶ X} (hf : f ≫ sX = sY)
    (i : ℤ) {d : ℕ} (hd : (dimPart sX d : Set X).Nonempty)
    (x : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))) :
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    pushforward k sX sY (canonicalDiagonalClassFamily k) 0 i (graphCorr k sX sY f hf)
        (DirectSum.lof ℚ ℕ _ d x) =
      ∑ e ∈ nonemptyDimParts k sY, DirectSum.lof ℚ ℕ _ e
        (correspondencePushforward k (partBase sX d) (partBase sY e)
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sX d)
          (relativeDimension_partBase sY e) 0 i (graphBlock k sX sY f hf d e) x) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  rw [graphCorr_eq_sum k sX sY f hf (D := nonemptyDimParts k sX) (E := nonemptyDimParts k sY)
    (fun d ⟨y, hy⟩ ↦ (mem_nonemptyDimParts k sX).2 ⟨_, hy⟩)
    (fun e he ↦ (mem_nonemptyDimParts k sY).2 he), map_sum, LinearMap.sum_apply,
    Finset.sum_eq_single d]
  · simp only [map_sum, LinearMap.sum_apply, pushforward_lof_lof_lof]
  · intro d' _ hd'
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun e _ ↦ pushforward_lof_lof_lof_of_ne k
      (canonicalDiagonalClassFamily k) sX sY 0 i (Ne.symm hd') e _ _
  · exact fun h ↦ (h ((mem_nonemptyDimParts k sX).2 hd)).elim

/-- **Stacks 0FG5 (1), for schemes**: pushforward of cycles by the graph `[Γ_f] ∈ Corr⁰(X, Y)` of
`f : Y ⟶ X` is the Gysin map `f^! : CH^i(X) ⟶ CH^i(Y)` of Stacks 0FF3, on classes of
`CH^i(X) = ∏_d CH_{d-i}(X_d)` read in `CH^i(X) ⊗ ℚ`. -/
theorem pushforward_graphCorr_codimensionToCodimChow [IsProper sX] [IsProper sY] {f : Y ⟶ X}
    (hf : f ≫ sX = sY) (i : ℤ) (α : codimensionChowGroup k sX i) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := locallyOfFiniteType_of_comp_eq hf
    pushforward k sX sY (canonicalDiagonalClassFamily k) 0 i (graphCorr k sX sY f hf)
        (codimensionToCodimChow k sX i α) =
      codimChowCongr k sY (add_zero i).symm
        (codimensionToCodimChow k sY i (codimensionGysin sY sX hf i α)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have := locallyOfFiniteType_of_comp_eq hf
  simp only [codimensionToCodimChow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum]
  rw [Finset.sum_congr rfl fun d hd ↦ pushforward_graphCorr_lof sX sY hf i
    ((mem_nonemptyDimParts k sX).1 hd) _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  simp only [correspondencePushforward_graphBlock_tmul, codimChowCongr_lof,
    LinearEquiv.baseChange_tmul, ← map_sum, ← TensorProduct.tmul_sum]
  rw [AddEquiv.coe_toIntLinearEquiv]
  have hs : ∀ d, (dimPartPiece sY sX f e d : Set (dimPart sY e).toScheme).Nonempty →
      d ∈ nonemptyDimParts k sX := fun d ⟨y, hy⟩ ↦ (mem_nonemptyDimParts k sX).2 ⟨_, hy⟩
  conv_rhs => rw [← sum_properChowPushforward_chowGroupRestrict_of_isClopenDecomposition
    (fieldChowSituation k) (partBase sY e) (U := fun d ↦ dimPartPiece sY sX f e d)
    (isClopenDecomposition_graphPieceOpen sX sY f e) (nonemptyDimParts k sX) hs _
    (codimensionGysin sY sX hf i α e)]
  congr 3
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [chowGroupRestrict_codimensionGysin]

/-- **Stacks 0FG5 (1), for schemes, with rational coefficients**: on `CH^i(X) ⊗ ℚ`, pushforward
of cycles by the graph `[Γ_f]` is `f^! ⊗ ℚ`. -/
theorem pushforward_graphCorr_comp_rationalCodimensionToCodimChow [IsProper sX] [IsProper sY]
    {f : Y ⟶ X} (hf : f ≫ sX = sY) (i : ℤ) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := locallyOfFiniteType_of_comp_eq hf
    pushforward k sX sY (canonicalDiagonalClassFamily k) 0 i (graphCorr k sX sY f hf) ∘ₗ
        rationalCodimensionToCodimChow k sX i =
      (codimChowCongr k sY (add_zero i).symm).toLinearMap ∘ₗ
        rationalCodimensionToCodimChow k sY i ∘ₗ
          (codimensionGysin sY sX hf i).toIntLinearMap.baseChange ℚ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have := locallyOfFiniteType_of_comp_eq hf
  refine TensorProduct.AlgebraTensorModule.ext fun q α ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, rationalCodimensionToCodimChow_tmul,
    LinearMap.baseChange_tmul, map_smul, AddMonoidHom.coe_toIntLinearMap,
    pushforward_graphCorr_codimensionToCodimChow, LinearEquiv.coe_coe]

end GraphPushforward

/-! ### The transposed graph -/

section Transpose

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]

variable (k) in
/-- **The transpose of Remark 0FG4** on the correspondences of Section 0FFZ between schemes of
constant dimensions `d` and `e`: `Corrʳ(X, Y) ⟶ Corr^{d-e+r}(Y, X)`, `c ↦ cᵗ`. For `X` and `Y`
of constant dimensions `d` and `e` only the summand `(d, e)` of
`Corrʳ(X, Y) = ⊕_{d', e'} CH_{e'-r}(X_{d'} × Y_{e'}) ⊗ ℚ` is nonzero, and on it this is the
transpose `Stacks.WeilCohomology.transposeEquiv` of Stacks 0FG4, the pushforward along the factor
switch `X_d × Y_e ≅ Y_e × X_d`. -/
def corrTranspose (d e : ℕ) (r : ℤ) : Corr k sX sY r →ₗ[ℚ] Corr k sY sX ((d : ℤ) - e + r) :=
  (DirectSum.lof ℚ ℕ (fun e' ↦ DirectSum ℕ fun d' ↦ Correspondence (fieldChowSituation k)
      (partBase sY e') (partBase sX d') d' ((d : ℤ) - e + r)) e ∘ₗ
    DirectSum.lof ℚ ℕ (fun d' ↦ Correspondence (fieldChowSituation k) (partBase sY e)
      (partBase sX d') d' ((d : ℤ) - e + r)) d) ∘ₗ
    (transposeEquiv (fieldChowSituation k) (partBase sX d) (partBase sY e) d e r).toLinearMap ∘ₗ
      (DirectSum.component ℚ ℕ (fun e' ↦ Correspondence (fieldChowSituation k) (partBase sX d)
          (partBase sY e') e' r) e ∘ₗ
        DirectSum.component ℚ ℕ (fun d' ↦ DirectSum ℕ fun e' ↦ Correspondence
          (fieldChowSituation k) (partBase sX d') (partBase sY e') e' r) d)

omit [IsSeparated sY] in
/-- The `(d, e)` component of the graph correspondence is its `(d, e)` block. -/
theorem component_component_graphCorr [QuasiCompact sY] {f : Y ⟶ X} (hf : f ≫ sX = sY)
    (d e : ℕ) :
    DirectSum.component ℚ ℕ (fun e' ↦ Correspondence (fieldChowSituation k) (partBase sX d)
        (partBase sY e') e' 0) e
      (DirectSum.component ℚ ℕ (fun d' ↦ DirectSum ℕ fun e' ↦ Correspondence
        (fieldChowSituation k) (partBase sX d') (partBase sY e') e' 0) d
        (graphCorr k sX sY f hf)) = graphBlock k sX sY f hf d e := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  classical
  rw [graphCorr_eq_sum k sX sY f hf
    (D := insert d (finite_setOf_nonempty_preimage_dimPart k sX f).toFinset)
    (E := insert e (finite_setOf_nonempty_dimPart sY).toFinset)
    (fun d' h ↦ Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 h))
    (fun e' h ↦ Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 h))]
  simp [map_sum, DirectSum.component.of]

variable (k) in
/-- **The transposed graph** `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)` of a morphism `f : Y ⟶ X` between
schemes of constant dimensions `d` and `e` (Remark 0FG4): the transpose of the graph
`[Γ_f] ∈ Corr⁰(X, Y)`. -/
def transposeGraphCorr [QuasiCompact sY] (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ) :
    Corr k sY sX ((d : ℤ) - e) :=
  corrCongr k sY sX (add_zero _) (corrTranspose k sX sY d e 0 (graphCorr k sX sY f hf))

omit [IsSeparated sY] in
/-- The transposed graph is the class of the transposed graph piece `Γ_fᵗ ∩ (Y_e × X_d)`, in the
summand `(e, d)`. -/
theorem transposeGraphCorr_eq [QuasiCompact sY] {f : Y ⟶ X} (hf : f ≫ sX = sY) (d e : ℕ) :
    transposeGraphCorr k sX sY f hf d e =
      DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ d ((1 : ℚ) ⊗ₜ[ℤ]
        QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (partBase sY e) (partBase sX d))
          (graphPiece k sX sY f hf d e ≫ (pullbackSymmetry (partBase sX d) (partBase sY e)).hom)
          ((d : ℤ) - ((d : ℤ) - e))))) := by
  simp only [transposeGraphCorr, corrTranspose, LinearMap.coe_comp, Function.comp_apply,
    component_component_graphCorr, corrCongr_lof_lof, LinearEquiv.coe_coe, graphBlock,
    transposeEquiv_tmul, correspondenceCongr_tmul]
  congr 3
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_))
  rw [← QuotientAddGroup.mk'_apply, chowTranspose_mk, cycleTranspose, properPushforwardHom_apply,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isIso (fieldChowSituation k) _ _
      (pullbackSymmetry (partBase sX d) (partBase sY e))]
  exact mk_cycleAssociatedToClosedSubscheme_heq _ _ _ (by ring)

/-- **Stacks 0FG5 (3b), for schemes**: for `X` and `Y` of constant dimensions `d` and `e`,
pullback of cycles by the transposed graph `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)` is the Gysin map
`f^! : CH_m(X) ⊗ ℚ ⟶ CH_{m-(d-e)}(Y) ⊗ ℚ`. -/
theorem pullback_transposeGraphCorr [IsProper sX] [IsProper sY] {f : Y ⟶ X} (hf : f ≫ sX = sY)
    {d e : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (m : ℤ) :
    haveI := locallyOfFiniteType_of_comp_eq hf
    pullback k sY sX (canonicalDiagonalClassFamily k) ((d : ℤ) - e) m
        (transposeGraphCorr k sX sY f hf d e) =
      (smoothGysinChow (fieldChowSituation k) sY sX hf ((d : ℤ) - e) m).toIntLinearMap.baseChange
        ℚ := by
  have := locallyOfFiniteType_of_comp_eq hf
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  have : IsProper ((graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        pullback.fst (partBase sY e) (partBase sX d)) := inferInstance
  have hgys : (fieldGysinSystem k).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _
  set γ := graphPiece k sX sY f hf d e ≫ (pullbackSymmetry (partBase sX d) (partBase sY e)).hom
    with hγdef
  have hγfst : γ ≫ pullback.fst (partBase sY e) (partBase sX d) =
      (graphPieceOpen sX sY f d e).ι := by
    rw [hγdef, Category.assoc, pullbackSymmetry_hom_comp_fst, graphPiece_snd]
  have hγsnd : (γ ≫ pullback.snd (partBase sY e) (partBase sX d)) ≫ (dimPart sX d).ι =
      graphPieceι sX sY f d e ≫ f := by
    simp only [hγdef, Category.assoc, pullbackSymmetry_hom_comp_snd_assoc, graphPiece_fst_assoc,
      morphismRestrict_ι, graphPieceι]
  have hγ : γ ≫ prodBase (partBase sY e) (partBase sX d) =
      (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by
    rw [prodBase, ← Category.assoc, hγfst]
  have hγA : (γ ≫ pullback.fst (partBase sY e) (partBase sX d)) ≫ partBase sY e =
      (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by rw [hγfst]
  have hγB : (γ ≫ pullback.snd (partBase sY e) (partBase sX d)) ≫ partBase sX d =
      (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by
    simpa [graphPieceι, partBase, hf, Category.assoc] using congrArg (· ≫ sX) hγsnd
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul q β =>
    obtain ⟨p, rfl⟩ : ∃ p, m = (d : ℤ) - p := ⟨d - m, by ring⟩
    obtain ⟨c, rfl⟩ := capFundamentalClassSurjective k sX d hX p β
    rw [transposeGraphCorr_eq, pullback_lof_lof, restrictPart, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap,
      chowGroupRestrict_chowCohomologyCapFundamentalClass_of_isOpenImmersion (fieldChowSituation k)
        (fieldGysinSystem k) hgys sX p (partBase sX d) (dimPart sX d).ι rfl d
        (schemeDeltaDimension_le_of_relativeDimension sX hX),
      correspondencePullback_tmul_chowCohomologyCapFundamentalClass (partBase sY e) (partBase sX d)
        (relativeDimension_partBase sY e) (relativeDimension_partBase sX d) _ γ hγ hγB hγA,
      includePart, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    congr 1
    have hhg : ((γ ≫ pullback.snd (partBase sY e) (partBase sX d)) ≫ (dimPart sX d).ι) ≫ sX =
        (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by
      rw [Category.assoc]; exact hγB
    have hhg' : (graphPieceι sX sY f d e ≫ f) ≫ sX =
        (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by rw [← hγsnd, hhg]
    have hdim : schemeDeltaDimension (fieldChowSituation k) sY ≤
        (((d : ℤ) - ((d : ℤ) - e) : ℤ) : EInt) := by
      rw [show (d : ℤ) - ((d : ℤ) - e) = e by ring]
      exact schemeDeltaDimension_le_of_relativeDimension sY hY
    rw [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_toIntLinearMap,
      chowCohomologyRestrictionOfEq_restrictionOfEq sX (partBase sX d) _ (dimPart sX d).ι
        (γ ≫ pullback.snd (partBase sY e) (partBase sX d)) rfl hγB hhg,
      Stacks.Chow.chowCohomologyRestrictionOfEq_congr sX _ hγsnd hhg hhg',
      ← chowGroupRestrict_capFundamentalClass_restrictionOfEq sX sY _ f hf
        (graphPieceι sX sY f d e) (Category.assoc _ _ _) _ hdim,
      properChowPushforward_chowGroupDegreeEquiv (hfack := properPushforwardDescends _ _ _ _ _ _),
      ← properChowPushforward_comp_apply (fieldChowSituation k) _ (partBase sY e) sY _
        (dimPart sY e).ι (graphPieceι sX sY f d e) (by rw [hγfst]) (hw := Category.assoc _ _ _)
        (hfacw := properPushforwardDescends _ _ _ _ _ _),
      properChowPushforward_chowGroupRestrict_graphPieceι_of_relativeDimension sX sY hX hY]
    have hF := BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq
      (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) hgys sX sY p hf
      ((d : ℤ) - e) (smoothGysinClass (fieldChowSituation k) sY sX hf ((d : ℤ) - e)) c
      (smoothGysinClass_bivariantCommute (fieldChowSituation k) sY sX hf ((d : ℤ) - e) p c) d
      (smoothGysinChow_fundamentalChowClass sY sX hf e d hY hX) (d := (d : ℤ) - ((d : ℤ) - e)) rfl
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans hF.symm)

/-- **Stacks 0FG5 (3)(a), for schemes, on a part**: for `X` and `Y` of constant dimensions `d`
and `e`, pushforward by the transposed graph `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)` of `1 ⊗ a`,
`a ∈ CH_{e-i}(Y_e)`, is `1 ⊗ (f_*a)|_{X_d}`. -/
theorem pushforward_transposeGraphCorr_lof [IsProper sX] [IsProper sY] {f : Y ⟶ X}
    (hf : f ≫ sX = sY) {d e : ℕ}
    (i : ℤ) (a : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - i)) :
    haveI := isProper_of_comp_eq sX sY hf
    haveI := (isClopenDecomposition_dimPart sY).isProper_ι e
    pushforward k sY sX (canonicalDiagonalClassFamily k) ((d : ℤ) - e) i
        (transposeGraphCorr k sX sY f hf d e)
        (DirectSum.lof ℚ ℕ (fun e : ℕ ↦
          TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - i))) e
          ((1 : ℚ) ⊗ₜ[ℤ] a)) =
      DirectSum.lof ℚ ℕ (fun d' : ℕ ↦ TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k)
          (partBase sX d') ((d' : ℤ) - (i + ((d : ℤ) - e))))) d
        ((1 : ℚ) ⊗ₜ[ℤ] chowGroupDegreeEquiv (fieldChowSituation k) (partBase sX d) (by ring)
          (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl
            ((e : ℤ) - i)
            (properChowPushforward (fieldChowSituation k) (partBase sY e) sX
              ((dimPart sY e).ι ≫ f) (by rw [Category.assoc, hf]) ((e : ℤ) - i)
              (properPushforwardDescends _ _ _ _ _ _) a))) := by
  have := isProper_of_comp_eq sX sY hf
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  have := (isClopenDecomposition_dimPart sY).isProper_ι e
  have hgys : (fieldGysinSystem k).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _
  have : IsProper (((dimPart sY e).ι ≫ f) ∣_ dimPart sX d) := by
    rw [← graphPiece_fst k sX sY f hf d e]; infer_instance
  have : IsProper ((graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        pullback.snd (partBase sY e) (partBase sX d)) := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]; infer_instance
  have hγfst : (graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        pullback.fst (partBase sY e) (partBase sX d) = (graphPieceOpen sX sY f d e).ι := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, graphPiece_snd]
  have hγsnd : (graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        pullback.snd (partBase sY e) (partBase sX d) = ((dimPart sY e).ι ≫ f) ∣_ dimPart sX d := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd, graphPiece_fst]
  have hγ : (graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        prodBase (partBase sY e) (partBase sX d) =
      (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by
    rw [prodBase, ← Category.assoc, hγfst]
  have hγA : ((graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        pullback.fst (partBase sY e) (partBase sX d)) ≫ partBase sY e =
      (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by rw [hγfst]
  have hres : (((dimPart sY e).ι ≫ f) ∣_ dimPart sX d) ≫ partBase sX d =
      (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by
    rw [morphismRestrict_ι_assoc, Category.assoc, hf]
  have hγB : ((graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        pullback.snd (partBase sY e) (partBase sX d)) ≫ partBase sX d =
      (graphPieceOpen sX sY f d e).ι ≫ partBase sY e := by rw [hγsnd, hres]
  obtain ⟨c, rfl⟩ := capFundamentalClassSurjective k (partBase sY e) e
    (relativeDimension_partBase sY e) i a
  rw [transposeGraphCorr_eq, pushforward_lof_lof_lof,
    correspondencePushforward_tmul_chowCohomologyCapFundamentalClass (partBase sY e)
      (partBase sX d) (relativeDimension_partBase sY e) (relativeDimension_partBase sX d) _ _ hγ
      hγA hγB]
  refine congrArg (DirectSum.lof ℚ ℕ _ d) (congrArg (TensorProduct.tmul ℤ (1 : ℚ)) ?_)
  rw [chowGroupRestrict_properChowPushforward (fieldChowSituation k) (partBase sY e) sX
      ((graphPieceOpen sX sY f d e).ι ≫ partBase sY e) (partBase sX d) ((dimPart sY e).ι ≫ f)
      (by rw [Category.assoc, hf]) (graphPieceOpen sX sY f d e).ι rfl (dimPart sX d).ι rfl
      (((dimPart sY e).ι ≫ f) ∣_ dimPart sX d) hres
      (isPullback_morphismRestrict ((dimPart sY e).ι ≫ f) (dimPart sX d)).flip _ _
      (properPushforwardDescends _ _ _ _ _ _),
    chowGroupRestrict_chowCohomologyCapFundamentalClass_of_isOpenImmersion
      (fieldChowSituation k) (fieldGysinSystem k) hgys (partBase sY e) i _
      (graphPieceOpen sX sY f d e).ι rfl e
      (schemeDeltaDimension_le_of_relativeDimension _ (relativeDimension_partBase sY e)),
    properChowPushforward_congr (fieldChowSituation k) _ _ _ _ hγsnd hγB hres _ _
      (properPushforwardDescends _ _ _ _ _ _)]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
    (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  refine properChowPushforward_heq_congr _ _ _ _ _ (by ring) _ _ _ _ ?_
  rw [Stacks.Chow.chowCohomologyRestrictionOfEq_congr _ _ hγfst hγA rfl]
  exact chowCohomologyCapFundamentalClass_heq_of_eq _ (by ring) _ _

end Transpose

/-! ### Stacks 0FG5 -/

section SmoothProjective

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X)

/-- **Stacks Project, Tag 0FG5 (2).** Let `f : Y ⟶ X` be a morphism of smooth projective
schemes over `k` and `[Γ_f] ∈ Corr⁰(X, Y)` its graph (Example 0FG1). Pullback of cycles by the
correspondence `[Γ_f]`, `β ↦ pr₁,*([Γ_f] · pr₂^*β)`, agrees with proper pushforward
`f_* : CH_m(Y) ⊗ ℚ ⟶ CH_m(X) ⊗ ℚ`, in every dimension `m`. -/
@[stacks 0FG5 "(2): pullback of cycles by the correspondence [Γ_f] agrees with the pushforward \
f_* : CH_*(Y) → CH_*(X), in every dimension, with rational coefficients"]
theorem pullback_graphCorrespondenceSP (m : ℤ) :
    haveI := isProper_of_comp_eq X.obj.hom Y.obj.hom (Over.w f.hom)
    pullback k X.obj.hom Y.obj.hom (canonicalDiagonalClassFamily k) 0 m
        (SmoothProjectiveCorr.toCorr X Y 0 (graphCorrespondenceSP f)) =
      ((chowGroupDegreeEquiv (fieldChowSituation k) X.obj.hom (sub_zero m).symm).toAddMonoidHom.comp
        (properChowPushforward (fieldChowSituation k) Y.obj.hom X.obj.hom f.hom.left
          (Over.w f.hom) m
          (properPushforwardDescends _ _ _ _ _ _))).toIntLinearMap.baseChange ℚ :=
  pullback_graphCorr X.obj.hom Y.obj.hom (Over.w f.hom) m

/-- The transposed graph `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)` of a morphism `f : Y ⟶ X` of smooth
projective schemes over `k` of constant dimensions `d` and `e` (Remark 0FG4). -/
def transposeGraphCorrespondenceSP (d e : ℕ) : SmoothProjectiveCorr Y X ((d : ℤ) - e) :=
  (SmoothProjectiveCorr.toCorr Y X _).symm
    (transposeGraphCorr k X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom) d e)

/-- **Stacks Project, Tag 0FG5 (3)(b).** Let `f : Y ⟶ X` be a morphism of smooth projective
schemes over `k`, with `X` and `Y` equidimensional of dimensions `d` and `e`. Pullback of cycles
by the transposed graph `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)` of Remark 0FG4,
`β ↦ pr₁,*([Γ_f]ᵗ · pr₂^*β)`, agrees with the Gysin map
`f^! : CH_m(X) ⊗ ℚ ⟶ CH_{m-(d-e)}(Y) ⊗ ℚ` of Stacks 0FF3, in every dimension `m`. -/
@[stacks 0FG5 "(3)(b): for X and Y equidimensional of dimensions d and e, pullback of cycles by \
the transposed graph [Γ_f]ᵗ ∈ Corr^{d-e}(Y, X) of Remark 0FG4 agrees with the Gysin map f^!, in \
every dimension, with rational coefficients"]
theorem pullback_transposeGraphCorrespondenceSP {d e : ℕ} (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (m : ℤ) :
    haveI := locallyOfFiniteType_of_comp_eq (Over.w f.hom)
    pullback k Y.obj.hom X.obj.hom (canonicalDiagonalClassFamily k) ((d : ℤ) - e) m
        (SmoothProjectiveCorr.toCorr Y X _ (transposeGraphCorrespondenceSP f d e)) =
      (smoothGysinChow (fieldChowSituation k) Y.obj.hom X.obj.hom (Over.w f.hom) ((d : ℤ) - e)
        m).toIntLinearMap.baseChange ℚ :=
  pullback_transposeGraphCorr X.obj.hom Y.obj.hom (Over.w f.hom) hX hY m

/-- The part on `X_d` of the equidimensional pushforward `f_* : CH^i(Y) ⟶ CH^{i+d-e}(X)`. -/
theorem equidimensionalPushforward_apply_self {d e : ℕ} (i q : ℤ) (h : q = i + d - e)
    (α : codimensionChowGroup k Y.obj.hom i) :
    haveI : IsProper f.hom.left := isProper_of_comp_eq X.obj.hom Y.obj.hom (Over.w f.hom)
    haveI := (isClopenDecomposition_dimPart Y.obj.hom).isProper_ι e
    equidimensionalPushforward f e d i q h α d =
      chowGroupDegreeEquiv (fieldChowSituation k) (partBase X.obj.hom d) (by omega)
        (chowGroupRestrict (fieldChowSituation k) X.obj.hom (partBase X.obj.hom d)
          (dimPart X.obj.hom d).ι rfl ((e : ℤ) - i)
          (properChowPushforward (fieldChowSituation k) (partBase Y.obj.hom e) X.obj.hom
            ((dimPart Y.obj.hom e).ι ≫ f.hom.left) (by rw [Category.assoc, Over.w f.hom])
            ((e : ℤ) - i) (properPushforwardDescends _ _ _ _ _ _) (α e))) := by
  simp only [equidimensionalPushforward, AddMonoidHom.pi_apply]
  rw [dite_eq_left trivial]
  rfl

/-- **Stacks 0FG5 (3)(a), on integral classes**: for `X` and `Y` equidimensional of dimensions
`d` and `e`, pushforward of cycles by the transposed graph `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)` carries the
class of `α ∈ CH^i(Y) = CH_{e-i}(Y)` to the class of `f_*α ∈ CH^{i+d-e}(X) = CH_{e-i}(X)`. -/
theorem pushforward_transposeGraphCorrespondenceSP_codimensionToCodimChow {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) (i : ℤ)
    (α : codimensionChowGroup k Y.obj.hom i) :
    haveI : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    haveI : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
    pushforward k Y.obj.hom X.obj.hom (canonicalDiagonalClassFamily k) ((d : ℤ) - e) i
        (SmoothProjectiveCorr.toCorr Y X _ (transposeGraphCorrespondenceSP f d e))
        (codimensionToCodimChow k Y.obj.hom i α) =
      codimensionToCodimChow k X.obj.hom (i + ((d : ℤ) - e))
        (equidimensionalPushforward f e d i (i + ((d : ℤ) - e)) (by ring) α) := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  rw [codimensionToCodimChow_of_relativeDimension Y.obj.hom hY,
    codimensionToCodimChow_of_relativeDimension X.obj.hom hX, transposeGraphCorrespondenceSP,
    LinearEquiv.apply_symm_apply, pushforward_transposeGraphCorr_lof X.obj.hom Y.obj.hom
      (Over.w f.hom) (d := d) (e := e), equidimensionalPushforward_apply_self]

/-- **Stacks Project, Tag 0FG5 (3)(a).** Let `f : Y ⟶ X` be a morphism of smooth projective
schemes over `k`, with `X` and `Y` equidimensional of dimensions `d` and `e`. Pushforward of
cycles by the transposed graph `[Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)` of Remark 0FG4,
`α ↦ pr₂,*([Γ_f]ᵗ · pr₁^*α)`, corresponds to pushforward of cycles by `f`,
`f_* : CH^i(Y) = CH_{e-i}(Y) ⟶ CH_{e-i}(X) = CH^{i+d-e}(X)`, on `CH^i(Y) ⊗ ℚ`. -/
@[stacks 0FG5 "(3)(a): for X and Y equidimensional of dimensions d and e, pushforward of cycles \
by the transposed graph [Γ_f]ᵗ ∈ Corr^{d-e}(Y, X) of Remark 0FG4 corresponds to pushforward of \
cycles by f, on CH^i(Y) ⊗ Q for every i"]
theorem pushforward_transposeGraphCorrespondenceSP {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) (i : ℤ) :
    haveI : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    haveI : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
    pushforward k Y.obj.hom X.obj.hom (canonicalDiagonalClassFamily k) ((d : ℤ) - e) i
        (SmoothProjectiveCorr.toCorr Y X _ (transposeGraphCorrespondenceSP f d e)) ∘ₗ
        rationalCodimensionToCodimChow k Y.obj.hom i =
      rationalCodimensionToCodimChow k X.obj.hom (i + ((d : ℤ) - e)) ∘ₗ
        (equidimensionalPushforward f e d i (i + ((d : ℤ) - e)) (by ring)).toIntLinearMap.baseChange
          ℚ := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  refine TensorProduct.AlgebraTensorModule.ext fun q α ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, rationalCodimensionToCodimChow_tmul,
    LinearMap.baseChange_tmul, map_smul, AddMonoidHom.coe_toIntLinearMap,
    pushforward_transposeGraphCorrespondenceSP_codimensionToCodimChow f hX hY]

/-- **Stacks Project, Tag 0FG5 (1).** Let `f : Y ⟶ X` be a morphism of smooth projective
schemes over `k` and `[Γ_f] ∈ Corr⁰(X, Y)` its graph (Example 0FG1). Pushforward of cycles by
the correspondence `[Γ_f]`, `α ↦ pr₂,*([Γ_f] · pr₁^*α)`, agrees with the Gysin map
`f^! : CH^i(X) ⟶ CH^i(Y)` of Stacks 0FF3, on `CH^i(X) ⊗ ℚ` for every `i`. The schemes need not be
equidimensional: `CH^i(X) = ∏_d CH_{d-i}(X_d)` is graded by codimension on the parts `X_d` of
constant dimension. -/
@[stacks 0FG5 "(1): pushforward of cycles by the correspondence [Γ_f] agrees with the Gysin map \
f^! : CH^*(X) → CH^*(Y), on CH^i(X) ⊗ Q for every i, X and Y not necessarily equidimensional"]
theorem pushforward_graphCorrespondenceSP (i : ℤ) :
    haveI : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    haveI : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
    haveI := locallyOfFiniteType_of_comp_eq (Over.w f.hom)
    pushforward k X.obj.hom Y.obj.hom (canonicalDiagonalClassFamily k) 0 i
        (SmoothProjectiveCorr.toCorr X Y 0 (graphCorrespondenceSP f)) ∘ₗ
        rationalCodimensionToCodimChow k X.obj.hom i =
      (codimChowCongr k Y.obj.hom (add_zero i).symm).toLinearMap ∘ₗ
        rationalCodimensionToCodimChow k Y.obj.hom i ∘ₗ
          (codimensionGysin Y.obj.hom X.obj.hom (Over.w f.hom) i).toIntLinearMap.baseChange ℚ :=
  pushforward_graphCorr_comp_rationalCodimensionToCodimChow X.obj.hom Y.obj.hom (Over.w f.hom) i

end SmoothProjective

end Stacks.WeilCohomology

end
