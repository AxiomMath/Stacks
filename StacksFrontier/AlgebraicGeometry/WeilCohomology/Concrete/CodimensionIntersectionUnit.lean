module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat

/-!
# The fundamental class is the unit of the intersection product

Let `X` be a scheme smooth over a field `k`. The fundamental class `[X] ∈ CH^0(X)` is a two-sided
unit for the intersection product of Stacks 0FC0,

  `[X] · β = β = β · [X]`   for `β ∈ CH^j(X)`.

On a scheme `W` smooth over `k` of constant dimension `N` this is a consequence of Stacks 0FC2.
By its first clause every `β ∈ CH_m(W)` is `c ∩ [W]_N` for some `c ∈ A^{N-m}(W)`, and by its second
clause `c ∩ γ = (c ∩ [W]_N) · γ` for every `γ`; at `γ = [W]_N` this reads
`β = c ∩ [W]_N = β · [W]_N`. Commutativity of the product gives `[W]_N · β = β`. On a scheme of
mixed dimension the product of `CH^*(X) = ∏_d CH_{d-*}(X_d)` is formed part by part, and the
fundamental class is `[X] = ([X_d]_d)_d`, so the identity holds on each part.

## Main results

* `Stacks.WeilCohomology.selfIntersectionProduct_fundamentalChowClass_right`,
  `Stacks.WeilCohomology.selfIntersectionProduct_fundamentalChowClass_left`: `β · [W] = β` and
  `[W] · β = β` for `W` smooth over `k` of constant dimension.
* `Stacks.WeilCohomology.codimensionIntersectionProduct_fundamentalClass_left`,
  `Stacks.WeilCohomology.codimensionIntersectionProduct_fundamentalClass_right`: `[X] · β = β` and
  `β · [X] = β` in `CH^*(X)` for a smooth projective `X` over `k`, componentwise on the parts
  `X_d`.

## References

* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

section ConstantDimension

variable {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
  [Smooth sW] {N : ℕ} (hN : RelativeDimension sW N)

/-- **The fundamental class is a right unit** for the intersection product on a scheme `W` smooth
over `k` of constant dimension `N`: `β · [W]_N = β` in `CH_m(W)`. By the first clause of
Stacks 0FC2, `β = c ∩ [W]_N` for some `c ∈ A^{N-m}(W)`; by its second clause
(`Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct`) at the class `[W]_N`,
`c ∩ [W]_N = (c ∩ [W]_N) · [W]_N`. -/
theorem selfIntersectionProduct_fundamentalChowClass_right (m : ℤ)
    (β : chowGroup (fieldChowSituation k) sW m) :
    selfIntersectionProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW N (canonicalDiagonalClassFamily k sW N hN) m N β
        (fundamentalChowClass (fieldChowSituation k) sW N) =
      chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring) β := by
  obtain ⟨c, hc⟩ := (chowCohomologyCapFundamentalClass_bijective_of_smooth_field k sW N hN
    (N - m)).2 (chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring : m = N - (N - m)) β)
  have h := canonicalDiagonalClassFamily_capEqProduct k sW N hN (N - m) c N
    (fundamentalChowClass (fieldChowSituation k) sW N)
  rw [chowCohomologyCap_fundamentalChowClass, hc] at h
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ β).symm)
  refine (selfIntersectionProduct_heq_of_heq sW (N : ℤ) _ (by ring : m = N - (N - m)) rfl
    (chowGroupDegreeEquiv_heq (fieldChowSituation k) sW (by ring : m = N - (N - m)) β).symm
    HEq.rfl).trans ?_
  exact (chowGroupDegreeEquiv_heq (fieldChowSituation k) sW _ _).symm.trans
    ((heq_of_eq h.symm).trans (chowGroupDegreeEquiv_heq (fieldChowSituation k) sW _ β))

/-- **The fundamental class is a left unit** for the intersection product on a scheme `W` smooth
over `k` of constant dimension `N`: `[W]_N · β = β` in `CH_m(W)`. -/
theorem selfIntersectionProduct_fundamentalChowClass_left (m : ℤ)
    (β : chowGroup (fieldChowSituation k) sW m) :
    selfIntersectionProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW N (canonicalDiagonalClassFamily k sW N hN) N m
        (fundamentalChowClass (fieldChowSituation k) sW N) β =
      chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring) β := by
  rw [canonicalDiagonalClassFamily_isSymmetric k sW N hN,
    selfIntersectionProduct_fundamentalChowClass_right sW hN m β]
  exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ β).symm))

end ConstantDimension

/-- **`[X] · β = β`** in `CH^*(X)` for a smooth projective scheme `X` over `k`: on each part
`X_d` of dimension `d` the product is `[X_d]_d · β_d = β_d`. -/
theorem codimensionIntersectionProduct_fundamentalClass_left
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (j : ℤ) (β : codimensionChowGroup k X.obj.hom j) (d : ℕ) :
    codimensionIntersectionProduct k X.obj.hom 0 j (fundamentalClass X) β d =
      chowGroupDegreeEquiv (fieldChowSituation k) (partBase X.obj.hom d) (by ring) (β d) := by
  rw [codimensionIntersectionProduct_apply]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
    (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  refine HEq.trans (selfIntersectionProduct_heq_of_heq (partBase X.obj.hom d) (d : ℤ) _
    (sub_zero (d : ℤ)) rfl (chowGroupDegreeEquiv_heq _ _ _ _) HEq.rfl) ?_
  rw [selfIntersectionProduct_fundamentalChowClass_left]
  exact chowGroupDegreeEquiv_heq _ _ _ _

/-- **`β · [X] = β`** in `CH^*(X)` for a smooth projective scheme `X` over `k`: on each part
`X_d` of dimension `d` the product is `β_d · [X_d]_d = β_d`. -/
theorem codimensionIntersectionProduct_fundamentalClass_right
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (i : ℤ) (β : codimensionChowGroup k X.obj.hom i) (d : ℕ) :
    codimensionIntersectionProduct k X.obj.hom i 0 β (fundamentalClass X) d =
      chowGroupDegreeEquiv (fieldChowSituation k) (partBase X.obj.hom d) (by ring) (β d) := by
  rw [codimensionIntersectionProduct_apply]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
    (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  refine HEq.trans (selfIntersectionProduct_heq_of_heq (partBase X.obj.hom d) (d : ℤ) _
    rfl (sub_zero (d : ℤ)) HEq.rfl (chowGroupDegreeEquiv_heq _ _ _ _)) ?_
  rw [selfIntersectionProduct_fundamentalChowClass_right]
  exact chowGroupDegreeEquiv_heq _ _ _ _

end Stacks.WeilCohomology

end
