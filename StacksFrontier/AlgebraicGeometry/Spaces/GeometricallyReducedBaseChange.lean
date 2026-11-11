module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension
import all StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension

/-!
# Geometric reducedness through reducedness of the base changes `X_{k'}`

Let `k` be a field and let `X` be an algebraic space over `k`. This file states Stacks 0E03 in
the source's terms: `X` is geometrically reduced exactly when the base changes `X_{k'}` are
reduced, for all extensions `k'/k`, for the finite purely inseparable ones, or for each of
`k^{1/p}`, `k^{perf}` and `k̄`.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_relocalizeRestrict_iff`: `X_{k'}` is
  reduced exactly when `U ×_{Spec k} Spec k'` is reduced for every étale scheme chart `U → X`.
* `AlgebraicGeometry.Space.contains_spec_of_isPerfectClosure`: the spectrum of a perfect closure
  of `k` lies in every big fppf site containing `Spec k`.
* `AlgebraicGeometry.Space.isGeometricallyReduced_tfae_isReduced_baseChange`: Stacks 0E03.

## Implementation notes

The base change `X_{k'}` is `CategoryTheory.OverShriek.relocalizeRestrict` along
`AlgebraicGeometry.Space.fieldExtensionMap`, an algebraic space over `k'` by Stacks 03I5, and a
reduced algebraic space is one with the étale-local property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of reducedness (Stacks 03E6). The base change of
a surjective étale atlas of `X` is a surjective étale atlas of `X_{k'}` and the base change of an
étale chart of `X` is an étale chart of `X_{k'}`, so reducedness of `X_{k'}` is the chart
condition of `AlgebraicGeometry.Space.isGeometricallyReduced_tfae`, from which the equivalences
follow.

A base change `X_{k'}` is formed in the chosen big fppf site, so it needs `Spec k'` to lie in
that site. Every algebraic extension of `k` does
(`AlgebraicGeometry.Space.contains_spec_of_isAlgebraic`, from the cardinality bound
`#k' ≤ max #k ℵ₀`), so only the condition over all extensions carries a containment hypothesis.

## References

* [Stacks Project, Tag 0E03](https://stacks.math.columbia.edu/tag/0E03)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section BaseChange

/-- The spectrum of a perfect closure of a field `k` lies in a big fppf site containing
`Spec k`, the perfect closure being purely inseparable, hence algebraic, over `k`. -/
theorem contains_spec_of_isPerfectClosure (B : BigFppfSite.{u}) (k K : Type u) [Field k]
    [Field K] [Algebra k K] (p : ℕ) [ExpChar k p] [ExpChar K p] [PerfectRing K p]
    [IsPerfectClosure (algebraMap k K) p] (hk : B.Contains (Spec (.of k))) :
    B.Contains (Spec (.of K)) :=
  have : IsPurelyInseparable k K := IsPRadical.isPurelyInseparable k K p
  contains_spec_of_isAlgebraic B k K hk

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (.of k))) (hk' : B.Contains (Spec (.of k')))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- The scheme of the base change along `k ⊆ k'` of a chart `U` of `X` is reduced exactly when
the fibre product of schemes `U ×_{Spec k} Spec k'` is. -/
private theorem isReduced_baseChangeChart_iff (U : BigFppfOver B (Spec (.of k)) hk) :
    IsReduced ((BigFppfOver.toScheme B (Spec (.of k')) hk').obj
        ((Over.pullback (fieldExtensionMap B k k' hk hk')).obj U)) ↔
      IsReduced (pullback (B.inclusion.map U.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  let e := (isPullback_baseChangeChart k k' B hk hk' U).isoPullback
  exact ⟨fun h ↦ @isReduced_of_isOpenImmersion _ _ e.inv inferInstance h,
    fun h ↦ @isReduced_of_isOpenImmersion _ _ e.hom inferInstance h⟩

/-- The base change `X_{k'}` of an algebraic space `X` over `k` along a field extension `k'/k`
is reduced exactly when every étale scheme chart `U → X` has `U ×_{Spec k} Spec k'` reduced:
the base changes of the étale charts of `X` are étale charts of `X_{k'}`, and the base change
of a surjective étale atlas of `X` is a surjective étale atlas of `X_{k'}`. -/
theorem hasEtaleLocalProperty_isReduced_relocalizeRestrict_iff
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    HasEtaleLocalProperty B (Spec (.of k')) hk'
        ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).obj X)
        (fun Y : Scheme.{u} => IsReduced Y) ↔
      ∀ (U : BigFppfOver B (Spec (.of k)) hk) (a : yoneda.obj U ⟶ X),
        IsEtale B (Spec (.of k)) hk a →
          IsReduced (pullback (B.inclusion.map U.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  have hX' := isAlgebraicSpace_relocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hk
    (fieldExtensionMap B k k' hk hk') X hX
  constructor
  · intro h U a ha
    have hall := (exists_atlas_iff_forall_etale B (Spec (.of k')) hk' _
      (fun Y : Scheme.{u} => IsReduced Y) hX').mp h
    have hetale := presheaf_relocalizeRestrict_chart k k' B hk hk' X
      (@AlgebraicGeometry.Etale.{u}) AlgebraicGeometry.etale_respectsIso U a
      (presheaf_etale_of_isEtale B (Spec (.of k)) hk ha)
    exact (isReduced_baseChangeChart_iff k k' B hk hk' U).mp (hall _ _ hetale)
  · intro h
    obtain ⟨U, a, hasurj, haetale⟩ := hX.exists_atlas
    refine ⟨(Over.pullback (fieldExtensionMap B k k' hk hk')).obj U,
      (OverShriek.restrictYonedaIso (fieldExtensionMap B k k' hk hk') U).hom ≫
        (OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).map a,
      presheaf_relocalizeRestrict_chart k k' B hk hk' X
        (@AlgebraicGeometry.Surjective.{u}) inferInstance U a hasurj,
      presheaf_relocalizeRestrict_chart k k' B hk hk' X
        (@AlgebraicGeometry.Etale.{u}) AlgebraicGeometry.etale_respectsIso U a haetale, ?_⟩
    exact (isReduced_baseChangeChart_iff k k' B hk hk' U).mpr
      (h U a (isEtale_of_presheaf_etale B (Spec (.of k)) hk haetale))

end BaseChange

/-- **Stacks 0E03.** Let `k` be a field of exponential characteristic `p` and let `X` be an
algebraic space over `k`. The following are equivalent:
1. `X` is geometrically reduced over `k`;
2. `X_{k'}` is reduced for every field extension `k'/k`;
3. `X_{k'}` is reduced for every finite purely inseparable field extension `k'/k`;
4. `X_{k^{1/p}}` is reduced;
5. `X_{k^{perf}}` is reduced;
6. `X_{k̄}` is reduced.

Here `X_{k'}` is the base change of `X` along `Spec k' → Spec k`, the restriction
`CategoryTheory.OverShriek.relocalizeRestrict` along `AlgebraicGeometry.Space.fieldExtensionMap`,
an algebraic space over `k'` by Stacks 03I5, and "reduced" is the étale-local property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of reducedness. As everywhere in the library, a
base change `X_{k'}` is formed in the chosen big fppf site, so in (2) the extension `k'` ranges
over the fields whose spectrum lies in that site; every algebraic extension of `k` does
(`AlgebraicGeometry.Space.contains_spec_of_isAlgebraic`), so (3)–(6) carry no such condition.
The exponential characteristic is used in place of the source's `p > 0`; in characteristic zero
the statement remains true, with `k^{1/p} = k`. -/
@[stacks 0E03]
theorem isGeometricallyReduced_tfae_isReduced_baseChange (k : Type u) [Field k] (p : ℕ)
    [ExpChar k p] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (kperf : Type u) [Field kperf] [Algebra k kperf] [ExpChar kperf p] [PerfectRing kperf p]
    [IsPerfectClosure (algebraMap k kperf) p]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] :
    List.TFAE
      [ IsGeometricallyReduced k B hk X hX,
        ∀ (k' : Type u) [Field k'] [Algebra k k'] (hk' : B.Contains (Spec (.of k'))),
          HasEtaleLocalProperty B (Spec (.of k')) hk'
            ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk hk')).obj X)
            (fun Y : Scheme.{u} => IsReduced Y),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          HasEtaleLocalProperty B (Spec (.of k')) (contains_spec_of_isAlgebraic B k k' hk)
            ((OverShriek.relocalizeRestrict (fieldExtensionMap B k k' hk
              (contains_spec_of_isAlgebraic B k k' hk))).obj X)
            (fun Y : Scheme.{u} => IsReduced Y),
        HasEtaleLocalProperty B (Spec (.of (AdjoinPthRoots k)))
          (contains_spec_of_isAlgebraic B k (AdjoinPthRoots k) hk)
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k (AdjoinPthRoots k) hk
            (contains_spec_of_isAlgebraic B k (AdjoinPthRoots k) hk))).obj X)
          (fun Y : Scheme.{u} => IsReduced Y),
        HasEtaleLocalProperty B (Spec (.of kperf))
          (contains_spec_of_isPerfectClosure B k kperf p hk)
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k kperf hk
            (contains_spec_of_isPerfectClosure B k kperf p hk))).obj X)
          (fun Y : Scheme.{u} => IsReduced Y),
        HasEtaleLocalProperty B (Spec (.of kbar)) (contains_spec_of_isAlgebraic B k kbar hk)
          ((OverShriek.relocalizeRestrict (fieldExtensionMap B k kbar hk
            (contains_spec_of_isAlgebraic B k kbar hk))).obj X)
          (fun Y : Scheme.{u} => IsReduced Y) ] := by
  have hT := isGeometricallyReduced_tfae k p B hk X hX kperf kbar
  dsimp only at hT
  have hb := fun (k' : Type u) [Field k'] [Algebra k k'] (hk' : B.Contains (Spec (.of k'))) ↦
    hasEtaleLocalProperty_isReduced_relocalizeRestrict_iff k k' B hk hk' X hX
  tfae_have 1 ↔ 6 := by
    rw [hb]
    exact hT.out 1 6
  tfae_have 1 ↔ 5 := by
    rw [hb]
    exact hT.out 1 5
  tfae_have 1 ↔ 4 := by
    rw [hb]
    exact hT.out 1 4
  tfae_have 1 ↔ 3 := by
    have h13 := hT.out 1 3
    rw [h13]
    constructor
    · intro h k' _ _ _ _
      exact (hb k' _).mpr (h k')
    · intro h k' _ _ _ _
      exact (hb k' _).mp (h k')
  tfae_have 2 → 6 := fun h ↦ h kbar _
  tfae_have 1 → 2 := by
    have h12 := hT.out 1 2
    intro h k' _ _ hk'
    exact (hb k' hk').mpr (h12.mp h k')
  tfae_finish

end AlgebraicGeometry.Space

end
