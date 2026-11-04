module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletionDiscreteValuation
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingDecomposition
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFamilyOperations
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingProperCurve
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.FiniteType
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingReduced

/-!
# Smoothing a separated curve with lci singularities

Let `k` be a field and let `X` be a scheme over `k` which is separated and of finite type over `k`
with `dim(X) ≤ 1`, a local complete intersection over `k`, and smooth over `k` away from finitely
many points. Then there is a flat, separated, finite type morphism `Y ⟶ Spec k⟦t⟧` whose generic
fibre is smooth and whose special fibre is isomorphic to `X`. This is [Stacks, Tag 0E7Z].

## The proof

This is the source's.

* `X = X' ⊔ X''` with `dim(X') ≤ 0` and `X''` equidimensional of dimension one
  (`Deformation.Examples.Smoothing.exists_isCompl_zeroDimensional_equidimensional`). The two pieces
  are open and closed, so each is again separated, of finite type, a local complete intersection,
  and smooth away from finitely many points.
* `X'` is dealt with as in the proof of [Stacks, Tag 0E7Y], by [Stacks, Tag 0E7W]
  (`Smoothing.exists_flat_finite_projective_smoothing_of_topologicalKrullDim_le_zero`).
* `X''` is reduced, being Cohen–Macaulay and smooth at its generic points
  (`Deformation.Examples.Smoothing.isReduced_of_syntomic_of_equidimensional`), so it has a
  compactification `X'' ⊆ X̄` with `X̄` H-projective over `k`, `X̄ ∖ X''` a finite set of closed
  points and discrete valuation rings as local rings there ([Stacks, Tag 0BXW],
  `Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`).
  A discrete valuation ring essentially of finite type over `k` is a complete intersection over
  `k`, so `X̄` is a local complete intersection over `k`
  (`Deformation.Examples.Smoothing.isLocalCompleteIntersectionOverField_of_isOpenImmersion`), and
  it is smooth away from finitely many points
  (`Deformation.Examples.Smoothing.finite_compl_smoothLocus_of_isOpenImmersion`).
  [Stacks, Tag 0E7Y] gives a flat projective `Ȳ ⟶ Spec k⟦t⟧` with smooth generic fibre and
  special fibre `X̄`, and removing the points of `X̄ ∖ X''` from `Ȳ` leaves the family for `X''`
  (`Deformation.Examples.Smoothing.exists_smoothing_of_opens`).
* The two families are glued as a disjoint union
  (`Deformation.Examples.Smoothing.exists_smoothing_of_isCompl`).

## Main results

* `Deformation.Examples.Smoothing.exists_flat_separated_finiteType_smoothing`: [Stacks, Tag 0E7Z].

## References

* [Stacks Project, Tag 0E7Z](https://stacks.math.columbia.edu/tag/0E7Z)
* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 0E7W](https://stacks.math.columbia.edu/tag/0E7W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples.Smoothing

variable (k : Type u) [Field k]

/-- The class of morphisms the families of [Stacks, Tag 0E7Z] are asked to lie in: separated and
of finite type. It is stable under disjoint unions. -/
theorem separated_finiteType_coprodDesc {Y₁ Y₂ S : Scheme.{u}} (g₁ : Y₁ ⟶ S) (g₂ : Y₂ ⟶ S)
    (h₁ : IsSeparated g₁ ∧ LocallyOfFiniteType g₁ ∧ QuasiCompact g₁)
    (h₂ : IsSeparated g₂ ∧ LocallyOfFiniteType g₂ ∧ QuasiCompact g₂) :
    IsSeparated (coprod.desc g₁ g₂) ∧ LocallyOfFiniteType (coprod.desc g₁ g₂) ∧
      QuasiCompact (coprod.desc g₁ g₂) := by
  obtain ⟨hs₁, hl₁, hq₁⟩ := h₁
  obtain ⟨hs₂, hl₂, hq₂⟩ := h₂
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  exact ⟨isSeparated_coprodDesc g₁ g₂, coprodDesc_of_isZariskiLocalAtSource g₁ g₂ _ hl₁ hl₂,
    quasiCompact_coprodDesc g₁ g₂⟩

/-- **[Stacks, Tag 0E7Z] for an equidimensional curve of dimension one.** -/
theorem exists_smoothing_of_equidimensional {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hlci : IsLocalCompleteIntersectionOverField f) (hfin : ((f.smoothLocus : Set X)ᶜ).Finite)
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      (IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g) ∧ Flat g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : X ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f := by
  have : IsReduced X := isReduced_of_syntomic_of_equidimensional k f hlci hfin hequi hdim
  obtain ⟨Xb, q, j, hj, hjq, hproj, hdom, -, hbd, hdvr⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced
      k f hdim.le
  have := hj
  have : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have hqlci : IsLocalCompleteIntersectionOverField q :=
    isLocalCompleteIntersectionOverField_of_isOpenImmersion k q f j hjq hlci
      (fun y hy => (hdvr y hy).2)
  have hqfin : ((q.smoothLocus : Set Xb)ᶜ).Finite :=
    finite_compl_smoothLocus_of_isOpenImmersion k q f j hjq hfin hbd
  have hqdim : topologicalKrullDim Xb ≤ 1 := by
    have : IsLocallyNoetherian Xb := LocallyOfFiniteType.isLocallyNoetherian q
    have : CompactSpace Xb := QuasiCompact.compactSpace_of_compactSpace q
    have : AlgebraicGeometry.IsNoetherian Xb := ⟨⟩
    have hdense : Dense (Set.range j.base) := hdom.denseRange
    exact (Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k j f q
      hjq hdense).trans hdim.le
  -- [Stacks, Tag 0E7Y] for the compactification.
  obtain ⟨Yb, G, hGflat, hGproj, hGsm, eb, heb⟩ :
      ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
        Flat g ∧ AlgebraicGeometry.IsProjective g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : Xb ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = q :=
    exists_flat_isProjective_smoothing_of_isProper k q hqlci hqdim hqfin
  -- Remove the boundary.
  obtain ⟨W, e', he'⟩ := exists_smoothing_of_opens k q G eb heb j.opensRange
  have : IsSeparated G := hGproj.isSeparated
  have : LocallyOfFiniteType G := hGproj.locallyOfFiniteType
  have : QuasiCompact G := hGproj.quasiCompact
  have : IsLocallyNoetherian Yb := LocallyOfFiniteType.isLocallyNoetherian G
  have hW : QuasiCompact W.ι := inferInstance
  refine ⟨W, W.ι ≫ G, ⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
    exact pullback_snd_ι_comp G _ W @Smooth hGsm
  · refine ⟨j.isoOpensRange ≪≫ e', ?_⟩
    rw [Iso.trans_hom, Category.assoc, he', ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hjq]

/-- **[Stacks, Tag 0E7Z].** Let `k` be a field and let `X` be a scheme over `k`. Assume
(1) `X` is separated, finite type over `k` and `dim(X) ≤ 1`, (2) `X` is a local complete
intersection over `k`, and (3) `X → Spec(k)` is smooth except at finitely many points. Then there
exists a flat, separated, finite type morphism `Y → Spec(k[[t]])` whose generic fibre is smooth and
whose special fibre is isomorphic to `X`.

Finite type is `LocallyOfFiniteType` together with `QuasiCompact`. The generic fibre is the fibre
over the zero ideal of `k⟦t⟧`, smooth over its residue field. The special fibre is the base change
along `Spec k ⟶ Spec k⟦t⟧` given by the constant coefficient, and the isomorphism with `X` is one
of schemes over `Spec k`. -/
@[stacks 0E7Z]
theorem exists_flat_separated_finiteType_smoothing {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) (hlci : IsLocalCompleteIntersectionOverField f)
    (hfin : ((f.smoothLocus : Set X)ᶜ).Finite) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : X ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f := by
  obtain ⟨U, V, hUV, hUci, hVci, hU0, hVequi, hVdim⟩ :=
    exists_isCompl_zeroDimensional_equidimensional k f hdim
  have hsyn : ∀ W : X.Opens, IsLocalCompleteIntersectionOverField (W.ι ≫ f) :=
    isLocalCompleteIntersectionOverField_ι_comp k f hlci
  have hset : IsCompl (U : Set X) (V : Set X) :=
    ⟨Set.disjoint_iff_inter_eq_empty.mpr (by
        rw [← TopologicalSpace.Opens.coe_inf, hUV.inf_eq_bot, TopologicalSpace.Opens.coe_bot]),
      codisjoint_iff.mpr (by
        change (U : Set X) ∪ V = Set.univ
        rw [← TopologicalSpace.Opens.coe_sup, hUV.sup_eq_top, TopologicalSpace.Opens.coe_top])⟩
  have hUcl : IsClosed (U : Set X) := hset.symm.compl_eq ▸ V.isOpen.isClosed_compl
  have hVcl : IsClosed (V : Set X) := hset.compl_eq ▸ U.isOpen.isClosed_compl
  -- The zero-dimensional piece, by [Stacks, Tag 0E7W].
  have zero : ∀ W : X.Opens, IsClosed (W : Set X) → topologicalKrullDim W ≤ 0 →
      ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
        (IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g) ∧ Flat g ∧
        Smooth (g.fiberToSpecResidueField
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
        ∃ e : W.toScheme ≅
            pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
          e.hom ≫ pullback.snd g
              (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = W.ι ≫ f := by
    intro W hW hW0
    have := quasiCompact_ι_comp_of_isClosed k f W hW
    obtain ⟨Y, g, hg, hfg, -, hsm, e, he⟩ :=
      exists_flat_finite_projective_smoothing_of_topologicalKrullDim_le_zero k (W.ι ≫ f)
        (hsyn W) hW0
    exact ⟨Y, g, ⟨inferInstance, inferInstance, inferInstance⟩, hg, hsm, e, he⟩
  obtain ⟨Y, g, ⟨hsep, hlft, hqc⟩, hg, hsm, e, he⟩ := exists_smoothing_of_isCompl k f hUV
    (fun _ _ g => IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g)
    (fun g₁ g₂ h₁ h₂ => separated_finiteType_coprodDesc g₁ g₂ h₁ h₂)
    (zero U hUcl hU0) (by
      by_cases hV : IsEmpty V
      · exact zero V hVcl ((topologicalKrullDim_eq_bot_iff_isEmpty V).mpr hV ▸ bot_le)
      · have := hVci
        have := quasiCompact_ι_comp_of_isClosed k f V hVcl
        exact exists_smoothing_of_equidimensional k (V.ι ≫ f) (hsyn V)
          (finite_compl_smoothLocus_ι_comp k f hfin V) hVequi (hVdim (not_isEmpty_iff.mp hV)))
  exact ⟨Y, g, hg, hsep, hlft, hqc, hsm, e, he⟩

end Deformation.Examples.Smoothing

end
