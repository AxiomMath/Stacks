module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BirationalGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusDisjointCover
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusReduction
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Composition
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import
  StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksCore.Tactic.StacksAttribute

/-!
# The geometric genus is a birational invariant in dimension one

Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`.  The
geometric genus `g_geom(X/k)` of `AlgebraicGeometry.geometricGenus` is unchanged by passing to
the reduction of `X`, by pulling back along a birational proper morphism onto `X`, and by passing
to the normalization of `X`.  This is [Stacks, Tag 0CE2], and
`AlgebraicGeometry.geometricGenus_reduction_birational_normalization` states all three clauses.

## Main results

* `AlgebraicGeometry.genus_eq_zero_of_topologicalKrullDim_le_zero`: a proper scheme of dimension
  at most zero over a field has genus zero.
* `AlgebraicGeometry.geometricGenus_eq_genus_normalizationOverField_of_dim_le_one`: over an
  algebraically closed field the geometric genus of a proper scheme of dimension at most one is
  exactly the genus of its normalization.
* `AlgebraicGeometry.geometricGenus_eq_of_isProper_of_isBirational`: clause (2), the geometric
  genus is unchanged along a birational proper morphism.
* `AlgebraicGeometry.geometricGenus_reduction_birational_normalization`: all three clauses of
  [Stacks, Tag 0CE2].

## References

* [Stacks Project, Tag 0CE2](https://stacks.math.columbia.edu/tag/0CE2)
* [Stacks Project, Tag 0CE1](https://stacks.math.columbia.edu/tag/0CE1)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The genus of a proper scheme of dimension at most zero over a field vanishes. -/
public theorem genus_eq_zero_of_topologicalKrullDim_le_zero (k : Type u) [Field k]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim (Z : Type u) ≤ (0 : WithBot ℕ∞)) :
    genus p = 0 := by
  have h1 : IsZero (cohomologyOverField k p (SheafOfModules.unit Z.ringCatSheaf) 1) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_le k p
      (SheafOfModules.unit Z.ringCatSheaf) (d := 0) (i := 1) hdim (by norm_num)
  have h2 : IsZero (structureSheafCohomology p 1) :=
    h1.of_iso (structureSheafCohomologyIsoCohomologyOverField k p 1)
  have := ModuleCat.subsingleton_of_isZero h2
  exact Module.finrank_zero_of_subsingleton

/-- Over an algebraically closed field, the geometric genus of a proper scheme of dimension at
most one is the genus of its normalization. -/
public theorem geometricGenus_eq_genus_normalizationOverField_of_dim_le_one
    (K : Type u) [Field K]
    [IsAlgClosed K] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of K)) [IsProper q]
    (hdim : topologicalKrullDim (Z : Type u) ≤ 1) :
    geometricGenus K q = genus (normalizationOverField K q ≫ q) := by
  classical
  have : IsNoetherian Z :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q }
  have : Finite (irreducibleComponents Z) :=
    (finite_irreducibleComponents_of_isNoetherian (X := Z)).to_subtype
  let : Fintype (irreducibleComponents Z) := Fintype.ofFinite _
  rw [geometricGenus_eq_sum_all_components q, genus_normalizationOverField_eq_sum_components K q]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  have hirr : IrreducibleSpace (irreducibleComponentIdeal W).subscheme := by
    apply Scheme.IdealSheafData.irreducibleSpace_subscheme
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact W.2.1
  have hdimW : topologicalKrullDim ((irreducibleComponentIdeal W).subscheme : Type u) ≤ 1 :=
    le_trans (irreducibleComponentIdeal
      W).subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le hdim
  rw [geometricGenus_eq_ite_genus_normalizationOverField K
    ((irreducibleComponentIdeal W).subschemeι ≫ q) hdimW]
  split_ifs with h
  · rfl
  · have : IsProper (normalizationOverField K ((irreducibleComponentIdeal W).subschemeι ≫ q) ≫
        ((irreducibleComponentIdeal W).subschemeι ≫ q)) :=
      isProper_normalizationOverField_comp K _
    refine (genus_eq_zero_of_topologicalKrullDim_le_zero K _ ?_).symm
    have hfin := isFinite_normalizationOverField K
      ((irreducibleComponentIdeal W).subschemeι ≫ q)
    have hdom := isDominant_normalizationOverField K
      ((irreducibleComponentIdeal W).subschemeι ≫ q)
    rw [topologicalKrullDim_eq_of_isFinite_of_isDominant
      (normalizationOverField K ((irreducibleComponentIdeal W).subschemeι ≫ q))]
    exact StacksTag09NX.le_zero_of_lt_one (lt_of_le_of_ne hdimW h)

/-! ### The geometric genus along a proper birational morphism -/

/-- **Stacks Project, Tag 0CE2 clause (2).** Let `k` be a field, let `X` be a proper scheme of
dimension at most one over `k` and let `f : X' ⟶ X` be a birational proper morphism.  Then `X'`
and `X` have the same geometric genus over `k`. -/
public theorem geometricGenus_eq_of_isProper_of_isBirational {k : Type u} [Field k]
    {X X' : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g] (f : X' ⟶ X) [IsProper f]
    (hf : IsBirational f) (hX : topologicalKrullDim (X : Type u) ≤ 1) :
    geometricGenus k (f ≫ g) = geometricGenus k g := by
  classical
  have hXnoeth : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  have hffin : IsFinite f := isFinite_of_isProper_of_isBirational f hf hX
  have hfdom : IsDominant f := hf.isDominant
  have hX' : topologicalKrullDim (X' : Type u) ≤ 1 := by
    rwa [topologicalKrullDim_eq_of_isFinite_of_isDominant f]
  obtain ⟨V, hVdense, hViso⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian f hf
  have hWpb := IsPullback.of_hasPullback g
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
  have hVpb := IsPullback.of_hasPullback (f ≫ g)
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
  have hsflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :=
    flat_specMap_algebraMap k (AlgebraicClosure k)
  have hpiflat : Flat (pullback.fst g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hWpb.flip hsflat
  have hpiflat' : Flat (pullback.fst (f ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hVpb.flip hsflat
  have hbp : NormalizedBaseChange.baseChangeMap hVpb hWpb ≫
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) =
      pullback.snd (f ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :=
    NormalizedBaseChange.baseChangeMap_comp_snd hVpb hWpb
  have hbpb := NormalizedBaseChange.isPullback_baseChangeMap hVpb hWpb
  have hbiso : IsIso (NormalizedBaseChange.baseChangeMap hVpb hWpb ∣_
      (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) ⁻¹ᵁ V)) :=
    NormalizedBaseChange.isIso_baseChangeMap_morphismRestrict hVpb hWpb V
  have hbbir : IsBirational (NormalizedBaseChange.baseChangeMap hVpb hWpb) := by
    refine isBirational_of_isIso_morphismRestrict _ _ hbiso ?_ ?_
    · intro x hx
      have hxy : pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
          (NormalizedBaseChange.baseChangeMap hVpb hWpb x) =
          f (pullback.fst (f ≫ g)
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) x) := by
        rw [← Scheme.Hom.comp_apply, hbpb.w, Scheme.Hom.comp_apply]
      show pullback.fst g _ (NormalizedBaseChange.baseChangeMap hVpb hWpb x) ∈ V
      rw [hxy]
      exact mem_of_mem_genericPoints_of_dense V hVdense
        (hf.bijOn.mapsTo (Scheme.Hom.mem_genericPoints_of_flat _ hx))
    · intro y hy
      exact mem_of_mem_genericPoints_of_dense V hVdense
        (Scheme.Hom.mem_genericPoints_of_flat _ hy)
  have hdimXK : topologicalKrullDim (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) : Type u) ≤ 1 := by
    rwa [topologicalKrullDim_baseChange k (AlgebraicClosure k) _ _ g (.of_hasPullback _ _)]
  have hdimX'K : topologicalKrullDim (pullback (C := Scheme.{u}) (f ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) : Type u) ≤ 1 := by
    rwa [topologicalKrullDim_baseChange k (AlgebraicClosure k) _ _ (f ≫ g) (.of_hasPullback _ _)]
  have hXKfin := finite_irreducibleComponents_of_locallyOfFiniteType (AlgebraicClosure k)
    (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  have hX'Knoeth : IsNoetherian (pullback (C := Scheme.{u}) (f ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) := {}
  have hX'Kcomp : Finite (irreducibleComponents (pullback (C := Scheme.{u}) (f ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  obtain ⟨hX'Kfin, lift, e, hlift, he⟩ :=
    exists_normalizationFactorization_of_isIntegralHom_of_isBirational hXKfin
      (NormalizedBaseChange.baseChangeMap hVpb hWpb)
      (fun U _ ↦ by
        have := finite_irreducibleComponents_opens
          (NormalizedBaseChange.baseChangeMap hVpb hWpb ⁻¹ᵁ U)
        exact Set.toFinite _) hbbir
  have hprop : IsProper (Scheme.normalization (pullback (C := Scheme.{u}) (f ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) hX'Kfin ≫
      pullback.snd (f ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
    isProper_normalizationOverField_comp (AlgebraicClosure k) _
  have hcomm : e.hom ≫ (Scheme.normalization _ hX'Kfin ≫ pullback.snd (f ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) =
      Scheme.normalization _ hXKfin ≫ pullback.snd g
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) := by
    rw [← Category.assoc, he, ← hbp, ← Category.assoc, hlift]
  rw [geometricGenus_eq_geometricGenus_pullback_snd k (f ≫ g) hX',
    geometricGenus_eq_geometricGenus_pullback_snd k g hX,
    geometricGenus_eq_genus_normalizationOverField_of_dim_le_one (AlgebraicClosure k) _ hdimX'K,
    geometricGenus_eq_genus_normalizationOverField_of_dim_le_one (AlgebraicClosure k) _ hdimXK,
    ← genus_comp_iso_eq (AlgebraicClosure k) (Scheme.normalization _ hX'Kfin ≫ pullback.snd (f ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) e, hcomm]

/-! ### All three clauses of the source -/

/-- Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`.  Then

1. the reduction `X_red` has the same geometric genus as `X`;
2. the source of a birational proper morphism `X' ⟶ X` has the same geometric genus as `X`; and
3. the normalization `X^ν` has the same geometric genus as `X`. -/
@[stacks 0CE2]
public theorem geometricGenus_reduction_birational_normalization {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hX : topologicalKrullDim (X : Type u) ≤ 1) :
    letI : IsProper (normalizationOverField k g ≫ g) :=
      isProper_normalizationOverField_comp k g
    geometricGenus k (X.reductionι ≫ g) = geometricGenus k g ∧
      (∀ (X' : Scheme.{u}) (f : X' ⟶ X) [IsProper f], IsBirational f →
        geometricGenus k (f ≫ g) = geometricGenus k g) ∧
      geometricGenus k (normalizationOverField k g ≫ g) = geometricGenus k g := by
  let : IsProper (normalizationOverField k g ≫ g) := isProper_normalizationOverField_comp k g
  refine ⟨(geometricGenus_reduction g).symm, fun X' f _ hf ↦
    geometricGenus_eq_of_isProper_of_isBirational g f hf hX, ?_⟩
  have hXfin := finite_irreducibleComponents_of_locallyOfFiniteType k g
  have hRfin := X.finite_irreducibleComponents_reduction hXfin
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hXfin
  have hdimR : topologicalKrullDim (X.nilradical.subscheme : Type u) ≤ 1 :=
    le_trans X.nilradical.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le hX
  have hνfin : IsFinite (X.nilradical.subscheme.normalization hRfin) :=
    isFinite_normalizationOverField k (X.nilradical.subschemeι ≫ g)
  have hRred : IsReduced X.nilradical.subscheme := inferInstanceAs (IsReduced X.reduction)
  have hνbir : IsBirational (X.nilradical.subscheme.normalization hRfin) :=
    Scheme.isBirational_normalization X.nilradical.subscheme hRfin
  have hfac : e.hom ≫ (X.nilradical.subscheme.normalization hRfin ≫
      X.nilradical.subschemeι) = normalizationOverField k g := he
  calc geometricGenus k (normalizationOverField k g ≫ g)
      = geometricGenus k (X.nilradical.subscheme.normalization hRfin ≫
          (X.nilradical.subschemeι ≫ g)) :=
        geometricGenus_eq_of_iso _ e (by rw [← hfac]; simp only [Category.assoc])
    _ = geometricGenus k (X.nilradical.subschemeι ≫ g) :=
        geometricGenus_eq_of_isProper_of_isBirational (X.nilradical.subschemeι ≫ g)
          (X.nilradical.subscheme.normalization hRfin) hνbir hdimR
    _ = geometricGenus k g := (geometricGenus_reduction g).symm

end AlgebraicGeometry

end
