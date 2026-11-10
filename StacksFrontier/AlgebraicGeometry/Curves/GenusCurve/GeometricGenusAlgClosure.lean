module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# The geometric genus of a base change to an algebraic closure

`AlgebraicGeometry.geometricGenus` of a proper scheme `X` over a field `k` is defined as a sum of
genera of normalizations indexed by the irreducible components of the base change `X_{k̄}`.  The
base change is itself a proper scheme over the algebraically closed field `k̄`, so it has a
geometric genus of its own, computed through a *second* base change, this time to an algebraic
closure of `k̄`.  This file proves that the two numbers agree for a scheme of dimension at most
one: `g_geom(X/k) = g_geom(X_{k̄}/k̄)`.

## Main results

* `AlgebraicGeometry.isIso_specMap_algebraMap_algebraicClosure`: `Spec` of the inclusion of an
  algebraically closed field into its algebraic closure is an isomorphism.
* `AlgebraicGeometry.isIso_pullback_fst_algebraicClosure`: base change along that inclusion is an
  isomorphism.
* `AlgebraicGeometry.genus_normalizationOverField_pullback_snd_eq`: over an algebraically closed
  field, the normalization of the base change to an algebraic closure has the genus of the
  normalization of the scheme itself.
* `AlgebraicGeometry.geometricGenus_eq_ite_genus_normalizationOverField`: over an algebraically
  closed field, the geometric genus of an irreducible reduced proper scheme of dimension at most
  one is the genus of its normalization in dimension one and zero otherwise.
* `AlgebraicGeometry.geometricGenus_eq_geometricGenus_pullback_snd`: the geometric genus over `k`
  of a proper scheme of dimension at most one equals the geometric genus over `k̄` of its base
  change to an algebraic closure.

## References

* [Stacks Project, Tag 0CE1](https://stacks.math.columbia.edu/tag/0CE1)
* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- `Spec` of the inclusion of an algebraically closed field into its algebraic closure is an
isomorphism. -/
public theorem isIso_specMap_algebraMap_algebraicClosure (K : Type u) [Field K] [IsAlgClosed K] :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
  have : IsIso (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    (RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).toCommRingCatIso.isIso_hom
  inferInstance

/-- The base change of a scheme over an algebraically closed field `K` to an algebraic closure of
`K` is isomorphic to the scheme itself, the first projection being the isomorphism. -/
public theorem isIso_pullback_fst_algebraicClosure (K : Type u) [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (c : Z ⟶ Spec (.of K)) :
    IsIso (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) :=
  have := isIso_specMap_algebraMap_algebraicClosure K
  (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso

/-- Over an algebraically closed field `K`, the normalization of the base change of a scheme to
an algebraic closure of `K` has the genus of the normalization of the scheme itself. -/
public theorem genus_normalizationOverField_pullback_snd_eq (K : Type u) [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (c : Z ⟶ Spec (.of K)) [IsProper c] :
    genus (normalizationOverField (AlgebraicClosure K)
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) ≫
      pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) =
      genus (normalizationOverField K c ≫ c) := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) with ha
  have : IsIso a := isIso_specMap_algebraMap_algebraicClosure K
  have : IsIso (pullback.fst c a) := isIso_pullback_fst_algebraicClosure K c
  have hBfin : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_locallyOfFiniteType K c
  have hAfin := finite_irreducibleComponents_of_smooth (pullback.fst c a) hBfin
  have hsq := isPullback_normalizationSchemeMap_of_etale (pullback.fst c a) hBfin
  have hiso : IsIso (normalizationSchemeMap (pullback.fst c a) hAfin hBfin) := by
    refine ⟨hsq.lift (𝟙 _) (Z.normalization hBfin ≫ inv (pullback.fst c a)) (by simp), ?_,
      hsq.lift_fst _ _ _⟩
    refine hsq.hom_ext ?_ ?_
    · rw [Category.assoc, hsq.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hsq.lift_snd, Category.id_comp, ← Category.assoc, hsq.w,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hw : normalizationSchemeMap (pullback.fst c a) hAfin hBfin ≫ Z.normalization hBfin =
      (pullback (C := Scheme.{u}) c a).normalization hAfin ≫ pullback.fst c a := hsq.w
  have hcomm : normalizationSchemeMap (pullback.fst c a) hAfin hBfin ≫
      (Z.normalization hBfin ≫ c) =
      ((pullback (C := Scheme.{u}) c a).normalization hAfin ≫ pullback.snd c a) ≫ a := by
    rw [← Category.assoc, hw, Category.assoc, pullback.condition, ← Category.assoc]
  have : IsProper (Z.normalization hBfin ≫ c) := isProper_normalizationOverField_comp K c
  exact genus_baseChange K (AlgebraicClosure K) _ _ _ (IsPullback.of_horiz_isIso ⟨hcomm⟩)

/-- Over an algebraically closed field `K`, the geometric genus of an irreducible, reduced and
proper scheme of dimension at most one is the genus of its normalization when it has dimension
one, and zero otherwise. -/
public theorem geometricGenus_eq_ite_genus_normalizationOverField (K : Type u) [Field K]
    [IsAlgClosed K] {Z : Scheme.{u}} (c : Z ⟶ Spec (.of K)) [IsProper c] [IrreducibleSpace Z]
    [IsReduced Z] (hle : topologicalKrullDim (Z : Type u) ≤ 1) :
    geometricGenus K c =
      if topologicalKrullDim (Z : Type u) = 1 then
        genus (normalizationOverField K c ≫ c)
      else 0 := by
  by_cases h : topologicalKrullDim (Z : Type u) = 1
  · rw [ite_eq_left h]
    have := isIso_pullback_fst_algebraicClosure K c
    set a := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) with ha
    have hirr : IrreducibleSpace (pullback (C := Scheme.{u}) c a) :=
      (Scheme.homeoOfIso (asIso (pullback.fst c a))).irreducibleSpace_iff.mpr ‹_›
    have hred : IsReduced (pullback (C := Scheme.{u}) c a) :=
      isReduced_of_isOpenImmersion (pullback.fst c a)
    have hdim : topologicalKrullDim (pullback (C := Scheme.{u}) c a : Type u) = 1 := by
      rwa [IsHomeomorph.topologicalKrullDim_eq _
        (Scheme.homeoOfIso (asIso (pullback.fst c a))).isHomeomorph]
    rw [geometricGenus_eq_genus_normalizationOverField K c hirr hred hdim, ← ha]
    exact genus_normalizationOverField_pullback_snd_eq K c
  · rw [ite_eq_right h]
    exact geometricGenus_eq_zero_of_dim_lt_one c (lt_of_le_of_ne hle h)

/-- **The geometric genus is computed by the base change to an algebraic closure.**  For a proper
scheme `X` of dimension at most one over a field `k`, the geometric genus of `X` over `k` equals
the geometric genus of `X_{k̄}` over the algebraic closure `k̄`. -/
public theorem geometricGenus_eq_geometricGenus_pullback_snd (k : Type u) [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hX : topologicalKrullDim (X : Type u) ≤ 1) :
    geometricGenus k g = geometricGenus (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) := by
  classical
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) with ha
  have : IsNoetherian (pullback (C := Scheme.{u}) g a) := {}
  let : Finite (irreducibleComponents (pullback (C := Scheme.{u}) g a)) :=
    (finite_irreducibleComponents_of_isNoetherian
      (X := pullback (C := Scheme.{u}) g a)).to_subtype
  let : Fintype (irreducibleComponents (pullback (C := Scheme.{u}) g a)) := Fintype.ofFinite _
  have hdimY : topologicalKrullDim (pullback (C := Scheme.{u}) g a : Type u) ≤ 1 := by
    rwa [topologicalKrullDim_baseChange k (AlgebraicClosure k) _ _ g (.of_hasPullback _ _)]
  rw [geometricGenus_eq_sum_all_components (pullback.snd g a)]
  change ∑ Z : irreducibleComponents (pullback (C := Scheme.{u}) g a),
      (if topologicalKrullDim (irreducibleComponentIdeal Z).subscheme = 1 then
        genus (normalizationOverField (AlgebraicClosure k)
            ((irreducibleComponentIdeal Z).subschemeι ≫ pullback.snd g a) ≫
          ((irreducibleComponentIdeal Z).subschemeι ≫ pullback.snd g a))
      else 0) = _
  refine Finset.sum_congr rfl fun Z _ => ?_
  have hirr : IrreducibleSpace (irreducibleComponentIdeal Z).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme _ _
      ((Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _).symm ▸ Z.2.1)
  have hdimZ : topologicalKrullDim ((irreducibleComponentIdeal Z).subscheme : Type u) ≤ 1 :=
    le_trans (irreducibleComponentIdeal
      Z).subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le hdimY
  exact (geometricGenus_eq_ite_genus_normalizationOverField (AlgebraicClosure k)
    ((irreducibleComponentIdeal Z).subschemeι ≫ pullback.snd g a) hdimZ).symm

end AlgebraicGeometry

end
