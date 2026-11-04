module

public import StacksFrontier.AlgebraicGeometry.Curves.GeometricGenusBridge.NormalizationModel
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusAlgClosure

/-!
# The geometric genus of a proper scheme as a sum of geometric genera in the sense of 0BYF

`AlgebraicGeometry.geometricGenus k g` of a proper scheme `X` over a field `k` is defined as the
sum, over the one-dimensional irreducible components `Z` of `X_{k̄}` with their reduced structure,
of the genus of the normalization of `Z` over `k̄`. Each such `Z` is a proper curve over the
algebraically closed field `k̄`, and by
`AlgebraicGeometry.genus_normalizationOverField_eq_geometricGenusOfModel` the genus of its
normalization is its geometric genus in the sense of [Stacks, Tag 0BYF], read off any
nonsingular projective model of `(Z_L)_red` over any extension `L/k̄`. So `geometricGenus` is the
sum of the 0BYF geometric genera of the one-dimensional geometric components.

## Main results

* `AlgebraicGeometry.geometricGenus_eq_geometricGenusOfModel`: for a proper curve `C` over an
  algebraically closed field `K`, `geometricGenus K c` is the 0BYF geometric genus of `C`, for
  every extension `L/K` and every nonsingular projective model of `(C_L)_red`.
* `AlgebraicGeometry.isCurve_irreducibleComponentIdeal_subschemeι_comp`: a one-dimensional
  irreducible component of a proper scheme over a field, with its reduced structure, is a proper
  curve.
* `AlgebraicGeometry.geometricGenus_eq_sum_geometricGenusOfModel`: `geometricGenus k g` is the
  sum, over the one-dimensional irreducible components `Z` of `X_{k̄}`, of the 0BYF geometric
  genus of `Z` over `k̄`, read off any family of models over any extension `L/k̄`.

## References

* [Stacks Project, Tag 0BYF](https://stacks.math.columbia.edu/tag/0BYF)
* [Stacks Project, Tag 0CE0](https://stacks.math.columbia.edu/tag/0CE0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **For a proper curve over an algebraically closed field, `geometricGenus` is the geometric
genus of [Stacks, Tag 0BYF].** Let `K` be algebraically closed, `C` a proper curve over `K`,
`L/K` a field extension and `M` a nonsingular projective model of `(C_L)_red` over `L`. Then
`geometricGenus K c = geometricGenusOfModel K L c M`. -/
theorem geometricGenus_eq_geometricGenusOfModel (K : Type u) [Field K] [IsAlgClosed K]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [IsProper c]
    (L : Type u) [Field L] [Algebra K L] :
    haveI : GeometricallyIrreducible c :=
      geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K C c
    ∀ M : NonsingularProjectiveModel L (reducedBaseChange K L c)
        (reducedBaseChangeStructureMap K L c),
      geometricGenus K c = geometricGenusOfModel K L c M := by
  intro M
  have h1 : topologicalKrullDim C = 1 := IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)
  rw [geometricGenus_eq_ite_genus_normalizationOverField K c h1.le, ite_eq_left h1]
  exact genus_normalizationOverField_eq_geometricGenusOfModel K c L M

/-- **A one-dimensional irreducible component of a proper scheme over a field is a proper
curve.** Let `q : Y ⟶ Spec K` be proper and `Z` an irreducible component of `Y` of dimension
one, with its reduced closed subscheme structure. Then `Z` is a curve over `K`: it is integral
(reduced and irreducible), separated, of finite type and of dimension one. -/
theorem isCurve_irreducibleComponentIdeal_subschemeι_comp (K : Type u) [Field K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [IsProper q] (Z : irreducibleComponents Y)
    (h : topologicalKrullDim (irreducibleComponentIdeal Z).subscheme = 1) :
    IsCurve K ((irreducibleComponentIdeal Z).subschemeι ≫ q) := by
  have : IrreducibleSpace (irreducibleComponentIdeal Z).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme _ _ <| by
      rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]; exact Z.2.1
  have : IsIntegral (irreducibleComponentIdeal Z).subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hP : IsProper ((irreducibleComponentIdeal Z).subschemeι ≫ q) := inferInstance
  exact { toLocallyOfFiniteType := hP.toLocallyOfFiniteType, toIsSeparated := hP.toIsSeparated,
          topologicalKrullDim_eq_one := h }

/-- **`geometricGenus` is the sum of the geometric genera of [Stacks, Tag 0BYF] of the
one-dimensional geometric components.** Let `X` be proper over a field `k`, with base change
`q : X_{k̄} ⟶ Spec k̄`. For each irreducible component `Z` of `X_{k̄}` of dimension one, with its
reduced structure (a proper curve over `k̄`, geometrically irreducible as `k̄` is algebraically
closed), let `M Z` be a nonsingular projective model of `(Z_L)_red` over a fixed extension
`L/k̄`. Then `geometricGenus k g` is the sum over these components of
`geometricGenusOfModel k̄ L Z (M Z)`. -/
theorem geometricGenus_eq_sum_geometricGenusOfModel (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsProper g] (L : Type u) [Field L] [Algebra (AlgebraicClosure k) L]
    [Fintype (irreducibleComponents
      (pullback (C := Scheme.{u}) g
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))]
    (M : ∀ (Z : irreducibleComponents
        (pullback (C := Scheme.{u}) g
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
      (h : topologicalKrullDim (irreducibleComponentIdeal Z).subscheme = 1),
      haveI := isCurve_irreducibleComponentIdeal_subschemeι_comp (AlgebraicClosure k)
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) Z h
      haveI : GeometricallyIrreducible ((irreducibleComponentIdeal Z).subschemeι ≫
          pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
        geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed (AlgebraicClosure k) _ _
      NonsingularProjectiveModel L
        (reducedBaseChange (AlgebraicClosure k) L ((irreducibleComponentIdeal Z).subschemeι ≫
          pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
        (reducedBaseChangeStructureMap (AlgebraicClosure k) L
          ((irreducibleComponentIdeal Z).subschemeι ≫
            pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))) :
    geometricGenus k g =
      ∑ Z, if h : topologicalKrullDim (irreducibleComponentIdeal Z).subscheme = 1 then
        haveI := isCurve_irreducibleComponentIdeal_subschemeι_comp (AlgebraicClosure k)
          (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) Z h
        haveI : GeometricallyIrreducible ((irreducibleComponentIdeal Z).subschemeι ≫
            pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
          geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed (AlgebraicClosure k) _ _
        geometricGenusOfModel (AlgebraicClosure k) L _ (M Z h)
      else 0 := by
  classical
  unfold geometricGenus
  dsimp only
  refine Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun Z _ => ?_
  by_cases h : topologicalKrullDim (irreducibleComponentIdeal Z).subscheme = 1
  · rw [ite_eq_left h, dite_eq_left h]
    have := isCurve_irreducibleComponentIdeal_subschemeι_comp (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) Z h
    exact genus_normalizationOverField_eq_geometricGenusOfModel (AlgebraicClosure k) _ L (M Z h)
  · rw [ite_eq_right h, dite_eq_right h]

end AlgebraicGeometry

end
