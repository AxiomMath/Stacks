module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafOfComplex
public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRankOneFreeLocusDescent

/-!
# The shape of the relative dualizing complex of a prestable family of curves

Let `f : X ⟶ S` be a prestable family of curves and `(ω^•_{X/S}, τ)` a relative dualizing
complex (Stacks 0E5X). This file proves that `ω^•_{X/S}` has cohomology sheaves only in degree
`-1` (Stacks 0E6P), so that `ω^•_{X/S} ≅ ω_{X/S}[1]` for the relative dualizing sheaf
`ω_{X/S} = H^{-1}(ω^•_{X/S})` (Stacks 0E6Q), and that `ω_{X/S}` is invertible (Stacks 0E6R).

Both assertions are étale local on `X`. The family is a scheme étale locally on `S`
(Stacks 0E6F), so every point of `X` lies in the image of the étale morphism `p : Z ⟶ X` of a
scheme chart `Z ⟶ U` over an affine `U`. There `Lp^*ω^•_{X/S}` is the right adjoint `a(𝒪_U)`
of `Rf_*` for the chart (the defining property of a relative dualizing complex), which is
read on the scheme by Stacks 0E6E; the chart is a proper at-worst-nodal family of schemes, for
which the base knows `a(𝒪_U)` (`AlgebraicGeometry.C1764Prereq.isZero_homology_chart`,
`AlgebraicGeometry.C1764Prereq.isInvertibleModule_homology_chart`). Étale pullback is exact, so
the cohomology sheaves of `ω^•_{X/S}` pull back to those of `Lp^*ω^•_{X/S}`.

## Main results

* `AlgebraicGeometry.C1764Prereq.isZero_homology_relDualizing_of_ne`: Stacks 0E6P.
* `AlgebraicGeometry.CurveFamily.isInvertible_dualizingSheafOfComplex`: Stacks 0E6R.
* `AlgebraicGeometry.C1764Prereq.nonempty_relDualizing_iso_single`: `ω^•_{X/S} ≅ ω_{X/S}[1]`.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Stacks 0E6P.** The cohomology sheaves of a relative dualizing complex of a prestable
family of curves vanish outside degree `-1`. On an affine étale scheme chart `p : Z ⟶ X` the
pullback of `H^i(ω^•_{X/S})` is `H^i(Lp^*ω^•_{X/S}) = 0`, so no point of `X` lies in the
support of `H^i(ω^•_{X/S})`. -/
theorem C1764Prereq.isZero_homology_relDualizing_of_ne {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) (i : ℤ) (hi : i ≠ -1) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj D.ω) := by
  refine Space.isZero_of_supportOfSheaf_eq_empty B integerBase hZ X.total _
    (Set.eq_empty_of_forall_notMem fun x hx => ?_)
  obtain ⟨U, Z, φ, q, p, hU, hp, hsq, w, rfl⟩ := C1764Prereq.exists_affine_chart X x
  have h₁ : IsZero ((Space.modulePullback B integerBase hZ p).obj
      ((DerivedCategory.homologyFunctor _ i).obj D.ω)) :=
    (C1764Prereq.isZero_homology_chart hX D hsq i hi).of_iso
      (Space.smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale p hp D.ω i).symm
  have h₂ := (Space.supportOfSheaf_eq_empty_iff_isZero B integerBase hZ (schemeSpace Z) _).2 h₁
  rw [Space.supportOfSheaf_modulePullback_eq_preimage_of_isFlat B integerBase hZ p
    (Space.isFlat_of_isEtale B integerBase hZ hp)] at h₂
  exact (Set.eq_empty_iff_forall_notMem.1 h₂ w) hx

/-- **Stacks 0E6R.** The relative dualizing sheaf `ω_{X/S} = H^{-1}(ω^•_{X/S})` of a prestable
family of curves is invertible. On an affine étale scheme chart `p : Z ⟶ X` the pullback of
`ω_{X/S}` is `H^{-1}(Lp^*ω^•_{X/S})`, which is invertible; so every point of `X` has an étale
neighbourhood on which `ω_{X/S}` is free of rank one (Stacks 0B8Q). -/
theorem CurveFamily.isInvertible_dualizingSheafOfComplex {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property
      (X.dualizingSheafOfComplex D) := by
  refine (Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    (Z := X.total) (X.dualizingSheafOfComplex D)).2
    (Space.isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus B integerBase hZ
      _ fun x => ?_)
  obtain ⟨U, Z, φ, q, p, hU, hp, hsq, w, rfl⟩ := C1764Prereq.exists_affine_chart X x
  have := C1764Prereq.isInvertibleModule_homology_chart hX D hsq
  have : Space.IsInvertibleModule (schemeSpace Z)
      ((Space.modulePullback B integerBase hZ p).obj (X.dualizingSheafOfComplex D)) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _
      (Space.smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale p hp D.ω (-1))
  exact Space.pointsMap_mem_etaleRankOneFreeLocus B integerBase hZ p hp _
    (Space.mem_etaleRankOneFreeLocus_of_isInvertibleModule _ _ this w)

/-- **`ω^•_{X/S} ≅ ω_{X/S}[1]`** (Stacks 0E6P, 0E6Q): a relative dualizing complex of a prestable
family of curves is its relative dualizing sheaf placed in degree `-1`. -/
theorem C1764Prereq.nonempty_relDualizing_iso_single {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    Nonempty (D.ω ≅ (DerivedCategory.singleFunctor _ (-1)).obj (X.dualizingSheafOfComplex D)) := by
  have : D.ω.IsLE (-1) := (DerivedCategory.isLE_iff _ _).2 fun i hi =>
    C1764Prereq.isZero_homology_relDualizing_of_ne hX D i (by omega)
  have : D.ω.IsGE (-1) := (DerivedCategory.isGE_iff _ _).2 fun i hi =>
    C1764Prereq.isZero_homology_relDualizing_of_ne hX D i (by omega)
  obtain ⟨A, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D.ω (-1)
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ (-1)).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-1)).app A).symm ≪≫
      (DerivedCategory.homologyFunctor _ (-1)).mapIso e.symm)⟩

end AlgebraicGeometry
