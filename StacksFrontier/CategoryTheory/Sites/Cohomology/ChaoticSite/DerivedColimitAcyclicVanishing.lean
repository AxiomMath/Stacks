module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionVanishing
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.ExtendedMooreBaseChange

/-!
# `Lπ_! = π_!` at a diagram with no higher derived colimits

Let `C` be a small category carrying the chaotic topology and let `D` be an abelian category with
coproducts indexed by the morphism universe of `C`, so that `π_!` is the colimit over `Cᵒᵖ` and
`Lπ_!` is its total left derived functor (`Stacks.CategoryHomology.totalDerivedColimit`). Let `Z`
be a diagram `Cᵒᵖ ⥤ D` with `L_nπ_!(Z) = 0` for every `n > 0`. Then the comparison
`Lπ_!(Z) ⟶ π_!(Z)` of the left derived functor is invertible at `Z` placed in degree zero.

This is the hypothesis-free form of
`Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_projective_restrict`, whose
hypothesis is that `Z` restrict to a **projective** simplicial object along a point resolution.
That hypothesis can fail where the vanishing holds: for a diagram of `B`-modules read on
underlying abelian groups the restriction is a simplicial abelian group built out of `B`, and `B`
need not be projective over `ℤ` — `ℤ/2` is not — while the vanishing follows from the module half
of Tag 08Q9 (`Stacks.ChaoticSite.leftDerivedColimForgetIso`). This is the case of
[Stacks, Tag 09CZ].

## Main results

* `Stacks.ChaoticSite.quasiIso_colimMap_projectiveResolution_of_isZero_leftDerived`: the colimit
  over `Cᵒᵖ`, applied degreewise, carries a projective resolution of such a `Z` to a
  quasi-isomorphism.
* `Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_isZero_leftDerived`: the
  comparison of `Lπ_!` with `π_!` is invertible at `Z` placed in degree zero.

## Implementation notes

The mechanism of the second statement is the one of
`Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_projective_restrict`: the
comparison of a total left derived functor is invertible at a K-projective complex, and
`Stacks.Homology.isIso_leftDerivedCounit_app_of_isIso_map` moves that along the augmentation of a
projective resolution, whose only hypothesis is that the underived functor invert it. Only that
hypothesis is proved differently here.

Its proof is the `ℕ`-indexed statement
`RingTheory.TorIndependence.quasiIso_map_projectiveResolution_of_isZero_leftDerived` carried to
the `ℤ`-indexed `CategoryTheory.ProjectiveResolution.π'` along
`ComplexShape.embeddingDownNat`, by
`HomologicalComplex.quasiIso_extendMap_iff` together with
`HomologicalComplex.mapHomologicalComplexExtendIso` and the factorisation of `π'` through
`HomologicalComplex.extendMap`. That factorisation holds by `rfl`, but its two sides are stated
at definitionally equal and syntactically distinct types, so it is used through
`HomologicalComplex.quasiIso_of_eq` rather than by `rw`.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChaoticSite

universe vD uD u

variable {C : Type u} [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

attribute [local instance] HasDerivedCategory.standard

omit [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D] in
/-- **The colimit over `Cᵒᵖ` carries a projective resolution of an acyclic diagram to a
quasi-isomorphism.** The statement for the `ℕ`-indexed resolution is
`RingTheory.TorIndependence.quasiIso_map_projectiveResolution_of_isZero_leftDerived`; this
carries it to the `ℤ`-indexed `CategoryTheory.ProjectiveResolution.π'`. -/
theorem quasiIso_colimMap_projectiveResolution_of_isZero_leftDerived (Z : Cᵒᵖ ⥤ D)
    (hZ : ∀ n : ℕ, 0 < n →
      IsZero ((((colim : (Cᵒᵖ ⥤ D) ⥤ D)).leftDerived n).obj Z)) :
    QuasiIso (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (ProjectiveResolution.of Z).π') := by
  have h1 : QuasiIso (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (ProjectiveResolution.of Z).π) :=
    RingTheory.TorIndependence.quasiIso_map_projectiveResolution_of_isZero_leftDerived
      (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ProjectiveResolution.of Z) hZ
  have h2 : QuasiIso (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (ProjectiveResolution.of Z).π
        ComplexShape.embeddingDownNat)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (HomologicalComplex.mapHomologicalComplexExtendIso (colim : (Cᵒᵖ ⥤ D) ⥤ D)
          (ProjectiveResolution.of Z).complex ComplexShape.embeddingDownNat).symm
        (HomologicalComplex.mapHomologicalComplexExtendIso (colim : (Cᵒᵖ ⥤ D) ⥤ D)
          ((ChainComplex.single₀ (Cᵒᵖ ⥤ D)).obj Z) ComplexShape.embeddingDownNat).symm
        (HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
          (colim : (Cᵒᵖ ⥤ D) ⥤ D) _ (ProjectiveResolution.of Z).π
          ComplexShape.embeddingDownNat).symm)).2
      ((HomologicalComplex.quasiIso_extendMap_iff _ _).2 h1)
  have hpi : (ProjectiveResolution.of Z).π' =
      HomologicalComplex.extendMap (ProjectiveResolution.of Z).π
          ComplexShape.embeddingDownNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat Z 0 0 (by simp)).hom :=
    rfl
  have hcomp : QuasiIso (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (ProjectiveResolution.of Z).π
          ComplexShape.embeddingDownNat) ≫
    ((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat Z 0 0 (by simp)).hom) :=
    (quasiIso_iff_comp_right _ _).mpr h2
  refine HomologicalComplex.quasiIso_of_eq ?_ hcomp
  exact (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (congrArg ((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map hpi.symm)

/-- **`Lπ_!(Z) = π_!(Z)` at a diagram with no higher derived colimits.** The comparison of the
total left derived functor `Stacks.CategoryHomology.totalDerivedColimit` with the colimit itself
is invertible at `Z` placed in degree zero, as soon as `L_nπ_!(Z) = 0` for every `n > 0`. -/
theorem isIso_totalDerivedColimitCounit_single_of_isZero_leftDerived (Z : Cᵒᵖ ⥤ D)
    (hZ : ∀ n : ℕ, 0 < n →
      IsZero ((((colim : (Cᵒᵖ ⥤ D) ⥤ D)).leftDerived n).obj Z)) :
    IsIso ((Stacks.CategoryHomology.totalDerivedColimitCounit C D).app
      ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj Z))) := by
  have := Stacks.CategoryHomology.colim_hasPointwiseLeftDerivedFunctor C D
  have := Stacks.CategoryHomology.totalDerivedColimit_isLeftDerivedFunctor C D
  have : CochainComplex.IsKProjective (ProjectiveResolution.of Z).cochainComplex :=
    CochainComplex.isKProjective_of_projective _ 0
  have := quasiIso_colimMap_projectiveResolution_of_isZero_leftDerived D Z hZ
  refine Stacks.Homology.isIso_leftDerivedCounit_app_of_isIso_map
    (P := (ProjectiveResolution.of Z).cochainComplex)
    (Stacks.CategoryHomology.totalDerivedColimit C D)
    (Stacks.CategoryHomology.totalDerivedColimitCounit C D)
    ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
      (ProjectiveResolution.of Z).π') ?_ ?_
  · exact Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso _
  · exact Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso
      (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ProjectiveResolution.of Z).π')

end Stacks.ChaoticSite

end
