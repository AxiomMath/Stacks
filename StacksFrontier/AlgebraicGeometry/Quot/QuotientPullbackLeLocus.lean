module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapTargetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotientOrder

/-!
# The locus where a pulled-back submodule lies in the kernel of a pulled-back quotient

Let `D` be the standing data of Stacks 09TR — a morphism `f : X ⟶ B` of algebraic spaces of
finite presentation and a quasi-coherent `𝒪_X`-module `F` — and let `T` be a test scheme. For a
quasi-coherent submodule `K ⊆ F_T` and a member `F_T ⟶ Q'` of `Quot_{F/X/B}(T)` with kernel `K'`,
the morphisms `t : T' ⟶ T` of the site after which the pullback of `K` lies in the pullback of
`K'` are exactly those factoring through a closed subspace of `T`. The containment after base
change is the vanishing of the pullback of the composite `K ⟶ F_T ⟶ Q'`.

## Main results

* `QuotSituation.quotientPullback_le_iff_isZeroAt_subobjectToQuotientSituation`: the pullback
  of `K` lies in the pullback of `K'` exactly when the map `K ⟶ F_T ⟶ F_T/K'` vanishes after
  base change.
* `AlgebraicGeometry.Space.QuotSituation.exists_isClosedSubspace_quotientPullback_le`:
  the locus of `T` over which the pullback of `K` lies in the pullback of `K'` is a closed
  subspace of `T`.

## References

* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
* [Stacks Project, Tag 0DP5](https://stacks.math.columbia.edu/tag/0DP5)
* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The `𝒪_{X_T}`-modules here have their sections in the universe `u` of the schemes, which the
-- ambient-universe abelian structure of the cohomology of modules on a site cannot describe;
-- left in place it is selected ahead of `SheafOfModules.instAbelian` and leaves the module
-- universe of every subobject and cokernel below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- The map `K ⟶ F_T ⟶ F_T/K'` from a quasi-coherent submodule of `F_T` to a member of
`Quot_{F/X/B}(T)`, as the standing datum of Stacks 083F over the test scheme `T`. -/
def subobjectToQuotientSituation {T : SchemesOver D.Y} (K K' : Subobject (D.baseChangeModule T))
    (hK : SheafOfModules.IsQuasicoherentOnSite
      (K : Modules.{u, u} B S hS (D.space T).1 (D.space T).2))
    (hK' : K' ∈ D.properlySupportedQuotients T) :
    ModuleMapSituation.{u, u} B S hS where
  X := D.space T
  Y := (schemeSpaceFunctor B S hS).obj T.left
  f := D.projection T
  F := (K : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
  G := D.quotientModule T K'
  quasicoherent_F := hK
  quasicoherent_G := hK'.1.1.1
  u := K.arrow ≫ D.quotientProjection T K'

variable {T : SchemesOver D.Y} {K K' : Subobject (D.baseChangeModule T)}
  (hK : SheafOfModules.IsQuasicoherentOnSite
    (K : Modules.{u, u} B S hS (D.space T).1 (D.space T).2))
  (hK' : K' ∈ D.properlySupportedQuotients T)

/-- The comparison `X_{T'} ≅ X_T ×_T T'` of the base change of the situation to a morphism
`t : T' ⟶ T` of the site with the base change of the datum of
`AlgebraicGeometry.Space.QuotSituation.subobjectToQuotientSituation`. -/
def subobjectToQuotientSpaceIso {T' : BigFppfOver B S hS} (t : T' ⟶ T.left) :
    D.space (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom)) ≅
      (D.subobjectToQuotientSituation K K' hK hK').baseChangeSpace
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t)) :=
  IsPullback.isoIsPullback _ _
    (isPullback_baseChangeMap D.f (CostructuredArrow.homMk t rfl :
      CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T))
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (D.projection T)
      ((schemeSpaceFunctor B S hS).map t))

/-- The comparison `D.subobjectToQuotientSpaceIso hK hK' t`, followed by the projection of the
base change of `D.subobjectToQuotientSituation K K' hK hK'` to `X_T`, is the map `X_{T'} ⟶ X_T`
induced by `t`. -/
theorem subobjectToQuotientSpaceIso_hom_comp {T' : BigFppfOver B S hS} (t : T' ⟶ T.left) :
    (D.subobjectToQuotientSpaceIso hK hK' t).hom ≫
        (D.subobjectToQuotientSituation K K' hK hK').baseChangeProjection
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t)) =
      D.relativeMap (CostructuredArrow.homMk t rfl :
        CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **Containment of pulled-back submodules is the zero locus of Stacks 083F.** For a morphism
`t : T' ⟶ T` of the site, the pullback of `K` is contained in the pullback of `K'` exactly when
the map `K ⟶ F_T ⟶ F_T/K'` vanishes at the test scheme `t`. -/
theorem quotientPullback_le_iff_isZeroAt_subobjectToQuotientSituation
    {T' : BigFppfOver B S hS} (t : T' ⟶ T.left) :
    D.quotientPullback (CostructuredArrow.homMk t rfl :
        CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K ≤
      D.quotientPullback (CostructuredArrow.homMk t rfl :
        CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K' ↔
      (D.subobjectToQuotientSituation K K' hK hK').IsZeroAt (modulePullbackSystem B S hS)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t)) := by
  rw [show D.quotientPullback _ K ≤ D.quotientPullback _ K' ↔ _ from
    Functor.conjSubobject_le_conjSubobject_iff
      (preservesFiniteColimits_spaceModulePullback (D.relativeMap (CostructuredArrow.homMk t rfl :
        CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T)))
      (D.baseChangeComparison (CostructuredArrow.homMk t rfl :
        CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T)) K K']
  have key := (modulePullbackSystem B S hS).map_eq_zero_isIso_comp_iff
    (D.subobjectToQuotientSpaceIso hK hK' t).hom
    ((D.subobjectToQuotientSituation K K' hK hK').baseChangeProjection
      (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t)))
    (K.arrow ≫ D.quotientProjection T K')
  rwa [D.subobjectToQuotientSpaceIso_hom_comp hK hK' t] at key

include hK hK' in
/-- **The locus over which a pulled-back submodule lies in a pulled-back member of the Quot
functor is a closed subspace of the test scheme.** For a quasi-coherent submodule `K` of `F_T`
and `K'` in `Quot_{F/X/B}(T)`, there is a closed subspace `Z` of `T` such that a morphism
`t : T' ⟶ T` of the site factors through `Z` exactly when the pullback of `K` along `t` lies in
the pullback of `K'`. -/
theorem exists_isClosedSubspace_quotientPullback_le :
    ∃ Z : Subfunctor (yoneda.obj T.left), IsClosedSubspace B S hS Z ∧
      ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T.left),
        D.quotientPullback (CostructuredArrow.homMk t rfl :
            CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K ≤
          D.quotientPullback (CostructuredArrow.homMk t rfl :
            CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K' ↔
          ∃ k : yoneda.obj T' ⟶ Z.toFunctor, k ≫ Z.ι = yoneda.map t := by
  obtain ⟨Z, hZ, -, hZloc⟩ :=
    (D.subobjectToQuotientSituation K K' hK hK').zeroLocusRepresentation_of_hasProperSupport
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
        (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.finitePresentation.1)
      hK'.1.2 hK'.1.1.2 hK'.2
  refine ⟨Z, hZ, fun T' t ↦ ?_⟩
  rw [D.quotientPullback_le_iff_isZeroAt_subobjectToQuotientSituation hK hK' t, hZloc]
  rfl

end QuotSituation

end AlgebraicGeometry.Space

end
