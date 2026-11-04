module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapEtaleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompCondition

/-!
# Base change of `Rf_*` under the pointwise condition of Stacks 0DKG

For a cartesian square of algebraic spaces with `f` quasi-compact and quasi-separated,
`K ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` such that the map of
Equation 0DKF is invertible at every geometric point of `X'` and in every degree, the composite
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_geometricPointwiseBaseChange`
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0DKH.** For a cartesian square of algebraic spaces with `f` quasi-compact and
quasi-separated, `K ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` satisfying the
equivalent conditions of Stacks 0DKG (in the form of condition (1)), the composite
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism. -/
@[stacks 0DKH]
theorem isIso_smallEtaleDerivedBaseChangeComp_of_geometricPointwiseBaseChange
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w K K' φ) :=
  isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange B S hS sq hfqc hfqs K hK K'
    hK' φ ((geometricPointwiseBaseChange_iff_affineChartwiseBaseChange sq K hK K' hK' φ).mp h)

end AlgebraicGeometry.Space

end
