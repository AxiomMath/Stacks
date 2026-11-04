module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExactNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Restriction of coherent adic systems to an étale chart

Let `X` be an algebraic space over a scheme `S`, let `U` be an affine étale scheme chart of `X`
and let `𝓘 ⊆ 𝒪_X` be a sheaf of ideals.  The restriction functor `Coh(X, 𝓘) ⥤ Coh(U, 𝓘𝒪_U)` is
the inverse image functor along the étale structure morphism `h_U ⟶ X` of the chart, viewed as a
morphism of algebraic spaces.  When `X` is Noetherian in the sense of Stacks 03EA, so is `U`, and
the restriction functor is exact.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicRestrictToChart` — **the restriction functor
  `Coh(X, 𝓘) ⥤ Coh(U, 𝓘𝒪_U)` at an étale chart `U` of `X`.**

## Main results

* `AlgebraicGeometry.Space.isNoetherian_chartSpace_of_isAffine` — **an affine étale chart of a
  Noetherian algebraic space is a Noetherian algebraic space.**
* `AlgebraicGeometry.Space.coherentAdicRestrictToChart_exact` and
  `AlgebraicGeometry.Space.preservesFiniteLimits_coherentAdicRestrictToChart` — **restriction to
  an étale chart is exact.**

## References

* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-! ### The chart as a Noetherian algebraic space -/

/-- **An affine étale chart of an algebraic space is quasi-compact.** -/
theorem isQuasiCompactSpace_chartSpace_of_isAffine (hU : IsAffine (chartScheme U)) :
    IsQuasiCompactSpace B S hS (chartSpace B S hS X U).1 :=
  isQuasiCompactSpace_yoneda_of_isAffine B S hS ((SmallEtale.toOver B S hS X.1).obj U) hU

/-- **An affine étale chart of an algebraic space is absolutely quasi-separated.** -/
theorem isAbsolutelyQuasiSeparated_chartSpace_of_isAffine
    (hZ : B.Contains (⊤_ Scheme.{u})) (hU : IsAffine (chartScheme U)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (chartSpace B S hS X U).1 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (chartSpace B S hS X U).1 hZ
    ⟨(SmallEtale.toOver B S hS X.1).obj U,
      have := hU
      inferInstance,
      ⟨⟨Equiv.refl _, fun _ _ => rfl⟩⟩⟩

/-- **An étale chart of a locally Noetherian algebraic space is locally Noetherian**, with no
affineness hypothesis. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_chartSpace
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    HasEtaleLocalProperty B S hS (chartSpace B S hS X U).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (chartSpace B S hS X U).2 X.2
    (chartToSpace B S hS X U).hom
    (isLocallyOfFiniteType_of_isEtale' B S hS _ (isEtale_chartToSpace B S hS X U)) hLN

/-- **An affine étale chart of a Noetherian algebraic space is a Noetherian algebraic space**, in
the sense of Stacks 03EA. -/
theorem isNoetherian_chartSpace_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hU : IsAffine (chartScheme U)) :
    IsNoetherian B S hS hZ (chartSpace B S hS X U).1 :=
  ⟨isQuasiCompactSpace_chartSpace_of_isAffine B S hS X U hU,
    isAbsolutelyQuasiSeparated_chartSpace_of_isAffine B S hS X U hZ hU,
    hasEtaleLocalProperty_isLocallyNoetherian_chartSpace B S hS X U hN.2.2⟩

/-! ### Restriction to the chart -/

variable
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (𝓘' : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1)
    (hU : IsAffine (chartScheme U))
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (hIcart' : IsCartesianOnAffineCharts 𝓘'.toSheafOfModules)
    (hw : IdealPowerMultipleCompatible B S hS
      (modulePullback B S hS (chartToSpace B S hS X U)) 𝓘 𝓘')

/-- **The restriction functor `Coh(X, 𝓘) ⥤ Coh(U, 𝓘𝒪_U)` at an affine étale chart `U` of `X`.** -/
def coherentAdicRestrictToChart :
    CoherentAdicSystems B S hS X.1 X.2 𝓘 ⥤
      CoherentAdicSystems B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 𝓘' :=
  coherentAdicPullback B S hS (chartToSpace B S hS X U) 𝓘 𝓘' hw
    (isCoherent_modulePullback_of_hasEtaleLocalProperty B S hS (chartToSpace B S hS X U)
      (isNoetherian_chartSpace_of_isAffine B S hS X U hZ hN hU).2.2)

include hIcart hIcart' in
/-- **Restriction to an affine étale chart of a Noetherian algebraic space is exact.** -/
theorem coherentAdicRestrictToChart_exact :
    exactFunctor (CoherentAdicSystems B S hS X.1 X.2 𝓘)
        (CoherentAdicSystems B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 𝓘')
      (coherentAdicRestrictToChart B S hS X U 𝓘 𝓘' hZ hN hU hw) :=
  coherentAdicPullback_exact B S hS (chartToSpace B S hS X U) 𝓘 𝓘' hZ hN
    (isNoetherian_chartSpace_of_isAffine B S hS X U hZ hN hU) hIcart hIcart' hw
    (isFlat_of_isEtale B S hS (isEtale_chartToSpace B S hS X U))

include hIcart hIcart' in
/-- **Restriction to an affine étale chart preserves finite limits**, and in particular carries
the cycles of a short complex of coherent adic systems to the cycles of the restricted complex. -/
theorem preservesFiniteLimits_coherentAdicRestrictToChart :
    PreservesFiniteLimits (coherentAdicRestrictToChart B S hS X U 𝓘 𝓘' hZ hN hU hw) :=
  ((exactFunctor_iff _).1
    (coherentAdicRestrictToChart_exact B S hS X U 𝓘 𝓘' hZ hN hU hIcart hIcart' hw)).1

end AlgebraicGeometry.Space

end
