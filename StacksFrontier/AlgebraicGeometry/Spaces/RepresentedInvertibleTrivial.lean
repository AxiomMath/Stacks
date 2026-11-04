module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleReflects
public import StacksFrontier.AlgebraicGeometry.Modules.SpecGlobalSectionsTrivial
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPointInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# An invertible module on the spectrum of a local ring is the structure sheaf

Let `U` be an object of the big fppf site over `S` whose underlying scheme is the spectrum of a
ring and carries a point with no proper open neighbourhood — the spectrum of a *local* ring and
its closed point.  Then every invertible `𝒪`-module on the small étale site of the representable
algebraic space `yoneda.obj U` is isomorphic to the structure sheaf.

This is the sheaf-level form, on the small étale site, of the triviality of the Picard group of
a local ring, and it is the input Stacks 0EPQ uses to choose a generator of an invertible module
at a codimension-zero point.

The proof has three steps and no new mathematics beyond assembling them.

* The sections over the whole chart of the restriction of an invertible module to an étale
  scheme chart carrying such a point are free of rank one,
  `AlgebraicGeometry.Space.nonempty_linearEquiv_chartRestrictionTop_of_isInvertibleModule`.  At
  the *identity* chart of `yoneda.obj U` that restriction is the right adjoint of the
  associated-module functor of Stacks 03DU applied to the module read on the small étale site of
  the scheme, by `AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`.
* A quasi-coherent module on the spectrum of a ring whose global sections are free of rank one is
  the structure sheaf, `AlgebraicGeometry.nonempty_iso_unit_of_isQuasicoherent_of_gammaTop`.  The
  structure sheaf itself restricts to the structure sheaf of the chart,
  `AlgebraicGeometry.Space.restrictToChartSchemeUnitIso`, so the two restrictions agree.
* Restriction to the small Zariski site reflects isomorphisms between quasi-coherent modules on
  the small étale site, `AlgebraicGeometry.SmallEtale.nonempty_iso_of_iso_restrictModule`, which
  is Descent, Proposition 03DX (2) at `τ = étale`; and the comparison of the small étale site of
  the scheme with that of the algebraic space it represents is an equivalence.

## Main definitions

* `AlgebraicGeometry.Space.idChartRestriction`: the restriction of a module on the small étale
  site of `yoneda.obj U` to the Zariski site of the scheme underlying `U`, in the shape of the
  right adjoint of Stacks 03DU, and
  `AlgebraicGeometry.Space.restrictToChartIsoIdChartRestriction` its comparison with the
  restriction to the identity chart.
* `AlgebraicGeometry.Space.idChartRestrictionUnitIso`: that restriction carries the structure
  sheaf to the structure sheaf.

## Main results

* `AlgebraicGeometry.Space.nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top`: **an
  invertible `𝒪`-module on the small étale site of `yoneda.obj U` is isomorphic to the structure
  sheaf**, when the scheme underlying `U` is the spectrum of a ring and has a point whose only
  open neighbourhood is the whole space.

## Implementation notes

The spectrum presentation of the scheme underlying `U` is taken as an *equality* of schemes
rather than as an isomorphism, because the consumer — the spectrum of a local ring at a
codimension-zero point of an algebraic space — has it as one, by `rfl`; and the point with no
proper open neighbourhood is taken as data rather than derived from local-ringness, so that
nothing here depends on how the scheme is presented as a spectrum.  Only
`AlgebraicGeometry.nonempty_iso_unit_of_isQuasicoherent_of_gammaTop` uses the equality.

`AlgebraicGeometry.Space.restrictToChart` and `AlgebraicGeometry.Space.restrictToChartScheme` are
two constructions of the same restriction which differ in how the Zariski opens of the chart are
regarded as étale charts; they are not equal by `rfl`.  Both are needed here, because the
freeness statement is proved for the first and the identity-chart presentation for the second, and
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionReadingsFunctor.lean`) is the comparison:
the two index functors are *equal*, so the comparison carries no quasi-coherence hypothesis and
no restriction on the module universe.

The algebraic space is written as `⟨yoneda.obj U, hY⟩` for an arbitrary proof `hY`, rather than
for `AlgebraicGeometry.isAlgebraicSpace_yoneda`, so that a consumer holding the algebraic space
in another spelling can apply the statement directly; being a `Prop`, the proof is irrelevant to
the types involved.

No `stacks` attribute is attached: the statement is the composition of clause (2) of Stacks 03DX
at `τ = étale`, of Stacks 03DU and of Stacks 05VP with the triviality of the Picard group of a
local ring, and each of those carries its own registration where it is proved.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The restriction to the scheme underlying a representable algebraic space -/

/-- The restriction of an `𝒪`-module on the small étale site of `yoneda.obj U` to the Zariski
site of the scheme underlying `U`: read the module on the small étale site of that scheme, then
restrict along the inclusion of its small Zariski site, the right adjoint of the
associated-module functor of Stacks 03DU. -/
def idChartRestriction (U : BigFppfOver B S hS) {hY : IsAlgebraicSpace B S hS (yoneda.obj U)}
    (M : Modules.{u, u} B S hS (yoneda.obj U) hY) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)

/-- **The restriction of a quasi-coherent module to the identity chart of `yoneda.obj U` is
`AlgebraicGeometry.Space.idChartRestriction`.** -/
def restrictToChartIsoIdChartRestriction (U : BigFppfOver B S hS)
    {hY : IsAlgebraicSpace B S hS (yoneda.obj U)} (M : Modules.{u, u} B S hS (yoneda.obj U) hY) :
    restrictToChart B S hS hY M (idEtaleChart B S hS U) ≅ idChartRestriction B S hS U M :=
  restrictToChartIsoRestrictToChartScheme B S hS hY M (idEtaleChart B S hS U) ≪≫
    restrictToChartSchemeIdEtaleChartIso B S hS U M

/-- **The restriction of the structure sheaf is the structure sheaf.** -/
def idChartRestrictionUnitIso (U : BigFppfOver B S hS)
    (hY : IsAlgebraicSpace B S hS (yoneda.obj U)) :
    idChartRestriction B S hS U (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj U) hY).O))) ≅
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf :=
  (restrictToChartSchemeIdEtaleChartIso B S hS U _).symm ≪≫
    restrictToChartSchemeUnitIso B S hS (yoneda.obj U) hY (idEtaleChart B S hS U)

/-! ### Triviality of an invertible module on the spectrum of a local ring -/

/-- **An invertible module on the small étale site of the spectrum of a local ring is isomorphic
to the structure sheaf.**  The ring is presented by an equality of the scheme underlying `U` with
a spectrum, and its locality by a point `t` of that scheme whose only open neighbourhood is the
whole space — the closed point of the spectrum of a local ring.

This is the sheaf-level triviality of the Picard group of a local ring, on the small étale site:
the sections of the restriction of the module to the identity chart are free of rank one, a
quasi-coherent module on a spectrum with free global sections is the structure sheaf, and
restriction to the small Zariski site reflects isomorphisms of quasi-coherent modules. -/
theorem nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top
    (U : BigFppfOver B S hS) {R : CommRingCat.{u}}
    (hU : (BigFppfOver.toScheme B S hS).obj U = Spec R)
    (t : chartScheme (idEtaleChart B S hS U))
    (ht : ∀ O : (chartScheme (idEtaleChart B S hS U)).Opens, t ∈ O → O = ⊤)
    (hY : IsAlgebraicSpace B S hS (yoneda.obj U)) (N : Modules.{u, u} B S hS (yoneda.obj U) hY)
    (hN : IsInvertibleModule ⟨yoneda.obj U, hY⟩ N) :
    Nonempty (N ≅ SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U) hY).O))) := by
  let G := representedSmallEtaleModuleEquivalence B S hS U
  let Nu : Modules.{u, u} B S hS (yoneda.obj U) hY :=
    SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U) hY).O))
  have hqcN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertibleModule ⟨yoneda.obj U, hY⟩ N hN
  have hqcNu : Nu.IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
  have hqcInv : ∀ (M : Modules.{u, u} B S hS (yoneda.obj U) hY), M.IsQuasicoherentOnSite →
      (G.inverse.obj M).IsQuasicoherentOnSite := fun M hM =>
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (G.counitIso.app M).symm hM)
  have hqcIC : ∀ (M : Modules.{u, u} B S hS (yoneda.obj U) hY), M.IsQuasicoherentOnSite →
      SheafOfModules.IsQuasicoherent (idChartRestriction B S hS U M) := fun M hM =>
    _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
      (G.inverse.obj M) (hqcInv M hM)
  obtain ⟨ybar, q, hq, hpt⟩ :=
    exists_geometricPoint_chartLift B S hS hY (idEtaleChart B S hS U) t
  obtain ⟨h⟩ := nonempty_linearEquiv_chartRestrictionTop_of_isInvertibleModule B S hS hY
    ⟨idEtaleChart B S hS U, q, hq⟩ (fun O hO => ht O (hpt ▸ hO)) N hN
  obtain ⟨eN⟩ := nonempty_iso_unit_of_isQuasicoherent_of_gammaTop hU
    (idChartRestriction B S hS U N) (hqcIC N hqcN)
    (Scheme.Modules.gammaTopTransport (restrictToChartIsoIdChartRestriction B S hS U N) h)
  obtain ⟨e⟩ := _root_.AlgebraicGeometry.SmallEtale.nonempty_iso_of_iso_restrictModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    (G.inverse.obj N) (G.inverse.obj Nu) (hqcInv N hqcN) (hqcInv Nu hqcNu)
    (eN ≪≫ (idChartRestrictionUnitIso B S hS U hY).symm)
  exact ⟨(G.counitIso.app N).symm ≪≫ G.functor.mapIso e ≪≫ G.counitIso.app Nu⟩

end AlgebraicGeometry.Space

end
