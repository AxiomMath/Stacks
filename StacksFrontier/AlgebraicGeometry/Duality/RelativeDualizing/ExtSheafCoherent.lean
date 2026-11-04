module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafStalkFormula
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
import StacksCore.Tactic.StacksAttribute

/-!
# The Ext sheaves against a dualizing complex are coherent

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` ([Stacks, Tag 0A87]) and
`F` a coherent `𝒪_X`-module. The first assertion of [Stacks, Tag 0ECM] is that every Ext sheaf
`𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, K)` is again a coherent `𝒪_X`-module. This file proves it, for
`𝓔ⁱ = Stacks.Duality.extSheafOf F K i`, an object of the standard model
`HasDerivedCategory.standard` of `D(𝒪_X)`.

On an affine open `U` the restriction `K|_U` lies in `D⁺_Coh(𝒪_U)`: its cohomology sheaves are
coherent ([Stacks, Tag 0A89]), and it is bounded below because its dualizing model over `Γ(X, U)`
is cohomologically bounded ([Stacks, Tag 0A7B]). The coherence clause of [Stacks, Tag 0D0C] and
the restriction isomorphism of [Stacks, Tag 08DL] then apply on `U`.

## Main results

* `Stacks.Duality.isBoundedBelow_restrict_of_hasDualizingModelOn`: the restriction of `K` to an
  affine open on which `K` has a dualizing model is cohomologically bounded below.
* `Stacks.Duality.derivedCategoryBPlus_restrict_of_isDualizingComplex`: the restriction of a
  dualizing complex to an affine open lies in `D⁺_Coh`.
* `Stacks.Duality.isCoherent_extSheafOf`: **the first assertion of [Stacks, Tag 0ECM]**, each
  Ext sheaf `𝓔xt^{-i}_{𝒪_X}(F, K)` of a coherent module against a dualizing complex on a locally
  Noetherian scheme is coherent (for the root predicate `SheafOfModules.IsCoherent` of
  [Stacks, Tag 01BW]).
* `Stacks.Duality.stacksIsCoherent_extSheafOf`: the same for the predicate
  `Stacks.SheafOfModules.IsCoherent`.

## References

* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Duality

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`,
--   `AlgebraicGeometry.isCoherent_homology_derivedSheafHom_of_isAffine`.
attribute [local instance 10000] HasDerivedCategory.standard
  AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **A dualizing complex is bounded below on an affine open.** If `K` has a dualizing model over
`Γ(X, U)` on the affine open `U`, then the restriction `K|_U` is cohomologically bounded below. -/
theorem isBoundedBelow_restrict_of_hasDualizingModelOn {K : DerivedCategory X.Modules}
    {U : X.Opens} {hU : IsAffineOpen U} (h : HasDualizingModelOn K U hU) :
    DerivedCategoryB.IsBoundedBelow
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) := by
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  let G : ModuleCat.{u} Γ(X, U) ⥤ U.toScheme.Modules :=
    tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom
  obtain ⟨a, ha⟩ :=
    Dualizing.isBoundedBelow_of_bounded ω (Dualizing.IsDualizingComplex.bounded hω)
  refine DerivedCategoryB.isBoundedBelow_of_iso e.symm ⟨a, fun n hn => ?_⟩
  exact (G.map_isZero (ha n hn)).of_iso
    ((Dualizing.mapDerivedCategoryHomologyIso G n).app ω)

/-- **A dualizing complex restricts to an object of `D⁺_Coh` on an affine open.** For a dualizing
complex `K` on `X` and an affine open `U`, the restriction `K|_U` is bounded below and has
coherent cohomology sheaves. -/
theorem derivedCategoryBPlus_restrict_of_isDualizingComplex {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) {U : X.Opens} (hU : IsAffineOpen U) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : U.toScheme.Modules => _root_.SheafOfModules.IsCoherent M)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) := by
  refine ⟨isBoundedBelow_restrict_of_hasDualizingModelOn (hK U hU), fun n => ?_⟩
  refine isCoherent_of_modulesIso ((DerivedCategoryB.mapDerivedCategoryHomologyIso
    (Scheme.Modules.restrictFunctor U.ι) n).app K).symm ?_
  exact isCoherent_restrict_of_isOpenImmersion U.ι _
    (isCoherent_homology_of_isDualizingComplex hK n)

/-- **The first assertion of [Stacks, Tag 0ECM].** Let `X` be a locally Noetherian scheme, `K` a
dualizing complex on `X` and `F` a coherent `𝒪_X`-module. Then every Ext sheaf
`𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, K)` is a coherent `𝒪_X`-module. -/
@[stacks 0ECM "the coherence assertion: for F coherent on a locally Noetherian scheme and K a \
dualizing complex, each Ext sheaf E^i = Ext^{-i}(F, K) is a coherent O_X-module",
  sga "6 I 3.7" "Clause b), special case"]
theorem isCoherent_extSheafOf (F : X.Modules) [hF : _root_.SheafOfModules.IsCoherent F]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) (i : ℤ) :
    _root_.SheafOfModules.IsCoherent (extSheafOf F K i) := by
  have hE : DerivedCategoryB.derivedCategoryBMinus
      (fun M : X.Modules => _root_.SheafOfModules.IsCoherent M)
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
    derivedCategoryBMinus_isCoherent_singleFunctor_obj F hF
  refine AlgebraicGeometry.Modules.isCoherent_of_restrict _
    (fun V : X.affineOpens => (V : X.Opens)) (iSup_affineOpens_eq_top X) fun V => ?_
  have _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := X.ringCatSheaf) (V : X.Opens)
  have _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := X.ringCatSheaf) (V : X.Opens)
  have _ : IsAffine (V : X.Opens).toScheme := V.2
  have hE' := derivedCategoryBMinus_isCoherent_restrictFunctor_mapDerivedCategory
    (V : X.Opens).ι ((DerivedCategory.singleFunctor X.Modules 0).obj F) hE
  have hK' := derivedCategoryBPlus_restrict_of_isDualizingComplex hK V.2
  have hres := isCoherent_homology_derivedSheafHom_of_isAffine (V : X.Opens).toScheme
    ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F))
    ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).mapDerivedCategory.obj K) hE' hK' (-i)
  refine isCoherent_of_modulesIso ((DerivedCategoryB.mapDerivedCategoryHomologyIso
    (Scheme.Modules.restrictFunctor (V : X.Opens).ι) (-i)).app _) ?_
  exact isCoherent_of_modulesIso
    ((DerivedCategory.homologyFunctor (V : X.Opens).toScheme.Modules (-i)).mapIso
      (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso (V : X.Opens)
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) K)).symm hres

/-- `Stacks.Duality.isCoherent_extSheafOf` for the second coherence predicate of this branch,
`Stacks.SheafOfModules.IsCoherent`. -/
theorem stacksIsCoherent_extSheafOf (F : X.Modules) [hF : _root_.SheafOfModules.IsCoherent F]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) (i : ℤ) :
    Stacks.SheafOfModules.IsCoherent (extSheafOf F K i) :=
  Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
    (isCoherent_extSheafOf F hK i)

end Stacks.Duality

end
