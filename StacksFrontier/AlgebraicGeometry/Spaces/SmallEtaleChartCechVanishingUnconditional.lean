module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSchemeModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingFromEssSurj

/-!
# The Čech vanishing clause of Descent, Lemma 03FJ for an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `K` be
an `𝒪_F`-module which is quasi-coherent on the small étale site of `F`. This file proves the
`Ȟ^p = 0` clause of Descent, Lemma 03FJ for `K`, on a finite affine covering family of an affine
étale chart and in every positive degree, and the uniform form of Descent, Proposition 03DW,
with no hypothesis beyond those of the source.

`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_of_iso_associatedPresheaf` proves the
vanishing granted an isomorphism of abelian presheaves between the restriction of `K` to the
slice at an affine chart and the presheaf `Mᵃ` of Tag 03DU.
`AlgebraicGeometry.Space.exists_isQuasicoherent_iso_over_of_isAffine` produces a quasi-coherent
module `G` on the chart's scheme and an isomorphism `Gᵃ ≅ K|_W`, but on the small étale site of
the chart *space* rather than on the slice. That isomorphism is carried to the slice in three
steps.

* **Stacks 070S (2) on the small étale site of a scheme.**
  `AlgebraicGeometry.Space.representedAssociatedModule` is built from
  `AlgebraicGeometry.SmallEtale.associatedModule`, a sheafification of a pullback, whereas
  `Stacks.Sites.associatedPresheaf` is the pullback-sections presheaf. The two agree by
  `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf`, which assembles Stacks 070S (2)
  (`AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`) with
  `AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso` and
  `AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules`.
* **The two sites are carried by one category.** The small étale site of the chart space is the
  slice of the small étale site of `F` at the chart, by Tag 04M0
  (`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`), and it is the small étale
  site of the chart scheme, by `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`. Those
  two readings send an object of the site to the same scheme over the chart's scheme, on the
  nose: `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_comp_toOver`, and hence
  `AlgebraicGeometry.Space.associatedPresheaf_comp_eq` for the two associated presheaves.
* **Cancelling the whiskering.** The two sides are then isomorphic after restriction along the
  Tag 04M0 comparison, and restriction along an equivalence is an equivalence of presheaf
  categories, so the isomorphism descends along
  `CategoryTheory.Functor.FullyFaithful.preimageIso`.

The size cutoff is not an obstruction: `AlgebraicGeometry.associatedBigEtaleSite B` carries the
same category of schemes as `B`, its `cutoff` being `B.cutoff` by `rfl`.

This file does not discharge the hypothesis `hEss` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingFromEssSurj`, an isomorphism
of sheaves of modules over `AlgebraicGeometry.Space.SmallEtale.sliceRingSheaf` at an affine
chart: the Čech hypothesis asks only for the underlying isomorphism of abelian presheaves. Nor
does it discharge `AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage`, the vanishing of a
relative higher direct image along an affine morphism of algebraic spaces; that is
`AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isAffineHom`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso'`: the abelian presheaf underlying
  `Gᵃ` on the small étale site of a scheme is the pullback-sections presheaf of Tag 03DS, for a
  quasi-coherent `AlgebraicGeometry.Scheme.Modules`.
* `AlgebraicGeometry.Space.representedAssociatedModulePresheafIso`: the same on the small étale
  site of the chart space, restricted along the Tag 04M0 comparison.

## Main results

* `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_comp_toOver` and
  `AlgebraicGeometry.Space.associatedPresheaf_comp_eq`: the two readings of the slice at a chart
  as a category of schemes over the chart's scheme are the same functor.
* `AlgebraicGeometry.Space.exists_iso_associatedPresheaf_of_isAffine`: the coefficient
  identification the Čech hypothesis asks for.
* `AlgebraicGeometry.Space.isZero_cechCohomology_of_isQuasicoherentOnSite`: the `Ȟ^p = 0`
  clause of Descent, Lemma 03FJ for the small étale site of an algebraic space, in every
  positive degree.
* `AlgebraicGeometry.Space.isZero_cechCohomology_chartwise`: its degree-one case for a module
  cartesian on affine charts.
* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts`: the
  uniform form of Descent, Proposition 03DW, which is the hypothesis carried at the eleven binder
  sites that `StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech` lists.

## Implementation notes

`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf` is the same assembly as
`AlgebraicGeometry.BigFppfOver.smallEtaleAssociatedModuleIsoSheaf`, stated at a generic
`AlgebraicGeometry.BigEtaleSite` rather than at `AlgebraicGeometry.BigFppfSite.toBigEtaleSite`;
the site needed here is `AlgebraicGeometry.associatedBigEtaleSite`.

The coefficient module of the `Chart` section is typed
`SheafOfModules.{u} (AlgebraicGeometry.Space.structureRingSheaf B S hS X)` and not
`AlgebraicGeometry.Space.Modules`, to which it is definitionally equal. The two readings carry
different `CategoryTheory.Category` instance terms on the same category, and with the
ringed-site reading instance search does not find `Category (Over W)` at the restriction to the
slice.

`AlgebraicGeometry.Space.associatedPresheaf_comp_eq` is proved by
`CategoryTheory.Functor.hext` and not by `congrArg` from
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_comp_toOver`: the latter route
leaves the elaborator to reassociate `(Φ ⋙ Ψ).op ⋙ P` into `Φ.op ⋙ (Ψ.op ⋙ P)`, and that
defeq check exhausts the heartbeat limit. For the same reason the restriction of the
coefficient module to the slice is named through `AlgebraicGeometry.Space.over_val_presheaf`
rather than unfolded to a three-fold composite inside a larger `rfl`.

No `@[stacks]` attribute is claimed. Stacks 03DW is a statement about the cohomology of a
quasi-coherent sheaf on a scheme, already registered in this tree by
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` and
`AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`; what is proved here is the
surjectivity statement for algebraic spaces that this tree calls 03DW's uniform form. Descent,
Lemma 03FJ is likewise already registered in the three cases Lemma 03FI admits, and the small
étale site of an algebraic space is not among them.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)
    (G : T.Modules) [G.IsQuasicoherent]

/-- The abelian presheaf underlying `Gᵃ` on the small étale site of `T` is the presheaf of
pullback sections of Tag 03DS. -/
noncomputable def associatedModulePresheafIso' :
    ((associatedModule B T hT).obj G).val.presheaf ≅
      Stacks.Sites.associatedPresheaf T G (toOver B T hT) :=
  (sheafToPresheaf (topology B T hT) AddCommGrpCat.{u}).mapIso
    ((SheafOfModules.toSheaf (structureSheaf B T hT)).mapIso
      (associatedModuleIsoSectionsSheaf B T hT G))

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (W : SmallEtale B S hS X.1)

/-- **The two readings of the slice at a chart as a category of schemes agree.** -/
theorem representedSmallEtaleEquivalence_functor_comp_toOver :
    (representedSmallEtaleEquivalence B S hS ((SmallEtale.toOver B S hS X.1).obj W)).functor ⋙
        _root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B) (chartScheme W)
          ((SmallEtale.toOver B S hS X.1).obj W).left.property =
      (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor ⋙
        SmallEtale.sliceToOver B S hS X.1 W :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The two associated presheaves agree. -/
theorem associatedPresheaf_comp_eq (G : (chartScheme W).Modules) [G.IsQuasicoherent] :
    (representedSmallEtaleEquivalence B S hS ((SmallEtale.toOver B S hS X.1).obj W)).functor.op ⋙
        Stacks.Sites.associatedPresheaf (chartScheme W) G
          (_root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B) (chartScheme W)
            ((SmallEtale.toOver B S hS X.1).obj W).left.property) =
      (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor.op ⋙
        Stacks.Sites.associatedPresheaf (chartScheme W) G
          (SmallEtale.sliceToOver B S hS X.1 W) :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The abelian presheaf underlying the restriction of an `𝒪_X`-module to the slice at a
chart. -/
theorem over_val_presheaf (K : SheafOfModules.{u} (structureRingSheaf B S hS X)) :
    (K.over W).val.presheaf = (Over.forget W).op ⋙ K.val.presheaf :=
  rfl

/-- The abelian presheaf underlying the reading on the chart space of `Gᵃ`. -/
noncomputable def representedAssociatedModulePresheafIso (G : (chartScheme W).Modules)
    [G.IsQuasicoherent] :
    ((representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj W)
          (chartSpace B S hS X W).2).obj G).val.presheaf ≅
      (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor.op ⋙
        Stacks.Sites.associatedPresheaf (chartScheme W) G
          (SmallEtale.sliceToOver B S hS X.1 W) :=
  Functor.isoWhiskerLeft
      (representedSmallEtaleEquivalence B S hS
        ((SmallEtale.toOver B S hS X.1).obj W)).functor.op
      (_root_.AlgebraicGeometry.SmallEtale.associatedModulePresheafIso' (associatedBigEtaleSite B)
        (chartScheme W) ((SmallEtale.toOver B S hS X.1).obj W).left.property G) ≪≫
    eqToIso (associatedPresheaf_comp_eq B S hS X W G)

/-- **The coefficient identification the Čech hypothesis asks for.** For a module `K` which is
quasi-coherent on the site and an étale chart `W` with affine underlying scheme, the abelian
presheaf underlying the restriction of `K` to the slice at `W` is isomorphic to the
pullback-sections presheaf of a quasi-coherent module on the chart's scheme. -/
theorem exists_iso_associatedPresheaf_of_isAffine
    (K : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hK : K.IsQuasicoherentOnSite) (hW : IsAffine (chartScheme W)) :
    ∃ (G : (chartScheme W).Modules) (_ : G.IsQuasicoherent),
      Nonempty ((Over.forget W).op ⋙ K.val.presheaf ≅
        Stacks.Sites.associatedPresheaf (chartScheme W) G
          (SmallEtale.sliceToOver B S hS X.1 W)) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isQuasicoherent_iso_over_of_isAffine B S hS X K hK W hW
  refine ⟨G, hG, ⟨?_⟩⟩
  have e1 : ((representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj W)
        (chartSpace B S hS X W).2).obj G).val.presheaf ≅
      (chartSmallEtaleRestriction B S hS X K W).val.presheaf :=
    (sheafToPresheaf _ _).mapIso ((SheafOfModules.toSheaf _).mapIso e)
  have θ : (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor.op ⋙
        (K.over W).val.presheaf ≅
      (SmallEtale.chartLocalizationEquivalence B S hS X.1 W).functor.op ⋙
        Stacks.Sites.associatedPresheaf (chartScheme W) G
          (SmallEtale.sliceToOver B S hS X.1 W) :=
    e1.symm ≪≫ representedAssociatedModulePresheafIso B S hS X W G
  exact eqToIso (over_val_presheaf B S hS X W K).symm ≪≫
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 W).op.congrLeft
      (E := AddCommGrpCat.{u})).fullyFaithfulInverse.preimageIso θ

end Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The `Ȟ^p = 0` clause of Descent, Lemma 03FJ for the small étale site of an algebraic
space, in every positive degree.**

Let `K` be an `𝒪_F`-module which is quasi-coherent on the small étale site, let `W` be an étale
chart of `F` whose underlying scheme is affine, and let `E` be a finite affine covering family of
`W`. Then the Čech cohomology of the underlying abelian presheaf of `K` on `E` vanishes in every
positive degree. -/
theorem isZero_cechCohomology_of_isQuasicoherentOnSite (K : Modules.{u, u} B S hS F hF)
    (hK : K.IsQuasicoherentOnSite) (W : SmallEtale B S hS F)
    [IsAffine (chartScheme W)] (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W)
    [hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E
      ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
        ((SheafOfModules.toSheaf
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K)) p) := by
  obtain ⟨G, hG, ⟨e⟩⟩ :=
    exists_iso_associatedPresheaf_of_isAffine B S hS ⟨F, hF⟩ W K hK ‹IsAffine (chartScheme W)›
  exact SmallEtale.isZero_cechCohomology_of_iso_associatedPresheaf B S hS F W E hfin haff hcov
    G _ e p hp

/-- **The Čech hypothesis of
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_univ`.** For a module
cartesian on affine charts, the Čech cohomology in degree one of its underlying abelian presheaf
on a finite affine covering family of an affine étale chart vanishes. -/
theorem isZero_cechCohomology_chartwise :
    ∀ K : Modules.{u, u} B S hS F hF, IsCartesianOnAffineCharts K →
      ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        ∀ E : PreZeroHypercover.{u} W, Finite E.I₀ →
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) →
          E.sieve₀ ∈ SmallEtale.topology B S hS F W →
          letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
          IsZero (Stacks.CechSite.cechCohomology E
            ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
              ((SheafOfModules.toSheaf
                (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K)) 1) := by
  intro K hK W hW E hfin haff hcov
  let : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : IsAffine (chartScheme W) := hW
  have hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a))) := fun _ _ ↦ inferInstance
  exact isZero_cechCohomology_of_isQuasicoherentOnSite K
    (isQuasicoherentOnSite_of_isCartesianOnAffineCharts K hK) W E hfin haff hcov 1 Nat.one_pos

/-- **The uniform form of Descent, Proposition 03DW.**

An epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is surjective on the
sections over every affine étale chart. The conclusion is the hypothesis carried at the eleven
binder sites listed in the module docstring of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech`. -/
theorem surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts :
    ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)) :=
  surjective_val_app_of_epi_of_kernel_isCartesian_univ isZero_cechCohomology_chartwise

end AlgebraicGeometry.Space

end
