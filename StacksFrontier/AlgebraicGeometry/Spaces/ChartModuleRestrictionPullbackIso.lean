module

public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparisonSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent

/-!
# Reducing invertibility of the chart-restriction comparison to affine opens

For a morphism `g : V ⟶ U` of étale charts of an algebraic space `F`,
`StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison` builds the inverse-image
comparison `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`, a morphism
`(chartSchemeMap g)^* M|_U ⟶ M|_V` of sheaves of modules on `chartScheme V`, and
`StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparisonSections` computes it on
sections — but only on the sections pulled back from a *Zariski sheafification unit*, since the
chart restriction is defined as a sheafification and nothing there says the unit is invertible.

This file supplies two things. First, the unit **is** invertible, because the presheaf it is the
unit of is already a sheaf: its underlying presheaf of abelian groups is the restriction of the
sections of `M` along the index functor `AlgebraicGeometry.Space.openChartFunctor`, which is
continuous. So the section computations apply to every section. Second, invertibility of the
comparison reduces to invertibility of its components over the affine Zariski opens of the
smaller chart scheme lying inside the preimage of an affine Zariski open of the larger — which
form a basis.

Together these are the *affine-local criterion* recorded as the first missing input in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafChartCartesian.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean`. What is
still *not* here is the invertibility statement itself; see the implementation notes.

## Main results

* `AlgebraicGeometry.Space.isSheaf_pushforward_uliftForPresentation`: **the presheaf whose
  Zariski sheafification is the chart restriction is already a sheaf.**
* `AlgebraicGeometry.Space.isIso_toSheafify_pushforward_uliftForPresentation` and
  `AlgebraicGeometry.Space.surjective_toSheafify_app_pushforward_uliftForPresentation`: **the
  Zariski sheafification unit of the chart restriction is therefore invertible**, and in
  particular surjective on the sections over a Zariski open.
* `AlgebraicGeometry.Space.exists_restrictToChartSchemePullbackComparison_app_pullbackSection`:
  **the inverse-image comparison on a section pulled back from an arbitrary section.** Every
  section of the chart restriction over `O` is the unit of a section `m` of `M` over the étale
  chart `openChart U O`, and the comparison carries the pull-back of that section to the unit of
  the restriction of `m` along `openChartHomOfLE V hle ≫ openChartRestrict g O`. This lifts
  `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_app_pullbackSection_toSheafify`
  off the image of the unit.
* `AlgebraicGeometry.Space.isIso_restrictToChartSchemePullbackComparison_of_forall_isAffineOpen`:
  **the affine-local criterion.** The comparison is invertible as soon as each of its components
  over such a pair of affine opens is.

## Implementation notes

**Why the sheaf condition is cheap.** The underlying presheaf of abelian groups of
`PresheafOfModules.pushforward (chartSchemeRestrictionRingHom U)` applied to the universe-lifted
sections of `M` is, on the nose, `(openChartFunctor U).op ⋙ M`'s sections — the change of scalars
does not touch the abelian group. So the sheaf condition is
`CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf` at
`AlgebraicGeometry.Space.isContinuous_openChartFunctor`, and
`CategoryTheory.isIso_toSheafify` turns it into invertibility of the unit. The topology of the
small étale site has to be spelled `AlgebraicGeometry.Space.SmallEtale.topology` and not
`(smallEtaleRingedSite …).J` for the continuity instance to be the one in scope, the latter being
a structure projection that instance search does not unfold.

**Affineness of the étale chart is free.** By
`AlgebraicGeometry.Space.openChartFunctor_comp_toScheme` the scheme underlying the étale chart
`openChart U O` *is* the open subscheme `O`, so `AlgebraicGeometry.IsAffineOpen` of `O` is
already `AlgebraicGeometry.IsAffine` of that chart, with no transport. That is what lets the
basis of this file meet Descent, Proposition 03DX(2) in the form
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite`, which asks for
affineness of the two charts.

**What is still missing, and what it would take.** Nothing here says the comparison *is*
invertible for quasi-coherent `M`. With the criterion of this file the remaining step is, over a
pair of affine opens, to identify the comparison with a base change and transport it to the chart
rings. Three of the four links of that step are available:

* `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` identifies the sections of the inverse
  image with `Γ(chartScheme V, O') ⊗_{Γ(chartScheme U, O)} Γ(M|_U, O)`, its `IsQuasicoherent`
  hypothesis discharged by
  `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`, and
  `AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso` turns it, with the
  normalisation `affinePullbackSectionsBaseChangeIso_one_tmul`, into a
  `Module.IsBaseChange` in the `LinearMap.liftBaseChange` spelling.
* `Stacks.BaseChange.bijective_liftBaseChange_iff` transports bijectivity of that base change
  across the renaming of the two base rings, which is what carries
  `AlgebraicGeometry.Space.sectionsBaseChange` — stated over the chart rings `𝒪_F(openChart U O)`
  and `𝒪_F(openChart V O')` — over to `Γ(chartScheme U, O)` and `Γ(chartScheme V, O')`. The two
  pairs are isomorphic by the components of
  `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`, which are invertible because that map
  is `AlgebraicGeometry.Scheme.restrictFunctorΓ.inv` whiskered, compatibly with the two ring maps
  by `AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict`.
* `AlgebraicGeometry.IsBaseChange.of_linearEquiv` carries a base change along linear
  equivalences on the two section groups.

The link that is **not** available is the equivalence those last two want: a
`Γ(chartScheme U, O)`-linear identification of `Γ(M|_U, O)` with `Γ(M, openChart U O)` that is
compatible with the computations of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean`. The
identification exists —
`AlgebraicGeometry.sectionsLinearEquivOfIso` applied to
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` is exactly it, and it elaborates —
but it is built from the *counit* of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`, whereas the section computations are
stated at the *unit* `CategoryTheory.toSheafify` of the underlying presheaf of abelian groups.
Identifying the two crosses the boundary between the `CommRingCat`-valued sections
`Γ(chartScheme U, O)`, over which `sectionsLinearEquivOfIso` is linear, and the `RingCat`-valued
sections `(chartScheme U).ringCatSheaf.obj.obj (op O)`, over which the sheafification of
presheaves of modules is linear; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Topologies/AssociatedModuleAffineBaseChange.lean` record that the
one defeq check which crosses that boundary exhausts the default recursion depth at these
concrete sheaf-section types. Supplying the missing link therefore means computing
`sectionsLinearEquivOfIso (restrictToChartSchemeIsoPushforward …) O` in terms of `toSheafify`,
on one side of that boundary only.

The identifications the tree already has are all on the `RingCat` side:
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` is linear over
`(chartScheme A).ringCatSheaf.obj.obj (op W)`, and so are
`PresheafOfModules.unitAppEquiv` and
`Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff`, which are the general forms of the
unit-is-an-isomorphism statement proved here. None of them is linear over
`Γ(chartScheme U, O)`, which is what the affine base change is stated over. Closing the gap is
therefore not a matter of finding the identification — several exist — but of choosing which side
of the `CommRingCat`/`RingCat` boundary the whole affine step is run on, and stating the affine
base change there.

**No `stacks` attribute is claimed.** Everything here is an input to the invertibility of the
chart-restriction comparison, which is Descent, Proposition 03DX(2) together with the
identification of the chart restriction with an inverse image, Stacks 03LY; no declaration here
asserts either. In particular none of this is Stacks 03M0, which is the characterization of
quasi-coherence of a module on an algebraic space by its restrictions to étale charts and is
registered elsewhere.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The presheaf the chart restriction sheafifies is already a sheaf -/

/-- **The presheaf whose Zariski sheafification is the chart restriction is already a sheaf.**
Its underlying presheaf of abelian groups is the restriction of the sections of `M` along the
index functor `AlgebraicGeometry.Space.openChartFunctor`, which is continuous
(`AlgebraicGeometry.Space.isContinuous_openChartFunctor`), and the restriction of a sheaf along a
continuous functor is a sheaf. -/
theorem isSheaf_pushforward_uliftForPresentation
    (M : Modules.{u, u} B S hS F hF) (U : SmallEtale B S hS F) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(chartScheme U))
      ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
          (SheafOfModules.uliftForPresentation M).val).presheaf :=
  have := isContinuous_openChartFunctor B S hS ⟨F, hF⟩ U
  (openChartFunctor B S hS F U).op_comp_isSheaf_of_isSheaf
    (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS F) _
    (SheafOfModules.uliftForPresentation M).isSheaf

/-- **The Zariski sheafification unit of the chart restriction is invertible.**  The presheaf it
is the unit of is already a sheaf,
`AlgebraicGeometry.Space.isSheaf_pushforward_uliftForPresentation`.

This is what makes the section computations of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean`, which hold
on the image of the unit, hold on every section of the chart restriction. -/
theorem isIso_toSheafify_pushforward_uliftForPresentation
    (M : Modules.{u, u} B S hS F hF) (U : SmallEtale B S hS F)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}] :
    IsIso (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
      ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
          (SheafOfModules.uliftForPresentation M).val).presheaf) :=
  CategoryTheory.isIso_toSheafify _
    (isSheaf_pushforward_uliftForPresentation B S hS F hF M U)

/-- **Every section of the chart restriction over a Zariski open is a sheafification unit.**
The unit is invertible by
`AlgebraicGeometry.Space.isIso_toSheafify_pushforward_uliftForPresentation`, so its component
over an open is a bijection; this is the surjectivity. -/
theorem surjective_toSheafify_app_pushforward_uliftForPresentation
    (M : Modules.{u, u} B S hS F hF) (U : SmallEtale B S hS F)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    (O : (chartScheme U).Opens) :
    Function.Surjective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
        ((PresheafOfModules.pushforward
          (chartSchemeRestrictionRingHom B S hS F U)).obj
            (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O)) :=
  have := isIso_toSheafify_pushforward_uliftForPresentation B S hS F hF M U
  (ConcreteCategory.bijective_of_isIso
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
      ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
          (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O))).2

/-- **The inverse-image chart comparison on a section pulled back from an arbitrary section.**
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_app_pullbackSection_toSheafify`
computes the comparison on the sections pulled back from a Zariski sheafification unit; because
that unit is surjective on sections
(`AlgebraicGeometry.Space.surjective_toSheafify_app_pushforward_uliftForPresentation`) the
computation applies to *every* section `a` of the chart restriction over `O`: some section `m` of
`M` over the étale chart `openChart U O` has `a` as its unit, and the comparison carries the
pull-back of `a` to the unit of the restriction of `m` along the morphism of étale charts
`openChartHomOfLE V hle ≫ openChartRestrict g O`.

This is the form the affine-local criterion consumes: it needs the comparison on all of
`Γ(M|_U, O)`, not only on a sheafification unit. -/
theorem exists_restrictToChartSchemePullbackComparison_app_pullbackSection
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (O : (chartScheme U).Opens) (O' : (chartScheme V).Opens)
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (a : (restrictToChartScheme B S hS F hF M U).val.obj (op O)) :
    ∃ m : ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
          (SheafOfModules.uliftForPresentation M).val).obj (op O),
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
          ((PresheafOfModules.pushforward
            (chartSchemeRestrictionRingHom B S hS F U)).obj
              (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O) m = a ∧
      (restrictToChartSchemePullbackComparison B S hS F hF M g).val.app (op O')
          (Scheme.Modules.pullbackSection (chartSchemeMap g)
            (restrictToChartScheme B S hS F hF M U) O O' hle a) =
        (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme V))
            ((PresheafOfModules.pushforward
              (chartSchemeRestrictionRingHom B S hS F V)).obj
                (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O')
          ((SheafOfModules.uliftForPresentation M).val.map
            (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O).op m) := by
  obtain ⟨m, hm⟩ :=
    surjective_toSheafify_app_pushforward_uliftForPresentation B S hS F hF M U O a
  refine ⟨m, hm, ?_⟩
  exact (congrArg (fun z => (restrictToChartSchemePullbackComparison B S hS F hF M g).val.app
        (op O') (Scheme.Modules.pullbackSection (chartSchemeMap g)
          (restrictToChartScheme B S hS F hF M U) O O' hle z)) hm.symm).trans
    (restrictToChartSchemePullbackComparison_app_pullbackSection_toSheafify
      B S hS F hF M g O O' hle m)

/-! ### The affine-local criterion -/

/-- **The affine-local criterion for invertibility of the inverse-image chart comparison.**  By
`Stacks.LeibnizDerivation.isBasis_affineOpens_le_preimage` the affine Zariski opens of the smaller
chart scheme lying inside the preimage of an affine Zariski open of the larger one form a basis,
and by `Stacks.LeibnizDerivation.isIso_of_isIso_app_basis` invertibility of a morphism of sheaves
of modules on a scheme follows from invertibility of its components on a basis. -/
theorem isIso_restrictToChartSchemePullbackComparison_of_forall_isAffineOpen
    (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (h : ∀ (O : (chartScheme U).Opens) (O' : (chartScheme V).Opens),
      IsAffineOpen O → IsAffineOpen O' → O' ≤ chartSchemeMap g ⁻¹ᵁ O →
      IsIso ((restrictToChartSchemePullbackComparison B S hS F hF M g).val.app (op O'))) :
    IsIso (restrictToChartSchemePullbackComparison B S hS F hF M g) :=
  Stacks.LeibnizDerivation.isIso_of_isIso_app_basis
    (restrictToChartSchemePullbackComparison B S hS F hF M g)
    (Stacks.LeibnizDerivation.isBasis_affineOpens_le_preimage (chartSchemeMap g))
    (fun p => h p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

end AlgebraicGeometry.Space

end
