module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.NatTransRestrict
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionChartRigidity
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalModule
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionOverlapComparison

/-!
# The comparison of functors of [Stacks, Tag 0GPJ], chart by chart

Let `X` and `Y` be quasi-compact and quasi-separated schemes, let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be
an equivalence, let `g : Y ≅ X` be the glued isomorphism of schemes and let `M = e(𝒪_X)` be the
glued invertible `𝒪_Y`-module.  The remaining conjunct of [Stacks, Tag 0GPJ] is a natural
isomorphism `e(𝓕) ≅ g^*𝓕 ⊗ M`.  This file builds it **over one chart**: over an open `V ⊆ Y` to
which `g` restricts as `f : V ≅ U` and on which `M` is the chart's invertible sheaf `L`.

## The two sides of a chart

Over the chart both functors are computed to be one and the same twisted inverse image
`𝓕 ↦ (f ≫ U.ι)^*𝓕 ⊗ L`:

* the left-hand side by the chart data, `AlgebraicGeometry.chartPullbackIso`: `α` identifies `e`
  followed by restriction to `V` with restriction to `U` followed by the chart functor, `β`
  identifies the chart functor with `f^*(-) ⊗ L`, and
  `AlgebraicGeometry.pullbackTensorFunctorQuasicoherentRestrictIso` absorbs the restriction to
  `U` into the morphism;
* the right-hand side by `AlgebraicGeometry.pullbackTensorFunctorPullbackIso`, which moves the
  inverse image along `V.ι` inside, followed by the restriction equation `V.ι ≫ g = f ≫ U.ι`
  tying the chart to the glued `g` and the identification of `M|_V` with `L`.

Composing one with the inverse of the other is the comparison over the chart,
`AlgebraicGeometry.chartComparisonIso`.

## Main definitions

* `AlgebraicGeometry.chartPullbackIso` — the left-hand side of a chart.
* `AlgebraicGeometry.pullbackTensorFunctorCongr` — the reindexing of `𝓕 ↦ g^*𝓕 ⊗ N` along an
  equality of morphisms.
* `AlgebraicGeometry.moduleChartPullbackIso` — the right-hand side of a chart.
* `AlgebraicGeometry.chartComparisonPullbackIso` — the comparison over a chart, with the
  restriction to `V` written as the inverse image along `V.ι`.
* `AlgebraicGeometry.chartComparisonIso` — the same with the restriction written as
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is the shape
  `Stacks.AlgebraicGeometry.ModuleNatTransGlue.exists_natIso_of_restrictIso` glues.
* `AlgebraicGeometry.pullbackTensorFunctorObjUnitIso` — the glued functor read at the structure
  sheaf is `M`, canonically and with no chart entering.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_schemeIso_comp_eq` — an affine open of `Y` is an affine
  open of `X` through `g`, compatibly with the two inclusions.  This is what presents the
  restriction of `𝓕 ↦ g^*𝓕 ⊗ M` to an affine open as a reconstruction chart functor, the shape
  the rigidity statement `AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` asks for.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  The same list
is declared in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### The left-hand side of a chart -/

/-- **What one reconstruction chart computes, with the chart map left whole.**  Let
`E : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be a functor and let `V ⊆ Y`, `U ⊆ X` carry the data of one chart of
[Stacks, Tag 0GPJ]: a functor `F`, an isomorphism of schemes `f : V ≅ U`, a sheaf `L` of
`𝒪_V`-modules and the two isomorphisms `α` and `β`.  Then `E` followed by the inverse image
along `V.ι` is `(f ≫ U.ι)^*(-) ⊗ L`.

This is `AlgebraicGeometry.pullbackTensorFunctorIsoOfChartIso` at the identity of `V`, written
out so that the twist is `L` itself rather than its inverse image along the identity. -/
def chartPullbackIso {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {V : Y.Opens} {U : X.Opens}
    {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
    (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L) :
    (E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) ⋙
        Scheme.Modules.pullback V.ι ≅
      pullbackTensorFunctor (f.hom ≫ U.ι) L :=
  Functor.isoWhiskerLeft E (quasicoherentRestrictionCompIotaIsoPullback V).symm ≪≫
    Functor.isoWhiskerRight α
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf)) ≪≫
    Functor.isoWhiskerLeft (quasicoherentRestriction U.ι) β ≪≫
    pullbackTensorFunctorQuasicoherentRestrictIso U f.hom L

/-! ### The right-hand side of a chart -/

/-- **Equal morphisms give equal inverse-image-and-tensor functors.**  For `g = g'` and a sheaf
`N` of `𝒪_W`-modules, `g^*(-) ⊗ N ≅ g'^*(-) ⊗ N`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackCongr` whiskered into the functor.  Writing the
reindexing this way rather than rewriting with the equality in the middle of a definition is what
makes it computable: the component at `A` is the image under the tensor functor of
`Scheme.Modules.pullbackCongr`, which is the shape
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq` is stated in. -/
def pullbackTensorFunctorCongr {X W : Scheme.{u}} {g g' : W ⟶ X} (h : g = g')
    (N : SheafOfModules.{u} W.ringCatSheaf) :
    pullbackTensorFunctor g N ≅ pullbackTensorFunctor g' N :=
  Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
    (Functor.isoWhiskerRight (Scheme.Modules.pullbackCongr h)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ W.presheaf
          (forget₂ CommRingCat RingCat) W.ringCatSheaf.2⟩).obj N))

/-- **The glued functor `𝓕 ↦ g^*𝓕 ⊗ M`, restricted to a chart.**  For `g : Y ≅ X`, a sheaf `M` of
`𝒪_Y`-modules, an open `V ⊆ Y` to which `g` restricts as `f : V ≅ U` and an identification of
`M|_V` with a sheaf `L` of `𝒪_V`-modules, the inverse image along `V.ι` of `g^*(-) ⊗ M` is
`(f ≫ U.ι)^*(-) ⊗ L`.

The inverse image is moved inside by
`AlgebraicGeometry.pullbackTensorFunctorPullbackIso`; the restriction equation
`V.ι ≫ g = f ≫ U.ι` then reindexes the morphism by
`AlgebraicGeometry.pullbackTensorFunctorCongr` and
`AlgebraicGeometry.pullbackTensorFunctorIsoOfSheafIso` the twist. -/
def moduleChartPullbackIso {X Y : Scheme.{u}} (g : Y ≅ X) (M : SheafOfModules.{u} Y.ringCatSheaf)
    {V : Y.Opens} {U : X.Opens} (f : V.toScheme ≅ U.toScheme)
    (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (hg : V.ι ≫ g.hom = f.hom ≫ U.ι)
    (hres : Scheme.Modules.restrict M V.ι ≅ L) :
    pullbackTensorFunctor g.hom M ⋙ Scheme.Modules.pullback V.ι ≅
      pullbackTensorFunctor (f.hom ≫ U.ι) L :=
  pullbackTensorFunctorPullbackIso g.hom V.ι M ≪≫
    pullbackTensorFunctorCongr hg ((Scheme.Modules.pullback V.ι).obj M) ≪≫
    pullbackTensorFunctorIsoOfSheafIso (f.hom ≫ U.ι)
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ hres)

/-! ### The comparison over a chart -/

/-- **The comparison of functors of [Stacks, Tag 0GPJ] over one chart.**  Both sides compute to
`(f ≫ U.ι)^*(-) ⊗ L`, so the restriction to `V` of `e(-)` is the restriction to `V` of
`g^*(-) ⊗ M`. -/
def chartComparisonPullbackIso {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (g : Y ≅ X) (M : SheafOfModules.{u} Y.ringCatSheaf) {V : Y.Opens} {U : X.Opens}
    {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
    (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L)
    (hg : V.ι ≫ g.hom = f.hom ≫ U.ι)
    (hres : Scheme.Modules.restrict M V.ι ≅ L) :
    (E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) ⋙
        Scheme.Modules.pullback V.ι ≅
      pullbackTensorFunctor g.hom M ⋙ Scheme.Modules.pullback V.ι :=
  chartPullbackIso E f L α β ≪≫ (moduleChartPullbackIso g M f L hg hres).symm

/-- **The comparison over one chart, written with the restriction functor.**  This is
`AlgebraicGeometry.chartComparisonPullbackIso` with the inverse image along `V.ι` replaced by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is the shape the glueing
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.exists_natIso_of_restrictIso` consumes. -/
def chartComparisonIso {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (g : Y ≅ X) (M : SheafOfModules.{u} Y.ringCatSheaf) {V : Y.Opens} {U : X.Opens}
    {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
    (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L)
    (hg : V.ι ≫ g.hom = f.hom ≫ U.ι)
    (hres : Scheme.Modules.restrict M V.ι ≅ L) :
    (E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) ⋙
        Scheme.Modules.restrictFunctor V.ι ≅
      pullbackTensorFunctor g.hom M ⋙ Scheme.Modules.restrictFunctor V.ι :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback V.ι) ≪≫
    chartComparisonPullbackIso E g M f L α β hg hres ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm

/-! ### The two inputs the rigidity statement needs over an affine open of `Y` -/

/-- **An affine open of `Y` is an affine open of `X`, through an isomorphism of schemes.**  For
`g : Y ≅ X` and an affine open `W ⊆ Y` there is an affine open `U ⊆ X` and an isomorphism
`β : W ≅ U` with `β ≫ U.ι = W.ι ≫ g`.

The open is the image `g(W)`, affine by
`AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`, and the isomorphism is
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` for the two open immersions `W.ι ≫ g` and
`g(W).ι`, which have the same range.

This is what presents the restriction to `W` of the glued functor `𝓕 ↦ g^*𝓕 ⊗ M` as a
reconstruction chart functor `𝓕 ↦ (β ≫ U.ι)^*𝓕 ⊗ N`, the shape
`AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` asks for. -/
theorem exists_isAffineOpen_schemeIso_comp_eq {X Y : Scheme.{u}} (g : Y ≅ X) (W : Y.Opens)
    (hW : IsAffineOpen W) :
    ∃ (U : X.Opens) (β : W.toScheme ≅ U.toScheme),
      IsAffineOpen U ∧ β.hom ≫ U.ι = W.ι ≫ g.hom :=
  ⟨g.hom ''ᵁ W,
    IsOpenImmersion.isoOfRangeEq (W.ι ≫ g.hom) (g.hom ''ᵁ W).ι
      (by simp [Scheme.Hom.comp_base, Set.range_comp]),
    hW.image_of_isOpenImmersion g.hom, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

/-- **The glued functor `𝓕 ↦ g^*𝓕 ⊗ M`, read at the structure sheaf, is `M`.**  The inverse
image of the structure sheaf is the structure sheaf
(`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`), which the right unitor
`AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso` then absorbs.

No chart enters: this is the *canonical* identification against which the per-chart comparisons
of [Stacks, Tag 0GPJ] are normalised at `𝒪_X`. -/
def pullbackTensorFunctorObjUnitIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : SheafOfModules.{u} Y.ringCatSheaf) :
    (pullbackTensorFunctor g M).obj (quasicoherentUnit X) ≅ M :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
          (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj M).mapIso
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g) ≪≫
    tensorLeftFunctorObjUnitSchemeIso M

end AlgebraicGeometry

end
