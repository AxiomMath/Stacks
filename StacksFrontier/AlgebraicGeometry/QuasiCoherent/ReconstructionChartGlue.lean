module

public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.NatTransRestrictLE
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentStage
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalNatIso

/-!
# Glueing the per-chart comparisons of [Stacks, Tag 0GPJ]

`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalNatIso.lean` builds the
comparison `e(𝓕)|_{V i} ≅ (g^*𝓕 ⊗ M)|_{V i}` over one chart.  This file glues the family into a
single natural isomorphism `e(𝓕) ≅ g^*𝓕 ⊗ M`, given that each chart's comparison is *normalised*
at the structure sheaf — that is, that it agrees there with the canonical, chart-free
identification `AlgebraicGeometry.pullbackTensorFunctorObjUnitIso`.

## The two steps

1. *Over an affine open `W ⊆ Y` contained in two charts the two comparisons are equal.*  The
   restriction to `W` of the glued functor `𝓕 ↦ g^*𝓕 ⊗ M` is a reconstruction chart functor,
   `AlgebraicGeometry.moduleAffineChartIso`: the affine open `W` of `Y` is an affine open `U` of
   `X` through `g` (`AlgebraicGeometry.exists_isAffineOpen_schemeIso_comp_eq`), and the twist is
   `M|_W`, invertible because `M` is.  So
   `AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` applies, and its hypothesis — agreement at
   `𝒪_X` — holds because each comparison restricted to `W` is, at `𝒪_X`, the restriction to `W`
   of `pullbackTensorFunctorObjUnitIso`, in which no chart occurs.
2. *The family glues.*  `Stacks.AlgebraicGeometry.ModuleNatTransGlue.exists_natIso_of_restrictIso`
   consumes the agreement on *sections* over the affine opens, and
   `Stacks.AlgebraicGeometry.ModuleNatTransGlue.ofRestrict_app_eq_of_restrictIsoOfLE` converts
   step 1 into that form.

## Main definitions

* `AlgebraicGeometry.moduleAffineChartIso` — the restriction of `𝓕 ↦ g^*𝓕 ⊗ M` to an affine open
  of `Y`, presented as a reconstruction chart functor.

## Main results

* `AlgebraicGeometry.restrictIsoOfLE_eq_of_app_unit` — step 1.
* `AlgebraicGeometry.exists_natIso_of_chartComparison` — step 2: **a family of per-chart
  comparisons, each normalised at the structure sheaf, glues to the natural isomorphism
  `e(𝓕) ≅ g^*𝓕 ⊗ M` that is the remaining conjunct of [Stacks, Tag 0GPJ].**

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

open Stacks.AlgebraicGeometry.ModuleNatTransGlue (restrictIsoOfLE)

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  The same list
is declared in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### An affine open of `Y` as a reconstruction chart -/

/-- **The restriction of the glued functor to an affine open of `Y`, as a reconstruction chart
functor.**  For `g : Y ≅ X`, an open `W ⊆ Y`, an open `U ⊆ X` and an isomorphism `b : W ≅ U`
with `b ≫ U.ι = W.ι ≫ g`, the restriction to `W` of `𝓕 ↦ g^*𝓕 ⊗ M` is `𝓕 ↦ (b ≫ U.ι)^*𝓕 ⊗ M|_W`.

This is `AlgebraicGeometry.moduleChartPullbackIso` with the twist taken to be `M|_W` itself and
the identification the identity; it is the shape
`AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` asks of the common target. -/
def moduleAffineChartIso {X Y : Scheme.{u}} (g : Y ≅ X) (M : Y.Modules) {W : Y.Opens}
    {U : X.Opens} (b : W.toScheme ≅ U.toScheme) (hb : b.hom ≫ U.ι = W.ι ≫ g.hom) :
    pullbackTensorFunctor g.hom M ⋙ Scheme.Modules.restrictFunctor W.ι ≅
      pullbackTensorFunctor (b.hom ≫ U.ι) (Scheme.Modules.restrict M W.ι) :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback W.ι) ≪≫
    moduleChartPullbackIso g M b (Scheme.Modules.restrict M W.ι) hb.symm (Iso.refl _)

/-! ### The two normalised comparisons agree over an affine open -/

/-- **Two per-chart comparisons normalised at the structure sheaf agree over an affine open
contained in both charts.**  Over an affine open `W ⊆ Y` the restriction of the glued functor is
a reconstruction chart functor (`AlgebraicGeometry.moduleAffineChartIso`), so the rigidity
statement `AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` applies; the two restricted
comparisons agree at `𝒪_X` because each is the restriction of the canonical, chart-free
`AlgebraicGeometry.pullbackTensorFunctorObjUnitIso`.

The glued module is `E(𝒪_X)`, not an arbitrary invertible module: that is what makes the
normalisation hypotheses satisfiable, as recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionChartRigidity.lean`. -/
theorem restrictIsoOfLE_eq_of_app_unit {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (g : Y ≅ X)
    {E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory}
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (E.obj (quasicoherentUnit X)).obj)
    {V₁ V₂ W : Y.Opens} (hW : IsAffineOpen W) (h₁ : W ≤ V₁) (h₂ : W ≤ V₂)
    (Θ₁ : (E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) ⋙
        Scheme.Modules.restrictFunctor V₁.ι ≅
      pullbackTensorFunctor g.hom (E.obj (quasicoherentUnit X)).obj ⋙
        Scheme.Modules.restrictFunctor V₁.ι)
    (Θ₂ : (E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) ⋙
        Scheme.Modules.restrictFunctor V₂.ι ≅
      pullbackTensorFunctor g.hom (E.obj (quasicoherentUnit X)).obj ⋙
        Scheme.Modules.restrictFunctor V₂.ι)
    (hn₁ : Θ₁.hom.app (quasicoherentUnit X) =
      (Scheme.Modules.restrictFunctor V₁.ι).map
        (pullbackTensorFunctorObjUnitIso g.hom (E.obj (quasicoherentUnit X)).obj).inv)
    (hn₂ : Θ₂.hom.app (quasicoherentUnit X) =
      (Scheme.Modules.restrictFunctor V₂.ι).map
        (pullbackTensorFunctorObjUnitIso g.hom (E.obj (quasicoherentUnit X)).obj).inv) :
    restrictIsoOfLE h₁ Θ₁ = restrictIsoOfLE h₂ Θ₂ := by
  obtain ⟨U, b, hU, hb⟩ := exists_isAffineOpen_schemeIso_comp_eq g W hW
  refine natIso_eq_of_app_unit_eq_of_iso U hU b _
    (Stacks.Modules.isInvertible_restrict_of_isInvertible _ W hM) (quasicoherentUnit X)
    ⟨Iso.refl _⟩ (moduleAffineChartIso g _ b hb) _ _ ?_
  rw [Stacks.AlgebraicGeometry.ModuleNatTransGlue.restrictIsoOfLE_hom_app,
    Stacks.AlgebraicGeometry.ModuleNatTransGlue.restrictIsoOfLE_hom_app, hn₁, hn₂,
    Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_restrictFunctor_map,
    Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_restrictFunctor_map]

/-! ### The glueing -/

/-- **The per-chart comparisons of [Stacks, Tag 0GPJ] glue**, once each is normalised at the
structure sheaf.  Let `E : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be a functor with `E(𝒪_X)` invertible, let
`g : Y ≅ X`, let `V i` be an open cover of `Y`, and suppose given for each `i` an isomorphism
`Θ i : E(-)|_{V i} ≅ (g^*(-) ⊗ E(𝒪_X))|_{V i}` whose component at `𝒪_X` is the restriction of the
canonical `AlgebraicGeometry.pullbackTensorFunctorObjUnitIso`.  Then
`E(-) ≅ g^*(-) ⊗ E(𝒪_X)`.

The agreement over the affine opens is `AlgebraicGeometry.restrictIsoOfLE_eq_of_app_unit` read
through `Stacks.AlgebraicGeometry.ModuleNatTransGlue.ofRestrict_app_eq_of_restrictIsoOfLE`, and
the glueing is
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.exists_natIso_of_restrictIso`. -/
theorem exists_natIso_of_chartComparison {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (g : Y ≅ X)
    {E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory}
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (E.obj (quasicoherentUnit X)).obj)
    {κ : Type u} {V : κ → Y.Opens} (hVcover : IsOpenCover V)
    (Θ : ∀ i, (E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) ⋙
        Scheme.Modules.restrictFunctor (V i).ι ≅
      pullbackTensorFunctor g.hom (E.obj (quasicoherentUnit X)).obj ⋙
        Scheme.Modules.restrictFunctor (V i).ι)
    (hn : ∀ i, (Θ i).hom.app (quasicoherentUnit X) =
      (Scheme.Modules.restrictFunctor (V i).ι).map
        (pullbackTensorFunctorObjUnitIso g.hom (E.obj (quasicoherentUnit X)).obj).inv) :
    Nonempty (E ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ≅
      pullbackTensorFunctor g.hom (E.obj (quasicoherentUnit X)).obj) := by
  refine Stacks.AlgebraicGeometry.ModuleNatTransGlue.exists_natIso_of_restrictIso hVcover Θ ?_
  intro A i j W h₁ h₂
  refine Stacks.AlgebraicGeometry.ModuleNatTransGlue.ofRestrict_app_eq_of_restrictIsoOfLE
    h₁ h₂ (Θ i) (Θ j) A ?_
  rw [restrictIsoOfLE_eq_of_app_unit g hM W.2 h₁ h₂ (Θ i) (Θ j) (hn i) (hn j)]

end AlgebraicGeometry

end
