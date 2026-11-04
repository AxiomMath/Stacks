module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueing
import StacksCore.Tactic.StacksAttribute

/-!
# Chartwise glueing data for quasi-coherent modules on an algebraic space

Stacks 03LZ refines the chartwise description of Stacks 03LY to quasi-coherent modules: a
quasi-coherent `𝒪_X`-module on an algebraic space `X` is given by a *quasi-coherent*
`𝒪_U`-module `F_U` on the small étale site of every étale scheme chart `U` of `X`, transition
isomorphisms `c_f : f^*F_U ≅ F_V` along the chartwise pullbacks, and the cocycle condition
`c_g ∘ g^*c_f = c_{g ≫ f}`.

Every morphism of the small étale site of `X` represents an étale morphism of algebraic spaces,
so the quasi-coherence input of Stacks 03GA is needed only for étale morphisms, where it holds
unconditionally: along an étale morphism the pullback of modules of Stacks 03LU is restriction
of sections, by Stacks 03LW.

## Main definitions

* `AlgebraicGeometry.Space.isChartwiseQuasicoherent` is datum (1) of Stacks 03LZ: the module of
  a chartwise glueing datum is quasi-coherent on every chart.
* `AlgebraicGeometry.Space.QuasicoherentChartModuleGlueingData` is the category of chartwise
  glueing data satisfying it.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartModuleInverseImage`: the chartwise
  pullback of modules preserves quasi-coherence, so the transitions of a chartwise
  quasi-coherent glueing datum are isomorphisms of quasi-coherent modules.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_chartModuleRestriction`: an
  `𝒪_X`-module is quasi-coherent exactly when its restriction to every étale scheme chart is.
* `AlgebraicGeometry.Space.quasicoherentChartModuleGlueingFunctor`: **the canonical chartwise
  description of quasi-coherent modules**, the functor of Stacks 03LY cut down to the
  quasi-coherent objects on both sides, whose being an equivalence is Stacks 03LZ.

## Where the equivalence of Stacks 03LZ is proved

Not proved here is the equivalence between `AlgebraicGeometry.Space.QuasicoherentSheaves` and
`AlgebraicGeometry.Space.QuasicoherentChartModuleGlueingData`.  What is proved here is the
*functor* between them, `AlgebraicGeometry.Space.quasicoherentChartModuleGlueingFunctor`, the
canonical chartwise description of Stacks 03LY cut down to the quasi-coherent objects on both
sides.

The equivalence is
`AlgebraicGeometry.Space.quasicoherentChartModuleGlueingEquivalence` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartQuasicoherentGlueingEquivalence.lean`, and
the results here are what it is assembled from:
`isQuasicoherentOnSite_iff_forall_chartModuleRestriction` says the quasi-coherence conditions on
the two sides correspond — in the form
`AlgebraicGeometry.Space.inverseImage_isChartwiseQuasicoherent` — the instance below says the
chartwise condition is closed under isomorphism, and
`CategoryTheory.Equivalence.congrFullSubcategory` cuts the equivalence of Stacks 03LY
(`AlgebraicGeometry.Space.chartModuleGlueingEquivalence`) down to the quasi-coherent objects on
both sides, which is Stacks 03LZ.

## References

* [Stacks Project, Tag 03LZ](https://stacks.math.columbia.edu/tag/03LZ)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Quasi-coherence of the chartwise pullbacks -/

/-- Along an étale morphism of algebraic spaces, the pullback of a module is quasi-coherent
exactly when its étale restriction is, the two being isomorphic by Stacks 03LW. -/
private theorem isQuasicoherentOnSite_modulePullback_iff {Y Z : AlgebraicSpaces B S hS}
    {f : Y ⟶ Z} (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    ((modulePullback B S hS f).obj M).IsQuasicoherentOnSite ↔
      ((etaleModulePullback B S hS f hf).obj M).IsQuasicoherentOnSite :=
  have e := (modulePullbackIsoEtaleModulePullback B S hS f hf).app M
  ⟨.of_iso e, .of_iso e.symm⟩

/-- **Stacks 03LZ.** The chartwise pullback of modules preserves quasi-coherence: a morphism of
étale scheme charts of `X` represents an étale morphism of algebraic spaces, along which the
pullback of Stacks 03LU is restriction of sections. -/
@[stacks 03LZ "the chartwise pullback preserves quasi-coherence"]
theorem isQuasicoherentOnSite_chartModuleInverseImage {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2)
    (hF : F.IsQuasicoherentOnSite) :
    ((chartModuleInverseImage B S hS X f).obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_modulePullback_iff B S hS (isEtale_chartMap B S hS X f) F).2
    (isQuasicoherentOnSite_etaleModulePullback B S hS _ (isEtale_chartMap B S hS X f) F hF)

/-- The restriction of a quasi-coherent `𝒪_X`-module to an étale scheme chart of `X` is
quasi-coherent. -/
theorem isQuasicoherentOnSite_chartModuleRestriction (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1) :
    ((chartModuleRestriction B S hS X U).obj M).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_modulePullback_iff B S hS (isEtale_chartToSpace B S hS X U) M).2
    (isQuasicoherentOnSite_etaleModulePullback B S hS _ (isEtale_chartToSpace B S hS X U) M hM)

/-- **Stacks 03LZ.** An `𝒪_X`-module is quasi-coherent exactly when its restriction to every
étale scheme chart of `X` is quasi-coherent: the chartwise family of restrictions of a module
satisfies datum (1) of Stacks 03LZ precisely for the quasi-coherent modules. -/
@[stacks 03LZ "quasi-coherence of a module is quasi-coherence of its chartwise restrictions"]
theorem isQuasicoherentOnSite_iff_forall_chartModuleRestriction
    (M : Modules.{u, u} B S hS X.1 X.2) :
    M.IsQuasicoherentOnSite ↔
      ∀ U : SmallEtale B S hS X.1,
        ((chartModuleRestriction B S hS X U).obj M).IsQuasicoherentOnSite := by
  refine ⟨fun hM U ↦ isQuasicoherentOnSite_chartModuleRestriction B S hS X M hM U, fun h ↦ ?_⟩
  exact isQuasicoherentOnSite_of_forall_affine_chart B S hS M fun A _ ↦
    (isQuasicoherentOnSite_modulePullback_iff B S hS (isEtale_chartToSpace B S hS X A) M).1 (h A)

/-! ### Chartwise quasi-coherent glueing data -/

/-- **Datum (1) of Stacks 03LZ**: the module of a chartwise glueing datum is quasi-coherent on
the small étale site of every étale scheme chart of `X`. -/
@[stacks 03LZ "datum (1): the chartwise modules are quasi-coherent"]
def isChartwiseQuasicoherent : ObjectProperty (ChartModuleGlueingData B S hS X) :=
  fun D ↦ ∀ U, (D.sheaf U).IsQuasicoherentOnSite

/-- **The data of Stacks 03LZ**: a quasi-coherent `𝒪_U`-module on the small étale site of every
étale scheme chart `U` of `X`, transition isomorphisms along the chartwise pullbacks, and the
cocycle condition relating them. -/
@[stacks 03LZ "the data (1), (2) and the cocycle condition"]
noncomputable abbrev QuasicoherentChartModuleGlueingData :=
  (isChartwiseQuasicoherent B S hS X).FullSubcategory

/-- Chartwise quasi-coherence is invariant under isomorphism of glueing data, an isomorphism of
glueing data being in particular an isomorphism of the modules on each chart. -/
instance : (isChartwiseQuasicoherent B S hS X).IsClosedUnderIsomorphisms where
  of_iso i hD U := SheafOfModules.IsQuasicoherentOnSite.of_iso
    { hom := ChartModuleGlueingData.Hom.app i.hom U
      inv := ChartModuleGlueingData.Hom.app i.inv U
      hom_inv_id := by
        rw [← ChartModuleGlueingData.comp_app, i.hom_inv_id,
          ChartModuleGlueingData.id_app]
      inv_hom_id := by
        rw [← ChartModuleGlueingData.comp_app, i.inv_hom_id,
          ChartModuleGlueingData.id_app] }
    (hD U)

/-- **The canonical chartwise description of quasi-coherent `𝒪_X`-modules**: the functor of
Stacks 03LY cut down to the quasi-coherent objects on both sides, so that composing it with the
inclusion of the chartwise quasi-coherent data is
`AlgebraicGeometry.Space.chartModuleGlueingFunctor` on the nose.  It is well defined because
the restriction of a quasi-coherent module to a chart is quasi-coherent, which is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_chartModuleRestriction`.  That this functor is an
equivalence is Stacks 03LZ, proved as
`AlgebraicGeometry.Space.quasicoherentChartModuleGlueingFunctor_isEquivalence` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartQuasicoherentGlueingEquivalence.lean`. -/
@[stacks 03LZ "the canonical chartwise description of quasi-coherent modules"]
noncomputable def quasicoherentChartModuleGlueingFunctor :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentChartModuleGlueingData B S hS X :=
  ObjectProperty.lift (isChartwiseQuasicoherent B S hS X)
    (ObjectProperty.ι _ ⋙ chartModuleGlueingFunctor B S hS X)
    fun M U ↦ isQuasicoherentOnSite_chartModuleRestriction B S hS X M.obj M.property U


end AlgebraicGeometry.Space

end
