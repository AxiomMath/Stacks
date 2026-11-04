module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Descent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal

/-!
# A sheaf of modules glued from quasi-coherent charts is quasi-coherent

Stacks 00AM glues a family of sheaves of modules on the charts `f i : Y i ⟶ S` of a cover of a
scheme by open immersions into a single sheaf of modules on `S`, and records the comparison with
the charts as the isomorphisms `Stacks.SheafOfModules.ModulesGlueData.chartIso`. Quasi-coherence of
the result is not part of that statement, and this file supplies it: a glued sheaf of modules is
quasi-coherent as soon as each chart's sheaf is, provided the charts cover.

Quasi-coherence is local on the base in the form `Stacks.Modules.isQuasicoherent_of_restrict`,
which asks for the restrictions to the members of a cover by *opens* of `S`. A chart is an open
immersion from an arbitrary scheme rather than the inclusion of an open subscheme, so the first
statement here moves the locality criterion to a cover by open immersions, by factoring a chart
through the inclusion of its open range.

## Main results

* `Stacks.SheafOfModules.isQuasicoherent_of_restrict_openImmersions`: **quasi-coherence is local
  along a cover by open immersions.**
* `Stacks.SheafOfModules.ModulesGlueData.isQuasicoherent_glued`: **a sheaf of modules glued from
  quasi-coherent charts is quasi-coherent.**
* `Stacks.SheafOfModules.ModulesDirectedGlueData.isQuasicoherent_glued`: the same for a locally
  directed glueing datum.

## Implementation notes

The factorization of a chart is `AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp`, and the
induced comparison of the two restrictions is assembled from
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`; the restriction along the isomorphism is
quasi-coherent by `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`, so no
presentation is transported by hand.

The covering hypothesis cannot be dropped: a glueing datum records nothing about the sections of
the glued sheaf over an open meeting no chart.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe w u

namespace Stacks.SheafOfModules

/-- **Quasi-coherence is local along a cover by open immersions.** If the open ranges of a family
of open immersions `f i : Y i ⟶ S` cover `S` and the restriction of a sheaf of modules `M` on `S`
along each `f i` is quasi-coherent, then `M` is quasi-coherent. -/
public theorem isQuasicoherent_of_restrict_openImmersions {S : Scheme.{u}} {ι : Type w}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)] (M : S.Modules)
    (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, (M.restrict (f i)).IsQuasicoherent) : M.IsQuasicoherent := by
  refine Stacks.Modules.isQuasicoherent_of_restrict M (fun i => (f i).opensRange) hf fun i => ?_
  have := h i
  have e : (M.restrict (f i)).restrict (f i).isoOpensRange.inv ≅
      M.restrict ((f i).opensRange).ι :=
    ((Scheme.Modules.restrictFunctorComp (f i).isoOpensRange.inv (f i)).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (f i))).app M
  exact (_root_.SheafOfModules.isQuasicoherent
    ((f i).opensRange : Scheme.{u}).ringCatSheaf).prop_of_iso e inferInstance

section Scheme

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S}
  [∀ i, IsOpenImmersion (f i)]

/-- **A sheaf of modules glued from quasi-coherent charts is quasi-coherent.** If the charts of a
glueing datum cover the scheme and the sheaf of modules on each chart is quasi-coherent, then so is
the sheaf of modules glued from the datum. -/
public theorem ModulesGlueData.isQuasicoherent_glued (D : ModulesGlueData S f)
    (hf : ⨆ i, (f i).opensRange = ⊤) (h : ∀ i, (D.mod i).IsQuasicoherent) :
    D.glued.IsQuasicoherent :=
  isQuasicoherent_of_restrict_openImmersions f D.glued hf fun i =>
    (_root_.SheafOfModules.isQuasicoherent (Y i).ringCatSheaf).prop_of_iso
      (D.chartIso i).symm (h i)

/-- **A sheaf of modules glued from quasi-coherent charts along a locally directed cover is
quasi-coherent.** -/
public theorem ModulesDirectedGlueData.isQuasicoherent_glued [Preorder ι]
    (D : ModulesDirectedGlueData S f) (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, (D.mod i).IsQuasicoherent) : D.glued.IsQuasicoherent :=
  D.toModulesGlueData.isQuasicoherent_glued hf h

end Scheme

end Stacks.SheafOfModules

end
