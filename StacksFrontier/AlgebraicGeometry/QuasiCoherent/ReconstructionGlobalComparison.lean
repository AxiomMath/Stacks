module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionChartGlue
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionChartNormalisation

/-!
# The comparison of functors of [Stacks, Tag 0GPJ]

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  This file produces the last conjunct of
[Stacks, Tag 0GPJ]: a single isomorphism of schemes `g : Y ≅ X`, a single invertible
`𝒪_Y`-module `M`, and a natural isomorphism `e(𝓕) ≅ g^*𝓕 ⊗ M`.  This is the step the source
dismisses with "We omit the details".

## How the three pieces fit

* `AlgebraicGeometry.exists_schemeIso_of_quasicoherentEquivalence_of_isAffineOpenCover` returns
  the glued isomorphism of schemes **together with the charts it was glued from**: the opens
  `V i` covering `Y`, the isomorphisms `f i : V i ≅ U i` to which `g` restricts, the invertible
  sheaves `L i`, and the two chart isomorphisms `α i` and `β i`.
* The module is `e(𝒪_X)`, invertible by
  `AlgebraicGeometry.isInvertible_map_quasicoherentUnit_of_quasicoherentEquivalence`.  It is not
  the module produced by gluing the `L i`: taking `e(𝒪_X)` is what makes the restriction
  `e(𝒪_X)|_{V i} ≅ L i` be `AlgebraicGeometry.restrictMapUnitIsoOfChartIso`, built from the very
  `α i` and `β i` the chart comparison is assembled from, and that is what makes the
  normalisation at `𝒪_X` automatic
  (`AlgebraicGeometry.chartComparisonIso_hom_app_quasicoherentUnit`) rather than something an
  action of the units of `Γ(V i, 𝒪)` would have to arrange.
* `AlgebraicGeometry.exists_natIso_of_chartComparison` glues the per-chart comparisons
  `AlgebraicGeometry.chartComparisonIso`, using the normalisation to make any two of them agree
  over an affine open contained in both charts.

## Main results

* `AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence` —
  **[Stacks, Tag 0GPJ] in full**, for quasi-compact quasi-separated schemes.

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
instance search, which works at `reducible` transparency, sees through neither. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-- **Stacks Project, Tag 0GPJ.**  Let `X` and `Y` be quasi-compact and quasi-separated schemes
and let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence of their categories of quasi-coherent
modules.  Then there are an isomorphism of schemes `g : Y ≅ X` and an invertible `𝒪_Y`-module
`M` with `e(𝓕) ≅ g^*𝓕 ⊗ M`, naturally in the quasi-coherent `𝒪_X`-module `𝓕`.

The module is `e(𝒪_X)`; the isomorphism is the one glued from the reconstruction charts.  As in
the affine case the comparison of functors is stated after forgetting quasi-coherence, between
functors into all `𝒪_Y`-modules, which loses nothing because the inclusion of the quasi-coherent
modules is fully faithful and quasi-coherence is invariant under isomorphism.

Nothing is assumed beyond the equivalence and quasi-compactness and quasi-separatedness of the
two schemes. -/
@[stacks 0GPJ "the tag IN FULL, for `X` and `Y` quasi-compact and quasi-separated: an \
equivalence of the categories of quasi-coherent modules gives an isomorphism of schemes \
`g : Y ≅ X`, an invertible `𝒪_Y`-module `M`, and a NATURAL isomorphism `e(𝓕) ≅ g^*𝓕 ⊗ M`.  No \
cover, no affineness and no further hypothesis of any kind beyond qcqs.  The scheme half is \
`exists_schemeIso_of_quasicoherentEquivalence` and the module half \
`isInvertible_map_quasicoherentUnit_of_quasicoherentEquivalence`, both already \
unconditional; what is new is the comparison of functors, which the Stacks source dismisses \
with \"We omit the details\".  It is glued from the per-chart comparisons \
`chartComparisonIso` by `exists_natIso_of_chartComparison`, whose agreement hypothesis is \
discharged by the rigidity `natIso_eq_of_app_unit_eq_of_iso` once the comparisons are \
normalised at `𝒪_X`; the normalisation is \
`chartComparisonIso_hom_app_quasicoherentUnit` and it is automatic, because the module is \
`e(𝒪_X)` and the identification of its restriction with the chart's `L` is \
`restrictMapUnitIsoOfChartIso`, built from the same `α` and `β`.  As in the affine case the \
comparison is stated after forgetting quasi-coherence, between functors into all \
`𝒪_Y`-modules"]
theorem exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    ∃ (g : Y ≅ X) (M : Y.Modules),
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M ∧
        Nonempty (e.functor ⋙ ObjectProperty.ι
            (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ≅
          pullbackTensorFunctor g.hom M) := by
  obtain ⟨g, V, G, f, L, α, β, hVcover, hVaff, hLinv, hgf⟩ :=
    exists_schemeIso_of_quasicoherentEquivalence_of_isAffineOpenCover e
      (fun i : X.affineOpens => (i : X.Opens)) (fun i => i.2) (iSup_affineOpens_eq_top X)
  exact ⟨g, (e.functor.obj (quasicoherentUnit X)).obj,
    isInvertible_map_quasicoherentUnit_of_quasicoherentEquivalence e,
    exists_natIso_of_chartComparison g
      (isInvertible_map_quasicoherentUnit_of_quasicoherentEquivalence e) hVcover
      (fun i => chartComparisonIso e.functor g (e.functor.obj (quasicoherentUnit X)).obj
        (f i) (L i) (α i) (β i) (hgf i)
        (restrictMapUnitIsoOfChartIso e.functor (f i) (L i) (α i) (β i)))
      fun i => chartComparisonIso_hom_app_quasicoherentUnit _ _ _ _ _ _ _⟩

end AlgebraicGeometry

end
