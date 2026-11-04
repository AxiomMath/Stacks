module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartSectionsTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveChartLocalGeneration
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSectionsQuasicoherent

/-!
# Steps 4–5 of the proof of Stacks 0GUT: a finite locally free module surjecting onto a module
generated over one cartesian chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓗` be a quasi-coherent
`𝒪_X`-module, and let `d` be a **cartesian** chart diagram over `f` — an étale scheme chart
`d.V` of `Y` and the scheme `d.U` presenting `d.V ×_Y X` — with `d.V` affine and the structure
morphism of `d.U` surjective.  Suppose finitely many sections of `𝓗` over `d.U` have the property
that their readings span the chart restriction of `𝓗` over every affine open of `chartScheme d.U`.

Then there is a finite locally free `𝒪_Y`-module `ℰ` whose pullback `f^*ℰ` is finite locally free
and admits an **epimorphism** onto `𝓗`.

This is the middle of the source's argument: the sections over the chart of `X` are the sections
of the direct image `f_*𝓗` over the chart of `Y` (Stacks 03LU, cartesian case), the resolution
property of `Y` covers the submodule of `f_*𝓗` they generate by a finite locally free module, and
the transpose along `f^* ⊣ f_*` of that covering is surjective because its chart values are
exactly the given spanning sections.

## Main results

* `AlgebraicGeometry.Space.chartDiagramOfIsPullback_U`: the chart of `X` of the chart diagram a
  cartesian square presents is, on the nose, the étale chart
  `AlgebraicGeometry.Space.etaleChartOfIsPullback` that square presents.
* `AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_epi_of_chartSections`:
  **steps 4–5 of the remaining proof of Stacks 0GUT**, as described above.

## Implementation notes

**The hypotheses, and where each comes from in Stacks 0GUT.**  Besides the data of the chart
diagram and the spanning sections:

* `hZ : B.Contains (⊤_ Scheme.{u})` is the containment of the terminal scheme in the site, needed
  to *state* the absolute quasi-separatedness of Stacks 03BS (3); it is a property of the ambient
  site, not of `f`, and it is the form in which
  `AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_quasicoherentSubmodule`
  asks for quasi-separatedness of `Y`.
* `hfqc : IsQuasiCompact B S hS f.hom` and `hfqs : IsQuasiSeparated B S hS f.hom` are **not**
  extra hypotheses of Stacks 0GUT: they are Stacks 0D34 for the relatively ample module, through
  `AlgebraicGeometry.Space.IsRelativelyAmple.isQuasiCompact` and
  `AlgebraicGeometry.Space.IsRelativelyAmple.isSeparated` followed by Stacks 03KK.  They are
  carried here because this statement does not mention a relatively ample module at all.
* `hYqc`, `hYqs` and `hYres` are the three hypotheses Stacks 0GUT puts on the target.

Everything is stated at `AlgebraicGeometry.Space.Modules.{u, u}`: the pushforward and pullback of
modules along a morphism of algebraic spaces exist only at the module universe of the schemes.

**Why the index type is only `Finite`.**  The spanning family produced by step 3 of the proof is
indexed by the index type of a family of generating sections, which is existentially bound there;
`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_quasicoherentSubmodule`
consumes a `Finset`, so a `Fintype` structure is chosen here by `Fintype.ofFinite`.

**Where the chart identification is needed, and where it is not.**  The chart of `X` of
`AlgebraicGeometry.Space.chartDiagramOfIsPullback` and
`AlgebraicGeometry.Space.etaleChartOfIsPullback` are the same term, so the ampleness of the
restriction of `L` and the surjectivity of the chart — both stated for the latter in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeAmple` — are hypotheses of the
former without any transport.  `AlgebraicGeometry.Space.chartDiagramOfIsPullback_U` records this.

**No tag is claimed.**  Stacks 0GUT is registered on the theorem that proves it, in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleMain`.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The chart of `X` of the chart diagram a cartesian square presents is the étale chart that
square presents.**  `AlgebraicGeometry.Space.chartDiagramOfIsPullback` and
`AlgebraicGeometry.Space.etaleChartOfIsPullback` build the same chart out of the same square, so
no identification is needed between the statements written for one and those written for the
other. -/
theorem chartDiagramOfIsPullback_U {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {U V : BigFppfOver B S hS} (q : U ⟶ V) (p : yoneda.obj U ⟶ X.1) (gV : yoneda.obj V ⟶ Y.1)
    (hgV : IsEtale B S hS gV) (hsq : IsPullback p (yoneda.map q) f.hom gV) :
    (chartDiagramOfIsPullback B S hS f q p gV hgV hsq).U =
      etaleChartOfIsPullback B S hS X hgV hsq :=
  rfl

/-- **Steps 4–5 of the remaining proof of Stacks 0GUT.**  Let `f : X ⟶ Y` be a quasi-compact,
quasi-separated morphism of algebraic spaces onto a quasi-compact, quasi-separated target with
the resolution property, let `𝓗` be a quasi-coherent `𝒪_X`-module, and let `d` be a chart diagram
over `f` whose square is cartesian, whose chart of `Y` is affine and whose chart of `X` has
surjective structure morphism.  If finitely many sections `a i` of `𝓗` over the chart of `X` have
readings spanning the chart restriction of `𝓗` over every affine open of the chart's scheme, then
there are a finite locally free `𝒪_Y`-module `ℰ` with `f^*ℰ` finite locally free and an
epimorphism `f^*ℰ ⟶ 𝓗`.

The proof is the source's argument. The chart component of Stacks 03LU is bijective for a
cartesian diagram (`AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback`),
so each `a i` is the reading of a unique section `τ i` of `f_*𝓗` over the chart of `Y`; the
resolution property of `Y` covers a quasi-coherent submodule of `f_*𝓗` containing all the `τ i`
by a finite locally free `ℰ`, and `ψ` is the transpose of that covering
(`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_quasicoherentSubmodule`);
each `a i` is then a value of the chartwise transpose of `ψ`
(`AlgebraicGeometry.Space.exists_modulePullbackUnitSection_eq_of_homEquiv_eq` read through
`AlgebraicGeometry.Space.modulePullbackHomFMap_app`), so the spanning hypothesis is the
hypothesis of
`AlgebraicGeometry.Space.spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict`,
and `AlgebraicGeometry.Space.epi_of_spanSieve_moduleFMapSpanningSet_mem` concludes. -/
theorem exists_finiteLocallyFree_modulePullback_epi_of_chartSections
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS X.1 X.2) (hH : H.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f.hom d.V.1.hom)
    (hVaff : IsAffine (chartScheme d.V)) (hsurj : IsSurjective B S hS d.U.1.hom)
    {I : Type u} [Finite I] (a : I → H.val.obj (op d.U))
    (hgen : ∀ O : (chartScheme d.U).Opens, IsAffineOpen O →
      ∀ y : (restrictToChartScheme B S hS X.1 X.2 H d.U).val.obj (op O),
        y ∈ Submodule.span ((chartScheme d.U).ringCatSheaf.obj.obj (op O))
          (Set.range fun i => chartSectionsToRestrict X H d.U O
            (H.val.map (openChartInclusion B S hS X.1 d.U O).op (a i)))) :
    ∃ (E : Modules.{u, u} B S hS Y.1 Y.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS f).obj E))
      (ψ : (modulePullback B S hS f).obj E ⟶ H), Epi ψ := by
  have := Fintype.ofFinite I
  choose τ hτ using fun i =>
    (bijective_modulePushforwardCounitApp_of_isPullback B S hS f H d hd).2 (a i)
  obtain ⟨G, E, hE, φ, hφ, hmem, hGqc, hflf, ψ, hψ⟩ :=
    exists_finiteLocallyFree_modulePullback_hom_quasicoherentSubmodule hZ f hfqc hfqs hYqc hYqs
      hYres H hH (Finset.univ : Finset I) d.V hVaff τ
  refine ⟨E, hflf, ψ, ?_⟩
  have hEqc : E.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite E hE
  choose ε hε using fun i =>
    exists_modulePullbackUnitSection_eq_of_homEquiv_eq B S hS f G φ ψ hφ hEqc hGqc hψ d hVaff
      (τ i) (hmem i (Finset.mem_univ i))
  have key : ∀ i, (modulePullbackHomFMap B S hS f E H ψ).app d (ε i) = a i := by
    intro i
    rw [modulePullbackHomFMap_app B S hS f E H ψ d (ε i)]
    exact (hε i).trans (hτ i)
  refine epi_of_spanSieve_moduleFMapSpanningSet_mem B S hS f E H ψ ?_
  refine spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict f E H hH ψ d hsurj ε
    (fun O hO y => ?_)
  simp only [key]
  exact hgen O hO y

end AlgebraicGeometry.Space

end
