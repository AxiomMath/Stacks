module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageCartesianChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# The image of a transposed map on the sections over a cartesian scheme chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`V` be an étale scheme chart of `Y`, and let `U` be a scheme presenting the fibre product
`V ×_Y X` — the situation produced by representability of `f`, for instance by
`AlgebraicGeometry.Space.IsRelativelyAmple.relativelyRepresentable`.  The proof of Stacks 0GUT
reads finitely many sections produced on `U` as sections of a direct image over `V`, encloses
them in a submodule `𝒢` covered by a finite locally free module `ℰ`, transposes along
`f^* ⊣ f_*`, and then needs the sections back on `U` to lie in the image of the transposed map
`ψ : f^*ℰ ⟶ ℱ`.  This file supplies the last step.

**Reading the sections is already available.**  The canonical map of sections
`(f_*ℱ)(V) → ℱ(U)` of a chart diagram over `f` — the chart component
`AlgebraicGeometry.Space.modulePushforwardCounitApp` of the chartwise universal property of the
direct image of Stacks 03LU — is bijective as soon as the square of the diagram is cartesian,
by `AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback` in
`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageCartesianChartSections.lean`, whose route is
the one the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyRelativeAmple.lean` ask for:
the comparison `AlgebraicGeometry.Space.chartLift` of the chart with the base change `V ×_Y X`
of Stacks 03G2 is an isomorphism, so the chart is an initial index of the limit computing the
sections of the direct image.  Along that route no identification of the chart produced by
representability with the one `AlgebraicGeometry.Space.smallBaseChange` builds is needed, and
`AlgebraicGeometry.Space.modulePushforwardChartIso` is not used.  What was still missing is the
passage from a cartesian square of presheaves to a chart diagram, which is
`AlgebraicGeometry.Space.chartDiagramOfIsPullback` below, and — for a reader who does want to go
through `AlgebraicGeometry.Space.modulePushforwardChartIso` — the identification of the two
charts itself, which is
`AlgebraicGeometry.Space.exists_iso_smallBaseChange_obj_of_isPullback`.

**The image of the transpose is what is proved here.**  The only characterisation `ψ` carries
is the adjunction equation `(modulePullbackAdjunction B S hS f).homEquiv ψ = φ ≫ 𝒢.ι` of
`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_of_hasResolutionProperty`.
`AlgebraicGeometry.Space.modulePushforwardCounitApp_homEquiv_app` turns it into a statement
about sections, and surjectivity of `φ` on the sections over an affine chart — Descent,
Proposition 03DW in the form
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite` — produces the
section of `ℰ` whose unit section `ψ` carries to the prescribed section.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramOfIsPullback` is the chart diagram of a cartesian square
  presenting a scheme over an étale chart `V` of `Y` as the fibre product `V ×_Y X`.

## Main results

* `AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_chartDiagramOfIsPullback`: **the
  sections of `f_*ℱ` over `V` are exactly the sections of `ℱ` over the scheme that a cartesian
  square presents as `V ×_Y X`.**
* `AlgebraicGeometry.Space.exists_iso_smallBaseChange_obj_of_isPullback`: **the chart of a
  cartesian chart diagram is the base-changed chart of Stacks 03G2**, by a unique isomorphism
  compatible with the two morphisms to `V ×_Y X`.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_homEquiv_app`: the chart reading of a
  section in the image of the transpose of `ψ : f^*ℰ ⟶ ℱ` is the value of `ψ` on the
  corresponding unit section.
* `AlgebraicGeometry.Space.exists_modulePullbackUnitSection_eq_of_homEquiv_eq`: **a section of
  `f_*ℱ` over an affine chart lying in a submodule covered by `ℰ` is, read on the chart of `X`,
  a value of the transposed map.**
* `AlgebraicGeometry.Space.mem_moduleFMapSpanningSet_modulePushforwardCounitApp`: the same
  membership in the form
  `AlgebraicGeometry.Space.epi_of_spanSieve_moduleFMapSpanningSet_mem` consumes.
* `AlgebraicGeometry.Space.exists_modulePullbackUnitSection_eq_of_isPullback`: the two combined,
  for a chart diagram whose square is cartesian and whose chart of `Y` is affine.

## Implementation notes

**No declaration here carries a tag.**  Stacks 0GUT and Stacks 0GUU are not proved; what is
added is one of the three chart transports their proofs consume, listed as missing in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyRelativeAmple.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyPushforwardSections.lean`.  The
other two — negative tensor powers of the ample module restricted to the chart, and descent of
an epimorphism of modules from the chart scheme to `X` — are untouched.

**Why `chartDiagramOfIsPullback` needs no representability hypothesis.**  A cartesian square
over an étale chart `gV` of `Y` makes its upper horizontal arrow `p : yoneda.obj U ⟶ X` a base
change of `gV`, hence étale by
`AlgebraicGeometry.Space.isEtale_of_isPullback_yoneda`, hence an étale chart of `X` by
`AlgebraicGeometry.Space.presheaf_etale_of_isEtale`; the commutativity of the square is the
commutativity of the chart diagram.  Representability of `f` is what *produces* such a square,
and is not used once one is given.

**The characterisation of `ψ` is used through its chartwise transpose.**
`AlgebraicGeometry.Space.modulePullbackHomFMap` of `ψ` is, by definition, the chart component of
the direct image applied to the transpose of `ψ`, so rewriting the adjunction equation inside it
is what connects the equation to sections; `AlgebraicGeometry.Space.modulePullbackHomFMap_app`
then reads its values as values of `ψ`.  That is the only available route: nothing else
describes `ψ` on sections.

**Quasi-coherence of the submodule is a hypothesis.**  Surjectivity of `φ` on the sections over
the affine chart needs `𝒢` quasi-coherent as well as `ℰ`.  It is available where the submodule
is produced — the proof of
`AlgebraicGeometry.Space.exists_finiteLocallyFree_epi_submodule_modulePushforward`
(`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyPushforwardSections.lean:137`)
establishes it as `hqc` from Descent, Proposition 03DX (2) — but that theorem's conclusion does
not record it, so a caller gluing the two must supply it separately or that conclusion must be
strengthened.  It is a genuine hypothesis of the statements below, discharged where they are
applied, not a deferred assertion.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### A cartesian square as a chart diagram -/

/-- **The chart diagram of a scheme presenting a fibre product.**  Let `gV : yoneda.obj V ⟶ Y`
be an étale scheme chart of `Y` and let a cartesian square present the fibre product of `gV`
with `f : X ⟶ Y` as a scheme `U` over `V`.  Then `U` is an étale scheme chart of `X`, by
stability of étaleness under base change, and the square is a chart diagram over `f`.

This is the form in which a cartesian square from
`CategoryTheory.Functor.relativelyRepresentable` — for instance the one
`AlgebraicGeometry.Space.exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple`
produces — enters the chart machinery of Stacks 03G3. -/
def chartDiagramOfIsPullback (f : X ⟶ Y) {U V : BigFppfOver B S hS} (q : U ⟶ V)
    (p : yoneda.obj U ⟶ X.1) (gV : yoneda.obj V ⟶ Y.1) (hgV : IsEtale B S hS gV)
    (hsq : IsPullback p (yoneda.map q) f.hom gV) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := ⟨CostructuredArrow.mk p,
    presheaf_etale_of_isEtale B S hS (isEtale_of_isPullback_yoneda B S hS hsq.flip hgV)⟩
  V := ⟨CostructuredArrow.mk gV, presheaf_etale_of_isEtale B S hS hgV⟩
  g := q
  comm := hsq.w

/-- **The sections of a direct image over an étale scheme chart of the target are the sections
over the scheme a cartesian square presents as the fibre product.**  This is
`AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback` at the chart diagram
`AlgebraicGeometry.Space.chartDiagramOfIsPullback`; the cartesian square of the chart diagram is
the given one. -/
theorem bijective_modulePushforwardCounitApp_chartDiagramOfIsPullback (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) {U V : BigFppfOver B S hS} (q : U ⟶ V)
    (p : yoneda.obj U ⟶ X.1) (gV : yoneda.obj V ⟶ Y.1) (hgV : IsEtale B S hS gV)
    (hsq : IsPullback p (yoneda.map q) f.hom gV) :
    Function.Bijective (modulePushforwardCounitApp B S hS f F
      (chartDiagramOfIsPullback B S hS f q p gV hgV hsq)) :=
  bijective_modulePushforwardCounitApp_of_isPullback B S hS f F
    (chartDiagramOfIsPullback B S hS f q p gV hgV hsq) hsq

/-! ### The chart of a cartesian chart diagram is the base-changed chart -/

/-- **The chart of a cartesian chart diagram is the base-changed étale scheme chart of
Stacks 03G2.**  For a representable `f` and a chart diagram whose square is cartesian, the chart
of `X` of the diagram is canonically isomorphic, over the base change `V ×_Y X` taken in the
spaces-étale site and hence over `V`, to the étale scheme chart
`AlgebraicGeometry.Space.smallBaseChange` builds.

This is the identification that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyRelativeAmple.lean` record as
missing for the sections of `AlgebraicGeometry.Space.modulePushforwardChartIso`: both charts map
isomorphically to `V ×_Y X` — the diagram's chart by
`AlgebraicGeometry.Space.isIso_chartLift_of_isPullback`, the base-changed chart by
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso` — and the comparison functor of
Stacks 03G1 is fully faithful, so the composite comes from a unique isomorphism of scheme
charts.  The clause pins that isomorphism down: nothing else is compatible with the two
morphisms to `V ×_Y X`. -/
theorem exists_iso_smallBaseChange_obj_of_isPullback (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f.hom d.V.1.hom) :
    ∃ i : d.U ≅ (smallBaseChange B S hS f hf).obj d.V,
      (comparisonFunctor B S hS X).map i.hom ≫
        (smallBaseChangeComparisonIso B S hS f hf d.V).hom = chartLift B S hS f d := by
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := isIso_chartLift_of_isPullback B S hS f d hd
  refine ⟨(comparisonFunctor B S hS X).preimageIso (asIso (chartLift B S hS f d) ≪≫
    (smallBaseChangeComparisonIso B S hS f hf d.V).symm), ?_⟩
  rw [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The image of a transposed map on the sections over a chart -/

/-- **The chart reading of the transpose of a morphism out of a module pullback is a value of
that morphism.**  For `ψ : f^*ℰ ⟶ ℱ` and a chart diagram `d`, the chart component of the direct
image applied to the transpose of `ψ` evaluated at a section `ε` of `ℰ` is the value of `ψ` on
the unit section of `ε`.

This is `AlgebraicGeometry.Space.modulePullbackHomFMap_app`, whose left-hand side is this chart
component by definition of `AlgebraicGeometry.Space.modulePullbackHomFMap`. -/
theorem modulePushforwardCounitApp_homEquiv_app (f : X ⟶ Y)
    (E : Modules.{u, u} B S hS Y.1 Y.2) (F : Modules.{u, u} B S hS X.1 X.2)
    (ψ : (modulePullback B S hS f).obj E ⟶ F) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (ε : E.val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F d
        (((modulePullbackAdjunction B S hS f).homEquiv E F ψ).val.app (op d.V) ε) =
      ψ.val.app (op d.U) (modulePullbackUnitSection B S hS f E d ε) :=
  modulePullbackHomFMap_app B S hS f E F ψ d ε

/-- The chartwise transpose of `ψ`, unfolded: its value at a section `ε` of `ℰ` is the chart
component of the direct image applied to the value at `ε` of the transpose of `ψ` along
`f^* ⊣ f_*`.  This is the definition of `AlgebraicGeometry.Space.modulePullbackHomFMap`, stated
so that the adjunction equation characterising `ψ` can be rewritten with. -/
theorem modulePullbackHomFMap_app_eq_counitApp (f : X ⟶ Y)
    (E : Modules.{u, u} B S hS Y.1 Y.2) (F : Modules.{u, u} B S hS X.1 X.2)
    (ψ : (modulePullback B S hS f).obj E ⟶ F) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (ε : E.val.obj (op d.V)) :
    (modulePullbackHomFMap B S hS f E F ψ).app d ε =
      modulePushforwardCounitApp B S hS f F d
        (((modulePullbackAdjunction B S hS f).homEquiv E F ψ).val.app (op d.V) ε) :=
  rfl

section Image

variable (f : X ⟶ Y) {E : Modules.{u, u} B S hS Y.1 Y.2} {F : Modules.{u, u} B S hS X.1 X.2}
  (G : ((modulePushforward B S hS f).obj F).Submodule) (φ : E ⟶ G.toSheafOfModules)
  (ψ : (modulePullback B S hS f).obj E ⟶ F)

/-- A section of `f_*ℱ` over an affine étale chart of `Y` lying in a submodule which an
epimorphism from `ℰ` covers is a value on that chart of the composite `ℰ ⟶ 𝒢 ⟶ f_*ℱ`.

Surjectivity of `φ` on the sections over an affine chart is Descent, Proposition 03DW in the
form `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`; see the
implementation notes on the quasi-coherence hypotheses. -/
theorem exists_comp_ι_val_app_eq_of_mem (hφ : Epi φ) (hE : E.IsQuasicoherentOnSite)
    (hG : G.toSheafOfModules.IsQuasicoherentOnSite) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine (chartScheme V))
    (σ : ((modulePushforward B S hS f).obj F).val.obj (op V)) (hσ : σ ∈ G.obj (op V)) :
    ∃ ε : E.val.obj (op V), (φ ≫ G.ι).val.app (op V) ε = σ := by
  obtain ⟨ε, hε⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite φ hφ hE hG V hV
    (⟨σ, hσ⟩ : G.obj (op V))
  exact ⟨ε, congrArg (fun m => G.ι.val.app (op V) m) hε⟩

/-- **A section of a direct image lying in the image submodule is, on the chart, a value of the
transposed map.**  Let `ψ : f^*ℰ ⟶ ℱ` be characterised by its transpose along `f^* ⊣ f_*` being
`φ ≫ 𝒢.ι`, with `φ : ℰ ⟶ 𝒢` an epimorphism onto a quasi-coherent submodule `𝒢` of `f_*ℱ`, and
let `d` be a chart diagram whose chart of `Y` is affine.  Then every section of `f_*ℱ` over that
chart which lies in `𝒢` is, read on the chart of `X` by the chartwise universal property of
Stacks 03LU, a value of `ψ`.

This is the source's *"`s_i` is in the image"* at `ℒ = 𝒪_X`, in the only form the
characterisation of `ψ` supports: the adjunction equation is turned into a statement about
sections by `AlgebraicGeometry.Space.modulePushforwardCounitApp_homEquiv_app`, and the section
of `ℰ` it is applied to comes from surjectivity of `φ` on the sections over the affine chart. -/
theorem exists_modulePullbackUnitSection_eq_of_homEquiv_eq (hφ : Epi φ)
    (hE : E.IsQuasicoherentOnSite) (hG : G.toSheafOfModules.IsQuasicoherentOnSite)
    (hψ : (modulePullbackAdjunction B S hS f).homEquiv E F ψ = φ ≫ G.ι)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (hV : IsAffine (chartScheme d.V))
    (σ : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) (hσ : σ ∈ G.obj (op d.V)) :
    ∃ ε : E.val.obj (op d.V),
      ψ.val.app (op d.U) (modulePullbackUnitSection B S hS f E d ε) =
        modulePushforwardCounitApp B S hS f F d σ := by
  obtain ⟨ε, hε⟩ := exists_comp_ι_val_app_eq_of_mem B S hS f G φ hφ hE hG d.V hV σ hσ
  refine ⟨ε, ?_⟩
  rw [← modulePushforwardCounitApp_homEquiv_app B S hS f E F ψ d ε, hψ, hε]

/-- **The chart reading of a section in the image submodule belongs to the spanning family of
the chartwise transpose.**  This is
`AlgebraicGeometry.Space.exists_modulePullbackUnitSection_eq_of_homEquiv_eq` in the form
`AlgebraicGeometry.Space.epi_of_spanSieve_moduleFMapSpanningSet_mem` consumes: the value is its
own restriction along the identity of the chart. -/
theorem mem_moduleFMapSpanningSet_modulePushforwardCounitApp (hφ : Epi φ)
    (hE : E.IsQuasicoherentOnSite) (hG : G.toSheafOfModules.IsQuasicoherentOnSite)
    (hψ : (modulePullbackAdjunction B S hS f).homEquiv E F ψ = φ ≫ G.ι)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (hV : IsAffine (chartScheme d.V))
    (σ : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) (hσ : σ ∈ G.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f F d σ ∈
      moduleFMapSpanningSet B S hS f E F (modulePullbackHomFMap B S hS f E F ψ) (op d.U) := by
  obtain ⟨ε, hε⟩ :=
    exists_modulePullbackUnitSection_eq_of_homEquiv_eq B S hS f G φ ψ hφ hE hG hψ d hV σ hσ
  refine ⟨d, 𝟙 d.U, ε, ?_⟩
  refine (CategoryTheory.congr_fun (F.val.presheaf.map_id (op d.U))
    ((modulePullbackHomFMap B S hS f E F ψ).app d ε)).trans ?_
  rw [modulePullbackHomFMap_app B S hS f E F ψ d ε]
  exact hε

/-- **The sections over the chart that lie in the image of the transposed map.**  For a chart
diagram whose underlying square is cartesian and whose chart of `Y` is affine, every section of
`ℱ` over the chart of `X` whose unique preimage under the chart component of Stacks 03LU lies in
the submodule `𝒢` is a value of the transposed map `ψ` on that chart.

The preimage exists and is unique by
`AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback`, and lies in the
image of `ψ` by `AlgebraicGeometry.Space.exists_modulePullbackUnitSection_eq_of_homEquiv_eq`. -/
theorem exists_modulePullbackUnitSection_eq_of_isPullback (hφ : Epi φ)
    (hE : E.IsQuasicoherentOnSite) (hG : G.toSheafOfModules.IsQuasicoherentOnSite)
    (hψ : (modulePullbackAdjunction B S hS f).homEquiv E F ψ = φ ≫ G.ι)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hsq : IsPullback d.U.1.hom (yoneda.map d.g) f.hom d.V.1.hom)
    (hV : IsAffine (chartScheme d.V)) (τ : F.val.obj (op d.U))
    (hτ : ∀ σ : ((modulePushforward B S hS f).obj F).val.obj (op d.V),
      modulePushforwardCounitApp B S hS f F d σ = τ → σ ∈ G.obj (op d.V)) :
    ∃ ε : E.val.obj (op d.V),
      ψ.val.app (op d.U) (modulePullbackUnitSection B S hS f E d ε) = τ := by
  obtain ⟨σ, hσ⟩ :=
    (bijective_modulePushforwardCounitApp_of_isPullback B S hS f F d hsq).2 τ
  obtain ⟨ε, hε⟩ := exists_modulePullbackUnitSection_eq_of_homEquiv_eq B S hS f G φ ψ hφ hE hG
    hψ d hV σ (hτ σ hσ)
  exact ⟨ε, hε.trans hσ⟩

end Image

end AlgebraicGeometry.Space

end
