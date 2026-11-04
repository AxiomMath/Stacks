module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence

/-!
# The stalk of a direct image of modules at a geometric point

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `G` be an `𝒪_Y`-module
and let `x̄` be a geometric point of `X`.  Stacks 0AES asserts, for `f` quasi-compact and
quasi-separated and `G` quasi-coherent, that

`(f_*G)_{x̄} = Γ(Y ×_X Spec(𝒪_{X, x̄}), p^*G)`,

where `p : Y ×_X Spec(𝒪_{X, x̄}) ⟶ Y` is the projection.

This file proves that identity with the strict henselization replaced by the filtered system of
small étale neighbourhoods of `x̄` out of which it is built: the geometric stalk of `f_*G` at `x̄`
is the colimit, over the small étale neighbourhoods `V` of `x̄`, of the sections of `p_V^*G` on
`Y ×_X V`, and the sections on `Y ×_X V` are the compatible families of sections of `G` over the
étale scheme charts of `Y` above `Y ×_X V`.  In that form the identity needs neither
quasi-compactness nor quasi-separatedness of `f`, nor quasi-coherence of `G`: those hypotheses
are what the source uses to replace the filtered colimit over the neighbourhood system by the
single algebraic space `Y ×_X Spec(𝒪_{X, x̄})`, by flat base change along the flat morphism
`Spec(𝒪_{X, x̄}) ⟶ X`, which is Stacks 073K.

## Main definitions

* `AlgebraicGeometry.Space.directImageChartSection`: the section of `G` over an étale scheme
  chart of `Y` above `Y ×_X V` cut out by a section of `f_*G` over the étale scheme chart `V` of
  `X`.
* `AlgebraicGeometry.Space.directImageChartSectionsEquiv`: the identification of the sections of
  `f_*G` over `V` with the sections of `p_V^*G` on `Y ×_X V`, the latter read as the compatible
  families of chartwise sections of `G`.

## Main results

* `AlgebraicGeometry.Space.directImageChartSection_eq_counitApp`: the chartwise section is the
  canonical map of sections of Stacks 03LU at the corresponding diagram of étale scheme charts,
  so it is the restriction of a section of `f_*G` to `Y ×_X V` and not another construction.
* `AlgebraicGeometry.Space.directImageChartSection_ext`: a section of `f_*G` over `V` is
  determined by its chartwise sections over `Y ×_X V`.
* `AlgebraicGeometry.Space.exists_geometricModuleStalkGerm_modulePushforward`: every element of
  `(f_*G)_{x̄}` is the germ of a section of `p_V^*G` on `Y ×_X V` for some small étale
  neighbourhood `V` of `x̄`.
* `AlgebraicGeometry.Space.geometricModuleStalkGerm_modulePushforward_eq_iff`: two sections of
  `f_*G` over the chart of a neighbourhood have the same germ at `x̄` exactly when their
  chartwise sections over `Y ×_X V` agree for some smaller neighbourhood `V`.

## Implementation notes

The canonical morphism `Spec(𝒪_{X, x̄}) ⟶ X` of the source is not available for an algebraic
space in this development, which is why the right hand side is written through the neighbourhood
system.  `AlgebraicGeometry.Space.etaleLocalRing` is the colimit of the section rings over the
category of small étale neighbourhoods of `x̄`, and that category lives one universe above the
schemes of the big fppf site, so the colimit is a `CommRingCat.{u + 1}` and
`AlgebraicGeometry.Space.strictHenselization` is a `Scheme.{u + 1}`.  The objects of
`AlgebraicGeometry.BigFppfOver B S hS` are schemes of universe `u`, so that spectrum is not an
object of the site, it is not an algebraic space over `S` here, and there is no fibre product
`Y ×_X Spec(𝒪_{X, x̄})` to take sections over.

Passing from the colimit over the neighbourhood system to the single space
`Y ×_X Spec(𝒪_{X, x̄})` is flat base change along `Spec(𝒪_{X, x̄}) ⟶ X`.  That is Stacks 073K,
whose base change map is constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean` but whose invertibility —
the clause the source's proof invokes — is not proved there.  So neither the source's formula
itself nor the quasi-compactness, quasi-separatedness and quasi-coherence hypotheses it carries
appear below.

The sections of `p_V^*G` on `Y ×_X V` are read as the limit of the sections of `G` over the
étale scheme charts of `Y` above `Y ×_X V`.  That reading is forced by the same universe
constraint one level down: for a general `f` the algebraic space `Y ×_X V` is not an étale
scheme chart of `Y`, so it is not an object of the small étale site of `Y` and sections of `G`
over it are not available directly; the pointwise right Kan extension
`AlgebraicGeometry.Space.ranChartIsLimit` along the comparison functor of Stacks 03G1 supplies
them as the limit over the charts above it.  The chart projections themselves are
`AlgebraicGeometry.Space.moduleChartProjection`, and `AlgebraicGeometry.Space.chartBaseChange`
is `Y ×_X V`.

## References

* [Stacks Project, Tag 0AES](https://stacks.math.columbia.edu/tag/0AES)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Sections of a direct image over an étale chart of the target -/

/-- The diagram of chartwise sections of an `𝒪_Y`-module `G` above `Y ×_X V`, for an étale
scheme chart `V` of `X`: it sends an étale scheme chart of `Y` above `Y ×_X V` to the sections
of `G` there.  Its limit is `Γ(Y ×_X V, p_V^*G)`. -/
noncomputable abbrev directImageChartDiagram (f : Y ⟶ X) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS X.1) :
    StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS Y).op ⥤
      Type u :=
  StructuredArrow.proj (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS Y).op ⋙
    (moduleSetSheaf B S hS Y G).obj

/-- The section of `G` over an étale scheme chart of `Y` above `Y ×_X V` cut out by a section of
the direct image `f_*G` over the étale scheme chart `V` of `X`: the chart projection of the
direct image at that chart. -/
noncomputable def directImageChartSection (f : Y ⟶ X) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS X.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS Y).op)
    (s : ((modulePushforward B S hS f).obj G).val.obj (op V)) :
    G.val.obj j.right :=
  (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS Y G) s

/-- Equal étale scheme charts above `Y ×_X V` have the same chart projection.  The statement is
phrased with `HEq` because the type of a chart projection mentions the chart. -/
private theorem moduleChartProjection_app_heq (f : Y ⟶ X)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS X.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS Y).op}
    (h : j = j') (s : ((modulePushforward B S hS f).obj G).val.obj (op V)) :
    HEq ((moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS Y G) s)
      ((moduleChartProjection B S hS f V j').app (moduleSetSheaf B S hS Y G) s) := by
  subst h
  rfl

/-- The chartwise section cut out by a section of the direct image is the canonical map of
sections of Stacks 03LU at the diagram of étale scheme charts which that chart names.  So it is
the restriction of a section of `f_*G` to `Y ×_X V`, additive and semilinear over the chartwise
pullback of regular functions, and not an independent construction. -/
theorem directImageChartSection_eq_counitApp (f : Y ⟶ X)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS X.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS Y).op)
    (s : ((modulePushforward B S hS f).obj G).val.obj (op V)) :
    directImageChartSection B S hS f G V j s =
      modulePushforwardCounitApp B S hS f G (chartDiagramOfIndex B S hS f V j) s :=
  eq_of_heq (moduleChartProjection_app_heq B S hS f G V
    (indexOfChartDiagram_chartDiagramOfIndex B S hS f V j).symm s)

/-- A section of the direct image `f_*G` over an étale scheme chart `V` of `X` is determined by
its chartwise sections over `Y ×_X V`: those sections are a limit over the étale scheme charts
of `Y` above `Y ×_X V`. -/
theorem directImageChartSection_ext (f : Y ⟶ X) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS X.1)
    {s t : ((modulePushforward B S hS f).obj G).val.obj (op V)}
    (h : ∀ j, directImageChartSection B S hS f G V j s =
      directImageChartSection B S hS f G V j t) :
    s = t :=
  moduleChartProjection_ext B S hS f V (moduleSetSheaf B S hS Y G) h

/-- **The sections of `p_V^*G` on `Y ×_X V` are the sections of `f_*G` over `V`.**  A section of
the direct image over an étale scheme chart `V` of `X` is the same thing as a compatible family
of sections of `G` over the étale scheme charts of `Y` above `Y ×_X V`, that is as an element of
`Γ(Y ×_X V, p_V^*G)`.

The two halves are the comparison of the direct image of sheaves of sets with its right Kan
extension form and the pointwise limit property of that Kan extension. -/
noncomputable def directImageChartSectionsEquiv (f : Y ⟶ X)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS X.1) :
    ((modulePushforward B S hS f).obj G).val.obj (op V) ≃
      (directImageChartDiagram B S hS f G V).sections where
  toFun s :=
    Types.isLimitEquivSections
      (ranChartIsLimit B S hS Y (moduleSetSheaf B S hS Y G).obj
        (chartBaseChange B S hS f V))
      (((smallEtaleDirectImageRanIso B S hS f).hom.app
        (moduleSetSheaf B S hS Y G)).hom.app (op V) s)
  invFun a :=
    ((smallEtaleDirectImageRanIso B S hS f).inv.app
        (moduleSetSheaf B S hS Y G)).hom.app (op V)
      ((Types.isLimitEquivSections
        (ranChartIsLimit B S hS Y (moduleSetSheaf B S hS Y G).obj
          (chartBaseChange B S hS f V))).symm a)
  left_inv s := by
    refine Eq.trans (congrArg
      (fun z ↦ ((smallEtaleDirectImageRanIso B S hS f).inv.app
          (moduleSetSheaf B S hS Y G)).hom.app (op V) z)
      ((Types.isLimitEquivSections
        (ranChartIsLimit B S hS Y (moduleSetSheaf B S hS Y G).obj
          (chartBaseChange B S hS f V))).symm_apply_apply _)) ?_
    exact congrArg
      (fun m : (smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS Y G) ⟶
          (smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS Y G) ↦ m.hom.app (op V) s)
      (Iso.hom_inv_id_app (smallEtaleDirectImageRanIso B S hS f)
        (moduleSetSheaf B S hS Y G))
  right_inv a := by
    refine Eq.trans (congrArg
      (Types.isLimitEquivSections
        (ranChartIsLimit B S hS Y (moduleSetSheaf B S hS Y G).obj
          (chartBaseChange B S hS f V)))
      (congrArg
        (fun m : (smallEtaleDirectImageRan B S hS f).obj (moduleSetSheaf B S hS Y G) ⟶
            (smallEtaleDirectImageRan B S hS f).obj (moduleSetSheaf B S hS Y G) ↦
          m.hom.app (op V) ((Types.isLimitEquivSections
            (ranChartIsLimit B S hS Y (moduleSetSheaf B S hS Y G).obj
              (chartBaseChange B S hS f V))).symm a))
        (Iso.inv_hom_id_app (smallEtaleDirectImageRanIso B S hS f)
          (moduleSetSheaf B S hS Y G)))) ?_
    exact (Types.isLimitEquivSections
      (ranChartIsLimit B S hS Y (moduleSetSheaf B S hS Y G).obj
        (chartBaseChange B S hS f V))).apply_symm_apply a

/-- The components of the identification are the chartwise sections: that is what makes it the
restriction of a section of `f_*G` to `Y ×_X V`. -/
theorem directImageChartSectionsEquiv_apply (f : Y ⟶ X)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS X.1)
    (s : ((modulePushforward B S hS f).obj G).val.obj (op V))
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS Y).op) :
    (directImageChartSectionsEquiv B S hS f G V s).1 j =
      directImageChartSection B S hS f G V j s :=
  (moduleChartProjection_app B S hS f V j (moduleSetSheaf B S hS Y G) s).symm

/-! ### The geometric stalk of a direct image -/

variable (G : Modules.{u, u} B S hS Y.1 Y.2) (x : GeometricPoint B S hS X.1)

/-- **Stacks 0AES, the generation half of the colimit form.**  Every element of the geometric
stalk `(f_*G)_{x̄}` is the germ at `x̄` of a section of `p_V^*G` on `Y ×_X V`, for some small
étale neighbourhood `V` of `x̄`: that section is a compatible family of sections of `G` over the
étale scheme charts of `Y` above `Y ×_X V`. -/
@[stacks 0AES "generation half, for the geometric point stalk expressed as the filtered colimit
over the etale neighbourhoods of x-bar, with the sections on Y times_X V read chartwise; the
canonical morphism Spec(O_{X, x-bar}) -> X is not constructed, since the etale local ring lives
one universe up and its spectrum is not an object of the site, so neither the source's formula
nor its quasi-compact, quasi-separated and quasi-coherent hypotheses appear"]
theorem exists_geometricModuleStalkGerm_modulePushforward (f : Y ⟶ X)
    (z : geometricModuleStalk B S hS X x ((modulePushforward B S hS f).obj G)) :
    ∃ (N : SmallEtaleNeighborhood x) (a : (directImageChartDiagram B S hS f G N.chart).sections),
      geometricModuleStalkGerm B S hS X x ((modulePushforward B S hS f).obj G) N
        ((directImageChartSectionsEquiv B S hS f G N.chart).symm a) = z := by
  obtain ⟨N, s, hs⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x
    ((modulePushforward B S hS f).obj G) z
  refine ⟨N, directImageChartSectionsEquiv B S hS f G N.chart s, ?_⟩
  rw [Equiv.symm_apply_apply]
  exact hs

/-- **Stacks 0AES, the separation half of the colimit form.**  Two sections of the direct image
`f_*G` over the chart of a small étale neighbourhood `N` of `x̄` have the same germ in the
geometric stalk `(f_*G)_{x̄}` exactly when, for some smaller neighbourhood `V`, their chartwise
sections of `G` over the étale scheme charts of `Y` above `Y ×_X V` agree — that is, exactly
when they agree in `Γ(Y ×_X V, p_V^*G)`. -/
@[stacks 0AES "separation half, for the geometric point stalk expressed as the filtered colimit
over the etale neighbourhoods of x-bar, with the sections on Y times_X V read chartwise; the
canonical morphism Spec(O_{X, x-bar}) -> X is not constructed, since the etale local ring lives
one universe up and its spectrum is not an object of the site, so neither the source's formula
nor its quasi-compact, quasi-separated and quasi-coherent hypotheses appear"]
theorem geometricModuleStalkGerm_modulePushforward_eq_iff (f : Y ⟶ X)
    (N : SmallEtaleNeighborhood x)
    (s t : ((modulePushforward B S hS f).obj G).val.obj (op N.chart)) :
    geometricModuleStalkGerm B S hS X x ((modulePushforward B S hS f).obj G) N s =
        geometricModuleStalkGerm B S hS X x ((modulePushforward B S hS f).obj G) N t ↔
      ∃ (M : SmallEtaleNeighborhood x) (g : M ⟶ N), ∀ j,
        directImageChartSection B S hS f G M.chart j
            (((modulePushforward B S hS f).obj G).val.map g.hom.op s) =
          directImageChartSection B S hS f G M.chart j
            (((modulePushforward B S hS f).obj G).val.map g.hom.op t) := by
  refine (geometricModuleStalkGerm_eq_iff B S hS X x
    ((modulePushforward B S hS f).obj G) N s t).trans ⟨?_, ?_⟩
  · rintro ⟨M, g, h⟩
    exact ⟨M, g, fun j ↦ congrArg (directImageChartSection B S hS f G M.chart j) h⟩
  · rintro ⟨M, g, h⟩
    exact ⟨M, g, directImageChartSection_ext B S hS f G M.chart h⟩

end AlgebraicGeometry.Space

end
