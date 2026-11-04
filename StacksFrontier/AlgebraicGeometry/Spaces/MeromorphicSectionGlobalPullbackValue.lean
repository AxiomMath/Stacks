module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullback

/-!
# The value of the global pullback of meromorphic sections over an étale chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules on the
small étale site of `Y`.  The global map

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

of Stacks 0ENC, part (1) — `AlgebraicGeometry.Space.pullbackMeromorphicSection` — is the
chartwise rule `m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` carried along three identifications, and nothing about
its *value* is visible from that construction.  This file computes it: over a commuting square
of étale charts `U` of `X` above `V` of `Y`, if the section is the image of a meromorphic
section `t` of `M ⊗_{𝒪_Y} 𝒦_Y` over `V`, then its pullback is over `U` the image of the
chartwise pullback of `t`.

A general meromorphic section is only *locally* of that form — the sheaf `𝒦(M)` of Stacks 0EN5
is a sheafification — so the hypothesis on `V` is what makes the statement a formula and not a
definition; it is the shape in which a local computation on `X` is reduced to one on `Y`.

## Main definitions

* `AlgebraicGeometry.Space.toMeromorphicSectionSheaf` is the sheafification map of Stacks 0EN5
  over an étale chart, from the meromorphic sections `M(V) ⊗_{𝒪_Y(V)} 𝒦_Y(V)` of
  `AlgebraicGeometry.Space.meromorphicSectionModule` to the sections of the sheaf `𝒦(M)`.

## Main results

* `AlgebraicGeometry.Space.meromorphicSectionSheafDescendedHom_restrict`: the descended
  morphism of Stacks 03G4 on a section over an étale chart `U` of `X` above the cartesian base
  change of a chart `V` of `Y` is the chartwise rule of the diagram that arrow determines.
* `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval`: **the global pullback map over a
  diagram of étale charts.**

## Implementation notes

The three identifications of `AlgebraicGeometry.Space.pullbackMeromorphicSection` are undone one
at a time: `AlgebraicGeometry.Space.equivSectionsSpacesDirectImage_val` turns the global
sections of the direct image into restriction along the arrow into the cartesian base change
that the diagram of charts determines
(`AlgebraicGeometry.Space.baseChangeArrowOfChartDiagram`),
`AlgebraicGeometry.Space.sheafifyForgetHomEquiv_symm_comp` says the extension over the
sheafification restricts to the descended morphism — which is where the hypothesis that the
section comes from `M ⊗_{𝒪_Y} 𝒦_Y` over `V` is used — and
`AlgebraicGeometry.Space.meromorphicSectionSheafDescendedHom_restrict` evaluates that morphism.
The presentation of the sheaf on `X` as the restriction of a spaces-étale sheaf enters twice,
once in each direction, and cancels.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sheafification map of Stacks 0EN5 over an étale chart.**  A meromorphic section of a
sheaf of `𝒪_F`-modules `M` over an étale scheme chart `V`, that is an element of
`M(V) ⊗_{𝒪_F(V)} 𝒦_F(V)`, read as a section of the sheaf `𝒦_F(M)` over `V`. -/
noncomputable def toMeromorphicSectionSheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F) :
    (meromorphicSectionModule B S hS F hF M).obj (op V) →
      (meromorphicSectionSheaf.{u, u} B S hS F hF M).val.obj (op V) := fun t ↦
  (toSheafify (SmallEtale.topology B S hS F)
    (meromorphicSectionModuleUp B S hS F hF M)).app (op V) (ULift.up t)

section Value

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
  (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- **The descended morphism of the chartwise rule on an étale chart above a cartesian base
change.**  The morphism of presheaves
`AlgebraicGeometry.Space.meromorphicSectionSheafDescendedHom` on a section over an étale scheme
chart `V` of `Y`, restricted to an étale scheme chart `U` of `X` above `X ×_Y V`, is the
chartwise rule of the diagram of charts that arrow determines, followed by the presentation of
the sheaf on `X`.

This is `AlgebraicGeometry.Space.descendedSection_restrict`, exactly as
`AlgebraicGeometry.Space.meromorphicSectionsDescendedHom_restrict` is over the presheaf of
sectionwise localizations. -/
theorem meromorphicSectionSheafDescendedHom_restrict
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (i : G ≅ (comparisonRestriction B S hS X).obj H)
    (α : meromorphicSectionModuleSetUp B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) ⟶ G.obj)
    (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V)
    (s : (meromorphicSectionModuleSetUp B S hS Y.1 Y.2 M).obj (op V)) :
    H.obj.map k.op
        ((meromorphicSectionSheafDescendedHom B S hS f M hf G H i α).app (op V) s) =
      i.hom.hom.app (op U) (α.app (op U) (ULift.up
        (chartPullbackMeromorphicSectionsSheaf B S hS f M hf
          (chartDiagramOfBaseChangeArrow B S hS f U V k) s.down))) :=
  descendedSection_restrict B S hS f G _ H i
    (FMap.compSource B S hS f (fmapMeromorphicSectionsSheafUp B S hS f M hf) α) U V k s

/-- **The global pullback map of Stacks 0ENC, part (1) over a pair of étale charts.**  Let `U`
be an étale scheme chart of `X` above the cartesian base change `X ×_Y V` of an étale scheme
chart `V` of `Y`, and let the meromorphic section `s` of `M` be, over `V`, the image of a
meromorphic section `t` of `M ⊗_{𝒪_Y} 𝒦_Y` over `V`.  Then the pullback `f^*s` is, over `U`,
the image of the chartwise pullback
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf` of `t` along the diagram of
charts that the arrow `U ⟶ X ×_Y V` determines:

`(f^*s)|_U = (m ⊗ a ↦ (f^*m) ⊗ (f^♯a)) (t)`.

Every meromorphic section is locally of this shape, the sheaf `𝒦(M)` of Stacks 0EN5 being a
sheafification, so this computes the global map of part (1) wherever it can be computed. -/
theorem pullbackMeromorphicSection_eval
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V)
    (t : (meromorphicSectionModule B S hS Y.1 Y.2 M).obj (op V))
    (ht : s.eval (op V) = toMeromorphicSectionSheaf B S hS Y.1 Y.2 M V t) :
    (pullbackMeromorphicSection B S hS f M hf s).eval (op U) =
      toMeromorphicSectionSheaf B S hS X.1 X.2 ((modulePullback B S hS f).obj M) U
        (chartPullbackMeromorphicSectionsSheaf B S hS f M hf
          (chartDiagramOfBaseChangeArrow B S hS f U V k) t) := by
  set GX := meromorphicSectionSheafSet B S hS X.1 X.2 ((modulePullback B S hS f).obj M)
  set H := (comparisonRestriction B S hS X).objPreimage GX
  set i := ((comparisonRestriction B S hS X).objObjPreimageIso GX).symm
  set α : meromorphicSectionModuleSetUp B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) ⟶ GX.obj :=
    Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS X.1)
      (meromorphicSectionModuleUp B S hS X.1 X.2 ((modulePullback B S hS f).obj M)))
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  set Ψ := (sheafifyForgetHomEquiv B S hS Y.1
      (meromorphicSectionModuleUp B S hS Y.1 Y.2 M)
      ((spacesDirectImageRestriction B S hS f).obj H)).symm
    (meromorphicSectionSheafDescendedHom B S hS f M hf GX H i α)
  have hstep : (pullbackMeromorphicSection B S hS f M hf s).eval (op U) =
      i.inv.hom.app (op U)
        ((equivSectionsSpacesDirectImage B S hS f H
          (((Functor.sectionsFunctor _).map Ψ) s)).val (op U)) := rfl
  have hval := equivSectionsSpacesDirectImage_val B S hS f H
    (((Functor.sectionsFunctor _).map Ψ) s) U V k
  have hσ : (((Functor.sectionsFunctor _).map Ψ) s).val (op V) =
      Ψ.app (op V) (s.eval (op V)) := rfl
  have hΨt : Ψ.app (op V) (toMeromorphicSectionSheaf B S hS Y.1 Y.2 M V t) =
      (meromorphicSectionSheafDescendedHom B S hS f M hf GX H i α).app (op V)
        (ULift.up t) :=
    congrArg
      (fun φ : meromorphicSectionModuleSetUp B S hS Y.1 Y.2 M ⟶
          ((spacesDirectImageRestriction B S hS f).obj H).obj ↦ φ.app (op V) (ULift.up t))
      (sheafifyForgetHomEquiv_symm_comp B S hS Y.1
        (meromorphicSectionModuleUp B S hS Y.1 Y.2 M)
        ((spacesDirectImageRestriction B S hS f).obj H)
        (meromorphicSectionSheafDescendedHom B S hS f M hf GX H i α))
  have hres := meromorphicSectionSheafDescendedHom_restrict B S hS f M hf GX H i α
    U V k (ULift.up t)
  have hii : ∀ z : GX.obj.obj (op U),
      i.inv.hom.app (op U) (i.hom.hom.app (op U) z) = z := fun z ↦
    congrArg (fun φ : GX ⟶ GX ↦ φ.hom.app (op U) z) i.hom_inv_id
  rw [hstep, hval, hσ, ht, hΨt, hres, hii]
  rfl

/-- The chartwise pullback of meromorphic sections depends on the vertical morphism of a diagram
of étale charts and not on the proof that the diagram commutes. -/
theorem chartPullbackMeromorphicSectionsSheaf_congr
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {g g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    {hc : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom}
    {hc' : U.1.hom ≫ f.hom = yoneda.map g' ≫ V.1.hom} (hg : g = g')
    (t : (meromorphicSectionModule B S hS Y.1 Y.2 M).obj (op V)) :
    chartPullbackMeromorphicSectionsSheaf B S hS f M hf ⟨U, V, g, hc⟩ t =
      chartPullbackMeromorphicSectionsSheaf B S hS f M hf ⟨U, V, g', hc'⟩ t := by
  cases hg
  rfl

/-- **The global pullback map of Stacks 0ENC, part (1) over a diagram of étale charts.**  Let
`d` be a commuting square of étale scheme charts, `U` of `X` above `V` of `Y`, and let the
meromorphic section `s` of `M` be, over `V`, the image of a meromorphic section `t` of
`M ⊗_{𝒪_Y} 𝒦_Y` over `V`.  Then the pullback `f^*s` is, over `U`, the image of the chartwise
pullback `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf` of `t` along `d`.

This is `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval` at the arrow into the
cartesian base change that `d` determines, the two constructions being mutually inverse
(`AlgebraicGeometry.Space.chartDiagramOfBaseChangeArrow_baseChangeArrow`). -/
theorem pullbackMeromorphicSection_eval_chartDiagram
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (t : (meromorphicSectionModule B S hS Y.1 Y.2 M).obj (op d.V))
    (ht : s.eval (op d.V) = toMeromorphicSectionSheaf B S hS Y.1 Y.2 M d.V t) :
    (pullbackMeromorphicSection B S hS f M hf s).eval (op d.U) =
      toMeromorphicSectionSheaf B S hS X.1 X.2 ((modulePullback B S hS f).obj M) d.U
        (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d t) := by
  obtain ⟨U, V, g, hc⟩ := d
  refine (pullbackMeromorphicSection_eval B S hS f M hf s U V
    (baseChangeArrowOfChartDiagram B S hS f ⟨U, V, g, hc⟩) t ht).trans
    (congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) U) ?_)
  exact chartPullbackMeromorphicSectionsSheaf_congr B S hS f M hf
    (chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f ⟨U, V, g, hc⟩) t

end Value

end AlgebraicGeometry.Space

end
