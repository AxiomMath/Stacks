module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOfOpenMorphismLift

/-!
# Transporting a morphism of modules on the open complement to a chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals which is cartesian on affine charts, let `U = X ∖ V(ℐ)` be the
open complement `AlgebraicGeometry.Space.idealComplement` and let `𝒢` and `ℱ` be
`𝒪_X`-modules.  A morphism `θ : 𝒢|_U ⟶ ℱ|_U` is a family of maps on the sections over the étale
charts of `U`, and the surjectivity argument for [Stacks, Tag 07UM] has to read it as a family of
maps on the sections over the Zariski opens of the scheme of an étale chart `A` of `X` lying off
the support of the chartwise sheaf of ideals.

This file performs that reading.  Restriction to `U` is restriction along the postcomposition
functor with the *identity* change of scalars, so the sections of `𝒢|_U` over a chart `P` of `U`
are the sections of `𝒢` over `AlgebraicGeometry.Space.pc … P`, on the nose; a chart of `X` which
is identified with such a postcomposition therefore carries a component of `θ`, and the family
`AlgebraicGeometry.Space.idealComplementChart` supplies such an identification for every open
off the support.  Compatibility of the resulting family with restriction is the naturality of
`θ` at the lifted morphism of charts of `U`, which is
`AlgebraicGeometry.Space.pcMap_idealComplementChartHom`.

## Main definitions

* `AlgebraicGeometry.Space.homOnChart`: **a component of `θ` read at a chart of `X` identified
  with the postcomposition of a chart of `U`.**
* `AlgebraicGeometry.Space.complementHomOnChart`: **the per-open family** — the component of `θ`
  at the étale chart of `X` cut out by a Zariski open of the chart's scheme lying off the
  support.

## Main results

* `AlgebraicGeometry.Space.restrictToIdealComplement_obj_val_obj`: the sections of `𝒢|_U` over a
  chart of `U` are the sections of `𝒢` over its postcomposition, by `rfl`.
* `AlgebraicGeometry.Space.homOnChart_rfl`: at the postcomposition itself the component of `θ` is
  `θ` itself, by `rfl`; together with
  `AlgebraicGeometry.Space.homOnChart_naturality` this pins the transport down.
* `AlgebraicGeometry.Space.homOnChart_naturality`: **the transported components commute with
  restriction along any morphism of charts of `X` admitting a lift to the charts of `U`.**  This
  is the naturality of `θ` at the lift.
* `AlgebraicGeometry.Space.complementHomOnChart_naturality`: **the per-open family commutes with
  restriction along the inclusion of the charts cut out by an inclusion of opens off the
  support**, and
  `AlgebraicGeometry.Space.complementHomOnChart_naturality_of_eq` is the same for an arbitrary
  morphism between relabellings of those charts.  This is the compatibility with restriction that
  `AlgebraicGeometry.Scheme.Modules.overHomOfSections` asks for, before the sections of the
  chart restriction are identified with the sections over the comparison charts.

## Implementation notes

**The transport is a substitution, not a comparison map.**
`AlgebraicGeometry.Space.restrictToIdealComplement` is
`AlgebraicGeometry.Space.etaleModulePullback` along `j : U ⟶ X`, that is, a direct image along
the postcomposition functor with the identity morphism of sheaves of rings; so the sections of
`𝒢|_U` over a chart of `U` are *equal* to the sections of `𝒢` over its postcomposition, and
`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj` is `rfl`.  The only content in
`AlgebraicGeometry.Space.homOnChart` is therefore the substitution of the chart of `X` for that
postcomposition, and it is performed by `subst` so that the component at a reflexive
identification is the component of `θ` by `rfl`.

**The morphism of charts and its lift are parameters with an equation.**  Writing the lift's
postcomposition in place would force a definitional check of the chosen lift inside the two
`CategoryTheory.eqToHom`s at every occurrence; taking the morphism `k` of charts of `X` and the
lift `l` separately, with the equation relating them, reduces the naturality statement to
`CategoryTheory.PresheafOfModules.naturality_apply` after two substitutions.

**The relabelling of the charts of `X` is a parameter too.**  The module-level identification of
the sections of the chart restriction is stated at
`AlgebraicGeometry.Space.openChartOfComparison` rather than at
`AlgebraicGeometry.Space.openChart`, and the two are equal but not definitionally so;
`AlgebraicGeometry.Space.complementHomOnChart_naturality_of_eq` therefore takes the relabelled
charts and the morphism between them as parameters with equations, so that a consumer at either
spelling supplies its own equalities.

No hypothesis beyond the one `AlgebraicGeometry.Space.exists_pc_eq_openChart` carries is used —
in particular neither module is assumed quasi-coherent — and no declaration here carries a
`stacks` tag: this is an input to the reduction of Stacks 07UM to an étale chart, not an
assertion of any tag.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)
    (G F : Modules.{u, u} B S hS X.1 X.2)

/-! ### The sections of a restriction to the open complement -/

/-- **The sections of `𝒢|_U` over an étale chart of `U = X ∖ V(ℐ)` are the sections of `𝒢` over
its postcomposition with `j : U ⟶ X`**, as a module over the same ring of regular functions.

Restriction to `U` is a direct image along the postcomposition functor with the identity change
of scalars, so this is `AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`. -/
theorem restrictToIdealComplement_obj_val_obj
    (P : SmallEtale B S hS (idealComplement B S hS X I).1) :
    ((restrictToIdealComplement B S hS X I).obj G).val.obj (op P) =
      G.val.obj (op (pc B S hS X I P)) :=
  etaleModulePullback_obj_val_obj B S hS (idealComplementι B S hS X I)
    (isEtale_idealComplementι B S hS X I) G P

/-! ### A component of `θ` at a chart of `X` -/

variable (θ : (restrictToIdealComplement B S hS X I).obj G ⟶
  (restrictToIdealComplement B S hS X I).obj F)

/-- **A component of `θ : 𝒢|_U ⟶ ℱ|_U` read at a chart of `X`** which is identified with the
postcomposition with `j : U ⟶ X` of a chart `P` of `U`: the sections of `𝒢|_U` over `P` are the
sections of `𝒢` over that postcomposition, so `θ` at `P` is a map of the sections of `𝒢` and `ℱ`
over the chart of `X`. -/
def homOnChart {P : SmallEtale B S hS (idealComplement B S hS X I).1}
    {Q : SmallEtale B S hS X.1} (hP : pc B S hS X I P = Q) :
    G.val.obj (op Q) ⟶ F.val.obj (op Q) := by
  subst hP
  exact θ.val.app (op P)

/-- At the postcomposition itself the component of `θ` is the component of `θ`. -/
theorem homOnChart_rfl (P : SmallEtale B S hS (idealComplement B S hS X I).1) :
    homOnChart B S hS X I G F θ (rfl : pc B S hS X I P = pc B S hS X I P) =
      θ.val.app (op P) := rfl

/-- **The transported components of `θ` commute with restriction along a morphism of charts of
`X` which lifts to the charts of `U = X ∖ V(ℐ)`.**

This is the naturality of `θ` at the lift `l`, which
`AlgebraicGeometry.Space.exists_pcMap_eq` produces for every morphism of charts of `X` between
two postcompositions.  It is the compatibility with restriction that a family of maps on sections
has to have in order to assemble into a morphism of modules. -/
theorem homOnChart_naturality
    {P' P : SmallEtale B S hS (idealComplement B S hS X I).1}
    {Q' Q : SmallEtale B S hS X.1} (hP' : pc B S hS X I P' = Q')
    (hP : pc B S hS X I P = Q) (k : Q' ⟶ Q) (l : P' ⟶ P)
    (hl : pcMap B S hS X I l = eqToHom hP' ≫ k ≫ eqToHom hP.symm)
    (x : G.val.obj (op Q)) :
    homOnChart B S hS X I G F θ hP' (G.val.map k.op x) =
      F.val.map k.op (homOnChart B S hS X I G F θ hP x) := by
  subst hP'
  subst hP
  obtain rfl : k = pcMap B S hS X I l := by
    rw [hl, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact PresheafOfModules.naturality_apply θ.val l.op x

/-! ### The per-open family -/

variable (hI : IsCartesianOnAffineCharts I.toSheafOfModules)

/-- **The per-open family**: the component of `θ : 𝒢|_U ⟶ ℱ|_U` at the étale chart of `X` cut out
by a Zariski open of a chart's scheme lying off the support of the chartwise sheaf of ideals.

The identification of that chart with the postcomposition of a chart of `U` is
`AlgebraicGeometry.Space.pc_idealComplementChart`. -/
def complementHomOnChart (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens)) :
    G.val.obj (op (openChart B S hS X.1 A V)) ⟶ F.val.obj (op (openChart B S hS X.1 A V)) :=
  homOnChart B S hS X I G F θ (pc_idealComplementChart B S hS X I hI A V hV)

/-- **The per-open family commutes with restriction along an arbitrary morphism between
relabellings of the charts cut out by an inclusion of Zariski opens off the support.**

The charts of `X` and the morphism between them are parameters with equations: the module-level
identification of the sections of the chart restriction is stated at
`AlgebraicGeometry.Space.openChartOfComparison`, and a consumer there supplies
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj` as `hQ'` and `hQ` and the
induced morphism of comparison charts as `k`. -/
theorem complementHomOnChart_naturality_of_eq (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens))
    {Q' Q : SmallEtale B S hS X.1} (hQ' : openChart B S hS X.1 A V' = Q')
    (hQ : openChart B S hS X.1 A V = Q) (k : Q' ⟶ Q) (x : G.val.obj (op Q)) :
    homOnChart B S hS X I G F θ
          ((pc_idealComplementChart B S hS X I hI A V' (h.trans hV)).trans hQ')
          (G.val.map k.op x) =
      F.val.map k.op (homOnChart B S hS X I G F θ
        ((pc_idealComplementChart B S hS X I hI A V hV).trans hQ) x) := by
  obtain ⟨l, hl⟩ := exists_pcMap_idealComplementChartHom_eq B S hS X I hI A h hV hQ' hQ k
  exact homOnChart_naturality B S hS X I G F θ _ _ k l hl x

/-- **The per-open family commutes with restriction along the inclusion of the charts cut out by
an inclusion of Zariski opens off the support.**

This is `AlgebraicGeometry.Space.complementHomOnChart_naturality_of_eq` at the identity
relabelling and `AlgebraicGeometry.Space.openChartHomOfLE`, and it is the hypothesis
`AlgebraicGeometry.Scheme.Modules.overHomOfSections` asks for, stated on the sections over the
étale charts rather than over the chart's scheme. -/
theorem complementHomOnChart_naturality (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens))
    (x : G.val.obj (op (openChart B S hS X.1 A V))) :
    complementHomOnChart B S hS X I G F θ hI A V' (h.trans hV)
          (G.val.map (openChartHomOfLE B S hS X.1 A h).op x) =
      F.val.map (openChartHomOfLE B S hS X.1 A h).op
        (complementHomOnChart B S hS X I G F θ hI A V hV x) :=
  complementHomOnChart_naturality_of_eq B S hS X I G F θ hI A h hV rfl rfl
    (openChartHomOfLE B S hS X.1 A h) x

end AlgebraicGeometry.Space

end
