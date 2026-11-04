module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChartTensorByBaseModule
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineTripleOverlap

/-!
# The ring of functions of a base-changed affine chart

Let `D` be the cartesian square of **Stacks 073J**,

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

a square of algebraic spaces over a scheme `S` of a big fppf site `B`, and suppose the two bases
`Y` and `Y'` are affine algebraic spaces.  Then their small étale sites have terminal charts `V₀`
and `V₀'` (`AlgebraicGeometry.Space.exists_isTerminal_isAffine_chart`), and the two coordinate
rings of **Stacks 073K**, part (2) are the rings of regular functions

  `A = Γ(chartScheme V₀, ⊤)`,    `Bᵣ = Γ(chartScheme V₀', ⊤)`

of their schemes, that is `AlgebraicGeometry.Space.baseChartRing` at those charts.

This file takes an étale scheme chart `U` of `X` and produces the chart of `X'` lying over it by
base change along the projection `g'`, and identifies its ring of functions: when `U` is affine,

  `𝒪_{X'}(U ×_X X')  ≅  𝒪_X(U) ⊗_A Bᵣ`,

an isomorphism of `𝒪_X(U)`-algebras.  That ring identification is the chart-wise content of the
second part of Stacks 073K, where the direct image of the pulled-back coefficient is compared
with the coefficient tensored by `Bᵣ` chart by chart.

## Main definitions

* `AlgebraicGeometry.Space.baseChartHom`: the morphism of schemes from an étale chart of `X` to
  the terminal chart of an affine `Y`, attached to a morphism `f : X ⟶ Y`.
* `AlgebraicGeometry.Space.baseChartAlgebra`: the `A`-algebra structure on the functions of a
  chart of `X` given by that morphism.
* `AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChart` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartDiagram`: **the chart of `X'` lying
  over a chart `U` of `X`**, and the commutative diagram of charts over `g'` it forms with `U`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartProjection`: the cartesian projection
  from that chart to `U`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquiv` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquivChart`: **the ring
  identification `𝒪_X(U) ⊗_A Bᵣ ≅ 𝒪_{X'}(U ×_X X')`**, as an algebra isomorphism over `A` and as
  one over `𝒪_X(U)`.

## Main results

* `AlgebraicGeometry.Space.isIso_chartHom_of_isTerminal` and
  `AlgebraicGeometry.Space.isAffine_chartScheme_of_isTerminal`: a terminal étale chart of an
  affine algebraic space has invertible structure morphism and affine scheme.
* `AlgebraicGeometry.Space.relativelyRepresentable_hom_of_isAffineSpace` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.relativelyRepresentable_g'`: a morphism of affine
  algebraic spaces is relatively representable, and so is the projection `g'`, which is what
  makes base change of étale charts along `g'` available.
* `AlgebraicGeometry.Space.BaseChangeDiagram.isPullback_chartScheme_baseChangeChart`: **the
  scheme of the base-changed chart is the fibre product of the scheme of `U` and the scheme of
  `V₀'` over the scheme of `V₀`**.
* `AlgebraicGeometry.Space.BaseChangeDiagram.isAffine_chartScheme_baseChangeChart`: it is affine
  when `U`, `V₀` and `V₀'` are.
* `AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquiv_tmul_one` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquiv_one_tmul`: the two
  commuting triangles — the identification carries `b ⊗ 1` to the pullback of `b` along the
  projection to `U`, and `1 ⊗ c` to the pullback of `c` along the structure morphism to `V₀'`.

## Implementation notes

*Where the base-changed chart comes from.*  `Y` and `Y'` are affine, hence representable, so `g`
is a morphism of representable presheaves and is relatively representable; relative
representability is stable under base change (**Stacks 02WB**), so the projection `g'` is
relatively representable too, and base change of étale scheme charts along it is **Stacks 03G2**,
part (4), `AlgebraicGeometry.Space.smallBaseChange`.  The chart produced here is its value at
`U`, and the chart diagram is `AlgebraicGeometry.Space.baseChangeChartDiagram`.

*Why the base-changed chart is the fibre product over the terminal charts.*  Pasting the
representability square of `g'` at `U` below the cartesian square of `D` gives a square of
presheaves whose cospan is the two structure morphisms to `Y`.  Its two lower corners are `Y'`
and `Y`, which are not representable presheaves but are isomorphic to ones, the isomorphisms
being the structure morphisms of the terminal charts `V₀'` and `V₀`;
`CategoryTheory.Limits.IsPullback.of_iso` transports the square along them, and the result has
all four corners representable, so it descends through the fully faithful Yoneda embedding to the
big fppf category over `S` and from there to schemes.  That is the square the affineness and the
tensor identification are read off from: `AlgebraicGeometry.IsAffine.of_isIso` for the first and
`AlgebraicGeometry.algEquivTensorAppTopOfIsPullback` for the second.

*The invertibility of the structure morphism of a terminal chart is an input of the
construction.*  It is `AlgebraicGeometry.Space.isIso_chartHom_of_isTerminal`, proved from the
chart that `AlgebraicGeometry.Space.IsAffineSpace` provides: that chart is terminal and its
structure morphism is invertible, and two terminal objects of the small étale site are uniquely
isomorphic.  The constructions below take the invertibility and the affineness of the chart
scheme as instance arguments, so they apply equally to any chart presenting the base as a scheme.

*The algebra structures are introduced by `letI`.*  Each of them depends on a morphism of
algebraic spaces and on a chart, so none can be an instance; the statements introduce them in the
same order in which the proofs do, which is what makes the two agree definitionally.

*The spellings of the corners.*  Every statement names the base-changed chart through
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChart` and its projection through
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChartProjection`, rather than through the
representable pullback of `CategoryTheory.Functor.relativelyRepresentable`.  The two spellings
are definitionally equal, but a goal mixing them is not type-correct at `implicit` transparency,
so `rw` refuses it; naming one spelling everywhere keeps the rewrites available.

No declaration here carries a `stacks` tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 02WB](https://stacks.math.columbia.edu/tag/02WB)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Terminal charts of an affine algebraic space -/

/-- The unique isomorphism, in the small étale site, between the chart that an isomorphism of the
presheaf with a representable one defines and a terminal étale chart. -/
def isoEtaleChartOfIsTerminal {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    (e : F ≅ yoneda.obj T) {V : SmallEtale B S hS F} (hV : IsTerminal V) :
    etaleChartOfIso B S hS e ≅ V where
  hom := hV.from _
  inv := (isTerminalEtaleChartOfIso B S hS e).from V
  hom_inv_id := (isTerminalEtaleChartOfIso B S hS e).hom_ext _ _
  inv_hom_id := hV.hom_ext _ _

/-- **The structure morphism of a terminal étale chart of an affine algebraic space is an
isomorphism.**

The chart `AlgebraicGeometry.Space.etaleChartOfIso` of the isomorphism with a representable
presheaf has invertible structure morphism and is terminal, so it is uniquely isomorphic to the
given chart, and a morphism of charts commutes with the two structure morphisms. -/
theorem isIso_chartHom_of_isTerminal {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : SmallEtale B S hS F} (hV : IsTerminal V) (hF : IsAffineSpace B S hS F) :
    IsIso V.obj.hom := by
  obtain ⟨T, -, ⟨e⟩⟩ := hF
  have hw : yoneda.map ((isoEtaleChartOfIsTerminal B S hS e hV).hom.hom.left) ≫ V.obj.hom =
      e.inv := CostructuredArrow.w (isoEtaleChartOfIsTerminal B S hS e hV).hom.hom
  have : IsIso ((isoEtaleChartOfIsTerminal B S hS e hV).hom.hom.left) :=
    ⟨(isoEtaleChartOfIsTerminal B S hS e hV).inv.hom.left,
      congrArg (fun k => k.hom.left) (isoEtaleChartOfIsTerminal B S hS e hV).hom_inv_id,
      congrArg (fun k => k.hom.left) (isoEtaleChartOfIsTerminal B S hS e hV).inv_hom_id⟩
  have : IsIso (yoneda.map ((isoEtaleChartOfIsTerminal B S hS e hV).hom.hom.left) ≫
      V.obj.hom) := by
    rw [hw]
    exact e.isIso_inv
  exact IsIso.of_isIso_comp_left
    (yoneda.map ((isoEtaleChartOfIsTerminal B S hS e hV).hom.hom.left)) V.obj.hom

/-- **The scheme of a terminal étale chart of an affine algebraic space is affine.**

The chart is isomorphic, in the small étale site, to the chart of the isomorphism with a
representable presheaf, whose scheme is the affine scheme that representable comes with. -/
theorem isAffine_chartScheme_of_isTerminal {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : SmallEtale B S hS F} (hV : IsTerminal V) (hF : IsAffineSpace B S hS F) :
    IsAffine (chartScheme V) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  have : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
    (etaleChartOfIso B S hS e)) := hT
  exact IsAffine.of_isIso
    ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).mapIso
      (isoEtaleChartOfIsTerminal B S hS e hV)).inv

/-- **A morphism of affine algebraic spaces is relatively representable.**

Both presheaves are isomorphic to representable ones, so the morphism factors as an isomorphism,
the Yoneda image of a morphism of the big fppf category over `S`, and an isomorphism; relative
representability contains the isomorphisms, holds for a Yoneda image by **Stacks 02W9**, and is
stable under composition. -/
theorem relativelyRepresentable_hom_of_isAffineSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hX : IsAffineSpace B S hS X.1) (hY : IsAffineSpace B S hS Y.1) :
    yoneda.relativelyRepresentable f.hom := by
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  obtain ⟨T, -, ⟨eX⟩⟩ := hX
  obtain ⟨T', -, ⟨eY⟩⟩ := hY
  have h : f.hom =
      eX.hom ≫ yoneda.map (yoneda.preimage (eX.inv ≫ f.hom ≫ eY.hom)) ≫ eY.inv := by
    rw [Functor.map_preimage]
    simp
  rw [h]
  exact MorphismProperty.comp_mem _ _ _ (Functor.relativelyRepresentable.of_isIso yoneda _)
    (MorphismProperty.comp_mem _ _ _ (Functor.relativelyRepresentable.map yoneda _)
      (Functor.relativelyRepresentable.of_isIso yoneda _))

/-! ### The structure morphism of a chart over an affine base -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The morphism of the big fppf category over `S` from an étale chart `U` of `X` to a chart `V₀`
of `Y` presenting `Y` as a scheme, attached to a morphism `f : X ⟶ Y` of algebraic spaces.

It is the unique morphism whose Yoneda image is the structure morphism of `U` followed by `f` and
by the inverse of the structure morphism of `V₀`. -/
def baseChartHom (f : X ⟶ Y) (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom]
    (U : SmallEtale B S hS X.1) :
    (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V₀ :=
  yoneda.preimage (U.obj.hom ≫ f.hom ≫ CategoryTheory.inv V₀.obj.hom)

/-- The Yoneda image of `AlgebraicGeometry.Space.baseChartHom`. -/
theorem yoneda_map_baseChartHom (f : X ⟶ Y) (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom]
    (U : SmallEtale B S hS X.1) :
    yoneda.map (baseChartHom B S hS f V₀ U) =
      U.obj.hom ≫ f.hom ≫ CategoryTheory.inv V₀.obj.hom :=
  Functor.map_preimage _ _

/-- `AlgebraicGeometry.Space.baseChartHom` lies over `f`: its Yoneda image followed by the
structure morphism of `V₀` is the structure morphism of `U` followed by `f`. -/
theorem yoneda_map_baseChartHom_comp (f : X ⟶ Y) (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom]
    (U : SmallEtale B S hS X.1) :
    yoneda.map (baseChartHom B S hS f V₀ U) ≫ V₀.obj.hom = U.obj.hom ≫ f.hom := by
  rw [yoneda_map_baseChartHom]
  simp

/-- The algebra structure on the ring of functions of an étale chart `U` of `X` over the
coordinate ring of an affine base, given by `AlgebraicGeometry.Space.baseChartHom`.

Not an instance: it depends on the morphism `f` and on the chart `V₀`. -/
@[instance_reducible]
def baseChartAlgebra (f : X ⟶ Y) (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom]
    (U : SmallEtale B S hS X.1) :
    Algebra (baseChartRing B S hS Y V₀) (Γ(chartScheme U, ⊤) : Type u) :=
  ((BigFppfOver.toScheme B S hS).map (baseChartHom B S hS f V₀ U)).appTop.hom.toAlgebra

namespace BaseChangeDiagram

variable {B S hS}

/-- **The projection of the cartesian square of Stacks 073J with affine bases is relatively
representable.**

The morphism `g` of the lower edge is relatively representable because its source and target are
affine, and `g'` is its base change along `f`; relative representability is stable under base
change, which is **Stacks 02WB**. -/
theorem relativelyRepresentable_g' (D : BaseChangeDiagram B S hS)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) :
    yoneda.relativelyRepresentable D.g'.hom :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS D.isPullback).flip
    (relativelyRepresentable_hom_of_isAffineSpace B S hS D.g hY' hY)

variable (D : BaseChangeDiagram B S hS) (hg' : yoneda.relativelyRepresentable D.g'.hom)
  (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]
  (U : SmallEtale B S hS D.X.1)

/-- **The chart of `X'` lying over a chart `U` of `X`**: the base change of `U` along the
projection `g'`, which is an étale chart by **Stacks 03G2**, part (4). -/
def baseChangeChart : SmallEtale B S hS D.X'.1 :=
  (smallBaseChange B S hS D.g' hg').obj U

/-- The cartesian projection from the base-changed chart to `U`, as a morphism of the big fppf
category over `S`. -/
def baseChangeChartProjection :
    (SmallEtale.toOver B S hS D.X'.1).obj (D.baseChangeChart hg' U) ⟶
      (SmallEtale.toOver B S hS D.X.1).obj U :=
  hg'.snd U.obj.hom

/-- **The commutative diagram of étale charts over the projection `g'`** formed by a chart `U` of
`X` and the chart of `X'` lying over it. -/
def baseChangeChartDiagram : ChartDiagram B S hS D.X'.1 D.X.1 D.g'.hom where
  U := D.baseChangeChart hg' U
  V := U
  g := D.baseChangeChartProjection hg' U
  comm := hg'.w U.obj.hom

/-- The chart of `X` of the diagram is `U` itself. -/
theorem baseChangeChartDiagram_V : (D.baseChangeChartDiagram hg' U).V = U := rfl

/-- The chart of `X'` of the diagram is
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeChart`. -/
theorem baseChangeChartDiagram_U :
    (D.baseChangeChartDiagram hg' U).U = D.baseChangeChart hg' U := rfl

/-- The vertical morphism of the diagram is the cartesian projection to `U`. -/
theorem baseChangeChartDiagram_g :
    (D.baseChangeChartDiagram hg' U).g = D.baseChangeChartProjection hg' U := rfl

/-- The square of presheaves exhibiting the base-changed chart as the fibre product of the chart
`U` and the base `Y'` over `Y`: the representability square of `g'` at `U` pasted below the
cartesian square of the diagram. -/
theorem isPullback_yoneda_baseChangeChart :
    IsPullback (yoneda.map (D.baseChangeChartProjection hg' U))
      ((D.baseChangeChart hg' U).obj.hom ≫ D.f'.hom) (U.obj.hom ≫ D.f.hom) D.g.hom :=
  (hg'.isPullback U.obj.hom).flip.paste_vert
    (AlgebraicSpaces.isPullback_hom B S hS D.isPullback)

/-- **The base-changed chart is the fibre product of `U` and the terminal chart `V₀'` of `Y'` over
the terminal chart `V₀` of `Y`**, as a square of the big fppf category over `S`.

The square of presheaves is transported along the structure morphisms of `V₀` and `V₀'`, which
are isomorphisms, and then descends through the fully faithful Yoneda embedding. -/
theorem isPullback_site_baseChangeChart :
    IsPullback (D.baseChangeChartProjection hg' U)
      (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U))
      (baseChartHom B S hS D.f V₀ U) (baseChartHom B S hS D.g V₀ V₀') := by
  refine IsPullback.of_map_of_faithful yoneda ?_
  refine (D.isPullback_yoneda_baseChangeChart hg' U).of_iso (Iso.refl _) (Iso.refl _)
    (asIso V₀'.obj.hom).symm (asIso V₀.obj.hom).symm (by simp) ?_ ?_ ?_
  · rw [yoneda_map_baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U)]
    simp
  · rw [yoneda_map_baseChartHom B S hS D.f V₀ U]
    simp
  · rw [yoneda_map_baseChartHom B S hS D.g V₀ V₀']
    simp

/-- **The same fibre product square, read in schemes.** -/
theorem isPullback_chartScheme_baseChangeChart :
    IsPullback ((BigFppfOver.toScheme B S hS).map (D.baseChangeChartProjection hg' U))
      ((BigFppfOver.toScheme B S hS).map
        (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U)))
      ((BigFppfOver.toScheme B S hS).map (baseChartHom B S hS D.f V₀ U))
      ((BigFppfOver.toScheme B S hS).map (baseChartHom B S hS D.g V₀ V₀')) :=
  (D.isPullback_site_baseChangeChart hg' V₀ V₀' U).map (BigFppfOver.toScheme B S hS)

/-- **The scheme of the base-changed chart of an affine chart is affine**, being the fibre product
of two affine schemes over an affine one. -/
theorem isAffine_chartScheme_baseChangeChart [IsAffine (chartScheme V₀)]
    [IsAffine (chartScheme V₀')] [IsAffine (chartScheme U)] :
    IsAffine (chartScheme (D.baseChangeChart hg' U)) := by
  exact IsAffine.of_isIso
    (D.isPullback_chartScheme_baseChangeChart hg' V₀ V₀' U).isoPullback.hom

/-- The algebra structure on the functions of the base-changed chart over the coordinate ring of
`Y`, given by the composite of the cartesian projection to `U` with the structure morphism of `U`
over the terminal chart of `Y`.

Not an instance: it depends on the square, on the chart and on the representability witness. -/
@[instance_reducible]
def baseChangeChartAlgebra :
    Algebra (baseChartRing B S hS D.Y V₀)
      (Γ(chartScheme (D.baseChangeChart hg' U), ⊤) : Type u) :=
  ((BigFppfOver.toScheme B S hS).map
    (D.baseChangeChartProjection hg' U ≫ baseChartHom B S hS D.f V₀ U)).appTop.hom.toAlgebra

/-- The algebra structure on the functions of the base-changed chart over the functions of `U`,
given by the cartesian projection.

Not an instance: it depends on the square, on the chart and on the representability witness. -/
@[instance_reducible]
def baseChangeChartChartAlgebra :
    Algebra (Γ(chartScheme U, ⊤) : Type u)
      (Γ(chartScheme (D.baseChangeChart hg' U), ⊤) : Type u) :=
  ((BigFppfOver.toScheme B S hS).map
    (D.baseChangeChartProjection hg' U)).appTop.hom.toAlgebra

/-- Pulling a function on the terminal chart of `Y` back to `U` and then to the base-changed
chart is pulling it back along the composite. -/
theorem appTop_baseChangeChart_projection (a : baseChartRing B S hS D.Y V₀) :
    ((BigFppfOver.toScheme B S hS).map (D.baseChangeChartProjection hg' U)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map
          (baseChartHom B S hS D.f V₀ U)).appTop.hom a) =
      ((BigFppfOver.toScheme B S hS).map
        (D.baseChangeChartProjection hg' U ≫
          baseChartHom B S hS D.f V₀ U)).appTop.hom a := by
  rw [(BigFppfOver.toScheme B S hS).map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Pulling a function on the terminal chart of `Y` back to the terminal chart of `Y'` and then to
the base-changed chart agrees with pulling it back through `U`: the two ways round the fibre
product square. -/
theorem appTop_baseChangeChart_base (a : baseChartRing B S hS D.Y V₀) :
    ((BigFppfOver.toScheme B S hS).map
          (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U))).appTop.hom
        (((BigFppfOver.toScheme B S hS).map
          (baseChartHom B S hS D.g V₀ V₀')).appTop.hom a) =
      ((BigFppfOver.toScheme B S hS).map
        (D.baseChangeChartProjection hg' U ≫
          baseChartHom B S hS D.f V₀ U)).appTop.hom a := by
  rw [(D.isPullback_site_baseChangeChart hg' V₀ V₀' U).w,
    (BigFppfOver.toScheme B S hS).map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- **The ring of functions of the base-changed chart of an affine chart is the tensor product
`𝒪_X(U) ⊗_A Bᵣ`** of the functions of the chart and the coordinate ring of `Y'` over the
coordinate ring of `Y`, as an algebra over the coordinate ring of `Y`.

This is `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback` at the fibre product square
`AlgebraicGeometry.Space.BaseChangeDiagram.isPullback_chartScheme_baseChangeChart`. -/
def chartRingTensorAlgEquiv [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    [IsAffine (chartScheme U)] :
    letI := baseChartAlgebra B S hS D.f V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.baseChangeChartAlgebra hg' V₀ U
    (Γ(chartScheme U, ⊤) : Type u) ⊗[baseChartRing B S hS D.Y V₀]
        (baseChartRing B S hS D.Y' V₀') ≃ₐ[baseChartRing B S hS D.Y V₀]
      (Γ(chartScheme (D.baseChangeChart hg' U), ⊤) : Type u) := by
  letI := baseChartAlgebra B S hS D.f V₀ U
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  letI := D.baseChangeChartAlgebra hg' V₀ U
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS D.Y.1).obj V₀)) := ‹IsAffine (chartScheme V₀)›
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS D.Y'.1).obj V₀')) := ‹IsAffine (chartScheme V₀')›
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS D.X.1).obj U)) := ‹IsAffine (chartScheme U)›
  exact AlgebraicGeometry.algEquivTensorAppTopOfIsPullback
    (D.isPullback_chartScheme_baseChangeChart hg' V₀ V₀' U) rfl rfl
    (D.appTop_baseChangeChart_projection hg' V₀ U)
    (D.appTop_baseChangeChart_base hg' V₀ V₀' U)

/-- The value of the identification on a pure tensor: the product of the two pullbacks, along the
cartesian projection to `U` and along the structure morphism to the terminal chart of `Y'`. -/
theorem chartRingTensorAlgEquiv_tmul [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    [IsAffine (chartScheme U)] (b : Γ(chartScheme U, ⊤))
    (c : baseChartRing B S hS D.Y' V₀') :
    letI := baseChartAlgebra B S hS D.f V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.baseChangeChartAlgebra hg' V₀ U
    D.chartRingTensorAlgEquiv hg' V₀ V₀' U (b ⊗ₜ[baseChartRing B S hS D.Y V₀] c) =
      ((BigFppfOver.toScheme B S hS).map
          (D.baseChangeChartProjection hg' U)).appTop.hom b *
        ((BigFppfOver.toScheme B S hS).map
          (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U))).appTop.hom c := by
  let := baseChartAlgebra B S hS D.f V₀ U
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.baseChangeChartAlgebra hg' V₀ U
  exact AlgebraicGeometry.algEquivTensorAppTopOfIsPullback_tmul
    (D.isPullback_chartScheme_baseChangeChart hg' V₀ V₀' U) rfl rfl
    (D.appTop_baseChangeChart_projection hg' V₀ U)
    (D.appTop_baseChangeChart_base hg' V₀ V₀' U) b c

/-- **The first commuting triangle**: the identification carries `b ⊗ 1` to the pullback of `b`
along the cartesian projection to `U`. -/
theorem chartRingTensorAlgEquiv_tmul_one [IsAffine (chartScheme V₀)]
    [IsAffine (chartScheme V₀')] [IsAffine (chartScheme U)] (b : Γ(chartScheme U, ⊤)) :
    letI := baseChartAlgebra B S hS D.f V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.baseChangeChartAlgebra hg' V₀ U
    D.chartRingTensorAlgEquiv hg' V₀ V₀' U (b ⊗ₜ[baseChartRing B S hS D.Y V₀] 1) =
      ((BigFppfOver.toScheme B S hS).map
        (D.baseChangeChartProjection hg' U)).appTop.hom b := by
  let := baseChartAlgebra B S hS D.f V₀ U
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.baseChangeChartAlgebra hg' V₀ U
  rw [D.chartRingTensorAlgEquiv_tmul hg' V₀ V₀' U b 1, map_one, mul_one]

/-- **The second commuting triangle**: the identification carries `1 ⊗ c` to the pullback of `c`
along the structure morphism of the base-changed chart over the terminal chart of `Y'`. -/
theorem chartRingTensorAlgEquiv_one_tmul [IsAffine (chartScheme V₀)]
    [IsAffine (chartScheme V₀')] [IsAffine (chartScheme U)]
    (c : baseChartRing B S hS D.Y' V₀') :
    letI := baseChartAlgebra B S hS D.f V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.baseChangeChartAlgebra hg' V₀ U
    D.chartRingTensorAlgEquiv hg' V₀ V₀' U (1 ⊗ₜ[baseChartRing B S hS D.Y V₀] c) =
      ((BigFppfOver.toScheme B S hS).map
        (baseChartHom B S hS D.f' V₀' (D.baseChangeChart hg' U))).appTop.hom c := by
  let := baseChartAlgebra B S hS D.f V₀ U
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.baseChangeChartAlgebra hg' V₀ U
  rw [D.chartRingTensorAlgEquiv_tmul hg' V₀ V₀' U 1 c, map_one, one_mul]

/-- **The ring identification as an isomorphism of `𝒪_X(U)`-algebras**, for the algebra structure
on the functions of the base-changed chart given by the cartesian projection to `U`.

The compatibility is the first commuting triangle,
`AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorAlgEquiv_tmul_one`. -/
def chartRingTensorAlgEquivChart [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    [IsAffine (chartScheme U)] :
    letI := baseChartAlgebra B S hS D.f V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.baseChangeChartChartAlgebra hg' U
    (Γ(chartScheme U, ⊤) : Type u) ⊗[baseChartRing B S hS D.Y V₀]
        (baseChartRing B S hS D.Y' V₀') ≃ₐ[Γ(chartScheme U, ⊤)]
      (Γ(chartScheme (D.baseChangeChart hg' U), ⊤) : Type u) := by
  letI := baseChartAlgebra B S hS D.f V₀ U
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  letI := D.baseChangeChartAlgebra hg' V₀ U
  letI := D.baseChangeChartChartAlgebra hg' U
  refine AlgEquiv.ofRingEquiv (f := (D.chartRingTensorAlgEquiv hg' V₀ V₀' U).toRingEquiv)
    fun b => ?_
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp only [Algebra.algebraMap_self_apply]
  exact D.chartRingTensorAlgEquiv_tmul_one hg' V₀ V₀' U b

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
