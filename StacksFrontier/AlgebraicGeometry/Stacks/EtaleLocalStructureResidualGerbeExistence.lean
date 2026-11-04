module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChartFibreRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChartPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChartRelationSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureResidualGerbeChart

/-!
# An étale neighbourhood preserving the residual gerbe: Stacks 0DU5

**Stacks 0DU5.** Let `𝒳` be an algebraic stack over `S` which is quasi-DM (Stacks 050D) with
separated diagonal `Δ_{𝒳/S}` (Stacks 04XB), and let `x ∈ |𝒳|` be a point which can be represented
by a quasi-compact morphism `Spec k ⟶ 𝒳`. Then there is a 1-morphism of algebraic stacks
`g : 𝒰 ⟶ 𝒳` with

1. a point `v ∈ |𝒰|` mapping to `x` such that `g` induces an isomorphism between the residual
   gerbes at `v` and `x`,
2. `g` representable by algebraic spaces and étale,
3. `𝒰 = [U/R]` for a groupoid scheme `(U, R, s, t, c)` with `U` and `R` affine and `s`, `t`
   finite, flat and locally of finite presentation.

The three clauses are
`AlgebraicGeometry.Stack.exists_etale_quotientStack_residualGerbeMap_of_compactSpace_targetFibre`,
whose only input beyond the hypotheses of the source is a quotient chart of `𝒳` through `x` whose
target map has quasi-compact fibre over the chart point. This module produces that input, which
is the whole of the source's own proof before the strong splitting of Stacks 04RZ.

## The argument

The source says "the first part of the proof is **exactly** the same as the first part of the
proof of Lemma 0DU3": an affine chart `U ⟶ 𝒳` through `x`, flat, locally of finite presentation
and locally quasi-finite (**Stacks 06MF**), made surjective by replacing `𝒳` with the open
substack `𝒳'` of its image (**Stacks 04XL**, **06FJ**), and then the quotient chart `[U/R] ⟶ 𝒳'`
of **Stacks 04WY** with `R = U ×_{𝒳'} U`.

What the fibre step then needs, and what a
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid` does not record, is that the arrow
scheme of the quotient chart *is* `U ×_{𝒳'} U`; that datum is retained by
`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid_relationSquare_of_isSurjective`,
and `AlgebraicGeometry.Stack.EtaleLocalStructure.exists_compactSpace_targetFibre_of_relation`
turns it, together with the quasi-compact representative of `x` on `𝒳`, into the
quasi-compactness of the fibre. The chart of `𝒳'` is a chart of `𝒳` by
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.compOpenSubstack`, which keeps the
groupoid scheme and changes only the 1-morphism, so the retained datum survives the passage back
to `𝒳`.

The point of the object scheme at which the fibre is formed is pinned down rather than produced:
the quasi-compact field-valued representative of `x` has to be compared at the *same* point as the
fibre, which is why the chart lemma states its clause about points as an identity for every point
of `|U|`.

## Main results

* `AlgebraicGeometry.Stack.exists_etale_quotientStack_residualGerbeMap`: Stacks 0DU5.

## References

* [Stacks Project, Tag 04RZ](https://stacks.math.columbia.edu/tag/04RZ)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u w

namespace AlgebraicGeometry.Stack

open EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DU5.** Let `𝒳` be an algebraic stack over `S` which is quasi-DM (Stacks 050D) with
separated diagonal `Δ_{𝒳/S}` (Stacks 04XB), and let `x ∈ |𝒳|` be a point which can be represented
by a quasi-compact morphism from the spectrum of a field. Then there is a 1-morphism of algebraic
stacks `g : 𝒰 ⟶ 𝒳` such that

1. some point `v ∈ |𝒰|` maps to `x`, the residual gerbes of `𝒰` at `v` and of `𝒳` at `x` exist,
   and the 1-morphism between them induced by `g` (Stacks 0DTH) is an isomorphism for every
   choice of them;
2. `g` is representable by algebraic spaces and étale;
3. `𝒰` is the quotient stack `[U/R]` of (the realization of) a groupoid scheme `(U, R, s, t, c)`
   with `U` and `R` affine and `s`, `t` finite, flat and locally of finite presentation: there is
   an equivalence over the site between that quotient stack and `𝒰`.

The parenthetical equivalent hypothesis of the source (`I_𝒳 ⟶ 𝒳` locally quasi-finite and
separated) is Stacks 0CL0, parts (1) and (5). See the module documentation for the proof. -/
@[stacks 0DU5]
theorem exists_etale_quotientStack_residualGerbeMap (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hQ : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom))
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hqc : ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (g : 𝒰 ⟶ 𝒳)
      (v : AlgebraicStacks.points B S hS 𝒰),
      (AlgebraicStacks.pointsMap B S hS g v = x ∧
        (∃ P : ObjectProperty 𝒰.val.val.obj, IsResidualGerbeAt B S hS 𝒰 v P) ∧
        (∃ Q : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x Q) ∧
        ∀ (P : ObjectProperty 𝒰.val.val.obj) (Q : ObjectProperty 𝒳.val.val.obj)
          (hv : IsResidualGerbeAt B S hS 𝒰 v P)
          (hx : IsResidualGerbeAt B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS g v) Q),
          Nonempty (Functor.IsEquivalenceOver
            (fullSubcategoryAlgebraicStack 𝒰 P hv.2.choose).val.val.p
            (fullSubcategoryAlgebraicStack 𝒳 Q hx.2.choose).val.val.p
            (CatFiberedInGroupoids.homFunctor
              (residualGerbeMap B S hS g hv.2.choose hx.2.choose
                (map_mem_of_isResidualGerbeAt B S hS g v _ rfl hv hx)).hom))) ∧
      (IsRepresentableByAlgebraicSpaces B S hS g.hom.hom ∧ IsEtale B S hS g) ∧
      ∃ (G : GroupoidScheme S) (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
        (hP : B.Contains (pullback G.source G.target).left),
        IsAffine G.objects.left ∧ IsAffine G.arrows.left ∧
        IsFinite G.source.left ∧ Flat G.source.left ∧ LocallyOfFinitePresentation G.source.left ∧
        IsFinite G.target.left ∧ Flat G.target.left ∧ LocallyOfFinitePresentation G.target.left ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (quotientStack (G.realization B hS hU hR hP)).p 𝒰.val.val.p) := by
  classical
  refine exists_etale_quotientStack_residualGerbeMap_of_compactSpace_targetFibre
    B S hS 𝒳 hQ x ?_
  obtain ⟨U, f, hU, hflat, hlfp, hlqf, hx⟩ :=
    exists_isAffine_chart B S hS B.contains_terminal 𝒳 hQ x
  let 𝒳' := imageSubstack f hflat hlfp
  have hrepι : IsRepresentableByAlgebraicSpaces B S hS (𝒳'.inclusion B S hS).hom.hom :=
    𝒳'.isOpenImmersion.1
  have hmono : AlgebraicStacks.IsMonomorphism B S hS (𝒳'.inclusion B S hS) :=
    AlgebraicStacks.isMonomorphism_of_isOpenImmersion B S hS _ 𝒳'.isOpenImmersion
  have hQ' : IsQuasiDMOver B S hS 𝒳'.toAlgebraicStack :=
    (AlgebraicStacks.isAbsolutelyQuasiDM_iff_isQuasiDMOver B S hS B.contains_terminal _).1
      (AlgebraicStacks.isAbsolutelyQuasiDM_of_isMonomorphism B S hS B.contains_terminal
        (𝒳'.inclusion B S hS) hmono hQ)
  have hΔ' := AlgebraicStacks.isSeparated_relativeDiagonal_structureMorphism_of_isRepresentable
    B S hS (𝒳'.inclusion B S hS) hrepι hΔ
  have := hU
  -- the quotient chart of `𝒳'` with the representation of its self-intersection retained
  obtain ⟨K, chart, eR, γ, hsq, hchart, hs, ht, hpt⟩ :=
    exists_chartGroupoid_relationSquare_of_isSurjective (imageChart f hflat hlfp)
      (@isAffineOpen_top _ hU) (isSurjective_imageChart f hflat hlfp)
      (isFlat_imageChart f hflat hlfp) (isLocallyOfFinitePresentation_imageChart f hflat hlfp)
      (isLocallyQuasiFinite_imageChart f hflat hlfp hlqf) hQ' hΔ'
  -- the point of the object scheme of the chart lying over `x`
  obtain ⟨p, hp⟩ := exists_point_imageChart f hflat hlfp x hx
  obtain ⟨q, hq⟩ := hchart (AlgebraicStacks.pointsMap B S hS (imageChart f hflat hlfp) p)
  obtain ⟨z, hz⟩ := (bijective_representedChartPointMap B S hS K.U).2 q
  have hqx : AlgebraicStacks.pointsMap B S hS (𝒳'.inclusion B S hS)
      (AlgebraicStacks.pointsMap B S hS chart (representedChartPointMap B S hS K.U z)) = x :=
    (congrArg (AlgebraicStacks.pointsMap B S hS (𝒳'.inclusion B S hS))
        ((congrArg (AlgebraicStacks.pointsMap B S hS chart) hz).trans hq)).trans
      ((congrFun (AlgebraicStacks.pointsMap_comp B S hS (imageChart f hflat hlfp)
        (𝒳'.inclusion B S hS)) p).symm.trans hp)
  have hzx : AlgebraicStacks.pointsMap B S hS (K.compOpenSubstack 𝒳').map
      ((K.compOpenSubstack 𝒳').point z) = x :=
    (ChartGroupoid.pointsMap_compOpenSubstack 𝒳' K z).trans
      ((congrArg (AlgebraicStacks.pointsMap B S hS (𝒳'.inclusion B S hS)) (hpt z)).trans hqx)
  refine exists_compactSpace_targetFibre_of_relation B S hS 𝒳 x hqc (𝒳'.inclusion B S hS) hmono
    (K.compOpenSubstack 𝒳') z chart eR hs ht hzx ?_
  exact (congrArg (fun r => AlgebraicStacks.pointsMap B S hS (𝒳'.inclusion B S hS)
      (AlgebraicStacks.pointsMap B S hS chart r))
    (pointClass_closedPointFieldValuedPoint_eq K.U z _)).trans hqx

end AlgebraicGeometry.Stack

end
