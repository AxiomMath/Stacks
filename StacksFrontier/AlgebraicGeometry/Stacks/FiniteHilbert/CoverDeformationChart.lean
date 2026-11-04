module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalEtaleChartScheme
public import
  StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciHilbertCoverDeformationRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusCoverProperties

/-!
# An étale chart for the deformation problem of Stacks 06D8

`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` asks, for a first-order thickening
`U ⊂ U'` of affine objects of the big fppf site, an algebraic space `X'` flat over `U'`, a
degree-`d` finite locally free cover `q : Z ⟶ U` and an unramified local complete intersection
morphism `f` from `Z` to the special fibre `X = U ×_{U'} X'`, for a deformation of the cover over
`U'` mapping to `X'`.

Given a universal first-order thickening `j : Z ⟶ W` of `Z` over `X'` with structure morphism
`y : W ⟶ X'`, this file takes a surjective étale atlas `v : V' ⟶ X'`, the base changes
`W_V = W ×_{X'} V'` and `Z_V = Z ×_W W_V`, the base change `X_V = U ×_{U'} V'` of the chart to
the special fibre, and the morphism `f_V : Z_V ⟶ X_V` induced by `f`, and shows:

* `Z_V ⟶ Z` is surjective and étale and `W_V ⟶ W` is étale, as base changes of `v`;
* `V' ⟶ U'` is flat, by flatness of `X'` read at the chart `v`;
* `f_V` is formally unramified and a local complete intersection morphism, by the same
  conditions on `f` read at the charts `Z_V ⟶ Z` and `X_V ⟶ X`;
* `Z_V ⊂ W_V` is a universal first-order thickening of `Z_V` over `V'` in the sense of schemes
  (`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_scheme_of_etaleChart`).

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.exists_etaleChart_of_coverDeformationData`: a cover
  deformation datum with a universal first-order thickening has an étale chart by schemes with the
  properties above.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FiniteHilbert

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An étale chart of a cover deformation datum.** Take the data of
`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations`: a morphism `i : U ⟶ U'` of the big
fppf site of `S`, an algebraic space `X'` over `U'` flat over `U'`, a morphism `q : Z ⟶ U` and an
unramified local complete intersection morphism `f` from `Z` to the special fibre
`(relocalizeRestrict i) X'`. Suppose given a first-order thickening `j` of `Z` (read over `U'`)
into an object `W` of the site of `U'`, with a morphism `y : W ⟶ X'` restricting to `f` along
`j`, which is a universal first-order thickening of `Z` over `X'`.

Then there are schemes `Z_V, W_V, X_V, V'` and morphisms
`a : Z_V ⟶ Z`, `b : W_V ⟶ W`, `j_V : Z_V ⟶ W_V`, `p_V : V' ⟶ U'`, `i_V : X_V ⟶ V'`,
`q_V : X_V ⟶ U`, `f_V : Z_V ⟶ X_V`, `g_V : W_V ⟶ V'` such that `a` is étale and surjective, `b`
is étale, `Z_V = Z ×_W W_V`, `p_V` is flat, `X_V = U ×_{U'} V'`, `f_V` is formally unramified
and a local complete intersection morphism lying over `a ≫ q`, `Z_V ⊂ W_V` is a universal
first-order thickening of `f_V ≫ i_V` with structure morphism `g_V`, and `g_V` lies over `b`. -/
theorem exists_etaleChart_of_coverDeformationData {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    {X' : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B U'.left.1 U'.left.2 X')
    (hflat : Space.IsFlat B U'.left.1 U'.left.2 (Space.toYonedaId B U'.left.1 U'.left.2 X'))
    {Z : BigFppfOver B S hS} (q : Z ⟶ U)
    (f : yoneda.obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶
      (OverShriek.relocalizeRestrict i.left).obj X')
    (hunr : Space.IsUnramified B U.left.1 U.left.2 f)
    (hlci : Space.IsLocalCompleteIntersection B U.left.1 U.left.2 f)
    {W : BigFppfOver B U'.left.1 U'.left.2}
    (j : (Over.map i.left).obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶ W)
    (hj : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B U'.left.1 U'.left.2).map j))
    (y : yoneda.obj W ⟶ X')
    (hjy : yoneda.map j ≫ y = yonedaEquiv.symm
      (show X'.obj (op ((Over.map i.left).obj (Over.mk q.left))) from
        yonedaEquiv (F := (OverShriek.relocalizeRestrict i.left).obj X') f))
    (huniv : Space.IsUniversalFirstOrderThickening B U'.left.1 U'.left.2
      (Subfunctor.range (yoneda.map j))
      (ObjectProperty.homMk y : schemeSpace W ⟶ ⟨X', hX'⟩)) :
    ∃ (ZV WV XV V' : Scheme.{u}) (a : ZV ⟶ (BigFppfOver.toScheme B S hS).obj Z)
      (b : WV ⟶ (BigFppfOver.toScheme B U'.left.1 U'.left.2).obj W) (jV : ZV ⟶ WV)
      (pV : V' ⟶ (BigFppfOver.toScheme B S hS).obj U') (iV : XV ⟶ V')
      (qV : XV ⟶ (BigFppfOver.toScheme B S hS).obj U) (fV : ZV ⟶ XV) (gV : WV ⟶ V'),
      Etale a ∧ Surjective a ∧ Etale b ∧
      IsPullback jV a b ((BigFppfOver.toScheme B U'.left.1 U'.left.2).map j) ∧
      Flat pV ∧ IsPullback iV qV pV ((BigFppfOver.toScheme B S hS).map i) ∧
      FormallyUnramified fV ∧ IsLocalCompleteIntersectionMorphism fV ∧
      fV ≫ qV = a ≫ (BigFppfOver.toScheme B S hS).map q ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening (fV ≫ iV) jV gV ∧
      gV ≫ pV = b ≫ (B.inclusion.map W.hom : _ ⟶ (BigFppfOver.toScheme B S hS).obj U') := by
  obtain ⟨V₀, v, hvsurj, hvet⟩ := hX'.exists_atlas
  obtain ⟨WV₀, b₀, fst, hpbW⟩ := hvet.1 y
  let gV₀ : WV₀ ⟶ V₀ := yoneda.preimage fst
  have hWV : IsPullback (yoneda.map b₀) (yoneda.map gV₀) y v := by
    rw [show yoneda.map gV₀ = fst from yoneda.map_preimage fst]
    exact hpbW.flip
  have hbet : Etale ((BigFppfOver.toScheme B U'.left.1 U'.left.2).map b₀) :=
    hvet.2 y fst b₀ hpbW
  have hbsurj : Surjective ((BigFppfOver.toScheme B U'.left.1 U'.left.2).map b₀) :=
    hvsurj.2 y fst b₀ hpbW
  let a₀ := pullback.snd b₀ j
  let jV₀ := pullback.fst b₀ j
  have hZV : IsPullback jV₀ a₀ b₀ j := IsPullback.of_hasPullback b₀ j
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B U'.left.1 U'.left.2
  have hZVs := hZV.map (BigFppfOver.toScheme B U'.left.1 U'.left.2)
  have haet : Etale ((BigFppfOver.toScheme B U'.left.1 U'.left.2).map a₀) :=
    MorphismProperty.of_isPullback (P := @Etale.{u}) hZVs hbet
  have hasurj : Surjective ((BigFppfOver.toScheme B U'.left.1 U'.left.2).map a₀) :=
    MorphismProperty.of_isPullback (P := @Surjective.{u}) hZVs hbsurj
  have hpflat : Flat (B.inclusion.map V₀.hom) := by
    refine hflat V₀ (Over.mk (𝟙 (B.obj U'.left.2))) v (𝟙 _)
      (Over.homMk V₀.hom (by simp)) hvet (Space.presheaf_etale_id _ _ _ _) ?_
    rw [Category.comp_id]
    exact (eq_toYonedaId B _ _ _).trans (eq_toYonedaId B _ _ (v ≫ _)).symm
  let XV₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (pullback.snd V₀.hom i.left)
  let κ : (Over.map i.left).obj XV₀ ⟶ V₀ :=
    Over.homMk (pullback.fst V₀.hom i.left) pullback.condition
  have hpbX : IsPullback κ.left XV₀.hom V₀.hom i.left := IsPullback.of_hasPullback _ _
  have hpbXs := hpbX.map B.inclusion
  have hw : (jV₀.left ≫ gV₀.left) ≫ V₀.hom = (a₀.left ≫ q.left) ≫ i.left := by
    have h : jV₀.left ≫ b₀.left = a₀.left ≫ j.left := congrArg CommaMorphism.left hZV.w
    rw [Category.assoc, Over.w gV₀, ← Over.w b₀, ← Category.assoc, h, Category.assoc, Over.w j]
    rfl
  let fV₀ := hpbX.lift (jV₀.left ≫ gV₀.left) (a₀.left ≫ q.left) hw
  let ZVU : BigFppfOver B U.left.1 U.left.2 := Over.mk (a₀.left ≫ q.left)
  let aU : ZVU ⟶ Over.mk q.left := Over.homMk a₀.left rfl
  let hU : ZVU ⟶ XV₀ := Over.homMk fV₀ (hpbX.lift_snd _ _ hw)
  let cX : yoneda.obj XV₀ ⟶ (OverShriek.relocalizeRestrict i.left).obj X' :=
    OverShriek.restrictYonedaHom i.left κ ≫ (OverShriek.relocalizeRestrict i.left).map v
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B U.left.1 U.left.2)
  have hca : P.presheaf (yoneda.map aU) :=
    (Space.presheaf_yoneda_map_etale_iff B _ _ aU).2 haet
  have hcX : P.presheaf cX := by
    have hR : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
    have hI : IsIso (OverShriek.restrictYonedaHom i.left κ) :=
      OverShriek.isIso_restrictYonedaHom_of_isPullback i.left κ hpbX
    have hres := @OverShriek.relative_relocalizeRestrict_map _ _ _ _ i.left P
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B U'.left.1 U'.left.2)) hR
      (fun s hs => inverseImage_restrictReindexSnd B U.left.1 U'.left.1 U.left.2 U'.left.2
        i.left (@Etale.{u}) s hs) _ _ v hvet
    exact MorphismProperty.RespectsIso.precomp _ _ _ hres
  let e : (Over.map i.left).obj ZVU ⟶ pullback b₀ j :=
    Over.homMk (𝟙 _) (by
      rw [Category.id_comp]
      exact ((Over.w a₀).symm.trans (Category.assoc _ _ _).symm :))
  have hea : (Over.map i.left).map aU = e ≫ a₀ :=
    Over.OverMorphism.ext (by simp [e, aU])
  have hef : (Over.map i.left).map hU ≫ κ = e ≫ jV₀ ≫ gV₀ :=
    Over.OverMorphism.ext (by simp [e, hU, κ, fV₀])
  let x : X'.obj (op ((Over.map i.left).obj (Over.mk q.left))) :=
    yonedaEquiv (F := (OverShriek.relocalizeRestrict i.left).obj X') f
  have hjyapp : y.app _ j = x := by
    have := congrArg yonedaEquiv hjy
    rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply] at this
  have hcomm : yoneda.map hU ≫ cX = yoneda.map aU ≫ f := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map,
      ← map_yonedaEquiv f aU]
    show v.app _ ((Over.map i.left).map hU ≫ κ) =
      X'.map ((Over.map i.left).map aU).op x
    rw [← hjyapp, ← NatTrans.naturality_apply, hef, hea]
    have hw' := congrFun (congrArg (fun α => α.app (op ((Over.map i.left).obj ZVU))) hWV.w)
      (e ≫ jV₀)
    show v.app _ (e ≫ jV₀ ≫ gV₀) = y.app _ ((e ≫ a₀) ≫ j)
    rw [Category.assoc, ← hZV.w]
    simp only [← Category.assoc]
    exact hw'.symm
  have hfunr : Unramified (B.inclusion.map fV₀) := hunr _ _ _ _ hU hca hcX hcomm
  have hfu : FormallyUnramified (B.inclusion.map fV₀) := formallyUnramified_of_unramified _
  have hflci : IsLocalCompleteIntersectionMorphism (B.inclusion.map fV₀) :=
    hlci _ _ _ _ hU hca hcX hcomm
  have hUniv := Space.isUniversalFirstOrderThickening_scheme_of_etaleChart B U'.left.1 U'.left.2
    j hj (ObjectProperty.homMk y : schemeSpace W ⟶ ⟨X', hX'⟩) huniv v hvet b₀ gV₀ hWV a₀ jV₀ hZV
  have hfi : B.inclusion.map fV₀ ≫ B.inclusion.map κ.left =
      (BigFppfOver.toScheme B U'.left.1 U'.left.2).map (jV₀ ≫ gV₀) := by
    rw [← Functor.map_comp, hpbX.lift_fst]
    rfl
  refine ⟨_, _, _, _, (BigFppfOver.toScheme B U'.left.1 U'.left.2).map a₀,
    (BigFppfOver.toScheme B U'.left.1 U'.left.2).map b₀,
    (BigFppfOver.toScheme B U'.left.1 U'.left.2).map jV₀, B.inclusion.map V₀.hom,
    B.inclusion.map κ.left, B.inclusion.map XV₀.hom, B.inclusion.map fV₀,
    (BigFppfOver.toScheme B U'.left.1 U'.left.2).map gV₀, haet, hasurj, hbet, hZVs, hpflat,
    hpbXs, hfu, hflci, ?_, by rw [hfi]; exact hUniv, ?_⟩
  · show B.inclusion.map fV₀ ≫ B.inclusion.map XV₀.hom =
      B.inclusion.map a₀.left ≫ B.inclusion.map q.left
    rw [← Functor.map_comp, ← Functor.map_comp, hpbX.lift_snd]
  · show B.inclusion.map gV₀.left ≫ B.inclusion.map V₀.hom =
      B.inclusion.map b₀.left ≫ B.inclusion.map W.hom
    rw [← Functor.map_comp, ← Functor.map_comp, Over.w gV₀, Over.w b₀]

end AlgebraicGeometry.Stack.FiniteHilbert

end
