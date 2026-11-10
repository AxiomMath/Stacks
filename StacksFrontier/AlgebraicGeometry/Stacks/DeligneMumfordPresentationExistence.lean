module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordChartUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EtaleSliceCover

/-!
# A DM algebraic stack has a surjective étale presentation by a scheme (Stacks 06N3)

This file proves the substantial direction of Stacks 06N3:
`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`, which
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem` states as a property of
the ambient site.

The proof follows the source's, with one change of route: no residual gerbe is needed. Take a
smooth surjective chart `b : W ⟶ 𝒳` by a scheme and an étale surjective chart `E ⟶ W ×_𝒳 W` with
its two smooth projections `s, t : E ⟶ W`
(`AlgebraicGeometry.Stack.exists_smoothChart_etaleChart_twoFibreProduct`). Because `𝒳` is DM,
`(s, t) : E ⟶ W × W` is unramified
(`AlgebraicGeometry.Stack.unramifiedAt_pullbackLift_of_isDMOver`, through Stacks 050H, part (4)).
Through every point of `E` there is then an étale slice of `W`
(`Stacks.AlgebraicGeometry.exists_etale_slice_cover_of_unramified_pair`), and the disjoint union
`Z` of the slices is étale over `𝒳`
(`AlgebraicGeometry.Stack.isRelativelyEtale_comp_of_etaleSlice`). Its image contains the image of
`E`, which is all of `|𝒳|`, so `Z ⟶ 𝒳` is a surjective étale presentation
(`AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isRelativelyEtale_of_finiteTypePoints`).

## Main results

* `AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isDMOver`.
* `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`: **Stacks 06N3**, the
  implication (1) ⇒ (2), (3).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic stack which is DM over `S` is Deligne–Mumford** (Stacks 06N3, (1) ⇒ (2)). -/
theorem isDeligneMumfordStack_of_isDMOver (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsDMOver.{u, w} B S hS 𝒳) : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val := by
  classical
  obtain ⟨W, b, hb, hbsurj, E, c, hc, hcsurj, s, t, ⟨es⟩, ⟨et⟩, hs, ht⟩ :=
    exists_smoothChart_etaleChart_twoFibreProduct.{u, w} B S hS 𝒳
  let F := BigFppfOver.toScheme B S hS
  let Q₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b
  obtain ⟨Z₀, P₀, ι₀, hZ₀, hP₀, hslice⟩ :=
    Stacks.AlgebraicGeometry.exists_etale_slice_cover_of_unramified_pair B E.left.property
      W.left.property (F.map s) (F.map t)
      (fun x => unramifiedAt_pullbackLift_of_isDMOver.{u, w} B S hS 𝒳 h𝒳 b c hc s t es et x)
  -- the slice and the étale chart as objects of the site
  let Z : BigFppfOver B S hS := BigFppfOver.mk B S hS hZ₀ (ι₀ ≫ B.inclusion.map W.hom)
  let ι : Z ⟶ W := Over.homMk (ObjectProperty.homMk ι₀) rfl
  have hpb : IsPullback (pullback.fst s ι) (pullback.snd s ι) s ι := IsPullback.of_hasPullback s ι
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨p₀, hp₀, het₀, hsurj₀, hx₀⟩ := hslice (F.obj (pullback s ι)) (F.map (pullback.fst s ι))
    (F.map (pullback.snd s ι)) (hpb.map F)
  let Pobj : BigFppfOver B S hS :=
    BigFppfOver.mk B S hS hP₀ (p₀ ≫ F.map (pullback.fst s ι) ≫ B.inclusion.map E.hom)
  have hw : p₀ ≫ B.inclusion.map (pullback s ι).hom = B.inclusion.map Pobj.hom := by
    rw [← Over.w (pullback.fst s ι)]
    rfl
  let p : Pobj ⟶ pullback s ι :=
    Over.homMk (ObjectProperty.homMk p₀) (ObjectProperty.hom_ext _ hw)
  have hp₂ : Function.Surjective (F.map (p ≫ pullback.snd s ι)).base := by
    rw [Functor.map_comp]
    exact hsurj₀
  have hp₁ : Etale (F.map (p ≫ pullback.fst s ι ≫ t)) := by
    rw [Functor.map_comp, Functor.map_comp]
    exact het₀
  have hrel : IsRelativelyEtale B S hS (schemeFibredCategoryMap B S hS ι ≫ b) :=
    isRelativelyEtale_comp_of_etaleSlice B S hS b b hb Q₀
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b b)
      c hc s t es et ι hpb p hp₀ hp₂ hp₁
  refine isDeligneMumfordStack_of_isRelativelyEtale_of_finiteTypePoints B S hS 𝒳 Z _ hrel ?_
  -- every point of `𝒳` is in the image
  rintro x -
  let := pointTopology B S hS (schemeFibredCategory B S hS E)
  let := pointTopology B S hS (schemeFibredCategory B S hS W)
  let := pointTopology B S hS (schemeFibredCategory B S hS Z)
  have hnat : ∀ {U V : BigFppfOver B S hS} (g : U ⟶ V)
      (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)),
      let := pointTopology B S hS (schemeFibredCategory B S hS U)
      let := pointTopology B S hS (schemeFibredCategory B S hS V)
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g) z =
        (pointsHomeomorphScheme B S hS V).toEquiv.symm
          (F.map g ((pointsHomeomorphScheme B S hS U).toEquiv z)) := fun {U V} g z => by
    let := pointTopology B S hS (schemeFibredCategory B S hS U)
    let := pointTopology B S hS (schemeFibredCategory B S hS V)
    refine (pointsHomeomorphScheme B S hS V).toEquiv.injective ?_
    rw [Equiv.apply_symm_apply]
    exact pointsHomeomorphScheme_naturality B S hS g z
  let b' : schemeStack.{u, w} B S hS W ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom b
  let 𝒬 := twoFibreProductAlgebraicStack B S hS b' b'
  let c' : schemeStack.{u, w} B S hS E ⟶ 𝒬 := Bicategory.InducedBicategory.mkHom c
  have hc' : IsSurjective B S hS c' :=
    pointsMap_surjective_of_isSurjectiveOnObjects B S hS c' hcsurj
  have hsnd : IsSurjective B S hS (twoFibreProductSquareAlgebraicStacks B S hS b' b').snd :=
    isSurjective_of_isTwoFibreProduct B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b' b') hbsurj
  have hall := isSurjective_comp B S hS _ _ (isSurjective_comp B S hS _ _ hc' hsnd) hbsurj
  -- `s` and `t` agree on points of `𝒳`
  let θ : schemeStackMap.{u, w} B S hS s ≫ b' ≅ schemeStackMap.{u, w} B S hS t ≫ b' :=
    Bicategory.InducedBicategory.isoMk
      (Bicategory.whiskerRightIso es b ≪≫ Bicategory.associator c Q₀.fst b ≪≫
        Bicategory.whiskerLeftIso c Q₀.iso ≪≫ (Bicategory.associator c Q₀.snd b).symm ≪≫
        Bicategory.whiskerRightIso et.symm b)
  let θt : (c' ≫ (twoFibreProductSquareAlgebraicStacks B S hS b' b').snd) ≫ b' ≅
      schemeStackMap.{u, w} B S hS t ≫ b' :=
    Bicategory.InducedBicategory.isoMk (Bicategory.whiskerRightIso et.symm b)
  obtain ⟨z, rfl⟩ := hall x
  set e := (pointsHomeomorphScheme B S hS E).toEquiv z with he
  obtain ⟨q, hq⟩ := hx₀ e
  refine ⟨(pointsHomeomorphScheme B S hS Z).toEquiv.symm ((p₀ ≫ F.map (pullback.snd s ι)) q), ?_⟩
  have key : ∀ e' : F.obj E,
      AlgebraicStacks.pointsMap B S hS b'
        ((pointsHomeomorphScheme B S hS W).toEquiv.symm (F.map s e')) =
      AlgebraicStacks.pointsMap B S hS b'
        ((pointsHomeomorphScheme B S hS W).toEquiv.symm (F.map t e')) := by
    intro e'
    have h₁ := congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS θ.hom)
      ((pointsHomeomorphScheme B S hS E).toEquiv.symm e')
    rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at h₁
    simpa only [Function.comp_apply, hnat,
      Equiv.apply_symm_apply] using h₁
  have hZpt : F.map ι ((p₀ ≫ F.map (pullback.snd s ι)) q) =
      F.map s ((p₀ ≫ F.map (pullback.fst s ι)) q) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  change AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ι ≫ b') _ = _
  rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hnat,
    Equiv.apply_symm_apply, hZpt, key, ← Scheme.Hom.comp_apply, Category.assoc, hq,
    congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS θt.hom) z,
    AlgebraicStacks.pointsMap_comp, Function.comp_apply, hnat]

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 06N3, the implication (1) ⇒ (2), (3).** A DM algebraic stack is Deligne–Mumford:
it has a surjective étale 1-morphism from a scheme of the site. -/
theorem existsEtalePresentationOfIsAbsolutelyDM :
    ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ := fun 𝒳 h𝒳 =>
  isDeligneMumfordStack_of_isDMOver.{u, w} B S hS 𝒳
    ((AlgebraicStacks.isAbsolutelyDM_iff_isDMOver.{u, w} B S hS hZ 𝒳).1 h𝒳)

end AlgebraicGeometry.Stack

end
