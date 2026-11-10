module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineMorphismTerminalArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase

/-!
# Terminal arrows of an affine flat 1-morphism lie over flat morphisms of schemes

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is affine (Stacks 0CHQ) and
flat (Stacks 06PW), and let `y` be an object of `𝒴` lying over an affine scheme `V`. The base
change of `f` along the scheme-valued point `(Sch/V) ⟶ 𝒴` of `y` is represented by an affine
scheme `W`, which gives a terminal arrow `(x₀, f x₀ ⟶ y)` of `CostructuredArrow f y` with `x₀`
over `W`
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineHom`).
This file adds that the morphism of schemes `W ⟶ V` underneath the terminal arrow is flat:
flatness of `f` is, by Stacks 06FM, the relative property of Stacks 03YK at flatness of
morphisms of algebraic spaces, and at the point `y` the representing morphism of that relative
property is the Yoneda image of `W ⟶ V`, which is flat exactly when `W ⟶ V` is (Stacks 03MJ for
representable presheaves).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isTerminal_of_isAffineHom_of_isFlat`.

## References

* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Flatness of a 1-morphism `f : 𝒳 ⟶ 𝒴` representable by algebraic spaces, read at a
scheme-valued point `y` of `𝒴` as the relative property of Stacks 03YK: the structural morphism
of the algebraic space representing the base change of `f` along `y` is flat. -/
private theorem isFlat_relocalizeToYoneda_of_isFlat
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hfl : AlgebraicStacks.IsFlat B S hS f)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom) (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.IsFlat B S hS (OverShriek.relocalizeToYoneda U.hom F) := by
  let flatP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsFlat B S hS h
  have : (spaceProperty B S hS flatP).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u + 1} B S hS) :=
    Space.isFlat_isLocalAtTarget_fpqc.{u, u + 1} B S hS
  have : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have : (spaceProperty B S hS flatP).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := spaceProperty B S hS flatP)
  have hrel : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (spaceProperty B S hS flatP)
      f.hom hf :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS flatP
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f.hom hf
      ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hfl)
  exact (prop_algebraicSpaceMap_iff B S hS (spaceProperty B S hS flatP) U F hF).1
    (hrel U y hy F hF ⟨e⟩)

/-- The morphism of schemes underneath the arrow `f x ⟶ y` obtained from an object `z` of the
2-fibre product over a scheme-valued point `y'` of `𝒴` with `y'` at the identity isomorphic to
`y`, is flat as soon as the top morphism of `z` is. -/
private theorem flat_map_hom_mapIso_toCostructuredArrow
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) {y : 𝒴.val.val.obj}
    (U : BigFppfOver B S hS) (y' : Over U.left ⥤ 𝒴.val.val.obj)
    (hy' : y' ⋙ 𝒴.val.val.p = Over.map U.hom) (ξ : y'.obj (Over.mk (𝟙 U.left)) ≅ y)
    [𝒴.val.val.p.IsHomLift (𝟙 U) ξ.hom]
    (z : TwoFibreProductOver (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y'
      (CatFiberedInGroupoids.homFunctor f.hom))
    (hz : Flat ((BigFppfOver.toScheme B S hS).map
      ((Over.map U.hom).map (TwoFibreProductOver.TerminalArrow.toTop z.x)))) :
    Flat ((BigFppfOver.toScheme B S hS).map
      (𝒴.val.val.p.map ((CostructuredArrow.mapIso ξ).functor.obj
      (TwoFibreProductOver.TerminalArrow.toCostructuredArrow (𝒞 := B.Schemes)
        (X := B.obj hS) (A := U.left) U.hom 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) y' z)).hom)) := by
  have hcomp : 𝒴.val.val.p.map ((CostructuredArrow.mapIso ξ).functor.obj
      (TwoFibreProductOver.TerminalArrow.toCostructuredArrow (𝒞 := B.Schemes)
        (X := B.obj hS) (A := U.left) U.hom 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) y' z)).hom =
      𝒴.val.val.p.map z.iso.inv ≫
        𝒴.val.val.p.map (y'.map (TwoFibreProductOver.TerminalArrow.toTop z.x)) ≫
          𝒴.val.val.p.map ξ.hom :=
    (Functor.map_comp _ _ _).trans ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans
      (Category.assoc _ _ _))
  rw [hcomp]
  have hv : 𝒴.val.val.p.IsHomLift (𝟙 z.base) z.iso.inv := by
    have := z.vertical
    infer_instance
  rw [IsHomLift.fac' 𝒴.val.val.p (𝟙 z.base) z.iso.inv, IsHomLift.fac' 𝒴.val.val.p (𝟙 U) ξ.hom]
  change Flat ((BigFppfOver.toScheme B S hS).map ((_ ≫ 𝟙 _ ≫ _) ≫
    (y' ⋙ 𝒴.val.val.p).map (TwoFibreProductOver.TerminalArrow.toTop z.x) ≫ _ ≫ 𝟙 _ ≫ _))
  rw [Functor.congr_hom hy' (TwoFibreProductOver.TerminalArrow.toTop z.x)]
  have : MorphismProperty.RespectsIso (@Flat.{u}) := Flat.isStableUnderBaseChange.respectsIso
  simp only [Category.id_comp, Functor.map_comp, eqToHom_map, eqToHom_trans]
  have hI : ∀ {X Y Z : BigFppfOver B S hS} (h₁ : X = Y) (h₂ : Y = Z),
      IsIso ((BigFppfOver.toScheme B S hS).map (eqToHom h₁ ≫ eqToHom h₂)) := by
    rintro X Y Z rfl rfl
    simp only [eqToHom_refl, Category.comp_id]
    infer_instance
  exact (@MorphismProperty.cancel_left_of_respectsIso _ _ _ _ _ _ _ _ _ (hI _ _)).2
    ((MorphismProperty.cancel_right_of_respectsIso _ _ _).2
      ((MorphismProperty.cancel_left_of_respectsIso _ _ _).2
        ((MorphismProperty.cancel_right_of_respectsIso _ _ _).2 hz)))

/-- **An affine flat 1-morphism has terminal arrows over flat morphisms of affine schemes.** For
`f : 𝒳 ⟶ 𝒴` affine and flat and `y` lying over an affine scheme, `CostructuredArrow f y` has a
terminal object `(x₀, f x₀ ⟶ y)` with `x₀` lying over an affine scheme and the morphism of
schemes underneath `f x₀ ⟶ y` flat. -/
theorem exists_isTerminal_of_isAffineHom_of_isFlat
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsAffineHom B S hS f)
    (hfl : AlgebraicStacks.IsFlat B S hS f) (y : 𝒴.val.val.obj)
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y))) :
    ∃ t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y,
      Nonempty (IsTerminal t) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj t.left)) ∧
        Flat ((BigFppfOver.toScheme B S hS).map (𝒴.val.val.p.map t.hom)) := by
  classical
  set U := 𝒴.val.val.p.obj y
  obtain ⟨y', hy', ξ, hξ⟩ := StacksRepresentableCFG.exists_pointOverMap_of_obj 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids U y rfl
  obtain ⟨F, hF, ⟨e⟩⟩ := hf.1 U y' hy'
  have haff : Space.IsAffineHom B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.affineMorphismProperty B S hS) U F hF).1
      (hf.2 U y' hy' F hF ⟨e⟩)
  obtain ⟨W, _, _, hpb⟩ := haff ⟨U, hy⟩ (𝟙 (yoneda.obj U))
  have iW : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ≅
      (OverShriek.relocalizePresheafFunctor U.hom).obj F :=
    hpb.isoIsPullback _ _ IsPullback.of_id_fst
  obtain ⟨j⟩ := OverShriek.nonempty_iso_yoneda_of_relocalize U.hom F iW.symm
  let e' := e.trans (PresheafOfCategories.equivalenceOverOfIso j)
  let z := TwoFibreProductOver.TerminalArrow.representingObject (𝒞 := B.Schemes)
    (X := B.obj hS) (A := U.left) U.hom 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) y' e'
  let t₀ := TwoFibreProductOver.TerminalArrow.toCostructuredArrow (𝒞 := B.Schemes)
      (X := B.obj hS) (A := U.left) U.hom 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) y' z
  have hA : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj
      (TwoFibreProductOver.TerminalArrow.representingObject U.hom 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) y' e').y)) := by
    rw [TwoFibreProductOver.TerminalArrow.p𝒳_obj_representingObject_y U.hom 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) y' e']
    exact W.property
  -- the representing morphism is the Yoneda image of the morphism `W ⟶ U`
  let ψ := yoneda.preimage (iW.symm.inv ≫ OverShriek.relocalizeToYoneda U.hom F)
  have h2 : Space.IsFlat B S hS (yoneda.map ψ) := by
    rw [show yoneda.map ψ = iW.hom ≫ OverShriek.relocalizeToYoneda U.hom F from
      Functor.map_preimage yoneda _]
    -- flatness of `f` as the relative property of Stacks 03YK, at the point `y'`
    exact (Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS _ iW.hom _).2
      (isFlat_relocalizeToYoneda_of_isFlat B S hS f hf.1 hfl U y' hy' F hF e)
  have key : ∀ (X : Over U.left) (_ : X = Over.mk ψ.left),
      Flat ((BigFppfOver.toScheme B S hS).map
        ((Over.map U.hom).map (TwoFibreProductOver.TerminalArrow.toTop X))) := by
    rintro X rfl
    exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget ψ).1 h2
  exact ⟨(CostructuredArrow.mapIso ξ).functor.obj t₀,
    ⟨(isTerminalRepresentingArrowStack B S hS f U y' hy' e').isTerminalObj
      (CostructuredArrow.mapIso ξ).functor⟩, hA,
    flat_map_hom_mapIso_toCostructuredArrow B S hS f U y' hy' ξ z
      (key z.x (TwoFibreProductOver.TerminalArrow.representingObject_x
        (𝒞 := B.Schemes) (X := B.obj hS) (A := U.left) U.hom
        𝒳.val.val.p 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) y' e'))⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
