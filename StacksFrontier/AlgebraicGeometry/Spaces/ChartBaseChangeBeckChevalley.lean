module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.CategoryTheory.Sites.Modules.PushforwardBaseChangeSquare

/-!
# The Beck–Chevalley square of a representable morphism at an étale chart of its target

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, and let `V` be an étale scheme chart of `X`, with structure morphism
`g : V ⟶ X`.  Its base change `W = V ×_X Y` is an étale scheme chart of `Y`, with structure
morphism `i : W ⟶ Y`, and the projection `f' : W ⟶ V` makes

```
  W --i--> Y
  |f'      |f
  V --g--> X
```

a cartesian square of algebraic spaces.  On the small étale sites it gives a square of functors:
base change of charts `u` along `f` and `uV` along `f'`, and postcomposition `p` with `g` and
`pY` with `i`, which are left adjoint to base change along `g` and along `i`.

The two composites of base change, `b ⋙ uV` and `u ⋙ bY`, are compared by the composition law
of chart base change (`AlgebraicGeometry.Space.chartSquareBaseChangeIso`), and this file proves
that the mate of that comparison, `uV ⋙ pY ⟶ p ⋙ u`, is an **isomorphism**
(`AlgebraicGeometry.Space.isIso_chartSquareMate`): on a chart `V'` of `V` it is the comparison
of the two fibre products `V' ×_V W` and `V' ×_X Y`, which agree because the square is
cartesian.  That is the input which
`StacksFrontier/CategoryTheory/Sites/Modules/PushforwardBaseChangeSquare.lean` turns into base
change for restriction of sheaves of modules.

## Main definitions

* `AlgebraicGeometry.Space.chartSquareTop`, `AlgebraicGeometry.Space.chartSquareMap`: the chart
  `W = V ×_X Y` of `Y` and the projection `f' : W ⟶ V`.
* `AlgebraicGeometry.Space.chartSquareBaseChangeIso`: `b ⋙ uV ≅ u ⋙ bY`.
* `AlgebraicGeometry.Space.chartSquareMate`: its mate `uV ⋙ pY ⟶ p ⋙ u`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartSquare`: the square is cartesian.
* `AlgebraicGeometry.Space.isIso_chartSquareMate`: the mate is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change along equal morphisms -/

/-- Base change of charts along equal morphisms gives equal functors, read as an isomorphism. -/
def smallBaseChangeCongr {X Y : AlgebraicSpaces B S hS} {a a' : X ⟶ Y} (h : a = a')
    (ha : yoneda.relativelyRepresentable a.hom) (ha' : yoneda.relativelyRepresentable a'.hom) :
    smallBaseChange B S hS a ha ≅ smallBaseChange B S hS a' ha' :=
  eqToIso (by subst h; rfl)

/-- The comparison of base change along equal morphisms commutes with the cartesian
projections. -/
theorem smallBaseChangeCongr_hom_app_left_comp_snd {X Y : AlgebraicSpaces B S hS} {a a' : X ⟶ Y}
    (h : a = a') (ha : yoneda.relativelyRepresentable a.hom)
    (ha' : yoneda.relativelyRepresentable a'.hom) (Z : SmallEtale B S hS Y.1) :
    ((smallBaseChangeCongr B S hS h ha ha').hom.app Z).hom.left ≫ ha'.snd Z.1.hom =
      ha.snd Z.1.hom := by
  subst h
  simp only [smallBaseChangeCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
  (V : SmallEtale B S hS X.1)

/-! ### The square -/

/-- The chart `W = V ×_X Y` of `Y`. -/
abbrev chartSquareTop : SmallEtale B S hS Y.1 := (smallBaseChange B S hS f hf).obj V

/-- The projection `f' : W ⟶ V`, as a morphism of algebraic spaces. -/
def chartSquareMap :
    chartSpace B S hS Y (chartSquareTop B S hS f hf V) ⟶ chartSpace B S hS X V :=
  ObjectProperty.homMk (yoneda.map (hf.snd V.1.hom))

/-- **The square is cartesian**, as a square of presheaves. -/
theorem isPullback_chartSquare :
    IsPullback (chartToSpace B S hS Y (chartSquareTop B S hS f hf V)).hom
      (chartSquareMap B S hS f hf V).hom f.hom (chartToSpace B S hS X V).hom :=
  hf.isPullback V.1.hom

/-- The square commutes, as a square of algebraic spaces. -/
theorem chartSquare_w :
    chartToSpace B S hS Y (chartSquareTop B S hS f hf V) ≫ f =
      chartSquareMap B S hS f hf V ≫ chartToSpace B S hS X V :=
  ObjectProperty.hom_ext _ (isPullback_chartSquare B S hS f hf V).w

/-- The projection `f'` is representable. -/
theorem relativelyRepresentable_chartSquareMap :
    yoneda.relativelyRepresentable (chartSquareMap B S hS f hf V).hom :=
  Functor.relativelyRepresentable.map yoneda (hf.snd V.1.hom)

/-- The composite `i ≫ f` is representable. -/
theorem relativelyRepresentable_chartSquare_comp :
    yoneda.relativelyRepresentable (chartToSpace B S hS Y (chartSquareTop B S hS f hf V) ≫ f).hom :=
  MorphismProperty.comp_mem _ _ _ (relativelyRepresentable_chartToSpace B S hS Y _) hf

/-- The composite `f' ≫ g` is representable. -/
theorem relativelyRepresentable_chartSquare_comp' :
    yoneda.relativelyRepresentable (chartSquareMap B S hS f hf V ≫ chartToSpace B S hS X V).hom :=
  MorphismProperty.comp_mem _ _ _ (relativelyRepresentable_chartSquareMap B S hS f hf V)
    (relativelyRepresentable_chartToSpace B S hS X V)

/-- **The two composites of base change around the square agree**: `b ⋙ uV ≅ u ⋙ bY`, by the
composition law of chart base change. -/
def chartSquareBaseChangeIso :
    smallBaseChange B S hS (chartToSpace B S hS X V)
      (relativelyRepresentable_chartToSpace B S hS X V) ⋙
        smallBaseChange B S hS (chartSquareMap B S hS f hf V)
          (relativelyRepresentable_chartSquareMap B S hS f hf V) ≅
      smallBaseChange B S hS f hf ⋙
        smallBaseChange B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
          (relativelyRepresentable_chartToSpace B S hS Y _) :=
  smallBaseChangeComp B S hS _ _ _ _ (relativelyRepresentable_chartSquare_comp' B S hS f hf V) ≪≫
    smallBaseChangeCongr B S hS (chartSquare_w B S hS f hf V).symm _
      (relativelyRepresentable_chartSquare_comp B S hS f hf V) ≪≫
    (smallBaseChangeComp B S hS _ _ _ _
      (relativelyRepresentable_chartSquare_comp B S hS f hf V)).symm

/-- The comparison `b ⋙ uV ≅ u ⋙ bY` commutes with the cartesian projections to the chart of `X`
it starts from. -/
theorem chartSquareBaseChangeIso_hom_app_left_comp_snd (Z : SmallEtale B S hS X.1) :
    ((chartSquareBaseChangeIso B S hS f hf V).hom.app Z).hom.left ≫
        (relativelyRepresentable_chartToSpace B S hS Y _).snd
          ((smallBaseChange B S hS f hf).obj Z).1.hom ≫ hf.snd Z.1.hom =
      (relativelyRepresentable_chartSquareMap B S hS f hf V).snd
          ((smallBaseChange B S hS (chartToSpace B S hS X V)
            (relativelyRepresentable_chartToSpace B S hS X V)).obj Z).1.hom ≫
        (relativelyRepresentable_chartToSpace B S hS X V).snd Z.1.hom := by
  have hf' := relativelyRepresentable_chartSquareMap B S hS f hf V
  have hg := relativelyRepresentable_chartToSpace B S hS X V
  have hi := relativelyRepresentable_chartToSpace B S hS Y (chartSquareTop B S hS f hf V)
  have h1 := relativelyRepresentable_chartSquare_comp' B S hS f hf V
  have h2 := relativelyRepresentable_chartSquare_comp B S hS f hf V
  set c1 := smallBaseChangeComp B S hS _ _ hf' hg h1
  set c2 := smallBaseChangeComp B S hS _ _ hi hf h2
  set cg := smallBaseChangeCongr B S hS (chartSquare_w B S hS f hf V).symm h1 h2
  have e1 := smallBaseChangeComp_hom_app_snd B S hS _ _ hf' hg h1 Z
  have e2 := smallBaseChangeComp_hom_app_snd B S hS _ _ hi hf h2 Z
  have eg := smallBaseChangeCongr_hom_app_left_comp_snd B S hS
    (chartSquare_w B S hS f hf V).symm h1 h2 Z
  have inv2 : (c2.inv.app Z).hom.left ≫ (c2.hom.app Z).hom.left = 𝟙 _ := by
    change ((c2.inv.app Z ≫ c2.hom.app Z)).hom.left = _
    rw [Iso.inv_hom_id_app]
    rfl
  have hd : ((chartSquareBaseChangeIso B S hS f hf V).hom.app Z).hom.left =
      (c1.hom.app Z).hom.left ≫ (cg.hom.app Z).hom.left ≫ (c2.inv.app Z).hom.left := rfl
  have e2' : (c2.inv.app Z).hom.left ≫ hi.snd ((smallBaseChange B S hS f hf).obj Z).1.hom ≫
      hf.snd Z.1.hom = h2.snd Z.1.hom :=
    (congrArg (fun k => (c2.inv.app Z).hom.left ≫ k) e2.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ h2.snd Z.1.hom) inv2).trans (Category.id_comp _)))
  rw [hd, Category.assoc, Category.assoc, e2', eg]
  exact e1

/-! ### The mate -/

/-- Postcomposition with `g` is left adjoint to base change along `g`. -/
abbrev chartSquareAdjX :=
  smallEtalePostcompBaseChangeAdjunction B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V) (relativelyRepresentable_chartToSpace B S hS X V)

/-- Postcomposition with `i` is left adjoint to base change along `i`. -/
abbrev chartSquareAdjY :=
  smallEtalePostcompBaseChangeAdjunction B S hS
    (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
    (isEtale_chartToSpace B S hS Y _) (relativelyRepresentable_chartToSpace B S hS Y _)

/-- **The mate** `uV ⋙ pY ⟶ p ⋙ u` of the comparison of the two composites of base change. -/
def chartSquareMate :
    smallBaseChange B S hS (chartSquareMap B S hS f hf V)
          (relativelyRepresentable_chartSquareMap B S hS f hf V) ⋙
        smallEtalePostcomp B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
          (isEtale_chartToSpace B S hS Y _) ⟶
      smallEtalePostcomp B S hS (chartToSpace B S hS X V) (isEtale_chartToSpace B S hS X V) ⋙
        smallBaseChange B S hS f hf :=
  ((mateEquiv (chartSquareAdjX B S hS V) (chartSquareAdjY B S hS f hf V)).symm
    (TwoSquare.mk _ _ _ _ (chartSquareBaseChangeIso B S hS f hf V).hom))

/-- The mate of the mate is the comparison of the two composites of base change. -/
theorem mateEquiv_chartSquareMate :
    (mateEquiv (chartSquareAdjX B S hS V) (chartSquareAdjY B S hS f hf V)
      (TwoSquare.mk _ _ _ _ (chartSquareMate B S hS f hf V)) :
        _ ⟶ _) =
      (chartSquareBaseChangeIso B S hS f hf V).hom :=
  (mateEquiv (chartSquareAdjX B S hS V)
    (chartSquareAdjY B S hS f hf V)).apply_symm_apply _

/-- **The mate is an isomorphism**: on a chart `V'` of `V` it compares the fibre products
`V' ×_V W` and `V' ×_X Y`, which agree because the square is cartesian. -/
theorem chartSquareMate_app (W' : SmallEtale B S hS (chartSpace B S hS X V).1) :
    (chartSquareMate B S hS f hf V).app W' =
      (smallEtalePostcomp B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
          (isEtale_chartToSpace B S hS Y _)).map
          ((smallBaseChange B S hS (chartSquareMap B S hS f hf V)
            (relativelyRepresentable_chartSquareMap B S hS f hf V)).map
            ((chartSquareAdjX B S hS V).unit.app W')) ≫
        (smallEtalePostcomp B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
          (isEtale_chartToSpace B S hS Y _)).map
          ((chartSquareBaseChangeIso B S hS f hf V).hom.app
            ((smallEtalePostcomp B S hS (chartToSpace B S hS X V)
              (isEtale_chartToSpace B S hS X V)).obj W')) ≫
        (chartSquareAdjY B S hS f hf V).counit.app
          ((smallBaseChange B S hS f hf).obj ((smallEtalePostcomp B S hS (chartToSpace B S hS X V)
              (isEtale_chartToSpace B S hS X V)).obj W')) := by
  simp [chartSquareMate]

/-- A morphism between two fibre products of one cospan, compatible with the projections, is an
isomorphism. -/
theorem isIso_of_isPullback_of_comp {C : Type*} [Category C] {P P' A A' Z : C}
    {fst : P ⟶ A} {snd : P ⟶ A'} {fst' : P' ⟶ A} {snd' : P' ⟶ A'} {a : A ⟶ Z} {a' : A' ⟶ Z}
    (h : IsPullback fst snd a a') (h' : IsPullback fst' snd' a a') (φ : P ⟶ P')
    (h₁ : φ ≫ fst' = fst) (h₂ : φ ≫ snd' = snd) : IsIso φ := by
  have : φ = (h.isoIsPullback _ _ h').hom :=
    h'.hom_ext (by rw [h₁, IsPullback.isoIsPullback_hom_fst])
      (by rw [h₂, IsPullback.isoIsPullback_hom_snd])
  rw [this]
  infer_instance

/-- A morphism of étale charts whose underlying morphism of the big fppf site becomes an
isomorphism under the Yoneda embedding is an isomorphism. -/
theorem isIso_of_isIso_yoneda_map_left {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A A' : SmallEtale B S hS F} (k : A ⟶ A') (h : IsIso (yoneda.map k.hom.left)) : IsIso k := by
  have : IsIso k.hom.left := isIso_of_reflects_iso _ yoneda
  have : IsIso ((CostructuredArrow.proj yoneda F).map k.hom) := by
    change IsIso k.hom.left
    infer_instance
  have : IsIso k.hom := isIso_of_reflects_iso _ (CostructuredArrow.proj yoneda F)
  have : IsIso ((ObjectProperty.ι (IsEtaleChart B S hS F)).map k) := by
    change IsIso k.hom
    infer_instance
  exact isIso_of_reflects_iso _ (ObjectProperty.ι (IsEtaleChart B S hS F))

/-- **The mate is an isomorphism**: on a chart `V'` of `V` it compares the fibre products
`V' ×_V W` and `V' ×_X Y`, which agree because the square is cartesian. -/
instance isIso_chartSquareMate : IsIso (chartSquareMate B S hS f hf V) := by
  have hf' := relativelyRepresentable_chartSquareMap B S hS f hf V
  have hg := relativelyRepresentable_chartToSpace B S hS X V
  have hi := relativelyRepresentable_chartToSpace B S hS Y (chartSquareTop B S hS f hf V)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W' => ?_
  apply isIso_of_isIso_yoneda_map_left
  have src : IsPullback (hf'.fst W'.1.hom ≫ hf.fst V.1.hom) (yoneda.map (hf'.snd W'.1.hom)) f.hom
      (W'.1.hom ≫ V.1.hom) :=
    (hf'.isPullback W'.1.hom).paste_horiz (hf.isPullback V.1.hom)
  refine isIso_of_isPullback_of_comp src (hf.isPullback (W'.1.hom ≫ V.1.hom)) _
    (CostructuredArrow.w ((chartSquareMate B S hS f hf V).app W').hom) ?_
  refine (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ?_)
  have e := chartSquareBaseChangeIso_hom_app_left_comp_snd B S hS f hf V
    ((smallEtalePostcomp B S hS (chartToSpace B S hS X V) (isEtale_chartToSpace B S hS X V)).obj W')
  rw [chartSquareMate_app]
  change ((smallBaseChange B S hS (chartSquareMap B S hS f hf V) hf').map
      ((chartSquareAdjX B S hS V).unit.app W')).hom.left ≫
    ((chartSquareBaseChangeIso B S hS f hf V).hom.app
      ((smallEtalePostcomp B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj W')).hom.left ≫
    ((chartSquareAdjY B S hS f hf V).counit.app _).hom.left ≫ hf.snd _ = _
  rw [smallEtalePostcompBaseChangeAdjunction_counit_left, e]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ hg.snd _)
    (smallBaseChange_map_snd B S hS _ hf' ((chartSquareAdjX B S hS V).unit.app W')))).trans
    ((Category.assoc _ _ _).trans ((congrArg (hf'.snd W'.1.hom ≫ ·)
      (smallEtalePostcompBaseChangeAdjunction_unit_left_comp_snd B S hS _ _ hg W')).trans
      (Category.comp_id _)))

end AlgebraicGeometry.Space
