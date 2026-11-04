module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Base change of an étale chart along a chart of the base

Let

```
X' --g'--> X
|f'         |f
v           v
Y' --g-->  Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`d : U' ⟶ V` be a commutative square of étale scheme charts over `g`, and let `W` be an étale
scheme chart of `X` with a morphism `b : W ⟶ V` over `f`.  This file builds the étale scheme
chart `T = W ×_V U'` of `X'`, together with its two chart diagrams `T ⟶ W` over `g'` and
`T ⟶ U'` over `f'`.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeAlong`: the étale scheme chart `W ×_V U'` of `X'`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartBaseChangeAlong`: it is the fibre product of `W` and
  `U'` over `V` in the big fppf category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) {U' : SmallEtale B S hS Y'.1} {V : SmallEtale B S hS Y.1}
  (d : (SmallEtale.toOver B S hS Y'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
  (hd : U'.1.hom ≫ g.hom = yoneda.map d ≫ V.1.hom) {W : SmallEtale B S hS X.1}
  (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
  (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom)

section Aux

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- Pasting two commutative squares along a common edge, over variables. -/
theorem square_paste_eq {P Q R T A' A'' B' : C} {i : P ⟶ Q} {π : P ⟶ R} {f₁ : Q ⟶ T} {u : R ⟶ T}
    {g₁ : Q ⟶ A'} {f₂ : A' ⟶ B'} {g₂ : T ⟶ B'} {d₁ : R ⟶ A''} {v : A'' ⟶ B'}
    (h1 : i ≫ f₁ = π ≫ u) (h2 : g₁ ≫ f₂ = f₁ ≫ g₂) (h3 : u ≫ g₂ = d₁ ≫ v) :
    (i ≫ g₁) ≫ f₂ = (π ≫ d₁) ≫ v := by
  rw [Category.assoc, h2, ← Category.assoc, h1, Category.assoc, h3, Category.assoc]

/-- A composite through two factorizations, over variables. -/
theorem comp_comp_eq_of_eq {P Q R T Z M : C} {pW : P ⟶ Q} {w : Q ⟶ T} {τ' : P ⟶ R}
    {h : R ⟶ T} {k : T ⟶ Z} {a : Q ⟶ Z} {b₁ : R ⟶ M} {b₂ : M ⟶ Z} {c : P ⟶ M}
    (e5 : w ≫ k = a) (e6 : h ≫ k = b₁ ≫ b₂) (e4 : τ' ≫ b₁ = c) (hc : c ≫ b₂ = pW ≫ a) :
    (pW ≫ w) ≫ k = (τ' ≫ h) ≫ k := by
  rw [Category.assoc, Category.assoc, e5, e6, ← Category.assoc, e4, hc]

/-- A composite through a functor, rewritten along a commutative square, over variables. -/
theorem map_comp_map_comp_eq {D : Type*} [Category D] (F : C ⥤ D) {P Q R T : C} {Z : D}
    (pm : P ⟶ Q) (f₂ : Q ⟶ R) (f₁ : P ⟶ T) (mm : T ⟶ R) (w₂ : F.obj R ⟶ Z) (w₁ : F.obj T ⟶ Z)
    (h : pm ≫ f₂ = f₁ ≫ mm) (hw : F.map mm ≫ w₂ = w₁) :
    F.map pm ≫ F.map f₂ ≫ w₂ = F.map f₁ ≫ w₁ := by
  rw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, hw]

end Aux

/-- The underlying object `W ×_V U'` of the big fppf category. -/
abbrev chartBaseChangeAlongObj : BigFppfOver B S hS := pullback b d

include hb hd in
/-- The structure morphism `W ×_V U' ⟶ X'`, from the universal property of `X' = X ×_Y Y'`. -/
def chartBaseChangeAlongHom : yoneda.obj (chartBaseChangeAlongObj d b) ⟶ X'.1 :=
  (AlgebraicSpaces.isPullback_hom B S hS sq).lift (yoneda.map (pullback.fst b d) ≫ W.1.hom)
    (yoneda.map (pullback.snd b d) ≫ U'.1.hom) (by
      rw [Category.assoc, hb, Category.assoc, hd, ← Category.assoc, ← Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, pullback.condition])

/-- The algebraic space represented by `W ×_V U'`. -/
abbrev chartBaseChangeAlongSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (chartBaseChangeAlongObj d b), isAlgebraicSpace_yoneda B S hS _⟩

/-- The square `W ×_V U'` of represented algebraic spaces is cartesian. -/
theorem isPullback_chartBaseChangeAlongSpace :
    IsPullback
      (ObjectProperty.homMk (yoneda.map (pullback.fst b d)) :
        chartBaseChangeAlongSpace d b ⟶ chartSpace B S hS X W)
      (ObjectProperty.homMk (yoneda.map (pullback.snd b d)) :
        chartBaseChangeAlongSpace d b ⟶ chartSpace B S hS Y' U')
      (chartSpaceMapOver B S hS b) (chartSpaceMapOver B S hS d) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    ((IsPullback.of_hasPullback b d).map yoneda)

include hb hd in
/-- **The cartesian square `W ×_V U' = W ×_Z Z'`**, where `Z = V ×_Y X` and `Z' = U' ×_{Y'} X'`:
the morphism `W ×_V U' ⟶ Z'` is the base change of `W ⟶ Z` along `Z' ⟶ Z`. -/
theorem exists_isPullback_chartBaseChangeAlongSpace :
    ∃ (τ' : chartBaseChangeAlongSpace d b ⟶ chartBaseChangeSpace B S hS f' U')
      (w : chartSpace B S hS X W ⟶ chartBaseChangeSpace B S hS f V)
      (h : chartBaseChangeSpace B S hS f' U' ⟶ chartBaseChangeSpace B S hS f V),
      IsPullback (ObjectProperty.homMk (yoneda.map (pullback.fst b d)) :
          chartBaseChangeAlongSpace d b ⟶ chartSpace B S hS X W) τ' w h ∧
        τ' ≫ chartBaseChangeInclusion B S hS f' U' =
          ObjectProperty.homMk (chartBaseChangeAlongHom sq d hd b hb) ∧
        τ' ≫ chartBaseChangeProjection B S hS f' U' =
          ObjectProperty.homMk (yoneda.map (pullback.snd b d)) ∧
        w ≫ chartBaseChangeInclusion B S hS f V = chartToSpace B S hS X W ∧
        w ≫ chartBaseChangeProjection B S hS f V = chartSpaceMapOver B S hS b := by
  have P1 := isPullback_chartBaseChangeInclusion B S hS f V
  have P2 := isPullback_chartBaseChangeInclusion B S hS f' U'
  have P4 := isPullback_chartBaseChangeAlongSpace d b
  let τsp : chartBaseChangeAlongSpace d b ⟶ X' :=
    ObjectProperty.homMk (chartBaseChangeAlongHom sq d hd b hb)
  let pW : chartBaseChangeAlongSpace d b ⟶ chartSpace B S hS X W :=
    ObjectProperty.homMk (yoneda.map (pullback.fst b d))
  let pU : chartBaseChangeAlongSpace d b ⟶ chartSpace B S hS Y' U' :=
    ObjectProperty.homMk (yoneda.map (pullback.snd b d))
  have hτg : τsp ≫ g' = pW ≫ chartToSpace B S hS X W :=
    ObjectProperty.hom_ext _ ((AlgebraicSpaces.isPullback_hom B S hS sq).lift_fst _ _ _)
  have hτf : τsp ≫ f' = pU ≫ chartToSpace B S hS Y' U' :=
    ObjectProperty.hom_ext _ ((AlgebraicSpaces.isPullback_hom B S hS sq).lift_snd _ _ _)
  have hbW : chartToSpace B S hS X W ≫ f =
      chartSpaceMapOver B S hS b ≫ chartToSpace B S hS Y V :=
    ObjectProperty.hom_ext _ hb
  have hdU : chartToSpace B S hS Y' U' ≫ g =
      chartSpaceMapOver B S hS d ≫ chartToSpace B S hS Y V :=
    ObjectProperty.hom_ext _ hd
  let w := P1.lift (chartToSpace B S hS X W) (chartSpaceMapOver B S hS b) hbW
  let h := P1.lift (chartBaseChangeInclusion B S hS f' U' ≫ g')
    (chartBaseChangeProjection B S hS f' U' ≫ chartSpaceMapOver B S hS d)
      (square_paste_eq P2.w sq.w hdU)
  have e6 : h ≫ chartBaseChangeInclusion B S hS f V = chartBaseChangeInclusion B S hS f' U' ≫ g' :=
    P1.lift_fst _ _ _
  have hL : IsPullback h (chartBaseChangeProjection B S hS f' U')
      (chartBaseChangeProjection B S hS f V) (chartSpaceMapOver B S hS d) :=
    IsPullback.of_right (e6 ▸ hdU ▸ P2.paste_horiz sq) (P1.lift_snd _ _ _) P1
  let τ' := P2.lift τsp pU hτf
  have e2 : τ' ≫ chartBaseChangeProjection B S hS f' U' = pU := P2.lift_snd _ _ _
  have e3 : w ≫ chartBaseChangeProjection B S hS f V = chartSpaceMapOver B S hS b :=
    P1.lift_snd _ _ _
  have e4 : τ' ≫ chartBaseChangeInclusion B S hS f' U' = τsp := P2.lift_fst _ _ _
  have e5 : w ≫ chartBaseChangeInclusion B S hS f V = chartToSpace B S hS X W :=
    P1.lift_fst _ _ _
  have e7 : h ≫ chartBaseChangeProjection B S hS f V =
      chartBaseChangeProjection B S hS f' U' ≫ chartSpaceMapOver B S hS d := P1.lift_snd _ _ _
  have hT : IsPullback pW τ' w h := by
    refine IsPullback.of_bot ?_ ?_ hL
    · rwa [e2, e3]
    · exact P1.hom_ext (comp_comp_eq_of_eq e5 e6 e4 hτg) (comp_comp_eq_of_eq e3 e7 e2 P4.w.symm)
  exact ⟨τ', w, h, hT, e4, e2, e5, e3⟩

include hb hd in
/-- **The structure morphism `W ×_V U' ⟶ X'` is étale.**  It factors as the base change
`W ×_V U' = W ×_Z Z'` of the étale morphism `W ⟶ Z = V ×_Y X`, followed by the étale structure
morphism of `Z' = U' ×_{Y'} X'`. -/
theorem isEtale_chartBaseChangeAlongHom :
    IsEtale B S hS (chartBaseChangeAlongHom sq d hd b hb) := by
  obtain ⟨τ', w, h, hT, e4, -, e5, -⟩ := exists_isPullback_chartBaseChangeAlongSpace sq d hd b hb
  have hw : IsEtale B S hS w.hom :=
    isEtale_of_isEtale_over B S hS (chartSpace B S hS X W).2
      (chartBaseChangeSpace B S hS f V).2 X.2 w.hom (chartToSpace B S hS X W).hom
      (chartBaseChangeInclusion B S hS f V).hom
      (isEtale_of_presheaf_etale B S hS W.2) (isEtale_chartBaseChangeInclusion B S hS f V)
      (congrArg (fun k : chartSpace B S hS X W ⟶ X => k.hom) e5)
  have hτ' := isEtale_of_isPullback B S hS _ τ' w h hT hw
  have hcomp := isEtale_comp B S hS hτ' (isEtale_chartBaseChangeInclusion B S hS f' U')
  exact (congrArg (fun k : chartBaseChangeAlongSpace d b ⟶ X' => IsEtale B S hS k.hom) e4).mp
    hcomp

/-- **The étale scheme chart `W ×_V U'` of `X'`.** -/
def chartBaseChangeAlong : SmallEtale B S hS X'.1 :=
  ⟨CostructuredArrow.mk (chartBaseChangeAlongHom sq d hd b hb),
    presheaf_etale_of_isEtale B S hS (isEtale_chartBaseChangeAlongHom sq d hd b hb)⟩

/-- The projection `W ×_V U' ⟶ W`, over `g'`. -/
theorem chartBaseChangeAlong_fst :
    (chartBaseChangeAlong sq d hd b hb).1.hom ≫ g'.hom =
      yoneda.map (pullback.fst b d) ≫ W.1.hom :=
  (AlgebraicSpaces.isPullback_hom B S hS sq).lift_fst _ _ _

/-- The projection `W ×_V U' ⟶ U'`, over `f'`. -/
theorem chartBaseChangeAlong_snd :
    (chartBaseChangeAlong sq d hd b hb).1.hom ≫ f'.hom =
      yoneda.map (pullback.snd b d) ≫ U'.1.hom :=
  (AlgebraicSpaces.isPullback_hom B S hS sq).lift_snd _ _ _

include sq in
/-- A morphism of the underlying objects into `W ×_V U'` is a morphism of étale scheme charts of
`X'` as soon as the two projections are compatible with the structure morphisms. -/
theorem chartBaseChangeAlong_hom_ext {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m₁ m₂ : Z ⟶ X'.1)
    (h₁ : m₁ ≫ g'.hom = m₂ ≫ g'.hom) (h₂ : m₁ ≫ f'.hom = m₂ ≫ f'.hom) : m₁ = m₂ :=
  (AlgebraicSpaces.isPullback_hom B S hS sq).hom_ext h₁ h₂

variable {W₂ : SmallEtale B S hS X.1}
  (b₂ : (SmallEtale.toOver B S hS X.1).obj W₂ ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
  (hb₂ : W₂.1.hom ≫ f.hom = yoneda.map b₂ ≫ V.1.hom) (m : W ⟶ W₂)
  (hm : (SmallEtale.toOver B S hS X.1).map m ≫ b₂ = b)

/-- The morphism `W ×_V U' ⟶ W₂ ×_V U'` of étale scheme charts of `X'` induced by a morphism
`W ⟶ W₂` of étale scheme charts of `X` over `V`. -/
def chartBaseChangeAlongMap :
    chartBaseChangeAlong sq d hd b hb ⟶ chartBaseChangeAlong sq d hd b₂ hb₂ :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (pullback.map b d b₂ d ((SmallEtale.toOver B S hS X.1).map m) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, hm]) (by rw [Category.comp_id, Category.id_comp])) (by
    refine chartBaseChangeAlong_hom_ext sq _ _ ?_ ?_
    · rw [Category.assoc, chartBaseChangeAlong_fst, chartBaseChangeAlong_fst]
      exact map_comp_map_comp_eq yoneda _ _ _ _ _ _ (pullback.lift_fst _ _ _)
        (CostructuredArrow.w m.hom)
    · rw [Category.assoc, chartBaseChangeAlong_snd, chartBaseChangeAlong_snd]
      exact map_comp_map_comp_eq yoneda _ _ _ (𝟙 _) _ _
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _).symm)
        ((congrArg (· ≫ U'.1.hom) (yoneda.map_id _)).trans (Category.id_comp _))))

/-- The induced morphism is compatible with the first projections. -/
theorem chartBaseChangeAlongMap_fst :
    (SmallEtale.toOver B S hS X'.1).map (chartBaseChangeAlongMap sq d hd b hb b₂ hb₂ m hm) ≫
        pullback.fst b₂ d = pullback.fst b d ≫ (SmallEtale.toOver B S hS X.1).map m :=
  pullback.lift_fst _ _ _

/-- The induced morphism is compatible with the second projections. -/
theorem chartBaseChangeAlongMap_snd :
    (SmallEtale.toOver B S hS X'.1).map (chartBaseChangeAlongMap sq d hd b hb b₂ hb₂ m hm) ≫
        pullback.snd b₂ d = pullback.snd b d :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The chart diagram `W ×_V U' ⟶ U'` over `f'`. -/
abbrev chartBaseChangeAlongDiagram : ChartDiagram B S hS X'.1 Y'.1 f'.hom :=
  ⟨chartBaseChangeAlong sq d hd b hb, U', pullback.snd b d, chartBaseChangeAlong_snd sq d hd b hb⟩

/-- The image of the cartesian form of a chart diagram in the algebraic spaces is the morphism
to the base change whose two components are the structure morphism and the vertical morphism. -/
theorem toSpaces_map_chartLift_comp_inclusion {P Q : AlgebraicSpaces B S hS} (p : P ⟶ Q)
    (e : ChartDiagram B S hS P.1 Q.1 p.hom) :
    (SpacesEtale.toSpaces B S hS P).map (chartLift B S hS p e) ≫
        chartBaseChangeInclusion B S hS p e.V = chartToSpace B S hS P e.U :=
  ObjectProperty.hom_ext _ (congrArg (fun k => k.hom)
    (((SpacesEtale.inclusion B S hS P).map (chartLift B S hS p e)).w))

/-- A morphism into the base change, with the right components, is the image of the chart lift. -/
private theorem toSpaces_map_chartLift_eq {P Q : AlgebraicSpaces B S hS} (p : P ⟶ Q)
    (e : ChartDiagram B S hS P.1 Q.1 p.hom)
    (t : chartSpace B S hS P e.U ⟶ chartBaseChangeSpace B S hS p e.V)
    (h₁ : t ≫ chartBaseChangeInclusion B S hS p e.V = chartToSpace B S hS P e.U)
    (h₂ : t ≫ chartBaseChangeProjection B S hS p e.V = chartSpaceMapOver B S hS e.g) :
    (SpacesEtale.toSpaces B S hS P).map (chartLift B S hS p e) = t :=
  (isPullback_chartBaseChangeInclusion B S hS p e.V).hom_ext
    ((toSpaces_map_chartLift_comp_inclusion p e).trans h₁.symm)
    ((chartLift_projection B S hS p e).trans h₂.symm)

include hb hd in
/-- **The cartesian form of `W ×_V U' ⟶ U'` is surjective as soon as that of `W ⟶ V` is.** -/
theorem isSurjective_chartLift_chartBaseChangeAlongDiagram
    (hsurj : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map
      (chartLift B S hS f ⟨W, V, b, hb⟩)).hom) :
    IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X').map
      (chartLift B S hS f' (chartBaseChangeAlongDiagram sq d hd b hb))).hom := by
  obtain ⟨τ', w, h, hT, e4, e2, e5, e3⟩ := exists_isPullback_chartBaseChangeAlongSpace sq d hd b hb
  have hw := toSpaces_map_chartLift_eq f ⟨W, V, b, hb⟩ w e5 e3
  have hτ := toSpaces_map_chartLift_eq f' (chartBaseChangeAlongDiagram sq d hd b hb) τ' e4 e2
  rw [hτ]
  rw [hw] at hsurj
  exact surjective_pointsMap_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS hT) hsurj

/-- The square of schemes underlying `W ×_V U'` is cartesian. -/
theorem isPullback_chartScheme_chartBaseChangeAlong :
    IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst b d))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd b d))
      ((BigFppfOver.toScheme B S hS).map b) ((BigFppfOver.toScheme B S hS).map d) :=
  (IsPullback.of_hasPullback b d).map (BigFppfOver.toScheme B S hS)

/-- **The base change of an affine chart along a diagram of affine charts is affine.** -/
theorem isAffine_chartBaseChangeAlong (hW : IsAffine (chartScheme W))
    (hU : IsAffine (chartScheme U')) (hV : IsAffine (chartScheme V)) :
    IsAffine (chartScheme (chartBaseChangeAlong sq d hd b hb)) := by
  have := hW
  have := hU
  have := hV
  exact IsAffine.of_isPullback (isPullback_chartScheme_chartBaseChangeAlong d b)

end AlgebraicGeometry.Space

end
