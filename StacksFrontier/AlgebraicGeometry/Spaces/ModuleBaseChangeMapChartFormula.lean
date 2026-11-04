module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFMapCompChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeUnitSquare

/-!
# The degree-zero base change map on chart sections

Let

```
X' --g'--> X
|f'         |f
v           v
Y' --g-->  Y
```

be a commutative square of algebraic spaces over a scheme `S` of a big fppf site `B`, and let
`F` be an `𝒪_X`-module.  `AlgebraicGeometry.Space.moduleBaseChangeMap` is the base change map
`g^*f_*F ⟶ f'_*(g')^*F`.  This file computes it on chart sections: for étale scheme charts
`T` of `X'`, `W` of `X`, `U'` of `Y'` and `V` of `Y` with vertical morphisms making the cube
commute, the base change map carries the unit section over `U'` of a section `s` of `f_*F` over
`V` to a section of `f'_*(g')^*F` over `U'` whose projection to `T` is the unit section, along
`T ⟶ W`, of the projection of `s` to `W`.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardCounitApp_moduleBaseChangeMap_unitSection`: the
  chart formula.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Transport

variable {X Y : AlgebraicSpaces B S hS}

/-- The linear map of sections of a morphism into a direct image, transported along an equality
of the two morphisms, at a chart diagram over the second morphism, is the linear map of sections
of the original morphism at the same charts read over the first. -/
theorem modulePushforwardCounitApp_comp_eqToHom {k₁ k₂ : X ⟶ Y} (h : k₁ = k₂)
    (F : Modules.{u, u} B S hS X.1 X.2) {N : Modules.{u, u} B S hS Y.1 Y.2}
    (ψ : N ⟶ (modulePushforward B S hS k₁).obj F) {U : SmallEtale B S hS X.1}
    {V : SmallEtale B S hS Y.1}
    (g₁ g₂ : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hg : g₂ = g₁) (c₁ : U.1.hom ≫ k₁.hom = yoneda.map g₁ ≫ V.1.hom)
    (c₂ : U.1.hom ≫ k₂.hom = yoneda.map g₂ ≫ V.1.hom) (s : N.val.obj (op V)) :
    modulePushforwardCounitApp B S hS k₂ F ⟨U, V, g₂, c₂⟩
        ((ψ ≫ eqToHom (congrArg (fun k : X ⟶ Y => (modulePushforward B S hS k).obj F) h)).val.app
          (op V) s) =
      modulePushforwardCounitApp B S hS k₁ F ⟨U, V, g₁, c₁⟩ (ψ.val.app (op V) s) := by
  subst h hg
  simp

/-- The linear map of sections of a morphism into a direct image, at a chart diagram. -/
theorem modulePushforwardHomFMap_app (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (φ : G ⟶ (modulePushforward B S hS f).obj F)
    (D : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op D.V)) :
    (modulePushforwardHomFMap B S hS f F G φ).app D s =
      modulePushforwardCounitApp B S hS f F D (φ.val.app (op D.V) s) := rfl

/-- The linear map of sections of the unit of `f^* ⊣ f_*` is the unit section. -/
theorem modulePushforwardHomFMap_unit_app (f : X ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (D : ChartDiagram B S hS X.1 Y.1 f.hom) (s : N.val.obj (op D.V)) :
    (modulePushforwardHomFMap B S hS f _ N ((modulePullbackAdjunction B S hS f).unit.app N)).app
        D s = modulePullbackUnitSection B S hS f N D s := rfl

/-- The identity morphism of modules on sections. -/
theorem id_val_app_apply' (N : Modules.{u, u} B S hS Y.1 Y.2) (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : N.val.obj V) : (𝟙 N : N ⟶ N).val.app V s = s := rfl

end Transport

section CompOfIso

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The composite of two linear maps of sections, at a composed chart diagram, is the linear map
of sections of the composite morphism into the direct image, at the same charts. -/
theorem ModuleFMap.compOfIso_app_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G)
    (ι : modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
      modulePushforward B S hS (f ≫ g)) (s : H.val.obj (op W)) :
    (ModuleFMap.compOfIso B S hS f g F G H ξ η ι).app (ChartDiagram.comp B S hS f g a b ha hb) s =
      modulePushforwardCounitApp B S hS (f ≫ g) F
        ⟨U, W, a ≫ b, (ChartDiagram.comp B S hS f g a b ha hb).comm⟩
        ((moduleFMapCompHom B S hS f g F G H ξ η ι).val.app (op W) s) := rfl

end CompOfIso


section Abstract

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- The unit identity of an inverse mate, with the mate supplied as a variable together with the
equation that identifies it. -/
theorem unit_comp_map_mateEquiv_symm_app {A : Type u₁} {B' : Type u₂} {C : Type u₃}
    {D : Type u₄} [Category.{v₁} A] [Category.{v₂} B'] [Category.{v₃} C] [Category.{v₄} D]
    {G : A ⥤ C} {H : B' ⥤ D} {L₁ : A ⥤ B'} {R₁ : B' ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : R₁ ⋙ G ⟶ H ⋙ R₂) (β : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hβ : β = (mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ α)) (c : A) :
    adj₂.unit.app (G.obj c) ≫ R₂.map (β.app c) = G.map (adj₁.unit.app c) ≫ α.app (L₁.obj c) := by
  subst hβ
  exact (unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ α) c).symm

/-- The component of a composite `a ≫ eqToHom e ≫ c⁻¹` of natural transformations, followed by
the component of `c`, stated over variables. -/
theorem comp_eqToHom_comp_inv_app_comp_hom_app {A : Type u₁} {C : Type u₃} [Category.{v₁} A]
    [Category.{v₃} C] {ι : Sort*} {P Q : A ⥤ C} (Φ : ι → A ⥤ C) {i j : ι} (a : P ≅ Φ i)
    (c : Q ≅ Φ j) (h : i = j) (sq : P ⟶ Q) (hsq : sq = a.hom ≫ eqToHom (congrArg Φ h) ≫ c.inv)
    (K : A) :
    sq.app K ≫ c.hom.app K = a.hom.app K ≫ eqToHom (congrArg (fun k => (Φ k).obj K) h) := by
  subst h hsq
  simp

/-- A composite ending in the inverse of an isomorphism, followed by the isomorphism. -/
theorem comp_comp_inv_comp_hom {C : Type u₃} [Category.{v₃} C] {W X Y Z : C} (x : W ⟶ X)
    (e : X ⟶ Z) (c : Y ≅ Z) : (x ≫ e ≫ c.inv) ≫ c.hom = x ≫ e := by
  simp

/-- Two rewrites of a composite, over variables. -/
theorem comp_eq_of_eq_comp_of_comp_eq {C : Type u₃} [Category.{v₃} C] {P Q R T Z : C}
    {a : P ⟶ R} {b : P ⟶ Q} {c : Q ⟶ R} {d : R ⟶ Z} {e : Q ⟶ T} {k : T ⟶ Z}
    (h1 : a = b ≫ c) (h2 : c ≫ d = e ≫ k) : a ≫ d = (b ≫ e) ≫ k := by
  rw [h1, Category.assoc, h2, Category.assoc]

/-- Reassociating the left-hand side of a chain of two equations, over variables. -/
theorem eq_of_eq_assoc {C : Type u₃} [Category.{v₃} C] {P Q R T : C} {m : P ⟶ T}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ T} {n : P ⟶ T} (h1 : m = a ≫ b ≫ c)
    (h2 : (a ≫ b) ≫ c = n) : m = n := by
  rw [h1, ← Category.assoc, h2]

end Abstract

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g) (F : Modules.{u, u} B S hS X.1 X.2)

/-- **The transpose of the base change map along `g^* ⊣ g_*`** is the direct image along `f` of
the unit of `(g')^* ⊣ g'_*`, followed by the comparison of the two composite direct images. -/
theorem unit_comp_map_moduleBaseChangeMap_app :
    (modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj F) ≫
        (modulePushforward B S hS g).map ((moduleBaseChangeMap f g f' g' comm).app F) =
      (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS g').unit.app F) ≫
        (modulePushforwardSquareComparison B S hS g' f' f g comm).app
          ((modulePullback B S hS g').obj F) :=
  unit_comp_map_mateEquiv_symm_app (modulePullbackAdjunction B S hS g')
    (modulePullbackAdjunction B S hS g) (modulePushforwardSquareComparison B S hS g' f' f g comm)
    (moduleBaseChangeMap f g f' g' comm) rfl F

/-- The linear map of sections of a morphism into a direct image carries back to that morphism. -/
theorem moduleFMapHom_modulePushforwardHomFMap {P Q : AlgebraicSpaces B S hS} (p : P ⟶ Q)
    (M : Modules.{u, u} B S hS P.1 P.2) (G : Modules.{u, u} B S hS Q.1 Q.2)
    (a : G ⟶ (modulePushforward B S hS p).obj M) :
    moduleFMapHom B S hS p M G (modulePushforwardHomFMap B S hS p M G a) = a :=
  (modulePushforwardHomEquiv B S hS p M G).symm_apply_apply a

/-- The composite of the linear maps of sections of two morphisms into direct images is the
composite of the morphisms followed by the comparison. -/
theorem moduleFMapCompHom_modulePushforwardHomFMap {P Q R : AlgebraicSpaces B S hS}
    (p : P ⟶ Q) (q : Q ⟶ R) (M : Modules.{u, u} B S hS P.1 P.2)
    (G : Modules.{u, u} B S hS Q.1 Q.2) (H : Modules.{u, u} B S hS R.1 R.2)
    (a : H ⟶ (modulePushforward B S hS q).obj G) (b : G ⟶ (modulePushforward B S hS p).obj M)
    (ι : modulePushforward B S hS p ⋙ modulePushforward B S hS q ≅
      modulePushforward B S hS (p ≫ q)) :
    moduleFMapCompHom B S hS p q M G H (modulePushforwardHomFMap B S hS q G H a)
        (modulePushforwardHomFMap B S hS p M G b) ι =
      a ≫ (modulePushforward B S hS q).map b ≫ ι.hom.app M := by
  rw [moduleFMapCompHom_eq, moduleFMapHom_modulePushforwardHomFMap,
    moduleFMapHom_modulePushforwardHomFMap]

/-- `AlgebraicGeometry.Space.modulePushforwardSquareComparison` is its definition, read as an
equation of natural transformations. -/
theorem modulePushforwardSquareComparison_def :
    modulePushforwardSquareComparison B S hS g' f' f g comm =
      (modulePushforwardCompIso B S hS g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) comm) ≫
        (modulePushforwardCompIso B S hS f' g).inv :=
  rfl


/-- The comparison of the two composite direct images around the square, at a module, followed by
the composition comparison along `f' ≫ g`, is the composition comparison along `g' ≫ f` followed
by the transport along the commutativity of the square. -/
theorem modulePushforwardSquareComparison_app_comp_compIso (K : Modules.{u, u} B S hS X'.1 X'.2) :
    (modulePushforwardSquareComparison B S hS g' f' f g comm).app K ≫
        (modulePushforwardCompIso B S hS f' g).hom.app K =
      (modulePushforwardCompIso B S hS g' f).hom.app K ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => (modulePushforward B S hS k).obj K) comm) := by
  have h1 : (modulePushforwardSquareComparison B S hS g' f' f g comm).app K =
      (modulePushforwardCompIso B S hS g' f).hom.app K ≫
        ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) comm)).app K ≫
          (modulePushforwardCompIso B S hS f' g).inv.app K) :=
    (NatTrans.congr_app (modulePushforwardSquareComparison_def f g f' g' comm) K).trans
      ((NatTrans.comp_app _ _ _).trans (congrArg (_ ≫ ·) (NatTrans.comp_app _ _ _)))
  have h2 : (eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) comm)).app K =
      eqToHom (congrArg (fun k : X' ⟶ Y => (modulePushforward B S hS k).obj K) comm) :=
    eqToHom_app _ _
  rw [h1, h2]
  exact comp_comp_inv_comp_hom _ _ ((modulePushforwardCompIso B S hS f' g).app K)

/-- **The two composites of the transposes around the square agree**, up to the transport along
the commutativity of the square: the unit of `g^* ⊣ g_*` followed by the direct image of the base
change map and the comparison along `f' ≫ g`, against the direct image of the unit of
`(g')^* ⊣ g'_*` followed by the comparison along `g' ≫ f`. -/
theorem unit_comp_map_moduleBaseChangeMap_comp_compIso :
    ((modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj F) ≫
        (modulePushforward B S hS g).map ((moduleBaseChangeMap f g f' g' comm).app F)) ≫
        (modulePushforwardCompIso B S hS f' g).hom.app ((modulePullback B S hS g').obj F) =
      ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS g').unit.app F) ≫
        (modulePushforwardCompIso B S hS g' f).hom.app ((modulePullback B S hS g').obj F)) ≫
        eqToHom (congrArg (fun k : X' ⟶ Y =>
          (modulePushforward B S hS k).obj ((modulePullback B S hS g').obj F)) comm) :=
  comp_eq_of_eq_comp_of_comp_eq (unit_comp_map_moduleBaseChangeMap_app f g f' g' comm F)
    (modulePushforwardSquareComparison_app_comp_compIso f g f' g' comm
      ((modulePullback B S hS g').obj F))

variable {f g f' g'} in
/-- **The chart formula for the base change map.**  For étale scheme charts `T` of `X'`, `W` of
`X`, `U'` of `Y'` and `V` of `Y`, with vertical morphisms `a : T ⟶ W` over `g'`, `b : W ⟶ V`
over `f`, `c : T ⟶ U'` over `f'` and `d : U' ⟶ V` over `g` such that `a ≫ b = c ≫ d`, the base
change map carries the unit section over `U'` of a section `s` of `f_*F` over `V` to the section
of `f'_*(g')^*F` over `U'` whose projection to `T` is the unit section along `a` of the
projection of `s` to `W`. -/
theorem modulePushforwardCounitApp_moduleBaseChangeMap_unitSection
    {T : SmallEtale B S hS X'.1} {W : SmallEtale B S hS X.1} {U' : SmallEtale B S hS Y'.1}
    {V : SmallEtale B S hS Y.1}
    (a : (SmallEtale.toOver B S hS X'.1).obj T ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (c : (SmallEtale.toOver B S hS X'.1).obj T ⟶ (SmallEtale.toOver B S hS Y'.1).obj U')
    (d : (SmallEtale.toOver B S hS Y'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (ha : T.1.hom ≫ g'.hom = yoneda.map a ≫ W.1.hom)
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom)
    (hc : T.1.hom ≫ f'.hom = yoneda.map c ≫ U'.1.hom)
    (hd : U'.1.hom ≫ g.hom = yoneda.map d ≫ V.1.hom) (habcd : a ≫ b = c ≫ d)
    (s : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    modulePushforwardCounitApp B S hS f' ((modulePullback B S hS g').obj F) ⟨T, U', c, hc⟩
        (((moduleBaseChangeMap f g f' g' comm).app F).val.app (op U')
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj F)
            ⟨U', V, d, hd⟩ s)) =
      modulePullbackUnitSection B S hS g' F ⟨T, W, a, ha⟩
        (modulePushforwardCounitApp B S hS f F ⟨W, V, b, hb⟩ s) := by
  have e1 : (modulePushforwardHomFMap B S hS f' ((modulePullback B S hS g').obj F)
        ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
        ((moduleBaseChangeMap f g f' g' comm).app F)).app ⟨T, U', c, hc⟩
        ((modulePushforwardHomFMap B S hS g
            ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
            ((modulePushforward B S hS f).obj F)
            ((modulePullbackAdjunction B S hS g).unit.app
              ((modulePushforward B S hS f).obj F))).app ⟨U', V, d, hd⟩ s) =
      modulePushforwardCounitApp B S hS f' ((modulePullback B S hS g').obj F) ⟨T, U', c, hc⟩
        (((moduleBaseChangeMap f g f' g' comm).app F).val.app (op U')
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj F)
            ⟨U', V, d, hd⟩ s)) :=
    (modulePushforwardHomFMap_app f' ((modulePullback B S hS g').obj F)
        ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
        ((moduleBaseChangeMap f g f' g' comm).app F) ⟨T, U', c, hc⟩ _).trans
      (congrArg (fun y => modulePushforwardCounitApp B S hS f'
          ((modulePullback B S hS g').obj F) ⟨T, U', c, hc⟩
          (((moduleBaseChangeMap f g f' g' comm).app F).val.app (op U') y))
        (modulePushforwardHomFMap_unit_app g ((modulePushforward B S hS f).obj F)
          ⟨U', V, d, hd⟩ s))
  have h1 := ModuleFMap.compOfIso_app B S hS f' g c d hc hd ((modulePullback B S hS g').obj F)
    ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
    ((modulePushforward B S hS f).obj F)
    (modulePushforwardHomFMap B S hS g
      ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
      ((modulePushforward B S hS f).obj F)
      ((modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj F)))
    (modulePushforwardHomFMap B S hS f' ((modulePullback B S hS g').obj F)
      ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
      ((moduleBaseChangeMap f g f' g' comm).app F))
    (modulePushforwardCompIso B S hS f' g)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f' g
      ((modulePullback B S hS g').obj F)) s
  have h1' := ModuleFMap.compOfIso_app_comp f' g c d hc hd ((modulePullback B S hS g').obj F)
    ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
    ((modulePushforward B S hS f).obj F)
    (modulePushforwardHomFMap B S hS g _ _ ((modulePullbackAdjunction B S hS g).unit.app
      ((modulePushforward B S hS f).obj F)))
    (modulePushforwardHomFMap B S hS f' _ _ ((moduleBaseChangeMap f g f' g' comm).app F))
    (modulePushforwardCompIso B S hS f' g) s
  have h2 := ModuleFMap.compOfIso_app B S hS g' f a b ha hb ((modulePullback B S hS g').obj F) F
    ((modulePushforward B S hS f).obj F)
    (modulePushforwardHomFMap B S hS f F ((modulePushforward B S hS f).obj F)
      (𝟙 ((modulePushforward B S hS f).obj F)))
    (modulePushforwardHomFMap B S hS g' ((modulePullback B S hS g').obj F) F
      ((modulePullbackAdjunction B S hS g').unit.app F))
    (modulePushforwardCompIso B S hS g' f)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS g' f
      ((modulePullback B S hS g').obj F)) s
  have h2' := ModuleFMap.compOfIso_app_comp g' f a b ha hb ((modulePullback B S hS g').obj F) F
    ((modulePushforward B S hS f).obj F)
    (modulePushforwardHomFMap B S hS f F _ (𝟙 ((modulePushforward B S hS f).obj F)))
    (modulePushforwardHomFMap B S hS g' _ F ((modulePullbackAdjunction B S hS g').unit.app F))
    (modulePushforwardCompIso B S hS g' f) s
  have h3a : moduleFMapCompHom B S hS f' g ((modulePullback B S hS g').obj F)
        ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
        ((modulePushforward B S hS f).obj F)
        (modulePushforwardHomFMap B S hS g
          ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
          ((modulePushforward B S hS f).obj F)
          ((modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj F)))
        (modulePushforwardHomFMap B S hS f' ((modulePullback B S hS g').obj F)
          ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
          ((moduleBaseChangeMap f g f' g' comm).app F))
        (modulePushforwardCompIso B S hS f' g) =
      (modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj F) ≫
        (modulePushforward B S hS g).map ((moduleBaseChangeMap f g f' g' comm).app F) ≫
        (modulePushforwardCompIso B S hS f' g).hom.app ((modulePullback B S hS g').obj F) :=
    moduleFMapCompHom_modulePushforwardHomFMap f' g ((modulePullback B S hS g').obj F)
      ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
      ((modulePushforward B S hS f).obj F) _ ((moduleBaseChangeMap f g f' g' comm).app F) _
  have h3b := unit_comp_map_moduleBaseChangeMap_comp_compIso f g f' g' comm F
  have h3 : moduleFMapCompHom B S hS f' g ((modulePullback B S hS g').obj F)
        ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
        ((modulePushforward B S hS f).obj F)
        (modulePushforwardHomFMap B S hS g
          ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
          ((modulePushforward B S hS f).obj F)
          ((modulePullbackAdjunction B S hS g).unit.app ((modulePushforward B S hS f).obj F)))
        (modulePushforwardHomFMap B S hS f' ((modulePullback B S hS g').obj F)
          ((modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F))
          ((moduleBaseChangeMap f g f' g' comm).app F))
        (modulePushforwardCompIso B S hS f' g) =
      ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS g').unit.app F) ≫
        (modulePushforwardCompIso B S hS g' f).hom.app ((modulePullback B S hS g').obj F)) ≫
        eqToHom (congrArg (fun k : X' ⟶ Y =>
          (modulePushforward B S hS k).obj ((modulePullback B S hS g').obj F)) comm) :=
    eq_of_eq_assoc h3a h3b
  have h5 : moduleFMapCompHom B S hS g' f ((modulePullback B S hS g').obj F) F
        ((modulePushforward B S hS f).obj F)
        (modulePushforwardHomFMap B S hS f F ((modulePushforward B S hS f).obj F)
          (𝟙 ((modulePushforward B S hS f).obj F)))
        (modulePushforwardHomFMap B S hS g' ((modulePullback B S hS g').obj F) F
          ((modulePullbackAdjunction B S hS g').unit.app F))
        (modulePushforwardCompIso B S hS g' f) =
      (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS g').unit.app F) ≫
        (modulePushforwardCompIso B S hS g' f).hom.app ((modulePullback B S hS g').obj F) :=
    (moduleFMapCompHom_modulePushforwardHomFMap g' f ((modulePullback B S hS g').obj F) F
        ((modulePushforward B S hS f).obj F) (𝟙 ((modulePushforward B S hS f).obj F)) _ _).trans
      (Category.id_comp _)
  have h4 := modulePushforwardCounitApp_comp_eqToHom comm ((modulePullback B S hS g').obj F)
    ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS g').unit.app F) ≫
        (modulePushforwardCompIso B S hS g' f).hom.app ((modulePullback B S hS g').obj F))
    (a ≫ b) (c ≫ d) habcd.symm (ChartDiagram.comp B S hS g' f a b ha hb).comm
    (ChartDiagram.comp B S hS f' g c d hc hd).comm s
  have e2 : (modulePushforwardHomFMap B S hS g' ((modulePullback B S hS g').obj F) F
        ((modulePullbackAdjunction B S hS g').unit.app F)).app ⟨T, W, a, ha⟩
        ((modulePushforwardHomFMap B S hS f F ((modulePushforward B S hS f).obj F)
          (𝟙 ((modulePushforward B S hS f).obj F))).app ⟨W, V, b, hb⟩ s) =
      modulePullbackUnitSection B S hS g' F ⟨T, W, a, ha⟩
        (modulePushforwardCounitApp B S hS f F ⟨W, V, b, hb⟩ s) :=
    (modulePushforwardHomFMap_unit_app g' F ⟨T, W, a, ha⟩ _).trans
      (congrArg (modulePullbackUnitSection B S hS g' F ⟨T, W, a, ha⟩)
        ((modulePushforwardHomFMap_app f F ((modulePushforward B S hS f).obj F)
            (𝟙 ((modulePushforward B S hS f).obj F)) ⟨W, V, b, hb⟩ s).trans
          (congrArg (modulePushforwardCounitApp B S hS f F ⟨W, V, b, hb⟩)
            (id_val_app_apply' ((modulePushforward B S hS f).obj F) (op V) s))))
  have k1 := (e1.symm.trans h1.symm).trans h1'
  have k3 := congrArg (fun m : (modulePushforward B S hS f).obj F ⟶
      (modulePushforward B S hS (f' ≫ g)).obj ((modulePullback B S hS g').obj F) =>
    modulePushforwardCounitApp B S hS (f' ≫ g) ((modulePullback B S hS g').obj F)
      ⟨T, V, c ≫ d, (ChartDiagram.comp B S hS f' g c d hc hd).comm⟩
        (m.val.app (op V) s)) h3
  have k5 := congrArg (fun m : (modulePushforward B S hS f).obj F ⟶
      (modulePushforward B S hS (g' ≫ f)).obj ((modulePullback B S hS g').obj F) =>
    modulePushforwardCounitApp B S hS (g' ≫ f) ((modulePullback B S hS g').obj F)
      ⟨T, V, a ≫ b, (ChartDiagram.comp B S hS g' f a b ha hb).comm⟩
        (m.val.app (op V) s)) h5.symm
  exact (((k1.trans k3).trans h4).trans k5).trans ((h2'.symm.trans h2).trans e2)

end Square

end AlgebraicGeometry.Space

end
