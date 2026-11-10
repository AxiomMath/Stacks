module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksCore.Tactic.StacksAttribute

/-!
# Pasting of derived base change maps of algebraic spaces

Two commutative squares of algebraic spaces sharing an edge paste to a commutative rectangle,
and the base change map of Stacks 07A7 for the rectangle
(`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`) is the composite of the base
change maps of the two squares, read through the composition isomorphisms of the two composite
legs: the composition law of derived pullbacks of Stacks 0D6D for horizontally composable squares
(Stacks 0E47), and the composition isomorphism of derived direct images for vertically
composable ones (Stacks 0E46).

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeMap_horizontal`: Stacks 0E47.
* `AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeMap_vertical`: Stacks 0E46.
* `Stacks.CategoryTheory.BaseChange.map_vertical`: the vertical pasting law for base change maps
  of squares of adjunctions.

## References

* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)
open Stacks.Cohomology.DerivedBaseChangePasting

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Abstract bookkeeping -/

/-- A functor carries a pair of mutually inverse morphisms to a pair of mutually inverse
morphisms. -/
theorem map_comp_map_eq_id {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {P Q : C}
    {x : P ⟶ Q} {y : Q ⟶ P} (h : x ≫ y = 𝟙 P) : H.map x ≫ H.map y = 𝟙 (H.obj P) := by
  rw [← H.map_comp, h, H.map_id]

/-- **The component of a horizontal composite of 2-squares, whiskered at the top and bottom.** -/
theorem twoSquare_app_of_eq_hComp_whisker {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₅] [Category* C₆]
    {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆}
    {B' : C₄ ⥤ C₆} {Tc : C₁ ⥤ C₅} {Bc : C₃ ⥤ C₆} (So : TwoSquare Tc L R' Bc)
    (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B') (dT : Tc ⟶ T ⋙ T') (dB : B ⋙ B' ⟶ Bc)
    (h : So = ((TwoSquare.hComp w w').whiskerTop dT).whiskerBottom dB) (K : C₁) :
    So.app K = R'.map (dT.app K) ≫ w'.app (T.obj K) ≫
      B'.map (w.app K) ≫ dB.app (L.obj K) := by
  subst h
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]

/-- **Vertical pasting of base change maps of squares of adjunctions.**  For two vertically
stacked squares of left adjoints with comparisons `σt`, `σb` and an outer comparison `σr` that is
their vertical paste through the composition isomorphisms `c`, `c'` of the vertical legs, the
base change map of the outer rectangle is the composite of those of the two squares, read
through the induced comparisons of right adjoints. -/
theorem _root_.Stacks.CategoryTheory.BaseChange.map_vertical
    {DB DC DD DB' DC' DD' : Type*} [Category* DB] [Category* DC] [Category* DD]
    [Category* DB'] [Category* DC'] [Category* DD']
    {Lf : DC ⥤ DB} {Rf : DB ⥤ DC} {Lg : DD ⥤ DC} {Rg : DC ⥤ DD} {Lfg : DD ⥤ DB}
    {Rfg : DB ⥤ DD} {Lf' : DC' ⥤ DB'} {Rf' : DB' ⥤ DC'} {Lg' : DD' ⥤ DC'} {Rg' : DC' ⥤ DD'}
    {Lfg' : DD' ⥤ DB'} {Rfg' : DB' ⥤ DD'} {Lk : DB ⥤ DB'} {Ll : DC ⥤ DC'} {Lm : DD ⥤ DD'}
    {Ct : DC ⥤ DB'} {Cb : DD ⥤ DC'} {Cr : DD ⥤ DB'}
    (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjfg : Lfg ⊣ Rfg) (adjf' : Lf' ⊣ Rf')
    (adjg' : Lg' ⊣ Rg') (adjfg' : Lfg' ⊣ Rfg') (c : Lg ⋙ Lf ≅ Lfg) (c' : Lg' ⋙ Lf' ≅ Lfg')
    (egt : Ll ⋙ Lf' ≅ Ct) (eft : Lf ⋙ Lk ≅ Ct) (egb : Lm ⋙ Lg' ≅ Cb) (efb : Lg ⋙ Ll ≅ Cb)
    (egr : Lm ⋙ Lfg' ≅ Cr) (efr : Lfg ⋙ Lk ≅ Cr)
    (σt : ∀ N, Lf'.obj (Ll.obj N) ⟶ Lk.obj (Lf.obj N))
    (σb : ∀ M, Lg'.obj (Lm.obj M) ⟶ Ll.obj (Lg.obj M))
    (σr : ∀ M, Lfg'.obj (Lm.obj M) ⟶ Lk.obj (Lfg.obj M))
    (hσt : ∀ N, egt.hom.app N ≫ eft.inv.app N = σt N)
    (hσb : ∀ M, egb.hom.app M ≫ efb.inv.app M = σb M)
    (hσr : ∀ M, egr.hom.app M ≫ efr.inv.app M = σr M)
    (hpaste : ∀ M, σr M = c'.inv.app (Lm.obj M) ≫ Lf'.map (σb M) ≫ σt (Lg.obj M) ≫
      Lk.map (c.hom.app M)) (K : DB) :
    Lm.map ((Adjunction.rightAdjointUniq ((adjg.comp adjf).ofNatIsoLeft c) adjfg).inv.app K) ≫
        Stacks.CategoryTheory.BaseChange.map adjg adjg' egb efb (Rf.obj K) ≫
        Rg'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' egt eft K) ≫
        (Adjunction.rightAdjointUniq ((adjg'.comp adjf').ofNatIsoLeft c') adjfg').hom.app
          (Lk.obj K) =
      Stacks.CategoryTheory.BaseChange.map adjfg adjfg' egr efr K := by
  have hSo : Stacks.CategoryTheory.BaseChange.pullbackComparison egr efr =
      ((TwoSquare.vComp (Stacks.CategoryTheory.BaseChange.pullbackComparison egb efb)
          (Stacks.CategoryTheory.BaseChange.pullbackComparison egt eft)).whiskerLeft
        c.hom).whiskerRight c'.inv := by
    refine NatTrans.ext (funext fun M => ?_)
    have h := hpaste M
    rw [← hσr, ← hσb, ← hσt] at h
    simpa [Stacks.CategoryTheory.BaseChange.pullbackComparison, TwoSquare.vComp,
      TwoSquare.whiskerLeft, TwoSquare.whiskerRight, Functor.map_comp, Category.assoc] using h
  have hdL : conjugateEquiv adjfg (adjg.comp adjf) c.hom =
      (Adjunction.rightAdjointUniq ((adjg.comp adjf).ofNatIsoLeft c) adjfg).inv := by
    have h := conjugateEquiv_comm adjfg (adjg.comp adjf) (α := c.hom) (β := c.inv)
      (Iso.inv_hom_id _)
    rw [conjugateEquiv_iso_inv] at h
    exact (Iso.comp_hom_eq_id _).1 h
  have hm := mate_twoSquare_paste adjg adjg' adjf adjf' adjfg adjfg' _ _ _ c.hom c'.inv _ _ hSo
    hdL (conjugateEquiv_iso_inv _ _ _)
  exact (twoSquare_app_of_eq_hComp_whisker _ _ _ _ _ hm K).symm

section Transport

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The inverse of `smallEtaleDerivedModulePullbackCongr` is the componentwise transport. -/
theorem smallEtaleDerivedModulePullbackCongr_inv_app {p q : X ⟶ Y} (e : p = q)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedModulePullbackCongr B S hS e).inv.app M =
      (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
        e.symm)).app M := by
  subst e
  simp [smallEtaleDerivedModulePullbackCongr]

/-- The composition law is compatible with an equality of the inner morphism. -/
theorem smallEtaleDerivedModulePullbackCompIso_congr_left {p q : X ⟶ Y} (e : p = q)
    (g : Y ⟶ Z)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) e)).app
          ((smallEtaleDerivedModulePullback B S hS g).obj M) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS q g).hom.app M =
      (smallEtaleDerivedModulePullbackCompIso B S hS p g).hom.app M ≫
        (transportNatTrans (congrArg (fun t : X ⟶ Y => smallEtaleDerivedModulePullback B S hS
          (t ≫ g)) e)).app M := by
  subst e
  simp

/-- The composition law is compatible with an equality of the outer morphism. -/
theorem smallEtaleDerivedModulePullbackCompIso_congr_right (f : X ⟶ Y) {p q : Y ⟶ Z}
    (e : p = q)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedModulePullback B S hS f).map
          ((transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
            e)).app M) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS f q).hom.app M =
      (smallEtaleDerivedModulePullbackCompIso B S hS f p).hom.app M ≫
        (transportNatTrans (congrArg (fun t : Y ⟶ Z => smallEtaleDerivedModulePullback B S hS
          (f ≫ t)) e)).app M := by
  subst e
  simp

end Transport

/-! ### The adjoint characterization with the transport split off -/

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- A component of a composite, rewritten through a factorization of its middle factor. -/
theorem eq_comp_comp_of_eq {C : Type*} [Category* C] {P Q R T : C} {x : P ⟶ T} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : R ⟶ T} {Q' : C} {b₁ : Q ⟶ Q'} {b₂ : Q' ⟶ R} (h : x = a ≫ b ≫ c)
    (hb : b = b₁ ≫ b₂) : x = (a ≫ b₁ ≫ b₂) ≫ c := by
  subst h hb
  simp only [Category.assoc]

/-- The inverse of the composition law followed by the transport, componentwise. -/
theorem smallEtaleDerivedModulePullbackCompIso_trans_congr_inv_app (N : _) :
    (smallEtaleDerivedModulePullbackCompIso B S hS g' f ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS w).inv.app N =
      (smallEtaleDerivedModulePullbackCongr B S hS w).inv.app N ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS g' f).inv.app N :=
  NatTrans.congr_app (Iso.trans_inv _ _) N

/-- The inverse of the square comparison, with the transport split off. -/
theorem smallEtaleDerivedPullbackSquareIso_inv_app (N : _) :
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w).inv.app N =
      (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
        w.symm)).app N ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS g' f).inv.app N :=
  ((congrArg (fun E => E.inv.app N)
      (smallEtaleDerivedPullbackSquareIso_eq B S hS f g f' g' w)).trans
      (smallEtaleDerivedModulePullbackCompIso_trans_congr_inv_app B S hS f g f' g' w N)).trans
    (congrArg (· ≫ (smallEtaleDerivedModulePullbackCompIso B S hS g' f).inv.app N)
      (smallEtaleDerivedModulePullbackCongr_inv_app B S hS w N))

/-- **The adjoint characterization of the base change map, with the transport split off.** -/
theorem smallEtaleDerivedBaseChangeMap_adjoint_split (K : _) :
    ((smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ _).symm
        (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K) =
      ((smallEtaleDerivedModulePullbackCompIso B S hS f' g).hom.app
            ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
              (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) ≫
          (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
            w.symm)).app
            ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
              (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS g' f).inv.app
            ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
              (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K)) ≫
        (smallEtaleDerivedModulePullback B S hS g').map
          ((smallEtaleDerivedModuleAdjunction B S hS f).counit.app K) :=
  eq_comp_comp_of_eq (smallEtaleDerivedModuleBaseChangeMap_adjoint B S hS f g f' g' w K)
    (smallEtaleDerivedPullbackSquareIso_inv_app B S hS f g f' g' w _)

end Square

/-! ### Stacks 0E47 -/

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (f'' : X'' ⟶ Y'') (g' : X' ⟶ X) (g'' : X'' ⟶ X') (g : Y' ⟶ Y) (h : Y'' ⟶ Y')

/-- The outer rectangle of two horizontally composable commutative squares commutes. -/
theorem comp_rectangle_smallEtaleDerivedBaseChange (w : g' ≫ f = f' ≫ g) (w' : g'' ≫ f' = f'' ≫ h) :
    (g'' ≫ g') ≫ f = f'' ≫ h ≫ g := by
  rw [Category.assoc, w, ← Category.assoc, w', Category.assoc]

/-- **Horizontal composition of the comparisons of iterated derived pullbacks** for two
horizontally composable commutative squares of algebraic spaces. -/
theorem smallEtaleDerivedSquareComparison_horizontal (w : g' ≫ f = f' ≫ g)
    (w' : g'' ≫ f' = f'' ≫ h)
    (M : _) :
    (smallEtaleDerivedModulePullback B S hS f'').map
          ((smallEtaleDerivedModulePullbackCompIso B S hS h g).inv.app M) ≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS f'' h).hom.app
            ((smallEtaleDerivedModulePullback B S hS g).obj M) ≫
          (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
            w'.symm)).app
            ((smallEtaleDerivedModulePullback B S hS g).obj M) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS g'' f').inv.app
            ((smallEtaleDerivedModulePullback B S hS g).obj M)) ≫
        (smallEtaleDerivedModulePullback B S hS g'').map
          ((smallEtaleDerivedModulePullbackCompIso B S hS f' g).hom.app M ≫
            (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
              w.symm)).app M ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS g' f).inv.app M) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app
          ((smallEtaleDerivedModulePullback B S hS f).obj M) =
      (smallEtaleDerivedModulePullbackCompIso B S hS f'' (h ≫ g)).hom.app M ≫
        (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
          (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g'' g h w
            w').symm)).app M ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS (g'' ≫ g') f).inv.app M :=
  squareComparison_horizontal (smallEtaleDerivedModulePullbackCompIso B S hS h g)
    (smallEtaleDerivedModulePullbackCompIso B S hS g'' g')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackCompIso B S hS g' f)
    (smallEtaleDerivedModulePullbackCompIso B S hS f'' h)
    (smallEtaleDerivedModulePullbackCompIso B S hS g'' f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f'' (h ≫ g))
    (smallEtaleDerivedModulePullbackCompIso B S hS (g'' ≫ g') f)
    (smallEtaleDerivedModulePullbackCompIso B S hS (f'' ≫ h) g)
    (smallEtaleDerivedModulePullbackCompIso B S hS g'' (g' ≫ f))
    (smallEtaleDerivedModulePullbackCompIso B S hS g'' (f' ≫ g))
    (smallEtaleDerivedModulePullbackCompIso B S hS (g'' ≫ f') g)
    (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) w.symm)
    (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) w'.symm)
    (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
      (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g'' g h w w').symm)
    (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
      (show g'' ≫ f' ≫ g = g'' ≫ g' ≫ f by rw [w]))
    (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
      (show f'' ≫ h ≫ g = g'' ≫ f' ≫ g by rw [← Category.assoc, ← w', Category.assoc]))
    (fun N => smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS f'' h g N)
    (fun N => smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS g'' g' f N)
    (fun N => smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS g'' f' g N)
    (fun N => smallEtaleDerivedModulePullbackCompIso_congr_right B S hS g'' w.symm N)
    (fun N => smallEtaleDerivedModulePullbackCompIso_congr_left B S hS w'.symm g N)
    M

/-- **Stacks 0E47 for algebraic spaces.**  For two horizontally composable commutative squares
`g' ≫ f = f' ≫ g` and `g'' ≫ f' = f'' ≫ h` of algebraic spaces, the composite of the base change
maps of the two squares, read through the composition law of derived pullbacks for the two
composite horizontal legs, is the base change map of the outer rectangle. -/
theorem smallEtaleDerivedBaseChangeMap_horizontal (w : g' ≫ f = f' ≫ g)
    (w' : g'' ≫ f' = f'' ≫ h) (K : _) :
    (smallEtaleDerivedModulePullbackCompIso B S hS h g).inv.app
          ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) ≫
        (smallEtaleDerivedModulePullback B S hS h).map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K) ≫
        smallEtaleDerivedModuleBaseChangeMap B S hS f' h f'' g'' w'
          ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f'')).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').hom.app K) =
      smallEtaleDerivedModuleBaseChangeMap B S hS f (h ≫ g) f'' (g'' ≫ g')
        (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g'' g h w w') K :=
  baseChangeMate_horizontal (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS f') (smallEtaleDerivedModuleAdjunction B S hS f'')
    (smallEtaleDerivedModulePullbackCompIso B S hS g'' g')
    (smallEtaleDerivedModulePullbackCompIso B S hS h g)
    _
    (smallEtaleDerivedModulePullbackCompIso B S hS f'' h).hom
    (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) w'.symm))
    (smallEtaleDerivedModulePullbackCompIso B S hS g'' f').inv
    _
    (smallEtaleDerivedSquareComparison_horizontal B S hS f f' f'' g' g'' g h w w')
    K _ _ _
    (smallEtaleDerivedBaseChangeMap_adjoint_split B S hS f g f' g' w K)
    (smallEtaleDerivedBaseChangeMap_adjoint_split B S hS f' h f'' g'' w'
      ((smallEtaleDerivedModulePullback B S hS g').obj K))
    (smallEtaleDerivedBaseChangeMap_adjoint_split B S hS f (h ≫ g) f'' (g'' ≫ g')
      (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g'' g h w w') K)

end Horizontal

/-! ### Stacks 0E46 -/

section Vertical

variable {X X' Y Y' Z Z' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y')
  (g' : Y' ⟶ Z') (k : X' ⟶ X) (l : Y' ⟶ Y) (m : Z' ⟶ Z)

/-- The outer rectangle of two vertically composable commutative squares commutes. -/
theorem comp_stack (wtop : k ≫ f = f' ≫ l) (wbot : l ≫ g = g' ≫ m) :
    k ≫ f ≫ g = (f' ≫ g') ≫ m := by
  rw [← Category.assoc, wtop, Category.assoc, wbot, Category.assoc]

/-- **Vertical composition of the comparisons of iterated derived pullbacks** for two vertically
composable commutative squares of algebraic spaces: the transposed form of
`AlgebraicGeometry.Space.smallEtaleDerivedSquareComparison_horizontal`. -/
theorem smallEtaleDerivedSquareComparison_vertical (wtop : k ≫ f = f' ≫ l)
    (wbot : l ≫ g = g' ≫ m) (M : _) :
    (smallEtaleDerivedModulePullbackCompIso B S hS (f' ≫ g') m).hom.app M ≫
        (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
          (comp_stack B S hS f g f' g' k l m wtop wbot).symm)).app M ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS k (f ≫ g)).inv.app M =
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g').inv.app
          ((smallEtaleDerivedModulePullback B S hS m).obj M) ≫
        (smallEtaleDerivedModulePullback B S hS f').map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g' m).hom.app M ≫
            (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
              wbot.symm)).app M ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS l g).inv.app M) ≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS f' l).hom.app
            ((smallEtaleDerivedModulePullback B S hS g).obj M) ≫
          (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
            wtop.symm)).app ((smallEtaleDerivedModulePullback B S hS g).obj M) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS k f).inv.app
            ((smallEtaleDerivedModulePullback B S hS g).obj M)) ≫
        (smallEtaleDerivedModulePullback B S hS k).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app M) :=
  (comp₄_inv
      ((smallEtaleDerivedModulePullback B S hS k).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS f g).inv.app M))
      ((smallEtaleDerivedModulePullback B S hS k).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app M))
      ((smallEtaleDerivedModulePullback B S hS f').map
        ((smallEtaleDerivedModulePullbackCompIso B S hS l g).hom.app M ≫
          (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
            wbot)).app M ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS g' m).inv.app M))
      ((smallEtaleDerivedModulePullback B S hS f').map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g' m).hom.app M ≫
          (transportNatTrans (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
            wbot.symm)).app M ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS l g).inv.app M))
      (map_comp_map_eq_id _ (Iso.hom_inv_id_app _ _))
      (squareComparison_comp_symm (smallEtaleDerivedModulePullbackCompIso B S hS f' l)
        (smallEtaleDerivedModulePullbackCompIso B S hS k f)
        (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) wtop.symm)
        (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) wtop) _)
      (map_comp_map_eq_id _ (squareComparison_comp_symm
        (smallEtaleDerivedModulePullbackCompIso B S hS g' m)
        (smallEtaleDerivedModulePullbackCompIso B S hS l g)
        (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) wbot.symm)
        (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) wbot) M))
      (Iso.inv_hom_id_app (smallEtaleDerivedModulePullbackCompIso B S hS f' g')
        ((smallEtaleDerivedModulePullback B S hS m).obj M))
      (squareComparison_comp_symm (smallEtaleDerivedModulePullbackCompIso B S hS k (f ≫ g))
        (smallEtaleDerivedModulePullbackCompIso B S hS (f' ≫ g') m)
        (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
          (comp_stack B S hS f g f' g' k l m wtop wbot))
        (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
          (comp_rectangle_smallEtaleDerivedBaseChange B S hS m l k g' f' g f wbot.symm
            wtop.symm)) M)
      (smallEtaleDerivedSquareComparison_horizontal B S hS m l k g' f' g f wbot.symm wtop.symm
        M)).symm

/-- **Stacks 0E46 for algebraic spaces.**  For two vertically composable commutative squares
`k ≫ f = f' ≫ l` and `l ≫ g = g' ≫ m` of algebraic spaces, the composite of the base change maps
of the two squares, read through the composition isomorphisms of derived direct images for the
two composite vertical legs, is the base change map of the outer rectangle. -/
theorem smallEtaleDerivedBaseChangeMap_vertical (wtop : k ≫ f = f' ≫ l)
    (wbot : l ≫ g = g' ≫ m) (K : _) :
    (smallEtaleDerivedModulePullback B S hS m).map
          ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS f g).inv.app K) ≫
        smallEtaleDerivedModuleBaseChangeMap B S hS g m g' l wbot
          ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS g')).map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f l f' k wtop K) ≫
        (smallEtaleDerivedPushforwardCompIsoToposHom B S hS f' g').hom.app
          ((smallEtaleDerivedModulePullback B S hS k).obj K) =
      smallEtaleDerivedModuleBaseChangeMap B S hS (f ≫ g) m (f' ≫ g') k
        (comp_stack B S hS f g f' g' k l m wtop wbot) K :=
  Stacks.CategoryTheory.BaseChange.map_vertical
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS g)
    (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))
    (smallEtaleDerivedModuleAdjunction B S hS f') (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModuleAdjunction B S hS (f' ≫ g'))
    (smallEtaleDerivedModulePullbackCompIso B S hS f g)
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' l)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f l f' k wtop)
    (smallEtaleDerivedModulePullbackCompIso B S hS g' m)
    (smallEtaleDerivedModulePullbackSquareIso B S hS g m g' l wbot)
    (smallEtaleDerivedModulePullbackCompIso B S hS (f' ≫ g') m)
    (smallEtaleDerivedModulePullbackSquareIso B S hS (f ≫ g) m (f' ≫ g') k
      (comp_stack B S hS f g f' g' k l m wtop wbot))
    _ _ _
    (fun N => congrArg (_ ≫ ·) (smallEtaleDerivedPullbackSquareIso_inv_app B S hS f l f' k wtop N))
    (fun M => congrArg (_ ≫ ·) (smallEtaleDerivedPullbackSquareIso_inv_app B S hS g m g' l wbot M))
    (fun M => congrArg (_ ≫ ·) (smallEtaleDerivedPullbackSquareIso_inv_app B S hS (f ≫ g) m
      (f' ≫ g') k (comp_stack B S hS f g f' g' k l m wtop wbot) M))
    (fun M => smallEtaleDerivedSquareComparison_vertical B S hS f g f' g' k l m wtop wbot M) K

end Vertical

end AlgebraicGeometry.Space

end
