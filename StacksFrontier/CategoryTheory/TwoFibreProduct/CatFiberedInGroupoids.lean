module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# 2-fibre products in the 2-category of categories fibred in groupoids

Fix a base category `C`. The 2-category of categories fibred in groupoids over `C` is
`CategoryTheory.CatFiberedInGroupoids` (Stacks 02XS), and a 2-fibre product of a cospan in a
`(2,1)`-category is a terminal object of the category of 2-commutative squares over that
cospan (`CategoryTheory.Bicategory.IsTwoFibreProduct`, Stacks 003Q). This file exhibits such a
terminal square for a cospan of categories fibred in groupoids: its apex is the 2-fibre product
over `C` of Stacks 0040 (`CategoryTheory.TwoFibreProductOver`), which is fibred in groupoids by
Stacks 0041, and its universal property is the one proved in
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase`. Since a 2-fibre product is a terminal
object, it follows that any 2-commutative square with the same universal property has an apex
equivalent to it.

The universes are the ones the construction forces. An object of the 2-category of categories
fibred in groupoids over `C : Type u₁` with `Category.{v₁} C` is a category with objects in
`Type u₂` and morphisms in `Type v₂`; an object of the 2-fibre product of such a cospan is a
quadruple `(U, x, y, φ)` with `U : C`, with `x` and `y` objects of the two factors and with `φ`
a morphism of the target, so it lies in `Type (max u₁ u₂ v₂)`, and a morphism of the 2-fibre
product lies in `Type (max v₁ v₂)`. The apex is therefore an object of the same 2-category only
when that 2-category's universes are already closed under those two operations, which is the
instantiation used below.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.underlyingIso`: the natural isomorphism of the
  underlying functors of a 2-isomorphism.
* `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`: the canonical 2-commutative
  square over a cospan, with apex the 2-fibre product over `C`.
* `CategoryTheory.CatFiberedInGroupoids.liftTwoFibreProductSquare` and
  `CategoryTheory.CatFiberedInGroupoids.preHomTwoFibreProductSquare`: the mediating 1-morphism
  from an arbitrary 2-commutative square to the canonical one, and that 1-morphism packaged as a
  pre-morphism of 2-commutative squares whose two comparison 2-cells are identities.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare`: the canonical
  square is a 2-fibre product.
* `CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`: a comparison 1-morphism
  between two 2-fibre products of one cospan of categories fibred in groupoids is an
  equivalence of the underlying categories.
* `CategoryTheory.CatFiberedInGroupoids.hom₂_ext_of_whiskerRight_isTwoFibreProduct`: the two
  projections of any 2-fibre product of the cospan jointly detect 2-morphisms into its apex.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

/-- The compatibility square of a cone morphism whose comparison isomorphisms are identities:
both sides reduce to the 2-cell filling the square. -/
theorem map_id_comp_id_eq {D : Type*} [Category D] {E₁ : Type*} [Category E₁]
    {E₂ : Type*} [Category E₂] (F : E₁ ⥤ D) (G : E₂ ⥤ D) {A : E₁} {B : E₂}
    (u : F.obj A ⟶ G.obj B) :
    u ≫ G.map (𝟙 B) ≫ 𝟙 (G.obj B) = F.map (𝟙 A) ≫ 𝟙 (F.obj A) ≫ u := by
  simp

/-- The compatibility square of a cone morphism whose comparison isomorphisms are identities,
with the two fillers identified by a given equality rather than being syntactically equal. -/
theorem map_id_comp_id_eq_of_eq {D : Type*} [Category D] {E₁ : Type*} [Category E₁]
    {E₂ : Type*} [Category E₂] (F : E₁ ⥤ D) (G : E₂ ⥤ D) {A : E₁} {B : E₂}
    {u v : F.obj A ⟶ G.obj B} (h : u = v) :
    u ≫ G.map (𝟙 B) ≫ 𝟙 (G.obj B) = F.map (𝟙 A) ≫ 𝟙 (F.obj A) ≫ v :=
  h ▸ map_id_comp_id_eq F G u

/-- Conjugating a commuting square by two isomorphisms: from `u ≫ bf.hom = af.hom ≫ i` one
gets `af.inv ≫ u = i ≫ bf.inv`. -/
theorem inv_comp_eq_comp_inv {D : Type*} [Category D] {A₁ A₂ B₁ B₂ : D} (af : A₁ ≅ A₂)
    (bf : B₁ ≅ B₂) (u : A₁ ⟶ B₁) (i : A₂ ⟶ B₂) (h : u ≫ bf.hom = af.hom ≫ i) :
    af.inv ≫ u = i ≫ bf.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Cancel the identities a strict bicategory's unitors leave behind in a compatibility
square. -/
theorem comp_eq_of_comp_id_eq {D : Type*} [Category D] {A B E F : D} {u : A ⟶ B}
    {v : B ⟶ F} {w : A ⟶ E} {t : E ⟶ F} (h : u ≫ v ≫ 𝟙 F = w ≫ 𝟙 E ≫ t) : u ≫ v = w ≫ t := by
  simpa using h

/-- The natural isomorphism of underlying functors of a 2-isomorphism. -/
def underlyingIso {X Y : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C} {f g : X ⟶ Y} (e : f ≅ g) :
    f.hom.toFunctor ≅ g.hom.toFunctor where
  hom := e.hom.hom.toNatTrans
  inv := e.inv.hom.toNatTrans
  hom_inv_id := congrArg (fun a => a.hom.toNatTrans) e.hom_inv_id
  inv_hom_id := congrArg (fun a => a.hom.toNatTrans) e.inv_hom_id

/-- Two 2-morphisms of categories fibred in groupoids are equal once their components are. -/
private theorem hom₂_ext_of_app {A B : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C} {f g : A ⟶ B}
    {η θ : f ⟶ g} (h : ∀ x, η.hom.toNatTrans.app x = θ.hom.toNatTrans.app x) : η = θ :=
  Bicategory.InducedBicategory.hom₂_ext <| BasedNatTrans.ext _ _ <| NatTrans.ext <| funext h

/-- Equal 2-morphisms of categories fibred in groupoids have equal components. -/
private theorem app_eq_of_eq {A B : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C} {f g : A ⟶ B}
    {η θ : f ⟶ g} (h : η = θ) (x : A.val.obj) :
    η.hom.toNatTrans.app x = θ.hom.toNatTrans.app x :=
  congrArg (fun b => b.hom.toNatTrans.app x) h

variable {X Y Z : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

/-- The canonical 2-commutative square over a cospan of categories fibred in groupoids,
with apex the 2-fibre product over the base. -/
def twoFibreProductSquare (f : X ⟶ Z) (g : Y ⟶ Z) : Bicategory.TwoCommSq f g where
  pt := ⟨BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor X.val.p Y.val.p Z.val.p
    f.hom.toFunctor g.hom.toFunctor),
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ X.2 Y.2 Z.2 f.hom.w g.hom.w⟩
  fst := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.fst _ _ _ _ _, w := TwoFibreProductOver.fst_comp_eq }
  snd := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.snd _ _ _ _ _, w := TwoFibreProductOver.snd_comp_eq }
  iso := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.psiIso _ _ _ _ _) (fun x => TwoFibreProductOver.psiIso_hom_vertical x))

/-- **The mediating 1-morphism from a 2-commutative square to the canonical 2-fibre product.**
It is `CategoryTheory.TwoFibreProductOver.lift` of the two legs of the square and of the 2-cell
filling it, read as a 1-morphism of categories fibred in groupoids. -/
@[implicit_reducible]
def liftTwoFibreProductSquare (f : X ⟶ Z) (g : Y ⟶ Z) (T : Bicategory.TwoCommSq f g) :
    T.pt ⟶ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).pt :=
  Bicategory.InducedBicategory.mkHom {
    toFunctor := TwoFibreProductOver.lift X.val.p Y.val.p Z.val.p
      f.hom.toFunctor g.hom.toFunctor T.pt.val.p
      T.fst.hom.toFunctor T.snd.hom.toFunctor T.fst.hom.w T.snd.hom.w
      (underlyingIso T.iso) (fun x => T.iso.hom.hom.isHomLift' x)
    w := TwoFibreProductOver.lift_comp_structureFunctor .. }

/-- **The mediating 1-morphism, as a pre-morphism of 2-commutative squares.** Both comparison
2-cells are identities: `CategoryTheory.TwoFibreProductOver.lift` is strictly compatible with
the two projections. -/
@[implicit_reducible]
def preHomTwoFibreProductSquare (f : X ⟶ Z) (g : Y ⟶ Z) (T : Bicategory.TwoCommSq f g) :
    Bicategory.TwoCommSq.PreHom T (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g) where
  hom := liftTwoFibreProductSquare.{v₁, v₂, u₁, u₂} f g T
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := Bicategory.InducedBicategory.hom₂_ext <| BasedNatTrans.ext _ _ <| NatTrans.ext <|
    funext fun x =>
      map_id_comp_id_eq f.hom.toFunctor g.hom.toFunctor (T.iso.hom.hom.toNatTrans.app x)

/-- The canonical square is a 2-fibre product in the 2-category of categories fibred in
groupoids. -/
noncomputable def isTwoFibreProduct_twoFibreProductSquare (f : X ⟶ Z) (g : Y ⟶ Z) :
    Bicategory.IsTwoFibreProduct (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g) := by
  refine CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun T => _root_.Quotient.mk _ (preHomTwoFibreProductSquare.{v₁, v₂, u₁, u₂} f g T)) ?_
  intro T a
  induction a using _root_.Quotient.inductionOn with
  | h a =>
    apply _root_.Quotient.sound
    let e := TwoFibreProductOver.liftIso (t := underlyingIso T.iso) a.hom.hom.toFunctor
      (underlyingIso a.isoFst.symm) (underlyingIso a.isoSnd.symm)
      (fun x => a.isoFst.inv.hom.isHomLift' x)
      (fun x => a.isoSnd.inv.hom.isHomLift' x)
      (by
        ext x
        have h := congrArg (fun b => b.hom.toNatTrans.app x) a.compat
        change T.iso.hom.hom.toNatTrans.app x ≫
          g.hom.toFunctor.map (a.isoSnd.hom.hom.toNatTrans.app x) ≫ 𝟙 _ =
          f.hom.toFunctor.map (a.isoFst.hom.hom.toNatTrans.app x) ≫ 𝟙 _ ≫
          (a.hom.hom.toFunctor.obj x).iso.hom at h
        exact inv_comp_eq_comp_inv (f.hom.toFunctor.mapIso ((underlyingIso a.isoFst).app x))
          (g.hom.toFunctor.mapIso ((underlyingIso a.isoSnd).app x)) _ _
          (comp_eq_of_comp_id_eq h))
      T.fst.hom.w T.snd.hom.w
      (fun x => T.iso.hom.hom.isHomLift' x)
    have he : ∀ x, (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).pt.val.p.IsHomLift
        (𝟙 (T.pt.val.p.obj x)) (e.hom.app x) := fun x =>
      TwoFibreProductOver.structureFunctor_isHomLift (e.hom.app x) (𝟙 (T.pt.val.p.obj x))
        (a.isoFst.inv.hom.isHomLift' x)
    refine ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e he), ?_, ?_⟩
    · exact Bicategory.InducedBicategory.hom₂_ext <| BasedNatTrans.ext _ _ <| NatTrans.ext <|
        funext fun x => congrArg (fun b => b.hom.toNatTrans.app x) a.isoFst.hom_inv_id
    · exact Bicategory.InducedBicategory.hom₂_ext <| BasedNatTrans.ext _ _ <| NatTrans.ext <|
        funext fun x => congrArg (fun b => b.hom.toNatTrans.app x) a.isoSnd.hom_inv_id

end CategoryTheory.CatFiberedInGroupoids

namespace CategoryTheory.Bicategory

universe v₁' v₂' u₁' u₂'

variable {C : Type u₁'} [Category.{v₁'} C]
  {X Y Z : CatFiberedInGroupoids.{v₁', v₂', u₁', u₂'} C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The comparison 1-morphism between two 2-fibre products of the same cospan of categories
fibred in groupoids is an equivalence of the underlying categories. -/
theorem isEquivalence_of_isTwoFibreProduct {P Q : TwoCommSq f g}
    (hP : IsTwoFibreProduct P) (hQ : IsTwoFibreProduct Q) (a : TwoCommSq.PreHom P Q) :
    a.hom.hom.toFunctor.IsEquivalence := by
  let b := _root_.Quotient.out (hP.from Q)
  obtain ⟨e₁, -, -⟩ : TwoCommSq.PreHom.Rel (a.comp b) (TwoCommSq.PreHom.id P) :=
    _root_.Quotient.exact (hP.hom_ext (_root_.Quotient.mk _ (a.comp b)) (𝟙 P))
  obtain ⟨e₂, -, -⟩ : TwoCommSq.PreHom.Rel (b.comp a) (TwoCommSq.PreHom.id Q) :=
    _root_.Quotient.exact (hQ.hom_ext (_root_.Quotient.mk _ (b.comp a)) (𝟙 Q))
  exact (CategoryTheory.Equivalence.mk a.hom.hom.toFunctor b.hom.hom.toFunctor
    (CatFiberedInGroupoids.underlyingIso e₁).symm
    (CatFiberedInGroupoids.underlyingIso e₂)).isEquivalence_functor

end CategoryTheory.Bicategory

namespace CategoryTheory.CatFiberedInGroupoids

open CategoryTheory.Bicategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

/-- **Whiskering with a composite is whiskering twice**, on the nose, in the 2-category of
categories fibred in groupoids. -/
theorem whiskerRight_comp_eq
    {A₁ A₂ A₃ A₄ : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C}
    {u v : A₁ ⟶ A₂} (η : u ⟶ v) (h : A₂ ⟶ A₃) (i : A₃ ⟶ A₄) :
    η ▷ (h ≫ i) = (η ▷ h) ▷ i :=
  hom₂_ext_of_app fun _ => rfl

variable {X Y Z : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}
  {f : X ⟶ Z} {g : Y ⟶ Z}
  {A : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

/-- **The projections of the canonical 2-fibre product jointly detect 2-morphisms.** Two
2-morphisms into the apex of `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` which
agree after whiskering with each projection are equal. -/
theorem hom₂_ext_of_whiskerRight_twoFibreProductSquare
    {a b : A ⟶ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).pt} {η θ : a ⟶ b}
    (hfst : η ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).fst =
      θ ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).fst)
    (hsnd : η ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).snd =
      θ ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).snd) : η = θ := by
  refine hom₂_ext_of_app fun z => TwoFibreProductOver.Hom.ext' ?_ ?_
  · exact app_eq_of_eq hfst z
  · exact app_eq_of_eq hsnd z

/-- **The projections of any 2-fibre product jointly detect 2-morphisms.** Two 2-morphisms into
the apex of a 2-fibre product of a cospan of categories fibred in groupoids which agree after
whiskering with each projection are equal. -/
theorem hom₂_ext_of_whiskerRight_isTwoFibreProduct
    {P : Bicategory.TwoCommSq f g} (hP : Bicategory.IsTwoFibreProduct P)
    {a b : A ⟶ P.pt} {η θ : a ⟶ b}
    (hfst : η ▷ P.fst = θ ▷ P.fst) (hsnd : η ▷ P.snd = θ ▷ P.snd) : η = θ := by
  have hQ : Bicategory.IsTwoFibreProduct (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g) :=
    isTwoFibreProduct_twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g
  let F := _root_.Quotient.out (hQ.from P)
  have : F.hom.hom.toFunctor.IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hP hQ F
  have hcancel : ∀ {W : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁,
        max (max u₁ u₂) (max v₁ v₂)} C} {u v : P.pt ⟶ W}
      (_ : u ≅ v), η ▷ u = θ ▷ u → η ▷ v = θ ▷ v := by
    intro W u v φ h
    refine (cancel_epi (Bicategory.whiskerLeftIso a φ).hom).1 ?_
    exact (Bicategory.whisker_exchange η φ.hom).trans
      ((congrArg (fun t => t ≫ (b ◁ φ.hom)) h).trans
        (Bicategory.whisker_exchange θ φ.hom).symm)
  have hF : η ▷ F.hom = θ ▷ F.hom := by
    refine hom₂_ext_of_whiskerRight_twoFibreProductSquare ?_ ?_
    · exact (whiskerRight_comp_eq η F.hom _).symm.trans
        ((hcancel F.isoFst hfst).trans (whiskerRight_comp_eq θ F.hom _))
    · exact (whiskerRight_comp_eq η F.hom _).symm.trans
        ((hcancel F.isoSnd hsnd).trans (whiskerRight_comp_eq θ F.hom _))
  exact hom₂_ext_of_app fun z => F.hom.hom.toFunctor.map_injective (app_eq_of_eq hF z)

end CategoryTheory.CatFiberedInGroupoids

end
