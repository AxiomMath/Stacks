module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# A section of a base-changed 2-fibre product is a diagonal with a filling 2-morphism

Fix a base category `C`, categories `X`, `Y` and `T` fibred in groupoids over it, a 1-morphism
`f : X ⟶ Y`, a category `A` over `C` with structure functor `r`, and a functor `y : A ⥤ Y` over
`C`. The 2-fibre product over `C` of `r` and `f` along `y` (`CategoryTheory.TwoFibreProductOver`)
has first projection to `A` and second projection to `X`.

Let `s : T ⥤ A` be a functor over `C` and let `H` be a *section of the first projection along
`s`*, that is a functor `T ⥤ A ×_Y X` with `H ⋙ fst = s`. This file reads off from `H` the data
of a dotted arrow for the square `(s ⋙ y, f)`: the diagonal `T ⟶ X` is `H` followed by the
second projection, and the 2-morphism `s ⋙ y ⟶ (diagonal) ≫ f` filling the square is the
comparison 2-cell `ψ` of the 2-fibre product, whiskered with `H`. It also reads off the converse
on 2-morphisms: a 2-morphism of the diagonals compatible with the two filling 2-morphisms gives,
objectwise, a morphism of the two sections.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.targetOfSection`: the lower edge `T ⟶ Y`, namely `s ⋙ y`.
* `CategoryTheory.CatFiberedInGroupoids.diagonalOfSection`: the diagonal `T ⟶ X`.
* `CategoryTheory.CatFiberedInGroupoids.betaOfSection`: the 2-morphism filling the square.
* `CategoryTheory.CatFiberedInGroupoids.sectionHomApp`: the morphism of the 2-fibre product at an
  object, attached to a 2-morphism of the diagonals compatible with the two fillers.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.diagonalOfSection_congr` and
  `CategoryTheory.CatFiberedInGroupoids.betaOfSection_congr`: equal sections have equal diagonals
  and, after transport along that equality, equal fillers.
* `CategoryTheory.CatFiberedInGroupoids.betaOfSection_app`: the components of the filler.
* `CategoryTheory.CatFiberedInGroupoids.sectionHomApp_a`: the first component of
  `CategoryTheory.CatFiberedInGroupoids.sectionHomApp` is the canonical identification of the two
  images under the first projection.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂ vA uA

variable {C : Type u₁} [Category.{v₁} C] {A : Type uA} [Category.{vA} A]
  {X Y T : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C}

/-- The image under a functor of a composite of two `eqToHom`s, as a single `eqToHom`. -/
private theorem map_eqToHom_comp_eqToHom {D : Type*} [Category D] {E : Type*} [Category E]
    (F : D ⥤ E) {a b c : D} (p : a = b) (q : b = c) :
    F.map (eqToHom p ≫ eqToHom q) = eqToHom (congrArg F.obj (p.trans q)) := by
  subst p q
  simp

/-- **The lower edge of the square a section fills**: the 1-morphism `T ⟶ Y` obtained by
following `s` into `A` and then `y`. -/
def targetOfSection (r : A ⥤ C) (y : A ⥤ Y.val.obj) (hy : y ⋙ Y.val.p = r)
    (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p) : T ⟶ Y :=
  Bicategory.InducedBicategory.mkHom ⟨s ⋙ y, by rw [Functor.assoc, hy, hs]⟩

/-- **The diagonal read off a section of the first projection**: the 1-morphism `T ⟶ X` obtained
by following the section into the 2-fibre product and then the second projection. -/
def diagonalOfSection (r : A ⥤ C) (y : A ⥤ Y.val.obj) (f : X ⟶ Y)
    (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p)
    (H : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s) : T ⟶ X :=
  Bicategory.InducedBicategory.mkHom {
    toFunctor := H ⋙ TwoFibreProductOver.snd r X.val.p Y.val.p y f.hom.toFunctor
    w := by
      rw [Functor.assoc, TwoFibreProductOver.snd_comp_eq,
        ← TwoFibreProductOver.fst_comp_eq, ← Functor.assoc, hH, hs] }

/-- The natural isomorphism underlying `CategoryTheory.CatFiberedInGroupoids.betaOfSection`: the
comparison 2-cell of the 2-fibre product, whiskered with the section and read through the
identification of the section's first component with `s`. -/
def betaNatIsoOfSection (r : A ⥤ C) (y : A ⥤ Y.val.obj) (f : X ⟶ Y)
    (s : T.val.obj ⥤ A)
    (H : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s) :
    (s ⋙ y) ≅ (H ⋙ TwoFibreProductOver.snd r X.val.p Y.val.p y f.hom.toFunctor) ⋙
      f.hom.toFunctor :=
  Functor.isoWhiskerRight (eqToIso hH.symm) y ≪≫
    Functor.isoWhiskerLeft H (TwoFibreProductOver.psiIso r X.val.p Y.val.p y f.hom.toFunctor)

/-- **The 2-morphism filling the square a section fills.** Its components are the comparison
isomorphisms of the objects of the 2-fibre product, which are vertical over `C`. -/
noncomputable def betaOfSection (r : A ⥤ C) (y : A ⥤ Y.val.obj) (hy : y ⋙ Y.val.p = r)
    (f : X ⟶ Y) (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p)
    (H : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s) :
    targetOfSection r y hy s hs ⟶ (diagonalOfSection r y f s hs H hH ≫ f) :=
  ⟨{ toNatTrans := (betaNatIsoOfSection r y f s H hH).hom
     isHomLift' := by
       intro z
       apply IsHomLift.of_fac' Y.val.p (𝟙 (T.val.p.obj z))
         ((betaNatIsoOfSection r y f s H hH).hom.app z)
         (Functor.congr_obj (show (s ⋙ y) ⋙ Y.val.p = T.val.p by
           rw [Functor.assoc, hy, hs]) z)
         (Functor.congr_obj (diagonalOfSection r y f s hs H hH ≫ f).hom.w z)
       dsimp [betaNatIsoOfSection, Functor.isoWhiskerRight, Functor.isoWhiskerLeft]
       simp only [eqToHom_app, eqToHom_map, TwoFibreProductOver.psiIso_hom_app]
       have := (H.obj z).vertical
       refine Eq.trans (Y.val.p.map_comp _ _) ?_
       refine Eq.trans (congrArg (fun t => _ ≫ t)
         (IsHomLift.fac' Y.val.p (𝟙 (H.obj z).base) (H.obj z).iso.hom)) ?_
       refine Eq.trans (congrArg (fun t => t ≫ _) (eqToHom_map Y.val.p _)) ?_
       simp only [Category.id_comp, eqToHom_trans]
       apply eqToHom_trans }⟩

/-- **The component of `CategoryTheory.CatFiberedInGroupoids.betaOfSection` at an object**: the
comparison isomorphism carried by the section at that object, preceded by the identification of
the section's first component with `s`. -/
theorem betaOfSection_app (r : A ⥤ C) (y : A ⥤ Y.val.obj) (hy : y ⋙ Y.val.p = r)
    (f : X ⟶ Y) (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p)
    (H : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s) (z : T.val.obj) :
    (betaOfSection r y hy f s hs H hH).hom.toNatTrans.app z =
      y.map (eqToHom (Functor.congr_obj hH z).symm) ≫ (H.obj z).iso.hom := by
  dsimp [betaOfSection, betaNatIsoOfSection, Functor.isoWhiskerRight, Functor.isoWhiskerLeft]
  simp only [eqToHom_app, TwoFibreProductOver.psiIso_hom_app]
  rfl

/-- Equal sections have equal diagonals. -/
theorem diagonalOfSection_congr (r : A ⥤ C) (y : A ⥤ Y.val.obj) (f : X ⟶ Y)
    (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p)
    (H K : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (hK : K ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (h : H = K) :
    diagonalOfSection r y f s hs H hH = diagonalOfSection r y f s hs K hK := by
  subst K
  rfl

/-- Equal sections have equal fillers, after transport along
`CategoryTheory.CatFiberedInGroupoids.diagonalOfSection_congr`. -/
theorem betaOfSection_congr (r : A ⥤ C) (y : A ⥤ Y.val.obj) (hy : y ⋙ Y.val.p = r)
    (f : X ⟶ Y) (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p)
    (H K : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (hK : K ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (h : H = K) :
    betaOfSection r y hy f s hs H hH =
      betaOfSection r y hy f s hs K hK ≫
        (eqToHom (diagonalOfSection_congr r y f s hs H K hH hK h).symm ▷ f) := by
  subst K
  simp only [eqToHom_refl, id_whiskerRight, Category.comp_id]

/-- **A 2-morphism of the diagonals compatible with the two fillers gives a morphism of the two
sections, objectwise.** The first component is the canonical identification of the two images
under the first projection, the second is the component of the 2-morphism, and the comparison
square is the compatibility with the fillers. -/
noncomputable def sectionHomApp (r : A ⥤ C) (y : A ⥤ Y.val.obj) (hy : y ⋙ Y.val.p = r)
    (f : X ⟶ Y) (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p)
    (H K : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (hK : K ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (η : diagonalOfSection r y f s hs H hH ⟶ diagonalOfSection r y f s hs K hK)
    (hβ : betaOfSection r y hy f s hs K hK =
      betaOfSection r y hy f s hs H hH ≫ (η ▷ f)) (z : T.val.obj) :
    H.obj z ⟶ K.obj z where
  hbase := eqToHom ((H.obj z).hx.symm.trans
    ((congrArg r.obj (Functor.congr_obj hH z)).trans (Functor.congr_obj hs z))) ≫
    eqToHom ((Functor.congr_obj hs z).symm.trans
      ((congrArg r.obj (Functor.congr_obj hK z)).symm.trans (K.obj z).hx))
  a := eqToHom (Functor.congr_obj hH z) ≫ eqToHom (Functor.congr_obj hK z).symm
  b := η.hom.toNatTrans.app z
  ha := by
    apply IsHomLift.of_fac' r _ _ (H.obj z).hx (K.obj z).hx
    refine Eq.trans (map_eqToHom_comp_eqToHom r _ _) ?_
    simp only [eqToHom_trans]
  hb := by
    apply IsHomLift.of_fac' X.val.p _ _ (H.obj z).hy (K.obj z).hy
    refine Eq.trans
      (IsHomLift.fac' X.val.p (𝟙 (T.val.p.obj z)) (η.hom.toNatTrans.app z)) ?_
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  w := by
    have hh := congrArg (fun t => t.hom.toNatTrans.app z) hβ
    change (betaOfSection r y hy f s hs K hK).hom.toNatTrans.app z =
      (betaOfSection r y hy f s hs H hH).hom.toNatTrans.app z ≫
        f.hom.toFunctor.map (η.hom.toNatTrans.app z) at hh
    dsimp [betaOfSection, betaNatIsoOfSection, Functor.isoWhiskerRight,
      Functor.isoWhiskerLeft] at hh
    simp only [TwoFibreProductOver.psiIso_hom_app, eqToHom_app] at hh
    have he : eqToHom (Functor.congr_obj hH z).symm ≫
        (eqToHom (Functor.congr_obj hH z) ≫ eqToHom (Functor.congr_obj hK z).symm) =
        eqToHom (Functor.congr_obj hK z).symm := by
      rw [eqToHom_trans_assoc, eqToHom_trans]
    refine (cancel_epi (y.map (eqToHom (Functor.congr_obj hH z).symm))).mp ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ (K.obj z).iso.hom)
      ((y.map_comp _ _).symm.trans (congrArg y.map he))) ?_
    exact hh.trans (Category.assoc _ _ _)

/-- The first component of `CategoryTheory.CatFiberedInGroupoids.sectionHomApp` is the canonical
identification of the two images under the first projection. -/
theorem sectionHomApp_a (r : A ⥤ C) (y : A ⥤ Y.val.obj) (hy : y ⋙ Y.val.p = r)
    (f : X ⟶ Y) (s : T.val.obj ⥤ A) (hs : s ⋙ r = T.val.p)
    (H K : T.val.obj ⥤ TwoFibreProductOver r X.val.p Y.val.p y f.hom.toFunctor)
    (hH : H ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (hK : K ⋙ TwoFibreProductOver.fst r X.val.p Y.val.p y f.hom.toFunctor = s)
    (η : diagonalOfSection r y f s hs H hH ⟶ diagonalOfSection r y f s hs K hK)
    (hβ : betaOfSection r y hy f s hs K hK =
      betaOfSection r y hy f s hs H hH ≫ (η ▷ f)) (z : T.val.obj) :
    (sectionHomApp r y hy f s hs H K hH hK η hβ z).a =
      eqToHom (Functor.congr_obj hH z) ≫ eqToHom (Functor.congr_obj hK z).symm := rfl

end CategoryTheory.CatFiberedInGroupoids

end
