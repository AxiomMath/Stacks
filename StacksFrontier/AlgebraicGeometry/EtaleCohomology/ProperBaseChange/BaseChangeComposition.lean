module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# Composing the underived étale base change maps of a tower of squares

Consider a tower of two commutative squares of schemes
```
W <--j-- Z
|i       |k
X <--h-- Y
|f       |e
S <--g-- T
```
that is, morphisms `f : X ⟶ S`, `g : T ⟶ S`, `h : Y ⟶ X`, `e : Y ⟶ T`, `i : W ⟶ X`,
`j : Z ⟶ W`, `k : Z ⟶ Y` with `e ≫ g = h ≫ f` and `k ≫ h = j ≫ i`.  Write `a = i ≫ f` and
`b = k ≫ e` for the two composites along the sides of the outer rectangle.

This file proves that the base change comparison
`Stacks.EtaleCohomology.etaleAbelianBaseChange` of the outer rectangle is the composite of the
comparisons of the two squares, read through the comparison isomorphisms identifying the inverse
image along a composite with the composite of the inverse images.  Nothing is assumed of the
squares beyond commutativity: neither need be cartesian.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso'` and
  `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'` — the composition isomorphisms
  `f_* ⋙ g_* ≅ (fg)_*` and `(fg)^{-1} ≅ g^{-1} ⋙ f^{-1}` for abelian sheaves on the small étale
  sites, with the composite `fg` carried as a named morphism together with an equation naming
  it.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'_assoc` — the associativity pentagon
  of the inverse image comparison.
* `Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv` — the base change comparison of a
  commutative square is the mate of the comparison of the two composite inverse images, in the
  named-composite form.
* `Stacks.EtaleCohomology.etaleAbelianBaseChange_comp_app` — the composition statement, at a
  sheaf.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Rearrange

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- Rearranging a commuting pentagon of isomorphisms, first form. -/
public lemma isoRearrange {A A' B W Z : 𝒞} (m : A ⟶ B) (p : A' ≅ A) (q : W ≅ B) (r : Z ≅ A')
    (s : W ≅ Z) (hcomm : m ≫ q.inv = p.inv ≫ r.inv ≫ s.inv) :
    r.hom ≫ p.hom ≫ m = s.inv ≫ q.hom := by
  rw [Iso.comp_inv_eq] at hcomm
  rw [hcomm]
  simp

/-- Rearranging a commuting pentagon of isomorphisms, second form. -/
public lemma isoRearrange₂ {A B C D E : 𝒞} (m : A ⟶ B) (n : B ⟶ C) (c : A ⟶ D) (d : D ≅ E)
    (e : E ≅ C) (hcomm : m ≫ n = (c ≫ d.hom) ≫ e.hom) :
    m ≫ n ≫ e.inv ≫ d.inv = c := by
  rw [← Category.assoc, hcomm]
  simp

/-- Rearranging a commuting pentagon of isomorphisms, third form. -/
public lemma isoRearrange₃ {A B C D E : 𝒞} (m : A ⟶ B) (d : B ≅ C) (c : A ⟶ D) (r : D ⟶ E)
    (s : E ≅ C) (hcomm : m ≫ d.hom = (c ≫ r) ≫ s.hom) :
    c ≫ r ≫ s.hom ≫ d.inv = m := by
  simp only [← Category.assoc]
  rw [← hcomm]
  simp

end Rearrange

section Mate

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- Taking mates commutes with whiskering the two vertical functors of a 2-square. -/
public lemma mateEquiv_whisker (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G G' : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (φ : G' ⟶ G) (ψ : H ⟶ H') :
    mateEquiv adj₁ adj₂ ((α.whiskerTop φ).whiskerBottom ψ) =
      ((mateEquiv adj₁ adj₂ α).whiskerRight φ).whiskerLeft ψ := by
  refine TwoSquare.ext _ _ fun d => ?_
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, mateEquiv]

end Mate

end Stacks.CategoryTheory

namespace Stacks.EtaleCohomology

/-! ### Cancelling a whiskered isomorphism -/

/-- Whiskering an isomorphism and its inverse on the left of a fixed functor cancel. -/
public lemma whiskerLeft_hom_inv_id_assoc {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] (F : C₁ ⥤ C₂) {G H : C₂ ⥤ C₃} (α : G ≅ H)
    {K : C₁ ⥤ C₃} (m : F ⋙ G ⟶ K) :
    Functor.whiskerLeft F α.hom ≫ Functor.whiskerLeft F α.inv ≫ m = m :=
  (Functor.isoWhiskerLeft F α).hom_inv_id_assoc m

/-- Whiskering an isomorphism and its inverse on the right of a fixed functor cancel. -/
public lemma whiskerRight_hom_inv_id_assoc {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] {G H : C₁ ⥤ C₂} (α : G ≅ H) (F : C₂ ⥤ C₃)
    {K : C₁ ⥤ C₃} (m : G ⋙ F ⟶ K) :
    Functor.whiskerRight α.hom F ≫ Functor.whiskerRight α.inv F ≫ m = m :=
  (Functor.isoWhiskerRight α F).hom_inv_id_assoc m

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

section CompIso

variable {X Y Z : Scheme.{u}}

/-- The composition isomorphism `f_* ⋙ g_* ≅ (fg)_*` for direct image of abelian sheaves on the
small étale sites, with the composite `fg` carried as a named morphism. -/
public def etaleAbelianDirectImageCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianDirectImage.{u, v} g ≅
      etaleAbelianDirectImage.{u, v} fg :=
  smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{max (u + 1) v}

/-- The composition isomorphism `(fg)^{-1} ≅ g^{-1} ⋙ f^{-1}` for inverse image of abelian
sheaves on the small étale sites, with the composite `fg` carried as a named morphism.  It is the
isomorphism of left adjoints attached to
`Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso'`. -/
public def etaleAbelianInverseImageCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleAbelianInverseImage.{u, v} fg ≅
      etaleAbelianInverseImage.{u, v} g ⋙ etaleAbelianInverseImage.{u, v} f :=
  (Adjunction.leftAdjointCompIso (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} fg)
    (etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg)).symm

/-- With the composite written out, the named-composite direct image comparison is
`Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso`. -/
public lemma etaleAbelianDirectImageCompIso'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleAbelianDirectImageCompIso'.{u, v} f g (f ≫ g) rfl =
      etaleAbelianDirectImageCompIso.{u, v} f g := by
  have h : smallEtaleBaseChangeComp' f g (f ≫ g) rfl = smallEtaleBaseChangeComp f g :=
    Iso.ext (by simp [smallEtaleBaseChangeComp'])
  exact congrArg (fun e => Functor.sheafPushforwardContinuousComp' (Iso.symm e)
    AddCommGrpCat.{max (u + 1) v} _ _ _) h

/-- With the composite written out, the named-composite inverse image comparison is
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso`. -/
public lemma etaleAbelianInverseImageCompIso'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleAbelianInverseImageCompIso'.{u, v} f g (f ≫ g) rfl =
      etaleAbelianInverseImageCompIso.{u, v} f g := by
  have h : etaleAbelianInverseImageCompIso.{u, v} f g =
      (etaleAbelianInverseImageDirectImageAdj.{u, v} (f ≫ g)).leftAdjointUniq
        (((etaleAbelianInverseImageDirectImageAdj.{u, v} g).comp
            (etaleAbelianInverseImageDirectImageAdj.{u, v} f)).ofNatIsoRight
          (etaleAbelianDirectImageCompIso.{u, v} f g)) := rfl
  have hsymm : (etaleAbelianInverseImageDirectImageAdj.{u, v} (f ≫ g)).leftAdjointUniq
        (((etaleAbelianInverseImageDirectImageAdj.{u, v} g).comp
            (etaleAbelianInverseImageDirectImageAdj.{u, v} f)).ofNatIsoRight
          (etaleAbelianDirectImageCompIso.{u, v} f g)) =
      (Adjunction.leftAdjointUniq
        (((etaleAbelianInverseImageDirectImageAdj.{u, v} g).comp
            (etaleAbelianInverseImageDirectImageAdj.{u, v} f)).ofNatIsoRight
          (etaleAbelianDirectImageCompIso.{u, v} f g))
        (etaleAbelianInverseImageDirectImageAdj.{u, v} (f ≫ g))).symm :=
    Iso.ext (NatTrans.ext (funext fun x => (Adjunction.leftAdjointUniq_inv_app _ _ x).symm))
  rw [h, hsymm, Adjunction.leftAdjointUniq_ofNatIsoRight_comp,
    ← etaleAbelianDirectImageCompIso'_rfl]
  rfl

/-- The named-composite inverse image comparison is the comparison at the written-out composite,
transported along the equation naming it. -/
public lemma etaleAbelianInverseImageCompIso'_eq (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg =
      eqToIso (congrArg (fun m : X ⟶ Z => etaleAbelianInverseImage.{u, v} m) hfg) ≪≫
        etaleAbelianInverseImageCompIso.{u, v} f g := by
  subst hfg
  exact (etaleAbelianInverseImageCompIso'_rfl.{u, v} f g).trans (Iso.ext (by simp)).symm

/-- **The associativity pentagon of the inverse image comparison.**  For `f : X₁ ⟶ X₀`,
`i : X₂ ⟶ X₁` and `j : X₃ ⟶ X₂` the two ways of comparing the inverse image along a threefold
composite with the composite of the three inverse images agree. -/
public lemma etaleAbelianInverseImageCompIso'_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀)
    (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁) (hq : q = j ≫ i)
    (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a) :
    Functor.isoWhiskerLeft (etaleAbelianInverseImage.{u, v} f)
          (etaleAbelianInverseImageCompIso'.{u, v} j i q hq).symm ≪≫
        (etaleAbelianInverseImageCompIso'.{u, v} q f p hp₁).symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (etaleAbelianInverseImageCompIso'.{u, v} i f a ha).symm
            (etaleAbelianInverseImage.{u, v} j) ≪≫
          (etaleAbelianInverseImageCompIso'.{u, v} j a p hp₂).symm := by
  have hpush := smallEtalePushforwardComp'_assoc j i f q hq a ha p hp₁ hp₂
    AddCommGrpCat.{max (u + 1) v}
  refine Adjunction.leftAdjointCompIso_assoc
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} i)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} j)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} a)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} q)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} p) _ _ _ _ ?_
  have hpush' : Functor.isoWhiskerRight (etaleAbelianDirectImageCompIso'.{u, v} j i q hq)
          (etaleAbelianDirectImage.{u, v} f) ≪≫
        etaleAbelianDirectImageCompIso'.{u, v} q f p hp₁ =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (etaleAbelianDirectImage.{u, v} j)
            (etaleAbelianDirectImageCompIso'.{u, v} i f a ha) ≪≫
          etaleAbelianDirectImageCompIso'.{u, v} j a p hp₂ := hpush
  rw [hpush']
  exact Iso.ext (by simp)

end CompIso

section Pasting

variable {S T W X Y Z : Scheme.{u}}

/-- The base change comparison of a commutative square is the mate, under the two
inverse-image/direct-image adjunctions, of the comparison of the two composite inverse images,
with the common composite carried as a named morphism. -/
public lemma etaleAbelianBaseChange_eq_mateEquiv {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hyp : g' ≫ f = f' ≫ g)
    (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    etaleAbelianBaseChange.{u, v} f g g' f' hyp =
      mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
        (TwoSquare.mk _ _ _ _
          ((etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).inv ≫
            (etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom)) := by
  have key : (etaleAbelianInverseImageCompIso.{u, v} f' g).symm.hom ≫
        ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
          eqToIso (congrArg (fun k : X' ⟶ Y => etaleAbelianInverseImage.{u, v} k) hyp)).inv =
      (etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).inv ≫
        (etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom := by
    rw [etaleAbelianInverseImageCompIso'_eq, etaleAbelianInverseImageCompIso'_eq]
    simp
  exact congrArg (fun α => mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f') (TwoSquare.mk _ _ _ _ α)) key

/-- **The base change comparisons of a tower of two commutative squares compose**, as an
identity of 2-squares.  The comparison attached to the outer rectangle is the vertical
composite of the comparisons attached to the two squares, whiskered with the inverse image
comparisons identifying the inverse image along a composite.  Every composite of two morphisms
of schemes is carried as a named morphism together with the equations naming it. -/
private theorem baseChangeComp_aux (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i)
    (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T) (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (P₁ : Y ⟶ S) (hP₁e : P₁ = e ≫ g) (hP₁h : P₁ = h ≫ f)
    (P₂ : Z ⟶ X) (hP₂k : P₂ = k ≫ h) (hP₂j : P₂ = j ≫ i)
    (P : Z ⟶ S) (hPb : P = b ≫ g) (hPj : P = j ≫ a) (hPP₂ : P = P₂ ≫ f)
    (hPk : P = k ≫ P₁) :
    etaleAbelianBaseChange.{u, v} g a b j hyp =
      TwoSquare.whiskerLeft
        (TwoSquare.whiskerRight
          (TwoSquare.vComp (etaleAbelianBaseChange.{u, v} g f e h sq₁)
            (etaleAbelianBaseChange.{u, v} h i k j sq₂))
          (etaleAbelianInverseImageCompIso'.{u, v} i f a ha).hom)
        (etaleAbelianInverseImageCompIso'.{u, v} k e b hb).inv := by
  have hA1 := etaleAbelianInverseImageCompIso'_assoc.{u, v} f i j a ha P₂ hP₂j P hPP₂ hPj
  have hA2 := etaleAbelianInverseImageCompIso'_assoc.{u, v} f h k P₁ hP₁h P₂ hP₂k P hPP₂ hPk
  have hA3 := etaleAbelianInverseImageCompIso'_assoc.{u, v} g e k P₁ hP₁e b hb P hPb hPk
  have h1 := Stacks.CategoryTheory.isoRearrange
    (Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} f)
      (etaleAbelianInverseImageCompIso'.{u, v} j i P₂ hP₂j).inv)
    (Functor.associator _ _ _)
    (etaleAbelianInverseImageCompIso'.{u, v} P₂ f P hPP₂)
    (Functor.isoWhiskerRight (etaleAbelianInverseImageCompIso'.{u, v} i f a ha)
      (etaleAbelianInverseImage.{u, v} j))
    (etaleAbelianInverseImageCompIso'.{u, v} j a P hPj)
    (congrArg Iso.hom hA1)
  have h2 := Stacks.CategoryTheory.isoRearrange₂
    (etaleAbelianInverseImageCompIso'.{u, v} P₂ f P hPP₂).hom
    (Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} f)
      (etaleAbelianInverseImageCompIso'.{u, v} k h P₂ hP₂k).hom)
    (etaleAbelianInverseImageCompIso'.{u, v} k P₁ P hPk).hom
    (Functor.isoWhiskerRight (etaleAbelianInverseImageCompIso'.{u, v} h f P₁ hP₁h)
      (etaleAbelianInverseImage.{u, v} k))
    (Functor.associator _ _ _)
    (congrArg Iso.inv hA2)
  have h3 := Stacks.CategoryTheory.isoRearrange₃
    (etaleAbelianInverseImageCompIso'.{u, v} b g P hPb).hom
    (Functor.isoWhiskerLeft (etaleAbelianInverseImage.{u, v} g)
      (etaleAbelianInverseImageCompIso'.{u, v} k e b hb))
    (etaleAbelianInverseImageCompIso'.{u, v} k P₁ P hPk).hom
    (Functor.whiskerRight (etaleAbelianInverseImageCompIso'.{u, v} e g P₁ hP₁e).hom
      (etaleAbelianInverseImage.{u, v} k))
    (Functor.associator _ _ _)
    (congrArg Iso.inv hA3)
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv] at h1 h2 h3
  rw [etaleAbelianBaseChange_eq_mateEquiv.{u, v} g a b j hyp P hPb hPj,
    etaleAbelianBaseChange_eq_mateEquiv.{u, v} g f e h sq₁ P₁ hP₁e hP₁h,
    etaleAbelianBaseChange_eq_mateEquiv.{u, v} h i k j sq₂ P₂ hP₂k hP₂j,
    ← mateEquiv_vcomp, ← Stacks.CategoryTheory.mateEquiv_whisker]
  refine congrArg (fun α => mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} j) α) ?_
  simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, h3]

/-- **The underived étale base change comparisons of a tower of two commutative squares
compose.**  For squares `e ≫ g = h ≫ f` and `k ≫ h = j ≫ i` of schemes, with `a = i ≫ f` and
`b = k ≫ e` the composites along the two sides of the outer rectangle, the comparison
`g_* a^{-1} ⟶ j_* b^{-1}` attached to the outer rectangle is `i^{-1}` of the comparison of the
lower square followed by the comparison of the upper square, read through the inverse image
comparisons for the two composites. -/
public theorem etaleAbelianBaseChange_comp_app (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i)
    (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T) (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (K : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianBaseChange.{u, v} g a b j hyp).app K =
      (etaleAbelianInverseImageCompIso'.{u, v} i f a ha).hom.app
          ((etaleAbelianDirectImage.{u, v} g).obj K) ≫
        (etaleAbelianInverseImage.{u, v} i).map
          ((etaleAbelianBaseChange.{u, v} g f e h sq₁).app K) ≫
        (etaleAbelianBaseChange.{u, v} h i k j sq₂).app
          ((etaleAbelianInverseImage.{u, v} e).obj K) ≫
        (etaleAbelianDirectImage.{u, v} j).map
          ((etaleAbelianInverseImageCompIso'.{u, v} k e b hb).inv.app K) := by
  have hPk : b ≫ g = k ≫ e ≫ g := by rw [hb, Category.assoc]
  have hPP₂ : b ≫ g = (k ≫ h) ≫ f := by
    rw [hb, Category.assoc, sq₁, ← Category.assoc]
  rw [baseChangeComp_aux.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp (e ≫ g) rfl sq₁
    (k ≫ h) rfl sq₂ (b ≫ g) rfl hyp hPP₂ hPk]
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp]

end Pasting

end Stacks.EtaleCohomology

end
