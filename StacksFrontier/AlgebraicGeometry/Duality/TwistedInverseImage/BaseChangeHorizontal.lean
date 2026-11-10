module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeStackingMate

/-!
# Base change for the twisted inverse image along a horizontal row of two squares

Let

```
X'' --k'--> X' --k--> X
|f''        |f'       |f
Y'' --l'--> Y' --l--> Y
```

be two cartesian squares of schemes placed side by side. [Stacks, Tag 0ATR] (Lemma 48.5.2) says
that, for quasi-compact quasi-separated schemes with `f`, `l` and `f'`, `l'` Tor-independent, the
base change maps of [Stacks, Tag 0AA6] for the two squares compose to the base change map for the
outer rectangle. That is what is proved here, as
`Stacks.Duality.twistedInverseImageBaseChangeMap_hcomp`.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedPullbackCompIsoConj` — the composition formula
  `Lb^* ⋙ La^* ≅ L(a ≫ b)^*` on the quasi-coherent derived categories, as the conjugate of the
  composition formula for derived direct image.

## Main results

All in the namespace `Stacks.Duality`.

* `quasiCoherentDerivedPushforwardSquareIso_transpose` — the comparison of derived direct image
  around a square, read for the transposed square, is the inverse comparison.
* `twistedInverseImagePushforwardBaseChange_hcomp` — the identity `ξ_rect = ξ_A ≫ᵥ ξ_B` for the
  transformation `ξ` of [Stacks, Tag 0A9K], read through the composition formula for derived
  direct image along the two horizontal composites.
* `isIso_twistedInverseImagePushforwardBaseChange_hcomp` — `ξ` for the rectangle is invertible as
  soon as it is for the two squares.
* `twistedInverseImageBaseChangeMap_hcomp` — **[Stacks, Tag 0ATR]**.

## Route

The comparison of derived direct image around the rectangle is that of its transpose read
backwards, and the transpose is a vertical stack, so
`Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso_vcomp` gives it as a horizontal paste of
the comparisons of the two squares. `ξ` is the mate of that comparison under the twisted inverse
image adjunctions of the three *vertical* morphisms, none of which is composite, so the first
identity is `CategoryTheory.mateEquiv_vcomp`, with no trade of adjunctions. The base change map
is the mate of `ξ⁻¹` under the derived adjunctions of the *horizontal* morphisms, two of which are
composite, and here the composite adjunction is traded for the adjunction of the composite by the
composition formula for derived pullback, which is defined as the conjugate of the one for derived
direct image so that the trade is by construction.

## References

* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty
open Stacks.Cohomology.DerivedBaseChangePasting (mate_twoSquare_paste)
open Stacks.CategoryTheory (mateEquiv_whisker)
open scoped CategoryTheory.TwoSquare

universe u

namespace Stacks.Duality

/-! ### Bookkeeping, with variable data -/

section Generic

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D] [Category.{v₅} E]
  [Category.{v₆} F]

/-- A 2-square is the whiskered horizontal composite of two 2-squares as soon as the inverse of
the underlying isomorphism is the vertical paste of the inverses. Stated with variable data, so
that the application site pays no unfolding of a derived functor. -/
theorem twoSquare_hcomp_of_symm
    {T : A ⥤ B} {T' : B ⥤ C} {L : A ⥤ D} {R : B ⥤ E} {R' : C ⥤ F} {B₁ : D ⥤ E}
    {B₂ : E ⥤ F} {To : A ⥤ C} {Bo : D ⥤ F}
    (So : To ⋙ R' ≅ L ⋙ Bo) (Sl : T ⋙ R ≅ L ⋙ B₁) (Sr : T' ⋙ R' ≅ R ⋙ B₂)
    (cT : T ⋙ T' ≅ To) (cB : B₁ ⋙ B₂ ≅ Bo)
    (h : So.symm = isoWhiskerLeft L cB.symm ≪≫ (associator L B₁ B₂).symm ≪≫
      isoWhiskerRight Sl.symm B₂ ≪≫ associator T R B₂ ≪≫ isoWhiskerLeft T Sr.symm ≪≫
      (associator T T' R').symm ≪≫ isoWhiskerRight cT R') :
    TwoSquare.mk To L R' Bo So.hom =
      ((TwoSquare.mk T L R B₁ Sl.hom ≫ₕ TwoSquare.mk T' R R' B₂ Sr.hom).whiskerTop
        cT.inv).whiskerBottom cB.hom := by
  have h' : So = (So.symm).symm := (Iso.symm_symm_eq So).symm
  rw [h', h]
  refine NatTrans.ext (funext fun Xa => ?_)
  simp [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

variable {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D} {Bm : C ⥤ D} {L' : C ⥤ E} {R' : D ⥤ F}
  {B' : E ⥤ F} {Lo : A ⥤ E} {Ro : B ⥤ F}

/-- **The inverse of a vertical composite of two invertible 2-squares, whiskered at the left and
at the right by isomorphisms, is the horizontal composite of the inverses**, whiskered at the top
and at the bottom. First half. -/
theorem vComp_whiskered_hom_inv_id (w : T ⋙ R ⟶ L ⋙ Bm) (w' : Bm ⋙ R' ⟶ L' ⋙ B')
    (cL : L ⋙ L' ≅ Lo) (cR : R ⋙ R' ≅ Ro) [IsIso w] [IsIso w'] :
    (((TwoSquare.mk _ _ _ _ w ≫ᵥ TwoSquare.mk _ _ _ _ w').whiskerRight cR.inv).whiskerLeft
        cL.hom) ≫
        ((TwoSquare.mk L T Bm R (inv w) ≫ₕ
          TwoSquare.mk L' Bm B' R' (inv w')).whiskerTop cL.inv).whiskerBottom
            cR.hom = 𝟙 _ := by
  refine NatTrans.ext (funext fun Xa => ?_)
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp, ← Functor.map_comp_assoc]

/-- The second half of `Stacks.Duality.vComp_whiskered_hom_inv_id`. -/
theorem vComp_whiskered_inv_hom_id (w : T ⋙ R ⟶ L ⋙ Bm) (w' : Bm ⋙ R' ⟶ L' ⋙ B')
    (cL : L ⋙ L' ≅ Lo) (cR : R ⋙ R' ≅ Ro) [IsIso w] [IsIso w'] :
    ((TwoSquare.mk L T Bm R (inv w) ≫ₕ
          TwoSquare.mk L' Bm B' R' (inv w')).whiskerTop cL.inv).whiskerBottom
            cR.hom ≫ (((TwoSquare.mk _ _ _ _ w ≫ᵥ TwoSquare.mk _ _ _ _ w').whiskerRight
              cR.inv).whiskerLeft cL.hom) = 𝟙 _ := by
  refine NatTrans.ext (funext fun Xa => ?_)
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp]

end Generic

/-! ### The composition formula for derived pullback, as a conjugate -/

section PullbackComp

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
  (hpusha : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward a).obj K.obj)).IsQuasicoherent)
  (hpushb : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward b).obj K.obj)).IsQuasicoherent)
  (hpushab : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (a ≫ b)).obj K.obj)).IsQuasicoherent)
  (hpulla : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback a).obj K.obj)).IsQuasicoherent)
  (hpullb : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPullback b).obj K.obj)).IsQuasicoherent)
  (hpullab : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback (a ≫ b)).obj K.obj)).IsQuasicoherent)

/-- **The composition formula `Lb^* ⋙ La^* ≅ L(a ≫ b)^*` on the quasi-coherent derived
categories**: the conjugate, under the derived adjunctions `L(a ≫ b)^* ⊣ R(a ≫ b)_*` and
`Lb^* ⋙ La^* ⊣ Ra_* ⋙ Rb_*`, of the composition formula for derived direct image. -/
def quasiCoherentDerivedPullbackCompIsoConj :
    quasiCoherentDerivedPullback b hpullb ⋙ quasiCoherentDerivedPullback a hpulla ≅
      quasiCoherentDerivedPullback (a ≫ b) hpullab :=
  (conjugateIsoEquiv (quasiCoherentDerivedAdjunction (a ≫ b) hpullab hpushab)
      ((quasiCoherentDerivedAdjunction b hpullb hpushb).comp
        (quasiCoherentDerivedAdjunction a hpulla hpusha))).symm
    (quasiCoherentDerivedPushforwardCompIso a b hpusha hpushb hpushab).symm

/-- The composition formula for derived pullback is conjugate to the inverse of the one for
derived direct image. -/
theorem conjugateEquiv_quasiCoherentDerivedPullbackCompIso_hom :
    conjugateEquiv (quasiCoherentDerivedAdjunction (a ≫ b) hpullab hpushab)
        ((quasiCoherentDerivedAdjunction b hpullb hpushb).comp
          (quasiCoherentDerivedAdjunction a hpulla hpusha))
        (quasiCoherentDerivedPullbackCompIsoConj a b hpusha hpushb hpushab hpulla hpullb
          hpullab).hom =
      (quasiCoherentDerivedPushforwardCompIso a b hpusha hpushb hpushab).inv := by
  have := congrArg Iso.hom (Equiv.apply_symm_apply
    (conjugateIsoEquiv (quasiCoherentDerivedAdjunction (a ≫ b) hpullab hpushab)
      ((quasiCoherentDerivedAdjunction b hpullb hpushb).comp
        (quasiCoherentDerivedAdjunction a hpulla hpusha)))
    (quasiCoherentDerivedPushforwardCompIso a b hpusha hpushb hpushab).symm)
  exact this

/-- The inverse of the composition formula for derived pullback is conjugate to the composition
formula for derived direct image. -/
theorem conjugateEquiv_quasiCoherentDerivedPullbackCompIso_inv :
    conjugateEquiv ((quasiCoherentDerivedAdjunction b hpullb hpushb).comp
          (quasiCoherentDerivedAdjunction a hpulla hpusha))
        (quasiCoherentDerivedAdjunction (a ≫ b) hpullab hpushab)
        (quasiCoherentDerivedPullbackCompIsoConj a b hpusha hpushb hpushab hpulla hpullb
          hpullab).inv =
      (quasiCoherentDerivedPushforwardCompIso a b hpusha hpushb hpushab).hom := by
  refine (Iso.inv_comp_eq_id (quasiCoherentDerivedPushforwardCompIso a b hpusha hpushb
    hpushab)).1 ?_
  rw [← conjugateEquiv_quasiCoherentDerivedPullbackCompIso_hom]
  exact conjugateEquiv_comm _ _ (Iso.inv_hom_id _)

end PullbackComp

/-! ### The transposed square -/

section Transpose

variable {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)

/-- **Derived direct image around the transposed square is the inverse comparison.** -/
theorem derivedPushforwardSquareIso_transpose (w : g' ≫ f = f' ≫ g) :
    derivedPushforwardSquareIso f' g' g f w.symm =
      (derivedPushforwardSquareIso g' f' f g w).symm := by
  ext K
  simp [derivedPushforwardSquareIso]

/-- `Stacks.Duality.derivedPushforwardSquareIso_transpose` on the quasi-coherent derived
categories. -/
theorem quasiCoherentDerivedPushforwardSquareIso_transpose (w : g' ≫ f = f' ≫ g) :
    quasiCoherentDerivedPushforwardSquareIso f' g' g f hpushf' hpushg hpushg' hpushf w.symm =
      (quasiCoherentDerivedPushforwardSquareIso g' f' f g hpushg' hpushf hpushf' hpushg
        w).symm := by
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  apply ObjectProperty.hom_ext
  have h := NatTrans.congr_app (congrArg Iso.hom
    (derivedPushforwardSquareIso_transpose g' f' f g w)) K.obj
  simpa [quasiCoherentDerivedPushforwardSquareIso] using h

/-- The mate of the base change map of a square is the inverse of its `ξ`. -/
private theorem mateEquiv_twistedInverseImageBaseChangeMap
    [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
    [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint] (sq : IsPullback g' f' f g)
    [IsIso (twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      sq)] :
    mateEquiv (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
        hpushg)
      (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
        hpushg')
      (TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap g' f' f g hpushg' hpushf hpushf'
        hpushg sq)) =
    TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange g' f' f g hpushg'
      hpushf hpushf' hpushg sq)) := by
  rw [twistedInverseImageBaseChangeMap_eq_mateEquiv_symm]
  exact Equiv.apply_symm_apply _ _

end Transpose

/-! ### The row of two squares -/

section Row

variable {X'' X' X Y'' Y' Y : Scheme.{u}} (k' : X'' ⟶ X') (k : X' ⟶ X) (f'' : X'' ⟶ Y'')
  (f' : X' ⟶ Y') (f : X ⟶ Y) (l' : Y'' ⟶ Y') (l : Y' ⟶ Y)
  (hpushk' : ∀ (K : quasiCoherentDerivedCategory X'') (i : ℤ),
    ((DerivedCategory.homologyFunctor X'.Modules i).obj
      ((derivedPushforward k').obj K.obj)).IsQuasicoherent)
  (hpushk : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward k).obj K.obj)).IsQuasicoherent)
  (hpushkk : ∀ (K : quasiCoherentDerivedCategory X'') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward (k' ≫ k)).obj K.obj)).IsQuasicoherent)
  (hpushf'' : ∀ (K : quasiCoherentDerivedCategory X'') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y''.Modules i).obj
      ((derivedPushforward f'').obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushl' : ∀ (K : quasiCoherentDerivedCategory Y'') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward l').obj K.obj)).IsQuasicoherent)
  (hpushl : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward l).obj K.obj)).IsQuasicoherent)
  (hpushll : ∀ (K : quasiCoherentDerivedCategory Y'') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward (l' ≫ l)).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f'' hpushf'').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]

omit [(quasiCoherentDerivedPushforward f'' hpushf'').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint] in
/-- **Derived direct image around a row of two commutative squares.** The comparison for the
outer rectangle is the horizontal paste of the comparisons for the two squares, the direct images
along the two composite horizontal morphisms being read through the composition formula. It is
the vertical stacking identity for the transposed rectangle, read backwards. -/
theorem quasiCoherentDerivedPushforwardSquareIso_hcomp (w₁ : k' ≫ f' = f'' ≫ l')
    (w₂ : k ≫ f = f' ≫ l) (w : (k' ≫ k) ≫ f = f'' ≫ l' ≫ l) :
    TwoSquare.mk _ _ _ _ (quasiCoherentDerivedPushforwardSquareIso (k' ≫ k) f'' f (l' ≫ l)
        hpushkk hpushf hpushf'' hpushll w).hom =
      ((TwoSquare.mk _ _ _ _ (quasiCoherentDerivedPushforwardSquareIso k' f'' f' l' hpushk'
          hpushf' hpushf'' hpushl' w₁).hom ≫ₕ
        TwoSquare.mk _ _ _ _ (quasiCoherentDerivedPushforwardSquareIso k f' f l hpushk hpushf
          hpushf' hpushl w₂).hom).whiskerTop
        (quasiCoherentDerivedPushforwardCompIso k' k hpushk' hpushk hpushkk).inv).whiskerBottom
        (quasiCoherentDerivedPushforwardCompIso l' l hpushl' hpushl hpushll).hom := by
  refine twoSquare_hcomp_of_symm _ _ _ _ _ ?_
  have hv := quasiCoherentDerivedPushforwardSquareIso_vcomp f'' k' l' f' k l f hpushf'' hpushl'
    hpushk' hpushf' hpushl hpushk hpushf hpushll hpushkk w.symm w₁.symm w₂.symm
  rw [quasiCoherentDerivedPushforwardSquareIso_transpose (k' ≫ k) f'' f (l' ≫ l) hpushkk hpushf
      hpushf'' hpushll w,
    quasiCoherentDerivedPushforwardSquareIso_transpose k' f'' f' l' hpushk' hpushf' hpushf''
      hpushl' w₁,
    quasiCoherentDerivedPushforwardSquareIso_transpose k f' f l hpushk hpushf hpushf' hpushl
      w₂] at hv
  exact hv

/-- **The transformation `ξ` of [Stacks, Tag 0A9K] for a row of two cartesian squares is the
vertical paste of the transformations of the two squares**, the derived direct images along the
two composite horizontal morphisms being read through the composition formula. `ξ` is the mate of
the comparison of derived direct image around the square under the twisted inverse image
adjunctions of the vertical morphisms, none of which is composite here. -/
theorem twistedInverseImagePushforwardBaseChange_hcomp (sq₁ : IsPullback k' f'' f' l')
    (sq₂ : IsPullback k f' f l) :
    twistedInverseImagePushforwardBaseChange (k' ≫ k) f'' f (l' ≫ l) hpushkk hpushf hpushf''
        hpushll (sq₁.paste_horiz sq₂) =
      ((TwoSquare.mk _ _ _ _ (twistedInverseImagePushforwardBaseChange k' f'' f' l' hpushk'
            hpushf' hpushf'' hpushl' sq₁) ≫ᵥ
          TwoSquare.mk _ _ _ _ (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf
            hpushf' hpushl sq₂)).whiskerRight
        (quasiCoherentDerivedPushforwardCompIso k' k hpushk' hpushk hpushkk).inv).whiskerLeft
        (quasiCoherentDerivedPushforwardCompIso l' l hpushl' hpushl hpushll).hom := by
  have h := congrArg (mateEquiv (twistedInverseImageAdjunction f'' hpushf'')
      (twistedInverseImageAdjunction f hpushf))
    (quasiCoherentDerivedPushforwardSquareIso_hcomp k' k f'' f' f l' l hpushk' hpushk hpushkk
      hpushf'' hpushf' hpushf hpushl' hpushl hpushll sq₁.w sq₂.w (sq₁.paste_horiz sq₂).w)
  rw [mateEquiv_whisker, mateEquiv_vcomp _ (twistedInverseImageAdjunction f' hpushf')] at h
  exact h

/-- **The transformation `ξ` for the outer rectangle of a row is invertible as soon as it is for
the two squares.** -/
theorem isIso_twistedInverseImagePushforwardBaseChange_hcomp (sq₁ : IsPullback k' f'' f' l')
    (sq₂ : IsPullback k f' f l)
    [IsIso (twistedInverseImagePushforwardBaseChange k' f'' f' l' hpushk' hpushf' hpushf''
      hpushl' sq₁)]
    [IsIso (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf hpushf' hpushl sq₂)] :
    IsIso (twistedInverseImagePushforwardBaseChange (k' ≫ k) f'' f (l' ≫ l) hpushkk hpushf
      hpushf'' hpushll (sq₁.paste_horiz sq₂)) := by
  rw [twistedInverseImagePushforwardBaseChange_hcomp k' k f'' f' f l' l hpushk' hpushk hpushkk
    hpushf'' hpushf' hpushf hpushl' hpushl hpushll sq₁ sq₂]
  exact ⟨_, vComp_whiskered_hom_inv_id _ _
      (quasiCoherentDerivedPushforwardCompIso l' l hpushl' hpushl hpushll)
      (quasiCoherentDerivedPushforwardCompIso k' k hpushk' hpushk hpushkk),
    vComp_whiskered_inv_hom_id _ _
      (quasiCoherentDerivedPushforwardCompIso l' l hpushl' hpushl hpushll)
      (quasiCoherentDerivedPushforwardCompIso k' k hpushk' hpushk hpushkk)⟩

section Gamma

/-- **[Stacks, Tag 0ATR] (Lemma 48.5.2): the base change maps of a row of two cartesian squares
compose to the base change map of the outer rectangle.** For

```
X'' --k'--> X' --k--> X
|f''        |f'       |f
Y'' --l'--> Y' --l--> Y
```

with both squares cartesian, the base change map `Stacks.Duality.twistedInverseImageBaseChangeMap`
of [Stacks, Tag 0AA6] for the rectangle — the square with horizontal edges `k' ≫ k` and `l' ≫ l` —
is the vertical paste of the base change maps of the right and of the left square, the derived
pullbacks along the two composite horizontals being read through the composition formula
`Stacks.Duality.quasiCoherentDerivedPullbackCompIsoConj`.

Each base change map is the mate of the inverse of the corresponding `ξ`
(`Stacks.Duality.twistedInverseImageBaseChangeMap_eq_mateEquiv_symm`), the rectangle's `ξ` is
the vertical paste of the two (`Stacks.Duality.twistedInverseImagePushforwardBaseChange_hcomp`),
and the inverse of a vertical paste is the horizontal paste of the inverses; the passage between
the two pastes is `Stacks.Cohomology.DerivedBaseChangePasting.mate_twoSquare_paste`, with the
composite adjunctions traded through the composition formulas, which are conjugate by
construction. -/
@[stacks 0ATR "for the base change map of Stacks 0AA6 attached to the twisted inverse image \
  f^x of Stacks 0A9E -- the right adjoint of Rf_* on D_QCoh: the map of the outer rectangle of a \
  row of two cartesian squares is the vertical composite of the maps of the two squares, read \
  through the composition formula for derived pullback along the two composite horizontal \
  morphisms. The source's quasi-compactness and quasi-separatedness enter as the preservation \
  of quasi-coherent cohomology by derived direct and inverse image along the morphisms of the \
  diagram and as the existence of the three right adjoints, which is what Stacks 08D5 part (1) \
  and Stacks 0A9E produce for a quasi-compact quasi-separated morphism. Invertibility of the \
  transformation xi of Stacks 0A9K for each of the two squares is an instance argument, exactly \
  as in Stacks.Duality.twistedInverseImageBaseChangeMap where the base change map is defined, \
  and it is Stacks 0A9K that produces it for a Tor-independent square; the rectangle's needs no \
  third input, by Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_hcomp"]
theorem twistedInverseImageBaseChangeMap_hcomp (sq₁ : IsPullback k' f'' f' l')
    (sq₂ : IsPullback k f' f l)
    [IsIso (twistedInverseImagePushforwardBaseChange k' f'' f' l' hpushk' hpushf' hpushf''
      hpushl' sq₁)]
    [IsIso (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf hpushf' hpushl sq₂)] :
    letI := isIso_twistedInverseImagePushforwardBaseChange_hcomp k' k f'' f' f l' l hpushk'
      hpushk hpushkk hpushf'' hpushf' hpushf hpushl' hpushl hpushll sq₁ sq₂
    twistedInverseImageBaseChangeMap (k' ≫ k) f'' f (l' ≫ l) hpushkk hpushf hpushf'' hpushll
        (sq₁.paste_horiz sq₂) =
      (((TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap k f' f l hpushk hpushf hpushf'
              hpushl sq₂) ≫ᵥ
          TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap k' f'' f' l' hpushk' hpushf'
            hpushf'' hpushl' sq₁)).whiskerLeft
        (quasiCoherentDerivedPullbackCompIsoConj l' l hpushl' hpushl hpushll
          (isQuasicoherent_homology_derivedPullback' l')
          (isQuasicoherent_homology_derivedPullback' l)
          (isQuasicoherent_homology_derivedPullback' (l' ≫ l))).hom).whiskerRight
        (quasiCoherentDerivedPullbackCompIsoConj k' k hpushk' hpushk hpushkk
          (isQuasicoherent_homology_derivedPullback' k')
          (isQuasicoherent_homology_derivedPullback' k)
          (isQuasicoherent_homology_derivedPullback' (k' ≫ k))).inv) := by
  let := isIso_twistedInverseImagePushforwardBaseChange_hcomp k' k f'' f' f l' l hpushk'
    hpushk hpushkk hpushf'' hpushf' hpushf hpushl' hpushl hpushll sq₁ sq₂
  have hinv : TwoSquare.mk _ _ _ _
        (inv (twistedInverseImagePushforwardBaseChange (k' ≫ k) f'' f (l' ≫ l) hpushkk hpushf
          hpushf'' hpushll (sq₁.paste_horiz sq₂))) =
      ((TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange k' f'' f' l' hpushk'
            hpushf' hpushf'' hpushl' sq₁)) ≫ₕ
        TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange k f' f l hpushk
          hpushf hpushf' hpushl sq₂))).whiskerTop
          (quasiCoherentDerivedPushforwardCompIso l' l hpushl' hpushl hpushll).inv).whiskerBottom
        (quasiCoherentDerivedPushforwardCompIso k' k hpushk' hpushk hpushkk).hom := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [twistedInverseImagePushforwardBaseChange_hcomp k' k f'' f' f l' l hpushk' hpushk hpushkk
      hpushf'' hpushf' hpushf hpushl' hpushl hpushll sq₁ sq₂]
    exact vComp_whiskered_hom_inv_id _ _
      (quasiCoherentDerivedPushforwardCompIso l' l hpushl' hpushl hpushll)
      (quasiCoherentDerivedPushforwardCompIso k' k hpushk' hpushk hpushkk)
  have hpaste := mate_twoSquare_paste
    (quasiCoherentDerivedAdjunction l (isQuasicoherent_homology_derivedPullback' l) hpushl)
    (quasiCoherentDerivedAdjunction k (isQuasicoherent_homology_derivedPullback' k) hpushk)
    (quasiCoherentDerivedAdjunction l' (isQuasicoherent_homology_derivedPullback' l') hpushl')
    (quasiCoherentDerivedAdjunction k' (isQuasicoherent_homology_derivedPullback' k') hpushk')
    (quasiCoherentDerivedAdjunction (l' ≫ l) (isQuasicoherent_homology_derivedPullback' (l' ≫ l))
      hpushll)
    (quasiCoherentDerivedAdjunction (k' ≫ k) (isQuasicoherent_homology_derivedPullback' (k' ≫ k))
      hpushkk)
    (TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap k f' f l hpushk hpushf hpushf'
      hpushl sq₂))
    (TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap k' f'' f' l' hpushk' hpushf'
      hpushf'' hpushl' sq₁)) _
    (quasiCoherentDerivedPullbackCompIsoConj l' l hpushl' hpushl hpushll
      (isQuasicoherent_homology_derivedPullback' l') (isQuasicoherent_homology_derivedPullback' l)
      (isQuasicoherent_homology_derivedPullback' (l' ≫ l))).hom
    (quasiCoherentDerivedPullbackCompIsoConj k' k hpushk' hpushk hpushkk
      (isQuasicoherent_homology_derivedPullback' k') (isQuasicoherent_homology_derivedPullback' k)
      (isQuasicoherent_homology_derivedPullback' (k' ≫ k))).inv
    _ _ rfl
    (conjugateEquiv_quasiCoherentDerivedPullbackCompIso_hom l' l hpushl' hpushl hpushll
      (isQuasicoherent_homology_derivedPullback' l') (isQuasicoherent_homology_derivedPullback' l)
      (isQuasicoherent_homology_derivedPullback' (l' ≫ l)))
    (conjugateEquiv_quasiCoherentDerivedPullbackCompIso_inv k' k hpushk' hpushk hpushkk
      (isQuasicoherent_homology_derivedPullback' k') (isQuasicoherent_homology_derivedPullback' k)
      (isQuasicoherent_homology_derivedPullback' (k' ≫ k)))
  rw [mateEquiv_twistedInverseImageBaseChangeMap k' f'' f' l' hpushk' hpushf' hpushf'' hpushl' sq₁,
    mateEquiv_twistedInverseImageBaseChangeMap k f' f l hpushk hpushf hpushf' hpushl sq₂,
    ← hinv] at hpaste
  refine (twistedInverseImageBaseChangeMap_eq_mateEquiv_symm (k' ≫ k) f'' f (l' ≫ l) hpushkk
    hpushf hpushf'' hpushll (sq₁.paste_horiz sq₂)).trans ?_
  rw [← hpaste]
  exact Equiv.symm_apply_apply _ _

end Gamma

end Row

end Stacks.Duality

end
