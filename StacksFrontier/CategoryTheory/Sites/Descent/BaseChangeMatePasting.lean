module

public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentBaseChange

/-!
# Pasting the base-change `2`-cells of a pseudofunctor, and base change through descent

Let `F` be a pseudofunctor from the locally discrete bicategory on `Cᵒᵖ` to `Cat` whose transition
functors are left adjoints. A commutative square `i ≫ f = f' ≫ g` of `C` has a comparison
isomorphism of the two composite inverse images, `CategoryTheory.Pseudofunctor.commSqTwoSquare`,
and its adjoint mate across the adjunctions of `f` and `f'` is the base-change `2`-cell
`R_f ⋙ g^* ⟶ i^* ⋙ R_{f'}`. This file proves the two pasting laws for these `2`-cells, and a
criterion for the `2`-cell to be invertible obtained by descent.

## Main results

* `CategoryTheory.Pseudofunctor.isoMapOfCommSq_symm`: the comparison of the transposed square is
  the inverse of the comparison of the square.
* `CategoryTheory.Pseudofunctor.isoMapOfCommSq_paste_horiz_app` and
  `CategoryTheory.Pseudofunctor.isoMapOfCommSq_paste_vert_app`: the comparison of a pasted square
  is the composite of the comparisons of its two halves and of the composition constraints.
* `CategoryTheory.Pseudofunctor.mateEquiv_commSqTwoSquare_paste_horiz_app` and
  `CategoryTheory.Pseudofunctor.mateEquiv_commSqTwoSquare_paste_vert_app`: **the pasting laws for
  the base-change `2`-cells**, horizontally (along the base-change direction) and vertically
  (along the direct-image direction).
* `CategoryTheory.Pseudofunctor.isIso_app_of_isIso_descentUnit`: **base change through
  descent.** Let `f : X ⟶ Y` be a morphism along which the canonical descent datum of an object
  `N` over `Y` recovers `N`, and likewise for its base change along `g : V ⟶ Y` and the object
  `g^* N`. A natural transformation `a : Φ ⟶ g^* ⋙ Ψ` between equalizer-preserving functors is
  invertible at `N` as soon as its composites with the base-change `2`-cells of the two squares
  `(f, g)` and `(X ×_Y X ⟶ Y, g)` are invertible.

## Implementation notes

The two coherences of the comparison isomorphisms are instances of
`CategoryTheory.Pseudofunctor.square_comp_coherence`: the vertical one directly, the horizontal one
after transposing the two squares, which inverts their comparisons.

The pasting laws for the mates are then Mathlib's `CategoryTheory.mateEquiv_vcomp` (horizontally,
where the adjunctions along the direct-image direction do not change) and
`CategoryTheory.mateEquiv_hcomp` (vertically, where they are composed), together with the
compatibility of mates with whiskering by the composition constraints. Vertically the composite
adjunction is compared with the adjunction of the composite morphism by
`CategoryTheory.conjugateEquiv` of the composition constraint.

In the descent criterion the object `N` is the equalizer of the reconstruction of its canonical
descent datum (`CategoryTheory.Pseudofunctor.singletonDescentAdjunction`), and so is `g^* N` for
the base-changed datum. The functor `Φ` carries the first equalizer to an equalizer, and `Ψ` the
second; the given composites are invertible maps between the two parallel pairs, compatible with
them by `CategoryTheory.Pseudofunctor.reconstructionFirst_baseChange` and
`CategoryTheory.Pseudofunctor.reconstructionSecond_baseChange`. The induced map of equalizers is
`a` followed by `Ψ` of the comparison of the two reconstructions, and that comparison is
invertible because both reconstructions are identified with `g^* N`, the identification being
`CategoryTheory.unit_mateEquiv`.

Nothing here carries a Stacks attribute: this is category-theoretic substrate, and the source
states none of it.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite TwoSquare

universe v v' u u' v₁ u₁

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- The comparison isomorphism of the transposed square is the inverse of the comparison
isomorphism of the square. -/
theorem isoMapOfCommSq_symm {X₁ X₂ Y₁ Y₂ : C} {i : X₂ ⟶ X₁} {f' : X₂ ⟶ Y₂} {f : X₁ ⟶ Y₁}
    {g : Y₂ ⟶ Y₁} (w : i ≫ f = f' ≫ g) :
    F.isoMapOfCommSq (CommSq.mk w.symm).op.toLoc =
      (F.isoMapOfCommSq (CommSq.mk w).op.toLoc).symm := by
  rw [isoMapOfCommSq_eq_comp F w, isoMapOfCommSq_eq_comp F w.symm]
  ext1
  simp
  rfl

/-! ### The coherences of the comparison isomorphisms of pasted squares -/

/-- **The comparison isomorphism of a horizontally pasted square.** For two squares
`i ≫ f = f' ≫ g` and `j ≫ f' = f'' ≫ e` sharing the edge `f'`, the comparison of the outer
square is the composite of the two comparisons and of the composition constraints of `F` along
the two composite edges `e ≫ g` and `j ≫ i`. -/
theorem isoMapOfCommSq_paste_horiz_app {X Y X' Y' X'' Y'' : C} (i : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (e : Y'' ⟶ Y')
    (w₁ : i ≫ f = f' ≫ g) (w₂ : j ≫ f' = f'' ≫ e) (w : (j ≫ i) ≫ f = f'' ≫ e ≫ g)
    (W : F.obj (.mk (op Y))) :
    (F.isoMapOfCommSq (CommSq.mk w).op.toLoc).hom.toNatTrans.app W =
      (F.map f''.op.toLoc).toFunctor.map
          ((F.mapComp' g.op.toLoc e.op.toLoc (e ≫ g).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app W) ≫
        (F.isoMapOfCommSq (CommSq.mk w₂).op.toLoc).hom.toNatTrans.app
            ((F.map g.op.toLoc).toFunctor.obj W) ≫
          (F.map j.op.toLoc).toFunctor.map
              ((F.isoMapOfCommSq (CommSq.mk w₁).op.toLoc).hom.toNatTrans.app W) ≫
            (F.mapComp' i.op.toLoc j.op.toLoc (j ≫ i).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
              ((F.map f.op.toLoc).toFunctor.obj W) := by
  have key := square_comp_coherence F g f f' i e (e ≫ g) f'' j (j ≫ i) w₁.symm rfl rfl w₂
    w.symm W
  rw [isoMapOfCommSq_symm F w, isoMapOfCommSq_symm F w₁] at key
  simp only [Iso.symm_hom] at key
  rw [← cancel_epi ((F.isoMapOfCommSq (CommSq.mk w).op.toLoc).inv.toNatTrans.app W),
    Cat.Hom.inv_hom_id_toNatTrans_app, reassoc_of% key]
  simp [← Functor.map_comp_assoc]

/-- **The comparison isomorphism of a vertically pasted square.** For two squares
`i ≫ f = f' ≫ g` and `i₁ ≫ h = h' ≫ i` sharing the edge `i`, the comparison of the outer square
`i₁ ≫ h ≫ f = (h' ≫ f') ≫ g` is the composite of the two comparisons and of the composition
constraints of `F` along the two composite edges `h ≫ f` and `h' ≫ f'`. -/
theorem isoMapOfCommSq_paste_vert_app {X Y X' Y' X₁ X'₁ : C} (i : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (i₁ : X'₁ ⟶ X₁) (h' : X'₁ ⟶ X') (h : X₁ ⟶ X)
    (w : i ≫ f = f' ≫ g) (w₁ : i₁ ≫ h = h' ≫ i) (w₂ : i₁ ≫ h ≫ f = (h' ≫ f') ≫ g)
    (W : F.obj (.mk (op Y))) :
    (F.isoMapOfCommSq (CommSq.mk w₂).op.toLoc).hom.toNatTrans.app W =
      (F.mapComp' f'.op.toLoc h'.op.toLoc (h' ≫ f').op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          ((F.map g.op.toLoc).toFunctor.obj W) ≫
        (F.map h'.op.toLoc).toFunctor.map
            ((F.isoMapOfCommSq (CommSq.mk w).op.toLoc).hom.toNatTrans.app W) ≫
          (F.isoMapOfCommSq (CommSq.mk w₁).op.toLoc).hom.toNatTrans.app
              ((F.map f.op.toLoc).toFunctor.obj W) ≫
            (F.map i₁.op.toLoc).toFunctor.map
              ((F.mapComp' f.op.toLoc h.op.toLoc (h ≫ f).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app W) := by
  have key := square_comp_coherence F f g i f' h (h ≫ f) i₁ h' (h' ≫ f') w rfl rfl w₁.symm w₂ W
  rw [isoMapOfCommSq_symm F w₁] at key
  simp only [Iso.symm_hom] at key
  rw [← reassoc_of% key]
  simp [← Functor.map_comp]

/-! ### The pasting laws for the base-change `2`-cells -/

section PasteHoriz

variable {X Y X' Y' X'' Y'' : C} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (e : Y'' ⟶ Y')
  (w₁ : i ≫ f = f' ≫ g) (w₂ : j ≫ f' = f'' ≫ e) (w : (j ≫ i) ≫ f = f'' ≫ e ≫ g)
  {Rf : F.obj (.mk (op X)) ⥤ F.obj (.mk (op Y))} (af : (F.map f.op.toLoc).toFunctor ⊣ Rf)
  {Rf' : F.obj (.mk (op X')) ⥤ F.obj (.mk (op Y'))}
  (af' : (F.map f'.op.toLoc).toFunctor ⊣ Rf')
  {Rf'' : F.obj (.mk (op X'')) ⥤ F.obj (.mk (op Y''))}
  (af'' : (F.map f''.op.toLoc).toFunctor ⊣ Rf'')

/-- **The horizontal pasting law for the base-change `2`-cells.** The base-change `2`-cell of
the outer square, along the composite `e ≫ g`, is the base-change `2`-cell of the right square
pulled back along `e`, followed by the base-change `2`-cell of the left square, read through the
composition constraints of `F` along `e ≫ g` and `j ≫ i`. -/
theorem mateEquiv_commSqTwoSquare_paste_horiz_app (M : F.obj (.mk (op X))) :
    (mateEquiv af af'' (commSqTwoSquare F w)).natTrans.app M =
      (F.mapComp' g.op.toLoc e.op.toLoc (e ≫ g).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app (Rf.obj M) ≫
        (F.map e.op.toLoc).toFunctor.map
            ((mateEquiv af af' (commSqTwoSquare F w₁)).natTrans.app M) ≫
          (mateEquiv af' af'' (commSqTwoSquare F w₂)).natTrans.app
              ((F.map i.op.toLoc).toFunctor.obj M) ≫
            Rf''.map ((F.mapComp' i.op.toLoc j.op.toLoc (j ≫ i).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
              M) := by
  have hc : commSqTwoSquare F w =
      ((commSqTwoSquare F w₁ ≫ₕ commSqTwoSquare F w₂).whiskerTop
          (F.mapComp' g.op.toLoc e.op.toLoc (e ≫ g).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans).whiskerBottom
        (F.mapComp' i.op.toLoc j.op.toLoc (j ≫ i).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans := by
    refine TwoSquare.ext _ _ fun W => ?_
    simp only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app,
      TwoSquare.hComp_app, Category.assoc]
    exact isoMapOfCommSq_paste_horiz_app F i f' f g j f'' e w₁ w₂ w W
  have hm : ∀ {A B A' B' : Type u'} [Category.{v'} A] [Category.{v'} B] [Category.{v'} A']
      [Category.{v'} B'] {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : A' ⥤ B'} {R₂ : B' ⥤ A'}
      (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G G' : A ⥤ A'} {H H' : B ⥤ B'}
      (S : TwoSquare G L₁ L₂ H) (φ : G' ⟶ G) (ψ : H ⟶ H'),
      mateEquiv adj₁ adj₂ ((S.whiskerTop φ).whiskerBottom ψ) =
        ((mateEquiv adj₁ adj₂ S).whiskerRight φ).whiskerLeft ψ := by
    intro A B A' B' _ _ _ _ L₁ R₁ L₂ R₂ adj₁ adj₂ G G' H H' S φ ψ
    refine TwoSquare.ext _ _ fun d => ?_
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
      TwoSquare.whiskerRight, mateEquiv]
  rw [hc, hm af af'', mateEquiv_vcomp af af' af'']
  simp [TwoSquare.vComp]

/-- The outer base-change `2`-cell of a horizontal pasting is invertible at `M` iff the pasted
middle composite is. -/
private theorem isIso_mateEquiv_commSqTwoSquare_paste_horiz_app_iff (M : F.obj (.mk (op X))) :
    IsIso ((mateEquiv af af'' (commSqTwoSquare F w)).natTrans.app M) ↔
      IsIso ((F.map e.op.toLoc).toFunctor.map
          ((mateEquiv af af' (commSqTwoSquare F w₁)).natTrans.app M) ≫
        (mateEquiv af' af'' (commSqTwoSquare F w₂)).natTrans.app
          ((F.map i.op.toLoc).toFunctor.obj M)) := by
  rw [mateEquiv_commSqTwoSquare_paste_horiz_app F i f' f g j f'' e w₁ w₂ w af af' af'' M]
  have := ((Cat.Hom.toNatIso (F.mapComp' g.op.toLoc e.op.toLoc
      (e ≫ g).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]))).app (Rf.obj M)).isIso_hom
  have := Functor.map_isIso Rf'' ((Cat.Hom.toNatIso (F.mapComp' i.op.toLoc j.op.toLoc
        (j ≫ i).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]))).app M).inv
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff]

/-- **The outer square of two horizontally pasted squares has invertible base-change `2`-cell**
as soon as the two squares have. -/
theorem isIso_mateEquiv_commSqTwoSquare_paste_horiz
    (h₁ : IsIso (mateEquiv af af' (commSqTwoSquare F w₁)).natTrans)
    (h₂ : IsIso (mateEquiv af' af'' (commSqTwoSquare F w₂)).natTrans) :
    IsIso (mateEquiv af af'' (commSqTwoSquare F w)).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [isIso_mateEquiv_commSqTwoSquare_paste_horiz_app_iff F i f' f g j f'' e w₁ w₂ w af af' af'']
  have := NatIso.isIso_app_of_isIso (mateEquiv af af' (commSqTwoSquare F w₁)).natTrans M
  have := NatIso.isIso_app_of_isIso (mateEquiv af' af'' (commSqTwoSquare F w₂)).natTrans
    ((F.map i.op.toLoc).toFunctor.obj M)
  infer_instance

/-- **Cancelling the second square in the horizontal pasting law.** If the outer square and the
second square have invertible base-change `2`-cells, then the inverse image along `e` of the
`2`-cell of the first square is invertible. -/
theorem isIso_whiskerRight_mateEquiv_commSqTwoSquare_of_paste_horiz
    (hout : IsIso (mateEquiv af af'' (commSqTwoSquare F w)).natTrans)
    (h₂ : IsIso (mateEquiv af' af'' (commSqTwoSquare F w₂)).natTrans) :
    IsIso (Functor.whiskerRight (mateEquiv af af' (commSqTwoSquare F w₁)).natTrans
      (F.map e.op.toLoc).toFunctor) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hx := (isIso_mateEquiv_commSqTwoSquare_paste_horiz_app_iff F i f' f g j f'' e w₁ w₂ w af
    af' af'' M).1 (NatIso.isIso_app_of_isIso _ M)
  have := NatIso.isIso_app_of_isIso (mateEquiv af' af'' (commSqTwoSquare F w₂)).natTrans
    ((F.map i.op.toLoc).toFunctor.obj M)
  rwa [isIso_comp_right_iff] at hx

/-- **Cancelling the first square in the horizontal pasting law.** If the outer square and the
first square have invertible base-change `2`-cells, then the `2`-cell of the second square is
invertible after precomposition with the inverse image along `i`. -/
theorem isIso_whiskerLeft_mateEquiv_commSqTwoSquare_of_paste_horiz
    (hout : IsIso (mateEquiv af af'' (commSqTwoSquare F w)).natTrans)
    (h₁ : IsIso (mateEquiv af af' (commSqTwoSquare F w₁)).natTrans) :
    IsIso (Functor.whiskerLeft (F.map i.op.toLoc).toFunctor
      (mateEquiv af' af'' (commSqTwoSquare F w₂)).natTrans) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hx := (isIso_mateEquiv_commSqTwoSquare_paste_horiz_app_iff F i f' f g j f'' e w₁ w₂ w af
    af' af'' M).1 (NatIso.isIso_app_of_isIso _ M)
  have := NatIso.isIso_app_of_isIso (mateEquiv af af' (commSqTwoSquare F w₁)).natTrans M
  rwa [isIso_comp_left_iff] at hx

end PasteHoriz

section PasteVert

variable {X Y X' Y' X₁ X'₁ : C} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (i₁ : X'₁ ⟶ X₁) (h' : X'₁ ⟶ X') (h : X₁ ⟶ X)
  (w : i ≫ f = f' ≫ g) (w₁ : i₁ ≫ h = h' ≫ i) (w₂ : i₁ ≫ h ≫ f = (h' ≫ f') ≫ g)
  {Rf : F.obj (.mk (op X)) ⥤ F.obj (.mk (op Y))} (af : (F.map f.op.toLoc).toFunctor ⊣ Rf)
  {Rf' : F.obj (.mk (op X')) ⥤ F.obj (.mk (op Y'))}
  (af' : (F.map f'.op.toLoc).toFunctor ⊣ Rf')
  {Rh : F.obj (.mk (op X₁)) ⥤ F.obj (.mk (op X))} (ah : (F.map h.op.toLoc).toFunctor ⊣ Rh)
  {Rh' : F.obj (.mk (op X'₁)) ⥤ F.obj (.mk (op X'))}
  (ah' : (F.map h'.op.toLoc).toFunctor ⊣ Rh')
  {Rhf : F.obj (.mk (op X₁)) ⥤ F.obj (.mk (op Y))}
  (ahf : (F.map (h ≫ f).op.toLoc).toFunctor ⊣ Rhf)
  {Rhf' : F.obj (.mk (op X'₁)) ⥤ F.obj (.mk (op Y'))}
  (ahf' : (F.map (h' ≫ f').op.toLoc).toFunctor ⊣ Rhf')

/-- **The vertical pasting law for the base-change `2`-cells.** The base-change `2`-cell of the
outer square, along the composite `h ≫ f`, is the base-change `2`-cell of the lower square at
`R_h M` followed by the direct image along `f'` of the base-change `2`-cell of the upper square,
read through the conjugates of the composition constraints of `F` along `h ≫ f` and
`h' ≫ f'`, which compare the direct images along the composites with the composites of the
direct images. -/
theorem mateEquiv_commSqTwoSquare_paste_vert_app (M : F.obj (.mk (op X₁))) :
    (mateEquiv ahf ahf' (commSqTwoSquare F w₂)).natTrans.app M =
      (F.map g.op.toLoc).toFunctor.map ((conjugateEquiv ahf (af.comp ah)
          (F.mapComp' f.op.toLoc h.op.toLoc (h ≫ f).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans).app M) ≫
        (mateEquiv af af' (commSqTwoSquare F w)).natTrans.app (Rh.obj M) ≫
          Rf'.map ((mateEquiv ah ah' (commSqTwoSquare F w₁)).natTrans.app M) ≫
            (conjugateEquiv (af'.comp ah') ahf'
              (F.mapComp' f'.op.toLoc h'.op.toLoc (h' ≫ f').op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans).app
                ((F.map i₁.op.toLoc).toFunctor.obj M) := by
  have hc : commSqTwoSquare F w₂ =
      ((commSqTwoSquare F w ≫ᵥ commSqTwoSquare F w₁).whiskerRight
          (F.mapComp' f'.op.toLoc h'.op.toLoc (h' ≫ f').op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans).whiskerLeft
        (F.mapComp' f.op.toLoc h.op.toLoc (h ≫ f).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans := by
    refine TwoSquare.ext _ _ fun W => ?_
    simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.vComp_app, Category.assoc]
    exact isoMapOfCommSq_paste_vert_app F i f' f g i₁ h' h w w₁ w₂ W
  rw [hc, conjugateEquiv_mateEquiv_vcomp ahf (af.comp ah) ahf',
    mateEquiv_conjugateEquiv_vcomp (af.comp ah) (af'.comp ah') ahf', mateEquiv_hcomp af af' ah ah']
  simp [TwoSquare.hComp]

/-- **The vertical pasting law, for invertibility.** If the outer square of two vertically
pasted squares has invertible base-change `2`-cell, then so is, at every object `M` over `X₁`,
the `2`-cell of the lower square at `R_h M` followed by the direct image along `f'` of the
`2`-cell of the upper square at `M`. -/
theorem isIso_mateEquiv_commSqTwoSquare_comp_of_paste_vert
    (hout : IsIso (mateEquiv ahf ahf' (commSqTwoSquare F w₂)).natTrans)
    (M : F.obj (.mk (op X₁))) :
    IsIso ((mateEquiv af af' (commSqTwoSquare F w)).natTrans.app (Rh.obj M) ≫
      Rf'.map ((mateEquiv ah ah' (commSqTwoSquare F w₁)).natTrans.app M)) := by
  have hx := NatIso.isIso_app_of_isIso (mateEquiv ahf ahf' (commSqTwoSquare F w₂)).natTrans M
  rw [mateEquiv_commSqTwoSquare_paste_vert_app F i f' f g i₁ h' h w w₁ w₂ af af' ah ah' ahf ahf'
    M] at hx
  have : IsIso (F.mapComp' f.op.toLoc h.op.toLoc (h ≫ f).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans :=
    (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc h.op.toLoc (h ≫ f).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]))).isIso_inv
  have : IsIso (F.mapComp' f'.op.toLoc h'.op.toLoc (h' ≫ f').op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans :=
    (Cat.Hom.toNatIso (F.mapComp' f'.op.toLoc h'.op.toLoc (h' ≫ f').op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]))).isIso_hom
  rwa [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff] at hx

end PasteVert

/-! ### Base change through descent -/

section Descent

variable {X Y V : C} (f : X ⟶ Y) (g : V ⟶ Y)
  (P : ChosenPullback f g) (XX : ChosenPullback f f) (QQ : ChosenPullback P.p₂ P.p₂)
  (hw : P.p₁ ≫ f = P.p₂ ≫ g)
  (j : QQ.pullback ⟶ XX.pullback)
  (hj : j ≫ XX.p = QQ.p ≫ g)
  (hs₁ : QQ.p₁ ≫ P.p₁ = j ≫ XX.p₁) (hs₂ : QQ.p₂ ≫ P.p₁ = j ≫ XX.p₂)
  {R : F.obj (.mk (.op X)) ⥤ F.obj (.mk (.op Y))}
  (af : (F.map f.op.toLoc).toFunctor ⊣ R)
  {T : F.obj (.mk (.op XX.pullback)) ⥤ F.obj (.mk (.op Y))}
  (af₁ : (F.map XX.p.op.toLoc).toFunctor ⊣ T)
  {Rq : F.obj (.mk (.op P.pullback)) ⥤ F.obj (.mk (.op V))}
  (aq : (F.map P.p₂.op.toLoc).toFunctor ⊣ Rq)
  {Tq : F.obj (.mk (.op QQ.pullback)) ⥤ F.obj (.mk (.op V))}
  (aq₁ : (F.map QQ.p.op.toLoc).toFunctor ⊣ Tq)
  {𝒟 : Type u₁} [Category.{v₁} 𝒟] (Φ : F.obj (.mk (.op Y)) ⥤ 𝒟)
  (Ψ : F.obj (.mk (.op V)) ⥤ 𝒟) (a : Φ ⟶ (F.map g.op.toLoc).toFunctor ⋙ Ψ)

include hs₁ hs₂ in
/-- **Base change through descent.** Let `N` be an object over `Y` which is recovered from its
canonical descent datum along `f` (the unit of
`CategoryTheory.Pseudofunctor.singletonDescentAdjunction` is invertible at `N`), and such that
`g^* N` is recovered from its canonical descent datum along the base change `P.p₂` of `f`. Let
`a : Φ ⟶ g^* ⋙ Ψ` be a natural transformation between functors preserving equalizers, such that
`a` followed by `Ψ` of the base-change `2`-cell of the square `(f, g)`, and of the square
`(X ×_Y X ⟶ Y, g)`, is invertible. Then `a` is invertible at `N`. -/
theorem isIso_app_of_isIso_descentUnit [HasEqualizers (F.obj (.mk (.op Y)))]
    [HasEqualizers (F.obj (.mk (.op V)))] [HasEqualizers 𝒟]
    [PreservesLimitsOfShape WalkingParallelPair Φ]
    [PreservesLimitsOfShape WalkingParallelPair Ψ]
    (hcol₁ : ∀ M, IsIso (a.app (R.obj M) ≫
      Ψ.map ((mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app M)))
    (hcol₂ : ∀ N, IsIso (a.app (T.obj N) ≫
      Ψ.map ((mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app N)))
    (N : F.obj (.mk (.op Y)))
    (hY : IsIso ((singletonDescentAdjunction F f XX af af₁).unit.app N))
    (hV : IsIso ((singletonDescentAdjunction F P.p₂ QQ aq aq₁).unit.app
      ((F.map g.op.toLoc).toFunctor.obj N))) :
    IsIso (a.app N) := by
  let D := (F.toDescentData (fun _ : Unit ↦ f)).obj N
  let D' := (singletonPullFunctor F f g P hw).obj D
  let r₁ := reconstructionFirst F f XX af af₁ D
  let r₂ := reconstructionSecond F f XX af af₁ D
  let r₁' := reconstructionFirst F P.p₂ QQ aq aq₁ D'
  let r₂' := reconstructionSecond F P.p₂ QQ aq aq₁ D'
  let E := equalizer r₁ r₂
  let E' := equalizer r₁' r₂'
  let u : N ⟶ E := (singletonDescentAdjunction F f XX af af₁).unit.app N
  have hu₀ : IsIso u := hY
  let N₀ := (F.map XX.p₁.op.toLoc).toFunctor.obj (D.obj ())
  let ε := (Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk hs₁).op.toLoc)).app (D.obj ())
  let β₀ : (F.map g.op.toLoc).toFunctor.obj (R.obj (D.obj ())) ⟶ Rq.obj (D'.obj ()) :=
    (mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app (D.obj ())
  let γ₀ : (F.map g.op.toLoc).toFunctor.obj (T.obj N₀) ⟶
      Tq.obj ((F.map QQ.p₁.op.toLoc).toFunctor.obj (D'.obj ())) :=
    (mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app N₀ ≫ Tq.map ε.hom
  have h₁ : (F.map g.op.toLoc).toFunctor.map r₁ ≫ γ₀ = β₀ ≫ r₁' :=
    reconstructionFirst_baseChange F f g P XX QQ hw j hj hs₁ af af₁ aq aq₁ D
  have h₂ : (F.map g.op.toLoc).toFunctor.map r₂ ≫ γ₀ = β₀ ≫ r₂' :=
    reconstructionSecond_baseChange F f g P XX QQ hw j hj hs₁ hs₂ af af₁ aq aq₁ D
  -- the comparison of the two reconstructions
  have hc : ((F.map g.op.toLoc).toFunctor.map (equalizer.ι r₁ r₂) ≫ β₀) ≫ r₁' =
      ((F.map g.op.toLoc).toFunctor.map (equalizer.ι r₁ r₂) ≫ β₀) ≫ r₂' := by
    rw [Category.assoc, Category.assoc, ← h₁, ← h₂, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, equalizer.condition]
  let c : (F.map g.op.toLoc).toFunctor.obj E ⟶ E' := equalizer.lift _ hc
  have hcι : c ≫ equalizer.ι r₁' r₂' =
      (F.map g.op.toLoc).toFunctor.map (equalizer.ι r₁ r₂) ≫ β₀ :=
    equalizer.lift_ι _ _
  -- the comparison is invertible: both reconstructions are identified with `g^* N`
  let e₀ := (singletonPullFunctorIso F f g P hw).app N
  have hu : u ≫ equalizer.ι r₁ r₂ = af.unit.app N :=
    (equalizer.lift_ι _ _).trans (af.homEquiv_id N)
  have hE : (singletonDescentAdjunction F P.p₂ QQ aq aq₁).homEquiv
      ((F.map g.op.toLoc).toFunctor.obj N) D' =
        reconstructionHomEquiv F P.p₂ QQ aq aq₁ D' ((F.map g.op.toLoc).toFunctor.obj N) := by
    simp only [singletonDescentAdjunction, Adjunction.adjunctionOfEquivRight]
    exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _
  have hx : (F.map g.op.toLoc).toFunctor.map u ≫ c =
      (singletonDescentAdjunction F P.p₂ QQ aq aq₁).homEquiv
        ((F.map g.op.toLoc).toFunctor.obj N) D' e₀.inv := by
    apply equalizer.hom_ext
    rw [Category.assoc, hcι, ← Functor.map_comp_assoc, hu, hE]
    refine (unit_mateEquiv af aq (commSqTwoSquare F hw) N).trans ?_
    refine Eq.trans ?_ (equalizer.lift_ι _ _).symm
    exact (aq.homEquiv_unit _ _ _).symm
  have hcIso : IsIso c := by
    have := hV
    have hiso : IsIso ((singletonDescentAdjunction F P.p₂ QQ aq aq₁).homEquiv
        ((F.map g.op.toLoc).toFunctor.obj N) D' e₀.inv) := by
      rw [Adjunction.homEquiv_unit]
      infer_instance
    rw [← hx] at hiso
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ ((F.map g.op.toLoc).toFunctor.map u) c
      (Functor.map_isIso _ u) hiso
  -- the two parallel pairs, and the maps between them
  have hM : IsIso (a.app (R.obj (D.obj ())) ≫ Ψ.map β₀) := hcol₁ _
  have hN : IsIso (a.app (T.obj N₀) ≫ Ψ.map γ₀) := by
    have h := hcol₂ N₀
    have heq : a.app (T.obj N₀) ≫ Ψ.map γ₀ = (a.app (T.obj N₀) ≫
        Ψ.map ((mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app N₀)) ≫
          Ψ.map (Tq.map ε.hom) := by
      simp only [γ₀, Functor.map_comp, Category.assoc]
      rfl
    rw [heq]
    exact IsIso.comp_isIso' h (Ψ.mapIso (Tq.mapIso ε)).isIso_hom
  let eM := asIso (a.app (R.obj (D.obj ())) ≫ Ψ.map β₀)
  let eN := asIso (a.app (T.obj N₀) ≫ Ψ.map γ₀)
  have hsq : ∀ (r : R.obj (D.obj ()) ⟶ T.obj N₀)
      (r' : Rq.obj (D'.obj ()) ⟶ Tq.obj ((F.map QQ.p₁.op.toLoc).toFunctor.obj (D'.obj ()))),
      (F.map g.op.toLoc).toFunctor.map r ≫ γ₀ = β₀ ≫ r' →
      Φ.map r ≫ eN.hom = eM.hom ≫ Ψ.map r' := by
    intro r r' hr
    simp only [eM, eN, asIso_hom, Category.assoc]
    rw [a.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp]
    rw [hr]
  let Θ := equalizerIsoOfCompatibleSquare Φ r₁ r₂ (Ψ.map r₁') (Ψ.map r₂') eM eN
      (hsq r₁ r₁' h₁) (hsq r₂ r₂' h₂) ≪≫ (PreservesEqualizer.iso Ψ r₁' r₂').symm
  have hmono : Mono (Ψ.map (equalizer.ι r₁' r₂')) := by
    have hι : Ψ.map (equalizer.ι r₁' r₂') = (PreservesEqualizer.iso Ψ r₁' r₂').hom ≫
        equalizer.ι (Ψ.map r₁') (Ψ.map r₂') := by
      rw [← PreservesEqualizer.iso_inv_ι Ψ r₁' r₂', Iso.hom_inv_id_assoc]
    rw [hι]
    infer_instance
  have hΘ : Θ.hom = a.app E ≫ Ψ.map c := by
    rw [← cancel_mono (Ψ.map (equalizer.ι r₁' r₂'))]
    simp only [Θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, PreservesEqualizer.iso_inv_ι]
    rw [equalizerIsoOfCompatibleSquare_hom_ι, ← Functor.map_comp, hcι, Functor.map_comp]
    exact a.naturality_assoc _ _
  have hE : IsIso (a.app E) := by
    have := hcIso
    have : IsIso (a.app E ≫ Ψ.map c) := by
      rw [← hΘ]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Ψ.map c)
  -- naturality of `a` along the unit
  have hnat : Φ.map u ≫ a.app E = a.app N ≫ ((F.map g.op.toLoc).toFunctor ⋙ Ψ).map u :=
    a.naturality u
  have : IsIso (a.app N ≫ ((F.map g.op.toLoc).toFunctor ⋙ Ψ).map u) := by
    rw [← hnat]
    exact IsIso.comp_isIso' inferInstance hE
  exact IsIso.of_isIso_comp_right _ (((F.map g.op.toLoc).toFunctor ⋙ Ψ).map u)

end Descent

end Pseudofunctor

end CategoryTheory

end
