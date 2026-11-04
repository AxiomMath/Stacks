module

public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Pushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentStackCartesian
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence

/-!
# Stacks 03YM, part 1: the fibres of the projection and condition (1)

This file contains the first steps of the proof of Stacks 03YM (assembled in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack`):

* the comparison isomorphisms of a pseudofunctor restricted along a functor, and descent data of
  such a restriction read over the images of chosen pullbacks (`imageDescentData`), over a
  variable functor and a variable pseudofunctor;
* the functor `rawProjection` written in terms of the `f`-map description of the hom-sets, its
  identification `rawProjection_eq_projection` with `Stacks.QCoh.projection`, and the
  identification `modulesToFiber` of its fibres with quasi-coherent modules (Stacks 04U3);
* the cartesian lifts `moduleCartesianMap` given by the units of the pullback–pushforward
  adjunction, and condition (1) of Stacks 026F, `isFibered_rawProjection`.

## References

* [Stacks Project, Tag 03YM](https://stacks.math.columbia.edu/tag/03YM)
* [Stacks Project, Tag 04U2](https://stacks.math.columbia.edu/tag/04U2)
* [Stacks Project, Tag 04U3](https://stacks.math.columbia.edu/tag/04U3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

/-! ### The pullback map of a pseudofunctor restricted along a functor -/

section Restriction

universe v₁ uu₁ v₂ uu₂ v₃ uu₃

variable {C : Type uu₁} [Category.{v₁} C] {D : Type uu₂} [Category.{v₂} D]
  (G : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v₃, uu₃})

open Opposite Bicategory

/-- The comparison isomorphism of the restriction of `F` along `G` for a factorisation `g ≫ f = fg`
in `C` is the comparison isomorphism of `F` for the image factorisation.

Read at a concrete `G` and `F` the two sides are definitionally equal, but deciding that requires
unfolding the composite pseudofunctor and `F`; the statement is therefore proved over a variable
functor and a variable pseudofunctor and used by instantiation. -/
private lemma toPseudofunctor_comp_mapComp' {X₀ X₁ X₂ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
    (fg : X₂ ⟶ X₀) (h : g ≫ f = fg) :
    (G.op.toPseudofunctor.comp F).mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h]) =
      F.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map fg).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← G.map_comp, h]) := by
  have h₁ : (G.map fg).op.toLoc = (G.map (g ≫ f)).op.toLoc := by rw [h]
  have h₂ : (G.map (g ≫ f)).op.toLoc = (G.map f).op.toLoc ≫ (G.map g).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← G.map_comp]
  have hB : (G.map fg).op.toLoc = (G.map f).op.toLoc ≫ (G.map g).op.toLoc := h₁.trans h₂
  apply Iso.ext
  -- The two structure 2-morphisms of `G.op.toPseudofunctor` are `eqToHom`s of the locally discrete
  -- bicategory `LocallyDiscrete Dᵒᵖ`, where any two parallel 2-morphisms agree.
  show F.map₂ (eqToHom h₁) ≫ F.map₂ (eqToHom h₂) ≫
      (F.mapComp (G.map f).op.toLoc (G.map g).op.toLoc).hom =
    F.map₂ (eqToHom hB) ≫ (F.mapComp (G.map f).op.toLoc (G.map g).op.toLoc).hom
  rw [F.map₂_eqToHom, F.map₂_eqToHom, F.map₂_eqToHom, ← Category.assoc, eqToHom_trans]

/-- The pullback map of the restriction of `F` along `G` along a morphism `g` of `C` is the
pullback map of `F` along the image of `g`. -/
private lemma toPseudofunctor_comp_pullHom
    {X₁ X₂ : C} {M₁ : F.obj (.mk (op (G.obj X₁)))} {M₂ : F.obj (.mk (op (G.obj X₂)))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map (G.map f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (G.map f₂).op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := G.op.toPseudofunctor.comp F)
        (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ g gf₁ gf₂ h₁ h₂ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (M₁ := M₁) (M₂ := M₂) φ
        (G.map g) (G.map gf₁) (G.map gf₂)
        (by rw [← G.map_comp, h₁]) (by rw [← G.map_comp, h₂]) := by
  show ((G.op.toPseudofunctor.comp F).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).hom.toNatTrans.app M₁ ≫
      (F.map (G.map g).op.toLoc).toFunctor.map φ ≫
      ((G.op.toPseudofunctor.comp F).mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).inv.toNatTrans.app M₂ = _
  rw [toPseudofunctor_comp_mapComp' G F f₁ g gf₁ h₁,
    toPseudofunctor_comp_mapComp' G F f₂ g gf₂ h₂]
  rfl

/-- A composite in a fibre of `F` of two morphisms between pullbacks along images of morphisms of
`C`, which agree with two morphisms of the corresponding fibre of the restriction of `F` along
`G`, is computed by the composite there.

The two fibres are definitionally the same category, but at a concrete `G` and `F` deciding that
unfolds `F` itself; stated over a variable functor and a variable pseudofunctor it is checked once,
and used by instantiation. -/
lemma toPseudofunctor_comp_comp {Y X₁ X₂ X₃ : C}
    {M₁ : F.obj (.mk (op (G.obj X₁)))} {M₂ : F.obj (.mk (op (G.obj X₂)))}
    {M₃ : F.obj (.mk (op (G.obj X₃)))} {a : Y ⟶ X₁} {b : Y ⟶ X₂} {c : Y ⟶ X₃}
    (φ' : (F.map (G.map a).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (G.map b).op.toLoc).toFunctor.obj M₂)
    (ψ' : (F.map (G.map b).op.toLoc).toFunctor.obj M₂ ⟶
      (F.map (G.map c).op.toLoc).toFunctor.obj M₃)
    (χ' : (F.map (G.map a).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (G.map c).op.toLoc).toFunctor.obj M₃)
    (φ : ((G.op.toPseudofunctor.comp F).map a.op.toLoc).toFunctor.obj M₁ ⟶
      ((G.op.toPseudofunctor.comp F).map b.op.toLoc).toFunctor.obj M₂)
    (ψ : ((G.op.toPseudofunctor.comp F).map b.op.toLoc).toFunctor.obj M₂ ⟶
      ((G.op.toPseudofunctor.comp F).map c.op.toLoc).toFunctor.obj M₃)
    (χ : ((G.op.toPseudofunctor.comp F).map a.op.toLoc).toFunctor.obj M₁ ⟶
      ((G.op.toPseudofunctor.comp F).map c.op.toLoc).toFunctor.obj M₃)
    (hφ : φ' = φ) (hψ : ψ' = ψ) (hχ : χ' = χ) (h : φ ≫ ψ = χ) : φ' ≫ ψ' = χ' := by
  subst hφ hψ hχ
  exact h

end Restriction

/-! ### Descent data restricted along a functor, read over images of chosen pullbacks

A descent datum of the restriction of `F` along `G`, for a family `f` in `C`, is read as a descent
datum of `F` for the image family, through chosen pullbacks of `C` whose images are pullbacks.
Everything here is stated over a variable functor and a variable pseudofunctor: at the concrete
functor and pseudofunctor of this file the identifications of the two fibres are definitional
but deciding them unfolds the pseudofunctor, so they are checked once here and used by
instantiation. -/

section ImageDescent

universe v₁ uu₁ v₂ uu₂ v₃ uu₃ w₀

variable {C : Type uu₁} [Category.{v₁} C] {D : Type uu₂} [Category.{v₂} D]
  (G : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v₃, uu₃})

open Opposite Limits

/-- The image of a chosen pullback under a functor, when the image square is a pullback. -/
private noncomputable def imageChosenPullback {A B T : C} {u : A ⟶ T} {v : B ⟶ T}
    (h : ChosenPullback u v)
    (hl : IsPullback (G.map h.p₁) (G.map h.p₂) (G.map u) (G.map v)) :
    ChosenPullback (G.map u) (G.map v) where
  pullback := G.obj h.pullback
  p₁ := G.map h.p₁
  p₂ := G.map h.p₂
  condition := hl.w
  isLimit := hl.isLimit
  p := G.map h.p
  hp₁ := by rw [← G.map_comp, h.hp₁]

/-- The image of a chosen threefold pullback, built from the image of a chosen pullback of the two
chosen pairwise pullbacks over the middle object. -/
private noncomputable def imageChosenPullback₃ {X₁ X₂ X₃ T : C}
    {u₁ : X₁ ⟶ T} {u₂ : X₂ ⟶ T} {u₃ : X₃ ⟶ T}
    {h₁₂ : ChosenPullback u₁ u₂} {h₂₃ : ChosenPullback u₂ u₃} {h₁₃ : ChosenPullback u₁ u₃}
    (l₁₂ : IsPullback (G.map h₁₂.p₁) (G.map h₁₂.p₂) (G.map u₁) (G.map u₂))
    (l₂₃ : IsPullback (G.map h₂₃.p₁) (G.map h₂₃.p₂) (G.map u₂) (G.map u₃))
    (l₁₃ : IsPullback (G.map h₁₃.p₁) (G.map h₁₃.p₂) (G.map u₁) (G.map u₃))
    (h : ChosenPullback h₁₂.p₂ h₂₃.p₁)
    (l : IsPullback (G.map h.p₁) (G.map h.p₂) (G.map h₁₂.p₂) (G.map h₂₃.p₁)) :
    ChosenPullback₃ (imageChosenPullback G h₁₂ l₁₂) (imageChosenPullback G h₂₃ l₂₃)
      (imageChosenPullback G h₁₃ l₁₃) where
  chosenPullback := imageChosenPullback G h l
  l :=
    { f := G.map (h₁₃.isPullback.lift (h.p₁ ≫ h₁₂.p₁) (h.p₂ ≫ h₂₃.p₂) (by
        rw [Category.assoc, h₁₂.condition, ← Category.assoc, h.condition, Category.assoc,
          h₂₃.condition, Category.assoc]))
      f_p₁ := by
        change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp, ← G.map_comp, IsPullback.lift_fst]
      f_p₂ := by
        change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp, ← G.map_comp, IsPullback.lift_snd]
      f_p := by
        change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp, ← G.map_comp, ← h₁₃.hp₁, IsPullback.lift_fst_assoc, Category.assoc,
          h₁₂.hp₁] }

omit [Category.{v₂} D] in
/-- The compatibility condition of `CategoryTheory.Pseudofunctor.DescentData.isoMk` for the
identifications of two descent data with equal components and equal gluing morphisms. -/
private lemma descentData_comm_of_eq {F' : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₃, uu₃}}
    {X₁ X₂ Y : C} {M₁ M₁' : F'.obj (.mk (op X₁))} {M₂ M₂' : F'.obj (.mk (op X₂))}
    (e₁ : M₁ = M₁') (e₂ : M₂ = M₂') {a : Y ⟶ X₁} {b : Y ⟶ X₂}
    (φ : (F'.map a.op.toLoc).toFunctor.obj M₁' ⟶ (F'.map b.op.toLoc).toFunctor.obj M₂')
    (ψ : (F'.map a.op.toLoc).toFunctor.obj M₁ ⟶ (F'.map b.op.toLoc).toFunctor.obj M₂)
    (h : ψ ≍ φ) :
    (F'.map a.op.toLoc).toFunctor.map (eqToIso e₁).hom ≫ φ =
      ψ ≫ (F'.map b.op.toLoc).toFunctor.map (eqToIso e₂).hom := by
  subst e₁ e₂
  obtain rfl := eq_of_heq h
  simp

variable {ι : Type w₀} {U : C} {X : ι → C} {f : ∀ i, X i ⟶ U}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (hsq : ∀ i j, IsPullback (G.map (sq i j).p₁) (G.map (sq i j).p₂) (G.map (f i)) (G.map (f j)))
  (sq₂ : ∀ i j k, ChosenPullback (sq i j).p₂ (sq j k).p₁)
  (hsq₂ : ∀ i j k, IsPullback (G.map (sq₂ i j k).p₁) (G.map (sq₂ i j k).p₂)
    (G.map (sq i j).p₂) (G.map (sq j k).p₁))
  (Dd : (G.op.toPseudofunctor.comp F).DescentData f)

/-- The gluing morphisms of a descent datum of the restriction, over the image chosen pullbacks. -/
private def imageHom (i j : ι) :
    (F.map (imageChosenPullback G (sq i j) (hsq i j)).p₁.op.toLoc).toFunctor.obj (Dd.obj i) ⟶
      (F.map (imageChosenPullback G (sq i j) (hsq i j)).p₂.op.toLoc).toFunctor.obj (Dd.obj j) :=
  Dd.hom (sq i j).p (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂

/-- The pullback map of `imageHom` at the images of a pair of morphisms into two members of the
family is the datum's own gluing morphism. -/
private lemma pullHom'_imageHom {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd) (G.map q) (G.map a) (G.map b)
        (by rw [← G.map_comp, ha]) (by rw [← G.map_comp, hb]) =
      Dd.hom q a b ha hb := by
  let P := sq i j
  let p := P.isPullback.lift a b (ha.trans hb.symm)
  have hp₁ : p ≫ P.p₁ = a := P.isPullback.lift_fst _ _ _
  have hp₂ : p ≫ P.p₂ = b := P.isPullback.lift_snd _ _ _
  have hp : p ≫ P.p = q := by rw [← P.hp₁, ← Category.assoc, hp₁, ha]
  refine (Pseudofunctor.DescentData'.pullHom'_eq_pullHom (F := F)
    (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
    (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
    _ _ _ _ (G.map p) (by rw [← G.map_comp, ha]) (by rw [← G.map_comp, hb])
    ((G.map_comp _ _).symm.trans (congrArg G.map hp₁))
    ((G.map_comp _ _).symm.trans (congrArg G.map hp₂))).trans ?_
  refine (toPseudofunctor_comp_pullHom G F (M₁ := Dd.obj i) (M₂ := Dd.obj j) (f₁ := P.p₁)
    (f₂ := P.p₂) (Dd.hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂) p a b hp₁ hp₂).symm.trans ?_
  exact Dd.pullHom_hom p P.p q hp P.p₁ P.p₂ P.hp₁ P.hp₂ a b hp₁ hp₂

/-- The normalisation condition of `CategoryTheory.Pseudofunctor.DescentData'` for `imageHom`, at
any morphism equal to the image of the identity. -/
private lemma imageHom_self_of_eq (i : ι) {a' : G.obj (X i) ⟶ G.obj (X i)}
    (ha' : G.map (𝟙 (X i)) = a') (h : a' ≫ G.map (f i) = G.map (f i)) :
    Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd) (G.map (f i)) a' a' h h = 𝟙 _ := by
  subst ha'
  exact (pullHom'_imageHom G F sq hsq Dd (f i) (𝟙 _) (𝟙 _) (Category.id_comp _)
    (Category.id_comp _)).trans (Dd.hom_self (f i) (𝟙 _) (Category.id_comp _))

/-- The cocycle condition for `imageHom` at the images of three morphisms into members of the
family, read at any morphisms equal to those images. -/
private lemma imageHom_comp_of_eq {Y : C} (q : Y ⟶ U) {i j k : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (c : Y ⟶ X k) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q)
    {Z : D} (hZ : G.obj Y = Z) {q' : Z ⟶ G.obj U} {a' : Z ⟶ G.obj (X i)}
    {b' : Z ⟶ G.obj (X j)} {c' : Z ⟶ G.obj (X k)}
    (hq : G.map q ≍ q') (ha' : G.map a ≍ a') (hb' : G.map b ≍ b') (hc' : G.map c ≍ c')
    (h₁ : a' ≫ G.map (f i) = q') (h₂ : b' ≫ G.map (f j) = q') (h₃ : c' ≫ G.map (f k) = q') :
    Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd) q' a' b' h₁ h₂ ≫
      Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd) q' b' c' h₂ h₃ =
      Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd) q' a' c' h₁ h₃ := by
  subst hZ
  obtain rfl := eq_of_heq hq
  obtain rfl := eq_of_heq ha'
  obtain rfl := eq_of_heq hb'
  obtain rfl := eq_of_heq hc'
  exact toPseudofunctor_comp_comp G F _ _ _ _ _ _
    (pullHom'_imageHom G F sq hsq Dd q a b ha hb)
    (pullHom'_imageHom G F sq hsq Dd q b c hb hc)
    (pullHom'_imageHom G F sq hsq Dd q a c ha hc)
    (Dd.hom_comp _ _ _ _ ha hb hc)

/-- The cocycle condition of `CategoryTheory.Pseudofunctor.DescentData'` for `imageHom`. -/
private lemma imageHom_comp (i j k : ι) :
    Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd)
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p₁
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p₂ ≫
      Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd)
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p₂
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p₃ =
      Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
        (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
        (imageHom G F sq hsq Dd)
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p₁
        (imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k) (hsq₂ i j k)).p₃ :=
  imageHom_comp_of_eq G F sq hsq Dd ((sq₂ i j k).p₁ ≫ (sq i j).p) ((sq₂ i j k).p₁ ≫ (sq i j).p₁)
    (sq₂ i j k).p ((sq₂ i j k).p₂ ≫ (sq j k).p₂) (by rw [Category.assoc, (sq i j).hp₁])
    (by rw [← (sq₂ i j k).hp₁, Category.assoc, (sq i j).hp₂])
    (by rw [Category.assoc, (sq j k).hp₂, ← (sq j k).hp₁, ← Category.assoc, ← (sq₂ i j k).condition,
      Category.assoc, (sq i j).hp₂])
    rfl (heq_of_eq (G.map_comp _ _)) (heq_of_eq (G.map_comp _ _)) HEq.rfl
    (heq_of_eq (G.map_comp _ _)) _ _ _

/-- A descent datum of the restriction of `F` along `G` for the family `f`, read as a descent datum
of `F` for the image family: its gluing morphisms are the pullback maps of `imageHom`. -/
private noncomputable def imageDescentData : F.DescentData (fun i => G.map (f i)) where
  obj i := Dd.obj i
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := Pseudofunctor.DescentData'.pullHom' (F := F)
    (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
    (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
    (imageHom G F sq hsq Dd) q f₁ f₂ hf₁ hf₂
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    Pseudofunctor.DescentData'.pullHom_pullHom' (F := F)
      (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
      (obj := fun i => Dd.obj i) (obj' := fun i => Dd.obj i)
      (imageHom G F sq hsq Dd) g q q' f₁ f₂ gf₁ gf₂ hq hf₁ hf₂ hgf₁ hgf₂
  hom_self _ q _ g hg := Pseudofunctor.DescentData'.pullHom'_self' (F := F)
    (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
    (obj := fun i => Dd.obj i) (imageHom G F sq hsq Dd)
    (fun i => imageHom_self_of_eq G F sq hsq Dd i (G.map_id _) _) q g hg
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := Pseudofunctor.DescentData'.comp_pullHom'' (F := F)
    (sq := fun i j => imageChosenPullback G (sq i j) (hsq i j))
    (obj := fun i => Dd.obj i) (imageHom G F sq hsq Dd)
    (sq₃ := fun i j k => imageChosenPullback₃ G (hsq i j) (hsq j k) (hsq i k) (sq₂ i j k)
      (hsq₂ i j k))
    (imageHom_comp G F sq hsq sq₂ hsq₂ Dd) q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- The gluing morphisms of `imageDescentData` at images of morphisms of `C` are those of the
datum. -/
private lemma imageDescentData_hom {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (imageDescentData G F sq hsq sq₂ hsq₂ Dd).hom (G.map q) (G.map a) (G.map b)
        (by rw [← G.map_comp, ha]) (by rw [← G.map_comp, hb]) =
      Dd.hom q a b ha hb :=
  pullHom'_imageHom G F sq hsq Dd q a b ha hb

end ImageDescent

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The fibre of the projection over an object of the site -/

/-- The category data of Stacks 04U2 underlying `AlgebraicGeometry.qcohProjection`, chosen once. -/
private noncomputable abbrev catData : AlgebraicGeometry.QCohCategoryData B S hS :=
  Classical.choice AlgebraicGeometry.exists_qcohCategoryData

/-- The identification of a hom-set of `AlgebraicGeometry.QCohObject` with the `Σ`-type of
Stacks 04U2. -/
private noncomputable abbrev rawHom (A C : AlgebraicGeometry.QCohObject B S hS) :=
  Equiv.cast (catData.hom_type A C)

/-- The projection from quasi-coherent modules on the big fppf site over `S` to that site, written
directly in terms of the `f`-map description of its hom-sets.

The `IsHomLift` instance arguments of the fibre API are found by unfolding this definition, which
is why it is `instance_reducible`. -/
@[instance_reducible]
private noncomputable def rawProjection :
    AlgebraicGeometry.QCohObject B S hS ⥤ AlgebraicGeometry.BigFppfOver B S hS where
  obj A := A.base
  map {A C} m := (rawHom A C m).1
  map_id A := by
    change (Equiv.cast (catData.hom_type A A) (𝟙 A)).1 = _
    rw [catData.identity]
    rfl
  map_comp {A C D} m n := by
    change (Equiv.cast (catData.hom_type A D) (m ≫ n)).1 = _
    rw [catData.composition]
    rfl

/-- `rawProjection` is `Stacks.QCoh.projection`.

(`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Fibred.lean` carries a private functor of the
same name and description for its own argument; the two files do not import one another's private
declarations, and the one here is stated over `AlgebraicGeometry.QCohObject`.) -/
private lemma rawProjection_eq_projection :
    rawProjection = projection (B := B) (S := S) (hS := hS) := by
  symm
  exact CategoryTheory.Functor.ext catData.projection_obj (fun A C m => catData.projection_map m)

/-- Quasi-coherence, as a property of the objects of `AlgebraicGeometry.Scheme.Modules`.

The declared type is `ObjectProperty T.Modules` and not the body's own
`ObjectProperty (SheafOfModules T.ringCatSheaf)`: the two agree only after `TopCat.Sheaf` unfolds,
and only the first is type-correct at the transparency used for implicit arguments. -/
private abbrev qcohProp (T : Scheme.{u}) : ObjectProperty T.Modules :=
  SheafOfModules.isQuasicoherent T.ringCatSheaf

/-- The forgetful functor from the big fppf site over `S` to schemes. -/
private abbrev schemeFunctor := AlgebraicGeometry.BigFppfOver.toScheme B S hS

/-- The quasi-coherent modules on the scheme underlying an object of the big fppf site over `S`. -/
private abbrev modulesOn (U : AlgebraicGeometry.BigFppfOver B S hS) :=
  (qcohProp (schemeFunctor.obj U)).FullSubcategory

/-- A quasi-coherent module on the scheme underlying `U`, read as an object of the fibre of
`rawProjection` over `U`. -/
private abbrev ofModule {U : AlgebraicGeometry.BigFppfOver B S hS} (M : modulesOn U) :
    rawProjection.Fiber U := ⟨⟨U, M.obj, M.property⟩, rfl⟩

/-- A morphism of quasi-coherent modules on `U`, read as a morphism of the fibre of `rawProjection`
over `U`; the direction is reversed, the fibre being the opposite category. -/
private noncomputable def ofModuleMap {U : AlgebraicGeometry.BigFppfOver B S hS}
    {M N : modulesOn U} (φ : N ⟶ M) : ofModule M ⟶ ofModule N := by
  let k : (ofModule M).1 ⟶ (ofModule N).1 := (rawHom _ _).symm
    ⟨𝟙 U, φ.hom ≫ (FMap.id (ofModule M).1).2⟩
  refine ⟨k, ?_⟩
  have hk : rawProjection.map k = 𝟙 U := by
    change (rawHom _ _ ((rawHom _ _).symm _)).1 = _
    simp only [Equiv.apply_symm_apply]
  rw [← hk]
  infer_instance

/-- Two morphisms of the fibre between modules are equal when their `f`-map descriptions are. -/
private lemma ofModule_hom_ext {U : AlgebraicGeometry.BigFppfOver B S hS} {M N : modulesOn U}
    {k l : ofModule M ⟶ ofModule N} (h : rawHom _ _ k.val = rawHom _ _ l.val) : k = l :=
  Subtype.ext ((rawHom _ _).injective h)

/-- The `f`-map description of `ofModuleMap φ`. -/
private lemma rawHom_ofModuleMap {U : AlgebraicGeometry.BigFppfOver B S hS} {M N : modulesOn U}
    (φ : N ⟶ M) :
    rawHom _ _ (ofModuleMap φ).val = ⟨𝟙 U, φ.hom ≫ (FMap.id (ofModule M).1).2⟩ :=
  Equiv.apply_symm_apply _ _

private lemma ofModuleMap_id {U : AlgebraicGeometry.BigFppfOver B S hS} (M : modulesOn U) :
    ofModuleMap (𝟙 M) = 𝟙 (ofModule M) := by
  apply ofModule_hom_ext
  rw [rawHom_ofModuleMap]
  show _ = Equiv.cast (catData.hom_type _ _) (𝟙 _)
  rw [catData.identity]
  exact Sigma.ext rfl (heq_of_eq (Category.id_comp _))

/-- Pushing a module forward along the identity returns it. -/
private noncomputable def identityIso {U : AlgebraicGeometry.BigFppfOver B S hS}
    (M : modulesOn U) :
    M.obj ≅ (Scheme.Modules.pushforward (schemeFunctor.map (𝟙 U))).obj M.obj :=
  (Scheme.Modules.pushforwardId _).symm.app M.obj ≪≫
    (Scheme.Modules.pushforwardCongr (by simp)).symm.app M.obj

private lemma ofModuleMap_comp {U : AlgebraicGeometry.BigFppfOver B S hS}
    {M N P : modulesOn U} (φ : N ⟶ M) (ψ : P ⟶ N) :
    ofModuleMap (ψ ≫ φ) = ofModuleMap φ ≫ ofModuleMap ψ := by
  apply ofModule_hom_ext
  rw [rawHom_ofModuleMap]
  show _ = Equiv.cast (catData.hom_type _ _) (_ ≫ _)
  rw [catData.composition]
  show _ = FMap.comp (rawHom _ _ (ofModuleMap φ).val) (rawHom _ _ (ofModuleMap ψ).val)
  rw [rawHom_ofModuleMap φ, rawHom_ofModuleMap ψ]
  refine Sigma.ext (Category.id_comp _).symm (heq_of_eq ?_)
  dsimp only [FMap.comp, FMap.id]
  -- The three coherence maps of `QCohHom.comp` and `QCohHom.id` are each an `eqToHom`, so the
  -- whole computation collapses by `eqToHom_trans`; what is left over is the transport of the
  -- two component maps past those `eqToHom`s.
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    Stacks.Modules.pushforwardId_inv_app,
    Stacks.Modules.pushforwardComp_hom_app,
    Stacks.Modules.pushforwardCongr_inv_app, Stacks.Modules.pushforward_id_eq,
    CategoryTheory.Functor.map_comp, eqToHom_refl, Category.assoc]
  cat_disch

private lemma ofModuleMap_bijective {U : AlgebraicGeometry.BigFppfOver B S hS}
    (M N : modulesOn U) : Function.Bijective (ofModuleMap (M := M) (N := N)) := by
  constructor
  · intro φ ψ h
    have h' := congrArg (fun m : ofModule M ⟶ ofModule N => rawHom _ _ m.val) h
    rw [rawHom_ofModuleMap φ, rawHom_ofModuleMap ψ, Sigma.mk.inj_iff] at h'
    simp only [heq_eq_eq, true_and] at h'
    have h'' : φ.hom ≫ (identityIso M).hom = ψ.hom ≫ (identityIso M).hom := h'
    exact ObjectProperty.hom_ext _ ((cancel_mono (identityIso M).hom).mp h'')
  · intro m
    let := m.2
    have hm : (rawHom _ _ m.val).1 = 𝟙 U :=
      (IsHomLift.eq_of_isHomLift rawProjection (a := (ofModule M).val)
        (b := (ofModule N).val) (𝟙 U) m.val).symm
    generalize he : rawHom _ _ m.val = q at hm
    obtain ⟨g, k⟩ := q
    dsimp at hm
    subst g
    refine ⟨ObjectProperty.homMk (k ≫ (identityIso M).inv), ?_⟩
    apply ofModule_hom_ext
    rw [rawHom_ofModuleMap, he]
    congr 1
    show (k ≫ (identityIso M).inv) ≫ (identityIso M).hom = k
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Stacks 04U3** in the form needed here: the comparison of the opposite of the category of
quasi-coherent modules on the scheme underlying `U` with the fibre of `rawProjection` over `U`. -/
private noncomputable def modulesToFiber (U : AlgebraicGeometry.BigFppfOver B S hS) :
    (modulesOn U)ᵒᵖ ⥤ rawProjection.Fiber U where
  obj M := ofModule M.unop
  map φ := ofModuleMap φ.unop
  map_id M := ofModuleMap_id M.unop
  map_comp φ ψ := ofModuleMap_comp φ.unop ψ.unop

private lemma modulesToFiber_isEquivalence (U : AlgebraicGeometry.BigFppfOver B S hS) :
    (modulesToFiber U).IsEquivalence := by
  have hf : (modulesToFiber U).Full := ⟨fun {M N} φ => by
    obtain ⟨ψ, hψ⟩ := (ofModuleMap_bijective M.unop N.unop).surjective φ
    exact ⟨ψ.op, hψ⟩⟩
  have hi : (modulesToFiber U).Faithful := ⟨fun {M N} φ ψ h =>
    Quiver.Hom.unop_inj ((ofModuleMap_bijective M.unop N.unop).injective h)⟩
  have he : (modulesToFiber U).EssSurj := ⟨by
    rintro ⟨⟨V, M, hM⟩, hx⟩
    change V = U at hx
    subst U
    exact ⟨Opposite.op ⟨M, hM⟩, ⟨Iso.refl _⟩⟩⟩
  exact {}

/-! ### Cartesian lifts and condition (1) -/

/-- The pullback of a quasi-coherent module is quasi-coherent, stated with `qcohProp` as its
conclusion.  Supplied inline to `ObjectProperty.lift` below the proof would be stored with the
conclusion `(RingedSpaceModuleAdjunction.modulePullback _).obj M.obj |>.IsQuasicoherent`, which is
the spelling that is not type-correct at the transparency used for implicit arguments; naming it
here fixes the conclusion once. -/
private lemma qcohProp_pullback {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U)
    (M : modulesOn U) :
    qcohProp (schemeFunctor.obj V)
      (((qcohProp (schemeFunctor.obj U)).ι ⋙
        Scheme.Modules.pullback (schemeFunctor.map f)).obj M) :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    (schemeFunctor.map f).toLRSHom.toShHom M.obj M.property

/-- Pullback of quasi-coherent modules along a morphism of the big fppf site over `S`. -/
private noncomputable def modulePullback {U V : AlgebraicGeometry.BigFppfOver B S hS}
    (f : V ⟶ U) : modulesOn U ⥤ modulesOn V :=
  ObjectProperty.lift _ ((qcohProp (schemeFunctor.obj U)).ι ⋙
    Scheme.Modules.pullback (schemeFunctor.map f)) (qcohProp_pullback f)

/-- The unit of the pullback–pushforward adjunction, read as an `f`-map of quasi-coherent modules
and hence as a morphism of `AlgebraicGeometry.QCohObject`. -/
private noncomputable def moduleCartesianMap {U V : AlgebraicGeometry.BigFppfOver B S hS}
    (f : V ⟶ U) (M : modulesOn U) :
    (ofModule ((modulePullback f).obj M)).val ⟶ (ofModule M).val :=
  (rawHom _ _).symm ⟨f, (Scheme.Modules.pullbackPushforwardAdjunction
    (schemeFunctor.map f)).unit.app M.obj⟩

private lemma moduleCartesianMap_isStronglyCartesian
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : V ⟶ U) (M : modulesOn U) :
    rawProjection.IsStronglyCartesian f (moduleCartesianMap f M) := by
  let m := moduleCartesianMap f M
  have h : AlgebraicGeometry.qcohProjection.IsStronglyCartesian
      (AlgebraicGeometry.qcohProjection.map m) m := by
    rw [AlgebraicGeometry.qcohHom_isStronglyCartesian_iff]
    have hm : AlgebraicGeometry.qcohHomEquivPullbackHom _ _ m =
        ⟨f, 𝟙 ((Scheme.Modules.pullback (schemeFunctor.map f)).obj M.obj)⟩ := by
      show (Equiv.sigmaCongrRight (fun g : V ⟶ U =>
        (Scheme.Modules.pullbackPushforwardAdjunction (schemeFunctor.map g)).homEquiv
          M.obj ((modulePullback f).obj M).obj |>.symm)
        (rawHom (ofModule ((modulePullback f).obj M)).val (ofModule M).val m)) = _
      dsimp only [m, moduleCartesianMap]
      rw [Equiv.apply_symm_apply]
      show (⟨f, (Scheme.Modules.pullbackPushforwardAdjunction (schemeFunctor.map f)).homEquiv _ _
        |>.symm
          ((Scheme.Modules.pullbackPushforwardAdjunction (schemeFunctor.map f)).unit.app M.obj)⟩ :
        Σ g : V ⟶ U, (Scheme.Modules.pullback (schemeFunctor.map g)).obj M.obj ⟶ _) = _
      -- `Adjunction.homEquiv_symm_unit` is instantiated at the spelling the goal uses before being
      -- rewritten with: its statement is `dsimp%`-normalised, so the functor in the second
      -- argument of `homEquiv` is a separate variable there and a keyed rewrite would have to
      -- unfold `Scheme.Modules.pullbackPushforwardAdjunction` to tie it to the adjunction.
      have hunit : ((Scheme.Modules.pullbackPushforwardAdjunction
            (schemeFunctor.map f)).homEquiv M.obj
            ((Scheme.Modules.pullback (schemeFunctor.map f)).obj M.obj)).symm
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (schemeFunctor.map f)).unit.app M.obj) =
          𝟙 ((Scheme.Modules.pullback (schemeFunctor.map f)).obj M.obj) :=
        Adjunction.homEquiv_symm_unit _ M.obj
      exact Sigma.ext rfl (heq_of_eq hunit)
    rw [hm]
    -- The goal is `IsIso ⟨f, 𝟙 _⟩.snd`; instance search does not reduce the projection of an
    -- explicit pair, so the identity instance is supplied directly.
    exact IsIso.id _
  have h' : rawProjection.IsStronglyCartesian (rawProjection.map m) m :=
    (congrArg (fun p : AlgebraicGeometry.QCohObject B S hS ⥤ AlgebraicGeometry.BigFppfOver B S hS =>
      p.IsStronglyCartesian (p.map m) m) rawProjection_eq_projection.symm).mp h
  simpa only [rawProjection, m, moduleCartesianMap, Equiv.apply_symm_apply] using h'

/-- Condition (1) of Stacks 026F for `rawProjection`: it is a fibred category.  The form stated
for `Stacks.QCoh.projection` is `Stacks.QCoh.projection_isFibered`. -/
private lemma isFibered_rawProjection :
    Functor.IsFibered (rawProjection (B := B) (S := S) (hS := hS)) := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  rintro ⟨U, M, hM⟩ V f
  exact ⟨_, moduleCartesianMap f ⟨M, hM⟩, moduleCartesianMap_isStronglyCartesian f ⟨M, hM⟩⟩

end Stacks.QCoh

end
