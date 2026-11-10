module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChangeMap

/-!
# The pullback maps of a cube of cartesian squares

Consider a commutative square of a big étale site
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
```
with a diagonal `h : X' ⟶ Y`, and its base change along `b : Y₁ ⟶ Y`: cartesian squares
`X₁ = X ×_Y Y₁`, `Y'₁ = Y' ×_Y Y₁`, `X'₁ = X' ×_{Y'} Y'₁` and the induced `k₁ : X'₁ ⟶ X₁`, so
that `X'₁ = X' ×_X X₁` as well. Each of the four vertical faces of the resulting cube is a
cartesian square and so carries the pullback map `g⁻¹f_* ⟶ f'_*p⁻¹` of Sites, Section 06UM
(`AlgebraicGeometry.SmallEtale.directImageBaseChange`). This file proves that these pullback
maps are compatible with stacking: the two composites
```
b⁻¹ l_* f'_* = b⁻¹ f_* k_* ⟶ f₁_* a⁻¹ k_* ⟶ f₁_* k₁_* a'⁻¹
b⁻¹ l_* f'_* ⟶ l₁_* b'⁻¹ f'_* ⟶ l₁_* f'₁_* a'⁻¹ = f₁_* k₁_* a'⁻¹
```
agree, both being the pullback map of the base change of `h` by `b` (Sites, Remarks 0F6X and
0F6Y). This is the identity on which the proof of [Stacks, Tag 0F7F] rests.

## Main definitions

* `AlgebraicGeometry.SmallEtale.pushforwardFactoredCompIso`: the comparison `a_* ⋙ b_* ≅ h_*`
  for a factorization `a ≫ b = h`.
* `AlgebraicGeometry.SmallEtale.pushforwardSquareIso`: the comparison `f'_* ⋙ l_* ≅ k_* ⋙ f_*`
  of a commutative square, through a diagonal.

## Main results

* `AlgebraicGeometry.SmallEtale.pullbackSectionAlongHom_directImageBaseChange`: the pullback
  map, evaluated on a pulled-back section, is a pulled-back section.
* `AlgebraicGeometry.SmallEtale.directImageBaseChange_cube`: the compatibility above.

## References

* [Stacks Project, Tag 0F7F](https://stacks.math.columbia.edu/tag/0F7F)
* [Stacks Project, Tag 0F6X](https://stacks.math.columbia.edu/tag/0F6X)
* [Stacks Project, Tag 0F6Y](https://stacks.math.columbia.edu/tag/0F6Y)
* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})

section Arrows

/-- The projection of an étale base change to the test object, under its two names. -/
lemma fiberProjection_eq_baseChangeObjProjection {X Y : B.Scheme} (f : X ⟶ Y)
    (V : SmallEtale B Y.obj Y.property) :
    fiberProjection B f V = baseChangeObjProjection B f V :=
  rfl

/-- Two morphisms into the iterated étale base change `(V ×_Y Y') ×_{Y'} X'` agreeing after the
projections to `V` and to `X'` are equal. -/
lemma baseChange_baseChange_hom_ext {X' Y' Y : B.Scheme} (f' : X' ⟶ Y') (l : Y' ⟶ Y)
    (V : SmallEtale B Y.obj Y.property) {T : B.Scheme}
    {x y : T ⟶ (baseChange B f' (baseChange B l V)).obj.left}
    (h₁ : x ≫ fiberProjection B f' (baseChange B l V) ≫ fiberProjection B l V =
      y ≫ fiberProjection B f' (baseChange B l V) ≫ fiberProjection B l V)
    (h₂ : x ≫ (baseChange B f' (baseChange B l V)).obj.hom =
      y ≫ (baseChange B f' (baseChange B l V)).obj.hom) : x = y := by
  refine (isPullback_fiberProjection B f' (baseChange B l V)).hom_ext ?_ h₂
  refine (isPullback_fiberProjection B l V).hom_ext ?_ ?_
  · simpa only [Category.assoc] using h₁
  · simp only [Category.assoc, (isPullback_fiberProjection B f' (baseChange B l V)).w]
    simp only [← Category.assoc, h₂]

/-- The inverse of the factored composition comparison of étale base changes, followed by the
two projections, is the projection of the base change along the composite. -/
@[reassoc]
lemma smallEtaleBaseChange_factoredCompIso_inv_app_fst {X Y Z : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) (W : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv.app W).hom.left ≫
        fiberProjection B f (baseChange B g W) ≫ fiberProjection B g W =
      fiberProjection B fg W := by
  have h : ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app W).hom.left ≫
      fiberProjection B fg W =
        fiberProjection B f (baseChange B g W) ≫ fiberProjection B g W :=
    smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z f g fg hfg W
  have hi : ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv.app W).hom.left ≫
      ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app W).hom.left = 𝟙 _ :=
    congrArg (fun φ => φ.hom.left)
      ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv_hom_id_app W)
  rw [← h, ← Category.assoc, hi, Category.id_comp]

/-- The factored composition comparison of étale base changes, followed by the projection of the
base change along the composite, is the composite of the two projections. -/
@[reassoc]
lemma smallEtaleBaseChange_factoredCompIso_hom_app_fiberProjection {X Y Z : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) (W : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app W).hom.left ≫
        fiberProjection B fg W =
      fiberProjection B f (baseChange B g W) ≫ fiberProjection B g W :=
  smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z f g fg hfg W

/-- The projection of the étale base change is natural in the test object. -/
@[reassoc]
lemma smallEtaleBaseChange_map_fiberProjection {X X' : B.Scheme} (p : X' ⟶ X)
    {W₁ W : SmallEtale B X.obj X.property} (i : W₁ ⟶ W) :
    ((smallEtaleBaseChange B p).map i).hom.left ≫ fiberProjection B p W =
      fiberProjection B p W₁ ≫ i.hom.left :=
  baseChangeObjProjection_naturality B p i

section SquareArrow

variable {X' X Y' Y : B.Scheme} (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
  (h : X' ⟶ Y) (hk : k ≫ f = h) (hl : f' ≫ l = h)

/-- For a commutative square `k ≫ f = f' ≫ l` with diagonal `h`, the comparison
`(V ×_Y X) ×_X X' ≅ V ×_Y X' ≅ (V ×_Y Y') ×_{Y'} X'` of the two iterated étale base changes of a
test object `V` of `Y`. -/
def squareBaseChangeArrow (V : SmallEtale B Y.obj Y.property) :
    baseChange B k (baseChange B f V) ⟶ baseChange B f' (baseChange B l V) :=
  (smallEtaleBaseChange_factoredCompIso B X' X Y k f h hk).hom.app V ≫
    (smallEtaleBaseChange_factoredCompIso B X' Y' Y f' l h hl).inv.app V

/-- The comparison of the two iterated base changes lies over the projection to `V`. -/
@[reassoc]
lemma squareBaseChangeArrow_fiberProjection (V : SmallEtale B Y.obj Y.property) :
    (squareBaseChangeArrow B k f' f l h hk hl V).hom.left ≫
        fiberProjection B f' (baseChange B l V) ≫ fiberProjection B l V =
      fiberProjection B k (baseChange B f V) ≫ fiberProjection B f V := by
  have h₁ := smallEtaleBaseChange_factoredCompIso_inv_app_fst B f' l h hl V
  have h₂ := smallEtaleBaseChange_factoredCompIso_hom_app_fiberProjection B k f h hk V
  simp only [squareBaseChangeArrow, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
    Category.assoc]
  rw [h₁, h₂]

/-- The comparison of the two iterated base changes lies over `X'`. -/
@[reassoc]
lemma squareBaseChangeArrow_hom (V : SmallEtale B Y.obj Y.property) :
    (squareBaseChangeArrow B k f' f l h hk hl V).hom.left ≫
        (baseChange B f' (baseChange B l V)).obj.hom =
      (baseChange B k (baseChange B f V)).obj.hom :=
  Over.w (squareBaseChangeArrow B k f' f l h hk hl V).hom

end SquareArrow

variable {X Y X' Y' : B.Scheme} (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (sq : IsPullback p f' f g)

/-- The comparison arrow of a cartesian square, followed by the projection, is the comparison of
the two étale base changes. -/
@[reassoc]
lemma fiberBaseChangeArrow_fiberProjection (V : SmallEtale B Y.obj Y.property) :
    (fiberBaseChangeArrow B p f' f g sq V).hom.left ≫ fiberProjection B p (baseChange B f V) =
      fiberBaseChangeMap B p f' f g sq V :=
  fiberBaseChangeArrow_proj B p f' f g sq V

/-- `AlgebraicGeometry.SmallEtale.fiberBaseChangeMap_fst`, reassociated. -/
@[reassoc] alias fiberBaseChangeMap_fiberProjection := fiberBaseChangeMap_fst

/-- `AlgebraicGeometry.SmallEtale.fiberBaseChangeMap_snd`, reassociated. -/
@[reassoc] alias fiberBaseChangeMap_hom := fiberBaseChangeMap_snd

end Arrows

section Pushforward

variable (A : Type*) [Category* A]

/-- The comparison `a_* ⋙ b_* ≅ h_*` of direct images of sheaves on small étale sites, for a
factorization `a ≫ b = h`. -/
def pushforwardFactoredCompIso {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (h : X ⟶ Z)
    (hab : a ≫ b = h) :
    (smallEtaleBaseChange B a).sheafPushforwardContinuous A
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property) ⋙
      (smallEtaleBaseChange B b).sheafPushforwardContinuous A
        (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B Y.obj Y.property) ≅
    (smallEtaleBaseChange B h).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B X.obj X.property) :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChange_factoredCompIso B X Y Z a b h hab)
    A (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)

/-- The comparison `a_* ⋙ b_* ≅ h_*` acts on sections by restriction along the comparison of
the two base changes. -/
lemma pushforwardFactoredCompIso_hom_app_hom_app {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : X ⟶ Z) (hab : a ≫ b = h) (F : Sheaf (SmallEtale.topology B X.obj X.property) A)
    (V : SmallEtale B Z.obj Z.property) :
    ((pushforwardFactoredCompIso B A a b h hab).hom.app F).hom.app (op V) =
      F.obj.map ((smallEtaleBaseChange_factoredCompIso B X Y Z a b h hab).inv.app V).op := by
  exact Category.id_comp _

variable {X' X Y' Y : B.Scheme}

/-- The comparison `f'_* ⋙ l_* ≅ k_* ⋙ f_*` of direct images for a commutative square
`k ≫ f = f' ≫ l`, read through a diagonal `h`. -/
def pushforwardSquareIso (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y) (h : X' ⟶ Y)
    (hk : k ≫ f = h) (hl : f' ≫ l = h) :
    (smallEtaleBaseChange B f').sheafPushforwardContinuous A
        (SmallEtale.topology B Y'.obj Y'.property) (SmallEtale.topology B X'.obj X'.property) ⋙
      (smallEtaleBaseChange B l).sheafPushforwardContinuous A
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B Y'.obj Y'.property) ≅
    (smallEtaleBaseChange B k).sheafPushforwardContinuous A
        (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property) ⋙
      (smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property) :=
  pushforwardFactoredCompIso B A f' l h hl ≪≫ (pushforwardFactoredCompIso B A k f h hk).symm

/-- The comparison of a square acts on sections by restriction along the comparison of the two
iterated base changes. -/
lemma pushforwardSquareIso_hom_app_hom_app (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (l : Y' ⟶ Y) (h : X' ⟶ Y) (hk : k ≫ f = h) (hl : f' ≫ l = h)
    (F : Sheaf (SmallEtale.topology B X'.obj X'.property) A)
    (V : SmallEtale B Y.obj Y.property) :
    ((pushforwardSquareIso B A k f' f l h hk hl).hom.app F).hom.app (op V) =
      F.obj.map (squareBaseChangeArrow B k f' f l h hk hl V).op := by
  simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    pushforwardFactoredCompIso_hom_app_hom_app, squareBaseChangeArrow, op_comp, F.obj.map_comp]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

end Pushforward

section PullbackSection

variable {X Y X' Y' : B.Scheme} (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (sq : IsPullback p f' f g)

/-- **The pullback map on a pulled-back section.** For a cartesian square and an abelian sheaf
`G` on `X`, the pullback map `g⁻¹f_*G ⟶ f'_*p⁻¹G`, evaluated at a section of `f_*G` pulled back to
an étale `T` over `Y'` along `arr : T ⟶ W ×_Y Y'`, is the section of `G` over `X_W` pulled back
along the induced arrow `T ×_{Y'} X' ⟶ X_W ×_X X'`. -/
lemma pullbackSectionAlongHom_directImageBaseChange
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (W : SmallEtale B Y.obj Y.property) (T : SmallEtale B Y'.obj Y'.property)
    (arr : T ⟶ (smallEtaleBaseChange B g).obj W) (s : G.obj.obj (op (baseChange B f W))) :
    (directImageBaseChange.{u, v} B p f' f g sq G).hom.app (op T)
        (pullbackSectionAlongHom B g AddCommGrpCat.{max (u + 1) v} (directImageSheaf B f G) W T
          arr s) =
      pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} G (baseChange B f W)
        (baseChange B f' T)
        ((smallEtaleBaseChange B f').map arr ≫ fiberBaseChangeArrow B p f' f g sq W) s := by
  have hdef : pullbackSectionAlongHom B g AddCommGrpCat.{max (u + 1) v} (directImageSheaf B f G)
      W T arr s = ((abPullback.{u, v} B g).obj (directImageSheaf B f G)).obj.map arr.op
        (abPullbackUnit.{u, v} B g (directImageSheaf B f G) W s) :=
    ConcreteCategory.comp_apply _ _ _
  have hnat := ConcreteCategory.congr_hom
    ((directImageBaseChange.{u, v} B p f' f g sq G).hom.naturality arr.op)
    (abPullbackUnit.{u, v} B g (directImageSheaf B f G) W s)
  have htri := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun φ => φ.hom)
    (directImageBaseChange_triangle.{u, v} B p f' f g sq G)) (op W)) s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hnat htri
  rw [hdef]
  refine hnat.trans ?_
  change ((abPullback.{u, v} B p).obj G).obj.map ((smallEtaleBaseChange B f').map arr).op
      ((directImageBaseChange.{u, v} B p f' f g sq G).hom.app
        (op ((smallEtaleBaseChange B g).obj W))
        (abPullbackUnit.{u, v} B g (directImageSheaf B f G) W s)) = _
  rw [show (directImageBaseChange.{u, v} B p f' f g sq G).hom.app
        (op ((smallEtaleBaseChange B g).obj W))
        (abPullbackUnit.{u, v} B g (directImageSheaf B f G) W s) =
      directImageBaseChangeApp.{u, v} B p f' f g sq G W s from htri]
  exact pullbackSectionAlongHom_restrict.{u, v} B p G _ _ _ s

end PullbackSection

section Cube

variable {X' X Y' Y X'₁ X₁ Y'₁ Y₁ : B.Scheme}
  (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y) (h : X' ⟶ Y) (hk : k ≫ f = h)
  (hl : f' ≫ l = h)
  (b : Y₁ ⟶ Y) (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (sqX : IsPullback a f₁ f b)
  (b' : Y'₁ ⟶ Y') (l₁ : Y'₁ ⟶ Y₁) (sqY : IsPullback b' l₁ l b)
  (a' : X'₁ ⟶ X') (f'₁ : X'₁ ⟶ Y'₁) (sqX' : IsPullback a' f'₁ f' b')
  (k₁ : X'₁ ⟶ X₁) (sqK : IsPullback a' k₁ k a)
  (h₁ : X'₁ ⟶ Y₁) (hk₁ : k₁ ≫ f₁ = h₁) (hl₁ : f'₁ ≫ l₁ = h₁)

/-- The two arrows of the cube along which sections are pulled back agree: both lie over the
base change of the diagonal by `b`. -/
lemma directImageBaseChange_cube_arrow (V : SmallEtale B Y.obj Y.property) :
    (smallEtaleBaseChange B k₁).map (fiberBaseChangeArrow B a f₁ f b sqX V) ≫
        fiberBaseChangeArrow B a' k₁ k a sqK (baseChange B f V) ≫
        (smallEtaleBaseChange B a').map (squareBaseChangeArrow B k f' f l h hk hl V) =
      squareBaseChangeArrow B k₁ f'₁ f₁ l₁ h₁ hk₁ hl₁ (baseChange B b V) ≫
        (smallEtaleBaseChange B f'₁).map (fiberBaseChangeArrow B b' l₁ l b sqY V) ≫
        fiberBaseChangeArrow B a' f'₁ f' b' sqX' (baseChange B l V) := by
  refine baseChangeObj_hom_ext B a' ?_
  simp only [← fiberProjection_eq_baseChangeObjProjection, ObjectProperty.FullSubcategory.comp_hom,
    Over.comp_left, Category.assoc, smallEtaleBaseChange_map_fiberProjection,
    fiberBaseChangeArrow_fiberProjection, fiberBaseChangeArrow_fiberProjection_assoc]
  refine baseChange_baseChange_hom_ext B f' l V ?_ ?_
  · simp only [Category.assoc, squareBaseChangeArrow_fiberProjection,
      fiberBaseChangeMap_fiberProjection_assoc, fiberBaseChangeMap_fiberProjection,
      smallEtaleBaseChange_map_fiberProjection_assoc, fiberBaseChangeArrow_fiberProjection_assoc,
      squareBaseChangeArrow_fiberProjection_assoc]
  · simp only [Category.assoc, Over.w, Over.w_assoc, fiberBaseChangeMap_hom]

/-- **The pullback maps of a cube of cartesian squares are compatible with stacking** (Sites,
Remarks 0F6X and 0F6Y, as used in the proof of [Stacks, Tag 0F7F]). For a commutative square
`k ≫ f = f' ≫ l` with diagonal `h` and its base change by `b : Y₁ ⟶ Y`, the pullback maps of the
four vertical faces satisfy, for every abelian sheaf `F` on `X'`,
```
b⁻¹ l_* f'_* F = b⁻¹ f_* k_* F ⟶ f₁_* a⁻¹ k_* F ⟶ f₁_* k₁_* a'⁻¹ F
  equals
b⁻¹ l_* f'_* F ⟶ l₁_* b'⁻¹ f'_* F ⟶ l₁_* f'₁_* a'⁻¹ F = f₁_* k₁_* a'⁻¹ F.
``` -/
theorem directImageBaseChange_cube
    (F : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{max (u + 1) v}) :
    (abPullback.{u, v} B b).map
        ((pushforwardSquareIso B AddCommGrpCat.{max (u + 1) v} k f' f l h hk hl).hom.app F) ≫
      directImageBaseChange.{u, v} B a f₁ f b sqX (directImageSheaf B k F) ≫
      ((smallEtaleBaseChange B f₁).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y₁.obj Y₁.property)
          (SmallEtale.topology B X₁.obj X₁.property)).map
        (directImageBaseChange.{u, v} B a' k₁ k a sqK F) =
    directImageBaseChange.{u, v} B b' l₁ l b sqY (directImageSheaf B f' F) ≫
      ((smallEtaleBaseChange B l₁).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y₁.obj Y₁.property)
          (SmallEtale.topology B Y'₁.obj Y'₁.property)).map
        (directImageBaseChange.{u, v} B a' f'₁ f' b' sqX' F) ≫
      (pushforwardSquareIso B AddCommGrpCat.{max (u + 1) v} k₁ f'₁ f₁ l₁ h₁ hk₁ hl₁).hom.app
        ((abPullback.{u, v} B a').obj F) := by
  let adj := (smallEtaleBaseChange B b).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B Y₁.obj Y₁.property)
  let A := AddCommGrpCat.{max (u + 1) v}
  have hf : adj.homEquiv
      (((smallEtaleBaseChange B k).sheafPushforwardContinuous A
          (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property) ⋙
        (smallEtaleBaseChange B f).sheafPushforwardContinuous A
          (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)).obj F)
      _ (directImageBaseChange.{u, v} B a f₁ f b sqX (directImageSheaf B k F)) =
      directImageBaseChangePushforward.{u, v} B a f₁ f b sqX (directImageSheaf B k F) :=
    Equiv.apply_symm_apply _ _
  have hl' : adj.homEquiv
      (((smallEtaleBaseChange B f').sheafPushforwardContinuous A
          (SmallEtale.topology B Y'.obj Y'.property) (SmallEtale.topology B X'.obj X'.property) ⋙
        (smallEtaleBaseChange B l).sheafPushforwardContinuous A
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).obj F)
      _ (directImageBaseChange.{u, v} B b' l₁ l b sqY (directImageSheaf B f' F)) =
      directImageBaseChangePushforward.{u, v} B b' l₁ l b sqY (directImageSheaf B f' F) :=
    Equiv.apply_symm_apply _ _
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, hf,
    adj.homEquiv_naturality_right, hl', Functor.map_comp]
  ext ⟨V⟩ s
  let T₁ := baseChange B f₁ (baseChange B b V)
  let T₂ := baseChange B l₁ (baseChange B b V)
  let arrK := (smallEtaleBaseChange B k₁).map (fiberBaseChangeArrow B a f₁ f b sqX V) ≫
    fiberBaseChangeArrow B a' k₁ k a sqK (baseChange B f V)
  let arrX' := (smallEtaleBaseChange B f'₁).map (fiberBaseChangeArrow B b' l₁ l b sqY V) ≫
    fiberBaseChangeArrow B a' f'₁ f' b' sqX' (baseChange B l V)
  have hP := ConcreteCategory.congr_hom
    (pushforwardSquareIso_hom_app_hom_app B A k f' f l h hk hl F V) s
  have hP₁ := fun t => ConcreteCategory.congr_hom
    (pushforwardSquareIso_hom_app_hom_app B A k₁ f'₁ f₁ l₁ h₁ hk₁ hl₁
      ((abPullback.{u, v} B a').obj F) (baseChange B b V)) t
  have eL := pullbackSectionAlongHom_directImageBaseChange.{u, v} B a' k₁ k a sqK F
    (baseChange B f V) T₁ (fiberBaseChangeArrow B a f₁ f b sqX V)
    (F.obj.map (squareBaseChangeArrow B k f' f l h hk hl V).op s)
  have eM := pullbackSectionAlongHom_map.{u, v} B a' F (squareBaseChangeArrow B k f' f l h hk hl V)
    (baseChange B k₁ T₁) arrK s
  have eR := pullbackSectionAlongHom_directImageBaseChange.{u, v} B a' f'₁ f' b' sqX' F
    (baseChange B l V) T₂ (fiberBaseChangeArrow B b' l₁ l b sqY V) s
  have eRe := pullbackSectionAlongHom_restrict.{u, v} B a' F (baseChange B f' (baseChange B l V))
    arrX' (squareBaseChangeArrow B k₁ f'₁ f₁ l₁ h₁ hk₁ hl₁ (baseChange B b V)) s
  have hA : arrK ≫ (smallEtaleBaseChange B a').map (squareBaseChangeArrow B k f' f l h hk hl V) =
      squareBaseChangeArrow B k₁ f'₁ f₁ l₁ h₁ hk₁ hl₁ (baseChange B b V) ≫ arrX' :=
    (Category.assoc _ _ _).trans (directImageBaseChange_cube_arrow B k f' f l h hk hl b a f₁ sqX
      b' l₁ sqY a' f'₁ sqX' k₁ sqK h₁ hk₁ hl₁ V)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, directImageBaseChangePushforward_app]
  refine (congrArg (fun t => (directImageBaseChange.{u, v} B a' k₁ k a sqK F).hom.app (op T₁)
    (pullbackSectionAlongHom B a A (directImageSheaf B k F) (baseChange B f V) T₁
      (fiberBaseChangeArrow B a f₁ f b sqX V) t)) hP).trans ?_
  refine (eL.trans eM).trans ?_
  refine (congrArg (fun m => pullbackSectionAlongHom B a' A F (baseChange B f' (baseChange B l V))
    (baseChange B k₁ T₁) m s) hA).trans ?_
  refine eRe.symm.trans ?_
  refine (hP₁ _).symm.trans ?_
  exact congrArg (fun t => ((pushforwardSquareIso B A k₁ f'₁ f₁ l₁ h₁ hk₁ hl₁).hom.app
    ((abPullback.{u, v} B a').obj F)).hom.app (op (baseChange B b V)) t) eR.symm

end Cube

end AlgebraicGeometry.SmallEtale

end
