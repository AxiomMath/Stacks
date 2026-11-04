module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Pushing a groupoid scheme forward along a morphism of base schemes

Let `g : Y ⟶ S` be a morphism of schemes. A groupoid scheme over `Y` is in particular a groupoid
scheme over `S`: its object and arrow schemes are regarded as schemes over `S` through `g`, and
all five structure morphisms are unchanged on underlying schemes.

## Main definitions

* `Stacks.Groupoids.overAscend`: a morphism of `Over Y` out of `CategoryTheory.Over.mk base`,
  read as a morphism of `Over S` into the image under `CategoryTheory.Over.map g`.
* `Stacks.Groupoids.overDescend`: the inverse operation.
* `Stacks.Groupoids.GroupoidScheme.pushforwardComp`: the composition morphism of the
  pushed-forward groupoid.
* `Stacks.Groupoids.GroupoidScheme.pushforward`: the pushed-forward groupoid scheme over `S`.

## Main results

* `Stacks.Groupoids.preservesLimitsOfShape_walkingCospan_overMap`: `CategoryTheory.Over.map g`
  preserves pullbacks.
* `Stacks.Groupoids.lift_comp_preservesPullbackIso_inv`: the comparison isomorphism of
  `CategoryTheory.Over.map g` for a pullback, on generalized points.
* `Stacks.Groupoids.GroupoidScheme.lift_comp_pushforwardComp`: composing two generalized arrows
  of the pushforward is composing them in the original groupoid.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Groupoids

section PullbackLeg

variable {C : Type*} [Category C] [HasPullbacks C]

/-- Replacing the left leg of a cospan by an isomorphic one. -/
def pullbackLeftLegIso {A A' B D : C} (i : A ≅ A') {fa : A ⟶ D} {f : A' ⟶ D} (b : B ⟶ D)
    (hf : fa = i.hom ≫ f) : pullback fa b ≅ pullback f b where
  hom := pullback.lift (pullback.fst fa b ≫ i.hom) (pullback.snd fa b)
    (by rw [Category.assoc, ← hf, pullback.condition])
  inv := pullback.lift (pullback.fst f b ≫ i.inv) (pullback.snd f b)
    (by rw [Category.assoc, hf, Iso.inv_hom_id_assoc, pullback.condition])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

/-- Replacing the right leg of a cospan by an isomorphic one. -/
def pullbackRightLegIso {A A' B D : C} (i : A ≅ A') {fa : A ⟶ D} {f : A' ⟶ D} (b : B ⟶ D)
    (hf : fa = i.hom ≫ f) : pullback b fa ≅ pullback b f where
  hom := pullback.lift (pullback.fst b fa) (pullback.snd b fa ≫ i.hom)
    (by rw [Category.assoc, ← hf, ← pullback.condition])
  inv := pullback.lift (pullback.fst b f) (pullback.snd b f ≫ i.inv)
    (by rw [Category.assoc, hf, Iso.inv_hom_id_assoc, ← pullback.condition])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- `pullbackLeftLegIso` leaves the second projection unchanged. -/
@[simp]
lemma pullbackLeftLegIso_hom_comp_snd {A A' B D : C} (i : A ≅ A') {fa : A ⟶ D} {f : A' ⟶ D}
    (b : B ⟶ D) (hf : fa = i.hom ≫ f) :
    (pullbackLeftLegIso i b hf).hom ≫ pullback.snd f b = pullback.snd fa b :=
  pullback.lift_snd _ _ _

/-- The first projection after `Stacks.Groupoids.pullbackLeftLegIso` is the first projection
followed by the isomorphism of left legs. -/
@[simp]
lemma pullbackLeftLegIso_hom_comp_fst {A A' B D : C} (i : A ≅ A') {fa : A ⟶ D} {f : A' ⟶ D}
    (b : B ⟶ D) (hf : fa = i.hom ≫ f) :
    (pullbackLeftLegIso i b hf).hom ≫ pullback.fst f b = pullback.fst fa b ≫ i.hom :=
  pullback.lift_fst _ _ _

/-- The inverse of `pullbackRightLegIso` leaves the first projection unchanged. -/
@[simp]
lemma pullbackRightLegIso_inv_comp_fst {A A' B D : C} (i : A ≅ A') {fa : A ⟶ D} {f : A' ⟶ D}
    (b : B ⟶ D) (hf : fa = i.hom ≫ f) :
    (pullbackRightLegIso i b hf).inv ≫ pullback.fst b fa = pullback.fst b f :=
  pullback.lift_fst _ _ _

/-- The second projection after the inverse of `Stacks.Groupoids.pullbackRightLegIso` is the
second projection followed by the inverse of the isomorphism of right legs. -/
@[simp]
lemma pullbackRightLegIso_inv_comp_snd {A A' B D : C} (i : A ≅ A') {fa : A ⟶ D} {f : A' ⟶ D}
    (b : B ⟶ D) (hf : fa = i.hom ≫ f) :
    (pullbackRightLegIso i b hf).inv ≫ pullback.snd b fa = pullback.snd b f ≫ i.inv :=
  pullback.lift_snd _ _ _

end PullbackLeg

section Cancel

variable {C : Type*} [Category C]

/-- Cancelling an isomorphism after a morphism into its target. -/
lemma comp_inv_comp_hom {T A B : C} (f : T ⟶ B) (i : A ≅ B) : (f ≫ i.inv) ≫ i.hom = f := by
  simp

end Cancel

section OverMap

variable {C : Type*} [Category C] {Y S : C}

/-- `CategoryTheory.Over.map g` preserves pullbacks. -/
instance preservesLimitsOfShape_walkingCospan_overMap (g : Y ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (Over.map g) :=
  have : PreservesLimitsOfShape WalkingCospan (Over.map g ⋙ Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget Y))
  preservesLimitsOfShape_of_reflects_of_preserves (Over.map g) (Over.forget S)

variable (g : Y ⟶ S)

/-- A generalized point of `(CategoryTheory.Over.map g).obj Z` out of a test object of `Over S`
whose structure morphism factors through `g` as `base ≫ g`: it is the same data as a morphism
of `Over Y` out of `CategoryTheory.Over.mk base`. -/
def overAscend {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom) {Z : Over Y}
    (u : (Over.mk base : Over Y) ⟶ Z) : A ⟶ (Over.map g).obj Z :=
  Over.homMk u.left (by rw [Over.map_obj_hom, ← Category.assoc, Over.w u]; exact hb)

/-- A generalized point of `(CategoryTheory.Over.map g).obj Z` read as a morphism of `Over Y`,
once the point of `Y` its test object is to lie over has been named. -/
def overDescend {A : Over S} {base : A.left ⟶ Y} {Z : Over Y} (u : A ⟶ (Over.map g).obj Z)
    (h : u.left ≫ Z.hom = base) : (Over.mk base : Over Y) ⟶ Z :=
  Over.homMk u.left h

/-- The underlying morphism of `Stacks.Groupoids.overAscend g hb u` is that of `u`. -/
@[simp]
lemma overAscend_left {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom) {Z : Over Y}
    (u : (Over.mk base : Over Y) ⟶ Z) : (overAscend g hb u).left = u.left := rfl

/-- The underlying morphism of `Stacks.Groupoids.overDescend g u h` is that of `u`. -/
@[simp]
lemma overDescend_left {A : Over S} {base : A.left ⟶ Y} {Z : Over Y}
    (u : A ⟶ (Over.map g).obj Z) (h : u.left ≫ Z.hom = base) :
    (overDescend g u h).left = u.left := rfl

/-- Ascending a descended generalized point returns it unchanged. -/
lemma overAscend_overDescend {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom)
    {Z : Over Y} (u : A ⟶ (Over.map g).obj Z) (h : u.left ≫ Z.hom = base) :
    overAscend g hb (overDescend g u h) = u :=
  Over.OverMorphism.ext rfl

/-- Ascending commutes with postcomposition. -/
lemma overAscend_comp {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom) {Z W : Over Y}
    (u : (Over.mk base : Over Y) ⟶ Z) (k : Z ⟶ W) :
    overAscend g hb (u ≫ k) = overAscend g hb u ≫ (Over.map g).map k :=
  Over.OverMorphism.ext rfl

/-- Ascending along the structure morphism of the test object itself is the image under
`CategoryTheory.Over.map`. -/
lemma overAscend_self {A Z : Over Y} (u : A ⟶ Z) :
    overAscend g (rfl : A.hom ≫ g = ((Over.map g).obj A).hom) u = (Over.map g).map u :=
  Over.OverMorphism.ext rfl

/-- An isomorphism between the images of two objects of `Over Y` which respects their structure
morphisms to `Y` descends to an isomorphism of `Over Y`. -/
def overDescendIso {Z W : Over Y} (u : (Over.map g).obj Z ≅ (Over.map g).obj W)
    (h : u.hom.left ≫ W.hom = Z.hom) : Z ≅ W where
  hom := Over.homMk u.hom.left h
  inv := Over.homMk u.inv.left (by
    rw [← h, ← Category.assoc, ← Over.comp_left, u.inv_hom_id, Over.id_left]
    exact Category.id_comp _)
  hom_inv_id := Over.OverMorphism.ext (congrArg Over.Hom.left u.hom_inv_id :)
  inv_hom_id := Over.OverMorphism.ext (congrArg Over.Hom.left u.inv_hom_id :)

/-- The underlying morphism of `Stacks.Groupoids.overDescendIso g u h` is that of `u`. -/
@[simp]
lemma overDescendIso_hom_left {Z W : Over Y} (u : (Over.map g).obj Z ≅ (Over.map g).obj W)
    (h : u.hom.left ≫ W.hom = Z.hom) : (overDescendIso g u h).hom.left = u.hom.left := rfl

/-- The image of a descended isomorphism is the isomorphism itself. -/
lemma map_overDescendIso_hom {Z W : Over Y} (u : (Over.map g).obj Z ≅ (Over.map g).obj W)
    (h : u.hom.left ≫ W.hom = Z.hom) :
    (Over.map g).map (overDescendIso g u h).hom = u.hom :=
  Over.OverMorphism.ext rfl

/-- The comparison isomorphism of `CategoryTheory.Over.map g` for a pullback, on generalized
points: the lift of a pair of generalized points of the images of the two legs which descends to
`Over Y`, followed by the inverse comparison isomorphism, is the ascent of the lift computed in
`Over Y`. -/
lemma lift_comp_preservesPullbackIso_inv [HasPullbacks C] {Z₁ Z₂ Z₃ : Over Y}
    (a : Z₁ ⟶ Z₃) (b : Z₂ ⟶ Z₃) {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom)
    (P : A ⟶ (Over.map g).obj Z₁) (Q : A ⟶ (Over.map g).obj Z₂)
    (p : (Over.mk base : Over Y) ⟶ Z₁) (q : (Over.mk base : Over Y) ⟶ Z₂)
    (hp : p.left = P.left) (hq : q.left = Q.left) (w' : p ≫ a = q ≫ b)
    (w : P ≫ (Over.map g).map a = Q ≫ (Over.map g).map b) :
    pullback.lift P Q w ≫ (PreservesPullback.iso (Over.map g) a b).inv =
      overAscend g hb (pullback.lift p q w') := by
  rw [Iso.comp_inv_eq]
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [pullback.lift_fst, pullback.lift_snd, Category.assoc, PreservesPullback.iso_hom_fst,
      PreservesPullback.iso_hom_snd, ← overAscend_comp]
  exacts [Over.OverMorphism.ext hp.symm, Over.OverMorphism.ext hq.symm]

end OverMap

namespace GroupoidScheme

universe u

open AlgebraicGeometry

variable {Y S : Scheme.{u}} (g : Y ⟶ S) (G : GroupoidScheme Y)

/-- The composition morphism of the pushforward of `G` along `g`: the composition morphism of
`G`, transported across the comparison isomorphism of
`Stacks.Groupoids.preservesLimitsOfShape_walkingCospan_overMap`. -/
def pushforwardComp :
    pullback ((Over.map g).map G.source) ((Over.map g).map G.target) ⟶
      (Over.map g).obj G.arrows :=
  (PreservesPullback.iso (Over.map g) G.source G.target).inv ≫ (Over.map g).map G.comp

/-- Composition of generalized arrows of the pushforward is the ascent of their composition in
`G`. -/
lemma lift_comp_pushforwardComp' {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom)
    (P Q : A ⟶ (Over.map g).obj G.arrows)
    (p q : (Over.mk base : Over Y) ⟶ G.arrows)
    (hp : p.left = P.left) (hq : q.left = Q.left)
    (w' : p ≫ G.source = q ≫ G.target)
    (w : P ≫ (Over.map g).map G.source = Q ≫ (Over.map g).map G.target) :
    pullback.lift P Q w ≫ pushforwardComp g G =
      overAscend g hb (pullback.lift p q w' ≫ G.comp) := by
  rw [pushforwardComp, ← Category.assoc,
    lift_comp_preservesPullbackIso_inv g G.source G.target hb P Q p q hp hq w' w,
    ← overAscend_comp]

/-- Composition of generalized arrows of the pushforward is composition in `G`, with the
composite named on both sides. -/
lemma lift_comp_pushforwardComp {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom)
    (P Q R : A ⟶ (Over.map g).obj G.arrows)
    (p q r : (Over.mk base : Over Y) ⟶ G.arrows)
    (hp : p.left = P.left) (hq : q.left = Q.left) (hr : r.left = R.left)
    (w' : p ≫ G.source = q ≫ G.target)
    (w : P ≫ (Over.map g).map G.source = Q ≫ (Over.map g).map G.target)
    (h : pullback.lift p q w' ≫ G.comp = r) :
    pullback.lift P Q w ≫ pushforwardComp g G = R := by
  rw [lift_comp_pushforwardComp' g G hb P Q p q hp hq w' w, h]
  exact Over.OverMorphism.ext hr

/-- The structure morphism of the test object of a generalized arrow `a` of the pushforward
factors through `g` as `(a.left ≫ G.arrows.hom) ≫ g`. -/
lemma arrows_base {A : Over S} (a : A ⟶ (Over.map g).obj G.arrows) :
    (a.left ≫ G.arrows.hom) ≫ g = A.hom :=
  (Category.assoc _ _ _).trans (Over.w a)

/-- Two composable generalized arrows of the pushforward lie over the same point of `Y`. -/
lemma arrows_base_of_source {A : Over S} (a b : A ⟶ (Over.map g).obj G.arrows)
    (wab : a ≫ (Over.map g).map G.source = b ≫ (Over.map g).map G.target) :
    b.left ≫ G.arrows.hom = a.left ≫ G.arrows.hom := by
  calc b.left ≫ G.arrows.hom = (b.left ≫ G.target.left) ≫ G.objects.hom := by
        rw [Category.assoc, Over.w G.target]
    _ = (a.left ≫ G.source.left) ≫ G.objects.hom :=
        congrArg (· ≫ G.objects.hom) (congrArg Over.Hom.left wab).symm
    _ = a.left ≫ G.arrows.hom := by rw [Category.assoc, Over.w G.source]

/-- The pushforward of a groupoid scheme `G` over `Y` along `g : Y ⟶ S`: the groupoid scheme
over `S` with the same object and arrow schemes, regarded as schemes over `S` through `g`, and
the same five structure morphisms. -/
def pushforward : GroupoidScheme S where
  objects := (Over.map g).obj G.objects
  arrows := (Over.map g).obj G.arrows
  source := (Over.map g).map G.source
  target := (Over.map g).map G.target
  comp := pushforwardComp g G
  identity := (Over.map g).map G.identity
  inverse := (Over.map g).map G.inverse
  source_identity := by
    rw [← Functor.map_comp, G.source_identity, CategoryTheory.Functor.map_id]
  target_identity := by
    rw [← Functor.map_comp, G.target_identity, CategoryTheory.Functor.map_id]
  source_inverse := by rw [← Functor.map_comp, G.source_inverse]
  target_inverse := by rw [← Functor.map_comp, G.target_inverse]
  source_comp := by
    rw [pushforwardComp, Category.assoc, ← Functor.map_comp, G.source_comp, Functor.map_comp,
      PreservesPullback.iso_inv_snd_assoc]
  target_comp := by
    rw [pushforwardComp, Category.assoc, ← Functor.map_comp, G.target_comp, Functor.map_comp,
      PreservesPullback.iso_inv_fst_assoc]
  left_identity := by
    intro A a w
    refine lift_comp_pushforwardComp g G (arrows_base g G a) _ a a
      (overDescend g a rfl ≫ G.target ≫ G.identity) (overDescend g a rfl)
      (overDescend g a rfl) rfl rfl rfl ?_ w ?_
    · rw [Category.assoc, Category.assoc, G.source_identity, Category.comp_id]
    · exact G.left_identity _ (overDescend g a rfl) _
  right_identity := by
    intro A a w
    refine lift_comp_pushforwardComp g G (arrows_base g G a) a _ a
      (overDescend g a rfl) (overDescend g a rfl ≫ G.source ≫ G.identity)
      (overDescend g a rfl) rfl rfl rfl ?_ w ?_
    · rw [Category.assoc, Category.assoc, G.target_identity, Category.comp_id]
    · exact G.right_identity _ (overDescend g a rfl) _
  left_inverse := by
    intro A a w
    refine lift_comp_pushforwardComp g G (arrows_base g G a) _ a
      (a ≫ (Over.map g).map G.source ≫ (Over.map g).map G.identity)
      (overDescend g a rfl ≫ G.inverse) (overDescend g a rfl)
      (overDescend g a rfl ≫ G.source ≫ G.identity) rfl rfl rfl ?_ w ?_
    · rw [Category.assoc, G.source_inverse]
    · exact G.left_inverse _ (overDescend g a rfl) _
  right_inverse := by
    intro A a w
    refine lift_comp_pushforwardComp g G (arrows_base g G a) a _
      (a ≫ (Over.map g).map G.target ≫ (Over.map g).map G.identity)
      (overDescend g a rfl) (overDescend g a rfl ≫ G.inverse)
      (overDescend g a rfl ≫ G.target ≫ G.identity) rfl rfl rfl ?_ w ?_
    · rw [Category.assoc, G.target_inverse]
    · exact G.right_inverse _ (overDescend g a rfl) _
  assoc := by
    intro A a b c wab wbc w₁ w₂
    have hbb : b.left ≫ G.arrows.hom = a.left ≫ G.arrows.hom :=
      arrows_base_of_source g G a b wab
    have hbc : c.left ≫ G.arrows.hom = a.left ≫ G.arrows.hom :=
      (arrows_base_of_source g G b c wbc).trans hbb
    have wab' : overDescend g a rfl ≫ G.source = overDescend g b hbb ≫ G.target :=
      Over.OverMorphism.ext (congrArg Over.Hom.left wab :)
    have wbc' : overDescend g b hbb ≫ G.source = overDescend g c hbc ≫ G.target :=
      Over.OverMorphism.ext (congrArg Over.Hom.left wbc :)
    have hL := lift_comp_pushforwardComp' g G (arrows_base g G a) a b
      (overDescend g a rfl) (overDescend g b hbb) rfl rfl wab' wab
    have hR := lift_comp_pushforwardComp' g G (arrows_base g G a) b c
      (overDescend g b hbb) (overDescend g c hbc) rfl rfl wbc' wbc
    have w₁' : (pullback.lift (overDescend g a rfl) (overDescend g b hbb) wab' ≫ G.comp) ≫
        G.source = overDescend g c hbc ≫ G.target := by
      rw [Category.assoc, G.source_comp, ← Category.assoc, pullback.lift_snd]
      exact wbc'
    have w₂' : overDescend g a rfl ≫ G.source =
        (pullback.lift (overDescend g b hbb) (overDescend g c hbc) wbc' ≫ G.comp) ≫
          G.target := by
      rw [Category.assoc, G.target_comp, ← Category.assoc, pullback.lift_fst]
      exact wab'
    refine Eq.trans (lift_comp_pushforwardComp' g G (arrows_base g G a) _ c
      (pullback.lift (overDescend g a rfl) (overDescend g b hbb) wab' ≫ G.comp)
      (overDescend g c hbc) (congrArg Over.Hom.left hL).symm rfl w₁' w₁) ?_
    refine Eq.trans ?_ (lift_comp_pushforwardComp' g G (arrows_base g G a) a _
      (overDescend g a rfl)
      (pullback.lift (overDescend g b hbb) (overDescend g c hbc) wbc' ≫ G.comp)
      rfl (congrArg Over.Hom.left hR).symm w₂' w₂).symm
    exact congrArg (overAscend g (arrows_base g G a))
      (G.assoc _ (overDescend g a rfl) (overDescend g b hbb) (overDescend g c hbc)
        wab' wbc' w₁' w₂')

/-- The object scheme of the pushforward is the image of that of `G`. -/
@[simp]
lemma pushforward_objects : (G.pushforward g).objects = (Over.map g).obj G.objects := rfl

/-- The arrow scheme of the pushforward is the image of that of `G`. -/
@[simp]
lemma pushforward_arrows : (G.pushforward g).arrows = (Over.map g).obj G.arrows := rfl

/-- The source morphism of the pushforward is the image of that of `G`. -/
@[simp]
lemma pushforward_source : (G.pushforward g).source = (Over.map g).map G.source := rfl

/-- The target morphism of the pushforward is the image of that of `G`. -/
@[simp]
lemma pushforward_target : (G.pushforward g).target = (Over.map g).map G.target := rfl

/-- The identity morphism of the pushforward is the image of that of `G`. -/
@[simp]
lemma pushforward_identity : (G.pushforward g).identity = (Over.map g).map G.identity := rfl

/-- The inverse morphism of the pushforward is the image of that of `G`. -/
@[simp]
lemma pushforward_inverse : (G.pushforward g).inverse = (Over.map g).map G.inverse := rfl

/-- The composition morphism of the pushforward is
`Stacks.Groupoids.GroupoidScheme.pushforwardComp`. -/
@[simp]
lemma pushforward_comp_eq : (G.pushforward g).comp = pushforwardComp g G := rfl

/-- Composition of generalized arrows of the pushforward is the ascent of their composition in
`G`. -/
lemma pushforward_compose {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom)
    (P Q : A ⟶ (G.pushforward g).arrows)
    (p q : (Over.mk base : Over Y) ⟶ G.arrows)
    (hp : p.left = P.left) (hq : q.left = Q.left)
    (w' : p ≫ G.source = q ≫ G.target)
    (w : P ≫ (G.pushforward g).source = Q ≫ (G.pushforward g).target) :
    (G.pushforward g).compose P Q w = overAscend g hb (G.compose p q w') :=
  lift_comp_pushforwardComp' g G hb P Q p q hp hq w' w

end GroupoidScheme

end Stacks.Groupoids

end

end
