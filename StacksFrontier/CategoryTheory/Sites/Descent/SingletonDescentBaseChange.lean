module

public import StacksFrontier.CategoryTheory.Limits.SelfPullbackBaseChange
public import StacksFrontier.CategoryTheory.Sites.Descent.DescentCounitLocal
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentAdjunction

/-!
# The counit of singleton descent after a base change

Let `F` be a pseudofunctor from the locally discrete bicategory on `C₀ᵒᵖ` to `Cat`, let
`f : X ⟶ Y` be a morphism with a chosen fibre product `XX` of `f` with itself, and let
`g : V ⟶ Y` be a second morphism with a chosen fibre product `P` of `f` and `g`. Then
`P.p₂ : X ×_Y V ⟶ V` is the base change of `f` along `g`; let `QQ` be a chosen fibre product of
`P.p₂` with itself and let `j : QQ ⟶ XX` be a morphism exhibiting `QQ` as the base change of
`XX` along `g`, as produced by
`CategoryTheory.Limits.ChosenPullback.baseChangedSelf`.

Assume the fibres of `F` over `Y` and over `V` have equalizers, so that
`CategoryTheory.Pseudofunctor.singletonDescentAdjunction` gives right adjoints to the
comparison functors of the singleton families `{f}` and `{P.p₂}`. Assume further that the
inverse image along `g` preserves finite limits, that descent along `{P.p₂}` is effective, and
that the two base-change `2`-cells attached to the squares `(f, g, P)` and `(XX.p, g, QQ)` are
invertible. This file proves that the counit of the adjunction for `{f}` becomes an isomorphism
after base change along `g`.

## Main definitions

* `CategoryTheory.Pseudofunctor.commSqTwoSquare`: the `2`-cell of inverse images attached to a
  commutative square;
* `CategoryTheory.Pseudofunctor.DescentData.component`: evaluation of a descent datum at one
  member of the family;
* `CategoryTheory.Pseudofunctor.singletonPullFunctor` and
  `CategoryTheory.Pseudofunctor.singletonPullFunctorIso`: the base change of descent data
  along `g` for the singleton family `{f}`, and its compatibility with the canonical descent
  datum of an object;
* `CategoryTheory.Pseudofunctor.reconstructionBaseChangeIso`: the comparison of the
  reconstruction of a descent datum with the reconstruction of its base change.

## Main results

* `CategoryTheory.Pseudofunctor.reconstructionFirst_baseChange` and
  `CategoryTheory.Pseudofunctor.reconstructionSecond_baseChange`: the two morphisms whose
  equalizer reconstructs an object from a descent datum are compatible with the base change;
* `CategoryTheory.Pseudofunctor.reconstructionBaseChangeIso_hom_ι`: the comparison of the two
  reconstructions is compatible with the two inclusions of the equalizers;
* `CategoryTheory.Pseudofunctor.isIso_singletonPullFunctor_map_counit`: **the counit becomes an
  isomorphism after the base change.**

## Implementation notes

The commutation `hw : P.p₁ ≫ f = P.p₂ ≫ g` of the square is taken as a hypothesis rather than
read off as `P.condition`, so that terms built from another proof of it agree with the ones here
on the nose.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe t v v' u u'

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- The `2`-cell of inverse images attached to a commutative square `i ≫ f = f' ≫ g`: the
comparison of the two composite inverse images, read as a `2`-square. -/
abbrev commSqTwoSquare {X₁ X₂ Y₁ Y₂ : C} {i : X₂ ⟶ X₁} {f' : X₂ ⟶ Y₂} {f : X₁ ⟶ Y₁}
    {g : Y₂ ⟶ Y₁} (w : i ≫ f = f' ≫ g) :
    TwoSquare (F.map g.op.toLoc).toFunctor (F.map f.op.toLoc).toFunctor
      (F.map f'.op.toLoc).toFunctor (F.map i.op.toLoc).toFunctor :=
  TwoSquare.mk _ _ _ _
    (Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk w).op.toLoc)).hom

/-- Evaluation at one member of a family: the functor sending a descent datum to its object
over that member and a morphism of descent data to its component there. -/
@[simps]
def DescentData.component {Y₁ : C} {ι : Type t} {Xf : ι → C} (ff : ∀ i, Xf i ⟶ Y₁) (i : ι) :
    F.DescentData ff ⥤ F.obj (.mk (.op (Xf i))) where
  obj D := D.obj i
  map φ := φ.hom i

section

variable {X₀ Y₀ : C} (f₀ : X₀ ⟶ Y₀) (sq : ChosenPullback f₀ f₀)
  {R₀ : F.obj (.mk (.op X₀)) ⥤ F.obj (.mk (.op Y₀))}
  (adj : (F.map f₀.op.toLoc).toFunctor ⊣ R₀)
  {T₀ : F.obj (.mk (.op sq.pullback)) ⥤ F.obj (.mk (.op Y₀))}
  (adjK : (F.map sq.p.op.toLoc).toFunctor ⊣ T₀)

/-- The first reconstruction morphism, with the identity written after the restricted
counit. -/
theorem reconstructionFirst_comp_id (D : F.DescentData (fun _ : Unit ↦ f₀)) :
    reconstructionFirst F f₀ sq adj adjK D =
      adjK.homEquiv _ _
        ((F.mapComp' f₀.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
            rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])).hom.toNatTrans.app
              (R₀.obj (D.obj ())) ≫
          (F.map sq.p₁.op.toLoc).toFunctor.map (adj.counit.app (D.obj ())) ≫
            𝟙 ((F.map sq.p₁.op.toLoc).toFunctor.obj (D.obj ()))) :=
  congrArg (adjK.homEquiv _ _)
    (congrArg (fun z => (F.mapComp' f₀.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])).hom.toNatTrans.app
            (R₀.obj (D.obj ())) ≫ z)
      (Category.comp_id
        ((F.map sq.p₁.op.toLoc).toFunctor.map (adj.counit.app (D.obj ())))).symm)

end

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

/-- The base change along `g` of descent data for the singleton family `{f}`: descent data for
the singleton family `{P.p₂}` of the base-changed morphism. -/
abbrev singletonPullFunctor :
    F.DescentData (fun _ : Unit ↦ f) ⥤ F.DescentData (fun _ : Unit ↦ P.p₂) :=
  DescentData.pullFunctor F (f := fun _ : Unit ↦ f) (f' := fun _ : Unit ↦ P.p₂)
    (p := g) (α := fun _ ↦ ()) (p' := fun _ ↦ P.p₁) (fun _ ↦ hw)

/-- Base change along `g` carries the canonical descent datum of an object to the canonical
descent datum of its inverse image. -/
abbrev singletonPullFunctorIso :
    F.toDescentData (fun _ : Unit ↦ f) ⋙ singletonPullFunctor F f g P hw ≅
      (F.map g.op.toLoc).toFunctor ⋙ F.toDescentData (fun _ : Unit ↦ P.p₂) :=
  DescentData.toDescentDataCompPullFunctorIso F (f := fun _ : Unit ↦ f)
    (f' := fun _ : Unit ↦ P.p₂) (p := g) (α := fun _ ↦ ()) (p' := fun _ ↦ P.p₁)
    (fun _ ↦ hw)

/-- The transpose of the counit-restricted morphism along `r` is compatible with the base change
along `g`, for any compatible families of squares `r`, `r'`. -/
private theorem baseChange_transpose_compatible (r : XX.pullback ⟶ X)
    (r' : QQ.pullback ⟶ P.pullback)
    (hr : r ≫ f = XX.p) (hr' : r' ≫ P.p₂ = QQ.p) (hs : r' ≫ P.p₁ = j ≫ r)
    (M : F.obj (.mk (.op X))) {N N' : _} (z : (F.map r.op.toLoc).toFunctor.obj M ⟶ N)
    (z' : (F.map r'.op.toLoc).toFunctor.obj ((F.map P.p₁.op.toLoc).toFunctor.obj M) ⟶ N')
    (n : (F.map j.op.toLoc).toFunctor.obj N ⟶ N')
    (hz : (F.map j.op.toLoc).toFunctor.map z ≫ n =
      (Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk hs).op.toLoc)).hom.app M ≫ z') :
    (F.map g.op.toLoc).toFunctor.map (af₁.homEquiv _ _
        ((Cat.Hom.toNatIso (F.mapComp' f.op.toLoc r.op.toLoc XX.p.op.toLoc (by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp, hr]))).hom.app (R.obj M) ≫
          (F.map r.op.toLoc).toFunctor.map (af.counit.app M) ≫ z)) ≫
        (mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app N ≫ Tq.map n =
      (mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app M ≫
        aq₁.homEquiv _ _
          ((Cat.Hom.toNatIso (F.mapComp' P.p₂.op.toLoc r'.op.toLoc QQ.p.op.toLoc (by
            rw [← Quiver.Hom.comp_toLoc, ← op_comp, hr']))).hom.app
              (Rq.obj ((F.map P.p₁.op.toLoc).toFunctor.obj M)) ≫
            (F.map r'.op.toLoc).toFunctor.map (aq.counit.app _) ≫ z') :=
  transpose_baseChange_compatible af af₁ aq aq₁
    (F.map g.op.toLoc).toFunctor (F.map P.p₁.op.toLoc).toFunctor (F.map j.op.toLoc).toFunctor
    (F.map r.op.toLoc).toFunctor (F.map r'.op.toLoc).toFunctor
    (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc r.op.toLoc XX.p.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, hr])))
    (Cat.Hom.toNatIso (F.mapComp' P.p₂.op.toLoc r'.op.toLoc QQ.p.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, hr'])))
    (Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk hs).op.toLoc))
    (Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk hw).op.toLoc))
    (Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk hj).op.toLoc))
    (mateEquiv af aq (commSqTwoSquare F hw)).natTrans
    (mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans
    (mateEquiv_counit af aq (commSqTwoSquare F hw))
    (mateEquiv_counit af₁ aq₁ (commSqTwoSquare F hj))
    (fun W ↦ square_comp_coherence F f g P.p₁ P.p₂ r XX.p j r' QQ.p hw hr hr' hs hj W)
    M _ _ z z' _ hz

/-- **The first reconstruction morphism is compatible with the base change**: its inverse image
along `g`, followed by the comparison of the two targets, is the comparison of the two sources
followed by the first reconstruction morphism of the base-changed descent datum. -/
theorem reconstructionFirst_baseChange (D : F.DescentData (fun _ : Unit ↦ f)) :
    (F.map g.op.toLoc).toFunctor.map (reconstructionFirst F f XX af af₁ D) ≫
        (mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app
            ((F.map XX.p₁.op.toLoc).toFunctor.obj (D.obj ())) ≫
          Tq.map ((Cat.Hom.toNatIso (F.isoMapOfCommSq
            (CommSq.mk hs₁).op.toLoc)).hom.app (D.obj ())) =
      (mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app (D.obj ()) ≫
        reconstructionFirst F P.p₂ QQ aq aq₁
          ((singletonPullFunctor F f g P hw).obj D) := by
  rw [reconstructionFirst_comp_id F f XX af af₁ D,
    reconstructionFirst_comp_id F P.p₂ QQ aq aq₁ ((singletonPullFunctor F f g P hw).obj D)]
  exact baseChange_transpose_compatible F f g P XX QQ hw j hj af af₁ aq aq₁ XX.p₁ QQ.p₁ XX.hp₁
    QQ.hp₁ hs₁ (D.obj ()) (𝟙 _) (𝟙 _) _ (by simp)

include hw hs₂ in
/-- **The second reconstruction morphism is compatible with the base change**: its inverse
image along `g`, followed by the comparison of the two targets, is the comparison of the two
sources followed by the second reconstruction morphism of the base-changed descent datum. -/
theorem reconstructionSecond_baseChange (D : F.DescentData (fun _ : Unit ↦ f)) :
    (F.map g.op.toLoc).toFunctor.map (reconstructionSecond F f XX af af₁ D) ≫
        (mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app
            ((F.map XX.p₁.op.toLoc).toFunctor.obj (D.obj ())) ≫
          Tq.map ((Cat.Hom.toNatIso (F.isoMapOfCommSq
            (CommSq.mk hs₁).op.toLoc)).hom.app (D.obj ())) =
      (mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app (D.obj ()) ≫
        reconstructionSecond F P.p₂ QQ aq aq₁
          ((singletonPullFunctor F f g P hw).obj D) :=
  baseChange_transpose_compatible F f g P XX QQ hw j hj af af₁ aq aq₁ XX.p₂ QQ.p₂ XX.hp₂
    QQ.hp₂ hs₂ (D.obj ())
    (D.hom XX.p (i₁ := ()) (i₂ := ()) XX.p₂ XX.p₁ XX.hp₂ XX.hp₁)
    (((singletonPullFunctor F f g P hw).obj D).hom QQ.p (i₁ := ()) (i₂ := ())
      QQ.p₂ QQ.p₁ QQ.hp₂ QQ.hp₁) _
    (square_descent_compatible F f g P.p₁ P.p₂ XX.p₁ XX.p₂ XX.p j QQ.p₁ QQ.p₂ QQ.p
      hw XX.hp₁ XX.hp₂ QQ.hp₁ QQ.hp₂ hs₁ hs₂ hj D)

section

variable [HasEqualizers (F.obj (.mk (.op Y)))] [HasEqualizers (F.obj (.mk (.op V)))]
  [PreservesFiniteLimits (F.map g.op.toLoc).toFunctor]

include hw hs₂ in
/-- **The inverse image of a reconstruction is the reconstruction of the base change.** Since
the inverse image along `g` preserves finite limits it carries the equalizer reconstructing an
object from a descent datum to the equalizer reconstructing an object from the base-changed
datum, by the two compatibilities of the reconstruction morphisms. -/
noncomputable def reconstructionBaseChangeIso
    (hβ : ∀ M, IsIso ((mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app M))
    (hγ : ∀ N, IsIso ((mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app N))
    (D : F.DescentData (fun _ : Unit ↦ f)) :
    (F.map g.op.toLoc).toFunctor.obj
        (equalizer (reconstructionFirst F f XX af af₁ D)
          (reconstructionSecond F f XX af af₁ D)) ≅
      equalizer (reconstructionFirst F P.p₂ QQ aq aq₁ ((singletonPullFunctor F f g P hw).obj D))
        (reconstructionSecond F P.p₂ QQ aq aq₁ ((singletonPullFunctor F f g P hw).obj D)) :=
  equalizerIsoOfCompatibleSquare (F.map g.op.toLoc).toFunctor _ _ _ _
    (@asIso _ _ _ _
      ((mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app (D.obj ()))
      (hβ (D.obj ())))
    (@asIso _ _ _ _
        ((mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app
          ((F.map XX.p₁.op.toLoc).toFunctor.obj (D.obj ())))
        (hγ ((F.map XX.p₁.op.toLoc).toFunctor.obj (D.obj ()))) ≪≫
      Tq.mapIso ((Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk hs₁).op.toLoc)).app (D.obj ())))
    (reconstructionFirst_baseChange F f g P XX QQ hw j hj hs₁ af af₁ aq aq₁ D)
    (reconstructionSecond_baseChange F f g P XX QQ hw j hj hs₁ hs₂ af af₁ aq aq₁ D)

include hw hs₂ in
/-- The comparison of `CategoryTheory.Pseudofunctor.reconstructionBaseChangeIso` is compatible
with the two inclusions of the equalizers. -/
theorem reconstructionBaseChangeIso_hom_ι
    (hβ : ∀ M, IsIso ((mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app M))
    (hγ : ∀ N, IsIso ((mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app N))
    (D : F.DescentData (fun _ : Unit ↦ f)) :
    (reconstructionBaseChangeIso F f g P XX QQ hw j hj hs₁ hs₂ af af₁ aq aq₁ hβ hγ D).hom ≫
        equalizer.ι
          (reconstructionFirst F P.p₂ QQ aq aq₁ ((singletonPullFunctor F f g P hw).obj D))
          (reconstructionSecond F P.p₂ QQ aq aq₁ ((singletonPullFunctor F f g P hw).obj D)) =
      (F.map g.op.toLoc).toFunctor.map
          (equalizer.ι (reconstructionFirst F f XX af af₁ D)
            (reconstructionSecond F f XX af af₁ D)) ≫
        (mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app (D.obj ()) :=
  equalizerIsoOfCompatibleSquare_hom_ι (F.map g.op.toLoc).toFunctor _ _ _ _ _ _
    (reconstructionFirst_baseChange F f g P XX QQ hw j hj hs₁ af af₁ aq aq₁ D)
    (reconstructionSecond_baseChange F f g P XX QQ hw j hj hs₁ hs₂ af af₁ aq aq₁ D)

include hw hs₁ hs₂ in
/-- **The counit of singleton descent becomes an isomorphism after base change along `g`**,
when descent along the base-changed morphism `P.p₂` is effective and the two base-change
`2`-cells are invertible. -/
theorem isIso_singletonPullFunctor_map_counit
    [(F.toDescentData (fun _ : Unit ↦ P.p₂)).IsEquivalence]
    (hβ : ∀ M, IsIso ((mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app M))
    (hγ : ∀ N, IsIso ((mateEquiv af₁ aq₁ (commSqTwoSquare F hj)).natTrans.app N))
    (D : F.DescentData (fun _ : Unit ↦ f)) :
    IsIso ((singletonPullFunctor F f g P hw).map
      ((singletonDescentAdjunction F f XX af af₁).counit.app D)) := by
  apply isIso_map_counit_of_isIso_mate (singletonDescentAdjunction F f XX af af₁)
    (singletonDescentAdjunction F P.p₂ QQ aq aq₁) (F.map g.op.toLoc).toFunctor
    (singletonPullFunctor F f g P hw)
    (singletonPullFunctorIso F f g P hw) D
  have hm : (singletonDescentAdjunction F P.p₂ QQ aq aq₁).homEquiv
        ((F.map g.op.toLoc).toFunctor.obj ((singletonDescentRightAdjoint F f XX af af₁).obj D))
        ((singletonPullFunctor F f g P hw).obj D)
        ((singletonPullFunctorIso F f g P hw).inv.app
            ((singletonDescentRightAdjoint F f XX af af₁).obj D) ≫
          (singletonPullFunctor F f g P hw).map
            ((singletonDescentAdjunction F f XX af af₁).counit.app D)) =
      (reconstructionBaseChangeIso F f g P XX QQ hw j hj hs₁ hs₂
        af af₁ aq aq₁ hβ hγ D).hom := by
    refine (Equiv.eq_symm_apply _).mp (Eq.trans ?_
      ((singletonDescentAdjunction F P.p₂ QQ aq aq₁).homEquiv_counit _ _ _).symm)
    ext ⟨⟩
    show (Cat.Hom.toNatIso (F.isoMapOfCommSq
          (CommSq.mk hw).op.toLoc)).hom.app
            ((singletonDescentRightAdjoint F f XX af af₁).obj D) ≫
        (F.map P.p₁.op.toLoc).toFunctor.map
          (((singletonDescentAdjunction F f XX af af₁).counit.app D).hom ()) =
      (F.map P.p₂.op.toLoc).toFunctor.map
          (reconstructionBaseChangeIso F f g P XX QQ hw j hj hs₁ hs₂
            af af₁ aq aq₁ hβ hγ D).hom ≫
        ((singletonDescentAdjunction F P.p₂ QQ aq aq₁).counit.app
          ((singletonPullFunctor F f g P hw).obj D)).hom ()
    rw [singletonDescentAdjunction_counit_hom, singletonDescentAdjunction_counit_hom,
      ← CategoryTheory.Functor.map_comp_assoc,
      reconstructionBaseChangeIso_hom_ι F f g P XX QQ hw j hj hs₁ hs₂
        af af₁ aq aq₁ hβ hγ D]
    refine Eq.trans (congrArg (fun z =>
        (Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk hw).op.toLoc)).hom.app
          ((singletonDescentRightAdjoint F f XX af af₁).obj D) ≫ z)
      (CategoryTheory.Functor.map_comp (F.map P.p₁.op.toLoc).toFunctor
        ((F.map f.op.toLoc).toFunctor.map (equalizer.ι (reconstructionFirst F f XX af af₁ D)
          (reconstructionSecond F f XX af af₁ D)))
        (af.counit.app (D.obj ())))) ?_
    refine Eq.trans
      ((Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk hw).op.toLoc)).hom.naturality_assoc
          (equalizer.ι (reconstructionFirst F f XX af af₁ D)
            (reconstructionSecond F f XX af af₁ D))
          ((F.map P.p₁.op.toLoc).toFunctor.map (af.counit.app (D.obj ())))).symm ?_
    refine Eq.trans (congrArg (fun z =>
        (F.map P.p₂.op.toLoc).toFunctor.map ((F.map g.op.toLoc).toFunctor.map
          (equalizer.ι (reconstructionFirst F f XX af af₁ D)
            (reconstructionSecond F f XX af af₁ D))) ≫ z)
      (mateEquiv_counit af aq (commSqTwoSquare F hw) (D.obj ())).symm) ?_
    exact (CategoryTheory.Functor.map_comp_assoc (F.map P.p₂.op.toLoc).toFunctor
      ((F.map g.op.toLoc).toFunctor.map (equalizer.ι (reconstructionFirst F f XX af af₁ D)
        (reconstructionSecond F f XX af af₁ D)))
      ((mateEquiv af aq (commSqTwoSquare F hw)).natTrans.app (D.obj ()))
      (aq.counit.app (((singletonPullFunctor F f g P hw).obj D).obj ()))).symm
  exact Eq.mpr (congrArg IsIso hm) (Iso.isIso_hom _)

end

end Pseudofunctor

end CategoryTheory

end
