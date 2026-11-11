module

public import Mathlib.CategoryTheory.Sites.Over

/-!
# Base change of a sheaf on a slice site along a morphism of the base

Let `(C, J)` be a site with pullbacks and `f : X ⟶ Y` a morphism of `C`. The functors
`Over.map f : Over X ⥤ Over Y` and `Over.pullback f : Over Y ⥤ Over X` are continuous, so a
sheaf `F` on the slice site `(Over Y, J.over Y)` gives a sheaf

  `F.baseChangePushforward f : T ↦ F(T ×_Y X)`

on the same slice site, the pushforward along `Over.pullback f` of the restriction of `F` along
`Over.map f`. It receives the canonical morphism `F ⟶ F.baseChangePushforward f`, restriction
along the first projections `T ×_Y X ⟶ T`.

When `C` is a big site of schemes, `Y = S` and `f : Z ⟶ S` is a closed immersion, this is the
sheaf of sections over the base change to `Z`, the direct image of the restriction of `F` to
the schemes over `Z`.

## Main definitions

* `CategoryTheory.Sheaf.baseChangePushforward f F`: the sheaf `T ↦ F(T ×_Y X)`.
* `CategoryTheory.Sheaf.toBaseChangePushforward f F`: the morphism
  `F ⟶ F.baseChangePushforward f`.

## Main results

* `CategoryTheory.Sheaf.toBaseChangePushforward_hom_app`: its component at `T` is restriction
  along the first projection.
* `CategoryTheory.Sheaf.isIso_toBaseChangePushforward_hom_app`: when `f` is a monomorphism it
  is invertible at every `T` whose structure morphism factors through `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

namespace Sheaf

variable {X Y : C} (f : X ⟶ Y) (F : Sheaf (J.over Y) A)

/-- The sheaf `T ↦ F(T ×_Y X)` on the slice site over `Y`: restriction along `Over.map f`
followed by pushforward along `Over.pullback f`. -/
abbrev baseChangePushforward : Sheaf (J.over Y) A :=
  ((Over.pullback f).sheafPushforwardContinuous A (J.over Y) (J.over X)).obj
    (((Over.map f).sheafPushforwardContinuous A (J.over X) (J.over Y)).obj F)

/-- The first projection `T ×_Y X ⟶ T`, as a morphism of the slice over `Y`. -/
abbrev baseChangeFst (T : Over Y) : (Over.map f).obj ((Over.pullback f).obj T) ⟶ T :=
  Over.homMk (pullback.fst T.hom f) pullback.condition

@[reassoc]
lemma baseChangeFst_naturality {T T' : Over Y} (g : T ⟶ T') :
    (Over.map f).map ((Over.pullback f).map g) ≫ baseChangeFst f T' =
      baseChangeFst f T ≫ g := by
  ext
  exact pullback.lift_fst _ _ _

/-- The canonical morphism `F ⟶ F.baseChangePushforward f`, restriction along the first
projections `T ×_Y X ⟶ T`. -/
def toBaseChangePushforward : F ⟶ F.baseChangePushforward f where
  hom :=
    { app := fun T => F.obj.map (baseChangeFst f T.unop).op
      naturality := fun T T' g => by
        change F.obj.map g ≫ F.obj.map (baseChangeFst f T'.unop).op =
          F.obj.map (baseChangeFst f T.unop).op ≫
            F.obj.map ((Over.map f).map ((Over.pullback f).map g.unop)).op
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        exact Quiver.Hom.unop_inj (baseChangeFst_naturality f g.unop).symm }

/-- The component of `toBaseChangePushforward` at `T` is restriction along the first
projection `T ×_Y X ⟶ T`. -/
lemma toBaseChangePushforward_hom_app (T : Over Y) :
    (F.toBaseChangePushforward f).hom.app (op T) = F.obj.map (baseChangeFst f T).op :=
  rfl

/-- If `f` is a monomorphism, the first projection `T ×_Y X ⟶ T` is an isomorphism as soon as
the structure morphism of `T` factors through `f`. -/
lemma isIso_baseChangeFst [Mono f] {T : Over Y} (g : T.left ⟶ X) (hg : g ≫ f = T.hom) :
    IsIso (baseChangeFst f T) := by
  have hc : 𝟙 T.left ≫ T.hom = g ≫ f := by rw [Category.id_comp, hg]
  refine ⟨Over.homMk (pullback.lift (𝟙 _) g hc) ?_, ?_, ?_⟩
  · change pullback.lift (𝟙 _) g hc ≫ pullback.snd T.hom f ≫ f = T.hom
    rw [reassoc_of% pullback.lift_snd, hg]
  · apply Over.OverMorphism.ext
    change pullback.fst T.hom f ≫ pullback.lift (𝟙 _) g hc = 𝟙 _
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← cancel_mono f, Category.assoc,
        hg, pullback.condition]
  · apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- If `f` is a monomorphism, `toBaseChangePushforward` is invertible at every object whose
structure morphism factors through `f`. -/
lemma isIso_toBaseChangePushforward_hom_app [Mono f] {T : Over Y} (g : T.left ⟶ X)
    (hg : g ≫ f = T.hom) : IsIso ((F.toBaseChangePushforward f).hom.app (op T)) := by
  rw [toBaseChangePushforward_hom_app]
  have := isIso_baseChangeFst f g hg
  exact Functor.map_isIso _ _

end Sheaf

end CategoryTheory
