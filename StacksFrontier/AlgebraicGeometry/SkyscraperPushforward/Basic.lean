module

public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pushforward of a skyscraper sheaf, and the inverse-image stalk as a functor

For a continuous `f : X ⟶ Y` and `x : X`, the direct image of the skyscraper sheaf at `x` is the
skyscraper sheaf at `f x`, and the stalk at `x` of the sheaf inverse image is naturally isomorphic,
as a functor of the sheaf, to the stalk at `f x`.

## Main definitions

* `Stacks.SkyscraperPushforward.skyscraperSheafPushforwardIso`:
  `skyscraperSheafFunctor x ⋙ TopCat.Sheaf.pushforward C f ≅ skyscraperSheafFunctor (f x)`.
* `Stacks.SkyscraperPushforward.stalkSheafifyNatIso` and
  `Stacks.SkyscraperPushforward.stalkPresheafPullbackNatIso`: the sheafification and presheaf
  inverse-image stalk comparisons as natural isomorphisms of functors.
* `Stacks.SkyscraperPushforward.stalkSheafPullbackNatIso`: the stalk of the sheaf inverse image as
  a natural isomorphism of functors, `TopCat.Sheaf.pullback A f ⋙ (stalk at x) ≅ (stalk at f x)`.
* `Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso`: a natural isomorphism between the
  same two functors, the conjugate of the skyscraper comparison under the composite of the
  inverse-image/direct-image adjunction with the stalk/skyscraper adjunction.
* `Stacks.SkyscraperPushforward.stalkInverseImageNatIso`: the stalk of the inverse image of a sheaf
  of rings along a morphism of schemes, as a natural isomorphism of functors.

## Main results

* `Stacks.SkyscraperPushforward.stalkSheafPullbackNatIso_hom_app`: the components of
  `stalkSheafPullbackNatIso` are `Stacks.SheafifyStalk.stalkSheafPullbackIso`.
* `Stacks.SkyscraperPushforward.stalkSheafPullbackIso_naturality`: the stalk comparison
  `Stacks.SheafifyStalk.stalkSheafPullbackIso` is natural in the sheaf.
* `Stacks.SkyscraperPushforward.stalkPullbackHom_homEquiv_symm`: the stalk of an adjoint mate is
  the induced map on stalks.
* `Stacks.SkyscraperPushforward.stalkPullbackHom_stalkMap`: at a morphism of schemes, the stalk of
  the adjoint mate of the comorphism is `AlgebraicGeometry.Scheme.Hom.stalkMap`.

## Implementation notes

`Stacks.SheafifyStalk.stalkSheafPullbackIso` is a composite of three natural comparisons, but its
naturality cannot be obtained by reassociating their naturality squares: that needs
`TopCat.Sheaf.pullback` identified with the sheafification of the presheaf inverse image through
`TopCat.Sheaf.pullbackIso`, a genuine isomorphism between chosen left adjoints, so the reassociated
equation is not type-correct at the transparency `rw` and `simp` use to build a motive. The three
are instead composed as natural isomorphisms of functors, where `Functor.isoWhiskerLeft` and
`Functor.isoWhiskerRight` need no associator.

Decidability for `skyscraperSheafFunctor` is supplied by the local instance
`Classical.propDecidable`, so that both sides of the skyscraper comparison use the same term and
`Iso.refl` type-checks; `stalkSkyscraperSheafAdjunction` needs it too.

`TopCat.Presheaf.stalk` is made implicitly reducible for `stalkPullbackHom_homEquiv_symm`, whose
first rewrite otherwise fails to match `F.stalk x` with `(stalkFunctor C x).obj F`.

The value category's hom universe equals the universe of the underlying space, as
`TopCat.Presheaf.stalkFunctor` and `TopCat.Sheaf.pullback` both require.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

noncomputable section

namespace Stacks.SkyscraperPushforward

section Skyscraper

attribute [local instance] Classical.propDecidable

variable {C : Type u} [Category.{v} C] [HasTerminal C] {X Y : TopCat.{v}}

/-- The direct image of a skyscraper sheaf is the skyscraper sheaf at the image point:
`skyscraperSheafFunctor x ⋙ f_* ≅ skyscraperSheafFunctor (f x)`. -/
@[ega "IV 21.9.1" "more general"]
public def skyscraperSheafPushforwardIso (f : X ⟶ Y) (x : X) :
    skyscraperSheafFunctor x ⋙ TopCat.Sheaf.pushforward C f ≅ skyscraperSheafFunctor (f x) :=
  Iso.refl _

end Skyscraper

section StalkPullback

variable (A : Type u) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}}

/-- Sheafification does not change stalks, as an isomorphism of functors with components
`TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso`. -/
public def stalkSheafifyNatIso (x : X) :
    TopCat.Presheaf.stalkFunctor A x ≅
      presheafToSheaf (Opens.grothendieckTopology X) A ⋙ TopCat.Sheaf.forget A X ⋙
        TopCat.Presheaf.stalkFunctor A x :=
  NatIso.ofComponents (fun P => TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso P x)
    (fun β => (Stacks.SheafifyStalk.stalkSheafifyIso_naturality A β x).symm)

/-- The presheaf inverse-image stalk comparison, as an isomorphism of functors
`(stalk at f x) ≅ f⁻¹ ⋙ (stalk at x)` on presheaves on `Y`, with components
`TopCat.Presheaf.stalkPullbackIso`. -/
public def stalkPresheafPullbackNatIso (f : X ⟶ Y) (x : X) :
    TopCat.Presheaf.stalkFunctor A (f x) ≅
      TopCat.Presheaf.pullback A f ⋙ TopCat.Presheaf.stalkFunctor A x :=
  NatIso.ofComponents (fun F => TopCat.Presheaf.stalkPullbackIso A f F x)
    (fun α => (Stacks.SheafifyStalk.stalkPullbackHom_naturality A f α x).symm)

/-- The stalk of the sheaf inverse image, as an isomorphism of functors
`f⁻¹ ⋙ (stalk at x) ≅ (stalk at f x)` on sheaves on `Y`. -/
@[ega "0 3.7.2" "more general"]
public def stalkSheafPullbackNatIso (f : X ⟶ Y) (x : X) :
    TopCat.Sheaf.pullback A f ⋙ TopCat.Sheaf.forget A X ⋙ TopCat.Presheaf.stalkFunctor A x ≅
      TopCat.Sheaf.forget A Y ⋙ TopCat.Presheaf.stalkFunctor A (f x) :=
  Functor.isoWhiskerRight (TopCat.Sheaf.pullbackIso A f)
      (TopCat.Sheaf.forget A X ⋙ TopCat.Presheaf.stalkFunctor A x) ≪≫
    Functor.isoWhiskerLeft (TopCat.Sheaf.forget A Y)
      (Functor.isoWhiskerLeft (TopCat.Presheaf.pullback A f) (stalkSheafifyNatIso A x).symm ≪≫
        (stalkPresheafPullbackNatIso A f x).symm)

/-- The components of `Stacks.SkyscraperPushforward.stalkSheafPullbackNatIso` are the per-sheaf
comparisons `Stacks.SheafifyStalk.stalkSheafPullbackIso`. -/
public theorem stalkSheafPullbackNatIso_hom_app (f : X ⟶ Y) (F : TopCat.Sheaf A Y) (x : X) :
    (stalkSheafPullbackNatIso A f x).hom.app F =
      (Stacks.SheafifyStalk.stalkSheafPullbackIso A f F x).hom :=
  rfl

/-- The inverse-image stalk comparison is natural in the sheaf: for `φ : F ⟶ G` on `Y` the square
relating `(f⁻¹F)_x ≅ F_{f(x)}` and `(f⁻¹G)_x ≅ G_{f(x)}` commutes. -/
public theorem stalkSheafPullbackIso_naturality (f : X ⟶ Y) {F G : TopCat.Sheaf A Y}
    (φ : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor A x).map
          ((TopCat.Sheaf.forget A X).map ((TopCat.Sheaf.pullback A f).map φ)) ≫
        (Stacks.SheafifyStalk.stalkSheafPullbackIso A f G x).hom =
      (Stacks.SheafifyStalk.stalkSheafPullbackIso A f F x).hom ≫
        (TopCat.Presheaf.stalkFunctor A (f x)).map ((TopCat.Sheaf.forget A Y).map φ) :=
  (stalkSheafPullbackNatIso A f x).hom.naturality φ

section Mates

attribute [local instance] Classical.propDecidable

/-- The isomorphism `(stalk at f x) ≅ f⁻¹ ⋙ (stalk at x)` on sheaves on `Y` conjugate to
`Stacks.SkyscraperPushforward.skyscraperSheafPushforwardIso` under the adjunctions
`f⁻¹ ⋙ (stalk at x) ⊣ skyscraperSheafFunctor x ⋙ f_*` and
`(stalk at f x) ⊣ skyscraperSheafFunctor (f x)`. -/
public def stalkSheafPullbackMateNatIso (f : X ⟶ Y) (x : X) :
    TopCat.Sheaf.forget A Y ⋙ TopCat.Presheaf.stalkFunctor A (f x) ≅
      TopCat.Sheaf.pullback A f ⋙ TopCat.Sheaf.forget A X ⋙ TopCat.Presheaf.stalkFunctor A x :=
  (conjugateIsoEquiv ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).comp
    (stalkSkyscraperSheafAdjunction x)) (stalkSkyscraperSheafAdjunction (f x))).symm
      (skyscraperSheafPushforwardIso f x)

end Mates

end StalkPullback

section Mate

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable (C : Type u) [Category.{v} C] [HasColimits.{v} C] {X Y : TopCat.{v}}

/-- The stalk of a presheaf-level adjoint mate is the induced map on stalks: for
`η : F ⟶ f_*G` with mate `f⁻¹F ⟶ G`, the composite `F_{f(x)} ⟶ (f⁻¹F)_x ⟶ G_x` is the stalk of
`η` followed by the direct-image stalk comparison. -/
public theorem stalkPullbackHom_homEquiv_symm (f : X ⟶ Y) {F : Y.Presheaf C} {G : X.Presheaf C}
    (η : F ⟶ (TopCat.Presheaf.pushforward C f).obj G) (x : X) :
    TopCat.Presheaf.stalkPullbackHom C f F x ≫ (TopCat.Presheaf.stalkFunctor C x).map
          (((TopCat.Presheaf.pullbackPushforwardAdjunction C f).homEquiv F G).symm η) =
      (TopCat.Presheaf.stalkFunctor C (f x)).map η ≫
        TopCat.Presheaf.stalkPushforward C f G x := by
  rw [TopCat.Presheaf.stalkPullbackHom, Category.assoc,
    ← Stacks.SheafifyStalk.stalkPushforward_naturality C f _ x, ← Category.assoc,
    ← Functor.map_comp, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

end Mate

section Schemes

open AlgebraicGeometry

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- The stalk of the inverse image of a sheaf of rings along a morphism of schemes `g`, naturally
in the sheaf: `g⁻¹ ⋙ (stalk at t) ≅ (stalk at g t)`. -/
public def stalkInverseImageNatIso (t : T) :
    TopCat.Sheaf.pullback CommRingCat.{u} g.base ⋙
        TopCat.Sheaf.forget CommRingCat.{u} T.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor CommRingCat.{u} t ≅
      TopCat.Sheaf.forget CommRingCat.{u} S.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor CommRingCat.{u} (g.base t) :=
  stalkSheafPullbackNatIso CommRingCat.{u} g.base t

/-- For a morphism of schemes `g : T ⟶ S`, the stalk at `t` of the presheaf-level adjoint mate of
the comorphism `g.c`, composed with the presheaf inverse-image stalk comparison, is
`AlgebraicGeometry.Scheme.Hom.stalkMap g t : 𝒪_{S,g(t)} ⟶ 𝒪_{T,t}`. -/
public theorem stalkPullbackHom_stalkMap (t : T) :
    TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} g.base S.presheaf t ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} t).map
          (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
            S.presheaf T.presheaf).symm g.c) =
      g.stalkMap t :=
  stalkPullbackHom_homEquiv_symm CommRingCat.{u} g.base g.c t

end Schemes

end Stacks.SkyscraperPushforward

end

end
