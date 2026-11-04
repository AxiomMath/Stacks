module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.ModuleSkyscraper.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The module-level stalk of a pullback of sheaves of modules

Let `f : X ⟶ Y` be a continuous map, let `O_X` and `O_Y` be sheaves of rings on `X` and `Y`,
and let `φ : O_Y ⟶ f_* O_X`. This file proves

`(f^* A)_x ≅ A_{f x} ⊗_{O_{Y, f x}} O_{X, x}`,

naturally in the sheaf of `O_Y`-modules `A`, where the extension of scalars on the right is
given as a left adjoint `L` of restriction of scalars along the stalk map of `φ`. It also
records the same isomorphism for a morphism of ringed spaces.

## Main definitions

* `Stacks.ModuleSkyscraper.stalkRingMap`: the map of stalk rings `O_{Y, f x} ⟶ O_{X, x}`
  induced by `φ`, with `stalkRingMap_germ` computing it on germs.
* `Stacks.ModuleSkyscraper.compAppEquiv`, `compApp`, `compPresheafIso`: the comparison over a
  single open of `Y`, and its presheaf-level assembly.
* `Stacks.ModuleSkyscraper.ringedSpaceStalkRingMap`: the stalk map of a morphism of ringed
  spaces.

## Main results

* `Stacks.ModuleSkyscraper.pushforwardSkyscraperIso`:
  `(skyscraper at x) ⋙ pushforward φ ≅ restrictScalars σ ⋙ (skyscraper at f x)`.
* `Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction`: the stalk of a pullback, as a natural
  isomorphism of functors.
* `Stacks.ModuleSkyscraper.ringedSpacePullbackStalkIso`: the same over
  `RingedSpaceModuleAdjunction.modulePullback`.

## References

* [Stacks Project, Tag 009A](https://stacks.math.columbia.edu/tag/009A)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

namespace Stacks.ModuleSkyscraper

section Site

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (OX : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (OY : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)
  (x : X)

/-- The map of stalk rings `O_{Y, f x} ⟶ O_{X, x}` induced by `φ`. -/
def stalkRingMap : Stalk OY (f x) ⟶ Stalk OX x :=
  (TopCat.Presheaf.stalkFunctor RingCat.{u} (f x)).map φ.hom ≫
    TopCat.Presheaf.stalkPushforward RingCat.{u} f OX.obj x

/-- The stalk map of `φ` sends the germ at `f x` of a section `r` of `O_Y` to the germ at `x` of
`φ r`. -/
lemma stalkRingMap_germ (V : Opens Y) (h : f x ∈ V) (r : OY.obj.obj (op V)) :
    (stalkRingMap f OX OY φ x).hom (germ OY (f x) V h r) =
      germ OX x ((Opens.map f).obj V) h (φ.hom.app (op V) r) :=
  (congrArg (TopCat.Presheaf.stalkPushforward RingCat.{u} f OX.obj x).hom
      (TopCat.Presheaf.stalkFunctor_map_germ_apply (C := RingCat.{u}) V (f x) h φ.hom r)).trans
    (TopCat.Presheaf.stalkPushforward_germ_apply RingCat.{u} f OX.obj V x h
      (φ.hom.app (op V) r))

/-- The module of values of the pushed-forward skyscraper: `M` with its scalars restricted
along the stalk map of `φ`. -/
abbrev restrictedValue (M : ModuleCat.{u} (Stalk OX x)) : ModuleCat.{u} (Stalk OY (f x)) :=
  (ModuleCat.restrictScalars (stalkRingMap f OX OY φ x).hom).obj M

variable (M : ModuleCat.{u} (Stalk OX x))

/-- Over an open of `Y`, the linear equivalence between the sections of the direct image of the
module skyscraper at `x` and those of the module skyscraper at `f x` with restricted scalars. -/
def compAppEquiv (V : (Opens Y)ᵒᵖ) :
    ((PresheafOfModules.pushforward φ.hom).obj (presheafObj OX x M)).obj V ≃ₗ[OY.obj.obj V]
      (presheafObj OY (f x) (restrictedValue f OX OY φ x M)).obj V where
  toFun s := s
  map_add' _ _ := rfl
  map_smul' r s := by
    funext h
    exact congrArg (· • s h) (stalkRingMap_germ f OX OY φ x (unop V) h.down r).symm
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl

/-- `compAppEquiv` as an isomorphism of `O_Y(V)`-modules. -/
def compApp (V : (Opens Y)ᵒᵖ) :
    ((PresheafOfModules.pushforward φ.hom).obj (presheafObj OX x M)).obj V ≅
      (presheafObj OY (f x) (restrictedValue f OX OY φ x M)).obj V :=
  LinearEquiv.toModuleIso (compAppEquiv f OX OY φ x M V)

/-- The presheaf-level comparison: the direct image of the module skyscraper at `x` is the
module skyscraper at `f x` with restricted scalars. -/
def compPresheafIso :
    (PresheafOfModules.pushforward φ.hom).obj (presheafObj OX x M) ≅
      presheafObj OY (f x) (restrictedValue f OX OY φ x M) :=
  PresheafOfModules.isoMk (compApp f OX OY φ x M) (fun {_ _} i => by ext s; funext h; rfl)

variable {M}

/-- **The direct image of the module skyscraper at `x` is the module skyscraper at `f x`**,
with scalars restricted along the stalk map of `φ`; naturally in the value module. -/
def pushforwardSkyscraperIso :
    functor OX x ⋙ SheafOfModules.pushforward φ ≅
      ModuleCat.restrictScalars (stalkRingMap f OX OY φ x).hom ⋙ functor OY (f x) :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.fullyFaithfulForget OY).preimageIso (compPresheafIso f OX OY φ x M))
    (fun {M N} g => by ext V s; funext h; rfl)

/-- **The module-level stalk of a pullback, naturally in the module.** If `L` is left adjoint
to restriction of scalars along the stalk map of `φ` — for a sheaf of commutative rings this
is `ModuleCat.extendScalars`, so that `L A = A ⊗_{O_{Y, f x}} O_{X, x}` — then

`(f^* A)_x ≅ L (A_{f x})`

as functors in `A`. -/
def pullbackStalkIsoOfAdjunction {L : ModuleCat.{u} (Stalk OY (f x)) ⥤ ModuleCat.{u} (Stalk OX x)}
    (adjL : L ⊣ ModuleCat.restrictScalars (stalkRingMap f OX OY φ x).hom) :
    SheafOfModules.pullback.{u} φ ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor OX x ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor OY (f x) ⋙ L :=
  ((conjugateIsoEquiv
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} φ).comp (adjunction OX x))
      ((adjunction OY (f x)).comp adjL)).symm
    (pushforwardSkyscraperIso f OX OY φ x)).symm

end Site

section RingedSpace

open RingedSpaceModuleAdjunction

variable {Z W : AlgebraicGeometry.RingedSpace.{u, u}} (g : Z ⟶ W) (z : Z.carrier)

/-- The map of stalk rings `O_{W, g z} ⟶ O_{Z, z}` of a morphism of ringed spaces. -/
abbrev ringedSpaceStalkRingMap :
    Stalk (structureSheafRing W) (g.hom.base z) ⟶ Stalk (structureSheafRing Z) z :=
  stalkRingMap g.hom.base (structureSheafRing Z) (structureSheafRing W) (structureSheafHom g) z

/-- **The module-level stalk of a pullback along a morphism of ringed spaces.** If `L` is left
adjoint to restriction of scalars along the stalk map of `g` at `z`, then
`(g^* A)_z ≅ L (A_{g z})` for the pullback `RingedSpaceModuleAdjunction.modulePullback g`,
naturally in `A`. -/
def ringedSpacePullbackStalkIso
    {L : ModuleCat.{u} (Stalk (structureSheafRing W) (g.hom.base z)) ⥤
      ModuleCat.{u} (Stalk (structureSheafRing Z) z)}
    (adjL : L ⊣ ModuleCat.restrictScalars (ringedSpaceStalkRingMap g z).hom) :
    modulePullback g ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing W) (g.hom.base z) ⋙ L :=
  pullbackStalkIsoOfAdjunction g.hom.base (structureSheafRing Z) (structureSheafRing W)
    (structureSheafHom g) z adjL

end RingedSpace

end Stacks.ModuleSkyscraper
